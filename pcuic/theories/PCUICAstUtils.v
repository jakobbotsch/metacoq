From Coq Require Import Ascii String OrderedType Lia Arith.
From MetaCoq.Template Require Import utils uGraph.
From MetaCoq.PCUIC Require Import PCUICAst PCUICSize.
Import List.ListNotations.
Require Import ssreflect.

From Equations Require Import Equations.

Set Asymmetric Patterns.

Derive NoConfusion for term.
Derive Signature for All.
Derive Signature for All2.

Open Scope pcuic.
Local Open Scope string_scope.
Fixpoint string_of_term (t : term) :=
  match t with
  | tRel n => "Rel(" ++ string_of_nat n ++ ")"
  | tVar n => "Var(" ++ n ++ ")"
  | tEvar ev args => "Evar(" ++ string_of_nat ev ++ "," ++ string_of_list string_of_term args ++ ")"
  | tSort s => "Sort(" ++ string_of_sort s ++ ")"
  | tProd na b t => "Prod(" ++ string_of_name na ++ "," ++
                            string_of_term b ++ "," ++ string_of_term t ++ ")"
  | tLambda na b t => "Lambda(" ++ string_of_name na ++ "," ++ string_of_term b
                                ++ "," ++ string_of_term t ++ ")"
  | tLetIn na b t' t => "LetIn(" ++ string_of_name na ++ "," ++ string_of_term b
                                 ++ "," ++ string_of_term t' ++ "," ++ string_of_term t ++ ")"
  | tApp f l => "App(" ++ string_of_term f ++ "," ++ string_of_term l ++ ")"
  | tConst c u => "Const(" ++ c ++ "," ++ string_of_universe_instance u ++ ")"
  | tInd i u => "Ind(" ++ string_of_inductive i ++ "," ++ string_of_universe_instance u ++ ")"
  | tConstruct i n u => "Construct(" ++ string_of_inductive i ++ "," ++ string_of_nat n ++ ","
                                    ++ string_of_universe_instance u ++ ")"
  | tCase (ind, i) t p brs =>
    "Case(" ++ string_of_inductive ind ++ "," ++ string_of_nat i ++ "," ++ string_of_term t ++ ","
            ++ string_of_term p ++ "," ++ string_of_list (fun b => string_of_term (snd b)) brs ++ ")"
  | tProj (ind, i, k) c =>
    "Proj(" ++ string_of_inductive ind ++ "," ++ string_of_nat i ++ "," ++ string_of_nat k ++ ","
            ++ string_of_term c ++ ")"
  | tFix l n => "Fix(" ++ (string_of_list (string_of_def string_of_term) l) ++ "," ++ string_of_nat n ++ ")"
  | tCoFix l n => "CoFix(" ++ (string_of_list (string_of_def string_of_term) l) ++ "," ++ string_of_nat n ++ ")"
  end.
Local Close Scope string_scope.

Fixpoint decompose_app_rec (t : term) l :=
  match t with
  | tApp f a => decompose_app_rec f (a :: l)
  | _ => (t, l)
  end.

Definition decompose_app t := decompose_app_rec t [].

Lemma decompose_app_rec_mkApps f l l' : decompose_app_rec (mkApps f l) l' =
                                    decompose_app_rec f (l ++ l').
Proof.
  induction l in f, l' |- *; simpl; auto; rewrite IHl ?app_nil_r; auto.
Qed.

Require Import ssrbool.

Lemma decompose_app_mkApps f l :
  ~~ isApp f -> decompose_app (mkApps f l) = (f, l).
Proof.
  intros Hf. rewrite /decompose_app decompose_app_rec_mkApps. rewrite app_nil_r.
  destruct f; simpl in *; (discriminate || reflexivity).
Qed.

Lemma mkApps_nested f l l' : mkApps (mkApps f l) l' = mkApps f (l ++ l').
Proof.
  induction l in f, l' |- *; destruct l'; simpl; rewrite ?app_nil_r; auto.
  rewrite <- IHl. simpl. reflexivity.
Qed.

Fixpoint decompose_prod (t : term) : (list name) * (list term) * term :=
  match t with
  | tProd n A B => let (nAs, B) := decompose_prod B in
                  let (ns, As) := nAs in
                  (n :: ns, A :: As, B)
  | _ => ([], [], t)
  end.

Fixpoint remove_arity (n : nat) (t : term) : term :=
  match n with
  | O => t
  | S n => match t with
          | tProd _ _ B => remove_arity n B
          | _ => t (* todo *)
          end
  end.

Definition isConstruct_app t :=
  match fst (decompose_app t) with
  | tConstruct _ _ _ => true
  | _ => false
  end.

(* was mind_decl_to_entry *)
Definition mind_body_to_entry (decl : mutual_inductive_body)
  : mutual_inductive_entry.
Proof.
  refine {| mind_entry_record := None; (* not a record *)
            mind_entry_finite := Finite; (* inductive *)
            mind_entry_params := _;
            mind_entry_inds := _;
            mind_entry_universes := decl.(ind_universes);
            mind_entry_private := None |}.
  - refine (match List.hd_error decl.(ind_bodies) with
            | Some i0 => _
            | None => nil (* assert false: at least one inductive in a mutual block *)
            end).
    pose (typ := decompose_prod i0.(ind_type)).
    destruct typ as [[names types] _].
    apply (List.firstn decl.(ind_npars)) in names.
    apply (List.firstn decl.(ind_npars)) in types.
    refine (List.combine _ _).
    exact (List.map get_ident names).
    exact (List.map LocalAssum types).
  - refine (List.map _ decl.(ind_bodies)).
    intros [].
    refine {| mind_entry_typename := ind_name;
              mind_entry_arity := remove_arity decl.(ind_npars) ind_type;
              mind_entry_template := false;
              mind_entry_consnames := _;
              mind_entry_lc := _;
            |}.
    refine (List.map (fun x => fst (fst x)) ind_ctors).
    refine (List.map (fun x => remove_arity decl.(ind_npars)
                                                (snd (fst x))) ind_ctors).
Defined.

Fixpoint decompose_prod_assum (Γ : context) (t : term) : context * term :=
  match t with
  | tProd n A B => decompose_prod_assum (Γ ,, vass n A) B
  | tLetIn na b bty b' => decompose_prod_assum (Γ ,, vdef na b bty) b'
  | _ => (Γ, t)
  end.

Fixpoint decompose_prod_n_assum (Γ : context) n (t : term) : option (context * term) :=
  match n with
  | 0 => Some (Γ, t)
  | S n =>
    match t with
    | tProd na A B => decompose_prod_n_assum (Γ ,, vass na A) n B
    | tLetIn na b bty b' => decompose_prod_n_assum (Γ ,, vdef na b bty) n b'
    | _ => None
    end
  end.

(* todo move *)
Lemma it_mkLambda_or_LetIn_app l l' t :
  it_mkLambda_or_LetIn (l ++ l') t = it_mkLambda_or_LetIn l' (it_mkLambda_or_LetIn l t).
Proof. induction l in l', t |- *; simpl; auto. Qed.

Lemma decompose_prod_n_assum_it_mkProd ctx ctx' ty :
  decompose_prod_n_assum ctx #|ctx'| (it_mkProd_or_LetIn ctx' ty) = Some (ctx' ++ ctx, ty).
Proof.
  revert ctx ty. induction ctx' using rev_ind; move=> // ctx ty.
  rewrite app_length /= it_mkProd_or_LetIn_app /=.
  destruct x as [na [body|] ty'] => /=;
  now rewrite !Nat.add_1_r /= IHctx' -app_assoc.
Qed.

Definition is_ind_app_head t :=
  let (f, l) := decompose_app t in
  match f with
  | tInd _ _ => true
  | _ => false
  end.

Lemma is_ind_app_head_mkApps ind u l : is_ind_app_head (mkApps (tInd ind u) l).
Proof.
  unfold is_ind_app_head.
  unfold decompose_app. rewrite decompose_app_rec_mkApps. now simpl; trivial.
Qed.

Lemma decompose_prod_assum_it_mkProd ctx ctx' ty :
  is_ind_app_head ty ->
  decompose_prod_assum ctx (it_mkProd_or_LetIn ctx' ty) = (ctx' ++ ctx, ty).
Proof.
  revert ctx ty. induction ctx' using rev_ind; move=> // ctx ty /=.
  destruct ty; unfold is_ind_app_head; simpl; try (congruence || reflexivity).
  move=> Hty. rewrite it_mkProd_or_LetIn_app /=.
  case: x => [na [body|] ty'] /=; by rewrite IHctx' // /snoc -app_assoc.
Qed.

Lemma reln_list_lift_above l p Γ :
  Forall (fun x => exists n, x = tRel n /\ p <= n /\ n < p + length Γ) l ->
  Forall (fun x => exists n, x = tRel n /\ p <= n /\ n < p + length Γ) (reln l p Γ).
Proof.
  generalize (le_refl p).
  generalize p at 1 3 5.
  induction Γ in p, l |- *. simpl. auto.
  intros. destruct a. destruct decl_body. simpl.
  assert(p0 <= S p) by lia.
  specialize (IHΓ l (S p) p0 H1). rewrite <- Nat.add_succ_comm, Nat.add_1_r.
  simpl in *. rewrite <- Nat.add_succ_comm in H0. eauto.
  simpl in *.
  specialize (IHΓ (tRel p :: l) (S p) p0 ltac:(lia)). rewrite <- Nat.add_succ_comm, Nat.add_1_r.
  eapply IHΓ. simpl in *. rewrite <- Nat.add_succ_comm in H0. auto.
  simpl in *.
  constructor. exists p. intuition lia. auto.
Qed.

Lemma to_extended_list_k_spec Γ k :
  Forall (fun x => exists n, x = tRel n /\ k <= n /\ n < k + length Γ) (to_extended_list_k Γ k).
Proof.
  pose (reln_list_lift_above [] k Γ).
  unfold to_extended_list_k.
  forward f. constructor. apply f.
Qed.

Lemma to_extended_list_lift_above Γ :
  Forall (fun x => exists n, x = tRel n /\ n < length Γ) (to_extended_list Γ).
Proof.
  pose (reln_list_lift_above [] 0 Γ).
  unfold to_extended_list.
  forward f. constructor. eapply Forall_impl; eauto. intros.
  destruct H; eexists; intuition eauto.
Qed.

Fixpoint reln_alt p Γ :=
  match Γ with
  | [] => []
  | {| decl_body := Some _ |} :: Γ => reln_alt (p + 1) Γ
  | {| decl_body := None |} :: Γ => tRel p :: reln_alt (p + 1) Γ
  end.

Lemma reln_alt_eq l Γ k : reln l k Γ = List.rev (reln_alt k Γ) ++ l.
Proof.
  induction Γ in l, k |- *; simpl; auto.
  destruct a as [na [body|] ty]; simpl.
  now rewrite IHΓ.
  now rewrite IHΓ -app_assoc.
Qed.

Lemma to_extended_list_k_cons d Γ k :
  to_extended_list_k (d :: Γ) k =
  match d.(decl_body) with
  | None => to_extended_list_k Γ (S k) ++ [tRel k]
  | Some b => to_extended_list_k Γ (S k)
  end.
Proof.
  rewrite /to_extended_list_k reln_alt_eq. simpl.
  destruct d as [na [body|] ty]. simpl.
  now rewrite reln_alt_eq Nat.add_1_r.
  simpl. rewrite reln_alt_eq.
  now rewrite -app_assoc !app_nil_r Nat.add_1_r.
Qed.

Lemma context_assumptions_length_bound Γ : context_assumptions Γ <= #|Γ|.
Proof.
  induction Γ; simpl; auto. destruct a as [? [?|] ?]; simpl; auto.
  lia.
Qed.


Lemma compose_map_decl f g x : map_decl f (map_decl g x) = map_decl (f ∘ g) x.
Proof.
  destruct x as [? [?|] ?]; reflexivity.
Qed.

Lemma map_decl_ext f g x : (forall x, f x = g x) -> map_decl f x = map_decl g x.
Proof.
  intros H; destruct x as [? [?|] ?]; rewrite /map_decl /=; f_equal; auto.
  now rewrite (H t).
Qed.

Lemma mkApps_inj :
  forall u v l,
    mkApps u l = mkApps v l ->
    u = v.
Proof.
  intros u v l eq.
  revert u v eq.
  induction l ; intros u v eq.
  - cbn in eq. assumption.
  - cbn in eq. apply IHl in eq.
    inversion eq. reflexivity.
Qed.

Lemma isApp_mkApps :
  forall u l,
    isApp u ->
    isApp (mkApps u l).
Proof.
  intros u l h.
  induction l in u, h |- *.
  - cbn. assumption.
  - cbn. apply IHl. reflexivity.
Qed.

Lemma decompose_app_rec_notApp :
  forall t l u l',
    decompose_app_rec t l = (u, l') ->
    isApp u = false.
Proof.
  intros t l u l' e.
  induction t in l, u, l', e |- *.
  all: try (cbn in e ; inversion e ; reflexivity).
  cbn in e. eapply IHt1. eassumption.
Qed.

Lemma decompose_app_notApp :
  forall t u l,
    decompose_app t = (u, l) ->
    isApp u = false.
Proof.
  intros t u l e.
  eapply decompose_app_rec_notApp. eassumption.
Qed.

Fixpoint nApp t :=
  match t with
  | tApp u _ => S (nApp u)
  | _ => 0
  end.

Lemma isApp_false_nApp :
  forall u,
    isApp u = false ->
    nApp u = 0.
Proof.
  intros u h.
  destruct u.
  all: try reflexivity.
  discriminate.
Qed.

Lemma nApp_mkApps :
  forall t l,
    nApp (mkApps t l) = nApp t + #|l|.
Proof.
  intros t l.
  induction l in t |- *.
  - simpl. lia.
  - simpl. rewrite IHl. cbn. lia.
Qed.

Lemma decompose_app_eq_mkApps :
  forall t u l l',
    decompose_app t = (mkApps u l', l) ->
    l' = [].
Proof.
  intros t u l l' e.
  apply decompose_app_notApp in e.
  apply isApp_false_nApp in e.
  rewrite nApp_mkApps in e.
  destruct l' ; cbn in e ; try lia.
  reflexivity.
Qed.

Lemma mkApps_nApp_inj :
  forall u u' l l',
    nApp u = nApp u' ->
    mkApps u l = mkApps u' l' ->
    u = u' /\ l = l'.
Proof.
  intros u u' l l' h e.
  induction l in u, u', l', h, e |- *.
  - cbn in e. subst.
    destruct l' ; auto.
    exfalso.
    rewrite nApp_mkApps in h. cbn in h. lia.
  - destruct l'.
    + cbn in e. subst. exfalso.
      rewrite nApp_mkApps in h. cbn in h. lia.
    + cbn in e. apply IHl in e.
      * destruct e as [e1 e2].
        inversion e1. subst. auto.
      * cbn. f_equal. auto.
Qed.

Lemma mkApps_notApp_inj :
  forall u u' l l',
    isApp u = false ->
    isApp u' = false ->
    mkApps u l = mkApps u' l' ->
    u = u' /\ l = l'.
Proof.
  intros u u' l l' h h' e.
  eapply mkApps_nApp_inj.
  - rewrite -> 2!isApp_false_nApp by assumption. reflexivity.
  - assumption.
Qed.

Lemma decompose_app_rec_inv {t l' f l} :
  decompose_app_rec t l' = (f, l) ->
  mkApps t l' = mkApps f l.
Proof.
  induction t in f, l', l |- *; try intros [= <- <-]; try reflexivity.
  simpl. apply/IHt1.
Qed.

Lemma decompose_app_inv {t f l} :
  decompose_app t = (f, l) -> t = mkApps f l.
Proof. by apply/decompose_app_rec_inv. Qed.

Lemma mkApps_Fix_spec mfix idx args t : mkApps (tFix mfix idx) args = t ->
                                        match decompose_app t with
                                        | (tFix mfix idx, args') => args' = args
                                        | _ => False
                                        end.
Proof.
  intros H; apply (f_equal decompose_app) in H.
  rewrite decompose_app_mkApps in H. reflexivity.
  destruct t; noconf H. rewrite <- H. reflexivity.
  simpl. reflexivity.
Qed.

Lemma decompose_app_rec_tFix mfix idx args t l :
  decompose_app_rec t l = (tFix mfix idx, args) -> mkApps t l = mkApps (tFix mfix idx) args.
Proof.
  unfold decompose_app.
  revert l args.
  induction t; intros args l' H; noconf H. simpl in H.
  now specialize (IHt1 _ _ H).
  reflexivity.
Qed.

Lemma decompose_app_tFix mfix idx args t :
  decompose_app t = (tFix mfix idx, args) -> t = mkApps (tFix mfix idx) args.
Proof. apply decompose_app_rec_tFix. Qed.

Lemma mkApps_size x l : size (mkApps x l) = size x + list_size size l.
Proof.
  induction l in x |- *; simpl; simp list_size. lia.
  rewrite IHl. simpl. lia.
Qed.

Lemma mkApps_eq_head {x l} : mkApps x l = x -> l = [].
Proof.
  assert (WF : WellFounded (precompose lt size))
    by apply wf_precompose, lt_wf.
  induction l. simpl. constructor.
  apply apply_noCycle_right. simpl. red. rewrite mkApps_size. simpl. lia.
Qed.

Lemma mkApps_eq_inv {x y l} : x = mkApps y l -> size y <= size x.
Proof.
  assert (WF : WellFounded (precompose lt size))
    by apply wf_precompose, lt_wf.
  induction l in x, y |- *. simpl. intros -> ; constructor.
  simpl. intros. specialize (IHl _ _ H). simpl in IHl. lia.
Qed.

Lemma mkApps_eq_left x y l : mkApps x l = mkApps y l -> x = y.
Proof.
  induction l in x, y |- *; simpl. auto.
  intros. simpl in *. specialize (IHl _ _ H). now noconf IHl.
Qed.

Lemma decompose_app_eq_right t l l' : decompose_app_rec t l = decompose_app_rec t l' -> l = l'.
Proof.
  induction t in l, l' |- *; simpl; intros [=]; auto.
  specialize (IHt1 _ _ H0). now noconf IHt1.
Qed.

Lemma mkApps_eq_right t l l' : mkApps t l = mkApps t l' -> l = l'.
Proof.
  intros. eapply (f_equal decompose_app) in H. unfold decompose_app in H.
  rewrite !decompose_app_rec_mkApps in H. apply decompose_app_eq_right in H.
  now rewrite !app_nil_r in H.
Qed.

Lemma atom_decompose_app t l : ~~ isApp t -> decompose_app_rec t l = pair t l.
Proof. destruct t; simpl; congruence. Qed.

Lemma mkApps_eq_inj {t t' l l'} :
  mkApps t l = mkApps t' l' ->
  ~~ isApp t -> ~~ isApp t' -> t = t' /\ l = l'.
Proof.
  intros Happ Ht Ht'. eapply (f_equal decompose_app) in Happ. unfold decompose_app in Happ.
  rewrite !decompose_app_rec_mkApps in Happ. rewrite !atom_decompose_app in Happ; auto.
  rewrite !app_nil_r in Happ. intuition congruence.
Qed.

Ltac solve_discr' :=
  match goal with
    H : mkApps _ _ = mkApps ?f ?l |- _ =>
    eapply mkApps_eq_inj in H as [? ?]; [|easy|easy]; subst; try intuition congruence
  | H : ?t = mkApps ?f ?l |- _ =>
    change t with (mkApps t []) in H ;
    eapply mkApps_eq_inj in H as [? ?]; [|easy|easy]; subst; try intuition congruence
  | H : mkApps ?f ?l = ?t |- _ =>
    change t with (mkApps t []) in H ;
    eapply mkApps_eq_inj in H as [? ?]; [|easy|easy]; subst; try intuition congruence
  end.

Lemma mkApps_eq_decompose {f args t} :
  mkApps f args = t ->
  ~~ isApp f ->
  fst (decompose_app t) = f.
Proof.
  intros H Happ; apply (f_equal decompose_app) in H.
  rewrite decompose_app_mkApps in H. auto. rewrite <- H. reflexivity.
Qed.

Ltac finish_discr :=
  repeat match goal with
         | [ H : ?x = ?x |- _ ] => clear H
         | [ H : mkApps _ _ = mkApps _ _ |- _ ] =>
           let H0 := fresh in let H1 := fresh in
                              specialize (mkApps_eq_inj H eq_refl eq_refl) as [H0 H1];
                              clear H;
                              try (congruence || (noconf H0; noconf H1))
         | [ H : mkApps _ _ = _ |- _ ] => apply mkApps_eq_head in H
         end.

Ltac prepare_discr :=
  repeat match goal with
         | [ H : mkApps ?f ?l = tApp ?y ?r |- _ ] => change (mkApps f l = mkApps y [r]) in H
         | [ H : tApp ?f ?l = mkApps ?y ?r |- _ ] => change (mkApps f [l] = mkApps y r) in H
         | [ H : mkApps ?x ?l = ?y |- _ ] =>
           match y with
           | mkApps _ _ => fail 1
           | _ => change (mkApps x l = mkApps y []) in H
           end
         | [ H : ?x = mkApps ?y ?l |- _ ] =>
           match x with
           | mkApps _ _ => fail 1
           | _ => change (mkApps x [] = mkApps y l) in H
           end
         end.


Inductive mkApps_spec : term -> list term -> term -> list term -> term -> Type :=
| mkApps_intro f l n :
    ~~ isApp f ->
    mkApps_spec f l (mkApps f (firstn n l)) (skipn n l) (mkApps f l).

Lemma decompose_app_rec_eq f l :
  ~~ isApp f ->
  decompose_app_rec f l = (f, l).
Proof.
  destruct f; simpl; try discriminate; congruence.
Qed.
Close Scope string_scope.

Lemma firstn_add {A} x y (args : list A) : firstn (x + y) args = firstn x args ++ firstn y (skipn x args).
Proof.
  induction x in y, args |- *. simpl. reflexivity.
  simpl. destruct args. simpl.
  now rewrite firstn_nil.
  rewrite IHx. now rewrite app_comm_cons.
Qed.


Lemma rev_map_spec {A B} (f : A -> B) (l : list A) : 
  rev_map f l = List.rev (map f l).
Proof.
  unfold rev_map.
  rewrite -(app_nil_r (List.rev (map f l))).
  generalize (@nil B).
  induction l; simpl; auto. intros l0.
  rewrite IHl. now rewrite -app_assoc.
Qed.

Lemma skipn_0 {A} (l : list A) : skipn 0 l = l.
Proof. reflexivity. Qed.

Lemma skipn_n_Sn {A} n s (x : A) xs : skipn n s = x :: xs -> skipn (S n) s = xs.
Proof.
  induction n in s, x, xs |- *.
  - unfold skipn. now intros ->.
  - destruct s; simpl. intros H; discriminate. apply IHn.
Qed. 

Lemma skipn_all {A} (l : list A) : skipn #|l| l = [].
Proof.
  induction l; simpl; auto.
Qed.

Lemma skipn_app_le {A} n (l l' : list A) : n <= #|l| -> skipn n (l ++ l') = skipn n l ++ l'.
Proof.
  induction l in n, l' |- *; simpl; auto.
  intros Hn. destruct n; try lia. reflexivity.
  intros Hn. destruct n. reflexivity.
  rewrite !skipn_S. apply IHl. lia.
Qed.

Lemma firstn_ge {A} (l : list A) n : #|l| <= n -> firstn n l = l.
Proof.
  induction l in n |- *; simpl; intros; auto. now rewrite firstn_nil.
  destruct n; simpl. lia. rewrite IHl; auto. lia.
Qed.

Lemma firstn_0 {A} (l : list A) n : n = 0 -> firstn n l = [].
Proof.
  intros ->. reflexivity.
Qed.


Arguments firstn : simpl nomatch.
Arguments skipn : simpl nomatch.


Lemma skipn_firstn_skipn {A} (l : list A) n : skipn n (firstn (S n) l) ++ skipn (S n) l = skipn n l.
Proof.
  induction l in n |- *; simpl; auto. now rewrite app_nil_r.
  destruct n=> /=; auto.
Qed.

Lemma firstn_firstn_firstn {A} (l : list A) n : firstn n (firstn (S n) l) = firstn n l.
Proof.
  induction l in n |- *; simpl; auto.
  destruct n=> /=; auto. now rewrite IHl.
Qed.

Lemma decompose_app_rec_inv' f l hd args :
  decompose_app_rec f l = (hd, args) ->
  ∑ n, ~~ isApp hd /\ l = skipn n args /\ f = mkApps hd (firstn n args).
Proof.
  destruct (isApp f) eqn:Heq.
  revert l args hd.
  induction f; try discriminate. intros.
  simpl in H.
  destruct (isApp f1) eqn:Hf1.
  2:{ rewrite decompose_app_rec_eq in H => //. now apply negbT.
      revert Hf1.
      inv H. exists 1. simpl. intuition auto. now eapply negbT. }
  destruct (IHf1 eq_refl _ _ _ H).
  clear IHf1.
  exists (S x); intuition auto. eapply (f_equal (skipn 1)) in H2.
  rewrite [l]H2. now rewrite skipn_skipn Nat.add_1_r.
  rewrite -Nat.add_1_r firstn_add H3 -H2.
  now rewrite [tApp _ _](mkApps_nested hd _ [f2]).
  rewrite decompose_app_rec_eq; auto. now apply negbT.
  move=> [] H ->. subst f. exists 0. intuition auto.
  now apply negbT.
Qed.

Lemma mkApps_elim_rec t l l' :
  let app' := decompose_app_rec (mkApps t l) l' in
  mkApps_spec app'.1 app'.2 t (l ++ l') (mkApps t (l ++ l')).
Proof.
  destruct app' as [hd args] eqn:Heq.
  subst app'.
  rewrite decompose_app_rec_mkApps in Heq.
  have H := decompose_app_rec_inv' _ _ _ _ Heq.
  destruct H. simpl. destruct a as [isapp [Hl' Hl]].
  subst t.
  have H' := mkApps_intro hd args x. rewrite Hl'.
  rewrite mkApps_nested. now rewrite firstn_skipn.
Qed.

Lemma mkApps_elim t l  :
  let app' := decompose_app (mkApps t l) in
  mkApps_spec app'.1 app'.2 t l (mkApps t l).
Proof.
  have H := @mkApps_elim_rec t l [].
  now rewrite app_nil_r in H.
Qed.

Lemma nisApp_mkApps {t l} : ~~ isApp (mkApps t l) -> ~~ isApp t /\ l = [].
Proof.
  induction l in t |- *; simpl; auto.
  intros. destruct (IHl _ H). discriminate.
Qed.

Lemma mkApps_nisApp {t t' l} : mkApps t l = t' -> ~~ isApp t' -> t = t' /\ l = [].
Proof.
  induction l in t |- *; simpl; auto.
  intros. destruct (IHl _ H). auto. subst. simpl in H0. discriminate.
Qed.

Definition application_atom t :=
  match t with
  | tVar _
  | tSort _
  | tInd _ _
  | tConstruct _ _ _
  | tLambda _ _ _ => true
  | _ => false
  end.

Lemma application_atom_mkApps {t l} : application_atom (mkApps t l) -> application_atom t /\ l = [].
Proof.
  induction l in t |- *; simpl; auto.
  intros. destruct (IHl _ H). discriminate.
Qed.

Ltac solve_discr :=
  (try (progress (prepare_discr; finish_discr; cbn [mkApps] in * )));
  (try (match goal with
        | [ H : is_true (application_atom _) |- _ ] => discriminate
        | [ H : is_true (application_atom (mkApps _ _)) |- _ ] =>
          destruct (application_atom_mkApps H); subst; try discriminate
        end)).

(** Use a coercion for this common projection of the global context. *)
Definition fst_ctx : global_env_ext -> global_env := fst.
Coercion fst_ctx : global_env_ext >-> global_env.

Definition empty_ext (Σ : global_env) : global_env_ext
  := (Σ, Monomorphic_ctx ContextSet.empty).


Definition isSort T :=
  match T with
  | tSort u => True
  | _ => False
  end.

Fixpoint isArity T :=
  match T with
  | tSort u => True
  | tProd _ _ codom => isArity codom
  | tLetIn _ _ _ codom => isArity codom
  | _ => False
  end.
