(* Distributed under the terms of the MIT license.   *)
Set Warnings "-notation-overridden".

From Coq Require Import Arith Bool List Lia CRelationClasses.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst
     PCUICUnivSubst PCUICTyping PCUICReduction PCUICClosed PCUICCSubst 
     PCUICSubstitution PCUICInversion PCUICSR.
Require Import String.
Local Open Scope string_scope.
Set Asymmetric Patterns.

Require Import ssreflect ssrbool.

From Equations Require Import Equations.

Local Ltac inv H := inversion H; subst.

Ltac solve_discr :=
  try progress (prepare_discr; finish_discr; cbn[mkApps] in * );
  try match goal with
    H : mkApps _ _ = mkApps ?f ?l |- _ =>
    eapply mkApps_eq_inj in H as [? ?]; [|easy|easy]; subst; try intuition congruence; try noconf H
  | H : ?t = mkApps ?f ?l |- _ =>
    change t with (mkApps t []) in H ;
    eapply mkApps_eq_inj in H as [? ?]; [|easy|easy]; subst; try intuition congruence; try noconf H
  | H : mkApps ?f ?l = ?t |- _ =>
    change t with (mkApps t []) in H ;
    eapply mkApps_eq_inj in H as [? ?]; [|easy|easy]; subst; try intuition congruence; try noconf H
  end.


(** * Weak-head call-by-value evaluation strategy.

  The [wcbveval] inductive relation specifies weak cbv evaluation.  It
  is shown to be a subrelation of the 1-step reduction relation from
  which conversion is defined. Hence two terms that reduce to the same
  wcbv head normal form are convertible.

  This reduction strategy is supposed to mimick at the Coq level the
  reduction strategy of ML programming languages. It is used to state
  the extraction conjecture that can be applied to Coq terms to produce
  (untyped) terms where all proofs are erased to a dummy value. *)

(** ** Big step version of weak cbv beta-zeta-iota-fix-delta reduction. *)

Definition atom t :=
  match t with
  | tInd _ _
  | tConstruct _ _ _
  | tFix _ _
  | tCoFix _ _
  | tLambda _ _ _
  | tSort _
  | tProd _ _ _ => true
  | _ => false
  end.

Definition isArityHead t :=
  match t with
  | tSort _
  | tProd _ _ _ => true
  | _ => false
  end.

Definition isEvar t :=
  match t with
  | tEvar _ _ => true
  | _ => false
  end.

Definition isFix t :=
  match t with
  | tFix _ _ => true
  | _ => false
  end.

Definition isFixApp t :=
  match fst (decompose_app t) with
  | tFix _ _ => true
  | _ => false
  end.

Definition isCoFix t :=
  match t with
  | tCoFix _ _ => true
  | _ => false
  end.

Definition isInd t :=
  match t with
  | tInd _ _ => true
  | _ => false
  end.

Definition isConstruct t :=
  match t with
  | tConstruct _ _ _ => true
  | _ => false
  end.

Definition isAssRel Γ x :=
  match x with
  | tRel i =>
    match option_map decl_body (nth_error Γ i) with
    | Some None => true
    | _ => false
    end
  | _ => false
  end.

Definition isAxiom Σ x :=
  match x with
  | tConst c u =>
    match lookup_env Σ c with
    | Some (ConstantDecl {| cst_body := None |}) => true
    | _ => false
    end
  | _ => false
  end.

Definition substl defs body : term :=
  fold_left (fun bod term => csubst term 0 bod)
    defs body.

Definition cunfold_fix (mfix : mfixpoint term) (idx : nat) :=
  match List.nth_error mfix idx with
  | Some d => Some (d.(rarg), substl (fix_subst mfix) d.(dbody))
  | None => None
  end.

Definition cunfold_cofix (mfix : mfixpoint term) (idx : nat) :=
  match List.nth_error mfix idx with
  | Some d =>
    Some (d.(rarg), substl (cofix_subst mfix) d.(dbody))
  | None => None
  end.

Definition isStuckFix t (args : list term) :=
  match t with
  | tFix mfix idx =>
    match cunfold_fix mfix idx with
    | Some (narg, fn) => #|args| <=? narg
    | None => false
    end
  | _ => false
  end.

Lemma atom_mkApps f l : atom (mkApps f l) -> (l = []) /\ atom f.
Proof.
  revert f; induction l using rev_ind. simpl. intuition auto.
  simpl. intros. now rewrite -mkApps_nested in H.
Qed.

Section Wcbv.
  Context (Σ : global_env).
  (* The local context is empty: we are only doing weak reductions *)

  Inductive eval : term -> term -> Type :=
  (** Reductions *)
  (** Beta *)
  | eval_beta f na t b a a' res :
      eval f (tLambda na t b) ->
      eval a a' ->
      eval (csubst a' 0 b) res ->
      eval (tApp f a) res

  (** Let *)
  | eval_zeta na b0 b0' t b1 res :
      eval b0 b0' ->
      eval (csubst b0' 0 b1) res ->
      eval (tLetIn na b0 t b1) res

  (**
  (** Local variables: defined or undefined *)
  | eval_rel_def i body res :
      option_map decl_body (nth_error Γ i) = Some (Some body) ->
      eval (lift0 (S i) body) res ->
      eval (tRel i) res

  | eval_rel_undef i :
      option_map decl_body (nth_error Γ i) = Some None ->
      eval (tRel i) (tRel i)
  *)

  (** Constant unfolding *)
  | eval_delta c decl body (isdecl : declared_constant Σ c decl) u res :
      decl.(cst_body) = Some body ->
      eval (subst_instance_constr u body) res ->
      eval (tConst c u) res

  (** Axiom *)
  | eval_axiom c decl (isdecl : declared_constant Σ c decl) u :
      decl.(cst_body) = None ->
      eval (tConst c u) (tConst c u)

  (** Case *)
  | eval_iota ind pars discr c u args p brs res :
      eval discr (mkApps (tConstruct ind c u) args) ->
      eval (iota_red pars c args brs) res ->
      eval (tCase (ind, pars) p discr brs) res

  (** Proj *)
  | eval_proj i pars arg discr args u a res :
      eval discr (mkApps (tConstruct i 0 u) args) ->
      nth_error args (pars + arg) = Some a ->
      eval a res ->
      eval (tProj (i, pars, arg) discr) res

  (** Fix unfolding, with guard *)
  | eval_fix f mfix idx argsv a av fn res :
      eval f (mkApps (tFix mfix idx) argsv) ->
      eval a av ->
      cunfold_fix mfix idx = Some (#|argsv|, fn) ->
      eval (tApp (mkApps fn argsv) av) res ->
      eval (tApp f a) res

  (** Fix stuck, with guard *)
  | eval_fix_value f mfix idx argsv a av narg fn :
      eval f (mkApps (tFix mfix idx) argsv) ->
      eval a av ->
      cunfold_fix mfix idx = Some (narg, fn) ->
      (#|argsv| < narg) ->
      eval (tApp f a) (tApp (mkApps (tFix mfix idx) argsv) av)

  (** CoFix-case unfolding *)
  | red_cofix_case ip mfix idx p args narg fn brs res :
      cunfold_cofix mfix idx = Some (narg, fn) ->
      eval (tCase ip p (mkApps fn args) brs) res ->
      eval (tCase ip p (mkApps (tCoFix mfix idx) args) brs) res

  (** CoFix-proj unfolding *)
  | red_cofix_proj p mfix idx args narg fn res :
      cunfold_cofix mfix idx = Some (narg, fn) ->
      eval (tProj p (mkApps fn args)) res ->
      eval (tProj p (mkApps (tCoFix mfix idx) args)) res

  (** Non redex-producing heads applied to values are values *)
  | eval_app_cong f f' a a' :
      eval f f' ->
      ~~ (isLambda f' || isFixApp f' || isArityHead f') ->
      eval a a' ->
      eval (tApp f a) (tApp f' a')

  (** Evars complicate reasoning due to the embedded substitution, we skip
      them for now *)
  (* | eval_evar n l l' : *)
  (*     Forall2 eval l l' -> *)
  (*     eval (tEvar n l) (tEvar n l') *)


  (** Atoms are values (includes abstractions, cofixpoints and constructors
      along with type constructors) *)
  | eval_atom t : atom t -> eval t t.

  (** Characterization of values for this reduction relation.
      Only constructors and cofixpoints can accumulate arguments.
      All other values are atoms and cannot have arguments:
      - box
      - abstractions
      - constant constructors
      - unapplied fixpoints and cofixpoints
   *)

  Definition value_head x :=
    isInd x || isConstruct x || isCoFix x || isAxiom Σ x.

  (* Lemma value_head_atom x : value_head x -> atom x. *)
  (* Proof. destruct x; auto. Qed. *)

  Inductive value : term -> Type :=
  | value_atom t : atom t -> value t
  (* | value_evar n l l' : Forall value l -> Forall value l' -> value (mkApps (tEvar n l) l') *)
  | value_app t l : value_head t -> All value l -> value (mkApps t l)
  | value_stuck_fix f args :
      All value args ->
      isStuckFix f args ->
      value (mkApps f args)
  .

  Lemma value_values_ind : forall P : term -> Type,
      (forall t, atom t -> P t) ->
      (* (forall n l l', Forall value l -> Forall P l -> Forall value l' -> Forall P l' -> *)
      (*                 P (mkApps (tEvar n l) l')) -> *)
      (forall t l, value_head t -> All value l -> All P l -> P (mkApps t l)) ->
      (forall f args,
          All value args ->
          All P args ->
          isStuckFix f args ->
          P (mkApps f args)) ->
      forall t : term, value t -> P t.
  Proof.
    intros P ???.
    fix value_values_ind 2. destruct 1.
    - apply X; auto.
    - eapply X0; auto.
      revert l a. fix aux 2. destruct 1. constructor; auto.
      constructor. now eapply value_values_ind. now apply aux.
    - eapply X1; eauto.
      clear i. revert args a. fix aux 2. destruct 1. constructor; auto.
      constructor. now eapply value_values_ind. now apply aux.
  Defined.

  Lemma value_head_nApp {t} : value_head t -> ~~ isApp t.
  Proof. destruct t; auto. Qed.
  Hint Resolve value_head_nApp : core.

  Lemma isStuckfix_nApp {t args} : isStuckFix t args -> ~~ isApp t.
  Proof. destruct t; auto. Qed.
  Hint Resolve isStuckfix_nApp : core.

  Lemma atom_nApp {t} : atom t -> ~~ isApp t.
  Proof. destruct t; auto. Qed.
  Hint Resolve atom_nApp : core.

  Lemma value_mkApps_inv t l :
    ~~ isApp t ->
    value (mkApps t l) ->
    ((l = []) * atom t) + (value_head t * All value l) + (isStuckFix t l * All value l).
  Proof.
    intros H H'. set (x := mkApps t l) in *. cut (x = mkApps t l); [|reflexivity].
    clearbody x. induction H' using value_values_ind; intro H1.
    - subst. now eapply atom_mkApps in H0.
    - move: (value_head_nApp H0) => Ht.
      apply mkApps_eq_inj in H1; intuition subst; auto.
    - move: (isStuckfix_nApp H0) => Hf.
      apply mkApps_eq_inj in H1; intuition subst; auto.
  Qed.

  (** The codomain of evaluation is only values: *)
  (*     It means no redex can remain at the head of an evaluated term. *)

  Lemma isFixApp_mkApps f args : ~~ isApp f -> isFixApp (mkApps f args) = isFixApp f.
  Proof.
    move=> Hf.
    rewrite /isFixApp !decompose_app_mkApps // /=.
    change f with (mkApps f []) at 2.
    rewrite !decompose_app_mkApps // /=.
  Qed.

  Lemma eval_to_value e e' : eval e e' -> value e'.
  Proof.
    induction 1; simpl; auto using value.
    - eapply (value_app (tConst c u) []).
      red in isdecl.
      rewrite /value_head /= isdecl.
      destruct decl as [? [b|] ?]; try discriminate.
      constructor. constructor.
    - change (tApp ?h ?a) with (mkApps h [a]).
      rewrite mkApps_nested.
      apply value_mkApps_inv in IHX1; [|easy].
      destruct IHX1 as [[(-> & _)|]|(stuck & vals)].
      + cbn in *.
        apply (value_stuck_fix _ [av]); [easy|].
        cbn.
        destruct (cunfold_fix mfix idx) as [(? & ?)|]; [|easy].
        noconf e. eapply Nat.leb_le. lia.
      + easy.
      + eapply value_stuck_fix; [now apply All_app_inv|].
        unfold isStuckFix in *.
        destruct (cunfold_fix mfix idx) as [(? & ?)|]; [|easy].
        noconf e. rewrite app_length /=.
        eapply Nat.leb_le; lia.
    - destruct (mkApps_elim f' [a']).
      eapply value_mkApps_inv in IHX1 => //.
      destruct IHX1; intuition subst.
      * rewrite a1.
        simpl. rewrite a1 in i. simpl in *.
        apply (value_app f0 [a']). destruct f0; simpl in * |- *; try congruence;
        constructor; auto. constructor. auto. constructor; auto.
      * rewrite [tApp _ _](mkApps_nested _ (firstn n l) [a']).
        constructor 2; auto. eapply All_app_inv; auto.
      * rewrite [tApp _ _](mkApps_nested _ (firstn n l) [a']).
        rewrite isFixApp_mkApps in i => //.
        destruct f0; simpl in *; try congruence.
        rewrite /isFixApp in i. simpl in i.
        rewrite orb_true_r orb_true_l in i. easy.
  Qed.

  Lemma value_head_spec t :
    implb (value_head t) (~~ (isLambda t || isFixApp t || isArityHead t)).
  Proof.
    destruct t; simpl; intuition auto; eapply implybT.
  Qed.

  Lemma eval_stuck_fix args argsv mfix idx :
    All2 eval args argsv ->
    isStuckFix (tFix mfix idx) argsv ->
    eval (mkApps (tFix mfix idx) args) (mkApps (tFix mfix idx) argsv).
  Proof.
    revert argsv.
    induction args as [|a args IH] using MCList.rev_ind;
      intros argsv all stuck.
    - apply All2_length in all.
      destruct argsv; [|easy].
      now apply eval_atom.
    - destruct argsv as [|? ? _] using MCList.rev_ind;
        [apply All2_length in all; rewrite app_length in all; now cbn in *|].
      apply All2_app_r in all as (all & ev_a).
      rewrite <- !mkApps_nested.
      cbn in *.
      destruct (cunfold_fix mfix idx) as [(? & ?)|] eqn:cuf; [|easy].
      eapply eval_fix_value.
      + apply IH; [easy|].
        destruct (cunfold_fix mfix idx) as [(? & ?)|]; [|easy].
        rewrite app_length /= in stuck.
        eapply Nat.leb_le in stuck. eapply Nat.leb_le. lia.
      + easy.
      + easy.
      + rewrite app_length /= in stuck.
        eapply Nat.leb_le in stuck; lia.
  Qed.

  Lemma stuck_fix_value_inv argsv mfix idx narg fn :
    value (mkApps (tFix mfix idx) argsv) -> 
    cunfold_fix mfix idx = Some (narg, fn) ->
    (All value argsv * isStuckFix (tFix mfix idx) argsv).
  Proof.
    remember (mkApps (tFix mfix idx) argsv) as tfix.
    intros hv; revert Heqtfix.
    induction hv using value_values_ind; intros eq; subst.
    unfold atom in H. destruct argsv using rev_case => //.
    split; auto. simpl. simpl in H. rewrite H0 //.
    rewrite -mkApps_nested /= in H. depelim H.
    solve_discr => //.
    solve_discr.
  Qed.
    
  Lemma stuck_fix_value_args argsv mfix idx narg fn :
    value (mkApps (tFix mfix idx) argsv) ->
    cunfold_fix mfix idx = Some (narg, fn) ->
    #|argsv| <= narg.
  Proof.
    intros val unf.
    eapply stuck_fix_value_inv in val; eauto.
    destruct val.
    simpl in i. rewrite unf in i.
    now eapply Nat.leb_le in i.
  Qed.

  Derive Signature for eval.

  Lemma value_final e : value e -> eval e e.
  Proof.
    induction 1 using value_values_ind; simpl; auto using value.
    - now constructor.
    - apply All_All2_refl in X0 as X1.
      move/implyP: (value_head_spec t).
      move/(_ H) => Ht.
      induction l using rev_ind. simpl.
      destruct t; try discriminate.
      (* * constructor.
        unfold value_head in H. simpl in H. destruct option_map as [[o|]|] => //. *)
      * unfold value_head in H. simpl in H.
        destruct lookup_env eqn:Heq => //.
        destruct g eqn:Heq' => //.
        destruct c as [? [b|] ?] eqn:Heq'' => //. subst.
        eapply eval_axiom. red.
        rewrite Heq. reflexivity.
        easy.
      * now eapply eval_atom.
      * now eapply eval_atom.
      * now eapply eval_atom.
      * rewrite -mkApps_nested.
        eapply All_app in X as [Hl Hx]. depelim Hx.
        eapply All_app in X0 as [Hl' Hx']. depelim Hx'.
        eapply All2_app_inv_r in X1 as [Hl'' [Hx'' [? [? ?]]]]. depelim a0. depelim a0.
        eapply eval_app_cong; auto.
        eapply IHl; auto.
        now eapply All_All2.
        (* move/andP: H => [Ht Ht']. *)
        destruct l using rev_ind; auto.
        eapply value_head_nApp in H.
        rewrite isFixApp_mkApps => //.
        rewrite -mkApps_nested; simpl.
        rewrite orb_false_r.
        destruct t; auto.
    - destruct f; try discriminate.
      apply All_All2_refl in X0.
      now apply eval_stuck_fix.
  Qed.

  Lemma closed_beta na t b u : closed (tLambda na t b) -> closed u -> closed (csubst u 0 b).
  Proof. simpl; move/andP => [ct cb] cu. now eapply closed_csubst. Qed.

  Lemma closed_def `{checker_flags} c decl u b : wf Σ -> declared_constant Σ c decl -> 
    cst_body decl = Some b ->
    closed (subst_instance_constr u b).
  Proof.
    move=> wfΣ Hc Hb.
    rewrite PCUICClosed.closedn_subst_instance_constr.
    apply declared_decl_closed in Hc => //. simpl in Hc. red in Hc.
    rewrite Hb in Hc. simpl in Hc. now move/andP: Hc.
  Qed.
  Lemma closed_iota ind pars c u args brs : forallb (test_snd (closedn 0)) brs ->
    closed (mkApps (tConstruct ind c u) args) ->
    closed (iota_red pars c args brs).
  Proof.
    unfold iota_red => cbrs cargs.
    eapply closedn_mkApps. solve_all.
    rewrite nth_nth_error.
    destruct (nth_error_spec brs c) as [br e|e].
    eapply All_nth_error in e; eauto. simpl in e. apply e.
    auto.
    eapply closedn_mkApps_inv in cargs.
    move/andP: cargs => [Hcons Hargs]. now rewrite forallb_skipn.
  Qed.

  Lemma closed_arg f args n a :  
    closed (mkApps f args) ->
    nth_error args n = Some a -> closed a.
  Proof.
    move/closedn_mkApps_inv/andP => [cf cargs].
    solve_all. eapply All_nth_error in cargs; eauto.
  Qed.


  Lemma closed_unfold_fix mfix idx narg fn : 
    closed (tFix mfix idx) ->
    unfold_fix mfix idx = Some (narg, fn) -> closed fn.
  Proof.
    unfold unfold_fix. destruct (nth_error mfix idx) eqn:Heq.
    move=> /= Hf Heq'; noconf Heq'.
    eapply closedn_subst0. unfold fix_subst. clear -Hf. generalize #|mfix|.
    induction n; simpl; auto. apply/andP; split; auto.
    simpl. rewrite fix_subst_length. solve_all.
    eapply All_nth_error in Hf; eauto. unfold test_def in Hf.
    rewrite PeanoNat.Nat.add_0_r in Hf. now move/andP: Hf.
    discriminate.
  Qed.

  Lemma closed_fix_substl_subst_eq {mfix idx d} : 
    closed (tFix mfix idx) ->
    nth_error mfix idx = Some d ->
    subst0 (fix_subst mfix) (dbody d) = substl (fix_subst mfix) (dbody d).
  Proof.  
    move=> /= Hf; f_equal; f_equal.
    have clfix : All (closedn 0) (fix_subst mfix).
    { clear idx.
      solve_all.
      unfold fix_subst.
      move: #|mfix| => n.
      induction n. constructor.
      constructor; auto.
      simpl. solve_all. }
    move: (fix_subst mfix) (dbody d) clfix.
    clear; induction fix_subst => Hfix /= //.
    now rewrite subst_empty.
    move=> Ha; depelim Ha.
    simpl in *.
    intros hnth.
    rewrite -IHfix_subst => //.
    rewrite (subst_app_decomp [_]). simpl.
    f_equal. rewrite lift_closed // closed_subst //.
  Qed.

  Lemma closed_unfold_fix_cunfold_eq mfix idx : 
    closed (tFix mfix idx) ->
    unfold_fix mfix idx = cunfold_fix mfix idx.
  Proof.
    unfold unfold_fix, cunfold_fix.
    destruct (nth_error mfix idx) eqn:Heq => //.
    intros cl; f_equal; f_equal.
    now rewrite (closed_fix_substl_subst_eq cl).
  Qed.
  
  Lemma closed_unfold_cofix_cunfold_eq mfix idx : 
    closed (tCoFix mfix idx) ->
    unfold_cofix mfix idx = cunfold_cofix mfix idx.
  Proof.  
    unfold unfold_cofix, cunfold_cofix.
    destruct (nth_error mfix idx) eqn:Heq => //.
    move=> /= Hf; f_equal; f_equal.
    have clfix : All (closedn 0) (cofix_subst mfix).
    { clear Heq d idx.
      solve_all.
      unfold cofix_subst.
      move: #|mfix| => n.
      induction n. constructor.
      constructor; auto.
      simpl. solve_all. }
    move: (cofix_subst mfix) (dbody d) clfix.
    clear; induction cofix_subst => Hfix /= //.
    now rewrite subst_empty.
    move=> Ha; dependent elimination Ha as [All_cons ca cf].
    simpl in *.
    rewrite -IHcofix_subst => //.
    rewrite (subst_app_decomp [wildcard]). simpl.
    f_equal. rewrite lift_closed // closed_subst //.
  Qed.

  Lemma closed_unfold_cofix mfix idx narg fn : 
    closed (tCoFix mfix idx) ->
    unfold_cofix mfix idx = Some (narg, fn) -> closed fn.
  Proof.
    unfold unfold_cofix. destruct (nth_error mfix idx) eqn:Heq.
    move=> /= Hf Heq'; noconf Heq'.
    eapply closedn_subst0. unfold cofix_subst. clear -Hf. generalize #|mfix|.
    induction n; simpl; auto. apply/andP; split; auto.
    simpl. rewrite cofix_subst_length. solve_all.
    eapply All_nth_error in Hf; eauto. unfold test_def in Hf.
    rewrite PeanoNat.Nat.add_0_r in Hf. now move/andP: Hf.
    discriminate.
  Qed.

  (** Evaluation preserves closedness: *)
  Lemma eval_closed `{checker_flags} {wfΣ : wf Σ} : forall t u, closed t -> eval t u -> closed u.
  Proof.
    move=> t u Hc ev. move: Hc.
    induction ev; simpl in *; auto;
      (move/andP=> [/andP[Hc Hc'] Hc''] || move/andP=> [Hc Hc'] || move=>Hc); auto.
    - eapply IHev3. unshelve eapply closed_beta. 3:eauto. exact na. simpl. eauto.
    - eapply IHev2. now rewrite closed_csubst.
    - apply IHev. eapply closed_def; eauto.
    - eapply IHev2. eapply closed_iota in Hc''. eauto. eauto.
    - eapply IHev2; auto. specialize (IHev1 Hc).
      eapply closedn_mkApps_inv in IHev1.
      move/andP: IHev1 => [Hcons Hargs]. solve_all.
      eapply All_nth_error in Hargs; eauto.
    - eapply IHev3.
      apply Bool.andb_true_iff.
      split; [|easy].
      specialize (IHev1 Hc).
      eapply closedn_mkApps_inv in IHev1.
      apply Bool.andb_true_iff in IHev1.
      eapply closedn_mkApps; [|easy].
      eapply closed_unfold_fix; [easy|].
      now rewrite closed_unfold_fix_cunfold_eq.
    - apply Bool.andb_true_iff.
      split; [|easy].
      solve_all.
    - eapply IHev. move/closedn_mkApps_inv/andP: Hc' => [Hfix Hargs].
      repeat (apply/andP; split; auto). eapply closedn_mkApps.
      rewrite -closed_unfold_cofix_cunfold_eq in e => //.
      eapply closed_unfold_cofix in e; eauto.
      auto.
    - eapply IHev. move/closedn_mkApps_inv/andP: Hc => [Hfix Hargs].
      eapply closedn_mkApps; eauto.
      rewrite -closed_unfold_cofix_cunfold_eq in e => //.
      eapply closed_unfold_cofix in e; eauto.
    - apply/andP; split; auto.
    Qed.

  (* Lemma eval_tApp_tFix_inv mfix idx a v : *)
  (*   eval (tApp (tFix mfix idx) a) v -> *)
  (*   (exists fn arg, *)
  (*       (unfold_fix mfix idx = Some (arg, fn)) * *)
  (*       (eval (tApp fn a) v)). *)
  (* Proof. *)
  (*   intros H; depind H; try solve_discr. *)
  (*   - depelim H. *)
  (*   - depelim H. *)
  (*   - eexists _, _; firstorder eauto. *)
  (*   - now depelim H. *)
  (*   - discriminate. *)
  (* Qed. *)

  (* TODO MOVE *)
  Lemma nApp_isApp_false :
    forall u,
      nApp u = 0 ->
      isApp u = false.
  Proof.
    intros u e.
    destruct u. all: simpl. all: try reflexivity.
    discriminate.
  Qed.

  Lemma eval_tRel n t :
    eval (tRel n) t -> False.
  Proof. now intros e; depelim e. Qed.

  Lemma eval_tVar i t : eval (tVar i) t -> False.
  Proof. now intros e; depelim e. Qed.

  Lemma eval_tEvar n l t : eval (tEvar n l) t -> False.
  Proof. now intros e; depelim e. Qed.

  Lemma eval_mkApps_tCoFix mfix idx args v :
    eval (mkApps (tCoFix mfix idx) args)  v ->
    exists args', v = mkApps (tCoFix mfix idx) args'.
  Proof.
    revert v.
    induction args using List.rev_ind; intros v ev.
    + exists [].
      now depelim ev.
    + rewrite <- mkApps_nested in ev.
      cbn in *.
      depelim ev;
        try solve [apply IHargs in ev1 as (? & ?); solve_discr].
      * apply IHargs in ev1 as (argsv & ->).
        exists (argsv ++ [a'])%list.
        now rewrite <- mkApps_nested.
      * easy.
  Qed.
  
  Derive NoConfusion for term.
  (*
  Inductive elim_mkApps_tConstruct_type
    : inductive -> nat -> Instance.t -> list term -> term -> Type :=
  | elim_mkApps_tConstruct_c i c u args :
      elim_mkApps_tConstruct_type i c u args (mkApps (tConstruct i c u) args).

  Lemma elim_mkApps_tConstruct i c u args :
    elim_mkApps_tConstruct_type (
  Print Instances NoConfusionPackage.
*)
  Unset SsrRewrite.
  
  Axiom uip : forall {A} {a a' : A} (e e' : a = a'), e = e'.
  
  Set Equations Debug.
  Lemma eval_unique' {t v v'} :
    forall (ev1 : eval t v) (ev2 : eval t v'),
      sigmaI (eval t) v ev1 = sigmaI (eval t) v' ev2.
  Proof.
    Local Ltac go :=
      solve [
          repeat
            match goal with
            | [H: _, H' : _ |- _] =>
              specialize (H _ H');
              try solve [apply (f_equal pr1) in H; cbn in *; solve_discr];
              noconf H
            end; easy].
    intros ev.
    revert v'.
    depind ev; intros v' ev'.
    - depelim ev'; go.
    - depelim ev'; go.
    - depelim ev'; try go.
      pose proof (PCUICWeakeningEnv.declared_constant_inj _ _ isdecl isdecl0) as <-.
      assert (body0 = body) as -> by congruence.
      specialize (IHev _ ev'); noconf IHev.
      f_equal.
      f_equal; apply uip.
    - depelim ev'; try go.
      pose proof (PCUICWeakeningEnv.declared_constant_inj _ _ isdecl isdecl0) as <-.
      f_equal.
      f_equal; apply uip.
    - depelim ev'; try go.
      + specialize (IHev1 _ ev'1); noconf IHev1.
        apply (f_equal pr1) in IHev1 as apps_eq; cbn in *.
        apply mkApps_eq_inj in apps_eq as (eq1 & eq2); try easy.
        noconf eq1.
        noconf eq2.
        specialize (IHev2 _ ev'2); noconf IHev2.
        f_equal.
        f_equal.
        change (pr2 {| pr1 := mkApps (tConstruct ind c u) args; pr2 := ev1 |} =
                pr2 {| pr1 := mkApps (tConstruct ind c u) args; pr2 := ev'1 |}).
        rewrite IHev1.
        destruct (mkApps (tConstruct ind c u) args).
        all: noconf IHev1.
        all: now repeat match goal with
                    | [H: _ = _ |- _] => assert (H = eq_refl) as -> by now apply uip
                    end.
      + 

        change (pr2 {| pr1 := mkApps (tConstruct ind c u) args; pr2 := ev1 |} =
                pr2 {| pr1 := mkApps (tConstruct ind c u) args; pr2 := ev'1 |}).
        destruct args using List.rev_ind.
        * cbn in *.
          noconf IHev1; subst.
          assert (e' = eq_refl) as -> by now apply uip.
          assert (e'0 = eq_refl) as -> by now apply uip.
          now assert (e = eq_refl) as -> by now apply uip.
        * rewrite <- (mkApps_nested (tConstruct ind c u) args [x]).
          cbn.
          cbn.
          replace e' with (eq_refl by now apply uip.
          cbn 
        depelim IHev1.
        Set Printing All.
        destruct (mkApps (tConstruct ind c u)); noconf IHev1.
        apply (f_equal_dep pr2) in IHev1.
        subst.
        noconf eq1.
        Set Printing All.
        revert ev1 ev'1 IHev1.
        rewrite <- (proj1 apps_eq).
        depelim ev'1.
        noconf H.
        noconf H0.
        specialize (IHev2 _ ev'2); noconf IHev2.
        now apply IHev2 in ev'2.
      + apply eval_mkApps_tCoFix in ev1 as (? & ?); solve_discr.
      + easy.
    - depelim ev'.
      + apply IHev1 in ev'1.
        apply mkApps_eq_inj in ev'1 as (ev'1 & <-); try easy.
        noconf ev'1.
        replace a0 with a in * by congruence.
        now apply IHev2 in ev'2.
      + apply eval_mkApps_tCoFix in ev1 as (? & ?); solve_discr.
      + easy.
    - depelim ev'.
      + apply IHev1 in ev'1; solve_discr.
      + apply IHev1 in ev'1.
        solve_discr.
        rewrite e0 in e. noconf e.
        apply IHev2 in ev'2. subst.
        now apply IHev3 in ev'3.
      + apply IHev1 in ev'1; solve_discr.
        apply IHev2 in ev'2; subst.
        rewrite e0 in e. noconf e. lia.
      + apply IHev1 in ev'1.
        subst f'.
        rewrite isFixApp_mkApps in i by easy.
        cbn in *.
        now rewrite Bool.orb_true_r in i.
      + easy.
    - depelim ev'.
      + apply IHev1 in ev'1; solve_discr.
      + apply IHev1 in ev'1; solve_discr.
        apply IHev2 in ev'2; subst.
        rewrite e0 in e; noconf e. lia.
      + apply IHev1 in ev'1; solve_discr.
        now apply IHev2 in ev'2; subst.
      + apply IHev1 in ev'1; subst.
        rewrite isFixApp_mkApps in i by easy.
        cbn in *.
        now rewrite Bool.orb_true_r in i.
      + easy.
    - depelim ev'.
      + apply eval_mkApps_tCoFix in ev'1 as (? & ?); solve_discr.
      + solve_discr.
        rewrite e0 in e.
        noconf e.
        now apply IHev in ev'.
      + easy.
    - depelim ev'.
      + apply eval_mkApps_tCoFix in ev'1 as (? & ?); solve_discr.
      + solve_discr.
        rewrite e0 in e.
        noconf e.
        now apply IHev in ev'.
      + easy.
    - depelim ev'.
      + now apply IHev1 in ev'1; subst.
      + apply IHev1 in ev'1; subst.
        rewrite isFixApp_mkApps in i by easy.
        cbn in *.
        now rewrite Bool.orb_true_r in i.
      + apply IHev1 in ev'1; subst.
        rewrite isFixApp_mkApps in i by easy.
        cbn in *.
        now rewrite Bool.orb_true_r in i.
      + apply IHev1 in ev'1; subst.
        now apply IHev2 in ev'2; subst.
      + easy.
    - now depelim ev'.
  Qed.

  Lemma eval_deterministic {t v v'} :
    eval t v ->
    eval t v' ->
    v = v'.
  Proof.
  intros ev.
  revert v'.
  depind ev; intros v' ev'.
  - depelim ev'.
    + apply IHev1 in ev'1.
      apply IHev2 in ev'2.
      subst.
      noconf ev'1.
      now apply IHev3 in ev'3.
    + apply IHev1 in ev'1; solve_discr.
    + apply IHev1 in ev'1; solve_discr.
    + apply IHev1 in ev'1; subst; easy.
    + easy.
  - depelim ev'.
    + apply IHev1 in ev'1.
      subst.
      now apply IHev2 in ev'2.
    + easy.
  - depelim ev'.
    + rewrite (PCUICWeakeningEnv.declared_constant_inj _ _ isdecl isdecl0) in *.
      replace body0 with body in * by congruence.
      now apply IHev in ev'.
    + now rewrite (PCUICWeakeningEnv.declared_constant_inj _ _ isdecl isdecl0) in *.
    + easy.
  - depelim ev'.
    + now rewrite (PCUICWeakeningEnv.declared_constant_inj _ _ isdecl isdecl0) in *.
    + easy.
    + easy.
  - depelim ev'.
    + apply IHev1 in ev'1.
      apply mkApps_eq_inj in ev'1; try easy.
      depelim ev'1.
      noconf H.
      noconf H0.
      now apply IHev2 in ev'2.
    + apply eval_mkApps_tCoFix in ev1 as (? & ?); solve_discr.
    + easy.
  - depelim ev'.
    + apply IHev1 in ev'1.
      apply mkApps_eq_inj in ev'1 as (ev'1 & <-); try easy.
      noconf ev'1.
      replace a0 with a in * by congruence.
      now apply IHev2 in ev'2.
    + apply eval_mkApps_tCoFix in ev1 as (? & ?); solve_discr.
    + easy.
  - depelim ev'.
    + apply IHev1 in ev'1; solve_discr.
    + apply IHev1 in ev'1.
      solve_discr.
      rewrite e0 in e. noconf e.
      apply IHev2 in ev'2. subst.
      now apply IHev3 in ev'3.
    + apply IHev1 in ev'1; solve_discr.
      apply IHev2 in ev'2; subst.
      rewrite e0 in e. noconf e. lia.
    + apply IHev1 in ev'1.
      subst f'.
      rewrite isFixApp_mkApps in i by easy.
      cbn in *.
      now rewrite Bool.orb_true_r in i.
    + easy.
  - depelim ev'.
    + apply IHev1 in ev'1; solve_discr.
    + apply IHev1 in ev'1; solve_discr.
      apply IHev2 in ev'2; subst.
      rewrite e0 in e; noconf e. lia.
    + apply IHev1 in ev'1; solve_discr.
      now apply IHev2 in ev'2; subst.
    + apply IHev1 in ev'1; subst.
      rewrite isFixApp_mkApps in i by easy.
      cbn in *.
      now rewrite Bool.orb_true_r in i.
    + easy.
  - depelim ev'.
    + apply eval_mkApps_tCoFix in ev'1 as (? & ?); solve_discr.
    + solve_discr.
      rewrite e0 in e.
      noconf e.
      now apply IHev in ev'.
    + easy.
  - depelim ev'.
    + apply eval_mkApps_tCoFix in ev'1 as (? & ?); solve_discr.
    + solve_discr.
      rewrite e0 in e.
      noconf e.
      now apply IHev in ev'.
    + easy.
  - depelim ev'.
    + now apply IHev1 in ev'1; subst.
    + apply IHev1 in ev'1; subst.
      rewrite isFixApp_mkApps in i by easy.
      cbn in *.
      now rewrite Bool.orb_true_r in i.
    + apply IHev1 in ev'1; subst.
      rewrite isFixApp_mkApps in i by easy.
      cbn in *.
      now rewrite Bool.orb_true_r in i.
    + apply IHev1 in ev'1; subst.
      now apply IHev2 in ev'2; subst.
    + easy.
  - now depelim ev'.
  Qed.
  
  Lemma eval_unique {t v} :
    forall (ev1 ev2 : eval t v),
      ev1 = ev2.
  Proof.
    intros ev1.
    induction ev1; intros ev2.
    - admit.
    - admit.
    - admit.
    - admit.
    - depelim ev2.
      + pose proof (eval_deterministic ev1_1 ev2_1).
        eapply mkApps_eq_inj in H as (eq1 & eq2); try easy.
        subst.
        revert ev2_1.
        rewrite <- eq1.
        rewrite <- eq1 in ev2_1.
        rewrite <- H in ev2_1.
        specialize (IHev1_1 ev2_1).
  Set SsrRewrite.

  Lemma eval_LetIn {n b ty t v} :
    eval (tLetIn n b ty t) v ->
    ∑ b',
      eval b b' * eval (csubst b' 0 t) v.
  Proof. now intros H; depelim H. Qed.

  Lemma eval_Const {c u v} :
    eval (tConst c u) v ->
    ∑ decl, declared_constant Σ c decl *
                 match cst_body decl with
                 | Some body => eval (subst_instance_constr u body) v
                 | None => v = tConst c u
                 end.
  Proof.
    intros H; depelim H.
    - exists decl.
      split; [easy|].
      now rewrite e.
    - exists decl.
      split; [easy|].
      now rewrite e.
    - easy.
  Qed.

  Lemma eval_mkApps_cong f f' l l' :
    eval f f' ->
    value_head f' ->
    All2 eval l l' ->
    eval (mkApps f l) (mkApps f' l').
  Proof.
    revert l'. induction l using rev_ind; intros l' evf vf' evl.
    depelim evl. eapply evf.
    eapply All2_app_inv in evl as [[? ?] [? ?]].
    intuition auto. subst. depelim a. depelim a.
    rewrite - !mkApps_nested /=. eapply eval_app_cong; auto.
    rewrite isFixApp_mkApps. auto.
    destruct l0 using rev_ind; simpl; [|rewrite - !mkApps_nested]; simpl in *; destruct f';
      try discriminate; try constructor.
  Qed.
  Arguments removelast : simpl nomatch.
  Lemma removelast_length {A} (l : list A) : 0 < #|l| -> #|removelast l| < #|l|.
  Proof.
    induction l; cbn -[removelast]; auto. intros.
    destruct l. auto.
    forward IHl. simpl; lia. cbn -[removelast] in *. simpl removelast. simpl. lia.
  Qed.

End Wcbv.

Arguments eval_deterministic {_ _ _ _}.

(** Well-typed closed programs can't go wrong: they always evaluate to a value. *)

Conjecture closed_typed_wcbeval : forall {cf : checker_flags} (Σ : global_env_ext) t T,
    Σ ;;; [] |- t : T -> ∑ u, eval (fst Σ) t u.
