(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config monad_utils utils uGraph.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICNormal PCUICSR
     PCUICGeneration PCUICReflect PCUICEquality PCUICInversion PCUICValidity
     PCUICWeakening PCUICPosition PCUICCumulativity PCUICInductives PCUICSafeLemmata PCUICSN
     PCUICPretty PCUICArities PCUICConfluence PCUICConversion PCUICWfUniverses.
From MetaCoq.Bidirectional Require BDMinimalTyping BDMinimalToPCUIC.
From MetaCoq.SafeChecker Require Import PCUICSafeReduce PCUICSafeConversion.

From Equations Require Import Equations.
Require Import ssreflect.

Import MonadNotation.

Local Set Keyed Unification.
Set Equations Transparent.

Lemma weakening_sq `{cf : checker_flags} {Σ Γ} Γ' {t T} :
  ∥ wf Σ.1 ∥ -> ∥ wf_local Σ (Γ ,,, Γ') ∥ ->
  ∥ Σ ;;; Γ |- t : T ∥ ->
  ∥ Σ ;;; Γ ,,, Γ' |- lift0 #|Γ'| t : lift0 #|Γ'| T ∥.
Proof.
  intros; sq; now eapply weakening.
Defined.

Definition wf_local_rel_abs_sq `{cf : checker_flags} {Σ Γ Γ' A na} :
  ∥ wf_local_rel Σ Γ Γ' ∥ -> {u & ∥ Σ ;;; Γ ,,, Γ' |- A : tSort u ∥ }
  -> ∥ wf_local_rel Σ Γ (Γ',, vass na A) ∥.
Proof.
  intros H [u Hu]; sq. now eapply wf_local_rel_abs.
Qed.

Definition wf_local_rel_def_sq `{cf : checker_flags} {Σ Γ Γ' t A na} :
  ∥ wf_local_rel Σ Γ Γ' ∥ -> ∥ isType Σ (Γ ,,, Γ') A ∥ -> ∥ Σ ;;; Γ ,,, Γ' |- t : A ∥
  -> ∥ wf_local_rel Σ Γ (Γ',, vdef na t A) ∥.
Proof.
  intros; sq. now eapply wf_local_rel_def.
Qed.

Definition wf_local_rel_app_inv_sq `{cf : checker_flags} {Σ Γ1 Γ2 Γ3} :
  ∥ wf_local_rel Σ Γ1 Γ2 ∥ -> ∥ wf_local_rel Σ (Γ1 ,,, Γ2) Γ3 ∥
  -> ∥ wf_local_rel Σ Γ1 (Γ2 ,,, Γ3) ∥.
Proof.
  intros; sq; now eapply wf_local_rel_app_inv.
Qed.

Fixpoint monad_All {T} {M : Monad T} {A} {P} (f : forall x, T (P x)) l : T (@All A P l)
  := match l with
     | [] => ret All_nil
     | a :: l => X <- f a ;;
                Y <- monad_All f l ;;
                ret (All_cons X Y)
     end.

Fixpoint monad_All2 {T E} {M : Monad T} {M' : MonadExc E T} wrong_sizes
         {A B R} (f : forall x y, T (R x y)) l1 l2
  : T (@All2 A B R l1 l2)
  := match l1, l2 with
     | [], [] => ret All2_nil
     | a :: l1, b :: l2 => X <- f a b ;;
                          Y <- monad_All2 wrong_sizes f l1 l2 ;;
                          ret (All2_cons X Y)
     | _, _ => raise wrong_sizes
     end.


Definition monad_prod {T} {M : Monad T} {A B} (x : T A) (y : T B): T (A * B)
  := X <- x ;; Y <- y ;; ret (X, Y).

Definition check_dec {T E} {M : Monad T} {M' : MonadExc E T} (e : E) {P}
           (H : {P} + {~ P})
  : T P
  := match H with
     | left x => ret x
     | right _ => raise e
     end.

Definition check_eq_true {T E} {M : Monad T} {M' : MonadExc E T} b (e : E)
  : T (b = true)
  := if b return T (b = true) then ret eq_refl else raise e.

Program Definition check_eq_nat {T E} {M : Monad T} {M' : MonadExc E T} n m (e : E)
  : T (n = m)
  := match Nat.eq_dec n m with
     | left p => ret p
     | right p => raise e
     end.


Definition mkApps_decompose_app_rec t l :
  mkApps t l = mkApps  (fst (decompose_app_rec t l)) (snd (decompose_app_rec t l)).
Proof.
  revert l; induction t; try reflexivity.
  intro l; cbn in *.
  transitivity (mkApps t1 ((t2 ::l))). reflexivity.
  now rewrite IHt1.
Qed.

Definition mkApps_decompose_app t :
  t = mkApps  (fst (decompose_app t)) (snd (decompose_app t))
  := mkApps_decompose_app_rec t [].

Lemma isType_red {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ T U} :
  isType Σ Γ T -> red Σ Γ T U -> isType Σ Γ U.
Proof.
  intros [s Hs] red; exists s.
  eapply subject_reduction; eauto.
Qed.




Derive NoConfusion EqDec for sort_family.

Inductive type_error :=
| UnboundRel (n : nat)
| UnboundVar (id : string)
| UnboundEvar (ev : nat)
| UndeclaredConstant (c : kername)
| UndeclaredInductive (c : inductive)
| UndeclaredConstructor (c : inductive) (i : nat)
| NotCumulSmaller (G : universes_graph) (Γ : context) (t u t' u' : term) (e : ConversionError)
| NotConvertible (G : universes_graph) (Γ : context) (t u : term)
| NotASort (t : term)
| NotAProduct (t t' : term)
| NotAnArity (t : term)
| NotAnInductive (t : term)
| IllFormedFix (m : mfixpoint term) (i : nat)
| UnsatisfiedConstraints (c : ConstraintSet.t)
| Msg (s : string).

Definition print_level := string_of_level.

Definition string_of_Z z :=
  if (z <=? 0)%Z then "-" ^ string_of_nat (Z.to_nat (- z)) else string_of_nat (Z.to_nat z).

Definition print_edge '(l1, n, l2)
  := "(" ^ print_level l1 ^ ", " ^ string_of_Z n ^ ", "
         ^ print_level l2 ^ ")".

Definition print_universes_graph (G : universes_graph) :=
  let levels := wGraph.VSet.elements G.1.1 in
  let edges := wGraph.EdgeSet.elements G.1.2 in
  string_of_list print_level levels
  ^ "\n" ^ string_of_list print_edge edges.

Definition string_of_conv_pb (c : conv_pb) : string :=
  match c with
  | Conv => "conversion"
  | Cumul => "cumulativity"
  end.

Definition print_term Σ Γ t :=
  print_term Σ Γ true false t.

Fixpoint string_of_conv_error Σ (e : ConversionError) : string :=
  match e with
  | NotFoundConstants c1 c2 =>
      "Both constants " ^ string_of_kername c1 ^ " and " ^ string_of_kername c2 ^
      " are not found in the environment."
  | NotFoundConstant c =>
      "Constant " ^ string_of_kername c ^
      " common in both terms is not found in the environment."
  | LambdaNotConvertibleAnn Γ1 na A1 t1 Γ2 na' A2 t2 =>
      "When comparing\n" ^ print_term Σ Γ1 (tLambda na A1 t1) ^
      "\nand\n" ^ print_term Σ Γ2 (tLambda na' A2 t2) ^
      "\nbinding annotations are not convertible\n"
  | LambdaNotConvertibleTypes Γ1 na A1 t1 Γ2 na' A2 t2 e =>
      "When comparing\n" ^ print_term Σ Γ1 (tLambda na A1 t1) ^
      "\nand\n" ^ print_term Σ Γ2 (tLambda na' A2 t2) ^
      "\ntypes are not convertible:\n" ^
      string_of_conv_error Σ e
  | ProdNotConvertibleAnn Γ1 na A1 B1 Γ2 na' A2 B2 =>
      "When comparing\n" ^ print_term Σ Γ1 (tProd na A1 B1) ^
      "\nand\n" ^ print_term Σ Γ2 (tProd na' A2 B2) ^
      "\nbinding annotations are not convertible:\n"
  | ProdNotConvertibleDomains Γ1 na A1 B1 Γ2 na' A2 B2 e =>
      "When comparing\n" ^ print_term Σ Γ1 (tProd na A1 B1) ^
      "\nand\n" ^ print_term Σ Γ2 (tProd na' A2 B2) ^
      "\ndomains are not convertible:\n" ^
      string_of_conv_error Σ e
  | CaseOnDifferentInd Γ ind par p c brs Γ' ind' par' p' c' brs' =>
      "The two stuck pattern-matching\n" ^
      print_term Σ Γ (tCase (ind, par) p c brs) ^
      "\nand\n" ^ print_term Σ Γ' (tCase (ind', par') p' c' brs') ^
      "\nare done on distinct inductive types."
  | CaseBranchNumMismatch
      ind par Γ p c brs1 m br brs2 Γ' p' c' brs1' m' br' brs2' =>
      "The two stuck pattern-matching\n" ^
      print_term Σ Γ (tCase (ind, par) p c (brs1 ++ (m,br) :: brs2)) ^
      "\nand\n" ^
      print_term Σ Γ' (tCase (ind, par) p' c' (brs1' ++ (m',br') :: brs2')) ^
      "\nhave a mistmatch in the branch number " ^ string_of_nat #|brs1| ^
      "\nthe number of parameters do not coincide\n" ^
      print_term Σ Γ br ^
      "\nhas " ^ string_of_nat m ^ " parameters while\n" ^
      print_term Σ Γ br' ^
      "\nhas " ^ string_of_nat m' ^ "."
  | DistinctStuckProj Γ p c Γ' p' c' =>
      "The two stuck projections\n" ^
      print_term Σ Γ (tProj p c) ^
      "\nand\n" ^
      print_term Σ Γ' (tProj p' c') ^
      "\nare syntactically different."
  | CannotUnfoldFix Γ mfix idx Γ' mfix' idx' =>
      "The two fixed-points\n" ^
      print_term Σ Γ (tFix mfix idx) ^
      "\nand\n" ^ print_term Σ Γ' (tFix mfix' idx') ^
      "\ncorrespond to syntactically distinct terms that can't be unfolded."
  | FixRargMismatch idx Γ u mfix1 mfix2 Γ' v mfix1' mfix2' =>
      "The two fixed-points\n" ^
      print_term Σ Γ (tFix (mfix1 ++ u :: mfix2) idx) ^
      "\nand\n" ^ print_term Σ Γ' (tFix (mfix1' ++ v :: mfix2') idx) ^
      "\nhave a mismatch in the function number " ^ string_of_nat #|mfix1| ^
      ": arguments " ^ string_of_nat u.(rarg) ^
      " and " ^ string_of_nat v.(rarg) ^ "are different."
  | FixMfixMismatch idx Γ mfix Γ' mfix' =>
      "The two fixed-points\n" ^
      print_term Σ Γ (tFix mfix idx) ^
      "\nand\n" ^
      print_term Σ Γ' (tFix mfix' idx) ^
      "\nhave a different number of mutually defined functions."
  | DistinctCoFix Γ mfix idx Γ' mfix' idx' =>
      "The two cofixed-points\n" ^
      print_term Σ Γ (tCoFix mfix idx) ^
      "\nand\n" ^ print_term Σ Γ' (tCoFix mfix' idx') ^
      "\ncorrespond to syntactically distinct terms."
  | CoFixRargMismatch idx Γ u mfix1 mfix2 Γ' v mfix1' mfix2' =>
      "The two co-fixed-points\n" ^
      print_term Σ Γ (tCoFix (mfix1 ++ u :: mfix2) idx) ^
      "\nand\n" ^ print_term Σ Γ' (tCoFix (mfix1' ++ v :: mfix2') idx) ^
      "\nhave a mismatch in the function number " ^ string_of_nat #|mfix1| ^
      ": arguments " ^ string_of_nat u.(rarg) ^
      " and " ^ string_of_nat v.(rarg) ^ "are different."
  | CoFixMfixMismatch idx Γ mfix Γ' mfix' =>
      "The two co-fixed-points\n" ^
      print_term Σ Γ (tCoFix mfix idx) ^
      "\nand\n" ^
      print_term Σ Γ' (tCoFix mfix' idx) ^
      "\nhave a different number of mutually defined functions."
  | StackHeadError leq Γ1 t1 args1 u1 l1 Γ2 t2 u2 l2 e =>
      "TODO stackheaderror\n" ^
      string_of_conv_error Σ e
  | StackTailError leq Γ1 t1 args1 u1 l1 Γ2 t2 u2 l2 e =>
      "TODO stacktailerror\n" ^
      string_of_conv_error Σ e
  | StackMismatch Γ1 t1 args1 l1 Γ2 t2 l2 =>
      "Convertible terms\n" ^
      print_term Σ Γ1 t1 ^
      "\nand\n" ^ print_term Σ Γ2 t2 ^
      "are convertible/convertible (TODO) but applied to a different number" ^
      " of arguments."
  | HeadMismatch leq Γ1 t1 Γ2 t2 =>
      "Terms\n" ^
      print_term Σ Γ1 t1 ^
      "\nand\n" ^ print_term Σ Γ2 t2 ^
      "\ndo not have the same head when comparing for " ^
      string_of_conv_pb leq
  end.

Definition string_of_type_error Σ (e : type_error) : string :=
  match e with
  | UnboundRel n => "Unbound rel " ^ string_of_nat n
  | UnboundVar id => "Unbound var " ^ id
  | UnboundEvar ev => "Unbound evar " ^ string_of_nat ev
  | UndeclaredConstant c => "Undeclared constant " ^ string_of_kername c
  | UndeclaredInductive c => "Undeclared inductive " ^ string_of_kername (inductive_mind c)
  | UndeclaredConstructor c i => "Undeclared inductive " ^ string_of_kername (inductive_mind c)
  | NotCumulSmaller G Γ t u t' u' e => "Terms are not <= for cumulativity:\n" ^
      print_term Σ Γ t ^ "\nand:\n" ^ print_term Σ Γ u ^
      "\nafter reduction:\n" ^
      print_term Σ Γ t' ^ "\nand:\n" ^ print_term Σ Γ u' ^
      "\nerror:\n" ^ string_of_conv_error Σ e ^
      "\nin universe graph:\n" ^ print_universes_graph G
  | NotConvertible G Γ t u => "Terms are not convertible:\n" ^
      print_term Σ Γ t ^ "\nand:\n" ^ print_term Σ Γ u ^
      "\nin universe graph:\n" ^ print_universes_graph G
  | NotASort t => "Not a sort"
  | NotAProduct t t' => "Not a product"
  | NotAnArity t => "Not an arity"
  | NotAnInductive t => "Not an inductive"
  | IllFormedFix m i => "Ill-formed recursive definition"
  | UnsatisfiedConstraints c => "Unsatisfied constraints"
  | Msg s => "Msg: " ^ s
  end.

Inductive typing_result (A : Type) :=
| Checked (a : A)
| TypeError (t : type_error).
Global Arguments Checked {A} a.
Global Arguments TypeError {A} t.

Instance typing_monad : Monad typing_result :=
  {| ret A a := Checked a ;
     bind A B m f :=
       match m with
       | Checked a => f a
       | TypeError t => TypeError t
       end
  |}.

Instance monad_exc : MonadExc type_error typing_result :=
  { raise A e := TypeError e;
    catch A m f :=
      match m with
      | Checked a => m
      | TypeError t => f t
      end
  }.


Lemma wf_local_rel_inv `{checker_flags} {Σ Γ1 Γ2} (w : wf_local_rel Σ Γ1 Γ2) :
  forall d Γ2', Γ2 = Γ2' ,, d ->
  wf_local_rel Σ Γ1 Γ2' × (∑ u, Σ ;;; Γ1 ,,, Γ2' |- d.(decl_type) : tSort u) ×
               match d.(decl_body) with
               | Some b => Σ ;;; Γ1 ,,, Γ2' |- b : d.(decl_type)
               | None => True
               end.
Proof.
  intros d Γ.
  destruct w; inversion 1; subst; cbn in *.
  split; [assumption|]. split; [assumption| trivial].
  split; [assumption|]. split; [assumption| trivial].
Defined.

Definition wf_local_app_inv `{cf : checker_flags} {Σ Γ1 Γ2} :
  wf_local Σ Γ1 -> wf_local_rel Σ Γ1 Γ2
  -> wf_local Σ (Γ1 ,,, Γ2).
Proof.
  intros H1 H2.
  apply wf_local_local_rel, wf_local_rel_app_inv.
  now apply wf_local_rel_local.
  now rewrite app_context_nil_l.
Defined.

Definition fix_context_i i mfix :=
  List.rev (mapi_rec (fun i (d : BasicAst.def term)
                      => vass (dname d) ((lift0 i) (dtype d))) mfix i).

Lemma lift_fix_context mfix : forall k k' j, j <= k ->
    fix_context_i (k + k') mfix = lift_context k' j (fix_context_i k mfix).
Proof.
  induction mfix. reflexivity.
  intros k k' j Hj.
  change ([vass (dname a) ((lift0 (k + k')) (dtype a))] ,,, fix_context_i (S (k + k')) mfix = lift_context k' j ([vass (dname a) ((lift0 k) (dtype a))] ,,, fix_context_i (S k) mfix)).
  erewrite lift_context_app, (IHmfix (S k) k' (S j)); cbn.
  unfold map_decl, vass; cbn. now rewrite simpl_lift.
  now apply le_n_S.
Qed.

Lemma wf_ext_gc_of_uctx {cf:checker_flags} {Σ : global_env_ext} (HΣ : ∥ wf_ext Σ ∥)
  : ∑ uctx', gc_of_uctx (global_ext_uctx Σ) = Some uctx'.
Proof.
  pose proof (global_ext_uctx_consistent _ HΣ) as HC.
  destruct Σ as [Σ φ].
  simpl in HC.
  unfold gc_of_uctx; simpl in *.
  apply gc_consistent_iff in HC.
  destruct (gc_of_constraints (global_ext_constraints (Σ, φ))).
  eexists; reflexivity.
  contradiction HC.
Defined.

Lemma wf_ext_is_graph {cf:checker_flags} {Σ : global_env_ext} (HΣ : ∥ wf_ext Σ ∥)
  : ∑ G, is_graph_of_uctx G (global_ext_uctx Σ).
Proof.
  destruct (wf_ext_gc_of_uctx HΣ) as [uctx Huctx].
  exists (make_graph uctx). unfold is_graph_of_uctx. now rewrite Huctx.
Defined.

Lemma map_squash {A B} (f : A -> B) : ∥ A ∥ -> ∥ B ∥.
Proof.
  intros []; constructor; auto.
Qed.

Lemma destArity_mkApps_None ctx t l :
  destArity ctx t = None -> destArity ctx (mkApps t l) = None.
Proof.
  induction l in t |- *. trivial.
  intros H. cbn. apply IHl. reflexivity.
Qed.

Lemma destArity_mkApps_Ind ctx ind u l :
  destArity ctx (mkApps (tInd ind u) l) = None.
Proof.
    apply destArity_mkApps_None. reflexivity.
Qed.

Section Reduce.
  Context {cf : checker_flags} {Σ : global_env_ext} (HΣ : ∥ wf Σ ∥).

  (* We get stack overflow on Qed after Equations definitions when this is transparent *)
  Opaque reduce_stack_full.

  Definition hnf := reduce_term RedFlags.default Σ HΣ.

  Theorem hnf_sound {Γ t h} : ∥ red (fst Σ) Γ t (hnf Γ t h) ∥.
  Proof.
    apply reduce_term_sound.
  Defined.
  
  Theorem hnf_complete {Γ t h} : ∥whnf RedFlags.default Σ Γ (hnf Γ t h)∥.
  Proof.
    apply reduce_term_complete.
  Qed.

  Inductive view_sort : term -> Type :=
  | view_sort_sort s : view_sort (tSort s)
  | view_sort_other t : ~isSort t -> view_sort t.

  Equations view_sortc (t : term) : view_sort t :=
    view_sortc (tSort s) := view_sort_sort s;
    view_sortc t := view_sort_other t _.

  Equations? reduce_to_sort (Γ : context) (t : term) (h : welltyped Σ Γ t)
    : typing_result (∑ u, ∥ red (fst Σ) Γ t (tSort u) ∥) :=
    reduce_to_sort Γ t h with view_sortc t := {
      | view_sort_sort s => ret (s; sq (refl_red _ _ _));
      | view_sort_other t _ with inspect (hnf Γ t h) :=
        | exist hnft eq with view_sortc hnft := {
          | view_sort_sort s => ret (s; _);
          | view_sort_other t _ => raise (NotASort t)
        }
      }.
  Proof.
    pose proof (hnf_sound (h:=h)).
    now rewrite eq.
  Qed.

  Lemma reduce_to_sort_complete {Γ t wt} e :
    reduce_to_sort Γ t wt = TypeError e ->
    (forall s, red Σ Γ t (tSort s) -> False).
  Proof.
    funelim (reduce_to_sort Γ t wt); try congruence.
    intros _ s r.
    pose proof (@hnf_complete Γ t0 h) as [wh].
    pose proof (@hnf_sound Γ t0 h) as [r'].
    destruct HΣ.
    eapply red_confluence in r as (?&r1&r2); eauto.
    apply invert_red_sort in r2 as ->.
    eapply whnf_red_inv in r1; eauto.
    depelim r1.
    clear Heq.
    rewrite H in n0.
    now cbn in n0.
  Qed.

  Inductive view_prod : term -> Type :=
  | view_prod_prod na A B : view_prod (tProd na A B)
  | view_prod_other t : ~isProd t -> view_prod t.

  Equations view_prodc (t : term) : view_prod t :=
    view_prodc (tProd na A B) := view_prod_prod na A B;
    view_prodc t := view_prod_other t _.

  Equations? reduce_to_prod (Γ : context) (t : term) (h : welltyped Σ Γ t)
    : typing_result (∑ na A B, ∥ red (fst Σ) Γ t (tProd na A B) ∥) :=
    reduce_to_prod Γ t h with view_prodc t := {
      | view_prod_prod na A B => ret (na; A; B; sq (refl_red _ _ _));
      | view_prod_other t _ with inspect (hnf Γ t h) :=
        | exist hnft eq with view_prodc hnft := {
          | view_prod_prod na A B => ret (na; A; B; _);
          | view_prod_other t' _ => raise (NotAProduct t t')
        }
      }.
  Proof.
    pose proof (hnf_sound (h:=h)).
    now rewrite eq.
  Qed.

  Lemma reduce_to_prod_complete {Γ t wt} e :
    reduce_to_prod Γ t wt = TypeError e ->
    (forall na A B, red Σ Γ t (tProd na A B) -> False).
  Proof.
    funelim (reduce_to_prod Γ t wt); try congruence.
    intros _ na a b r.
    pose proof (@hnf_complete Γ t0 h) as [wh].
    pose proof (@hnf_sound Γ t0 h) as [r'].
    destruct HΣ.
    eapply red_confluence in r as (?&r1&r2); eauto.
    apply invert_red_prod in r2 as (?&?&(->&?)&?); auto.
    eapply whnf_red_inv in r1; auto.
    depelim r1.
    clear Heq.
    rewrite H in n0.
    now cbn in n0.
  Qed.

  Definition isInd (t : term) : bool :=
    match t with
    | tInd _ _ => true
    | _ => false
    end.

  Inductive view_ind : term -> Type :=
  | view_ind_tInd ind u : view_ind (tInd ind u)
  | view_ind_other t : negb (isInd t) -> view_ind t.

  Equations view_indc (t : term) : view_ind t :=
    view_indc (tInd ind u) => view_ind_tInd ind u;
    view_indc t => view_ind_other t _.

  Equations? reduce_to_ind (Γ : context) (t : term) (h : welltyped Σ Γ t)
    : typing_result (∑ i u l, ∥ red (fst Σ) Γ t (mkApps (tInd i u) l) ∥) :=
    reduce_to_ind Γ t h with inspect (decompose_app t) := {
      | exist (thd, args) eq_decomp with view_indc thd := {
        | view_ind_tInd i u => ret (i; u; args; sq _);
        | view_ind_other t _ with inspect (reduce_stack RedFlags.default Σ HΣ Γ t Empty h) := {
          | exist (hnft, π) eq with view_indc hnft := {
            | view_ind_tInd i u with inspect (decompose_stack π) := {
              | exist (l, _) eq_decomp => ret (i; u; l; _)
              };
            | view_ind_other _ _ => raise (NotAnInductive t)
            }
          }
        }
      }.
  Proof.
    - assert (X : mkApps (tInd i u) args = t); [|rewrite X; apply refl_red].
      etransitivity. 2: symmetry; eapply mkApps_decompose_app.
      now rewrite <- eq_decomp.
    - pose proof (reduce_stack_sound RedFlags.default Σ HΣ _ _ Empty h).
      rewrite <- eq in H.
      cbn in *.
      assert (π = appstack l ε) as ->.
      2: { now rewrite zipc_appstack in H. }
      unfold reduce_stack in eq.
      destruct reduce_stack_full as (?&_&stack_val&?).
      subst x.
      unfold Pr in stack_val.
      cbn in *.
      assert (decomp: decompose_stack π = ((decompose_stack π).1, ε)).
      { rewrite stack_val.
        now destruct decompose_stack. }
      apply decompose_stack_eq in decomp as ->.
      now rewrite <- eq_decomp0.
  Qed.

  Lemma reduce_to_ind_complete Γ ty wat e :
    reduce_to_ind Γ ty wat = TypeError e ->
    forall ind u args,
      red Σ Γ ty (mkApps (tInd ind u) args) ->
      False.
  Proof.
    funelim (reduce_to_ind Γ ty wat); try congruence.
    intros _ ind u args r.
    pose proof (reduce_stack_whnf RedFlags.default Σ HΣ Γ t ε h) as wh.
    unfold reduce_stack in *.
    destruct reduce_stack_full as ((hd&π)&r'&stack_valid&(notapp&_)).
    destruct wh as [wh].
    apply Req_red in r' as [r'].
    unfold Pr in stack_valid.
    cbn in *.
    destruct HΣ.
    eapply red_confluence in r as (?&r1&r2); [|eassumption|exact r'].
    assert (exists args, π = appstack args ε) as (?&->).
    { exists ((decompose_stack π).1).
      assert (decomp: decompose_stack π = ((decompose_stack π).1, ε)).
      { now rewrite stack_valid; destruct decompose_stack. }
      now apply decompose_stack_eq in decomp. }

    unfold zipp in wh.
    rewrite stack_context_appstack decompose_stack_appstack in wh.
    rewrite zipc_appstack in r1.
    cbn in *.
    rewrite app_nil_r in wh.
    apply red_mkApps_tInd in r2 as (?&->&?); auto.
    eapply whnf_red_inv in r1; eauto.
    apply whnf_red_mkApps_inv in r1 as (?&?); auto.
    depelim w.
    noconf e0.
    discriminate i0.
  Qed.
  
  Definition term_rel : Relation_Definitions.relation (∑ Γ t, welltyped Σ Γ t) :=
    fun '(Γ2; B; H) '(Γ1; t1; H2) =>
      ∥∑ na A, red (fst Σ) Γ1 t1 (tProd na A B) × (Γ1,, vass na A) = Γ2∥.

  Definition cod B t := match t with tProd _ _ B' => B = B' | _ => False end.

  Lemma wf_cod : WellFounded cod.
  Proof using.
    intros ?. induction a; econstructor; cbn in *; intros; try tauto; subst. eauto.
  Defined.

  Lemma wf_cod' : WellFounded (Relation_Operators.clos_trans _ cod).
  Proof using.
    clear HΣ.
    eapply Subterm.WellFounded_trans_clos. exact wf_cod.
  Defined.

  Lemma Acc_no_loop X (R : X -> X -> Prop) t : Acc R t -> R t t -> False.
  Proof.
    induction 1. intros. eapply H0; eauto.
  Qed.

  Ltac sq' := try (destruct HΣ; clear HΣ);
    repeat match goal with
          | H : ∥ _ ∥ |- _ => destruct H; try clear H
          end; try eapply sq.

  Definition wf_reduction_aux : WellFounded term_rel.
  Proof.
    intros (Γ & s & H). sq'.
    induction (normalisation Σ Γ s H) as [s _ IH].
    induction (wf_cod' s) as [s _ IH_sub] in Γ, H, IH |- *.
    econstructor.
    intros (Γ' & B & ?) [(na & A & ? & ?)]. subst.
    eapply Relation_Properties.clos_rt_rtn1 in r. inversion r.
      + subst. eapply IH_sub. econstructor. cbn. reflexivity.
        intros. eapply IH.
        inversion H0.
        * subst. econstructor. eapply prod_red_r. eassumption.
        * subst. eapply cored_red in H2 as [].
          eapply cored_red_trans. 2: eapply prod_red_r. 2:eassumption.
          eapply PCUICReduction.red_prod_r. eauto.
        * constructor. do 2 eexists. now split.
      + subst. eapply IH.
        * eapply red_neq_cored.
          eapply Relation_Properties.clos_rtn1_rt. exact r.
          intros ?. subst.
          eapply Relation_Properties.clos_rtn1_rt in X1.
          eapply cored_red_trans in X0; [| exact X1 ].
          eapply Acc_no_loop in X0. eauto.
          eapply @normalisation; eauto.
        * constructor. do 2 eexists. now split.
  Grab Existential Variables.
  - eapply red_welltyped; sq.
    3:eapply Relation_Properties.clos_rtn1_rt in r; eassumption. all:eauto.
  - destruct H as [].
    eapply inversion_Prod in X0 as (? & ? & ? & ? & ?) ; auto.
    eapply cored_red in H0 as [].
    econstructor. econstructor. econstructor. eauto.
    2:reflexivity. econstructor; pcuic. 
    eapply subject_reduction; eauto.
  Qed.

  Instance wf_reduction : WellFounded term_rel.
  Proof.
    refine (Wf.Acc_intro_generator 1000 _).
    exact wf_reduction_aux.
  Defined.
  Opaque wf_reduction.
  Opaque Acc_intro_generator.
  Opaque Wf.Acc_intro_generator.
  Ltac sq := try (destruct HΣ as [wfΣ]; clear HΣ);
    repeat match goal with
          | H : ∥ _ ∥ |- _ => destruct H
          end; try eapply sq.
    
  (* Definition of normalized arities *)
  Definition arity_ass := aname * term.

  Fixpoint mkNormalArity (l : list arity_ass) (s : Universe.t) : term :=
    match l with
    | [] => tSort s
    | (na, A) :: l => tProd na A (mkNormalArity l s)
    end.
  
  Lemma mkNormalArity_it_mkProd_or_LetIn (l : list arity_ass) (s : Universe.t) :
    mkNormalArity l s = it_mkProd_or_LetIn (rev_map (fun '(na, A) => vass na A) l) (tSort s).
  Proof.
    rewrite rev_map_spec.
    induction l; auto.
    cbn.
    destruct a.
    rewrite IHl it_mkProd_or_LetIn_app; auto.
  Qed.

  Lemma isArity_mkNormalArity l s :
    isArity (mkNormalArity l s).
  Proof.
    induction l as [|(na & A) l IH]; cbn; auto.
  Qed.

  Record conv_arity {Γ T} : Type :=
    build_conv_arity {
        conv_ar_context : list arity_ass;
        conv_ar_univ : Universe.t;
        conv_ar_red : ∥red Σ Γ T (mkNormalArity conv_ar_context conv_ar_univ)∥
      }.

  Global Arguments conv_arity : clear implicits.
  
  Lemma conv_arity_Is_conv_to_Arity {Γ T} :
    conv_arity Γ T ->
    Is_conv_to_Arity Σ Γ T.
  Proof.
    intros [asses univ r].
    eexists.
    split; [eassumption|].
    apply isArity_mkNormalArity.
  Qed.

  Definition conv_arity_or_not Γ T : Type :=
    (conv_arity Γ T) + {~Is_conv_to_Arity Σ Γ T}.
  
  Lemma isArity_red Γ u v :
    isArity u ->
    red Σ Γ u v ->
    isArity v.
  Proof.
    intros arity_u r.
    induction r using red_rect_n1; [easy|].
    eapply isArity_red1; eassumption.
  Qed.
  
  Lemma Is_conv_to_Arity_red Γ T T' :
    Is_conv_to_Arity Σ Γ T ->
    red Σ Γ T T' ->
    Is_conv_to_Arity Σ Γ T'.
  Proof.
    unfold Is_conv_to_Arity.
    intros [T'' (redT'' & is_arity)] red.
    sq.
    destruct (red_confluence wfΣ red X) as (a & reda' & reda'').
    exists a.
    split; [easy|].
    clear -is_arity reda''.
    eapply isArity_red; eauto.
  Qed.
  
  Inductive view_prod_sort : term -> Type :=
  | view_prod_sort_prod na A B : view_prod_sort (tProd na A B)
  | view_prod_sort_sort u : view_prod_sort (tSort u)
  | view_prod_sort_other t :
      ~isProd t ->
      ~isSort t ->
      view_prod_sort t.
  
  Equations view_prod_sortc (t : term) : view_prod_sort t := { 
    | tProd na A B => view_prod_sort_prod na A B;
    | tSort u => view_prod_sort_sort u;
    | t => view_prod_sort_other t _ _
    }.
  
  Equations? (noeqns) reduce_to_arity (Γ : context) (T : term) (wt : welltyped Σ Γ T)
    : conv_arity_or_not Γ T
    by wf ((Γ;T; wt) : (∑ Γ t, welltyped Σ Γ t)) term_rel :=
    reduce_to_arity Γ T wt with inspect (hnf Γ T wt) :=
      | exist Thnf eqhnf with view_prod_sortc Thnf := {
        | view_prod_sort_prod na A B with reduce_to_arity (Γ,, vass na A) B _ := {
          | inleft car => inleft {| conv_ar_context := (na, A) :: conv_ar_context car;
                                    conv_ar_univ := conv_ar_univ car |};
          | inright nocar => inright _
          };
        | view_prod_sort_sort u => inleft {| conv_ar_context := [];
                                             conv_ar_univ := u |};
        | view_prod_sort_other nonar notprod notsort => inright _
        }.
  Proof.
    all: pose proof (@hnf_sound Γ T wt) as [r].
    all: rewrite <- ?eqhnf in r.
    all: destruct HΣ as [wf].
    - destruct wt as (?&typ).
      eapply subject_reduction in r; eauto.
      apply inversion_Prod in r as (?&?&?&?&?); auto.
      econstructor; eauto.
    - constructor.
      eexists _, _; split; eauto.
    - destruct car as [c_ar c_univ [c_red]]; cbn.
      constructor.
      etransitivity; eauto.
      eapply red_prod; eauto.
    - eapply Is_conv_to_Arity_red in H as (?&[r']&isar); eauto.
      apply invert_red_prod in r' as (?&?&(->&?)&?); auto.
      contradiction nocar.
      eexists; eauto using sq.
    - constructor; auto.
    - pose proof (@hnf_complete Γ T wt) as [w].
      destruct HΣ.
      apply Is_conv_to_Arity_inv in H as [(na&A&B&[r'])|(u&[r'])]; auto.
      + eapply red_confluence in r' as (?&r1&r2); eauto.
        apply invert_red_prod in r2 as (?&?&(->&?)&?); auto.
        eapply whnf_red_inv in r1; eauto.
        depelim r1.
        rewrite H in notprod; auto.
      + eapply red_confluence in r' as (?&r1&r2); eauto.
        apply invert_red_sort in r2 as ->.
        eapply whnf_red_inv in r1; eauto.
        depelim r1.
        rewrite H in notsort; cbn in *; auto.
  Qed.
  
  Definition reduce_to_arity_check Γ T wt : typing_result (conv_arity Γ T) :=
    match reduce_to_arity Γ T wt with
    | inleft car => ret car
    | inright _ => raise (NotAnArity T)
    end.
End Reduce.

Global Arguments conv_arity : clear implicits.

Section Typecheck.
  Context {cf : checker_flags} {Σ : global_env_ext} (HΣ : ∥ wf Σ ∥)
          (Hφ : ∥ on_udecl Σ.1 Σ.2 ∥)
          (G : universes_graph) (HG : is_graph_of_uctx G (global_ext_uctx Σ)).

  Local Definition HΣ' : ∥ wf_ext Σ ∥.
  Proof.
    destruct HΣ, Hφ; now constructor.
  Defined.

  Definition isType_welltyped {Γ t}
    : isType Σ Γ t -> welltyped Σ Γ t.
  Proof.
    intros []. now econstructor.
  Qed.

  Lemma validity_wf {Γ t T} :
    ∥ wf_local Σ Γ ∥ -> ∥ Σ ;;; Γ |- t : T ∥ -> welltyped Σ Γ T.
  Proof.
    destruct HΣ as [wΣ]. intros [wΓ] [X].
    intros. eapply validity_term in X; try assumption.
    destruct X. now exists (tSort x).
  Defined.

  Lemma wat_welltyped {Γ T} :
    ∥ isType Σ Γ T ∥ -> welltyped Σ Γ T.
  Proof.
    destruct HΣ as [wΣ]. intros [X].
    now apply isType_welltyped.
  Defined.


  Definition iscumul Γ := isconv_term Σ HΣ Hφ G HG Γ Cumul.

  Program Definition convert_leq Γ t u
          (ht : welltyped Σ Γ t) (hu : welltyped Σ Γ u)
    : typing_result (∥ Σ ;;; Γ |- t <= u ∥) :=
    match leqb_term Σ G t u with true => ret _ | false =>
    match iscumul Γ t ht u hu with
    | ConvSuccess => ret _
    | ConvError e => (* fallback *)  (* nico *)
      let t' := hnf HΣ Γ t ht in
      let u' := hnf HΣ Γ u hu in
      raise (NotCumulSmaller G Γ t u t' u' e)
    end end.
  Next Obligation.
    symmetry in Heq_anonymous; eapply leqb_term_spec in Heq_anonymous; tea.
    constructor. now constructor.
  Qed.
  Next Obligation.
    symmetry in Heq_anonymous; apply isconv_term_sound in Heq_anonymous.
    assumption.
  Qed.

  Section InferAux.
    Variable (infer : forall Γ (HΓ : ∥ wf_local Σ Γ ∥) (t : term),
                 typing_result ({ A : term & ∥ Σ ;;; Γ |- t : A ∥ })).

    Program Definition infer_type Γ HΓ t
      : typing_result ({u : Universe.t & ∥ Σ ;;; Γ |- t : tSort u ∥}) :=
      tx <- infer Γ HΓ t ;;
      u <- reduce_to_sort HΣ Γ tx.π1 _ ;;
      ret (u.π1; _).
    Next Obligation.
      eapply validity_wf; eassumption.
    Defined.
    Next Obligation.
      destruct HΣ, HΓ, X, X0.
      now constructor; eapply type_reduction.
    Defined.

    (* Why doesn't the straightforward definition type check? *)
    (*
    Program Definition infer_prod Γ HΓ t
      : typing_result (∑ na A B, ∥ Σ ;;; Γ |- t : tProd na A B ∥) :=
      '(T; p) <- infer Γ HΓ t;;
      '(na; A; B; r) <- reduce_to_prod Γ T _;;
      ret (na; A; B; _).
     *)
    
    Program Definition infer_applicable Γ HΓ t
      : typing_result (∑ na A B, ∥ Σ ;;; Γ |- t : tProd na A B ∥) :=
      match infer Γ HΓ t with
      | Checked (u; p) =>
        match reduce_to_prod HΣ Γ u _ with
        | Checked (na; A; B; r) => Checked (na; A; B; _)
        | TypeError te => TypeError te
        end
      | TypeError te => TypeError te
      end.
    Next Obligation.
      eapply validity_wf; eauto.
    Defined.
    Next Obligation.
      destruct HΣ, p, r.
      constructor.
      eapply type_reduction; eauto.
    Defined.
    
    Program Definition infer_constructor Γ HΓ t
      : typing_result (∑ i u l, ∥ Σ ;;; Γ |- t : mkApps (tInd i u) l ∥) :=
      match infer Γ HΓ t with
      | Checked (T; p) =>
        match reduce_to_ind HΣ Γ T _ with
        | Checked (i; u; l; r) => Checked (i; u; l; _)
        | TypeError te => TypeError te
        end
      | TypeError te => TypeError te
      end.
    Next Obligation.
      eapply validity_wf; eauto.
    Defined.
    Next Obligation.
      destruct p, r, HΣ.
      constructor.
      eapply type_reduction; eauto.
    Defined.
    
    Program Definition infer_scheme Γ HΓ t :
      typing_result (∑ ctx u, ∥ Σ ;;; Γ |- t : mkNormalArity ctx u ∥) :=
      '(T; p) <- infer Γ HΓ t;;
      car <- reduce_to_arity_check HΣ Γ T _;;
      ret (conv_ar_context car; conv_ar_univ car; _).
    Next Obligation.
      eapply validity_wf; eauto.
    Defined.
    Next Obligation.
      destruct car as [? ? [r]].
      cbn.
      destruct HΣ, p.
      constructor; eapply type_reduction; eauto.
    Defined.

    Program Definition infer_cumul Γ HΓ t A (hA : ∥ isType Σ Γ A ∥)
      : typing_result (∥ Σ ;;; Γ |- t : A ∥) :=
      A' <- infer Γ HΓ t ;;
      X <- convert_leq Γ A'.π1 A _ _ ;;
      ret _.
    Next Obligation. now eapply validity_wf. Qed.
    Next Obligation. destruct hA; now apply wat_welltyped. Qed.
    Next Obligation.
      destruct HΣ, HΓ, hA, X, X0. constructor. eapply type_Cumul'; eassumption.
    Qed.
    
  End InferAux.


  Program Definition lookup_ind_decl ind
    : typing_result
        ({decl & {body & declared_inductive (fst Σ) decl ind body}}) :=
    match lookup_env (fst Σ) ind.(inductive_mind) with
    | Some (InductiveDecl decl) =>
      match nth_error decl.(ind_bodies) ind.(inductive_ind) with
      | Some body => ret (decl; body; _)
      | None => raise (UndeclaredInductive ind)
      end
    | _ => raise (UndeclaredInductive ind)
    end.
  Next Obligation.
    split.
    - symmetry in Heq_anonymous0.
      etransitivity. eassumption. reflexivity.
    - now symmetry.
  Defined.

  Lemma check_constraints_spec ctrs
    : check_constraints G ctrs -> valid_constraints (global_ext_constraints Σ) ctrs.
  Proof.
    pose proof HΣ'.
    intros HH.
    refine (check_constraints_sound G (global_ext_uctx Σ) _ _ HG _ HH).
    now apply wf_ext_global_uctx_invariants.
    now apply global_ext_uctx_consistent.
  Qed.
  
  Lemma is_graph_of_uctx_levels (l : Level.t) :
    wGraph.VSet.mem l (uGraph.wGraph.V G) <->
    LevelSet.mem l (global_ext_levels Σ).
  Proof.
    unfold is_graph_of_uctx in HG.
      case_eq (gc_of_uctx (global_ext_uctx Σ)); [intros [lvs cts] XX|intro XX];
        rewrite -> XX in *; simpl in *; [|contradiction].
      unfold gc_of_uctx in XX; simpl in XX.
      destruct (gc_of_constraints Σ); [|discriminate].
      inversion XX; subst. generalize (global_ext_levels Σ); intros lvs; cbn.
      clear.
      unfold is_true.
      rewrite LevelSet.mem_spec.
      rewrite wGraph.VSet.mem_spec.
      split.
      2: { apply no_prop_levels_no_prop_level. }
      intro H.
      apply LevelSetProp.FM.elements_2.
      unfold no_prop_levels in H.
      rewrite LevelSet.fold_spec in H.
      cut (SetoidList.InA eq l (LevelSet.elements lvs)
           \/ wGraph.VSet.In l wGraph.VSet.empty). {
        intros [|H0]; [trivial|].
        now apply wGraph.VSet.empty_spec in H0. }
      revert H. generalize (LevelSet.elements lvs), wGraph.VSet.empty; clear.
      intros lvs; induction lvs; cbn; [intuition|].
      intros S H. apply IHlvs in H. destruct H as [H|H].
      + left. now constructor 2.
      + destruct a; cbn in *. 
        all: apply wGraph.VSet.add_spec in H; destruct H as [H|H]; [left|now right].
        all: rewrite H; now constructor.
  Qed.

  Program Definition check_consistent_instance uctx u
    : typing_result (consistent_instance_ext Σ uctx u)
    := match uctx with
       | Monomorphic_ctx _ =>
         check_eq_nat #|u| 0 (Msg "monomorphic instance should be of length 0")
       | Polymorphic_ctx (inst, cstrs) =>
         let '(inst, cstrs) := AUContext.repr (inst, cstrs) in
         check_eq_true (forallb (fun l => wGraph.VSet.mem l (uGraph.wGraph.V G)) u)
                       (Msg "not all levels are contained in the graph") ;;
         X <- check_eq_nat #|u| #|inst|
                          (Msg "instance does not have the right length");;
         match check_constraints G (subst_instance_cstrs u cstrs) with
         | true => ret (conj _ _)
         | false => raise (Msg "ctrs not satisfiable")
         end
       end.
  Next Obligation.
    eapply forallb_All in H. eapply All_forallb'; tea.
    clear -cf HG. intros x; simpl. apply is_graph_of_uctx_levels.
  Qed.
  Next Obligation.
    repeat split.
    - now rewrite mapi_length in X.
    - eapply check_constraints_spec; eauto.
  Qed.

  Definition eqb_opt_term (t u : option term) :=
    match t, u with
    | Some t, Some u => eqb_term Σ G t u
    | None, None => true
    | _, _ => false
    end.


  Lemma eqb_opt_term_spec t u
    : eqb_opt_term t u -> eq_opt_term Σ (global_ext_constraints Σ) t u.
  Proof.
    destruct t, u; try discriminate; cbn.
    apply eqb_term_spec; tea. trivial.
  Qed.

  Definition eqb_decl (d d' : context_decl) :=
    eqb_opt_term d.(decl_body) d'.(decl_body) && eqb_term Σ G d.(decl_type) d'.(decl_type).

  Lemma eqb_decl_spec d d'
    : eqb_decl d d' -> eq_decl Σ (global_ext_constraints Σ) d d'.
  Proof.
    unfold eqb_decl, eq_decl.
    intro H. rtoProp. apply eqb_opt_term_spec in H.
    eapply eqb_term_spec in H0; tea. now split.
  Qed.

  Definition eqb_context (Γ Δ : context) := forallb2 eqb_decl Γ Δ.

  Lemma eqb_context_spec Γ Δ
    : eqb_context Γ Δ -> eq_context Σ (global_ext_constraints Σ) Γ Δ.
  Proof.
    unfold eqb_context, eq_context.
    intro HH. apply forallb2_All2 in HH.
    eapply All2_impl; try eassumption.
    cbn. apply eqb_decl_spec.
  Qed.

  Obligation Tactic := Program.Tactics.program_simplify ; eauto 2.
  
  Section check_fix.
    Context (infer : forall Γ (HΓ : ∥wf_local Σ Γ∥) t, typing_result (∑ A, ∥Σ;;; Γ |- t : A∥)).
    Context (Γ : context).
    Context (HΓ : ∥wf_local Σ Γ∥).

    Equations check_fix_types (mfix : mfixpoint term)
      : typing_result (∥ All (fun d => isType Σ Γ (dtype d)) mfix ∥) :=
     check_fix_types [] => Checked (sq All_nil);
     check_fix_types (def :: mfix) with infer_type infer Γ HΓ (dtype def) := {
       | Checked (s; t) with check_fix_types mfix := {
         | Checked a => Checked _;
         | TypeError e2 => TypeError _
         };
       | TypeError e1 => TypeError _
       }.
    Next Obligation.
      destruct a as [a], t as [t].
      constructor; constructor; auto.
      exists s; auto.
    Defined.
    
    Context (mfix : mfixpoint term).
    Context (all_types : ∥ All (fun d => isType Σ Γ (dtype d)) mfix ∥).

    Definition fix_ok d :=
      ∥ Σ ;;; Γ ,,, fix_context mfix |- dbody d : lift0 #|fix_context mfix| (dtype d) ∥.
    
    Equations check_fix_bodies_aux
              (mfix : mfixpoint term) (types : ∥ All (fun d => isType Σ Γ (dtype d)) mfix∥)
      : typing_result (All fix_ok mfix) :=
      check_fix_bodies_aux [] types => Checked All_nil;
      check_fix_bodies_aux (def :: mfix') types
        with infer_cumul infer (Γ ,,, fix_context mfix) _
                         (dbody def) (lift0 #|fix_context mfix| (dtype def)) _ := {
        | Checked t with check_fix_bodies_aux mfix' _ := {
          | Checked a => Checked (All_cons t a);
          | TypeError e2 => TypeError e2
          };
        | TypeError e1 => TypeError e1
        }.
    Next Obligation.
      sq.
      eapply PCUICWeakening.All_mfix_wf; eauto.
    Defined.
    Next Obligation.
      sq. depelim types.
      destruct i as [s HH].
      exists s.
      apply weakening with (T := tSort s); try assumption.
      now apply All_mfix_wf.
    Defined.
    Next Obligation.
      sq.
      now depelim types.
    Qed.
    
    Definition check_fix_bodies := check_fix_bodies_aux mfix all_types.

  End check_fix.
  
  Program Fixpoint infer (Γ : context) (HΓ : ∥ wf_local Σ Γ ∥) (t : term) {struct t}
    : typing_result ({ A : term & ∥ Σ ;;; Γ |- t : A ∥ }) :=
    match t with
    | tRel n =>
          match nth_error Γ n with
          | Some c => ret ((lift0 (S n)) (decl_type c); _)
          | None   => raise (UnboundRel n)
          end

    | tVar n  => raise (UnboundVar n)
    | tEvar ev args => raise (UnboundEvar ev)

    | tSort u =>
            check_eq_true (wf_universeb Σ u)
                          (Msg ("Sort contains an undeclared level " ^ string_of_sort u));;
            ret (tSort (Universe.super u); _)

    | tProd na A B =>
          s1 <- infer_type infer Γ HΓ A ;;
          s2 <- infer_type infer (Γ ,, vass na A) _ B ;;
          ret (tSort (Universe.sort_of_product s1.π1 s2.π1); _)

    | tLambda na A t =>
          s1 <- infer_type infer Γ HΓ A ;;
          B <- infer (Γ ,, vass na A) _ t ;;
          ret (tProd na A B.π1; _)

    | tLetIn n b b_ty b' =>
          infer_type infer Γ HΓ b_ty ;;
          infer_cumul infer Γ HΓ b b_ty _ ;;
          b'_ty <- infer (Γ ,, vdef n b b_ty) _ b' ;;
          ret (tLetIn n b b_ty b'_ty.π1; _)

    | tApp t u =>
          pi <- infer_applicable infer Γ HΓ t;;
          infer_cumul infer Γ HΓ u pi.π2.π1 _ ;;
          ret (subst10 u pi.π2.π2.π1; _)

    | tConst cst u =>
          match lookup_env (fst Σ) cst with
          | Some (ConstantDecl d) =>
            check_consistent_instance d.(cst_universes) u ;;
            let ty := subst_instance_constr u d.(cst_type) in
            ret (ty; _)
          |  _ => raise (UndeclaredConstant cst)
          end

    | tInd ind u =>
          d <- lookup_ind_decl ind ;;
          check_consistent_instance d.π1.(ind_universes) u ;;
          let ty := subst_instance_constr u d.π2.π1.(ind_type) in
          ret (ty; _)

    | tConstruct ind k u =>
          d <- lookup_ind_decl ind ;;
          match nth_error d.π2.π1.(ind_ctors) k with
          | Some cdecl =>
            check_consistent_instance d.π1.(ind_universes) u ;;
            ret (type_of_constructor d.π1 cdecl (ind, k) u; _)
          | None => raise (UndeclaredConstructor ind k)
          end

    | tCase (ind, par) p c brs =>
      I <- infer_constructor infer Γ HΓ c;;
      let '(ind'; I') := I in let '(u; I'') := I' in let '(args; H) := I'' in
      check_eq_true (eqb ind ind')
                    (* bad case info *)
                    (NotConvertible G Γ (tInd ind u) (tInd ind' u)) ;;
      d <- lookup_ind_decl ind' ;;
      let '(decl; d') := d in let '(body; HH) := d' in
      check_coind <- check_eq_true (negb (isCoFinite (ind_finite decl)))
            (Msg "Case on coinductives disallowed") ;;
      check_eq_true (ind_npars decl =? par)
                    (Msg "not the right number of parameters") ;;
      IS <- infer_scheme infer Γ HΓ p ;;
      let '(pctx; IS') := IS in let '(ps; typ_p) := IS' in
      check_eq_true
        (leb_sort_family (universe_family ps) (ind_kelim body))
        (Msg "cannot eliminate over this sort") ;;
      let pty := mkNormalArity pctx ps in
      let params := firstn par args in
      match build_case_predicate_type ind decl body params u ps with
      | None => raise (Msg "failure in build_case_predicate_type")
      | Some pty' =>
        (* We could avoid one useless sort comparison by only comparing *)
        (* the contexts [pctx] and [indctx] (what is done in Coq). *)
        match iscumul Γ pty _ pty' _ with
        | ConvError e => raise (NotCumulSmaller G Γ pty pty' pty pty' e)
        | ConvSuccess =>
          match map_option_out (build_branches_type ind decl body params u p) with
          | None => raise (Msg "failure in build_branches_type")
          | Some btys =>
            let btyswf : ∥ All (isType Σ Γ ∘ snd) btys ∥ := _ in
            (fix check_branches (brs btys : list (nat * term))
              (HH : ∥ All (isType Σ Γ ∘ snd) btys ∥) {struct brs}
                : typing_result
                  (All2 (fun br bty => br.1 = bty.1 /\ ∥ Σ ;;; Γ |- br.2 : bty.2 ∥) brs btys)
                        := match brs, btys with
                           | [], [] => ret All2_nil
                           | (n, t) :: brs , (m, A) :: btys =>
                             W <- check_dec (Msg "not nat eq")
                                           (EqDecInstances.nat_eqdec n m) ;;
                             Z <- infer_cumul infer Γ HΓ t A _ ;;
                             X <- check_branches brs btys _ ;;
                             ret (All2_cons (conj _ _) X)
                           | [], _ :: _
                           | _ :: _, [] => raise (Msg "wrong number of branches")
                           end) brs btys btyswf ;;
              ret (mkApps p (List.skipn par args ++ [c]); _)
          end
        end
      end

    | tProj (ind, n, k) c =>
          d <- lookup_ind_decl ind ;;
          match nth_error d.π2.π1.(ind_projs) k with
          | Some pdecl =>
            I <- infer_constructor infer Γ HΓ c;;
            let '(ind'; I') := I in let '(u; I'') := I' in let '(args; H) := I'' in
            check_eq_true (eqb ind ind')
                          (NotConvertible G Γ (tInd ind u) (tInd ind' u)) ;;
            check_eq_true (ind_npars d.π1 =? n)
                          (Msg "not the right number of parameters") ;;
            check_eq_true (#|args| =? ind_npars d.π1) (* probably redundant *)
                          (Msg "not the right number of parameters") ;;
            let ty := snd pdecl in
            ret (subst0 (c :: List.rev args) (subst_instance_constr u ty);
                   _)
          | None => raise (Msg "projection not found")
          end

    | tFix mfix n =>
      match nth_error mfix n with
      | None => raise (IllFormedFix mfix n)
      | Some decl =>
        XX <- check_fix_types infer Γ HΓ mfix;;
        YY <- check_fix_bodies infer Γ HΓ mfix XX;;
        check_eq_true (forallb (fun d => isLambda (dbody d)) mfix)
                      (Msg "all fixes must start with a lambda");;
        guarded <- check_eq_true (fix_guard mfix) (Msg "Unguarded fixpoint") ;;
        wffix <- check_eq_true (wf_fixpoint Σ.1 mfix) (Msg "Ill-formed fixpoint: not defined on a mutually inductive family") ;;
        ret (dtype decl; _)
      end

    | tCoFix mfix n =>
      match nth_error mfix n with
      | None => raise (IllFormedFix mfix n)
      | Some decl =>
        XX <- check_fix_types infer Γ HΓ mfix;;
        YY <- check_fix_bodies infer Γ HΓ mfix XX;;
        guarded <- check_eq_true (cofix_guard mfix) (Msg "Unguarded cofixpoint") ;;
        wfcofix <- check_eq_true (wf_cofixpoint Σ.1 mfix) (Msg "Ill-formed cofixpoint: not producing values in a mutually coinductive family") ;;
        ret (dtype decl; _)
      end
    end.

  (* tRel *)
  Next Obligation. intros; sq; now econstructor. Defined.
  (* tSort *)
  Next Obligation.
    eapply (reflect_bP (wf_universe_reflect _ _)) in H.
    sq; econstructor; tas.
  Defined.
  (* tProd *)
  Next Obligation.
    (* intros Γ HΓ t na A B Heq_t [s ?];  *)
      sq; econstructor; cbn; easy. Defined.
  Next Obligation.
    (* intros Γ HΓ t na A B Heq_t [s1 ?] [s2 ?]; *)
    sq; econstructor; eassumption.
  Defined.
  (* tLambda *)
  Next Obligation.
    (* intros Γ HΓ t0 na A t Heq_t [s ?]; *)
      sq; econstructor; cbn; easy.
  Defined.
  Next Obligation.
    (* intros Γ HΓ t0 na A t Heq_t [s ?] [B ?]; *)
      sq; econstructor; eassumption.
  Defined.
  (* tLetIn *)
  Next Obligation.
    (* intros Γ HΓ t n b b_ty b' Heq_t [? ?]; *)
      sq. econstructor; eauto.
  Defined.
  Next Obligation.
    (* intros Γ HΓ t n b b_ty b' Heq_t [? ?] H0; *)
    sq; econstructor; cbn; eauto.
  Defined.
  Next Obligation.
    (* intros Γ HΓ t n b b_ty b' Heq_t [? ?] H0 [? ?]; *)
    sq; econstructor; eassumption.
  Defined.

  (* tApp *)
  Next Obligation.
    cbn in *; sq.
    eapply validity_term in X1 ; try assumption. destruct X1 as [s HH].
    eapply inversion_Prod in HH ; try assumption.
    destruct HH as [s1 [_ [HH _]]].
    eexists. eassumption.
  Defined.
  Next Obligation.
    cbn in *; sq; econstructor.
    2: eassumption.
    eassumption.
  Defined.

  (* tConst *)
  Next Obligation.
    rename Heq_anonymous into HH.
    sq; constructor; try assumption.
    symmetry in HH.
    etransitivity. eassumption. reflexivity.
  Defined.

  (* tInd *)
  Next Obligation.
    sq; econstructor; eassumption.
  Defined.

  (* tConstruct *)
  Next Obligation.
    sq; econstructor; tea. now split.
  Defined.

  (* tCase *)
  Next Obligation. simpl; eauto using validity_wf. Qed.
  Next Obligation.
    destruct X10. sq.
    change (eqb ind I = true) in H0.
    destruct (eqb_spec ind I) as [e|e]; [destruct e|discriminate].
    change (eqb (ind_npars d) par = true) in H1.
    destruct (eqb_spec (ind_npars d) par) as [e|e]; [|discriminate].
    rename Heq_anonymous into HH. symmetry in HH.
    simpl in *.
    eapply validity in X7; eauto.
    rewrite <- e in HH.
    eapply PCUICInductiveInversion.WfArity_build_case_predicate_type in HH; eauto.
    destruct HH as [[s Hs] ?]. eexists; eauto.
    rewrite mkNormalArity_it_mkProd_or_LetIn in X1.
    eapply validity in X1; eauto.
    eapply PCUICInductives.isType_it_mkProd_or_LetIn_inv in X1; eauto.
    eapply isType_wf_universes in X1. simpl in X1.
    now exact (PCUICWfUniverses.reflect_bP (wf_universe_reflect _ _) X1). auto.
  Qed.

  Next Obligation.
    symmetry in Heq_anonymous1.
    unfold iscumul in Heq_anonymous1. simpl in Heq_anonymous1.
    apply isconv_term_sound in Heq_anonymous1.
    red in Heq_anonymous1.
    noconf Heq_I''.
    noconf Heq_I'. noconf Heq_I.
    noconf Heq_d. noconf Heq_d'.
    noconf Heq_IS.
    noconf Heq_IS'.
    simpl in *; sq.
    change (eqb ind I = true) in H0.
    destruct (eqb_spec ind I) as [e|e]; [destruct e|discriminate H0].
    change (eqb (ind_npars d) par = true) in H1.
    destruct (eqb_spec (ind_npars d) par) as [e|e]; [|discriminate]; subst.
    assert (wfΣ : wf_ext Σ) by (split; auto).
    have val:= validity_term wfΣ H.
    eapply type_Cumul' in typ_p; [| |eassumption].
    2:{ eapply PCUICInductiveInversion.WfArity_build_case_predicate_type; eauto.
        eapply validity in typ_p; eauto.
        rewrite mkNormalArity_it_mkProd_or_LetIn in typ_p.
        eapply PCUICInductives.isType_it_mkProd_or_LetIn_inv in typ_p; eauto.
        eapply isType_wf_universes in typ_p. simpl in typ_p.
        now exact (PCUICWfUniverses.reflect_bP (wf_universe_reflect _ _) typ_p). auto. }
    have [pctx' da] : (∑ pctx', destArity [] pty' =  Some (pctx', X0)).
    { symmetry in Heq_anonymous0.
      unshelve eapply (PCUICInductives.build_case_predicate_type_spec (Σ.1, ind_universes d)) in Heq_anonymous0 as [parsubst [_ ->]].
      eauto. eapply (PCUICWeakeningEnv.on_declared_inductive wfΣ) in HH as [? ?]. eauto.
      eexists. rewrite !destArity_it_mkProd_or_LetIn; simpl. reflexivity. }
    eapply PCUICInductiveInversion.build_branches_type_wt. 6:eapply typ_p. all:eauto.
  Defined.

  Next Obligation.
    sq.
    depelim HH; auto.
  Defined.
  Next Obligation.
    sq.
    depelim HH; auto.
  Defined.

  (* The obligation tactic removes a useful let here. *)
  Obligation Tactic := idtac.
  Next Obligation.
    intros. clearbody btyswf. idtac; Program.Tactics.program_simplify.
    symmetry in Heq_anonymous1.
    unfold iscumul in Heq_anonymous1. simpl in Heq_anonymous1.
    apply isconv_term_sound in Heq_anonymous1.
    noconf Heq_I''. noconf Heq_I'. noconf Heq_I.
    noconf Heq_d. noconf Heq_d'.
    noconf Heq_IS. noconf Heq_IS'.
    simpl in *.
    assert (∥ All2 (fun x y  => ((fst x = fst y) *
                              (Σ;;; Γ |- snd x : snd y) * isType Σ Γ y.2)%type) brs btys ∥). {
      solve_all. simpl in *.
      destruct btyswf. eapply All2_sq. solve_all. simpl in *; intuition (sq; auto). }
    clear H3. sq.
    change (eqb ind I = true) in H0.
    destruct (eqb_spec ind I) as [e|e]; [destruct e|discriminate H0].
    change (eqb (ind_npars d) par = true) in H1.
    destruct (eqb_spec (ind_npars d) par) as [e|e]; [|discriminate]; subst.
    assert (wfΣ : wf_ext Σ) by (split; auto).
    eapply type_Cumul' in typ_p; eauto.
    2:{ eapply PCUICInductiveInversion.WfArity_build_case_predicate_type; eauto.
        now eapply validity in H.
        eapply validity in typ_p; eauto.
        rewrite mkNormalArity_it_mkProd_or_LetIn in typ_p.
        eapply PCUICInductives.isType_it_mkProd_or_LetIn_inv in typ_p; eauto.
        eapply isType_wf_universes in typ_p. simpl in typ_p.
        now exact (PCUICWfUniverses.reflect_bP (wf_universe_reflect _ _) typ_p). auto. }
    have [pctx' da] : (∑ pctx', destArity [] pty' =  Some (pctx', X0)).
    { symmetry in Heq_anonymous0.
      unshelve eapply (PCUICInductives.build_case_predicate_type_spec (Σ.1, ind_universes d)) in Heq_anonymous0 as [parsubst [_ ->]].
      eauto. eapply (PCUICWeakeningEnv.on_declared_inductive wfΣ) in HH as [? ?]. eauto.
      eexists. rewrite !destArity_it_mkProd_or_LetIn; simpl. reflexivity. }
    eapply type_Case with (pty0:=pty'); tea.
    - reflexivity.
    - symmetry; eassumption.
    - destruct isCoFinite; auto.
    - symmetry; eauto.
  Defined.

  Obligation Tactic := Program.Tactics.program_simplify ; eauto 2.

  (* tProj *)
  Next Obligation.
    simpl in *; sq; eapply type_Proj with (pdecl := (i, t0)).
    - split. eassumption. split. symmetry; eassumption. cbn in *.
      now apply beq_nat_true.
    - cbn. destruct (ssrbool.elimT (eqb_spec ind I)); auto.
    - now apply beq_nat_true.
  Defined.

  (* tFix *)
  Next Obligation.
    assert (∥ All
              (fun d =>
                 ((Σ;;; Γ ,,, fix_context mfix |- dbody d : (lift0 #|fix_context mfix|) (dtype d))
                  * (isLambda (dbody d) = true))%type) mfix ∥).
    { destruct XX.
      apply All_sq.
      apply forallb_All in H.
      apply (All_impl (All_mix YY H)).
      intros ? ([]&islam); constructor; auto. }
    sq; econstructor; try eassumption.
    symmetry; eassumption.
  Qed.

  (* tCoFix *)
  Next Obligation.
    assert (∥ All
              (fun d =>
                 (Σ;;; Γ ,,, fix_context mfix |- dbody d : (lift0 #|fix_context mfix|) (dtype d))%type)
              mfix ∥).
    {
      eapply All_sq, All_impl.  exact YY.
      now cbn; intros ? []. }
    sq; econstructor; try eassumption.
    symmetry; eassumption.
  Qed.

  Lemma sq_wfl_nil : ∥ wf_local Σ [] ∥.
  Proof.
   repeat constructor.
  Qed.

  Program Fixpoint check_context Γ : typing_result (∥ wf_local Σ Γ ∥)
    := match Γ with
       | [] => ret sq_wfl_nil
       | {| decl_body := None; decl_type := A |} :: Γ =>
         HΓ <- check_context Γ ;;
         XX <- infer_type infer Γ HΓ A ;;
         ret _
       | {| decl_body := Some t; decl_type := A |} :: Γ =>
         HΓ <- check_context Γ ;;
         XX <- infer_type infer Γ HΓ A ;;
         XX <- infer_cumul infer Γ HΓ t A _ ;;
         ret _
       end.
  Next Obligation.
    sq. econstructor; tas. econstructor; eauto.
  Qed.
  Next Obligation.
    sq. econstructor; tea.
  Qed.
  Next Obligation.
    sq. econstructor; tas. econstructor; eauto.
  Qed.

(* 
  Program Definition check_isWfArity Γ (HΓ : ∥ wf_local Σ Γ ∥) A
    : typing_result (∥ isWfArity Σ Γ A ∥) :=
    match destArity [] A with
    | None => raise (Msg (print_term Σ Γ A ^ " is not an arity"))
    | Some (ctx, s) => XX <- check_context (Γ ,,, ctx) ;;
                      ret _
    end.
  Next Obligation.
    destruct XX. constructor. exists ctx, s.
    split; auto.
  Defined. *)

  Program Definition check_isType Γ (HΓ : ∥ wf_local Σ Γ ∥) A
    : typing_result (∥ isType Σ Γ A ∥) :=
    s <- infer Γ HΓ A ;;
    s' <- reduce_to_sort HΣ Γ s.π1 _ ;;
    ret _.
  Next Obligation. now eapply validity_wf. Defined.
  Next Obligation. destruct X0. sq. eexists. eapply type_reduction; tea. Defined.

  Program Definition check Γ (HΓ : ∥ wf_local Σ Γ ∥) t A
    : typing_result (∥ Σ;;; Γ |- t : A ∥) :=
    check_isType Γ HΓ A ;;
    infer_cumul infer Γ HΓ t A _.
  
End Typecheck.


Definition infer' {cf:checker_flags} {Σ} (HΣ : ∥ wf_ext Σ ∥)
  := infer (map_squash fst HΣ) (map_squash snd HΣ).

Definition make_graph_and_infer {cf:checker_flags} {Σ} (HΣ : ∥ wf_ext Σ ∥)
  := let '(G; HG) := wf_ext_is_graph HΣ in infer' HΣ G HG.



Section CheckEnv.
  Context  {cf:checker_flags}.

  Inductive env_error :=
  | IllFormedDecl (e : string) (e : type_error)
  | AlreadyDeclared (id : string).

  Inductive EnvCheck (A : Type) :=
  | CorrectDecl (a : A)
  | EnvError (Σ : global_env_ext) (e : env_error).
  Global Arguments EnvError {A} Σ e.
  Global Arguments CorrectDecl {A} a.

  Global Instance envcheck_monad : Monad EnvCheck :=
    {| ret A a := CorrectDecl a ;
       bind A B m f :=
         match m with
         | CorrectDecl a => f a
         | EnvError g e => EnvError g e
         end
    |}.

  Global Instance envcheck_monad_exc
    : MonadExc (global_env_ext * env_error) EnvCheck :=
    { raise A '(g, e) := EnvError g e;
      catch A m f :=
        match m with
        | CorrectDecl a => m
        | EnvError g t => f (g, t)
        end
    }.

  Definition wrap_error {A} Σ (id : string) (check : typing_result A) : EnvCheck A :=
    match check with
    | Checked a => CorrectDecl a
    | TypeError e => EnvError Σ (IllFormedDecl id e)
    end.

  Definition check_wf_type kn Σ HΣ HΣ' G HG t
    : EnvCheck (∑ u, ∥ Σ;;; [] |- t : tSort u ∥)
    := wrap_error Σ (string_of_kername  kn) (@infer_type _ Σ HΣ (@infer _ Σ HΣ HΣ' G HG) [] sq_wfl_nil t).

  Definition check_wf_judgement kn Σ HΣ HΣ' G HG t ty
    : EnvCheck (∥ Σ;;; [] |- t : ty ∥)
    := wrap_error Σ (string_of_kername kn) (@check _ Σ HΣ HΣ' G HG [] sq_wfl_nil t ty).

  Definition infer_term Σ HΣ HΣ' G HG t :=
    wrap_error Σ "toplevel term" (@infer _ Σ HΣ HΣ' G HG [] sq_wfl_nil t).

  Program Fixpoint check_fresh id env : EnvCheck (∥ fresh_global id env ∥) :=
    match env with
    | [] => ret (sq (Forall_nil _))
    | g :: env =>
      p <- check_fresh id env;;
      match eq_constant id g.1 with
      | true => EnvError (empty_ext env) (AlreadyDeclared (string_of_kername id))
      | false => ret _
      end
    end.
  Next Obligation.
    sq. constructor; tas. simpl.
    change (false = eqb id k) in Heq_anonymous.
    destruct (eqb_spec id k); [discriminate|].
    easy.
  Defined.

  (* todo move *)
  Definition VariableLevel_get_noprop (l : Level.t) : option VariableLevel.t
    := match l with
       | Level.lSet => None
       | Level.Level s => Some (VariableLevel.Level s)
       | Level.Var n => Some (VariableLevel.Var n)
       end.

  Definition add_uctx (uctx : wGraph.VSet.t × GoodConstraintSet.t)
             (G : universes_graph) : universes_graph
    := let levels := wGraph.VSet.union uctx.1 G.1.1 in
       let edges := wGraph.VSet.fold
                      (fun l E =>
                         match VariableLevel_get_noprop l with
                         | None => E
                         | Some ll => wGraph.EdgeSet.add (edge_of_level ll) E
                         end)
                      uctx.1 G.1.2 in
       let edges := GoodConstraintSet.fold
                      (fun ctr => wGraph.EdgeSet.add (edge_of_constraint ctr))
                      uctx.2 edges in
       (levels, edges, G.2).


  Definition check_variance univs (variances : option (list Variance.t)) :=
    match variances with
    | None => true
    | Some v =>
      match univs with
      | Monomorphic_ctx _ => false
      | Polymorphic_ctx auctx => eqb #|v| #|UContext.instance (AUContext.repr auctx)|
      end
    end.

  Definition Build_on_inductive_sq {Σ ind mdecl}
    : ∥ Alli (on_ind_body (lift_typing typing) Σ ind mdecl) 0 (ind_bodies mdecl) ∥ ->
      ∥ wf_local Σ (ind_params mdecl) ∥ ->
      context_assumptions (ind_params mdecl) = ind_npars mdecl ->
      ind_guard mdecl ->
      check_variance (ind_universes mdecl) (ind_variance mdecl) ->
      ∥ on_inductive (lift_typing typing) Σ ind mdecl ∥.
  Proof.
    intros H H0 H1 H2 H3. sq. econstructor; try eassumption.
    unfold check_variance in H3. unfold on_variance.
    destruct (ind_universes mdecl) eqn:E;
    destruct (ind_variance mdecl) eqn:E'; try congruence.
    2:split. now eapply eqb_eq in H3.
  Defined.

  Program Fixpoint monad_Alli {T} {M : Monad T} {A} {P} (f : forall n x, T (∥ P n x ∥)) l n
    : T (∥ @Alli A P n l ∥)
    := match l with
       | [] => ret (sq Alli_nil)
       | a :: l => X <- f n a ;;
                    Y <- monad_Alli f l (S n) ;;
                    ret _
       end.
  Next Obligation.
    sq. constructor; assumption.
  Defined.


  (* Definition Build_on_ind_body Σ mind mdecl i idecl ind_indices ind_sort *)
  (*   : ind_type idecl = *)
  (*     it_mkProd_or_LetIn (ind_params mdecl) *)
  (*                        (it_mkProd_or_LetIn ind_indices (tSort ind_sort)) -> *)
  (*     ∥ on_type (lift_typing typing) Σ [] (ind_type idecl) ∥ -> *)
  (*     forall onConstructors : on_constructors P Σ mind mdecl i idecl (ind_ctors idecl), *)
  (*       (ind_projs idecl <> [] -> *)
  (*        on_projections P Σ mind mdecl i idecl ind_indices (ind_projs idecl)) -> *)
  (*       check_ind_sorts P onConstructors ind_sort -> on_ind_body P Σ mind mdecl i idecl *)


  Lemma check_one_ind_body:
    forall Σ : global_env_ext,
      ∥ wf Σ ∥ ->
      ∥ on_udecl Σ.1 Σ.2 ∥ ->
      forall G : universes_graph,
        is_graph_of_uctx G (global_ext_uctx Σ) ->
        forall (id : kername) (mdecl : mutual_inductive_body)
          (n : nat) (x : one_inductive_body),
          EnvCheck (∥ on_ind_body (lift_typing typing) Σ id mdecl n x ∥).
  Proof.
    intros Σ HΣ HΣ'0 G HG id mdecl n [].
  Admitted.

  Program Definition check_wf_decl (Σ : global_env_ext) HΣ HΣ' G HG
             kn (d : global_decl)
    : EnvCheck (∥ on_global_decl (lift_typing typing) Σ kn d ∥) :=
    match d with
    | ConstantDecl cst =>
      match cst.(cst_body) with
      | Some term => check_wf_judgement kn Σ HΣ HΣ' G HG term cst.(cst_type) ;; ret _
      | None => check_wf_type kn Σ HΣ HΣ' G HG cst.(cst_type) ;; ret _
      end
    | InductiveDecl mdecl =>
      X1 <- monad_Alli (check_one_ind_body Σ HΣ HΣ' G HG kn mdecl) _ _ ;;
      let id := string_of_kername kn in
      X2 <- wrap_error Σ id (check_context HΣ HΣ' G HG (ind_params mdecl)) ;;
      X3 <- wrap_error Σ id (check_eq_nat (context_assumptions (ind_params mdecl))
                                       (ind_npars mdecl)
                                       (Msg "wrong number of parameters")) ;;
      X4 <- wrap_error Σ id (check_eq_true (ind_guard mdecl) (Msg "guard"));;
      X5 <- wrap_error Σ id (check_eq_true (check_variance mdecl.(ind_universes) mdecl.(ind_variance)) (Msg "variance"));;
      ret (Build_on_inductive_sq X1 X2 X3 X4 X5)
    end.
  Next Obligation.
    sq. unfold on_constant_decl; rewrite <- Heq_anonymous; tas.
  Qed.
  Next Obligation.
    sq. unfold on_constant_decl; rewrite <- Heq_anonymous.
    eexists. eassumption.
  Qed.


  Definition uctx_of_udecl u : ContextSet.t :=
    (levels_of_udecl u, constraints_of_udecl u).

  Lemma add_uctx_make_graph levels1 levels2 ctrs1 ctrs2
  : add_uctx (levels1, ctrs1) (make_graph (levels2, ctrs2))
    = make_graph (wGraph.VSet.union levels1 levels2,
                  GoodConstraintSet.union ctrs1 ctrs2).
  Admitted.

  Lemma gc_of_constraints_union S S'
    : gc_of_constraints (ConstraintSet.union S S') =
      (S1 <- gc_of_constraints S ;;
       S2 <- gc_of_constraints S' ;;
       ret (GoodConstraintSet.union S1 S2)).
  Admitted.

  Lemma no_prop_levels_union S S'
    : no_prop_levels (LevelSet.union S S')
      = wGraph.VSet.union (no_prop_levels S) (no_prop_levels S').
  Admitted.

  (* rely on proof irrelevance *)
  Axiom graph_eq : forall (G G' : universes_graph),
      wGraph.VSet.Equal G.1.1 G'.1.1
      -> wGraph.EdgeSet.Equal G.1.2 G'.1.2
      -> G.2 = G'.2
      -> G = G'.


  Program Definition check_udecl id (Σ : global_env) (HΣ : ∥ wf Σ ∥) G
          (HG : is_graph_of_uctx G (global_uctx Σ)) (udecl : universes_decl)
    : EnvCheck (∑ uctx', gc_of_uctx (uctx_of_udecl udecl) = Some uctx' /\
                         ∥ on_udecl Σ udecl ∥) :=
    let levels := levels_of_udecl udecl in
    let global_levels := global_levels Σ in
    let all_levels := LevelSet.union levels global_levels in
    check_eq_true (LevelSet.for_all (fun l => negb (LevelSet.mem l global_levels)) levels)
       (empty_ext Σ, IllFormedDecl id (Msg ("non fresh level in " ^ print_lset levels)));;
    check_eq_true (ConstraintSet.for_all (fun '(l1, _, l2) => LevelSet.mem l1 all_levels && LevelSet.mem l2 all_levels) (constraints_of_udecl udecl))
                                    (empty_ext Σ, IllFormedDecl id (Msg ("non declared level in " ^ print_lset levels ^
                                    " |= " ^ print_constraint_set (constraints_of_udecl udecl))));;
    check_eq_true match udecl with
                  | Monomorphic_ctx ctx
                    => LevelSet.for_all (negb ∘ Level.is_var) ctx.1
                  | _ => true
                  end (empty_ext Σ, IllFormedDecl id (Msg "Var level in monomorphic context")) ;;
    (* TODO: could be optimized by reusing G *)
    match gc_of_uctx (uctx_of_udecl udecl) as X' return (X' = _ -> EnvCheck _) with
    | None => fun _ =>
      raise (empty_ext Σ, IllFormedDecl id (Msg "constraints trivially not satisfiable"))
    | Some uctx' => fun Huctx =>
      check_eq_true (wGraph.is_acyclic (add_uctx uctx' G))
                    (empty_ext Σ, IllFormedDecl id (Msg "constraints not satisfiable"));;
                                 ret (uctx'; (conj _ _))
    end eq_refl.
  Next Obligation.
    assert (HH: ConstraintSet.For_all
                  (fun '(l1, _, l2) =>
                     LevelSet.In l1 (LevelSet.union (levels_of_udecl udecl) (global_levels Σ)) /\
                     LevelSet.In l2 (LevelSet.union (levels_of_udecl udecl) (global_levels Σ)))
                  (constraints_of_udecl udecl)). {
      clear -H0. apply ConstraintSet.for_all_spec in H0.
      2: now intros x y [].
      intros [[l ct] l'] Hl. specialize (H0 _ Hl). simpl in H0.
      apply andb_true_iff in H0. destruct H0 as [H H0].
      apply LevelSet.mem_spec in H. apply LevelSet.mem_spec in H0.
      now split. }
    repeat split.
    - clear -H. apply LevelSet.for_all_spec in H.
      2: now intros x y [].
      intros l Hl. specialize (H l Hl); cbn in H.
      apply negb_true_iff in H. now apply LevelSetFact.not_mem_iff in H.
    - exact HH.
    - clear -H1. destruct udecl; trivial.
    - clear -HΣ HH Huctx H2 HG. unfold gc_of_uctx, uctx_of_udecl in *.
      simpl in *.
      unfold satisfiable_udecl.
      unfold is_graph_of_uctx in HG. unfold gc_of_uctx in *.
      case_eq (gc_of_constraints (global_uctx Σ).2);
        [|intro XX; rewrite XX in HG; contradiction HG].
      intros Σctrs HΣctrs.
      unfold global_ext_constraints. simpl in *.
      rewrite HΣctrs in HG.
      case_eq (gc_of_constraints (constraints_of_udecl udecl));
        [|intro XX; rewrite XX in Huctx; discriminate Huctx].
      intros ctrs Hctrs. rewrite Hctrs in Huctx. simpl in *.
      eapply (is_consistent_spec (global_ext_uctx (Σ, udecl))).
      { apply wf_global_uctx_invariants in HΣ.
        split.
        + clear -HΣ. cbn. apply LevelSet.union_spec; right.
          apply HΣ.
        + intros [[l ct] l'] Hl.
          apply ConstraintSet.union_spec in Hl. destruct Hl.
          apply (HH _ H). clear -HΣ H ct. destruct HΣ as [_ HΣ].
          specialize (HΣ (l, ct, l') H).
          split; apply LevelSet.union_spec; right; apply HΣ. }
      unfold is_consistent, global_ext_uctx, gc_of_uctx, global_ext_constraints.
      simpl.
      rewrite gc_of_constraints_union.
      rewrite HΣctrs Hctrs.
      inversion Huctx; subst; clear Huctx.
      clear -H2 cf. rewrite add_uctx_make_graph in H2.
      refine (eq_rect _ (fun G => wGraph.is_acyclic G = true) H2 _ _).
      apply graph_eq; try reflexivity.
      + simpl. unfold global_ext_levels. simpl.
        rewrite no_prop_levels_union. reflexivity.
      + simpl. unfold global_ext_levels. simpl.
        rewrite no_prop_levels_union. reflexivity.
  Defined.

  Program Fixpoint check_wf_env (Σ : global_env)
    : EnvCheck (∑ G, (is_graph_of_uctx G (global_uctx Σ) /\ ∥ wf Σ ∥)) :=
    match Σ with
    | [] => ret (init_graph; _)
    | d :: Σ =>
        G <- check_wf_env Σ ;;
        check_fresh d.1 Σ ;;
        let udecl := universes_decl_of_decl d.2 in
        uctx <- check_udecl (string_of_kername d.1) Σ _ G.π1 (proj1 G.π2) udecl ;;
        let G' := add_uctx uctx.π1 G.π1 in
        check_wf_decl (Σ, udecl) _ _ G' _ d.1 d.2 ;;
        match udecl with
        | Monomorphic_ctx _ => ret (G'; _)
        | Polymorphic_ctx _ => ret (G.π1; _)
        end
    end.
  Next Obligation.
    repeat constructor. apply graph_eq; try reflexivity.
    cbn. symmetry. apply wGraph.VSetProp.singleton_equal_add.
  Qed.
  Next Obligation.
    sq. unfold is_graph_of_uctx, gc_of_uctx; simpl.
    unfold gc_of_uctx in e. simpl in e.
    case_eq (gc_of_constraints (constraints_of_udecl (universes_decl_of_decl g)));
      [|intro HH; rewrite HH in e; discriminate e].
    intros ctrs' Hctrs'. rewrite Hctrs' in e.
    cbn in e. inversion e; subst; clear e.
    unfold global_ext_constraints; simpl.
    rewrite gc_of_constraints_union. rewrite Hctrs'.
    red in i. unfold gc_of_uctx in i; simpl in i.
    case_eq (gc_of_constraints (global_constraints Σ));
      [|intro HH; rewrite HH in i; cbn in i; contradiction i].
    intros Σctrs HΣctrs; rewrite HΣctrs in i; simpl in *.
    subst G. unfold global_ext_levels; simpl. rewrite no_prop_levels_union.
    symmetry; apply add_uctx_make_graph.
  Qed.
  Next Obligation.
    split; sq. 2: constructor; tas.
    unfold is_graph_of_uctx, gc_of_uctx; simpl.
    unfold gc_of_uctx in e. simpl in e.
    case_eq (gc_of_constraints (constraints_of_udecl (universes_decl_of_decl g)));
      [|intro HH; rewrite HH in e; discriminate e].
    intros ctrs' Hctrs'. rewrite Hctrs' in e.
    cbn in e. inversion e; subst; clear e.
    unfold global_ext_constraints; simpl.
    rewrite gc_of_constraints_union.
    assert (eq: monomorphic_constraints_decl g
                = constraints_of_udecl (universes_decl_of_decl g)). {
      destruct g. destruct c, cst_universes; try discriminate; reflexivity.
      destruct m, ind_universes; try discriminate; reflexivity. }
    rewrite eq; clear eq. rewrite Hctrs'.
    red in i. unfold gc_of_uctx in i; simpl in i.
    case_eq (gc_of_constraints (global_constraints Σ));
      [|intro HH; rewrite HH in i; cbn in i; contradiction i].
    intros Σctrs HΣctrs; rewrite HΣctrs in i; simpl in *.
    subst G. unfold global_ext_levels; simpl. rewrite no_prop_levels_union.
    assert (eq: monomorphic_levels_decl g
                = levels_of_udecl (universes_decl_of_decl g)). {
      destruct g. destruct c, cst_universes; try discriminate; reflexivity.
      destruct m, ind_universes; try discriminate; reflexivity. }
    rewrite eq. symmetry; apply add_uctx_make_graph.
  Qed.
  Next Obligation.
    split; sq. 2: constructor; tas.
    unfold global_uctx; simpl.
    assert (eq1: monomorphic_levels_decl g = LevelSet.empty). {
      destruct g. destruct c, cst_universes; try discriminate; reflexivity.
      destruct m, ind_universes; try discriminate; reflexivity. }
    rewrite eq1; clear eq1.
    assert (eq1: monomorphic_constraints_decl g = ConstraintSet.empty). {
      destruct g. destruct c, cst_universes; try discriminate; reflexivity.
      destruct m, ind_universes; try discriminate; reflexivity. }
    rewrite eq1; clear eq1.
    assumption.
  Qed.

  Lemma wf_consistent Σ : wf Σ -> consistent (global_constraints Σ).
  Proof.
    destruct Σ.
    - exists {| valuation_mono := fun _ => 1%positive;  valuation_poly := fun _ => 0 |}.
      intros x Hx; now apply ConstraintSetFact.empty_iff in Hx.
    - inversion 1; subst. subst udecl. clear -H2.
      destruct H2 as [_ [_ [_ [v Hv]]]].
      exists v. intros ct Hc. apply Hv. simpl in *.
      apply ConstraintSet.union_spec in Hc. destruct Hc.
      apply ConstraintSet.union_spec; simpl.
      + left. destruct d.
        destruct c, cst_universes. assumption.
        apply ConstraintSetFact.empty_iff in H; contradiction.
        destruct m, ind_universes. assumption.
        apply ConstraintSetFact.empty_iff in H; contradiction.
      + apply ConstraintSet.union_spec; simpl.
        now right.
  Qed.


  Program Definition typecheck_program (p : program) φ Hφ
    : EnvCheck (∑ A, ∥ (p.1, φ) ;;; [] |- p.2  : A ∥) :=
    let Σ := fst p in
    G <- check_wf_env Σ ;;
    uctx <- check_udecl "toplevel term" Σ _ G.π1 (proj1 G.π2) φ ;;
    let G' := add_uctx uctx.π1 G.π1 in
    @infer_term (Σ, φ) (proj2 G.π2) Hφ G' _ (snd p).
  Next Obligation.
    (* todo: factorize with check_wf_env second obligation *)
    sq. unfold is_graph_of_uctx, gc_of_uctx; simpl.
    unfold gc_of_uctx in e. simpl in e.
    case_eq (gc_of_constraints (constraints_of_udecl φ));
      [|intro HH; rewrite HH in e; discriminate e].
    intros ctrs' Hctrs'. rewrite Hctrs' in e.
    cbn in e. inversion e; subst; clear e.
    unfold global_ext_constraints; simpl.
    rewrite gc_of_constraints_union. rewrite Hctrs'.
    red in i. unfold gc_of_uctx in i; simpl in i.
    case_eq (gc_of_constraints (global_constraints p.1));
      [|intro HH; rewrite HH in i; cbn in i; contradiction i].
    intros Σctrs HΣctrs; rewrite HΣctrs in i; simpl in *.
    subst G. unfold global_ext_levels; simpl. rewrite no_prop_levels_union.
    symmetry; apply add_uctx_make_graph.
  Qed.

End CheckEnv.

Definition principal_type {cf:checker_flags} Σ Γ t T :=
  forall T',
    Σ ;;; Γ |- t : T' ->
    Σ ;;; Γ |- T <= T'.

(*
Definition principal_sort {cf:checker_flags} Σ Γ t u :=
  forall u',
    Σ ;;; Γ |- t : tSort u' ->
    leq_universe Σ u u'.

Definition principal_prod {cf:checker_flags} Σ Γ t na A B :=
  forall na' A' B',
    Σ ;;; Γ |- t : tProd na' A' B' ->
    Σ ;;; Γ |- tProd na A B <= tProd na' A' B'.

Definition principal_ind {cf:checker_flags} Σ Γ t ind u args :=
  forall ind' u' args',
    Σ ;;; Γ |- t : mkApps (tInd ind' u') args' ->
    Σ ;;; Γ |- mkApps (tInd ind u) args <= mkApps (tInd ind' u') args'.
*)

Definition Pcheck {cf:checker_flags} Σ Γ t T :=
  (forall wfΣ onud G isg wfΓ T' isT,
      Σ ;;; Γ |- T <= T' ->
      match @infer_cumul _ Σ wfΣ onud G isg (@infer _ Σ wfΣ onud G isg) Γ wfΓ t T' isT with
      | Checked _ => True
      | TypeError _ => False
      end).

Definition Pinfer {cf:checker_flags} Σ Γ t (T : term) :=
  (forall wfΣ onud G isg wfΓ,
      match @infer _ Σ wfΣ onud G isg Γ wfΓ t with
      | Checked (T; _) => ∥principal_type Σ Γ t T∥
      | TypeError _ => False
      end).

Definition Psort {cf:checker_flags} Σ Γ t (u : Universe.t) :=
  (forall wfΣ onud G isg wfΓ,
      match @infer_type _ Σ wfΣ (@infer _ Σ wfΣ onud G isg) Γ wfΓ t with
      | Checked (u; _) => ∥principal_type Σ Γ t (tSort u)∥
      | TypeError _ => False
      end).

Definition Pprod {cf:checker_flags} Σ Γ t (na : aname) (A B : term) :=
  (forall wfΣ onud G isg wfΓ,
      match @infer_applicable _ Σ wfΣ (@infer _ Σ wfΣ onud G isg) Γ wfΓ t with
      | Checked (na; A; B; _) => ∥principal_type Σ Γ t (tProd na A B)∥
      | TypeError _ => False
      end).

Definition Pind {cf:checker_flags} Σ Γ (ind : inductive) t (u : Instance.t) (args : list term) :=
  (forall wfΣ onud G isg wfΓ,
      match @infer_constructor _ Σ wfΣ (@infer _ Σ wfΣ onud G isg) Γ wfΓ t with
      | Checked (ind; u; args; _) => ∥principal_type Σ Γ t (mkApps (tInd ind u) args)∥
      | TypeError _ => False
      end).

Definition PΓ (cf : checker_flags) (Σ : global_env_ext) (Γ : context)
           (wfΓ : BDMinimalTyping.All_local_env
                    (BDMinimalTyping.lift_sorting BDMinimalTyping.checking BDMinimalTyping.infering_sort Σ) Γ) :=
  True.

Ltac simpl_infer :=
  cbn -[infer_cumul infer_type infer_applicable infer_constructor].

Ltac specialize_IHs :=
  match goal with
  | [H: context[infer_cumul _ _ _ _ _ _ _ ?t _ _] |-
     context[infer_cumul ?wfΣ ?onud ?G ?isg ?inf ?Γ ?wfΓ ?t ?T ?isT]] =>
    specialize (H wfΣ onud G isg wfΓ T isT)
  | [H: context[infer _ _ _ _ _ _ ?t] |- context[infer ?wfΣ ?onud ?G ?isg ?Γ ?wfΓ ?t]] =>
    specialize (H wfΣ onud G isg wfΓ)
  | [H: context[infer_type _ _ _ _ ?T] |-
     context[infer_type ?wfΣ (infer ?wfΣ ?onud ?G ?isg) ?Γ ?wfΓ ?T]] =>
    specialize (H wfΣ onud G isg wfΓ)
  | [H: context[infer_applicable _ _ _ _ ?t] |-
     context[infer_applicable ?wfΣ (infer ?wfΣ ?onud ?G ?isg) ?Γ ?wfΓ ?t]] =>
    specialize (H wfΣ onud G isg wfΓ)
  | [H: context[infer_constructor _ _ _ _ ?t] |-
     context[infer_constructor ?wfΣ (infer ?wfΣ ?onud ?G ?isg) ?Γ ?wfΓ ?t]] =>
    specialize (H wfΣ onud G isg wfΓ)
  end.

Ltac tac :=
  simpl_infer;
  repeat
    match goal with
    | [H: context[infer_cumul _ _ _ _ _ _ _ ?t _ _] |-
       context[infer_cumul ?wfΣ ?onud ?G ?isg ?inf ?Γ ?wfΓ ?t ?T ?isT]] =>
      specialize (H wfΣ onud G isg wfΓ T isT)
    | [H: context[infer _ _ _ _ _ _ ?t] |- context[infer ?wfΣ ?onud ?G ?isg ?Γ ?wfΓ ?t]] =>
      specialize (H wfΣ onud G isg wfΓ);
      destruct (infer wfΣ onud G isg Γ wfΓ t) as [(?&?)|]; [|contradiction]
    | [H: context[infer_type _ _ _ _ ?T] |-
       context[infer_type ?wfΣ (infer ?wfΣ ?onud ?G ?isg) ?Γ ?wfΓ ?T]] =>
      specialize (H wfΣ onud G isg wfΓ);
      destruct (infer_type wfΣ (infer wfΣ onud G isg) Γ wfΓ T) as [(?&?)|]; [|contradiction]
    | [H: context[infer_applicable _ _ _ _ ?t] |-
       context[infer_applicable ?wfΣ (infer ?wfΣ ?onud ?G ?isg) ?Γ ?wfΓ ?t]] =>
      specialize (H wfΣ onud G isg wfΓ);
      destruct (infer_applicable wfΣ (infer wfΣ onud G isg) Γ wfΓ t) as [(?&?&?&?)|];
      [|contradiction]
    | [H: context[infer_constructor _ _ _ _ ?t] |-
       context[infer_constructor ?wfΣ (infer ?wfΣ ?onud ?G ?isg) ?Γ ?wfΓ ?t]] =>
      specialize (H wfΣ onud G isg wfΓ);
      destruct (infer_constructor wfΣ (infer wfΣ onud G isg) Γ wfΓ t) as [(?&?&?&?)|];
      [|contradiction]
    end.

Ltac program_rewrite eq :=
  match type of eq with
  | ?l = ?r =>
    match goal with
    | |- context[match ?l with _ => _ end (@eq_refl _ ?l)] =>
      let eqid := fresh "eq" in
      generalize (@eq_refl _ l); intros eqid;
      let lid := fresh "l" in
      set (lid := l) at 1; change (lid = l) in eqid;
      let efid := fresh "ef" in
      pose (efid := eq); symmetry in efid;
      change (r = lid) in efid;
      destruct efid
    end
  end.

Ltac program_destruct t :=
  let eqid := fresh "peq" in
  generalize (@eq_refl _ t);
  intros eqid;
  let pid := fresh "p" in
  set (pid := t) at 1;
  change (pid = t) in eqid;
  destruct pid.

Lemma cumul_Ind_Ind_inv {cf:checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ ind u args ind' u' args'} : 
  Σ ;;; Γ |- mkApps (tInd ind u) args <= mkApps (tInd ind' u') args' ->
  eq_inductive ind ind' *
  PCUICEquality.R_global_instance Σ (eq_universe Σ) (leq_universe Σ) (IndRef ind) #|args| u u' *
  All2 (conv Σ Γ) args args'.
Proof.
  intros cum.
  eapply invert_cumul_ind_l in cum as [ui' [l' [redl [ru conv]]]]; auto.
  eapply red_mkApps_tInd in redl as [args'' [eqind red']]; auto.
  apply mkApps_eq_inj in eqind as [eq ->]=> //; auto. noconf eq.
  intuition auto.
  eapply eq_inductive_refl.
  transitivity args''; auto.
  eapply All2_symmetry. typeclasses eauto.
  eapply (All2_impl red'). intros x y; apply red_conv.
Qed.

Arguments LevelSet.mem : simpl never.

Lemma declared_subst_instance_level inst l levels :
  LevelSet.In
    l
    (LevelSet.union
       (fold_right LevelSet.add LevelSet.empty (map Level.Var (seq 0 #|inst|)))
       levels) ->
  Forall (fun l => LevelSet.mem l levels) inst ->
  declared Level.lSet levels ->
  declared (subst_instance_level inst l) levels.
Proof.
  intros isin all declset.
  apply LevelSet.union_spec in isin.
  destruct l; cbn in *.
  - destruct isin; auto.
  - destruct isin; auto.
    clear -H.
    exfalso.
    revert H; generalize 0; induction #|inst|; intros ? H.
    + apply LevelSet.empty_spec in H; auto.
    + apply LevelSet.add_spec in H as [|]; eauto; discriminate.
  - rewrite nth_nth_error.
    destruct nth_error eqn:nth; auto.
    eapply nth_error_forall in nth; eauto.
    apply LevelSet.mem_spec; auto.
Qed.

Lemma mapi_seq {X Y} (f : nat -> X) (ys : list Y) :
  mapi (fun i _ => f i) ys = map f (seq 0 #|ys|).
Proof.
  unfold mapi.
  generalize 0.
  induction ys; intros n; auto.
  cbn; f_equal; auto.
Qed.

Lemma check_consistent_instance_complete {cf:checker_flags} Σ wfΣ udecl u onud G isg te :
  consistent_instance_ext Σ udecl u ->
  PCUICWeakeningEnv.on_udecl_prop Σ udecl ->
  @check_consistent_instance _ Σ wfΣ onud G isg udecl u = TypeError te ->
  False.
Proof.
  intros cons (cstrs&_).
  unfold check_consistent_instance in *.
  destruct udecl.
  - cbn in cons.
    destruct check_eq_nat eqn:c; [intros [=]|now rewrite cons in c].
  - cbn in cons.
    destruct cons as (?&?&?).
    destruct cst.
    destruct check_eq_true eqn:all_mem; cbn.
    2: { intros _.
         eapply forallb_impl in H.
         - erewrite H in all_mem; discriminate all_mem.
         - cbn.
           intros ? ? ?.
           eapply is_graph_of_uctx_levels; eauto. }
    destruct check_eq_nat eqn:len; cbn.
    2: { rewrite mapi_length H0 in len.
         cbn in len.
         unfold check_eq_nat in len.
         revert len.
         program_destruct (Nat.eq_dec #|l| #|l|); intros [=].
         congruence. }
    program_destruct (check_constraints G (subst_instance_cstrs u t));
      intros [=].
    change (global_ext_constraints Σ) with (global_ext_uctx Σ).2 in H1.
    eapply check_constraints_complete in H1; eauto.
    1: apply wf_ext_global_uctx_invariants; sq; eauto with pcuic.
    1: apply global_ext_uctx_consistent; sq; eauto with pcuic.
    intros c cin.
    apply PCUICUnivSubstitution.In_subst_instance_cstrs in cin as (?&->&?).
    cbn in *.
    apply cstrs in H2.
    destruct x as ((?&?)&?).
    cbn in *.
    apply forallb_Forall in H.
    rewrite mapi_seq in H2.
    rewrite <- H0 in H2.
    assert (declared Level.lSet (global_ext_levels Σ)).
    { apply LevelSet.union_spec; right.
      apply LevelSet.mem_spec, global_levels_Set. }
    split; apply declared_subst_instance_level; auto.
    1: destruct H2 as (isin&_).
    2: destruct H2 as (_&isin).
    all: apply LevelSet.union_spec.
    all: apply LevelSet.union_spec in isin as [|isin];
      [now auto|].
    all: right.
    all: apply LevelSet.union_spec; right; auto.
Qed.

Lemma convert_leq_complete {cf:checker_flags} Σ wfΣ onud G isg Γ t u wtt wtu te :
  @convert_leq _ Σ wfΣ onud G isg Γ t u wtt wtu = TypeError te ->
  Σ ;;; Γ |- t <= u ->
  False.
Proof.
  unfold convert_leq.
  program_destruct (leqb_term Σ G t u); [intros [=]|].
  unfold iscumul.
  program_destruct (isconv_term Σ wfΣ onud G isg Γ Cumul t wtt u wtu);
    [intros [=]|].
  intros _ cum.
  apply eq_sym, isconv_term_complete in peq0.
  apply sq, peq0 in cum; auto.
Qed.

Lemma check_fix_types_complete {cf:checker_flags} Σ wfΣ onud G isg Γ wfΓ mfix te :
  All (fun d =>
         ∑ u, BDMinimalTyping.infering_sort Σ Γ (dtype d) u
              × Psort Σ Γ (dtype d) u) mfix ->
  @check_fix_types _ Σ wfΣ (infer wfΣ onud G isg) Γ wfΓ mfix = TypeError te ->
  False.
Proof.
  funelim (check_fix_types _ _ _ _ _); intros all [=].
  - depelim all.
    destruct s as (u&infu&IH).
    red in IH.
    epose proof (IH _ _ _ _ _) as IH.
    now erewrite Heq in IH.
  - depelim all.
    eauto.
Qed.

Lemma check_fix_bodies_complete {cf:checker_flags} Σ wfΣ onud G isg Γ wfΓ mfix types te :
  All (fun d =>
         BDMinimalTyping.checking Σ (Γ,,, fix_context mfix) (dbody d)
                                  (lift0 #|fix_context mfix| (dtype d))
         × Pcheck Σ (Γ,,, fix_context mfix) (dbody d) (lift0 #|fix_context mfix| (dtype d)))
      mfix ->
  @check_fix_bodies _ Σ wfΣ onud G isg (infer wfΣ onud G isg) Γ wfΓ mfix types = TypeError te ->
  False.
Proof.
  unfold check_fix_bodies.
  generalize mfix at 1 2 3 4 6 8 10, types at 1.
  intros mfix' types'.
  funelim (check_fix_bodies_aux _ _ _ _ _ _ _ _ _ _ _); intros all [=].
  - destruct types as [types].
    depelim types.
    depelim all.
    destruct p as (checkbod&IH).
    red in IH.
    unshelve epose proof (IH _ _ _ _ _ _ _ _) as IH.
    9: erewrite Heq in IH; eauto.
    reflexivity.
  - destruct types as [types].
    depelim types.
    depelim all.
    eapply Hind; eauto.
Qed.

Lemma bd_completeness {cf:checker_flags} :
  BDMinimalTyping.env_prop Pcheck Pinfer Psort Pprod Pind PΓ.
Proof.
  apply BDMinimalTyping.typing_ind_env; intros;
    unfold Pcheck, Pinfer, Psort, Pprod, Pind, PΓ in *; intros.
  all: clear PΣ.
  - auto.
  - cbn.
    program_rewrite H.
    destruct wfΣ0.
    constructor.
    red.
    intros.
    eapply inversion_Rel in X0 as (?&?&?&?); auto.
    rewrite e in eq; noconf eq; auto.
  - unfold infer, infer_obligation_2.
    destruct (wf_universe_reflect Σ s); [|congruence].
    cbn.
    destruct wfΣ0.
    constructor; red; intros.
    eapply inversion_Sort in X0 as (?&?&?); auto.
  - tac.
    destruct wfΣ0.
    destruct s as [typs], H as [princt], s0 as [typb], H0 as [princb].
    constructor.
    intros T typ.
    eapply inversion_Prod in typ as (?&?&dom&cod&prod); auto.
    cbn.
    apply princt in dom.
    apply princb in cod.
    etransitivity; eauto.
    apply cumul_Sort_inv in dom.
    apply cumul_Sort_inv in cod.
    do 2 constructor.
    apply leq_universe_product_mon; auto.
  - tac.
    destruct wfΣ0, s0 as [typt], H as [princt], s1 as [typb], H0 as [princb].
    constructor; intros T typ.
    eapply inversion_Lambda in typ as (?&?&typt'&typb'&cum); auto.
    cbn.
    etransitivity; [|eassumption].
    eapply congr_cumul_prod; auto.
  - tac.
    specialize (H0 ltac:(reflexivity)).
    destruct infer_cumul; [|contradiction].
    tac.
    sq.
    intros ? typ.
    eapply inversion_LetIn in typ as (?&?&?&?&?&?); auto.
    etransitivity; [|eassumption].
    eapply cumul_LetIn_bo; eauto.
  - tac.
    destruct wfΣ0.
    destruct H as [princt], s as [typt].
    apply BDMinimalToPCUIC.bidirectional_to_PCUIC, princt in X; eauto with pcuic.
    apply cumul_Prod_Prod_inv in X as (?&?&?); auto.
    forward H0.
    { cbn.
      eapply conv_cumul; eauto.
      symmetry; auto. }
    destruct infer_cumul; [|easy].
    cbn in *.
    sq.
    intros T typ.
    apply inversion_App in typ as (?&?&?&typt'&?&?); auto.
    etransitivity; [|eassumption].
    eapply princt in typt'.
    eapply cumul_Prod_Prod_inv in typt' as (?&?&?); auto.
    eapply PCUICSubstitution.substitution_cumul0; eauto.
  - cbn.
    assert (isdecl := H).
    unfold BDMinimalTyping.declared_constant in H.
    program_destruct (lookup_env Σ.1 cst);
      rewrite <- peq in H; noconf H.
    cbn.
    destruct check_consistent_instance eqn:cons.
    2: { destruct wfΣ0.
         eapply check_consistent_instance_complete; eauto.
         symmetry in peq.
         eapply PCUICWeakeningEnv.weaken_lookup_on_global_env' in peq; eauto. }
    
    destruct wfΣ0.
    constructor.
    intros T typ.
    apply inversion_Const in typ as (?&?&?&?&?); auto.
    eapply PCUICWeakeningEnv.declared_constant_inj in isdecl; eauto.
    subst; auto.
  - simpl_infer.
    assert (isdecl := H).
    unfold BDMinimalTyping.declared_inductive, BDMinimalTyping.declared_minductive in H.
    destruct H as (look_mind&look_oib).
    unfold lookup_ind_decl.
    program_rewrite look_mind.
    program_rewrite look_oib.
    cbn.
    destruct check_consistent_instance eqn:cons.
    2: { destruct wfΣ0.
         eapply check_consistent_instance_complete; eauto.
         symmetry in eq.
         eapply PCUICWeakeningEnv.weaken_lookup_on_global_env' in eq; eauto. }
    destruct wfΣ0.
    constructor.
    intros T typ.
    apply inversion_Ind in typ as (?&?&?&isdecl'&?&?); auto.
    destruct (PCUICWeakeningEnv.declared_inductive_inj isdecl isdecl') as (->&->).
    auto.
  - simpl_infer.
    assert (isdecl := H).
    destruct H as ((look_mind&look_oib)&look_ctor).
    red in look_mind.
    unfold lookup_ind_decl.
    cbn in *.
    program_rewrite look_mind.
    program_rewrite look_oib.
    program_rewrite look_ctor.
    destruct check_consistent_instance eqn:cons.
    2: { destruct wfΣ0.
         eapply check_consistent_instance_complete; eauto.
         clear -eq w.
         symmetry in eq.
         eapply PCUICWeakeningEnv.weaken_lookup_on_global_env' in eq; eauto. }
    destruct wfΣ0.
    constructor.
    intros T typ.
    apply inversion_Construct in typ as (?&?&?&?&isdecl'&?&?); auto.
    destruct (PCUICWeakeningEnv.declared_constructor_inj isdecl isdecl') as (->&->&->).
    auto.
  - tac.
    destruct wfΣ0.
    destruct H0 as [princc].
    destruct s as [typc].
    apply BDMinimalToPCUIC.bidirectional_to_PCUIC in X0; eauto with pcuic.
    assert (cum_c := X0).
    eapply princc, cumul_Ind_Ind_inv in cum_c as ((?&?)&?); eauto.
    change (eq_inductive x ind) with (eqb x ind) in i.
    apply eqb_eq in i as ->.
    destruct check_eq_true eqn:eq.
    2: { rewrite eq_inductive_refl in eq; discriminate. }
    clear eq.
    assert (isdecl' := isdecl).
    destruct isdecl as (look_mind&look_oib).
    red in look_mind.
    unfold lookup_ind_decl.
    program_rewrite look_mind.
    program_rewrite look_oib.
    simpl_infer.
    destruct check_eq_true eqn:eq'.
    2: { rewrite H in eq'; discriminate eq'. }
    subst npar.
    destruct check_eq_true eqn:eq'' in |- *.
    2: { rewrite Nat.eqb_refl in eq''; discriminate eq''. }
    assert (ptyty: isType Σ Γ pty).
    { eapply PCUICInductiveInversion.WfArity_build_case_predicate_type; eauto.
      eapply validity; eauto. }
    specialize (H4 (sq w) onud G isg wfΓ pty (sq ptyty) ltac:(reflexivity)) as IH.
    unfold infer_cumul in IH.
    destruct infer; [|contradiction IH].
    destruct a3 as (P&[typp]).
    simpl_infer.
    cbn -[convert_leq] in IH.
    destruct convert_leq; [|contradiction IH].
    unfold reduce_to_arity_check.
    destruct reduce_to_arity eqn:red_ar.
    2: { cbn.
         clear red_ar.
         unshelve eapply build_case_predicate_type_spec in H3.
         2: eapply PCUICWeakeningEnv.on_declared_inductive; eauto.
         destruct H3 as (?&?&->).
         cbn in a3.
         destruct a3 as [cum].
         contradiction n.
         eapply invert_cumul_arity_r; eauto.
         apply isArity_it_mkProd_or_LetIn; auto. }
    cbn.
    destruct check_eq_true eqn:check_sort in |- *.
    2: { clear red_ar.
         assert (exists ctx', pty = it_mkProd_or_LetIn ctx' (tSort ps)) as (?&->).
         { unshelve eapply build_case_predicate_type_spec in H3.
           2: eapply PCUICWeakeningEnv.on_declared_inductive; eauto.
           destruct H3 as (?&?&->).
           eexists (vass _ _  :: _).
           reflexivity. }
         destruct a3 as [cum].
         eapply cumul_trans in cum; auto.
         forward cum.
         { eapply conv_cumul.
           eapply PCUICCanonicity.conv_it_mkProd_or_LetIn_smash. }
         destruct c0 as [c_ctx c_univ [c_red]]; cbn in *.
         eapply cumul_red_l_inv in cum; [| |eassumption]; auto.
         rewrite mkNormalArity_it_mkProd_or_LetIn in cum.
         apply it_mkProd_or_LetIn_ass_inv in cum as (?&?); auto; cycle 1.
         - clear.
           induction c_ctx as [|(?&?) ? IH] using MCList.rev_ind; cbn.
           + constructor.
           + rewrite rev_map_app; constructor; auto.
         - apply PCUICContexts.smash_context_assumption_context.
           constructor.
         - destruct onud.
           assert (wfext: wf_ext Σ) by eauto with pcuic.
           clear -l check_sort H5 wfext.
           depelim l.
           assert (leq := l).
           apply leq_universe_props in l; eauto.
           2: todo "incomplete, typing wrong?".
           destruct (ind_kelim idecl), c_univ, ps.
           all: cbn in *.
           all: try easy.
           + destruct UnivExprSet.for_all; discriminate.
           + destruct UnivExprSet.for_all; discriminate.
           + destruct UnivExprSet.for_all; discriminate.
           + todo "small".
           + todo "small". }
    
    todo "tCase".
  - simpl_infer.
    destruct p as ((?&?)&?).
    assert (isproj := H).
    destruct H as ((look_mind&look_oib)&look_proj&pars).
    red in look_mind.
    unfold lookup_ind_decl.
    program_rewrite look_mind.
    program_rewrite look_oib.
    cbn.
    program_rewrite look_proj.
    tac.
    cbn in *.
    subst n.
    clear X.
    destruct wfΣ0.
    destruct H0 as [princc], s as [typc].
    apply BDMinimalToPCUIC.bidirectional_to_PCUIC, princc in X0; eauto with pcuic.
    apply cumul_Ind_Ind_inv in X0 as ((ix&_)&conv_inf_deriv_args).
    change (is_true (eqb x i)) in ix.
    apply eqb_eq in ix as ->.
    destruct check_eq_true eqn:eq2.
    2: { rewrite eq_inductive_refl in eq2; discriminate. }
    destruct check_eq_true eqn:eq3 in |- *.
    2: { rewrite Nat.eqb_refl in eq3; discriminate. }
    destruct check_eq_true eqn:eq4 in |- *.
    2: { apply All2_length in conv_inf_deriv_args.
         rewrite conv_inf_deriv_args H1 Nat.eqb_refl in eq4.
         discriminate. }
    constructor.
    intros T typ.
    apply inversion_Proj in typ as (larger_inst&?&?&?&larger_args&isproj'&typc'&?&cum); auto.
    cbn in *.
    destruct (PCUICWeakeningEnv.declared_projection_inj isproj isproj') as (<-&<-&<-).
    red in isproj.
    assert (H := typc').
    apply princc, cumul_Ind_Ind_inv in H as ((_&larger_R)&conv_larger).
    set (proj := (i, ind_npars x, n0)).
    set (small_proj_ctx := projection_context x x2 proj.1.1 x0).
    set (large_proj_ctx := projection_context x x2 proj.1.1 larger_inst).
    assert (consistent_instance_ext Σ (ind_universes x) x0).
    { clear -w typc isproj.
      destruct isproj.
      apply validity_term in typc as (s&typ); auto.
      eapply invert_type_mkApps_ind in typ as (?&?); eauto. }
    assert (consistent_instance_ext Σ (ind_universes x) larger_inst).
    { clear -w typc' isproj.
      destruct isproj.
      apply validity_term in typc' as (s&typ); auto.
      eapply invert_type_mkApps_ind in typ as (?&?); eauto. }

    etransitivity; [|eassumption].
    eapply (subst_cumul _ small_proj_ctx large_proj_ctx []); auto.
    + eapply projection_subslet with (p := proj); eauto.
      cbn.
      eapply validity_term; eauto.
    + eapply projection_subslet with (p := proj); eauto.
      cbn.
      eapply validity_term; eauto.
    + constructor; auto.
      apply All2_rev; auto.
    + eapply weaken_wf_local; auto.
      eapply PCUICWeakening.weaken_wf_local; eauto with pcuic.
      eapply wf_projection_context with (p := proj); eauto.
    + eapply weaken_cumul with (Δ := Γ); auto.
      4: { apply PCUICInductiveInversion.projection_cumulative_indices; eauto.
           - eapply PCUICWeakeningEnv.weaken_lookup_on_global_env' in look_mind; auto.
           - clear eq4.
             apply Nat.eqb_eq in a1.
             rewrite <- a1; auto. }
      eapply PCUICClosed.closed_wf_local; eauto.
      * eapply wf_projection_context with (p := proj); eauto with pcuic.
      * cbn.
        autorewrite with len.
        cbn.
        eapply PCUICWeakeningEnv.on_declared_projection in isproj; eauto.
        rewrite isproj.(onNpars).
        rewrite PCUICClosed.closedn_subst_instance_constr.
        eapply PCUICClosed.declared_projection_closed; eauto.
      * cbn.
        autorewrite with len.
        cbn.
        eapply PCUICWeakeningEnv.on_declared_projection in isproj; eauto.
        rewrite isproj.(onNpars).
        rewrite PCUICClosed.closedn_subst_instance_constr.
        eapply PCUICClosed.declared_projection_closed; eauto.
  - simpl_infer.
    program_rewrite H0.
    destruct check_fix_types eqn:types.
    2: { eauto using check_fix_types_complete. }
    destruct check_fix_bodies eqn:bodies.
    2: { eapply check_fix_bodies_complete; [|eauto].
         eapply (All_impl X0).
         cbn.
         intros ? (?&?&?); auto. }
    destruct check_eq_true eqn:alllam.
    2: { assert (forallb (fun d => isLambda (dbody d)) mfix = true).
         - apply forallb_Forall, All_Forall.
           apply (All_impl X0).
           intros ? (?&?&?); auto.
         - rewrite H2 in alllam; discriminate. }
    destruct check_eq_true eqn:guard in |- *.
    2: { rewrite H in guard; discriminate. }
    destruct check_eq_true eqn:wffix in |- *.
    2: { rewrite H1 in wffix; discriminate. }
    destruct wfΣ0.
    constructor.
    intros T typ.
    apply inversion_Fix in typ as (?&?&?&?&?&?&?); auto.
    congruence.
  - simpl_infer.
    program_rewrite H0.
    destruct check_fix_types eqn:types.
    2: { eauto using check_fix_types_complete. }
    destruct check_fix_bodies eqn:bodies.
    2: { eauto using check_fix_bodies_complete. }
    destruct check_eq_true eqn:guard.
    2: { rewrite H in guard; discriminate. }
    destruct check_eq_true eqn:wffix in |- *.
    2: { rewrite H1 in wffix; discriminate. }
    destruct wfΣ0.
    constructor.
    intros T typ.
    apply inversion_CoFix in typ as (?&?&?&?&?&?&?); auto.
    congruence.
  - unfold infer_type.
    tac.
    destruct wfΣ0.
    destruct s as [typ].
    destruct H as [princx].
    apply BDMinimalToPCUIC.bidirectional_to_PCUIC, princx in X; eauto with pcuic.
    eapply cumul_red_r_inv in X; eauto.
    eapply invert_cumul_sort_r in X as (?&rsort&?).
    match goal with
    | |- context[reduce_to_sort ?a ?b ?c ?d] => program_destruct (reduce_to_sort a b c d)
    end.
    2: { eauto using reduce_to_sort_complete. }
    destruct a as (u'&[rsort']).
    constructor.
    intros T' typ'.
    apply princx in typ'.
    cbn in rsort'.
    eapply red_confluence in rsort as (?&(r1&r2)); eauto.
    apply invert_red_sort in r1 as ->.
    apply invert_red_sort in r2 as [= <-].
    cbn.
    etransitivity; eauto.
    eapply red_cumul_inv; auto.
  - unfold infer_applicable.
    specialize_IHs.
    program_destruct (infer wfΣ0 onud G isg Γ wfΓ t);
      rewrite <- peq in H; auto.
    destruct a as (T'&[typ']).
    destruct H as [princT'].
    match goal with
    | |- context[reduce_to_prod ?a ?b ?c ?d] => program_destruct (reduce_to_prod a b c d)
    end.
    2: { apply BDMinimalToPCUIC.bidirectional_to_PCUIC, princT' in X; eauto with pcuic.
         destruct wfΣ0.
         eapply cumul_red_r_inv in X; eauto.
         eapply invert_cumul_prod_r in X as (?&?&?&((rprod&?)&?)&?); auto.
         eauto using reduce_to_prod_complete. }
    destruct a as (na'&a&b&[rprod]).
    destruct wfΣ0.
    constructor.
    intros T'' typ''.
    apply princT' in typ''.
    etransitivity; eauto.
    eapply red_cumul_inv; auto.
  - unfold infer_constructor.
    specialize_IHs.
    program_destruct (infer wfΣ0 onud G isg Γ wfΓ t);
      rewrite <- peq in H; auto.
    destruct a as (T'&[typ']).
    destruct H as [princT'].
    match goal with
    | |- context[reduce_to_ind ?a ?b ?c ?d] => program_destruct (reduce_to_ind a b c d)
    end.
    2: { apply BDMinimalToPCUIC.bidirectional_to_PCUIC, princT' in X; eauto with pcuic.
         destruct wfΣ0.
         eapply cumul_red_r_inv in X; eauto.
         eapply invert_cumul_ind_r in X as (?&?&r&?&?); auto.
         eauto using reduce_to_ind_complete. }
    destruct a as (i&u&indargs&[rind]).
    destruct wfΣ0.
    constructor.
    intros T'' typ''.
    apply princT' in typ''.
    etransitivity; eauto.
    eapply red_cumul_inv; auto.
  - unfold infer_cumul.
    tac.
    cbn in *.
    destruct s, H as [princx].
    apply BDMinimalToPCUIC.bidirectional_to_PCUIC, princx in X; eauto with pcuic.
    destruct convert_leq eqn:conv; [now auto|].
    destruct wfΣ0.
    apply convert_leq_complete in conv; eauto.
    transitivity T; auto.
    transitivity T'; auto.
Qed.
