(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool List Arith Lia.
From MetaCoq.Template Require Import config monad_utils utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICPrincipality PCUICConfluence
     PCUICCumulativity PCUICSR PCUICPosition PCUICEquality PCUICNameless
     PCUICAlpha PCUICNormal PCUICInversion PCUICReduction PCUICSubstitution
     PCUICConversion PCUICContextConversion PCUICValidity PCUICCtxShape
     PCUICArities
     PCUICWeakeningEnv PCUICGeneration PCUICParallelReductionConfluence.

Require Import Equations.Prop.DepElim.
Derive Signature for red.
Import MonadNotation.

Local Set Keyed Unification.
Set Equations With UIP.

Set Default Goal Selector "!".
Require Import ssreflect ssrbool.


Inductive conv_pb :=
| Conv
| Cumul.

Definition conv_cum `{cf : checker_flags} leq Σ Γ u v :=
  match leq with
  | Conv => ∥ Σ ;;; Γ |- u = v ∥
  | Cumul => ∥ Σ ;;; Γ |- u <= v ∥
  end.

Lemma conv_conv_cum_l `{cf : checker_flags} :
  forall (Σ : global_env_ext) leq Γ u v, wf Σ ->
      Σ ;;; Γ |- u = v ->
      conv_cum leq Σ Γ u v.
Proof.
  intros Σ [] Γ u v h.
  - cbn. constructor. assumption.
  - cbn. constructor. now apply conv_cumul.
Qed.

Lemma conv_conv_cum_r `{cf : checker_flags} :
  forall (Σ : global_env_ext) leq Γ u v, wf Σ ->
      Σ ;;; Γ |- u = v ->
      conv_cum leq Σ Γ v u.
Proof.
  intros Σ [] Γ u v wfΣ h.
  - cbn. constructor. apply conv_sym; auto.
  - cbn. constructor. apply conv_cumul.
    now apply conv_sym.
Qed.

Global Instance conv_cum_refl {leq Γ} :
  RelationClasses.Reflexive (conv_cum leq Σ Γ).
Proof.
  destruct leq; constructor; reflexivity.
Qed.

Lemma conv_conv_cum {leq Γ u v} :
  ∥ Σ ;;; Γ |- u = v ∥ -> conv_cum leq Σ Γ u v.
Proof.
  intros h; destruct leq.
  - assumption.
  - destruct h. cbn.
    constructor. now eapply conv_cumul.
Qed.

Global Instance conv_cum_trans {leq Γ} :
  RelationClasses.Transitive (conv_cum leq Σ Γ).
Proof.
  intros u v w h1 h2. destruct leq; cbn in *; sq; etransitivity; eassumption.
Qed.

Lemma red_conv_cum_l {leq Γ u v} :
  red (fst Σ) Γ u v -> conv_cum leq Σ Γ u v.
Proof.
  induction 1.
  - reflexivity.
  - etransitivity; tea.
    destruct leq.
    + simpl. destruct IHX. constructor.
      eapply conv_red_l; eauto.
    + simpl. constructor.
      eapply cumul_red_l.
      * eassumption.
      * eapply cumul_refl'.
Qed.

Lemma red_conv_cum_r {leq Γ u v} :
  red (fst Σ) Γ u v -> conv_cum leq Σ Γ v u.
Proof.
  induction 1.
  - reflexivity.
  - etransitivity; tea.
    destruct leq.
    + simpl. destruct IHX. constructor.
      eapply conv_red_r; eauto.
    + simpl. constructor.
      eapply cumul_red_r.
      * eapply cumul_refl'.
      * assumption.
Qed.

Lemma conv_cum_Prod leq Γ na1 na2 A1 A2 B1 B2 :
  Σ ;;; Γ |- A1 = A2 ->
            conv_cum leq Σ (Γ,, vass na1 A1) B1 B2 ->
            conv_cum leq Σ Γ (tProd na1 A1 B1) (tProd na2 A2 B2).
Proof.
  intros h1 h2; destruct leq.
  - simpl in *. destruct h2 as [h2]. constructor.
    eapply conv_trans => //.
    + eapply conv_Prod_r. eassumption.
    + eapply conv_Prod_l. eassumption.
  - simpl in *. destruct h2 as [h2]. constructor.
    eapply cumul_trans.
    + auto.
    + eapply cumul_Prod_r. eassumption.
    + eapply conv_cumul. eapply conv_Prod_l. assumption.
Qed.

Lemma conv_cum_Lambda leq Γ na1 na2 A1 A2 t1 t2 :
  Σ ;;; Γ |- A1 = A2 ->
            conv_cum leq Σ (Γ ,, vass na1 A1) t1 t2 ->
            conv_cum leq Σ Γ (tLambda na1 A1 t1) (tLambda na2 A2 t2).
Proof.
  intros X H. destruct leq; cbn in *; sq.
  - etransitivity.
    + eapply conv_Lambda_r. eassumption.
    + now eapply conv_Lambda_l.
  - etransitivity.
    + eapply cumul_Lambda_r. eassumption.
    + eapply conv_cumul, conv_Lambda_l; tea.
Qed.

Lemma conv_cum_LetIn leq Γ na1 na2 t1 t2 A1 A2 u1 u2 :
  Σ;;; Γ |- t1 = t2 ->
           Σ;;; Γ |- A1 = A2 ->
                    conv_cum leq Σ (Γ ,, vdef na1 t1 A1) u1 u2 ->
                    conv_cum leq Σ Γ (tLetIn na1 t1 A1 u1) (tLetIn na2 t2 A2 u2).
Proof.
  intros X H H'. destruct leq; cbn in *; sq.
  - etransitivity.
    + eapply conv_LetIn_bo. eassumption.
    + etransitivity.
      * eapply conv_LetIn_tm. eassumption.
      * eapply conv_LetIn_ty with (na := na1). assumption.
  - etransitivity.
    + eapply cumul_LetIn_bo. eassumption.
    + etransitivity.
      * eapply conv_cumul, conv_LetIn_tm; tea.
      * eapply conv_cumul, conv_LetIn_ty with (na := na1); tea.
Qed.

Lemma conv_cum_conv_ctx leq Γ Γ' T U :
  conv_cum leq Σ Γ T U ->
  conv_context Σ Γ Γ' ->
  conv_cum leq Σ Γ' T U.
Proof.
  destruct leq; cbn; intros; sq.
  - eapply conv_conv_ctx; eassumption.
  - eapply cumul_conv_ctx; eassumption.
Qed.


Lemma it_mkLambda_or_LetIn_conv_cum leq Γ Δ1 Δ2 t1 t2 :
  conv_context Σ (Γ ,,, Δ1) (Γ ,,, Δ2) ->
  conv_cum leq Σ (Γ ,,, Δ1) t1 t2 ->
  conv_cum leq Σ Γ (it_mkLambda_or_LetIn Δ1 t1) (it_mkLambda_or_LetIn Δ2 t2).
Proof.
  induction Δ1 in Δ2, t1, t2 |- *; intros X Y.
  - apply context_relation_length in X.
    destruct Δ2; cbn in *; [trivial|].
    rewrite app_length in X; lia.
  - apply context_relation_length in X as X'.
    destruct Δ2 as [|c Δ2]; simpl in *; [rewrite app_length in X'; lia|].
    dependent destruction X.
    + eapply IHΔ1; tas; cbn.
      inv c0. eapply conv_cum_Lambda; tea.
    + eapply IHΔ1; tas; cbn.
      inversion c0; subst; eapply conv_cum_LetIn; auto.
Qed.

Lemma Lambda_conv_cum_inv :
  forall leq Γ na1 na2 A1 A2 b1 b2,
    wf_local Σ Γ ->
    conv_cum leq Σ Γ (tLambda na1 A1 b1) (tLambda na2 A2 b2) ->
    ∥ Σ ;;; Γ |- A1 = A2 ∥ /\ conv_cum leq Σ (Γ ,, vass na1 A1) b1 b2.
Proof.
  intros * wfΓ.
  destruct leq; simpl in *.
  - destruct 1.
    eapply conv_alt_red in X as [l [r [[redl redr] eq]]].
    eapply red_lambda_inv in redl as [A1' [b1' [[-> ?] ?]]].
    eapply red_lambda_inv in redr as [A2' [b2' [[-> ?] ?]]].
    depelim eq. assert (Σ ;;; Γ |- A1 = A2).
    { eapply conv_trans with A1'; auto.
      eapply conv_trans with A2'; auto.
      - constructor. assumption.
      - apply conv_sym; auto.
    }
    split; constructor; auto.
    eapply conv_trans with b1'; auto.
    eapply conv_trans with b2'; auto.
    + constructor; auto.
    + apply conv_sym; auto.
      eapply conv_conv_ctx; eauto.
      constructor; auto. 1: reflexivity.
      constructor. now apply conv_sym.
  - destruct 1.
    eapply cumul_alt in X as [l [r [[redl redr] eq]]].
    eapply red_lambda_inv in redl as [A1' [b1' [[-> ?] ?]]].
    eapply red_lambda_inv in redr as [A2' [b2' [[-> ?] ?]]].
    depelim eq.
    assert (Σ ;;; Γ |- A1 = A2).
    { eapply conv_trans with A1'; auto.
      eapply conv_trans with A2'; auto.
      - constructor. assumption.
      - apply conv_sym; auto.
    }
    split; constructor; auto.
    eapply red_cumul_cumul; tea.
    eapply cumul_trans with b2'; auto.
    + constructor; auto.
    + eapply cumul_conv_ctx; tas.
      * eapply red_cumul_cumul_inv; tea.
        reflexivity.
      * symmetry in X.
        constructor. 1: reflexivity.
        now constructor.
Qed.



Definition nodelta_flags := RedFlags.mk true true true false true true.

(* TODO MOVE *)
Lemma All2_app_inv_both :
  forall A B (P : A -> B -> Type) l1 l2 r1 r2,
    #|l1| = #|r1| ->
    All2 P (l1 ++ l2) (r1 ++ r2) ->
    All2 P l1 r1 × All2 P l2 r2.
Proof.
  intros A B P l1 l2 r1 r2 e h.
  apply All2_app_inv in h as [[w1 w2] [[e1 h1] h2]].
  assert (e2 : r1 = w1 × r2 = w2).
  { apply All2_length in h1. rewrite h1 in e.
    clear - e e1.
    induction r1 in r2, w1, w2, e, e1 |- *.
    - destruct w1. 2: discriminate.
      intuition eauto.
    - destruct w1. 1: discriminate.
      simpl in e. apply Nat.succ_inj in e.
      simpl in e1. inversion e1. subst.
      eapply IHr1 in e. 2: eassumption.
      intuition eauto. f_equal. assumption.
  }
  destruct e2 as [? ?]. subst.
  intuition auto.
Qed.

Lemma strengthening `{cf : checker_flags} :
  forall {Σ Γ Γ' Γ'' t T},
    wf Σ.1 ->
    Σ ;;; Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ'
    |- lift #|Γ''| #|Γ'| t : lift #|Γ''| #|Γ'| T ->
    Σ;;; Γ ,,, Γ' |- t : T.
Admitted.

Section Lemmata.
  Context {cf : checker_flags}.
  Context (flags : RedFlags.t).

  Lemma eq_term_zipc_inv :
    forall φ u v π,
      eq_term φ (zipc u π) (zipc v π) ->
      eq_term φ u v.
  Proof.
    intros Σ u v π h.
    induction π in u, v, h |- *.
    all: try solve [
             simpl in h ; try apply IHπ in h ;
             cbn in h ; inversion h ; subst ; assumption
           ].
    - simpl in h. apply IHπ in h.
      inversion h. subst.
      match goal with
      | h : All2 _ _ _ |- _ => rename h into a
      end.
      apply All2_app_inv_both in a. 2: reflexivity.
      destruct a as [_ a]. inversion a. subst.
      intuition eauto.
    - simpl in h. apply IHπ in h.
      inversion h. subst.
      match goal with
      | h : All2 _ _ _ |- _ => rename h into a
      end.
      apply All2_app_inv_both in a. 2: reflexivity.
      destruct a as [_ a]. inversion a. subst.
      intuition eauto.
    - simpl in h. apply IHπ in h.
      inversion h. subst.
      match goal with
      | h : All2 _ _ _ |- _ => rename h into a
      end.
      apply All2_app_inv_both in a. 2: reflexivity.
      destruct a as [_ a]. inversion a. subst.
      intuition eauto.
  Qed.

  Lemma eq_term_zipx_inv :
    forall φ Γ u v π,
      eq_term φ (zipx Γ u π) (zipx Γ v π) ->
      eq_term φ u v.
  Proof.
    intros Σ Γ u v π h.
    eapply eq_term_zipc_inv.
    eapply eq_term_it_mkLambda_or_LetIn_inv.
    eassumption.
  Qed.

  Lemma eq_term_upto_univ_zipc :
    forall Re u v π,
      RelationClasses.Reflexive Re ->
      eq_term_upto_univ Re Re u v ->
      eq_term_upto_univ Re Re (zipc u π) (zipc v π).
  Proof.
    intros Re u v π he h.
    induction π in u, v, h |- *.
    all: try solve [
               simpl ; try apply IHπ ;
               cbn ; constructor ; try apply eq_term_upto_univ_refl ; assumption
             ].
    - assumption.
    - simpl. apply IHπ. constructor.
      apply All2_app.
      + apply All2_same.
        intros. split ; auto. split. all: apply eq_term_upto_univ_refl.
        all: assumption.
      + constructor.
        * simpl. intuition eauto. reflexivity.
        * apply All2_same.
          intros. split ; auto. split. all: apply eq_term_upto_univ_refl.
          all: assumption.
    - simpl. apply IHπ. constructor.
      apply All2_app.
      + apply All2_same.
        intros. split ; auto. split. all: apply eq_term_upto_univ_refl.
        all: assumption.
      + constructor.
        * simpl. intuition eauto. reflexivity.
        * apply All2_same.
          intros. split ; auto. split. all: apply eq_term_upto_univ_refl.
          all: assumption.
    - simpl. apply IHπ. destruct indn as [i n].
      constructor.
      + assumption.
      + apply eq_term_upto_univ_refl. all: assumption.
      + eapply All2_same.
        intros. split ; auto. apply eq_term_upto_univ_refl. all: assumption.
    - simpl. apply IHπ. destruct indn as [i n].
      constructor.
      + apply eq_term_upto_univ_refl. all: assumption.
      + assumption.
      + eapply All2_same.
        intros. split ; auto. apply eq_term_upto_univ_refl. all: assumption.
    - simpl. apply IHπ. destruct indn as [i n].
      constructor.
      + apply eq_term_upto_univ_refl. all: assumption.
      + apply eq_term_upto_univ_refl. all: assumption.
      + apply All2_app.
        * eapply All2_same.
          intros. split ; auto. apply eq_term_upto_univ_refl. all: assumption.
        * constructor.
          -- simpl. intuition eauto.
          -- eapply All2_same.
             intros. split ; auto. apply eq_term_upto_univ_refl.
             all: assumption.
  Qed.

  Lemma eq_term_zipc :
    forall (Σ : global_env_ext) u v π,
      eq_term (global_ext_constraints Σ) u v ->
      eq_term (global_ext_constraints Σ) (zipc u π) (zipc v π).
  Proof.
    intros Σ u v π h.
    eapply eq_term_upto_univ_zipc.
    - intro. eapply eq_universe_refl.
    - assumption.
  Qed.

  Lemma eq_term_upto_univ_zipp :
    forall Re u v π,
      RelationClasses.Reflexive Re ->
      eq_term_upto_univ Re Re u v ->
      eq_term_upto_univ Re Re (zipp u π) (zipp v π).
  Proof.
    intros Re u v π he h.
    unfold zipp.
    case_eq (decompose_stack π). intros l ρ e.
    eapply eq_term_upto_univ_mkApps.
    - assumption.
    - apply All2_same. intro. reflexivity.
  Qed.

  Lemma eq_term_zipp :
    forall (Σ : global_env_ext) u v π,
      eq_term (global_ext_constraints Σ) u v ->
      eq_term (global_ext_constraints Σ) (zipp u π) (zipp v π).
  Proof.
    intros Σ u v π h.
    eapply eq_term_upto_univ_zipp.
    - intro. eapply eq_universe_refl.
    - assumption.
  Qed.

  Lemma eq_term_upto_univ_zipx :
    forall Re Γ u v π,
      RelationClasses.Reflexive Re ->
      eq_term_upto_univ Re Re u v ->
      eq_term_upto_univ Re Re (zipx Γ u π) (zipx Γ v π).
  Proof.
    intros Re Γ u v π he h.
    eapply eq_term_upto_univ_it_mkLambda_or_LetIn ; auto.
    eapply eq_term_upto_univ_zipc ; auto.
  Qed.

  Lemma eq_term_zipx :
    forall φ Γ u v π,
      eq_term φ u v ->
      eq_term φ (zipx Γ u π) (zipx Γ v π).
  Proof.
    intros Σ Γ u v π h.
    eapply eq_term_upto_univ_zipx ; auto.
    intro. eapply eq_universe_refl.
  Qed.


  (* red is the reflexive transitive closure of one-step reduction and thus
     can't be used as well order. We thus define the transitive closure,
     but we take the symmetric version.
   *)
  Inductive cored Σ Γ: term -> term -> Prop :=
  | cored1 : forall u v, red1 Σ Γ u v -> cored Σ Γ v u
  | cored_trans : forall u v w, cored Σ Γ v u -> red1 Σ Γ v w -> cored Σ Γ w u.

  Derive Signature for cored.

  Hint Resolve eq_term_upto_univ_refl : core.

  (* Lemma conv_context : *)
  (*   forall Σ Γ u v ρ, *)
  (*     wf Σ.1 -> *)
  (*     Σ ;;; Γ ,,, stack_context ρ |- u = v -> *)
  (*     Σ ;;; Γ |- zipc u ρ = zipc v ρ. *)
  (* Proof. *)
  (*   intros Σ Γ u v ρ hΣ h. *)
  (*   induction ρ in u, v, h |- *. *)
  (*   - assumption. *)
  (*   - simpl. eapply IHρ. eapply conv_App_l ; auto. *)
  (*   - simpl. eapply IHρ. eapply conv_App_r ; auto. *)
  (*   - simpl. eapply IHρ. eapply conv_App_r ; auto. *)
  (*   - simpl. eapply IHρ. eapply conv_Case_c ; auto. *)
  (*   - simpl. eapply IHρ. eapply conv_Proj_c ; auto. *)
  (*   - simpl. eapply IHρ. eapply conv_Prod_l ; auto. *)
  (*   - simpl. eapply IHρ. eapply conv_Prod_r ; auto. *)
  (*   - simpl. eapply IHρ. eapply conv_Lambda_l ; auto. *)
  (*   - simpl. eapply IHρ. eapply conv_Lambda_r ; auto. *)
  (*   - simpl. eapply IHρ. eapply conv_App_r ; auto. *)
  (* Qed. *)

  Context (Σ : global_env_ext).

  Inductive welltyped Σ Γ t : Prop :=
  | iswelltyped A : Σ ;;; Γ |- t : A -> welltyped Σ Γ t.

  Arguments iswelltyped {Σ Γ t A} h.

  Definition wellformed Σ Γ t :=
    welltyped Σ Γ t \/ ∥ isWfArity typing Σ Γ t ∥.

  (* Here we use use the proof irrelevance axiom to show that wellformed is really squashed.
     Using SProp would avoid this.
   *)

  Lemma wellformed_irr :
    forall {Σ Γ t} (h1 h2 : wellformed Σ Γ t), h1 = h2.
  Proof. intros. apply ProofIrrelevance.proof_irrelevance. Qed.

  Context (hΣ : ∥ wf Σ ∥).

  Lemma welltyped_alpha Γ u v :
      welltyped Σ Γ u ->
      eq_term_upto_univ eq eq u v ->
      welltyped Σ Γ v.
  Proof.
    intros [A h] e.
    destruct hΣ.
    exists A. eapply typing_alpha ; eauto.
  Qed.

  Lemma wellformed_alpha Γ u v :
      wellformed Σ Γ u ->
      eq_term_upto_univ eq eq u v ->
      wellformed Σ Γ v.
  Proof.
    destruct hΣ as [hΣ'].
    intros [X|X] e; [left|right].
    - destruct X as [A Hu]. eexists. eapply typing_alpha; tea.
    - destruct X. constructor.
      now eapply isWfArity_alpha.
  Qed.


  Lemma red_cored_or_eq :
    forall Γ u v,
      red Σ Γ u v ->
      cored Σ Γ v u \/ u = v.
  Proof.
    intros Γ u v h.
    induction h.
    - right. reflexivity.
    - destruct IHh.
      + left. eapply cored_trans ; eassumption.
      + subst. left. constructor. assumption.
  Qed.

  Lemma cored_it_mkLambda_or_LetIn :
    forall Γ Δ u v,
      cored Σ (Γ ,,, Δ) u v ->
      cored Σ Γ (it_mkLambda_or_LetIn Δ u)
               (it_mkLambda_or_LetIn Δ v).
  Proof.
    intros Γ Δ u v h.
    induction h.
    - constructor. apply red1_it_mkLambda_or_LetIn. assumption.
    - eapply cored_trans.
      + eapply IHh.
      + apply red1_it_mkLambda_or_LetIn. assumption.
  Qed.

  Lemma cored_welltyped :
    forall {Γ u v},
      welltyped Σ Γ u ->
      cored (fst Σ) Γ v u ->
      welltyped Σ Γ v.
  Proof.
    destruct hΣ as [wΣ]; clear hΣ.
    intros Γ u v h r.
    revert h. induction r ; intros h.
    - destruct h as [A h]. exists A.
      eapply subject_reduction1 ; eauto with wf.
    - specialize IHr with (1 := ltac:(eassumption)).
      destruct IHr as [A ?]. exists A.
      eapply subject_reduction1 ; eauto with wf.
  Qed.

  Lemma cored_trans' :
    forall {Γ u v w},
      cored Σ Γ u v ->
      cored Σ Γ v w ->
      cored Σ Γ u w.
  Proof.
    intros Γ u v w h1 h2. revert w h2.
    induction h1 ; intros z h2.
    - eapply cored_trans ; eassumption.
    - eapply cored_trans.
      + eapply IHh1. assumption.
      + assumption.
  Qed.

  (* This suggests that this should be the actual definition.
     ->+ = ->*.->
   *)
  Lemma cored_red_trans :
    forall Γ u v w,
      red Σ Γ u v ->
      red1 Σ Γ v w ->
      cored Σ Γ w u.
  Proof.
    intros Γ u v w h1 h2.
    revert w h2. induction h1 ; intros w h2.
    - constructor. assumption.
    - eapply cored_trans.
      + eapply IHh1. eassumption.
      + assumption.
  Qed.

  Lemma cored_case :
    forall Γ ind p c c' brs,
      cored Σ Γ c c' ->
      cored Σ Γ (tCase ind p c brs) (tCase ind p c' brs).
  Proof.
    intros Γ ind p c c' brs h.
    revert ind p brs. induction h ; intros ind p brs.
    - constructor. constructor. assumption.
    - eapply cored_trans.
      + eapply IHh.
      + econstructor. assumption.
  Qed.

  Lemma welltyped_context :
    forall Γ t,
      welltyped Σ Γ (zip t) ->
      welltyped Σ (Γ ,,, stack_context (snd t)) (fst t).
  Proof.
    destruct hΣ as [wΣ].
    intros Γ [t π] h. simpl.
    destruct h as [T h].
    induction π in Γ, t, T, h |- *.
    - cbn. cbn in h. eexists. eassumption.
    - simpl. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [B h].
      apply inversion_App in h as hh ; auto.
      destruct hh as [na [A' [B' [? [? ?]]]]].
      eexists. eassumption.
    - simpl. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [B h].
      apply inversion_App in h as hh ; auto.
      destruct hh as [na [A' [B' [? [? ?]]]]].
      eexists. eassumption.
    - simpl. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [B h].
      apply inversion_Fix in h as hh. 2: assumption.
      destruct hh as [decl [? [? [hw [? ?]]]]].
      apply typing_wf_local in h.
      clear -h hw wΣ.
      eapply PCUICWeakening.All_mfix_wf in hw; eauto.
      clear h.
      rewrite fix_context_fix_context_alt in hw.
      rewrite map_app in hw. simpl in hw.
      unfold def_sig at 2 in hw. simpl in hw.
      unfold fix_context_alt in hw.
      rewrite mapi_app in hw.
      rewrite rev_app_distr in hw.
      simpl in hw.
      rewrite !app_context_assoc in hw.
      apply wf_local_app in hw.
      match type of hw with
      | context [ List.rev ?l ] =>
        set (Δ := List.rev l) in *
      end.
      assert (e : #|Δ| = #|mfix1|).
      { subst Δ. rewrite List.rev_length.
        rewrite mapi_length. rewrite map_length.
        reflexivity.
      }
      rewrite map_length in hw. rewrite <- e in hw.
      clearbody Δ. clear e.
      replace (#|Δ| + 0) with #|Δ| in hw by lia.
      set (Γ' := Γ ,,, stack_context π) in *.
      clearbody Γ'. clear Γ. rename Γ' into Γ.
      rewrite <- app_context_assoc in hw.
      inversion hw. subst.
      match goal with
      | hh : lift_typing _ _ _ _ _ |- _ => rename hh into h
      end.
      simpl in h. destruct h as [s h].
      exists (tSort s).
      eapply @strengthening with (Γ' := []). 1: assumption.
      exact h.
    - simpl. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [B h].
      apply inversion_Fix in h as hh. 2: assumption.
      destruct hh as [decl [? [? [? [ha ?]]]]].
      clear - ha wΣ.
      apply All_app in ha as [_ ha].
      inversion ha. subst.
      intuition eauto. simpl in *.
      match goal with
      | hh : _ ;;; _ |- _ : _ |- _ => rename hh into h
      end.
      rewrite fix_context_length in h.
      rewrite app_length in h. simpl in h.
      rewrite fix_context_fix_context_alt in h.
      rewrite map_app in h. simpl in h.
      unfold def_sig at 2 in h. simpl in h.
      rewrite <- app_context_assoc in h.
      eexists. eassumption.
    - simpl. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [B h].
      apply inversion_App in h as hh ; auto.
      destruct hh as [na [A' [B' [? [? ?]]]]].
      eexists. eassumption.
    - simpl. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [B h].
      destruct indn.
      apply inversion_Case in h as hh ; auto.
      destruct hh as [uni [args [mdecl [idecl [ps [pty [btys
                                 [? [? [? [? [? [? [ht0 [? ?]]]]]]]]]]]]]]].
      eexists. eassumption.
    - simpl. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [B h].
      destruct indn.
      apply inversion_Case in h as hh ; auto.
      destruct hh as [uni [args [mdecl [idecl [ps [pty [btys
                                 [? [? [? [? [? [? [ht0 [? ?]]]]]]]]]]]]]]].
      eexists. eassumption.
    - simpl. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [B h].
      destruct indn.
      apply inversion_Case in h as hh ; auto.
      destruct hh as [uni [args [mdecl [idecl [ps [pty [btys
                                 [? [? [? [? [? [? [ht0 [? ?]]]]]]]]]]]]]]].
      apply All2_app_inv in a as [[? ?] [[? ?] ha]].
      inversion ha. subst.
      intuition eauto. simpl in *.
      eexists. eassumption.
    - simpl. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [T' h].
      apply inversion_Proj in h
        as [uni [mdecl [idecl [pdecl [args [? [? [? ?]]]]]]]] ; auto.
      eexists. eassumption.
    - simpl. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [T' h].
      apply inversion_Prod in h as hh ; auto.
      destruct hh as [s1 [s2 [? [? ?]]]].
      eexists. eassumption.
    - cbn. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [T' h].
      apply inversion_Prod in h as hh ; auto.
      destruct hh as [s1 [s2 [? [? ?]]]].
      eexists. eassumption.
    - cbn. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [T' h].
      apply inversion_Lambda in h as hh ; auto.
      destruct hh as [s1 [B [? [? ?]]]].
      eexists. eassumption.
    - cbn. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [T' h].
      apply inversion_Lambda in h as hh ; auto.
      destruct hh as [s1 [B [? [? ?]]]].
      eexists. eassumption.
    - cbn. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [U h].
      apply inversion_LetIn in h as [s [A [? [? [? ?]]]]]. 2: auto.
      eexists. eassumption.
    - cbn. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [U h].
      apply inversion_LetIn in h as [s [A [? [? [? ?]]]]]. 2: auto.
      eexists. eassumption.
    - cbn. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [U h].
      apply inversion_LetIn in h as [s [A [? [? [? ?]]]]]. 2: auto.
      eexists. eassumption.
    - cbn. cbn in h. cbn in IHπ. apply IHπ in h.
      destruct h as [B h].
      apply inversion_App in h as hh ; auto.
      destruct hh as [na [A' [B' [? [? ?]]]]].
      eexists. eassumption.
  Qed.

  Lemma wellformed_context :
    forall Γ t,
      wellformed Σ Γ (zip t) ->
      wellformed Σ (Γ ,,, stack_context (snd t)) (fst t).
  Proof.
    destruct hΣ as [wΣ].
    intros Γ [t π] [[A h]|h].
    - destruct (welltyped_context Γ (t, π) (iswelltyped h)) as [? ?].
      left. econstructor. eassumption.
    - simpl. induction π in t, h |- *.
      all: try (specialize (IHπ _ h)).
      all: simpl in *.
      1: right ; assumption.
      all: destruct IHπ as [[A' h'] | [[Δ [s [h1 h2]]]]] ; [| try discriminate].
      all: try solve [
        apply inversion_App in h' ; auto ;
        rdestruct h' ;
        left ; econstructor ; eassumption
      ].
      + assert (hwf := typing_wf_local h').
        apply inversion_Fix in h'. 2: assumption.
        destruct h' as [decl [? [? [hw [? ?]]]]].
        apply PCUICWeakening.All_mfix_wf in hw; eauto.
        clear - hw wΣ.
        rewrite fix_context_fix_context_alt in hw.
        rewrite map_app in hw. simpl in hw.
        unfold def_sig at 2 in hw. simpl in hw.
        unfold fix_context_alt in hw.
        rewrite mapi_app in hw.
        rewrite rev_app_distr in hw.
        simpl in hw.
        rewrite !app_context_assoc in hw.
        apply wf_local_app in hw.
        match type of hw with
        | context [ List.rev ?l ] =>
          set (Δ := List.rev l) in *
        end.
        assert (e : #|Δ| = #|mfix1|).
        { subst Δ. rewrite List.rev_length.
          rewrite mapi_length. rewrite map_length.
          reflexivity.
        }
        rewrite map_length in hw. rewrite <- e in hw.
        clearbody Δ. clear e.
        replace (#|Δ| + 0) with #|Δ| in hw by lia.
        set (Γ' := Γ ,,, stack_context π) in *.
        clearbody Γ'. clear Γ. rename Γ' into Γ.
        rewrite <- app_context_assoc in hw.
        inversion hw. subst.
        match goal with
        | hh : lift_typing _ _ _ _ _ |- _ => rename hh into h
        end.
        simpl in h. destruct h as [s h].
        left. exists (tSort s).
        eapply @strengthening with (Γ' := []). 1: assumption.
        exact h.
      + apply inversion_Fix in h'. 2: assumption.
        destruct h' as [decl [? [? [? [ha ?]]]]].
        clear - ha wΣ.
        apply All_app in ha as [_ ha].
        inversion ha. subst.
        intuition eauto. simpl in *.
        match goal with
        | hh : _ ;;; _ |- _ : _ |- _ => rename hh into h
        end.
        rewrite fix_context_length in h.
        rewrite app_length in h. simpl in h.
        rewrite fix_context_fix_context_alt in h.
        rewrite map_app in h. simpl in h.
        unfold def_sig at 2 in h. simpl in h.
        rewrite <- app_context_assoc in h.
        left. eexists. eassumption.
      + destruct indn.
        apply inversion_Case in h' ; auto. cbn in h'. rdestruct h'.
        left. econstructor. eassumption.
      + destruct indn.
        apply inversion_Case in h' ; auto. cbn in h'. rdestruct h'.
        left. econstructor. eassumption.
      + destruct indn.
        apply inversion_Case in h' ; auto. cbn in h'. rdestruct h'.
        match goal with
        | h : All2 _ _ _ |- _ => rename h into a
        end.
        apply All2_app_inv in a as [[? ?] [[? ?] ha]].
        inversion ha. subst. intuition eauto.
        simpl in *.
        left. econstructor. eassumption.
      + apply inversion_Proj in h' ; auto.
        cbn in h'. rdestruct h'.
        left. eexists. eassumption.
      + apply inversion_Prod in h' ; auto. rdestruct h'.
        left. eexists. eassumption.
      + cbn in h1. apply destArity_app_Some in h1 as [Δ' [h1 h1']].
        subst. left. rewrite app_context_assoc in h2. cbn in *.
        apply wf_local_app in h2. inversion h2. subst. cbn in *.
        destruct X0. eexists. eassumption.
      + apply inversion_Prod in h' ; auto. rdestruct h'.
        left. eexists. eassumption.
      + cbn in h1. apply destArity_app_Some in h1 as [Δ' [h1 h1']].
        subst. right. constructor. exists Δ', s.
        rewrite app_context_assoc in h2. cbn in h2.
        split ; eauto.
      + apply inversion_Lambda in h' ; auto. rdestruct h'.
        left. eexists. eassumption.
      + apply inversion_Lambda in h' ; auto. rdestruct h'.
        left. eexists. eassumption.
      + apply inversion_LetIn in h'. 2: auto. rdestruct h'.
        left. eexists. eassumption.
      + cbn in h1. apply destArity_app_Some in h1 as [Δ' [h1 h1']].
        subst. rewrite app_context_assoc in h2. simpl in h2.
        left. apply wf_local_app in h2.
        inversion h2. subst. cbn in *.
        eexists. eassumption.
      + apply inversion_LetIn in h'. 2: auto. rdestruct h'.
        left. eexists. eassumption.
      + cbn in h1. apply destArity_app_Some in h1 as [Δ' [h1 h1']].
        subst. rewrite app_context_assoc in h2. simpl in h2.
        left. apply wf_local_app in h2.
        inversion h2. subst. cbn in *.
        match goal with
        | h : ∃ s : Universe.t, _ |- _ =>
          destruct h
        end.
        eexists. eassumption.
      + apply inversion_LetIn in h'. 2: auto. rdestruct h'.
        left. eexists. eassumption.
      + cbn in h1. apply destArity_app_Some in h1 as [Δ' [h1 h1']].
        subst. rewrite app_context_assoc in h2. simpl in h2.
        right. constructor. exists Δ', s.
        split. all: auto.
  Qed.

  Lemma cored_red :
    forall Γ u v,
      cored Σ Γ v u ->
      ∥ red Σ Γ u v ∥.
  Proof.
    intros Γ u v h.
    induction h.
    - constructor. econstructor.
      + constructor.
      + assumption.
    - destruct IHh as [r].
      constructor. econstructor ; eassumption.
  Qed.

  Lemma cored_context :
    forall Γ t u π,
      cored Σ (Γ ,,, stack_context π) t u ->
      cored Σ Γ (zip (t, π)) (zip (u, π)).
  Proof.
    intros Γ t u π h. induction h.
    - constructor. eapply red1_context. assumption.
    - eapply cored_trans.
      + eapply IHh.
      + eapply red1_context. assumption.
  Qed.

  Lemma cored_zipx :
    forall Γ u v π,
      cored Σ (Γ ,,, stack_context π) u v ->
      cored Σ [] (zipx Γ u π) (zipx Γ v π).
  Proof.
    intros Γ u v π h.
    eapply cored_it_mkLambda_or_LetIn.
    eapply cored_context.
    rewrite app_context_nil_l.
    assumption.
  Qed.

  Lemma red_zipx :
    forall Γ u v π,
      red Σ (Γ ,,, stack_context π) u v ->
      red Σ [] (zipx Γ u π) (zipx Γ v π).
  Proof.
    intros Γ u v π h.
    eapply red_it_mkLambda_or_LetIn.
    eapply red_context.
    rewrite app_context_nil_l.
    assumption.
  Qed.

  Lemma cumul_zippx :
    forall Γ u v ρ,
      Σ ;;; (Γ ,,, stack_context ρ) |- u <= v ->
      Σ ;;; Γ |- zippx u ρ <= zippx v ρ.
  Proof.
    intros Γ u v ρ h.
    induction ρ in u, v, h |- *.
    all: try solve [
      unfold zippx ; simpl ;
      eapply cumul_it_mkLambda_or_LetIn ;
      assumption
    ].
    - cbn. assumption.
    - unfold zippx. simpl.
      case_eq (decompose_stack ρ). intros l π e.
      unfold zippx in IHρ. rewrite e in IHρ.
      apply IHρ.
      eapply cumul_App_l. assumption.
    - unfold zippx. simpl.
      eapply cumul_it_mkLambda_or_LetIn. cbn.
      eapply cumul_Lambda_r.
      assumption.
    - unfold zippx. simpl.
      eapply cumul_it_mkLambda_or_LetIn. cbn.
      eapply cumul_Lambda_r.
      assumption.
    - unfold zippx. simpl.
      eapply cumul_it_mkLambda_or_LetIn. cbn.
      eapply cumul_LetIn_bo. assumption.
  Qed.

  Lemma conv_alt_it_mkLambda_or_LetIn :
    forall Δ Γ u v,
      Σ ;;; (Δ ,,, Γ) |- u = v ->
      Σ ;;; Δ |- it_mkLambda_or_LetIn Γ u = it_mkLambda_or_LetIn Γ v.
  Proof.
    intros Δ Γ u v h. revert Δ u v h.
    induction Γ as [| [na [b|] A] Γ ih ] ; intros Δ u v h.
    - assumption.
    - simpl. cbn. eapply ih.
      eapply conv_LetIn_bo. assumption.
    - simpl. cbn. eapply ih.
      eapply conv_Lambda_r. assumption.
  Qed.

  Lemma conv_alt_it_mkProd_or_LetIn :
    forall Δ Γ B B',
      Σ ;;; (Δ ,,, Γ) |- B = B' ->
      Σ ;;; Δ |- it_mkProd_or_LetIn Γ B = it_mkProd_or_LetIn Γ B'.
  Proof.
    intros Δ Γ B B' h.
    induction Γ as [| [na [b|] A] Γ ih ] in Δ, B, B', h |- *.
    - assumption.
    - simpl. cbn. eapply ih.
      eapply conv_LetIn_bo. assumption.
    - simpl. cbn. eapply ih.
      eapply conv_Prod_r. assumption.
  Qed.

  Lemma conv_zipp :
    forall Γ u v ρ,
      Σ ;;; Γ |- u = v ->
      Σ ;;; Γ |- zipp u ρ = zipp v ρ.
  Proof.
    intros Γ u v ρ h.
    unfold zipp.
    destruct decompose_stack.
    induction l in u, v, h |- *.
    - assumption.
    - simpl.  eapply IHl. eapply conv_App_l. assumption.
  Qed.

  Lemma cumul_zipp :
    forall Γ u v π,
      Σ ;;; Γ |- u <= v ->
      Σ ;;; Γ |- zipp u π <= zipp v π.
  Proof.
    intros Γ u v π h.
    unfold zipp.
    destruct decompose_stack as [l ρ].
    induction l in u, v, h |- *.
    - assumption.
    - simpl.  eapply IHl. eapply cumul_App_l. assumption.
  Qed.

  Lemma conv_cum_zipp' :
    forall leq Γ u v π,
      conv_cum leq Σ Γ u v ->
      conv_cum leq Σ Γ (zipp u π) (zipp v π).
  Proof.
    intros leq Γ u v π h.
    destruct leq.
    - destruct h. constructor. eapply conv_zipp. assumption.
    - destruct h. constructor. eapply cumul_zipp. assumption.
  Qed.

  Lemma conv_alt_zippx :
    forall Γ u v ρ,
      Σ ;;; (Γ ,,, stack_context ρ) |- u = v ->
      Σ ;;; Γ |- zippx u ρ = zippx v ρ.
  Proof.
    intros Γ u v ρ h.
    revert u v h. induction ρ ; intros u v h.
    all: try solve [
      unfold zippx ; simpl ;
      eapply conv_alt_it_mkLambda_or_LetIn ;
      assumption
    ].
    - cbn. assumption.
    - unfold zippx. simpl.
      case_eq (decompose_stack ρ). intros l π e.
      unfold zippx in IHρ. rewrite e in IHρ.
      apply IHρ.
      eapply conv_App_l. assumption.
    - unfold zippx. simpl.
      eapply conv_alt_it_mkLambda_or_LetIn. cbn.
      eapply conv_Lambda_r.
      assumption.
    - unfold zippx. simpl.
      eapply conv_alt_it_mkLambda_or_LetIn. cbn.
      eapply conv_Lambda_r.
      assumption.
    - unfold zippx. simpl.
      eapply conv_alt_it_mkLambda_or_LetIn. cbn.
      eapply conv_LetIn_bo. assumption.
  Qed.

  Lemma conv_zippx :
    forall Γ u v ρ,
      Σ ;;; Γ ,,, stack_context ρ |- u = v ->
      Σ ;;; Γ |- zippx u ρ = zippx v ρ.
  Proof.
    intros Γ u v ρ uv. eapply conv_alt_zippx ; assumption.
  Qed.

  Lemma conv_cum_zippx' :
    forall Γ leq u v ρ,
      conv_cum leq Σ (Γ ,,, stack_context ρ) u v ->
      conv_cum leq Σ Γ (zippx u ρ) (zippx v ρ).
  Proof.
    intros Γ leq u v ρ h.
    destruct leq.
    - cbn in *. destruct h as [h]. constructor.
      eapply conv_alt_zippx ; assumption.
    - cbn in *. destruct h. constructor.
      eapply cumul_zippx. assumption.
  Qed.


  Derive Signature for Acc.

  Lemma wf_fun :
    forall A (R : A -> A -> Prop) B (f : B -> A),
      well_founded R ->
      well_founded (fun x y => R (f x) (f y)).
  Proof.
    intros A R B f h x.
    specialize (h (f x)).
    dependent induction h.
    constructor. intros y h.
    eapply H0 ; try reflexivity. assumption.
  Qed.

  Lemma Acc_fun :
    forall A (R : A -> A -> Prop) B (f : B -> A) x,
      Acc R (f x) ->
      Acc (fun x y => R (f x) (f y)) x.
  Proof.
    intros A R B f x h.
    dependent induction h.
    constructor. intros y h.
    eapply H0 ; try reflexivity. assumption.
  Qed.

  (* TODO Put more general lemma in Inversion *)
  Lemma welltyped_it_mkLambda_or_LetIn :
    forall Γ Δ t,
      welltyped Σ Γ (it_mkLambda_or_LetIn Δ t) ->
      welltyped Σ (Γ ,,, Δ) t.
  Proof.
    destruct hΣ as [wΣ].
    intros Γ Δ t h.
    induction Δ as [| [na [b|] A] Δ ih ] in Γ, t, h |- *.
    - assumption.
    - simpl. apply ih in h. cbn in h.
      destruct h as [T h].
      apply inversion_LetIn in h as hh ; auto.
      destruct hh as [s1 [A' [? [? [? ?]]]]].
      exists A'. assumption.
    - simpl. apply ih in h. cbn in h.
      destruct h as [T h].
      apply inversion_Lambda in h as hh ; auto.
      pose proof hh as [s1 [B [? [? ?]]]].
      exists B. assumption.
  Qed.

  Lemma it_mkLambda_or_LetIn_welltyped :
    forall Γ Δ t,
      welltyped Σ (Γ ,,, Δ) t ->
      welltyped Σ Γ (it_mkLambda_or_LetIn Δ t).
  Proof.
    intros Γ Δ t [T h].
    eexists. eapply PCUICGeneration.type_it_mkLambda_or_LetIn.
    eassumption.
  Qed.

  Lemma welltyped_it_mkLambda_or_LetIn_iff :
    forall Γ Δ t,
      welltyped Σ Γ (it_mkLambda_or_LetIn Δ t) <->
      welltyped Σ (Γ ,,, Δ) t.
  Proof.
    intros. split.
    - apply welltyped_it_mkLambda_or_LetIn.
    - apply it_mkLambda_or_LetIn_welltyped.
  Qed.

  Lemma isWfArity_it_mkLambda_or_LetIn :
    forall Γ Δ T,
      isWfArity typing Σ Γ (it_mkLambda_or_LetIn Δ T) ->
      isWfArity typing Σ (Γ ,,, Δ) T.
  Proof.
    intro Γ; induction Δ in Γ |- *; intro T; [easy|].
    destruct a as [na [bd|] ty].
    - simpl. cbn. intro HH. apply IHΔ in HH.
      destruct HH as [Δ' [s [HH HH']]].
      cbn in HH; apply destArity_app_Some in HH.
      destruct HH as [Δ'' [HH1 HH2]].
      exists Δ'', s. split; tas.
      refine (eq_rect _ (fun Γ => wf_local Σ Γ) HH' _ _).
      rewrite HH2. rewrite app_context_assoc. reflexivity.
    - simpl. cbn. intro HH. apply IHΔ in HH.
      destruct HH as [Δ' [s [HH HH']]]. discriminate.
  Qed.

  Lemma wellformed_it_mkLambda_or_LetIn :
    forall Γ Δ t,
      wellformed Σ Γ (it_mkLambda_or_LetIn Δ t) ->
      wellformed Σ (Γ ,,, Δ) t.
  Proof.
    intros Γ Δ t [Hwf|Hwf];
      [left; now apply welltyped_it_mkLambda_or_LetIn |
       right; destruct Hwf; constructor].
    now apply isWfArity_it_mkLambda_or_LetIn.
  Qed.


  Lemma wellformed_zipp :
    forall Γ t ρ,
      wellformed Σ Γ (zipp t ρ) ->
      wellformed Σ Γ t.
  Proof.
    destruct hΣ as [wΣ].
    intros Γ t ρ h.
    unfold zipp in h.
    case_eq (decompose_stack ρ). intros l π e.
    rewrite e in h. clear - h wΣ.
    destruct h as [[A h]|[h]].
    - left.
      induction l in t, A, h |- *.
      + eexists. eassumption.
      + apply IHl in h.
        destruct h as [T h].
        apply inversion_App in h as hh ; auto.
        rdestruct hh. econstructor. eassumption.
    - right. constructor. destruct l.
      + assumption.
      + destruct h as [ctx [s [h1 _]]].
        rewrite destArity_tApp in h1. discriminate.
  Qed.

  (* WRONG *)
  Lemma it_mkLambda_or_LetIn_wellformed :
    forall Γ Δ t,
      wellformed Σ (Γ ,,, Δ) t ->
      wellformed Σ Γ (it_mkLambda_or_LetIn Δ t).
  Abort.

  (* Wrong for t = alg univ, π = ε, Γ = vass A *)
  Lemma zipx_wellformed :
    forall {Γ t π},
      wellformed Σ Γ (zipc t π) ->
      wellformed Σ [] (zipx Γ t π).
  (* Proof. *)
  (*   intros Γ t π h. *)
  (*   eapply it_mkLambda_or_LetIn_wellformed. *)
  (*   rewrite app_context_nil_l. *)
  (*   assumption. *)
  (* Qed. *)
  Abort.

  Lemma wellformed_zipx :
    forall {Γ t π},
      wellformed Σ [] (zipx Γ t π) ->
      wellformed Σ Γ (zipc t π).
  Proof.
    intros Γ t π h.
    apply wellformed_it_mkLambda_or_LetIn in h.
    rewrite app_context_nil_l in h.
    assumption.
  Qed.

  Lemma wellformed_zipc_stack_context Γ t π ρ args
    : decompose_stack π = (args, ρ)
      -> wellformed Σ Γ (zipc t π)
      -> wellformed Σ (Γ ,,, stack_context π) (zipc t (appstack args ε)).
  Proof.
    intros h h1.
    apply decompose_stack_eq in h. subst.
    rewrite stack_context_appstack.
    induction args in Γ, t, ρ, h1 |- *.
    - cbn in *.
      now apply (wellformed_context Γ (t, ρ)).
    - simpl. eauto.
  Qed.

  (* Wrong  *)
  Lemma wellformed_zipc_zippx :
    forall Γ t π,
      wellformed Σ Γ (zipc t π) ->
      wellformed Σ Γ (zippx t π).
  (* Proof. *)
  (*   intros Γ t π h. *)
  (*   unfold zippx. *)
  (*   case_eq (decompose_stack π). intros l ρ e. *)
  (*   pose proof (decompose_stack_eq _ _ _ e). subst. clear e. *)
  (*   rewrite zipc_appstack in h. *)
  (*   zip fold in h. *)
  (*   apply wellformed_context in h ; simpl in h. *)
  (*   eapply it_mkLambda_or_LetIn_wellformed. *)
  (*   assumption. *)
  (* Qed. *)
  Abort.

  Lemma red_const :
    forall {Γ c u cty cb cu},
      Some (ConstantDecl {| cst_type := cty ; cst_body := Some cb ; cst_universes := cu |})
      = lookup_env Σ c ->
      red (fst Σ) Γ (tConst c u) (subst_instance_constr u cb).
  Proof.
    intros Γ c u cty cb cu e.
    econstructor.
    - econstructor.
    - econstructor.
      + symmetry in e.  exact e.
      + reflexivity.
  Qed.

  Lemma cored_const :
    forall {Γ c u cty cb cu},
      Some (ConstantDecl {| cst_type := cty ; cst_body := Some cb ; cst_universes := cu |})
      = lookup_env Σ c ->
      cored (fst Σ) Γ (subst_instance_constr u cb) (tConst c u).
  Proof.
    intros Γ c u cty cb cu e.
    symmetry in e.
    econstructor.
    econstructor.
    - exact e.
    - reflexivity.
  Qed.

  Derive Signature for cumul.
  Derive Signature for red1.

  Lemma app_cored_r :
    forall Γ u v1 v2,
      cored Σ Γ v1 v2 ->
      cored Σ Γ (tApp u v1) (tApp u v2).
  Proof.
    intros Γ u v1 v2 h.
    induction h.
    - constructor. constructor. assumption.
    - eapply cored_trans.
      + eapply IHh.
      + constructor. assumption.
  Qed.

  Fixpoint isAppProd (t : term) : bool :=
    match t with
    | tApp t l => isAppProd t
    | tProd na A B => true
    | _ => false
    end.

  Fixpoint isProd t :=
    match t with
    | tProd na A B => true
    | _ => false
    end.

  Lemma isAppProd_mkApps :
    forall t l, isAppProd (mkApps t l) = isAppProd t.
  Proof.
    intros t l. revert t.
    induction l ; intros t.
    - reflexivity.
    - cbn. rewrite IHl. reflexivity.
  Qed.

  Lemma isProdmkApps :
    forall t l,
      isProd (mkApps t l) ->
      l = [].
  Proof.
    intros t l h.
    revert t h.
    induction l ; intros t h.
    - reflexivity.
    - cbn in h. specialize IHl with (1 := h). subst.
      cbn in h. discriminate h.
  Qed.

  Lemma isSortmkApps :
    forall t l,
      isSort (mkApps t l) ->
      l = [].
  Proof.
    intros t l h.
    revert t h.
    induction l ; intros t h.
    - reflexivity.
    - cbn in h. specialize IHl with (1 := h). subst.
      cbn in h. exfalso. assumption.
  Qed.

  Lemma isAppProd_isProd :
    forall Γ t,
      isAppProd t ->
      welltyped Σ Γ t ->
      isProd t.
  Proof.
    destruct hΣ as [wΣ].
    intros Γ t hp hw.
    induction t in Γ, hp, hw |- *.
    all: try discriminate hp.
    - reflexivity.
    - simpl in hp.
      specialize IHt1 with (1 := hp).
      assert (welltyped Σ Γ t1) as h.
      { destruct hw as [T h].
        apply inversion_App in h as hh ; auto.
        destruct hh as [na [A' [B' [? [? ?]]]]].
        eexists. eassumption.
      }
      specialize IHt1 with (1 := h).
      destruct t1.
      all: try discriminate IHt1.
      destruct hw as [T hw'].
      apply inversion_App in hw' as ihw' ; auto.
      destruct ihw' as [na' [A' [B' [hP [? ?]]]]].
      apply inversion_Prod in hP as [s1 [s2 [? [? bot]]]] ; auto.
      apply PCUICConversion.invert_cumul_prod_r in bot ; auto.
      destruct bot as [? [? [? [[r ?] ?]]]].
      exfalso. clear - r wΣ.
      revert r. generalize (Universe.sort_of_product s1 s2). intro s. clear.
      intro r.
      dependent induction r.
      assert (h : P = tSort s).
      { clear - r. induction r ; auto. subst.
        dependent destruction r0.
        assert (h : isSort (mkApps (tFix mfix idx) args)).
        { rewrite <- H. constructor. }
        apply isSortmkApps in h. subst. cbn in H.
        discriminate.
      }
      subst.
      dependent destruction r0.
      assert (h : isSort (mkApps (tFix mfix idx) args)).
      { rewrite <- H. constructor. }
      apply isSortmkApps in h. subst. cbn in H.
      discriminate.
  Qed.

  Lemma mkApps_Prod_nil :
    forall Γ na A B l,
      welltyped Σ Γ (mkApps (tProd na A B) l) ->
      l = [].
  Proof.
    intros Γ na A B l h.
    pose proof (isAppProd_isProd) as hh.
    specialize hh with (2 := h).
    rewrite isAppProd_mkApps in hh.
    specialize hh with (1 := eq_refl).
    apply isProdmkApps in hh. assumption.
  Qed.

  Lemma mkApps_Prod_nil' :
    forall Γ na A B l,
      wellformed Σ Γ (mkApps (tProd na A B) l) ->
      l = [].
  Proof.
    intros Γ na A B l [h | [[ctx [s [hd hw]]]]].
    - eapply mkApps_Prod_nil. eassumption.
    - destruct l ; auto.
      cbn in hd. rewrite destArity_tApp in hd. discriminate.
  Qed.

  (* TODO MOVE or even replace old lemma *)
  Lemma decompose_stack_noStackApp :
    forall π l ρ,
      decompose_stack π = (l,ρ) ->
      isStackApp ρ = false.
  Proof.
    intros π l ρ e.
    destruct ρ. all: auto.
    exfalso. eapply decompose_stack_not_app. eassumption.
  Qed.

  (* TODO MOVE *)
  Lemma stack_context_decompose :
    forall π,
      stack_context (snd (decompose_stack π)) = stack_context π.
  Proof.
    intros π.
    case_eq (decompose_stack π). intros l ρ e.
    cbn. pose proof (decompose_stack_eq _ _ _ e). subst.
    rewrite stack_context_appstack. reflexivity.
  Qed.

  Lemma it_mkLambda_or_LetIn_inj :
    forall Γ u v,
      it_mkLambda_or_LetIn Γ u =
      it_mkLambda_or_LetIn Γ v ->
      u = v.
  Proof.
    intros Γ u v e.
    revert u v e.
    induction Γ as [| [na [b|] A] Γ ih ] ; intros u v e.
    - assumption.
    - simpl in e. cbn in e.
      apply ih in e.
      inversion e. reflexivity.
    - simpl in e. cbn in e.
      apply ih in e.
      inversion e. reflexivity.
  Qed.

  Hint Resolve conv_refl conv_alt_red : core.
  Hint Resolve conv_refl : core.


  (* Let bindings are not injective, so it_mkLambda_or_LetIn is not either.
     However, when they are all lambdas they become injective for conversion.
     stack_contexts only produce lambdas so we can use this property on them.
     It only applies to stacks manipulated by conversion/reduction which are
     indeed let-free.
   *)
  Fixpoint let_free_context (Γ : context) :=
    match Γ with
    | [] => true
    | {| decl_name := na ; decl_body := Some b ; decl_type := B |} :: Γ => false
    | {| decl_name := na ; decl_body := None ; decl_type := B |} :: Γ =>
      let_free_context Γ
    end.

  Lemma let_free_context_app :
    forall Γ Δ,
      let_free_context (Γ ,,, Δ) = let_free_context Δ && let_free_context Γ.
  Proof.
    intros Γ Δ.
    induction Δ as [| [na [b|] B] Δ ih ] in Γ |- *.
    - simpl. reflexivity.
    - simpl. reflexivity.
    - simpl. apply ih.
  Qed.

  Lemma let_free_context_rev :
    forall Γ,
      let_free_context (List.rev Γ) = let_free_context Γ.
  Proof.
    intros Γ.
    induction Γ as [| [na [b|] B] Γ ih ].
    - reflexivity.
    - simpl. rewrite let_free_context_app. simpl.
      apply andb_false_r.
    - simpl. rewrite let_free_context_app. simpl.
      rewrite ih. rewrite andb_true_r. reflexivity.
  Qed.

  Fixpoint let_free_stack (π : stack) :=
    match π with
    | ε => true
    | App u ρ => let_free_stack ρ
    | Fix f n args ρ => let_free_stack ρ
    | Fix_mfix_ty na bo ra mfix1 mfix2 idx ρ => let_free_stack ρ
    | Fix_mfix_bd na ty ra mfix1 mfix2 idx ρ => let_free_stack ρ
    | CoFix f n args ρ => let_free_stack ρ
    | Case_p indn c brs ρ => let_free_stack ρ
    | Case indn p brs ρ => let_free_stack ρ
    | Case_brs indn p c m brs1 brs2 ρ => let_free_stack ρ
    | Proj p ρ => let_free_stack ρ
    | Prod_l na B ρ => let_free_stack ρ
    | Prod_r na A ρ => let_free_stack ρ
    | Lambda_ty na u ρ => let_free_stack ρ
    | Lambda_tm na A ρ => let_free_stack ρ
    | LetIn_bd na B u ρ => let_free_stack ρ
    | LetIn_ty na b u ρ => let_free_stack ρ
    | LetIn_in na b B ρ => false
    | coApp u ρ => let_free_stack ρ
    end.

  Lemma let_free_stack_context :
    forall π,
      let_free_stack π ->
      let_free_context (stack_context π).
  Proof.
    intros π h.
    induction π.
    all: try solve [ simpl ; rewrite ?IHπ // ].
    simpl. rewrite let_free_context_app.
    rewrite IHπ => //. rewrite andb_true_r. rewrite let_free_context_rev.
    match goal with
    | |- context [ mapi ?f ?l ] =>
      generalize l
    end.
    intro l. unfold mapi.
    generalize 0 at 2. intro n.
    induction l in n |- *.
    - simpl. reflexivity.
    - simpl. apply IHl.
  Qed.

  Lemma cored_red_cored :
    forall Γ u v w,
      cored Σ Γ w v ->
      red Σ Γ u v ->
      cored Σ Γ w u.
  Proof.
    intros Γ u v w h1 h2.
    revert u h2. induction h1 ; intros t h2.
    - eapply cored_red_trans ; eassumption.
    - eapply cored_trans.
      + eapply IHh1. assumption.
      + assumption.
  Qed.

  Lemma red_neq_cored :
    forall Γ u v,
      red Σ Γ u v ->
      u <> v ->
      cored Σ Γ v u.
  Proof.
    intros Γ u v r n.
    destruct r.
    - exfalso. apply n. reflexivity.
    - eapply cored_red_cored ; try eassumption.
      constructor. assumption.
  Qed.

  Lemma red_welltyped :
    forall {Γ u v},
      welltyped Σ Γ u ->
      ∥ red (fst Σ) Γ u v ∥ ->
      welltyped Σ Γ v.
  Proof.
    destruct hΣ as [wΣ]; clear hΣ.
    intros Γ u v h [r].
    revert h. induction r ; intros h.
    - assumption.
    - specialize IHr with (1 := ltac:(eassumption)).
      destruct IHr as [A ?]. exists A.
      eapply subject_reduction1 ; eauto with wf.
  Qed.

  Lemma red_cored_cored :
    forall Γ u v w,
      red Σ Γ v w ->
      cored Σ Γ v u ->
      cored Σ Γ w u.
  Proof.
    intros Γ u v w h1 h2.
    revert u h2. induction h1 ; intros t h2.
    - assumption.
    - eapply cored_trans.
      + eapply IHh1. assumption.
      + assumption.
  Qed.

  (* TODO MOVE It needs wf Σ entirely *)
  Lemma subject_conversion :
    forall Γ u v A B,
      Σ ;;; Γ |- u : A ->
      Σ ;;; Γ |- v : B ->
      Σ ;;; Γ |- u = v ->
      ∑ C,
        Σ ;;; Γ |- u : C ×
        Σ ;;; Γ |- v : C.
  Proof.
    intros Γ u v A B hu hv h.
    (* apply conv_conv_alt in h. *)
    (* apply conv_alt_red in h as [u' [v' [? [? ?]]]]. *)
    (* pose proof (subject_reduction _ Γ _ _ _ hΣ hu r) as hu'. *)
    (* pose proof (subject_reduction _ Γ _ _ _ hΣ hv r0) as hv'. *)
    (* pose proof (typing_alpha _ _ _ _ hu' e) as hv''. *)
    (* pose proof (principal_typing _ hv' hv'') as [C [? [? hvC]]]. *)
    (* apply eq_term_sym in e as e'. *)
    (* pose proof (typing_alpha _ _ _ _ hvC e') as huC. *)
    (* Not clear.*)
  Abort.
  
  Derive Signature for typing.

  Lemma Proj_red_cond :
    forall Γ i pars narg i' c u l,
      wellformed Σ Γ (tProj (i, pars, narg) (mkApps (tConstruct i' c u) l)) ->
      nth_error l (pars + narg) <> None.
  Proof.
    intros Γ i pars narg i' c u l [[T h]|[[ctx [s [e _]]]]];
      [|discriminate].
    destruct hΣ.
    apply inversion_Proj in h; auto.
    destruct h as [uni [mdecl [idecl [pdecl [args' [d [hc [? ?]]]]]]]].
    eapply on_declared_projection in d; auto. destruct d as [? [? ?]]; auto.
    simpl in *.
    destruct p.
    destruct o0; auto.
  Admitted.

  Lemma cored_zipc :
    forall Γ t u π,
      cored Σ (Γ ,,, stack_context π) t u ->
      cored Σ Γ (zipc t π) (zipc u π).
  Proof.
    intros Γ t u π h.
    do 2 zip fold. eapply cored_context. assumption.
  Qed.

  Lemma red_zipc :
    forall Γ t u π,
      red Σ (Γ ,,, stack_context π) t u ->
      red Σ Γ (zipc t π) (zipc u π).
  Proof.
    intros Γ t u π h.
    do 2 zip fold. eapply red_context. assumption.
  Qed.

  Lemma wellformed_zipc_zipp :
    forall Γ t π,
      wellformed Σ Γ (zipc t π) ->
      wellformed Σ (Γ ,,, stack_context π) (zipp t π).
  Proof.
    intros Γ t π h.
    unfold zipp.
    case_eq (decompose_stack π). intros l ρ e.
    pose proof (decompose_stack_eq _ _ _ e). subst. clear e.
    rewrite zipc_appstack in h.
    zip fold in h.
    apply wellformed_context in h. simpl in h.
    rewrite stack_context_appstack.
    assumption.
  Qed.

  Lemma conv_cum_context_convp :
    forall Γ Γ' leq u v,
      conv_cum leq Σ Γ u v ->
      conv_context Σ Γ Γ' ->
      conv_cum leq Σ Γ' u v.
  Proof.
    intros Γ Γ' leq u v h hx.
    destruct hΣ.
    destruct leq.
    - simpl. destruct h. constructor.
      eapply conv_conv_ctx. all: eauto.
    - simpl in *. destruct h. constructor.
      eapply cumul_conv_ctx. all: eauto.
  Qed.

End Lemmata.

Lemma declared_inductive_valid_type {cf:checker_flags} Σ Γ mdecl idecl i u :
  wf Σ.1 ->
  wf_local Σ Γ ->
  declared_inductive Σ.1 mdecl i idecl ->
  consistent_instance_ext Σ (ind_universes mdecl) u ->
  isType Σ Γ (subst_instance_constr u (ind_type idecl)).
Proof.
  move=> wfΣ wfΓ declc Hu.
  pose declc as declc'.
  apply on_declared_inductive in declc' as [onmind onind]; auto.
  apply onArity in onind.
  destruct onind as [s Hs].
  epose proof (PCUICUnivSubstitution.typing_subst_instance_decl Σ) as s'.
  destruct declc.
  specialize (s' [] _ _ _ _ u wfΣ H Hs Hu).
  simpl in s'. eexists; eauto.
  eapply (PCUICWeakening.weaken_ctx (Γ:=[]) Γ); eauto.
Qed.

Set Default Goal Selector "1".

Lemma Case_Construct_ind_eq {cf:checker_flags} Σ (hΣ : ∥ wf Σ.1 ∥) :
forall {Γ ind ind' npar pred i u brs args},
  wellformed Σ Γ (tCase (ind, npar) pred (mkApps (tConstruct ind' i u) args) brs) ->
  ind = ind'.
Proof.
destruct hΣ as [wΣ].
intros Γ ind ind' npar pred i u brs args [[A h]|[[ctx [s [e _]]]]];
  [|discriminate].
apply inversion_Case in h as ih ; auto.
destruct ih
  as [uni [args' [mdecl [idecl [pty [indctx [pctx [ps [btys [? [? [? [ht0 [? ?]]]]]]]]]]]]]].
  pose proof ht0 as typec.
  eapply inversion_mkApps in typec as [A' [U [tyc [tyargs tycum]]]]; auto.
  eapply (inversion_Construct Σ wΣ) in tyc as [mdecl' [idecl' [cdecl' [wfl [declc [Hu tyc]]]]]].
  epose proof (Construct_Ind_ind_eq _ ht0 declc); eauto.
  simpl in X. destruct declc. simpl in X.
  destruct declared_constructor_inv as [cs [csort onc']].
  intuition auto.
Qed.

Lemma Proj_Constuct_ind_eq {cf:checker_flags} Σ (hΣ : ∥ wf Σ.1 ∥):
forall Γ i i' pars narg c u l,
  wellformed Σ Γ (tProj (i, pars, narg) (mkApps (tConstruct i' c u) l)) ->
  i = i'.
Proof.
destruct hΣ as [wΣ].
intros Γ i i' pars narg c u l [[T h]|[[ctx [s [e _]]]]];
  [|discriminate].
apply inversion_Proj in h ; auto.
destruct h as [uni [mdecl [idecl [pdecl [args' [? [hc [? ?]]]]]]]].
pose proof hc as typec.
eapply inversion_mkApps in typec as [A' [U [tyc [tyargs tycum]]]]; auto.
eapply (inversion_Construct Σ wΣ) in tyc as [mdecl' [idecl' [cdecl' [wfl [declc [Hu tyc]]]]]].
epose proof (Construct_Ind_ind_eq _ hc declc); eauto.
simpl in X. destruct declc. simpl in X.
destruct declared_constructor_inv as [cs [csort onc']].
intuition auto.
Qed.

Lemma isWAT_tLetIn {cf:checker_flags} {Σ : global_env_ext} (HΣ' : wf Σ)
      {Γ} (HΓ : wf_local Σ Γ) {na t A B}
  : isWfArity_or_Type Σ Γ (tLetIn na t A B)
    <~> (isType Σ Γ A × (Σ ;;; Γ |- t : A)
                      × isWfArity_or_Type Σ (Γ,, vdef na t A) B).
Proof.
  split; intro HH.
  - destruct HH as [[ctx [s [H1 H2]]]|[s H]].
    + cbn in H1. apply destArity_app_Some in H1.
      destruct H1 as [ctx' [H1 HH]]; subst ctx.
      rewrite app_context_assoc in H2. repeat split.
      * apply wf_local_app in H2. inversion H2; subst. assumption.
      * apply wf_local_app in H2. inversion H2; subst. assumption.
      * left. exists ctx', s. split; tas.
    + apply inversion_LetIn in H; tas. destruct H as [s1 [A' [HA [Ht [HB H]]]]].
      repeat split; tas. 1: eexists; eassumption.
      apply cumul_Sort_r_inv in H.
      destruct H as [s' [H H']].
      right. exists s'. eapply type_reduction; tea.
      apply invert_red_letin in H; tas.
      destruct H as [[? [? [? [? [[[H ?] ?] ?]]]]]|H].
      * apply invert_red_sort in H; inv H.
      * etransitivity.
        2: apply weakening_red_0 with (Γ' := [_]) (N := tSort _);
          tea; reflexivity.
        exact (red_rel_all _ (Γ ,, vdef na t A) 0 t A' eq_refl).
  - destruct HH as [HA [Ht [[ctx [s [H1 H2]]]|HB]]].
    + left. exists ([vdef na t A] ,,, ctx), s. split.
      cbn. now rewrite destArity_app H1.
      now rewrite app_context_assoc.
    + right. destruct HB as [sB HB].
      eexists. eapply type_reduction; tas.
      * econstructor; tea.
        apply HA.π2.
      * apply red1_red.
        apply red_zeta with (b':=tSort sB).
Defined.
(*
Lemma type_Case' {cf:checker_flags} Σ Γ indnpar u p c brs args :
  let ind := indnpar.1 in
  let npar := indnpar.2 in
      forall mdecl idecl (isdecl : declared_inductive Σ.1 mdecl ind idecl),
    mdecl.(ind_npars) = npar ->
    wf Σ.1 ->
    let params := List.firstn npar args in
    forall ps pty, build_case_predicate_type ind mdecl idecl params u ps =
                Some pty ->                
    Σ ;;; Γ |- p : pty ->
    leb_sort_family (universe_family ps) idecl.(ind_kelim) ->
    Σ ;;; Γ |- c : mkApps (tInd ind u) args ->
    forall btys, map_option_out (build_branches_type ind mdecl idecl params u p) =
                Some btys ->
    All2 (fun br bty => (br.1 = bty.1) × (Σ ;;; Γ |- br.2 : bty.2)) brs btys ->
    Σ ;;; Γ |- tCase indnpar p c brs : mkApps p (skipn npar args ++ [c]).
Proof.
  (* intros mdecl idecl isdecl wfΣ H pars pty X indctx pctx ps btys H0 X0 H1 X1 X2.
  econstructor; tea.
  eapply type_Case_valid_btys in H0; tea.
  eapply All2_All_mix_right; tas. *)
Admitted.
*)
