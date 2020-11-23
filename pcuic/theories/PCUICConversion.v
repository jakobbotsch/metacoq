(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICLiftSubst PCUICTyping
     PCUICSubstitution PCUICPosition PCUICCumulativity PCUICReduction
     PCUICConfluence PCUICClosed PCUICParallelReductionConfluence PCUICEquality
     PCUICContextConversion PCUICWeakening PCUICUnivSubst PCUICUnivSubstitution
.

Require Import ssreflect.
Require Import CRelationClasses.
Require Import Equations.Type.Relation Equations.Type.Relation_Properties.
Require Import Equations.Prop.DepElim.

Set Default Goal Selector "!".


Ltac tc := try typeclasses eauto 10.
Ltac pcuic := intuition eauto 5 with pcuic ||
  (try solve [repeat red; cbn in *; intuition auto; eauto 5 with pcuic || (try lia || congruence)]).

Hint Resolve eq_universe_leq_universe' : pcuic.

Derive Signature for conv cumul assumption_context.
Derive Signature for clos_refl_trans_1n.

(* todo move *)
Lemma All2_refl {A} {P : A -> A -> Type} l :
  (forall x, P x x) ->
  All2 P l l.
Proof.
  intros HP. induction l; constructor; auto.
Qed.

(** Remark that confluence is needed for transitivity of conv and cumul. *)

Instance conv_trans {cf:checker_flags} (Σ : global_env_ext) {Γ} :
  wf Σ -> Transitive (conv Σ Γ).
Proof.
  intros wfΣ t u v X0 X1.
  eapply conv_alt_red in X0 as [t' [u' [[tt' uu'] eq]]].
  eapply conv_alt_red in X1 as [u'' [v' [[uu'' vv'] eq']]].
  eapply conv_alt_red.
  destruct (red_confluence wfΣ uu' uu'') as [u'nf [ul ur]].
  eapply red_eq_term_upto_univ_r in ul as [tnf [redtnf ?]]; tea; tc.
  eapply red_eq_term_upto_univ_l in ur as [unf [redunf ?]]; tea; tc.
  exists tnf, unf.
  intuition auto.
  - now transitivity t'.
  - now transitivity v'.
  - now transitivity u'nf.
Qed.

Instance cumul_trans {cf:checker_flags} (Σ : global_env_ext) Γ :
  wf Σ -> Transitive (cumul Σ Γ).
Proof.
  intros wfΣ t u v X X0.
  eapply cumul_alt in X as [v' [v'' [[redl redr] eq]]].
  eapply cumul_alt in X0 as [w [w' [[redl' redr'] eq']]].
  destruct (red_confluence wfΣ redr redl') as [nf [nfl nfr]].
  eapply cumul_alt.
  eapply red_eq_term_upto_univ_r in eq; tc;eauto with pcuic.
  destruct eq as [v'0 [red'0 eq2]].
  eapply red_eq_term_upto_univ_l in eq'; tc;eauto with pcuic.
  destruct eq' as [v'1 [red'1 eq1]].
  exists v'0, v'1.
  split. 1: split.
  - transitivity v' ; auto.
  - transitivity w' ; auto.
  - eapply leq_term_trans with nf; eauto.
Qed.

Instance conv_context_trans {cf:checker_flags} Σ :
  wf Σ.1 -> Transitive (fun Γ Γ' => conv_context Σ Γ Γ').
Proof.
  intros wfΣ.
  eapply context_relation_trans.
  intros.
  depelim X2; depelim X3; try constructor; auto.
  * etransitivity; eauto.
  * etransitivity.
    + eapply conv_trans; eauto.
    + eapply conv_conv_ctx => //.
      - apply c0.
      - apply conv_context_sym => //.
  * etransitivity; eauto.
  * eapply conv_trans; eauto.
    eapply conv_conv_ctx => //.
    + apply c0.
    + apply conv_context_sym => //.
  * etransitivity; eauto.
  * eapply conv_trans; eauto.
    eapply conv_conv_ctx => //.
    + apply c0.
    + apply conv_context_sym => //.
  * eapply conv_trans; eauto.
    eapply conv_conv_ctx => //; eauto.
    apply conv_context_sym => //.
  * etransitivity; eauto.
  * eapply conv_trans; eauto.
    eapply conv_conv_ctx => //; eauto.
    apply conv_context_sym => //.
  * etransitivity; eauto.
  * eapply conv_trans; eauto.
    eapply conv_conv_ctx => //; eauto.
    apply conv_context_sym => //.
  * eapply conv_trans; eauto.
    eapply conv_conv_ctx => //; eauto.
    apply conv_context_sym => //.
Qed.


Section EquivalenceConvCumulDefs.

  Context {cf:checker_flags} (Σ : global_env_ext) (wfΣ : wf Σ) (Γ : context).

  Proposition conv_conv1 M N :
    conv1 Σ Γ M N <~> conv Σ Γ M N.
  Proof.
    split; intro H.
    - induction H.
      + destruct r as [[r|r]|r].
        * eapply red_conv; eauto.
        * now econstructor 3; tea.
        * now constructor.
      + reflexivity.
      + etransitivity; tea.
    - induction H.
      + constructor. now right.
      + etransitivity; tea.
        constructor. left. now left.
      + etransitivity; tea.
        constructor. left. now right.
  Qed.


  Proposition cumul_cumul1 M N :
    cumul1 Σ Γ M N <~> cumul Σ Γ M N.
  Proof.
    split; intro H.
    - induction H.
      + destruct r as [[r|r]|r].
        * eapply red_cumul; eauto.
        * now econstructor 3; tea.
        * now constructor.
      + reflexivity.
      + etransitivity; tea.
    - induction H.
      + constructor. now right.
      + etransitivity; tea.
        constructor. left. now left.
      + etransitivity; tea.
        constructor. left. now right.
  Qed.

End EquivalenceConvCumulDefs.



(* TODO MOVE *)
Fixpoint isFixApp t : bool :=
  match t with
  | tApp f u => isFixApp f
  | tFix mfix idx => true
  | _ => false
  end.

(* TODO MOVE *)
Lemma isFixApp_mkApps :
  forall t l,
    isFixApp (mkApps t l) = isFixApp t.
Proof.
  intros t l. induction l in t |- *.
  - cbn. reflexivity.
  - cbn. rewrite IHl. reflexivity.
Qed.


Lemma congr_cumul_prod_l : forall `{checker_flags} Σ Γ na na' M1 M2 N1,
  wf Σ.1 ->
  eq_binder_annot na na' ->
  Σ ;;; Γ |- M1 = N1 ->
  Σ ;;; Γ |- (tProd na M1 M2) <= (tProd na' N1 M2).
Proof.
  intros.
  eapply conv_alt_red in X0 as (dom & dom' & (rdom & rdom') & eqdom).
  eapply cumul_alt.
  exists (tProd na dom M2), (tProd na' dom' M2).
  split; [split| auto].
  - eapply red_prod; eauto.
  - eapply red_prod; eauto.
  - constructor; [assumption|apply eqdom|reflexivity].
Qed.

Lemma congr_cumul_prod : forall `{checker_flags} Σ Γ na na' M1 M2 N1 N2,
  wf Σ.1 ->
  eq_binder_annot na na' ->
  Σ ;;; Γ |- M1 = N1 ->
  Σ ;;; (Γ ,, vass na M1) |- M2 <= N2 ->
  Σ ;;; Γ |- (tProd na M1 M2) <= (tProd na' N1 N2).
Proof.
  intros * wfΣ ? ?.
  transitivity (tProd na' N1 M2).
  - eapply congr_cumul_prod_l; eauto.
  - eapply (cumul_conv_ctx _ _ _ (Γ ,, vass na' N1)) in X0.
    2:{ constructor; [apply conv_ctx_refl|constructor; auto]. }
    clear X.
    eapply cumul_alt in X0 as (codom & codom' & (rcodom & rcodom') & eqcodom).
    eapply cumul_alt.
    exists (tProd na' N1 codom), (tProd na' N1 codom').
    split; [split|].
    + eapply red_prod; eauto.
    + eapply red_prod; auto.
    + constructor; auto. reflexivity.
Qed.

Lemma cumul_Sort_inv {cf:checker_flags} Σ Γ s s' :
  Σ ;;; Γ |- tSort s <= tSort s' ->
  leq_universe (global_ext_constraints Σ) s s'.
Proof.
  intros H. depind H.
  - now inversion l.
  - depelim r. solve_discr.
  - depelim r. solve_discr.


Qed.

Lemma cumul_Sort_Prod_inv {cf:checker_flags} Σ Γ s na dom codom :
  Σ ;;; Γ |- tSort s <= tProd na dom codom ->
  False.
Proof.
  intros H. depind H.
  - now inversion l.
  - depelim r. solve_discr.
  - depelim r.
    + solve_discr.
    + eapply IHcumul. reflexivity.
    + eapply IHcumul. reflexivity.
Qed.

Lemma cumul_Sort_l_inv {cf:checker_flags} Σ Γ s T :
  Σ ;;; Γ |- tSort s <= T ->
  ∑ s', red Σ Γ T (tSort s') * leq_universe Σ s s'.
Proof.
  intros H. depind H.
  - now inversion l.
  - depelim r. solve_discr.
  - destruct IHcumul as [s' [redv leq]].
    exists s'. split; auto. now eapply red_step with v.
Qed.

Lemma cumul_Sort_r_inv {cf:checker_flags} Σ Γ s T :
  Σ ;;; Γ |- T <= tSort s ->
  ∑ s', red Σ Γ T (tSort s') * leq_universe Σ s' s.
Proof.
  intros H. depind H.
  - now inversion l.
  - destruct IHcumul as [s' [redv leq]].
    exists s'. split; auto. now eapply red_step with v.
  - depelim r. solve_discr.
Qed.

Lemma cumul_LetIn_l_inv {cf:checker_flags} (Σ : global_env_ext) Γ na b B codom T :
  wf Σ ->
  Σ ;;; Γ |- tLetIn na b B codom <= T ->
  ∑ codom', red Σ Γ T codom' *
                     (Σ ;;; Γ |- codom {0 := b} <= codom').
Proof.
  intros wfΣ H. depind H.
  - inv l. eexists (u' {0 := t'}); intuition eauto.
    + eapply red1_red. constructor.
    + transitivity (codom {0 := t'}).
      * constructor.
        eapply eq_term_upto_univ_subst; trivial; cbnr.
        exact _.
      * constructor. now eapply subst_leq_term.
  - depelim r.
    + exists u; intuition auto.
    + solve_discr.
    + specialize (IHcumul _ _ _ _ _ wfΣ eq_refl).
      destruct IHcumul as [codom' [reddom' leq]].
      exists codom'; intuition auto.
      transitivity (codom {0 := r}); eauto.
      eapply red_cumul. eapply (red_red Σ _ [vdef na b B] []) => //.
      * constructor. 1: now eapply red1_red.
        constructor.
      * rewrite -{1}(subst_empty 0 b). repeat constructor.
    + specialize (IHcumul _ _ _ _ _ wfΣ eq_refl).
      destruct IHcumul as [codom' [reddom' leq]].
      exists codom'; intuition auto.
    + specialize (IHcumul _ _ _ _ _ wfΣ eq_refl).
      destruct IHcumul as [codom' [reddom' leq]].
      exists codom'; intuition auto.
      eapply transitivity; [|eassumption].
      eapply red_cumul.
      rewrite -{1 2}(subst_empty 0 b).
      eapply (untyped_substitution_red _ _ [vdef na b B] []); auto.
      repeat constructor.
  - specialize (IHcumul wfΣ).
    destruct IHcumul as [codom' [reddom' leq]] => //.
    exists codom'; intuition auto.
    now eapply red_step with v.
Qed.

Lemma cumul_LetIn_r_inv {cf:checker_flags} (Σ : global_env_ext) Γ na b B codom T :
  wf Σ ->
  Σ ;;; Γ |- T <= tLetIn na b B codom ->
  ∑ codom', red Σ Γ T codom' *
                     (Σ ;;; Γ |- codom' <= codom {0 := b}).
Proof.
  intros wfΣ H; depind H; auto.
  - inv l. eexists (u {0 := t0}); intuition eauto.
    + eapply red1_red. constructor.
    + transitivity (codom {0 := t0}).
      * constructor. eapply eq_term_upto_univ_subst; trivial; try exact _.
        reflexivity.
      * constructor. eapply eq_term_upto_univ_subst; auto with pcuic.
        reflexivity.
  - specialize (IHcumul wfΣ).
    destruct IHcumul as [codom' [reddom' leq]] => //.
    exists codom'; intuition auto.
    now eapply red_step with v.
  - depelim r.
    + eexists ; intuition eauto.
    + solve_discr.
    + specialize (IHcumul _ _ _ _ _ wfΣ eq_refl).
      destruct IHcumul as [codom' [reddom' leq]].
      exists codom'; intuition auto.
      transitivity (codom {0 := r}); eauto.
      eapply red_cumul_inv. eapply (red_red Σ _ [vdef na b B] []) => //.
      * constructor. 1: now eapply red1_red.
        constructor.
      * rewrite -{1}(subst_empty 0 b). repeat constructor.
    + specialize (IHcumul _ _ _ _ _ wfΣ eq_refl).
      destruct IHcumul as [codom' [reddom' leq]].
      exists codom'; intuition auto.
    + specialize (IHcumul _ _ _ _ _ wfΣ eq_refl).
      destruct IHcumul as [codom' [reddom' leq]].
      exists codom'; intuition auto.
      eapply transitivity; [eassumption|].
      eapply red_cumul_inv.
      rewrite -{1 2}(subst_empty 0 b).
      eapply (untyped_substitution_red _ _ [vdef na b B] []); auto.
      repeat constructor.
Qed.

Lemma conv_Prod_l_inv {cf:checker_flags} (Σ : global_env_ext) Γ na dom codom T :
  wf Σ ->
  Σ ;;; Γ |- tProd na dom codom = T ->
  ∑ na' dom' codom', red Σ Γ T (tProd na' dom' codom') *
                     (Σ ;;; Γ |- dom = dom') * (Σ ;;; Γ ,, vass na dom |- codom = codom').
Proof.
  intros wfΣ H; depind H; auto.
  - inv e. exists na', a', b'; intuition eauto; constructor; auto.
  - depelim r.
    + solve_discr.
    + specialize (IHconv _ _ _ _ wfΣ eq_refl).
      destruct IHconv as [na' [dom' [codom' [[reddom' eqdom'] leq]]]].
      exists na', dom', codom'; intuition auto.
      * transitivity N1; eauto.
      * eapply conv_conv_ctx; eauto. constructor; cbnr.
        constructor.
        ++ reflexivity.
        ++ symmetry; eapply red_conv; auto.
    + specialize (IHconv _ _ _ _ wfΣ eq_refl).
      destruct IHconv as [na' [dom' [codom' [[reddom' eqdom'] leq]]]].
      exists na', dom', codom'; intuition auto.
      transitivity N2; eauto.
  - destruct IHconv as [na' [dom' [codom' [[reddom' eqdom'] leq]]]] => //.
    exists na', dom', codom'; intuition auto.
    now eapply red_step with v.
Qed.

Lemma cumul_Prod_l_inv {cf:checker_flags} (Σ : global_env_ext) Γ na dom codom T :
  wf Σ ->
  Σ ;;; Γ |- tProd na dom codom <= T ->
  ∑ na' dom' codom', red Σ Γ T (tProd na' dom' codom') *
           (eq_binder_annot na na') * (Σ ;;; Γ |- dom = dom') * (Σ ;;; Γ ,, vass na dom |- codom <= codom').
Proof.
  intros wfΣ H; depind H; auto.
  - inv l. exists na', a', b'; intuition eauto; constructor; auto.
  - depelim r.
    + solve_discr.
    + specialize (IHcumul _ _ _ _ wfΣ eq_refl).
      destruct IHcumul as [na' [dom' [codom' [[reddom' eqdom'] leq]]]].
      exists na', dom', codom'; intuition auto.
      * transitivity N1; eauto.
      * eapply cumul_conv_ctx; eauto. constructor; cbnr.
        constructor; auto. symmetry; eapply red_conv; auto.
    + specialize (IHcumul _ _ _ _ wfΣ eq_refl).
      destruct IHcumul as [na' [dom' [codom' [[reddom' eqdom'] leq]]]].
      exists na', dom', codom'; intuition auto.
      transitivity N2; eauto. eapply red_cumul; auto.
  - destruct IHcumul as [na' [dom' [codom' [[reddom' eqdom'] leq]]]] => //.
    exists na', dom', codom'; intuition auto.
    now eapply red_step with v.
Qed.

Lemma conv_Prod_r_inv {cf:checker_flags} (Σ : global_env_ext) Γ na' dom' codom' T :
  wf Σ ->
  Σ ;;; Γ |- T = tProd na' dom' codom' ->
  ∑ na dom codom, red Σ Γ T (tProd na dom codom) *
   (eq_binder_annot na na') * (Σ ;;; Γ |- dom = dom') * (Σ ;;; Γ ,, vass na' dom' |- codom = codom').
Proof.
  intros wfΣ H; depind H; auto.
  - inv e. exists na, a, b; intuition eauto; constructor; auto.
  - destruct IHconv as [na [dom [codom [[reddom' eqdom'] leq]]]] => //.
    exists na, dom, codom; intuition auto.
    now eapply red_step with v.
  - depelim r.
    + solve_discr.
    + specialize (IHconv _ _ _ _ wfΣ eq_refl).
      destruct IHconv as [na [dom [codom [[reddom' eqdom'] leq]]]].
      eexists _, _, _; intuition eauto.
      * transitivity N1; eauto. symmetry; apply red_conv; auto.
      * eapply conv_conv_ctx; eauto. constructor; cbnr.
        constructor; auto. symmetry. eapply red_conv; auto.
    + specialize (IHconv _ _ _ _ wfΣ eq_refl).
      destruct IHconv as [na [dom [codom [[reddom' eqdom'] leq]]]].
      eexists _, _, _; intuition eauto.
      transitivity N2; eauto. symmetry; eapply red_conv; auto.
Qed.

Lemma cumul_Prod_r_inv {cf:checker_flags} (Σ : global_env_ext) Γ na' dom' codom' T :
  wf Σ ->
  Σ ;;; Γ |- T <= tProd na' dom' codom' ->
  ∑ na dom codom, red Σ Γ T (tProd na dom codom) *
  (eq_binder_annot na na') * (Σ ;;; Γ |- dom = dom') * (Σ ;;; Γ ,, vass na' dom' |- codom <= codom').
Proof.
  intros wfΣ H; depind H; auto.
  - inv l. exists na, a, b; intuition eauto; constructor; auto.
  - destruct IHcumul as [na [dom [codom [[reddom' eqdom'] leq]]]] => //.
    exists na, dom, codom; intuition auto.
    now eapply red_step with v.
  - depelim r.
    + solve_discr.
    + specialize (IHcumul _ _ _ _ wfΣ eq_refl).
      destruct IHcumul as [na [dom [codom [[reddom' eqdom'] leq]]]].
      eexists _, _, _; intuition eauto.
      * transitivity N1; eauto. symmetry; apply red_conv; auto.
      * eapply cumul_conv_ctx; eauto. constructor; cbnr.
        constructor; auto. symmetry. eapply red_conv; auto.
    + specialize (IHcumul _ _ _ _ wfΣ eq_refl).
      destruct IHcumul as [na [dom [codom [[reddom' eqdom'] leq]]]].
      eexists _, _, _; intuition eauto.
      transitivity N2; eauto. eapply red_cumul_inv; auto.
Qed.

Lemma cumul_Prod_Sort_inv {cf:checker_flags} Σ Γ s na dom codom :
  Σ ;;; Γ |- tProd na dom codom <= tSort s -> False.
Proof.
  intros H; depind H; auto.
  - now inversion l.
  - depelim r.
    + solve_discr.
    + eapply IHcumul; reflexivity.
    + eapply IHcumul; reflexivity.
  - depelim r. solve_discr.
Qed.

Ltac splits := repeat split.
  
Lemma cumul_Prod_Prod_inv {cf:checker_flags} (Σ : global_env_ext) Γ na na' dom dom' codom codom' :
  wf Σ ->
  Σ ;;; Γ |- tProd na dom codom <= tProd na' dom' codom' ->
  (eq_binder_annot na na') × (Σ ;;; Γ |- dom = dom') × (Σ ;;; Γ ,, vass na' dom' |- codom <= codom').
Proof.
  intros wfΣ H; depind H; auto.
  - inv l. splits; auto; constructor; auto.
  - depelim r.
    + solve_discr.
    + destruct (IHcumul na na' N1 _ _ _ wfΣ eq_refl) as [e [? ?]].
      splits; auto. transitivity N1=> //. now eapply red_conv, red1_red.
    + destruct (IHcumul na na' _ _ N2 _ wfΣ eq_refl) as [? [? ?]].
      splits; auto. eapply cumul_trans. 1: auto. 2:eauto.
      eapply cumul_conv_ctx; eauto.
      * eapply red_cumul; eauto.
      * constructor; now auto with pcuic.
  - depelim r.
    + solve_discr.
    + destruct (IHcumul na na' _ _ _ _ wfΣ eq_refl) as [? [? ?]].
      splits; auto.
      * transitivity N1 => //. symmetry => //.
        now eapply red_conv, red1_red.
      * eapply cumul_red_ctx_inv. 1: auto. 1: eauto.
        constructor.
        -- eapply All2_local_env_red_refl.
        -- reflexivity.
        -- red. now eapply red1_red.
    + destruct (IHcumul na na' _ _ _ _ wfΣ eq_refl) as [? [? ?]].
      splits; auto.
      eapply cumul_trans with N2; auto.
      now eapply red1_red, red_cumul_inv in r.
Qed.

Section Inversions.
  Context {cf : checker_flags}.
  Context (Σ : global_env_ext).
  Context (wfΣ : wf Σ).

  Definition Is_conv_to_Arity Σ Γ T :=
    exists T', ∥ red Σ Γ T T' ∥ /\ isArity T'.

  Lemma arity_red_to_prod_or_sort :
    forall Γ T,
      isArity T ->
      (exists na A B, ∥ red Σ Γ T (tProd na A B) ∥) \/
      (exists u, ∥ red Σ Γ T (tSort u) ∥).
  Proof.
    intros Γ T a.
    induction T in Γ, a |- *. all: try contradiction.
    - right. eexists. constructor. reflexivity.
    - left. eexists _,_,_. constructor. reflexivity.
    - simpl in a. eapply IHT3 in a as [[na' [A [B [r]]]] | [u [r]]].
      + left. eexists _,_,_. constructor.
        eapply red_trans.
        * eapply red1_red. eapply red_zeta.
        * eapply untyped_substitution_red with (s := [T1]) (Γ' := []) in r.
          -- simpl in r. eassumption.
          -- assumption.
          -- instantiate (1 := [],, vdef na T1 T2).
             replace (untyped_subslet Γ [T1] ([],, vdef na T1 T2))
              with (untyped_subslet Γ [subst0 [] T1] ([],, vdef na T1 T2))
              by (now rewrite subst_empty).
             eapply untyped_cons_let_def.
             constructor.
      + right. eexists. constructor.
        eapply red_trans.
        * eapply red1_red. eapply red_zeta.
        * eapply untyped_substitution_red with (s := [T1]) (Γ' := []) in r.
          -- simpl in r. eassumption.
          -- assumption.
          -- replace (untyped_subslet Γ [T1] ([],, vdef na T1 T2))
              with (untyped_subslet Γ [subst0 [] T1] ([],, vdef na T1 T2))
              by (now rewrite subst_empty).
            eapply untyped_cons_let_def.
            constructor.
  Qed.

  Lemma Is_conv_to_Arity_inv :
    forall Γ T,
      Is_conv_to_Arity Σ Γ T ->
      (exists na A B, ∥ red Σ Γ T (tProd na A B) ∥) \/
      (exists u, ∥ red Σ Γ T (tSort u) ∥).
  Proof.
    intros Γ T [T' [r a]].
    induction T'.
    all: try contradiction.
    - right. eexists. eassumption.
    - left. eexists _, _, _. eassumption.
    - destruct r as [r1].
      eapply arity_red_to_prod_or_sort in a as [[na' [A [B [r2]]]] | [u [r2]]].
      + left. eexists _,_,_. constructor.
        eapply red_trans. all: eassumption.
      + right. eexists. constructor.
        eapply red_trans. all: eassumption.
  Qed.

  Lemma invert_red_sort Γ u v :
    red Σ Γ (tSort u) v -> v = tSort u.
  Proof.
    intros H. generalize_eq x (tSort u).
    induction H; simplify *.
    - depind r. solve_discr.
    - reflexivity.
    - rewrite IHclos_refl_trans2; auto.
  Qed.

  Lemma invert_cumul_sort_r Γ C u :
    Σ ;;; Γ |- C <= tSort u ->
               ∑ u', red Σ Γ C (tSort u') * leq_universe (global_ext_constraints Σ) u' u.
  Proof.
    intros Hcum.
    eapply cumul_alt in Hcum as [v [v' [[redv redv'] leqvv']]].
    eapply invert_red_sort in redv' as ->.
    depelim leqvv'. exists s. intuition eauto.
  Qed.

  Lemma invert_cumul_sort_l Γ C u :
    Σ ;;; Γ |- tSort u <= C ->
               ∑ u', red Σ Γ C (tSort u') * leq_universe (global_ext_constraints Σ) u u'.
  Proof.
    intros Hcum.
    eapply cumul_alt in Hcum as [v [v' [[redv redv'] leqvv']]].
    eapply invert_red_sort in redv as ->.
    depelim leqvv'. exists s'. intuition eauto.
  Qed.

  Lemma invert_red_prod Γ na A B v :
    red Σ Γ (tProd na A B) v ->
    ∑ A' B', (v = tProd na A' B') *
             (red Σ Γ A A') *
             (red Σ (vass na A :: Γ) B B').
  Proof.
    intros H. generalize_eq x (tProd na A B). revert na A B.
    induction H; simplify_dep_elim.
    - depelim r.
      + solve_discr.
      + do 2 eexists. repeat split; eauto with pcuic.
      + do 2 eexists. repeat split; eauto with pcuic.
    - do 2 eexists. repeat split; eauto with pcuic.
    - specialize (IHclos_refl_trans1 _ _ _ eq_refl).
      destruct IHclos_refl_trans1 as (? & ? & (-> & ?) & ?).
      specialize (IHclos_refl_trans2 _ _ _ eq_refl).
      destruct IHclos_refl_trans2 as (? & ? & (-> & ?) & ?).
      do 2 eexists. repeat split; eauto with pcuic.
      + now transitivity x.
      + transitivity x0; auto.
        eapply PCUICConfluence.red_red_ctx. 1: auto. 1: eauto.
        constructor.
        * eapply All2_local_env_red_refl.
        * reflexivity. 
        * red. auto.
  Qed.

  Lemma invert_cumul_prod_r Γ C na A B :
    Σ ;;; Γ |- C <= tProd na A B ->
    ∑ na' A' B', red Σ.1 Γ C (tProd na' A' B') *
                 eq_binder_annot na na' *
                 (Σ ;;; Γ |- A = A') *
                 (Σ ;;; (Γ ,, vass na A) |- B' <= B).
  Proof.
    intros Hprod.
    eapply cumul_alt in Hprod as [v [v' [[redv redv'] leqvv']]].
    eapply invert_red_prod in redv' as (A' & B' & ((-> & Ha') & ?)) => //.
    depelim leqvv'.
    do 3 eexists; intuition eauto.
    - now symmetry.
    - eapply conv_trans with A'; auto.
      eapply conv_sym; auto.
      constructor; auto.
    - eapply cumul_trans with B'; auto.
      + constructor. eapply leqvv'2.
      + now eapply red_cumul_inv.
  Qed.

  Lemma eq_term_upto_univ_arity_l :
    forall Re Rle u v,
      isArity u ->
      eq_term_upto_univ Σ Re Rle u v ->
      isArity v.
  Proof.
    intros Re Rle u v a e.
    induction u in a, v, Rle, e |- *. all: try contradiction.
    all: dependent destruction e.
    all: cbn in *; eauto.
  Qed.

  Lemma eq_term_upto_univ_arity_r :
    forall Re Rle u v,
      isArity u ->
      eq_term_upto_univ Σ Re Rle v u ->
      isArity v.
  Proof.
    intros Re Rle u v a e.
    induction u in a, v, Rle, e |- *. all: try contradiction.
    all: dependent destruction e.
    all: cbn in *; eauto.
  Qed.

  Lemma isArity_subst :
    forall u v k,
      isArity u ->
      isArity (u { k := v }).
  Proof.
    intros u v k h.
    induction u in v, k, h |- *. all: try contradiction.
    - simpl. constructor.
    - simpl in *. eapply IHu2. assumption.
    - simpl in *. eapply IHu3. assumption.
  Qed.

  Lemma isArity_red1 :
    forall Γ u v,
      red1 Σ Γ u v ->
      isArity u ->
      isArity v.
  Proof.
    intros Γ u v h a.
    induction u in Γ, v, h, a |- *. all: try contradiction.
    - dependent destruction h.
      apply (f_equal nApp) in H as eq. simpl in eq.
      rewrite nApp_mkApps in eq. simpl in eq.
      destruct args. 2: discriminate.
      simpl in H. discriminate.
    - dependent destruction h.
      + apply (f_equal nApp) in H as eq. simpl in eq.
        rewrite nApp_mkApps in eq. simpl in eq.
        destruct args. 2: discriminate.
        simpl in H. discriminate.
      + assumption.
      + simpl in *. eapply IHu2. all: eassumption.
    - dependent destruction h.
      + simpl in *. apply isArity_subst. assumption.
      + apply (f_equal nApp) in H as eq. simpl in eq.
        rewrite nApp_mkApps in eq. simpl in eq.
        destruct args. 2: discriminate.
        simpl in H. discriminate.
      + assumption.
      + assumption.
      + simpl in *. eapply IHu3. all: eassumption.
  Qed.
  
  Lemma isArity_red Γ u v :
    red Σ Γ u v ->
    isArity u ->
    isArity v.
  Proof.
    intros r isar.
    induction r using red_rect_n1; eauto using isArity_red1.
  Qed.

  Lemma invert_cumul_arity_r :
    forall (Γ : context) (C : term) T,
      isArity T ->
      Σ;;; Γ |- C <= T ->
      Is_conv_to_Arity Σ Γ C.
  Proof.
    intros Γ C T a h.
    apply cumul_alt in h as (?&?&(r1&r2)&?).
    exists x; split; [constructor; auto|].
    eapply eq_term_upto_univ_arity_r.
    2: eassumption.
    eapply isArity_red; eauto.
  Qed.

  Lemma invert_cumul_arity_l :
    forall (Γ : context) (C : term) T,
      isArity C ->
      Σ;;; Γ |- C <= T ->
      Is_conv_to_Arity Σ Γ T.
  Proof.
    intros Γ C T a h.
    apply cumul_alt in h as (?&?&(r1&r2)&?).
    exists x0; split; [constructor; auto|].
    eapply eq_term_upto_univ_arity_l.
    2: eassumption.
    eapply isArity_red; eauto.
  Qed.

  Lemma invert_cumul_prod_l Γ C na A B :
    Σ ;;; Γ |- tProd na A B <= C ->
               ∑ na' A' B', red Σ.1 Γ C (tProd na' A' B') *
                  eq_binder_annot na na' *
                  (Σ ;;; Γ |- A = A') *
                  (Σ ;;; (Γ ,, vass na A) |- B <= B').
  Proof.
    intros Hprod.
    eapply cumul_alt in Hprod as [v [v' [[redv redv'] leqvv']]].
    eapply invert_red_prod in redv as (A' & B' & ((-> & Ha') & ?)) => //.
    depelim leqvv'.
    do 3 eexists; intuition eauto.
    - eapply conv_trans with A'; auto.
      now constructor.
    - eapply cumul_trans with B'; eauto.
      + now eapply red_cumul.
      + now constructor; apply leqvv'2.
  Qed.

  Lemma invert_red_letin Γ C na d ty b :
    red Σ.1 Γ (tLetIn na d ty b) C ->
    (∑ d' ty' b',
     ((C = tLetIn na d' ty' b') *
      red Σ.1 Γ d d' *
      red Σ.1 Γ ty ty' *
      red Σ.1 (Γ ,, vdef na d ty) b b')) +
    (red Σ.1 Γ (subst10 d b) C)%type.
  Proof.
    generalize_eq x (tLetIn na d ty b).
    intros e H. revert na d ty b e.
    eapply clos_rt_rt1n_iff in H.
    induction H; simplify_dep_elim.
    + left; do 3 eexists. repeat split; eauto with pcuic.
    + depelim r; try specialize (IHclos_refl_trans_1n _ _ _ _ eq_refl) as
      [(? & ? & ? & ((? & ?) & ?) & ?)|?].
      - right. now apply clos_rt_rt1n_iff.
      - solve_discr.
      - left. do 3 eexists. repeat split; eauto with pcuic.
        * now transitivity r.
        * eapply PCUICConfluence.red_red_ctx; eauto.
          simpl. constructor; auto using All2_local_env_red_refl.
          simpl. split; auto.
      - right; auto. transitivity (b {0 := r}); auto.
        eapply (red_red _ _ [vass na ty] []); eauto.
        constructor. constructor.
      - left. do 3 eexists. repeat split; eauto with pcuic.
        * now transitivity r.
        * eapply PCUICConfluence.red_red_ctx; eauto.
          simpl. constructor; auto using All2_local_env_red_refl.
          simpl. split; auto.
      - right; auto.
      - left. do 3 eexists. repeat split; eauto with pcuic.
        now transitivity r.
      - right; auto.
        transitivity (r {0 := d}); auto.
        eapply (substitution_untyped_let_red _ _ [vdef na d ty] []); eauto.
        rewrite -{1}(subst_empty 0 d). constructor. constructor.
  Qed.

  Lemma cumul_red_r_inv :
    forall (Γ : context) T U U',
    Σ ;;; Γ |- T <= U ->
    red Σ.1 Γ U U' ->
    Σ ;;; Γ |- T <= U'.
  Proof.
    intros * cumtu red.
    apply cumul_alt in cumtu.
    destruct cumtu as [v [v' [[redl redr] eq]]].
    apply cumul_alt.
    destruct (red_confluence wfΣ redr red) as [nf [nfl nfr]].
    eapply (fill_le _ wfΣ) in eq. 3:eapply nfl. 2:eapply reflexivity.
    destruct eq as [t'' [u'' [[l r] eq]]].
    exists t''. exists u''. repeat split; auto.
    - now transitivity v.
    - now transitivity nf.
  Qed.

  Lemma cumul_red_l_inv :
    forall (Γ : context) T T' U,
    Σ ;;; Γ |- T <= U ->
    red Σ.1 Γ T T' ->
    Σ ;;; Γ |- T' <= U.
  Proof.
    intros * cumtu red.
    apply cumul_alt in cumtu.
    destruct cumtu as [v [v' [[redl redr] eq]]].
    apply cumul_alt.
    destruct (red_confluence wfΣ redl red) as [nf [nfl nfr]].
    eapply (fill_le _ wfΣ) in eq. 2:eapply nfl. 2:eapply reflexivity.
    destruct eq as [t'' [u'' [[l r] eq]]].
    exists t''. exists u''. repeat split; auto.
    - now transitivity nf.
    - now transitivity v'.
  Qed.

  Lemma invert_cumul_letin_l Γ C na d ty b :
    Σ ;;; Γ |- tLetIn na d ty b <= C ->
    Σ ;;; Γ |- subst10 d b <= C.
  Proof.
    intros Hlet.
    eapply cumul_red_l_inv; eauto.
    eapply red1_red; constructor.
  Qed.

  Lemma invert_cumul_letin_r Γ C na d ty b :
    Σ ;;; Γ |- C <= tLetIn na d ty b ->
    Σ ;;; Γ |- C <= subst10 d b.
  Proof.
    intros Hlet.
    eapply cumul_red_r_inv; eauto.
    eapply red1_red; constructor.
  Qed.


  Lemma conv_red_l_inv :
    forall (Γ : context) T T' U,
    Σ ;;; Γ |- T = U ->
    red Σ.1 Γ T T' ->
    Σ ;;; Γ |- T' = U.
  Proof.
    intros * cumtu red.
    apply conv_alt_red in cumtu.
    destruct cumtu as [v [v' [[redl redr] eq]]].
    apply conv_alt_red.
    destruct (red_confluence wfΣ redl red) as [nf [nfl nfr]].
    eapply (fill_eq _ wfΣ) in eq. 2:eapply nfl. 2:eapply reflexivity.
    destruct eq as [t'' [u'' [[l r] eq]]].
    exists t''. exists u''. repeat split; auto.
    - now transitivity nf.
    - now transitivity v'.
  Qed.

  Lemma invert_conv_letin_l Γ C na d ty b :
    Σ ;;; Γ |- tLetIn na d ty b = C ->
    Σ ;;; Γ |- subst10 d b = C.
  Proof.
    intros Hlet.
    eapply conv_red_l_inv; eauto.
    eapply red1_red; constructor.
  Qed.

  Lemma invert_conv_letin_r Γ C na d ty b :
    Σ ;;; Γ |- C = tLetIn na d ty b ->
    Σ ;;; Γ |- C = subst10 d b.
  Proof.
    intros Hlet. symmetry; symmetry in Hlet.
    now eapply invert_conv_letin_l.
  Qed.

  Lemma app_mkApps :
    forall u v t l,
      isApp t = false ->
      tApp u v = mkApps t l ->
      ∑ l',
        (l = l' ++ [v]) ×
        u = mkApps t l'.
  Proof.
    intros u v t l h e.
    induction l in u, v, t, e, h |- * using list_rect_rev.
    - cbn in e. subst. cbn in h. discriminate.
    - rewrite <- mkApps_nested in e. cbn in e.
      exists l. inversion e. subst. auto.
  Qed.

  (* TODO deprecate? #[deprecated(note="use red_mkApps_tInd")] *)
  Notation invert_red_ind := red_mkApps_tInd.

  Lemma invert_cumul_ind_l :
    forall Γ ind ui l T,
      Σ ;;; Γ |- mkApps (tInd ind ui) l <= T ->
      ∑ ui' l',
        red Σ.1 Γ T (mkApps (tInd ind ui') l') ×
        R_global_instance Σ (eq_universe Σ) (leq_universe Σ) (IndRef ind) #|l| ui ui' ×
        All2 (fun a a' => Σ ;;; Γ |- a = a') l l'.
  Proof.
    intros Γ ind ui l T h.
    eapply cumul_alt in h as [v [v' [[redv redv'] leqvv']]].
    eapply invert_red_ind in redv as [l' [? ha]]; auto. subst.
    eapply eq_term_upto_univ_mkApps_l_inv in leqvv'
      as [u [l'' [[e ?] ?]]].
    subst.
    dependent destruction e.
    eexists _,_. split ; eauto. split ; auto.
    - now rewrite (All2_length _ _ ha).
    - eapply All2_trans.
      * intros x y z h1 h2. eapply conv_trans ; eauto.
      * eapply All2_impl ; eauto.
      * eapply All2_impl ; eauto.
        intros x y h. eapply conv_refl. assumption.
  Qed.

  Lemma invert_cumul_ind_r :
    forall Γ ind ui l T,
      Σ ;;; Γ |- T <= mkApps (tInd ind ui) l ->
      ∑ ui' l',
        red Σ.1 Γ T (mkApps (tInd ind ui') l') ×
        R_global_instance Σ (eq_universe Σ) (leq_universe Σ) (IndRef ind) #|l| ui' ui ×
        All2 (fun a a' => Σ ;;; Γ |- a = a') l l'.
  Proof.
    intros Γ ind ui l T h.
    eapply cumul_alt in h as [v [v' [[redv redv'] leqvv']]].
    eapply invert_red_ind in redv' as [l' [? ?]]; auto. subst.
    eapply eq_term_upto_univ_mkApps_r_inv in leqvv'
      as [u [l'' [[e ?] ?]]].
    subst.
    dependent destruction e.
    eexists _,_. split ; eauto. split ; auto.
    - rewrite (All2_length _ _ a); auto.
    - eapply All2_trans.
      * intros x y z h1 h2. eapply conv_trans ; eauto.
      * eapply All2_impl ; eauto.
      * eapply All2_swap.
        eapply All2_impl ; eauto.
        intros x y h. eapply conv_sym; auto. now constructor.
  Qed.

End Inversions.

Lemma assumption_context_app Γ Γ' :
  assumption_context (Γ' ,,, Γ) ->
  assumption_context Γ * assumption_context Γ'.
Proof.
  induction Γ; simpl; split; try constructor; auto.
  - depelim H. constructor; auto. now eapply IHΓ.
  - depelim H. now eapply IHΓ.
Qed.

(* Unused... *)
Lemma it_mkProd_or_LetIn_ass_inv {cf : checker_flags} (Σ : global_env_ext) Γ ctx ctx' s s' :
  wf Σ ->
  assumption_context ctx ->
  assumption_context ctx' ->
  Σ ;;; Γ |- it_mkProd_or_LetIn ctx (tSort s) <= it_mkProd_or_LetIn ctx' (tSort s') ->
  context_relation (fun ctx ctx' => conv_decls Σ (Γ ,,, ctx) (Γ ,,, ctx')) ctx ctx' *
   leq_term Σ.1 Σ (tSort s) (tSort s').
Proof.
  intros wfΣ.
  revert Γ ctx' s s'.
  induction ctx using rev_ind.
  - intros. destruct ctx' using rev_ind.
    + simpl in X.
      eapply cumul_Sort_inv in X.
      split; constructor; auto.
    + destruct x as [na [b|] ty].
      * elimtype False.
        apply assumption_context_app in H0.
        destruct H0. inv a0.
      * rewrite it_mkProd_or_LetIn_app in X.
        apply assumption_context_app in H0 as [H0 _].
        specialize (IHctx' H0).
        simpl in IHctx'. simpl in X.
        unfold mkProd_or_LetIn in X. simpl in X.
        eapply cumul_Sort_Prod_inv in X. depelim X.
  - intros.
    rewrite it_mkProd_or_LetIn_app in X.
    simpl in X.
    eapply assumption_context_app in H as [H H'].
    destruct x as [na [b|] ty].
    + elimtype False. inv H'.
    + rewrite /mkProd_or_LetIn /= in X.
      destruct ctx' using rev_ind.
      * simpl in X.
        now eapply cumul_Prod_Sort_inv in X.
      * eapply assumption_context_app in H0 as [H0 Hx].
        destruct x as [na' [b'|] ty']; [elimtype False; inv Hx|].
        rewrite it_mkProd_or_LetIn_app in X.
        rewrite /= /mkProd_or_LetIn /= in X.
        eapply cumul_Prod_Prod_inv in X as [eqann [Hdom Hcodom]]; auto.
        specialize (IHctx (Γ ,, vass na' ty') l0 s s' H H0 Hcodom).
        clear IHctx'.
        intuition auto.
        eapply context_relation_app_inv.
        ** eapply (context_relation_length _ _ _ a).
        ** constructor; [constructor|constructor; auto].
        ** unshelve eapply (context_relation_impl _ a).
           simpl; intros Γ0 Γ' d d'.
           rewrite !app_context_assoc.
           intros X; destruct X.
           *** constructor; auto.
              eapply conv_conv_ctx; eauto.
              eapply conv_context_app_same.
              constructor; [apply conv_ctx_refl|constructor; auto]; now symmetry.
           *** constructor; auto.
              eapply conv_conv_ctx; eauto.
              eapply conv_context_app_same.
              constructor; [apply conv_ctx_refl|constructor]; now symmetry.
           *** constructor; auto; eapply conv_conv_ctx; eauto.
              **** eapply conv_context_app_same.
                constructor; [apply conv_ctx_refl|constructor;auto];
                now symmetry.
              **** eapply conv_context_app_same.
                constructor; [apply conv_ctx_refl|constructor;auto];
                now symmetry.
Qed.

(** Injectivity of products, the essential property of cumulativity needed for subject reduction. *)
Lemma cumul_Prod_inv {cf:checker_flags} Σ Γ na na' A B A' B' :
  wf Σ.1 -> wf_local Σ Γ ->
  Σ ;;; Γ |- tProd na A B <= tProd na' A' B' ->
   (eq_binder_annot na na' * (Σ ;;; Γ |- A = A') * (Σ ;;; Γ ,, vass na' A' |- B <= B'))%type.
Proof.
  intros wfΣ wfΓ H; depind H.
  - depelim l.
    splits; auto.
    all: now constructor.

  - depelim r.
    + solve_discr.
    + specialize (IHcumul _ _ _ _ _ _ wfΣ wfΓ eq_refl).
      intuition auto.
      econstructor 2; eauto.
    + specialize (IHcumul _ _ _ _ _ _ wfΣ wfΓ eq_refl).
      intuition auto. apply cumul_trans with N2.
      * auto.
      * eapply cumul_conv_ctx; eauto.
        -- econstructor 2. 1: eauto.
           constructor. reflexivity.
        -- constructor. 1: now apply conv_ctx_refl.
           constructor; auto.
      * auto.

  - depelim r.
    + solve_discr.
    + specialize (IHcumul _ _ _ _ _ _ wfΣ wfΓ eq_refl).
      intuition auto.
      * econstructor 3. 2:eauto. auto.
      * eapply cumul_conv_ctx in b. 1: eauto. 1: auto.
        constructor. 1: eapply conv_ctx_refl.
        constructor; auto. eapply conv_sym; auto.
    + specialize (IHcumul _ _ _ _ _ _ wfΣ wfΓ eq_refl).
      intuition auto. apply cumul_trans with N2. 1-2: auto.
      eapply cumul_red_r; eauto. reflexivity.
Qed.

Lemma tProd_it_mkProd_or_LetIn na A B ctx s :
  tProd na A B = it_mkProd_or_LetIn ctx (tSort s) ->
  { ctx' & ctx = (ctx' ++ [vass na A]) /\
           destArity [] B = Some (ctx', s) }.
Proof.
  intros. exists (removelast ctx).
  revert na A B s H.
  induction ctx using rev_ind; intros; noconf H.
  rewrite it_mkProd_or_LetIn_app in H. simpl in H.
  destruct x as [na' [b'|] ty']; noconf H; simpl in *.
  rewrite removelast_app. 1: congruence.
  simpl. rewrite app_nil_r. intuition auto.
  rewrite destArity_it_mkProd_or_LetIn. simpl. now rewrite app_context_nil_l.
Qed.

Section Inversions.
  Context {cf : checker_flags}.
  Context (Σ : global_env_ext) (wfΣ : wf Σ).

  Lemma cumul_App_r {Γ f u v} :
    Σ ;;; Γ |- u = v ->
    Σ ;;; Γ |- tApp f u <= tApp f v.
  Proof.
    intros h.
    induction h.
    - eapply cumul_refl. constructor.
      + apply eq_term_upto_univ_refl; typeclasses eauto.
      + assumption.
    -  eapply cumul_red_l ; try eassumption.
       econstructor. assumption.
    - eapply cumul_red_r ; try eassumption.
      econstructor. assumption.
  Qed.
  
  Lemma cumul_mkApps Γ hd args hd' args' :
    Σ;;; Γ |- hd <= hd' ->
    All2 (conv Σ Γ) args args' ->
    Σ;;; Γ |- mkApps hd args <= mkApps hd' args'.
  Proof.
    intros cum cum_args.
    revert hd hd' cum.
    induction cum_args; intros hd hd' cum; auto.
    cbn.
    apply IHcum_args.
    eapply cumul_trans; auto.
    - eapply cumul_App_l; eauto.
    - eapply cumul_App_r; eauto.
  Qed.

  Lemma conv_App_r {Γ f x y} :
    Σ ;;; Γ |- x = y ->
    Σ ;;; Γ |- tApp f x = tApp f y.
  Proof.
    intros h.
    induction h.
    - constructor. constructor.
      + apply eq_term_upto_univ_refl; typeclasses eauto.
      + assumption.
    - eapply conv_red_l ; eauto.
      econstructor. assumption.
    - eapply conv_red_r ; eauto.
      econstructor. assumption.
  Qed.

  Lemma conv_Prod_l:
    forall {Γ na na' A1 A2 B},
      eq_binder_annot na na' ->
      Σ ;;; Γ |- A1 = A2 ->
      Σ ;;; Γ |- tProd na A1 B = tProd na' A2 B.
  Proof.
    intros Γ na na' eqna A1 A2 B h.
    induction h.
    - constructor. constructor.
      + assumption.
      + assumption.
      + apply eq_term_refl.
    - eapply conv_red_l ; eauto.
      econstructor. assumption.
    - eapply conv_red_r ; eauto.
      econstructor. assumption.
  Qed.

  Lemma conv_Prod_r  :
    forall {Γ na A B1 B2},
      Σ ;;; Γ ,, vass na A |- B1 = B2 ->
      Σ ;;; Γ |- tProd na A B1 = tProd na A B2.
  Proof.
    intros Γ na A B1 B2 h.
    induction h.
    - constructor. constructor.
      + reflexivity.
      + apply eq_term_refl.
      + assumption.
    - eapply conv_red_l ; eauto.
      econstructor. assumption.
    - eapply conv_red_r ; eauto.
      econstructor. assumption.
  Qed.

  Lemma cumul_Prod_l:
    forall {Γ na na' A1 A2 B},
      eq_binder_annot na na' ->
      Σ ;;; Γ |- A1 = A2 ->
      Σ ;;; Γ |- tProd na A1 B <= tProd na' A2 B.
  Proof.
    intros Γ na na' eqna A1 A2 B h.
    induction h.
    - constructor. constructor.
      + assumption.
      + assumption.
      + apply leq_term_refl.
    - eapply cumul_red_l ; eauto.
      econstructor. assumption.
    - eapply cumul_red_r ; eauto.
      econstructor. assumption.
  Qed.

  Lemma cumul_Prod_r :
    forall {Γ na A B1 B2},
      Σ ;;; Γ ,, vass na A |- B1 <= B2 ->
      Σ ;;; Γ |- tProd na A B1 <= tProd na A B2.
  Proof.
    intros Γ na A B1 B2 h.
    induction h.
    - eapply cumul_refl. constructor.
      + reflexivity. 
      + apply eq_term_refl.
      + assumption.
    - eapply cumul_red_l ; try eassumption.
      econstructor. assumption.
    - eapply cumul_red_r ; try eassumption.
      econstructor. assumption.
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
    destruct leq; constructor.
    + now eapply red_conv.
    + now eapply red_cumul.
  Qed.

  Lemma red_conv_cum_r {leq Γ u v} :
    red (fst Σ) Γ u v -> conv_cum leq Σ Γ v u.
  Proof.
   induction 1.
   - destruct leq; constructor.
     + now eapply conv_red_r.
     + now eapply cumul_red_r.
   - reflexivity.
   - etransitivity; tea.
  Qed.

  Lemma conv_cum_Prod leq Γ na1 na2 A1 A2 B1 B2 :
    eq_binder_annot na1 na2 ->
    Σ ;;; Γ |- A1 = A2 ->
    conv_cum leq Σ (Γ,, vass na1 A1) B1 B2 ->
    conv_cum leq Σ Γ (tProd na1 A1 B1) (tProd na2 A2 B2).
  Proof.
    intros hann h1 h2; destruct leq.
    - simpl in *. destruct h2 as [h2]. constructor.
      eapply conv_trans => //.
      + eapply conv_Prod_r. eassumption.
      + eapply conv_Prod_l; eassumption.
    - simpl in *. destruct h2 as [h2]. constructor.
      eapply cumul_trans.
      + auto.
      + eapply cumul_Prod_r. eassumption.
      + eapply conv_cumul. eapply conv_Prod_l; assumption.
  Qed.

  Lemma Prod_conv_cum_inv : 
    forall {Γ leq na1 na2 A1 A2 B1 B2},
    conv_cum leq Σ Γ (tProd na1 A1 B1) (tProd na2 A2 B2) ->
      eq_binder_annot na1 na2 /\ ∥ Σ ;;; Γ |- A1 = A2 ∥ /\
      conv_cum leq Σ (Γ,, vass na1 A1) B1 B2.
  Proof.
    intros *; destruct leq; simpl.
    - intros [[na1' [A1' [B1' [[[Hred eqann] eqA] eqB]]]]%conv_Prod_r_inv]. 2: assumption.
      apply invert_red_prod in Hred. 2: assumption.
      destruct Hred as [? [? [[[= ? ?%eq_sym ?%eq_sym] redA] redB]]].
      subst.
      assert (Σ;;;Γ |- A1 = A2) as HA by
        (etransitivity; [apply red_conv, redA | assumption]).
      split; auto.        
      split; constructor. 1: assumption.
      etransitivity. 1: apply red_conv, redB. 
      eapply conv_conv_ctx. 1,2 : eassumption.
      apply ctx_rel_vass. 1: reflexivity.
      now constructor.
    - intros [[eqann [eqA cumB]]%cumul_Prod_Prod_inv]. 2: assumption.
      split; auto; split; constructor. 1: assumption.
      eapply cumul_conv_ctx. 1,2: eassumption.
      apply ctx_rel_vass. 1: reflexivity.
      now constructor.  
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
  
  Lemma conv_cum_red leq Γ t1 t2 t1' t2' :
    red Σ Γ t1' t1 ->
    red Σ Γ t2' t2 ->
    conv_cum leq Σ Γ t1 t2 ->
    conv_cum leq Σ Γ t1' t2'.
  Proof.
    intros r1 r2 cc.
    destruct leq; cbn in *.
    - destruct cc.
      constructor.
      eapply red_conv_conv; eauto.
      apply conv_sym.
      eapply red_conv_conv; eauto.
      apply conv_sym.
      auto.
    - destruct cc.
      constructor.
      eapply red_cumul_cumul; eauto.
      eapply red_cumul_cumul_inv; eauto.
  Qed.

  Lemma conv_cum_red_conv leq Γ Γ' t1 t2 t1' t2' :
    conv_context Σ Γ Γ' ->
    red Σ Γ t1' t1 ->
    red Σ Γ' t2' t2 ->
    conv_cum leq Σ Γ t1 t2 ->
    conv_cum leq Σ Γ t1' t2'.
  Proof.
    intros conv_ctx r1 r2 cc.
    eapply conv_cum_red; [now eauto|reflexivity|].
    eapply conv_cum_conv_ctx; eauto.
    2: apply conv_context_sym; eauto.
    eapply conv_cum_red; [reflexivity|now eauto|].
    eapply conv_cum_conv_ctx; eauto.
  Qed.

  Lemma conv_cum_red_inv leq Γ t1 t2 t1' t2' :
    red Σ Γ t1 t1' ->
    red Σ Γ t2 t2' ->
    conv_cum leq Σ Γ t1 t2 ->
    conv_cum leq Σ Γ t1' t2'.
  Proof.
    intros r1 r2 cc.
    destruct leq; cbn in *.
    - destruct cc.
      constructor.
      eapply conv_red_l_inv; [eauto| |eauto].
      apply conv_sym.
      eapply conv_red_l_inv; [eauto| |eauto].
      apply conv_sym.
      auto.
    - destruct cc.
      constructor.
      eapply cumul_red_l_inv; [eauto| |eauto].
      eapply cumul_red_r_inv; [eauto| |eauto].
      auto.
  Qed.
  
  Lemma conv_cum_red_conv_inv leq Γ Γ' t1 t2 t1' t2' :
    conv_context Σ Γ Γ' ->
    red Σ Γ t1 t1' ->
    red Σ Γ' t2 t2' ->
    conv_cum leq Σ Γ t1 t2 ->
    conv_cum leq Σ Γ t1' t2'.
  Proof.
    intros conv_ctx r1 r2 cc.
    eapply conv_cum_red_inv; [now eauto|reflexivity|].
    eapply conv_cum_conv_ctx; eauto.
    2: apply conv_context_sym; eauto.
    eapply conv_cum_red_inv; [reflexivity|now eauto|].
    eapply conv_cum_conv_ctx; eauto.
  Qed.
  
  Lemma conv_cum_red_iff leq Γ t1 t2 t1' t2' :
    red Σ Γ t1' t1 ->
    red Σ Γ t2' t2 ->
    conv_cum leq Σ Γ t1 t2 <-> conv_cum leq Σ Γ t1' t2'.
  Proof.
    intros r1 r2.
    split; intros cc.
    - eapply conv_cum_red; eauto.
    - eapply conv_cum_red_inv; eauto.
  Qed.

  Lemma conv_cum_red_conv_iff leq Γ Γ' t1 t2 t1' t2' :
    conv_context Σ Γ Γ' ->
    red Σ Γ t1' t1 ->
    red Σ Γ' t2' t2 ->
    conv_cum leq Σ Γ t1 t2 <-> conv_cum leq Σ Γ t1' t2'.
  Proof.
    intros conv_ctx r1 r2.
    split; intros cc.
    - eapply conv_cum_red_conv; eauto.
    - eapply conv_cum_red_conv_inv; eauto.
  Qed.

  Lemma cumul_Case_c :
    forall Γ indn p brs u v,
      Σ ;;; Γ |- u = v ->
      Σ ;;; Γ |- tCase indn p u brs <= tCase indn p v brs.
  Proof.
    intros Γ [ind n] p brs u v h.
    induction h.
    - constructor. constructor.
      + eapply eq_term_refl.
      + assumption.
      + eapply All2_same.
        intros. split ; eauto.
        reflexivity.
    - eapply cumul_red_l ; eauto.
      constructor. assumption.
    - eapply cumul_red_r ; eauto.
      constructor. assumption.
  Qed.

  Lemma cumul_Proj_c :
    forall Γ p u v,
      Σ ;;; Γ |- u = v ->
      Σ ;;; Γ |- tProj p u <= tProj p v.
  Proof.
    intros Γ p u v h.
    induction h.
    - eapply cumul_refl. constructor. assumption.
    - eapply cumul_red_l ; try eassumption.
      econstructor. assumption.
    - eapply cumul_red_r ; try eassumption.
      econstructor. assumption.
  Qed.

  Lemma conv_App_l :
    forall {Γ f g x},
      Σ ;;; Γ |- f = g ->
      Σ ;;; Γ |- tApp f x = tApp g x.
  Proof.
    intros Γ f g x h.
    induction h.
    - constructor. constructor.
      + apply eq_term_eq_term_napp; auto. typeclasses eauto.
      + apply eq_term_refl.
    - eapply conv_red_l ; eauto.
      econstructor. assumption.
    - eapply conv_red_r ; eauto.
      econstructor. assumption.
  Qed.

  Lemma App_conv :
    forall Γ t1 t2 u1 u2,
      Σ ;;; Γ |- t1 = t2 ->
      Σ ;;; Γ |- u1 = u2 ->
      Σ ;;; Γ |- tApp t1 u1 = tApp t2 u2.
  Proof.
    intros. etransitivity.
    - eapply conv_App_l. eassumption.
    - apply conv_App_r. assumption.
  Qed.

  Lemma mkApps_conv_args Γ f f' u v :
    Σ ;;; Γ |- f = f' ->
    All2 (fun x y => Σ ;;; Γ |- x = y) u v ->
    Σ ;;; Γ |- mkApps f u = mkApps f' v.
  Proof.
    move=> convf cuv. induction cuv in f, f', convf |- *.
    - auto.
    - simpl. apply IHcuv.
      now apply App_conv.
  Qed.

  Lemma conv_Case_p :
    forall Γ indn c brs u v,
      Σ ;;; Γ |- u = v ->
      Σ ;;; Γ |- tCase indn u c brs = tCase indn v c brs.
  Proof.
    intros Γ [ind n] c brs u v h.
    induction h.
    - constructor. constructor.
      + assumption.
      + eapply eq_term_refl.
      + eapply All2_same.
        intros. split ; eauto. reflexivity.
    - eapply conv_red_l ; eauto.
      constructor. assumption.
    - eapply conv_red_r ; eauto.
      constructor. assumption.
  Qed.

  Lemma conv_Case_c :
    forall Γ indn p brs u v,
      Σ ;;; Γ |- u = v ->
      Σ ;;; Γ |- tCase indn p u brs = tCase indn p v brs.
  Proof.
    intros Γ [ind n] p brs u v h.
    induction h.
    - constructor. constructor.
      + eapply eq_term_refl.
      + assumption.
      + eapply All2_same.
        intros. split ; eauto. reflexivity.
    - eapply conv_red_l ; eauto.
      constructor. assumption.
    - eapply conv_red_r ; eauto.
      constructor. assumption.
  Qed.

  Lemma conv_Case_one_brs :
    forall Γ indn p c brs brs',
      OnOne2 (fun u v => u.1 = v.1 × Σ ;;; Γ |- u.2 = v.2) brs brs' ->
      Σ ;;; Γ |- tCase indn p c brs = tCase indn p c brs'.
  Proof.
    intros Γ [ind n] p c brs brs' h.
    apply OnOne2_split in h as [[m br] [[m' br'] [l1 [l2 [[? h] [? ?]]]]]].
    simpl in *. subst.
    induction h.
    - constructor. constructor.
      + reflexivity.
      + reflexivity.
      + apply All2_app.
        * apply All2_same. intros. intuition reflexivity.
        * constructor.
          -- simpl. intuition reflexivity.
          -- apply All2_same. intros. intuition reflexivity.
    - eapply conv_red_l ; eauto.
      constructor. apply OnOne2_app. constructor. simpl.
      intuition eauto.
    - eapply conv_red_r ; eauto.
      constructor. apply OnOne2_app. constructor. simpl.
      intuition eauto.
  Qed.

  Lemma conv_Case_brs :
    forall Γ indn p c brs brs',
      All2 (fun u v => u.1 = v.1 × Σ ;;; Γ |- u.2 = v.2) brs brs' ->
      Σ ;;; Γ |- tCase indn p c brs = tCase indn p c brs'.
  Proof.
    intros Γ [ind n] p c brs brs' h.
    apply All2_many_OnOne2 in h.
    induction h.
    - reflexivity.
    - etransitivity.
      + eassumption.
      + apply conv_Case_one_brs. assumption.
  Qed.

  Lemma conv_Case :
    forall Γ indn p p' c c' brs brs',
      Σ ;;; Γ |- p = p' ->
      Σ ;;; Γ |- c = c' ->
      All2 (fun u v => u.1 = v.1 × Σ ;;; Γ |- u.2 = v.2) brs brs' ->
      Σ ;;; Γ |- tCase indn p c brs = tCase indn p' c' brs'.
  Proof.
    intros Γ [ind n] p p' c c' brs brs' hp hc hbrs.
    etransitivity.
    - eapply conv_Case_p. eassumption.
    - etransitivity.
      + eapply conv_Case_c. eassumption.
      + apply conv_Case_brs. all: assumption.
  Qed.

  Lemma conv_Proj_c :
    forall Γ p u v,
      Σ ;;; Γ |- u = v ->
      Σ ;;; Γ |- tProj p u = tProj p v.
  Proof.
    intros Γ p u v h.
    induction h.
    - now repeat constructor.
    - eapply conv_red_l ; try eassumption.
      econstructor. assumption.
    - eapply conv_red_r ; try eassumption.
      econstructor. assumption.
  Qed.

  Lemma conv_Fix_one_type :
    forall Γ mfix mfix' idx,
      wf Σ.1 ->
      OnOne2 (fun u v =>
        Σ ;;; Γ |- dtype u = dtype v ×
        dbody u = dbody v ×
        (rarg u = rarg v) *
        eq_binder_annot (dname u) (dname v)
      ) mfix mfix' ->
      Σ ;;; Γ |- tFix mfix idx = tFix mfix' idx.
  Proof.
    intros Γ mfix mfix' idx wΣ h.
    apply OnOne2_split in h
      as [[na ty bo ra] [[na' ty' bo' ra'] [l1 [l2 [[h [? ?]] [? ?]]]]]].
    simpl in *. subst.
    induction h.
    - constructor. constructor.
      apply All2_app.
      + apply All2_same. intros. intuition reflexivity.
      + constructor.
        * simpl. intuition reflexivity.
        * apply All2_same. intros. intuition reflexivity.
    - eapply conv_red_l ; eauto.
      constructor. apply OnOne2_app. constructor. simpl.
      intuition eauto.
    - eapply conv_red_r ; eauto.
      constructor. apply OnOne2_app. constructor. simpl.
      intuition eauto.
  Qed.

  Lemma conv_Fix_types :
    forall Γ mfix mfix' idx,
      wf Σ.1 ->
      All2 (fun u v =>
        Σ ;;; Γ |- dtype u = dtype v ×
        dbody u = dbody v ×
        (rarg u = rarg v) *
        (eq_binder_annot (dname u) (dname v))
      ) mfix mfix' ->
      Σ ;;; Γ |- tFix mfix idx = tFix mfix' idx.
  Proof.
    intros Γ mfix mfix' idx wΣ h.
    apply All2_many_OnOne2 in h.
    induction h.
    - reflexivity.
    - etransitivity.
      + eassumption.
      + apply conv_Fix_one_type. all: assumption.
  Qed.

  Lemma conv_Fix_one_body :
    forall Γ mfix mfix' idx,
      wf Σ.1 ->
      OnOne2 (fun u v =>
        dtype u = dtype v ×
        Σ ;;; Γ ,,, fix_context mfix |- dbody u = dbody v ×
        (rarg u = rarg v) *
        (eq_binder_annot (dname u) (dname v))
      ) mfix mfix' ->
      Σ ;;; Γ |- tFix mfix idx = tFix mfix' idx.
  Proof.
    intros Γ mfix mfix' idx wΣ h.
    apply OnOne2_split in h
      as [[na ty bo ra] [[na' ty' bo' ra'] [l1 [l2 [[? [h [? ?]]] [? ?]]]]]].
    simpl in *. subst.
    induction h.
    - constructor. constructor.
      apply All2_app.
      + apply All2_same. intros. intuition reflexivity.
      + constructor.
        * simpl. intuition reflexivity.
        * apply All2_same. intros. intuition reflexivity.
    - eapply conv_red_l ; eauto.
      eapply fix_red_body. apply OnOne2_app. constructor. simpl.
      intuition eauto.
      rewrite fix_context_fix_context_alt in r.
      rewrite map_app in r. simpl in r.
      unfold def_sig at 2 in r. simpl in r.
      rewrite fix_context_fix_context_alt.
      rewrite map_app. simpl.
      unfold def_sig at 2. simpl.
      assumption.
    - rewrite fix_context_fix_context_alt in r.
      rewrite map_app in r. simpl in r.
      unfold def_sig at 2 in r. simpl in r.
      eapply red1_eq_context_upto_l in r as [v' [r e]].
      4:{
        instantiate (1 := Γ ,,, fix_context_alt (map def_sig l1 ++ (na', ty') :: map def_sig l2)).
        eapply eq_context_upto_cat.
        - eapply eq_context_upto_refl. instantiate (1 := eq). auto.
        - unfold fix_context_alt. eapply eq_context_upto_rev'.
          rewrite 2!mapi_app. cbn.
          eapply eq_context_upto_cat.
          + constructor; auto.
            * eapply eq_term_upto_univ_refl. all: auto.
            * eapply eq_context_upto_refl. auto.
          + eapply eq_context_upto_refl. auto.
      }
      2: auto.
      2:{ intros ? ? ? e. apply eq_univ_make in e. subst. reflexivity. }
      etransitivity; tea.
      eapply conv_red_r ; revgoals.
      + eapply fix_red_body. apply OnOne2_app. constructor. simpl.
        split.
        * rewrite fix_context_fix_context_alt.
          rewrite map_app. simpl.
          unfold def_sig at 2. simpl.
          instantiate (1 := mkdef _ na' ty' v' ra'). simpl.
          exact r.
        * simpl. reflexivity.
      + constructor. constructor.
        apply All2_app.
        * apply All2_same. intros. intuition reflexivity.
        * constructor.
          -- simpl. intuition eauto.
             ++ eapply eq_term_upto_univ_refl.
                all: apply eq_universe_refl.
             ++ eapply upto_eq_impl. 3: assumption.
                all: apply eq_universe_refl.
          -- apply All2_same. intros. intuition reflexivity.
  Qed.

  Lemma conv_Fix_bodies :
    forall Γ mfix mfix' idx,
      wf Σ.1 ->
      All2 (fun u v =>
        dtype u = dtype v ×
        Σ ;;; Γ ,,, fix_context mfix |- dbody u = dbody v ×
        (rarg u = rarg v) *
        (eq_binder_annot (dname u) (dname v))
      ) mfix mfix' ->
      Σ ;;; Γ |- tFix mfix idx = tFix mfix' idx.
  Proof.
    intros Γ mfix mfix' idx wΣ h.
    assert (thm :
      Σ ;;; Γ |- tFix mfix idx = tFix mfix' idx ×
      eq_context_upto Σ eq (Γ ,,, fix_context mfix) (Γ ,,, fix_context mfix')
    ).
    { apply All2_many_OnOne2 in h.
      induction h.
      - split; reflexivity.
      - destruct IHh.
        split.
        + etransitivity.
          * eassumption.
          * apply conv_Fix_one_body. 1: assumption.
            eapply OnOne2_impl. 1: eassumption.
            intros [na ty bo ra] [na' ty' bo' ra'] [? [hh ?]].
            simpl in *. intuition eauto.
            eapply conv_eq_context_upto. 2: eassumption.
            eapply eq_context_impl. 2: eassumption.
            intros ? ? []. eapply eq_universe_refl.
        + eapply eq_ctx_trans.
          * intros ? ? ? [] []. reflexivity.
          * eassumption.
          * apply OnOne2_split in r
              as [[na ty bo ra] [[na' ty' bo' ra'] [l1 [l2 [[? [? [? ?]]] [? ?]]]]]].
            simpl in *. subst.
            rewrite 2!fix_context_fix_context_alt.
            rewrite 2!map_app. simpl.
            unfold def_sig at 2 5. simpl.
            eapply eq_context_upto_cat.
            -- eapply eq_context_upto_refl. auto.
            -- eapply eq_context_upto_rev'.
               rewrite 2!mapi_app. cbn.
               eapply eq_context_upto_cat.
               ++ constructor; tas.
                  ** eapply eq_term_upto_univ_refl. all: auto.
                  ** eapply eq_context_upto_refl. auto.
               ++ eapply eq_context_upto_refl. auto.
    }
    apply thm.
  Qed.

  Lemma conv_Fix :
    forall Γ mfix mfix' idx,
      wf Σ.1 ->
      All2 (fun u v =>
        Σ;;; Γ |- dtype u = dtype v ×
        Σ;;; Γ ,,, fix_context mfix |- dbody u = dbody v ×
        (rarg u = rarg v) *
        (eq_binder_annot (dname u) (dname v))
      ) mfix mfix' ->
      Σ ;;; Γ |- tFix mfix idx = tFix mfix' idx.
  Proof.
    intros Γ mfix mfix' idx wΣ h.
    assert (h' : ∑ mfix'',
      All2 (fun u v =>
        Σ;;; Γ |- dtype u = dtype v ×
        dbody u = dbody v ×
        rarg u = rarg v ×
        (eq_binder_annot (dname u) (dname v))
      ) mfix'' mfix' ×
      All2 (fun u v =>
        dtype u = dtype v ×
        Σ;;; Γ ,,, fix_context mfix |- dbody u = dbody v ×
        rarg u = rarg v ×
        (eq_binder_annot (dname u) (dname v))
      ) mfix mfix''
    ).
    { set (P1 := fun u v => Σ ;;; Γ |- u = v).
      set (P2 := fun u v => Σ ;;; Γ ,,, fix_context mfix |- u = v).
      change (
        All2 (fun u v =>
          P1 u.(dtype) v.(dtype) ×
          P2 u.(dbody) v.(dbody) ×
          (rarg u = rarg v) *
          (eq_binder_annot (dname u) (dname v))
        ) mfix mfix'
      ) in h.
      change (
        ∑ mfix'',
          All2 (fun u v =>
            P1 u.(dtype) v.(dtype) × dbody u = dbody v × (rarg u = rarg v) ×
            (eq_binder_annot (dname u) (dname v))
          ) mfix'' mfix' ×
          All2 (fun u v =>
            dtype u = dtype v × P2 u.(dbody) v.(dbody) × rarg u = rarg v ×
            (eq_binder_annot (dname u) (dname v))
          ) mfix mfix''
      ).
      clearbody P1 P2.
      induction h.
      - exists []. split. all: constructor.
      - destruct IHh as [l'' [h1 h2]].
        eexists (mkdef _ (dname x) _ _ _ :: l''). split.
        + constructor. 2: assumption.
          simpl. intuition eauto.
        + constructor. 2: assumption.
          intuition eauto.
    }
    destruct h' as [mfix'' [h1 h2]].
    etransitivity.
    - eapply conv_Fix_bodies. all: eassumption.
    - eapply conv_Fix_types. all: assumption.
  Qed.

  Lemma conv_CoFix_one_type :
    forall Γ mfix mfix' idx,
      wf Σ.1 ->
      OnOne2 (fun u v =>
        Σ ;;; Γ |- dtype u = dtype v ×
        dbody u = dbody v ×
        rarg u = rarg v ×
        eq_binder_annot (dname u) (dname v)
      ) mfix mfix' ->
      Σ ;;; Γ |- tCoFix mfix idx = tCoFix mfix' idx.
  Proof.
    intros Γ mfix mfix' idx wΣ h.
    apply OnOne2_split in h
      as [[na ty bo ra] [[na' ty' bo' ra'] [l1 [l2 [[h [? ?]] [? ?]]]]]].
    simpl in *. subst.
    induction h.
    - constructor. constructor.
      apply All2_app.
      + apply All2_same. intros. intuition reflexivity.
      + constructor.
        * simpl. intuition try reflexivity.
        * apply All2_same. intros. intuition reflexivity.
    - eapply conv_red_l ; eauto.
      constructor. apply OnOne2_app. constructor. simpl.
      intuition eauto.
    - eapply conv_red_r ; eauto.
      constructor. apply OnOne2_app. constructor. simpl.
      intuition eauto.
  Qed.

  Lemma conv_CoFix_types :
    forall Γ mfix mfix' idx,
      wf Σ.1 ->
      All2 (fun u v =>
        Σ ;;; Γ |- dtype u = dtype v ×
        dbody u = dbody v ×
        rarg u = rarg v ×
        eq_binder_annot (dname u) (dname v)
      ) mfix mfix' ->
      Σ ;;; Γ |- tCoFix mfix idx = tCoFix mfix' idx.
  Proof.
    intros Γ mfix mfix' idx wΣ h.
    apply All2_many_OnOne2 in h.
    induction h.
    - reflexivity.
    - etransitivity.
      + eassumption.
      + apply conv_CoFix_one_type. all: assumption.
  Qed.

  Lemma conv_CoFix_one_body :
    forall Γ mfix mfix' idx,
      wf Σ.1 ->
      OnOne2 (fun u v =>
        dtype u = dtype v ×
        Σ ;;; Γ ,,, fix_context mfix |- dbody u = dbody v ×
        rarg u = rarg v ×
        eq_binder_annot u.(dname) v.(dname)
      ) mfix mfix' ->
      Σ ;;; Γ |- tCoFix mfix idx = tCoFix mfix' idx.
  Proof.
    intros Γ mfix mfix' idx wΣ h.
    apply OnOne2_split in h
      as [[na ty bo ra] [[na' ty' bo' ra'] [l1 [l2 [[? [h []]] [? ?]]]]]].
    simpl in *. subst.
    induction h.
    - constructor. constructor.
      apply All2_app.
      + apply All2_same. intros. intuition reflexivity.
      + constructor.
        * simpl. intuition reflexivity.
        * apply All2_same. intros. intuition reflexivity.
    - eapply conv_red_l ; eauto.
      eapply cofix_red_body. apply OnOne2_app. constructor. simpl.
      intuition eauto.
      rewrite fix_context_fix_context_alt in r.
      rewrite map_app in r. simpl in r.
      unfold def_sig at 2 in r. simpl in r.
      rewrite fix_context_fix_context_alt.
      rewrite map_app. simpl.
      unfold def_sig at 2. simpl.
      assumption.
    - rewrite fix_context_fix_context_alt in r.
      rewrite map_app in r. simpl in r.
      unfold def_sig at 2 in r. simpl in r.
      eapply red1_eq_context_upto_l in r as [v' [r e]].
      4:{
        instantiate (1 := Γ ,,, fix_context_alt (map def_sig l1 ++ (na', ty') :: map def_sig l2)).
        eapply eq_context_upto_cat.
        - eapply eq_context_upto_refl. instantiate (1 := eq). auto.
        - unfold fix_context_alt. eapply eq_context_upto_rev'.
          rewrite 2!mapi_app. cbn.
          eapply eq_context_upto_cat.
          + constructor.
            * assumption.
            * eapply eq_term_upto_univ_refl. all: auto.
            * eapply eq_context_upto_refl. auto.
          + eapply eq_context_upto_refl. auto.
      }
      2: auto.
      2:{ intros ? ? ? e. apply eq_univ_make in e. subst. reflexivity. }
      etransitivity; tea.
      eapply conv_red_r ; revgoals.
      + eapply cofix_red_body. apply OnOne2_app. constructor. simpl.
        split.
        * rewrite fix_context_fix_context_alt.
          rewrite map_app. simpl.
          unfold def_sig at 2. simpl.
          instantiate (1 := mkdef _ na' ty' v' ra'). simpl.
          exact r.
        * simpl. reflexivity.
      + constructor. constructor.
        apply All2_app.
        * apply All2_same. intros. intuition reflexivity.
        * constructor.
          -- simpl. intuition eauto.
             ++ eapply eq_term_upto_univ_refl.
                all: apply eq_universe_refl.
             ++ eapply upto_eq_impl. 3: assumption.
                all: apply eq_universe_refl.
          -- apply All2_same. intros. intuition reflexivity.
  Qed.

  Lemma conv_CoFix_bodies :
    forall Γ mfix mfix' idx,
      wf Σ.1 ->
      All2 (fun u v =>
        dtype u = dtype v ×
        Σ ;;; Γ ,,, fix_context mfix |- dbody u = dbody v ×
        rarg u = rarg v ×
        eq_binder_annot u.(dname) v.(dname)
      ) mfix mfix' ->
      Σ ;;; Γ |- tCoFix mfix idx = tCoFix mfix' idx.
  Proof.
    intros Γ mfix mfix' idx wΣ h.
    assert (thm :
      Σ ;;; Γ |- tCoFix mfix idx = tCoFix mfix' idx ×
      eq_context_upto Σ eq (Γ ,,, fix_context mfix) (Γ ,,, fix_context mfix')
    ).
    { apply All2_many_OnOne2 in h.
      induction h.
      - split; reflexivity.
      - destruct IHh.
        split.
        + etransitivity.
          * eassumption.
          * apply conv_CoFix_one_body. 1: assumption.
            eapply OnOne2_impl. 1: eassumption.
            intros [na ty bo ra] [na' ty' bo' ra'] [? [hh ?]].
            simpl in *. intuition eauto.
            eapply conv_eq_context_upto. 2: eassumption.
            eapply eq_context_impl. 2: eassumption.
            intros ? ? []. eapply eq_universe_refl.
        + eapply eq_ctx_trans.
          * intros ? ? ? [] []. reflexivity.
          * eassumption.
          * apply OnOne2_split in r
              as [[na ty bo ra] [[na' ty' bo' ra'] [l1 [l2 [[? [? []]] [? ?]]]]]].
            simpl in *. subst.
            rewrite 2!fix_context_fix_context_alt.
            rewrite 2!map_app. simpl.
            unfold def_sig at 2 5. simpl.
            eapply eq_context_upto_cat.
            -- eapply eq_context_upto_refl. auto.
            -- eapply eq_context_upto_rev'.
               rewrite 2!mapi_app. cbn.
               eapply eq_context_upto_cat.
               ++ constructor.
                  ** assumption.
                  ** eapply eq_term_upto_univ_refl. all: auto.
                  ** eapply eq_context_upto_refl. auto.
               ++ eapply eq_context_upto_refl. auto.
    }
    apply thm.
  Qed.

  Lemma conv_CoFix :
  forall Γ mfix mfix' idx,
    wf Σ.1 ->
    All2 (fun u v =>
      Σ;;; Γ |- dtype u = dtype v ×
      Σ;;; Γ ,,, fix_context mfix |- dbody u = dbody v ×
      rarg u = rarg v ×
      eq_binder_annot u.(dname) v.(dname)
    ) mfix mfix' ->
    Σ ;;; Γ |- tCoFix mfix idx = tCoFix mfix' idx.
  Proof.
    intros Γ mfix mfix' idx wΣ h.
    assert (h' : ∑ mfix'',
      All2 (fun u v =>
        Σ;;; Γ |- dtype u = dtype v ×
        dbody u = dbody v ×
        rarg u = rarg v ×
        eq_binder_annot u.(dname) v.(dname)
      ) mfix'' mfix' ×
      All2 (fun u v =>
        dtype u = dtype v ×
        Σ;;; Γ ,,, fix_context mfix |- dbody u = dbody v ×
        rarg u = rarg v ×
        eq_binder_annot u.(dname) v.(dname)
      ) mfix mfix''
    ).
    { set (P1 := fun u v => Σ ;;; Γ |- u = v).
      set (P2 := fun u v => Σ ;;; Γ ,,, fix_context mfix |- u = v).
      change (
        All2 (fun u v =>
          P1 u.(dtype) v.(dtype) ×
          P2 u.(dbody) v.(dbody) ×
          rarg u = rarg v ×
          eq_binder_annot u.(dname) v.(dname)
        ) mfix mfix'
      ) in h.
      change (
        ∑ mfix'',
          All2 (fun u v =>
            P1 u.(dtype) v.(dtype) × dbody u = dbody v × rarg u = rarg v ×
            eq_binder_annot u.(dname) v.(dname)
          ) mfix'' mfix' ×
          All2 (fun u v =>
            dtype u = dtype v × P2 u.(dbody) v.(dbody) × rarg u = rarg v ×
            eq_binder_annot u.(dname) v.(dname)
          ) mfix mfix''
      ).
      clearbody P1 P2.
      induction h.
      - exists []. split. all: constructor.
      - destruct IHh as [l'' [h1 h2]].
        eexists (mkdef _ (dname x) _ _ _ :: l''). split.
        + constructor. 2: assumption.
          simpl. intuition eauto.
        + constructor. 2: assumption.
          intuition eauto.
    }
    destruct h' as [mfix'' [h1 h2]].
    etransitivity.
    - eapply conv_CoFix_bodies. all: eassumption.
    - eapply conv_CoFix_types. all: assumption.
  Qed.

  Lemma conv_Lambda_l :
    forall Γ na A b na' A',
      eq_binder_annot na na' ->
      Σ ;;; Γ |- A = A' ->
      Σ ;;; Γ |- tLambda na A b = tLambda na' A' b.
  Proof.
    intros Γ na A b na' A' hna h.
    induction h.
    - eapply conv_refl. now constructor.
    - eapply conv_red_l ; try eassumption.
      econstructor. assumption.
    - eapply conv_red_r ; try eassumption.
      econstructor. assumption.
  Qed.

  Lemma conv_Lambda_r :
    forall Γ na A b b',
      Σ ;;; Γ,, vass na A |- b = b' ->
      Σ ;;; Γ |- tLambda na A b = tLambda na A b'.
  Proof.
    intros Γ na A b b' h.
    induction h.
    - now repeat constructor.
    - eapply conv_red_l ; try eassumption.
      econstructor. assumption.
    - eapply conv_red_r ; try eassumption.
      econstructor. assumption.
  Qed.

  Lemma cumul_LetIn_bo :
    forall Γ na ty t u u',
      Σ ;;; Γ ,, vdef na ty t |- u <= u' ->
      Σ ;;; Γ |- tLetIn na ty t u <= tLetIn na ty t u'.
  Proof.
    intros Γ na ty t u u' h.
    induction h.
    - eapply cumul_refl. constructor.
      all: try eapply eq_term_refl.
      + reflexivity.
      + assumption.
    - eapply cumul_red_l ; try eassumption.
      econstructor. assumption.
    - eapply cumul_red_r ; try eassumption.
      econstructor. assumption.
  Qed.

  Lemma cumul_Lambda_r :
    forall Γ na A b b',
      Σ ;;; Γ,, vass na A |- b <= b' ->
      Σ ;;; Γ |- tLambda na A b <= tLambda na A b'.
  Proof.
    intros Γ na A b b' h.
    induction h.
    - eapply cumul_refl. constructor.
      + reflexivity. 
      + eapply eq_term_refl.
      + assumption.
    - eapply cumul_red_l ; try eassumption.
      econstructor. assumption.
    - eapply cumul_red_r ; try eassumption.
      econstructor. assumption.
  Qed.

  Lemma cumul_it_mkLambda_or_LetIn :
    forall Δ Γ u v,
      Σ ;;; (Δ ,,, Γ) |- u <= v ->
      Σ ;;; Δ |- it_mkLambda_or_LetIn Γ u <= it_mkLambda_or_LetIn Γ v.
  Proof.
    intros Δ Γ u v h. revert Δ u v h.
    induction Γ as [| [na [b|] A] Γ ih ] ; intros Δ u v h.
    - assumption.
    - simpl. cbn. eapply ih.
      eapply cumul_LetIn_bo. assumption.
    - simpl. cbn. eapply ih.
      eapply cumul_Lambda_r. assumption.
  Qed.

  Lemma cumul_it_mkProd_or_LetIn_codom :
    forall Δ Γ B B',
      Σ ;;; (Δ ,,, Γ) |- B <= B' ->
      Σ ;;; Δ |- it_mkProd_or_LetIn Γ B <= it_mkProd_or_LetIn Γ B'.
  Proof.
    intros Δ Γ B B' h.
    induction Γ as [| [na [b|] A] Γ ih ] in Δ, B, B', h |- *.
    - assumption.
    - simpl. cbn. eapply ih.
      eapply cumul_LetIn_bo. assumption.
    - simpl. cbn. eapply ih.
      eapply cumul_Prod_r. assumption.
  Qed.

  Lemma mkApps_conv_weak :
    forall Γ u1 u2 l,
      Σ ;;; Γ |- u1 = u2 ->
      Σ ;;; Γ |- mkApps u1 l = mkApps u2 l.
  Proof.
    intros Γ u1 u2 l. induction l in u1, u2 |- *; cbn. 1: trivial.
    intros X. apply IHl. now apply conv_App_l.
  Qed.

  Lemma conv_cum_Lambda leq Γ na1 na2 A1 A2 t1 t2 :
      eq_binder_annot na1 na2 ->
      Σ ;;; Γ |- A1 = A2 ->
      conv_cum leq Σ (Γ ,, vass na1 A1) t1 t2 ->
      conv_cum leq Σ Γ (tLambda na1 A1 t1) (tLambda na2 A2 t2).
  Proof.
    intros eqna X H. destruct leq; cbn in *; sq.
    - etransitivity.
      + eapply conv_Lambda_r. eassumption.
      + now eapply conv_Lambda_l.
    - etransitivity.
      + eapply cumul_Lambda_r. eassumption.
      + eapply conv_cumul, conv_Lambda_l; tea.
  Qed.

  Lemma conv_LetIn_tm Γ na na' ty t t' u :
      eq_binder_annot na na' ->
      Σ ;;; Γ |- t = t' ->
      Σ ;;; Γ |- tLetIn na t ty u = tLetIn na' t' ty u.
  Proof.
    intros hna; induction 1.
    - constructor 1. constructor; try reflexivity;
      assumption.
    - econstructor 2; tea. now constructor.
    - econstructor 3; tea. now constructor.
  Qed.

  Lemma conv_LetIn_ty Γ na na' ty ty' t u :
      eq_binder_annot na na' ->
      Σ ;;; Γ |- ty = ty' ->
      Σ ;;; Γ |- tLetIn na t ty u = tLetIn na' t ty' u.
  Proof.
    intros hna. induction 1.
    - constructor 1. constructor; try reflexivity;
      assumption.
    - econstructor 2; tea. now constructor.
    - econstructor 3; tea. now constructor.
  Qed.

  Lemma conv_LetIn_bo :
    forall Γ na ty t u u',
      Σ ;;; Γ ,, vdef na ty t |- u = u' ->
      Σ ;;; Γ |- tLetIn na ty t u = tLetIn na ty t u'.
  Proof.
    intros Γ na ty t u u' h.
    induction h.
    - now repeat constructor.
    - eapply conv_red_l ; try eassumption.
      econstructor. assumption.
    - eapply conv_red_r ; try eassumption.
      econstructor. assumption.
  Qed.

  Lemma conv_cum_LetIn leq Γ na1 na2 t1 t2 A1 A2 u1 u2 :
      eq_binder_annot na1 na2 ->
      Σ;;; Γ |- t1 = t2 ->
      Σ;;; Γ |- A1 = A2 ->
      conv_cum leq Σ (Γ ,, vdef na1 t1 A1) u1 u2 ->
      conv_cum leq Σ Γ (tLetIn na1 t1 A1 u1) (tLetIn na2 t2 A2 u2).
  Proof.
    intros hna X H H'. destruct leq; cbn in *; sq.
    - etransitivity.
      + eapply conv_LetIn_bo. eassumption.
      + etransitivity.
        * eapply conv_LetIn_tm.
          ++ eassumption.
          ++ eassumption.
        * eapply conv_LetIn_ty with (na := na2). 
          ++ reflexivity.
          ++ assumption. 
    - etransitivity.
      + eapply cumul_LetIn_bo. eassumption.
      + etransitivity.
        * eapply conv_cumul, conv_LetIn_tm; tea.
        * eapply conv_cumul, conv_LetIn_ty with (na := na2); tea.
          reflexivity.
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

  Lemma it_mkLambda_or_LetIn_conv Γ Δ1 Δ2 t1 t2 :
      conv_context Σ (Γ ,,, Δ1) (Γ ,,, Δ2) ->
      Σ ;;; Γ ,,, Δ1 |- t1 = t2 ->
      Σ ;;; Γ |- it_mkLambda_or_LetIn Δ1 t1 = it_mkLambda_or_LetIn Δ2 t2.
  Proof.
    induction Δ1 in Δ2, t1, t2 |- *; intros X Y.
    - apply context_relation_length in X.
      destruct Δ2; cbn in *; [trivial|].
      exfalso. rewrite app_length in X; lia.
    - apply context_relation_length in X as X'.
      destruct Δ2 as [|c Δ2]; simpl in *; [exfalso; rewrite app_length in X'; lia|].
      dependent destruction X.
      + eapply IHΔ1; tas; cbn.
        inv c0. etransitivity.
        * eapply conv_Lambda_r; tea.
        * now eapply conv_Lambda_l.
      + eapply IHΔ1; tas; cbn.
        etransitivity.
        * eapply conv_LetIn_bo; tea.
        * inv c0.
          -- eapply conv_LetIn_ty; tea.
          -- etransitivity.
             ++ eapply conv_LetIn_tm; tea.
             ++ eapply conv_LetIn_ty with (na := na'); tea. reflexivity.
  Qed.

  Lemma red_lambda_inv Γ na A1 b1 T :
    red Σ Γ (tLambda na A1 b1) T ->
    ∑ A2 b2, (T = tLambda na A2 b2) *
             red Σ Γ A1 A2 * red Σ (Γ ,, vass na A1) b1 b2.
  Proof.
    intros. eapply clos_rt_rt1n_iff in X. depind X.
    - eexists _, _; intuition eauto.
    - depelim r; solve_discr; specialize (IHX _ _ _ _ eq_refl);
      destruct IHX as [A2 [B2 [[-> ?] ?]]].
      + eexists _, _; intuition eauto.
        1: now eapply red_step with M'.
        eapply PCUICConfluence.red_red_ctx; eauto.
        constructor; auto.
        * eapply All2_local_env_red_refl.
        * red. auto.
      + eexists _, _; intuition eauto.
        now eapply red_step with M'.
  Qed.

  Lemma Lambda_conv_cum_inv :
    forall leq Γ na1 na2 A1 A2 b1 b2,
      conv_cum leq Σ Γ (tLambda na1 A1 b1) (tLambda na2 A2 b2) ->
      eq_binder_annot na1 na2 /\ ∥ Σ ;;; Γ |- A1 = A2 ∥ /\ conv_cum leq Σ (Γ ,, vass na1 A1) b1 b2.
  Proof.
    intros *.
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
      split; [|split]; tas. all:constructor; auto.
      eapply conv_trans with b1'; auto.
      eapply conv_trans with b2'; auto.
      + constructor; auto.
      + apply conv_sym; auto.
        eapply conv_conv_ctx; eauto.
        constructor; auto. 1: reflexivity.
        constructor; now symmetry.
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
      split; [|split]; tas. all:constructor; auto.
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

End Inversions.

Lemma cum_LetIn `{cf:checker_flags} Σ Γ na1 na2 t1 t2 A1 A2 u1 u2 :
  wf Σ.1 ->
  eq_binder_annot na1 na2 ->
  Σ;;; Γ |- t1 = t2 ->
  Σ;;; Γ |- A1 = A2 ->
  cumul Σ (Γ ,, vdef na1 t1 A1) u1 u2 ->
  cumul Σ Γ (tLetIn na1 t1 A1 u1) (tLetIn na2 t2 A2 u2).
Proof.
  intros wfΣ Hna X H H'.
  eapply cumul_trans => //.
  + eapply cumul_LetIn_bo. eassumption.
  + etransitivity.
    * eapply conv_cumul. eapply conv_LetIn_tm; tea.
    * eapply conv_cumul, conv_LetIn_ty with (na := na2).
      ++ reflexivity.
      ++ assumption.
Qed.

Lemma untyped_substitution_conv `{cf : checker_flags} (Σ : global_env_ext) Γ Γ' Γ'' s M N :
  wf Σ -> wf_local Σ (Γ ,,, Γ' ,,, Γ'') ->
  untyped_subslet Γ s Γ' ->
  Σ ;;; Γ ,,, Γ' ,,, Γ'' |- M = N ->
  Σ ;;; Γ ,,, subst_context s 0 Γ'' |- subst s #|Γ''| M = subst s #|Γ''| N.
Proof.
  intros wfΣ wfΓ Hs. induction 1.
  - constructor.
    now apply subst_eq_term.
  - eapply substitution_untyped_let_red in r. 3:eauto. all:eauto with wf.
    eapply red_conv_conv; eauto.
  - eapply substitution_untyped_let_red in r. 3:eauto. all:eauto with wf.
    eapply red_conv_conv_inv; eauto.
Qed.

Lemma substitution_conv `{cf : checker_flags} (Σ : global_env_ext) Γ Γ' Γ'' s M N :
  wf Σ -> wf_local Σ (Γ ,,, Γ' ,,, Γ'') -> subslet Σ Γ s Γ' ->
  Σ ;;; Γ ,,, Γ' ,,, Γ'' |- M = N ->
  Σ ;;; Γ ,,, subst_context s 0 Γ'' |- subst s #|Γ''| M = subst s #|Γ''| N.
Proof.
  intros wfΣ wfΓ Hs. induction 1.
  - constructor.
    now apply subst_eq_term.
  - eapply substitution_let_red in r. 4:eauto. all:eauto with wf.
    eapply red_conv_conv; eauto.
  - eapply substitution_let_red in r. 4:eauto. all:eauto with wf.
    eapply red_conv_conv_inv; eauto.
Qed.

Lemma red_subst_conv {cf:checker_flags} (Σ : global_env_ext) Γ Δ Γ' s s' b : wf Σ ->
  All2 (red Σ Γ) s s' ->
  untyped_subslet Γ s Δ ->
  conv Σ (Γ ,,, Γ') (subst s #|Γ'| b) (subst s' #|Γ'| b).
Proof.
  move=> wfΣ eqsub subs.
  apply red_conv. now eapply red_red.
Qed.

Derive Signature for untyped_subslet.

Lemma conv_subst_conv {cf:checker_flags} (Σ : global_env_ext) Γ Δ Δ' Γ' s s' b : wf Σ ->
  All2 (conv Σ Γ) s s' ->
  untyped_subslet Γ s Δ ->
  untyped_subslet Γ s' Δ' ->
  conv Σ (Γ ,,, Γ') (subst s #|Γ'| b) (subst s' #|Γ'| b).
Proof.
  move=> wfΣ eqsub subs subs'.
  assert(∑ s0 s'0, All2 (red Σ Γ) s s0 * All2 (red Σ Γ) s' s'0 * All2 (eq_term Σ Σ) s0 s'0)
    as [s0 [s'0 [[redl redr] eqs]]].
  { clear subs'; induction eqsub in Δ, subs |- *.
    * depelim subs. exists [], []; split; auto.
    * depelim subs.
    - specialize (IHeqsub _ subs) as [s0 [s'0 [[redl redr] eqs0]]].
      eapply conv_alt_red in r as [v [v' [[redv redv'] eqvv']]].
      exists (v :: s0), (v' :: s'0). repeat split; constructor; auto.
    - specialize (IHeqsub _ subs) as [s0 [s'0 [[redl redr] eqs0]]].
      eapply conv_alt_red in r as [v [v' [[redv redv'] eqvv']]].
      exists (v :: s0), (v' :: s'0). repeat split; constructor; auto. }
  eapply conv_trans => //.
  * apply red_conv. eapply red_red => //; eauto.
  * eapply conv_sym, conv_trans => //.
  ** apply red_conv. eapply red_red => //; eauto.
  ** apply conv_refl. red. apply eq_term_upto_univ_substs; try typeclasses eauto; try reflexivity.
     now symmetry.
Qed.

Lemma subslet_untyped_subslet {cf:checker_flags} Σ Γ s Γ' : subslet Σ Γ s Γ' -> untyped_subslet Γ s Γ'.
Proof.
  induction 1; constructor; auto.
Qed.

Lemma untyped_subst_conv {cf:checker_flags} {Σ} Γ Γ0 Γ1 Δ s s' T U :
  wf Σ.1 ->
  untyped_subslet Γ s Γ0 ->
  untyped_subslet Γ s' Γ1 ->
  All2 (conv Σ Γ) s s' ->
  wf_local Σ (Γ ,,, Γ0 ,,, Δ) ->
  Σ;;; Γ ,,, Γ0 ,,, Δ |- T = U ->
  Σ;;; Γ ,,, subst_context s 0 Δ |- subst s #|Δ| T = subst s' #|Δ| U.
Proof.
  move=> wfΣ subss subss' eqsub wfctx eqty.
  eapply conv_trans => //.
  * eapply untyped_substitution_conv => //.
  ** eapply wfctx.
  ** auto.
  ** apply eqty.
  * clear eqty.
    rewrite -(subst_context_length s 0 Δ).
    eapply conv_subst_conv => //; eauto using subslet_untyped_subslet.
Qed.

Lemma subst_conv {cf:checker_flags} {Σ} Γ Γ0 Γ1 Δ s s' T U :
  wf Σ.1 ->
  subslet Σ Γ s Γ0 ->
  subslet Σ Γ s' Γ1 ->
  All2 (conv Σ Γ) s s' ->
  wf_local Σ (Γ ,,, Γ0 ,,, Δ) ->
  Σ;;; Γ ,,, Γ0 ,,, Δ |- T = U ->
  Σ;;; Γ ,,, subst_context s 0 Δ |- subst s #|Δ| T = subst s' #|Δ| U.
Proof.
  move=> wfΣ subss subss' eqsub wfctx eqty.
  eapply conv_trans => //.
  * eapply substitution_conv => //.
  ** eapply wfctx.
  ** auto.
  ** apply eqty.
  * clear eqty.
    rewrite -(subst_context_length s 0 Δ).
    eapply conv_subst_conv => //; eauto using subslet_untyped_subslet.
Qed.

Lemma context_relation_subst {cf:checker_flags} {Σ} Γ Γ0 Γ1 Δ Δ' s s' :
  wf Σ.1 ->
  wf_local Σ (Γ ,,, Γ0 ,,, Δ) ->
  subslet Σ Γ s Γ0 ->
  subslet Σ Γ s' Γ1 ->
  All2 (conv Σ Γ) s s' ->
  context_relation
  (fun Γ0 Γ' : PCUICAst.context => conv_decls Σ (Γ ,,, Γ0) (Γ ,,, Γ'))
  (Γ0 ,,, Δ)
  (Γ1 ,,, Δ') ->
  context_relation
  (fun Γ0 Γ' : PCUICAst.context => conv_decls Σ (Γ ,,, Γ0) (Γ ,,, Γ'))
  (subst_context s 0 Δ)
  (subst_context s' 0 Δ').
Proof.
  move=> wfΣ wfl subss subss' eqsub ctxr.
  assert (hlen: #|Γ0| = #|Γ1|).
  { rewrite -(subslet_length subss) -(subslet_length subss').
    now apply All2_length in eqsub. }
  assert(clen := context_relation_length _ _ _ ctxr).
  autorewrite with len in clen. rewrite hlen in clen.
  assert(#|Δ| = #|Δ'|) by lia.
  clear clen.
  move: Δ' wfl ctxr H.
  induction Δ as [|d Δ]; intros * wfl ctxr len0; destruct Δ' as [|d' Δ']; simpl in len0; try lia.
  - constructor.
  - rewrite !subst_context_snoc. specialize (IHΔ Δ'). depelim wfl; specialize (IHΔ wfl);
    depelim ctxr; depelim c; noconf len0; simpl.
    * constructor; auto. constructor; tas. simpl.
      ** rewrite !Nat.add_0_r -H.
        eapply subst_conv; eauto. now rewrite -app_context_assoc.
    * constructor; auto. constructor; tas; simpl;
      rewrite !Nat.add_0_r -H;
      eapply subst_conv; eauto; now rewrite -app_context_assoc.
    * constructor; auto. constructor; tas; simpl;
      rewrite !Nat.add_0_r -H;
      eapply subst_conv; eauto; now rewrite -app_context_assoc.
Qed.

Lemma weaken_conv {cf:checker_flags} {Σ Γ t u} Δ :
  wf Σ.1 -> wf_local Σ Δ -> wf_local Σ Γ ->
  closedn #|Γ| t -> closedn #|Γ| u ->
  Σ ;;; Γ |- t = u ->
  Σ ;;; Δ ,,, Γ |- t = u.
Proof.
  intros wfΣ wfΔ wfΓ clt clu ty.
  epose proof (weakening_conv Σ [] Γ Δ t u wfΣ).
  rewrite !app_context_nil_l in X.
  forward X by eauto using typing_wf_local.
  pose proof (closed_wf_local wfΣ wfΓ).
  rewrite closed_ctx_lift in X; auto.
  rewrite !lift_closed in X => //.
Qed.

Lemma weaken_cumul {cf:checker_flags} {Σ Γ t u} Δ :
  wf Σ.1 -> closedn_ctx 0 Γ ->
  closedn #|Γ| t -> closedn #|Γ| u ->
  Σ ;;; Γ |- t <= u ->
  Σ ;;; Δ ,,, Γ |- t <= u.
Proof.
  intros wfΣ clΓ clt clu ty.
  epose proof (weakening_cumul Σ [] Γ Δ t u wfΣ).
  rewrite !app_context_nil_l in X.
  forward X by eauto.
  rewrite closed_ctx_lift in X; auto.
  rewrite !lift_closed in X => //.
Qed.

Lemma conv_subst_instance {cf:checker_flags} (Σ : global_env_ext) Γ u A B univs :
  valid_constraints (global_ext_constraints (Σ.1, univs))
                    (subst_instance_cstrs u Σ) ->
  Σ ;;; Γ |- A = B ->
  (Σ.1,univs) ;;; subst_instance_context u Γ
                   |- subst_instance_constr u A = subst_instance_constr u B.
Proof.
  intros HH X0. induction X0.
  - econstructor.
    eapply eq_term_subst_instance; tea.
  - econstructor 2. 1: eapply red1_subst_instance; cbn; eauto. eauto.
  - econstructor 3. 1: eauto. eapply red1_subst_instance; cbn; eauto.
Qed.

Lemma context_relation_subst_instance {cf:checker_flags} {Σ} Γ Δ u u' :
  wf Σ.1 ->
  wf_local Σ Γ -> wf_local Σ (subst_instance_context u Δ) ->
  R_universe_instance (eq_universe (global_ext_constraints Σ)) u u' ->
  context_relation
  (fun Γ0 Γ' : PCUICAst.context => conv_decls Σ (Γ ,,, Γ0) (Γ ,,, Γ'))
  (subst_instance_context u Δ)
  (subst_instance_context u' Δ).
Proof.
  move=> wfΣ wf wf0 equ.
  assert (cl := closed_wf_local wfΣ wf0).
  rewrite closedn_subst_instance_context in cl.
  induction Δ as [|d Δ] in cl, wf0 |- *.
  - constructor.
  - simpl.
    rewrite closedn_ctx_cons in cl. apply andP in cl as [clctx cld].
    simpl in wf0.
    destruct d as [na [b|] ty] => /=.
    * depelim wf0; simpl in *.
      simpl in cld. unfold closed_decl in cld. simpl in cld. simpl.
      apply andP in cld as [clb clty].
      constructor; auto. constructor; [reflexivity|..].
      ** apply weaken_conv; auto; autorewrite with len.
         1-2:now rewrite closedn_subst_instance_constr.
        constructor. red.
        apply eq_term_upto_univ_subst_instance_constr; try typeclasses eauto. auto.
      ** constructor. red.
        apply eq_term_upto_univ_subst_instance_constr; try typeclasses eauto. auto.
    * depelim wf0; simpl in *.
      simpl in cld. unfold closed_decl in cld. simpl in cld. simpl.
      constructor; auto. constructor; [reflexivity|..]. apply weaken_conv; auto.
      1-2:autorewrite with len; now rewrite closedn_subst_instance_constr.
      constructor. red.
      apply eq_term_upto_univ_subst_instance_constr; try typeclasses eauto. auto.
Qed.

Definition conv_ctx_rel {cf:checker_flags} Σ Γ Δ Δ' :=
  All2_local_env (on_decl (fun Γ' _ x y => Σ ;;; Γ ,,, Γ' |- x = y)) Δ Δ'.

Definition cumul_ctx_rel {cf:checker_flags} Σ Γ Δ Δ' :=
  All2_local_env (on_decl (fun Γ' _ x y => Σ ;;; Γ ,,, Γ' |- x <= y)) Δ Δ'.

Lemma cumul_ctx_subst_instance {cf:checker_flags} {Σ} Γ Δ u u' :
  wf Σ.1 ->
  wf_local Σ Γ ->
  R_universe_instance (eq_universe (global_ext_constraints Σ)) u u' ->
  cumul_ctx_rel Σ Γ (subst_instance_context u Δ) (subst_instance_context u' Δ).
Proof.
  move=> wfΣ wf equ.
  induction Δ as [|d Δ].
  - constructor.
  - simpl.
    destruct d as [na [b|] ty] => /=.
    * constructor; eauto.
      split.
      + constructor. eapply eq_term_leq_term.
        eapply eq_term_upto_univ_subst_instance_constr; try typeclasses eauto; auto.
      + constructor. eapply eq_term_leq_term.
        eapply eq_term_upto_univ_subst_instance_constr; try typeclasses eauto; auto.
    * constructor; auto.
      constructor. eapply eq_term_leq_term. simpl.
      apply eq_term_upto_univ_subst_instance_constr; try typeclasses eauto. auto.
Qed.

Lemma context_relation_over_same {cf:checker_flags} Σ Γ Δ Δ' :
  context_relation (fun Γ0 Γ'  => conv_decls Σ (Γ ,,, Γ0) (Γ ,,, Γ')) Δ Δ' ->
  context_relation (conv_decls Σ) (Γ ,,, Δ) (Γ ,,, Δ').
Proof.
  induction 1; simpl; try constructor; pcuic.
Qed.

Lemma context_relation_over_same_app {cf:checker_flags} Σ Γ Δ Δ' :
  context_relation (conv_decls Σ) (Γ ,,, Δ) (Γ ,,, Δ') ->
  context_relation (fun Γ0 Γ' => conv_decls Σ (Γ ,,, Γ0) (Γ ,,, Γ')) Δ Δ'.
Proof.
  move=> H. pose (context_relation_length _ _ _ H).
  autorewrite with len in e. assert(#|Δ| = #|Δ'|) by lia.
  move/context_relation_app: H => H.
  now specialize (H H0) as [_ H].
Qed.

Lemma eq_term_inds {cf:checker_flags} (Σ : global_env_ext) u u' ind mdecl :
  R_universe_instance (eq_universe (global_ext_constraints Σ)) u u' ->
  All2 (eq_term Σ Σ) (inds (inductive_mind ind) u (ind_bodies mdecl))
    (inds (inductive_mind ind) u' (ind_bodies mdecl)).
Proof.
  move=> equ.
  unfold inds. generalize #|ind_bodies mdecl|.
  induction n; constructor; auto.
  clear IHn.
  repeat constructor. destruct ind; simpl in *.
  eapply (R_global_instance_empty_impl _ _ _ _ _ _ 0).
  4:{ unfold R_global_instance. simpl. eauto. }
  all:typeclasses eauto.
Qed.

Lemma conv_inds {cf:checker_flags} (Σ : global_env_ext) Γ u u' ind mdecl :
  R_universe_instance (eq_universe (global_ext_constraints Σ)) u u' ->
  All2 (conv Σ Γ) (inds (inductive_mind ind) u (ind_bodies mdecl))
    (inds (inductive_mind ind) u' (ind_bodies mdecl)).
Proof.
  move=> equ.
  unfold inds. generalize #|ind_bodies mdecl|.
  induction n; constructor; auto.
  clear IHn.
  repeat constructor. destruct ind; simpl in *.
  eapply (R_global_instance_empty_impl _ _ _ _ _ _ 0).
  4:{ unfold R_global_instance. simpl. eauto. }
  all:typeclasses eauto.
Qed.

Lemma R_global_instance_length Σ Req Rle ref napp i i' :
  R_global_instance Σ Req Rle ref napp i i' -> #|i| = #|i'|.
Proof.
  unfold R_global_instance.
  destruct global_variance.
  { induction i in l, i' |- *; destruct l, i'; simpl; auto; try easy. }
  { unfold R_universe_instance.
    intros H % Forall2_length. now rewrite !map_length in H. }
Qed.

Lemma R_universe_instance_variance_irrelevant Re Rle i i' :
  #|i| = #|i'| ->
  R_universe_instance_variance Re Rle [] i i'.
Proof.
  now induction i in i' |- *; destruct i'; simpl; auto.
Qed.

Lemma weakening_conv_gen :
  forall {cf : checker_flags} (Σ : global_env × universes_decl)
    (Γ Γ' Γ'' : PCUICAst.context) (M N : term) k,
  wf Σ.1 -> k = #|Γ''| ->
  Σ;;; Γ ,,, Γ' |- M = N ->
  Σ;;; Γ ,,, Γ'' ,,, lift_context k 0 Γ' |- lift k #|Γ'| M = lift k #|Γ'| N.
Proof.
  intros; subst k; now eapply weakening_conv.
Qed.

Lemma cumul_it_mkProd_or_LetIn {cf : checker_flags} (Σ : PCUICAst.global_env_ext)
  (Δ Γ Γ' : PCUICAst.context) (B B' : term) :
  wf Σ.1 ->
  context_relation (fun Γ Γ' => conv_decls Σ (Δ ,,, Γ) (Δ  ,,, Γ')) Γ Γ' ->
  Σ ;;; Δ ,,, Γ |- B <= B' ->
  Σ ;;; Δ |- PCUICAst.it_mkProd_or_LetIn Γ B <= PCUICAst.it_mkProd_or_LetIn Γ' B'.
Proof.
  move=> wfΣ; move: B B' Γ' Δ.
  induction Γ as [|d Γ] using rev_ind; move=> B B' Γ' Δ;
  destruct Γ' as [|d' Γ'] using rev_ind; try clear IHΓ';
    move=> H; try solve [simpl; auto].
  + depelim H. apply app_eq_nil in H; intuition discriminate.
  + depelim H. apply app_eq_nil in H; intuition discriminate.
  + assert (clen : #|Γ| = #|Γ'|).
    { apply context_relation_length in H.
      autorewrite with len in H; simpl in H. lia. }
    apply context_relation_app in H as [cd cctx] => //.
    depelim cd; depelim c.
    - rewrite !it_mkProd_or_LetIn_app => //=.
      simpl. move=> HB. apply congr_cumul_prod => //.
      eapply IHΓ.
      * unshelve eapply (context_relation_impl _ cctx).
        simpl. intros * X. rewrite !app_context_assoc in X.
        destruct X; constructor; auto.
      * now rewrite app_context_assoc in HB.
    - rewrite !it_mkProd_or_LetIn_app => //=.
      simpl. intros HB. apply cum_LetIn => //; auto.
      eapply IHΓ.
      * unshelve eapply (context_relation_impl _ cctx).
        simpl. intros * X. rewrite !app_context_assoc in X.
        destruct X; constructor; auto.
      * now rewrite app_context_assoc in HB.
    - rewrite !it_mkProd_or_LetIn_app => //=.
      simpl.
      intros HB. apply cum_LetIn => //; auto.
      eapply IHΓ.
      * unshelve eapply (context_relation_impl _ cctx).
        simpl. intros * X. rewrite !app_context_assoc in X.
        destruct X; constructor; auto.
      * now rewrite app_context_assoc in HB.
Qed.

Require Import CMorphisms.
Notation conv_terms Σ Γ := (All2 (conv Σ Γ)).

Instance conv_terms_Proper {cf:checker_flags} Σ Γ : CMorphisms.Proper (eq ==> eq ==> arrow)%signature (conv_terms Σ Γ).
Proof. intros x y -> x' y' -> f. exact f. Qed.

Lemma conv_terms_alt {cf:checker_flags} Σ Γ args args' :
  conv_terms Σ Γ args args' <~>
  ∑ argsr argsr',
    All2 (red Σ Γ) args argsr ×
    All2 (red Σ Γ) args' argsr' ×
    All2 (eq_term Σ Σ) argsr argsr'.
Proof.
  split.
  - intros conv.
    induction conv.
    + exists [], []; eauto with pcuic.
    + apply conv_alt_red in r as (xr&yr&(xred&yred)&xy).
      specialize IHconv as (argsr&argsr'&?&?&?).
      exists (xr :: argsr), (yr :: argsr').
      eauto 7 with pcuic.
  - intros (argsr&argsr'&r&r'&eqs).
    induction eqs in args, args', r, r' |- *; depelim r; depelim r'; [constructor|].
    constructor; auto.
    apply conv_alt_red; eauto.
Qed.

Lemma conv_terms_conv_ctx {cf:checker_flags} (Σ : global_env_ext) Γ Γ' ts ts' :
  wf Σ ->
  conv_context Σ Γ Γ' ->
  conv_terms Σ Γ ts ts' ->
  conv_terms Σ Γ' ts ts'.
Proof.
  intros wf ctx conv.
  induction conv; [constructor|].
  constructor; auto.
  eapply conv_conv_ctx; eauto.
Qed.

Lemma conv_terms_red {cf:checker_flags} (Σ : global_env_ext) Γ ts ts' tsr tsr' :
  All2 (red Σ Γ) ts tsr ->
  All2 (red Σ Γ) ts' tsr' ->
  conv_terms Σ Γ tsr tsr' ->
  conv_terms Σ Γ ts ts'.
Proof.
  intros all all' conv.
  induction conv in ts, ts', all, all' |- *; depelim all; depelim all'; [constructor|].
  constructor; [|auto].
  eapply red_conv_conv; eauto.
  symmetry.
  eapply red_conv_conv; eauto.
  symmetry.
  eauto.
Qed.

Lemma conv_terms_red_inv {cf:checker_flags} (Σ : global_env_ext) Γ ts ts' tsr tsr' :
  wf Σ ->
  All2 (red Σ Γ) ts tsr ->
  All2 (red Σ Γ) ts' tsr' ->
  conv_terms Σ Γ ts ts' ->
  conv_terms Σ Γ tsr tsr'.
Proof.
  intros wf all all' conv.
  induction conv in tsr, tsr', all, all' |- *; depelim all; depelim all'; [constructor|].
  constructor; [|auto].
  eapply conv_red_l_inv; [eauto| |eauto].
  symmetry.
  eapply conv_red_l_inv; [eauto| |eauto].
  symmetry.
  eauto.
Qed.

Lemma conv_terms_red_conv {cf:checker_flags} (Σ : global_env_ext) Γ Γ' ts ts' tsr tsr' :
  wf Σ ->
  conv_context Σ Γ Γ' ->
  All2 (red Σ Γ) ts tsr ->
  All2 (red Σ Γ') ts' tsr' ->
  conv_terms Σ Γ tsr tsr' ->
  conv_terms Σ Γ ts ts'.
Proof.
  intros wf convctx all all2 conv.
  eapply conv_terms_red.
  1: eassumption.
  1: apply All2_same; reflexivity.
  eapply conv_terms_conv_ctx; eauto.
  1: eapply conv_context_sym; eauto.
  eapply conv_terms_red.
  1: apply All2_same; reflexivity.
  1: eauto.
  eapply conv_terms_conv_ctx; eauto.
Qed.

Lemma cumul_subst_conv {cf:checker_flags} (Σ : global_env_ext) Γ Δ Δ' Γ' s s' b : wf Σ ->
  All2 (conv Σ Γ) s s' ->
  untyped_subslet Γ s Δ ->
  untyped_subslet Γ s' Δ' ->
  cumul Σ (Γ ,,, Γ') (subst s #|Γ'| b) (subst s' #|Γ'| b).
Proof.
  move=> wfΣ eqsub subs subs'.
  eapply conv_cumul. eapply conv_subst_conv; eauto.
Qed.

Lemma subst_cumul {cf:checker_flags} {Σ} Γ Γ0 Γ1 Δ s s' T U :
  wf Σ.1 ->
  subslet Σ Γ s Γ0 ->
  subslet Σ Γ s' Γ1 ->
  All2 (conv Σ Γ) s s' ->
  wf_local Σ (Γ ,,, Γ0 ,,, Δ) ->
  Σ;;; Γ ,,, Γ0 ,,, Δ |- T <= U ->
  Σ;;; Γ ,,, subst_context s 0 Δ |- subst s #|Δ| T <= subst s' #|Δ| U.
Proof.
  move=> wfΣ subss subss' eqsub wfctx eqty.
  eapply cumul_trans => //.
  * eapply substitution_cumul => //.
  ** eauto.
  ** auto.
  ** eapply eqty.
  * clear eqty.
    rewrite -(subst_context_length s 0 Δ).
    eapply cumul_subst_conv => //; eauto using subslet_untyped_subslet.
Qed.

Lemma untyped_subst_cumul {cf:checker_flags} {Σ} Γ Γ0 Γ1 Δ s s' T U :
  wf Σ.1 ->
  untyped_subslet Γ s Γ0 ->
  untyped_subslet Γ s' Γ1 ->
  All2 (conv Σ Γ) s s' ->
  wf_local Σ (Γ ,,, Γ0 ,,, Δ) ->
  Σ;;; Γ ,,, Γ0 ,,, Δ |- T <= U ->
  Σ;;; Γ ,,, subst_context s 0 Δ |- subst s #|Δ| T <= subst s' #|Δ| U.
Proof.
  move=> wfΣ subss subss' eqsub wfctx eqty.
  eapply cumul_trans => //.
  * eapply substitution_untyped_cumul => //.
  ** eauto.
  ** eapply eqty.
  * clear eqty.
    rewrite -(subst_context_length s 0 Δ).
    eapply cumul_subst_conv => //; eauto using subslet_untyped_subslet.
Qed.

Lemma conv_ctx_subst {cf:checker_flags} Σ Γ Γ' Δ Δ' s s' :
  wf Σ.1 ->
  wf_local Σ (Γ ,,, Γ' ,,, Δ) ->
  conv_ctx_rel Σ (Γ ,,, Γ') Δ Δ' ->
  All2 (conv Σ []) s s' ->
  subslet Σ [] s Γ ->
  subslet Σ [] s' Γ ->
  conv_ctx_rel Σ (subst_context s 0 Γ') (subst_context s #|Γ'| Δ) (subst_context s' #|Γ'| Δ').
Proof.
  intros wfΣ wf. induction 1.
  - simpl. constructor.
  - rewrite !subst_context_snoc /=.
    intros Hs subs subs'.
    depelim wf.
    specialize (IHX wf Hs subs subs').
    constructor; auto.
    red. red in p. simpl.
    epose proof (subst_conv [] Γ Γ (Γ' ,,, Γ0) _ _ _ _ wfΣ subs subs' Hs).
    rewrite app_context_nil_l app_context_assoc in X0.
    specialize (X0 wf p).
    rewrite subst_context_app in X0; autorewrite with len in X0.
    rewrite app_context_nil_l in X0.
    now rewrite -(All2_local_env_length X).
  - rewrite !subst_context_snoc /=.
    intros Hs subs subs'.
    depelim wf.
    specialize (IHX wf Hs subs subs').
    constructor; auto.
    red. red in p. simpl.
    destruct p as [pb pt].
    epose proof (subst_conv [] Γ Γ (Γ' ,,, Γ0) _ _ _ _ wfΣ subs subs' Hs) as X0.
    rewrite app_context_nil_l app_context_assoc in X0.
    specialize (X0 wf pb).
    epose proof (subst_conv [] Γ Γ (Γ' ,,, Γ0) _ _ _ _ wfΣ subs subs' Hs) as X1.
    rewrite app_context_nil_l app_context_assoc in X1.
    specialize (X1 wf pt).
    rewrite !subst_context_app !app_context_nil_l in X0, X1; autorewrite with len in X0, X1.
    now rewrite -(All2_local_env_length X).
Qed.

Lemma conv_terms_weaken {cf:checker_flags} Σ Γ Γ' args args' :
  wf Σ.1 ->
  wf_local Σ Γ ->
  wf_local Σ Γ' ->
  All (closedn #|Γ|) args -> All (closedn #|Γ|) args' ->
  conv_terms Σ Γ args args' ->
  conv_terms Σ (Γ' ,,, Γ) args args'.
Proof.
  intros wfΣ wf wf' cl cl' conv.
  solve_all.
  eapply weaken_conv; eauto.
Qed.

Lemma conv_terms_subst {cf:checker_flags} Σ Γ Γ' Γ'' Δ s s' args args' :
  wf Σ.1 ->
  wf_local Σ (Γ ,,, Γ' ,,, Δ) ->
  subslet Σ Γ s Γ' ->
  subslet Σ Γ s' Γ'' ->
  conv_terms Σ Γ s s' ->
  conv_terms Σ (Γ ,,, Γ' ,,, Δ) args args' ->
  conv_terms Σ (Γ ,,, subst_context s 0 Δ) (map (subst s #|Δ|) args) (map (subst s' #|Δ|) args').
Proof.
  intros wfΣ wf cl cl' convs conv.
  eapply All2_map.
  eapply (All2_impl conv).
  intros x y eqxy.
  eapply subst_conv; eauto.
Qed.

Lemma cumul_ctx_subst {cf:checker_flags} Σ Γ Γ' Γ'0 Γ'' Δ Δ' s s' :
  wf Σ.1 ->
  wf_local Σ (Γ ,,, Γ' ,,, Γ'' ,,, Δ) ->
  cumul_ctx_rel Σ (Γ ,,, Γ' ,,, Γ'') Δ Δ' ->
  All2 (conv Σ Γ) s s' ->
  untyped_subslet Γ s Γ' ->
  untyped_subslet Γ s' Γ'0 ->
  cumul_ctx_rel Σ (Γ ,,, subst_context s 0 Γ'') (subst_context s #|Γ''| Δ) (subst_context s' #|Γ''| Δ').
Proof.
  intros wfΣ wf. induction 1.
  - simpl. constructor.
  - rewrite !subst_context_snoc /=.
    intros Hs subs subs'.
    depelim wf.
    specialize (IHX wf Hs subs subs').
    constructor; auto.
    red. red in p. simpl.
    epose proof (untyped_subst_cumul Γ Γ' Γ'0 (Γ'' ,,, Γ0) _ _ _ _ wfΣ subs subs' Hs).
    rewrite app_context_assoc in X0.
    specialize (X0 wf p).
    rewrite !subst_context_app app_context_assoc in X0; autorewrite with len in X0.
    now rewrite -(All2_local_env_length X).
  - rewrite !subst_context_snoc /=.
    intros Hs subs subs'. depelim wf.
    specialize (IHX wf Hs subs subs').
    constructor; auto.
    red. red in p. simpl.
    destruct p as [pb pt].
    epose proof (untyped_subst_cumul Γ Γ' Γ'0 (Γ'' ,,, Γ0) _ _ _ _ wfΣ subs subs' Hs) as X0.
    rewrite app_context_assoc in X0.
    specialize (X0 wf pb).
    epose proof (untyped_subst_cumul Γ Γ' Γ'0 (Γ'' ,,, Γ0) _ _ _ _ wfΣ subs subs' Hs) as X1.
    rewrite !app_context_assoc in X1.
    specialize (X1 wf pt).
    rewrite !subst_context_app !app_context_assoc in X0, X1; autorewrite with len in X0, X1.
    now rewrite -(All2_local_env_length X).
Qed.

Lemma All2_local_env_nth_error {cf:checker_flags} Σ Γ Δ Δ' :
  cumul_ctx_rel Σ Γ Δ Δ' ->
  assumption_context Δ ->
  forall n decl, nth_error Δ n = Some decl ->
  ∑ decl', (nth_error Δ' n = Some decl') * (Σ ;;; Γ ,,, skipn (S n) Δ |- decl_type decl <= decl_type decl').
Proof.
  induction 1.
  - move=> n decl /= //. now rewrite nth_error_nil.
  - move=> H [|n'] decl /= //.
    + rewrite /nth_error /= => [= <-].
      eexists; intuition eauto.
    + rewrite /= => Hnth.
      forward IHX by now depelim H.
      destruct (IHX _ _ Hnth) as [decl' [Hnth' cum]].
      eexists; intuition eauto.
  - move=> H; elimtype False; depelim H; simpl in H0; noconf H0.
Qed.

Require Import ssrbool.

Lemma closed_ctx_decl k d Γ : closedn_ctx k (d :: Γ) =
  closed_decl (k + #|Γ|) d && closedn_ctx k Γ.
Proof.
  unfold closedn_ctx at 1.
  rewrite mapi_rev /= forallb_app {2}/id /= andb_true_r.
  replace (#|Γ| - 0) with #|Γ| by lia.
  rewrite andb_comm. f_equal.
  unfold closedn_ctx.
  rewrite mapi_rev (mapi_rec_add _ _ 1 0) /=.
  f_equal.
Qed.

Lemma weaken_cumul_ctx {cf:checker_flags} Σ Γ Γ' Δ Δ' :
  wf Σ.1 ->
  closed_ctx (Γ' ,,, Δ) ->
  closed_ctx (Γ' ,,, Δ') ->
  wf_local Σ Γ ->
  cumul_ctx_rel Σ Γ' Δ Δ' ->
  cumul_ctx_rel Σ (Γ ,,, Γ') Δ Δ'.
Proof.
  intros wfΣ wf wf' wf''. induction 1.
  - simpl. constructor.
  - rewrite /= closed_ctx_decl in wf.
    rewrite /= closed_ctx_decl in wf'.
    move/andP: wf => [wfd wf].
    move/andP: wf' => [wfd' wf'].
    constructor; auto.
    + now eapply IHX.
    + red. red in p.
      rewrite -app_context_assoc.
      eapply weaken_cumul; eauto.
      autorewrite with len; simpl; rewrite (All2_local_env_length X).
      now autorewrite with len in wfd'.
  - rewrite /= closed_ctx_decl in wf.
    rewrite /= closed_ctx_decl in wf'.
    move/andP: wf => [wfd wf].
    move/andP: wf' => [wfd' wf'].
    constructor; auto.
    + now eapply IHX.
    + red. red in p.
      rewrite -app_context_assoc.
      autorewrite with len in *.
      destruct p.
      move/andP: wfd => /= [wfb wft].
      move/andP: wfd' => /= [wfb' wft'].
      rewrite <- (All2_local_env_length X) in *.
      split; eapply weaken_cumul; autorewrite with len; eauto.
Qed.
