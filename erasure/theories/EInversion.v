(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Lia.
From MetaCoq.Template Require Import config utils monad_utils BasicAst AstUtils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction PCUICTyping
     PCUICWeakening PCUICSubstitution PCUICChecker PCUICRetyping PCUICMetaTheory
     PCUICWcbvEval PCUICSR PCUICValidity.
From MetaCoq.Erasure Require Import EAstUtils ELiftSubst ETyping EWcbvEval Extract Prelim.

From Equations Require Import Equations.

Local Open Scope list_scope.
Set Asymmetric Patterns.
Import MonadNotation.

Module PA := PCUICAst.
Module P := PCUICWcbvEval.

Local Existing Instance default_checker_flags.

(** ** Inversion on eval *)


Notation type_Construct_inv := PCUICInversion.inversion_Construct.
Notation type_tFix_inv := PCUICInversion.inversion_Fix.

Lemma eval_box_apps:
  forall (Σ' : E.global_declarations) (e : E.term) (x x' : list E.term),
    All2 (eval Σ') x x' ->
    eval Σ' e EAst.tBox -> eval Σ' (EAst.mkApps e x) EAst.tBox.
Proof.
  intros Σ' e x H2. revert e H2; induction x using rev_ind; cbn; intros; eauto using eval.
  eapply All2_app_inv in H as ((l1' & l2') & (-> & H) & H2).
  depelim H2.
  specialize (IHx e _ H H0). simpl.
  rewrite mkApps_app. simpl. econstructor; eauto.
Qed.
