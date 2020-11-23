(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICTyping PCUICAst PCUICAstUtils
  PCUICWeakening PCUICSubstitution PCUICArities
  PCUICWcbvEval PCUICSR  PCUICInversion
  PCUICUnivSubstitution PCUICElimination (* PCUICContextConversion *)
  PCUICUnivSubst PCUICWeakeningEnv PCUICCumulativity PCUICConfluence
  PCUICInduction PCUICLiftSubst PCUICContexts PCUICGeneration PCUICSpine
  PCUICConversion PCUICValidity PCUICInductives  PCUICConversion
  PCUICInductiveInversion PCUICNormal PCUICSafeLemmata
  PCUICParallelReductionConfluence PCUICSN
  PCUICWcbvEval PCUICClosed PCUICReduction PCUICCSubst.


Module PA := PCUICAst.
Module P := PCUICWcbvEval.

Local Existing Instance config.extraction_checker_flags.

Require Import Equations.Prop.DepElim.
Require Import ssreflect.

Lemma negb_False (p : bool) : negb p -> p -> False.
Proof.
intros n pos. rewrite pos in n => //.
Qed.

(* Arities*)


Lemma isArity_subst:
  forall x2 : term, forall s n, isArity x2 -> isArity (subst s n x2).
Proof.
  induction x2; cbn in *; try tauto; intros; eauto.
Qed.

Lemma isArity_typing_spine {cf:checker_flags} {Σ : global_env_ext} {Γ L T T'} :
    wf Σ -> wf_local Σ Γ -> typing_spine Σ Γ T' L T ->     
    Is_conv_to_Arity Σ Γ T' -> Is_conv_to_Arity Σ Γ T.
Proof.
  intros.
  depind X1.
  - destruct H as (? & ? & ?). sq.
    eapply PCUICCumulativity.red_cumul_inv in H.
    eapply (cumul_trans _ _ _ _ _) in c; tea.
    eapply invert_cumul_arity_l in c; eauto.
  - eapply IHX1.
    destruct H as (? & ? & ?). sq.
    eapply PCUICCumulativity.red_cumul_inv in H.
    eapply (cumul_trans _ _ _ _ _) in c; tea.
    eapply invert_cumul_arity_l in c; eauto.
    destruct c as (? & H1 & H2). sq.
    eapply invert_red_prod in H1 as (? & ? & [] & ?); eauto; subst.
    exists (x2 {0 := hd}). split; sq.
    eapply (PCUICSubstitution.substitution_red Σ Γ [_] [] [_]). eauto. econstructor. econstructor.
    rewrite subst_empty. eassumption. eauto. cbn. eassumption. cbn in H2.
    now eapply isArity_subst.
Qed.

Ltac destruct_sigma H := 
  repeat match type of H with
  | @sigT _ (fun x => _) => let v := fresh x in
    destruct H as (v & H); simpl in H
  | (_ × _)%type => destruct H as (? & H); simpl in H
  end.
  
Lemma closedn_mkApps k f args : closedn k (mkApps f args) = closedn k f && forallb (closedn k) args.
Proof.
  induction args using rev_ind; simpl => //.
  - now rewrite andb_true_r.
  - now rewrite -mkApps_nested /= IHargs forallb_app andb_assoc /= andb_true_r.
Qed. 


Section Arities.
  Context {cf:checker_flags} {Σ : global_env_ext}.
  Context {wfΣ : wf Σ}.

  Lemma invert_cumul_arity_l_gen (Γ : context) (C T : term) :
    Is_conv_to_Arity Σ Γ C -> Σ;;; Γ |- C <= T -> Is_conv_to_Arity Σ Γ T.
  Proof.
    intros [ar [red isA]]. sq.
    intros cum.
    have: Σ ;;; Γ |- ar <= T.
    { transitivity C; eauto. now eapply cumul_red_l_inv; eauto. }
    now eapply invert_cumul_arity_l.
  Qed.

  Lemma invert_cumul_arity_r_gen (Γ : context) (C T : term) :
    Is_conv_to_Arity Σ Γ C -> Σ;;; Γ |- T <= C -> Is_conv_to_Arity Σ Γ T.
  Proof.
    intros [ar [red isA]]. sq.
    intros cum.
    have: Σ ;;; Γ |- T <= ar.
    { transitivity C; eauto. now eapply cumul_red_r_inv; eauto. }
    now eapply invert_cumul_arity_r.
  Qed.
  
  Lemma isArity_ind ind i args : isArity (mkApps (tInd ind i) args) -> False.  
  Proof. destruct args using rev_case; rewrite -? mkApps_nested; auto. Qed.

  Lemma Is_conv_to_Arity_ind Γ ind i args : Is_conv_to_Arity Σ Γ (mkApps (tInd ind i) args) -> False.  
  Proof. 
    intros [ar [red eq]]. sq. 
    eapply red_mkApps_tInd in red as (? & ? & ?); auto. subst ar.
    now eapply isArity_ind in eq.
  Qed.

  Lemma typing_spine_arity_mkApps_Ind Γ T l i u args : 
    wf_local Σ Γ ->
    typing_spine Σ Γ T l (mkApps (tInd i u) args) -> 
    Is_conv_to_Arity Σ Γ T -> False.
  Proof.
    intros wf sp isc.
    eapply (isArity_typing_spine wfΣ wf sp) in isc.
    now eapply Is_conv_to_Arity_ind.
  Qed.

End Arities.

Lemma All2_map_left' {A B  C} (P : A -> B -> Type) l l' (f : C -> A) :
  All2 P (map f l) l' -> All2 (fun x y => P (f x) y) l l'.
Proof. intros. rewrite - (map_id l') in X. eapply All2_map_inv; eauto. Qed.

Lemma head_mkApps t args : head (mkApps t args) = head t.
Proof.
  induction args using rev_ind; simpl; auto.
  now rewrite -mkApps_nested /= head_tapp.
Qed.

Section Spines.
  Context {cf : checker_flags}.
  Context {Σ : global_env_ext}.
  Context (wfΣ : wf Σ.1).
  
  Lemma wf_fixpoint_inv mfix idx decl :
    wf_fixpoint Σ mfix ->
    nth_error mfix idx = Some decl ->
    ∑ mind, (check_one_fix decl = Some mind)  *
      check_recursivity_kind Σ mind Finite.
  Proof.
    rewrite /wf_fixpoint => wffix nthe.
    move: wffix; case E: (map_option_out (map check_one_fix mfix)) => [l|] //.
    apply map_option_Some in E.
    eapply All2_map_left' in E.
    eapply All2_nth_error_Some in E; eauto.
    destruct E as [kn [Hl Hcheck]].
    destruct l as [|hd tl].
    now rewrite nth_error_nil in Hl => //.
    move/andP=> [eqhd checkrec].
    exists kn. split; auto.
    enough (hd = kn) as -> => //.
    clear -Hl eqhd.
    eapply forallb_All in eqhd.
    destruct idx; simpl in Hl; [congruence|].
    eapply All_nth_error in eqhd; eauto.
    now eapply Reflect.eqb_eq in eqhd.
  Qed.
  
  Lemma wf_cofixpoint_inv mfix idx decl :
    wf_cofixpoint Σ mfix ->
    nth_error mfix idx = Some decl ->
    ∑ mind, (check_one_cofix decl = Some mind)  *
      check_recursivity_kind Σ mind CoFinite.
  Proof.
    rewrite /wf_cofixpoint => wffix nthe.
    move: wffix; case E: (map_option_out (map check_one_cofix mfix)) => [l|] //.
    apply map_option_Some in E.
    eapply All2_map_left' in E.
    eapply All2_nth_error_Some in E; eauto.
    destruct E as [kn [Hl Hcheck]].
    destruct l as [|hd tl].
    now rewrite nth_error_nil in Hl => //.
    move/andP=> [eqhd checkrec].
    exists kn. split; auto.
    enough (hd = kn) as -> => //.
    clear -Hl eqhd.
    eapply forallb_All in eqhd.
    destruct idx; simpl in Hl; [congruence|].
    eapply All_nth_error in eqhd; eauto.
    now eapply Reflect.eqb_eq in eqhd.
  Qed.

  Lemma expand_lets_nil t : expand_lets [] t = t.
  Proof. by rewrite /expand_lets /expand_lets_k /= subst_empty lift0_id. Qed.

  Lemma context_assumptions_context {Γ} :
    assumption_context Γ -> 
    context_assumptions Γ = #|Γ|.
  Proof.
    induction 1; simpl; auto.
  Qed.

  Lemma subst_context_lift_id Γ k n : n <= k -> subst_context [tRel n] k (lift_context (S n) (S k) Γ) = lift_context n k Γ.
  Proof.
    intros nk.
    rewrite subst_context_alt !lift_context_alt.
    rewrite mapi_compose.
    apply mapi_ext; len.
    intros n' [? [?|] ?]; unfold lift_decl, subst_decl, map_decl; simpl.
    intros. 
    now rewrite !Nat.add_succ_r !subst_reli_lift_id //.
    f_equal.
    now rewrite !Nat.add_succ_r !subst_reli_lift_id //.
  Qed.
  
  Lemma expand_lets_assumption_context Γ Δ :
    assumption_context Γ -> expand_lets_ctx Γ Δ = Δ.
  Proof.
    induction Γ using rev_ind.
    - by rewrite /expand_lets_ctx /expand_lets_k_ctx /= lift0_context subst0_context.
    - intros ass. eapply assumption_context_app in ass as [assl assx].
      depelim assx.
      rewrite /expand_lets_ctx /expand_lets_k_ctx; len; simpl.
      rewrite extended_subst_app /=. 
      rewrite subst_app_context /=; len.
      rewrite subst_context_lift_id // lift0_context.
      rewrite (context_assumptions_context assl). simpl.
      rewrite !Nat.add_1_r subst_context_lift_id //.
      rewrite /expand_lets_ctx /expand_lets_k_ctx in IHΓ.
      rewrite (context_assumptions_context assl) in IHΓ .
      now simpl in IHΓ.
  Qed.
  
  (* TODO: Where to put this? *)
  Lemma red_it_mkProd_or_LetIn_smash Γ Δ t :
    red Σ Γ
        (it_mkProd_or_LetIn Δ t)
        (it_mkProd_or_LetIn (smash_context [] Δ) (expand_lets Δ t)).
  Proof.
    induction Δ in Γ, t |- * using ctx_length_rev_ind; cbn.
    - now rewrite expand_lets_nil.
    - change (Γ0 ++ [d]) with ([d],,, Γ0).
      rewrite smash_context_app_expand.
      destruct d as [na [b|] ty]; cbn.
      + unfold app_context.
        rewrite expand_lets_vdef it_mkProd_or_LetIn_app app_nil_r.
        cbn.
        rewrite lift0_context lift0_id subst_empty.
        rewrite subst_context_smash_context.
        cbn.
        etransitivity.
        { apply red1_red.
          apply red_zeta. }
        unfold subst1.
        rewrite subst_it_mkProd_or_LetIn.
        rewrite Nat.add_0_r.
        apply X.
        now rewrite subst_context_length.
      + unfold app_context.
        rewrite expand_lets_vass !it_mkProd_or_LetIn_app.
        cbn.
        apply red_prod_r.
        rewrite subst_context_lift_id; auto.
        rewrite lift0_context.
        now apply X.
  Qed.
  
  Lemma conv_it_mkProd_or_LetIn_smash Γ Δ T :
    Σ ;;; Γ |- it_mkProd_or_LetIn Δ T = it_mkProd_or_LetIn (smash_context [] Δ) (expand_lets Δ T).
  Proof.
    eapply red_conv_conv.
    - apply red_it_mkProd_or_LetIn_smash.
    - reflexivity.
  Qed.

  Lemma typing_spine_smash Γ Δ T args T' : 
    typing_spine Σ Γ (it_mkProd_or_LetIn Δ T) args T' ->
    typing_spine Σ Γ (it_mkProd_or_LetIn (smash_context [] Δ) (expand_lets Δ T)) args T'.
  Proof.
    revert T.
    induction Δ using ctx_length_rev_ind; intros T.
    simpl. now rewrite expand_lets_nil.
    rewrite it_mkProd_or_LetIn_app /= smash_context_app.
    destruct d as [na [b|] ty] => /=.
    - autorewrite with len.
      rewrite /mkProd_or_LetIn /=.
      move=> sp; eapply typing_spine_letin_inv in sp; auto.
      rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r in sp.
      specialize (X (subst_context [b] 0 Γ0) ltac:(now autorewrite with len) _ sp).
      rewrite expand_lets_vdef.
      rewrite subst_context_smash_context /= subst_context_nil.
      eapply X.
    - autorewrite with len.
      rewrite /mkProd_or_LetIn /=.
      move=> sp.
      rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=.
      rewrite expand_lets_vass.
      eapply typing_spine_strengthen; eauto.
      eapply congr_cumul_prod; eauto.
      eapply conv_cumul.
      symmetry.
      eapply conv_it_mkProd_or_LetIn_smash. 
  Qed.
  
  Lemma typing_spine_nth_error Γ Δ T args T' n arg decl : 
    assumption_context Δ ->
    wf_local Σ (Γ ,,, Δ) ->  
    typing_spine Σ Γ (it_mkProd_or_LetIn Δ T) args T' ->
    nth_error args n = Some arg ->
    nth_error (List.rev Δ) n = Some decl ->
    Σ ;;; Γ |- arg : subst (List.rev (firstn n args)) 0 decl.(decl_type).
  Proof.
    induction Δ in decl, n, args, arg, T |- * using ctx_length_rev_ind.
    intros. now rewrite nth_error_nil in H1.
    destruct d as [na [b|] ty]; intros ass; eapply assumption_context_app in ass as [assΓ ass].
    * elimtype False; depelim ass.
    * simpl. rewrite !it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /= //.
      intros wf sp; depelim sp. rewrite nth_error_nil //.
      pose proof (All_local_env_app _ _ _ wf) as [_ wfty].
      eapply All_local_env_app in wfty as [wfty _]. depelim wfty.
      eapply cumul_Prod_inv in c as [dom codom]. 2-3:pcuic.
      assert (Σ ;;; Γ |- hd : ty).
      { eapply type_Cumul'; pcuic. eapply conv_cumul. now symmetry. }
      eapply (substitution_cumul0 _ _ _ _ _ _ hd) in codom; eauto.
      eapply typing_spine_strengthen in sp; eauto.
      rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r in sp.
      destruct n => /=.
      + intros [= ->].
        rewrite List.rev_app_distr /= => [=] <- /=.
        now rewrite subst_empty.
      + rewrite List.rev_app_distr => Hnth /= hnth.
        specialize (X (subst_context [hd] 0 Γ0) ltac:(len; reflexivity) (subst [hd] #|Γ0| T) tl n arg
          (subst_decl [hd] n decl)).
        forward X by now eapply assumption_context_fold.
        forward X.
        { eapply substitution_wf_local; eauto. constructor. constructor. now rewrite subst_empty.
          now rewrite app_context_assoc in wf. }
        specialize (X sp Hnth).
        forward X.
        rewrite nth_error_rev; len.
        now eapply nth_error_Some_length in hnth; len in hnth.
        rewrite List.rev_involutive nth_error_subst_context.
        pose proof (nth_error_Some_length hnth).
        rewrite nth_error_rev // rev_involutive in hnth. len in hnth.
        rewrite hnth. simpl. len in H.
        replace (#|Γ0| - S (#|Γ0| - S n) + 0)%nat with n by lia. reflexivity.
        rewrite (subst_app_simpl) /=; len.
        rewrite firstn_length_le. now eapply nth_error_Some_length in Hnth.
        eapply X.
  Qed.

  Lemma typing_spine_all_inv Γ Δ T args T' :
    typing_spine Σ Γ (it_mkProd_or_LetIn Δ T) args T' ->
    #|args| = context_assumptions Δ ->
    (Σ ;;; Γ |- subst (List.rev args) 0 (expand_lets Δ T) <= T') * (isType Σ Γ T').
  Proof.
    induction Δ in args, T |- * using ctx_length_rev_ind.
    - simpl. destruct args => // sp _ /=; rewrite subst_empty expand_lets_nil.
      now depelim sp.
    - rewrite it_mkProd_or_LetIn_app /=; destruct d as [na [b|] ty].
      * rewrite /mkProd_or_LetIn /=. simpl => /= sp.
        eapply typing_spine_letin_inv in sp; eauto.
        len => hargs.
        rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r in sp.
        specialize (X (subst_context [b] 0 Γ0) ltac:(now len) _ _ sp).
        forward X by now len.
        now rewrite expand_lets_vdef.
      * rewrite /mkProd_or_LetIn /=. simpl => /= sp.
        simpl; len => hargs. simpl in hargs.
        rewrite Nat.add_1_r in hargs. destruct args => //.
        depelim sp. noconf hargs.
        eapply cumul_Prod_inv in c as [dom codom]. 2-3:pcuic.
        rewrite expand_lets_vass. simpl.
        eapply (substitution_cumul0 _ _ _ _ _ _ t) in codom; eauto.
        eapply typing_spine_strengthen in sp; eauto.
        rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r in sp.
        specialize (X (subst_context [t] 0 Γ0) ltac:(len; reflexivity) (subst [t] #|Γ0| T) _ sp).
        forward X by now len.
        rewrite subst_app_simpl /=; len; rewrite H.
        now rewrite -(expand_lets_subst_comm _ _ _).
  Qed.

  Lemma typing_spine_more_inv Γ Δ ind u args args' T' :
    typing_spine Σ Γ (it_mkProd_or_LetIn Δ (mkApps (tInd ind u) args)) args' T' ->
    #|args'| > context_assumptions Δ -> False.
  Proof.
    induction Δ in args, args' |- * using ctx_length_rev_ind.
    - simpl. destruct args' using rev_case => /= // sp hargs // /=; try lia.
      depelim sp. eapply (f_equal (@length _)) in H; simpl in H; len in H. lia.
      eapply invert_cumul_prod_r in c as (? & ? & ? & ((? & ?) & ?) & ?); auto.
      eapply red_mkApps_tInd in r as (? & ? & ?); auto. solve_discr.
    - rewrite it_mkProd_or_LetIn_app /=; destruct d as [na [b|] ty].
      * rewrite /mkProd_or_LetIn /=. simpl => /= sp.
        eapply typing_spine_letin_inv in sp; eauto.
        len => hargs.
        rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r subst_mkApps /= in sp.
        apply (H (subst_context [b] 0 Γ0) ltac:(now len) _ _ sp). now len.
      * rewrite /mkProd_or_LetIn /=. simpl => /= sp.
        simpl; len => /= hargs.
        rewrite Nat.add_1_r in hargs. destruct args'; simpl in * => //. lia.
        depelim sp.
        eapply cumul_Prod_inv in c as [dom codom]; pcuic.
        eapply (substitution_cumul0 _ _ _ _ _ _ t) in codom; eauto.
        eapply typing_spine_strengthen in sp; eauto.
        rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r subst_mkApps /= in sp.
        apply (H (subst_context [t] 0 Γ0) ltac:(len; reflexivity) _ _ sp).
        now len.
  Qed.

  Lemma firstn_subst_context (Γ : context) n k s :  
    assumption_context Γ ->
    firstn (#|Γ| - n) (subst_context s k Γ) =
    subst_context s (k + n) (firstn (#|Γ| - n) Γ).
  Proof.
    induction Γ in n, k |-  * using ctx_length_rev_ind; simpl; auto.
    destruct d as [na [b|] ty]; simpl; len; simpl; auto;
    rewrite subst_context_app /=.
    intros ass. eapply assumption_context_app in ass as [_ ass]. depelim ass.
    intros ass. eapply assumption_context_app in ass as [ass _].
    destruct n.
    rewrite Nat.sub_0_r.
    rewrite !firstn_all2; len; simpl; try lia.
    now rewrite subst_context_app.
    replace (#|Γ| + 1 - S n) with (#|Γ| - n) by lia.
    rewrite /app_context !firstn_app; len;
    replace (#|Γ| - n - #|Γ|) with 0 by lia. simpl.
    rewrite Nat.add_succ_r !app_nil_r. apply H; now try lia.
  Qed.

  Lemma typing_spine_nth_error_None Γ Δ T args T' : 
    assumption_context Δ ->
    wf_local Σ (Γ ,,, Δ) ->  
    typing_spine Σ Γ (it_mkProd_or_LetIn Δ T) args T' ->
    nth_error args #|Δ| = None ->
    Σ ;;; Γ |- (subst0 (List.rev args) (it_mkProd_or_LetIn (firstn (#|Δ| - #|args|) Δ) T)) <= T'.
  Proof.
    induction Δ in args, T |- * using ctx_length_rev_ind.
    { intros. eapply nth_error_None in H0. simpl in H0 |- *. destruct args => //; simpl in H0; try lia.
      rewrite subst_empty. simpl in X0. now depelim X0. }
    destruct d as [na [b|] ty]; intros ass; eapply assumption_context_app in ass as [assΓ ass].
    * elimtype False; depelim ass.
    * simpl. rewrite !it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /= //.
      intros wf sp.
      pose proof (All_local_env_app _ _ _ wf) as [_ wfty].
      eapply All_local_env_app in wfty as [wfty _]. depelim wfty.
      intros Hargs. eapply nth_error_None in Hargs.
      len in Hargs. len; simpl.      
      depelim sp. 
      + eapply invert_cumul_prod_l in c as [na' [dom [codom [[[red eqann] eqdom] cum]]]]; auto.
        simpl. rewrite subst_empty. simpl; len.
        simpl. rewrite Nat.sub_0_r firstn_app_2. simpl.
        rewrite it_mkProd_or_LetIn_app /= /mkProd_or_LetIn /=.
        etransitivity.
        2:{ eapply conv_cumul, conv_sym, red_conv. eauto. }
        eapply congr_cumul_prod; eauto.
      + eapply cumul_Prod_inv in c as [dom codom]. 2-3:pcuic.
        assert (Σ ;;; Γ |- hd : ty).
        { eapply type_Cumul'; pcuic. eapply conv_cumul. now symmetry. }
        eapply (substitution_cumul0 _ _ _ _ _ _ hd) in codom; eauto.
        eapply typing_spine_strengthen in sp; eauto.
        rewrite /subst1 subst_it_mkProd_or_LetIn Nat.add_0_r in sp.
        simpl. replace (#|Γ0| + 1 - S #|tl|) with (#|Γ0| - #|tl|) by lia.
        rewrite firstn_app. rewrite (firstn_0 _ (_ - _ - _)); try lia; rewrite app_nil_r.
        move: Hargs; simpl; rewrite Nat.add_1_r => hlen.
        specialize (X (subst_context [hd] 0 Γ0) ltac:(len; reflexivity) (subst [hd] #|Γ0| T) tl).
        forward X by now eapply assumption_context_fold.
        forward X.
        { eapply substitution_wf_local; eauto. constructor. constructor. now rewrite subst_empty.
          now rewrite app_context_assoc in wf. }
        specialize (X sp).
        forward X. len. apply nth_error_None. lia.
        rewrite subst_app_simpl.
        simpl. rewrite subst_it_mkProd_or_LetIn.
        simpl. len.
        len in X.
        rewrite firstn_length_le. lia.
        replace (#|Γ0| - #|tl| + #|tl|)%nat with #|Γ0| by lia.
        rewrite firstn_subst_context in X => //.
  Qed.

  Lemma assumption_context_firstn n Γ :
    assumption_context Γ ->
    assumption_context (firstn n Γ).
  Proof.
    induction n in Γ |- *; simpl; try constructor; auto.
    intros. destruct Γ; simpl; try constructor.
    depelim H. constructor. auto.
  Qed.

  Lemma typing_spine_nth_error_None_prod Γ Δ T args T' n decl : 
    assumption_context Δ ->
    wf_local Σ (Γ ,,, Δ) ->  
    typing_spine Σ Γ (it_mkProd_or_LetIn Δ T) args T' ->
    nth_error args n = None ->
    nth_error (List.rev Δ) n = Some decl ->
    ∑ na dom codom, Σ ;;; Γ |- tProd na dom codom <= T'.
  Proof.
    intros ass wf sp nth nth'.
    eapply typing_spine_nth_error_None in sp; eauto;
    eapply nth_error_None in nth;
    eapply nth_error_Some_length in nth'; len in nth'.
    rewrite subst_it_mkProd_or_LetIn in sp.
    2:{ eapply nth_error_None. lia. }
    set (ctx := subst_context (List.rev args) 0 (firstn (#|Δ| - #|args|) Δ)) in *.
    assert (#|ctx| > 0).
    { rewrite /ctx; len. rewrite firstn_length_le; lia. }
    assert (assumption_context ctx).
    { rewrite /ctx. apply assumption_context_fold. now apply assumption_context_firstn. }  
    destruct ctx using rev_case; simpl in *. lia.
    rewrite it_mkProd_or_LetIn_app in sp.
    move/assumption_context_app: H0 => [ass' assx].
    destruct x as [na [b|] ty]. elimtype False. depelim assx.
    rewrite /mkProd_or_LetIn in sp.
    eexists _, _, _; eauto. eapply sp.
  Qed.

  Lemma wf_fixpoint_spine Γ mfix idx decl args ty : 
    wf_fixpoint Σ.1 mfix ->
    nth_error mfix idx = Some decl ->
    isType Σ Γ (dtype decl) ->
    PCUICGeneration.typing_spine Σ Γ (dtype decl) args ty ->
    match nth_error args decl.(rarg) with 
    | Some arg =>
      ∑ ind u indargs,
      (Σ ;;; Γ |- arg : mkApps (tInd ind u) indargs) *
      check_recursivity_kind Σ.1 (inductive_mind ind) Finite
    | None => ∑ na dom codom, Σ ;;; Γ |- tProd na dom codom <= ty
    end.
  Proof.
    move=> wffix nthe isty.
    eapply wf_fixpoint_inv in nthe; eauto.
    destruct nthe as [mind' [cfix ck]].
    move=> sp. 
    destruct decl as [dna dty dbod rarg].
    rewrite /check_one_fix in cfix. simpl in *.
    case E: (decompose_prod_assum [] dty) => [Γ' concl].
    rewrite E in cfix.
    eapply decompose_prod_assum_it_mkProd_or_LetIn in E.
    simpl in E. subst dty.
    destruct (nth_error _ rarg) eqn:Hnth => //.
    pose proof (nth_error_Some_length Hnth).
    len in H. simpl in H.
    eapply typing_spine_smash in sp.
    destruct (nth_error args rarg) eqn:hargs.
    - eapply typing_spine_nth_error in sp; eauto; cycle 1.
      * eapply smash_context_assumption_context; constructor.
      * eapply wf_local_smash_end; eauto.
        destruct isty as [s Hs].
        eapply inversion_it_mkProd_or_LetIn in Hs; eauto.
        now eapply typing_wf_local.
      * destruct (decompose_app (decl_type c)) as [hd tl] eqn:da.
        destruct (destInd hd) as [[i u]|] eqn:di => //.
        destruct i as [mind i]. noconf cfix.
        eapply decompose_app_inv in da. rewrite da in sp.
        rewrite subst_mkApps in sp.
        destruct hd => //; noconf di. simpl in sp.
        eexists _, ui, _; intuition eauto.
    - eapply typing_spine_nth_error_None_prod in sp; eauto.
      * eapply smash_context_assumption_context; constructor.
      * eapply wf_local_smash_end; eauto.
        destruct isty as [s Hs].
        eapply inversion_it_mkProd_or_LetIn in Hs; eauto.
        now eapply typing_wf_local.
  Qed.

  Lemma wf_cofixpoint_spine Γ mfix idx decl args ty : 
    wf_cofixpoint Σ.1 mfix ->
    nth_error mfix idx = Some decl ->
    isType Σ Γ (dtype decl) ->
    PCUICGeneration.typing_spine Σ Γ (dtype decl) args ty ->
    ∑ Γ' T, (decompose_prod_assum [] (dtype decl) = (Γ', T)) *
    ∑ ind u indargs, (T = mkApps (tInd ind u) indargs) *
    check_recursivity_kind Σ.1 (inductive_mind ind) CoFinite *
    if #|args| <? context_assumptions Γ' then
      (Σ ;;; Γ |- subst0 (List.rev args)
      (it_mkProd_or_LetIn (firstn (context_assumptions Γ' - #|args|) (smash_context [] Γ'))
        (expand_lets Γ' T)) <= ty)
    else
      (#|args| = context_assumptions Γ') *
      (Σ ;;; Γ |- subst (List.rev args) 0 (expand_lets Γ' T) <= ty).
  Proof.
    move=> wffix nthe isty.
    eapply wf_cofixpoint_inv in nthe; eauto.
    destruct nthe as [mind' [cfix ck]].
    move=> sp. 
    destruct decl as [dna dty dbod rarg].
    rewrite /check_one_cofix in cfix. simpl in *.
    case E: (decompose_prod_assum [] dty) => [Γ' concl].
    rewrite E in cfix.
    eapply decompose_prod_assum_it_mkProd_or_LetIn in E.
    simpl in E. subst dty. exists Γ', concl. split; auto.
    destruct (decompose_app concl) as [hd tl] eqn:da.
    destruct (destInd hd) as [[mind i]|] eqn:di => //.
    destruct mind => //. destruct hd => //.
    noconf di. noconf cfix.
    eapply decompose_app_inv in da.
    eexists _, _, _; intuition eauto.
    destruct (Nat.ltb #|args| (context_assumptions Γ')) eqn:lt; [
      eapply Nat.ltb_lt in lt|eapply Nat.ltb_nlt in lt; destruct (Nat.eqb #|args| (context_assumptions Γ')) eqn:eq; 
      [eapply Nat.eqb_eq in eq|eapply Nat.eqb_neq in eq]].
    - eapply typing_spine_smash in sp.
      destruct (nth_error args #|args|) eqn:hargs.
      { rewrite (proj2 (nth_error_None _ _)) // in hargs. }
      destruct (nth_error (List.rev (smash_context [] Γ')) #|args|) as [decl|] eqn:hnth.
      eapply typing_spine_nth_error_None in sp; eauto.
      * now len in sp.
      * eapply smash_context_assumption_context; constructor.
      * eapply wf_local_smash_end; eauto.
        destruct isty as [s Hs].
        eapply inversion_it_mkProd_or_LetIn in Hs; eauto.
        now eapply typing_wf_local.
      * len; simpl. eapply nth_error_None in hargs => //; len in hnth.
        eapply nth_error_None. lia.
      * eapply nth_error_None in hnth => //. len in hnth. lia.
    - eapply typing_spine_all_inv in sp => //.
      subst concl.
      rewrite expand_lets_mkApps subst_mkApps /= in sp.
      destruct sp. split; auto.
      now rewrite expand_lets_mkApps subst_mkApps /=.
    - subst concl; eapply typing_spine_more_inv in sp; try lia.
  Qed.
  
  (* Lemma app_fix_prod_indarg Σ mfix idx args na dom codom decl :
    wf Σ.1 ->
    Σ ;;; [] |- mkApps (tFix mfix idx) args : tProd na dom codom ->
    nth_error mfix idx = Some decl ->
    #|args| = decl.(rarg) ->
    ∑ ind u indargs, dom = mkApps (tInd ind u) indargs *
      isType Σ [] (mkApps (tInd ind u) indargs) * 
      (check_recursivity_kind Σ.1 (inductive_mind ind) Finite).
  Proof.
    intros wfΣ  tapp.
    eapply inversion_mkApps in tapp as [A [Hfix Hargs]]; eauto.
    eapply inversion_Fix in Hfix;eauto.
    destruct Hfix as [decl [fixg [Hnth [Hist [_ [wf cum]]]]]].
    rewrite /wf_fixpoint in wf. *)

End Spines.

(*
Section Normalization.
  Context {cf:checker_flags} (Σ : global_env_ext).
  Context {wfΣ : wf Σ}.
  
  Section reducible.
    Lemma reducible Γ t : sum (∑ t', red1 Σ Γ t t') (forall t', red1 Σ Γ t t' -> False).
    Proof.
    Local Ltac lefte := left; eexists; econstructor; eauto.
    Local Ltac leftes := left; eexists; econstructor; solve [eauto].
    Local Ltac righte := right; intros t' red; depelim red; solve_discr; eauto 2.
    induction t in Γ |- * using term_forall_list_ind.
    (*all:try solve [righte].
    - destruct (nth_error Γ n) eqn:hnth.
        destruct c as [na [b|] ty]; [lefte|righte].
        * rewrite hnth; reflexivity.
        * rewrite hnth /= // in e.
        * righte. rewrite hnth /= // in e.
    - admit.
    - destruct (IHt1 Γ) as [[? ?]|]; [lefte|].
        destruct (IHt2 (Γ ,, vass n t1)) as [[? ?]|]; [|righte].
        leftes.
    - destruct (IHt1 Γ) as [[? ?]|]; [lefte|].
        destruct (IHt2 (Γ ,, vass n t1)) as [[? ?]|]; [|righte].
        leftes.
    - destruct (IHt1 Γ) as [[? ?]|]; [lefte|].
        destruct (IHt2 Γ) as [[? ?]|]; [lefte|].
        destruct (IHt3 (Γ ,, vdef n t1 t2)) as [[? ?]|]; [|].
        leftes. lefte.
    - destruct (IHt1 Γ) as [[? ?]|]; [lefte|].
        destruct (IHt2 Γ) as [[? ?]|]; [leftes|].
        destruct (PCUICParallelReductionConfluence.view_lambda_fix_app t1 t2).
        * rewrite [tApp _ _](mkApps_nested _ _ [a]).
        destruct (unfold_fix mfix i) as [[rarg body]|] eqn:unf.
        destruct (is_constructor rarg (l ++ [a])) eqn:isc; [leftes|]; eauto.
        right => t' red; depelim red; solve_discr; eauto.
        rewrite -mkApps_nested in H. noconf H. eauto. 
        rewrite -mkApps_nested in H. noconf H. eauto.
        eapply (f_equal (@length _)) in H1. rewrite /= app_length /= // in H1; lia.
        eapply (f_equal (@length _)) in H1. rewrite /= app_length /= // in H1; lia.
        righte; try (rewrite -mkApps_nested in H; noconf H); eauto.
        eapply (f_equal (@length _)) in H1. rewrite /= app_length /= // in H1; lia.
        eapply (f_equal (@length _)) in H1. rewrite /= app_length /= // in H1; lia.
        * admit.
        * righte. destruct args using rev_case; solve_discr; noconf H.
        rewrite H in i. eapply negb_False; eauto.
        rewrite -mkApps_nested; eapply isFixLambda_app_mkApps' => //.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.*)
    
    Admitted.
  End reducible.

  Lemma reducible' Γ t : sum (∑ t', red1 Σ Γ t t') (normal Σ Γ t).
  Proof.
    Ltac lefte := left; eexists; econstructor; eauto.
    Ltac leftes := left; eexists; econstructor; solve [eauto].
    Ltac righte := right; (solve [repeat (constructor; eauto)])||(repeat constructor).
    induction t in Γ |- * using term_forall_list_ind.
    all:try solve [righte].
    - destruct (nth_error Γ n) eqn:hnth.
      destruct c as [na [b|] ty]; [lefte|].
      * rewrite hnth; reflexivity.
      * right. do 2 constructor; rewrite hnth /= //.
      * righte. rewrite hnth /= //.
    - admit.
    - destruct (IHt1 Γ) as [[? ?]|]; [lefte|].
      destruct (IHt2 (Γ ,, vass n t1)) as [[? ?]|]; [|].
      leftes. right; solve[constructor; eauto].
    - destruct (IHt1 Γ) as [[? ?]|]; [lefte|].
      destruct (IHt2 (Γ ,, vass n t1)) as [[? ?]|]; [leftes|leftes].
    - destruct (IHt1 Γ) as [[? ?]|]; [lefte|].
      destruct (IHt2 Γ) as [[? ?]|]; [leftes|].
      destruct (PCUICParallelReductionConfluence.view_lambda_fix_app t1 t2).
      * rewrite [tApp _ _](mkApps_nested _ _ [a]).
        destruct (unfold_fix mfix i) as [[rarg body]|] eqn:unf.
        destruct (is_constructor rarg (l ++ [a])) eqn:isc; [leftes|]; eauto.
        right; constructor. rewrite -mkApps_nested. constructor. admit. admit.  admit.
      * admit.
      * admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
  Admitted. 

  Lemma normalizer {Γ t ty} :
    Σ ;;; Γ |- t : ty ->
    ∑ nf, (red Σ.1 Γ t nf) * normal Σ Γ nf.
  Proof.
    intros Hty.
    unshelve epose proof (PCUICSN.normalisation Σ Γ t (iswelltyped _ _ _ ty Hty)).
    clear ty Hty.
    move: t H. eapply Fix_F.
    intros x IH.    
    destruct (reducible' Γ x) as [[t' red]|nred].
    specialize (IH t'). forward IH by (constructor; auto).
    destruct IH as [nf [rednf norm]].
    exists nf; split; auto. now transitivity t'.
    exists x. split; [constructor|assumption].
  Qed. 

  Derive Signature for neutral normal.

  Lemma typing_var {Γ n ty} : Σ ;;; Γ |- (tVar n) : ty -> False.
  Proof. intros Hty; depind Hty; eauto. Qed.

  Lemma typing_evar {Γ n l ty} : Σ ;;; Γ |- (tEvar n l) : ty -> False.
  Proof. intros Hty; depind Hty; eauto. Qed.

  Definition axiom_free Σ :=
    forall c decl, declared_constant Σ c decl -> cst_body decl <> None.

  Lemma neutral_empty t ty : axiom_free Σ -> Σ ;;; [] |- t : ty -> neutral Σ [] t -> False.
  Proof.
    intros axfree typed ne.
    pose proof (PCUICClosed.subject_closed wfΣ typed) as cl.
    depind ne.
    - now simpl in cl.
    - now eapply typing_var in typed.
    - now eapply typing_evar in typed.
    - eapply inversion_Const in typed as [decl [wfd [declc [cu cum]]]]; eauto.
      specialize (axfree  _ _ declc). specialize (H decl).
      destruct (cst_body decl); try congruence.
      now specialize (H t declc eq_refl).
    - simpl in cl; move/andP: cl => [clf cla].
      eapply inversion_App in typed as [na [A [B [Hf _]]]]; eauto.
    - simpl in cl; move/andP: cl => [/andP[_ clc] _].
      eapply inversion_Case in typed; firstorder eauto.
    - eapply inversion_Proj in typed; firstorder auto.
  Qed.

  Lemma ind_normal_constructor t i u args : 
    axiom_free Σ ->
    Σ ;;; [] |- t : mkApps (tInd i u) args -> normal Σ [] t -> construct_cofix_discr (head t).
  Proof.
    intros axfree Ht capp. destruct capp.
    - eapply neutral_empty in H; eauto.
    - eapply inversion_Sort in Ht as (? & ? & ? & ? & ?); auto.
      eapply invert_cumul_sort_l in c as (? & ? & ?).
      eapply red_mkApps_tInd in r as (? & eq & ?); eauto; eauto.
      solve_discr.
    - eapply inversion_Prod in Ht as (? & ? & ? & ? & ?); auto.
      eapply invert_cumul_sort_l in c as (? & ? & ?).
      eapply red_mkApps_tInd in r as (? & eq & ?); eauto; eauto.
      solve_discr.
    - eapply inversion_Lambda in Ht as (? & ? & ? & ? & ?); auto.
      eapply invert_cumul_prod_l in c as (? & ? & ? & (? & ?) & ?); auto.
      eapply red_mkApps_tInd in r as (? & eq & ?); eauto; eauto.
      solve_discr.
    - now rewrite head_mkApps /= /head /=.
    - eapply PCUICValidity.inversion_mkApps in Ht as (? & ? & ?); auto.
      eapply inversion_Ind in t as (? & ? & ? & decli & ? & ?); auto.
      eapply PCUICSpine.typing_spine_strengthen in t0; eauto.
      pose proof (on_declared_inductive wfΣ decli) as [onind oib].
      rewrite oib.(ind_arity_eq) in t0.
      rewrite !subst_instance_constr_it_mkProd_or_LetIn in t0.
      eapply typing_spine_arity_mkApps_Ind in t0; eauto.
      eexists; split; [sq|]; eauto.
      now do 2 eapply isArity_it_mkProd_or_LetIn.
    - admit. (* wf of fixpoints *)
    - now rewrite /head /=. 
  Admitted.

  Lemma red_normal_constructor t i u args : 
    axiom_free Σ ->
    Σ ;;; [] |- t : mkApps (tInd i u) args ->
    ∑ hnf, (red Σ.1 [] t hnf) * construct_cofix_discr (head hnf).
  Proof.
    intros axfree Ht. destruct (normalizer Ht) as [nf [rednf capp]].
    exists nf; split; auto.
    eapply subject_reduction in Ht; eauto.
    now eapply ind_normal_constructor.
  Qed.

End Normalization.
*)

(** Evaluation is a subrelation of reduction: *)

Tactic Notation "redt" uconstr(y) := eapply (CRelationClasses.transitivity (R:=red _ _) (y:=y)).

Section WeakNormalization.
  Context {cf:checker_flags} (Σ : global_env_ext).
  Context {wfΣ : wf Σ}.
  
  Section reducible.
  Notation wh_neutral := (whne RedFlags.default).
  Notation wh_normal := (whnf RedFlags.default).

  Transparent construct_cofix_discr.

  Lemma value_whnf t : closed t -> value Σ t -> wh_normal Σ [] t.
  Proof.
    intros cl ev.
    induction ev in cl |- * using value_values_ind.
    destruct t; simpl in H; try discriminate; try solve [constructor; constructor].
    - eapply (whnf_indapp _ _ [] _ _ []).
    - eapply (whnf_cstrapp _ _ [] _ _ _ []).
    - eapply (whnf_fixapp _ _ [] _ _ []).
      destruct unfold_fix as [[rarg body]|] => /= //.
      now rewrite nth_error_nil.
    - eapply (whnf_cofixapp _ _ [] _ _ []). 
    - unfold value_head in H. destruct t => //.
      constructor; eapply whne_mkApps.
      cbn in H; destruct lookup_env eqn:eq => //.
      destruct g => //. destruct c => //. destruct cst_body => //.
      eapply whne_const; eauto.
    - destruct f => //. cbn in H.
      destruct cunfold_fix as [[rarg body]|] eqn:unf => //.
      pose proof cl as cl'.
      rewrite closedn_mkApps in cl'. move/andP: cl' => [clfix _].
      rewrite -P.closed_unfold_fix_cunfold_eq in unf => //.
      rewrite /unfold_fix in unf.
      destruct nth_error eqn:nth => //. noconf unf.
      eapply whnf_fixapp. rewrite /unfold_fix nth.
      eapply Nat.leb_le in H. now eapply nth_error_None.
  Qed.

  Lemma eval_whne t t' : closed t -> eval Σ t t' -> wh_normal Σ [] t'.
  Proof.
    intros cl ev.
    pose proof (eval_closed Σ _ _ cl ev).
    eapply eval_to_value in ev.
    now eapply value_whnf.
  Qed.

  (*
  Lemma reducible Γ t : sum (∑ t', red1 Σ Γ t t') (wh_normal Σ Γ t).
  Proof.
    Ltac lefte := left; eexists; econstructor; eauto.
    Ltac leftes := left; eexists; econstructor; solve [eauto].
    Ltac righte := right; (solve [repeat (constructor; eauto)])||(repeat constructor).
    induction t in Γ |- * using term_forall_list_ind.
    all:try solve [righte].
    - destruct (nth_error Γ n) eqn:hnth.
      destruct c as [na [b|] ty]; [lefte|].
      * rewrite hnth; reflexivity.
      * right. do 2 constructor; rewrite hnth /= //.
      * righte. rewrite hnth /= //. admit.
    - destruct (IHt1 Γ) as [[? ?]|]; [lefte|].
      destruct (IHt2 Γ) as [[? ?]|]; [leftes|].
      destruct (IHt2 (Γ ,, vass n t1)) as [[? ?]|]; [|].
      leftes. leftes.
    - destruct (IHt1 Γ) as [[? ?]|]; [lefte|].
      destruct (IHt2 Γ) as [[? ?]|]; [leftes|].
      destruct (PCUICParallelReductionConfluence.view_lambda_fix_app t1 t2).
      * rewrite [tApp _ _](mkApps_nested _ _ [a]).
        destruct (unfold_fix mfix i) as [[rarg body]|] eqn:unf.
        + destruct (is_constructor rarg (l ++ [a])) eqn:isc; [leftes|]; eauto.
          right. rewrite /is_constructor in isc.
          destruct nth_error eqn:eq.
          ++ constructor; eapply whne_fixapp; eauto. admit.
          ++ eapply whnf_fixapp. rewrite unf //.
        + right. eapply whnf_fixapp. rewrite unf //.
      * left. induction l; simpl. eexists. constructor.
        eexists. eapply app_red_l. eapply red1_mkApps_l. constructor.
      * admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
  Admitted. 

  Lemma normalizer {Γ t ty} :
    Σ ;;; Γ |- t : ty ->
    ∑ nf, (red Σ.1 Γ t nf) * wh_normal Σ Γ nf.
  Proof.
    intros Hty.
    unshelve epose proof (PCUICSN.normalisation Σ Γ t (iswelltyped _ _ _ ty Hty)).
    clear ty Hty.
    move: t H. eapply Fix_F.
    intros x IH.    
    destruct (reducible  Γ x) as [[t' red]|nred].
    specialize (IH t'). forward IH by (constructor; auto).
    destruct IH as [nf [rednf norm]].
    exists nf; split; auto. now transitivity t'.
    exists x. split; [constructor|assumption].
  Qed. *)

  Lemma typing_var {Γ n ty} : Σ ;;; Γ |- (tVar n) : ty -> False.
  Proof. intros Hty; depind Hty; eauto. Qed.

  Lemma typing_evar {Γ n l ty} : Σ ;;; Γ |- (tEvar n l) : ty -> False.
  Proof. intros Hty; depind Hty; eauto. Qed.

  Definition axiom_free Σ :=
    forall c decl, declared_constant Σ c decl -> cst_body decl <> None.

  Lemma invert_cumul_prod_ind {Γ na dom codom ind u args} :
    Σ ;;; Γ |- tProd na dom codom <= mkApps (tInd ind u) args -> False.
  Proof.
    intros ht; eapply invert_cumul_prod_l in ht as (? & ? & ? & ((? & ?) & ?) & ?); auto.
    eapply red_mkApps_tInd in r as (? & ? & ?); auto. solve_discr.
  Qed.

  Lemma invert_cumul_ind_prod {Γ na dom codom ind u args} :
    Σ ;;; Γ |- mkApps (tInd ind u) args <= tProd na dom codom -> False.
  Proof.
    intros ht; eapply invert_cumul_prod_r in ht as (? & ? & ? & ((? & ?) & ?) & ?); auto.
    eapply red_mkApps_tInd in r as (? & ? & ?); auto. solve_discr.
  Qed.

  Lemma invert_cumul_ind_ind {Γ ind ind' u u' args args'} :
    Σ ;;; Γ |- mkApps (tInd ind u) args <= mkApps (tInd ind' u') args' ->
    (Reflect.eqb ind ind' * PCUICEquality.R_global_instance Σ (eq_universe Σ) (leq_universe Σ) (IndRef ind) #|args| u u' *
      All2 (conv Σ Γ) args args').
  Proof.
    intros ht; eapply invert_cumul_ind_l in ht as (? & ? & ? & ? & ?); auto.
    eapply red_mkApps_tInd in r as (? & ? & ?); auto. solve_discr.
    noconf H. subst.
    intuition auto. eapply eq_inductive_refl.
    transitivity x1; auto. symmetry. now eapply red_terms_conv_terms.
  Qed.

  Lemma typing_cofix_coind {Γ mfix idx args ind u indargs} :
    Σ ;;; Γ |- mkApps (tCoFix mfix idx) args : mkApps (tInd ind u) indargs ->
    check_recursivity_kind Σ.1 (inductive_mind ind) CoFinite.
  Proof.
    intros tyarg.
    eapply inversion_mkApps in tyarg as [A [Hcof sp]]; auto.
    eapply inversion_CoFix in Hcof as (? & ? & ? & ? & ? & ? & ?); auto.
    eapply nth_error_all in a; eauto.
    simpl in a.
    eapply typing_spine_strengthen in sp; eauto.
    eapply wf_cofixpoint_spine in sp as (Γ' & concl & da & ?); eauto.
    eapply decompose_prod_assum_it_mkProd_or_LetIn in da.
    simpl in da.
    move: s => [ind' [u' [indargs' [[ceq ccum] ck]]]].
    subst concl.  move: ck.
    elim: Nat.ltb_spec => Hargs.
    - rewrite subst_it_mkProd_or_LetIn; len.
      set (ctx := subst_context _ _ _).
      assert(assumption_context ctx).
      eapply assumption_context_fold, assumption_context_firstn, smash_context_assumption_context; constructor.
      assert (#|ctx| > 0).
      { rewrite /ctx; len; rewrite firstn_length_le. len; lia. lia. }
      destruct ctx as [|ctx [na [b|] ty]] using rev_case. simpl in H0; lia.
      elimtype False; move/assumption_context_app: H => [ass assd]; depelim assd.
      move/assumption_context_app: H => [ass assd]; depelim assd.
      rewrite it_mkProd_or_LetIn_app /mkProd_or_LetIn /= => cum.
      now eapply invert_cumul_prod_ind in cum.
    - move=> [hargs ccum'].
      rewrite expand_lets_mkApps subst_mkApps /= in ccum'.
      eapply invert_cumul_ind_ind in ccum' as ((? & ?) & ?).
      len in r. eapply Reflect.eqb_eq in i1. now subst ind'.
  Qed.

  Lemma check_recursivity_kind_inj {mind rk rk'} :
    check_recursivity_kind Σ mind rk ->
    check_recursivity_kind Σ mind rk' -> rk = rk'.
  Proof.
    rewrite /check_recursivity_kind.
    case: lookup_env => //; case => // m.
    elim: Reflect.eqb_spec;
    elim: Reflect.eqb_spec; congruence.
  Qed.
  
  Lemma invert_cumul_sort_ind {Γ s ind u args} :
    Σ;;; Γ |- tSort s <= mkApps (tInd ind u) args -> False.
  Proof.
    intros cum.
    apply PCUICConversion.invert_cumul_sort_l in cum as (?&?&?).
    apply PCUICConfluence.red_mkApps_tInd in r as (?&?&?); auto.
    solve_discr.
  Qed.

  Lemma invert_ind_ind Γ ind u args ind' u' args' :
    Σ;;; Γ |- mkApps (tInd ind u) args : mkApps (tInd ind' u') args' -> False.
  Proof.
    intros typ.
    eapply inversion_mkApps in typ as (?&?&?); auto.
    eapply inversion_Ind in t as (?&?&?&decl&?&?); auto.
    eapply PCUICSpine.typing_spine_strengthen in t0; eauto.
    pose proof (PCUICWeakeningEnv.on_declared_inductive wfΣ decl) as [onind oib].
    rewrite oib.(ind_arity_eq) in t0.
    rewrite !subst_instance_constr_it_mkProd_or_LetIn in t0.
    eapply typing_spine_arity_mkApps_Ind in t0; eauto.
    eexists; split; [sq|]; eauto.
    now do 2 eapply PCUICArities.isArity_it_mkProd_or_LetIn.
  Qed.

  Lemma invert_fix_ind Γ mfix i args ind u args' :
    match unfold_fix mfix i with
    | Some (rarg, _) => nth_error args rarg = None
    | _ => True
    end ->
    Σ;;; Γ |- mkApps (tFix mfix i) args : mkApps (tInd ind u) args' -> False.
  Proof.
    intros no_arg typ.
    eapply inversion_mkApps in typ as (?&?&?); eauto.
    eapply inversion_Fix in t as (? & ? & ? & ? & ? & ? & ?); auto.
    eapply PCUICSpine.typing_spine_strengthen in t0; eauto.
    eapply nth_error_all in a; eauto. simpl in a.
    unfold unfold_fix in no_arg.
    rewrite e in no_arg.
    eapply (wf_fixpoint_spine wfΣ) in t0; eauto.
    rewrite no_arg in t0. destruct t0 as [na [dom [codom cum]]].
    eapply PCUICConversion.invert_cumul_prod_l in cum; auto.
    destruct cum as (? & ? & ? & ((? & ?) & ?) & ?).
    eapply PCUICConfluence.red_mkApps_tInd in r as [? [eq _]]; auto.
    solve_discr.
  Qed.

  Lemma wh_neutral_empty_gen t Γ : axiom_free Σ -> wh_neutral Σ Γ t -> forall ty, Σ ;;; Γ |- t : ty -> Γ = [] -> False
  with wh_normal_empty_gen t Γ i u args : axiom_free Σ -> wh_normal Σ Γ t -> Σ ;;; Γ |- t : mkApps (tInd i u) args -> 
      Γ = [] -> construct_cofix_discr (head t).
  Proof.
    intros axfree ne ty typed.
    2:intros axfree ne typed.
    all:pose proof (subject_closed wfΣ typed) as cl;
    destruct ne; intros eqΓ;  simpl in *; try discriminate.
    - rewrite eqΓ in cl => //.
    - now eapply typing_var in typed.
    - now eapply typing_evar in typed.
    - clear wh_neutral_empty_gen wh_normal_empty_gen. subst.
      apply inversion_Const in typed as [decl' [wfd [declc [cu cum]]]]; eauto.
      specialize (axfree  _ _ declc).
      red in declc. rewrite declc in e. noconf e. congruence.
    - simpl in cl; move/andP: cl => [clf cla].
      eapply inversion_App in typed as [na [A [B [Hf _]]]]; eauto.
    - specialize (wh_neutral_empty_gen _ _ axfree ne). subst.
      simpl in cl. 
      eapply inversion_mkApps in typed as (? & ? & ?); eauto.
      eapply inversion_Fix in t as (? & ? & ? & ? & ? & ? & ?); auto.
      eapply typing_spine_strengthen in t0; eauto.
      eapply nth_error_all in a; eauto. simpl in a.
      rewrite /unfold_fix in e. rewrite e1 in e. noconf e.
      eapply (wf_fixpoint_spine wfΣ) in t0; eauto.
      rewrite e0 in t0. destruct t0 as [ind [u [indargs [tyarg ckind]]]].
      clear wh_normal_empty_gen.
      now specialize (wh_neutral_empty_gen _ tyarg eq_refl).
    - move/andP: cl => [/andP[_ clc] _].
      eapply inversion_Case in typed; firstorder eauto.
    - eapply inversion_Proj in typed; firstorder auto.
    - eapply wh_neutral_empty_gen in w; eauto.
    - eapply inversion_Sort in typed as (? & ? & ?); auto.
      eapply invert_cumul_sort_l in c as (? & ? & ?); auto.
      eapply red_mkApps_tInd in r as (? & eq & ?); eauto; eauto.
      solve_discr.
    - eapply inversion_Prod in typed as (? & ? & ? & ? & ?); auto.
      eapply invert_cumul_sort_l in c as (? & ? & ?); auto.
      eapply red_mkApps_tInd in r as (? & eq & ?); eauto; eauto.
      solve_discr.
    - eapply inversion_Lambda in typed as (? & ? & ? & ? & ?); auto.
      eapply invert_cumul_prod_l in c as (? & ? & ? & ((? & ?) & ?) & ?); auto.
      eapply red_mkApps_tInd in r as (? & eq & ?); eauto; eauto.
      solve_discr.
    - now rewrite head_mkApps /= /head /=.
    - exfalso; eapply invert_ind_ind; eauto.
    - exfalso; eapply invert_fix_ind; eauto.
    - now rewrite head_mkApps /head /=.
  Qed.

  Lemma wh_neutral_empty t ty : axiom_free Σ ->
    Σ ;;; [] |- t : ty -> 
    wh_neutral Σ [] t -> 
    False.
  Proof. intros; eapply wh_neutral_empty_gen; eauto. Qed.

  Lemma wh_normal_ind_discr t i u args : axiom_free Σ -> 
      Σ ;;; [] |- t : mkApps (tInd i u) args -> 
      wh_normal Σ [] t -> 
      construct_cofix_discr (head t).
  Proof. intros. eapply wh_normal_empty_gen; eauto. Qed.

  Lemma whnf_ind_finite t ind u indargs : 
    axiom_free Σ ->
    Σ ;;; [] |- t : mkApps (tInd ind u) indargs ->
    wh_normal Σ [] t ->
    check_recursivity_kind Σ (inductive_mind ind) Finite ->
    isConstruct_app t.
  Proof.
    intros axfree typed whnf ck.
    rewrite /isConstruct_app.
    eapply wh_normal_ind_discr in whnf; eauto.
    rewrite /head in whnf.
    destruct (decompose_app t) as [hd tl] eqn:da; simpl in *.
    destruct hd eqn:eqh => //. subst hd.
    eapply decompose_app_inv in da. subst.
    eapply typing_cofix_coind in typed.
    now move: (check_recursivity_kind_inj typed ck).
  Qed.

  Lemma fix_app_is_constructor {mfix idx args ty narg fn} : 
    axiom_free Σ ->
    Σ;;; [] |- mkApps (tFix mfix idx) args : ty ->
    unfold_fix mfix idx = Some (narg, fn) ->
    match nth_error args narg return Type with
    | Some a => wh_normal Σ [] a -> isConstruct_app a
    | None => ∑ na dom codom, Σ ;;; [] |- tProd na dom codom <= ty
    end.
  Proof.
    intros axfree typed unf.
    eapply inversion_mkApps in typed as (? & ? & ?); eauto.
    eapply inversion_Fix in t as (? & ? & ? & ? & ? & ? & ?); auto.
    eapply typing_spine_strengthen in t0; eauto.
    eapply nth_error_all in a; eauto. simpl in a.
    rewrite /unfold_fix in unf. rewrite e in unf.
    noconf unf.
    eapply (wf_fixpoint_spine wfΣ) in t0; eauto.
    rewrite /is_constructor. destruct (nth_error args (rarg x0)) eqn:hnth.
    destruct_sigma t0. destruct t0.
    intros norm.
    eapply whnf_ind_finite in t0; eauto.
    assumption.
  Qed.

  (** Evaluation on well-typed terms corresponds to reduction. 
      It differs in two ways from standard reduction: 
      - using closed substitution operations applicable only on closed terms
      - it does not check that fixpoints that are applied to enough arguments 
        have a constructor at their recursive argument as it is ensured by typing. *)

  Lemma wcbeval_red t ty u :
    axiom_free Σ ->
    Σ ;;; [] |- t : ty ->
    eval Σ t u -> red Σ [] t u.
  Proof.
  intros axfree Hc He.
  revert ty Hc.
  induction He; simpl; move=> ty Ht;
    try solve[econstructor; eauto].

  - eapply inversion_App in Ht as (? & ? & ? & ? & ? & ?); auto.
    redt (tApp (tLambda na t b) a); eauto.
    eapply red_app; eauto.
    redt (tApp (tLambda na t b) a'). eapply red_app; eauto.
    specialize (IHHe1 _ t0). specialize (IHHe2 _ t1).
    redt (csubst a' 0 b).
    rewrite (closed_subst a' 0 b).
    eapply eval_closed; eauto. now eapply subject_closed in t1.
    eapply red1_red. constructor.
    pose proof (subject_closed wfΣ t1); auto.
    eapply eval_closed in H; eauto.
    eapply subject_reduction in IHHe1. 2-3:eauto.
    eapply inversion_Lambda in IHHe1 as (? & ? & ? & ? & ?); eauto.
    eapply (substitution0 _ []) in t3; eauto.
    eapply IHHe3.
    rewrite (closed_subst a' 0 b); auto.
    rewrite /subst1 in t3. eapply t3.
    eapply type_Cumul; eauto.
    eapply subject_reduction in IHHe2; eauto.
    eapply cumul_Prod_inv in c0 as [dom codom]; eauto.
    eapply conv_cumul; now symmetry.

  - eapply inversion_LetIn in Ht as (? & ? & ? & ? & ? & ?); auto.
    redt (tLetIn na b0' t b1); eauto.
    eapply red_letin; eauto.
    redt (b1 {0 := b0'}); auto.
    do 2 econstructor.
    specialize (IHHe1 _ t1).
    rewrite /subst1.
    rewrite -(closed_subst b0' 0 b1).
    eapply subject_reduction in t1; eauto. eapply subject_closed in t1; eauto.
    eapply IHHe2.
    rewrite closed_subst.
    eapply subject_reduction in t1; eauto. eapply subject_closed in t1; eauto.
    eapply substitution_let in t2; eauto.
    eapply subject_reduction in t2.
    3:{ eapply (red_red _ _ [vass na t] []); eauto. repeat constructor. }    
    eapply t2. auto.
    

  - redt (subst_instance_constr u body); auto.
    eapply red1_red. econstructor; eauto.
    eapply IHHe. eapply subject_reduction; eauto.
    eapply red1_red. econstructor; eauto.

  - epose proof (subject_reduction Σ [] _ _ _ wfΣ Ht).
    apply inversion_Case in Ht; auto; destruct_sigma Ht.
    specialize (IHHe1 _ t0).
    assert (red Σ [] (tCase (ind, pars) p discr brs) (iota_red pars c args brs)).
    { redt _.
      eapply red_case; eauto. eapply All2_refl; intros; eauto.
      eapply red1_red; constructor. }
    specialize (X X0).
    redt _; eauto.

  - epose proof (subject_reduction Σ [] _ _ _ wfΣ Ht).
    apply inversion_Proj in Ht; auto; destruct_sigma Ht.
    specialize (IHHe1 _ t).
    assert (red Σ [] (tProj (i, pars, arg) discr) a).
    { redt _.
      eapply red_proj_c; eauto.
      eapply red1_red; constructor; auto. }
    specialize (X X0).
    redt _; eauto.

  - epose proof (subject_reduction Σ [] _ _ _ wfΣ Ht).
    apply inversion_App in Ht; auto; destruct_sigma Ht.
    specialize (IHHe1 _ t).
    specialize (IHHe2 _ t0).
    epose proof (subject_reduction Σ [] _ _ _ wfΣ t IHHe1) as Ht2.
    epose proof (subject_reduction Σ [] _ _ _ wfΣ t0 IHHe2) as Ha2.
    assert (red Σ [] (tApp f a) (tApp (mkApps fn argsv) av)).
    { redt _.
      eapply red_app; eauto.
      rewrite ![tApp _ _](mkApps_nested _ _ [_]).
      eapply red1_red. 
      rewrite -closed_unfold_fix_cunfold_eq in e.
      eapply subject_closed in Ht2; auto.
      rewrite closedn_mkApps in Ht2. now move/andP: Ht2 => [clf _].
      eapply red_fix; eauto.
      assert (Σ ;;; [] |- mkApps (tFix mfix idx) (argsv ++ [av]) : B {0 := av}).
      { rewrite -mkApps_nested /=. eapply type_App; eauto. }
      epose proof (fix_app_is_constructor axfree X0 e); eauto.
      rewrite /is_constructor.
      destruct nth_error eqn:hnth => //.
      assert (All (closedn 0) (argsv ++ [av])).
      { eapply subject_closed in X0; eauto.
        rewrite closedn_mkApps in X0.
        move/andP: X0 => [clfix clargs].
        now eapply forallb_All in clargs. }
      assert (All (value Σ) (argsv ++ [av])).
      { eapply All_app_inv; [|constructor; [|constructor]].
        eapply eval_to_value in He1.
        eapply value_mkApps_inv in He1 as [[[-> Hat]|[vh vargs]]|[hstuck vargs]] => //.
        now eapply eval_to_value in He2. }
      solve_all.
      eapply nth_error_all in X3; eauto. simpl in X3.
      destruct X3 as [cl val]. eapply X1, value_whnf; auto.
      eapply nth_error_None in hnth; len in hnth; simpl in *. lia. }      
    redt _; eauto.

  - apply inversion_App in Ht; auto; destruct_sigma Ht.
    specialize (IHHe1 _ t).
    specialize (IHHe2 _ t0).
    now eapply red_app.

  - epose proof (subject_reduction Σ [] _ _ _ wfΣ Ht).
    apply inversion_Case in Ht; auto; destruct_sigma Ht.
    pose proof (subject_closed wfΣ t0) as H.
    rewrite closedn_mkApps in H. move/andP: H => [clcofix clargs].
    assert (red Σ [] (tCase ip p (mkApps (tCoFix mfix idx) args) brs) (tCase ip p (mkApps fn args) brs)).
    { eapply red1_red. eapply red_cofix_case.
      rewrite -closed_unfold_cofix_cunfold_eq in e; eauto. }
    specialize (X X0).
    specialize (IHHe _ X).
    redt _; eauto.
    
  - epose proof (subject_reduction Σ [] _ _ _ wfΣ Ht).
    apply inversion_Proj in Ht; auto; destruct_sigma Ht.
    pose proof (subject_closed wfΣ t) as H.
    rewrite closedn_mkApps in H. move/andP: H => [clcofix clargs].
    assert (red Σ [] (tProj p (mkApps (tCoFix mfix idx) args)) (tProj p (mkApps fn args))).
    { eapply red1_red. eapply red_cofix_proj.
      rewrite -closed_unfold_cofix_cunfold_eq in e; eauto. }
    specialize (X X0).
    specialize (IHHe _ X).
    redt _; eauto.

  - eapply inversion_App in Ht as (? & ? & ? & Hf & Ha & Ht); auto.
    specialize (IHHe1 _ Hf).
    specialize (IHHe2 _ Ha).
    now eapply red_app.
  Qed.

  Lemma eval_ind_canonical t i u args : 
    axiom_free Σ ->
    Σ ;;; [] |- t : mkApps (tInd i u) args -> 
    forall t', eval Σ t t' ->
    construct_cofix_discr (head t').
  Proof.
    intros axfree Ht t' eval.
    pose proof (subject_closed wfΣ Ht).
    eapply subject_reduction in Ht. 3:eapply wcbeval_red; eauto. 2:auto.
    eapply eval_whne in eval; auto.
    eapply wh_normal_ind_discr; eauto.
  Qed.

  End reducible.
End WeakNormalization.
