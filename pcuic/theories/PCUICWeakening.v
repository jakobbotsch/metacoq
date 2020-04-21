(* Distributed under the terms of the MIT license.   *)
From Coq Require Import Bool List ZArith Lia.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
  PCUICLiftSubst PCUICUnivSubst PCUICEquality PCUICTyping PCUICWeakeningEnv
  PCUICClosed PCUICReduction PCUICPosition.
Require Import ssreflect.

From Equations Require Import Equations.

Set Default Goal Selector "!".

(** * Weakening lemmas for typing derivations.

  [weakening_*] proves weakening of typing, reduction etc... w.r.t. the *local* environment. *)

Set Asymmetric Patterns.
Generalizable Variables Σ Γ t T.

Derive Signature NoConfusion for All_local_env.
Derive Signature for All_local_env_over.

(* FIXME inefficiency in equations: using a very slow "pattern_sigma" to simplify an equality between sigma types *)
Ltac Equations.CoreTactics.destruct_tele_eq H ::= noconf H.

(* Derive Signature NoConfusion for All_local_env. *)
Derive NoConfusion for All_local_env_over.
Derive NoConfusion for context_decl.

Lemma typed_liftn `{checker_flags} Σ Γ t T n k :
  wf Σ.1 -> wf_local Σ Γ -> k >= #|Γ| ->
  Σ ;;; Γ |- t : T -> lift n k T = T /\ lift n k t = t.
Proof.
  intros wfΣ wfΓ Hk Hty.
  apply typecheck_closed in Hty; eauto.
  destruct Hty as [_ Hcl].
  rewrite -> andb_and in Hcl. destruct Hcl as [clb clty].
  pose proof (closed_upwards k clb).
  pose proof (closed_upwards k clty).
  simpl in *. forward H0 by lia.
  apply (lift_closed n) in H0.
  simpl in *. forward H1 by lia.
  now apply (lift_closed n) in H1.
Qed.

Lemma weaken_nth_error_ge {Γ Γ' v Γ''} : #|Γ'| <= v ->
  nth_error (Γ ,,, Γ') v =
  nth_error (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') (#|Γ''| + v).
Proof.
  intros Hv.
  rewrite -> !nth_error_app_context_ge, ?lift_context_length.
  - f_equal. lia.
  - rewrite lift_context_length. lia.
  - rewrite lift_context_length. lia.
  - auto.
Qed.

Lemma weaken_nth_error_lt {Γ Γ' Γ'' v} : v < #|Γ'| ->
  nth_error (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') v =
  option_map (lift_decl #|Γ''| (#|Γ'| - S v)) (nth_error (Γ ,,, Γ') v).
Proof.
  simpl. intros Hv.
  rewrite -> !nth_error_app_context_lt.
  - rewrite nth_error_lift_context_eq.
    do 2 f_equal. lia.
  - lia.
  - now rewrite lift_context_length.
Qed.

Lemma lift_context_lift_context n k Γ : lift_context n 0 (lift_context k 0 Γ) =
  lift_context (n + k) 0 Γ.
Proof. rewrite !lift_context_alt.
  rewrite mapi_compose.
  apply mapi_ext.
  intros n' x.
  rewrite /lift_decl compose_map_decl.
  apply map_decl_ext => y.
  rewrite mapi_length; autorewrite with  len.
  rewrite simpl_lift //; lia.
Qed.

Lemma lift_simpl {Γ'' Γ' : context} {i t} :
  i < #|Γ'| ->
  lift0 (S i) (lift #|Γ''| (#|Γ'| - S i) t) = lift #|Γ''| #|Γ'| (lift0 (S i) t).
Proof.
  intros. assert (#|Γ'| = S i + (#|Γ'| - S i)) by easy.
  rewrite -> H0 at 2.
  rewrite permute_lift; try easy.
Qed.

Lemma lift_iota_red n k pars c args brs :
  lift n k (iota_red pars c args brs) =
  iota_red pars c (List.map (lift n k) args) (List.map (on_snd (lift n k)) brs).
Proof.
  unfold iota_red. rewrite !lift_mkApps. f_equal; auto using map_skipn.
  rewrite nth_map; simpl; auto.
Qed.

Lemma parsubst_empty k a : subst [] k a = a.
Proof.
  induction a in k |- * using term_forall_list_ind; simpl; try congruence;
    try solve [f_equal; eauto; solve_all; eauto].

  - elim (Nat.compare_spec k n); destruct (Nat.leb_spec k n); intros; try easy.
    + subst. rewrite Nat.sub_diag. simpl. rewrite Nat.sub_0_r. reflexivity.
    + assert (n - k > 0) by lia.
      assert (exists n', n - k = S n').
      * exists (Nat.pred (n - k)). lia.
      * destruct H2. rewrite H2. simpl. now rewrite Nat.sub_0_r.
Qed.

Lemma lift_unfold_fix n k mfix idx narg fn :
  unfold_fix mfix idx = Some (narg, fn) ->
  unfold_fix (map (map_def (lift n k) (lift n (#|mfix| + k))) mfix) idx = Some (narg, lift n k fn).
Proof.
  unfold unfold_fix.
  rewrite nth_error_map. destruct (nth_error mfix idx) eqn:Hdef; try congruence.
  case e: isLambda => //.
  intros [= <- <-]. simpl.
  rewrite isLambda_lift e.
  repeat f_equal.
  rewrite (distr_lift_subst_rec _ _ n 0 k).
  rewrite fix_subst_length. f_equal.
  unfold fix_subst. rewrite !map_length.
  generalize #|mfix| at 2 3. induction n0; auto. simpl.
  f_equal. apply IHn0.
Qed.
Hint Resolve lift_unfold_fix : pcuic.

Lemma lift_unfold_cofix n k mfix idx narg fn :
  unfold_cofix mfix idx = Some (narg, fn) ->
  unfold_cofix (map (map_def (lift n k) (lift n (#|mfix| + k))) mfix) idx = Some (narg, lift n k fn).
Proof.
  unfold unfold_cofix.
  rewrite nth_error_map. destruct (nth_error mfix idx) eqn:Hdef; try congruence.
  intros [= <- <-]. simpl. repeat f_equal.
  rewrite (distr_lift_subst_rec _ _ n 0 k).
  rewrite cofix_subst_length. f_equal.
  unfold cofix_subst. rewrite !map_length.
  generalize #|mfix| at 2 3. induction n0; auto. simpl.
  f_equal. apply IHn0.
Qed.
Hint Resolve lift_unfold_cofix : pcuic.

Lemma decompose_app_rec_lift n k t l :
  let (f, a) := decompose_app_rec t l in
  decompose_app_rec (lift n k t) (map (lift n k) l)  = (lift n k f, map (lift n k) a).
Proof.
  induction t in k, l |- *; simpl; auto with pcuic.
  - specialize (IHt1 k (t2 :: l)).
    destruct decompose_app_rec. now rewrite IHt1.
Qed.

Lemma decompose_app_lift n k t f a :
  decompose_app t = (f, a) -> decompose_app (lift n k t) = (lift n k f, map (lift n k) a).
Proof.
  generalize (decompose_app_rec_lift n k t []).
  unfold decompose_app. destruct decompose_app_rec.
  now move=> Heq [= <- <-].
Qed.
Hint Rewrite decompose_app_lift using auto : lift.

Lemma lift_is_constructor:
  forall (args : list term) (narg : nat) n k,
    is_constructor narg args = true -> is_constructor narg (map (lift n k) args) = true.
Proof.
  intros args narg.
  unfold is_constructor; intros.
  rewrite nth_error_map. destruct nth_error; try discriminate. simpl.
  unfold isConstruct_app in *. destruct decompose_app eqn:Heq.
  eapply decompose_app_lift in Heq as ->.
  destruct t0; try discriminate || reflexivity.
Qed.
Hint Resolve lift_is_constructor : core.

Hint Rewrite lift_subst_instance_constr : lift.
Hint Rewrite lift_mkApps : lift.
Hint Rewrite distr_lift_subst distr_lift_subst10 : lift.
Hint Rewrite lift_iota_red : lift.

Lemma lift_declared_constant `{checker_flags} Σ cst decl n k :
  wf Σ ->
  declared_constant Σ cst decl ->
  decl = map_constant_body (lift n k) decl.
Proof.
  unfold declared_constant.
  intros.
  eapply lookup_on_global_env in H0; eauto.
  destruct H0 as [Σ' [wfΣ' decl']].
  red in decl'. red in decl'.
  destruct decl. simpl in *. destruct cst_body.
  - unfold map_constant_body. simpl.
    pose proof decl' as declty.
    apply typecheck_closed in declty; eauto.
    + destruct declty as [declty Hcl].
      rewrite -> andb_and in Hcl. destruct Hcl as [clb clty].
      pose proof (closed_upwards k clb).
      pose proof (closed_upwards k clty).
      simpl in *. forward H0 by lia. forward H1 by lia.
      apply (lift_closed n k) in H0.
      apply (lift_closed n k) in H1. rewrite H0 H1. reflexivity.

  - red in decl'.
    destruct decl'.
    apply subject_closed in t; auto.
    eapply closed_upwards in t; simpl.
    * apply (lift_closed n k) in t. unfold map_constant_body. simpl.
      rewrite t. reflexivity.
    * lia.
Qed.

Definition lift_mutual_inductive_body n k m :=
  map_mutual_inductive_body (fun k' => lift n (k' + k)) m.

Lemma lift_wf_local `{checker_flags} Σ Γ n k :
  wf Σ.1 ->
  wf_local Σ Γ ->
  lift_context n k Γ = Γ.
Proof.
  intros wfΣ.
  induction 1; auto; unfold lift_context, snoc; rewrite fold_context_snoc0; auto; unfold snoc;
    f_equal; auto; unfold map_decl; simpl.
  - destruct t0 as [s Hs]. unfold vass. f_equal.
    eapply typed_liftn; eauto. lia.
  - red in t0. destruct t0. unfold vdef. f_equal.
    + f_equal. eapply typed_liftn; eauto. lia.
    + eapply typed_liftn in t0 as [Ht HT]; eauto. lia.
Qed.

Lemma closed_wf_local `{checker_flags} Σ Γ :
  wf Σ.1 ->
  wf_local Σ Γ ->
  closed_ctx Γ.
Proof.
  intros wfΣ. unfold closed_ctx, mapi. intros wf. generalize 0.
  induction wf; intros n; auto; unfold closed_ctx, snoc; simpl;
    rewrite mapi_rec_app forallb_app; unfold id, closed_decl.
  - simpl.
    destruct t0 as [s Hs].
    eapply typecheck_closed in Hs as [closedΓ tcl]; eauto.
    rewrite -> andb_and in *. simpl in *; rewrite andb_true_r in tcl |- *.
    simpl in *. intuition auto.
    + apply IHwf.
    + erewrite closed_upwards; eauto. rewrite List.rev_length. lia.
  - simpl. eapply typecheck_closed in t1 as [closedΓ tcl]; eauto.
    rewrite -> andb_and in *. intuition auto.
    + apply IHwf.
    + erewrite closed_upwards; eauto.
      * erewrite closed_upwards; eauto.
        rewrite List.rev_length. lia.
      * rewrite List.rev_length. lia.
Qed.

Lemma lift_declared_minductive `{checker_flags} Σ cst decl n k :
  wf Σ ->
  declared_minductive Σ cst decl ->
  lift_mutual_inductive_body n k decl = decl.
Proof.
  intros wfΣ Hdecl. eapply on_declared_minductive in Hdecl; eauto.
  destruct decl. simpl in *. f_equal.
  - apply onParams in Hdecl. simpl in *.
    eapply lift_wf_local; eauto; eauto.
  - apply onInductives in Hdecl.
    revert Hdecl. simpl. generalize ind_bodies at 2 4 5.
    intros.
    eapply (Alli_mapi_id Hdecl).
    clear Hdecl. intros.
    destruct x; simpl in *.
    destruct (decompose_prod_assum [] ind_type) eqn:Heq.
    destruct (decompose_prod_assum [] (lift n k ind_type)) eqn:Heq'.
    destruct X. simpl in *.
    assert (lift n k ind_type = ind_type).
    { repeat red in onArity.
      destruct onArity as [s Hs].
      eapply typed_liftn; eauto; eauto.
      - constructor.
      - simpl. lia.
    }
    rewrite H0 in Heq'. rewrite Heq in Heq'. revert Heq'; intros [= <- <-].
    f_equal; auto.
    + eapply All_map_id. eapply All2_All_left; tea.
      intros [[x p] n'] y [cs [s Hty] Hargs _].
      unfold on_pi2; cbn; f_equal; f_equal.
      simpl in Hty.
      eapply typed_liftn. 4:eapply Hty.
      * eauto.
      * apply typing_wf_local in Hty; eauto.
      * change PCUICEnvironment.arities_context with arities_context. lia.
    + destruct(eq_dec ind_projs []) as [Hp|Hp].
      * subst; auto.
      * specialize (onProjections Hp).
        destruct onProjections as [_ _ _ onProjections].
        apply (Alli_map_id onProjections).
        intros n1 [x p].
        unfold on_projection. simpl.
        intros [s Hty].
        unfold on_snd; f_equal; f_equal.
        eapply typed_liftn. 4:eapply Hty. all:eauto.
        -- eapply typing_wf_local in Hty; eauto.
        -- simpl.
           rewrite smash_context_length. simpl.
           rewrite context_assumptions_fold. lia.
Qed.

Lemma lift_declared_inductive `{checker_flags} Σ ind mdecl idecl n k :
  wf Σ ->
  declared_inductive Σ mdecl ind idecl ->
  map_one_inductive_body (context_assumptions mdecl.(ind_params))
                         (length (arities_context mdecl.(ind_bodies))) (fun k' => lift n (k' + k))
                         (inductive_ind ind) idecl = idecl.
Proof.
  unfold declared_inductive. intros wfΣ [Hmdecl Hidecl].
  eapply (lift_declared_minductive _ _ _ n k) in Hmdecl. 2: auto.
  unfold lift_mutual_inductive_body in Hmdecl.
  destruct mdecl. simpl in *.
  injection Hmdecl. intros Heq.
  clear Hmdecl.
  pose proof Hidecl as Hidecl'.
  rewrite <- Heq in Hidecl'.
  rewrite nth_error_mapi in Hidecl'.
  clear Heq.
  unfold option_map in Hidecl'. rewrite Hidecl in Hidecl'.
  congruence.
Qed.

Lemma subst0_inds_lift ind u mdecl n k t :
  (subst0 (inds (inductive_mind ind) u (ind_bodies mdecl))
          (lift n (#|arities_context (ind_bodies mdecl)| + k) t)) =
  lift n k (subst0 (inds (inductive_mind ind) u (ind_bodies mdecl)) t).
Proof.
  rewrite (distr_lift_subst_rec _ _ n 0 k). simpl.
  unfold arities_context. rewrite rev_map_length inds_length.
  f_equal. generalize (ind_bodies mdecl).
  clear. intros.
  induction l; unfold inds; simpl; auto. f_equal. auto.
Qed.

Lemma lift_declared_constructor `{checker_flags} Σ c u mdecl idecl cdecl n k :
  wf Σ ->
  declared_constructor Σ mdecl idecl c cdecl ->
  lift n k (type_of_constructor mdecl cdecl c u) = (type_of_constructor mdecl cdecl c u).
Proof.
  unfold declared_constructor. destruct c as [i ci]. intros wfΣ [Hidecl Hcdecl].
  eapply (lift_declared_inductive _ _ _ _ n k) in Hidecl; eauto.
  unfold type_of_constructor. destruct cdecl as [[id t'] arity].
  destruct idecl; simpl in *.
  injection Hidecl.
  intros.
  pose Hcdecl as Hcdecl'.
  rewrite <- H1 in Hcdecl'.
  rewrite nth_error_map in Hcdecl'. rewrite Hcdecl in Hcdecl'.
  simpl in Hcdecl'. injection Hcdecl'.
  intros.
  rewrite <- H3 at 2.
  rewrite <- lift_subst_instance_constr.
  now rewrite subst0_inds_lift.
Qed.

Lemma lift_declared_projection `{checker_flags} Σ c mdecl idecl pdecl n k :
  wf Σ ->
  declared_projection Σ mdecl idecl c pdecl ->
  on_snd (lift n (S (ind_npars mdecl + k))) pdecl = pdecl.
Proof.
  intros.
  destruct H0 as [[Hmdecl Hidecl] [Hpdecl Hnpar]].
  eapply declared_decl_closed in Hmdecl; auto.
  simpl in Hmdecl.
  pose proof (onNpars _ _ _ _ Hmdecl).
  apply onInductives in Hmdecl.
  eapply nth_error_alli in Hmdecl; eauto.
  pose proof (onProjections Hmdecl) as onp; eauto. forward onp.
  1: now eapply nth_error_Some_non_nil in Hpdecl.
  eapply on_projs, nth_error_alli in onp; eauto.
  move: onp => /= /andb_and[Hd _]. simpl in Hd.
  rewrite smash_context_length in Hd. simpl in *.
  change PCUICEnvironment.context_assumptions with context_assumptions in H0.
  rewrite H0 in Hd.
  destruct pdecl as [id ty]. unfold on_snd; simpl in *.
  f_equal. eapply lift_closed.
  eapply closed_upwards; eauto. lia.
Qed.

Lemma lift_fix_context:
  forall (mfix : list (def term)) (n k : nat),
    fix_context (map (map_def (lift n k) (lift n (#|mfix| + k))) mfix) = lift_context n k (fix_context mfix).
Proof.
  intros mfix n k. unfold fix_context.
  rewrite map_vass_map_def rev_mapi.
  fold (fix_context mfix).
  rewrite (lift_context_alt n k (fix_context mfix)).
  unfold lift_decl. now rewrite mapi_length fix_context_length.
Qed.

Hint Rewrite <- lift_fix_context : lift.

Lemma All_local_env_lift `{checker_flags}
      (P Q : context -> term -> option term -> Type) c n k :
  All_local_env Q c ->
  (forall Γ t T,
      Q Γ t T ->
      P (lift_context n k Γ) (lift n (#|Γ| + k) t)
        (option_map (lift n (#|Γ| + k)) T)
  ) ->
  All_local_env P (lift_context n k c).
Proof.
  intros Hq Hf.
  induction Hq in |- *; try econstructor; eauto;
    simpl; rewrite lift_context_snoc; econstructor; eauto.
  - simpl. eapply (Hf _ _ None). eauto.
  - simpl. eapply (Hf _ _ None). eauto.
  - simpl. eapply (Hf _ _ (Some t)). eauto.
Qed.

Lemma lift_destArity ctx t n k :
  destArity (lift_context n k ctx) (lift n (#|ctx| + k) t) =
        match destArity ctx t with
        | Some (args, s) => Some (lift_context n k args, s)
        | None => None
        end.
Proof.
  revert ctx.
  induction t in n, k |- * using term_forall_list_ind; intros ctx; simpl; trivial.
  - move: (IHt2 n k (ctx,, vass n0 t1)).
    now rewrite lift_context_snoc /= /lift_decl /map_decl /vass /= => ->.
  - move: (IHt3 n k (ctx,, vdef n0 t1 t2)).
    now rewrite lift_context_snoc /= /lift_decl /map_decl /vass /= => ->.
Qed.

(* Lemma lift_strip_outer_cast n k t : lift n k (strip_outer_cast t) = strip_outer_cast (lift n k t). *)
(* Proof. *)
(*   induction t; simpl; try reflexivity. *)
(*   destruct Nat.leb; reflexivity. *)
(*   now rewrite IHt1. *)
(* Qed. *)

Definition on_pair {A B C D} (f : A -> B) (g : C -> D) (x : A * C) :=
  (f (fst x), g (snd x)).

Lemma lift_instantiate_params_subst n k params args s t :
  instantiate_params_subst (mapi_rec (fun k' decl => lift_decl n (k' + k) decl) params #|s|)
                           (map (lift n k) args) (map (lift n k) s) (lift n (#|s| + k) t) =
  option_map (on_pair (map (lift n k)) (lift n (#|s| + k + #|params|))) (instantiate_params_subst params args s t).
Proof.
  induction params in args, t, n, k, s |- *.
  - destruct args; simpl; rewrite ?Nat.add_0_r; reflexivity.
  - simpl. simpl. (* rewrite <- lift_strip_outer_cast. generalize (strip_outer_cast t). *)
    (* clear t; intros t. *)
    destruct a as [na [body|] ty]; simpl; try congruence.
    + destruct t; simpl; try congruence.
      specialize (IHparams n k args (subst0 s body :: s) t3).
      rewrite <- Nat.add_succ_r. simpl in IHparams.
      rewrite Nat.add_succ_r.
      replace (#|s| + k + S #|params|) with (S (#|s| + k + #|params|)) by lia.
      rewrite <- IHparams.
      rewrite distr_lift_subst. reflexivity.
    + destruct t; simpl; try congruence.
      destruct args; simpl; try congruence.
      specialize (IHparams n k args (t :: s) t2). simpl in IHparams.
      replace (#|s| + k + S #|params|) with (S (#|s| + k + #|params|)) by lia.
      rewrite <- IHparams. auto.
Qed.

Lemma instantiate_params_subst_length params args s t ctx t' :
  instantiate_params_subst params args s t = Some (ctx, t') ->
  #|ctx| = #|s| + #|params|.
Proof.
  induction params in args, s, t, ctx, t' |- * ;
  destruct args; simpl; auto; try congruence.
  - rewrite Nat.add_0_r. congruence.
  - destruct decl_body.
    + simpl.
      destruct t; simpl; try congruence.
      intros. erewrite IHparams; eauto. simpl. lia.
    + destruct t; simpl; try congruence.
  - destruct decl_body.
    + simpl.
      destruct t; simpl; try congruence.
      intros. erewrite IHparams; eauto. simpl. lia.
    + destruct t; simpl; try congruence.
      intros. erewrite IHparams; eauto. simpl. lia.
Qed.

Lemma closed_ctx_lift n k ctx : closed_ctx ctx -> lift_context n k ctx = ctx.
Proof.
  induction ctx in n, k |- *; auto.
  unfold closed_ctx, id. simpl.
  rewrite mapi_app forallb_app List.rev_length /= lift_context_snoc0 /snoc Nat.add_0_r.
  move/andb_and => /= [Hctx /andb_and [Ha _]].
  rewrite IHctx // lift_decl_closed //. now apply: closed_decl_upwards.
Qed.

Lemma closed_tele_lift n k ctx :
  closed_ctx ctx ->
  mapi (fun (k' : nat) (decl : context_decl) => lift_decl n (k' + k) decl) (List.rev ctx) = List.rev ctx.
Proof.
  rewrite /closedn_ctx /mapi. simpl. generalize 0.
  induction ctx using rev_ind.
  1: move=> //.
  move=> n0.
  rewrite /closedn_ctx !rev_app_distr /id /=.
  move/andP => [closedx Hctx].
  rewrite lift_decl_closed.
  - rewrite (@closed_decl_upwards n0) //; try lia.
  - f_equal. now rewrite IHctx.
Qed.

Lemma lift_instantiate_params n k params args t :
  closed_ctx params ->
  option_map (lift n k) (instantiate_params params args t) =
  instantiate_params params (map (lift n k) args) (lift n k t).
Proof.
  unfold instantiate_params.
  move/(closed_tele_lift n k params)=> Heq.
  rewrite -{2}Heq.
  specialize (lift_instantiate_params_subst n k (List.rev params) args [] t).
  move=> /= Heq'; rewrite Heq'.
  case E: (instantiate_params_subst (List.rev params) args)=> [[l' t']|] /= //.
  rewrite distr_lift_subst.
  move/instantiate_params_subst_length: E => -> /=.  do 3 f_equal. lia.
Qed.
Hint Rewrite lift_instantiate_params : lift.

(* bug eauto with let .. in hypothesis failing *)
Lemma lift_decompose_prod_assum_rec ctx t n k :
  let (ctx', t') := decompose_prod_assum ctx t in
  (lift_context n k ctx', lift n (length ctx' + k) t') =
  decompose_prod_assum (lift_context n k ctx) (lift n (length ctx + k) t).
Proof.
  induction t in n, k, ctx |- *; simpl;
    try rewrite -> Nat.sub_diag, Nat.add_0_r; try (eauto; congruence).
  - specialize (IHt2 (ctx ,, vass na t1) n k).
    destruct decompose_prod_assum. rewrite IHt2. simpl.
    rewrite lift_context_snoc. reflexivity.
  - specialize (IHt3 (ctx ,, vdef na t1 t2) n k).
    destruct decompose_prod_assum. rewrite IHt3. simpl.
    rewrite lift_context_snoc. reflexivity.
Qed.

Lemma lift_decompose_prod_assum t n k :
  let (ctx', t') := decompose_prod_assum [] t in
  (lift_context n k ctx', lift n (length ctx' + k) t') =
  decompose_prod_assum [] (lift n k t).
Proof. apply lift_decompose_prod_assum_rec. Qed.

Lemma lift_it_mkProd_or_LetIn n k ctx t :
  lift n k (it_mkProd_or_LetIn ctx t) =
  it_mkProd_or_LetIn (lift_context n k ctx) (lift n (length ctx + k) t).
Proof.
  induction ctx in n, k, t |- *; simpl; try congruence.
  pose (lift_context_snoc n k ctx a). unfold snoc in e. rewrite -> e. clear e.
  simpl. rewrite -> IHctx.
  pose (lift_context_snoc n k ctx a).
  now destruct a as [na [b|] ty].
Qed.
Hint Rewrite lift_it_mkProd_or_LetIn : lift.

Lemma to_extended_list_lift n k c :
  to_extended_list (lift_context n k c) = to_extended_list c.
Proof.
  unfold to_extended_list, to_extended_list_k. generalize 0.
  unf_term. generalize (nil term) at 1 2.
  induction c in n, k |- *; simpl; intros. 1: reflexivity.
  rewrite -> lift_context_snoc0. unfold snoc. simpl.
  destruct a. destruct decl_body.
  - unfold lift_decl, map_decl. simpl.
    now rewrite -> IHc.
  - simpl. apply IHc.
Qed.

Lemma to_extended_list_map_lift:
  forall (n k : nat) (c : context), to_extended_list c = map (lift n (#|c| + k)) (to_extended_list c).
Proof.
  intros n k c.
  pose proof (to_extended_list_lift_above c). unf_term.
  symmetry. solve_all.
  destruct H as [x' [-> Hx]]. simpl.
  destruct (leb_spec_Set (#|c| + k) x').
  - f_equal. lia.
  - reflexivity.
Qed.

Lemma weakening_red1 `{CF:checker_flags} Σ Γ Γ' Γ'' M N :
  wf Σ ->
  red1 Σ (Γ ,,, Γ') M N ->
  red1 Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') (lift #|Γ''| #|Γ'| M) (lift #|Γ''| #|Γ'| N).
Proof.
  intros wfΣ H.
  remember (Γ ,,, Γ') as Γ0. revert Γ Γ' Γ'' HeqΓ0.
  induction H using red1_ind_all in |- *; intros Γ0 Γ' Γ'' HeqΓ0; try subst Γ; simpl;
    autorewrite with lift;
    try solve [  econstructor; eauto with pcuic ].

  - elim (leb_spec_Set); intros Hn.
    + rewrite -> simpl_lift; try lia. rewrite -> Nat.add_succ_r.
      econstructor; eauto.
      erewrite (weaken_nth_error_ge Hn) in H. eauto.

    + rewrite <- lift_simpl by easy.
      econstructor.
      rewrite -> (weaken_nth_error_lt Hn).
      now unfold lift_decl; rewrite -> option_map_decl_body_map_decl, H.

  - econstructor; eauto with pcuic.
    rewrite H0. f_equal.
    eapply (lookup_on_global_env _ _ _ _ wfΣ) in H.
    destruct H as [Σ' [wfΣ' decl']].
    red in decl'. red in decl'.
    rewrite -> H0 in decl'.
    apply typecheck_closed in decl'; eauto.
    destruct decl'.
    rewrite -> andb_and in i. destruct i as [Hclosed _].
    simpl in Hclosed.
    pose proof (closed_upwards #|Γ'| Hclosed).
    forward H by lia.
    apply (lift_closed #|Γ''| #|Γ'|) in H. auto.

  - simpl. constructor.
    now rewrite -> nth_error_map, H.

  - constructor.
    specialize (IHred1 Γ0 (Γ' ,, vass na N) Γ'' eq_refl).
    rewrite -> lift_context_snoc, Nat.add_0_r in IHred1. apply IHred1.

  - constructor.
    specialize (IHred1 Γ0 (Γ' ,, vdef na b t) Γ'' eq_refl).
    rewrite -> lift_context_snoc, Nat.add_0_r in IHred1. apply IHred1.

  - constructor.
    induction X; constructor; auto.
    intuition; eauto.

  - constructor.
    specialize (IHred1 Γ0 (Γ' ,, vass na M1) Γ'' eq_refl).
    rewrite -> lift_context_snoc, Nat.add_0_r in IHred1. apply IHred1.

  - constructor.
    induction X; constructor; auto.
    intuition; eauto.

  - constructor.
    rewrite -> (OnOne2_length X). generalize (#|mfix1|).
    induction X; simpl; constructor; simpl; intuition eauto.
    congruence.

  - apply fix_red_body. rewrite !lift_fix_context.
    rewrite <- (OnOne2_length X).
    eapply OnOne2_map.
    unfold on_Trel; solve_all; cbn. 2: congruence.
    specialize (b0 Γ0 (Γ' ,,, fix_context mfix0)).
    rewrite app_context_assoc in b0. specialize (b0 Γ'' eq_refl).
    rewrite -> app_context_length, fix_context_length in *.
    rewrite -> lift_context_app in *.
    rewrite -> app_context_assoc, Nat.add_0_r in *.
    auto.

  - constructor.
    rewrite -> (OnOne2_length X). generalize (#|mfix1|).
    induction X; simpl; constructor; intuition eauto; cbn.
    congruence.

  - apply cofix_red_body. rewrite !lift_fix_context.
    rewrite <- (OnOne2_length X).
    eapply OnOne2_map. unfold on_Trel; solve_all; cbn. 2: congruence.
    specialize (b0 Γ0 (Γ' ,,, fix_context mfix0)).
    rewrite app_context_assoc in b0. specialize (b0 Γ'' eq_refl).
    rewrite -> app_context_length, fix_context_length in *.
    rewrite -> lift_context_app in *.
    rewrite -> app_context_assoc, Nat.add_0_r in *.
    auto.
Qed.

Lemma weakening_red `{CF:checker_flags} Σ Γ Γ' Γ'' M N :
  wf Σ ->
  red Σ (Γ ,,, Γ') M N ->
  red Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') (lift #|Γ''| #|Γ'| M) (lift #|Γ''| #|Γ'| N).
Proof.
  intros wfΣ; induction 1.
  - constructor.
  - eapply red_trans with (lift #|Γ''| #|Γ'| P); eauto.
    simpl; eapply red1_red. eapply weakening_red1; auto.
Qed.

Fixpoint lift_stack n k π :=
  match π with
  | ε => ε
  | App u π =>
      let k' := #|stack_context π| + k in
      App (lift n k' u) (lift_stack n k π)
  | Fix mfix idx args π =>
      let k' := #|stack_context π| + k in
      let k'' := #|mfix| + k' in
      let mfix' := List.map (map_def (lift n k') (lift n k'')) mfix in
      Fix mfix' idx (map (lift n k') args) (lift_stack n k π)
  | Fix_mfix_ty na bo ra mfix1 mfix2 idx π =>
      let k' := #|stack_context π| + k in
      let k'' := #|mfix1| + S #|mfix2| + k' in
      let mfix1' := List.map (map_def (lift n k') (lift n k'')) mfix1 in
      let mfix2' := List.map (map_def (lift n k') (lift n k'')) mfix2 in
      Fix_mfix_ty na (lift n k'' bo) ra mfix1' mfix2' idx (lift_stack n k π)
  | Fix_mfix_bd na ty ra mfix1 mfix2 idx π =>
      let k' := #|stack_context π| + k in
      let k'' := #|mfix1| + S #|mfix2| + k' in
      let mfix1' := List.map (map_def (lift n k') (lift n k'')) mfix1 in
      let mfix2' := List.map (map_def (lift n k') (lift n k'')) mfix2 in
      Fix_mfix_bd na (lift n k' ty) ra mfix1' mfix2' idx (lift_stack n k π)
  | CoFix mfix idx args π =>
      let k' := #|stack_context π| + k in
      let k'' := #|mfix| + k' in
      let mfix' := List.map (map_def (lift n k') (lift n k'')) mfix in
      CoFix mfix' idx (map (lift n k') args) (lift_stack n k π)
  | Case_p indn c brs π =>
      let k' := #|stack_context π| + k in
      let brs' := List.map (on_snd (lift n k')) brs in
      Case_p indn (lift n k' c) brs' (lift_stack n k π)
  | Case indn pred brs π =>
      let k' := #|stack_context π| + k in
      let brs' := List.map (on_snd (lift n k')) brs in
      Case indn (lift n k' pred) brs' (lift_stack n k π)
  | Case_brs indn pred c m brs1 brs2 π =>
      let k' := #|stack_context π| + k in
      let brs1' := List.map (on_snd (lift n k')) brs1 in
      let brs2' := List.map (on_snd (lift n k')) brs2 in
      Case_brs indn (lift n k' pred) (lift n k' c) m brs1' brs2' (lift_stack n k π)
  | Proj p π =>
      Proj p (lift_stack n k π)
  | Prod_l na B π =>
      let k' := #|stack_context π| + k in
      Prod_l na (lift n (S k') B) (lift_stack n k π)
  | Prod_r na A π =>
      let k' := #|stack_context π| + k in
      Prod_r na (lift n k' A) (lift_stack n k π)
  | Lambda_ty na b π =>
      let k' := #|stack_context π| + k in
      Lambda_ty na (lift n (S k') b) (lift_stack n k π)
  | Lambda_tm na A π =>
      let k' := #|stack_context π| + k in
      Lambda_tm na (lift n k' A) (lift_stack n k π)
  | LetIn_bd na B u π =>
      let k' := #|stack_context π| + k in
      LetIn_bd na (lift n k' B) (lift n (S k') u) (lift_stack n k π)
  | LetIn_ty na b u π =>
      let k' := #|stack_context π| + k in
      LetIn_ty na (lift n k' b) (lift n (S k') u) (lift_stack n k π)
  | LetIn_in na b B π =>
      let k' := #|stack_context π| + k in
      LetIn_in na (lift n k' b) (lift n k' B) (lift_stack n k π)
  | coApp u π =>
      let k' := #|stack_context π| + k in
      coApp (lift n k' u) (lift_stack n k π)
  end.

(* TODO MOVE *)
Lemma fix_context_alt_length :
  forall l,
    #|fix_context_alt l| = #|l|.
Proof.
  intro l.
  unfold fix_context_alt.
  rewrite List.rev_length.
  rewrite mapi_length. reflexivity.
Qed.

Lemma lift_zipc :
  forall n k t π,
    let k' := #|stack_context π| + k in
    lift n k (zipc t π) =
    zipc (lift n k' t) (lift_stack n k π).
Proof.
  intros n k t π k'.
  induction π in n, k, t, k' |- *.
  all: try reflexivity.
  all: try solve [
    simpl ; rewrite IHπ ; cbn ; reflexivity
  ].
  - simpl. rewrite IHπ. cbn. f_equal.
    rewrite lift_mkApps. cbn. reflexivity.
  - simpl. rewrite IHπ. cbn. f_equal. f_equal.
    rewrite map_app. rewrite !app_length. cbn. reflexivity.
  - simpl. rewrite IHπ. cbn. f_equal. f_equal.
    rewrite map_app. rewrite !app_length. cbn. f_equal.
    unfold map_def at 1. cbn. f_equal.
    rewrite fix_context_alt_length.
    rewrite !app_length. cbn. rewrite !map_length.
    f_equal. f_equal. lia.
  - simpl. rewrite IHπ. cbn. f_equal. f_equal.
    rewrite lift_mkApps. cbn. reflexivity.
  - simpl. rewrite IHπ. cbn. f_equal. f_equal.
    rewrite map_app. cbn. reflexivity.
Qed.

Lemma weakening_eta1 u v n k :
  eta1 u v -> eta1 (lift n k u) (lift n k v).
Proof.
  induction 1 in k |- * using eta1_ind_all; cbn;
    try (constructor; auto; fail).
  - refine (transport (fun x => eta1 x _) _ (eta_red _ _ _)). do 2 f_equal.
    rewrite permute_lift; [lia|].
    now rewrite Nat.add_comm.
  - constructor. eapply OnOne2_map. eapply OnOne2_impl; tea.
    intros [? ?] [? ?] [[? ?] ?]; cbn in *; split; auto.
  - constructor. eapply OnOne2_map. eapply OnOne2_impl; tea.
    intros ? ? [? ?]; cbn in *; auto.
  - constructor. replace #|mfix1| with #|mfix0|;
      [|eapply OnOne2_length; eassumption].
    eapply OnOne2_map. eapply OnOne2_impl; tea.
    intros ? ? [[? ?] ?]; cbn in *; split; auto.
    inversion e1; congruence.
  - apply fix_eta_body.
    replace #|mfix1| with #|mfix0|;
      [|eapply OnOne2_length; eassumption].
    eapply OnOne2_map. eapply OnOne2_impl; tea.
    intros ? ? [[? ?] ?]; cbn in *; split; auto.
    inversion e1; congruence.
  - constructor. replace #|mfix1| with #|mfix0|;
      [|eapply OnOne2_length; eassumption].
    eapply OnOne2_map. eapply OnOne2_impl; tea.
    intros ? ? [[? ?] ?]; cbn in *; split; auto.
    inversion e1; congruence.
  - apply cofix_eta_body.
    replace #|mfix1| with #|mfix0|;
      [|eapply OnOne2_length; eassumption].
    eapply OnOne2_map. eapply OnOne2_impl; tea.
    intros ? ? [[? ?] ?]; cbn in *; split; auto.
    inversion e1; congruence.
Defined.

Lemma weakening_eta u v n k :
  eta u v -> eta (lift n k u) (lift n k v).
Proof.
  induction 1; [constructor 1|econstructor 2|econstructor 3];
    eauto using weakening_eta1.
Defined.


Lemma weakening_upto_domain u v :
  upto_domain u v -> forall n k, upto_domain (lift n k u) (lift n k v).
Proof.
  induction u in v |- * using term_forall_list_ind;
    intro e; invs e; cbn; constructor; eauto.
  1-2: solve_all.
  - rewrite (All2_length _ _ X0). solve_all.
  - rewrite (All2_length _ _ X0). solve_all.
Qed.

Lemma weakening_cumul `{CF:checker_flags} Σ Γ Γ' Γ'' M N :
  wf Σ.1 ->
  Σ ;;; Γ ,,, Γ' |- M <= N ->
  Σ ;;; Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ' |- lift #|Γ''| #|Γ'| M <= lift #|Γ''| #|Γ'| N.
Proof.
  intros wfΣ. induction 1.
  - econstructor.
    + apply lift_leq_term; eassumption.
    + eapply weakening_upto_domain; eassumption.
  - eapply weakening_red1 in r; auto.
    econstructor 2; eauto.
  - eapply weakening_red1 in r; auto.
    econstructor 3; eauto.
  - eapply cumul_eta_l. 2: eauto.
    eapply weakening_eta1. assumption.
  - eapply cumul_eta_r. 1: eauto.
    eapply weakening_eta1. assumption.
Qed.

Lemma destArity_it_mkProd_or_LetIn ctx ctx' t :
  destArity ctx (it_mkProd_or_LetIn ctx' t) =
  destArity (ctx ,,, ctx') t.
Proof.
  induction ctx' in ctx, t |- *; simpl; auto.
  rewrite IHctx'. destruct a as [na [b|] ty]; reflexivity.
Qed.

Lemma lift_build_case_predicate_type ind mdecl idecl u params ps n k :
  closed_ctx (subst_instance_context u (ind_params mdecl)) ->
  build_case_predicate_type ind mdecl
    (map_one_inductive_body (context_assumptions mdecl.(ind_params))
            (length (arities_context (ind_bodies mdecl))) (fun k' => lift n (k' + k))
            (inductive_ind ind) idecl)
    (map (lift n k) params) u ps
  = option_map (lift n k) (build_case_predicate_type ind mdecl idecl params u ps).
Proof.
  intros closedpars. unfold build_case_predicate_type.
  rewrite -> ind_type_map. simpl.
  epose proof (lift_instantiate_params n k _ params (subst_instance_constr u (ind_type idecl))) as H.
  rewrite <- lift_subst_instance_constr.
  erewrite <- H; trivial. clear H.
  case_eq (instantiate_params (subst_instance_context u (ind_params mdecl)) params (subst_instance_constr u (ind_type idecl))) ; cbnr.
  intros ity eq.
  pose proof (lift_destArity [] ity n k) as H; cbn in H. rewrite H; clear H.
  destruct destArity as [[ctx s] | ]; [|reflexivity]. simpl. f_equal.
  rewrite lift_it_mkProd_or_LetIn; cbn. unf_term. f_equal. f_equal.
  - destruct idecl; reflexivity.
  - rewrite lift_mkApps; cbn; f_equal. rewrite map_app. f_equal.
    + rewrite !map_map lift_context_length; apply map_ext. clear.
      intro. now rewrite -> permute_lift by lia.
    + now rewrite -> to_extended_list_lift, <- to_extended_list_map_lift.
Qed.

Lemma lift_build_branches_type ind mdecl idecl u p params n k :
  closed_ctx (subst_instance_context u (ind_params mdecl)) ->
  build_branches_type ind mdecl
         (map_one_inductive_body (context_assumptions mdecl.(ind_params))
            #|arities_context (ind_bodies mdecl)| (fun k' => lift n (k' + k))
            (inductive_ind ind) idecl)
         (map (lift n k) params) u (lift n k p)
  = map (option_map (on_snd (lift n k)))
        (build_branches_type ind mdecl idecl params u p).
Proof.
  intros closedpars. unfold build_branches_type.
  rewrite -> ind_ctors_map.
  rewrite -> mapi_map, map_mapi. eapply mapi_ext. intros i x.
  destruct x as [[id t] arity]. simpl.
  rewrite <- lift_subst_instance_constr.
  rewrite subst0_inds_lift.
  rewrite <- lift_instantiate_params ; trivial.
  match goal with
  | |- context [ option_map _ (instantiate_params ?x ?y ?z) ] =>
    destruct (instantiate_params x y z) eqn:Heqip; cbnr
  end.
  epose proof (lift_decompose_prod_assum t0 n k).
  destruct (decompose_prod_assum [] t0).
  rewrite <- H.
  destruct (decompose_app t1) as [fn arg] eqn:?.
  rewrite (decompose_app_lift _ _ _ fn arg); auto. simpl.
  destruct (chop _ arg) eqn:Heqchop.
  eapply chop_map in Heqchop.
  rewrite -> Heqchop. clear Heqchop.
  unfold on_snd. simpl. f_equal.
  rewrite -> lift_it_mkProd_or_LetIn, !lift_mkApps, map_app; simpl.
  rewrite -> !lift_mkApps, !map_app, lift_context_length.
  rewrite -> permute_lift by lia. arith_congr.
  now rewrite -> to_extended_list_lift, <- to_extended_list_map_lift.
Qed.

Lemma weakening_typing_prop {cf:checker_flags} : env_prop (fun Σ Γ0 t T =>
  forall Γ Γ' Γ'' : context,
  wf_local Σ (Γ ,,, Γ'') ->
  Γ0 = Γ ,,, Γ' ->
  Σ;;; Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ' |- lift #|Γ''| #|Γ'| t : lift #|Γ''| #|Γ'| T)
  (fun Σ Γ0 _  => 
  forall Γ Γ' Γ'' : context,
  Γ0 = Γ ,,, Γ' ->
  wf_local Σ (Γ ,,, Γ'') ->
  wf_local Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ')).
Proof.
  apply typing_ind_env;   
    intros Σ wfΣ Γ0; !!intros; subst Γ0; simpl in *; try solve [econstructor; eauto];
        try specialize (forall_Γ  _ _ _ eq_refl wf).
    
  - induction Γ'; simpl; auto.
    depelim X; unfold snoc in H; noconf H;
    rewrite lift_context_snoc; simpl; constructor.
    + eapply IHΓ'; eauto.
    + red. exists (tu.π1). simpl.
      rewrite Nat.add_0_r. apply t0; auto.
    + eapply IHΓ'; eauto. 
    + red. exists (tu.π1). simpl.
      rewrite Nat.add_0_r. apply t1; auto.
    + simpl. rewrite Nat.add_0_r. apply t0; auto.
  
  - elim (leb_spec_Set); intros Hn.
    + rewrite -> simpl_lift; try lia. rewrite -> Nat.add_succ_r.
      constructor. 1: auto.
      now rewrite <- (weaken_nth_error_ge Hn).
    + assert (forall t, lift0 (S n) (lift #|Γ''| (#|Γ'| - S n) t) = lift #|Γ''| #|Γ'| (lift0 (S n) t)).
      * intros.
        assert (H:#|Γ'| = S n + (#|Γ'| - S n)) by easy.
        rewrite -> H at 2.
        rewrite permute_lift; easy.
      * rewrite <- H.
        rewrite -> map_decl_type. constructor; auto.
        now rewrite -> (weaken_nth_error_lt Hn), heq_nth_error.

  - econstructor; auto.
    specialize (IHb Γ (Γ' ,, vass n t) Γ'' wf eq_refl).
    rewrite -> lift_context_snoc, plus_0_r in IHb.
    eapply IHb.

  - econstructor; auto.
    simpl.
    specialize (IHb Γ (Γ' ,, vass n t) Γ'' wf eq_refl).
    rewrite -> lift_context_snoc, plus_0_r in IHb.
    eapply IHb.

  - econstructor; auto.
    specialize (IHb Γ Γ' Γ'' wf eq_refl). simpl.
    specialize (IHb' Γ (Γ' ,, vdef n b b_ty) Γ'' wf eq_refl).
    rewrite -> lift_context_snoc, plus_0_r in IHb'.
    apply IHb'.

  - eapply refine_type. 1: econstructor; auto.
    now rewrite -> distr_lift_subst10.

  - autorewrite with lift.
    rewrite -> map_cst_type. constructor; auto.
    erewrite <- lift_declared_constant; eauto.

  - autorewrite with lift.
    erewrite <- (ind_type_map (fun k' => lift #|Γ''| (k' + #|Γ'|))).
    pose proof isdecl as isdecl'.
    destruct isdecl. intuition auto.
    eapply lift_declared_inductive in isdecl'. 2: auto.
    rewrite -> isdecl'.
    econstructor; try red; intuition eauto.

  - rewrite (lift_declared_constructor _ (ind, i) u mdecl idecl cdecl _ _ wfΣ isdecl).
    econstructor; eauto.

  - rewrite -> lift_mkApps, map_app, map_skipn.
    specialize (IHc _ _ _ wf eq_refl).
    specialize (IHp _ _ _ wf eq_refl).
    assert (Hclos: closed_ctx (subst_instance_context u (ind_params mdecl))). {
      destruct isdecl as [Hmdecl Hidecl].
      eapply on_declared_minductive in Hmdecl; eauto.
      eapply onParams in Hmdecl.
      rewrite closedn_subst_instance_context.
      eapply closed_wf_local in Hmdecl; eauto. }
    simpl. econstructor.
    7:{ cbn. rewrite -> firstn_map.
        erewrite lift_build_branches_type; tea.
        rewrite map_option_out_map_option_map.
        subst params. erewrite heq_map_option_out. reflexivity. }
    all: eauto.
    -- erewrite -> lift_declared_inductive; eauto.
    -- simpl. erewrite firstn_map, lift_build_case_predicate_type; tea.
       subst params. erewrite heq_build_case_predicate_type; reflexivity.
    -- destruct idecl; simpl in *; auto.
    -- now rewrite -> !lift_mkApps in IHc.
    -- solve_all.

  - simpl.
    erewrite (distr_lift_subst_rec _ _ _ 0 #|Γ'|).
    simpl. rewrite -> map_rev.
    subst ty.
    rewrite -> List.rev_length, lift_subst_instance_constr.
    replace (lift #|Γ''| (S (#|args| + #|Γ'|)) (snd pdecl))
      with (snd (on_snd (lift #|Γ''| (S (#|args| + #|Γ'|))) pdecl)) by now destruct pdecl.
    econstructor.
    + red. split.
      * apply (proj1 isdecl).
      * split.
        -- rewrite -> (proj1 (proj2 isdecl)). f_equal.
           rewrite -> heq_length.
           symmetry. eapply lift_declared_projection; eauto.
        -- apply (proj2 (proj2 isdecl)).
    + specialize (IHc _ _ _ wf eq_refl).
      rewrite -> lift_mkApps in *. eapply IHc.
    + now rewrite -> map_length.

  - rewrite -> (map_dtype _ (lift #|Γ''| (#|mfix| + #|Γ'|))).
    eapply type_Fix; auto.
    * eapply fix_guard_lift ; eauto.
    * rewrite -> nth_error_map, heq_nth_error. reflexivity.
    * eapply All_map.
      eapply (All_impl X0); simpl.
      intros x [s [Hs Hs']]; exists s.
      now specialize (Hs' _ _ _ wf eq_refl).
    * eapply All_map.
      eapply (All_impl X1); simpl.
      intros x [[Hb Hlam] IH].
      rewrite lift_fix_context.
      specialize (IH Γ (Γ' ,,,  (fix_context mfix)) Γ'' wf).
      rewrite app_context_assoc in IH. specialize (IH eq_refl).
      split; auto.
      + rewrite lift_context_app Nat.add_0_r app_context_assoc in IH.
        rewrite app_context_length fix_context_length in IH.
        rewrite lift_context_length fix_context_length.
        rewrite permute_lift; try lia. now rewrite (Nat.add_comm #|Γ'|).
      + now rewrite isLambda_lift.

  - rewrite -> (map_dtype _ (lift #|Γ''| (#|mfix| + #|Γ'|))).
    eapply type_CoFix; auto.
    * rewrite -> nth_error_map, heq_nth_error. reflexivity.
    * eapply All_map.
      eapply (All_impl X0); simpl.
      intros x [s [Hs Hs']]; exists s.
      now specialize (Hs' _ _ _ wf eq_refl).
    * eapply All_map.
      eapply (All_impl X1); simpl.
      intros x [Hb IH].
      rewrite lift_fix_context.
      specialize (IH Γ (Γ' ,,,  (fix_context mfix)) Γ'' wf).
      rewrite app_context_assoc in IH. specialize (IH eq_refl).
      rewrite lift_context_app Nat.add_0_r app_context_assoc in IH.
      rewrite app_context_length fix_context_length in IH.
      rewrite lift_context_length fix_context_length.
      rewrite permute_lift; try lia. now rewrite (Nat.add_comm #|Γ'|).

  - econstructor; eauto; [|now eapply weakening_cumul].
    destruct IHB.
    + left. destruct i as [[ctx [u [Hd IH]]]]. simpl in *.
      exists (lift_context #|Γ''| #|Γ'| ctx), u.
      rewrite (lift_destArity [] B #|Γ''| #|Γ'|) ?Hd.
      split; auto.
      apply All_local_env_app_inv; intuition auto.
      clear -wf a.
      induction ctx; try constructor; depelim a.
      -- rewrite lift_context_snoc.
          inversion H. subst. simpl in H3; noconf H3.
          simpl in H0; noconf H0.
          constructor; auto.
          * eapply IHctx. eapply a.
          * simpl. destruct tu as [u tu]. exists u.
            specialize (t0 Γ (Γ' ,,, ctx) Γ''). forward t0; auto.
            rewrite app_context_assoc in t0.
            specialize (t0 eq_refl). simpl in t0.
            rewrite app_context_length lift_context_app app_context_assoc Nat.add_0_r in t0. apply t0.
      -- rewrite lift_context_snoc.
          inversion H. subst. noconf H3.
          constructor; auto.
          ++ eapply IHctx. eapply a.
          ++ simpl.
            specialize (t1 Γ (Γ' ,,, ctx) Γ''). forward t1 by auto.
            rewrite app_context_assoc in t1.
            specialize (t1 eq_refl). simpl in t1.
            rewrite app_context_length lift_context_app app_context_assoc Nat.add_0_r in t1.
            eexists. apply t1.
          ++ simpl.
            specialize (t0 Γ (Γ' ,,, ctx) Γ'' wf).
            rewrite app_context_assoc in t0.
            specialize (t0 eq_refl). simpl in t0.
            rewrite app_context_length lift_context_app app_context_assoc Nat.add_0_r in t0.
            apply t0.
    + right. destruct s as [u Hu]; exists u. intuition; now eapply weakening_cumul.
Qed.

Lemma weakening_typing `{cf : checker_flags} Σ Γ Γ' Γ'' (t : term) :
  wf Σ.1 ->
  wf_local Σ (Γ ,,, Γ'') ->
  forall T, Σ ;;; Γ ,,, Γ' |- t : T ->
       Σ ;;; Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ' |-
       lift #|Γ''| #|Γ'| t : lift #|Γ''| #|Γ'| T.
Proof.
  intros HΣ HΓ'' T H.
  exact ((weakening_typing_prop Σ HΣ _ t T H).2 _ _ _ HΓ'' eq_refl).
Qed.

Lemma weakening_wf_local `{cf : checker_flags} Σ Γ Γ' Γ'' :
  wf Σ.1 ->
  wf_local Σ (Γ ,,, Γ') ->
  wf_local Σ (Γ ,,, Γ'') ->
  wf_local Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ').
Proof.
  intros HΣ HΓΓ' HΓ''.
  exact (env_prop_wf_local _ _ weakening_typing_prop
                           Σ HΣ _ HΓΓ' _ _ _ eq_refl HΓ'').
Qed.

Lemma weakening `{cf : checker_flags} Σ Γ Γ' (t : term) T :
  wf Σ.1 -> wf_local Σ (Γ ,,, Γ') ->
  Σ ;;; Γ |- t : T ->
  Σ ;;; Γ ,,, Γ' |- lift0 #|Γ'| t : lift0 #|Γ'| T.
Proof.
  intros HΣ HΓΓ' * H.
  pose (weakening_typing Σ Γ [] Γ' t).
  forward t0; eauto.
Qed.

(** Variant with more freedom on the length to apply it in backward-chainings. *)
Lemma weakening_length {cf:checker_flags} Σ Γ Γ' t T n :
  wf Σ.1 ->
  n = #|Γ'| ->
  wf_local Σ (Γ ,,, Γ') ->
  Σ ;;; Γ |- t : T ->
  Σ ;;; Γ ,,, Γ' |- (lift0 n) t : (lift0 n) T.
Proof. intros wfΣ ->; now apply weakening. Qed.

Lemma weakening_conv `{cf:checker_flags} :
  forall Σ Γ Γ' Γ'' M N,
    wf Σ.1 ->
    Σ ;;; Γ ,,, Γ' |- M = N ->
    Σ ;;; Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ' |- lift #|Γ''| #|Γ'| M = lift #|Γ''| #|Γ'| N.
Proof.
  intros Σ Γ Γ' Γ'' M N wfΣ. induction 1.
  - econstructor.
    + apply lift_eq_term; eassumption.
    + now eapply weakening_upto_domain.
  - eapply weakening_red1 in r ; auto.
    econstructor 2 ; eauto.
  - eapply weakening_red1 in r ; auto.
    econstructor 3 ; eauto.
  - eapply conv_eta_l. 2: eassumption.
    eapply weakening_eta1. assumption.
  - eapply conv_eta_r. 1: eassumption.
    eapply weakening_eta1. assumption.
Qed.

Lemma weaken_wf_local {cf:checker_flags} {Σ Γ } Δ : 
  wf Σ.1 -> 
  wf_local Σ Δ ->
  wf_local Σ Γ -> wf_local Σ (Δ ,,, Γ).
Proof.
  intros wfΣ wfΔ wfΓ.
  move: (weakening_wf_local _ [] Γ Δ wfΣ).
  rewrite !app_context_nil_l.
  move/(_ wfΓ wfΔ).
  rewrite closed_ctx_lift //.
  now eapply closed_wf_local.
Qed.

Lemma weaken_ctx {cf:checker_flags} {Σ Γ t T} Δ : 
  wf Σ.1 -> wf_local Σ Δ ->
  Σ ;;; Γ |- t : T ->
  Σ ;;; Δ ,,, Γ |- t : T.
Proof.
  intros wfΣ wfΔ ty.
  epose proof (weakening_typing Σ [] Γ Δ t wfΣ).
  rewrite !app_context_nil_l in X.
  forward X by eauto using typing_wf_local.
  pose proof (typing_wf_local ty).
  pose proof (closed_wf_local _ _ wfΣ (typing_wf_local ty)).
  specialize (X _ ty).
  eapply PCUICClosed.typecheck_closed in ty as [_ closed]; auto.
  move/andP: closed => [ct cT].
  rewrite !lift_closed // in X.
  now rewrite closed_ctx_lift in X.
Qed.

Lemma weakening_gen : forall (cf : checker_flags) (Σ : global_env × universes_decl)
  (Γ Γ' : context) (t T : term) n, n = #|Γ'| ->
  wf Σ.1 ->
  wf_local Σ (Γ ,,, Γ') ->
  Σ;;; Γ |- t : T -> Σ;;; Γ ,,, Γ' |- (lift0 n) t : (lift0 n) T.
Proof.
  intros ; subst n; now apply weakening.
Qed.

Corollary All_mfix_wf {cf:checker_flags} Σ Γ mfix :
 wf Σ.1 -> wf_local Σ Γ ->
 All (fun d : def term => isType Σ Γ (dtype d)) mfix ->
 wf_local Σ (Γ ,,, fix_context mfix).
Proof.
  move=> wfΣ wf a; move: wf.
  change (fix_context mfix) with (fix_context_gen #|@nil context_decl| mfix).
  change Γ with (Γ ,,, []).
  generalize (@nil context_decl) as Δ.
  rewrite /fix_context_gen.
  intros Δ wfΔ.  
  eapply All_local_env_app_inv. split; auto.
  induction a in Δ, wfΔ |- *; simpl; auto.
  + constructor.
  + simpl.
    eapply All_local_env_app_inv. split; auto.
    * repeat constructor.
      simpl.
      destruct p as [s Hs].
      exists s. eapply (weakening Σ Γ Δ _ (tSort s)); auto.
    * specialize (IHa (Δ ,,, [vass (dname x) (lift0 #|Δ| (dtype x))])).
      rewrite app_length in IHa. simpl in IHa.
      forward IHa.
      ** simpl; constructor; auto.
        destruct p as [s Hs]. 
        exists s. eapply (weakening Σ Γ Δ _ (tSort s)); auto.
      ** eapply All_local_env_impl; eauto.
        simpl; intros.
        rewrite app_context_assoc. apply X.
Qed.
