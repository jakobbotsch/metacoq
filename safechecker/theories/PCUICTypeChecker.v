(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils uGraph.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICNormal PCUICSR
     PCUICGeneration PCUICReflect PCUICEquality PCUICInversion PCUICValidity
     PCUICWeakening PCUICPosition PCUICCumulativity PCUICSafeLemmata PCUICSN
     PCUICPretty PCUICArities PCUICConfluence PCUICSize
     PCUICContextConversion PCUICConversion PCUICWfUniverses
     PCUICGlobalEnv 
     (* Used for support lemmas *)
     PCUICInductives PCUICWfUniverses
     PCUICContexts PCUICSubstitution PCUICSpine PCUICInductiveInversion
     PCUICClosed PCUICUnivSubstitution PCUICWeakeningEnv.

From MetaCoq.SafeChecker Require Import PCUICSafeReduce PCUICErrors PCUICEqualityDec
  PCUICSafeConversion PCUICWfReduction PCUICWfEnv.

From Equations Require Import Equations.
Require Import ssreflect ssrbool.

Local Set Keyed Unification.
Set Equations Transparent.

(** It otherwise tries [auto with *], very bad idea. *)
Ltac Coq.Program.Tactics.program_solve_wf ::= 
  match goal with 
  | |- @Wf.well_founded _ _ => auto with subterm wf
  | |- ?T => match type of T with
                | Prop => auto
                end
  end.

Section Typecheck.
  Context {cf : checker_flags} {Σ : global_env_ext} (HΣ : ∥ wf Σ ∥)
          (Hφ : ∥ on_udecl Σ.1 Σ.2 ∥)
          (G : universes_graph) (HG : is_graph_of_uctx G (global_ext_uctx Σ)).

  (* We get stack overflow on Qed after Equations definitions when this is transparent *)
  Opaque reduce_stack_full.

  Local Definition HΣ' : ∥ wf_ext Σ ∥.
  Proof.
    destruct HΣ, Hφ; now constructor.
  Defined.

  Notation hnf := (hnf HΣ).

  Definition isconv Γ := isconv_term Σ HΣ Hφ G HG Γ Conv.
  Definition iscumul Γ := isconv_term Σ HΣ Hφ G HG Γ Cumul.
  
  Program Definition convert Γ t u
          (ht : welltyped Σ Γ t) (hu : welltyped Σ Γ u)
    : typing_result (∥ Σ ;;; Γ |- t = u ∥) :=
    match eqb_term Σ G t u with true => ret _ | false =>
    match isconv Γ t ht u hu with
    | ConvSuccess => ret _
    | ConvError e => (* fallback *)  (* nico *)
      let t' := hnf Γ t ht in
      let u' := hnf Γ u hu in
      (* match leq_term (snd Σ) t' u' with true => ret _ | false => *)
      raise (NotCumulSmaller G Γ t u t' u' e)
      (* end *)
    end end.
  Next Obligation.
    symmetry in Heq_anonymous; eapply eqb_term_spec in Heq_anonymous; tea.
    constructor. now constructor.
  Qed.
  Next Obligation.
    symmetry in Heq_anonymous; apply isconv_term_sound in Heq_anonymous.
    assumption.
  Qed.

  Program Definition convert_leq Γ t u
          (ht : welltyped Σ Γ t) (hu : welltyped Σ Γ u)
    : typing_result (∥ Σ ;;; Γ |- t <= u ∥) :=
    match leqb_term Σ G t u with true => ret _ | false =>
    match iscumul Γ t ht u hu with
    | ConvSuccess => ret _
    | ConvError e => (* fallback *)  (* nico *)
      let t' := hnf Γ t ht in
      let u' := hnf Γ u hu in
      (* match leq_term (snd Σ) t' u' with true => ret _ | false => *)
      raise (NotCumulSmaller G Γ t u t' u' e)
      (* end *)
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
    
    Program Definition infer_scheme Γ HΓ t :
      typing_result (∑ ctx u, ∥ Σ ;;; Γ |- t : mkAssumArity ctx u ∥) :=
      '(T; p) <- infer Γ HΓ t;;
      match reduce_to_arity HΣ Γ T _ with
      | inleft car => ret (conv_ar_context car; conv_ar_univ car; _)
      | inright _ => TypeError (NotAnArity T)
      end.
    Next Obligation.
      intros; subst.
      cbn in *.
      eapply validity_wf; eauto.
    Qed.
    Next Obligation.
      destruct car as [? ? [r]].
      cbn.
      clear Heq_anonymous.
      sq.
      eapply type_reduction; eauto.
    Qed.

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

    Program Definition check_consistent_instance uctx u
      : typing_result (consistent_instance_ext Σ uctx u)
      := match uctx with
         | Monomorphic_ctx _ =>
           check_eq_nat #|u| 0 (Msg "monomorphic instance should be of length 0")
         | Polymorphic_ctx (inst, cstrs) =>
           let '(inst, cstrs) := AUContext.repr (inst, cstrs) in
           check_eq_true (forallb (fun l => LevelSet.mem l (uGraph.wGraph.V G)) u)
                         (Msg "undeclared level in instance") ;;
           X <- check_eq_nat #|u| #|inst|
         (Msg "instance does not have the right length");;
         match check_constraints G (subst_instance_cstrs u cstrs) with
         | true => ret (conj _ _)
         | false => raise (Msg "ctrs not satisfiable")
         end
           (* #|u| = #|inst| /\ valid_constraints φ (subst_instance_cstrs u cstrs) *)
         end.
    Next Obligation.
      eapply forallb_All in H. eapply All_forallb'; tea.
      clear -cf HG. intros x; simpl. now apply is_graph_of_uctx_levels.
    Qed.
    Next Obligation.
      repeat split.
      - now rewrite mapi_length in X.
      - eapply check_constraints_spec; eauto.
    Qed.

    Obligation Tactic := Program.Tactics.program_simplify ; eauto 2.
    
    Program Definition check_is_allowed_elimination (u : Universe.t) (al : allowed_eliminations) :
      typing_result (is_allowed_elimination Σ u al) :=
      let o :=
          match al return option (is_allowed_elimination Σ u al) with
          | IntoSProp =>
            match Universe.is_sprop u with
            | true => Some _
            | false => None
            end
          | IntoPropSProp =>
            match is_propositional u with
            | true => Some _
            | false => None
            end
          | IntoSetPropSProp =>
            match is_propositional u || check_eqb_universe G u Universe.type0 with
            | true => Some _
            | false => None
            end
          | IntoAny => Some _
          end in
      match o with
      | Some t => Checked t
      | None => TypeError (Msg "Cannot eliminate over this sort")
      end.
    Next Obligation.
      unfold is_allowed_elimination, is_allowed_elimination0.
      destruct check_univs; auto.
      intros val sat.
      symmetry in Heq_anonymous.
      apply is_sprop_val with (v := val) in Heq_anonymous.
      now rewrite Heq_anonymous.
    Qed.
    Next Obligation.
      unfold is_allowed_elimination, is_allowed_elimination0.
      destruct check_univs; auto.
      intros val sat.
      unfold is_propositional in *.
      destruct Universe.is_prop eqn:prop.
      - apply is_prop_val with (v := val) in prop; rewrite prop; auto.
      - destruct Universe.is_sprop eqn:sprop.
        + apply is_sprop_val with (v := val) in sprop; rewrite sprop; auto.
        + discriminate.
    Qed.
    Next Obligation.
      unfold is_allowed_elimination, is_allowed_elimination0.
      destruct check_univs eqn:cu; auto.
      intros val sat.
      unfold is_propositional in *.
      destruct Universe.is_prop eqn:prop.
      - apply is_prop_val with (v := val) in prop; rewrite prop; auto.
      - destruct Universe.is_sprop eqn:sprop.
        + apply is_sprop_val with (v := val) in sprop; rewrite sprop; auto.
        + destruct check_eqb_universe eqn:check; [|discriminate].
          eapply check_eqb_universe_spec' in check; eauto.
          * unfold eq_universe, eq_universe0 in check.
            rewrite cu in check.
            specialize (check val sat).
            now rewrite check.
          * destruct HΣ, Hφ.
            now apply wf_ext_global_uctx_invariants.
          * destruct HΣ, Hφ.
            now apply global_ext_uctx_consistent.
    Qed.
    Next Obligation.
      unfold is_allowed_elimination, is_allowed_elimination0.
      destruct check_univs; auto.
    Qed.
    
    Equations? (noeqns) infer_constructor (Γ : context) (HΓ : ∥wf_local Σ Γ∥) (c : term)
      : typing_result (∑ ind u args, ∥ Σ;;; Γ |- c : mkApps (tInd ind u) args ∥) :=
      infer_constructor Γ HΓ c with infer Γ HΓ c := {
        | TypeError te => TypeError te;
        | Checked (cty; c_typ) with reduce_to_ind HΣ Γ cty _ := {
          | TypeError te => TypeError te;
          | Checked (ind; u; args; typ) => Checked (ind; u; args; _)
          }
        }.
    Proof.
      - eapply validity_wf; eauto.
      - sq.
        eapply type_reduction; eauto.
    Qed.
    
  Definition wt_decl (Σ : global_env_ext) Γ d :=
    match d with
    | {| decl_body := Some b; decl_type := ty |} => 
      welltyped Σ Γ ty /\ welltyped Σ Γ b
    | {| decl_body := None; decl_type := ty |} =>
      welltyped Σ Γ ty
    end.
  
  Definition wf_env_conv (Γ : context) (t u : term) :
    welltyped Σ Γ t -> welltyped Σ Γ u -> typing_result (∥ Σ;;; Γ |- t = u ∥) :=
    @convert Γ t u.

  Definition wf_env_cumul (Γ : context) (t u : term) :
    welltyped Σ Γ t -> welltyped Σ Γ u -> typing_result (∥ Σ;;; Γ |- t <= u ∥) :=
    @convert_leq Γ t u.

   Program Definition check_cumul_decl Γ d d' : wt_decl Σ Γ d -> wt_decl Σ Γ d' -> typing_result (∥ cumul_decls Σ Γ Γ d d' ∥) := 
    match d, d' return wt_decl Σ Γ d -> wt_decl Σ Γ d' -> typing_result _ with
    | {| decl_name := na; decl_body := Some b; decl_type := ty |},
      {| decl_name := na'; decl_body := Some b'; decl_type := ty' |} => 
      fun wtd wtd' =>
      eqna <- check_eq_true (eqb_binder_annot na na') (Msg "Binder annotations do not match") ;;
      cumb <- convert Γ b b' _ _ ;;
      cumt <- convert_leq Γ ty ty' _ _ ;;
      ret (let 'sq cumb := cumb in 
            let 'sq cumt := cumt in
            sq _)
    | {| decl_name := na; decl_body := None; decl_type := ty |},
      {| decl_name := na'; decl_body := None; decl_type := ty' |} => 
      fun wtd wtd' =>
      eqna <- check_eq_true (eqb_binder_annot na na') (Msg "Binder annotations do not match") ;;
      cumt <- convert_leq Γ ty ty' wtd wtd';;
      ret (let 'sq cumt := cumt in sq _)      
    | _, _ =>
      fun wtd wtd' => raise (Msg "While checking cumulativity of contexts: declarations do not match")
    end.
  Next Obligation.
    constructor; pcuics. now apply eqb_binder_annot_spec.
  Qed.
  Next Obligation.
    constructor; pcuics. now apply eqb_binder_annot_spec.
  Qed.
  
  Lemma cumul_ctx_rel_cons {Γ Δ Δ' d d'} (c : cumul_ctx_rel Σ Γ Δ Δ') (p : cumul_decls Σ (Γ,,, Δ) (Γ ,,, Δ') d d') : 
    cumul_ctx_rel Σ Γ (Δ ,, d) (Δ' ,, d').
  Proof.
    destruct d as [na [b|] ty], d' as [na' [b'|] ty']; try constructor; auto.
    depelim p. depelim p.
  Qed.
  
  Lemma cumul_ctx_rel_close Γ Δ Δ' : 
    cumul_ctx_rel Σ Γ Δ Δ' ->
    cumul_context Σ (Γ ,,, Δ) (Γ ,,, Δ').
  Proof.
    induction 1; pcuic.
  Qed.
  
  Lemma cumul_decls_irrel_sec  Γ Γ' d d' :
    cumul_decls Σ Γ Γ d d' ->
    cumul_decls Σ Γ Γ' d d'.
  Proof.
    intros cum; depelim cum; intros; constructor; auto.
  Qed.
  
  Lemma inv_wf_local Γ d :
    wf_local Σ (Γ ,, d) ->
    wf_local Σ Γ * wt_decl Σ Γ d.
  Proof.
    intros wfd; depelim wfd; split; simpl; pcuic.
    now exists t.
  Qed.
  
  Lemma context_cumulativity_welltyped Γ Γ' t : 
    welltyped Σ Γ t ->
    cumul_context Σ Γ' Γ ->
    wf_local Σ Γ' ->
    welltyped Σ Γ' t.
  Proof.
    destruct HΣ.
    intros [s Hs] cum wfΓ'; exists s; eapply context_cumulativity; pcuics.
  Qed.

  Lemma context_cumulativity_wt_decl Γ Γ' d :
    wt_decl Σ Γ d ->
    cumul_context Σ Γ' Γ ->
    wf_local Σ Γ' ->
    wt_decl Σ Γ' d.
  Proof.
    destruct HΣ.
    destruct d as [na [b|] ty]; simpl;
    intuition pcuics; eapply context_cumulativity_welltyped; pcuics.
  Qed.
 
  Program Fixpoint check_cumul_ctx Γ Δ Δ' 
    (wfΔ : ∥ wf_local Σ (Γ ,,, Δ) ∥) (wfΔ' : ∥ wf_local Σ (Γ ,,, Δ') ∥) : 
    typing_result (∥ cumul_ctx_rel Σ Γ Δ Δ' ∥) :=
    match Δ, Δ' with
    | [], [] => ret (sq (ctx_rel_nil _))
    | decl :: Δ, decl' :: Δ' => 
      cctx <- check_cumul_ctx Γ Δ Δ' _ _ ;;
      cdecl <- check_cumul_decl (Γ ,,, Δ) decl decl' _ _ ;;
      ret _
    | _, _ => raise (Msg "While checking cumulativity of contexts: contexts have not the same length")
    end.
    Next Obligation.
      sq; now depelim wfΔ.
    Qed.
    Next Obligation.
      sq; now depelim wfΔ'.
    Qed.
    Next Obligation.
      sq.
      depelim wfΔ; simpl.
      destruct l; eexists; eauto.
      destruct l; split; eexists; eauto.
    Qed.
    Next Obligation.
      destruct wfΔ as [wfΔ], wfΔ' as [wfΔ'], cctx.
      assert(cumul_context Σ (Γ ,,, Δ) (Γ ,,, Δ')).
      now apply cumul_ctx_rel_close.
      simpl in *. eapply inv_wf_local in wfΔ as [wfΔ wfd].
      eapply inv_wf_local in wfΔ' as [wfΔ' wfd'].
      eapply context_cumulativity_wt_decl. 3:eassumption. all:pcuics.
    Qed.
    Next Obligation.
      sq; simpl in *.
      eapply inv_wf_local in wfΔ as [wfΔ wfd].
      eapply inv_wf_local in wfΔ' as [wfΔ' wfd'].
      apply cumul_ctx_rel_cons. auto.
      eapply cumul_decls_irrel_sec; pcuics.
    Qed.
    Next Obligation.
      split. intros. intros []. congruence. intros []; congruence.
    Qed.
    Next Obligation.
      split. intros. intros []. congruence. intros []; congruence.
    Qed.

    Lemma isArity_instantiate_params_subst params pars s ty res :
      isArity ty ->
      instantiate_params_subst params pars s ty = Some res ->
      isArity res.2.
    Proof.
      induction params in pars, s, ty, res |- *; intros isar inst; cbn in *.
      - destruct pars; [|congruence].
        noconf inst; auto.
      - destruct decl_body.
        + destruct ty; try discriminate inst.
          cbn in *.
          apply IHparams in inst; auto.
        + destruct ty; try discriminate inst.
          cbn in *.
          destruct pars; [discriminate|].
          apply IHparams in inst; auto.
    Qed.
    
    Lemma isArity_instantiate_params ctx params ty res :
      isArity ty ->
      instantiate_params ctx params ty = Some res ->
      isArity res.
    Proof.
      intros isAr inst.
      unfold instantiate_params in *.
      destruct instantiate_params_subst as [(?&?)|] eqn:inst'; [|discriminate].
      apply isArity_instantiate_params_subst in inst'; auto.
      noconf inst.
      apply PCUICCanonicity.isArity_subst; auto.
    Qed.
    
    Lemma isArity_destArity t :
      isArity t <-> exists ctx u, destArity [] t = Some (ctx, u).
    Proof.
      induction t; cbn in *.
      all: split; [intros; try easy|intros (?&?&[=])]; subst.
      - auto.
      - apply IHt2 in H as (?&?&eq).
        rewrite destArity_app eq.
        cbn.
        eauto.
      - rewrite destArity_app in H0.
        destruct destArity as [(?&?)|] eqn:dest in H0; cbn in *; [|congruence].
        noconf H0.
        apply IHt2.
        eauto.
      - apply IHt3 in H as (?&?&eq).
        rewrite destArity_app eq.
        cbn.
        eauto.
      - rewrite destArity_app in H0.
        destruct destArity as [(?&?)|] eqn:dest in H0; cbn in *; [|congruence].
        noconf H0.
        apply IHt3.
        eauto.
    Qed.
    
    Equations? build_case_predicate_context
             (ind : inductive)
             (mdecl : mutual_inductive_body) (idecl : one_inductive_body)
             (isdecl : declared_inductive Σ mdecl ind idecl)
             (params : list term)
             (u : Instance.t)
             (npars_eq : #|params| = ind_npars mdecl) : context :=
      build_case_predicate_context ind mdecl idecl isdecl params u npars_eq
        with inspect (instantiate_params (subst_instance_context u (ind_params mdecl)) params
                                         (subst_instance_constr u (ind_type idecl))) := {
        | exist None inst_none => False_rect _ _;
        | exist (Some inst_params) inst_some with inspect (destArity [] inst_params) := {
          | exist None dest_none => False_rect _ _;
          | exist (Some (ctx, _)) _ =>
            (ctx,, vass {| binder_name := nNamed (ind_name idecl);
                           binder_relevance := ind_relevance idecl |}
                        (mkApps (tInd ind u) (map (lift0 #|ctx|) params ++ to_extended_list ctx)))
          }
        }.
    Proof.
      all: destruct HΣ.
      all: apply PCUICWeakeningEnv.on_declared_inductive in isdecl as (on_ind&on_oib); auto.
      all: rewrite ->(ind_arity_eq on_oib) in *.
      all: rewrite ->!subst_instance_constr_it_mkProd_or_LetIn in *.
      - symmetry in inst_some.
        apply isArity_instantiate_params in inst_some; auto.
        + apply isArity_destArity in inst_some as (?&?&?); congruence.
        + repeat apply isArity_it_mkProd_or_LetIn.
          apply isArity_destArity.
          rewrite (subst_instance_destArity []).
          cbn.
          eauto.
      - cbn in *.
        symmetry in inst_none.
        match type of inst_none with
        | ?a = ?b => enough (∑ t, a = Some t) as (?&?) by congruence
        end.
        apply PCUICCtxShape.instantiate_params_ok.
        + apply context_relation_refl; intros.
          unfold PCUICCtxShape.same_shape.
          destruct decl_body; auto.
        + rewrite npars_eq.
          rewrite subst_instance_context_assumptions.
          rewrite <- (onNpars on_ind).
          auto.
    Qed.
    
    Definition last_nonempty {X : Type} (xs : list X) : 0 < #|xs| -> X :=
      match xs with
      | [] => fun ne => ltac:(exfalso; inversion ne)
      | x :: xs => fun _ => last xs x
      end.
    
    Equations? infer_case
             (Γ : context) (wfΓ : ∥ wf_local Σ Γ ∥)
             (ind : inductive)
             (pars : nat)
             (p c : term)
             (brs : list (nat × term))
      : typing_result (∑ A, ∥ Σ ;;; Γ |- tCase (ind, pars) p c brs : A ∥) :=
      infer_case Γ wfΓ ind pars p c brs with infer_constructor Γ wfΓ c := {

       | TypeError te => TypeError te;
       | Checked (ind'; scrut_u; args; typ_c) with inspect (eqb ind ind') := {

        | exist false ind_neq =>
          TypeError (NotConvertible G Γ (tInd ind scrut_u) (tInd ind' scrut_u));
        | exist true ind_eq with lookup_ind_decl ind := {

         | TypeError te => TypeError te;
         | Checked (decl; body; isdecl) with inspect (isCoFinite (ind_finite decl)) := {

          | exist true is_coind => TypeError (Msg "Case on coinductives disallowed");
          | exist false not_coind with inspect (pars =? ind_npars decl) := {

           | exist false pars_neq => TypeError (Msg "Not the right number of parameters");
           | exist true pars_eq with split_at pars args := {

            | (params, indices) with infer_scheme infer Γ wfΓ p := {

             | TypeError te => TypeError te;
             | Checked (pred_ctx; pred_sort; typ_p)
                 with check_is_allowed_elimination ps (ind_kelim body) := {

              | TypeError te => TypeError te;
              | Checked al_elim
                  with inspect (build_case_predicate_context
                                  ind decl body isdecl params scrut_u pars_eq) := {
               | exist ind_ctx is_build_ctx
                   with check_cumul_ctx Γ ind_ctx (arity_ass_context pred_ctx) _ _ := {

                | TypeError te => TypeError te;
                | Checked cum_ctx with view_indc (last_nonempty pred_ctx _) := {

                 | view_ind_other t notind => False_rect _ _;
                 | view_ind_tInd ind'' pred_u 
            }
           }
          }
         }
        }
       }.
        
      cty <- infer Γ HΓ c ;;
      I <- reduce_to_ind HΣ Γ cty.π1 _ ;;
      let '(ind'; I') := I in let '(scrut_inst; I'') := I' in let '(args; H) := I'' in
      check_eq_true (eqb ind ind')
                    (* bad case info *)
                    (NotConvertible G Γ (tInd ind scrut_inst) (tInd ind' scrut_inst)) ;;
      d <- lookup_ind_decl ind' ;;
      let '(decl; d') := d in let '(body; HH) := d' in
      check_coind <- check_eq_true (negb (isCoFinite (ind_finite decl)))
            (Msg "Case on coinductives disallowed") ;;
      check_eq_true (ind_npars decl =? par)
                    (Msg "not the right number of parameters") ;;
      IS <- infer_scheme infer Γ HΓ p ;;
      let '(pred_ctx; IS') := IS in let '(ps; typ_p) := IS' in
      check_is_allowed_elimination ps (ind_kelim body);;
      let pred_ctx := arity_ass_context pctx in
      check_cumul_ctx build_case_
      let pty := mkAssumArity pctx ps in
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

  End InferAux.

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
      ty <- infer Γ HΓ t ;;
      pi <- reduce_to_prod HΣ Γ ty.π1 _ ;;
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
      cty <- infer Γ HΓ c ;;
      I <- reduce_to_ind HΣ Γ cty.π1 _ ;;
      let '(ind'; I') := I in let '(scrut_inst; I'') := I' in let '(args; H) := I'' in
      check_eq_true (eqb ind ind')
                    (* bad case info *)
                    (NotConvertible G Γ (tInd ind scrut_inst) (tInd ind' scrut_inst)) ;;
      d <- lookup_ind_decl ind' ;;
      let '(decl; d') := d in let '(body; HH) := d' in
      check_coind <- check_eq_true (negb (isCoFinite (ind_finite decl)))
            (Msg "Case on coinductives disallowed") ;;
      check_eq_true (ind_npars decl =? par)
                    (Msg "not the right number of parameters") ;;
      IS <- infer_scheme infer Γ HΓ p ;;
      let '(pred_ctx; IS') := IS in let '(ps; typ_p) := IS' in
      check_is_allowed_elimination ps (ind_kelim body);;
      let pred_ctx := arity_ass_context pctx in
      check_cumul_ctx build_case_
      let pty := mkAssumArity pctx ps in
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
        c_ty <- infer Γ HΓ c ;;
        I <- reduce_to_ind HΣ Γ c_ty.π1 _ ;;
        let '(ind'; I') := I in let '(u; I'') := I' in let '(args; H) := I'' in
        check_eq_true (eqb ind ind')
                      (NotConvertible G Γ (tInd ind u) (tInd ind' u)) ;;
        check_eq_true (ind_npars d.π1 =? n)
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
        XX <- (fix check_types (mfix : mfixpoint term) {struct mfix}
              : typing_result (∥ All (fun x => isType Σ Γ (dtype x)) mfix ∥)
              := match mfix with
                 | [] => ret (sq All_nil)
                 | def :: mfix =>
       (* probably not tail recursive but needed so that next line terminates *)
                   W <- infer_type infer Γ HΓ (dtype def) ;;
                   Z <- check_types mfix ;;
                   ret _
                 end)
           mfix ;;
        YY <- (fix check_bodies (mfix' : mfixpoint term)
              (XX : ∥ All (fun x => isType Σ Γ (dtype x)) mfix' ∥)
            {struct mfix'}
                : typing_result (All (fun d =>
              ∥ Σ ;;; Γ ,,, fix_context mfix |- dbody d : (lift0 #|fix_context mfix|) (dtype d) ∥
              /\ isLambda (dbody d) = true) mfix')
              := match mfix' with
                 | [] => ret All_nil
                 | def :: mfix' =>
                   W1 <- infer_cumul infer (Γ ,,, fix_context mfix) _ (dbody def)
                                    (lift0 #|fix_context mfix| (dtype def)) _ ;;
                   W2 <- check_eq_true (isLambda (dbody def))
                                      (Msg "not a lambda") ;;
                   Z <- check_bodies mfix' _ ;;
                   ret (All_cons (conj W1 W2) Z)
                 end) mfix _ ;;
        guarded <- check_eq_true (fix_guard Σ Γ mfix) (Msg "Unguarded fixpoint") ;;
        wffix <- check_eq_true (wf_fixpoint Σ.1 mfix) (Msg "Ill-formed fixpoint: not defined on a mutually inductive family") ;;
        ret (dtype decl; _)
      end

    | tCoFix mfix n =>
      match nth_error mfix n with
      | None => raise (IllFormedFix mfix n)
      | Some decl =>
        XX <-  (fix check_types (mfix : mfixpoint term) {struct mfix}
        : typing_result (∥ All (fun x => isType Σ Γ (dtype x)) mfix ∥)
        := match mfix with
           | [] => ret (sq All_nil)
           | def :: mfix =>
            (* probably not tail recursive but needed so that next line terminates *)
             W <- infer_type infer Γ HΓ (dtype def) ;;
             Z <- check_types mfix ;;
             ret _
           end)
         mfix ;;
        YY <- (fix check_bodies (mfix' : mfixpoint term)
        (XX' : ∥ All (fun x => isType Σ Γ (dtype x)) mfix' ∥)
        {struct mfix'}
        : typing_result (All (fun d =>
            ∥ Σ ;;; Γ ,,, fix_context mfix |- dbody d : (lift0 #|fix_context mfix|) (dtype d) ∥) mfix')
              := match mfix' with
                 | [] => ret All_nil
                 | def :: mfix' =>
                   W1 <- infer_cumul infer (Γ ,,, fix_context mfix) _ (dbody def)
                                    (lift0 #|fix_context mfix| (dtype def)) _ ;;
                   Z <- check_bodies mfix' _ ;;
                   ret (All_cons W1 Z)
                 end) mfix _ ;;
        guarded <- check_eq_true (cofix_guard Σ Γ mfix) (Msg "Unguarded cofixpoint") ;;
        wfcofix <- check_eq_true (wf_cofixpoint Σ.1 mfix) (Msg "Ill-formed cofixpoint: not producing values in a mutually coinductive family") ;;
        ret (dtype decl; _)
      end
    end.

  (* tRel *)
  Next Obligation. intros; sq; now econstructor. Defined.
  (* tSort *)
  Next Obligation.
    eapply (elimT wf_universe_reflect) in H.
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
  Next Obligation. simpl; eauto using validity_wf. Qed.
  Next Obligation.
    cbn in *; sq.
    eapply type_reduction in X1 ; try eassumption.
    eapply validity_term in X1 ; try assumption. destruct X1 as [s HH].
    eapply inversion_Prod in HH ; try assumption.
    destruct HH as [s1 [_ [HH _]]].
    eexists. eassumption.
  Defined.
  Next Obligation.
    cbn in *; sq; econstructor.
    2: eassumption.
    eapply type_reduction; eassumption.
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
  Next Obligation. simpl; eauto using validity_wf. Qed.
  Next Obligation.
    destruct X1, X11. sq.
    change (eqb ind I = true) in H0.
    destruct (eqb_spec ind I) as [e|e]; [destruct e|discriminate].
    change (eqb (ind_npars d) par = true) in H1.
    destruct (eqb_spec (ind_npars d) par) as [e|e]; [|discriminate].
    rename Heq_anonymous into HH. symmetry in HH.
    simpl in *.
    rewrite <- e in HH.
    eapply PCUICInductiveInversion.WfArity_build_case_predicate_type in HH; eauto.
    destruct HH as [[s Hs] ?]. eexists; eauto.
    eapply isType_red; [|eassumption].
    eapply validity; eauto.
    rewrite mkAssumArity_it_mkProd_or_LetIn in X.
    eapply validity in X; auto.
    eapply PCUICInductives.isType_it_mkProd_or_LetIn_inv in X; eauto.
    eapply isType_wf_universes in X; auto.
    now exact (elimT wf_universe_reflect X).
  Qed.

  Next Obligation.
    symmetry in Heq_anonymous1.
    unfold iscumul in Heq_anonymous1. simpl in Heq_anonymous1.
    apply isconv_term_sound in Heq_anonymous1.
    red in Heq_anonymous1.
    noconf Heq_I''.
    noconf Heq_I'. noconf Heq_I.
    noconf Heq_d. noconf Heq_d'.
    noconf Heq_IS. noconf Heq_IS'.
    simpl in *; sq.
    change (eqb ind I = true) in H0.
    destruct (eqb_spec ind I) as [e|e]; [destruct e|discriminate H0].
    change (eqb (ind_npars d) par = true) in H1.
    destruct (eqb_spec (ind_npars d) par) as [e|e]; [|discriminate]; subst.
    assert (wfΣ : wf_ext Σ) by (split; auto).
    eapply type_reduction in X11; eauto.
    have val:= validity_term wfΣ X11.
    eapply type_Cumul' in typ_p; [| |eassumption].
    2:{ eapply PCUICInductiveInversion.WfArity_build_case_predicate_type; eauto.
        eapply validity in typ_p; eauto.
        rewrite mkAssumArity_it_mkProd_or_LetIn in typ_p.
        eapply PCUICInductives.isType_it_mkProd_or_LetIn_inv in typ_p; eauto.
        apply isType_wf_universes in typ_p; auto.
        now exact (elimT wf_universe_reflect typ_p). }
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
    eapply type_reduction in X11; eauto.
    eapply type_Cumul' in typ_p; eauto.
    2:{ eapply PCUICInductiveInversion.WfArity_build_case_predicate_type; eauto.
        eapply validity in X11; eauto.
        eapply validity in typ_p; auto.
        rewrite mkAssumArity_it_mkProd_or_LetIn in typ_p.
        eapply PCUICInductives.isType_it_mkProd_or_LetIn_inv in typ_p; eauto.
        apply isType_wf_universes in typ_p; auto.
        now exact (elimT wf_universe_reflect typ_p). }
    eapply type_Case with (pty0:=pty'); tea.
    - reflexivity.
    - symmetry; eassumption.
    - destruct isCoFinite; auto.
    - symmetry; eauto.
  Defined.

  Obligation Tactic := Program.Tactics.program_simplify ; eauto 2.

  (* tProj *)
  Next Obligation. simpl; eauto using validity_wf. Qed.
  Next Obligation.
    simpl in *; sq; eapply type_Proj with (pdecl := (i, t0)).
    - split. eassumption. split. symmetry; eassumption. cbn in *.
      now apply beq_nat_true.
    - cbn. destruct (ssrbool.elimT (eqb_spec ind I)); [assumption|].
      eapply type_reduction; eassumption.
    - eapply type_reduction in X5; eauto.
      eapply validity_term in X5; eauto.
      destruct (ssrbool.elimT (eqb_spec ind I)); auto.
      unshelve eapply (PCUICInductives.isType_mkApps_Ind _ X7 _) in X5 as [parsubst [argsubst [[sp sp'] cu]]]; eauto.
      pose proof (PCUICContexts.context_subst_length2 (PCUICSpine.inst_ctx_subst sp)).
      pose proof (PCUICContexts.context_subst_length2 (PCUICSpine.inst_ctx_subst sp')).
      autorewrite with len in H, H2.
      destruct (PCUICWeakeningEnv.on_declared_inductive HΣ X7) eqn:ond.
      rewrite -o.(onNpars) -H.
      forward (o0.(onProjections)).
      intros H'; rewrite H' nth_error_nil // in Heq_anonymous.
      destruct ind_cshapes as [|cs []]; auto.
      intros onps.
      unshelve epose proof (onps.(on_projs_noidx _ _ _ _ _ _)).
      rewrite ond /= in H2.
      change (ind_indices o0) with (ind_indices o0) in *.
      destruct (ind_indices o0) => //.
      simpl in H2.
      rewrite List.skipn_length in H2.
      rewrite List.firstn_length. lia.
  Qed.

  (* tFix *)
  Next Obligation. sq. constructor; auto. exists W; auto. Defined.
  Next Obligation. sq. now eapply PCUICWeakening.All_mfix_wf in XX0. Defined.
  Next Obligation.
    sq. cbn in *. depelim XX.
    destruct i as [s HH].
    exists s.
    change (tSort s) with (lift0 #|fix_context mfix| (tSort s)).
    apply weakening; try assumption.
    now apply All_mfix_wf.
  Defined.
  Next Obligation.
    clear -XX HΣ. sq.
    now depelim XX.
  Qed.
  Next Obligation.
    assert (∥ All (fun d => ((Σ;;; Γ ,,, fix_context mfix |- dbody d : (lift0 #|fix_context mfix|) (dtype d)) * (isLambda (dbody d) = true))%type) mfix ∥). {
      eapply All_sq, All_impl.  exact YY.
      cbn; intros ? []. sq; now constructor. }
    sq; econstructor; try eassumption.
    symmetry; eassumption.
  Qed.

  (* tCoFix *)
  Next Obligation. sq. constructor; auto. exists W; auto. Defined.
  Next Obligation. sq. now eapply PCUICWeakening.All_mfix_wf in XX. Defined.
  Next Obligation.
    sq. cbn in *. depelim XX'.
    destruct i as [s HH].
    exists s.
    change (tSort s) with (lift0 #|fix_context mfix| (tSort s)).
    apply weakening; try assumption.
    now apply All_mfix_wf.
  Defined.
  Next Obligation.
    clear -XX' HΣ. sq.
    now depelim XX'.
  Qed.
  Next Obligation.
    assert (∥ All (fun d => ((Σ;;; Γ ,,, fix_context mfix |- dbody d : (lift0 #|fix_context mfix|) (dtype d)))%type) mfix ∥). {
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
