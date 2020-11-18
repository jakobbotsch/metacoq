(* Distributed under the terms of the MIT license. *)

Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.

From Coq Require Import Bool String List Program.
From MetaCoq.Template Require Import config monad_utils utils uGraph.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICArities PCUICInduction
     PCUICLiftSubst PCUICUnivSubst PCUICTyping PCUICSafeLemmata PCUICSubstitution PCUICValidity
     PCUICGeneration PCUICInversion PCUICValidity PCUICInductives PCUICInductiveInversion
     PCUICSpine PCUICSR PCUICCumulativity PCUICConversion PCUICConfluence PCUICArities
     PCUICWeakeningEnv PCUICContexts.
From MetaCoq.SafeChecker Require Import PCUICSafeReduce PCUICSafeChecker.
Local Open Scope string_scope.
Set Asymmetric Patterns.
Import monad_utils.MonadNotation.

Hint Constructors assumption_context : pcuic.

Derive NoConfusion for type_error.

Set Equations With UIP.
Set Equations Transparent.

Add Search Blacklist "_graph_mut".

Add Search Blacklist "obligation".

Require Import ssreflect.

Definition well_sorted {cf:checker_flags} Σ Γ T := 
  ∥ ∑ s, Σ ;;; Γ |- T : tSort s ∥.

Lemma well_sorted_well_typed {cf:checker_flags} {Σ Γ T} : well_sorted Σ Γ T -> welltyped Σ Γ T.
Proof.
  intros [[s Hs]]; now exists (tSort s).
Qed.

Coercion well_sorted_well_typed : well_sorted >-> welltyped.

(** * Retyping

  The [infer] function provides a fast (and loose) type inference
  function which assumes that the provided term is already well-typed in
  the given context and recomputes its type. Only reduction (for
  head-reducing types to uncover dependent products or inductives) and
  substitution are costly here. No universe checking or conversion is done
  in particular. *)

Definition principal_type {cf:checker_flags} Σ Γ t := { T : term | ∥ (Σ ;;; Γ |- t : T) * (forall T', Σ ;;; Γ |- t : T' -> Σ ;;; Γ |- T <= T') ∥ }.
Definition principal_sort {cf:checker_flags} Σ Γ T := { s : Universe.t | ∥ (Σ ;;; Γ |- T : tSort s) * (forall s', Σ ;;; Γ |- T : tSort s' -> leq_universe Σ s s') ∥ }.

Definition principal_typed_type {cf:checker_flags} {Σ Γ t} (wt : principal_type Σ Γ t) := proj1_sig wt.
Definition principal_sort_sort {cf:checker_flags} Σ Γ T (ps : principal_sort Σ Γ T) : Universe.t := proj1_sig ps.
Coercion principal_typed_type : principal_type >-> term.
Coercion principal_sort_sort : principal_sort >-> Universe.t.

Section TypeOf.
  Context {cf : checker_flags}.
  Context (Σ : global_env_ext).
  Context (hΣ : ∥ wf Σ ∥) (Hφ : ∥ on_udecl Σ.1 Σ.2 ∥).
  Context (G : universes_graph) (HG : is_graph_of_uctx G (global_ext_uctx Σ)).

  Lemma typing_welltyped Γ t T : Σ ;;; Γ |- t : T -> welltyped Σ Γ T.
  Proof.
    intros H.
    destruct hΣ. destruct Hφ.
    apply validity in H; auto. destruct H as [s tyT].
    econstructor; eauto.
  Qed.
End TypeOf.

Definition on_subterm P Pty Γ t : Type := 
  match t with
  | tProd na t b => Pty Γ t * Pty (Γ ,, vass na t) b
  | tLetIn na d t t' => 
    Pty Γ t * P Γ d * P (Γ ,, vdef na d t) t'
  | tLambda na t b => Pty Γ t * P (Γ ,, vass na t) b
  | _ => True
  end.

Lemma welltyped_subterm {cf:checker_flags} {Σ : global_env_ext} (wfΣ : ∥ wf Σ ∥) {Γ t} :
  welltyped Σ Γ t -> on_subterm (welltyped Σ) (well_sorted Σ) Γ t.
Proof.
  destruct t; simpl; auto; intros [T HT]; sq.
  eapply inversion_Prod in HT as (? & ? & ? & ? & ?); auto; split; try econstructor; eauto.
  eapply inversion_Lambda in HT as (? & ? & ? & ? & ?); auto; split; try econstructor; eauto.
  eapply inversion_LetIn in HT as (? & ? & ? & ? & ? & ?); auto; split; [split|]; try econstructor; eauto.
Qed.

Section TypeOf.
  Context {cf : checker_flags}.
  Context (Σ : global_env_ext).
  Context (hΣ : ∥ wf Σ ∥) (Hφ : ∥ on_udecl Σ.1 Σ.2 ∥).

  Local Notation ret t := (exist t _).

  Section SortOf.
    Obligation Tactic := idtac.
    Program Definition infer_as_sort {Γ t} (wf : well_sorted Σ Γ t)
      (tx : principal_type Σ Γ t) : principal_sort Σ Γ t :=
      match @reduce_to_sort cf Σ hΣ Γ tx _ with
      | Checked (u ; _) => u
      | TypeError e => !
      end.
      
    Next Obligation. intros Γ t [[s Hs]] [ty [[Hty Hp]]]; simpl.
      eapply typing_welltyped; eauto. Defined.
    Next Obligation. intros Γ t ws [s [[Hs Hp]]]. simpl in *.
      unfold infer_as_sort_obligation_1.
      destruct ws as [[s' Hs']]. 
      specialize (Hp _ Hs') as s'cum.
      eapply invert_cumul_sort_r in s'cum as [u' [redu' leq]].
      destruct reduce_to_sort => //.
      intros u wc [= <-].
      sq.
      split.
      - now eauto using type_reduction.
      - intros ? typ.
        apply (cumul_Sort_inv _ Γ).
        specialize (Hp _ typ).
        eapply cumul_red_l_inv; eauto.
    Qed.
    Next Obligation.
      simpl. intros.
      pose proof (reduce_to_sort_complete hΣ _ (eq_sym Heq_anonymous)).
      clear Heq_anonymous.
      destruct tx as (?&[(?&?)]).
      destruct wf as [(?&?)].
      apply c in t1.
      eapply invert_cumul_sort_r in t1 as (?&r&_).
      eauto.
    Qed.
  End SortOf.

  Program Definition infer_as_prod Γ T
    (wf : welltyped Σ Γ T)
    (isprod : ∥ ∑ na A B, Σ ;;; Γ |- T <= tProd na A B ∥) : 
    ∑ na' A' B', ∥ red Σ.1 Γ T (tProd na' A' B') ∥ :=
    match @reduce_to_prod cf Σ hΣ Γ T wf with
    | Checked p => p
    | TypeError e => !
    end.
    Next Obligation.
      destruct isprod as [(?&?&?&cum)].
      destruct hΣ.
      apply invert_cumul_prod_r in cum as cum'; auto;
        destruct cum' as (?&?&?&(?&?)&?).
      symmetry in Heq_anonymous.
      now eapply reduce_to_prod_complete in Heq_anonymous.
    Qed.
  
  Equations lookup_ind_decl ind : typing_result
        ({decl & {body & declared_inductive (fst Σ) decl ind body}}) :=
  lookup_ind_decl ind with inspect (lookup_env (fst Σ) ind.(inductive_mind)) :=
    { | exist (Some (InductiveDecl decl)) look with inspect (nth_error decl.(ind_bodies) ind.(inductive_ind)) :=
      { | exist (Some body) eqnth => Checked (decl; body; _);
        | ret None => raise (UndeclaredInductive ind) };
      | _ => raise (UndeclaredInductive ind) }.
  Next Obligation.
    split.
    - symmetry in look.
      etransitivity. eassumption. reflexivity.
    - now symmetry.
  Defined.

  Lemma lookup_ind_decl_complete ind e : lookup_ind_decl ind = TypeError e -> 
    ((∑ mdecl idecl, declared_inductive Σ mdecl ind idecl) -> False).
  Proof.
    apply_funelim (lookup_ind_decl ind).
    1-2:intros * _ her [mdecl [idecl [declm decli]]];
    red in declm; rewrite declm in e0; congruence.
    1-2:intros * _ _ => // => _ [mdecl [idecl [declm /= decli]]].
    red in declm. rewrite declm in e1. noconf e1.
    congruence.
  Qed.

  Obligation Tactic := idtac.

  Equations? infer (Γ : context) (t : term) (wt : welltyped Σ Γ t) : principal_type Σ Γ t 
    by struct t :=
  { infer Γ (tRel n) wt with 
    inspect (option_map (lift0 (S n) ∘ decl_type) (nth_error Γ n)) := 
    { | ret None => !;
      | ret (Some t) => ret t };
    
    infer Γ (tVar n) wt := !;
    infer Γ (tEvar ev args) wt := !;

    infer Γ (tSort s) _ := ret (tSort (Universe.super s));

    infer Γ (tProd n ty b) wt :=
      let ty1 := infer Γ ty (welltyped_subterm hΣ wt).1 in
      let s1 := infer_as_sort (welltyped_subterm hΣ wt).1 ty1 in
      let ty2 := infer (Γ ,, vass n ty) b (welltyped_subterm hΣ wt).2 in
      let s2 := infer_as_sort (welltyped_subterm hΣ wt).2 ty2 in
      ret (tSort (Universe.sort_of_product s1 s2));

    infer Γ (tLambda n t b) wt :=
      let t2 := infer (Γ ,, vass n t) b (welltyped_subterm hΣ wt).2 in
      ret (tProd n t t2);

    infer Γ (tLetIn n b b_ty b') wt :=
      let b'_ty := infer (Γ ,, vdef n b b_ty) b' (welltyped_subterm hΣ wt).2 in
      ret (tLetIn n b b_ty b'_ty);

    infer Γ (tApp t a) wt :=
      let ty := infer Γ t _ in
      let pi := infer_as_prod Γ ty _ _ in
      ret (subst10 a pi.π2.π2.π1);

    infer Γ (tConst cst u) wt with inspect (lookup_env (fst Σ) cst) :=
      { | ret (Some (ConstantDecl d)) := ret (subst_instance_constr u d.(cst_type));
        |  _ := ! };

    infer Γ (tInd ind u) wt with inspect (lookup_ind_decl ind) :=
      { | ret (Checked decl) := ret (subst_instance_constr u decl.π2.π1.(ind_type));
        | ret (TypeError e) := ! };
    
    infer Γ (tConstruct ind k u) wt with inspect (lookup_ind_decl ind) :=
      { | ret (Checked d) with inspect (nth_error d.π2.π1.(ind_ctors) k) := 
        { | ret (Some cdecl) => ret (type_of_constructor d.π1 cdecl (ind, k) u);
          | ret None => ! };
      | ret (TypeError e) => ! };

    infer Γ (tCase (ind, par) p c brs) wt with inspect (reduce_to_ind hΣ Γ (infer Γ c _) _) :=
      { | ret (Checked indargs) =>
          ret (mkApps p (List.skipn par indargs.π2.π2.π1 ++ [c]));
        | ret (TypeError _) => ! };

    infer Γ (tProj (ind, n, k) c) wt with inspect (@lookup_ind_decl ind) :=
      { | ret (Checked d) with inspect (nth_error d.π2.π1.(ind_projs) k) :=
        { | ret (Some pdecl) with inspect (reduce_to_ind hΣ Γ (infer Γ c _) _) :=
          { | ret (Checked indargs) => 
              let ty := snd pdecl in
              ret (subst0 (c :: List.rev (indargs.π2.π2.π1)) (subst_instance_constr indargs.π2.π1 ty));
            | ret (TypeError _) => ! };
         | ret None => ! };
        | ret (TypeError e) => ! };

    infer Γ (tFix mfix n) wt with inspect (nth_error mfix n) :=
      { | ret (Some f) => ret f.(dtype);
        | ret None => ! };

    infer Γ (tCoFix mfix n) wt with inspect (nth_error mfix n) :=
      { | ret (Some f) => ret f.(dtype);
        | ret None => ! }
  }.
  Proof.
    all:try clear infer.
    all:destruct hΣ, Hφ; destruct wt as [T HT].
    all:try solve [econstructor; eauto].

    - sq. destruct (nth_error Γ n) eqn:hnth => //.
      eapply inversion_Rel in HT as (? & ? & ? & ?); auto.
      rewrite e in hnth; noconf hnth. noconf wildcard0.
      split; [now constructor|].
      intros T' Ht'.
      eapply inversion_Rel in Ht' as (? & ? & ? & ?); auto.
      now rewrite e in e0; noconf e0.
      
    - eapply inversion_Rel in HT as (? & ? & ? & ?); auto.
      rewrite e in wildcard => //.
     
    - depind HT. eapply IHHT1; eauto.

    - depind HT; eapply IHHT1; eauto.

    - eapply inversion_Sort in HT as (wfΓ & wf & cum); auto.
      sq.
      split. econstructor; eauto.
      intros T' (wfΓ'' & wf' & cum')%inversion_Sort; auto.
            
    (*- eapply inversion_Prod in HT as (? & ? & ? & ? & ?); try econstructor; eauto.

    - destruct hΣ. destruct Hφ. destruct (inversion_Prod Σ w HT) as (? & ? & ? & ? & ?); try econstructor; eauto.*)

    - simpl in *.
      destruct (inversion_Prod Σ w HT) as (? & ? & ? & ? & ?).
      subst ty1 s1.
      destruct infer_as_sort as [x1 [[Hx1 Hx1p]]]; simpl.
      destruct infer_as_sort as [x2 [[Hx2 Hx2p]]]; simpl.
      subst s2; simpl in *. sq.
      split.
      * specialize (Hx1p _ t0).
        specialize (Hx2p _ t).
        econstructor; eauto.
      * intros T' Ht'.
        eapply inversion_Prod in Ht' as (? & ? & ? & ? & ?); auto.
        etransitivity; eauto. constructor. constructor.
        eapply leq_universe_product_mon; eauto.

    - simpl in t2. destruct (inversion_Lambda Σ w HT) as (? & ? & ? & ? & ?).
      destruct infer as [bty' [[Hbty pbty]]]; subst t2; simpl in *.
      sq. split.
      * econstructor; eauto.
      * intros T' (? & ? & ? & ? & ?)%inversion_Lambda; auto.
        specialize (pbty _ t3).
        transitivity (tProd n t x2); eauto.
        eapply congr_cumul_prod; auto.

    - simpl in b'_ty.
      destruct (inversion_LetIn Σ w HT) as (? & ? & ? & ? & ? & ?).
      destruct infer as [bty' [[Hbty pbty]]]; subst b'_ty; simpl in *.
      sq; split.
      * econstructor; eauto.
      * intros T' (? & ? & ? & ? & ? & ?)%inversion_LetIn; auto.
        etransitivity; eauto.
        eapply cumul_LetIn_bo; eauto.

    - eapply inversion_App in HT as (? & ? & ? & ? & ?); try econstructor; eauto.

    - simpl in ty. destruct inversion_App as (? & ? & ? & ? & ? & ?).
      destruct infer as [bty' [[Hbty pbty]]]; subst ty; simpl in *.
      apply wat_welltyped; auto.
      sq.
      eapply validity_term; eauto.
    - simpl in ty. destruct inversion_App as (? & ? & ? & ? & ? & ?).
      destruct infer as [bty' [[Hbty pbty]]]; subst ty; simpl in *.
      sq. exists x, x0, x1. now eapply pbty.
      
    - simpl in *. destruct inversion_App as (? & ? & ? & ? & ? & ?).
      destruct infer as [tty [[Htty pbty]]]; subst ty; simpl in *.
      destruct pi as [na' [A' [B' [red]]]].
      sq. split.
      * simpl.
        eapply type_reduction in Htty; eauto.
        eapply type_App; eauto.
        specialize (pbty _ t0).
        assert (Σ ;;; Γ |- tProd na' A' B' <= tProd x x0 x1).
        eapply cumul_red_l_inv; eauto.
        eapply cumul_Prod_Prod_inv in X as [_ [Ha _]]; auto.
        eapply type_Cumul'; eauto.
        eapply validity in Htty; auto.
        eapply isType_tProd in Htty; pcuic.
        eapply conv_cumul. now symmetry.
      * intros T' (? & ? & ? & ? & ? & ?)%inversion_App; auto.
        specialize (pbty _ t2). simpl.
        etransitivity; [|eassumption].
        assert (Σ ;;; Γ |- tProd na' A' B' <= tProd x2 x3 x4).
        { eapply cumul_red_l_inv; eauto. }
        eapply cumul_Prod_Prod_inv in X as [eqann [Ha Hb]]; auto.
        eapply (substitution_cumul _ Γ [vass x2 x3] []); eauto.
        eapply validity in t2; pcuic.
        eapply isType_tProd in t2 as [_ ist]; auto.
        now eapply isType_wf_local in ist. pcuic.
        constructor. constructor.
        now rewrite subst_empty.

    - eapply inversion_Const in HT as [decl ?] => //.
      intuition auto. rewrite a0 in wildcard. noconf wildcard.
      sq. split.
      * constructor; eauto.
      * intros T' [decl [wf [lookup [cu cum]]]]%inversion_Const; auto.
        red in lookup. congruence.
    - apply inversion_Const in HT as [decl [wf [lookup [cu cum]]]]; auto.
      red in lookup. subst wildcard0. rewrite lookup in e. congruence.
    - apply inversion_Const in HT as [decl [wf [lookup [cu cum]]]]; auto.
      red in lookup. subst wildcard0. rewrite lookup in e. congruence.

    - destruct decl as [decl [body decli]].
      eapply inversion_Ind in HT; auto.
      dependent elimination HT as [(mdecl; idecl; (wf'', (decli', (rest, cum))))].
      pose proof (declared_inductive_inj decli decli') as [-> ->].
      sq. split.
      * econstructor; eauto.
      * intros T' HT'.
        eapply inversion_Ind in HT'; auto.
        dependent elimination HT' as [(mdecl'; idecl'; (wf''', (decli'', (rest', cum'))))].
        simpl.
        now destruct (declared_inductive_inj decli decli'') as [-> ->].
    - eapply inversion_Ind in HT; auto.
      dependent elimination HT as [(mdecl; idecl; (wf'', (decli', (rest, cum))))].
      move: wildcard0. destruct decli' as [look hnth].
      move=> looki.
      eapply lookup_ind_decl_complete. now symmetry.
      exists mdecl, idecl. split; auto.

    - destruct d as [decl [body decli]].
      assert (declared_constructor Σ decl body (ind, k) cdecl) as declc.
      { red; intuition auto. }
      eapply inversion_Construct in HT; auto.
      dependent elimination HT as [(mdecl; idecl; cdecl; (wf'', (declc', (rest, cum))))].
      pose proof (declared_constructor_inj declc declc') as [-> [-> ->]].
      sq. split.
      * econstructor; eauto.
      * intros T' HT'.
        eapply inversion_Construct in HT'; auto.
        dependent elimination HT' as [(mdecl'; idecl'; cdecl'; (wf''', (declc'', (rest', cum'))))].
        simpl.
        now destruct (declared_constructor_inj declc declc'') as [-> [-> ->]].
    - eapply inversion_Construct in HT; auto.
      dependent elimination HT as [(mdecl; idecl; cdecl'; (wf'', (declc'', (rest, cum))))].
      destruct declc''.
      destruct d as [decl [body decli]].
      pose proof (declared_inductive_inj decli H0) as [-> ->]. simpl in *. congruence.
    
    - symmetry in wildcard2.
      eapply inversion_Construct in HT; auto.
      dependent elimination HT as [(mdecl; idecl; cdecl; (wf'', (declc', (rest, cum))))].
      eapply lookup_ind_decl_complete in wildcard2; eauto.
      now destruct declc'.
    
    - eapply inversion_Case in HT; auto.
      destruct HT as (u & args & mdecl & idecl & ps & pty & btys & decli & indp & bcp & Hpty & lebs
        & isco & Hc & Hbtys & all & cum).
      eexists; eauto.
    - simpl. destruct inversion_Case as (u & args & mdecl & idecl & ps & pty & btys & decli & indp & bcp & Hpty & lebs
        & isco & Hc & Hbtys & all & cum).
      destruct infer as [cty [[Hty Hp]]]. simpl.
      eapply validity in Hty.
      eapply wat_welltyped; auto. sq; auto. auto.
    - simpl in *.
      destruct inversion_Case as (u & args & mdecl & idecl & ps & pty & btys & decli & indp & bcp & Hpty & lebs
        & isco & Hc & Hbtys & all & cum).
      destruct infer as [cty [[Hty Hp]]].
      simpl in wildcard. destruct reduce_to_ind => //.
      injection wildcard. intros ->. clear wildcard.
      destruct a as [i [u' [l [red]]]].
      simpl.
      eapply type_reduction in Hty; eauto.
      pose proof (Hp _ Hc).
      assert (Σ ;;; Γ |- mkApps (tInd i u') l <= mkApps (tInd ind u) args).
      { eapply cumul_red_l_inv; eauto. }
      eapply cumul_Ind_Ind_inv in X0 as [[eqi Ru] cl]; auto.
      sq; split; simpl.
      * pose proof (Reflect.eqb_eq i ind eqi) as ->.
        simpl in *. subst par.
        pose proof (validity_term _ Hc).
        eapply (isType_mkApps_Ind w decli) in X0 as [parsubst [argsubst [[sppars spargs] cu]]]; pcuic.
        pose proof (PCUICContexts.context_subst_length2 sppars).
        len in H.
        set (oib := (on_declared_inductive w decli).2) in *.
        eapply type_Cumul'. econstructor; eauto.
        assert (Σ ;;; Γ |- c : mkApps (tInd ind u) (firstn (ind_npars mdecl) args ++  skipn (ind_npars mdecl) l)).
        { eapply type_Cumul'. eauto.
          + exists (subst_instance_univ u (ind_sort oib)).
            eapply type_mkApps. econstructor; pcuic.
            eapply wf_arity_spine_typing_spine; eauto.
            constructor. 
            unshelve epose proof (on_inductive_inst _ _ _ _ _ _ w ltac:(pcuic) _ _ oib cu); eauto.
            eapply on_declared_inductive; eauto.
            rewrite oib.(ind_arity_eq) -it_mkProd_or_LetIn_app subst_instance_constr_it_mkProd_or_LetIn.
            eapply isType_weaken; eauto. pcuic.
            rewrite oib.(ind_arity_eq) subst_instance_constr_it_mkProd_or_LetIn.
            eapply arity_spine_it_mkProd_or_LetIn; eauto.
            rewrite subst_instance_constr_it_mkProd_or_LetIn subst_it_mkProd_or_LetIn.
            simpl. rewrite -(app_nil_r (skipn _ _)).
            eapply arity_spine_it_mkProd_or_LetIn_smash; eauto.
            2:{ simpl. constructor; auto. }
            eapply validity_term in Hty; eauto.
            unshelve epose proof (isType_mkApps_Ind w decli _ Hty) as [parsubst' [argsubst' [[spars' spargs'] ?]]]; pcuic.
            eapply (subslet_cumul _ _ _ (smash_context [] (subst_context parsubst' 0 
              (subst_instance_context u' (ind_indices oib))))); pcuic.
            eapply wf_local_smash_end; eauto. eapply spargs'.
            eapply wf_local_smash_end; eauto. eapply spargs.  
            eapply inductive_cumulative_indices; eauto.
            destruct decli as [declm ?]. 
            apply (weaken_lookup_on_global_env' _ _ _ w declm).
            now eapply All2_firstn.
            eapply spine_subst_smash in spargs'.
            eapply spargs'. auto.

          + transitivity (mkApps (tInd ind u) l).
            constructor. eapply PCUICEquality.eq_term_upto_univ_napp_mkApps.
            now rewrite Nat.add_0_r; constructor.
            eapply All2_refl. intros. reflexivity. 
            rewrite -{1}(firstn_skipn (ind_npars mdecl) l). eapply conv_cumul, mkApps_conv_args; auto.
            eapply All2_app. now eapply All2_firstn. eapply All2_refl; eauto. }
        exists ps.
        eapply type_mkApps; eauto.
        eapply wf_arity_spine_typing_spine; eauto.
        split. now eapply validity in Hpty.
        pose proof (validity_term w X0) as vt; auto.
        eapply (build_case_predicate_type_spec _ _ _ _ _ _ _ _ oib) in bcp as [parsubst' [csubst ->]]; auto.
        pose proof (PCUICContexts.context_subst_fun sppars csubst). subst parsubst'.
        unshelve epose proof (isType_mkApps_Ind w decli _ vt) as [parsubst' [argsubst' [[spars' spargs'] ?]]]; pcuic.
        change (ind_indices (on_declared_inductive w decli).2) with (ind_indices oib) in spargs'.
        subst oib; destruct on_declared_inductive as [onmind oib].
        rewrite onmind.(onNpars) in H.
        pose proof (firstn_length_le_inv _ _ H).
        pose proof (subslet_length spargs'). len in H1.
        rewrite skipn_all_app_eq in spargs'. now rewrite H.
        rewrite (firstn_app_left _ 0) in spars'; try lia.
        simpl in spars'. rewrite app_nil_r in spars'.
        pose proof (PCUICContexts.context_subst_fun spars' csubst). subst parsubst'.
        eapply PCUICSpine.arity_spine_it_mkProd_or_LetIn; eauto.
        + simpl.
          econstructor. 2:constructor.
          rewrite subst_mkApps /= map_app.
          rewrite -H1.
          rewrite map_map_compose map_subst_lift_id.
          relativize (to_extended_list _).
          erewrite (spine_subst_subst_to_extended_list_k spargs').
          2:{ rewrite to_extended_list_k_subst. simpl. 
              eapply PCUICSubstitution.map_subst_instance_constr_to_extended_list_k. }
          assumption.
        + simpl.
          eapply conv_cumul.
          eapply mkApps_conv_args; auto.
          eapply All2_app. 2:repeat (constructor; auto).
          eapply All2_skipn. now symmetry in cl.
      * intros T'' Hc'.
        eapply inversion_Case in Hc' as (u'' & args' & mdecl' & idecl' & ps' & pty'
           & btys' & decli' & indp' & bcp' & Hpty' & lebs' & isco' & Hc' & Hbtys' & all' & cum'); auto.
        etransitivity. simpl in cum'. 2:eassumption.
        eapply conv_cumul, mkApps_conv_args; auto.
        eapply All2_app. 2:repeat (constructor; auto).
        eapply All2_skipn.
        specialize (Hp _ Hc').
        assert (Σ ;;; Γ |- mkApps (tInd i u') l <= mkApps (tInd ind u'') args').
        { eapply cumul_red_l_inv; eauto. }
        eapply cumul_Ind_Ind_inv in X0 as [[eqi' Ru'] cl']; auto.
      
    - simpl in wildcard1.
      destruct inversion_Case as (u & args & mdecl & idecl & ps & pty & btys & decli & indp & bcp & Hpty & lebs
        & isco & Hc & Hbtys & all & cum).
      destruct infer as [cty [[Hty Hp]]]. simpl.
      destruct validity as [_ i]. simpl in wildcard1.
      specialize (Hp _ Hc).
      eapply invert_cumul_ind_r in Hp as [ui' [l' [red [Ru ca]]]]; auto.
      symmetry in wildcard1; eapply reduce_to_ind_complete in wildcard1 => //.
      eauto.

    - eapply inversion_Proj in HT as (u & mdecl & idecl & pdecl' & args & declp & Hc & Hargs & cum); auto.
      simpl in cum.
      eexists; eauto.
    - simpl; destruct inversion_Proj as (u & mdecl & idecl & pdecl' & args & declp & Hc & Hargs & cum); auto.
      destruct infer as [cty [[Hc' Hc'']]]. simpl.
      eapply validity in Hc'; auto.
      eapply wat_welltyped; auto. sq; auto.
    - simpl in *. destruct inversion_Proj as (u & mdecl & idecl & pdecl' & args & declp & Hc & Hargs & cum); auto.
      destruct infer as [cty [[Hc' Hc'']]]. simpl.
      destruct reduce_to_ind => //. injection wildcard1. intros ->.
      clear wildcard1.
      destruct a as [i [u' [l [red]]]]. simpl.
      simpl in red.
      eapply type_reduction in Hc'; eauto.
      pose proof (Hc'' _ Hc).
      assert (Σ ;;; Γ |- mkApps (tInd i u') l <= mkApps (tInd ind u) args).
      { eapply cumul_red_l_inv; eauto. }
      eapply cumul_Ind_Ind_inv in X0 as [[eqi' Ru'] cl']; eauto.
      destruct d as [decl [body decli]].
      pose proof (declared_inductive_inj (proj1 declp) decli) as [-> ->].
      assert (declared_projection Σ mdecl idecl (ind, n, k) pdecl).
      { red; intuition eauto. simpl. eapply declp. }
      pose proof (@Reflect.eqb_eq inductive _). apply H0 in eqi'. subst ind.
      destruct (declared_projection_inj declp H) as [_ [_ ->]].
      sq. split; auto.
      * econstructor; eauto. now rewrite (All2_length _ _ cl').
      * intros.
        eapply inversion_Proj in X0 as (u'' & mdecl' & idecl' & pdecl'' & args' & 
            declp' & Hc''' & Hargs' & cum'); auto.
        simpl in *. subst ty.
        destruct (declared_projection_inj H declp') as [-> [-> ->]].
        etransitivity; eauto.
        specialize (Hc'' _ Hc''').
        assert (Σ ;;; Γ |- mkApps (tInd i u') l <= mkApps (tInd i u'') args').
        { eapply cumul_red_l_inv; eauto. }
        eapply cumul_Ind_Ind_inv in X0 as [[eqi'' Ru''] cl'']; auto.
        assert (consistent_instance_ext Σ (ind_universes mdecl) u').
        { eapply validity in Hc'; eauto.
          destruct Hc' as [s Hs].
          eapply invert_type_mkApps_ind in Hs. intuition eauto. all:auto. eapply declp. }
        assert (consistent_instance_ext Σ (ind_universes mdecl) u'').
          { eapply validity in Hc'''; eauto.
            destruct Hc''' as [s Hs]; auto.
            eapply invert_type_mkApps_ind in Hs. intuition eauto. all:auto. eapply declp. }
        transitivity (subst0 (c :: List.rev l) (subst_instance_constr u'' pdecl''.2)); cycle 1.
        eapply conv_cumul.
        eapply (subst_conv _ (projection_context mdecl idecl i u')
        (projection_context mdecl idecl i u'') []); auto.
        eapply (projection_subslet _ _ _ _ _ _ (i, n, k)); eauto.
        simpl. eapply validity; eauto.
        eapply (projection_subslet _ _ _ _ _ _ (i, n, k)); eauto.
        simpl. eapply validity; eauto.
        constructor; auto. now apply All2_rev.
        eapply PCUICWeakening.weaken_wf_local; eauto.
        eapply PCUICWeakening.weaken_wf_local; pcuic.
        eapply (wf_projection_context _ (p:= (i, n, k))); pcuic.
        eapply (substitution_cumul _ Γ (projection_context mdecl idecl i u') []); auto.
        eapply PCUICWeakening.weaken_wf_local; pcuic.
        eapply PCUICWeakening.weaken_wf_local; pcuic.
        eapply (wf_projection_context _ (p:=(i, n, k))); pcuic.
        eapply (projection_subslet _ _ _ _ _ _ (i, n, k)); eauto.
        simpl. eapply validity; eauto.
        rewrite -(All2_length _ _ cl'') in Hargs'. rewrite Hargs' in Ru''.
        unshelve epose proof (projection_cumulative_indices w declp _ H1 H2 Ru'').
        { eapply (PCUICWeakeningEnv.weaken_lookup_on_global_env' _ _ _ w (proj1 (proj1 declp))). }
        eapply PCUICWeakeningEnv.on_declared_projection in declp; eauto.
        eapply weaken_cumul in X0; eauto.
        eapply PCUICClosed.closed_wf_local; eauto.
        eapply (wf_projection_context _ (p:= (i, n, k))); pcuic.
        len. simpl. len. simpl.
        rewrite declp.(onNpars).
        rewrite PCUICClosed.closedn_subst_instance_constr.
        now apply (PCUICClosed.declared_projection_closed w declp').
        simpl; len. rewrite declp.(onNpars).
        rewrite PCUICClosed.closedn_subst_instance_constr.
        now apply (PCUICClosed.declared_projection_closed w declp').

    - simpl in *.
      destruct inversion_Proj as (u & mdecl & idecl & pdecl' & args & declp & Hc & Hargs & cum); auto.
      destruct infer as [cty [[Hc' Hc'']]]. simpl.
      symmetry in wildcard3.
      pose proof (reduce_to_ind_complete _ _ _ _ _ wildcard3).
      clear wildcard3; simpl. specialize (Hc'' _ Hc) as typ.
      eapply invert_cumul_ind_r in typ as [ui' [l' [red [Rgl Ra]]]]; auto.
      eauto.

    - eapply inversion_Proj in HT as (u & mdecl & idecl & pdecl' & args & declp & Hc & Hargs & cum); auto.
      destruct declp; simpl in *.
      destruct d as [decl [body decli]].
      destruct (declared_inductive_inj decli H0) as [-> ->].
      simpl in *. intuition congruence.

    - eapply inversion_Proj in HT as (u & mdecl & idecl & pdecl' & args & declp & Hc & Hargs & cum); auto.
      symmetry in wildcard5.
      eapply lookup_ind_decl_complete in wildcard5; auto.
      destruct declp. do 2 eexists; eauto.
    
    - eapply inversion_Fix in HT as [decl [fg [hnth [htys [hbods [wf cum]]]]]]; auto.
      sq; split.
      * econstructor; eauto.
        eapply nth_error_all in htys; eauto. destruct htys as [s Hs]. pcuic.
      * intros T' HT'.
        eapply inversion_Fix in HT' as [decl' [fg' [hnth' [htys' [hbods' [wf' cum']]]]]]; auto.
        congruence.
      
    - now eapply inversion_Fix in HT as [decl [fg [hnth [htys [hbods [wf cum]]]]]]; auto.

    - eapply inversion_CoFix in HT as [decl [fg [hnth [htys [hbods [wf cum]]]]]]; auto.
      sq; split.
      * econstructor; eauto.
        eapply nth_error_all in htys; eauto. destruct htys as [s Hs]. pcuic.
      * intros T' HT'.
        eapply inversion_CoFix in HT' as [decl' [fg' [hnth' [htys' [hbods' [wf' cum']]]]]]; auto.
        congruence.
      
    - now eapply inversion_CoFix in HT as [decl [fg [hnth [htys [hbods [wf cum]]]]]]; auto.
  Defined.

  Definition type_of Γ t wt : term := (infer Γ t wt).
  
  Open Scope type_scope.
  
  Definition map_typing_result {A B} (f : A -> B) (e : typing_result A) : typing_result B :=
    match e with
    | Checked a => Checked (f a)
    | TypeError e => TypeError e
    end.

  Arguments iswelltyped {cf Σ Γ t A}.

  Lemma infer_clause_1_irrel Γ n H wt wt' : infer_clause_1 infer Γ n H wt = infer_clause_1 infer Γ n H wt' :> term.
  Proof.
    destruct H as [[b|] eq]; simp infer. simpl. reflexivity. bang.
  Qed.

  (* Lemma infer_irrel {Γ t} (wt wt' : welltyped Σ Γ t) : infer Γ t wt = infer Γ t wt' :> term.
  Proof.
    funelim (infer Γ t wt); try solve [simp infer; simpl; try bang; auto].

    simp infer. simpl. f_equal. 
    simp infer. simpl. f_equal. apply H.
    simp infer; simpl; f_equal. apply H.
    simp infer. simpl. 
    simp infer. eapply infer_clause_1_irrel. revert Heqcall. bang.
  Qed.*)

  Lemma type_of_subtype {Γ t T} (wt : Σ ;;; Γ |- t : T) :
    ∥ Σ ;;; Γ |- type_of Γ t (iswelltyped wt) <= T ∥.
  Proof.
    unfold type_of.
    destruct infer as [P [[HP Hprinc]]].
    sq. simpl. now eapply Hprinc.
  Qed.

  (* Note the careful use of squashing here: the principal type is accessible 
    computationally but the proof it is principal is squashed (in Prop).
    The [PCUICPrincipality.principal_type] proof gives an unsquashed version of the
    same theorem. *)
  Theorem principal_types {Γ t} (wt : welltyped Σ Γ t) : 
    ∑ P, ∥ forall T, Σ ;;; Γ |- t : T -> (Σ ;;; Γ |- t : P) * (Σ ;;; Γ |- P <= T) ∥.
  Proof.
    exists (infer Γ t wt).
    destruct infer as [T' [[HT' HT]]].
    sq. intuition eauto.
  Qed.

End TypeOf.
