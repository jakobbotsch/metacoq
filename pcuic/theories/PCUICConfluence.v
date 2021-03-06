(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICRelations PCUICAst PCUICLiftSubst PCUICTyping
     PCUICReduction PCUICWeakening PCUICEquality PCUICUnivSubstitution
     PCUICParallelReduction PCUICParallelReductionConfluence.

Require Import ssreflect.
From Equations Require Import Equations.
Require Import CRelationClasses CMorphisms.
Require Import Equations.Prop.DepElim.
Require Import Equations.Type.Relation Equations.Type.Relation_Properties.


Ltac tc := try typeclasses eauto 10.

Lemma red1_eq_context_upto_l Σ Re Γ Δ u v :
  RelationClasses.Reflexive Re ->
  SubstUnivPreserving Re ->
  red1 Σ Γ u v ->
  eq_context_upto Σ Re Γ Δ ->
  ∑ v', red1 Σ Δ u v' *
        eq_term_upto_univ Σ Re Re v v'.
Proof.
  intros he he' h e.
  induction h in Δ, e |- * using red1_ind_all.
  all: try solve [
    eexists ; split ; [
      solve [ econstructor ; eauto ]
    | eapply eq_term_upto_univ_refl ; eauto
    ]
  ].
  all: try solve [
    destruct (IHh _ e) as [? [? ?]] ;
    eexists ; split ; [
      solve [ econstructor ; eauto ]
    | constructor; eauto ;
      eapply eq_term_upto_univ_refl ; eauto
    ]
  ].
  all: try solve [
    match goal with
    | r : red1 _ (?Γ ,, ?d) _ _ |- _ =>
      assert (e' : eq_context_upto Σ Re (Γ,, d) (Δ,, d)) ; [
        constructor ; eauto ;
        eapply eq_term_upto_univ_refl ; eauto
      |
      ]
    end ;
    destruct (IHh _ e') as [? [? ?]] ;
    eexists ; split ; [
      solve [ econstructor ; eauto ]
    | constructor ; eauto ;
      eapply eq_term_upto_univ_refl ; eauto
    ]
  ].
  - assert (h : ∑ b',
                (option_map decl_body (nth_error Δ i) = Some (Some b')) *
                eq_term_upto_univ Σ Re Re body b').
    { induction i in Γ, Δ, H, e |- *.
      - destruct e.
        + cbn in *. discriminate.
        + simpl in *. discriminate.
        + simpl in *. inversion H. subst. clear H.
          eexists. split ; try constructor; eauto.
      - destruct e.
        + cbn in *. discriminate.
        + simpl in *. eapply IHi in H ; eauto.
        + simpl in *. eapply IHi in H ; eauto.
    }
    destruct h as [b' [e1 e2]].
    eexists. split.
    + constructor. eassumption.
    + eapply eq_term_upto_univ_lift ; eauto.
  - destruct (IHh _ e) as [? [? ?]].
    eexists. split.
    + solve [ econstructor ; eauto ].
    + destruct ind.
      econstructor ; eauto.
      * eapply eq_term_upto_univ_refl ; eauto.
      * eapply All2_same.
        intros. split ; eauto.
        eapply eq_term_upto_univ_refl ; eauto.
  - destruct (IHh _ e) as [? [? ?]].
    eexists. split.
    + solve [ econstructor ; eauto ].
    + destruct ind.
      econstructor ; eauto.
      * eapply eq_term_upto_univ_refl ; eauto.
      * eapply All2_same.
        intros. split ; eauto.
        eapply eq_term_upto_univ_refl ; eauto.
  - destruct ind.
    assert (h : ∑ brs0,
      OnOne2 (on_Trel_eq (red1 Σ Δ) snd fst) brs brs0 *
      All2 (fun x y =>
                (fst x = fst y) *
                eq_term_upto_univ Σ Re Re (snd x) (snd y))%type
       brs' brs0
    ).
    { induction X.
      - destruct p0 as [[p1 p2] p3].
        eapply p2 in e as hh.
        destruct hh as [? [? ?]].
        eexists. split.
        + constructor.
          instantiate (1 := (_,_)).
          split ; eauto.
        + constructor.
          * split ; eauto.
          * eapply All2_same.
            intros. split ; eauto.
            eapply eq_term_upto_univ_refl ; eauto.
      - destruct IHX as [brs0 [? ?]].
        eexists. split.
        + eapply OnOne2_tl. eassumption.
        + constructor.
          * split ; eauto.
            eapply eq_term_upto_univ_refl ; eauto.
          * eassumption.
    }
    destruct h as [? [? ?]].
    eexists. split.
    + eapply case_red_brs. eassumption.
    + econstructor. all: try eapply eq_term_upto_univ_refl ; eauto.
  - destruct (IHh _ e) as [x [redl redr]].
    exists (tApp x M2).
    split. constructor; auto.
    constructor. eapply eq_term_upto_univ_impl. 5:eauto.
    all:auto. 1-3:typeclasses eauto.
    reflexivity.
  - assert (h : ∑ ll,
      OnOne2 (red1 Σ Δ) l ll *
      All2 (eq_term_upto_univ Σ Re Re) l' ll
    ).
    { induction X.
      - destruct p as [p1 p2].
        eapply p2 in e as hh. destruct hh as [? [? ?]].
        eexists. split.
        + constructor. eassumption.
        + constructor.
          * assumption.
          * eapply All2_same.
            intros.
            eapply eq_term_upto_univ_refl ; eauto.
      - destruct IHX as [ll [? ?]].
        eexists. split.
        + eapply OnOne2_tl. eassumption.
        + constructor ; eauto.
          eapply eq_term_upto_univ_refl ; eauto.
    }
    destruct h as [? [? ?]].
    eexists. split.
    + eapply evar_red. eassumption.
    + constructor. assumption.
  - assert (h : ∑ mfix',
      OnOne2 (fun d d' =>
          red1 Σ Δ d.(dtype) d'.(dtype) ×
          (d.(dname), d.(dbody), d.(rarg)) =
          (d'.(dname), d'.(dbody), d'.(rarg))
        ) mfix0 mfix'
      *
      All2 (fun x y =>
        eq_term_upto_univ Σ Re Re (dtype x) (dtype y) *
        eq_term_upto_univ Σ Re Re (dbody x) (dbody y) *
        (rarg x = rarg y))%type mfix1 mfix').
    { induction X.
      - destruct p as [[p1 p2] p3].
        eapply p2 in e as hh. destruct hh as [? [? ?]].
        eexists. split.
        + constructor.
          instantiate (1 := mkdef _ _ _ _ _).
          split ; eauto.
        + constructor.
          * simpl. repeat split ; eauto.
            eapply eq_term_upto_univ_refl ; eauto.
          * eapply All2_same.
            intros. repeat split ; eauto.
            all: eapply eq_term_upto_univ_refl ; eauto.
      - destruct IHX as [? [? ?]].
        eexists. split.
        + eapply OnOne2_tl. eassumption.
        + constructor ; eauto.
          repeat split ; eauto.
          all: eapply eq_term_upto_univ_refl ; eauto.
    }
    destruct h as [? [? ?]].
    eexists. split.
    + eapply fix_red_ty. eassumption.
    + constructor. assumption.
  - assert (h : ∑ mfix',
      OnOne2 (fun d d' =>
          red1 Σ (Δ ,,, fix_context mfix0) d.(dbody) d'.(dbody) ×
          (d.(dname), d.(dtype), d.(rarg)) =
          (d'.(dname), d'.(dtype), d'.(rarg))
        ) mfix0 mfix' *
      All2 (fun x y =>
        eq_term_upto_univ Σ Re Re (dtype x) (dtype y) *
        eq_term_upto_univ Σ Re Re (dbody x) (dbody y) *
        (rarg x = rarg y))%type mfix1 mfix').
    { (* Maybe we should use a lemma using firstn or skipn to keep
         fix_context intact. Anything general?
       *)
      Fail induction X using OnOne2_ind_l.
      (* This FAILs because it reduces the type of X before unifying
         unfortunately...
       *)
      change (
        OnOne2
      ((fun L (x y : def term) =>
       (red1 Σ (Γ ,,, fix_context L) (dbody x) (dbody y)
        × (forall Δ : context,
           eq_context_upto Σ Re (Γ ,,, fix_context L) Δ ->
           ∑ v' : term,
             red1 Σ Δ (dbody x) v' × eq_term_upto_univ Σ Re Re (dbody y) v'))
       × (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)) mfix0) mfix0 mfix1
      ) in X.
      Fail induction X using OnOne2_ind_l.
      revert mfix0 mfix1 X.
      refine (OnOne2_ind_l _ (fun (L : mfixpoint term) (x y : def term) =>
    ((red1 Σ (Γ ,,, fix_context L) (dbody x) (dbody y)
     × (forall Δ0 : context,
        eq_context_upto Σ Re (Γ ,,, fix_context L) Δ0 ->
        ∑ v' : term,
          red1 Σ Δ0 (dbody x) v' × eq_term_upto_univ Σ Re Re (dbody y) v'))
    × (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)))
  (fun L mfix0 mfix1 o => ∑ mfix' : list (def term),
  OnOne2
      (fun d d' : def term =>
       red1 Σ (Δ ,,, fix_context L) (dbody d) (dbody d')
       × (dname d, dtype d, rarg d) = (dname d', dtype d', rarg d')) mfix0 mfix'
    × All2
        (fun x y : def term =>
         (eq_term_upto_univ Σ Re Re (dtype x) (dtype y)
          × eq_term_upto_univ Σ Re Re (dbody x) (dbody y)) ×
         rarg x = rarg y) mfix1 mfix') _ _).
      - intros L x y l [[p1 p2] p3].
        assert (
           e' : eq_context_upto Σ Re (Γ ,,, fix_context L) (Δ ,,, fix_context L)
        ).
        { eapply eq_context_upto_cat ; eauto.
          eapply eq_context_upto_refl. assumption.
        }
        eapply p2 in e' as hh. destruct hh as [? [? ?]].
        eexists. constructor.
        + constructor.
          instantiate (1 := mkdef _ _ _ _ _).
          split ; eauto.
        + constructor.
          * simpl. repeat split ; eauto.
            eapply eq_term_upto_univ_refl ; eauto.
          * eapply All2_same. intros.
            repeat split ; eauto.
            all: eapply eq_term_upto_univ_refl ; eauto.
      - intros L x l l' h [? [? ?]].
        eexists. constructor.
        + eapply OnOne2_tl. eassumption.
        + constructor ; eauto.
          repeat split ; eauto.
          all: eapply eq_term_upto_univ_refl ; eauto.
    }
    destruct h as [? [? ?]].
    eexists. split.
    + eapply fix_red_body. eassumption.
    + constructor. assumption.
  - assert (h : ∑ mfix',
      OnOne2 (fun d d' =>
          red1 Σ Δ d.(dtype) d'.(dtype) ×
          (d.(dname), d.(dbody), d.(rarg)) =
          (d'.(dname), d'.(dbody), d'.(rarg))
        ) mfix0 mfix' *
      All2 (fun x y =>
        eq_term_upto_univ Σ Re Re (dtype x) (dtype y) *
        eq_term_upto_univ Σ Re Re (dbody x) (dbody y) *
        (rarg x = rarg y))%type mfix1 mfix'
    ).
    { induction X.
      - destruct p as [[p1 p2] p3].
        eapply p2 in e as hh. destruct hh as [? [? ?]].
        eexists. split.
        + constructor.
          instantiate (1 := mkdef _ _ _ _ _).
          split ; eauto.
        + constructor.
          * simpl. repeat split ; eauto.
            eapply eq_term_upto_univ_refl ; eauto.
          * eapply All2_same.
            intros. repeat split ; eauto.
            all: eapply eq_term_upto_univ_refl ; eauto.
      - destruct IHX as [? [? ?]].
        eexists. split.
        + eapply OnOne2_tl. eassumption.
        + constructor ; eauto.
          repeat split ; eauto.
          all: eapply eq_term_upto_univ_refl ; eauto.
    }
    destruct h as [? [? ?]].
    eexists. split.
    + eapply cofix_red_ty. eassumption.
    + constructor. assumption.
  - assert (h : ∑ mfix',
      OnOne2 (fun d d' =>
          red1 Σ (Δ ,,, fix_context mfix0) d.(dbody) d'.(dbody) ×
          (d.(dname), d.(dtype), d.(rarg)) =
          (d'.(dname), d'.(dtype), d'.(rarg))
        ) mfix0 mfix' *
      All2 (fun x y =>
        eq_term_upto_univ Σ Re Re (dtype x) (dtype y) *
        eq_term_upto_univ Σ Re Re (dbody x) (dbody y) *
        (rarg x = rarg y))%type mfix1 mfix').
    { (* Maybe we should use a lemma using firstn or skipn to keep
         fix_context intact. Anything general?
       *)
      Fail induction X using OnOne2_ind_l.
      (* This FAILs because it reduces the type of X before unifying
         unfortunately...
       *)
      change (
        OnOne2
      ((fun L (x y : def term) =>
       (red1 Σ (Γ ,,, fix_context L) (dbody x) (dbody y)
        × (forall Δ : context,
           eq_context_upto Σ Re (Γ ,,, fix_context L) Δ ->
           ∑ v' : term,
             red1 Σ Δ (dbody x) v' × eq_term_upto_univ Σ Re Re (dbody y) v' ))
       × (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)) mfix0) mfix0 mfix1
      ) in X.
      Fail induction X using OnOne2_ind_l.
      revert mfix0 mfix1 X.
      refine (OnOne2_ind_l _ (fun (L : mfixpoint term) (x y : def term) =>
    (red1 Σ (Γ ,,, fix_context L) (dbody x) (dbody y)
     × (forall Δ0 : context,
        eq_context_upto Σ Re (Γ ,,, fix_context L) Δ0 ->
        ∑ v' : term,
           red1 Σ Δ0 (dbody x) v' × eq_term_upto_univ Σ Re Re (dbody y) v' ))
    × (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)) (fun L mfix0 mfix1 o => ∑ mfix' : list (def term),
  (OnOne2
      (fun d d' : def term =>
       red1 Σ (Δ ,,, fix_context L) (dbody d) (dbody d')
       × (dname d, dtype d, rarg d) = (dname d', dtype d', rarg d')) mfix0 mfix'
    × All2
        (fun x y : def term =>
         (eq_term_upto_univ Σ Re Re (dtype x) (dtype y)
          × eq_term_upto_univ Σ Re Re (dbody x) (dbody y)) ×
         rarg x = rarg y) mfix1 mfix')) _ _).
      - intros L x y l [[p1 p2] p3].
        assert (
           e' : eq_context_upto Σ Re (Γ ,,, fix_context L) (Δ ,,, fix_context L)
        ).
        { eapply eq_context_upto_cat ; eauto.
          eapply eq_context_upto_refl. assumption.
        }
        eapply p2 in e' as hh. destruct hh as [? [? ?]].
        eexists. constructor.
        + constructor.
          instantiate (1 := mkdef _ _ _ _ _).
          split ; eauto.
        + constructor.
          * simpl. repeat split ; eauto.
            eapply eq_term_upto_univ_refl ; eauto.
          * eapply All2_same. intros.
            repeat split ; eauto.
            all: eapply eq_term_upto_univ_refl ; eauto.
      - intros L x l l' h [? [? ?]].
        eexists. constructor.
        + eapply OnOne2_tl. eassumption.
        + constructor ; eauto.
          repeat split ; eauto.
          all: eapply eq_term_upto_univ_refl ; eauto.
    }
    destruct h as [? [? ?]].
    eexists. split.
    + eapply cofix_red_body. eassumption.
    + constructor. assumption.
Qed.


Lemma red1_eq_term_upto_univ_l Σ Re Rle napp Γ u v u' :
  RelationClasses.Reflexive Re ->
  SubstUnivPreserving Re ->
  RelationClasses.Reflexive Rle ->
  RelationClasses.Transitive Re ->
  RelationClasses.Transitive Rle ->
  RelationClasses.subrelation Re Rle ->
  eq_term_upto_univ_napp Σ Re Rle napp u u' ->
  red1 Σ Γ u v ->
  ∑ v', red1 Σ Γ u' v' *
         eq_term_upto_univ_napp Σ Re Rle napp v v'.
Proof.
  unfold RelationClasses.subrelation.
  intros he he' hle tRe tRle hR e h.
  induction h in napp, u', e, tRle, Rle, hle, hR |- * using red1_ind_all.
  all: try solve [
    dependent destruction e ;
    edestruct IHh as [? [? ?]] ; [ .. | eassumption | ] ; eauto ;
    eexists ; split ; [
      solve [ econstructor ; eauto ]
    | constructor ; eauto
    ]
  ].
  (* tLambda and tProd *)
  10,13: solve [
    dependent destruction e ;
    edestruct IHh as [? [? ?]] ; [ .. | eassumption | ] ; eauto ;
    clear h ;
    lazymatch goal with
    | r : red1 _ (?Γ,, vass ?na ?A) ?u ?v,
      e :  eq_term_upto_univ_napp _ _ _ _ ?A ?B
      |- _ =>
      let hh := fresh "hh" in
      eapply red1_eq_context_upto_l in r as hh ; revgoals ; [
        eapply eq_context_vass (* with (nb := na) *) ; [
          eapply e
        | eapply eq_context_upto_refl ; eauto
        ]
      | assumption
      | assumption
      | destruct hh as [? [? ?]]
      ]
    end ;
    eexists ; split ; [
      solve [ econstructor ; eauto ]
    | constructor ; eauto ;
      eapply eq_term_upto_univ_trans ; eauto ;
      eapply eq_term_upto_univ_leq ; eauto
    ]
  ].
  - dependent destruction e. dependent destruction e1.
    eexists. split.
    + constructor.
    + eapply eq_term_upto_univ_substs ; eauto.
      eapply leq_term_leq_term_napp; eauto.
  - dependent destruction e.
    eexists. split.
    + constructor.
    + eapply eq_term_upto_univ_substs ; try assumption.
      eapply leq_term_leq_term_napp; eauto.
      auto.
  - dependent destruction e.
    eexists. split.
    + constructor. eassumption.
    + eapply eq_term_upto_univ_refl ; assumption.
  - dependent destruction e.
    apply eq_term_upto_univ_mkApps_l_inv in e2 as [? [? [[h1 h2] h3]]]. subst.
    dependent destruction h1.
    eexists. split.
    + constructor.
    + unfold iota_red. eapply eq_term_upto_univ_napp_mkApps.
      * simpl. eapply (eq_term_upto_univ_leq _ _ _ 0). auto. auto with arith.
        eapply All2_nth
          with (P := fun x y =>  eq_term_upto_univ Σ Re Re (snd x) (snd y)).
        -- solve_all.
        -- cbn. eapply eq_term_upto_univ_refl ; eauto.
      * eapply All2_skipn. assumption.
  - apply eq_term_upto_univ_napp_mkApps_l_inv in e as [? [? [[h1 h2] h3]]]. subst.
    dependent destruction h1.
    unfold unfold_fix in H.
    case_eq (nth_error mfix idx) ;
      try (intros e ; rewrite e in H ; discriminate H).
    intros d e. rewrite e in H. inversion H. subst. clear H.
    eapply All2_nth_error_Some in a as hh ; try eassumption.
    destruct hh as [d' [e' [[? ?] erarg]]].
    unfold is_constructor in H0.
    case_eq (nth_error args (rarg d)) ;
      try (intros bot ; rewrite bot in H0 ; discriminate H0).
    intros a' ea.
    rewrite ea in H0.
    eapply All2_nth_error_Some in ea as hh ; try eassumption.
    destruct hh as [a'' [ea' ?]].
    eexists. split.
    + eapply red_fix.
      * unfold unfold_fix. rewrite e'; eauto.
      * unfold is_constructor. rewrite <- erarg. rewrite ea'.
        eapply isConstruct_app_eq_term_l ; eassumption.
    + eapply eq_term_upto_univ_napp_mkApps.
      * eapply eq_term_upto_univ_substs ; eauto.
        -- eapply (eq_term_upto_univ_leq _ _ _ 0) ; eauto with arith. 
        -- unfold fix_subst.
           apply All2_length in a as el. rewrite <- el.
           generalize #|mfix|. intro n.
           induction n.
           ++ constructor.
           ++ constructor ; eauto.
              constructor. assumption.
      * assumption.
  - dependent destruction e.
    apply eq_term_upto_univ_mkApps_l_inv in e2 as [? [? [[h1 h2] h3]]]. subst.
    dependent destruction h1.
    unfold unfold_cofix in H.
    case_eq (nth_error mfix idx) ;
      try (intros e ; rewrite e in H ; discriminate H).
    intros d e. rewrite e in H. inversion H. subst. clear H.
    eapply All2_nth_error_Some in e as hh ; try eassumption.
    destruct hh as [d' [e' [[? ?] erarg]]].
    eexists. split.
    + eapply red_cofix_case.
      unfold unfold_cofix. rewrite e'. reflexivity.
    + constructor. all: eauto.
      eapply eq_term_upto_univ_mkApps. all: eauto.
      eapply eq_term_upto_univ_substs ; eauto; try exact _.
      eapply (eq_term_upto_univ_leq _ _ _ 0); auto with arith.
      typeclasses eauto.
      unfold cofix_subst.
      apply All2_length in a0 as el. rewrite <- el.
      generalize #|mfix|. intro n.
      induction n.
      * constructor.
      * constructor ; eauto.
        constructor. assumption.
  - dependent destruction e.
    apply eq_term_upto_univ_mkApps_l_inv in e as [? [? [[h1 h2] h3]]]. subst.
    dependent destruction h1.
    unfold unfold_cofix in H.
    case_eq (nth_error mfix idx) ;
      try (intros e ; rewrite e in H ; discriminate H).
    intros d e. rewrite e in H. inversion H. subst. clear H.
    eapply All2_nth_error_Some in e as hh ; try eassumption.
    destruct hh as [d' [e' [[? ?] erarg]]].
    eexists. split.
    + eapply red_cofix_proj.
      unfold unfold_cofix. rewrite e'. reflexivity.
    + constructor.
      eapply eq_term_upto_univ_mkApps. all: eauto.
      eapply eq_term_upto_univ_substs ; eauto; try exact _.
      eapply (eq_term_upto_univ_leq _ _ _ 0); auto with arith.
      typeclasses eauto.
      unfold cofix_subst.
      apply All2_length in a as el. rewrite <- el.
      generalize #|mfix|. intro n.
      induction n.
      * constructor.
      * constructor ; eauto.
        constructor. assumption.
  - dependent destruction e.
    eexists. split.
    + econstructor. all: eauto.
    + eapply (eq_term_upto_univ_leq _ _ _ 0); tas. auto. auto with arith.
      now apply eq_term_upto_univ_subst_instance_constr.
  - dependent destruction e.
    apply eq_term_upto_univ_mkApps_l_inv in e as [? [? [[h1 h2] h3]]]. subst.
    dependent destruction h1.
    eapply All2_nth_error_Some in h2 as hh ; try eassumption.
    destruct hh as [arg' [e' ?]].
    eexists. split.
    + constructor. eassumption.
    + eapply eq_term_upto_univ_leq ; eauto.
      eapply eq_term_eq_term_napp; auto. typeclasses eauto.
  - dependent destruction e.
    edestruct IHh as [? [? ?]] ; [ .. | eassumption | ] ; eauto.
    clear h.
    lazymatch goal with
    | r : red1 _ (?Γ,, vdef ?na ?a ?A) ?u ?v,
      e1 : eq_term_upto_univ _ _ _ ?A ?B,
      e2 : eq_term_upto_univ _ _ _ ?a ?b
      |- _ =>
      let hh := fresh "hh" in
      eapply red1_eq_context_upto_l in r as hh ; revgoals ; [
        eapply eq_context_vdef (* with (nb := na) *) ; [
          eapply e2
        | eapply e1
        | eapply eq_context_upto_refl ; eauto
        ]
      | assumption
      | assumption
      | destruct hh as [? [? ?]]
      ]
     end.
    eexists. split.
    + eapply letin_red_body ; eauto.
    + constructor ; eauto.
      eapply eq_term_upto_univ_trans ; eauto.
      eapply eq_term_upto_univ_leq ; eauto.
  - dependent destruction e.
    assert (h : ∑ brs0,
               OnOne2 (on_Trel_eq (red1 Σ Γ) snd fst) brs'0 brs0 *
               All2 (fun x y =>
                       (fst x = fst y) *
                       (eq_term_upto_univ Σ Re Re (snd x) (snd y))
                       )%type brs' brs0
           ).
    { induction X in a, brs'0 |- *.
      - destruct p0 as [[p1 p2] p3].
        dependent destruction a. destruct p0 as [h1 h2].
        eapply p2 in h2 as hh ; eauto.
        destruct hh as [? [? ?]].
        eexists. split.
        + constructor.
          instantiate (1 := (_, _)). cbn. split ; eauto.
        + constructor. all: eauto.
          split ; eauto. cbn. transitivity (fst hd) ; eauto.
      - dependent destruction a.
        destruct (IHX _ a) as [? [? ?]].
        eexists. split.
        + eapply OnOne2_tl. eassumption.
        + constructor. all: eauto.
    }
    destruct h as [brs0 [? ?]].
    eexists. split.
    + eapply case_red_brs. eassumption.
    + constructor. all: eauto.
  - dependent destruction e.
    assert (h : ∑ args,
               OnOne2 (red1 Σ Γ) args' args *
               All2 (eq_term_upto_univ Σ Re Re) l' args
           ).
    { induction X in a, args' |- *.
      - destruct p as [p1 p2].
        dependent destruction a.
        eapply p2 in e as hh ; eauto.
        destruct hh as [? [? ?]].
        eexists. split.
        + constructor. eassumption.
        + constructor. all: eauto.
      - dependent destruction a.
        destruct (IHX _ a) as [? [? ?]].
        eexists. split.
        + eapply OnOne2_tl. eassumption.
        + constructor. all: eauto.
    }
    destruct h as [? [? ?]].
    eexists. split.
    + eapply evar_red. eassumption.
    + constructor. all: eauto.
  - dependent destruction e.
    assert (h : ∑ mfix,
               OnOne2 (fun d0 d1 =>
                   red1 Σ Γ d0.(dtype) d1.(dtype) ×
                   (d0.(dname), d0.(dbody), d0.(rarg)) =
                   (d1.(dname), d1.(dbody), d1.(rarg))
                 ) mfix' mfix *
               All2 (fun x y =>
                 eq_term_upto_univ Σ Re Re x.(dtype) y.(dtype) *
                 eq_term_upto_univ Σ Re Re x.(dbody) y.(dbody) *
                 (x.(rarg) = y.(rarg)))%type mfix1 mfix
           ).
    { induction X in a, mfix' |- *.
      - destruct p as [[p1 p2] p3].
        dependent destruction a.
        destruct p as [[h1 h2] h3].
        eapply p2 in h1 as hh ; eauto.
        destruct hh as [? [? ?]].
        eexists. split.
        + constructor.
          instantiate (1 := mkdef _ _ _ _ _).
          simpl. eauto.
        + constructor. all: eauto.
          simpl. inversion p3.
          repeat split ; eauto.
      - dependent destruction a. destruct p as [[h1 h2] h3].
        destruct (IHX _ a) as [? [? ?]].
        eexists. split.
        + eapply OnOne2_tl. eassumption.
        + constructor. all: eauto.
    }
    destruct h as [? [? ?]].
    eexists. split.
    + eapply fix_red_ty. eassumption.
    + constructor. all: eauto.
  - dependent destruction e.
    assert (h : ∑ mfix,
               OnOne2 (fun x y =>
                   red1 Σ (Γ ,,, fix_context mfix0) x.(dbody) y.(dbody) ×
                   (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)
                 ) mfix' mfix *
               All2 (fun x y =>
                 eq_term_upto_univ Σ Re Re x.(dtype) y.(dtype) *
                 eq_term_upto_univ Σ Re Re x.(dbody) y.(dbody) *
                 (x.(rarg) = y.(rarg))
               ) mfix1 mfix
           ).
    { revert mfix' a.
      refine (OnOne2_ind_l _ (fun L x y => (red1 Σ (Γ ,,, fix_context L) (dbody x) (dbody y)
        × (forall Rle napp (u' : term),
           RelationClasses.Reflexive Rle ->
           RelationClasses.Transitive Rle ->
           (forall u u'0 : Universe.t, Re u u'0 -> Rle u u'0) ->
           eq_term_upto_univ_napp Σ Re Rle napp (dbody x) u' ->
           ∑ v' : term,
             red1 Σ (Γ ,,, fix_context L) u' v'
                  × eq_term_upto_univ_napp Σ Re Rle napp (dbody y) v' ))
       × (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)) (fun L mfix0 mfix1 o => forall mfix', All2
      (fun x y : def term =>
       (eq_term_upto_univ Σ Re Re (dtype x) (dtype y)
        × eq_term_upto_univ Σ Re Re (dbody x) (dbody y)) ×
       rarg x = rarg y) mfix0 mfix' -> ∑ mfix : list (def term),
  ( OnOne2
      (fun x y : def term =>
       red1 Σ (Γ ,,, fix_context L) (dbody x) (dbody y)
       × (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)) mfix' mfix ) *
  ( All2
      (fun x y : def term =>
       (eq_term_upto_univ Σ Re Re (dtype x) (dtype y)
        × eq_term_upto_univ Σ Re Re (dbody x) (dbody y)) ×
       rarg x = rarg y) mfix1 mfix )) _ _ _ _ X).
      - clear X. intros L x y l [[p1 p2] p3] mfix' h.
        dependent destruction h. destruct p as [[h1 h2] h3].
        eapply p2 in h2 as hh ; eauto.
        destruct hh as [? [? ?]].
        eexists. split.
        + constructor. constructor.
          instantiate (1 := mkdef _ _ _ _ _).
          simpl. eauto. reflexivity.
        + constructor. constructor; simpl. all: eauto.
          inversion p3.
          simpl. repeat split ; eauto. destruct y0. simpl in *.
          congruence.
      - clear X. intros L x l l' h ih mfix' ha.
        dependent destruction ha. destruct p as [[h1 h2] h3].
        destruct (ih _ ha) as [? [? ?]].
        eexists. split.
        + eapply OnOne2_tl. eauto.
        + constructor. constructor. all: eauto.
    }
    destruct h as [mfix [? ?]].
    assert (h : ∑ mfix,
      OnOne2 (fun x y =>
                  red1 Σ (Γ ,,, fix_context mfix') x.(dbody) y.(dbody) ×
                  (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)
               ) mfix' mfix ×
        All2 (fun x y =>
                eq_term_upto_univ Σ Re Re x.(dtype) y.(dtype) *
                eq_term_upto_univ Σ Re Re x.(dbody) y.(dbody) *
                (x.(rarg) = y.(rarg))
             ) mfix1 mfix %type
    ).
    { clear X.
      assert (hc : eq_context_upto Σ
                     Re
                     (Γ ,,, fix_context mfix0)
                     (Γ ,,, fix_context mfix')
             ).
      { eapply eq_context_upto_cat.
        - eapply eq_context_upto_refl. assumption.
        - clear - a. induction a.
          + constructor.
          + destruct r as [[? ?] ?].
            eapply All2_eq_context_upto.
            eapply All2_rev.
            eapply All2_mapi.
            constructor.
            * intros i. split.
              -- cbn. constructor.
              -- cbn. eapply eq_term_upto_univ_lift. eauto.
            * eapply All2_impl ; eauto.
              intros ? ? [[? ?] ?] i. split.
              -- cbn. constructor.
              -- cbn. eapply eq_term_upto_univ_lift. eauto.
      }
      clear a.
      eapply OnOne2_impl_exist_and_All ; try eassumption.
      clear o a0.
      intros x x' y [r e] [[? ?] ?].
      inversion e. clear e.
      eapply red1_eq_context_upto_l in r as [? [? ?]].
      3: eassumption. all: tea.
      eexists. constructor.
      instantiate (1 := mkdef _ _ _ _ _). simpl.
      intuition eauto.
      intuition eauto.
      - rewrite H1. eauto.
      - eapply eq_term_upto_univ_trans ; eassumption.
      - etransitivity ; eauto.
    }
    destruct h as [? [? ?]].
    eexists. split.
    +  eapply fix_red_body. eassumption.
    + constructor. all: eauto.
  - dependent destruction e.
    assert (h : ∑ mfix,
               OnOne2 (fun d0 d1 =>
                   red1 Σ Γ d0.(dtype) d1.(dtype) ×
                   (d0.(dname), d0.(dbody), d0.(rarg)) =
                   (d1.(dname), d1.(dbody), d1.(rarg))
                 ) mfix' mfix *
               All2 (fun x y =>
                 eq_term_upto_univ Σ Re Re x.(dtype) y.(dtype) *
                 eq_term_upto_univ Σ Re Re x.(dbody) y.(dbody) *
                 (x.(rarg) = y.(rarg)))%type mfix1 mfix
           ).
    { induction X in a, mfix' |- *.
      - destruct p as [[p1 p2] p3].
        dependent destruction a.
        destruct p as [[h1 h2] h3].
        eapply p2 in h1 as hh ; eauto.
        destruct hh as [? [? ?]].
        eexists. split.
        + constructor.
          instantiate (1 := mkdef _ _ _ _ _).
          simpl. eauto.
        + constructor. all: eauto.
          simpl. inversion p3.
          repeat split ; eauto.
      - dependent destruction a. destruct p as [[h1 h2] h3].
        destruct (IHX _ a) as [? [? ?]].
        eexists. split.
        + eapply OnOne2_tl. eassumption.
        + constructor. all: eauto.
    }
    destruct h as [? [? ?]].
    eexists. split.
    + eapply cofix_red_ty. eassumption.
    + constructor. all: eauto.
  - dependent destruction e.
    assert (h : ∑ mfix,
               OnOne2 (fun x y =>
                   red1 Σ (Γ ,,, fix_context mfix0) x.(dbody) y.(dbody) ×
                   (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)
                 ) mfix' mfix *
               All2 (fun x y =>
                 eq_term_upto_univ Σ Re Re x.(dtype) y.(dtype) *
                 eq_term_upto_univ Σ Re Re x.(dbody) y.(dbody) *
                 (x.(rarg) = y.(rarg))
               ) mfix1 mfix
           ).
    { revert mfix' a.
      refine (OnOne2_ind_l _ (fun L x y => (red1 Σ (Γ ,,, fix_context L) (dbody x) (dbody y)
        × (forall Rle napp (u' : term),
           RelationClasses.Reflexive Rle ->
           RelationClasses.Transitive Rle ->
           (forall u u'0 : Universe.t, Re u u'0 -> Rle u u'0) ->
           eq_term_upto_univ_napp Σ Re Rle napp (dbody x) u' ->
           ∑ v' : term,
             red1 Σ (Γ ,,, fix_context L) u' v'
               × eq_term_upto_univ_napp Σ Re Rle napp (dbody y) v'))
       × (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)) (fun L mfix0 mfix1 o => forall mfix', All2
      (fun x y : def term =>
       (eq_term_upto_univ Σ Re Re (dtype x) (dtype y)
        × eq_term_upto_univ Σ Re Re (dbody x) (dbody y)) ×
       rarg x = rarg y) mfix0 mfix' -> ∑ mfix : list (def term),
  ( OnOne2
      (fun x y : def term =>
       red1 Σ (Γ ,,, fix_context L) (dbody x) (dbody y)
       × (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)) mfix' mfix ) *
  ( All2
      (fun x y : def term =>
       (eq_term_upto_univ Σ Re Re (dtype x) (dtype y)
        × eq_term_upto_univ Σ Re Re (dbody x) (dbody y)) ×
       rarg x = rarg y) mfix1 mfix )) _ _ _ _ X).
      - clear X. intros L x y l [[p1 p2] p3] mfix' h.
        dependent destruction h. destruct p as [[h1 h2] h3].
        eapply p2 in h2 as hh ; eauto.
        destruct hh as [? [? ?]].
        noconf p3. hnf in H. noconf H.
        eexists. split; simpl.
        + constructor.
          instantiate (1 := mkdef _ _ _ _ _).
          simpl. eauto.
        + constructor. all: eauto.
          simpl. repeat split ; eauto; congruence.
      - clear X. intros L x l l' h ih mfix' ha.
        dependent destruction ha. destruct p as [[h1 h2] h3].
        destruct (ih _ ha) as [? [? ?]].
        eexists. split.
        + eapply OnOne2_tl. eauto.
        + constructor. all: eauto.
    }
    destruct h as [mfix [? ?]].
    assert (h : ∑ mfix,
      OnOne2 (fun x y =>
                  red1 Σ (Γ ,,, fix_context mfix') x.(dbody) y.(dbody) ×
                  (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)
               ) mfix' mfix ×
        All2 (fun x y =>
                eq_term_upto_univ Σ Re Re x.(dtype) y.(dtype) *
                eq_term_upto_univ Σ Re Re x.(dbody) y.(dbody) *
                (x.(rarg) = y.(rarg))
             ) mfix1 mfix
    ).
    { clear X.
      assert (hc : eq_context_upto Σ
                     Re
                     (Γ ,,, fix_context mfix0)
                     (Γ ,,, fix_context mfix')
             ).
      { eapply eq_context_upto_cat.
        - eapply eq_context_upto_refl. assumption.
        - clear - a. induction a.
          + constructor.
          + destruct r as [[? ?] ?].
            eapply All2_eq_context_upto.
            eapply All2_rev.
            eapply All2_mapi.
            constructor.
            * intros i. split.
              -- cbn. constructor.
              -- cbn. eapply eq_term_upto_univ_lift. eauto.
            * eapply All2_impl ; eauto.
              intros ? ? [[? ?] ?] i. split.
              -- cbn. constructor.
              -- cbn. eapply eq_term_upto_univ_lift. eauto.
      }
      clear a.
      eapply OnOne2_impl_exist_and_All ; try eassumption.
      clear o a0.
      intros x x' y [r e] [[? ?] ?].
      inversion e. clear e.
      eapply red1_eq_context_upto_l in r as [? [? ?]].
      3: eassumption. all: tea.
      eexists.
      instantiate (1 := mkdef _ _ _ _ _). simpl.
      intuition eauto.
      - rewrite H1. eauto.
      - eapply eq_term_upto_univ_trans ; eassumption.
      - etransitivity ; eauto.
    }
    destruct h as [? [? ?]].
    eexists. split.
    +  eapply cofix_red_body. eassumption.
    + constructor. all: eauto.
Qed.

Lemma red1_eq_context_upto_r Σ Re Γ Δ u v :
  RelationClasses.Reflexive Re ->
  RelationClasses.Symmetric Re ->
  SubstUnivPreserving Re ->
  red1 Σ Γ u v ->
  eq_context_upto Σ Re Δ Γ ->
  ∑ v', red1 Σ Δ u v' *
        eq_term_upto_univ Σ Re Re v' v.
Proof.
  intros.
  destruct (red1_eq_context_upto_l Σ Re Γ Δ u v); auto.
  now apply eq_context_upto_sym.
  exists x. intuition auto.
  now eapply eq_term_upto_univ_sym.
Qed.

Lemma red1_eq_term_upto_univ_r Σ Re Rle napp Γ u v u' :
  RelationClasses.Reflexive Re ->
  SubstUnivPreserving Re ->
  RelationClasses.Reflexive Rle ->
  RelationClasses.Symmetric Re ->
  RelationClasses.Transitive Re ->
  RelationClasses.Transitive Rle ->
  RelationClasses.subrelation Re Rle ->
  eq_term_upto_univ_napp Σ Re Rle napp u' u ->
  red1 Σ Γ u v ->
  ∑ v', red1 Σ Γ u' v' ×
        eq_term_upto_univ_napp Σ Re Rle napp v' v.
Proof.
  intros he he' hle tRe tRle hR e h uv.
  destruct (red1_eq_term_upto_univ_l Σ Re (flip Rle) napp Γ u v u'); auto.
  - now eapply flip_Transitive.
  - intros x y X. symmetry in X. apply e. auto.
  - eapply eq_term_upto_univ_napp_flip; eauto.
  - exists x. intuition auto.
    eapply (eq_term_upto_univ_napp_flip Σ Re (flip Rle) Rle); eauto.
    + now eapply flip_Transitive.
    + unfold flip. intros ? ? H. symmetry in H. eauto.
Qed.

Section RedEq.
  Context (Σ : global_env_ext).
  Context {Re Rle : Universe.t -> Universe.t -> Prop}
          {refl : RelationClasses.Reflexive Re}
          {refl': RelationClasses.Reflexive Rle}
          {pres : SubstUnivPreserving Re}
          {sym : RelationClasses.Symmetric Re}
          {trre : RelationClasses.Transitive Re}
          {trle : RelationClasses.Transitive Rle}.
  Context (inclre : RelationClasses.subrelation Re Rle).

  Lemma red_eq_term_upto_univ_r {Γ T V U} :
    eq_term_upto_univ Σ Re Rle T U -> red Σ Γ U V ->
    ∑ T', red Σ Γ T T' * eq_term_upto_univ Σ Re Rle T' V.
  Proof.
    intros eq r.
    induction r in T, eq |- *.
    - eapply red1_eq_term_upto_univ_r in eq as [v' [r' eq']]; eauto.
    - exists T; split; eauto.
    - case: (IHr1 _ eq) => T' [r' eq'].
      case: (IHr2 _ eq') => T'' [r'' eq''].
      exists T''. split=>//.
      now transitivity T'.
  Qed.

  Lemma red_eq_term_upto_univ_l {Γ u v u'} :
    eq_term_upto_univ Σ Re Rle u u' ->
    red Σ Γ u v ->
    ∑ v',
    red Σ Γ u' v' *
    eq_term_upto_univ Σ Re Rle v v'.
  Proof.
    intros eq r.
    induction r in u', eq |- *.
    - eapply red1_eq_term_upto_univ_l in eq as [v' [r' eq']]; eauto.
    - exists u'. split; auto.
    - case: (IHr1 _ eq) => T' [r' eq'].
      case: (IHr2 _ eq') => T'' [r'' eq''].
      exists T''. split=>//.
      now transitivity T'.
  Qed.
End RedEq.



Polymorphic Derive Signature for Relation.clos_refl_trans.

Derive Signature for red1.

Lemma local_env_telescope P Γ Γ' Δ Δ' :
  All2_telescope (on_decl P) Γ Γ' Δ Δ' ->
  All2_local_env_over P Γ Γ' (List.rev Δ) (List.rev Δ').
Proof.
  induction 1. simpl. constructor.
  - simpl. eapply All2_local_env_over_app. constructor. constructor.
    simpl. apply p.
    revert IHX.
    generalize (List.rev Δ) (List.rev Δ'). induction 1. constructor.
    constructor. auto. red in p0. red. red. red. red in p0.
    rewrite !app_context_assoc. cbn. apply p0.
    constructor. auto. destruct p0. unfold on_decl_over in *. simpl.
    rewrite !app_context_assoc. cbn. intuition.
  - simpl. eapply All2_local_env_over_app. constructor. constructor.
    simpl. unfold on_decl_over, on_decl in *. destruct p. split; intuition auto.
    revert IHX.
    generalize (List.rev Δ) (List.rev Δ'). induction 1. constructor.
    constructor. auto. red in p0. red. red. red. red in p0.
    rewrite !app_context_assoc. cbn. apply p0.
    constructor. auto. destruct p0. unfold on_decl_over in *. simpl.
    rewrite !app_context_assoc. cbn. intuition.
Qed.

Lemma All_All2_telescopei_gen P (Γ Γ' Δ Δ' : context) (m m' : mfixpoint term) :
  (forall Δ Δ' x y,
    All2_local_env_over P Γ Γ' Δ Δ' ->
    P Γ Γ' x y ->
    P (Γ ,,, Δ) (Γ' ,,, Δ') (lift0 #|Δ| x) (lift0 #|Δ'| y)) ->
  All2 (on_Trel_eq (P Γ Γ') dtype dname) m m' ->
  All2_local_env_over P Γ Γ' Δ Δ' ->
  All2_telescope_n (on_decl P) (fun n : nat => lift0 n)
                   (Γ ,,, Δ) (Γ' ,,, Δ') #|Δ|
    (map (fun def : def term => vass (dname def) (dtype def)) m)
    (map (fun def : def term => vass (dname def) (dtype def)) m').
Proof.
  intros weakP.
  induction 1 in Δ, Δ' |- *; cbn. constructor.
  intros. destruct r. rewrite e. constructor.
  red.
  rewrite {2}(All2_local_env_length X0).
  now eapply weakP.
  specialize (IHX (vass (dname y) (lift0 #|Δ| (dtype x)) :: Δ)
                  (vass (dname y) (lift0 #|Δ'| (dtype y)) :: Δ')).
  forward IHX.
  constructor; auto. now eapply weakP. simpl in IHX.
  rewrite {2}(All2_local_env_length X0).
  apply IHX.
Qed.

Lemma All_All2_telescopei P (Γ Γ' : context) (m m' : mfixpoint term) :
  (forall Δ Δ' x y,
    All2_local_env_over P Γ Γ' Δ Δ' ->
    P Γ Γ' x y ->
    P (Γ ,,, Δ) (Γ' ,,, Δ') (lift0 #|Δ| x) (lift0 #|Δ'| y)) ->
  All2 (on_Trel_eq (P Γ Γ') dtype dname) m m' ->
  All2_telescope_n (on_decl P) (fun n => lift0 n)
                   Γ Γ' 0
                   (map (fun def => vass (dname def) (dtype def)) m)
                   (map (fun def => vass (dname def) (dtype def)) m').
Proof.
  specialize (All_All2_telescopei_gen P Γ Γ' [] [] m m'). simpl.
  intros. specialize (X X0 X1). apply X; constructor.
Qed.

Lemma All2_All2_local_env_fix_context P (Γ Γ' : context) (m m' : mfixpoint term) :
  (forall Δ Δ' x y,
    All2_local_env_over P Γ Γ' Δ Δ' ->
    P Γ Γ' x y ->
    P (Γ ,,, Δ) (Γ' ,,, Δ') (lift0 #|Δ| x) (lift0 #|Δ'| y)) ->
  All2 (on_Trel_eq (P Γ Γ') dtype dname) m m' ->
  All2_local_env (on_decl (on_decl_over P Γ Γ')) (fix_context m) (fix_context m').
Proof.
  intros Hweak a. unfold fix_context.
  eapply local_env_telescope.
  cbn.
  rewrite - !(mapi_mapi
                (fun n def => vass (dname def) (dtype def))
                (fun n decl => lift_decl n 0 decl)).
  eapply All2_telescope_mapi.
  rewrite !mapi_cst_map.
  eapply All_All2_telescopei; eauto.
Qed.

Section RedPred.
  Context {cf : checker_flags}.
  Context {Σ : global_env}.
  Context (wfΣ : wf Σ).

  Hint Resolve pred1_ctx_over_refl : pcuic.
  Hint Unfold All2_prop2_eq : pcuic.
  Hint Transparent context : pcuic.
  Hint Transparent mfixpoint : pcuic.

  Hint Mode pred1 ! ! ! ! - : pcuic.

  Ltac pcuic := simpl; try typeclasses eauto with pcuic.

  (** Strong substitutivity gives context conversion of reduction!
      It cannot be strenghtened to deal with let-ins: pred1 is
      precisely not closed by arbitrary reductions in contexts with let-ins.
   *)

  Lemma pred1_ctx_pred1 Γ Γ' Δ Δ' t u :
    #|Γ| = #|Γ'| ->
    pred1 Σ (Γ ,,, Δ) (Γ' ,,, Δ) t u ->
    assumption_context Δ ->
    pred1_ctx Σ (Γ ,,, Δ) (Γ' ,,, Δ') ->
    pred1 Σ (Γ ,,, Δ) (Γ' ,,, Δ') t u.
  Proof.
    intros Hlen X H X0.
    pose proof (strong_substitutivity _ wfΣ _ _ (Γ ,,, Δ) (Γ' ,,, Δ') _ _ ids ids X).
    forward X1.
    { red. intros.
      destruct (leb_spec_Set (S x) #|Δ|).
      rewrite nth_error_app_lt in H0. lia.
      apply nth_error_assumption_context in H0 => //; rewrite H0 //.
      case e: (decl_body d) => [b|] //. eexists x, _; intuition eauto.
      rewrite H0. simpl. rewrite e. reflexivity. }
    forward X1.
    { red. intros.
      destruct (leb_spec_Set (S x) #|Δ|).
      rewrite nth_error_app_lt in H0. lia.
      apply nth_error_assumption_context in H0 => //; rewrite H0 //.
      case e: (decl_body d) => [b|] //. eexists x, _; intuition eauto.
      rewrite nth_error_app_ge in H0 |- *; try lia.
      eapply All2_local_env_app in X0 as [_ X0] => //.
      pose proof (All2_local_env_length X0).
      rewrite nth_error_app_ge. lia. now rewrite -H1 H0 /= e. }
    forward X1.
    red. intros x; split. eapply pred1_refl_gen; auto.
    destruct option_map as [[o|]|]; auto.
    now rewrite !subst_ids in X1.
  Qed.

  Lemma pred1_ctx_pred1_inv Γ Γ' Δ Δ' t u :
    #|Γ| = #|Γ'| ->
    pred1 Σ (Γ ,,, Δ) (Γ' ,,, Δ') t u ->
    assumption_context Δ ->
    assumption_context Δ' ->
    pred1_ctx Σ (Γ ,,, Δ) (Γ' ,,, Δ) ->
    pred1 Σ (Γ ,,, Δ) (Γ' ,,, Δ) t u.
  Proof.
    intros Hlen X H H' X0.
    assert(lenΔ : #|Δ| = #|Δ'|). 
    { eapply pred1_pred1_ctx in X. eapply All2_local_env_length in X.
      rewrite !app_context_length in X. lia. }
    pose proof (strong_substitutivity _ wfΣ _ _ (Γ ,,, Δ) (Γ' ,,, Δ) _ _ ids ids X).
    forward X1.
    { red. intros. simpl.
      destruct (leb_spec_Set (S x) #|Δ|).
      rewrite nth_error_app_lt in H0. lia.
      apply nth_error_assumption_context in H0 => //; rewrite H0 //.
      case e: (decl_body d) => [b|] //. eexists x, _; intuition eauto.
      rewrite nth_error_app_ge in H0. lia. rewrite nth_error_app_ge. lia.
      rewrite H0. simpl. rewrite e. reflexivity. }
    forward X1.
    { red. intros.
      destruct (leb_spec_Set (S x) #|Δ|).
      rewrite nth_error_app_lt in H0. lia.
      apply nth_error_assumption_context in H0 => //; rewrite H0 //.
      case e: (decl_body d) => [b|] //. eexists x, _; intuition eauto.
      rewrite nth_error_app_ge in H0 |- *; try lia.
      eapply All2_local_env_app in X0 as [_ X0] => //.
      pose proof (All2_local_env_length X0).
      rewrite nth_error_app_ge. lia. now rewrite lenΔ H0 /= e. }
    forward X1.
    red. intros x; split. eapply pred1_refl_gen; auto.
    destruct option_map as [[o|]|]; auto.
    now rewrite !subst_ids in X1.
  Qed.

  Ltac noconf H := repeat (DepElim.noconf H; simpl NoConfusion in * ).

  Lemma red1_pred1 Γ : forall M N, red1 Σ Γ M N -> pred1 Σ Γ Γ M N.
  Proof with pcuic.
    induction 1 using red1_ind_all; intros; pcuic.
    - constructor; pcuic.
      eapply OnOne2_All2 ...
    - constructor; pcuic.
      eapply OnOne2_All2...
    - constructor; pcuic.
      + apply All2_All2_local_env_fix_context.
        now intros; eapply weakening_pred1_pred1.
        (* Missing name equality *)
        eapply OnOne2_All2...
        intros.
        simpl in *. intuition auto. now noconf b.
      + eapply OnOne2_All2; pcuic; simpl;
        unfold on_Trel; simpl; intros; intuition auto.
        noconf b; noconf H. rewrite H0. pcuic.
        apply pred1_refl_gen.
        eapply All2_local_env_app_inv; pcuic.
        apply All2_All2_local_env_fix_context.
        now intros; eapply weakening_pred1_pred1.
        (* Missing name equality *)
        eapply OnOne2_All2...
        intros.
        intros. unfold on_Trel.
        simpl in *. intuition auto.
        congruence. congruence.

        pcuic.
        apply pred1_refl_gen; pcuic.
        eapply All2_local_env_app_inv; pcuic.
        apply All2_All2_local_env_fix_context.
        now intros; eapply weakening_pred1_pred1.
        (* Missing name equality *)
        eapply OnOne2_All2...
        intros.
        intros. unfold on_Trel.
        simpl in *. intuition auto. congruence.

    - constructor; pcuic.
      apply All2_All2_local_env_fix_context.
      now intros; eapply weakening_pred1_pred1.
      (* Missing name equality *)
      + eapply OnOne2_All2...
        intros.
        intros. unfold on_Trel.
        simpl in *. intuition auto. noconf b. noconf H.
        rewrite H0; pcuic. congruence.
      + eapply OnOne2_All2...
        intros.
        * intros. unfold on_Trel.
          simpl in *. intuition auto. noconf b. noconf H. rewrite H0. pcuic.
          assert(fix_context mfix0 = fix_context mfix1).
          clear -X.
          unfold fix_context, mapi. generalize 0 at 2 4.
          induction X; intros. intuition auto. simpl.
          noconf b. noconf H. now rewrite H H0.
          simpl; now rewrite IHX.
          now rewrite -H. congruence.
        * intros. unfold on_Trel.
          simpl in *. intuition pcuic.
          assert(fix_context mfix0 = fix_context mfix1).
          clear -X.
          unfold fix_context, mapi. generalize 0 at 2 4.
          induction X; intros. intuition auto. simpl.
          noconf b; noconf H. now rewrite H H0.
          simpl; now rewrite IHX.
          rewrite -H. pcuic.

    - constructor; pcuic.
      apply All2_All2_local_env_fix_context.
      now intros; eapply weakening_pred1_pred1.
      (* Missing name equality *)
      + eapply OnOne2_All2...
        intros.
        intros. unfold on_Trel.
        simpl in *. intuition auto. noconf b. noconf H.
        rewrite H; pcuic.
      + eapply OnOne2_All2...
        * unfold on_Trel.
          simpl in *. intuition pcuic. noconf b; noconf H.
          rewrite -H0; pcuic.
          eapply pred1_ctx_pred1; pcuic.
          apply fix_context_assumption_context.
          apply All2_local_env_over_app. pcuic.
          apply All2_All2_local_env_fix_context.
          now intros; eapply weakening_pred1_pred1.
          eapply OnOne2_All2...
          unfold on_Trel.
          simpl in *. intuition pcuic. congruence. congruence.
        * unfold on_Trel.
          simpl in *. intuition pcuic.
          eapply pred1_ctx_pred1; pcuic.
          apply fix_context_assumption_context.
          apply All2_local_env_over_app. pcuic.
          apply All2_All2_local_env_fix_context.
          now intros; eapply weakening_pred1_pred1.
          eapply OnOne2_All2...
          unfold on_Trel.
          simpl in *. intuition pcuic. congruence.

    - constructor; pcuic.
      apply All2_All2_local_env_fix_context.
      now intros; eapply weakening_pred1_pred1.
      + eapply OnOne2_All2...
        unfold on_Trel.
        simpl in *. intuition pcuic. noconf b; noconf H; rewrite H0; pcuic.
        congruence.
      + eapply OnOne2_All2...
        * unfold on_Trel.
          simpl in *. intuition pcuic. noconf b; noconf H; rewrite H0; pcuic.
          assert(fix_context mfix0 = fix_context mfix1).
          { clear -X.
            unfold fix_context, mapi. generalize 0 at 2 4.
            induction X; intros. intuition auto. simpl. noconf b; noconf H. congruence.
            simpl; now rewrite IHX. }
          now rewrite -H. congruence.
        * unfold on_Trel.
          simpl in *. intuition pcuic.
          eapply pred1_ctx_pred1; pcuic.
          apply fix_context_assumption_context.
          apply All2_local_env_over_app. pcuic.
          apply All2_All2_local_env_fix_context.
          now intros; eapply weakening_pred1_pred1.
          eapply OnOne2_All2...
          unfold on_Trel.
          simpl in *. intuition pcuic.
          noconf b; noconf H; rewrite H0; pcuic. congruence.
  Qed.

End RedPred.

Section PredRed.
  Context {cf : checker_flags}.
  Context {Σ : global_env}.
  Context (wfΣ : wf Σ).

  Lemma weakening_red_0 Γ Γ' M N n :
    n = #|Γ'| ->
    red Σ Γ M N ->
    red Σ (Γ ,,, Γ') (lift0 n M) (lift0 n N).
  Proof. now move=> ->; apply (weakening_red Σ Γ [] Γ'). Qed.

  Lemma red_abs_alt Γ na M M' N N' : red Σ Γ M M' -> red Σ (Γ ,, vass na M) N N' ->
                                 red Σ Γ (tLambda na M N) (tLambda na M' N').
  Proof.
    intros. eapply (transitivity (y := tLambda na M N')).
    now eapply (red_ctx (tCtxLambda_r _ _ tCtxHole)).
    now eapply (red_ctx (tCtxLambda_l _ tCtxHole _)).
  Qed.

  Lemma red_letin_alt Γ na d0 d1 t0 t1 b0 b1 :
    red Σ Γ d0 d1 -> red Σ Γ t0 t1 -> red Σ (Γ ,, vdef na d0 t0) b0 b1 ->
    red Σ Γ (tLetIn na d0 t0 b0) (tLetIn na d1 t1 b1).
  Proof.
    intros; eapply (transitivity (y := tLetIn na d0 t0 b1)).
    now eapply (red_ctx (tCtxLetIn_r _ _ _ tCtxHole)).
    eapply (transitivity (y := tLetIn na d0 t1 b1)).
    now eapply (red_ctx (tCtxLetIn_b _ _ tCtxHole _)).
    now apply (red_ctx (tCtxLetIn_l _ tCtxHole _ _)).
  Qed.

  Lemma red_prod_alt Γ na M M' N N' :
    red Σ Γ M M' -> red Σ (Γ ,, vass na M') N N' ->
    red Σ Γ (tProd na M N) (tProd na M' N').
  Proof.
    intros. eapply (transitivity (y := tProd na M' N)).
    now eapply (red_ctx (tCtxProd_l _ tCtxHole _)).
    now eapply (red_ctx (tCtxProd_r _ _ tCtxHole)).
  Qed.

  (** Parallel reduction is included in the reflexive transitive closure of 1-step reduction *)
  Lemma pred1_red Γ Γ' : forall M N, pred1 Σ Γ Γ' M N -> red Σ Γ M N.
  Proof.
    revert Γ Γ'. eapply (@pred1_ind_all_ctx Σ _
                                            (fun Γ Γ' =>
       All2_local_env (on_decl (fun Γ Γ' M N => pred1 Σ Γ Γ' M N -> red Σ Γ M N)) Γ Γ')%type);
                   intros; try reflexivity; pcuic.
    eapply All2_local_env_impl; eauto.
    - (* Contexts *)
      unfold on_decl => Δ Δ' t T U Hlen.
      destruct t; auto.
      destruct p; auto. intuition.

    - (* Beta *)
      apply red_trans with (tApp (tLambda na t0 b1) a0).
      eapply (@red_app Σ); [apply red_abs|]; auto with pcuic.
      apply red_trans with (tApp (tLambda na t0 b1) a1).
      eapply (@red_app Σ); auto with pcuic.
      apply red1_red. constructor.

    - (* Zeta *)
      eapply red_trans with (tLetIn na d0 t0 b1).
      eapply red_letin; eauto with pcuic.
      eapply red_trans with (tLetIn na d1 t1 b1).
      eapply red_letin; eauto with pcuic.
      eapply red1_red; constructor.

    - (* Rel in context *)
      eapply nth_error_pred1_ctx in X0; eauto.
      destruct X0 as [body' [Hnth Hpred]].
      eapply red_trans with (lift0 (S i) body').
      eapply red1_red; constructor; auto.
      eapply nth_error_pred1_ctx_all_defs in H; eauto.
      specialize (Hpred H).
      rewrite -(firstn_skipn (S i) Γ).
      eapply weakening_red_0 => //.
      rewrite firstn_length_le //.
      destruct nth_error eqn:Heq.
      eapply nth_error_Some_length in Heq. lia. noconf Hnth.

    - (* Iota *)
      transitivity (tCase (ind, pars) p (mkApps (tConstruct ind c u) args1) brs1).
      eapply red_case; auto.
      eapply red_mkApps. auto. solve_all. red in X2; solve_all.
      eapply red1_red. constructor.

    - move: H H0.
      move => unf isc.
      transitivity (mkApps (tFix mfix1 idx) args1).
      eapply red_mkApps. eapply red_fix_congr. red in X3. solve_all. eapply a.
      solve_all.
      eapply red_step. econstructor; eauto. 2:eauto.
      eapply (is_constructor_pred1 Σ). eapply (All2_impl X4); intuition eauto. auto.

    - transitivity (tCase ip p1 (mkApps (tCoFix mfix1 idx) args1) brs1).
      eapply red_case; eauto.
      eapply red_mkApps; [|solve_all].
      eapply red_cofix_congr. red in X3; solve_all. eapply a0.
      red in X7; solve_all.
      eapply red_step. econstructor; eauto. eauto.

    - transitivity (tProj p (mkApps (tCoFix mfix1 idx) args1)).
      eapply red_proj_c; eauto.
      eapply red_mkApps; [|solve_all].
      eapply red_cofix_congr. red in X3; solve_all. eapply a.
      eapply red_step. econstructor; eauto. eauto.

    - transitivity (tProj (i, pars, narg) (mkApps (tConstruct i 0 u) args1)).
      eapply red_proj_c; eauto.
      eapply red_mkApps; [|solve_all]. auto.
      eapply red1_red. econstructor; eauto.

    - now eapply red_abs_alt.
    - now eapply red_app.
    - now eapply red_letin_alt => //.
    - eapply red_case => //. red in X3; solve_all.
    - now eapply red_proj_c.
    - eapply red_fix_congr. red in X3; solve_all. eapply a.
    - eapply red_cofix_congr. red in X3; solve_all. eapply a.
    - eapply red_prod; auto.
    - eapply red_evar; auto. solve_all.
  Qed.

  Lemma All2_local_env_mix P Q x y : All2_local_env P x y -> All2_local_env Q x y ->
    All2_local_env (fun Γ Γ' d t T => 
      (P Γ Γ' d t T) * (Q Γ Γ' d t T))%type x y.
  Proof.
    intros HP HQ; induction HP; depelim HQ; try (simpl in H; noconf H); 
      try (simpl in H0; noconf H0); constructor; intuition eauto.
  Qed.

  Lemma pred1_red_r_gen_fix_context Γ0 Γ'0 Δ Δ' mfix0 mfix1  : 
    pred1_ctx Σ (Γ'0 ,,, Δ) (Γ'0 ,,, Δ') ->
    All2_local_env
       (on_decl
          (on_decl_over
             (fun (Γ Γ' : context) (t t0 : term) =>
                forall Γ0 Γ'0 Δ Δ' : context,
                  Γ = Γ0 ,,, Δ
                  -> Γ' = Γ'0 ,,, Δ'
                    -> pred1_ctx Σ (Γ'0 ,,, Δ) (Γ'0 ,,, Δ')
                      -> pred1 Σ (Γ'0 ,,, Δ) (Γ'0 ,,, Δ') t t0) 
             (Γ0 ,,, Δ) (Γ'0 ,,, Δ'))) (fix_context mfix0)
       (fix_context mfix1) ->
    All2_local_env (on_decl (on_decl_over (pred1 Σ) (Γ'0 ,,, Δ) (Γ'0 ,,, Δ')))
      (fix_context mfix0) (fix_context mfix1).
  Proof.
    intros H.
    generalize (fix_context mfix0), (fix_context mfix1).
    induction 1; constructor; auto.
    red. red in p.
    unfold on_decl_over in *.
    rewrite - !app_context_assoc; eapply p; rewrite !app_context_assoc; try reflexivity.
    eapply All2_local_env_app_inv; auto.
    destruct p; repeat red in o, o0 |- *; intuition auto; red.
    rewrite - !app_context_assoc; eapply o; rewrite !app_context_assoc; try reflexivity.
    eapply All2_local_env_app_inv; auto.
    rewrite - !app_context_assoc; eapply o0; rewrite !app_context_assoc; try reflexivity.
    eapply All2_local_env_app_inv; auto.
  Qed.

  Lemma pred1_red_r_gen Γ Γ' Δ Δ' : forall M N, pred1 Σ (Γ ,,, Δ) (Γ' ,,, Δ') M N -> 
    pred1_ctx Σ (Γ' ,,, Δ) (Γ' ,,, Δ') ->
    pred1 Σ (Γ' ,,, Δ) (Γ' ,,, Δ') M N.
  Proof.
    intros M N.
    generalize_eq Γ0 (Γ ,,, Δ); intro e.
    generalize_eq Γ'0 (Γ' ,,, Δ'); intros e' p.
    rewrite e'.
    revert Γ Γ' Δ Δ' e e'.
    revert Γ0 Γ'0 M N p.
    refine (@pred1_ind_all_ctx Σ _ 
      (fun Γ Γ' =>
       All2_local_env (on_decl (fun Γ0 Γ'0 M N => 
       forall Γ Γ' Δ Δ' : context,
       Γ0 = Γ ,,, Δ -> Γ'0 = Γ' ,,, Δ' ->
       pred1 Σ Γ0 Γ'0 M N ->
       pred1_ctx Σ (Γ' ,,, Δ) (Γ' ,,, Δ') ->
       pred1 Σ (Γ' ,,, Δ) (Γ' ,,, Δ') M N)) Γ Γ')%type
       _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
      intros; subst; try solve [econstructor; eauto].

    - eapply (All2_local_env_impl _ _ _ _ X0). clear X0; intros.
      red in X0 |- *.
      destruct t as [[t t']|].
      intuition subst. specialize (a Γ1 Γ'0 Δ0 Δ' eq_refl eq_refl). eauto.
      eapply b; eauto. intros; subst. eapply X0; eauto.
    
    - econstructor; eauto. 
      specialize (X0 Γ0 Γ'0 (Δ ,, vass na t0) (Δ' ,, vass na t1) eq_refl).
      apply X0. reflexivity. simpl. constructor; auto. eapply X2; eauto.

    - econstructor; eauto. 
      eapply (X4 Γ0 Γ'0 (Δ ,, vdef na d0 t0) (Δ' ,, vdef na d1 t1) eq_refl eq_refl).
      simpl; constructor; auto. red. split. eapply X2; auto. eapply X0; auto.

    - econstructor; eauto.
      solve_all. red in X2. solve_all.

    - econstructor; eauto.
      eapply pred1_red_r_gen_fix_context; eauto.
      red. red in X3.
      solve_all. red  in a |- *.
      intuition auto. eapply b1;  eauto.
      rewrite - !app_context_assoc; eapply b; 
        rewrite !app_context_assoc; try reflexivity.
        apply All2_local_env_app_inv; eauto.
        eapply pred1_red_r_gen_fix_context; eauto.
      solve_all.
      
    - econstructor; eauto.
      eapply pred1_red_r_gen_fix_context; eauto.
      red. red in X3.
      solve_all. red in a0 |- *.
      intuition auto. eapply b2; eauto.
      rewrite - !app_context_assoc; eapply b0; 
        rewrite !app_context_assoc; try reflexivity.
        apply All2_local_env_app_inv; eauto.
        eapply pred1_red_r_gen_fix_context; eauto.
      solve_all.
      solve_all.
      red in X7. solve_all.
      
    - econstructor; eauto.
      eapply pred1_red_r_gen_fix_context; eauto.
      red in X3 |- *.
      solve_all. red in a |- *.
      intuition auto. eapply b1; eauto.
      rewrite - !app_context_assoc; eapply b; 
        rewrite !app_context_assoc; try reflexivity.
        apply All2_local_env_app_inv; eauto.
        eapply pred1_red_r_gen_fix_context; eauto.
      solve_all.

    - econstructor; eauto.
      solve_all.

    - econstructor; eauto.
      eapply (X2 _ _ (Δ ,, vass na M) (Δ' ,, vass na M')); try reflexivity.
      simpl; constructor; eauto.
      red. eapply X0; eauto.
    
    - econstructor; eauto.
      eapply (X4 _ _ (Δ ,, vdef na d0 t0) (Δ' ,, vdef na d1 t1)); try reflexivity.
      simpl; constructor; eauto.
      red. split. eapply X0; eauto. eapply X2; eauto.

    - econstructor; eauto.
      red in X3. solve_all. 

    - econstructor; eauto.
      eapply pred1_red_r_gen_fix_context; eauto.
      red in X3 |- *; solve_all.
      eapply a; eauto.
      rewrite - !app_context_assoc; eapply b; 
      rewrite !app_context_assoc; try reflexivity.
      apply All2_local_env_app_inv; eauto.
      eapply pred1_red_r_gen_fix_context; eauto.

    - econstructor; eauto.
      eapply pred1_red_r_gen_fix_context; eauto.
      red in X3 |- *; solve_all.
      eapply a; eauto.
      rewrite - !app_context_assoc; eapply b; 
      rewrite !app_context_assoc; try reflexivity.
      apply All2_local_env_app_inv; eauto.
      eapply pred1_red_r_gen_fix_context; eauto.

    - econstructor; eauto.
      eapply (X2 _ _ (Δ ,, vass na M0) (Δ' ,, vass na M1)); try reflexivity.
      simpl; constructor; eauto.
      red. eapply X0; eauto.

    - econstructor; eauto. solve_all.
  Qed.

  Lemma pred1_pred1_r Γ Γ' : forall M N, pred1 Σ Γ Γ' M N -> 
    pred1 Σ Γ' Γ' M N.
  Proof.
    intros M N pred.
    apply (pred1_red_r_gen _ _ [] [] M N pred).
    simpl. eapply pred1_ctx_refl.
  Qed.

  Lemma pred1_red_r Γ Γ' : forall M N, pred1 Σ Γ Γ' M N -> red Σ Γ' M N.
  Proof.
    intros M N p.
    eapply pred1_pred1_r in p.
    now eapply pred1_red in p.
  Qed.

End PredRed.



Generalizable Variables A B R S.

Section AbstractConfluence.
  Section Definitions.

    Context {A : Type}.
    Definition joinable (R : A -> A -> Type) (x y : A) := ∑ z, R x z * R y z.
    Definition diamond (R : A -> A -> Type) := forall x y z, R x y -> R x z -> joinable R y z.
    Definition confluent (R : relation A) := diamond (clos_refl_trans R).

  End Definitions.

  Global Instance joinable_proper A :
    Proper (relation_equivalence ==> relation_equivalence)%signature (@joinable A).
  Proof.
    reduce_goal. split; unfold joinable; intros.
    destruct X0. exists x1. intuition eauto. setoid_rewrite (X x0 x1) in a. auto.
    specialize (X y0 x1). now apply X in b.
    red in X.
    destruct X0 as [z [rl rr]].
    apply X in rl. apply X in rr.
    exists z; split; auto.
  Qed.

  Global Instance diamond_proper A : Proper (relation_equivalence ==> iffT)%signature (@diamond A).
  Proof.
    reduce_goal.
    rewrite /diamond.
    split; intros.
    setoid_rewrite <- (X x0 y0) in X1.
    setoid_rewrite <- (X x0 z) in X2.
    specialize (X0 _ _ _ X1 X2).
    pose (joinable_proper _ _ _ X).
    now apply r in X0.
    setoid_rewrite (X x0 y0) in X1.
    setoid_rewrite (X x0 z) in X2.
    specialize (X0 _ _ _ X1 X2).
    pose (joinable_proper _ _ _ X).
    now apply r in X0.
  Qed.

  Lemma clos_rt_proper A : Proper (relation_equivalence ==> relation_equivalence) (@clos_refl_trans A).
  Proof.
    reduce_goal. split; intros.
    induction X0; try apply X in r; try solve [econstructor; eauto].
    induction X0; try apply X in r; try solve [econstructor; eauto].
  Qed.

  Global Instance confluent_proper A : Proper (relation_equivalence ==> iffT)%signature (@confluent A).
  Proof.
    reduce_goal.
    split; rewrite /confluent; auto.
    pose proof (diamond_proper A). apply X0. apply clos_rt_proper.
    now symmetry.
    pose proof (diamond_proper A). apply X0. apply clos_rt_proper.
    now symmetry.
  Qed.

  Lemma sandwich {A} (R S : A -> A -> Type) :
    inclusion R S -> inclusion S (clos_refl_trans R) ->
    (iffT (confluent S) (confluent R)).
  Proof.
    intros inclR inclS.
    apply clos_rt_monotone in inclR.
    apply clos_rt_monotone in inclS.
    assert (inclusion (clos_refl_trans S) (clos_refl_trans R)).
    etransitivity; eauto.
    apply clos_rt_idempotent.
    rewrite /confluent.
    apply diamond_proper.
    now apply relation_equivalence_inclusion.
  Qed.

  Section Diamond.
    Context {A} {R S : relation A}.
    Context (sc : diamond R).

    Lemma diamond_t1n_t_confluent t u v :
      trans_clos_1n R t u ->
      R t v ->
      ∑ t', trans_clos_1n R u t' * trans_clos_1n R v t'.
    Proof.
      move => tu.
      revert v.
      induction tu.
      intros.
      - destruct (sc _ _ _ r X); auto.
        eexists; split; constructor; intuition eauto.
      - move => v xv.
        destruct (sc _ _ _ r xv); auto.
        destruct p. specialize (IHtu _ r0).
        destruct IHtu as [nf [redl redr]].
        exists nf. split; auto.
        econstructor 2; eauto.
    Qed.

    Lemma diamond_t1n_t1n_confluent {t u v} :
      trans_clos_1n R t u ->
      trans_clos_1n R t v ->
      ∑ t', trans_clos_1n R u t' * trans_clos_1n R v t'.
    Proof.
      move => tu tv.
      induction tv in u, tu |- *.
      - eapply diamond_t1n_t_confluent; eauto.
      - eapply diamond_t1n_t_confluent in r; eauto.
        destruct r as [nf [redl redr]].
        specialize (IHtv _ redr) as [nf' [redl' redr']].
        exists nf'; intuition auto.
        apply trans_clos_t1n_iff.
        econstructor 2; eapply trans_clos_t1n_iff; eauto.
    Qed.

    Lemma diamond_t_t_confluent {t u v} :
      trans_clos R t u ->
      trans_clos R t v ->
      ∑ t', trans_clos R u t' * trans_clos R v t'.
    Proof.
      move => tu tv.
      apply trans_clos_t1n_iff in tu;
        apply trans_clos_t1n_iff in tv.
      destruct (diamond_t1n_t1n_confluent tu tv).
      exists x. split; apply trans_clos_t1n_iff; intuition auto.
    Qed.

    Lemma commutes_diamonds_diamond :
      commutes R S -> diamond S -> diamond (relation_disjunction R S).
    Proof.
      intros HRS HS x y z xy xz.
      destruct xy, xz.
      destruct (sc _ _ _ r r0).
      eexists; intuition auto. now left. now left.
      destruct (HRS _ _ _ r s).
      exists x0.
      intuition auto. right; auto. left; auto.
      destruct (HRS _ _ _ r s).
      eexists; intuition auto. left; eauto. right; auto.
      destruct (HS _ _ _ s s0). intuition auto.
      eexists. split; right; eauto.
    Qed.

    Lemma commutes_disj_joinable :
      commutes R S -> confluent R -> confluent S ->
      forall x y z, relation_disjunction R S x y ->
                    relation_disjunction R S x z ->
                    joinable (clos_refl_trans (relation_disjunction R S)) y z.
    Proof.
      intros.
      destruct X2. destruct X3.
      destruct (X0 _ _ _ (rt_step r) (rt_step r0)).
      exists x0; intuition auto. now eapply clos_rt_disjunction_left.
      now apply clos_rt_disjunction_left.
      destruct (X _ _ _ r s).
      exists x0.
      intuition auto. now eapply clos_rt_disjunction_right, rt_step.
      now apply clos_rt_disjunction_left, rt_step.
      destruct X3.
      destruct (X _ _ _ r s).
      exists x0.
      intuition auto. now eapply clos_rt_disjunction_left, rt_step.
      now apply clos_rt_disjunction_right, rt_step.
      destruct (X1 _ _ _ (rt_step s) (rt_step s0)).
      exists x0; intuition auto. now eapply clos_rt_disjunction_right.
      now apply clos_rt_disjunction_right.
    Qed.

  End Diamond.

  Theorem diamond_confluent `{Hrefl : Reflexive A R} : diamond R -> confluent R.
  Proof.
    move=> Hdia x y z H H'.
    apply clos_rt_t_incl in H.
    apply clos_rt_t_incl in H'.
    pose proof (clos_t_rt_equiv (R:=R)).
    apply (joinable_proper _ _ _ X).
    apply (diamond_t_t_confluent Hdia H H').
  Qed.

  Corollary confluent_union {A} {R S : relation A} :
    Reflexive R ->
    commutes R S -> diamond R -> diamond S -> confluent (relation_disjunction R S).
  Proof.
    intros HRR HRS Hcom HR HS. apply diamond_confluent.
    now apply commutes_diamonds_diamond.
  Qed.

End AbstractConfluence.

Unset Universe Minimization ToSet.



Lemma red_pred {cf:checker_flags} {Σ : global_env} {Γ t u} : wf Σ -> clos_refl_trans (red1 Σ Γ) t u -> clos_refl_trans (pred1 Σ Γ Γ) t u.
Proof.
  intros wfΣ. eapply clos_rt_monotone.
  intros x y H.
  eapply red1_pred1; auto.
Qed.

Section RedConfluence.
  Context {cf : checker_flags}.
  Context {Σ : global_env} (wfΣ : wf Σ).

  Instance pred1_refl Γ : Reflexive (pred1 Σ Γ Γ).
  Proof. red; apply pred1_refl. Qed.

  Definition pred1_rel : (context * term) -> (context * term) -> Type :=
    fun t u => pred1 Σ (fst t) (fst u) (snd t) (snd u).

  Instance pred1_rel_refl : Reflexive pred1_rel.
  Proof. red. intros [ctx x]. red. simpl. apply pred1_refl. Qed.

  Lemma red1_weak_confluence Γ t u v :
    red1 Σ Γ t u -> red1 Σ Γ t v ->
    ∑ t', red Σ Γ u t' * red Σ Γ v t'.
  Proof.
    move/(red1_pred1 wfΣ) => tu.
    move/(red1_pred1 wfΣ) => tv.
    eapply pred1_diamond in tu; eauto.
    destruct tu as [redl redr].
    eapply pred1_red in redl; auto.
    eapply pred1_red in redr; auto.
    eexists _; split; eauto.
  Qed.

  Lemma diamond_pred1_rel : diamond pred1_rel.
  Proof.
    move=> t u v tu tv.
    destruct (pred1_diamond wfΣ tu tv).
    eexists (rho_ctx Σ (fst t), rho Σ (rho_ctx Σ (fst t)) (snd t)).
    split; auto.
  Qed.

  Lemma pred1_rel_confluent : confluent pred1_rel.
  Proof.
    eapply diamond_confluent. apply diamond_pred1_rel.
  Qed.

  Lemma red_trans_clos_pred1 Γ t u :
    red Σ Γ t u ->
    trans_clos pred1_rel (Γ, t) (Γ, u).
  Proof.
    induction 1.
    constructor. now eapply red1_pred1 in r.
    constructor. pcuic.
    econstructor 2; eauto.
  Qed.

  Definition on_one_decl (P : context -> term -> term -> Type) (Γ : context) (b : option (term × term)) (t t' : term) :=
    match b with
    | Some (b0, b') => ((P Γ b0 b' * (t = t')) + (P Γ t t' * (b0 = b')))%type
    | None => P Γ t t'
    end.

  Section OnOne_local_2.
    Context (P : forall (Γ : context), option (term * term) -> term -> term -> Type).

    (** We allow alpha-conversion *)
    Inductive OnOne2_local_env : context -> context -> Type :=
    | localenv2_cons_abs Γ na t t' :
        P Γ None t t' ->
        OnOne2_local_env (Γ ,, vass na t) (Γ ,, vass na t')
    | localenv2_cons_def Γ na b b' t t' :
        P Γ (Some (b, b')) t t' ->
        OnOne2_local_env (Γ ,, vdef na b t) (Γ ,, vdef na b' t')
    | localenv2_cons_tl Γ Γ' d :
        OnOne2_local_env Γ Γ' ->
        OnOne2_local_env (Γ ,, d) (Γ' ,, d).
  End OnOne_local_2.

  Inductive clos_refl_trans_ctx_decl (R : relation context_decl) (x : context_decl) : context_decl -> Type :=
    rt_ctx_decl_step : forall y, R x y -> clos_refl_trans_ctx_decl R x y
  | rt_ctx_decl_refl y : decl_body x = decl_body y -> decl_type x = decl_type y -> clos_refl_trans_ctx_decl R x y
  | rt_ctx_decl_trans : forall y z, clos_refl_trans_ctx_decl R x y -> clos_refl_trans_ctx_decl R y z ->
                               clos_refl_trans_ctx_decl R x z.

  Inductive eq_context_upto_names : context -> context -> Type :=
  | eq_context_nil : eq_context_upto_names [] []
  | eq_context_decl x y Γ Γ' :
      decl_body x = decl_body y -> decl_type x = decl_type y ->
      eq_context_upto_names Γ Γ' ->
      eq_context_upto_names (Γ ,, x) (Γ' ,, y).

  Derive Signature for eq_context_upto_names.

  Global Instance eq_context_upto_names_refl : Reflexive eq_context_upto_names.
  Proof. intros Γ; induction Γ; constructor; auto. Qed.

  Global Instance eq_context_upto_names_sym : Symmetric eq_context_upto_names.
  Proof. intros Γ Γ' H; induction H; constructor; auto. Qed.

  Global Instance eq_context_upto_names_trans : Transitive eq_context_upto_names.
  Proof.
    intros Γ0 Γ1 Γ2 H.
    induction H in Γ2 |- *; intros H2; depelim H2; econstructor; auto.
    etransitivity; eauto.
    etransitivity; eauto.
  Qed.

  Inductive clos_refl_trans_ctx (R : relation context) (x : context) : context -> Type :=
  | rt_ctx_step : forall y, R x y -> clos_refl_trans_ctx R x y
  | rt_ctx_refl y : eq_context_upto_names x y -> clos_refl_trans_ctx R x y
  | rt_ctx_trans : forall y z, clos_refl_trans_ctx R x y -> clos_refl_trans_ctx R y z -> clos_refl_trans_ctx R x z.

  Global Instance clos_refl_trans_ctx_refl R :
    Reflexive (clos_refl_trans_ctx R).
  Proof. intros HR. constructor 2. reflexivity. Qed.

  Global Instance clos_refl_trans_ctx_trans R : Transitive (clos_refl_trans_ctx R).
  Proof.
    intros x y z; econstructor 3; eauto.
  Qed.

  Definition red1_ctx := (OnOne2_local_env (on_one_decl (fun Δ t t' => red1 Σ Δ t t'))).

  Definition red1_rel : relation (context * term) :=
    relation_disjunction (fun '(Γ, t) '(Δ, u) => (red1 Σ Γ t u * (Γ = Δ)))%type
                         (fun '(Γ, t) '(Δ, u) => (red1_ctx Γ Δ * (t = u)))%type.

  Definition red_ctx : relation context :=
    All2_local_env (on_decl (fun Γ Δ t u => red Σ Γ t u)).

  Lemma red1_ctx_pred1_ctx Γ Γ' : red1_ctx Γ Γ' -> pred1_ctx Σ Γ Γ'.
  Proof.
    intros. induction X; try constructor. pcuic. red. pcuic.
    now eapply red1_pred1. pcuic.
    destruct p as [[redb ->]|[redt ->]].
    - split; pcuic. now eapply red1_pred1.
    - split; pcuic. now eapply red1_pred1.
    - destruct d as [na [b|] ty].
      * constructor; intuition auto. red.
        split; now eapply pred1_refl_gen.
      * constructor; intuition auto. red.
        now eapply pred1_refl_gen.
  Qed.

  Lemma pred1_ctx_red_ctx Γ Γ' : pred1_ctx Σ Γ Γ' -> red_ctx Γ Γ'.
  Proof.
    intros. induction X; try constructor; pcuic.
    now eapply pred1_red in p.
    destruct p as [redb redt].
    split. now apply pred1_red in redb.
    now apply pred1_red in redt.
  Qed.

  Definition red_rel_ctx :=
    fun '(Γ, t) '(Δ, u) =>
      (red Σ Γ t u * red_ctx Γ Δ)%type.

  Lemma pred1_red' Γ Γ' : forall M N, pred1 Σ Γ Γ' M N -> red_rel_ctx (Γ, M) (Γ', N).
  Proof.
    intros * Hred.
    split. apply (pred1_red wfΣ _ _ _ _ Hred).
    eapply pred1_pred1_ctx in Hred.
    now eapply pred1_ctx_red_ctx.
  Qed.


  Lemma clos_rt_OnOne2_local_env_incl R :
    inclusion (OnOne2_local_env (on_one_decl (fun Δ => clos_refl_trans (R Δ))))
              (clos_refl_trans (OnOne2_local_env (on_one_decl R))).
  Proof.
    intros x y H.
    induction H; firstorder.
    - red in p.
      induction p. repeat constructor. firstorder.
      constructor 2.
      econstructor 3 with (Γ ,, vass na y); auto.
    - subst.
      induction a. repeat constructor. firstorder.
      constructor 2.
      econstructor 3 with (Γ ,, vdef na y t'); auto.
    - subst.
      induction a. constructor. constructor. red. right. firstorder.
      constructor 2.
      econstructor 3 with (Γ ,, vdef na b' y); auto.
    - clear H. induction IHOnOne2_local_env. constructor. now constructor 3.
      constructor 2.
      eapply transitivity. eauto. auto.
  Qed.

  Lemma clos_rt_OnOne2_local_env_ctx_incl R :
    inclusion (clos_refl_trans (OnOne2_local_env (on_one_decl R)))
              (clos_refl_trans_ctx (OnOne2_local_env (on_one_decl R))).
  Proof.
    intros x y H.
    induction H; firstorder; try solve[econstructor; eauto].
  Qed.

  Lemma OnOne2_local_env_impl R S :
    (forall Δ, inclusion (R Δ) (S Δ)) ->
    inclusion (OnOne2_local_env (on_one_decl R))
              (OnOne2_local_env (on_one_decl S)).
  Proof.
    intros H x y H'.
    induction H'; try solve [econstructor; firstorder].
  Qed.

  Lemma red_ctx_clos_rt_red1_ctx : inclusion red_ctx (clos_refl_trans_ctx red1_ctx).
  Proof.
    intros x y H.
    induction H; try firstorder.
    red in p.
    transitivity (Γ ,, vass na t').
    eapply clos_rt_OnOne2_local_env_ctx_incl, clos_rt_OnOne2_local_env_incl. constructor. red.
    eassumption.
    clear p H.
    transitivity (Γ ,, vass na' t').
    { constructor 2. repeat constructor; auto. apply reflexivity. }
    induction IHAll2_local_env; try solve[repeat constructor; auto].
    etransitivity; eauto.
    transitivity (Γ ,, vdef na b t').
    - eapply clos_rt_OnOne2_local_env_ctx_incl, clos_rt_OnOne2_local_env_incl. constructor 2. red.
      right. split; auto.
    - transitivity (Γ ,, vdef na b' t').
      eapply clos_rt_OnOne2_local_env_ctx_incl, clos_rt_OnOne2_local_env_incl.
      constructor 2. red. left; split; auto.
      clear -IHAll2_local_env.
      transitivity (Γ ,, vdef na' b' t').
      { constructor 2. repeat constructor; auto. apply reflexivity. }
      induction IHAll2_local_env; try solve[repeat constructor; auto].
      etransitivity; eauto.
  Qed.

  Inductive clos_refl_trans_ctx_t (R : relation (context * term)) (x : context * term) : context * term -> Type :=
  | rt_ctx_t_step : forall y, R x y -> clos_refl_trans_ctx_t R x y
  | rt_ctx_t_refl y : eq_context_upto_names (fst x) (fst y) -> snd x = snd y -> clos_refl_trans_ctx_t R x y
  | rt_ctx_t_trans : forall y z, clos_refl_trans_ctx_t R x y -> clos_refl_trans_ctx_t R y z -> clos_refl_trans_ctx_t R x z.

  Global Instance clos_refl_trans_ctx_t_refl R :
    Reflexive (clos_refl_trans_ctx_t R).
  Proof. intros HR. constructor 2. reflexivity. auto. Qed.

  Global Instance clos_refl_trans_ctx_t_trans R : Transitive (clos_refl_trans_ctx_t R).
  Proof.
    intros x y z; econstructor 3; eauto.
  Qed.

  Definition clos_rt_ctx_t_monotone (R S : relation _) :
    inclusion R S -> inclusion (clos_refl_trans_ctx_t R) (clos_refl_trans_ctx_t S).
  Proof.
    move => incls x y.
    induction 1; solve [econstructor; eauto].
  Qed.

  Lemma clos_rt_ctx_t_disjunction_left (R S : relation _) :
    inclusion (clos_refl_trans_ctx_t R)
              (clos_refl_trans_ctx_t (relation_disjunction R S)).
  Proof.
    apply clos_rt_ctx_t_monotone.
    intros x y H; left; exact H.
  Qed.

  Lemma clos_rt_ctx_t_disjunction_right (R S : relation _) :
    inclusion (clos_refl_trans_ctx_t S)
              (clos_refl_trans_ctx_t (relation_disjunction R S)).
  Proof.
    apply clos_rt_ctx_t_monotone.
    intros x y H; right; exact H.
  Qed.

  Lemma clos_refl_trans_ctx_t_prod_l (R : relation _) (S : relation _) :
    (forall x y b, R x y -> S (x, b) (y, b)) ->
    forall x y b,
      clos_refl_trans_ctx R x y ->
      clos_refl_trans_ctx_t S (x, b) (y, b).
  Proof.
    intros. induction X0; try solve [econstructor; eauto].
  Qed.

  Lemma clos_refl_trans_ctx_t_prod_r (R : relation term) (S : relation (context * term)) a :
    (forall x y, R x y -> S (a, x) (a, y)) ->
    forall x y,
      clos_refl_trans R x y ->
      clos_refl_trans_ctx_t S (a, x) (a, y).
  Proof.
    intros. induction X0; try solve [econstructor; eauto].
    constructor 2. simpl. apply reflexivity. reflexivity.
  Qed.

  Lemma clos_rt_red1_rel_ctx_rt_ctx_red1_rel : inclusion red_rel_ctx (clos_refl_trans_ctx_t red1_rel).
  Proof.
    move=> [Γ t] [Δ u] [redt redctx].
    eapply clos_rt_rt1n_iff in redt.
    induction redt.
    induction redctx; try solve [constructor; eauto].
    - constructor 2; simpl; apply reflexivity.
    - red in p.
      etransitivity.
      * eapply clos_rt_ctx_t_disjunction_right.
        instantiate (1:= (Γ',, vass na' t', x)).
        eapply clos_refl_trans_ctx_t_prod_l. intros. split; eauto.
        transitivity (Γ ,, vass na' t).
        constructor 2. repeat constructor; apply reflexivity.
        apply red_ctx_clos_rt_red1_ctx. constructor; auto.
      * clear p. eapply clos_rt_ctx_t_disjunction_right.
        constructor 2; simpl; reflexivity.
    - red in p. destruct p. etransitivity.
      * eapply clos_rt_ctx_t_disjunction_right.
        instantiate (1:= (Γ',, vdef na b' t', x)).
        eapply clos_refl_trans_ctx_t_prod_l. intros. split; eauto.
        apply red_ctx_clos_rt_red1_ctx. constructor; auto.
        red. split; auto.
      * clear r r0.
        eapply clos_rt_ctx_t_disjunction_right.
        eapply clos_refl_trans_ctx_t_prod_l. intros. split; eauto.
        constructor 2. constructor; auto. apply reflexivity.
    - transitivity (Γ, y).
      * eapply clos_rt_ctx_t_disjunction_left.
        eapply clos_refl_trans_ctx_t_prod_r. intros. split; eauto.
        constructor. apply r.
      * apply IHredt.
  Qed.

  Definition red1_rel_alpha : relation (context * term) :=
    relation_disjunction (fun '(Γ, t) '(Δ, u) => (red1 Σ Γ t u * (Γ = Δ)))%type
     (relation_disjunction
        (fun '(Γ, t) '(Δ, u) => ((red1_ctx Γ Δ * (t = u))))
        (fun '(Γ, t) '(Δ, u) => ((eq_context_upto_names Γ Δ * (t = u)))))%type.

  Lemma clos_rt_red1_rel_rt_ctx : inclusion (clos_refl_trans red1_rel) (clos_refl_trans_ctx_t red1_rel).
  Proof.
    intros x y H.
    induction H.
    - destruct x, y. constructor. auto.
    - constructor 2; apply reflexivity.
    - econstructor 3; eauto.
  Qed.

  Lemma red1_rel_alpha_pred1_rel : inclusion red1_rel_alpha pred1_rel.
  Proof.
    intros [ctx t] [ctx' t'].
    rewrite /red1_rel_alpha /pred1_rel /=.
    intros [[l <-]|[[r <-]|[r <-]]].
    - now eapply red1_pred1.
    - eapply pred1_refl_gen. now apply red1_ctx_pred1_ctx.
    - eapply pred1_refl_gen.
      induction r.
      * constructor.
      * destruct x as [na [b|] ty], y as [na' [b'|] ty']; simpl in *; noconf e; try noconf e0.
        constructor; auto. red. split; now apply pred1_refl_gen.
        constructor; auto. red; now apply pred1_refl_gen.
  Qed.

  Lemma pred1_rel_red1_rel_alpha : inclusion pred1_rel (clos_refl_trans red1_rel_alpha).
  Proof.
    intros x y pred. red in pred.
    eapply pred1_red' in pred; auto.
    destruct pred.
    destruct x, y. simpl in *.
    transitivity (c, t0).
    - eapply clos_rt_disjunction_left.
      eapply clos_refl_trans_prod_r; tea. intros. split; eauto.
    - eapply clos_rt_disjunction_right.
      eapply (clos_refl_trans_prod_l (fun x y => red1_ctx x y + eq_context_upto_names x y))%type.
      intros. red. destruct X; intuition auto.
      clear r.
      apply red_ctx_clos_rt_red1_ctx in r0.
      induction r0. constructor; auto.
      constructor. auto.
      now transitivity y.
  Qed.

  Lemma pred_rel_confluent : confluent red1_rel_alpha.
  Proof.
    notypeclasses refine (fst (sandwich _ _ _ _) _).
    3:eapply pred1_rel_confluent; eauto.
    - apply red1_rel_alpha_pred1_rel.
    - apply pred1_rel_red1_rel_alpha.
  Qed.

  Lemma clos_refl_trans_out Γ x y :
    clos_refl_trans (red1 Σ Γ) x y -> clos_refl_trans red1_rel (Γ, x) (Γ, y).
  Proof.
    induction 1. constructor. red. left. firstorder.
    constructor 2.
    econstructor 3; eauto.
  Qed.

  Lemma red_red_ctx Γ Δ t u :
    red Σ Γ t u ->
    red_ctx Δ Γ ->
    red Σ Δ t u.
  Proof.
    move=> H Hctx. induction H.
    revert Δ Hctx.
    induction r using red1_ind_all; intros Δ Hctx; try solve [eapply red_step; repeat (constructor; eauto)].
    - red in Hctx.
      eapply nth_error_pred1_ctx in Hctx; eauto.
      destruct Hctx as [x' [? ?]].
      eapply red_step. constructor. eauto.
      rewrite -(firstn_skipn (S i) Δ).
      eapply weakening_red_0; auto.
      rewrite firstn_length_le //.
      destruct (nth_error Δ) eqn:Heq => //.
      eapply nth_error_Some_length in Heq. lia.
    - repeat econstructor; eassumption.
    - repeat econstructor; eassumption.
    - repeat econstructor; eassumption.
    - repeat econstructor; eassumption.
    - eapply red_abs_alt. eauto. eauto.
    - eapply red_abs_alt. eauto. apply (IHr (Δ ,, vass na N)).
      constructor; auto. red. auto.
    - eapply red_letin; eauto.
    - eapply red_letin; eauto.
    - eapply red_letin_alt; eauto.
      eapply (IHr (Δ ,, vdef na b t)). constructor; eauto.
      red. split; eauto.
    - eapply red_case; eauto. unfold on_Trel; pcuic.
    - eapply red_case; eauto. unfold on_Trel; pcuic.
    - eapply red_case; eauto. unfold on_Trel; pcuic.
      eapply OnOne2_All2; eauto. simpl. intuition eauto.
    - eapply red_proj_c; eauto.
    - eapply red_app; eauto.
    - eapply red_app; eauto.
    - eapply red_prod_alt; eauto.
    - eapply red_prod_alt; eauto. apply (IHr (Δ ,, vass na M1)); constructor; auto.
      red; eauto.
    - eapply red_evar.
      eapply OnOne2_All2; simpl; eauto. simpl. intuition eauto.
    - eapply red_fix_one_ty.
      eapply OnOne2_impl ; eauto.
      intros [? ? ? ?] [? ? ? ?] [[r ih] e]. simpl in *.
      inversion e. subst. clear e.
      split ; auto.
    - eapply red_fix_one_body.
      eapply OnOne2_impl ; eauto.
      intros [? ? ? ?] [? ? ? ?] [[r ih] e]. simpl in *.
      inversion e. subst. clear e.
      split ; auto.
      eapply ih.
      clear - Hctx. induction (fix_context mfix0).
      + assumption.
      + simpl. destruct a as [na [b|] ty].
        * constructor ; firstorder (hnf ; auto).
        * constructor ; firstorder (hnf ; auto).
    - eapply red_cofix_one_ty.
      eapply OnOne2_impl ; eauto.
      intros [? ? ? ?] [? ? ? ?] [[r ih] e]. simpl in *.
      inversion e. subst. clear e.
      split ; auto.
    - eapply red_cofix_one_body.
      eapply OnOne2_impl ; eauto.
      intros [? ? ? ?] [? ? ? ?] [[r ih] e]. simpl in *.
      inversion e. subst. clear e.
      split ; auto.
      eapply ih.
      clear - Hctx. induction (fix_context mfix0).
      + assumption.
      + simpl. destruct a as [na [b|] ty].
        * constructor ; firstorder (hnf ; auto).
        * constructor ; firstorder (hnf ; auto).
    - auto.
    - eapply red_trans; eauto.
  Qed.

  Lemma clos_red_rel_out x y :
    clos_refl_trans red1_rel x y ->
    clos_refl_trans pred1_rel x y.
  Proof.
    eapply clos_rt_monotone. clear x y.
    intros [Γ t] [Δ u] hred.
    destruct hred as [[ht eq]|[hctx eq]]. subst.
    red. simpl. now eapply red1_pred1.
    subst. red.
    simpl.
    eapply pred1_refl_gen. now eapply red1_ctx_pred1_ctx.
  Qed.

  Lemma red1_rel_alpha_red1_rel : inclusion (clos_refl_trans red1_rel_alpha) (clos_refl_trans_ctx_t red1_rel).
  Proof.
    intros x y H.
    induction H.
    - destruct x, y.
      destruct r. destruct p; subst.
      constructor. firstorder.
      destruct r. destruct p; subst.
      constructor. firstorder.
      destruct p; subst.
      constructor 2. simpl. auto. reflexivity.
    - constructor 2; reflexivity.
    - econstructor 3; eauto.
  Qed.

  Lemma red1_rel_alpha_red1_rel_inv : inclusion (clos_refl_trans_ctx_t red1_rel) (clos_refl_trans red1_rel_alpha).
  Proof.
    intros x y H.
    induction H.
    - destruct x, y.
      destruct r. destruct p; subst.
      constructor. firstorder.
      destruct p. subst.
      constructor. firstorder.
    - destruct x, y. simpl in *.
      subst. constructor. firstorder.
    - econstructor 3; eauto.
  Qed.

  Lemma clos_red_rel_out_inv x y :
    clos_refl_trans pred1_rel x y ->
    clos_refl_trans red1_rel_alpha x y.
  Proof.
    induction 1.
    red in r.
    destruct x as [Γ t], y as [Δ u]; simpl in *.
    pose proof (pred1_pred1_ctx _ r).
    apply red1_rel_alpha_red1_rel_inv.
    transitivity (Γ, u).
    eapply clos_refl_trans_ctx_t_prod_r. intros. red. left. split; eauto.
    now apply pred1_red in r.
    eapply clos_refl_trans_ctx_t_prod_l. intros. red. right. split; eauto.
    now apply red_ctx_clos_rt_red1_ctx, pred1_ctx_red_ctx.
    constructor 2.
    etransitivity; eauto.
  Qed.

  Global Instance red_ctx_refl : Reflexive red_ctx.
  Proof.
    move=> x.
    induction x as [|[na [b|] ty] ctx]; constructor; intuition (try red; auto).
  Qed.

  Global Instance red_ctx_trans : Transitive red_ctx.
  Proof.
    move=> Γ Γ' Γ'' H1 H2.
    unfold red_ctx in *.
    induction H1 in Γ'', H2 |- *; depelim H2; try (hnf in H; noconf H);
    constructor; auto.
    red in o, p. red.
    transitivity t'; eauto.
    eapply red_red_ctx; eauto.
    destruct p, o. red.
    split.
    transitivity b'; eauto.
    eapply red_red_ctx; eauto.
    transitivity t'; eauto.
    eapply red_red_ctx; eauto.
  Qed.

  Lemma clos_rt_red1_rel_red1 x y :
    clos_refl_trans red1_rel x y ->
    red_ctx (fst x) (fst y) *
    clos_refl_trans (red1 Σ (fst x)) (snd x) (snd y).
  Proof.
    intros H.
    eapply clos_rt_rt1n_iff in H.
    induction H.
    - split. red. induction (fst x) as [|[na [b|] ty] tl]; try constructor; hnf; eauto.
      constructor 2.
    - destruct x as [Γ t], y as [Δ u], z as [Δ' u']; simpl in *.
      destruct IHclos_refl_trans_1n.
      red in r. destruct r.
      * destruct p. subst. split. auto.
        transitivity u; auto.
      * destruct p. subst. split.
        apply red1_ctx_pred1_ctx in r.
        apply pred1_ctx_red_ctx in r.
        etransitivity; eauto.
        eapply red_red_ctx; eauto.
        apply red1_ctx_pred1_ctx in r.
        now apply pred1_ctx_red_ctx in r.
  Qed.

  Lemma decl_body_eq_context_upto_names Γ Γ' n d :
    option_map decl_body (nth_error Γ n) = Some d ->
    eq_context_upto_names Γ Γ' ->
    option_map decl_body (nth_error Γ' n) = Some d.
  Proof.
    move: Γ' n d; induction Γ; destruct n; simpl; intros; try congruence.
    noconf H. depelim X. simpl. now rewrite -e.
    depelim X. simpl. apply IHΓ; auto.
  Qed.

  Lemma decl_type_eq_context_upto_names Γ Γ' n d :
    option_map decl_type (nth_error Γ n) = Some d ->
    eq_context_upto_names Γ Γ' ->
    option_map decl_type (nth_error Γ' n) = Some d.
  Proof.
    move: Γ' n d; induction Γ; destruct n; simpl; intros; try congruence.
    noconf H. depelim X. simpl. now rewrite -e0.
    depelim X. simpl. apply IHΓ; auto.
  Qed.

  Lemma eq_context_upto_names_app Γ Γ' Δ :
    eq_context_upto_names Γ Γ' ->
    eq_context_upto_names (Γ ,,, Δ) (Γ' ,,, Δ).
  Proof.
    induction Δ; auto. constructor; auto.
  Qed.

  Lemma red1_eq_context_upto_names Γ Γ' t u :
    eq_context_upto_names Γ Γ' ->
    red1 Σ Γ t u ->
    red1 Σ Γ' t u.
  Proof.
    move=> Hctx H.
    revert Γ' Hctx.
    induction H using red1_ind_all; intros Δ Hctx; try solve [repeat (econstructor; eauto)].
    - constructor.
      now eapply decl_body_eq_context_upto_names.
    - constructor. apply (IHred1 (Δ ,, vass na N)). constructor; auto.
    - constructor. apply (IHred1 (Δ ,, vdef na b t)). constructor; auto.
    - constructor. solve_all.
    - constructor. apply (IHred1 (Δ ,, vass na M1)). constructor; auto.
    - constructor. solve_all.
    - constructor. solve_all.
    - eapply fix_red_body; solve_all.
      eapply (b0 (Δ ,,, fix_context mfix0)).
      now apply eq_context_upto_names_app.
    - eapply cofix_red_ty; solve_all.
    - eapply cofix_red_body; solve_all.
      eapply (b0 (Δ ,,, fix_context mfix0)).
      now apply eq_context_upto_names_app.
  Qed.

  Lemma clos_rt_red1_eq_context_upto_names Γ Γ' t u :
    eq_context_upto_names Γ Γ' ->
    clos_refl_trans (red1 Σ Γ) t u ->
    clos_refl_trans (red1 Σ Γ') t u.
  Proof.
    intros HΓ H. move: H. apply clos_rt_monotone => x y.
    now apply red1_eq_context_upto_names.
  Qed.

  Lemma red_eq_context_upto_names Γ Γ' t u :
    eq_context_upto_names Γ Γ' ->
    red Σ Γ t u ->
    red Σ Γ' t u.
  Proof.
    intros HΓ H. move: H. apply clos_rt_monotone => x y.
    now apply red1_eq_context_upto_names.
  Qed.

  Lemma eq_context_upto_names_red_ctx Γ Δ Γ' Δ' :
    eq_context_upto_names Γ Γ' ->
    eq_context_upto_names Δ Δ' ->
    red_ctx Γ Δ ->
    red_ctx Γ' Δ'.
  Proof.
    intros.
    induction X in X0, Δ, Δ', X1 |- *. depelim X1. depelim X0. constructor.
    destruct x as [na b ty], y as [na' b' ty']; simpl in *.
    subst.
    depelim X1. depelim X0. 
    red in o. simpl in *. subst.
    destruct y as [? [b'|] ?]; noconf e.
    constructor; auto. eapply IHX; eauto.
    red. eapply red_eq_context_upto_names; eauto.
    destruct o. depelim X0. simpl in *.
    destruct y as [? [b'|] ?]; noconf e. subst; simpl in *.
    constructor. eapply IHX; eauto.
    red.
    split; eauto using red_eq_context_upto_names.
  Qed.

  Instance proper_red_ctx :
    Proper (eq_context_upto_names ==> eq_context_upto_names ==> iffT) red_ctx.
  Proof.
    reduce_goal.
    split.
    intros. eapply eq_context_upto_names_red_ctx; eauto.
    intros. symmetry in X, X0. eapply eq_context_upto_names_red_ctx; eauto.
  Qed.

  Lemma clos_rt_red1_alpha_out x y :
    clos_refl_trans red1_rel_alpha x y ->
    red_ctx (fst x) (fst y) *
    clos_refl_trans (red1 Σ (fst x)) (snd x) (snd y).
  Proof.
    intros H.
    eapply clos_rt_rt1n_iff in H.
    induction H.
    - split. red. induction (fst x) as [|[na [b|] ty] tl]; try constructor; hnf; eauto.
      constructor 2.
    - destruct x as [Γ t], y as [Δ u], z as [Δ' u']; simpl in *.
      destruct IHclos_refl_trans_1n.
      red in r. destruct r.
      * destruct p. subst. split. auto.
        transitivity u; auto.
      * destruct r. destruct p. subst. split.
        apply red1_ctx_pred1_ctx in r.
        apply pred1_ctx_red_ctx in r.
        etransitivity; eauto.
        eapply red_red_ctx; eauto.
        apply red1_ctx_pred1_ctx in r.
        now apply pred1_ctx_red_ctx in r.
        destruct p. subst.
        split; auto.
        eapply eq_context_upto_names_red_ctx. 3:eauto. now symmetry in e. reflexivity.
        eapply clos_rt_red1_eq_context_upto_names; eauto. now symmetry in e.
  Qed.

  Lemma red1_red1_ctx_inv Γ Δ Δ' t u :
     red1 Σ (Γ ,,, Δ) t u ->
     assumption_context Δ ->
     red1_ctx (Γ ,,, Δ) (Γ ,,, Δ') ->
     red Σ (Γ ,,, Δ') t u.
   Proof.
     intros redt assΔ redΔ.
     apply red1_pred1 in redt => //.
     eapply red1_ctx_pred1_ctx in redΔ => //.
     eapply pred1_ctx_pred1 in redt; eauto.
     now eapply pred1_red_r in redt.
   Qed.
  
  Lemma red_red1_ctx_inv Γ Δ Δ' t u :
    red Σ (Γ ,,, Δ) t u ->
    assumption_context Δ ->
    red1_ctx (Γ ,,, Δ) (Γ ,,, Δ') ->
    red Σ (Γ ,,, Δ') t u.
  Proof.
    intros redt assΔ redΔ. induction redt.
    - eapply red1_red1_ctx_inv; eauto.
    - reflexivity.
    - now transitivity y.
  Qed.
    
  Inductive clos_refl_trans_ctx_1n (R : relation context) (x : context) : context -> Type :=
  | rt1n_ctx_eq : clos_refl_trans_ctx_1n R x x
  | rt1n_ctx_trans : forall y z, eq_context_upto_names x y + R x y -> clos_refl_trans_ctx_1n R y z -> clos_refl_trans_ctx_1n R x z.


  Lemma clos_refl_trans_ctx_to_1n (x y : context) :
    clos_refl_trans_ctx red1_ctx x y <~> clos_refl_trans_ctx_1n red1_ctx x y.
  Proof.
    split.
    induction 1. econstructor 2. eauto. constructor; auto.
    econstructor 2. left; eauto. constructor.
    clear X1 X2.
    induction IHX1 in z, IHX2 |- *.
    destruct IHX2. constructor.
    destruct s. econstructor 2. left; eauto. auto.
    econstructor 2. right; eauto. eauto.
    specialize (IHIHX1 _ IHX2). econstructor 2; eauto.

    induction 1. constructor 2. eapply eq_context_upto_names_refl.
    destruct s. econstructor 3. constructor 2; eauto. eauto.
    econstructor 3. constructor 1; eauto. eauto.
  Qed. 

  Lemma clos_rt_red1_red1_rel_alpha Γ x y :
    clos_refl_trans (red1 Σ Γ) x y -> clos_refl_trans red1_rel_alpha (Γ, x) (Γ, y).
  Proof.
    induction 1. constructor. red. left. firstorder.
    constructor 2.
    econstructor 3; eauto.
  Qed.

  Lemma red1_confluent Γ : confluent (red1 Σ Γ).
  Proof.
    intros x y z.
    intros.
    pose proof (pred_rel_confluent (Γ, x) (Γ, y) (Γ, z)).
    forward X1 by now eapply clos_rt_red1_red1_rel_alpha.
    forward X1 by now eapply clos_rt_red1_red1_rel_alpha.
    destruct X1 as [[Δ nf] [redl redr]].
    exists nf.
    eapply clos_rt_red1_alpha_out in redl.
    eapply clos_rt_red1_alpha_out in redr. simpl in *.
    intuition auto.
  Qed.

  Lemma pred_red {Γ t u} :
    clos_refl_trans (pred1 Σ Γ Γ) t u ->
    clos_refl_trans (red1 Σ Γ) t u.
  Proof.
    intros pred.
    eapply (clos_rt_red1_rel_red1 (Γ, t) (Γ, u)).
    apply clos_refl_trans_out.
    apply (clos_rt_red1_alpha_out (Γ, t) (Γ, u)).
    apply clos_red_rel_out_inv.
    induction pred. constructor; auto. constructor 2.
    now transitivity (Γ, y).
  Qed.

End RedConfluence.

Arguments red1_ctx _ _ _ : clear implicits.


Section ConfluenceFacts.
  Context {cf : checker_flags}.
  Context (Σ : global_env) (wfΣ : wf Σ).

  Lemma red_mkApps_tConstruct (Γ : context)
        ind pars k (args : list term) c :
    red Σ Γ (mkApps (tConstruct ind pars k) args) c ->
    ∑ args' : list term,
    (c = mkApps (tConstruct ind pars k) args') * (All2 (red Σ Γ) args args').
  Proof.
    move => Hred. eapply red_pred in Hred.
    generalize_eq x (mkApps (tConstruct ind pars k) args).
    induction Hred in ind, pars, k, args |- * ; simplify *.
    - eapply pred1_mkApps_tConstruct in r as [r' [eq redargs]].
      subst y. exists r'. intuition auto. solve_all. now apply pred1_red in X.
    - exists args; split; eauto. apply All2_same; auto.
    - specialize IHHred1 as [? [? ?]]. reflexivity. subst y.
      specialize (IHHred2 _ _ _ _ eq_refl) as [? [? ?]]. subst z.
      exists x0. intuition auto. eapply All2_trans; eauto.
      intros ? ? ?; eapply red_trans.
    - assumption.
  Qed.

  Lemma red_mkApps_tInd (Γ : context)
        ind u (args : list term) c :
    red Σ Γ (mkApps (tInd ind u) args) c ->
    ∑ args' : list term,
    (c = mkApps (tInd ind u) args') * (All2 (red Σ Γ) args args').
  Proof.
    move => Hred. eapply red_pred in Hred; tas.
    generalize_eq x (mkApps (tInd ind u) args).
    induction Hred in ind, u, args |- * ; simplify *.
    - eapply pred1_mkApps_tInd in r as [r' [eq redargs]].
      subst y. exists r'. intuition auto. solve_all. now apply pred1_red in X.
    - exists args; split; eauto. apply All2_same; auto.
    - specialize IHHred1 as [? [? ?]]. reflexivity. subst y.
      specialize (IHHred2 _ _ _ eq_refl) as [? [? ?]]. subst z.
      exists x0. intuition auto. eapply All2_trans; eauto.
      intros ? ? ?; eapply red_trans.
  Qed.

  Lemma red_mkApps_tRel (Γ : context) k b (args : list term) c :
    nth_error Γ k = Some b -> decl_body b = None ->
    red Σ Γ (mkApps (tRel k) args) c ->
    ∑ args' : list term,
    (c = mkApps (tRel k) args') * (All2 (red Σ Γ) args args').
  Proof.
    move => Hnth Hb Hred. eapply red_pred in Hred; tas.
    generalize_eq x (mkApps (tRel k) args).
    induction Hred in k, b, Hnth, Hb, args |- * ; simplify *.
    - eapply pred1_mkApps_tRel in r as [r' [eq redargs]]; eauto.
      subst y. exists r'. intuition auto. solve_all. now apply pred1_red in X.
    - exists args; split; eauto. apply All2_same; auto.
    - specialize IHHred1 as [? [? ?]]; eauto. subst.
      specialize (IHHred2 _ _ _ Hnth Hb eq_refl) as [? [? ?]]. subst z.
      exists x0. intuition auto. eapply All2_trans; eauto.
      intros ? ? ?; eapply red_trans.
  Qed.

  Lemma red_mkApps_tConst_axiom (Γ : context)
        cst u (args : list term) cb c :
    declared_constant Σ cst cb -> cst_body cb = None ->
    red Σ Γ (mkApps (tConst cst u) args) c ->
    ∑ args' : list term,
    (c = mkApps (tConst cst u) args') * (All2 (red Σ Γ) args args').
  Proof.
    move => Hdecl Hbody Hred. eapply red_pred in Hred; tas.
    generalize_eq x (mkApps (tConst cst u) args).
    induction Hred in cst, u, args, Hdecl |- *; simplify *.
    - eapply pred1_mkApps_tConst_axiom in r as [r' [eq redargs]]; eauto.
      subst y. exists r'. intuition auto. solve_all. now apply pred1_red in X.
    - exists args; split; eauto. apply All2_same; auto.
    - specialize (IHHred1 _ _ _ Hdecl eq_refl) as [? [? ?]]. subst y.
      specialize (IHHred2 _ _ _ Hdecl eq_refl) as [? [? ?]]. subst z.
      exists x0. intuition auto. eapply All2_trans; eauto.
      intros ? ? ?; eapply red_trans.
  Qed.

  Lemma clos_rt_red1_ctx_red_ctx :
    inclusion (clos_refl_trans (@red1_ctx Σ)) (@red_ctx Σ).
  Proof.
    intros x y H. induction H.
    - apply red1_ctx_pred1_ctx in r => //.
      apply pred1_ctx_red_ctx in r => //.
    - reflexivity.
    - now eapply (red_ctx_trans wfΣ); eauto.
  Qed.

  Lemma red_confluence {Γ t u v} :
    red Σ Γ t u -> red Σ Γ t v ->
    ∑ v', red Σ Γ u v' * red Σ Γ v v'.
  Proof.
    move=> H H'.
    destruct (red1_confluent wfΣ _ _ _ _ H H') as [nf [redl redr]].
    exists nf; intuition auto.
  Qed.

End ConfluenceFacts.

Arguments red_confluence {cf} {Σ} wfΣ {Γ t u v}.

(** We can now derive transitivity of the conversion relation,
    see [PCUICConversion.v] *)
