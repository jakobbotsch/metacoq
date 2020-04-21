(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool List Arith CMorphisms.
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICReflect PCUICLiftSubst.

Require Import ssreflect.
From Equations.Prop Require Import DepElim.
Set Equations With UIP.


Local Open Scope type_scope.

Section CRelationLemmas.
  Local Set Universe Polymorphism.
  Context {A : Type} (R : crelation A).

  Lemma flip_Reflexive : Reflexive R -> Reflexive (flip R).
  Proof.
    intros HR x. unfold flip. apply reflexivity.
  Qed.

  Lemma flip_Symmetric : Symmetric R -> Symmetric (flip R).
  Proof.
    intros HR x y. unfold flip. apply symmetry.
  Qed.

  Lemma flip_Transitive : Transitive R -> Transitive (flip R).
  Proof.
    intros HR x y z xy yz.
    unfold flip in *. now transitivity y.
  Qed.

End CRelationLemmas.

Definition R_universe_instance R :=
  fun u u' => Forall2 R (List.map Universe.make u) (List.map Universe.make u').

Lemma R_universe_instance_impl R R' :
  RelationClasses.subrelation R R' ->
  RelationClasses.subrelation (R_universe_instance R) (R_universe_instance R').
Proof.
  intros H x y xy. eapply Forall2_impl ; tea.
Qed.

Lemma R_universe_instance_impl' R R' :
  RelationClasses.subrelation R R' ->
  forall u u', R_universe_instance R u u' -> R_universe_instance R' u u'.
Proof.
  intros H x y xy. eapply Forall2_impl ; tea.
Qed.

(** ** Syntactic equality up-to universes
  We don't look at printing annotations *)

Inductive eq_term_upto_univ (Re Rle : Universe.t -> Universe.t -> Prop) : term -> term -> Type :=
| eq_Rel n  :
    eq_term_upto_univ Re Rle (tRel n) (tRel n)

| eq_Evar e args args' :
    All2 (eq_term_upto_univ Re Re) args args' ->
    eq_term_upto_univ Re Rle (tEvar e args) (tEvar e args')

| eq_Var id :
    eq_term_upto_univ Re Rle (tVar id) (tVar id)

| eq_Sort s s' :
    Rle s s' ->
    eq_term_upto_univ Re Rle (tSort s) (tSort s')

| eq_App t t' u u' :
    eq_term_upto_univ Re Rle t t' ->
    eq_term_upto_univ Re Re u u' ->
    eq_term_upto_univ Re Rle (tApp t u) (tApp t' u')

| eq_Const c u u' :
    R_universe_instance Re u u' ->
    eq_term_upto_univ Re Rle (tConst c u) (tConst c u')

| eq_Ind i u u' :
    R_universe_instance Re u u' ->
    eq_term_upto_univ Re Rle (tInd i u) (tInd i u')

| eq_Construct i k u u' :
    R_universe_instance Re u u' ->
    eq_term_upto_univ Re Rle (tConstruct i k u) (tConstruct i k u')

| eq_Lambda na na' ty ty' t t' :
    eq_term_upto_univ Re Re ty ty' ->
    eq_term_upto_univ Re Rle t t' ->
    eq_term_upto_univ Re Rle (tLambda na ty t) (tLambda na' ty' t')

| eq_Prod na na' a a' b b' :
    eq_term_upto_univ Re Re a a' ->
    eq_term_upto_univ Re Rle b b' ->
    eq_term_upto_univ Re Rle (tProd na a b) (tProd na' a' b')

| eq_LetIn na na' t t' ty ty' u u' :
    eq_term_upto_univ Re Re t t' ->
    eq_term_upto_univ Re Re ty ty' ->
    eq_term_upto_univ Re Rle u u' ->
    eq_term_upto_univ Re Rle (tLetIn na t ty u) (tLetIn na' t' ty' u')

| eq_Case indn p p' c c' brs brs' :
    eq_term_upto_univ Re Re p p' ->
    eq_term_upto_univ Re Re c c' ->
    All2 (fun x y =>
      (fst x = fst y) *
      eq_term_upto_univ Re Re (snd x) (snd y)
    ) brs brs' ->
    eq_term_upto_univ Re Rle (tCase indn p c brs) (tCase indn p' c' brs')

| eq_Proj p c c' :
    eq_term_upto_univ Re Re c c' ->
    eq_term_upto_univ Re Rle (tProj p c) (tProj p c')

| eq_Fix mfix mfix' idx :
    All2 (fun x y =>
      eq_term_upto_univ Re Re x.(dtype) y.(dtype) *
      eq_term_upto_univ Re Re x.(dbody) y.(dbody) *
      (x.(rarg) = y.(rarg))
    ) mfix mfix' ->
    eq_term_upto_univ Re Rle (tFix mfix idx) (tFix mfix' idx)

| eq_CoFix mfix mfix' idx :
    All2 (fun x y =>
      eq_term_upto_univ Re Re x.(dtype) y.(dtype) *
      eq_term_upto_univ Re Re x.(dbody) y.(dbody) *
      (x.(rarg) = y.(rarg))
    ) mfix mfix' ->
    eq_term_upto_univ Re Rle (tCoFix mfix idx) (tCoFix mfix' idx).


(* ** Syntactic conversion up-to universes *)

Definition eq_term `{checker_flags} φ :=
  eq_term_upto_univ (eq_universe φ) (eq_universe φ).

(* ** Syntactic cumulativity up-to universes *)

Definition leq_term `{checker_flags} φ :=
  eq_term_upto_univ (eq_universe φ) (leq_universe φ).

Instance eq_term_upto_univ_refl Re Rle :
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  Reflexive (eq_term_upto_univ Re Rle).
Proof.
  intros hRe hRle t.
  induction t in Rle, hRle |- * using term_forall_list_ind.
  all: simpl.
  all: try constructor. all: eauto.
  all: try solve [eapply All_All2 ; eauto].
  all: try solve [eapply Forall2_same ; eauto].
  - eapply All_All2; eauto. simpl. intuition eauto.
  - eapply All_All2; eauto. simpl. intuition eauto.
Qed.

Instance eq_term_refl `{checker_flags} φ : Reflexive (eq_term φ).
Proof.
  apply eq_term_upto_univ_refl. all: exact _.
Qed.

Instance leq_term_refl `{checker_flags} φ : Reflexive (leq_term φ).
Proof.
  apply eq_term_upto_univ_refl; exact _.
Qed.

(* TODO MOVE *)
Existing Instance All2_symP.

(* TODO MOVE *)
Instance Forall2_symP :
  forall A (P : A -> A -> Prop),
    RelationClasses.Symmetric P ->
    Symmetric (Forall2 P).
Proof.
  intros A P h l l' hl.
  induction hl. all: auto.
Qed.

Derive Signature for eq_term_upto_univ.

Instance eq_term_upto_univ_sym Re Rle :
  RelationClasses.Symmetric Re ->
  RelationClasses.Symmetric Rle ->
  Symmetric (eq_term_upto_univ Re Rle).
Proof.
  intros he hle u v e.
  induction u in Rle, hle, v, e |- * using term_forall_list_ind.
  all: dependent destruction e.
  all: try solve [
    econstructor ; eauto ;
    try eapply Forall2_symP ; eauto
  ].
  - econstructor.
    eapply All2_All_mix_left in X as h; eauto.
    clear a X.
    induction h.
    + constructor.
    + destruct r as [h1 h2]. eapply h1 in h2 ; auto.
  - econstructor; eauto.
    eapply All2_All_mix_left in X as h; eauto.
    clear a X.
    induction h.
    + constructor.
    + destruct r as [h1 [h2 h3]]. eapply h1 in h3 ; auto.
  - econstructor.
    eapply All2_All_mix_left in X as h; eauto.
    clear a X.
    induction h.
    + constructor.
    + destruct r as [[h1 h2] [[h3 h4] h5]].
      eapply h1 in h3 ; auto.
  - econstructor.
    eapply All2_All_mix_left in X as h; eauto.
    clear a X.
    induction h.
    + constructor.
    + destruct r as [[h1 h2] [[h3 h4] h5]]. eapply h1 in h3 ; auto.
Qed.

Instance eq_term_sym `{checker_flags} φ : Symmetric (eq_term φ).
Proof.
  eapply eq_term_upto_univ_sym. all: exact _.
Qed.


Instance eq_term_upto_univ_trans Re Rle :
  RelationClasses.Transitive Re ->
  RelationClasses.Transitive Rle ->
  Transitive (eq_term_upto_univ Re Rle).
Proof.
  intros he hle u v w e1 e2.
  induction u in Rle, hle, v, w, e1, e2 |- * using term_forall_list_ind.
  all: dependent destruction e1.
  all: try solve [ eauto ].
  all: try solve [
    dependent destruction e2 ; econstructor ; eauto ;
    try eapply Forall2_trans ; eauto
  ].
  - dependent destruction e2.
    econstructor.
    eapply All2_All_mix_left in X as h; eauto.
    clear a X.
    induction h in a0, args'0 |- *.
    + assumption.
    + dependent destruction a0. constructor ; eauto.
      destruct r as [h1 h2]. eauto.
  - dependent destruction e2.
    econstructor; eauto.
    eapply All2_All_mix_left in X as h; eauto.
    clear a X.
    induction h in a0, brs'0 |- *.
    + assumption.
    + dependent destruction a0. constructor ; eauto.
      destruct r as [h1 [h2 h3]].
      destruct p0 as [? ?]. split; eauto.
      transitivity (fst y); auto.
  - dependent destruction e2.
    econstructor.
    eapply All2_All_mix_left in X as h; eauto.
    clear a X.
    induction h in a0, mfix'0 |- *.
    + assumption.
    + dependent destruction a0. constructor ; eauto.
      intuition eauto.
      transitivity (rarg y); auto.
  - dependent destruction e2.
    econstructor.
    eapply All2_All_mix_left in X as h; eauto.
    clear a X.
    induction h in a0, mfix'0 |- *.
    + assumption.
    + dependent destruction a0. constructor ; eauto.
      intuition eauto.
      transitivity (rarg y); auto.
Qed.

Instance eq_term_trans {cf:checker_flags} φ : Transitive (eq_term φ).
Proof.
  eapply eq_term_upto_univ_trans. all: exact _.
Qed.

Instance leq_term_trans {cf:checker_flags} φ : Transitive (leq_term φ).
Proof.
  eapply eq_term_upto_univ_trans ; exact _.
Qed.


Instance eq_term_upto_univ_equiv Re (hRe : RelationClasses.Equivalence Re)
  : Equivalence (eq_term_upto_univ Re Re).
Proof.
  constructor. all: exact _.
Defined.

Instance eq_term_equiv {cf:checker_flags} φ : Equivalence (eq_term φ) :=
  {| Equivalence_Reflexive := eq_term_refl _;
     Equivalence_Symmetric := eq_term_sym _;
     Equivalence_Transitive := eq_term_trans _ |}.

Instance leq_term_preorder {cf:checker_flags} φ : PreOrder (leq_term φ) :=
  {| PreOrder_Reflexive := leq_term_refl _;
     PreOrder_Transitive := leq_term_trans _ |}.

Instance R_universe_instance_equiv R (hR : RelationClasses.Equivalence R)
  : RelationClasses.Equivalence (R_universe_instance R).
Proof.
  split.
  - intro. apply Forall2_same. reflexivity.
  - intros x y xy. eapply Forall2_sym, Forall2_impl; tea. now symmetry.
  - intros x y z xy yz. eapply Forall2_trans; tea. apply hR.
Qed.

Lemma R_universe_instance_antisym Re Rle (hRe : RelationClasses.Equivalence Re) :
  RelationClasses.Antisymmetric _ Re Rle ->
  RelationClasses.Antisymmetric _ (R_universe_instance Re) (R_universe_instance Rle).
Proof.
  intros H x y H1 H2.
  eapply Forall2_sym in H2.
  eapply Forall2_impl; [eapply Forall2_and|]; [exact H1|exact H2|].
  cbn; intros ? ? [? ?]. eapply H; assumption.
Qed.

Lemma eq_term_upto_univ_antisym Re Rle (hRe : RelationClasses.Equivalence Re) :
  RelationClasses.Antisymmetric _ Re Rle ->
  Antisymmetric (eq_term_upto_univ Re Re) (eq_term_upto_univ Re Rle).
Proof.
  intros hR u v h h'.
  induction u in v, h, h' |- * using term_forall_list_ind.
  all: simpl ; inversion h ; subst; inversion h' ;
       subst ; try constructor ; auto.
Qed.

Instance leq_term_antisym {cf:checker_flags} φ
  : Antisymmetric (eq_term φ) (leq_term φ).
Proof.
  eapply eq_term_upto_univ_antisym; exact _.
Qed.


Instance eq_term_upto_univ_impl Re Re' Rle Rle' :
  RelationClasses.subrelation Re Re' ->
  RelationClasses.subrelation Rle Rle' ->
  subrelation (eq_term_upto_univ Re Rle) (eq_term_upto_univ Re' Rle').
Proof.
  intros he hle t t'.
  induction t in t', Rle, Rle', hle |- * using term_forall_list_ind;
    try (inversion 1; subst; constructor;
         eauto using R_universe_instance_impl'; fail).
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
  - inversion 1; subst; constructor; eauto.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x ? y [? ?]. split; eauto.
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x [? ?] y [[? ?] ?]. repeat split; eauto.
  - inversion 1; subst; constructor.
    eapply All2_impl'; tea.
    eapply All_impl; eauto.
    cbn. intros x [? ?] y [[? ?] ?]. repeat split; eauto.
Qed.


Instance eq_term_upto_univ_leq Re Rle :
  RelationClasses.subrelation Re Rle ->
  subrelation (eq_term_upto_univ Re Re) (eq_term_upto_univ Re Rle).
Proof.
  intros H. eapply eq_term_upto_univ_impl; exact _.
Qed.

Instance eq_term_leq_term {cf:checker_flags} φ
  : subrelation (eq_term φ) (leq_term φ).
Proof.
  eapply eq_term_upto_univ_leq; exact _.
Qed.

Instance leq_term_partial_order {cf:checker_flags} φ
  : PartialOrder (eq_term φ) (leq_term φ).
Proof.
  split. intros eqxy; split; now eapply eq_term_leq_term.
  intros [xy yx].
  now eapply leq_term_antisym.
Qed.


Local Ltac lih :=
  lazymatch goal with
  | ih : forall Rle v n k, eq_term_upto_univ _ _ ?u _ -> _
    |- eq_term_upto_univ _ _ (lift _ _ ?u) _ =>
    eapply ih
  end.

Lemma eq_term_upto_univ_lift Re Rle n k :
  Proper (eq_term_upto_univ Re Rle ==> eq_term_upto_univ Re Rle) (lift n k).
Proof.
  intros u v e.
  induction u in v, n, k, e, Rle |- * using term_forall_list_ind.
  all: dependent destruction e.
  all: try (cbn ; constructor ; try lih ; assumption).
  - cbn. constructor. solve_all.
  - cbn. constructor ; try lih ; try assumption. solve_all.
  - cbn. constructor.
    pose proof (All2_length _ _ a).
    solve_all. rewrite H. cbn. eauto.
  - cbn. constructor.
    pose proof (All2_length _ _ a).
    solve_all. rewrite H. cbn. eauto.
Qed.

Lemma lift_eq_term {cf:checker_flags} φ n k T U :
  eq_term φ T U -> eq_term φ (lift n k T) (lift n k U).
Proof.
  apply eq_term_upto_univ_lift.
Qed.

Lemma lift_leq_term {cf:checker_flags} φ n k T U :
  leq_term φ T U -> leq_term φ (lift n k T) (lift n k U).
Proof.
  apply eq_term_upto_univ_lift.
Qed.


Local Ltac sih :=
  lazymatch goal with
  | ih : forall Rle v n x y, _ -> eq_term_upto_univ _ _ ?u _ -> _ -> _
    |- eq_term_upto_univ _ _ (subst _ _ ?u) _ => eapply ih
  end.

Lemma eq_term_upto_univ_substs Re Rle :
  RelationClasses.subrelation Re Rle ->
  forall u v n l l',
    eq_term_upto_univ Re Rle u v ->
    All2 (eq_term_upto_univ Re Re) l l' ->
    eq_term_upto_univ Re Rle (subst l n u) (subst l' n v).
Proof.
  unfold RelationClasses.subrelation; intros hR u v n l l' hu hl.
  induction u in v, n, l, l', hu, hl, Rle, hR |- * using term_forall_list_ind.
  all: dependent destruction hu.
  all: try solve [ cbn ; constructor ; try sih ; eauto ].
  - cbn. destruct (Nat.leb_spec0 n n0).
    + case_eq (nth_error l (n0 - n)).
      * intros t e. eapply All2_nth_error_Some in e as h ; eauto.
        destruct h as [t' [e' h]].
        rewrite e'.
        eapply eq_term_upto_univ_lift.
        eapply eq_term_upto_univ_leq ; eauto.
      * intros h. eapply All2_nth_error_None in h as hh ; eauto.
        rewrite hh.
        apply All2_length in hl as e. rewrite <- e.
        constructor.
    + constructor.
  - cbn. constructor. solve_all.
  - cbn. constructor ; try sih ; eauto. solve_all.
  - cbn. constructor ; try sih ; eauto.
    pose proof (All2_length _ _ a).
    solve_all. cbn. now rewrite H.
  - cbn. constructor ; try sih ; eauto.
    pose proof (All2_length _ _ a).
    solve_all. cbn. now rewrite H.
Qed.

Lemma eq_term_upto_univ_subst Re Rle :
  RelationClasses.subrelation Re Rle ->
  forall u v n x y,
    eq_term_upto_univ Re Rle u v ->
    eq_term_upto_univ Re Re x y ->
    eq_term_upto_univ Re Rle (u{n := x}) (v{n := y}).
Proof.
  intros hR u v n x y e1 e2.
  eapply eq_term_upto_univ_substs; eauto.
Qed.

Lemma subst_eq_term {cf:checker_flags} φ l k T U :
  eq_term φ T U ->
  eq_term φ (subst l k T) (subst l k U).
Proof.
  intros Hleq.
  eapply eq_term_upto_univ_substs; try easy.
  now eapply All2_same.
Qed.

Lemma subst_leq_term {cf:checker_flags} φ l k T U :
  leq_term φ T U ->
  leq_term φ (subst l k T) (subst l k U).
Proof.
  intros Hleq.
  eapply eq_term_upto_univ_substs; try easy.
  intro; apply eq_universe_leq_universe.
  now eapply All2_same.
Qed.



(** ** Boolean version **  *)

Fixpoint eqb_term_upto_univ (equ lequ : Universe.t -> Universe.t -> bool) (u v : term) : bool :=
  match u, v with
  | tRel n, tRel m =>
    eqb n m

  | tEvar e args, tEvar e' args' =>
    eqb e e' &&
    forallb2 (eqb_term_upto_univ equ equ) args args'

  | tVar id, tVar id' =>
    eqb id id'

  | tSort u, tSort u' =>
    lequ u u'

  | tApp u v, tApp u' v' =>
    eqb_term_upto_univ equ lequ u u' &&
    eqb_term_upto_univ equ equ v v'

  | tConst c u, tConst c' u' =>
    eqb c c' &&
    forallb2 equ (map Universe.make u) (map Universe.make u')

  | tInd i u, tInd i' u' =>
    eqb i i' &&
    forallb2 equ (map Universe.make u) (map Universe.make u')

  | tConstruct i k u, tConstruct i' k' u' =>
    eqb i i' &&
    eqb k k' &&
    forallb2 equ (map Universe.make u) (map Universe.make u')

  | tLambda na A t, tLambda na' A' t' =>
    eqb_term_upto_univ equ equ A A' &&
    eqb_term_upto_univ equ lequ t t'

  | tProd na A B, tProd na' A' B' =>
    eqb_term_upto_univ equ equ A A' &&
    eqb_term_upto_univ equ lequ B B'

  | tLetIn na B b u, tLetIn na' B' b' u' =>
    eqb_term_upto_univ equ equ B B' &&
    eqb_term_upto_univ equ equ b b' &&
    eqb_term_upto_univ equ lequ u u'

  | tCase indp p c brs, tCase indp' p' c' brs' =>
    eqb indp indp' &&
    eqb_term_upto_univ equ equ p p' &&
    eqb_term_upto_univ equ equ c c' &&
    forallb2 (fun x y =>
      eqb (fst x) (fst y) &&
      eqb_term_upto_univ equ equ (snd x) (snd y)
    ) brs brs'

  | tProj p c, tProj p' c' =>
    eqb p p' &&
    eqb_term_upto_univ equ equ c c'

  | tFix mfix idx, tFix mfix' idx' =>
    eqb idx idx' &&
    forallb2 (fun x y =>
      eqb_term_upto_univ equ equ x.(dtype) y.(dtype) &&
      eqb_term_upto_univ equ equ x.(dbody) y.(dbody) &&
      eqb x.(rarg) y.(rarg)
    ) mfix mfix'

  | tCoFix mfix idx, tCoFix mfix' idx' =>
    eqb idx idx' &&
    forallb2 (fun x y =>
      eqb_term_upto_univ equ equ x.(dtype) y.(dtype) &&
      eqb_term_upto_univ equ equ x.(dbody) y.(dbody) &&
      eqb x.(rarg) y.(rarg)
    ) mfix mfix'

  | _, _ => false
  end.

Ltac eqspec :=
  lazymatch goal with
  | |- context [ eqb ?u ?v ] =>
    destruct (eqb_spec u v) ; nodec ; subst
  end.

Ltac eqspecs :=
  repeat eqspec.

Local Ltac equspec equ h :=
  repeat lazymatch goal with
  | |- context [ equ ?x ?y ] =>
    destruct (h x y) ; nodec ; subst
  end.

Local Ltac ih :=
  repeat lazymatch goal with
  | ih : forall lequ Rle hle t', reflectT (eq_term_upto_univ _ _ ?t _) _,
    hle : forall u u', reflectT (?Rle u u') (?lequ u u')
    |- context [ eqb_term_upto_univ _ ?lequ ?t ?t' ] =>
    destruct (ih lequ Rle hle t') ; nodec ; subst
  end.

Lemma eqb_term_upto_univ_impl (equ lequ : _ -> _ -> bool) Re Rle :
  RelationClasses.subrelation equ Re ->
  RelationClasses.subrelation lequ Rle ->
  subrelation (eqb_term_upto_univ equ lequ) (eq_term_upto_univ Re Rle).
Proof.
  intros he hle t t'.
  induction t in t', lequ, Rle, hle |- * using term_forall_list_ind.
  all: destruct t'; try discriminate 1. all: cbn -[eqb].
  - eqspec; [intros _|discriminate]. constructor.
  - eqspec; [intros _|discriminate]. constructor.
  - eqspec; [|discriminate]. constructor.
    cbn in H. apply forallb2_All2 in H.
    eapply All2_impl'; tea.
    eapply All_impl; tea. eauto.
  - constructor; eauto.
  - intro. rtoProp. constructor; eauto.
  - intro. rtoProp. constructor; eauto.
  - intro. rtoProp. constructor; eauto.
  - intro. rtoProp. constructor; eauto.
  - unfold kername in *. eqspec; [|discriminate].
    intro. rtoProp. constructor; eauto.
    apply forallb2_Forall2 in H0.
    eapply Forall2_impl; tea; eauto.
  - unfold kername in *. eqspec; [|discriminate].
    intro. rtoProp. constructor; eauto.
    apply forallb2_Forall2 in H0.
    eapply Forall2_impl; tea; eauto.
  - unfold kername in *. eqspec; [|discriminate].
    eqspec; [|discriminate].
    intro. rtoProp. constructor; eauto.
    apply forallb2_Forall2 in H0.
    eapply Forall2_impl; tea; eauto.
  - eqspec; [|discriminate]. intro. rtoProp.
    destruct indn. econstructor; eauto.
    apply forallb2_All2 in H0.
    eapply All2_impl'; tea.
    red in X. eapply All_impl; tea.
    cbn -[eqb]. intros x X0 y. eqspec; [|discriminate].
    intro. split; eauto.
  - eqspec; [|discriminate]. intro. constructor; eauto.
  - eqspec; [|discriminate].
    econstructor; eauto.
    cbn -[eqb] in H; apply forallb2_All2 in H.
    eapply All2_impl'; tea.
    red in X. eapply All_impl; tea.
    cbn -[eqb]. intros x X0 y. eqspec; [|rewrite andb_false_r; discriminate].
    intro. rtoProp. split; tas. split; eapply X0; tea.
  - eqspec; [|discriminate].
    econstructor; eauto.
    cbn -[eqb] in H; apply forallb2_All2 in H.
    eapply All2_impl'; tea.
    red in X. eapply All_impl; tea.
    cbn -[eqb]. intros x X0 y. eqspec; [|rewrite andb_false_r; discriminate].
    intro. rtoProp. split; tas. split; eapply X0; tea.
Qed.


Lemma reflect_eq_term_upto_univ equ lequ (Re Rle : Universe.t -> Universe.t -> Prop) :
  (forall u u', reflectT (Re u u') (equ u u')) ->
  (forall u u', reflectT (Rle u u') (lequ u u')) ->
  forall t t', reflectT (eq_term_upto_univ Re Rle t t')
                   (eqb_term_upto_univ equ lequ t t').
Proof.
  intros he hle t t'.
  induction t in t', lequ, Rle, hle |- * using term_forall_list_ind.
  all: destruct t' ; nodec.
  (* all: try solve [ *)
  (*   cbn - [eqb] ; eqspecs ; equspec equ h ; ih ; *)
  (*   constructor ; constructor ; assumption *)
  (* ]. *)
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    constructor. constructor ; assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    constructor. constructor ; assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    cbn.
    induction X in l0 |- *.
    + destruct l0.
      * constructor. constructor. constructor.
      * constructor. intro bot. inversion bot. inversion X.
    + destruct l0.
      * constructor. intro bot. inversion bot. subst. inversion X0.
      * cbn. destruct (p _ _ he t).
        -- destruct (IHX l0).
           ++ constructor. constructor. constructor ; try assumption.
              inversion e0. subst. assumption.
           ++ constructor. intro bot. inversion bot. subst.
              inversion X0. subst.
              apply f. constructor. assumption.
        -- constructor. intro bot. apply f.
           inversion bot. subst. inversion X0. subst. assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    constructor. constructor. assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    constructor. constructor ; assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    constructor. constructor ; assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    constructor. constructor ; assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    constructor. constructor ; assumption.
  - cbn - [eqb].
    pose proof (eqb_spec s k) as H.
    match goal with
    | |- context G[ eqb ?x ?y ] =>
      set (toto := eqb x y) in * ;
      let G' := context G[toto] in
      change G'
    end.
    destruct H ; nodec. subst.
    equspec equ he. equspec lequ hle. ih.
    cbn. induction u in ui |- *.
    + destruct ui.
      * constructor. constructor. constructor.
      * constructor. intro bot. inversion bot. subst. inversion H0.
    + destruct ui.
      * constructor. intro bot. inversion bot. subst. inversion H0.
      * cbn. equspec equ he. equspec lequ hle.
        -- cbn. destruct (IHu ui).
           ++ constructor. constructor.
              inversion e. subst.
              constructor ; assumption.
           ++ constructor. intro bot. apply f.
              inversion bot. subst. constructor. inversion H0.
              subst. assumption.
        -- constructor. intro bot. apply f.
           inversion bot. subst. inversion H0. subst.
           assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    simpl. induction u in ui |- *.
    + destruct ui.
      * constructor. constructor. constructor.
      * constructor. intro bot. inversion bot. subst. inversion H0.
    + destruct ui.
      * constructor. intro bot. inversion bot. subst. inversion H0.
      * cbn. equspec equ he. equspec lequ hle.
        -- cbn. destruct (IHu ui).
           ++ constructor. constructor.
              inversion e. subst.
              constructor ; assumption.
           ++ constructor. intro bot. apply f.
              inversion bot. subst. constructor. inversion H0.
              subst. assumption.
        -- constructor. intro bot. apply f.
           inversion bot. subst. inversion H0. subst.
           assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    simpl. induction u in ui |- *.
    + destruct ui.
      * constructor. constructor. constructor.
      * constructor. intro bot. inversion bot. subst. inversion H0.
    + destruct ui.
      * constructor. intro bot. inversion bot. subst. inversion H0.
      * cbn. equspec equ he. equspec lequ hle.
        -- cbn. destruct (IHu ui).
           ++ constructor. constructor.
              inversion e. subst.
              constructor ; assumption.
           ++ constructor. intro bot. apply f.
              inversion bot. subst. constructor. inversion H0.
              subst. assumption.
        -- constructor. intro bot. apply f.
           inversion bot. subst. inversion H0. subst.
           assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    cbn - [eqb].
    destruct indn as [i n].
    induction l in brs, X |- *.
    + destruct brs.
      * constructor. constructor ; try assumption.
        constructor.
      * constructor. intro bot. inversion bot. subst. inversion X2.
    + destruct brs.
      * constructor. intro bot. inversion bot. subst. inversion X2.
      * cbn - [eqb]. inversion X. subst.
        destruct a, p. cbn - [eqb]. eqspecs.
        -- cbn - [eqb]. pose proof (X0 equ Re he t0) as hh. cbn in hh.
           destruct hh.
           ++ cbn - [eqb].
              destruct (IHl X1 brs).
              ** constructor. constructor ; try assumption.
                 constructor ; try easy.
                 inversion e2. subst. assumption.
              ** constructor. intro bot. apply f. inversion bot. subst.
                 constructor ; try assumption.
                 inversion X4. subst. assumption.
           ++ constructor. intro bot. apply f. inversion bot. subst.
              inversion X4. subst. destruct X5. assumption.
        -- constructor. intro bot. inversion bot. subst.
           inversion X4. subst. destruct X5. cbn in e1. subst.
           apply n2. reflexivity.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    constructor. constructor ; assumption.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    cbn - [eqb]. induction m in X, mfix |- *.
    + destruct mfix.
      * constructor. constructor. constructor.
      * constructor. intro bot. inversion bot. subst. inversion X0.
    + destruct mfix.
      * constructor. intro bot. inversion bot. subst. inversion X0.
      * cbn - [eqb]. inversion X. subst.
        destruct X0 as [h1 h2].
        destruct (h1 equ Re he (dtype d)).
        -- destruct (h2 equ Re he (dbody d)).
           ++ cbn - [eqb]. eqspecs.
              ** cbn - [eqb]. destruct (IHm X1 mfix).
                 --- constructor. constructor. constructor ; try easy.
                     inversion e2. assumption.
                 --- constructor. intro bot. apply f.
                     inversion bot. subst. constructor.
                     inversion X0. subst. assumption.
              ** constructor. intro bot. inversion bot. subst.
                 apply n. inversion X0. subst. destruct X2 as [[? ?] ?].
                 assumption.
           ++ constructor. intro bot. apply f.
              inversion bot. subst. inversion X0. subst.
              apply X2.
        -- constructor. intro bot. apply f.
           inversion bot. subst. inversion X0. subst. apply X2.
  - cbn - [eqb]. eqspecs. equspec equ he. equspec lequ hle. ih.
    cbn - [eqb]. induction m in X, mfix |- *.
    + destruct mfix.
      * constructor. constructor. constructor.
      * constructor. intro bot. inversion bot. subst. inversion X0.
    + destruct mfix.
      * constructor. intro bot. inversion bot. subst. inversion X0.
      * cbn - [eqb]. inversion X. subst.
        destruct X0 as [h1 h2].
        destruct (h1 equ Re he (dtype d)).
        -- destruct (h2 equ Re he (dbody d)).
           ++ cbn - [eqb]. eqspecs.
              ** cbn - [eqb]. destruct (IHm X1 mfix).
                 --- constructor. constructor. constructor ; try easy.
                     inversion e2. assumption.
                 --- constructor. intro bot. apply f.
                     inversion bot. subst. constructor.
                     inversion X0. subst. assumption.
              ** constructor. intro bot. inversion bot. subst.
                 apply n. inversion X0. subst. destruct X2 as [[? ?] ?].
                 assumption.
           ++ constructor. intro bot. apply f.
              inversion bot. subst. inversion X0. subst.
              apply X2.
        -- constructor. intro bot. apply f.
           inversion bot. subst. inversion X0. subst. apply X2.
Qed.

Lemma eqb_term_upto_univ_refl :
  forall (eqb leqb : Universe.t -> Universe.t -> bool) t,
    (forall u, eqb u u) ->
    (forall u, leqb u u) ->
    eqb_term_upto_univ eqb leqb t t.
Proof.
  intros eqb leqb t eqb_refl leqb_refl.
  induction t using term_forall_list_ind in leqb, leqb_refl |- *.
  all: simpl.
  all: rewrite -> ?Nat.eqb_refl, ?eq_string_refl, ?eq_inductive_refl.
  all: repeat rewrite -> eq_prod_refl
        by (eauto using eq_prod_refl, Nat.eqb_refl, eq_string_refl, eq_inductive_refl).
  all: repeat lazymatch goal with
      | ih : forall leqb, _ -> @?P leqb |- _ =>
        rewrite -> ih by assumption ; clear ih
      end.
  all: simpl.
  all: try solve [ eauto ].
  - induction X.
    + reflexivity.
    + simpl. rewrite -> p by assumption. auto.
  - eapply forallb2_map. eapply forallb2_refl.
    intro l. eapply eqb_refl.
  - eapply forallb2_map. eapply forallb2_refl.
    intro l. eapply eqb_refl.
  - eapply forallb2_map. eapply forallb2_refl.
    intro l. eapply eqb_refl.
  - induction X.
    + reflexivity.
    + simpl. rewrite Nat.eqb_refl. rewrite -> p0 by assumption.
      assumption.
  - induction X.
    + reflexivity.
    + simpl. rewrite Nat.eqb_refl.
      destruct p as [e1 e2].
      rewrite -> e1 by assumption. rewrite -> e2 by assumption.
      assumption.
  - induction X.
    + reflexivity.
    + simpl. rewrite -> Nat.eqb_refl.
      destruct p as [e1 e2].
      rewrite -> e1 by assumption. rewrite -> e2 by assumption.
      assumption.
Qed.

(** ** Behavior on mkApps and it_mkLambda_or_LetIn **  *)

Lemma eq_term_upto_univ_mkApps Re Rle u1 l1 u2 l2 :
    eq_term_upto_univ Re Rle u1 u2 ->
    All2 (eq_term_upto_univ Re Re) l1 l2 ->
    eq_term_upto_univ Re Rle (mkApps u1 l1) (mkApps u2 l2).
Proof.
  intros hu hl. induction l1 in u1, u2, l2, hu, hl |- *.
  - inversion hl. subst. assumption.
  - inversion hl. subst. simpl.
    eapply IHl1.
    + constructor. all: assumption.
    + assumption.
Qed.

Lemma eq_term_upto_univ_mkApps_l_inv Re Rle u l t :
    eq_term_upto_univ Re Rle (mkApps u l) t ->
    ∑ u' l',
      eq_term_upto_univ Re Rle u u' *
      All2 (eq_term_upto_univ Re Re) l l' *
      (t = mkApps u' l').
Proof.
  intros h. induction l in u, t, h, Rle |- *.
  - cbn in h. exists t, []. split ; auto.
  - cbn in h. apply IHl in h as [u' [l' [[h1 h2] h3]]].
    dependent destruction h1. subst.
    eexists. eexists. split; [ split | ].
    + eassumption.
    + constructor.
      * eassumption.
      * eassumption.
    + cbn. reflexivity.
Qed.

Lemma eq_term_upto_univ_mkApps_r_inv Re Rle u l t :
    eq_term_upto_univ Re Rle t (mkApps u l) ->
    ∑ u' l',
      eq_term_upto_univ Re Rle u' u *
      All2 (eq_term_upto_univ Re Re) l' l *
      (t = mkApps u' l').
Proof.
  intros h. induction l in u, t, h, Rle |- *.
  - cbn in h. exists t, []. split ; auto.
  - cbn in h. apply IHl in h as [u' [l' [[h1 h2] h3]]].
    dependent destruction h1. subst.
    eexists. eexists. split; [ split | ].
    + eassumption.
    + constructor.
      * eassumption.
      * eassumption.
    + cbn. reflexivity.
Qed.

Lemma eq_term_upto_univ_it_mkLambda_or_LetIn Re Rle Γ :
  RelationClasses.Reflexive Re ->
  respectful (eq_term_upto_univ Re Rle) (eq_term_upto_univ Re Rle)
             (it_mkLambda_or_LetIn Γ) (it_mkLambda_or_LetIn Γ).
Proof.
  intros he u v h.
  induction Γ as [| [na [b|] A] Γ ih ] in u, v, h |- *.
  - assumption.
  - simpl. cbn. apply ih. constructor ; try apply eq_term_upto_univ_refl.
    all: auto.
  - simpl. cbn. apply ih. constructor ; try apply eq_term_upto_univ_refl.
    all: auto.
Qed.

Lemma eq_term_it_mkLambda_or_LetIn {cf:checker_flags} φ Γ :
  respectful (eq_term φ) (eq_term φ)
             (it_mkLambda_or_LetIn Γ) (it_mkLambda_or_LetIn Γ).
Proof.
  apply eq_term_upto_univ_it_mkLambda_or_LetIn; exact _.
Qed.

Lemma eq_term_upto_univ_it_mkProd_or_LetIn Re Rle Γ :
  RelationClasses.Reflexive Re ->
  respectful (eq_term_upto_univ Re Rle) (eq_term_upto_univ Re Rle)
             (it_mkProd_or_LetIn Γ) (it_mkProd_or_LetIn Γ).
Proof.
  intros he u v h.
  induction Γ as [| [na [b|] A] Γ ih ] in u, v, h |- *.
  - assumption.
  - simpl. cbn. apply ih. constructor ; try apply eq_term_upto_univ_refl.
    all: auto.
  - simpl. cbn. apply ih. constructor ; try apply eq_term_upto_univ_refl.
    all: auto.
Qed.

Lemma eq_term_it_mkProd_or_LetIn {cf:checker_flags} φ Γ:
  respectful (eq_term φ) (eq_term φ)
             (it_mkProd_or_LetIn Γ) (it_mkProd_or_LetIn Γ).
Proof.
  eapply eq_term_upto_univ_it_mkProd_or_LetIn ; exact _.
Qed.

Lemma eq_term_it_mkLambda_or_LetIn_inv {cf:checker_flags} φ Γ u v :
    eq_term φ (it_mkLambda_or_LetIn Γ u) (it_mkLambda_or_LetIn Γ v) ->
    eq_term φ u v.
Proof.
  revert u v. induction Γ as [| [na [b|] A] Γ ih ] ; intros u v h.
  - assumption.
  - simpl in h. cbn in h. apply ih in h. inversion h. subst.
    assumption.
  - simpl in h. cbn in h. apply ih in h. inversion h. subst.
    assumption.
Qed.


(** ** Syntactic equality up to printing anotations ** *)

Definition upto_names := eq_term_upto_univ eq eq.

Infix "≡" := upto_names (at level 60).

Infix "≡'" := (eq_term_upto_univ eq eq) (at level 60).
Notation upto_names' := (eq_term_upto_univ eq eq).

Instance upto_names_ref : Reflexive upto_names.
Proof.
  eapply eq_term_upto_univ_refl; exact _.
Qed.

Instance upto_names_sym : Symmetric upto_names.
Proof.
  eapply eq_term_upto_univ_sym; exact _.
Qed.

Instance upto_names_trans : Transitive upto_names.
Proof.
  eapply eq_term_upto_univ_trans; exact _.
Qed.

(* todo: rename *)
(* Definition nleq_term t t' := *)
(*   eqb_term_upto_univ eqb eqb t t'. *)

(* Corollary reflect_upto_names : *)
(*   forall t t', reflectT (upto_names t t') (nleq_term t t'). *)
(* Proof. *)
(*   intros t t'. eapply reflect_eq_term_upto_univ. *)
(*   all: intros u u'; eapply reflect_reflectT, eqb_spec. *)
(* Qed. *)

Lemma upto_names_impl Re Rle :
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  subrelation upto_names (eq_term_upto_univ Re Rle).
Proof.
  intros he hle. eapply eq_term_upto_univ_impl.
  all: intros ? ? []; eauto.
Qed.

Lemma upto_names_impl_eq_term {cf:checker_flags} φ u v :
    u ≡ v -> eq_term φ u v.
Proof.
  eapply upto_names_impl ; exact _.
Qed.

Lemma upto_names_impl_leq_term {cf:checker_flags} φ u v :
    u ≡ v -> leq_term φ u v.
Proof.
  eapply upto_names_impl ; exact _.
Qed.



Lemma eq_term_upto_univ_isApp Re Rle u v :
  eq_term_upto_univ Re Rle u v ->
  isApp u = isApp v.
Proof.
  induction 1.
  all: reflexivity.
Qed.


(** ** Equality on contexts ** *)

Inductive eq_context_upto (Re : Universe.t -> Universe.t -> Prop) : context -> context -> Type :=
| eq_context_nil : eq_context_upto Re [] []
| eq_context_vass na A Γ nb B Δ :
    eq_term_upto_univ Re Re A B ->
    eq_context_upto Re Γ Δ ->
    eq_context_upto Re (Γ ,, vass na A) (Δ ,, vass nb B)
| eq_context_vdef na u A Γ nb v B Δ :
    eq_term_upto_univ Re Re u v ->
    eq_term_upto_univ Re Re A B ->
    eq_context_upto Re Γ Δ ->
    eq_context_upto Re (Γ ,, vdef na u A) (Δ ,, vdef nb v B).

Definition eq_def_upto Re d d' : Type :=
  (eq_term_upto_univ Re Re d.(dtype) d'.(dtype)) *
  (eq_term_upto_univ Re Re d.(dbody) d'.(dbody)) *
  (d.(rarg) = d'.(rarg)).

Inductive rel_option {A B} (R : A -> B -> Type) : option A -> option B -> Type :=
| rel_some : forall a b, R a b -> rel_option R (Some a) (Some b)
| rel_none : rel_option R None None.

Definition eq_decl_upto Re d d' : Type :=
  rel_option (eq_term_upto_univ Re Re) d.(decl_body) d'.(decl_body) *
  eq_term_upto_univ Re Re d.(decl_type) d'.(decl_type).

(* TODO perhaps should be def *)
Lemma All2_eq_context_upto Re :
  subrelation (All2 (eq_decl_upto Re)) (eq_context_upto Re).
Proof.
  intros Γ Δ h.
  induction h.
  - constructor.
  - destruct r as [h1 h2].
    destruct x as [na bo ty], y as [na' bo' ty'].
    simpl in h1, h2.
    destruct h1.
    + constructor ; eauto.
    + constructor ; eauto.
Qed.

Lemma eq_context_upto_refl Re :
  RelationClasses.Reflexive Re ->
  Reflexive (eq_context_upto Re).
Proof.
  intros hRe Γ.
  induction Γ as [| [na [bo |] ty] Γ ih].
  - constructor.
  - constructor ; eauto.
    all: eapply eq_term_upto_univ_refl ; eauto.
  - constructor ; eauto.
    all: eapply eq_term_upto_univ_refl ; eauto.
Qed.

Lemma eq_context_upto_sym Re :
  RelationClasses.Symmetric Re ->
  Symmetric (eq_context_upto Re).
Proof.
  intros hRe Γ Δ.
  induction 1; constructor; eauto using eq_term_upto_univ_sym.
  all:eapply eq_term_upto_univ_sym; auto.
Qed.

Lemma eq_context_upto_cat Re Γ Δ Γ' Δ' :
  eq_context_upto Re Γ Γ' ->
  eq_context_upto Re Δ Δ' ->
  eq_context_upto Re (Γ ,,, Δ) (Γ' ,,, Δ').
Proof.
  intros h1 h2. induction h2 in Γ, Γ', h1 |- *.
  - assumption.
  - simpl. constructor ; eauto.
  - simpl. constructor ; eauto.
Qed.

Lemma eq_context_upto_rev Re Γ Δ :
  eq_context_upto Re Γ Δ ->
  eq_context_upto Re (rev Γ) (rev Δ).
Proof.
  induction 1.
  - constructor.
  - rewrite 2!rev_cons. eapply eq_context_upto_cat ; eauto.
    constructor ; eauto. constructor.
  - rewrite 2!rev_cons. eapply eq_context_upto_cat ; eauto.
    constructor ; eauto. constructor.
Qed.

Lemma eq_context_upto_rev' :
  forall Γ Δ Re,
    eq_context_upto Re Γ Δ ->
    eq_context_upto Re (List.rev Γ) (List.rev Δ).
Proof.
  intros Γ Δ Re h.
  induction h.
  - constructor.
  - simpl. eapply eq_context_upto_cat.
    + repeat constructor. assumption.
    + assumption.
  - simpl. eapply eq_context_upto_cat.
    + repeat constructor. all: assumption.
    + assumption.
Qed.

Lemma eq_context_impl :
  forall Re Re',
    RelationClasses.subrelation Re Re' ->
    subrelation (eq_context_upto Re) (eq_context_upto Re').
Proof.
  intros Re Re' hR Γ Δ h.
  induction h.
  - constructor.
  - constructor. 2: assumption.
    eapply eq_term_upto_univ_impl. all: eassumption.
  - constructor. 3: assumption.
    all: eapply eq_term_upto_univ_impl. all: eassumption.
Qed.

Lemma eq_context_upto_length :
  forall Re Γ Δ,
    eq_context_upto Re Γ Δ ->
    #|Γ| = #|Δ|.
Proof.
  intros Re Γ Δ h.
  induction h. all: simpl ; auto.
Qed.

Section ContextUpTo.

  Context (Re : Universe.t -> Universe.t -> Prop).
  Context (ReR : RelationClasses.Reflexive Re).
  Context (ReS : RelationClasses.Symmetric Re).
  Context (ReT : RelationClasses.Transitive Re).

  Notation eq_ctx := (eq_context_upto Re).

  Global Instance eq_ctx_refl : Reflexive eq_ctx.
  Proof. now intros ?; apply eq_context_upto_refl. Qed.

  Global Instance eq_ctx_sym : Symmetric eq_ctx.
  Proof.
    intros x y. now apply eq_context_upto_sym.
  Qed.

  Global Instance eq_ctx_trans : Transitive eq_ctx.
  Proof.
    intros Γ0 Γ1 Γ2 H. induction H in Γ2 |- *.
    - intros H2; inversion H2; subst; constructor; auto.
    - intros H2; inversion H2; subst; constructor; auto.
      etransitivity; eauto.
    - intros H2; inversion H2; subst; constructor; auto.
      all: etransitivity; eauto.
  Qed.

End ContextUpTo.


(* todo: unify *)
Definition eq_opt_term `{checker_flags} φ (t u : option term) :=
  match t, u with
  | Some t, Some u => eq_term φ t u
  | None, None => True
  | _, _ => False
  end.

Definition eq_decl `{checker_flags} φ (d d' : context_decl) :=
  eq_opt_term φ d.(decl_body) d'.(decl_body) * eq_term φ d.(decl_type) d'.(decl_type).

Definition eq_context `{checker_flags} φ (Γ Δ : context) :=
  All2 (eq_decl φ) Γ Δ.


Lemma lift_eq_decl `{checker_flags} ϕ n k d d' :
  eq_decl ϕ d d' -> eq_decl ϕ (lift_decl n k d) (lift_decl n k d').
Proof.
  destruct d, d', decl_body, decl_body0;
    unfold eq_decl, map_decl; cbn; intuition auto using lift_eq_term.
Qed.

Lemma lift_eq_context `{checker_flags} φ l l' n k :
  eq_context φ l l' ->
  eq_context φ (lift_context n k l) (lift_context n k l').
Proof.
  induction l in l', n, k |- *; intros; destruct l'; rewrite -> ?lift_context_snoc0.
  constructor.
  all: inversion X; subst. constructor.
  - apply All2_length in X1. rewrite X1.
    now apply lift_eq_decl.
  - now apply IHl.
Qed.


Lemma eq_term_upto_univ_mkApps_inv Re u l u' l' :
  isApp u = false ->
  isApp u' = false ->
  eq_term_upto_univ Re Re (mkApps u l) (mkApps u' l') ->
  eq_term_upto_univ Re Re u u' * All2 (eq_term_upto_univ Re Re) l l'.
Proof.
  intros hu hu' h.
  apply eq_term_upto_univ_mkApps_l_inv in h as hh.
  destruct hh as [v [args [[h1 h2] h3]]].
  apply eq_term_upto_univ_isApp in h1 as hh1. rewrite hu in hh1.
  apply mkApps_notApp_inj in h3 ; auto.
  destruct h3 as [? ?]. subst. split ; auto.
Qed.

Lemma isLambda_eq_term_l Re u v :
    isLambda u ->
    eq_term_upto_univ Re Re u v ->
    isLambda v.
Proof.
  intros h e.
  destruct u; try discriminate.
  depelim e. auto.
Qed.

Lemma isLambda_eq_term_r Re u v :
    isLambda v ->
    eq_term_upto_univ Re Re u v ->
    isLambda u.
Proof.
  intros h e.
  destruct v ; try discriminate.
  depelim e. auto.
Qed.

Lemma isConstruct_app_eq_term_l Re u v :
    isConstruct_app u ->
    eq_term_upto_univ Re Re u v ->
    isConstruct_app v.
Proof.
  intros h e.
  case_eq (decompose_app u). intros t1 l1 e1.
  case_eq (decompose_app v). intros t2 l2 e2.
  unfold isConstruct_app in *.
  rewrite e1 in h. cbn in h.
  rewrite e2. cbn.
  destruct t1 ; try discriminate.
  apply decompose_app_inv in e1 as ?. subst.
  apply decompose_app_inv in e2 as ?. subst.
  apply eq_term_upto_univ_mkApps_inv in e as hh.
  - destruct hh as [h1 h2].
    dependent destruction h1. reflexivity.
  - reflexivity.
  - eapply decompose_app_notApp. eassumption.
Qed.

Lemma isConstruct_app_eq_term_r :
  forall Re u v,
    isConstruct_app v ->
    eq_term_upto_univ Re Re u v ->
    isConstruct_app u.
Proof.
  intros Re u v h e.
  case_eq (decompose_app u). intros t1 l1 e1.
  case_eq (decompose_app v). intros t2 l2 e2.
  unfold isConstruct_app in *.
  rewrite e2 in h. cbn in h.
  rewrite e1. cbn.
  destruct t2 ; try discriminate.
  apply decompose_app_inv in e1 as ?. subst.
  apply decompose_app_inv in e2 as ?. subst.
  apply eq_term_upto_univ_mkApps_inv in e as hh.
  - destruct hh as [h1 h2].
    dependent destruction h1. reflexivity.
  - eapply decompose_app_notApp. eassumption.
  - reflexivity.
Qed.

(* TODO MOVE *)
Instance subrelation_same :
  forall A (R : A -> A -> Prop),
    RelationClasses.subrelation R R.
Proof.
  intros A R x y h. assumption.
Qed.

Lemma eq_term_upto_univ_flip (Re Rle Rle' : Universe.t -> Universe.t -> Prop) u v :
  RelationClasses.Reflexive Re ->
  RelationClasses.Reflexive Rle ->
  RelationClasses.Symmetric Re ->
  RelationClasses.Transitive Re ->
  RelationClasses.Transitive Rle ->
  RelationClasses.subrelation Re Rle ->
  (forall x y, Rle x y -> Rle' y x) ->
  eq_term_upto_univ Re Rle u v ->
  eq_term_upto_univ Re Rle' v u.
Proof.
  intros Rerefl Rlerefl Resym Retrans Rletrans incl incl' H.
  assert (Resub : RelationClasses.subrelation Re Re).
  { typeclasses eauto. }
  revert Rerefl Rlerefl Resym Retrans Rletrans incl incl' Resub.
  revert Re Rle u v H Rle'.
  induction 1; intros; constructor; intuition auto.
  - eapply All2_symP; auto. eapply eq_term_upto_univ_sym; auto.
  - eapply Forall2_sym. eapply Forall2_map_inv in r.
    eapply Forall2_map. solve_all.
  - eapply Forall2_sym. eapply Forall2_map_inv in r.
    eapply Forall2_map. solve_all.
  - eapply Forall2_sym. eapply Forall2_map_inv in r.
    eapply Forall2_map. solve_all.
  - eapply All2_sym. solve_all.
    simpl in *. subst. now eapply eq_term_upto_univ_sym.
  - eapply All2_sym. solve_all.
    now eapply eq_term_upto_univ_sym.
    now eapply eq_term_upto_univ_sym.
  - eapply All2_sym. solve_all.
    now eapply eq_term_upto_univ_sym.
    now eapply eq_term_upto_univ_sym.
Qed.


Lemma eq_univ_make :
  forall u u',
    Forall2 eq (map Universe.make u) (map Universe.make u') ->
    u = u'.
Proof.
  intros u u' H. eapply Forall2_map' in H.
  eapply Forall2_eq. eapply Forall2_impl; tea.
  clear. intros [] [] H; now inversion H.
Qed.



(** ** Syntactic equality up-to domains
  We don't look at printing annotations *)

Inductive upto_domain : term -> term -> Type :=
| utd_Rel n  : upto_domain (tRel n) (tRel n)

| utd_Evar e args args' :
    All2 (upto_domain) args args' ->
    upto_domain (tEvar e args) (tEvar e args')

| utd_Var id : upto_domain (tVar id) (tVar id)

| utd_Sort s : upto_domain (tSort s) (tSort s)

| utd_App t t' u u' :
    upto_domain t t' ->
    upto_domain u u' ->
    upto_domain (tApp t u) (tApp t' u')

| utd_Const c u : upto_domain (tConst c u) (tConst c u)

| utd_Ind i u : upto_domain (tInd i u) (tInd i u)

| utd_Construct i k u : upto_domain (tConstruct i k u) (tConstruct i k u)

| utd_Lambda na na' ty ty' t t' :
    upto_domain t t' ->
    upto_domain (tLambda na ty t) (tLambda na' ty' t')

| utd_Prod na na' a a' b b' :
    upto_domain a a' ->
    upto_domain b b' ->
    upto_domain (tProd na a b) (tProd na' a' b')

| utd_LetIn na na' t t' ty ty' u u' :
    upto_domain t t' ->
    upto_domain ty ty' ->
    upto_domain u u' ->
    upto_domain (tLetIn na t ty u) (tLetIn na' t' ty' u')

| utd_Case indn p p' c c' brs brs' :
    upto_domain p p' ->
    upto_domain c c' ->
    All2 (fun x y => x.1 = y.1 × upto_domain x.2 y.2) brs brs' ->
    upto_domain (tCase indn p c brs) (tCase indn p' c' brs')

| utd_Proj p c c' :
    upto_domain c c' ->
    upto_domain (tProj p c) (tProj p c')

| utd_Fix mfix mfix' idx :
    All2 (fun x y => upto_domain x.(dtype) y.(dtype) ×
                  upto_domain x.(dbody) y.(dbody) ×
                  x.(rarg) = y.(rarg)
                ) mfix mfix' ->
    upto_domain (tFix mfix idx) (tFix mfix' idx)

| utd_CoFix mfix mfix' idx :
    All2 (fun x y => upto_domain x.(dtype) y.(dtype) ×
                  upto_domain x.(dbody) y.(dbody) ×
                  x.(rarg) = y.(rarg)
                ) mfix mfix' ->
    upto_domain (tCoFix mfix idx) (tCoFix mfix' idx).


Derive Signature for upto_domain.

Instance upto_domain_refl :
  Reflexive upto_domain.
Proof.
  intros t.
  induction t using term_forall_list_ind; constructor; auto.
  all: try solve [eapply All_All2 ; eauto].
  - eapply All_All2; eauto. simpl. intuition eauto.
  - eapply All_All2; eauto. simpl. intuition eauto.
Qed.

Instance upto_domain_sym : Symmetric upto_domain.
Proof.
  intros u v e.
  induction u in v, e |- * using term_forall_list_ind;
    invs e; constructor; eauto.
  all: eapply All2_sym; solve_all.
Qed.

Instance upto_domain_trans : Transitive upto_domain.
Proof.
  intros u v w e1 e2.
  induction u in v, w, e1, e2 |- * using term_forall_list_ind;
    invs e1; invs e2; constructor; eauto.
  - solve_all.
    induction X0 in args'0, X1 |- *; invs X1; constructor; intuition eauto.
  - solve_all.
    induction X2 in brs'0, X5 |- *; invs X5; constructor; intuition eauto.
    rdest; cbn in *; congruence.
  - solve_all.
    induction X0 in mfix'0, X1 |- *; invs X1; constructor; intuition eauto.
    rdest; cbn in *; congruence.
  - solve_all.
    induction X0 in mfix'0, X1 |- *; invs X1; constructor; intuition eauto.
    rdest; cbn in *; congruence.
Qed.
