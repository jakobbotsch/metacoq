From Coq Require Import Bool Arith Lia SetoidList.

Export ListNotations.

Notation "#| l |" := (List.length l) (at level 0, l at level 99, format "#| l |").
Arguments nil {_}, _.

Lemma app_tip_assoc {A} (l : list A) x l' : (l ++ [x]) ++ l' = l ++ (x :: l').
Proof. now rewrite <- app_assoc. Qed.

Fixpoint fold_left_i_aux {A B} (f : A -> nat -> B -> A) (n0 : nat) (l : list B)
         (a0 : A) {struct l} : A
  := match l with
     | [] => a0
     | b :: l => fold_left_i_aux f (S n0) l (f a0 n0 b)
     end.
Definition fold_left_i {A B} f := @fold_left_i_aux A B f 0.

Fixpoint mapi_rec {A B} (f : nat -> A -> B) (l : list A) (n : nat) : list B :=
  match l with
  | [] => []
  | hd :: tl => f n hd :: mapi_rec f tl (S n)
  end.

Definition mapi {A B} (f : nat -> A -> B) (l : list A) := mapi_rec f l 0.

Program Fixpoint safe_nth {A} (l : list A) (n : nat | n < List.length l) : A :=
  match l with
  | nil => _
  | hd :: tl =>
    match n with
    | 0 => hd
    | S n => safe_nth tl n
    end
  end.
Next Obligation.
  exfalso. simpl in H. inversion H.
Defined.
Next Obligation.
  simpl in H. auto with arith.
Defined.


Lemma nth_error_safe_nth {A} n (l : list A) (isdecl : n < Datatypes.length l) :
  nth_error l n = Some (safe_nth l (exist _ n isdecl)).
Proof.
  revert n isdecl; induction l; intros.
  - inversion isdecl.
  - destruct n as [| n']; simpl.
    reflexivity.
    simpl in IHl.
    simpl in isdecl.
    now rewrite <- IHl.
Qed.

Definition rev {A} (l : list A) : list A :=
  let fix aux (l : list A) (acc : list A) : list A :=
      match l with
      | [] => acc
      | x :: l => aux l (x :: acc)
      end
  in aux l [].

Definition rev_map {A B} (f : A -> B) (l : list A) : list B :=
  let fix aux (l : list A) (acc : list B) : list B :=
      match l with
      | [] => acc
      | x :: l => aux l (f x :: acc)
      end
  in aux l [].

Fact rev_cons :
  forall {A} {l} {a : A},
    rev (a :: l) = (rev l ++ [a])%list.
Proof.
  intro A.
  unfold rev.
  match goal with
  | |- forall l a, ?faux _ _ = _ => set (aux := faux)
  end.
  assert (h : forall l acc, aux l acc = (aux l [] ++ acc)%list).
  { intro l. induction l ; intro acc.
    - cbn. reflexivity.
    - cbn. rewrite (IHl [a]). rewrite IHl.
      change (a :: acc) with ([a] ++ acc)%list.
      auto with datatypes.
  }
  intros l a.
  apply h.
Defined.

Fact rev_map_cons :
  forall {A B} {f : A -> B} {l} {a : A},
    rev_map f (a :: l) = (rev_map f l ++ [f a])%list.
Proof.
  intros A B f.
  unfold rev_map.
  match goal with
  | |- forall l a, ?faux _ _ = _ => set (aux := faux)
  end.
  assert (h : forall l acc, aux l acc = (aux l [] ++ acc)%list).
  { intro l. induction l ; intro acc.
    - cbn. reflexivity.
    - cbn. rewrite (IHl [f a]). rewrite IHl.
      change (f a :: acc) with ([f a] ++ acc)%list.
      auto with datatypes.
  }
  intros l a.
  apply h.
Defined.

Fact rev_length :
  forall {A} {l : list A},
    List.length (rev l) = List.length l.
Proof.
  intro A.
  unfold rev.
  match goal with
  | |- context [ List.length (?faux _ _) ] => set (aux := faux)
  end.
  assert (h : forall l acc, List.length (aux l acc) = (List.length acc + List.length l)%nat).
  { intro l. induction l ; intro acc.
    - cbn. auto with arith.
    - cbn. rewrite IHl. cbn. auto with arith.
  }
  intro l. apply h.
Defined.

Fact rev_map_length :
  forall {A B} {f : A -> B} {l : list A},
    List.length (rev_map f l) = List.length l.
Proof.
  intros A B f.
  unfold rev_map.
  match goal with
  | |- context [ List.length (?faux _ _) ] => set (aux := faux)
  end.
  assert (h : forall l acc, List.length (aux l acc) =
                       (List.length acc + List.length l)%nat).
  { intro l. induction l ; intro acc.
    - cbn. auto with arith.
    - cbn. rewrite IHl. cbn. auto with arith.
  }
  intro l. apply h.
Defined.

Fact rev_map_app :
  forall {A B} {f : A -> B} {l1 l2},
    (rev_map f (l1 ++ l2) = rev_map f l2 ++ rev_map f l1)%list.
Proof.
  intros A B f l1 l2. revert B f l2.
  induction l1 ; intros B f l2.
  - simpl. cbn. rewrite app_nil_r. reflexivity.
  - simpl. rewrite !rev_map_cons. rewrite IHl1.
    rewrite app_assoc. reflexivity.
Defined.


Lemma map_map_compose :
  forall (A B C : Type) (f : A -> B) (g : B -> C) (l : list A),
    map g (map f l) = map (fun x => g (f x)) l.
Proof. apply map_map. Qed.

Lemma map_id_f {A} (l : list A) (f : A -> A) :
  (forall x, f x = x) ->
  map f l = l.
Proof.
  induction l; intros; simpl; try easy.
  rewrite H. f_equal. eauto.
Qed.

Section Reverse_Induction.
  Context {A : Type}.
  Lemma rev_list_ind :
    forall P:list A-> Type,
      P [] ->
        (forall (a:A) (l:list A), P (List.rev l) -> P (List.rev (a :: l))) ->
        forall l:list A, P (Coq.Lists.List.rev l).
  Proof.
    induction l; auto.
  Qed.

  Theorem rev_ind :
    forall P:list A -> Type,
      P [] ->
      (forall (x:A) (l:list A), P l -> P (l ++ [x])) -> forall l:list A, P l.
  Proof.
    intros.
    generalize (rev_involutive l).
    intros E; rewrite <- E.
    apply (rev_list_ind P).
    auto.

    simpl.
    intros.
    apply (X0 a (List.rev l0)).
    auto.
  Qed.

End Reverse_Induction.

Lemma skipn_nil :
  forall {A} n, @skipn A n [] = [].
Proof.
  intros A [| n] ; reflexivity.
Qed.


Lemma skipn_S {A} a (l : list A) n : skipn (S n) (a :: l) = skipn n l.
Proof. reflexivity. Qed.

Lemma mapi_ext_size {A B} (f g : nat -> A -> B) l k :
  (forall k' x, k' < k + #|l| -> f k' x = g k' x) ->
  mapi_rec f l k = mapi_rec g l k.
Proof.
  intros Hl. generalize (Le.le_refl k). generalize k at 1 3 4.
  induction l in k, Hl |- *. simpl. auto.
  intros. simpl in *. erewrite Hl; try lia.
  f_equal. eapply (IHl (S k)); try lia. intros. apply Hl. lia.
Qed.

Lemma map_ext_size {A B} (f g : nat -> A -> B) l :
  (forall k x, k < #|l| -> f k x = g k x) ->
  mapi f l = mapi g l.
Proof.
  intros Hl. unfold mapi. apply mapi_ext_size. simpl. auto.
Qed.

Lemma firstn_map {A B} n (f : A -> B) l : firstn n (map f l) = map f (firstn n l).
Proof.
  revert l; induction n. reflexivity.
  destruct l; simpl in *; congruence.
Qed.

Lemma map_ext {A B : Type} (f g : A -> B) (l : list A) :
  (forall x, f x = g x) ->
  map f l = map g l.
Proof.
  intros.
  induction l; trivial.
  intros. simpl. rewrite H. congruence.
Defined.

Require Import ssreflect.

Lemma map_skipn {A B} (f : A -> B) (l : list A) (n : nat) : map f (skipn n l) = skipn n (map f l).
Proof.
  elim: n l => l // IHn.
  by case => //.
Qed.

Lemma nth_error_map {A B} (f : A -> B) n l : nth_error (map f l) n = option_map f (nth_error l n).
Proof.
  elim: n l; case => // IHn l /=.
  - by case: l => //.
  - by case => //.
Qed.

Lemma map_nil {A B} (f : A -> B) (l : list A) : l <> [] -> map f l <> [].
Proof. induction l; simpl; congruence. Qed.
Hint Resolve map_nil : wf.

Inductive nth_error_Spec {A} (l : list A) (n : nat) : option A -> Type :=
| nth_error_Spec_Some x : nth_error l n = Some x -> n < length l -> nth_error_Spec l n (Some x)
| nth_error_Spec_None : length l <= n -> nth_error_Spec l n None.

Lemma mapi_rec_eqn {A B} (f : nat -> A -> B) (l : list A) a n :
  mapi_rec f (a :: l) n = f n a :: mapi_rec f l (S n).
Proof. simpl. f_equal. Qed.

Lemma nth_error_mapi_rec {A B} (f : nat -> A -> B) n k l :
  nth_error (mapi_rec f l k) n = option_map (f (n + k)) (nth_error l n).
Proof.
  induction l in n, k |- *.
  - destruct n; reflexivity.
  - destruct n; simpl.
    + reflexivity.
    + rewrite IHl. by rewrite <- Nat.add_succ_comm.
Qed.

Lemma nth_error_mapi {A B} (f : nat -> A -> B) n l :
  nth_error (mapi f l) n = option_map (f n) (nth_error l n).
Proof.
  unfold mapi; rewrite nth_error_mapi_rec.
  now rewrite -> Nat.add_0_r.
Qed.

Lemma nth_error_Some_length {A} {l : list A} {n t} : nth_error l n = Some t -> n < length l.
Proof. rewrite <- nth_error_Some. destruct (nth_error l n); congruence. Qed.

Lemma nth_error_Some_non_nil {A} (l : list A) (n : nat) (x : A) : nth_error l n = Some x -> l <> [].
Proof.
  destruct l, n; simpl; congruence.
Qed.

Lemma nth_error_spec {A} (l : list A) (n : nat) : nth_error_Spec l n (nth_error l n).
Proof.
  destruct nth_error eqn:Heq.
  constructor; auto. now apply nth_error_Some_length in Heq.
  constructor; auto. now apply nth_error_None in Heq.
Qed.

Lemma nth_error_app_left {A} (l l' : list A) n t : nth_error l n = Some t -> nth_error (l ++ l') n = Some t.
Proof. induction l in n |- *; destruct n; simpl; try congruence. auto. Qed.

Lemma nth_error_nil {A} n : nth_error (nil A) n = None.
Proof. destruct n; auto. Qed.
Hint Rewrite @nth_error_nil.

Fixpoint chop {A} (n : nat) (l : list A) :=
  match n with
  | 0 => ([], l)
  | S n =>
    match l with
    | hd :: tl =>
      let '(l, r) := chop n tl in
      (hd :: l, r)
    | [] => ([], [])
    end
  end.

Lemma nth_map {A} (f : A -> A) n l d :
  (d = f d) ->
  nth n (map f l) d = f (nth n l d).
Proof.
  induction n in l |- *; destruct l; simpl; auto.
Qed.

Lemma mapi_map {A B C} (f : nat -> B -> C) (l : list A) (g : A -> B) :
  mapi f (map g l) = mapi (fun i x => f i (g x)) l.
Proof.
  unfold mapi. generalize 0. induction l; simpl; congruence.
Qed.

Lemma map_mapi {A B C} (f : nat -> A -> B) (l : list A) (g : B -> C) :
  map g (mapi f l) = mapi (fun i x => g (f i x)) l.
Proof.
  unfold mapi. generalize 0. induction l; simpl; congruence.
Qed.

Lemma chop_map {A B} (f : A -> B) n l l' l'' :
  chop n l = (l', l'') -> chop n (map f l) = (map f l', map f l'').
Proof.
  induction n in l, l', l'' |- *; destruct l; try intros [= <- <-]; simpl; try congruence.
  destruct (chop n l) eqn:Heq. specialize (IHn _ _ _ Heq).
  intros [= <- <-]. now rewrite IHn. Qed.

Lemma chop_n_app {A} {l l' : list A} {n} : n = length l -> chop n (l ++ l') = (l, l').
Proof.
  intros ->. induction l; simpl; try congruence.
  now rewrite IHl.
Qed.

Lemma mapi_mapi {A B C} (g : nat -> A -> B) (f : nat -> B -> C) (l : list A) :
  mapi f (mapi g l) = mapi (fun n x => f n (g n x)) l.
Proof. unfold mapi. generalize 0. induction l; simpl; try congruence. Qed.


Lemma mapi_cst_map {A B} (f : A -> B) l : mapi (fun _ => f) l = map f l.
Proof.
  unfold mapi. generalize 0. induction l; cbn; auto. intros. now rewrite IHl.
Qed.

Lemma mapi_rec_ext {A B} (f g : nat -> A -> B) (l : list A) n :
  (forall k x, n <= k -> k < length l + n -> f k x = g k x) ->
  mapi_rec f l n = mapi_rec g l n.
Proof.
  intros Hfg. induction l in n, Hfg |- *; simpl; try congruence.
  intros. rewrite Hfg; simpl; try lia. f_equal.
  rewrite IHl; auto. intros. apply Hfg. simpl; lia. simpl. lia.
Qed.

Lemma mapi_ext {A B} (f g : nat -> A -> B) (l : list A) :
  (forall n x, f n x = g n x) ->
  mapi f l = mapi g l.
Proof. intros; now apply mapi_rec_ext. Qed.

Lemma mapi_rec_Sk {A B} (f : nat -> A -> B) (l : list A) k :
  mapi_rec f l (S k) = mapi_rec (fun n x => f (S n) x) l k.
Proof.
  induction l in k |- *; simpl; congruence.
Qed.

Lemma mapi_rec_add {A B : Type} (f : nat -> A -> B) (l : list A) (n k : nat) :
  mapi_rec f l (n + k) = mapi_rec (fun (k : nat) (x : A) => f (n + k) x) l k.
Proof.
  induction l in n, k |- *; simpl; auto.
  f_equal. rewrite (IHl (S n) k). rewrite mapi_rec_Sk.
  eapply mapi_rec_ext. intros. f_equal. lia.
Qed.

Lemma mapi_rec_app {A B} (f : nat -> A -> B) (l l' : list A) n :
  (mapi_rec f (l ++ l') n = mapi_rec f l n ++ mapi_rec f l' (length l + n))%list.
Proof.
  induction l in n |- *; simpl; try congruence.
  rewrite IHl. f_equal. now rewrite <- Nat.add_succ_comm.
Qed.

Lemma mapi_app {A B} (f : nat -> A -> B) (l l' : list A) :
  (mapi f (l ++ l') = mapi f l ++ mapi (fun n x => f (length l + n) x) l')%list.
Proof.
  unfold mapi; rewrite mapi_rec_app.
  f_equal. generalize 0.
  induction l'; intros. reflexivity. rewrite mapi_rec_eqn.
  change (S (length l + n)) with (S (length l) + n).
  rewrite (Nat.add_succ_comm _ n). now rewrite IHl'.
Qed.

Lemma rev_mapi_rec {A B} (f : nat -> A -> B) (l : list A) n k : k <= n ->
  List.rev (mapi_rec f l (n - k)) = mapi_rec (fun k x => f (Nat.pred (length l) + n - k) x) (List.rev l) k.
Proof.
  unfold mapi. revert n k.
  induction l using rev_ind; simpl; try congruence.
  intros. rewrite rev_unit. simpl.
  rewrite mapi_rec_app rev_app_distr; simpl. rewrite IHl; auto. simpl.
  rewrite app_length. simpl. f_equal. f_equal. lia. rewrite mapi_rec_Sk.
  apply mapi_rec_ext. intros. f_equal. rewrite List.rev_length in H1.
  rewrite Nat.add_1_r. simpl; lia.
Qed.

Lemma rev_mapi {A B} (f : nat -> A -> B) (l : list A) :
  List.rev (mapi f l) = mapi (fun k x => f (Nat.pred (length l) - k) x) (List.rev l).
Proof.
  unfold mapi. change 0 with (0 - 0) at 1.
  rewrite rev_mapi_rec; auto. now rewrite Nat.add_0_r.
Qed.

Lemma mapi_rec_rev {A B} (f : nat -> A -> B) (l : list A) n :
  mapi_rec f (List.rev l) n = List.rev (mapi (fun k x => f (length l + n - S k) x) l).
Proof.
  unfold mapi. revert n.
  induction l using rev_ind; simpl; try congruence.
  intros. rewrite rev_unit. simpl.
  rewrite IHl mapi_rec_app.
  simpl. rewrite rev_unit. f_equal.
  rewrite app_length. simpl. f_equal. lia.
  rewrite app_length. simpl.
  f_equal. eapply mapi_rec_ext. intros.
  f_equal. lia.
Qed.

Lemma mapi_rev {A B} (f : nat -> A -> B) (l : list A) :
  mapi f (List.rev l) = List.rev (mapi (fun k x => f (length l - S k) x) l).
Proof. unfold mapi at 1. rewrite mapi_rec_rev. now rewrite Nat.add_0_r. Qed.

Lemma mapi_rec_length {A B} (f : nat -> A -> B) (l : list A) n :
  length (mapi_rec f l n) = length l.
Proof. induction l in n |- *; simpl; try congruence. Qed.

Lemma mapi_length {A B} (f : nat -> A -> B) (l : list A) :
  length (mapi f l) = length l.
Proof. apply mapi_rec_length. Qed.

Lemma skipn_length {A} n (l : list A) : n <= length l -> length (skipn n l) = length l - n.
Proof.
  induction l in n |- *; destruct n; simpl; auto.
  intros. rewrite IHl; auto with arith.
Qed.

Lemma combine_map_id {A B} (l : list (A * B)) :
 l = combine (map fst l) (map snd l).
Proof.
  induction l ; simpl; try easy.
  destruct a. now f_equal.
Qed.

Local Ltac invs H := inversion H; subst; clear H.

Lemma last_inv A (l1 l2 : list A) x y :
  (l1 ++ [x] = l2 ++ [y] -> l1 = l2 /\ x = y)%list.
Proof.
  revert l2. induction l1; cbn; intros.
  - destruct l2; cbn in H; invs H. eauto. destruct l2; invs H2.
  - destruct l2; invs H. destruct l1; invs H2.
    eapply IHl1 in H2 as []. split; congruence.
Qed.

Arguments skipn : simpl nomatch.

Lemma skipn_all2 :
  forall {A n} (l : list A),
    #|l| <= n ->
         skipn n l = [].
Proof.
  intros A n l h. revert l h.
  induction n ; intros l h.
  - destruct l.
    + reflexivity.
    + cbn in h. inversion h.
  - destruct l.
    + reflexivity.
    + simpl. apply IHn. cbn in h. lia.
Qed.

Lemma not_empty_map {A B} (f : A -> B) l : l <> [] -> map f l <> [].
Proof.
  intro H; destruct l; intro e; now apply H.
Qed.

Lemma nth_error_skipn_add A l m n (a : A) :
  nth_error l (m + n) = Some a ->
  nth_error (skipn m l) n = Some a.
Proof.
  induction m in n, l |- *.
  - cbn. destruct l; firstorder.
  - cbn. destruct l.
    + inversion 1.
    + eapply IHm.
Qed.

Lemma skipn_all_app :
  forall A (l1 l2 : list A),
    skipn #|l1| (l1 ++ l2) = l2.
Proof.
  intros A l1 l2.
  induction l1 in l2 |- *.
  - reflexivity.
  - simpl. eauto.
Qed.

Lemma rev_app :
  forall A (l l' : list A),
    (rev (l ++ l') = rev l' ++ rev l)%list.
Proof.
  intros A l l'.
  induction l in l' |- *.
  - simpl. change (rev (nil A)) with (nil A).
    rewrite app_nil_r. reflexivity.
  - simpl. rewrite rev_cons. rewrite IHl.
    rewrite rev_cons. rewrite app_assoc. reflexivity.
Qed.

Lemma rev_invol :
  forall A (l : list A),
    rev (rev l) = l.
Proof.
  intros A l. induction l ; eauto.
  rewrite rev_cons. rewrite rev_app. simpl.
  rewrite IHl. reflexivity.
Qed.

Lemma list_ind_rev :
  forall A (P : list A -> Prop),
    P nil ->
    (forall a l, P l -> P (l ++ [a])%list) ->
    forall l, P l.
Proof.
  intros A P h1 h2 l.
  rewrite <- rev_invol.
  generalize (rev l). clear l. intro l.
  induction l ; auto.
  rewrite rev_cons. eauto.
Qed.

Lemma list_rect_rev :
  forall A (P : list A -> Type),
    P nil ->
    (forall a l, P l -> P (l ++ [a])%list) ->
    forall l, P l.
Proof.
  intros A P h1 h2 l.
  rewrite <- rev_invol.
  generalize (rev l). clear l. intro l.
  induction l ; auto.
  rewrite rev_cons. eauto.
Qed.



Lemma last_app {A} (l l' : list A) d : l' <> [] -> last (l ++ l') d = last l' d.
Proof.
  revert l'. induction l; simpl; auto. intros.
  destruct l. simpl. destruct l'; congruence. simpl.
  specialize (IHl _ H). apply IHl.
Qed.

Lemma last_nonempty_eq {A} {l : list A} {d d'} : l <> [] -> last l d = last l d'.
Proof.
  induction l; simpl; try congruence.
  intros. destruct l; auto. apply IHl. congruence.
Qed.

Lemma nth_error_removelast {A} (args : list A) n :
  n < Nat.pred #|args| -> nth_error args n = nth_error (removelast args) n.
Proof.
  induction n in args |- *; destruct args; intros; auto.
  simpl. destruct args. inversion H. reflexivity.
  simpl. rewrite IHn. simpl in H. auto with arith.
  destruct args, n; reflexivity.
Qed.

Lemma nth_error_skipn {A} n (l : list A) i : nth_error (skipn n l) i = nth_error l (n + i).
Proof.
  induction l in n, i |- *; destruct n; simpl; auto.
    by case: i.
Qed.

Lemma skipn_skipn {A} n m (l : list A) : skipn n (skipn m l) = skipn (m + n) l.
Proof.
  induction m in n, l |- *. auto.
  simpl. destruct l. destruct n; reflexivity.
  now rewrite skipn_S skipn_S.
Qed.

Lemma skipn_nth_error {A} (l : list A) i :
  match nth_error l i with
  | Some a => skipn i l = a :: skipn (S i) l
  | None => skipn i l = []
  end.
Proof.
  induction l in i |- *. destruct i. reflexivity. reflexivity.
  destruct i. simpl. reflexivity.
  simpl. specialize (IHl i). destruct nth_error.
  rewrite [skipn _ _]IHl. reflexivity.
  rewrite [skipn _ _]IHl. reflexivity.
Qed.

Lemma nth_error_app_ge {A} (l l' : list A) (v : nat) :
  length l <= v ->
  nth_error (l ++ l') v = nth_error l' (v - length l).
Proof.
  revert v; induction l; simpl; intros.
  now rewrite Nat.sub_0_r.
  destruct v. lia.
  simpl. rewrite IHl; auto with arith.
Qed.

Lemma nth_error_app_lt {A} (l l' : list A) (v : nat) :
  v < length l ->
  nth_error (l ++ l') v = nth_error l v.
Proof.
  revert v; induction l; simpl; intros. easy.
  destruct v; trivial.
  simpl. rewrite IHl; auto with arith.
Qed.

Lemma nth_error_rev {A} (l : list A) i : i < #|l| ->
  nth_error l i = nth_error (List.rev l) (#|l| - S i).
Proof.
  revert l. induction i. destruct l; simpl; auto.
  induction l using rev_ind; simpl. auto.
  rewrite rev_app_distr. simpl.
  rewrite app_length. simpl.
  replace (#|l| + 1 - 0) with (S #|l|) by lia. simpl.
  rewrite Nat.sub_0_r in IHl. auto with arith.

  destruct l. simpl; auto. simpl. intros. rewrite IHi. lia.
  assert (#|l| - S i < #|l|) by lia.
  rewrite nth_error_app_lt. rewrite List.rev_length; auto.
  reflexivity.
Qed.

Lemma map_inj :
  forall A B (f : A -> B) l l',
    (forall x y, f x = f y -> x = y) ->
    map f l = map f l' ->
    l = l'.
Proof.
  intros A B f l l' h e.
  induction l in l', e |- *.
  - destruct l' ; try discriminate. reflexivity.
  - destruct l' ; try discriminate. inversion e.
    f_equal ; eauto.
Qed.

Section ListSize.
  Context {A} (size : A -> nat).

  Fixpoint list_size (l : list A) : nat :=
    match l with
    | [] =>  0
    | a :: v => S (size a + list_size v)
    end.

  Lemma list_size_app (l l' : list A)
    : list_size (l ++ l') = list_size l + list_size l'.
  Proof.
    induction l; simpl. reflexivity.
    rewrite IHl; lia.
  Qed.

  Lemma list_size_rev (l : list A)
    : list_size (rev l) = list_size l.
  Proof.
    induction l; simpl. reflexivity.
    rewrite rev_cons list_size_app IHl; cbn; lia.
  Qed.

End ListSize.

Section ListSizeMap.
  Context {A} (sizeA : A -> nat).
  Context {B} (sizeB : B -> nat).

  Lemma list_size_map (f : A -> B) l :
    list_size sizeB (map f l) = list_size (fun x => sizeB (f x)) l.
  Proof.
    induction l; simpl; eauto.
  Qed.

  Lemma list_size_mapi_rec_eq (l : list A) (f : nat -> A -> B) k :
    (forall i x, sizeB (f i x) = sizeA x) ->
    list_size sizeB (mapi_rec f l k) = list_size sizeA l.
  Proof.
    intro H. induction l in k |- *. reflexivity.
    simpl. rewrite IHl. rewrite H. lia.
  Qed.

  Lemma list_size_mapi_eq (l : list A) (f : nat -> A -> B) :
    (forall i x, sizeB (f i x) = sizeA x) ->
    list_size sizeB (mapi f l) = list_size sizeA l.
  Proof.
    unfold mapi. intros. now apply list_size_mapi_rec_eq.
  Qed.

  Lemma list_size_map_eq (l : list A) (f : A -> B) :
    (forall x, sizeA x = sizeB (f x)) ->
    list_size sizeB (map f l) = list_size sizeA l.
  Proof.
    intros.
    induction l; simpl; auto.
  Qed.

  Lemma list_size_mapi_rec_le (l : list A) (f : nat -> A -> B) k :
    (forall i x, sizeB (f i x) <= sizeA x) ->
    list_size sizeB (mapi_rec f l k) <= list_size sizeA l.
  Proof.
    intro H. induction l in k |- *. reflexivity.
    simpl. specialize (H k a). specialize (IHl (S k)). lia.
  Qed.

  Lemma list_size_mapi_le (l : list A) (f : nat -> A -> B) :
    (forall i x, sizeB (f i x) <= sizeA x) ->
    list_size sizeB (mapi f l) <= list_size sizeA l.
  Proof.
    unfold mapi. intros. now apply list_size_mapi_rec_le.
  Qed.

  Lemma list_size_map_le (l : list A) (f : A -> B) :
    (forall x, sizeB (f x) <= sizeA x) ->
    list_size sizeB (map f l) <= list_size sizeA l.
  Proof.
    intros.
    induction l; simpl; auto. specialize (H a).
    lia.
  Qed.

End ListSizeMap.

Lemma list_size_map_hom {A} (size : A -> nat) (l : list A) (f : A -> A) :
  (forall x, size x = size (f x)) ->
  list_size size (map f l) = list_size size l.
Proof.
  intros.
  induction l; simpl; auto.
Defined.

Lemma InA_In_eq {A} x (l : list A) : InA Logic.eq x l <-> In x l.
Proof.
  etransitivity. eapply InA_alt.
  firstorder. now subst.
Qed.

Lemma forallb_rev {A} (p : A -> bool) l :
  forallb p (List.rev l) = forallb p l.
Proof.
  induction l using rev_ind; simpl; try congruence.
  rewrite rev_unit forallb_app. simpl. rewrite <- IHl.
  now rewrite andb_comm andb_true_r.
Qed.

Lemma fold_left_andb_forallb {A} P l x :
  fold_left (fun b x => P x && b) l (P x) = @forallb A P (x :: l).
Proof.
  cbn. rewrite <- fold_left_rev_right. rewrite <- forallb_rev.
  induction (List.rev l); cbn.
  - now rewrite andb_true_r.
  - rewrite IHl0. rewrite !andb_assoc.
    f_equal. now rewrite andb_comm.
Qed.

Lemma nth_nth_error {A} n l (d : A) :
  nth n l d = match nth_error l n with
              | Some x => x
              | None => d
              end.
Proof.
  symmetry. apply nth_default_eq.
Qed.

Lemma firstn_add {A} x y (args : list A) : firstn (x + y) args = firstn x args ++ firstn y (skipn x args).
Proof.
  induction x in y, args |- *. simpl. reflexivity.
  simpl. destruct args. simpl.
  now rewrite firstn_nil.
  rewrite IHx. now rewrite app_comm_cons.
Qed.

Lemma firstn_app_left (A : Type) (n : nat) (l1 l2 : list A) k :
  k = #|l1| + n ->
  firstn k (l1 ++ l2) = l1 ++ firstn n l2.
Proof. intros ->; apply firstn_app_2. Qed.

Lemma skipn_all_app_eq {A} n (l l' : list A) : n = #|l| -> skipn n (l ++ l') = l'.
Proof.
  move->. apply skipn_all_app.
Qed.

Lemma rev_case {A} (P : list A -> Type) :
  P nil -> (forall l x, P (l ++ [x])) -> forall l, P l.
Proof.
  intros; now apply rev_ind.
Qed.

Lemma firstn_length_le_inv {A} n (l : list A) : #|firstn n l| = n -> n <= #|l|.
Proof.
  induction l in n |- *; simpl; auto with arith;
  destruct n; simpl; auto with arith. discriminate.
Qed.

Lemma mapi_rec_compose {A B C} (g : nat -> B -> C) (f : nat -> A -> B) k l :
  mapi_rec g (mapi_rec f l k) k = mapi_rec (fun k x => g k (f k x)) l k.
Proof.
  induction l in k |- *; simpl; auto. now rewrite IHl.
Qed.

Lemma mapi_compose {A B C} (g : nat -> B -> C) (f : nat -> A -> B) l :
  mapi g (mapi f l) = mapi (fun k x => g k (f k x)) l.
Proof. apply mapi_rec_compose. Qed.
