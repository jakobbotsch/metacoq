From Coq Require Import Bool String Program List.
From MetaCoq.Template Require Import config monad_utils utils uGraph Pretty All.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping
     TemplateToPCUIC PCUICInversion.
From MetaCoq.SafeChecker Require Import PCUICSafeReduce PCUICSafeChecker
     SafeTemplateChecker.
From MetaCoq.Erasure Require ErasureFunction EAstUtils.
From MetaCoq.Erasure Require Import SafeErasureFunction SafeTemplateErasure.

Module EF := ErasureFunction.
Module E := EAst.
Module EUtils := EAstUtils.

Import ListNotations.
Import MonadNotation.

Existing Instance envcheck_monad.
Existing Instance extraction_checker_flags.

Local Open Scope string_scope.

Inductive box_type :=
| TBox (_ : E.erasure_reason)
| TArr (dom : box_type) (codom : box_type)
| TApp (_ : box_type) (_ : box_type)
| TRel (_ : nat)
| TInd (_ : ident)
| TConst (_ : ident).

Fixpoint print_box_type  (bt : box_type) :=
  match bt with
  | TBox x => "⧈"
  | TArr dom codom => print_box_type dom ++ " → " ++ print_box_type codom
  | TApp t1 t2 => parens false (print_box_type t1 ++ " " ++ print_box_type t2)
  | TRel i => "'a" ++ string_of_nat i
  | TInd s => s
  | TConst s => s
  end.

Ltac sq' := repeat match goal with
         | H : ∥ _ ∥ |- _ => destruct H; try clear H
         end; try eapply sq.

Import PCUICSafeLemmata.


Module P := PCUICAst.
Module PInv := MetaCoq.PCUIC.PCUICInversion.

Import PInv.

Ltac solve_erase :=
    sq;
    let X := fresh "X" in
    match goal with
    | [H : welltyped _ _ (P.tEvar _ _) |- _ ] =>
      destruct H as [? X];
      (* inversion on evar gives [False] *)
      now eapply inversion_Evar in X
    | [H : welltyped _ _ (P.tLambda _ _ _) |- _  ] =>
      destruct H as [? X];
      eapply inversion_Lambda in X as (? & ? & ? & ? & ?);auto;eexists;eauto
    | [H : welltyped _ _ (P.tLetIn _ _ _ _) |- _ ] =>
      destruct H as [? X];
      eapply inversion_LetIn in X as (? & ? & ? & ? & ? & ?);auto;eexists;eauto
    | [H : welltyped _ _ (P.tApp _ _) |- _ ] =>
      destruct H as [? X];
      eapply inversion_App in X as (? & ? & ? & ? & ? & ?);auto;eexists;eauto
    | [H : welltyped _ _ (P.tCase _ _ _ _) |- _] =>
      destruct H as [? X];
      eapply inversion_Case in X as
          (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?);auto;eexists;eauto
    | [H : welltyped _ _ (P.tProj _ _)  |- _] =>
      destruct H as [? X];
      eapply inversion_Proj in X as
          (? & ? & ? & ? & ? & ? & ? & ? & ?);auto;eexists;eauto
    |  [H : welltyped _ _ (P.tProd _ _ _)  |- _] =>
       destruct H as [? X];
       eapply PInv.inversion_Prod in X as (? & ? & ? & ? & ?);auto;eexists;eauto
    | [H : welltyped _ _ _  |- _] => destruct H as [? X];eexists;eauto
    end.

Program Fixpoint erase_type (Σ : P.global_env_ext)
           (HΣ : ∥ PCUICTyping.wf_ext Σ ∥)
           (Γ : PCUICAst.context)
           (ty : P.term)
           (* TODO: we need to pass [isType] instead, but this require to
             implement the function in a different way *)
           (Hty : welltyped Σ Γ ty)
  : typing_result box_type :=
  match (flag_of_type Σ HΣ Γ ty Hty) with
  | Checked (Some r) => ret (TBox r)
  | TypeError (NotASort _) (* TODO: figure out how to get rid of this case*)
  | Checked None =>
    match ty with
    | P.tRel i => ret (TRel i)
    | P.tSort _ => ret (TBox E.ER_type)
    | P.tProd na b t =>
      match flag_of_type Σ HΣ (P.vass na b :: Γ) t _  with
          | Checked (Some _) => ret (TBox E.ER_type)
          | Checked None =>
            t1 <- erase_type Σ HΣ Γ b _ ;;
            t2 <- erase_type Σ HΣ (P.vass na b :: Γ) t _ ;;
            ret (TArr t1 t2)
          | TypeError te => TypeError te
      end
    | P.tApp t1 t2 =>
      t1' <- erase_type Σ HΣ Γ t1 _ ;;
      t2' <- erase_type Σ HΣ Γ t2 _ ;;
      ret (TApp t1' t2')
    | P.tInd ind _ => ret (TInd ind.(inductive_mind))
    | P.tLambda na t b => (* NOTE: assume that this is a type scheme, meaning that applied to enough args it ends up a type *)
      erase_type Σ HΣ (P.vass na t :: Γ) b _
    | P.tConst nm _ =>
      (* NOTE: since the original term is well-typed, we know that the constant, applied to enough argument is a valid type (meaning that the constant is a type scheme), so, we just leave the constant name in the erased version *)
      ret (TConst nm)
    | P.tEvar _ _  | P.tCase _ _ _ _ | P.tProj _ _
    | P.tFix _ _ | P.tCoFix _ _ | P.tVar _ | P.tLetIn _ _ _ _
    | P.tConstruct _ _ _ => TypeError (Msg ("Not supported type: " ++ string_of_term ty))
    end
  | TypeError te => TypeError te
  end.
Solve Obligations with
    (intros;
    try (subst;
        try clear dependent filtered_var;
        try clear dependent filtered_var0;
        try clear dependent Heq_anonymous;
        try clear dependent Heq_anonymous0;solve_erase);try easy).


Fixpoint mk_arrs (l : list box_type) (codom : box_type) :=
  match l with
  | [] => codom
  | x :: l' => TArr x (mk_arrs l' codom)
  end.

Fixpoint mk_arrsM (l : (list (typing_result box_type))) (codom : box_type) :=
  match l with
  | [] => ret codom
  | x :: l' =>
    x' <- x ;;
    res <- mk_arrsM l' codom ;;
    ret (TArr x' res)
  end.

(* An attempt to reimplement erasure for types that always applied to a well-formed types. This breaks when we do a recurison in the application case.
  Using decompose_app requires some well-foundness argument for fix *)

(* Program Fixpoint erase_type (Σ : P.global_env_ext) *)
(*            (HΣ : ∥ PCUICTyping.wf_ext Σ ∥) *)
(*            (Γ : PCUICAst.context) *)
(*            (ty : P.term) *)
(*            (Hty :  ∥ isType Σ Γ ty ∥) *)
(*   : typing_result box_type := *)
(*   match (flag_of_type Σ HΣ Γ ty _) with *)
(*   | Checked (Some r) => ret (TBox r) *)
(*   | TypeError (NotASort _) | Checked None => *)
(*     match ty with *)
(*     | P.tRel i => ret (TRel i) *)
(*     | P.tSort _ => ret (TBox E.ER_type) *)
(*     | P.tProd na b t => *)
(*       match flag_of_type Σ HΣ (P.vass na b :: Γ) t _  with *)
(*           | Checked (Some _) => ret (TBox E.ER_type) *)
(*           | Checked None => *)
(*             t1 <- erase_type Σ HΣ Γ b _ ;; *)
(*             t2 <- erase_type Σ HΣ (P.vass na b :: Γ) t _ ;; *)
(*             ret (TArr t1 t2) *)
(*           | TypeError te => TypeError te *)
(*       end *)
(*     | P.tApp t1 t2 => *)
(*       let '(t, args) := decompose_app t1 in *)
(*       let eargs := map (fun x => erase_type Σ HΣ Γ x _) args in *)
(*       t2' <- erase_type Σ HΣ Γ t2 _ ;; *)
(*       (* t2' <- erase_type Σ HΣ Γ t2 _ ;; *) *)
(*       res <- mk_arrsM eargs t2' ;; *)
(*       (* ret (TApp (TInd "") t2') *) *)
(*       ret (TApp (TInd "") t2') *)
(*     | P.tInd ind _ => ret (TInd ind.(inductive_mind)) *)
(*     | P.tLambda na t b => (* NOTE: assume that this is a type scheme, meaning that applied to enough args it ends up a type *) *)
(*       erase_type Σ HΣ (P.vass na t :: Γ) b _ *)
(*     | P.tConst nm _ => *)
(*       (* NOTE: since the original term is well-typed, we know that the constant, applied to enough argument is a valid type (meaning that the constant is a type scheme), so, we just leave the constant name in the erased version *) *)
(*       ret (TConst nm) *)
(*     | P.tEvar _ _  | P.tCase _ _ _ _ | P.tProj _ _ *)
(*     | P.tFix _ _ | P.tCoFix _ _ | P.tVar _ | P.tLetIn _ _ _ _ *)
(*     | P.tConstruct _ _ _ => TypeError (Msg ("Not supported type: " ++ string_of_term ty)) *)
(*     end *)
(*   | TypeError te => TypeError te *)
(*   end. *)
(* Solve Obligations with *)
(*     (intros; *)
(*     try (subst; *)
(*         try clear dependent filtered_var; *)
(*         try clear dependent filtered_var0; *)
(*         try clear dependent Heq_anonymous; *)
(*         try clear dependent Heq_anonymous0;solve_erase);try easy). *)
(* Next Obligation. *)
(*   try clear dependent Heq_anonymous0. *)
(*   sq. destruct Hty as [? X]. *)
(*   eapply inversion_App in X as (? & ? & ? & ? & ? & ?);auto. *)
(*   ;eexists;eauto. *)
(*   eexists;eauto. *)
(* Qed. *)
(* Next Obligation. *)
(*   try clear dependent Heq_anonymous; *)
(*     try clear dependent Heq_anonymous0. *)
(*   (* destruct Hty as [? X]. *) *)
(*   solve_erase. *)
(*   sq;match goal with *)
(*     |  [H : isType _ _ (P.tProd _ _ _)  |- _] => *)
(*        destruct H as [? X]; *)
(*          eapply PInv.inversion_Prod in X as (? & ? & ? & ? & ?);auto;eexists;eauto *)
(*   end. *)
(*   solve_erase. *)
(*   eapply PInv.inversion_Prod in X as (? & ? & ? & ? & ?);auto;eexists;eauto. *)
(* Qed. *)

Program Definition erase_type_program (p : Ast.program)
  : EnvCheck (EAst.global_context * box_type) :=
  let Σ := List.rev (trans_global (Ast.empty_ext p.1)).1 in
  G <- check_wf_env_only_univs Σ ;;
  Σ' <- wrap_error (empty_ext Σ) "erasure of the global context" (SafeErasureFunction.erase_global Σ _) ;;
  t <- wrap_error (empty_ext Σ) ("During erasure of " ++ string_of_term (trans p.2)) (erase_type (empty_ext Σ) _ nil (trans p.2) _);;
  ret (Monad:=envcheck_monad) (Σ', t).
Next Obligation.
  unfold trans_global.
  simpl. unfold wf_ext, empty_ext. simpl.
  unfold on_global_env_ext. destruct H0. constructor.
  split; auto. simpl. todo "on_udecl on empty universe context".
Qed.

Next Obligation.
  unfold trans_global.
  simpl. unfold wf_ext, empty_ext. simpl.
  unfold on_global_env_ext. destruct H0. todo "assuming well-typedness".
Qed.

Definition erase_and_print_type {cf : checker_flags} (p : Ast.program)
  : string + string :=
  let p := fix_program_universes p in
  match erase_type_program p return string + string with
  | CorrectDecl (Σ', t) =>
    inl ("Environment is well-formed and " ++ Pretty.print_term (Ast.empty_ext p.1) [] true p.2 ++
         " erases to: " ++ nl ++ print_box_type t)
  | EnvError Σ' (AlreadyDeclared id) =>
    inr ("Already declared: " ++ id)
  | EnvError Σ' (IllFormedDecl id e) =>
    inr ("Type error: " ++ PCUICSafeChecker.string_of_type_error Σ' e ++ ", while checking " ++ id)
  end.


Quote Recursively Definition ex1 := (forall (A : Type),  list A -> 0 = 0 -> A).
Compute erase_and_print_type ex1.

Definition non_neg := {n : nat | 0 < n}.

Quote Recursively Definition ex2 := (forall (A : Type), {n : nat | 0 < n} -> A).
Compute erase_and_print_type ex2.

Fixpoint lookup_env (Σ : P.global_env) (id : ident) : option P.global_decl :=
  match Σ with
  | nil => None
  | hd :: tl =>
    if ident_eq id hd.1 then Some hd.2
    else lookup_env tl id
  end.

Definition lookup_ind_decl (Σ : P.global_env) ind i :=
  match lookup_env Σ ind with
  | Some (P.InductiveDecl {| P.ind_bodies := l; P.ind_universes := uctx |}) =>
    match nth_error l i with
    | Some body => Some body
    | None => None
    end
  | _ => None
  end.

Definition lookup_const (Σ : P.global_env) const :=
  match lookup_env Σ const with
  | Some (P.ConstantDecl b) => Some b
  | _ => None
  end.

Definition get_shift (n : nat) (g : list bool) :=
  List.count_occ Bool.bool_dec (List.firstn (1+n) g) true.

Fixpoint debox_types (g : list bool) (t : E.term) :=
  match t with
  | E.tRel i => E.tRel (i - get_shift i g)
  | E.tEvar ev args => E.tEvar ev (List.map (debox_types g) args)
  | E.tLambda na M => match na.(E.binder_erasure_reason) with
                   | Some ER_type => debox_types (true :: g) M
                   | _ => E.tLambda na (debox_types (false :: g) M)
                   end
  | E.tApp u v => match v with
               | E.tBox ER_type => debox_types g u
               | _ => E.tApp (debox_types g u) (debox_types g v)
               end
  | E.tLetIn na b b' => E.tLetIn na (debox_types g b) (debox_types (false :: g) b')
  | E.tCase ind c brs =>
    let brs' := List.map (on_snd (debox_types g)) brs in
    E.tCase ind (debox_types g c) brs'
  | E.tProj p c => E.tProj p (debox_types g c)
  | E.tFix mfix idx =>
    let mfix' := List.map (E.map_def (debox_types g)) mfix in
    E.tFix mfix' idx
  | E.tCoFix mfix idx =>
    let comfix' := List.map (E.map_def (debox_types g)) mfix in
    E.tCoFix comfix' idx
  | E.tBox r => t
  | E.tVar _ => t
  | E.tConst _ => t
  | E.tConstruct _ _ => t
  end.

(* TODO : should go to the EAstUtils module *)
Fixpoint isConstruct_app (t : E.term) : bool :=
  match (EUtils.decompose_app t).1 with
  | E.tConstruct _ _  => true
  | _ => false
  end.

(* TODO : should go to the EAstUtils module *)
Fixpoint isConst_app (t : E.term) : bool :=
  match (EUtils.decompose_app t).1 with
  | E.tConst _ => true
  | _ => false
  end.


SearchPattern (term -> bool).
About isConst_app.

(** Remove all boxes applied to global constants and contructors.
    Assumes that constants applied to all logical arguments and constructors are fylly applied. *)
Fixpoint debox_all (t : E.term) :=
  match t with
  | E.tRel i => E.tRel i
  | E.tEvar ev args => E.tEvar ev (List.map debox_all args)
  | E.tLambda na M => E.tLambda na (debox_all M)
  | E.tApp u v =>
    match v with
    | E.tBox _ =>
      if (isConstruct_app u || isConst_app u)
      then debox_all u (* ignore the box if it's applied to a constructor or a global constant*)
      else E.tApp (debox_all u) (debox_all v)
    | _ => E.tApp (debox_all u) (debox_all v)
    end
  | E.tLetIn na b b' => E.tLetIn na (debox_all b) (debox_all b')
  | E.tCase ind c brs =>
    let brs' := List.map (on_snd debox_all) brs in
    E.tCase ind (debox_all c) brs'
  | E.tProj p c => E.tProj p (debox_all c)
  | E.tFix mfix idx =>
    let mfix' := List.map (E.map_def debox_all) mfix in
    E.tFix mfix' idx
  | E.tCoFix mfix idx =>
    let comfix' := List.map (E.map_def debox_all) mfix in
    E.tCoFix comfix' idx
  | E.tBox r => t
  | E.tVar _ => t
  | E.tConst _ => t
  | E.tConstruct _ _ => t
  end.


Fixpoint adjust_indices (g : list bool) (t : E.term) :=
  match t with
  | E.tRel i => E.tRel (i - get_shift i g)
  | E.tEvar ev args => E.tEvar ev (List.map (adjust_indices g) args)
  | E.tLambda na M =>
    (* we always push [false], bacuse we only adjust for top-level lambdas *)
    E.tLambda na (adjust_indices (false :: g) M)
  | E.tApp u v => E.tApp (adjust_indices g u) (adjust_indices g v)
  | E.tLetIn na b b' =>
    (* we always push [false], bacuse we only adjust for top-level lambdas *)
    E.tLetIn na (adjust_indices g b) (adjust_indices (false :: g) b')
  | E.tCase ind c brs =>
    let brs' := List.map (on_snd (adjust_indices g)) brs in
    E.tCase ind (adjust_indices g c) brs'
  | E.tProj p c => E.tProj p (adjust_indices g c)
  | E.tFix mfix idx =>
    let g := (repeat false (length mfix) ++ g)%list in
    let mfix' := List.map (E.map_def (adjust_indices g)) mfix in
    E.tFix mfix' idx
  | E.tCoFix mfix idx =>
    let g := (repeat false (length mfix) ++ g)%list in
    let comfix' := List.map (E.map_def (adjust_indices g)) mfix in
    E.tCoFix comfix' idx
  | E.tBox r => t
  | E.tVar _ => t
  | E.tConst _ => t
  | E.tConstruct _ _ => t
  end.

Fixpoint decompose_arr (t : box_type) : list box_type × box_type :=
  match t with
  | TArr A B =>
      let (dom, codom) := decompose_arr B in
      (A :: dom, codom)
  | _ => ([], t)
  end.


Definition keep (o : option E.erasure_reason) : bool :=
  match o with
  | Some _ => false
  | None   => true
  end.

Definition is_TBox (ty : box_type) :=
  match ty with
  | TBox x => true
  | _ => false
  end.

Fixpoint Edecompose_lam (t : E.term) : (list E.aname) × E.term :=
  match t with
  | E.tLambda n b =>
      let (ns, b) := Edecompose_lam b in
      (n :: ns, b)
  | _ => ([], t)
  end.

Definition Eit_mkLambda (l : list E.aname) (t : E.term) :=
fold_left (fun acc nm => E.tLambda nm acc) l t.

Definition debox_top_level (t : E.term) :=
  let (params, body) := Edecompose_lam t in
  let bitmask := rev (map (negb ∘ keep ∘ E.binder_erasure_reason) params) in
  let filtered_params := rev (filter (keep ∘ E.binder_erasure_reason) params) in
  Eit_mkLambda filtered_params (adjust_indices bitmask body).

Section DeboxTopLevelExamples.
  Definition x := E.mkBindAnn (nNamed "x") None.
  Definition y := E.mkBindAnn (nNamed "y") None.
  Definition p := E.mkBindAnn (nNamed "x") (Some E.ER_prop).
  Example debox_top_level_1 :
    debox_top_level
      (E.tLambda x (E.tLambda p (E.tLambda y (E.tApp (E.tRel 2) (E.tRel 0))))) =
    (E.tLambda x (E.tLambda y (E.tApp (E.tRel 1) (E.tRel 0)))).
  Proof. reflexivity. Qed.

  Example debox_top_level_2 :
    debox_top_level
      (E.tLambda x (E.tLambda y (E.tLambda p (E.tApp (E.tRel 2) (E.tRel 1))))) =
    (E.tLambda x (E.tLambda y (E.tApp (E.tRel 1) (E.tRel 0)))).
  Proof. reflexivity. Qed.
End DeboxTopLevelExamples.

Definition is_fully_applied_ctor (Σ : P.global_env)
           (ind : inductive)
           (ctor : nat) (n_app : nat) :=
  match PCUICChecker.lookup_constructor_decl Σ ind.(inductive_mind) ind.(inductive_ind) ctor with
  | PCUICChecker.Checked (_,_,ty) =>
    let (dom, _) :=
        PCUICAstUtils.decompose_prod ty in
    Nat.eqb n_app (length dom.2)
  | _ => false
  end.

Definition find_indices {A : Type}
           (f : A -> bool) : list A -> list nat :=
  let worker := fix go (i : nat) l :=
              match l with
              | [] => []
              | x :: tl =>
                if f x then i :: go (1+i)%nat tl
                else go (1+i)%nat tl
              end in
  worker 0.

Fixpoint last_option {A} (l : list A) : option A :=
  match l with
  | [] => None
  | [a] => Some a
  | a :: (_ :: _) as l0 => last_option l0
  end.

Definition last_box_index l := last_option (find_indices is_TBox l).

Compute last_box_index
        (decompose_arr (TArr (TBox (E.ER_type))
                       ((TArr (TRel 0) (TArr (TBox (E.ER_type)) (TRel 1)))))).1.

Program Definition is_logargs_applied_const (Σ : P.global_env_ext)
           (HΣ : ∥ PCUICTyping.wf_ext Σ ∥)
           (Γ : PCUICAst.context)
           (const : ident) (n_app : nat) : typing_result bool :=
  match lookup_const Σ const with
  | Some b =>
    ety <- erase_type Σ HΣ Γ b.(P.cst_type) _ ;;
    let (dom, _) := decompose_arr ety in
    match last_box_index dom with
    | Some i => ret (Nat.leb (i+1) n_app)
    | None => ret true
    end
  | _ => TypeError (Msg ("Constant not found: " ++ const))
  end.
Next Obligation.
  sq. destruct Σ; destruct HΣ as [p1 p2];simpl in *.
  todo "everything coming from well-formed environment is well typed".
Qed.

Program Definition test_applied_to_logargs  (p : Ast.program) (const : ident) (n_app : nat)
  : EnvCheck bool :=
  let p := fix_program_universes p in
  let Σ := List.rev (trans_global (Ast.empty_ext p.1)).1 in
  G <- check_wf_env_only_univs Σ ;;
  t <- wrap_error (empty_ext Σ) "during cheking applied constant" (is_logargs_applied_const (empty_ext Σ) _ [] const n_app) ;;
  ret (Monad:=envcheck_monad) t.
Next Obligation.
  unfold trans_global.
  simpl. unfold wf_ext, empty_ext. simpl.
  unfold on_global_env_ext. destruct H0. constructor.
  split; auto. simpl. todo "on_udecl on empty universe context".
Qed.

Quote Recursively Definition ex3 := combine.

Compute (test_applied_to_logargs ex3 "Coq.Lists.List.combine" 2).

Definition test_fully_applied_constructor (p : Ast.program) (ind_nm : ident) (ind_i : nat) (ctor : nat) (n_app : nat) :=
  let p := fix_program_universes p in
  let Σ := List.rev (trans_global (Ast.empty_ext p.1)).1 in
  (is_fully_applied_ctor Σ (mkInd ind_nm ind_i) ctor n_app).

Quote Recursively Definition q_prod
  := (fun (x y : nat) => (x,y)).

Compute ((test_fully_applied_constructor q_prod "Coq.Init.Datatypes.prod" 0 0 4)).


Definition forallb_defs {A : Set} (f : A -> bool) (ds : list (E.def A)) :=
  (* this way of defining is fixpoint-firendly, i.e. is we [map] first and then apply [forallb] it fails to work with the definition below *)
  forallb (fun x => f x.(E.dbody)) ds.

Definition check_ctors_applied (Σ : P.global_env) :=
  fix go (apps : list E.term) (t : E.term) :=
    match t with
    | E.tRel i => true
    | E.tEvar ev args => forallb (go []) args
    | E.tLambda na M => go [] M
    | E.tApp u v => (go (v :: apps) u) && (go [] v)
    | E.tLetIn na b b' => (go [] b) && (go [] b')
    | E.tCase ind c brs =>
      let brs' := forallb (fun x => go [] (snd x)) brs in
      (go [] c) && brs'
    | E.tProj p c => go [] c
    | E.tFix mfix idx =>
      forallb_defs (go []) mfix
    | E.tCoFix mfix idx =>
      forallb_defs (go []) mfix
    | E.tBox r => true
    | E.tVar _ => true
    | E.tConst _ => true
    | E.tConstruct ind i =>
      is_fully_applied_ctor Σ ind i (length apps)
    end.

Definition check_consts_applied
  (Σ : P.global_env_ext) (HΣ : ∥ PCUICTyping.wf_ext Σ ∥) :=
  fix go (apps : list E.term) (t : E.term) : typing_result bool:=
    match t with
    | E.tRel i => ret true
    | E.tEvar ev args =>
      res <- monad_map (go []) args ;;
      ret (forallb id res)
    | E.tLambda na M => go [] M
    | E.tApp u v =>
      b1 <- go (v :: apps) u ;;
      b2 <- go [] v ;;
      ret (b1 && b2)
    | E.tLetIn na b b' =>
      b1 <- go [] b;;
      b2 <- go [] b';;
      ret (b1 && b2)
    | E.tCase ind c brs =>
      b1 <- go [] c ;;
      res <- monad_map (fun x => go [] (snd x)) brs ;;
      ret (b1 && forallb id res)
    | E.tProj p c => go [] c
    | E.tFix mfix idx =>
      res <- monad_map (fun x => go [] (E.dbody x)) mfix ;;
      ret (forallb id res)
    | E.tCoFix mfix idx =>
      res <- monad_map (fun x => go [] (E.dbody x)) mfix ;;
      ret (forallb id res)
    | E.tBox r => ret true
    | E.tVar _ => ret true
    | E.tConst nm => is_logargs_applied_const Σ HΣ [] nm (length apps)
    | E.tConstruct ind i => ret true
    end.
