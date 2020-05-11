From Coq Require Import Bool String Ascii Program List.
From MetaCoq.Template Require Import config monad_utils utils uGraph Pretty All.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping
     TemplateToPCUIC PCUICInversion.
From MetaCoq.SafeChecker Require Import PCUICSafeReduce PCUICSafeChecker
     SafeTemplateChecker.
From MetaCoq.Erasure Require ErasureFunction EAstUtils EPretty.
From MetaCoq.Erasure Require Import SafeErasureFunction SafeTemplateErasure.

Module EF := ErasureFunction.
Module E := EAst.
Module EUtils := EAstUtils.

Import ListNotations.
Import MonadNotation.

Existing Instance envcheck_monad.
Existing Instance extraction_checker_flags.

Local Open Scope string_scope.

(** OCaml-like types with boxes *)
Inductive box_type :=
| TBox (_ : E.erasure_reason)
| TArr (dom : box_type) (codom : box_type)
| TApp (_ : box_type) (_ : box_type)
| TRel (_ : nat)
| TInd (_ : inductive)
| TConst (_ : ident).

Definition is_arr (bt : box_type) : bool :=
  match bt with
  | TArr _ _ => true
  | _ => false
  end.

Fixpoint tokenize_aux (buffer : string) (sep : ascii) (s : string) : list string :=
  match s with
  | EmptyString => if (buffer =? EmptyString)%string then []
                  else [buffer]
  | String c tl =>
    if Ascii.eqb c sep
    then buffer :: tokenize_aux EmptyString sep tl
    else tokenize_aux (buffer ++ String c EmptyString) sep tl
  end.

Definition tokenize := tokenize_aux EmptyString.

Definition split_kername (s : kername) : string * ident :=
  let path_lst := tokenize "." s in
  let (path,name) := chop (#|path_lst| - 1)path_lst in
  (String.concat "." path, hd "" name).

Eval lazy in (split_kername "Coq.ZArith.BinInt.Z.add").


Fixpoint print_box_type (Σ : E.global_context) (bt : box_type) :=
  match bt with
  | TBox x => "□"
  | TArr dom codom => parens (negb (is_arr dom)) (print_box_type Σ dom) ++ " → " ++ print_box_type Σ codom
  | TApp t1 t2 => parens false (print_box_type Σ t1 ++ " " ++ print_box_type Σ t2)
  | TRel i => "'a" ++ string_of_nat i
  | TInd s =>
    match EPretty.lookup_ind_decl Σ s.(inductive_mind) s.(inductive_ind) with
    | Some oib =>
      let (path,_) := split_kername s.(inductive_mind) in
      path ++ "." ++ oib.(E.ind_name)
    | None => "UndeclaredIductive(" ++ s.(inductive_mind)
                                    ++ ","
                                    ++ s.(inductive_mind)
                                    ++ ")"
    end
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

Definition boxed_sort (r : option E.erasure_reason) :=
  match r with
  | Some E.ER_type => true
  | _ => false
  end.

Definition boxed_prop (r : option E.erasure_reason) :=
  match r with
  | Some E.ER_prop => true
  | _ => false
  end.

(** The type erasure procedure. It produces a list of names used to bind type variables and a prenex type with some parts (corresponding to quantification over types and propositions) replaced with boxes. Fails for types that are not prenex or non-extractable dependent types (e.g. containing constructors of inductive types) *)
Program Fixpoint erase_type (Σ : P.global_env_ext)
           (HΣ : ∥ PCUICTyping.wf_ext Σ ∥)
           (Γ : PCUICAst.context)
           (db : list (option nat)) (* for reindexing tRels in types *)
           (names : list name) (* names of the binders in [tProd] for further printing *)
           (j : nat) (* how many binders we are under *)
           (l_arr : bool) (* [true] is we are erasing a domain of the function type*)
           (ty : P.term)
           (* TODO: we need to pass [isType] instead, but this requires to
             implement the function in a different way *)
           (Hty : welltyped Σ Γ ty)
  : typing_result (list name * box_type) :=
  match (flag_of_type Σ HΣ Γ ty Hty) with
  | Checked (Some r) => ret (names, TBox r)
  | TypeError (NotASort _) (* TODO: figure out how to get rid of this case*)
  | Checked None =>
    match ty with
    | P.tRel i =>
      (* we use well-typedness to provide a witness that there is something in the context *)
      let v := safe_nth Γ (exist i _) in
      match (nth_error db i) with
      | Some (Some n) => ret (names, TRel n)
      | Some None => TypeError (Msg ("Variable " ++ string_of_name v.(decl_name) ++ " is not translated. Probably not a prenex type"))
      | _ => TypeError (Msg ("Variable " ++ string_of_name v.(decl_name) ++ " is not found in the translation context"))
      end
    | P.tSort _ => ret (names,TBox E.ER_type)
    | P.tProd na t b =>
      let wt_t := _ in
      let wt_b := _ in
      ft <- flag_of_type Σ HΣ Γ t wt_t ;;
      match flag_of_type Σ HΣ (P.vass na t :: Γ) b wt_b  with
          | Checked (Some _) => ret (names, TBox E.ER_type)
          | Checked None =>
            (* we pass [true] flag to indicate that we translate the domain *)
            '(nms1, t1) <- erase_type Σ HΣ Γ db names j true t wt_t ;;
            (* if it is a binder for a type variable, e.g [forall A, ...] and we are in the codomain, we add current variable to the translation context [db], otherwise, we add [None], because it's either not a binder for a type variable or the type is not prenex. This guarantees that non-prenex types will fail *)
            let db' := if boxed_sort ft && (negb l_arr) then Some j :: db
                       else None :: db in
            (* we only count binders for type variables *)
            let j' := if boxed_sort ft then (1+j)%nat else j in
            '(nms2, t2) <- erase_type Σ HΣ (P.vass na t :: Γ) db' names j' l_arr b wt_b ;;
            (* we keep track of the binders for types *)
            let names' := if boxed_sort ft then (nms1++ [na] ++ nms2)%list
                          else (nms1 ++ nms2)%list in
            ret (names', TArr t1 t2)
          | TypeError te => TypeError te
      end
    | P.tApp t1 t2 =>
      '(nms1, t1') <- erase_type Σ HΣ Γ db names j l_arr t1 _ ;;
      '(nms2,t2') <- erase_type Σ HΣ Γ db names j l_arr t2 _ ;;
      ret (nms1 ++ nms2, TApp t1' t2')%list
    | P.tInd ind _ =>
      decl <- lookup_ind_decl ind ;;
      let oib := projT1 (projT2 decl) in
      ret (names,TInd ind)
    | P.tLambda na t b => (* NOTE: assume that this is a type scheme, meaning that applied to enough args it ends up a type *)
      erase_type Σ HΣ (P.vass na t :: Γ) db names j l_arr b _
    | P.tConst nm _ =>
      (* NOTE: since the original term is well-typed (need also to be a type!), we know that the constant, applied to enough arguments is a valid type (meaning that the constant is a type scheme), so, we just leave the constant name in the erased version *)
      ret (names, TConst nm)
    | P.tEvar _ _  | P.tCase _ _ _ _ | P.tProj _ _
    | P.tFix _ _ | P.tCoFix _ _ | P.tVar _ | P.tLetIn _ _ _ _
    | P.tConstruct _ _ _ => TypeError (Msg ("Not supported type: " ++ string_of_term ty))
    end
  | TypeError te => TypeError te
  end.
Solve Obligations with
    ((intros;subst;
    try clear dependent filtered_var;
    try clear dependent filtered_var0;
    try clear dependent Heq_anonymous;
     try clear dependent Heq_anonymous0);try solve_erase;try easy).
Next Obligation.
  sq'. inversion Hty as [? X]. eapply inversion_Rel in X as (? & ? & ? & ?);eauto.
  apply nth_error_Some;easy.
Qed.
Next Obligation. easy. Qed.
Next Obligation.
  clear dependent Heq_anonymous;solve_erase.
Qed.
Next Obligation.
  sq'. inversion Hty as [? X]. eapply inversion_Rel in X as (? & ? & ? & ?);eauto.
  apply nth_error_Some;easy.
Qed.
Next Obligation. easy. Qed.
Next Obligation.
  clear dependent Heq_anonymous;solve_erase.
Qed.


Fixpoint debox_box_type (bt : box_type) : box_type :=
  match bt with
  | TBox _ => bt
  | TArr dom codom =>
    match dom with
    | TBox _ => debox_box_type codom (* we turn [box -> ty] into [ty] *)
    | _ => TArr (debox_box_type dom) (debox_box_type codom)
    end
  | TApp ty1 ty2 =>
    match ty2 with
    | TBox _ => debox_box_type ty1 (* we turn [(ty1 box)] into [ty1] *)
    | _ => TApp (debox_box_type ty1) (debox_box_type ty2)
    end
  | TRel _ => bt
  | TInd _ => bt
  | TConst _ => bt
  end.

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
  : EnvCheck (EAst.global_context * (list name * box_type)) :=
  let Σ := List.rev (trans_global (Ast.empty_ext p.1)).1 in
  G <- check_wf_env_only_univs Σ ;;
  Σ' <- wrap_error (empty_ext Σ) "erasure of the global context" (SafeErasureFunction.erase_global Σ _) ;;
  t <- wrap_error (empty_ext Σ) ("During erasure of " ++ string_of_term (trans p.2)) (erase_type (empty_ext Σ) _ nil [] [] 0 false (trans p.2) _);;
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

Definition erase_and_print_type {cf : checker_flags} (after_erasure : box_type -> box_type) (p : Ast.program)
  : string + string :=
  let p := fix_program_universes p in
  match erase_type_program p return string + string with
  | CorrectDecl (Σ', t) =>
    let t' := after_erasure t.2 in
    inl ("Environment is well-formed and " ++ Pretty.print_term (Ast.empty_ext p.1) [] true p.2 ++
         " erases to: " ++ nl ++ print_box_type  Σ' t')
  | EnvError Σ' (AlreadyDeclared id) =>
    inr ("Already declared: " ++ id)
  | EnvError Σ' (IllFormedDecl id e) =>
    inr ("Type error: " ++ PCUICSafeChecker.string_of_type_error Σ' e ++ ", while checking " ++ id)
  end.


Quote Recursively Definition ex1 :=
  (forall (A : Type),  list A -> list A -> 0 = 0 -> forall (B : Type), B -> A -> A).
Compute erase_and_print_type id ex1.

(** The standard extraction can extract non-prenex types  *)
Definition ex2 : forall (A : Type), (forall A : Type, A -> A) -> A -> forall B : Type, B -> nat := fun A f _ _ _  => 0.
Recursive Extraction ex2.

(** But non-prenex types might require [Obj.magic] *)
Definition ex3 : forall (A : Type),  A -> (forall A : Type, A -> A) -> A :=
  fun A a f => f _ a.
Recursive Extraction ex3.

(** Erasing and deboxing *)
Quote Recursively Definition ex4 :=
  (forall (A : Type), A ->forall (B : Type) (C : Type), B -> C).
Compute erase_type_program ex4.
Compute erase_and_print_type id ex4.
Compute erase_and_print_type debox_box_type ex4.

(** Tesing mutual iductives *)
Inductive tree (A : Set) : Set :=
  node : A -> forest A -> tree A
with forest (A : Set) : Set :=
    leaf : A -> forest A
  | cons : tree A -> forest A -> forest A.

Quote Recursively Definition ex_mutual := (forall (A: Set), forest A -> tree A -> A).
Compute erase_and_print_type debox_box_type ex_mutual.

(* TODO : check why [eq_refl] is not erased *)
Quote Recursively Definition ex4' := (forall (A : 0 = 0 -> Type) (B : Type), option (A eq_refl) -> B).
Compute erase_and_print_type debox_box_type ex4'.

Quote Recursively Definition ex5_fail :=
  (forall (A : Type), (forall (B : Type), B -> B) -> A).
Compute erase_and_print_type id ex5_fail.
(* Type error: Msg: Variable B is not translated. Probably not a prenex type *)

Definition non_neg := {n : nat | 0 < n}.

Quote Recursively Definition ex6 := (forall (A : Type), {n : nat | 0 < n} -> A).
Compute erase_type_program ex6.
Compute erase_and_print_type debox_box_type ex6.

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
    (* we always push [false], because we only adjust for top-level lambdas *)
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
    ety <- erase_type Σ HΣ Γ [] [] 0 false b.(P.cst_type) _ ;;
    let (dom, _) := decompose_arr ety.2 in
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

Quote Recursively Definition ex_combine := combine.

Compute (test_applied_to_logargs ex_combine "Coq.Lists.List.combine" 2).

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
