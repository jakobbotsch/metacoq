(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import utils Ast.
Require Import FSets ExtrOcamlBasic ExtrOcamlString ExtrOcamlZInt.

(** * Extraction setup for template-coq.

    Any extracted code planning to link with the plugin's OCaml reifier
    should use these same directives for consistency.
*)


(* Ignore [Decimal.int] before the extraction issue is solved:
   https://github.com/coq/coq/issues/7017. *)
Extract Inductive Decimal.int => unit [ "(fun _ -> ())" "(fun _ -> ())" ] "(fun _ _ _ -> assert false)".

Extract Constant ascii_compare =>
 "fun x y -> match Char.compare x y with 0 -> Eq | x when x < 0 -> Lt | _ -> Gt".

Extraction Blacklist config uGraph Universes Ast String List Nat Int
           UnivSubst Typing Checker Retyping OrderedType Logic Common Equality UnivSubst.
Set Warnings "-extraction-opaque-accessed".
Set Warnings "-extraction-reserved-identifier".

Cd "gen-src".

From MetaCoq.Template Require Import TemplateMonad.Extractable config Induction
     LiftSubst UnivSubst Pretty.

Recursive Extraction Library Extractable.
Extraction Library MCOption.
Extraction Library Induction.
Extraction Library LiftSubst.
Extraction Library UnivSubst.
Extraction Library Pretty.
Extraction Library config.

Cd "..".
