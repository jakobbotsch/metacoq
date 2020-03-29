From MetaCoq Require Import utils.
From MetaCoq.Erasure Require Import EAst.

Definition get_shift (n : nat) (g : list bool) :=
  List.count_occ Bool.bool_dec (List.firstn (1+n) g) true.

Fixpoint debox (g : list bool) (t : term) :=
  match t with
  | tRel i => tRel (i - get_shift i g)
  | tEvar ev args => tEvar ev (List.map (debox g) args)
  | tLambda na M => match na.(binder_erasure_reason) with
                   | Some ER_type => debox (true :: g) M
                   | _ => tLambda na (debox (false :: g) M)
                   end
  | tApp u v => match v with
               | tBox ER_type => debox g u
               | _ => tApp (debox g u) (debox g v)
               end
  | tLetIn na b b' => tLetIn na (debox g b) (debox (false :: g) b')
  | tCase ind c brs =>
    let brs' := List.map (on_snd (debox g)) brs in
    tCase ind (debox g c) brs'
  | tProj p c => tProj p (debox g c)
  | tFix mfix idx =>
    let mfix' := List.map (map_def (debox g)) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let comfix' := List.map (map_def (debox g)) mfix in
    tCoFix comfix' idx
  | tBox r => t
  | tVar _ => t
  | tConst _ => t
  | tConstruct _ _ => t
  end.
