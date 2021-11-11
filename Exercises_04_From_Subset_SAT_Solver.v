Set Implicit Arguments.
Require Import Cpdt.CpdtTactics.
Require Import Classical_Prop.
Require Import List.

Definition var := nat % type. 
Definition total_map (A : Type) := var -> A.
Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).
Definition t_update {A : Type} (m : total_map A)
                    (x : var) (v : A) :=
  fun x' => if PeanoNat.Nat.eqb x x' then v else m x'.
(* to create an empty total map with default value *)
Notation "'_' '!->' v" := (t_empty v)
                            (at level 100, right associativity).
(* extending existing map with some bindings *)
Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).

Definition tvals := total_map bool.

Inductive literal : Set :=
| Var : var -> literal
| Not : var -> literal                 
| Disj : literal -> literal -> literal.

Inductive formula : Set :=
| Lit : literal -> formula
| Conj : formula -> formula -> formula.    

(*             (x \/ y \/ ~z) : Lit (Disj (Var x) (Disj (Var y) (Not z)))       *)

Inductive formulaTrue : tvals -> formula -> Prop :=
| TVar : forall tv var, tv var = true -> formulaTrue tv (Lit (Var var))
| TNot : forall tv var, tv var = false -> formulaTrue tv (Lit (Not var))
| TDisj : forall l1 l2 tv, formulaTrue tv (Lit l1) \/ formulaTrue tv (Lit l2) ->
                           formulaTrue tv (Lit (Disj l1 l2))
| TConj : forall f1 f2 tv, formulaTrue tv f1 -> formulaTrue tv f2 -> formulaTrue tv (Conj f1 f2). 

Definition backtracking : forall f : formula, {truth : tvals | formulaTrue truth f } + {forall truth, ~ formulaTrue truth f }.
