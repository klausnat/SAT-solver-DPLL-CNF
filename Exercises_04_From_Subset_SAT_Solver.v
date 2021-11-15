Set Implicit Arguments.
Require Import Cpdt.CpdtTactics.
Require Import Classical_Prop.
Require Import List.
Require Import Bool.Bool.

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

Eval simpl in formulaTrue (fun _ => false) (Lit (Var 1)).

Inductive maybe (A : Set) (P : A -> Prop) : Set :=
| Unknown : maybe P
| Found : forall x : A, P x -> maybe P.

(* we can define some new notations for convenient usage of type maybe. *)
Notation "{{ x | P }}" := (maybe (fun x => P)).
Notation "??" := (Unknown _ ).
Notation "[| x |]" := (Found _ x _).

Fixpoint vars_in_liter l : list var :=
  match l with
  | Var v => v :: nil
  | Not v => v :: nil
  | Disj l1 l2 => vars_in_liter l1 ++ vars_in_liter l2
  end.                               

Fixpoint vars_in_formula_dupl f : list var :=
  match f with
  | Lit l => vars_in_liter l
  | Conj f1 f2 => vars_in_formula_dupl f1 ++ vars_in_formula_dupl f2
  end.                                 

Definition eq_nat_dec (n m : var) : {n = m} + {n <> m}.
decide equality.
Defined.

Definition In_lst (x : var) (ls : list var) : {In x ls} + {~(In x ls)}.
  induction ls.
  - crush.
  - inversion IHls.
    left. crush.
    destruct (eq_nat_dec x a).
    + left. crush.
    + right. crush. 
Defined.       

Fixpoint remove_dups ls : list var :=
  match ls with
  | nil => nil
  | x :: xs => match (In_lst x xs) with 
                 | left _ => remove_dups xs
                 | right _ => x :: remove_dups xs 
                 end
  end.            

Print map.
(*
map = 
fun (A B : Type) (f : A -> B) =>
fix map (l : list A) : list B := match l with
                                 | nil => nil
                                 | a :: t => f a :: map t
                                 end
     : forall A B : Type, (A -> B) -> list A -> list B
*)
(* DO NOT WORKS CORRECTLY. TO BE FINISHED, not all possible maps included *)
Fixpoint all_maps (l : list var) : list tvals :=
  match l with
  | nil => (fun _ => false) :: nil
  | c :: cs =>
    (c !-> true ; (fun _ => false)) ::
    map (fun lst_tvals => (c !-> true; lst_tvals)) (all_maps cs) 
  end.

Eval simpl in all_maps (1 :: 2 :: 3 :: nil).
(* for test
 = (1 !-> true; (fun _ : var => false))
       :: (1 !-> true; 2 !-> true; (fun _ : var => false))
          :: (1 !-> true; 2 !-> true; 3 !-> true; (fun _ : var => false)) :: nil
     : list tvals
*)

(* 
vars in formula no duplicates, full list of vars :
remove_dups ( vars_in_formula_dupl f )

algorithm
1) create all possible combinations of maps. starting with all vars in list = false
2) check each map and first one where formula is formulaTrue will be our map.

create all possible combinations of maps

map :: forall A B : Type, (A -> B) -> list A -> list B

*)

Search eq.

  
Definition checkOneMap (f : formula) (map : tvals) : {formulaTrue map f} + {~formulaTrue map f}.
  Hint Constructors formulaTrue.
  induction f.
  - induction l.
    + destruct (map v) as [H | H'] eqn:G; crush. right. intros. inversion H. crush. 
    + destruct (map v) as [H | H'] eqn:G; crush. right. intros. inversion H. crush.
    + inversion IHl1; inversion IHl2; crush. right. intros. inversion H1. crush. 
  - inversion IHf1; inversion IHf2; crush. right. intros. inversion H1. crush.
    right. intros. inversion H1; crush. right. intros. inversion H1; crush.
Defined. 

Theorem no_Vars_in_formula : forall f, all_maps (remove_dups (vars_in_formula_dupl f)) = nil -> (forall truth, ~(formulaTrue truth f)). Admitted. (* if no variables in formula,  *)

Definition checkFormula : forall f : formula, {truth : tvals | formulaTrue truth f } + {forall truth, ~ formulaTrue truth f }.
  Hint Constructors formulaTrue.
  intros. 
  induction (all_maps (remove_dups (vars_in_formula_dupl f))) eqn:E.
  - right. apply no_Vars_in_formula. assumption. 
  - destruct (checkOneMap f a) as [H | H'] eqn:G.
    + left. exists a. assumption.
    + apply IHl.
