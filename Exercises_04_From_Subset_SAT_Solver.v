Set Implicit Arguments.
Require Import Cpdt.CpdtTactics.
Require Import Classical_Prop.
Require Import List.

(*
Implement the DPLL satisfibility decision procedure for boolean formulas in conjunc-
tive normal form, with a dependent type that guarantees its correctness. An example
of a reasonable type for this function would be ∀ f : formula, {truth : tvals | formu-
laTrue truth f } + {∀ truth, ¬ formulaTrue truth f }. Implement at least "the basic
backtracking algorithm" as defined here:

                             http://en.wikipedia.org/wiki/DPLL_algorithm

It might also be instructive to implement the unit propagation and pure literal elimi-
nation optimizations described there or some other optimizations that have been used
in modern SAT solvers.
*)

(* 
Inductive sumbool (A : Prop) (B : Prop) : Set :=
  left : A → {A} + {B} | right : B → {A} + {B}  

Inductive sig (A : Type) (P : A → Prop) : Type :=
exist : ∀ x : A, P x → sig P

Notation
"{ x : A | P }" := sig (fun x : A ⇒ P)

*)

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

Inductive formula : Set :=
| Var : var -> formula
| Not : var -> formula
| Conj : formula -> formula -> formula. 

Inductive formulaTrue : tvals -> formula -> Prop :=
| TVar : forall tv var, tv var = true -> formulaTrue tv (Var var)
| TNotVar : forall tv var, tv var = false -> formulaTrue tv (Not var)
| TConj : forall f1 f2 tv, formulaTrue tv f1 -> formulaTrue tv f2 -> formulaTrue tv (Conj f1 f2). 

(* Группа функций для извлечения списка переменных из двух формул НИЖЕ *)
Fixpoint vars_in_formula f : list var :=
  match f with
  | Var v => v :: nil
  | Not v => v :: nil
  | Conj f1 f2 => (vars_in_formula f1) ++ (vars_in_formula f2)
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

(* list of vars from two lists. no duplicates *)
Fixpoint unite_lists ls1 ls2 : list var :=
  match ls1 with
    | nil => ls2
    | x :: xs => match (In_lst x ls2) with 
                 | left _ => unite_lists xs ls2
                 | right _ => x :: unite_lists xs ls2
                 end
    end.

(* only elements, which present in both lists, common elements *)
Fixpoint only_commons ls1 ls2 : list var :=
    match ls1 with
    | nil => nil
    | x :: xs => match ls2 with 
                 | nil => nil
                 | _ => match (In_lst x ls2) with
                        | left _ => x :: only_commons xs ls2
                        | right _ => only_commons xs ls2
                        end                          
                 end
    end.

Definition vars_in_two_formulas f1 f2 : list var :=
  unite_lists (vars_in_formula f1) (vars_in_formula f2).


(* only vars which present in both formulas. Vars that can contradict *)
Definition common_vars_for_two_formulas f1 f2 : list var :=
  only_commons (vars_in_formula f1) (vars_in_formula f2).

Lemma vars_in_formula_not_nil : forall f, vars_in_formula f = nil -> False.
  intros. induction f; crush. Search (_ ++ _) nil.
  (* app_eq_nil: forall [A : Type] (l l' : list A), l ++ l' = nil -> l = nil /\ l' = nil *)
  apply app_eq_nil in H. crush.
  Qed. 

Lemma unite_nil : forall ls1 ls2, unite_lists ls1 ls2 = nil -> ls1 = nil /\ ls2 = nil.
  intros. induction ls1. crush.
  simpl in H. crush.
  destruct (In_lst a ls2). crush. crush.
  destruct (In_lst a ls2). crush. crush.
Qed.   

Lemma vars_in_two_formulas_not_nil : forall f1 f2, vars_in_two_formulas f1 f2 = nil -> False.
  intros. unfold vars_in_two_formulas in H.
  apply unite_nil in H. crush. apply vars_in_formula_not_nil in H0.
  crush.
Qed. 
  
Theorem notExists : forall f1 f2, vars_in_two_formulas f1 f2 = nil -> forall comb, ~(formulaTrue comb f1 /\ formulaTrue comb f2).
  intros. apply vars_in_two_formulas_not_nil in H. crush.
Qed.   

Definition combined_map :
  forall (f1 f2 : formula) (m1 m2 : tvals) (pf1 : formulaTrue m1 f1) (pf2 : formulaTrue m2 f2),
    {comb : tvals | formulaTrue comb f1 /\ formulaTrue comb f2} +
    {forall comb, ~(formulaTrue comb f1 /\ formulaTrue comb f2)}.
  Print sumbool. 
    refine (fix F (f1 f2 : formula) (m1 m2 : tvals) (pf1 : formulaTrue m1 f1) (pf2 : formulaTrue m2 f2) :
         {comb : tvals | formulaTrue comb f1 /\ formulaTrue comb f2} +
         {forall comb, ~(formulaTrue comb f1 /\ formulaTrue comb f2)} :=
              match vars_in_two_formulas f1 f2 as res with 
              | nil => inright (notExists res)
              | (x :: xs) => _ (* if contradictions on precise meanings right if no contrad-s *)
              end
           ); crush.  
    
(* Группа функций для извлечения списка переменных из двух формул ВЫШЕ *)

Definition checkFormula : forall f : formula,
    {truth : tvals | formulaTrue truth f } + {forall truth, ~(formulaTrue truth f) }.
  Hint Constructors formulaTrue.

  intros.
  induction f.
  - constructor.
    econstructor.
    constructor.
    assert (( v !-> true ; _ !-> false ) v = true).
    { induction v. crush. crush. }
    apply H.
  - constructor.
    econstructor.
    constructor.
    assert (( v !-> false ; _ !-> true ) v = false).
    { induction v. crush. crush. }
    apply H.
  - crush. 
    + destruct a.
      destruct a0.
      destruct (combined_map f f0) as [ L i | R j ].
      * left. destruct L. exists x1. constructor. crush. crush.
      * right. crush. apply R with truth. crush. inversion H; crush. inversion H; crush. 
    + apply inright. intros. inversion H. apply b with truth. apply H4.
    + apply inright. intros. inversion H. apply b with truth. apply H3.
    + apply inright. intros. inversion H. apply b in H3. inversion H3. 
Defined.       


Eval simpl in checkFormula (Var 6).
Eval simpl in checkFormula (Not 6).
Eval simpl in checkFormula (Conj (Var 6) (Not 6)).


(* когда пыталась доказать третий случай, однажды понуждалась в этой теореме *)
Theorem sameMap : forall x x0 f, formulaTrue x0 f ->
                                 forall vr, x vr = x0 vr ->
                                            formulaTrue x f.
  Admitted. 

(* можно сделать работу с сумбул more convenient - не использовано пока *)
Notation "’Yes’" := (left ).
Notation "’No’" := (right ).
Notation "’Reduce’ x" := (if x then Yes else No) (at level 50).



  
  refine (fix F (f : formula) : {truth : tvals | formulaTrue truth f } + {forall truth, ~(formulaTrue truth f) } :=
            match f return {truth : tvals | formulaTrue truth f } + {forall truth, ~(formulaTrue truth f) } with
            | Var x => left (exist ( x !-> true ; _ !-> false ), formulaTrue ( x !-> true ; _ !-> false ) (Var x)) 
            end); crush.
Defined.


