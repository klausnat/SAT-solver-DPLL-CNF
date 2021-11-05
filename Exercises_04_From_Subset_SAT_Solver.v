Require Import Cpdt.CpdtTactics.
Require Import Classical_Prop.
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

Theorem sameMap : forall x x0 f, formulaTrue x0 f ->
                                 forall vr, x vr = x0 vr ->
                                            formulaTrue x f.
  Admitted. 


Definition checkFormula : forall f : formula,
    {truth : tvals | formulaTrue truth f } + {forall truth, ~(formulaTrue truth f) }.
  Hint Constructors formulaTrue.
(* delete below *)
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
      constructor. econstructor. constructor.
      apply f.
      assert (H : (forall vr, x vr = x0 vr) \/ ~(forall vr, x vr = x0 vr)). apply classic.
      destruct H.
      * eapply sameMap. apply f0. apply H.
      * crush. exfalso. apply H. intros. induction vr. 
      
      
      
    + apply inright. intros. inversion H. apply b with truth. apply H4.
    + apply inright. intros. inversion H. apply b with truth. apply H3.
    + apply inright. intros. inversion H. apply b in H3. inversion H3. 
      


(* Defined. *)

Eval simpl in checkFormula (Var 6).
Eval simpl in checkFormula (Not 6).

(* delete abowe *)





  
  refine (fix F (f : formula) : {truth : tvals | formulaTrue truth f } + {forall truth, ~(formulaTrue truth f) } :=
            match f return {truth : tvals | formulaTrue truth f } + {forall truth, ~(formulaTrue truth f) } with
            | Var x => left (exist ( x !-> true ; _ !-> false ), formulaTrue ( x !-> true ; _ !-> false ) (Var x)) 
            end); crush.
Defined.


    


  
