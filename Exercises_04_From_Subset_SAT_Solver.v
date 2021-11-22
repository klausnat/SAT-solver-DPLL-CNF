Set Implicit Arguments.
Set Asymmetric Patterns.
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

Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
  (x !-> v ; m) x = v.
Proof. Admitted. 


Definition partial_map (A : Type) := total_map (option A).
Definition empty {A : Type} : partial_map A :=
  t_empty None.
Definition update {A : Type} (m : partial_map A)
           (x : var) (v : A) :=
  (x !-> Some v ; m).
 Notation "x '!->' v ';' m" := (update m x v)
  (at level 100, v at next level, right associativity).
(* We can also hide the last case when it is empty. *)
Notation "x '!->' v" := (update empty x v)
  (at level 100).

Lemma t_apply_empty : forall (A : Type) (x : var) (v : A),
  (_ !-> v) x = v.
crush. Qed. 
Lemma apply_empty : forall (A : Type) (x : var),
  @empty A x = None.
Proof. crush. Qed. 

Lemma update_eq : forall (A : Type) (m : partial_map A) x v,
  (x !-> v ; m) x = Some v.
Proof.
  intros. unfold update. rewrite t_update_eq.
  reflexivity.
Qed.

Lemma update_shadow : forall (A : Type) (m : partial_map A) x v1 v2,
  (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m). crush. Admitted. 

Definition tvals := partial_map bool.

Inductive literal : Set :=
| Var : var -> literal
| Not : var -> literal.               

Inductive formula : Set :=
| Lit : literal -> formula.


(*             (x \/ y \/ ~z) : Lit (Disj (Var x) (Disj (Var y) (Not z)))       *)

Inductive formulaTrue : tvals -> formula -> Prop :=
| TVar : forall tv var, tv var = Some true -> formulaTrue tv (Lit (Var var))
| TNot : forall tv var, tv var = Some false -> formulaTrue tv (Lit (Not var)).

Eval simpl in formulaTrue (fun _ => Some false) (Lit (Var 1)).

Fixpoint vars_in_liter l : list var :=
  match l with
  | Var v => v :: nil
  | Not v => v :: nil
   end.                               

Fixpoint vars_in_formula_dupl f : list var :=
  match f with
  | Lit l => vars_in_liter l
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

Fixpoint helper_makeAllMaps var (cur_maps : list tvals) : list tvals :=
  match cur_maps with
  | nil => nil
  | map :: maps => (var !-> true ; map) :: helper_makeAllMaps var maps
  end.                                                

Fixpoint makeAllMaps (ls : list var) (cur_maps : list tvals) : list tvals :=
            match ls return list tvals with
            | nil => cur_maps 
            | v :: vars => makeAllMaps vars ((helper_makeAllMaps v cur_maps) ++ cur_maps)
            end.                  

Fixpoint CreateAllFalsesMap (ls : list var) map : tvals :=
  match ls with
  | nil => map
  | x :: xs => CreateAllFalsesMap xs (x !-> false ; map) 
  end.                                 

Eval simpl in CreateAllFalsesMap (1 :: 2 :: 3 :: nil) empty.

Eval simpl in makeAllMaps (1 :: 2 :: 3 :: nil) ( (CreateAllFalsesMap (1 :: 2 :: 3 :: nil) empty) :: nil).

(* что список принадлежит формуле (это ее контекст) with duplicates, I probably don't need this Prop *)
Inductive formula_List_Vars : list var -> formula -> Prop := 
| FVars_Var : forall var ls, In var ls -> formula_List_Vars ls (Lit (Var var))
| FVars_Not : forall var ls, In var ls -> formula_List_Vars ls (Lit (Not var)).

(* что мапа принадлежит формуле, может формула и не true на этой мапе. НАДО? *)
Inductive formula_map : tvals -> formula -> Prop :=
| FM_Var_True : forall map var, map var = Some true -> formula_map map (Lit (Var var))
| FM_Var_False : forall map var, map var = Some false -> formula_map map (Lit (Var var))
| FM_Not_True : forall map var, map var = Some true -> formula_map map (Lit (Not var))
| FM_Not_False : forall map var, map var = Some false -> formula_map map (Lit (Not var)).

Inductive formula_all_maps : list tvals -> formula -> Prop :=
  | Constr : forall map ls f, In map ls -> formula_map map f -> ls <> nil -> formula_all_maps ls f.

Theorem all_maps_not_nil : forall f, formula_all_maps nil f -> False.
  intros. induction f; destruct l; crush. simpl in H. inversion H. inversion H0.
  inversion H. inversion H0. Qed. 

Definition checkOneMap (f : formula) (map : tvals) : {formulaTrue map f} + {~formulaTrue map f}.
  Hint Constructors formulaTrue.
  induction f.
  - induction l.
    + destruct (map v) eqn:G. destruct b eqn:E. left. constructor. auto. right.
      unfold not. intros. inversion H. crush. right. unfold not. intros. inversion H. crush.
    + destruct (map v) eqn:G. (destruct b); crush. right; crush. inversion H. crush.
      right. unfold not. intros. inversion H. crush.
Defined.       

Definition checkFormula : forall f : formula, {truth : tvals | formulaTrue truth f } + {forall truth, ~formulaTrue truth f }.
  intros f. 
  assert (H : formula_List_Vars (remove_dups (vars_in_formula_dupl f)) f ).
  { induction f. induction l. simpl. constructor. crush. simpl. constructor. crush. }
  assert (G : formula_all_maps (makeAllMaps (remove_dups (vars_in_formula_dupl f)) ( (CreateAllFalsesMap (remove_dups (vars_in_formula_dupl f)) empty) :: nil)) f).
  { induction f.
    - induction l.
      + simpl in H. simpl. eapply Constr. simpl. crush. constructor.
        rewrite update_shadow. rewrite update_eq. reflexivity. crush. 
      + simpl in H. simpl. eapply Constr. simpl. crush. constructor.
        rewrite update_shadow. rewrite update_eq. reflexivity. crush. 
  }
  generalize dependent f.
  intros. 
  destruct (makeAllMaps (remove_dups (vars_in_formula_dupl f))
                        (CreateAllFalsesMap (remove_dups (vars_in_formula_dupl f)) empty :: nil)) eqn:F.
  apply all_maps_not_nil in G. inversion G.
  clear F. clear H.
  destruct (checkOneMap f t) eqn:E.
  constructor. exists t. apply f0.
  induction l eqn:H'.
  right. intros. 

  generalize dependent f. 
