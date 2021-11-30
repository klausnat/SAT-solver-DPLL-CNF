Set Implicit Arguments.
Set Asymmetric Patterns.
Require Import Cpdt.CpdtTactics.
Require Import Classical_Prop.
Require Import List.
Require Import Bool.Bool.

Definition var := nat % type. 
Definition total_map := var -> bool.
Definition t_empty : total_map :=
  (fun _ => false).
Definition t_update (m : total_map)
                    (x : var) (v : bool) :=
  fun x' => if PeanoNat.Nat.eqb x x' then v else m x'.
(* to create an empty total map with default value *)
Notation "'_' '!->' v" := t_empty
                            (at level 100, right associativity).
(* extending existing map with some bindings *)
Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).

Lemma t_update_eq : forall (m : total_map) x v,
  (x !-> v ; m) x = v.
Proof. intros. 
       unfold t_update. rewrite PeanoNat.Nat.eqb_refl. crush. Qed. 

Definition tvals := total_map.

Inductive formula : Set :=
| Var : var -> formula
| Not : var -> formula
| Disj : formula -> formula -> formula                        
| Conj : formula -> formula -> formula.   

Definition eq_nat_dec (n m : var) : {n = m} + {n <> m}.
decide equality.
Defined.
(* 
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
 *)

Definition nodup_var := nodup eq_nat_dec. 

Fixpoint vars_in_formula f : list var :=
  match f with
  | Var v => v :: nil
  | Not v => v :: nil
  | Disj f1 f2 => nodup_var (vars_in_formula f1 ++ vars_in_formula f2)             
  | Conj f1 f2 => nodup_var (vars_in_formula f1 ++ vars_in_formula f2)
  end.                                 

Inductive maybe (A : Set) (P : A -> Prop) : Set :=
| Unknown : maybe P
| Found : forall x : A, P x -> maybe P.

(* we can define some new notations for convenient usage of type maybe. *)
Notation "{{ x | P }}" := (maybe (fun x => P)).
Notation "??" := (Unknown _ ).
Notation "[| x |]" := (Found _ x _).

Fixpoint evalFormula f map {struct f} : bool :=
  match f with
  | Var v => map v 
  | Not v => negb (map v)  
  | Disj f1 f2 => orb (evalFormula f1 map) (evalFormula f2 map)  
  | Conj f1 f2 => andb (evalFormula f1 map) (evalFormula f2 map)
  end.  

Fixpoint CreateAllFalsesMap (ls : list var) map : tvals :=
  match ls with
  | nil => map
  | x :: xs => CreateAllFalsesMap xs (x !-> false ; map) 
  end.                                 

Eval simpl in CreateAllFalsesMap (1 :: 2 :: 3 :: nil) t_empty.
(* remove_dups (vars_in_formula_dupl f) - all vars in formula 

checkVars начинает работу с карты, на которой all vars = false. 
1) пробует изменить первую вару на тру. если нашли решение - возвращаем 
2) 

*)

Definition checkVars : forall (ls : list var) (f : formula) (map : tvals), {{ map' | evalFormula f map' = true }}.
  refine (fix F (ls : list var) (f : formula) (map : tvals) : {{ map' | evalFormula f map' = true }} := 
  match ls with
  | nil => _
  | x :: xs => match F xs f (x !-> true; map) with
               | ?? => F xs f (x !-> false; map)
               | res => res
               end
  end).
  destruct (evalFormula f map) eqn:E.
  - eapply (Found _ map E).
  - apply ??.
Defined.     

Definition f :=  (Disj (Var 1) (Disj (Var 2) (Not 3))).
Eval simpl in checkVars (nodup_var (vars_in_formula f)) f t_empty.

Definition f1 :=  (Conj (Var 1) (Not 1)).
Eval simpl in checkVars ((vars_in_formula f1)) f1 t_empty.

Search PeanoNat.Nat.eqb.
Locate PeanoNat.Nat.eqb.
Check PeanoNat.Nat.eqb.

Print In. 
(* отличается от библиотечного In тем, что возвращает bool, а не Prop *)
Fixpoint In_var_ls' (x : var) (ls : list var) : bool :=
  match ls with
  | nil => false
  | x' :: xs => match PeanoNat.Nat.eqb x x' with
                | true => true
                | false => In_var_ls' x xs
                end                     
  end.                                                                   

Eval simpl in In_var_ls' 0 (1 :: 2 :: 3 :: nil).

Locate reflect.
Print Coq.Bool.Bool.reflect.
(*
Inductive reflect (P : Prop) : bool -> Set :=
    ReflectT : P -> reflect P true | ReflectF : ~ P -> reflect P false
*)
Lemma In_reflect : forall x ls, reflect (In x ls) (In_var_ls' x ls).
  intros. induction ls.
  - crush.
  - destruct (PeanoNat.Nat.eqb x a) eqn:E.
    + crush. constructor. left.
      apply PeanoNat.Nat.eqb_eq. rewrite PeanoNat.Nat.eqb_sym. auto.
    + crush. inversion IHls. constructor. crush. constructor. crush. 
      Search PeanoNat.Nat.eqb. assert (H' : PeanoNat.Nat.eqb x x = true ).
      apply (PeanoNat.Nat.eqb_refl x). crush. 
Qed.   

(* Definition In_var_ls : forall x ls, {In_var_ls' x ls = true} + {~(In_var_ls' x ls = true)}. *)

Inductive formula_List_Vars : list var -> formula -> Set := 
| FVars_Var : forall v ls, In_var_ls' v ls  = true -> formula_List_Vars ls (Var v)
| FVars_Not : forall v ls, In_var_ls' v ls = true -> formula_List_Vars ls (Not v)
| FVars_Disj : forall f1 f2 ls1 ls2, formula_List_Vars ls1 f1->
                                     formula_List_Vars ls2 f2 ->
                                     formula_List_Vars (nodup_var (ls1 ++ ls2)) (Disj f1 f2)
| FVars_Conj : forall f1 f2 ls1 ls2, formula_List_Vars ls1 f1 ->
                                     formula_List_Vars ls2 f2 ->
                                     formula_List_Vars (nodup_var (ls1 ++ ls2)) (Conj f1 f2).
Search list. 
Inductive formula_List_Vars_sub : list var -> formula -> Set := 
| FVars_Var : forall v ls, In_var_ls' v ls  = true -> formula_List_Vars ls (Var v)
| FVars_Not : forall v ls, In_var_ls' v ls = true -> formula_List_Vars ls (Not v)
| FVars_Disj : forall f1 f2 ls1 ls2, formula_List_Vars ls1 f1->
                                     formula_List_Vars ls2 f2 ->
                                     formula_List_Vars (nodup_var (ls1 ++ ls2)) (Disj f1 f2)
| FVars_Conj : forall f1 f2 ls1 ls2, formula_List_Vars ls1 f1 ->
                                     formula_List_Vars ls2 f2 ->
                                     formula_List_Vars (nodup_var (ls1 ++ ls2)) (Conj f1 f2).


Lemma flv : forall f, formula_List_Vars (vars_in_formula f) f.
  intros. induction f0.
  - crush. constructor. crush. rewrite (PeanoNat.Nat.eqb_refl v). reflexivity.
  - crush. constructor. crush. rewrite (PeanoNat.Nat.eqb_refl v). reflexivity.
  - simpl. constructor. crush. crush.
  - simpl. constructor. crush. crush. 
Qed.

Fixpoint eq_map (ls : list var) (m1 m2 : tvals) : bool :=
  match ls with
  | nil => true
  | x :: xs => if eqb (m1 x) (m2 x) then eq_map xs m1 m2 else false
  end.                                                              

Notation "m1 '==(' vrs ')' m2" := (eq_map vrs m1 m2 = true) (at level 50).

Lemma inFalse : forall v vrs m1, In_var_ls' v vrs = true -> (v !-> true ; m1) ==(vrs) (v !-> false ; m1). Admitted.

Inductive formulaTrue : tvals -> formula -> Prop :=
| TVar : forall tv var, tv var = true -> formulaTrue tv (Var var)
| TNot : forall tv var, tv var = false -> formulaTrue tv (Not var)
| TDisj : forall f1 f2 tv, formulaTrue tv f1 \/ formulaTrue tv f2 ->
                           formulaTrue tv (Disj f1 f2)
| TConj : forall f1 f2 tv, formulaTrue tv f1 -> formulaTrue tv f2 -> formulaTrue tv (Conj f1 f2). 

Inductive formula_map : tvals -> formula -> Set :=
| FM_Var_True : forall map var, map var = true -> formula_map map (Var var)
| FM_Var_False : forall map var, map var = false -> formula_map map (Var var)
| FM_Not_True : forall map var, map var = true -> formula_map map (Not var)
| FM_Not_False : forall map var, map var = false -> formula_map map (Not var)
| FM_Disj : forall f1 f2 map, formula_map map f1 ->
                              formula_map map f2 ->
                              formula_map map (Disj f1 f2)
| FM_Conj : forall f1 f2 map, formula_map map f1 ->
                              formula_map map f2 ->
                              formula_map map (Conj f1 f2).

Lemma t_empty_map : forall f, formula_map t_empty f.
  intros. induction f0. apply FM_Var_False. unfold t_empty. auto.
  apply FM_Not_False. unfold t_empty. auto. constructor. auto. crush. constructor. crush. crush. 
Qed.

Definition checkOneMap (f : formula) (map : tvals) : {formulaTrue map f} + {~formulaTrue map f}.
  Hint Constructors formulaTrue.
  induction f.
  - destruct (map v) eqn:G. left. constructor. auto. right.
      unfold not. intros. inversion H. crush. 
  - destruct (map v) eqn:G. right; crush. inversion H. crush.
    left. constructor. auto.
  - inversion IHf1; inversion IHf2; crush. right. intros. inversion H1. crush.
  - inversion IHf1; inversion IHf2; crush. right. intros. inversion H1. crush.
    right. intros. inversion H1. crush. right. intros. inversion H1. crush. 
Defined.   

Lemma not_nil : forall f, formula_List_Vars nil f -> forall truth, ~ formulaTrue truth f.
  intros.
  induction f0.
  - crush. inversion H. inversion H3.
  - crush. inversion H. inversion H3.
  - unfold not. intros. inversion H. crush.
    inversion H0.
    (* доказать, что ls1 = nil /\ ls2 = nil, subst.  *)
Admitted. 

Definition CheckFormulaHelp : forall f ls map, formula_List_Vars_sub ls f -> formula_map map f -> {truth : tvals | formulaTrue truth f } + {forall truth, ~ formulaTrue truth f }.
refine (fix F f ls map pf1 pf2 : {truth : tvals | formulaTrue truth f } + {forall truth, ~ formulaTrue truth f } :=
          match ls return {truth : tvals | formulaTrue truth f } + {forall truth, ~ formulaTrue truth f } with
          | nil => _
          | x :: xs => match F f xs (x !-> true; map) _ _ with
                       | ?? => F xs f (x !-> false; map)
                       | res => res
                       end
          end).                  
- admit. 
- 

  Definition CheckFormula (f : formula) : {truth : tvals | formulaTrue truth f } + {forall truth, ~ formulaTrue truth f } := @CheckFormulaHelp f (vars_in_formula f) t_empty (flv f) (t_empty_map f). 


Definition checkFormula : forall (f : formula) (pf :  formula_List_Vars (vars_in_formula f) f),
    {truth : tvals | evalFormula f truth = true } + {forall truth, evalFormula f truth = false}.
refine (fix F f pf : {truth : tvals | evalFormula f truth = true } + {forall truth, evalFormula f truth = false} :=
          match f return {truth : tvals | evalFormula f truth = true } + {forall truth, evalFormula f truth = false} with
          | Var v => _
          | Not v => _
          | Disj f1 f2 => _
          | Conj f1 f2 => _
          end).                  

(* Definition CheckFormulaHelp : forall f ls map, formula_List_Vars ls f -> formula_map map f -> *)
(*   {truth : tvals | formula_map truth f -> formulaDenote truth f = true} + {forall truth, formula_map truth f ->  evalFormula truth f = false}. *)

Definition checkVars : forall (ls : list var) (f : formula) (map : tvals), {{ map' | evalFormula f map' = true }}.

1. как показать, что если ls = nil то map уже не удастся изменять. Не нашли
2. как показать, что если map изменить нельзя, то не существует возможной оценки.
3. что значит, что map изменять нельзя.

Definition checkVars' : forall (ls : list var) (f : formula) (map : tvals), { map' | evalFormula f map' = true } + {
forall map', map'
evalFormula f map' = false
                                                                                                                   }.
  
  refine (fix F (ls : list var) (f : formula) (map : tvals) : { map' | evalFormula f map' = true } + {forall map', evalFormula f map' = false} := 
  match ls with
  | nil => _
  | x :: xs => match F xs f (x !-> true; map) with
               | ?? => F xs f (x !-> false; map)
               | res => res
               end
  end).
  destruct (evalFormula f map) eqn:E.
  - eapply (Found _ map E).
  - apply ??.
Defined.     

(* BELOW NAT"S DEFINITIONS *)




Inductive formulaTrue : tvals -> formula -> Prop :=
| TVar : forall tv var, tv var = Some true -> formulaTrue tv (Lit (Var var))
| TNot : forall tv var, tv var = Some false -> formulaTrue tv (Lit (Not var)).

(* что список принадлежит формуле (это ее контекст) with duplicates, I probably don't need this Prop *)
Inductive formula_List_Vars : list var -> formula -> Prop := 
| FVars_Var : forall var ls, In var ls -> formula_List_Vars ls (Lit (Var var))
| FVars_Not : forall var ls, In var ls -> formula_List_Vars ls (Lit (Not var)).

(* что мапа принадлежит формуле, может формула и не true на этой мапе. НАДО? *)
Inductive formula_map : tvals -> formula -> Set :=
| FM_Var_True : forall map var, map var = Some true -> formula_map map (Lit (Var var))
| FM_Var_False : forall map var, map var = Some false -> formula_map map (Lit (Var var))
| FM_Not_True : forall map var, map var = Some true -> formula_map map (Lit (Not var))
| FM_Not_False : forall map var, map var = Some false -> formula_map map (Lit (Not var)).

Inductive formula_all_maps : list tvals -> formula -> Type :=
| FAM_Var : forall map ls v, In map ls -> formula_map map (Lit (Var v)) -> length ls = 2  -> formula_all_maps ls (Lit (Var v))
| FAM_Not : forall map ls v, In map ls -> formula_map map (Lit (Not v)) -> length ls = 2  -> formula_all_maps ls (Lit (Not v)).

Theorem all_maps_not_nil : forall f, formula_all_maps nil f -> False.
  intros. induction f; destruct l; crush. inversion X. crush. inversion X. crush. 
Qed. 

Definition checkOneMap (f : formula) (map : tvals) : {formulaTrue map f} + {~formulaTrue map f}.
  Hint Constructors formulaTrue.
  induction f.
  - induction l.
    + destruct (map v) eqn:G. destruct b eqn:E. left. constructor. auto. right.
      unfold not. intros. inversion H. crush. right. unfold not. intros. inversion H. crush.
    + destruct (map v) eqn:G. (destruct b); crush. right; crush. inversion H. crush.
      right. unfold not. intros. inversion H. crush.
Defined.       

Definition equal_maps_on_formula (m1 m2 : tvals) : Prop :=
  forall (v : var) (f : formula) (ls : list var), formula_List_Vars ls f /\ m1 v = m2 v /\ In v ls.

(* теорема в своем док-ве опирается на длину списка всех возможных для формулы мапов *)
Theorem FAM : forall f t, formula_all_maps (t :: nil) f -> ~ formulaTrue t f -> (forall truth, ~formulaTrue truth f ).
  intros. unfold not. intros.
inversion X. crush. crush. Qed. 

(* ПЛАН РАБОТЫ 
0) ввести длину списка в formula_all_maps
0) переписать определение (In map tvals) чтобы оно было ориентировано на tvals 
1) создать подтип от formula_all_maps, formula_all_maps_sub : list tvals -> formula -> n
*)

Definition checkFormula : forall f : formula, {truth : tvals | formulaTrue truth f } + {forall truth, ~formulaTrue truth f }.
  intros f.
  assert (H : formula_List_Vars (remove_dups (vars_in_formula_dupl f)) f ).
  { induction f. induction l. simpl. constructor. crush. simpl. constructor. crush. }
  assert (G : formula_all_maps (makeAllMaps (remove_dups (vars_in_formula_dupl f)) ( (CreateAllFalsesMap (remove_dups (vars_in_formula_dupl f)) empty) :: nil)) f).
  { induction f.
    - induction l.
      + simpl in H. simpl. eapply FAM_Var. simpl. crush. constructor.
        rewrite update_shadow. rewrite update_eq. reflexivity. crush. 
      + simpl in H. simpl. eapply FAM_Not. simpl. crush. constructor.
        rewrite update_shadow. rewrite update_eq. reflexivity. crush. 
  }
  remember (remove_dups (vars_in_formula_dupl f)) as fav.
  remember (makeAllMaps fav (CreateAllFalsesMap fav empty :: nil)) as fam.
  clear Heqfav H Heqfam fav.
    generalize dependent f. generalize dependent fam.
  refine (fix F fam f pf :  {truth : tvals | formulaTrue truth f} + {forall truth : tvals, ~ formulaTrue truth f} :=
            match f return  {truth : tvals | formulaTrue truth f} + {forall truth : tvals, ~ formulaTrue truth f}
            with
            | Lit (Var v) => _
            | Lit (Not v) => _
            end).                 
  - destruct fam.
    + crush. apply all_maps_not_nil in pf. inversion pf.
    + 


  

  - admit.
  - left. exists x. auto. 
  - 
    
