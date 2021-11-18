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

Definition tvals := partial_map bool.

Inductive literal : Set :=
| Var : var -> literal
| Not : var -> literal                 
| Disj : literal -> literal -> literal.

Inductive formula : Set :=
| Lit : literal -> formula
| Conj : formula -> formula -> formula.    

(*             (x \/ y \/ ~z) : Lit (Disj (Var x) (Disj (Var y) (Not z)))       *)

Inductive formulaTrue : tvals -> formula -> Prop :=
| TVar : forall tv var, tv var = Some true -> formulaTrue tv (Lit (Var var))
| TNot : forall tv var, tv var = Some false -> formulaTrue tv (Lit (Not var))
| TDisj : forall l1 l2 tv, formulaTrue tv (Lit l1) \/ formulaTrue tv (Lit l2) ->
                           formulaTrue tv (Lit (Disj l1 l2))
| TConj : forall f1 f2 tv, formulaTrue tv f1 -> formulaTrue tv f2 -> formulaTrue tv (Conj f1 f2). 

Eval simpl in formulaTrue (fun _ => Some false) (Lit (Var 1)).

Print option. 
(* We, probably do not need this definition of maybe Inductive type... *)
Inductive maybe (A : Set) (P : A -> Prop) : Set :=
| Unknown : maybe P
| Found : forall x : A, P x -> maybe P.

(* we can define some new notations for convenient usage of type maybe. *)
Notation "{{ x | P }}" := (maybe (fun x => P)).
Notation "??" := (Unknown _ ).
Notation "[| x |]" := (Found _ x _).

Notation "x <- e1 ; e2" := (match e1 with
                             | Unknown => ??
                             | Found x _ => e2
                           end)
(right associativity, at level 60).

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

(* СОЗДАЕМ ВСЕВОЗМОЖНЫЕ МАПЫ ДЛЯ ЭТОЙ ФОРМУЛЫ, думаю, это неправильный подход, попробую создать мапу из зависимых индуктивных типов. 
при вызове первым списком всевозможных мапов передавать ((всем присвоить false) :: nil), то есть всем варам в списке присвоили - false, эту мапу будем размножать до состояния "все возможные" 
ПЛАН:
- взяли переменную из списка и cur_maps. 
- создали новый набор cur_maps, где эта переменная заменена на true.
- создали новый cur_maps, который сумма исходного cur_maps и созданного на втором шаге. cur_maps = cur_maps ++ generated_maps
- вызвали fixpoint F на следующей переменной и на новом, увеличенном cur_maps.
 *)

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
| FVars_Var : forall var, formula_List_Vars (var :: nil) (Lit (Var var))
| FVars_Not : forall var, formula_List_Vars (var :: nil) (Lit (Not var))
| FVars_Disj : forall liter1 liter2 ls1 ls2, formula_List_Vars ls1 (Lit liter1) ->
                                         formula_List_Vars ls2 (Lit liter2) ->
                                         formula_List_Vars (ls1 ++ ls2) (Lit (Disj liter1 liter2))
| FVars_Conj : forall f1 f2 ls1 ls2, formula_List_Vars ls1 f1 ->
                                 formula_List_Vars ls2 f2 ->
                                 formula_List_Vars (ls1 ++ ls2) (Conj f1 f2).

(* что мапа принадлежит формуле, может формула и не true на этой мапе. НАДО? *)
Inductive formula_map : tvals -> formula -> Prop :=
| FM_Var_True : forall map var, map var = Some true -> formula_map map (Lit (Var var))
| FM_Var_False : forall map var, map var = Some false -> formula_map map (Lit (Var var))
| FM_Not_True : forall map var, map var = Some true -> formula_map map (Lit (Not var))
| FM_Not_False : forall map var, map var = Some false -> formula_map map (Lit (Not var))
| FM_Disj : forall lit1 lit2 map, formula_map map (Lit lit1) ->
                                  formula_map map (Lit lit2) ->
                                  formula_map map (Lit (Disj lit1 lit2)) 
| FM_Conj : forall f1 f2 map, formula_map map f1 ->
                              formula_map map f2 ->
                              formula_map map (Conj f1 f2).

(* какрта связана со списком переменных *)
Definition map_and_vars (ls : list tvals) (map : tvals) :=
  forall var res, map var = Some res /\ In map ls.

(* представитель этого типа является доказательством того, что в списке мапов перечислены все мапы формулы *)
(*
Inductive formula_allMaps : list tvals -> formula -> Prop :=
| LstMpsVar : forall ls var m1 m2 ls,
                     In_ls m1 ls = left (In m1 ls) /\ FM_Var_True m1 (Lit (Var var)) ->
                     In_ls m2 ls = left (In m2 ls) /\ FM_Var_False m2 (Lit (Var var)) ->
                     formula_allMaps ls (Lit (Var var)). *) 

Definition checkOneMap (f : formula) (map : tvals) : {formulaTrue map f} + {~formulaTrue map f}.
  Hint Constructors formulaTrue.
  induction f.
  - induction l.
    + destruct (map v) eqn:G. destruct b eqn:E. left. constructor. auto. right.
      unfold not. intros. inversion H. crush. right. unfold not. intros. inversion H. crush.
    + destruct (map v) eqn:G. (destruct b); crush. right; crush. inversion H. crush.
      right. unfold not. intros. inversion H. crush.
    + inversion IHl1; inversion IHl2; crush. right. intros. inversion H1; crush.
  - inversion IHf1; inversion IHf2; crush. right. intros. inversion H1; crush.
    right. intros. inversion H1; crush. right. intros. inversion H1; crush. 
Defined.     

Definition checkAllMaps : forall (f : formula) (ls : list tvals), option (exists map, formulaTrue map f /\ map_and_vars ls map). Admitted. 

(* if no variables in formula,  *)
(*
Theorem no_Vars_in_formula : forall f, all_maps (remove_dups (vars_in_formula_dupl f)) = nil -> (forall truth, ~(formulaTrue truth f)).
  intros. Admitted.
Print Exists. 
*)
(* Exists: forall [A : Type], (A -> Prop) -> list A -> Prop *)

Definition inclusion {A : Type} (m m' : partial_map A) :=
  forall x v, m x = Some v -> m' x = Some v.

Print sumor.
(** %\vspace{-.15in}% [[
Inductive sumor (A : Type) (B : Prop) : Type :=
    inleft : A -> A + {B} | inright : B -> A + {B}
]] *)

Notation "!!" := (inright _ _).
(** %\def\indash{-}\catcode`-=13\def-{\indash\kern0pt }% *)

Notation "x <-- e1 ; e2" := (match e1 with
                               | inright _ => !!
                               | inleft (exist x _) => e2
                             end)
(right associativity, at level 60).

(** %\catcode`-=12% *)(* *)
(** printing * $\times$ *)
Print checkOneMap.
(* 
Inductive formula_map : tvals -> formula -> Prop (все возможные мапы для конкр. формулы)
                                                   
Definition checkOneMap (f : formula) (map : tvals) : {formulaTrue map f} + {~formulaTrue map f}.
*)
                                              
Definition checkFormula : forall f : formula, {truth : tvals | formulaTrue truth f } + {forall truth, ~formulaTrue truth f }. 
  refine (fix F (f : formula) : {truth : tvals | formulaTrue truth f } + {forall truth, ~(formulaTrue truth f) } :=
            match makeAllMaps (remove_dups (vars_in_formula_dupl f)) ( (CreateAllFalsesMap (remove_dups (vars_in_formula_dupl f)) empty) :: nil)
            return {truth : tvals | formulaTrue truth f } + {forall truth, ~ formulaTrue truth f } with
            | nil => inright _
            | map :: maps => match checkOneMap f map with
                             | left pf => inleft _
                             | right pf => match checkAllMaps f maps with
                                           | None => _
                                           | Some mp => _
                                           end 
                             end                
            end).
  - admit.                      (* список мапов нил. значит нет подходящей мапы, дошли до конца *)
  - exists map. auto.           
  - apply F.
  - apply F. 
    (* checkAllMaps должна возвращать доказательство того, что мап не существует, все перебрали *)
