Require Import Classical Logic.
Require Import Ensembles.
Require Import Finite_sets.
Require Import Powerset_facts.
Require Import Bool.
Require Import SetoidClass.

Section Def.
  Variable t : Type. (* Prop Variable Type *)

  Inductive formula :=
  | fVar : t -> formula
  | fNot : formula -> formula
  | fAnd : formula -> formula -> formula
  | fOr : formula -> formula -> formula
  | fImpl : formula -> formula -> formula.

  Record Assignment :=
    {
      R :> t -> bool -> Prop;
      P : forall v, exists! b, R v b
    }.

  Definition fun_to_assignment (f : t -> bool) : Assignment.
    refine (Build_Assignment (fun v b =>  f v = b) _).
    intro v.
    exists (f v).
    unfold unique; auto.
  Defined.

  Inductive eval : formula -> Assignment -> bool -> Prop :=
  | eval_var v (A : Assignment) b : A v b -> eval (fVar v) A b
  | eval_not f A b : eval f A b -> eval (fNot f) A (negb b)
  | eval_and f1 f2 A b1 b2 : eval f1  A b1 -> eval f1 A b2 -> eval (fAnd f1 f2) A (andb b1 b2)
  | eval_or f1 f2 A b1 b2 : eval f1  A b1 -> eval f1 A b2 -> eval (fOr f1 f2) A (orb b1 b2)
  | eval_impl f1 f2 A b1 b2 :
      eval f1  A b1 -> eval f1 A b2 -> eval (fImpl f1 f2) A (orb (negb b1) b2).

  Definition Satisfiable (T : Ensemble formula) : Prop :=
    exists I, forall f, In _ T f -> eval f I true.

  Definition Finite_Satisfiable (T : Ensemble formula) : Prop :=
    (forall T', Finite _ T' -> Included _ T' T -> Satisfiable T').


End Def.

