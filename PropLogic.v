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
  | eval_and f1 f2 A b1 b2 : eval f1 A b1 -> eval f2 A b2 -> eval (fAnd f1 f2) A (andb b1 b2)
  | eval_or f1 f2 A b1 b2 : eval f1 A b1 -> eval f2 A b2 -> eval (fOr f1 f2) A (orb b1 b2)
  | eval_impl f1 f2 A b1 b2 :
      eval f1 A b1 -> eval f2 A b2 -> eval (fImpl f1 f2) A (orb (negb b1) b2).

  Definition Satisfiable (T : Ensemble formula) : Prop :=
    exists I, forall f, In _ T f -> eval f I true.

  Definition Finite_Satisfiable (T : Ensemble formula) : Prop :=
    (forall T', Finite _ T' -> Included _ T' T -> Satisfiable T').


End Def.

Lemma eval_exclusive : forall t (f : formula t) (I : Assignment t), ~(eval t f I true /\ eval t f I false).
Proof.
  intros t f I.
  induction f.
  {
    intro H.
    destruct H as [Ht Hf].
    destruct I as [R P].
    inversion Ht; subst.
    inversion Hf; subst.
    set (P t0) as H.
    destruct H as [x H].
    unfold unique in H.
    destruct H as [HRx Heq].
    apply Heq in H0.
    apply Heq in H1.
    congruence.
  } {
    intro H; apply IHf.
    destruct H as [Ht Hf].
    inversion Ht; subst; inversion Hf; subst.
    rewrite H0, H1.
    apply negb_true_iff in H0.
    apply negb_false_iff in H1.
    subst.
    auto.
  } {
    intro H.
    destruct H as [Ht Hf].
    inversion Ht; subst.
    inversion Hf; subst.
    apply andb_true_iff in H1.
    destruct H1; subst.
    apply andb_false_iff in H2.
    destruct H2; subst; auto.
  } {
    intro H.
    destruct H as [Ht Hf].
    inversion Ht; subst.
    inversion Hf; subst.
    apply orb_false_iff in H2.
    destruct H2; subst; auto.
    apply orb_true_iff in H1.
    destruct H1; subst; auto.
  } {
    intro H.
    destruct H as [Ht Hf].
    inversion Ht; subst.
    inversion Hf; subst.
    apply orb_false_iff in H2.
    rewrite negb_false_iff in H2.
    destruct H2; subst.
    apply orb_true_iff in H1.
    auto.
  }
Qed.

