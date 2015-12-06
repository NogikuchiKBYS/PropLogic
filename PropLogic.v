Require Import Classical Logic.
Require Import Ensembles.
Require Import Finite_sets.
Require Import Finite_sets_facts.
Require Import Powerset_facts.
Require Import Bool.
Require Import SetoidClass.

Set Implicit Arguments.

Lemma Included_trans : forall U A B C, Included U A B -> Included U B C -> Included U A C.
Proof.
  unfold Included.
  auto.
Qed.

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
      Pexuniq : forall v, exists! b, R v b
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

Lemma Finite_Satis_FiniteSatis : forall t (T : Ensemble (formula t)),
                             Finite _ T -> Satisfiable T -> Finite_Satisfiable T.
Proof.
  intros t T Hf Hs.
  destruct Hs as [I HI].
  intros T' _ Hincl.
  exists I.
  intro f.
  specialize (HI f).
  intro Hin.
  apply HI.
  apply Hincl.
  apply Hin.
Qed.

Lemma eval_exclusive : forall t (f : formula t) (I : Assignment t) b1 b2,
                         eval f I b1 -> eval f I b2 -> b1 = b2.
Proof.
  intros t f I b1 b2 He1.
  generalize b2 as b; clear b2.
  induction He1; intros b' H'.
  {
    inversion H'; subst.
    set (Pexuniq A) as exuniq.
    specialize (exuniq v).
    destruct exuniq as [b0 Hb0].
    destruct Hb0 as [Hb0 Huniq].
    apply Huniq in H.
    apply Huniq in H1; subst.
    assumption.
  } {
    inversion H'; subst.
    rewrite (IHHe1 b0); auto.
  } {
    inversion H'; subst.
    rewrite (IHHe1_1 b0); auto.
    rewrite (IHHe1_2 b3); auto.
  } {
    inversion H'; subst.
    rewrite (IHHe1_1 b0); auto.
    rewrite (IHHe1_2 b3); auto.
  } {
    inversion H'; subst.
    rewrite (IHHe1_1 b0); auto.
    rewrite (IHHe1_2 b3); auto.
  }
Qed.

Lemma eval_exclusive' : forall t (f : formula t) I, ~(eval f I true /\ eval f I false).
Proof.
  intros.
  intro H.
  destruct H as [Ht Hf].
  apply diff_true_false.
  rewrite (eval_exclusive Ht Hf).
  reflexivity.
Qed.

Lemma eval_exist : forall t (f : formula t) (I : Assignment t), eval f I true \/ eval f I false.
Proof.
  intros t f I.
  induction f.
  {
    destruct I as [R P].
    set (P t0) as H.
    destruct H as [b H].
    case_eq b; intro; subst; [left | right]; constructor; apply H.
  } {
    destruct IHf; [right | left]; rewrite <- negb_involutive; constructor; auto.
  } {
    destruct IHf1; destruct IHf2; [left | right | right | right];
    [
      replace true with (true && true) |
      replace false with (true && false) |
      replace false with (false && true) |
      replace false with (false && false)
    ]; constructor; auto.
   } {
    destruct IHf1; destruct IHf2; [left | left | left | right];
    [
      replace true with (true || true) |
      replace true with (true || false) |
      replace true with (false || true) |
      replace false with (false || false)
    ]; constructor; auto.
  } {
    destruct IHf1; destruct IHf2; [left | right | left | left];
    [
      replace true with (negb true || true) |
      replace false with (negb true || false) |
      replace true with (negb  false || true) |
      replace true with (negb false || false)
    ]; constructor; auto.
  }
Qed.

Lemma Add_intro : forall U (A : Ensemble U) (x y : U), In U A y \/ x = y -> In U (Add U A x) y.
Proof.
  intros.
  destruct H.
  {
    apply Add_intro1.
    assumption.
  } {
    subst.
    apply Add_intro2.
  }
Qed.

Lemma Subtract_in_iff : forall U A x y, In U (Subtract U A x) y <-> In U A y /\ x <> y.
Proof.
  intros.
  split; intro H.
  {
    apply Subtract_inv in H.
    assumption.
  } {
    destruct H as [Hin Hne].
    constructor; auto.
    intro Hs.
    inversion Hs.
    congruence.
  }
Qed.

