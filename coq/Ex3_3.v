Require Import Nat.
Require Import List.
Require Import Arith.
Require Import Lia.
Import ListNotations.

Inductive star {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
| refl_star : forall x : A, star R x x
| step_star : forall x y z : A, R x y -> star R y z -> star R x z.

Inductive star' {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
| refl_star_prime : forall x : A, star' R x x
| step_star_prime : forall x y z : A, star' R x y -> R y z -> star' R x z.

(* Helper: star is closed under appending a step on the right *)
Lemma star_trans_step {A : Type} (R : A -> A -> Prop) :
  forall x y z, star R x y -> R y z -> star R x z.
Proof.
  intros x y z Hstar Hstep.
  induction Hstar as [x | x w y Hxw Hwy IH].
  - eapply step_star. exact Hstep. apply refl_star.
  - eapply step_star. exact Hxw. apply IH. exact Hstep.
Qed.

(* Helper: star' is closed under prepending a step on the left *)
Lemma star'_step_trans {A : Type} (R : A -> A -> Prop) :
  forall x y z, R x y -> star' R y z -> star' R x z.
Proof.
  intros x y z Hstep Hstar'.
  induction Hstar' as [w | w u v Hwu IH Huv].
  - eapply step_star_prime. apply refl_star_prime. exact Hstep.
  - eapply step_star_prime.
    + apply IH. exact Hstep.
    + exact Huv.
Qed.

(* star' R x y -> star R x y *)
Theorem star'_implies_star {A : Type} (R : A -> A -> Prop) :
  forall x y, star' R x y -> star R x y.
Proof.
  intros x y H.
  induction H as [x | x w y Hxw IH Hwy].
  - apply refl_star.
  - eapply star_trans_step. exact IH. exact Hwy.
Qed.

(* star R x y -> star' R x y *)
Theorem star_implies_star' {A : Type} (R : A -> A -> Prop) :
  forall x y, star R x y -> star' R x y.
Proof.
  intros x y H.
  induction H as [x | x w y Hxw Hwy IH].
  - apply refl_star_prime.
  - eapply star'_step_trans. exact Hxw. exact IH.
Qed.

(* Equivalence *)
Theorem star_iff_star' {A : Type} (R : A -> A -> Prop) :
  forall x y, star R x y <-> star' R x y.
Proof.
  intros x y. split.
  - apply star_implies_star'.
  - apply star'_implies_star.
Qed.
