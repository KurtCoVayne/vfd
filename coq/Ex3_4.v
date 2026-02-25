Require Import Nat.
Require Import Arith.
Require Import Lia.

Inductive star {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
| refl_star : forall x : A, star R x x
| step_star : forall x y z : A, R x y -> star R y z -> star R x z.

Inductive iter {A : Type} (R : A -> A -> Prop) : nat -> A -> A -> Prop :=
| iter_refl : forall x : A, iter R 0 x x
| iter_step : forall (n : nat) (x y z : A),
    R x y -> iter R n y z -> iter R (S n) x z.

Theorem star_implies_iter {A : Type} (R : A -> A -> Prop) :
  forall x y, star R x y -> exists n, iter R n x y.
Proof.
  intros x y H.
  induction H as [x | x w y Hxw Hwy IH].
  - exists 0. apply iter_refl.
  - destruct IH as [n Hn].
    exists (S n). eapply iter_step. exact Hxw. exact Hn.
Qed.

Theorem iter_implies_star {A : Type} (R : A -> A -> Prop) :
  forall n x y, iter R n x y -> star R x y.
Proof.
  intros n x y H.
  induction H as [x | n x w y Hxw Hwy IH].
  - apply refl_star.
  - eapply step_star. exact Hxw. exact IH.
Qed.
