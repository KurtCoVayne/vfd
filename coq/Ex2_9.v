Import Nat.
Require Import Arith.
Require Import Lia.

Print add.

Fixpoint itadd (n m : nat) : nat :=
  match m with
  | O => n
  | S m' => itadd (S n) m'
  end.

Theorem itadd_correct : forall n m, itadd n m = n + m.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [| m' IHm]; intros n.
    - simpl. rewrite Nat.add_0_r. reflexivity.
    - simpl. rewrite IHm. rewrite Nat.add_succ_r. reflexivity.
Qed.