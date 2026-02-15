Require Import Nat.
Require Import PeanoNat.

Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Fixpoint length (l : natlist) : nat :=
  match l with
  | nil => O
  | cons _ t => S (length t)
  end.

Fixpoint count (n : nat) (l : natlist) : nat :=
  match l with
  | nil => O
  | cons h t => if Nat.eqb n h then S (count n t) else count n t
  end.
  
Print Nat.le_0_l.
Print le_n_S.
Print le_S. 

Theorem count_le_length : forall (n : nat) (l : natlist),
  count n l <= length l.
Proof.
  induction l as [| h t IH].
    simpl. apply Nat.le_0_l.
    simpl. destruct (Nat.eqb n h) eqn:E.
      apply le_n_S. apply IH.
      apply le_S. apply IH.
Qed.

