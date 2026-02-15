Require Import Nat.

Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Fixpoint snoc (l : natlist) (n : nat) : natlist :=
  match l with
  | nil => cons n nil
  | cons h t => cons h (snoc t n)
  end.

Fixpoint rev (l : natlist) : natlist :=
  match l with
  | nil => nil
  | cons h t => snoc (rev t) h
  end.

Lemma rev_snoc : forall l n,
  rev (snoc l n) = cons n (rev l).
Proof.
  intros l n.
  induction l as [| h t IH].
  - reflexivity.
  - simpl.
    rewrite IH.
    reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  induction l as [| h t IH].
  - reflexivity.
  - simpl.
    rewrite (rev_snoc (rev t) h).
    rewrite IH.
    reflexivity.
Qed.
