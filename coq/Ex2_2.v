
Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

Print nat_ind.

Fixpoint add (n m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (add n' m)
  end.

Fixpoint double (n : nat) : nat :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma plus_n_Sm : forall n m : nat,
  S (add n m) = add n (S m).
Proof.
  induction n as [| n' IH].
  - reflexivity.
  - intros m.
    simpl.
    rewrite IH.
    reflexivity.
Qed.


Theorem double_eq_add : forall n : nat, double n = add n n.
Proof.
  induction n as [| n' IH].
    reflexivity.
    simpl. rewrite IH. rewrite plus_n_Sm. reflexivity.
Qed.