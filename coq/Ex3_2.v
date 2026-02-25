Require Import Nat.
Require Import List.
Require Import Arith.
Require Import Lia.
Import ListNotations.


Inductive Palindrome (A : Type) : list A -> Prop :=
| Palindrome_nil : Palindrome A []
| Palindrome_single : forall x : A, Palindrome A [x]
| Palindrome_step : forall (x : A) (xs : list A), Palindrome A xs -> Palindrome A (x :: xs ++ [x]).

Print rev_app_distr.

Theorem palindrome_rev : forall (A : Type) (xs : list A), Palindrome A xs -> rev xs = xs.
Proof.
  intros A xs H.
  induction H.
    simpl. reflexivity.
    simpl. reflexivity.
    simpl. rewrite rev_app_distr. rewrite IHPalindrome. reflexivity.
Qed.