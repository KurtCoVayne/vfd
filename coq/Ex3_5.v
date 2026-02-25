Require Import List.
Require Import Lia.
Import ListNotations.

(* Alphabet *)
Inductive alpha : Type :=
| a : alpha
| b : alpha.

Lemma alpha_dec : forall (x y : alpha), {x = y} + {x <> y}.
Proof. decide equality. Qed.

(* Grammar S: S -> ε | aSb | SS *)
Inductive S : list alpha -> Prop :=
| S_eps  : S []
| S_aSb  : forall w, S w -> S ([a] ++ w ++ [b])
| S_SS   : forall w1 w2, S w1 -> S w2 -> S (w1 ++ w2).

(* Grammar T: T -> ε | TaTb *)
Inductive T : list alpha -> Prop :=
| T_eps  : T []
| T_TaTb : forall w1 w2, T w1 -> T w2 -> T (w1 ++ [a] ++ w2 ++ [b]).

(* ===== Direction 1: T w -> S w ===== *)

(* Helper: S is closed under the TaTb production *)
Lemma S_from_TaTb : forall w1 w2, S w1 -> S w2 -> S (w1 ++ [a] ++ w2 ++ [b]).
Proof.
  intros w1 w2 H1 H2.
  apply S_SS with (w1 := w1) (w2 := [a] ++ w2 ++ [b]).
  - exact H1.
  - apply S_aSb. exact H2.
Qed.

Theorem T_implies_S : forall w, T w -> S w.
Proof.
  intros w H.
  induction H as [ | w1 w2 Hw1 IH1 Hw2 IH2].
  - apply S_eps.
  - apply S_from_TaTb; assumption.
Qed.

(* ===== Direction 2: S w -> T w ===== *)

(* The key lemma: T is closed under concatenation (corresponds to S_SS) *)
Lemma T_concat : forall w1 w2, T w1 -> T w2 -> T (w1 ++ w2).
Proof.
  (* Induction on the second argument w2 *)
  intros w1 w2 H1 H2.
  generalize dependent w1.
  induction H2 as [ | v1 v2 Hv1 IH1 Hv2 IH2].
  - intros w1 H1. rewrite app_nil_r. exact H1.
  - intros w1 H1.
    (* w2 = v1 ++ [a] ++ v2 ++ [b], need T (w1 ++ v1 ++ [a] ++ v2 ++ [b]) *)
    (* By IH1: T (w1 ++ v1) *)
    (* Then T_TaTb (w1 ++ v1) v2 gives the result *)
    replace (w1 ++ v1 ++ [a] ++ v2 ++ [b])
      with ((w1 ++ v1) ++ [a] ++ v2 ++ [b])
      by (repeat rewrite app_assoc; reflexivity).
    apply T_TaTb.
    + apply IH1. exact H1.
    + exact Hv2.
Qed.

Theorem S_implies_T : forall w, S w -> T w.
Proof.
  intros w H.
  induction H as [ | w Hw IH | w1 w2 Hw1 IH1 Hw2 IH2].
  - (* S_eps *) apply T_eps.
    replace ([a] ++ w ++ [b]) with ([] ++ [a] ++ w ++ [b]) by reflexivity.
    apply T_TaTb.
    + apply T_eps.
    + exact IH.
    apply T_concat; assumption.
Qed.


Theorem S_iff_T : forall w, S w <-> T w.
Proof.
  intros w. split.
  - apply S_implies_T.
  - apply T_implies_S.
Qed.
