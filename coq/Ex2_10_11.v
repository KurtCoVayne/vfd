Require Import Nat.
Require Import List.
(* lia *)
Require Import Arith.
Require Import Lia.
Import ListNotations.

Inductive tree0: Type :=
| Tip  : tree0
| Node : tree0 -> tree0 -> tree0.

Fixpoint nodes (t : tree0) : nat :=
  match t with
  | Tip => 1
  | Node l r => 1 + nodes l + nodes r
  end.

Fixpoint explode (n: nat) (t: tree0) : tree0 :=
  match n with
  | O => t
  | S n' => Node (explode n' t) (explode n' t)
  end.


(* Test tree *)
Compute nodes (explode 0 Tip).
Compute nodes (explode 1 Tip).
Compute nodes (explode 2 Tip).
Compute nodes (explode 3 Tip).
Compute nodes (explode 4 Tip).
Compute nodes (explode 5 Tip).
Compute nodes (explode 6 Tip).
Compute nodes (explode 7 Tip).
Compute nodes (explode 8 Tip).

(* Two Nodes *)
Definition one_deep := Node Tip Tip.
Compute nodes (explode 0 one_deep).
Compute nodes (explode 1 one_deep).
Compute nodes (explode 2 one_deep).
Compute nodes (explode 3 one_deep).
Compute nodes (explode 4 one_deep).
Compute nodes (explode 5 one_deep).
Compute nodes (explode 6 one_deep).
Compute nodes (explode 7 one_deep).
Compute nodes (explode 8 one_deep).

Theorem explode_0 : forall t : tree0, nodes (explode 0 t) = nodes t.
Proof.
  intros t.
  simpl.
  reflexivity.
Qed.

Theorem explode_1_tip : forall t : tree0, nodes (explode 1 t) = 2 * nodes t + 1.
Proof.
  intros t.
  simpl.
  rewrite <- plus_n_O.
  lia.
Qed.

Theorem explode_S_tip : forall n : nat,
  nodes (explode (S n) Tip) = 2 * nodes (explode n Tip) + 1.
Proof.
  intros n.
  simpl.
  (* rewrite <- plus_n_O. *)
  lia.
Qed.


Lemma one_le_pow2 : forall n, 1 <= 2 ^ n.
Proof.
  induction n as [| n' IH].
  - simpl. lia.
  - rewrite Nat.pow_succ_r by lia. lia.
Qed.

(* Explode for any n of tip *)
Theorem explode_n_tip : forall n : nat,
  nodes (explode n Tip) = 2 ^ (n + 1) - 1.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - auto.
  - auto.
    rewrite explode_S_tip.
    rewrite IHn'.
    replace (S n' + 1) with (n' + 2) by lia.
    replace (n' + 2) with (S (n' + 1)) by lia.
    rewrite Nat.pow_succ_r by lia.
    pose proof (one_le_pow2 (n' + 1)).
    lia.
Qed.

Theorem explode_1 : forall t : tree0,
  nodes (explode 1 t) = 2 * nodes t + 1.
Proof.
  intros t.
  destruct t as [| l r].
  - apply explode_1_tip.
  - simpl. lia.
Qed.

Theorem explode_S : forall n : nat, forall t : tree0,
  nodes (explode (S n) t) = 2 * nodes (explode n t) + 1.
Proof.
  intros n t.
  destruct t as [| l r].
  - apply explode_S_tip.
  - simpl. lia.
Qed.

Theorem explode_n : forall n : nat, forall t : tree0,
  nodes (explode n t) = 2 ^ n * nodes t + (2 ^ n - 1).
Proof.
  intros n t.
  induction n as [| n' IHn'].
  - simpl. lia.
  - rewrite explode_S.
    rewrite IHn'.
    pose proof (one_le_pow2 n').
    rewrite Nat.pow_succ_r by lia.
    rewrite <- Nat.mul_assoc.
    remember (2 ^ n' * nodes t) as m.
    remember (2 ^ n') as p.
    lia.
Qed.

Inductive exp : Type :=
| Var : exp
| Const : nat -> exp
| Add : exp -> exp -> exp
| Mul : exp -> exp -> exp.

Fixpoint eval (e : exp) (x : nat) : nat :=
  match e with
  | Var => x
  | Const n => n
  | Add e1 e2 => eval e1 x + eval e2 x
  | Mul e1 e2 => eval e1 x * eval e2 x
  end.

Definition Poly := list nat.


Fixpoint evalp_with_order (l: Poly) (x: nat) (n: nat) : nat :=
  match l with
  | [] => 0
  | a :: xs =>
      a * (x ^ n) + evalp_with_order xs x (S n)
  end.

Definition evalp (l: Poly) (x: nat) : nat :=
  evalp_with_order l x 0.


Fixpoint poly_add (p q : Poly) : Poly :=
  match p, q with
  | [], q => q
  | p, [] => p
  | a :: p', b :: q' =>
      (a + b) :: poly_add p' q'
  end.

Fixpoint poly_scalar_mul (a : nat) (p : Poly) : Poly :=
  match p with
  | [] => []
  | b :: p' => (a * b) :: poly_scalar_mul a p'
  end.

Definition poly_shift (p : Poly) : Poly :=
  0 :: p.

Fixpoint poly_mul (p q : Poly) : Poly :=
  match p with
  | [] => []
  | a :: p' =>
      poly_add
        (poly_scalar_mul a q)
        (poly_shift (poly_mul p' q))
  end.

Fixpoint exp_to_poly (e : exp) : Poly :=
  match e with
  | Var => [0; 1]
  | Const n => [n]
  | Add e1 e2 =>
      poly_add (exp_to_poly e1) (exp_to_poly e2)
  | Mul e1 e2 =>
      poly_mul (exp_to_poly e1) (exp_to_poly e2)
  end.

Definition coeffs (e: exp) : list nat :=
  exp_to_poly e.

(* Examples *)
Compute coeffs (Add (Mul Var Var) (Mul (Const 2) Var)). (* 2x + x^2  = [0;2;1] *)
Compute evalp (coeffs (Add (Mul Var Var) (Mul (Const 2) Var))) 3. (* 2*3 + 3^2 = 6 + 9 = 15 *)
Compute eval (Add (Mul Var Var) (Mul (Const 2) Var)) 3. (* 2*3 + 3^2 = 6 + 9 = 15 *)
(* With Polynomial Multiplication *)
Definition expr1 := (Mul (Add Var (Const 1)) (Add Var (Const 2))).
Compute coeffs expr1. (* (x + 1)(x + 2) = x^2 + 3x + 2 = [2;3;1] *)
Compute evalp (coeffs expr1) 3. (* (3 + 1)(3 + 2) = 4 * 5 = 20 *)
Compute eval expr1 3. (* (3 + 1)(3 + 2) = 4 * 5 = 20 *)

Lemma evalp_of_var : forall x, evalp [0; 1] x = x.
Proof.
  intros x.
  simpl.
  unfold evalp.
  simpl.
  lia.
Qed.

Lemma evalp_of_const : forall n x, evalp [n] x = n.
Proof.
  intros n x.
  simpl.
  unfold evalp.
  simpl.
  lia.
Qed.

Lemma evalp_with_order_add : forall p q x n,
  evalp_with_order (poly_add p q) x n = 
  evalp_with_order p x n + evalp_with_order q x n.
Proof.
  intros p q x n.
  generalize dependent q.
  generalize dependent n.
  induction p as [| a p' IHp]; intros n q.
  - simpl. lia.
  - destruct q as [| b q'].
    + simpl. lia.
    + simpl. rewrite IHp. lia.
Qed.

Lemma evalp_add : forall p q x,
  evalp (poly_add p q) x = evalp p x + evalp q x.
Proof.
  intros p q x.
  unfold evalp.
  apply evalp_with_order_add.
Qed.

(* Helper lemma for scalar multiplication *)
Lemma evalp_with_order_scalar_mul : forall a p x n,
  evalp_with_order (poly_scalar_mul a p) x n = 
  a * evalp_with_order p x n.
Proof.
  intros a p x n.
  generalize dependent n.
  induction p as [| b p' IHp]; intros n.
  - simpl. lia.
  - simpl. rewrite IHp. lia.
Qed.


(* Helper lemma for shift *)
Lemma evalp_with_order_shift : forall p x n,
  evalp_with_order (poly_shift p) x n = 
  evalp_with_order p x (S n).
Proof.
  intros p x n.
  simpl.
  lia.
Qed.

Lemma evalp_with_order_succ : forall p x n,
  evalp_with_order p x (S n) = x * evalp_with_order p x n.
Proof.
  intros p x n.
  generalize dependent n.
  induction p as [| a p' IHp]; intros n.
  - simpl. lia.
  - simpl. 
    rewrite <- Nat.pow_succ_r.
    rewrite IHp.
    replace (x ^ S n) with (x * x ^ n).
    + lia.
    + simpl. reflexivity.
    + simpl. lia.
Qed.

Lemma evalp_with_order_scale : forall q x n,
  evalp_with_order q x n = x ^ n * evalp_with_order q x 0.
Proof.
  intros q x n.
  generalize dependent n.
  induction q as [| b q' IHq]; intros n.
  - simpl. lia.
  - simpl.
    rewrite IHq.
    rewrite (evalp_with_order_succ q' x 0).
    rewrite Nat.pow_succ_r by lia.
    nia.
Qed.

Lemma evalp_with_order_mul : forall p q x n,
  evalp_with_order (poly_mul p q) x n = 
  evalp_with_order p x n * evalp_with_order q x 0.
Proof.
  intros p q x n.
  generalize dependent q.
  generalize dependent n.
  induction p as [| a p' IHp]; intros n q.
  - simpl. lia.
  - simpl. 
  rewrite evalp_with_order_add.
  rewrite evalp_with_order_scalar_mul.
  rewrite evalp_with_order_shift.
  rewrite evalp_with_order_scale.
  rewrite IHp.
  rewrite evalp_with_order_succ.
  nia.
Qed.

Lemma evalp_mul : forall p q x,
  evalp (poly_mul p q) x = evalp p x * evalp q x.
Proof.
  intros p q x.
  unfold evalp.
  rewrite evalp_with_order_mul.
  reflexivity.
Qed.

Theorem eval_correct : forall e x,
  eval e x = evalp (coeffs e) x.
Proof.
  intros e x.
  induction e as [| n | e1 IHe1 e2 IHe2 | e1 IHe1 e2 IHe2].
  - simpl. rewrite evalp_of_var. reflexivity.
  - simpl. rewrite evalp_of_const. reflexivity.
  - simpl. rewrite evalp_add. rewrite <- IHe1, <- IHe2. reflexivity.
  - simpl. rewrite evalp_mul. rewrite <- IHe1, <- IHe2. reflexivity.
Qed.