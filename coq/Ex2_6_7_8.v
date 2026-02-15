Require Import Nat.
Require Import List.
(* lia *)
Require Import Arith.
Require Import Lia.
Import ListNotations.

Inductive tree (A : Type) : Type :=
| Tip  : tree A
| Node : tree A -> A -> tree A -> tree A.

Arguments Tip {A}.
Arguments Node {A}.

Fixpoint preorder {A : Type} (t : tree A) : list A :=
  match t with
  | Tip => []
  | Node l x r => x :: preorder l ++ preorder r
  end.

Fixpoint inorder {A : Type} (t : tree A) : list A :=
  match t with
  | Tip => []
  | Node l x r => inorder l ++ x :: inorder r
  end.

Fixpoint postorder {A : Type} (t : tree A) : list A :=
  match t with
  | Tip => []
  | Node l x r => postorder l ++ postorder r ++ [x]
  end.


Definition example_tree : tree nat :=
  Node
    (Node
      (Node Tip 1 Tip)
      3
      (Node Tip 4 Tip))
    5
    (Node
      Tip
      8
      (Node Tip 9 Tip)).

Compute preorder example_tree.

Fixpoint sum_tree (t : tree nat) : nat :=
  match t with
  | Tip => 0
  | Node l x r => x + sum_tree l + sum_tree r
  end.

Compute sum_tree example_tree.

Definition sum_list (l : list nat) : nat :=
  fold_right plus 0 l.

Lemma sum_list_app :
  forall l1 l2 : list nat,
    sum_list (l1 ++ l2) = sum_list l1 + sum_list l2.
Proof.
    intros l1 l2.
    induction l1 as [| h t IH].
    - simpl. lia.
    - simpl. rewrite IH. lia.
Qed.

Compute sum_list (preorder example_tree).

Theorem sum_tree_equiv :
  forall t : tree nat,
    sum_tree t = sum_list (preorder t).
Proof.
  intros t.
  induction t as [| l IHl x r IHr].
  - (* case: Tip *)
    reflexivity.
  - (* case: Node l x r *)
    simpl.
    rewrite IHl.
    rewrite IHr.
    rewrite sum_list_app.
    lia.
Qed.

Fixpoint mirror {A : Type} (t : tree A) : tree A :=
  match t with
  | Tip => Tip
  | Node l x r => Node (mirror r) x (mirror l)
  end.

Theorem mirror_of_preorder_is_rev_postorder :
  forall (A : Type) (t : tree A),
    preorder (mirror t) = rev (postorder t).
Proof.
  intros A t.
  induction t as [| l IHl x r IHr].
    -
      reflexivity.
    -
      simpl.
      rewrite IHl.
      rewrite IHr.
      simpl.
      rewrite rev_app_distr.
      rewrite rev_app_distr.
      simpl.
      reflexivity.
Qed.

Fixpoint intersperse {A : Type} (sep : A) (l : list A) : list A :=
  match l with
  | [] => []
  | [x] => [x]
  | x :: xs => x :: sep :: intersperse sep xs
  end.

Theorem intersperse_of_a_funct_equiv
    : forall (A B : Type) (f : A -> B) (a : A) (l : list A),
        map f (intersperse a l) = intersperse (f a) (map f l).
Proof.
    intros A B f a l.
    induction l as [| h t IH].
    -
      reflexivity.
    -
      destruct t as [| h' t'].
      +
        reflexivity.
        +
        (* rewrite map *)
        simpl.
        inversion IH.
        simpl.
        reflexivity.
Qed.