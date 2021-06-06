Require Import PeanoNat.

Theorem l_one : forall m n : nat,
    m <> n -> S m <> S n.
Proof.
  auto.
Qed.

Theorem l_two : forall n : nat,
    S n <> n.
Proof.
  intros n.
  induction n as [| n' Hn'].
  - unfold not. discriminate.
  - apply (l_one (S n') n'). assumption.
Qed.

Theorem l_three : forall x : nat,
    x <> 1 -> exists u : nat, x <> S u.
Proof.
  intros x H.
  induction x as [| x' Hx'].
  - exists 0. unfold not. discriminate.
  - exists 0. apply H.
Qed.

Theorem l_four_a : forall x : nat,
    x + 1 = S x.
Proof.
  intros. induction x as [| x' Hx'].
  - compute. reflexivity.
  - simpl. rewrite Hx'. reflexivity.
Qed.                  

Theorem l_four_b : forall x y : nat,
    x + (S y) = S (x + y).
Proof.
  intros. induction x as [| x' Hx'].
  - simpl. reflexivity.
  - simpl. rewrite Hx'. reflexivity.
Qed.

Theorem l_five : forall x y z : nat,
    (x + y) + z = x + (y + z).
Proof.
  intros. induction x as [| x' Hx'].
  - simpl. reflexivity.
  - simpl. rewrite Hx'. reflexivity.
Qed.  

Theorem plus_x_O : forall x : nat,
    x = x + 0.
Proof.
  intros. induction x as [| x' Hx'].
  - reflexivity.
  - simpl. rewrite <- Hx'. reflexivity.
Qed.

Theorem plus_n_Sm : forall x y : nat,
    S (x + y) = x + S y.
Proof.
  intros. induction x as [| x' Hx'].
  - simpl. reflexivity.
  - simpl. rewrite Hx'. reflexivity.
Qed.

Theorem l_six : forall x y : nat,
    x + y = y + x.
Proof.
  intros. induction x as [| x' Hx'].
  - simpl. rewrite <- plus_x_O. reflexivity.
  - simpl. simpl. rewrite Hx'. rewrite plus_n_Sm. reflexivity.
Qed.

