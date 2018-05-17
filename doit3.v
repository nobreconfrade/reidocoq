Require Import aula3 aula4 aula5.

(** **** Exercise: 2 stars, each one, recommended (basic_induction)  *)
(** Prove the following using induction. You might need previously
    proven results. *)

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
intros n.
induction n.
 -simpl. reflexivity.
 -simpl. assumption.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
intros n m.
induction n.
 - simpl. reflexivity.
 - simpl. rewrite IHn. reflexivity.
Qed. 

Theorem plus_comm : forall n m : nat, n + m = m + n.
Proof.
intros n m.
induction n.
 - induction m.
  + reflexivity.
  + simpl. rewrite <- IHm. simpl. reflexivity.
 - simpl. rewrite IHn. rewrite plus_n_Sm. reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
intros n m p.
induction n.
 - simpl. reflexivity.
 - simpl. rewrite IHn. reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

(** Use induction to prove this simple fact about [double]: *)

Lemma double_plus : forall n, double n = n + n .
Proof.
intros n.
induction n.
 - simpl. reflexivity.
 - simpl. rewrite IHn. rewrite plus_n_Sm. reflexivity.
Qed.
(** **** Exercise: 2 stars, optional (evenb_S)  *)
(** One inconvenient aspect of our definition of [evenb n] is the
    recursive call on [n - 2]. This makes proofs about [evenb n]
    harder when done by induction on [n], since we may need an
    induction hypothesis about [n - 2]. The following lemma gives an
    alternative characterization of [evenb (S n)] that works better
    with induction: *)

Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
intros n.
induction n.
 - simpl. reflexivity.
 - rewrite IHn. simpl. rewrite negb_involutive. reflexivity.
Qed.