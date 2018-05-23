Require Import aula3 aula4 aula5 aula6 aula7.

(** Complete the definitions of [nonzeros], [oddmembers] and
    [countoddmembers] below. Have a look at the tests to understand
    what these functions should do. *)

(** **** Exercise: 2 star  *)
Fixpoint nonzeros (l:natlist) : natlist :=
match l with
 | nil => nil 
 | h :: t => match h with
             | 0 => nonzeros t
             | S n => h :: nonzeros t
             end
end.

(** **** Exercise: 1 star  *)
Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof.
simpl.
reflexivity.
Qed.
(** **** Exercise: 2 star  *)
Fixpoint oddmembers (l:natlist) : natlist :=
match l with
 | nil => nil
 | h :: t => match oddb h with
            |false => oddmembers t
            |true => h :: oddmembers t
            end
end.
            

(** **** Exercise: 1 star  *)
Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof.
simpl.
reflexivity.
Qed.

(** **** Exercise: 2 star  *)
Definition countoddmembers (l:natlist) : nat := (length(oddmembers l)).


(** **** Exercise: 1 star  *)
Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
Proof.
unfold countoddmembers.
simpl.
reflexivity.
Qed.

(** **** Exercise: 1 star  *)
Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
Proof.
reflexivity.
Qed.
(** **** Exercise: 1 star  *)
Example test_countoddmembers3:
  countoddmembers nil = 0.
Proof.
reflexivity.
Qed.

(** **** Exercise: 3 stars, advanced (alternate)  *)
(** Complete the definition of [alternate], which "zips up" two lists
    into one, alternating between elements taken from the first list
    and elements from the second.  See the tests below for more
    specific examples.

    Note: one natural and elegant way of writing [alternate] will fail
    to satisfy Coq's requirement that all [Fixpoint] definitions be
    "obviously terminating."  If you find yourself in this rut, look
    for a slightly more verbose solution that considers elements of
    both lists at the same time.  (One possible solution requires
    defining a new kind of pairs, but this is not the only way.)  *)

Fixpoint alternate (l1 l2 : natlist) : natlist :=
match l1 with
| nil => l2
| h :: t => match l2 with
           | nil => l1
           | h0 :: t0 => h :: h0 :: alternate t t0
           end
end.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof.
simpl.
reflexivity.
Qed.

Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof.
simpl.
reflexivity.
Qed.

Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
Proof.
simpl.
reflexivity.
Qed.

Example test_alternate4:
  alternate [] [20;30] = [20;30].
Proof.
simpl.
reflexivity.
Qed.

