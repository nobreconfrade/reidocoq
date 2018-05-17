(*** Exercício de Programação Funcional**)

(** Defina um programa que compute o antecessor do antecessor de um dado número n **)

(** 1 star **)

Definition minustwo (n : nat) : nat :=
  match n with
  | 0 => 0
  | 1 => 0
  | S(S(n')) => n'
 end.

(** Teste a função minustwo **)
(** 1 star **)

Example test_minustwo_1 : minustwo 4 = 2.
  Proof.
  simpl.
  reflexivity.
  Qed.

(** 1 star **)
Example test_minustwo_2 : minustwo 1 = 0.
  Proof.
  simpl.
  reflexivity.
  Qed.

(** 1 star **)
Example test_minustwo_3 : minustwo 0 = 0.
  Proof.
  simpl.
  reflexivity.
  Qed.

(** Defina uma função que some 2 **)
(** 1 star **)

Definition plustwo (n : nat) : nat := S(S(n)).

(** Teste a função plustwo **)
(** 1 star **)

Example test_plustwo_1 : plustwo 4 = 6.
  Proof.
  unfold plustwo.
  reflexivity.

(** 1 star **)
Example test_plustwo_2 : plustwo 0 = 2.
  Proof.
  unfold plustwo.
  reflexivity.

Inductive fruta : Type :=
  | morango : fruta
  | uva : fruta
  | laranja : fruta.

Inductive salada : Type :=
  | salada1 : fruta -> salada
  | salada2 : fruta -> fruta -> salada
  | salada3 : fruta -> fruta -> fruta -> salada.

(** Defina o tipo fruta (morango, uva e laranja) **)
(** 1 star **)

(** Defina o tipo salada, onde uma salada é formada pela combinação de até três frutas **)
(** 1 star **)
