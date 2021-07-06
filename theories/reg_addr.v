From HypVeri Require Import machine monad.
From stdpp Require Import  fin_maps list countable fin  vector.

Ltac solveWordSize :=
  pose proof word_size_at_least as G;
  unfold word_size_lower_bound in G;
  lia.

Ltac solveRegCount :=
  pose proof reg_count_at_least as G;
  unfold reg_count_lower_bound in G;
  lia.

Program Definition W0 : word := (@nat_to_fin 0 word_size _).
Solve Obligations with solveWordSize.

Program Definition W1 : word := (@nat_to_fin 1 word_size _).
Solve Obligations with solveWordSize.

Program Definition W2 : word := (@nat_to_fin 2 word_size _).
Solve Obligations with solveWordSize.

Program Definition R0 :reg_name := (R 0 _).
Solve Obligations with solveRegCount.

Program Definition R1 :reg_name := (R 1 _).
Solve Obligations with solveRegCount.

Program Definition R2 :reg_name := (R 2 _).
Solve Obligations with solveRegCount.


Definition incr_word (n : word) (p : nat) : option word :=
  match (nat_lt_dec (n + p) word_size) with
  | left l => Some (@nat_to_fin (n + p) _ l)
  | _ => None
  end.

Infix "+w" := incr_word (at level 70, no associativity).

Definition incr_word_unsafe (n : word) (p : nat) :  word :=
  match (n +w p) with
    | Some w => w
    | None => W0
  end.

Infix "^+w" := incr_word_unsafe (at level 70, no associativity).


(* Program Definition page_offset_to_addr (p :pid) (offset:fin page_size) : addr := *)
(*   ((mm_translation_inv p)  !!! offset). *)

(* Program Definition word_add (w:word) (n:nat):word:= *)
(*   (@nat_to_fin (((fin_to_nat w)+n) mod word_size) _ _). *)
(* Next Obligation. *)
(* Proof. *)
(*   intros. *)
(*   apply mod_bound_pos. *)
(*   lia. *)
(*   pose proof word_size_at_least. *)
(*   lia. *)
(* Defined. *)
