From stdpp Require Import base.
From HypVeri Require Import lang.
From machine_utils Require Export solve_pure.

(* Extend the [solve_pure] tactic from [machine_utils] with additional hints
   for solving goals specific to our machine.

   See the comments in [machine_utils/theories/solve_pure.v] on how to
   extend [solve_pure] with more hints.
*)

(** decode_instruction w = Some ? *)

Class DecodeInstr (w: Word) (i: instruction) :=
  MkDecodeInstr: decode_instruction w = Some i.
#[global] Hint Mode DecodeInstr + - : typeclass_instances.

Instance DecodeInstr_encode (i: instruction) :
  DecodeInstr (encode_instruction i) i.
Proof. apply decode_encode_instruction. Qed.

(* Proxy lemma for DecodeInstr *)
Lemma DecodeInstr_prove w i :
  DecodeInstr w i →
  decode_instruction w = Some i.
Proof.
  intros ->. reflexivity.
Qed.
#[export] Hint Resolve DecodeInstr_prove : solve_pure.
