From HypVeri.algebra Require Import base.
From HypVeri.rules Require Import rules_base mov str.

Section instr.
  (* shorthands for writing programs *)

  Definition str_I r a := encode_instruction (Str r a).
  Definition mov_word_I ra w := encode_instruction (Mov ra (inl w)).
  Definition halt_I := encode_instruction Halt.

  Definition hvc_I := encode_instruction Hvc.
  Definition run_I := encode_hvc_func Run.
  Definition yield_I := encode_hvc_func Yield.




  Context `{gen_VMG Σ}.

  Definition program (instr: list Word) (b:Addr):=
    ([∗ list] a;w ∈ (finz.seq b (length instr));instr, (a ->a w))%I.

End instr.
