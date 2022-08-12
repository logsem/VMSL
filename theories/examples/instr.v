From HypVeri.algebra Require Import base.
From HypVeri.rules Require Import rules_base.

Section instr.
  (* shorthands for writing programs *)

  Context `{hypparams: HypervisorParameters}.

  Definition mov_word_I ra w := encode_instruction (Mov ra (inl w)).
  Definition mov_reg_I ra rb := encode_instruction (Mov ra (inr rb)).
  Definition add_I ra rb := encode_instruction (Add ra rb).
  Definition halt_I := encode_instruction Halt.
  Definition str_I ra rb := encode_instruction (Str ra rb).
  Definition ldr_I ra rb := encode_instruction (Ldr ra rb).
  Definition br_I r := encode_instruction (Br r).
  Definition cmp_word_I ra w := encode_instruction (Cmp ra (inl w)).
  Definition bne_I r := encode_instruction (Bne r).

  Definition hvc_I := encode_instruction Hvc.
  Definition run_I := encode_hvc_func Run.
  Definition yield_I := encode_hvc_func Yield.
  Definition mem_lend_I := encode_hvc_func Lend.
  Definition mem_share_I := encode_hvc_func Share.
  Definition mem_reclaim_I := encode_hvc_func Reclaim.
  Definition mem_retrieve_I := encode_hvc_func Retrieve.
  Definition mem_relinquish_I := encode_hvc_func Relinquish.
  Definition msg_send_I := encode_hvc_func Send.
  Definition msg_poll_I := encode_hvc_func Poll.

  Definition encode_instructions (l: list instruction) :=
    map encode_instruction l.

  Lemma encode_instructions_length l :
   length (encode_instructions l) = length l.
  Proof. rewrite map_length //. Qed.

  Context `{gen_VMG Σ}.

  Definition program (instr: list Word) (b:Addr):=
    ([∗ list] a;w ∈ (finz.seq b (length instr));instr, (a ->a w))%I.

End instr.
