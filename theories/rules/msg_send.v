From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base stdpp_extra.
From HypVeri.algebra Require Import base reg mem pagetable mailbox.
From HypVeri.lang Require Import lang_extra mem_extra reg_extra current_extra.

Section msg_send.
  Context `{hypparams: HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.

Lemma hvc_send_primary {E wi r0 w sacc p_tx mem_tx q p_rx mem_rx l} ai j :
  tpa ai ≠ p_tx ->
  tpa ai ∈ sacc ->
  decode_instruction wi = Some(Hvc) ->
  decode_hvc_func r0 = Some(Send) ->
  decode_vmid w = Some j ->
  j ≠ V0 ->
  ((finz.to_z l) < page_size)%Z ->
  {SS{{ ▷(PC @@ V0 ->r ai) ∗
        ▷ ai ->a wi ∗
        ▷ V0 -@{q}A> sacc ∗
        ▷ (R0 @@ V0 ->r r0) ∗
        ▷ (R1 @@ V0 ->r w) ∗
        ▷ (R2 @@ V0 ->r l) ∗
        ▷ TX@ V0 := p_tx ∗
        ▷ memory_page p_tx mem_tx ∗
        ▷ RX@ j := p_rx ∗ ▷ RX_state@ j := None∗
        ▷ memory_page p_rx mem_rx}}}
   ExecI @ V0 ; E {{{ RET (false, ExecI) ;
                  PC @@ V0 ->r (ai ^+ 1)%f ∗ ai ->a wi
                  ∗ V0 -@{q}A> sacc
                  ∗ R0 @@ V0 ->r r0
                  ∗ R1 @@ V0 ->r w
                  ∗ R2 @@ V0 ->r l
                  ∗ TX@ V0 := p_tx
                  ∗ RX@ j := p_rx ∗ RX_state@ j :=Some(l, V0)
                  ∗ memory_page p_tx mem_tx
                  ∗ (∃ des, ⌜(Z.to_nat (finz.to_z l)) = length des ⌝ ∗ ⌜(list_to_map (zip (finz.seq p_rx (length des)) des))⊆ mem_tx⌝
                                          ∗ memory_page p_rx ((list_to_map (zip (finz.seq p_rx (length des)) des))∪ mem_rx)) }}}.
  Proof.
  Admitted.

  Lemma hvc_send_secondary {E i wi r0 w sacc p_tx mem_tx q p_rx mem_rx l r0_ r1_ r2_ P R'} ai j Q P' R:
    tpa ai ≠ p_tx ->
    tpa ai ∈ sacc ->
    decode_instruction wi = Some(Hvc) ->
    decode_hvc_func r0 = Some(Send) ->
    decode_vmid w = Some j ->
    ((finz.to_z l) < page_size)%Z ->
    i ≠ V0 ->
    let T' := (PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi
                        ∗ i -@{q}A> sacc
                        ∗ R0 @@ i ->r r0 ∗ R1 @@ i ->r w ∗ R2 @@ i ->r l
                        ∗ R0 @@ V0 ->r (encode_hvc_func Send) ∗ R1 @@ V0 ->r w ∗ R2 @@ V0 ->r l
                        ∗ TX@ i := p_tx ∗ RX@ j := p_rx ∗ RX_state@j := Some(l, i)
                        ∗ memory_page p_tx mem_tx
                        ∗ (∃ des, ⌜(Z.to_nat (finz.to_z l)) = length des ⌝ ∗ ⌜(list_to_map (zip (finz.seq p_rx (length des)) des))⊆ mem_tx⌝
                                          ∗ memory_page p_rx ((list_to_map (zip (finz.seq p_rx (length des)) des))∪ mem_rx)))%I in
    {SS{{ ▷ (VMProp V0 Q (1/2)%Qp) ∗
          ▷ (VMProp i P 1%Qp) ∗
          ▷ (PC @@ i ->r ai) ∗ ▷ ai ->a wi ∗
          ▷ i -@{q}A> sacc ∗
          ▷ (R0 @@ i ->r r0) ∗ ▷ (R1 @@ i ->r w) ∗ ▷ (R2 @@ i ->r l) ∗
          ▷ (R0 @@ V0 ->r r0_) ∗ ▷ (R1 @@ V0 ->r r1_) ∗ ▷ (R2 @@ V0 ->r r2_) ∗
          ▷ TX@ i := p_tx ∗
          ▷ memory_page p_tx mem_tx ∗
          ▷ RX@ j := p_rx ∗ ▷ RX_state@ j := None ∗
          ▷ memory_page p_rx mem_rx ∗
          ▷ (T' ∗ R ∗ VMProp i P' (1/2)%Qp -∗ (Q ∗ R')) ∗
          ▷ R
    }}}
      ExecI @ i ; E {{{ RET (true, ExecI) ; R' ∗ VMProp i P' 1%Qp}}}.
  Proof.
  Admitted.
  (* can a VM send msg to itself?? no, TODO: fix opsem *)

  (*TODO: error cases*)

End msg_send.
