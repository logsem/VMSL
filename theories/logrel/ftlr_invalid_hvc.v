From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.algebra Require Import base pagetable mem trans.
From HypVeri.rules Require Import rules_base.
From HypVeri.logrel Require Import logrel logrel_extra.
From HypVeri Require Import proofmode.
Import uPred.

Section ftlr_invalid_hvc.
  Context `{hypconst:HypervisorConstants}.
  Context `{hypparams:!HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.


Lemma ftlr_invalid_hvc {i trans' mem_acc_tx ai regs ps_acc p_tx p_rx ps_na instr r0} trans rx_state:
  base_extra.is_total_gmap regs ->
  {[p_tx; p_rx]} ⊆ ps_acc ->
  ps_na ## ps_acc ∪ pages_in_trans (trans_memory_in_trans i trans) ->
  p_rx ∉ ps_acc ∖ {[p_rx; p_tx]} ∪ pages_in_trans (trans_memory_in_trans i trans) ->
  p_tx ∉ ps_acc ∖ {[p_rx; p_tx]} ∪ pages_in_trans (trans_memory_in_trans i trans) ->
  regs !! PC = Some ai ->
  tpa ai ∈ ps_acc ->
  tpa ai ≠ p_tx ->
  dom (gset Addr) mem_acc_tx = set_of_addr (ps_acc ∖ {[p_tx]}) ->
  tpa ai ∈ ps_acc ∖ {[p_tx]} ->
  mem_acc_tx !! ai = Some instr ->
  decode_instruction instr = Some Hvc ->
  regs !! R0 = Some r0 ->
  decode_hvc_func r0 = None ->
  ⊢
  ▷ (∀ (a : gmap reg_name Addr) (a0 : gset PID) (a1 : gmap Addr transaction) (a2 : option (Addr * VMID)),
          ⌜base_extra.is_total_gmap a⌝
            → ⌜{[p_tx; p_rx]} ⊆ a0⌝
              → ⌜ps_na ## a0 ∪ pages_in_trans (trans_memory_in_trans i a1)⌝
                → ⌜p_rx ∉ a0 ∖ {[p_rx; p_tx]} ∪ pages_in_trans (trans_memory_in_trans i a1)⌝
                  → ⌜p_tx ∉ a0 ∖ {[p_rx; p_tx]} ∪ pages_in_trans (trans_memory_in_trans i a1)⌝
                    → ([∗ map] r↦w ∈ a, r @@ i ->r w) -∗
                      TX@i:=p_tx -∗
                      p_tx -@O> - ∗ p_tx -@E> true -∗
                      i -@{1 / 2}A> a0 -∗
                      i -@{1 / 2}A> a0 -∗
                      LB@ i := [ps_na] -∗
                      transaction_hpool_global_transferred a1 -∗
                      transaction_pagetable_entries_transferred i a1 -∗
                      retrieval_entries_transferred i a1 -∗
                      R0 @@ V0 ->r encode_hvc_func Run -∗
                      R1 @@ V0 ->r encode_vmid i -∗
                      (∃ r2 : Addr, R2 @@ V0 ->r r2) -∗
                      RX_state@i:= a2 -∗
                      mailbox.rx_page i p_rx -∗
                      rx_pages (list_to_set list_of_vmids ∖ {[i]}) -∗
                      ▷ VMProp V0 (vmprop_zero i p_rx) (1 / 2) -∗
                      VMProp i (vmprop_unknown i p_tx p_rx trans') 1 -∗
                      transaction_pagetable_entries_owned i a1 -∗
                      pagetable_entries_excl_owned i (a0 ∖ {[p_rx; p_tx]} ∖ pages_in_trans a1) -∗
                      retrieval_entries_owned i a1 -∗
                      (∃ mem : lang.mem, memory_pages (a0 ∪ pages_in_trans (trans_memory_in_trans i a1)) mem) -∗
                      WP ExecI @ i {{ _, True }}) -∗
   ([∗ map] r↦w ∈ regs, r @@ i ->r w) -∗
   TX@i:=p_tx -∗
   p_tx -@O> - ∗ p_tx -@E> true -∗
   i -@{1 / 2}A> ps_acc -∗
   i -@{1 / 2}A> ps_acc -∗
   LB@ i := [ps_na] -∗
   transaction_hpool_global_transferred trans -∗
   transaction_pagetable_entries_transferred i trans -∗
   retrieval_entries_transferred i trans -∗
   R0 @@ V0 ->r encode_hvc_func Run -∗
   R1 @@ V0 ->r encode_vmid i -∗
   (∃ r2 : Addr, R2 @@ V0 ->r r2) -∗
   RX_state@i:= rx_state -∗
   mailbox.rx_page i p_rx -∗
   rx_pages (list_to_set list_of_vmids ∖ {[i]}) -∗
   ▷ VMProp V0 (vmprop_zero i p_rx) (1 / 2) -∗
   VMProp i (vmprop_unknown i p_tx p_rx trans') 1 -∗
   transaction_pagetable_entries_owned i trans -∗
   pagetable_entries_excl_owned i (ps_acc ∖ {[p_rx; p_tx]} ∖ pages_in_trans trans) -∗
   retrieval_entries_owned i trans -∗
   (∃ mem1 : mem, memory_pages ((ps_acc ∪ (pages_in_trans (trans_memory_in_trans i trans))) ∖ ps_acc) mem1) -∗
   ([∗ map] k↦v ∈ mem_acc_tx, k ->a v) -∗
   (∃ mem2 : mem, memory_page p_tx mem2) -∗
   SSWP ExecI @ i {{ bm, (if bm.1 then VMProp_holds i (1 / 2) else True) -∗ WP bm.2 @ i {{ _, True }} }}.
  Proof.
    iIntros (Htotal_regs Hsubset_mb Hdisj_na Hnin_rx Hnin_tx Hlookup_PC Hin_ps_acc Hneq_ptx Hdom_mem_acc_tx Hin_ps_acc_tx
                         Hlookup_mem_ai Heqn Hlookup_reg_R0 Hdecode_hvc).
    iIntros "IH regs tx pgt_tx pgt_acc pgt_acc' LB trans_hpool_global tran_pgt_transferred retri R0z R1z R2z rx_state rx other_rx prop0
             propi tran_pgt_owned pgt_owned retri_owned mem_rest mem_acc_tx mem_tx".
    set ps_mem_in_trans := (pages_in_trans (trans_memory_in_trans i trans)).
    pose proof (Htotal_regs R2) as[r2 Hlookup_reg_R2].
    iDestruct (reg_big_sepM_split_upd3 i Hlookup_PC Hlookup_reg_R0 Hlookup_reg_R2 with "[$regs]")
      as "(PC & R0 & R2 & Hacc_regs)";eauto.
    iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "mem_acc_tx") as "[mem_instr Hacc_mem_acc_tx]".


    iApply (invalid_hvc_func with "[PC mem_instr pgt_acc' R0 R2 tx]");iFrameAutoSolve.
    iNext.
    iIntros "(PC & mem_instr & pgt_acc' & tx & R0 & R2 ) _".
    iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R2]") as (regs') "[%Htotal_regs' regs]".

    iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
    iApply ("IH" $! _ ps_acc trans _ Htotal_regs' Hsubset_mb Hdisj_na Hnin_rx Hnin_tx with "regs tx pgt_tx pgt_acc pgt_acc' LB trans_hpool_global
                            tran_pgt_transferred retri R0z R1z R2z rx_state rx other_rx prop0 propi tran_pgt_owned pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx]
                            ").
    {
      iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx $mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
      iExists mem_acc_tx;by iFrame "mem_acc_tx".
      iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
      set_solver +.
    }
  Qed.

End ftlr_invalid_hvc.