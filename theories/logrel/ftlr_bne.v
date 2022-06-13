From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.algebra Require Import base pagetable mem trans.
From HypVeri.rules Require Import rules_base bne.
From HypVeri.logrel Require Import logrel logrel_extra.
From HypVeri Require Import proofmode.
Import uPred.

Section ftlr_bne.
  Context `{hypconst:HypervisorConstants}.
  Context `{hypparams:!HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.

Lemma ftlr_bne {i mem_acc_tx ai regs rxs ps_acc p_tx p_rx instr trans op} P:
  base_extra.is_total_gmap regs ->
  base_extra.is_total_gmap rxs ->
  {[p_tx; p_rx]} ⊆ ps_acc ->
  currently_accessible_in_trans_memory_pages i trans ⊆ ps_acc ∖ {[p_tx; p_rx]} ->
  p_rx ∉ ps_acc ∖ {[p_rx; p_tx]} ∪ accessible_in_trans_memory_pages i trans ->
  p_tx ∉ ps_acc ∖ {[p_rx; p_tx]} ∪ accessible_in_trans_memory_pages i trans ->
  regs !! PC = Some ai ->
  tpa ai ∈ ps_acc ->
  tpa ai ≠ p_tx ->
  dom (gset Word) mem_acc_tx = set_of_addr (ps_acc ∖ {[p_tx]}) ->
  tpa ai ∈ ps_acc ∖ {[p_tx]} ->
  mem_acc_tx !! ai = Some instr ->
  decode_instruction instr = Some (Bne op) ->
  ⊢ ▷ (∀ (a : gmap reg_name Word) (a0 : gset PID) (a1 : gmap Word transaction) (a2 : gmap VMID (option (Word * VMID))),
              ⌜base_extra.is_total_gmap a2⌝ -∗
              ⌜base_extra.is_total_gmap a⌝ -∗
              ⌜{[p_tx; p_rx]} ⊆ a0⌝ -∗
              ⌜currently_accessible_in_trans_memory_pages i a1 ⊆ a0 ∖ {[p_tx; p_rx]}⌝ -∗
              ⌜p_rx ∉ a0 ∖ {[p_rx; p_tx]} ∪ accessible_in_trans_memory_pages i a1⌝ -∗
              ⌜p_tx ∉ a0 ∖ {[p_rx; p_tx]} ∪ accessible_in_trans_memory_pages i a1⌝ -∗
              ([∗ map] r↦w ∈ a, r @@ i ->r w) -∗
              TX@i:=p_tx -∗
              p_tx -@O> - ∗ p_tx -@E> true -∗
              mailbox.rx_page i p_rx -∗
              i -@A> a0 -∗
              pagetable_entries_excl_owned i (a0 ∖ {[p_rx; p_tx]} ∖ currently_accessible_in_trans_memory_pages i a1) -∗
              transaction_hpool_global_transferred a1 -∗
              transaction_pagetable_entries_transferred i a1 -∗
              retrievable_transaction_transferred i a1 -∗
              rx_state_get i a2 -∗
              rx_states_global (delete i a2) -∗
              transaction_pagetable_entries_owned i a1 -∗
              retrieved_transaction_owned i a1 -∗
              (∃ mem : lang.mem, memory_pages (a0 ∪ (accessible_in_trans_memory_pages i a1)) mem) -∗
              (P a1 a2) -∗
              WP ExecI @ i {{ _, True }}) -∗
   ([∗ map] r↦w ∈ regs, r @@ i ->r w) -∗
   TX@i:=p_tx -∗
   p_tx -@O> - ∗ p_tx -@E> true -∗
   i -@A> ps_acc -∗
   pagetable_entries_excl_owned i (ps_acc ∖ {[p_rx; p_tx]} ∖ (currently_accessible_in_trans_memory_pages i trans)) -∗
   transaction_hpool_global_transferred trans -∗
   transaction_pagetable_entries_transferred i trans -∗
   retrievable_transaction_transferred i trans -∗
   rx_state_get i rxs -∗
   mailbox.rx_page i p_rx -∗
   rx_states_global (delete i rxs) -∗
   transaction_pagetable_entries_owned i trans -∗
   retrieved_transaction_owned i trans -∗
   (∃ mem1 : mem, memory_pages ((ps_acc ∪ (accessible_in_trans_memory_pages i trans)) ∖ ps_acc) mem1) -∗
   ([∗ map] k↦v ∈ mem_acc_tx, k ->a v) -∗
   (∃ mem2 : mem, memory_page p_tx mem2) -∗
   (P trans rxs) -∗
   SSWP ExecI @ i {{ bm, (if bm.1 then VMProp_holds i (1 / 2) else True) -∗ WP bm.2 @ i {{ _, True }} }}.
  Proof.
    iIntros (Htotal_regs Htotal_rxs Hsubset_mb Hsubset_acc Hnin_rx Hnin_tx Hlookup_PC Hin_ps_acc Hneq_ptx Hdom_mem_acc_tx Hin_ps_acc_tx Hlookup_mem_ai Heqn).
    iIntros "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri rx_state rx other_rx tran_pgt_owned
                 retri_owned mem_rest mem_acc_tx mem_tx P".
    destruct op as [| | n nle].
    {
      apply decode_instruction_valid in Heqn.
      inversion Heqn.
      unfold reg_valid_cond in *.
      exfalso.
      naive_solver.
    }
    {
      apply decode_instruction_valid in Heqn.
      inversion Heqn.
      unfold reg_valid_cond in *.
      exfalso.
      naive_solver.
    }
    pose proof (Htotal_regs (R n nle)) as [a_arg1 Hlookup_arg1].
    pose proof (Htotal_regs NZ) as [a_nz Hlookup_nz].
    (* getting registers *)
    iDestruct ((reg_big_sepM_split_upd3 i Hlookup_PC Hlookup_arg1 Hlookup_nz)
                with "[$regs]") as "(PC & r_arg1 & r_nz & Hacc_regs)"; [done | done | done | done |].
    (* getting mem *)
    iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "[$mem_acc_tx]")
      as "[mem_instr Hacc_mem_acc_tx]".
    iApply (bne _ (R n nle) with "[PC tx pgt_acc mem_instr r_arg1 r_nz]"); iFrameAutoSolve.
    iNext. iIntros "(PC & mem_instr & r_arg1 & pgt_acc & r_nz & tx) _".
    iDestruct ("Hacc_regs" with "[$PC $r_arg1 $r_nz]") as (regs') "[%Htotal_regs' regs]";iFrame.
    iDestruct ("Hacc_mem_acc_tx" with "mem_instr") as "mem_acc_tx".
    iApply ("IH" $! _ ps_acc trans _ Htotal_rxs Htotal_regs' Hsubset_mb Hsubset_acc Hnin_rx Hnin_tx with "regs tx pgt_tx rx pgt_acc pgt_owned
                       trans_hpool_global tran_pgt_transferred retri rx_state other_rx
                           tran_pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx] P").
    {
      iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx $mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
      iExists mem_acc_tx;by iFrame "mem_acc_tx".
      iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
      set_solver +.
    }
  Qed.

End ftlr_bne.
