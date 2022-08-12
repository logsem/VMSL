From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang trans_extra.
From HypVeri.algebra Require Import base pagetable mem trans.
From HypVeri.rules Require Import run.
From HypVeri.logrel Require Import logrel logrel_extra.
From HypVeri Require Import stdpp_extra proofmode.
Import uPred.

Section ftlr_run.
  Context `{hypconst:HypervisorConstants}.
  Context `{hypparams:!HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.

Lemma ftlr_run Φ_t Φ_r {i mem_acc_tx ai regs rxs ps_acc p_tx p_rx instr trans r0}:
  base_extra.is_total_gmap regs ->
  base_extra.is_total_gmap rxs ->
  {[p_tx; p_rx]} ⊆ ps_acc ->
  i ≠ V0 ->
  currently_accessible_in_trans_memory_pages i trans ⊆ ps_acc ∖ {[p_tx; p_rx]} ->
  p_rx ∉ ps_acc ∖ {[p_rx; p_tx]} ∪ accessible_in_trans_memory_pages i trans ->
  p_tx ∉ ps_acc ∖ {[p_rx; p_tx]} ∪ accessible_in_trans_memory_pages i trans ->
  regs !! PC = Some ai ->
  tpa ai ∈ ps_acc ->
  tpa ai ≠ p_tx ->
  dom mem_acc_tx = set_of_addr (ps_acc ∖ {[p_tx]}) ->
  tpa ai ∈ ps_acc ∖ {[p_tx]} ->
  mem_acc_tx !! ai = Some instr ->
  decode_instruction instr = Some Hvc ->
  regs !! R0 = Some r0 ->
  decode_hvc_func r0 = Some Run ->
  p_tx ≠ p_rx ->
  ⊢ ▷ (∀ (a : gmap reg_name Addr) (a0 : gset PID) (a1 : gmap Addr transaction) (a2 : gmap VMID (option (Addr * VMID))),
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
              ((∃ r0 : Addr, R0 @@ V0 ->r r0 ∗ ⌜decode_hvc_func r0 = Some Run⌝) ∗
              (∃ r1 : Addr, R1 @@ V0 ->r r1 ∗ ⌜decode_vmid r1 = Some i⌝) ∗ (∃ r2 : Addr, R2 @@ V0 ->r r2) ∗
              ▷ VMProp V0 (vmprop_zero i Φ_t Φ_r a1 a2) (1 / 2) ∗ ∃ P, VMProp i P 1) -∗
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
   ((∃ r0 : Addr, R0 @@ V0 ->r r0 ∗ ⌜decode_hvc_func r0 = Some Run⌝) ∗
    (∃ r1 : Addr, R1 @@ V0 ->r r1 ∗ ⌜decode_vmid r1 = Some i⌝) ∗ (∃ r2 : Addr, R2 @@ V0 ->r r2) ∗
    ▷ VMProp V0 (vmprop_zero i Φ_t Φ_r trans rxs) (1 / 2) ∗ ∃ P, VMProp i P 1) -∗
   SSWP ExecI @ i {{ bm, (if bm.1 then VMProp_holds i (1 / 2) else True) -∗ WP bm.2 @ i {{ _, True }} }}.
  Proof.
    iIntros (Htotal_regs Htotal_rxs Hsubset_mb Hneq_0 Hsubset_acc Hnin_rx Hnin_tx Hlookup_PC Hin_ps_acc Hneq_ptx Hdom_mem_acc_tx Hin_ps_acc_tx
                         Hlookup_mem_ai Heqn Hlookup_reg_R0).
    iIntros ( Hdecode_hvc Hneq_mb) "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri rx_state rx other_rx
                          tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx ([% [R0z %]]& [% [R1z %]] & [% R2z] & prop0 &propi)".
    pose proof (Htotal_regs R0) as [a_arg1 Hlookup_arg1].
    pose proof (Htotal_regs R2) as [a_arg2 Hlookup_arg2].
    (* getting registers *)
    iDestruct ((reg_big_sepM_split_upd3 i Hlookup_PC Hlookup_arg1 Hlookup_arg2)
                with "[$regs]") as "(PC & r_arg1 & r_arg2 & Hacc_regs)"; [done | done | done | done |].
    (* getting mem *)
    iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "[$mem_acc_tx]")
      as "[mem_instr Hacc_mem_acc]".
    rewrite Hlookup_arg1 in Hlookup_reg_R0.
    inversion Hlookup_reg_R0.
    subst a_arg1.
    iApply (run_not_primary (r0 := r0) ai i with "[PC tx pgt_acc mem_instr r_arg1 r_arg2]"); iFrameAutoSolve.
    iNext.
    iIntros "(PC & mem_instr & pgt_acc & tx & r_arg1 & r_arg2) _".
    iDestruct ("Hacc_regs" with "[$PC $r_arg1 $r_arg2]") as (regs') "[%Htotal_regs' regs]";iFrame.
    iDestruct ("Hacc_mem_acc" with "[mem_instr]") as "mem"; iFrame.
    iAssert (memory_pages (ps_acc ∖ {[p_tx]}) _)%I with "[mem]" as "mem_acc".
    by iFrame.
    iApply ("IH" $!  _ ps_acc trans _ Htotal_rxs Htotal_regs' Hsubset_mb Hsubset_acc Hnin_rx Hnin_tx with "regs tx pgt_tx rx pgt_acc pgt_owned
                 trans_hpool_global tran_pgt_transferred retri rx_state other_rx tran_pgt_owned
                  retri_owned [mem_rest mem_acc mem_tx] [R0z R1z R2z $prop0 $propi]").
    {
      iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
      iSplitL "mem_acc".
      iExists mem_acc_tx; by iFrame "mem_acc".
      iFrame "mem_tx".
      iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
      set_solver +.
    }
    {
      iSplitL "R0z". iExists _; iFrame. done.
      iSplitL "R1z". iExists _; iFrame. done.
      iExists _. iFrame.
    }
  Qed.

End ftlr_run.
