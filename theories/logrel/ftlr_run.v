From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang trans_extra.
From HypVeri.algebra Require Import base pagetable mem trans.
From HypVeri.rules Require Import run.
From HypVeri.logrel Require Import logrel logrel_extra.
From HypVeri Require Import proofmode.
Import uPred.

Section ftlr_run.
  Context `{hypconst:HypervisorConstants}.
  Context `{hypparams:!HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.

Lemma ftlr_run {i trans' mem_acc_tx ai regs ps_acc p_tx p_rx ps_na instr trans rx_state r0}:
  base_extra.is_total_gmap regs ->
  {[p_tx; p_rx]} ⊆ ps_acc ->
  i ≠ V0 ->
  ps_na ## ps_acc ∪ accessible_in_trans_memory_pages i trans ->
  p_rx ∉ ps_acc ∖ {[p_rx; p_tx]} ∪ accessible_in_trans_memory_pages i trans ->
  p_tx ∉ ps_acc ∖ {[p_rx; p_tx]} ∪ accessible_in_trans_memory_pages i trans ->
  regs !! PC = Some ai ->
  tpa ai ∈ ps_acc ->
  tpa ai ≠ p_tx ->
  dom (gset Addr) mem_acc_tx = set_of_addr (ps_acc ∖ {[p_tx]}) ->
  tpa ai ∈ ps_acc ∖ {[p_tx]} ->
  mem_acc_tx !! ai = Some instr ->
  decode_instruction instr = Some Hvc ->
  regs !! R0 = Some r0 ->
  decode_hvc_func r0 = Some Run ->
  p_tx ≠ p_rx ->
  ⊢
  ▷ (∀ (a : gmap reg_name Addr) (a0 a1: gset PID) (a2 a3: gmap Addr transaction) (a4 : option (Addr * VMID)),
          ⌜base_extra.is_total_gmap a⌝
            → ⌜{[p_tx; p_rx]} ⊆ a1⌝
              → ⌜a0 ## a1 ∪ accessible_in_trans_memory_pages i a3⌝
                → ⌜p_rx ∉ a1 ∖ {[p_rx; p_tx]} ∪ accessible_in_trans_memory_pages i a3⌝
                  → ⌜p_tx ∉ a1 ∖ {[p_rx; p_tx]} ∪ accessible_in_trans_memory_pages i a3⌝
                    → ([∗ map] r↦w ∈ a, r @@ i ->r w) -∗
                      TX@i:=p_tx -∗
                      p_tx -@O> - ∗ p_tx -@E> true -∗
                      i -@{1 / 2}A> a1 -∗
                      i -@{1 / 2}A> a1 -∗
                      LB@ i := [a0] -∗
                      transaction_hpool_global_transferred a3 -∗
                      transaction_pagetable_entries_transferred i a3 -∗
                      retrieval_entries_transferred i a3 -∗
                      R0 @@ V0 ->r encode_hvc_func Run -∗
                      R1 @@ V0 ->r encode_vmid i -∗
                      (∃ r2 : Addr, R2 @@ V0 ->r r2) -∗
                      RX_state@i:= a4 -∗
                      mailbox.rx_page i p_rx -∗
                      rx_pages (list_to_set list_of_vmids ∖ {[i]}) -∗
                      (∃ trans, ▷ VMProp V0 (vmprop_zero i p_tx p_rx trans) (1 / 2)) -∗
                      VMProp i (vmprop_unknown i p_tx p_rx a2) 1 -∗
                      transaction_pagetable_entries_owned i a3 -∗
                      pagetable_entries_excl_owned i (a1 ∖ {[p_rx; p_tx]} ∖ (accessible_in_trans_memory_pages i a3)) -∗
                      retrieval_entries_owned i a3 -∗
                      (∃ mem : lang.mem, memory_pages (a1 ∪ (accessible_in_trans_memory_pages i a3)) mem) -∗
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
   (∃ trans, ▷ VMProp V0 (vmprop_zero i p_tx p_rx trans) (1 / 2)) -∗
   VMProp i (vmprop_unknown i p_tx p_rx trans') 1 -∗
   transaction_pagetable_entries_owned i trans -∗
   pagetable_entries_excl_owned i (ps_acc ∖ {[p_rx; p_tx]} ∖ (accessible_in_trans_memory_pages i trans)) -∗
   retrieval_entries_owned i trans -∗
   (∃ mem1 : mem, memory_pages ((ps_acc ∪ (accessible_in_trans_memory_pages i trans)) ∖ ps_acc) mem1) -∗
   ([∗ map] k↦v ∈ mem_acc_tx, k ->a v) -∗
   (∃ mem2 : mem, memory_page p_tx mem2) -∗
   SSWP ExecI @ i {{ bm, (if bm.1 then VMProp_holds i (1 / 2) else True) -∗ WP bm.2 @ i {{ _, True }} }}.
  Proof.
    iIntros (Htotal_regs Hsubset_mb Hneq_0 Hdisj_na Hnin_rx Hnin_tx Hlookup_PC Hin_ps_acc Hneq_ptx Hdom_mem_acc_tx Hin_ps_acc_tx
                         Hlookup_mem_ai Heqn  Hlookup_reg_R0 Hdecode_hvc).
    iIntros (Hneq_mb) "IH regs tx pgt_tx pgt_acc pgt_acc' LB trans_hpool_global tran_pgt_transferred retri R0z R1z R2z rx_state rx other_rx prop0
             propi tran_pgt_owned pgt_owned retri_owned mem_rest mem_acc_tx mem_tx".
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
    iApply (run_not_primary (r0 := r0) ai i with "[PC tx pgt_acc' mem_instr r_arg1 r_arg2]"); iFrameAutoSolve.
    iNext.
    iIntros "(PC & mem_instr & pgt_acc' & tx & r_arg1 & r_arg2) _".
    iDestruct ("Hacc_regs" with "[$PC $r_arg1 $r_arg2]") as (regs') "[%Htotal_regs' regs]";iFrame.
    iDestruct ("Hacc_mem_acc" with "[mem_instr]") as "mem"; iFrame.
    iAssert (memory_pages (ps_acc ∖ {[p_tx]}) _)%I with "[mem]" as "mem_acc".
    by iFrame.
    iApply ("IH" $!  _ _ ps_acc _ trans _ Htotal_regs' Hsubset_mb Hdisj_na Hnin_rx Hnin_tx with "regs tx pgt_tx pgt_acc pgt_acc'
                 LB trans_hpool_global tran_pgt_transferred retri R0z R1z R2z rx_state rx other_rx [prop0] propi tran_pgt_owned
                 pgt_owned retri_owned [mem_rest mem_acc mem_tx]").
    { iDestruct "prop0" as "[%x prop0]". iExists x. iFrame. }
    {
      iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
      iSplitL "mem_acc".
      iExists mem_acc_tx; by iFrame "mem_acc".
      iFrame "mem_tx".
      iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
      set_solver +.
    }
  Qed.

End ftlr_run.
