From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.algebra Require Import base pagetable mem trans mailbox.
From HypVeri.rules Require Import msg_poll.
From HypVeri.logrel Require Import logrel logrel_extra.
From HypVeri Require Import proofmode.
Import uPred.

Section ftlr_msg_poll.
  Context `{hypconst:HypervisorConstants}.
  Context `{hypparams:!HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.

  Lemma ftlr_msg_poll {i mem_acc_tx ai regs ps_acc p_tx p_rx instr trans rxs r0} P:
  (∀ trans trans' rxs rxs', delete i rxs = delete i rxs' -> except i trans = except i trans' -> P trans rxs ⊣⊢ P trans' rxs') ->
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
    dom (gset Addr) mem_acc_tx = set_of_addr (ps_acc ∖ {[p_tx]}) ->
    tpa ai ∈ ps_acc ∖ {[p_tx]} ->
    mem_acc_tx !! ai = Some instr ->
    decode_instruction instr = Some Hvc ->
    regs !! R0 = Some r0 ->
    decode_hvc_func r0 = Some Poll ->
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
   P trans rxs -∗
   SSWP ExecI @ i {{ bm, (if bm.1 then VMProp_holds i (1 / 2) else True) -∗ WP bm.2 @ i {{ _, True }} }}.
  Proof.
    iIntros (P_eq Htotal_regs Htotal_rxs Hsubset_mb Hneq_0 Hsubset_acc Hnin_rx Hnin_tx Hlookup_PC Hin_ps_acc Hneq_ptx Hdom_mem_acc_tx Hin_ps_acc_tx
                         Hlookup_mem_ai Heqn).
    iIntros (Hlookup_reg_R0 Hdecode_hvc Hneq_mb) "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri rx_state rx other_rx
             tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx P".
    set ps_mem_in_trans := accessible_in_trans_memory_pages i trans.
    pose proof (Htotal_regs R1) as[r1 Hlookup_reg_R1].
    pose proof (Htotal_regs R2) as[r2 Hlookup_reg_R2].
    iDestruct (reg_big_sepM_split_upd4 i Hlookup_PC Hlookup_reg_R0 Hlookup_reg_R1 Hlookup_reg_R2 with "[$regs]")
      as "(PC & R0 & R1 & R2 & Hacc_regs)";eauto.
    iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "mem_acc_tx") as "[mem_instr Hacc_mem_acc_tx]".

    pose proof (Htotal_rxs i) as [rx_state Hlookup_rs].
    iDestruct ("rx_state" $! rx_state with "[]") as "rx_state". done.

    destruct (rx_state).
    { (* apply [msg_poll_full] *)
      destruct p.
      iApply (msg_poll_full ai with "[PC mem_instr pgt_acc R0 R1 R2 tx rx_state]");iFrameAutoSolve.
      iNext. iIntros "(PC & mem_instr & tx & pgt_acc & R0 & R1 & R2 & rx_state ) _".
      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
      iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".

      set rxs' := <[i:= None]> rxs.
      iApply ("IH" $! _ ps_acc trans rxs' with "[] [] [] [] [] [] regs tx pgt_tx rx pgt_acc pgt_owned trans_hpool_global
                            tran_pgt_transferred retri [rx_state] [other_rx] tran_pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx]
                            [P]");auto.
      {
        iPureIntro.
        intro.
        destruct (decide (k = i)).
        {
          exists None.
          rewrite /rxs'.
          subst k. rewrite lookup_insert //.
        }
        specialize (Htotal_rxs k).
        rewrite /rxs' lookup_insert_ne //.
      }
      {
        iIntros (?) "%Hlookup_rs'".
        rewrite lookup_insert in Hlookup_rs'.
        inversion Hlookup_rs'.
        done.
      }
      {
        rewrite /rx_states_global.
        replace (delete i rxs) with (delete i rxs'). done.
        rewrite /rxs' delete_insert_delete //.
      }
      {
        iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx $mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
        iExists mem_acc_tx;by iFrame "mem_acc_tx".
        iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
        set_solver +.
      }
      {
        iApply (P_eq with "P").
        rewrite /rxs' delete_insert_delete //.
        done.
      }
    }
    (* apply [msg_poll_empty] *)
      iApply (msg_poll_empty ai with "[PC mem_instr pgt_acc R0 R2 tx rx_state]");iFrameAutoSolve.
      iNext. iIntros "(PC & mem_instr & tx & pgt_acc & R0 & R2 & rx_state ) _".
      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
      iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".

      iApply ("IH" $! _ ps_acc trans _ Htotal_rxs Htotal_regs' Hsubset_mb Hsubset_acc Hnin_rx Hnin_tx with "regs tx pgt_tx rx pgt_acc pgt_owned trans_hpool_global
                            tran_pgt_transferred retri [rx_state] other_rx tran_pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx]
                            P").
      {
        rewrite /rx_state_get.
        iIntros (?) "%Hlookup_rs'".
        rewrite Hlookup_rs in Hlookup_rs'.
        inversion Hlookup_rs'.
        done.
      }
      {
        iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx $mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
        iExists mem_acc_tx;by iFrame "mem_acc_tx".
        iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
        set_solver +.
      }
Qed.

End ftlr_msg_poll.
