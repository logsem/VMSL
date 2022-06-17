From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.algebra Require Import base pagetable mem trans.
From HypVeri.rules Require Import rules_base ldr.
From HypVeri.logrel Require Import logrel logrel_extra.
From HypVeri Require Import proofmode.
Import uPred.

Section ftlr_ldr.
  Context `{hypconst:HypervisorConstants}.
  Context `{hypparams:!HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.

Lemma ftlr_ldr {i mem_acc_tx ai regs rxs ps_acc p_tx p_rx instr trans src dst} P:
  base_extra.is_total_gmap regs ->
  base_extra.is_total_gmap rxs ->
  {[p_tx; p_rx]} ⊆ ps_acc ->
  currently_accessible_in_trans_memory_pages i trans ⊆ ps_acc ∖ {[p_tx; p_rx]} ->
  p_rx ∉ ps_acc ∖ {[p_rx; p_tx]} ∪ accessible_in_trans_memory_pages i trans ->
  p_tx ∉ ps_acc ∖ {[p_rx; p_tx]} ∪ accessible_in_trans_memory_pages i trans ->
  regs !! PC = Some ai ->
  tpa ai ∈ ps_acc ->
  tpa ai ≠ p_tx ->
  dom mem_acc_tx = set_of_addr (ps_acc ∖ {[p_tx]}) ->
  tpa ai ∈ ps_acc ∖ {[p_tx]} ->
  mem_acc_tx !! ai = Some instr ->
  decode_instruction instr = Some (Ldr dst src) ->
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
   (P trans rxs) -∗
   SSWP ExecI @ i {{ bm, (if bm.1 then VMProp_holds i (1 / 2) else True) -∗ WP bm.2 @ i {{ _, True }} }}.
  Proof.
    iIntros (Htotal_regs Htotal_rxs Hsubset_mb Hsubset_acc Hnin_rx Hnin_tx Hlookup_PC Hin_ps_acc Hneq_ptx Hdom_mem_acc_tx Hin_ps_acc_tx Hlookup_mem_ai Heqn).
    iIntros "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri rx_state rx other_rx tran_pgt_owned
                 retri_owned mem_rest mem_acc_tx mem_tx P".
    pose proof Heqn as Hdecode.
    apply decode_instruction_valid in Heqn.
    inversion Heqn as [| | ? ? Hvalid_dst Hvalid_src Hvalid_neq | | | | | | | | | ].
    subst dst0 src0.
    unfold reg_valid_cond in Hvalid_dst, Hvalid_src.
    pose proof (Htotal_regs src) as [a_src Hlookup_src].
    pose proof (Htotal_regs dst) as [w_dst Hlookup_dst].
    (* getting registers *)
    iDestruct ((reg_big_sepM_split_upd3 i Hlookup_PC Hlookup_src Hlookup_dst)
                with "[$regs]") as "(PC & r_src & r_dst & Hacc_regs)"; [by destruct_and ! | by destruct_and ! | done | done |].
    (* case analysis on src  *)
    destruct (decide ((tpa a_src) ∈ ps_acc)) as [Hin' | Hin''].
    { (* has access to the page, more cases.. *)
      destruct (decide((tpa a_src) = p_tx)).
      { (* trying to read from tx page, fail *)
        (* getting mem *)
        iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "[mem_acc_tx]")
          as "[mem_instr Hacc_mem_acc_tx]"; first done.
        iApply (ldr_access_tx (w3 := w_dst) ai a_src dst src with "[PC pgt_acc tx mem_instr r_src r_dst]"); iFrameAutoSolve.
        iNext.
        iIntros "(tx & PC & a_instr & r_src & acc & r_dst) _".
        by iApply wp_terminated.
      }
      { (* normal case *)
        destruct (decide (a_src = ai)) as [|Hneq''].
        { (* exact same addr *)
          iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "[mem_acc_tx]")
            as "[mem_instr Hacc_mem_acc_tx]"; first done.
          iApply (ldr_same_addr (s := ps_acc) ai a_src dst src with "[PC mem_instr r_src r_dst tx pgt_acc]"); iFrameAutoSolve.
          { symmetry;done. }
          iNext. iIntros "(PC & mem_instr & r_src & r_dst & pgt_acc & tx) _".
          iDestruct ("Hacc_regs" with "[$PC $r_src $r_dst]") as (regs') "[%Htotal_regs' regs]";iFrame.
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
        }
        { (* different addresses *)
          destruct (decide ((tpa a_src) = (tpa ai))) as [Heqn'|].
          { (* in same page *)
            pose proof Hin_ps_acc as Hin_ps_acc.
            rewrite <-Heqn' in Hin_ps_acc.
            assert (tpa a_src ∈ ps_acc ∖ {[p_tx]}) as Hin_ps_acc'.
            set_solver + Hin_ps_acc n.
            pose proof (elem_of_memory_pages_lookup _ _ _ Hin_ps_acc' Hdom_mem_acc_tx) as [w_src Hlookup_a_src].
            iDestruct (mem_big_sepM_split2 mem_acc_tx Hneq'' Hlookup_a_src Hlookup_mem_ai with "[$mem_acc_tx]")
              as "[a_src [a_instr Hacc_mem_acc_tx]]".
            iApply (ldr_same_page (s := ps_acc) ai a_src dst src with "[PC a_instr a_src r_src r_dst tx pgt_acc]"); iFrameAutoSolve.
            set_solver. intro; apply Hneq''. symmetry;done. symmetry;done.
            iNext. iIntros "(PC & mem_instr & r_src & a_src & r_dst & pgt_acc & tx) _".
            iDestruct ("Hacc_regs" with "[$PC $r_src $r_dst]") as (regs') "[%Htotal_regs' regs]";iFrame.
            iDestruct ("Hacc_mem_acc_tx" with "[a_src mem_instr]") as "mem_acc_tx"; iFrame.
            iApply ("IH" $! _ ps_acc trans _ Htotal_rxs Htotal_regs' Hsubset_mb Hsubset_acc Hnin_rx Hnin_tx with "regs tx pgt_tx rx pgt_acc pgt_owned
                       trans_hpool_global tran_pgt_transferred retri rx_state other_rx
                           tran_pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx] P").
            {
              iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx $mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
              iExists mem_acc_tx;by iFrame "mem_acc_tx".
              iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
              set_solver +.
            }
          }
          { (* in difference pages *)
            (* getting mem *)
            assert (tpa a_src ∈ ps_acc ∖ {[p_tx]}) as Hin_ps_acc'.
            set_solver + Hin' n.
            pose proof (elem_of_memory_pages_lookup _ _ _ Hin_ps_acc' Hdom_mem_acc_tx) as [w_src Hlookup_a_src].
            iDestruct (mem_big_sepM_split2 mem_acc_tx Hneq'' Hlookup_a_src Hlookup_mem_ai with "[$mem_acc_tx]")
              as "[a_src [mem_instr Hacc_mem_acc_tx]]".
            iApply (ldr (s := ps_acc) ai a_src dst src with "[PC mem_instr a_src r_src r_dst tx pgt_acc]"); iFrameAutoSolve.
            { set_solver. }
            iNext. iIntros "(PC & mem_instr & r_src & a_src & r_dst & pgt_acc & tx) _".
            iDestruct ("Hacc_regs" with "[$PC $r_src $r_dst]") as (regs') "[%Htotal_regs' regs]";iFrame.
            iDestruct ("Hacc_mem_acc_tx" with "[a_src mem_instr]") as "mem_acc_tx"; iFrame.
            iApply ("IH" $! _ ps_acc trans _ Htotal_rxs Htotal_regs' Hsubset_mb Hsubset_acc Hnin_rx Hnin_tx with "regs tx pgt_tx rx pgt_acc pgt_owned
                       trans_hpool_global tran_pgt_transferred retri rx_state other_rx
                           tran_pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx] P").
            {
              iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx $mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
              iExists mem_acc_tx;by iFrame "mem_acc_tx".
              iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
              set_solver +.
            }
          }
        }
      }
    }
    { (* no access to the page, apply ldr_error *)
      (* getting mem *)
      (* we don't update memory *)
      iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "[mem_acc_tx]")
        as "[mem_instr Hacc_mem_acc_tx]"; first done.
      iApply (ldr_no_access (s := ps_acc) ai a_src dst src with "[PC mem_instr r_src r_dst tx pgt_acc]"); iFrameAutoSolve.
      iNext. iIntros "(PC & mem_instr & r_src & pgt_acc & r_dst & tx) _".
      by iApply wp_terminated.
    }
  Qed.

End ftlr_ldr.
