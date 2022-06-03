From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.algebra Require Import base pagetable mem trans.
From HypVeri.rules Require Import rules_base str.
From HypVeri.logrel Require Import logrel logrel_extra.
From HypVeri Require Import proofmode.
Import uPred.

Section ftlr_str.
  Context `{hypconst:HypervisorConstants}.
  Context `{hypparams:!HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.

Lemma ftlr_str {i mem_acc_tx ai regs rxs ps_acc p_tx p_rx instr trans src dst} P:
  base_extra.is_total_gmap regs ->
  base_extra.is_total_gmap rxs ->
  {[p_tx; p_rx]} ⊆ ps_acc ->
  currently_accessible_in_trans_memory_pages i trans ⊆ ps_acc ∖ {[p_tx; p_rx]} ->
  p_rx ∉ ps_acc ∖ {[p_rx; p_tx]} ∪ accessible_in_trans_memory_pages i trans ->
  p_tx ∉ ps_acc ∖ {[p_rx; p_tx]} ∪ accessible_in_trans_memory_pages i trans ->
  regs !! PC = Some ai ->
  tpa ai ∈ ps_acc ->
  tpa ai ≠ p_tx ->
  dom (gset Addr) mem_acc_tx = set_of_addr (ps_acc ∖ {[p_tx]}) ->
  tpa ai ∈ ps_acc ∖ {[p_tx]} ->
  mem_acc_tx !! ai = Some instr ->
  decode_instruction instr = Some (Str src dst) ->
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
    inversion Heqn as [| | | ? ? Hvalid_dst Hvalid_src Hvalid_neq | | | | | | | | ].
    subst dst0 src0.
    unfold reg_valid_cond in Hvalid_dst, Hvalid_src.
    pose proof (Htotal_regs src) as [a_src Hlookup_src].
    pose proof (Htotal_regs dst) as [w_dst Hlookup_dst].
    (* getting registers *)
    iDestruct ((reg_big_sepM_split_upd3 i Hlookup_PC Hlookup_src Hlookup_dst)
                with "[$regs]") as "(PC & r_src & r_dst & Hacc_regs)"; [by destruct_and ! | by destruct_and ! | done | done |].
    (* case analysis on src  *)
    destruct (decide ((tpa w_dst) ∈ ps_acc)) as [Hin' | Hin''].
    { (* has access to the page, more cases.. *)
      destruct (decide((tpa w_dst) = p_rx)).
      { (* trying to write to rx page, fail *)
        (* getting mem *)
        iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "[mem_acc_tx]")
          as "[mem_instr Hacc_mem_acc_tx]"; first done.
        iDestruct "rx" as "(rx & rx_own & rx_excl)".
        iApply (str_access_rx (p := p_rx) ai w_dst src dst with "[PC pgt_acc tx rx mem_instr r_src r_dst]"); iFrameAutoSolve.
        iNext. iIntros "(PC & mem_instr & r_dst & acc & r_src & tx & rx) _".
        by iApply wp_terminated.
      }
      { (* normal case *)
        destruct (decide (w_dst = ai)) as [|Hneq''].
        { (* exact same addr *)
          iDestruct (mem_big_sepM_split_upd mem_acc_tx Hlookup_mem_ai with "[mem_acc_tx]")
            as "[mem_instr Hacc_mem_acc_tx]"; first done.
          iDestruct "rx" as "(rx & rx_own & rx_excl)".
          iApply (str_same_addr (p := p_rx) (s := ps_acc) ai w_dst src dst with "[PC mem_instr r_src r_dst tx rx pgt_acc]"); iFrameAutoSolve.
          { symmetry;done. }
          iNext. iIntros "(PC & mem_instr & r_dst & r_src & pgt_acc & tx & rx) _".
          iDestruct ("Hacc_regs" with "[$PC $r_src $r_dst]") as (regs') "[%Htotal_regs' regs]";iFrame.
          iDestruct ("Hacc_mem_acc_tx" with "mem_instr") as "mem_acc_tx".
          iCombine "rx rx_own rx_excl" as "rx".
          iApply ("IH" $! _ ps_acc trans _ Htotal_rxs Htotal_regs' Hsubset_mb Hsubset_acc Hnin_rx Hnin_tx with "regs tx pgt_tx rx pgt_acc pgt_owned
                       trans_hpool_global tran_pgt_transferred retri rx_state other_rx
                           tran_pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx] P").
          {
            iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx $mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
            iExists (<[ai:=a_src]> mem_acc_tx);iFrame "mem_acc_tx". iPureIntro. rewrite dom_insert_lookup_L. set_solver + Hdom_mem_acc_tx. eauto.
            iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
            set_solver +.
          }
        }
        { (* different addresses *)
          destruct (decide ((tpa w_dst)=(tpa ai))) as [Heqn'|].
          { (* in same page *)
            pose proof Hin_ps_acc_tx as Hin_ps_acc_tx'.
            rewrite <-Heqn' in Hin_ps_acc_tx'.
            pose proof (elem_of_memory_pages_lookup _ _ _ Hin_ps_acc_tx' Hdom_mem_acc_tx) as [w_src Hlookup_a_dst].
            iDestruct (mem_big_sepM_split_upd2 mem_acc_tx Hneq'' Hlookup_a_dst Hlookup_mem_ai with "[$mem_acc_tx]")
              as "[a_dst [mem_instr Hacc_mem_acc_tx]]".
            iDestruct "rx" as "(rx & rx_own & rx_excl)".
            iApply (str_same_page (s := ps_acc) (p := p_rx) ai w_dst src dst with "[PC mem_instr rx a_dst r_src r_dst tx pgt_acc]"); iFrameAutoSolve.
            done.
            iNext. iIntros "(PC & mem_instr & r_dst & a_dst & r_src & pgt_acc & tx & rx) _".
            iDestruct ("Hacc_regs" with "[$PC $r_src $r_dst]") as (regs') "[%Htotal_regs' regs]";iFrame.
            iDestruct ("Hacc_mem_acc_tx" with "[a_dst mem_instr]") as "mem_acc_tx"; iFrame.
            iCombine "rx rx_own rx_excl" as "rx".
            iApply ("IH" $! _ ps_acc trans _ Htotal_rxs Htotal_regs' Hsubset_mb Hsubset_acc Hnin_rx Hnin_tx with "regs tx pgt_tx rx pgt_acc pgt_owned
                       trans_hpool_global tran_pgt_transferred retri rx_state other_rx
                           tran_pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx] P").
            {
              iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx $mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
              iExists (<[w_dst:=a_src]> (<[ai:=instr]>mem_acc_tx)); iFrame "mem_acc_tx".
              iPureIntro. rewrite !dom_insert_lookup_L;eauto. rewrite lookup_insert_is_Some. right;done.
              iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
              set_solver +.
            }
          }
          { (* in difference pages *)
            (* getting mem *)
            destruct (decide (tpa w_dst = p_tx)).
            {
              iDestruct ("mem_tx") as "[%mem_tx [%Hdom_mem_tx mem_tx]]".
              rewrite -set_of_addr_singleton in Hdom_mem_tx.
              assert ( (tpa w_dst) ∈ ({[ p_tx ]}: gset _) ). set_solver + e.
              epose proof (elem_of_memory_pages_lookup _ w_dst _ H Hdom_mem_tx) as [w_src Hlookup_a_src];auto.
              iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "[$mem_acc_tx]") as "[mem_instr Hacc_mem_acc_tx]".
              iDestruct (mem_big_sepM_split_upd mem_tx Hlookup_a_src with "[$mem_tx]") as "[a_src Hacc_mem_tx]".
              iDestruct "rx" as "(rx & rx_own & rx_excl)".
              iApply (str (s := ps_acc) (p := p_rx) ai w_dst src dst with "[PC mem_instr a_src r_src r_dst rx tx pgt_acc]"); iFrameAutoSolve.
              { set_solver. }
              iNext. iIntros "(PC & mem_instr & r_dst & a_dst & r_src & pgt_acc & tx & rx) _".
              iCombine "rx rx_own rx_excl" as "rx".
              iDestruct ("Hacc_regs" with "[$PC $r_src $r_dst]") as (regs') "[%Htotal_regs' regs]";iFrame.
              iDestruct ("Hacc_mem_acc_tx" with "mem_instr") as "mem_acc_tx".
              iDestruct ("Hacc_mem_tx" with "a_dst") as "mem_tx".
              iApply ("IH" $! _ ps_acc trans _ Htotal_rxs Htotal_regs' Hsubset_mb Hsubset_acc Hnin_rx Hnin_tx with "regs tx pgt_tx rx pgt_acc pgt_owned
                       trans_hpool_global tran_pgt_transferred retri rx_state other_rx
                           tran_pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx] P").
              {
                iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
                iSplitL "mem_acc_tx".
                iExists mem_acc_tx; iFrame "mem_acc_tx". done.
                iExists (<[w_dst := a_src]> mem_tx). iFrame "mem_tx".
                iPureIntro. rewrite !dom_insert_lookup_L;eauto. rewrite -set_of_addr_singleton //.
                iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
                set_solver +.
              }
            }
            {
              assert (tpa w_dst ∈ ps_acc ∖ {[p_tx]}). set_solver + n1 Hin'.
              pose proof (elem_of_memory_pages_lookup _ _ _ H Hdom_mem_acc_tx) as [w_src Hlookup_a_src].
              iDestruct (mem_big_sepM_split_upd2 mem_acc_tx Hneq'' Hlookup_a_src Hlookup_mem_ai with "[$mem_acc_tx]")
                as "[a_src [mem_instr Hacc_mem_acc_tx]]".
              iDestruct "rx" as "(rx & rx_own & rx_excl)".
              iApply (str (s := ps_acc) (p := p_rx) ai w_dst src dst with "[PC mem_instr a_src r_src r_dst rx tx pgt_acc]"); iFrameAutoSolve.
              { set_solver. }
              iNext. iIntros "(PC & mem_instr & r_dst & a_dst & r_src & pgt_acc & tx & rx) _".
              iCombine "rx rx_own rx_excl" as "rx".
              iDestruct ("Hacc_regs" with "[$PC $r_src $r_dst]") as (regs') "[%Htotal_regs' regs]";iFrame.
              iDestruct ("Hacc_mem_acc_tx" with "[a_dst mem_instr]") as "mem_acc_tx"; iFrame.

              iApply ("IH" $! _ ps_acc trans _ Htotal_rxs Htotal_regs' Hsubset_mb Hsubset_acc Hnin_rx Hnin_tx with "regs tx pgt_tx rx pgt_acc pgt_owned
                       trans_hpool_global tran_pgt_transferred retri rx_state other_rx
                           tran_pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx] P").
              {
                iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx $mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
                iExists (<[w_dst:=a_src]> (<[ai:=instr]>mem_acc_tx)); iFrame "mem_acc_tx".
                iPureIntro. rewrite !dom_insert_lookup_L;eauto. rewrite lookup_insert_is_Some. right;done.
                iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
                set_solver +.
              }
            }
          }
        }
      }
    }
    { (* no access to the page, apply str_error *)
      (* getting mem *)
      (* we don't update memory *)
      iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "[$mem_acc_tx]")
        as "[mem_instr Hacc_mem_acc_tx]".
      iApply (str_no_access (s := ps_acc) ai w_dst src dst with "[PC mem_instr r_src r_dst tx pgt_acc]"); iFrameAutoSolve.
      iNext. iIntros "(PC & mem_instr & r_dst & pgt_acc & tx & r_src) _".
      by iApply wp_terminated.
    }
  Qed.

End ftlr_str.
