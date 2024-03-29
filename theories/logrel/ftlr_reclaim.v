From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang trans_extra.
From HypVeri.algebra Require Import base pagetable mem trans.
From HypVeri.rules Require Import mem_reclaim.
From HypVeri.logrel Require Import logrel logrel_extra.
From HypVeri Require Import proofmode.
Import uPred.

Section ftlr_reclaim.
  Context `{hypconst:HypervisorConstants}.
  Context `{hypparams:!HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.

Lemma ftlr_reclaim {i mem_acc_tx ai regs ps_acc p_tx p_rx instr trans rxs r0} P:
  (∀ trans trans' rxs rxs', delete i rxs = delete i rxs' -> except i trans = except i trans' ->
                            (∀ (x:VMID), x ≠ i -> trans_rel_secondary x trans trans') ->
                            P trans rxs ⊣⊢ P trans' rxs') ->
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
  decode_instruction instr = Some Hvc ->
  regs !! R0 = Some r0 ->
  decode_hvc_func r0 = Some Reclaim ->
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
    iIntros (P_eq Htotal_regs Htotal_rxs Hsubset_mb Hsubset_acc Hnin_rx Hnin_tx Hlookup_PC Hin_ps_acc Hneq_ptx Hdom_mem_acc_tx Hin_ps_acc_tx
                         Hlookup_mem_ai Heqn Hlookup_reg_R0).
    iIntros (Hdecode_hvc Hneq_mb) "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri rx_state rx other_rx
             tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx P".
    set ps_mem_in_trans := accessible_in_trans_memory_pages i trans.
    pose proof (Htotal_regs R1) as[r1 Hlookup_reg_R1].
    pose proof (Htotal_regs R2) as[r2 Hlookup_reg_R2].
    iDestruct (reg_big_sepM_split_upd4 i Hlookup_PC Hlookup_reg_R0 Hlookup_reg_R1 Hlookup_reg_R2 with "[$regs]")
      as "(PC & R0 & R1 & R2 & Hacc_regs)";eauto.
    iDestruct (get_trans_ps_disj with "trans_hpool_global") as %Hdisj_tran.
    iDestruct "trans_hpool_global" as (hpool) "(%Heq_hsall & fresh_handles & trans)".

    destruct (decide (r1 ∈ valid_handles)) as [Hin_hs_all |Hnotin_hs_all].
    2: { (* apply [mem_reclaim_invalid_handle] *)
      iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "mem_acc_tx") as "[mem_instr Hacc_mem_acc_tx]".

      iApply (mem_reclaim_invalid_handle ai with "[$PC $mem_instr $R0 $R1 $R2 $pgt_acc $tx]");auto.
      iNext. iIntros "(PC & mem_instr & R0 & R1 & R2 & pgt_acc & tx) _".

      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
      iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".

      iApply ("IH" $! _ _ trans _ Htotal_rxs Htotal_regs' with "[] [] [] [] regs tx pgt_tx rx pgt_acc pgt_owned [fresh_handles trans]
                            tran_pgt_transferred retri rx_state other_rx tran_pgt_owned
                             retri_owned [mem_rest mem_acc_tx mem_tx] P");auto.
      {
        iExists hpool.
        iSplitL "";auto. iFrame.
      }
      {
        iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx $mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
        iExists mem_acc_tx;by iFrame "mem_acc_tx".
        iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
        set_solver +.
      }
    }
    destruct (decide (r1 ∈ hpool)) as [Hin_hpool | Hnotin_hpool].
    { (* apply [mem_reclaim_fresh_handle] *)
      iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "mem_acc_tx") as "[mem_instr Hacc_mem_acc_tx]".

      iApply (mem_reclaim_fresh_handle ai with "[$PC $mem_instr $R0 $R1 $R2 $pgt_acc $tx $fresh_handles]");auto.
      iNext. iIntros "(PC & mem_instr & R0 & R1 & R2 & pgt_acc & tx & fresh_handles) _".

      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
      iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".

      iApply ("IH" $! _ _ trans _ Htotal_rxs Htotal_regs' with "[] [] [] [] regs tx pgt_tx rx pgt_acc pgt_owned [fresh_handles trans]
                            tran_pgt_transferred retri rx_state other_rx tran_pgt_owned
                            retri_owned [mem_rest mem_acc_tx mem_tx] P");auto.
      {
        iExists hpool.
        iSplitL "";auto. iFrame.
      }
      {
        iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx $mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
        iExists mem_acc_tx;by iFrame "mem_acc_tx".
        iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
        set_solver +.
      }
    }
    assert(r1 ∈ dom trans) as Hin_trans_dom.
    {
      rewrite -Heq_hsall in Hin_hs_all.
      rewrite elem_of_union in Hin_hs_all.
      destruct Hin_hs_all;first contradiction.
      done.
    }
    apply elem_of_dom in Hin_trans_dom as [tran Hlookup_tran].
    iDestruct (big_sepM_delete _ trans _  _ Hlookup_tran with "trans") as "([tran pgt_tran] & trans)".

    destruct(decide (tran.1.1.1.1 = i)) as [Heq_tran | Hneq_tran].
    2: { (*apply [mem_reclaim_invalid_trans]*)
      iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "mem_acc_tx") as "[mem_instr Hacc_mem_acc_tx]".

      iApply (mem_reclaim_invalid_trans ai with "[$PC $mem_instr $R0 $R1 $R2 $pgt_acc $tx $tran]");auto.
      iNext. iIntros "(PC & mem_instr & R0 & R1 & R2 & pgt_acc & tx & tran) _".

      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
      iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".

      iApply ("IH" $! _ _ trans _ Htotal_rxs Htotal_regs' with "[] [] [] [] regs tx pgt_tx rx pgt_acc pgt_owned [fresh_handles tran pgt_tran trans]
                            tran_pgt_transferred retri rx_state other_rx tran_pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx] P");auto.
      {
        iExists hpool.
        iSplitL "";auto.
        iFrame "fresh_handles".
        rewrite (big_sepM_delete _ trans).
        iFrame. done.
      }
      {
        iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx $mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
        iExists mem_acc_tx;by iFrame "mem_acc_tx".
        iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
        set_solver +.
      }
    }

    iDestruct ("retri") as "[retri retri']".
    iDestruct (big_sepFM_lookup_Some Hlookup_tran with "retri") as "[re retri]".
    left;done.

    destruct (tran.2) eqn:Heq_retri.
    { (* apply [mem_reclaim_retrieved] *)
      iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "mem_acc_tx") as "[mem_instr Hacc_mem_acc_tx]".

      iApply (mem_reclaim_retrieved ai with "[$PC $mem_instr $R0 $R1 $R2 $pgt_acc $tx $re]");auto.
      iNext. iIntros "(PC & mem_instr & R0 & R1 & R2 & pgt_acc & tx & re) _".

      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
      iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".

      iApply ("IH" $! _ _ trans _ Htotal_rxs Htotal_regs' with "[] [] [] [] regs tx pgt_tx rx pgt_acc pgt_owned [fresh_handles tran pgt_tran trans]
                            tran_pgt_transferred [re retri retri'] rx_state other_rx tran_pgt_owned
                            retri_owned [mem_rest mem_acc_tx mem_tx] P");auto.
      {
        iExists hpool.
        iSplitL "";auto.
        iFrame "fresh_handles".
        rewrite (big_sepM_delete _ trans).
        iFrame. done.
      }
      {
        rewrite /retrievable_transaction_transferred.
        iDestruct (big_sepFM_delete_acc_True tran with "retri") as "retri".
        left;done.
        rewrite Heq_retri.
        iDestruct ("retri" with "re") as "retri".
        rewrite insert_id;auto.
        iFrame.
      }
      {
        iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx $mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
        iExists mem_acc_tx;by iFrame "mem_acc_tx".
        iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
        set_solver +.
      }
    }

    assert(tran.1 = (i, tran.1.1.1.2, tran.1.1.2, tran.1.2)) as Hrw_tran.
    {
      rewrite -Heq_tran.
      repeat destruct tran as [tran ?]. simpl. done.
    }
    rewrite Hrw_tran.

    iDestruct (big_sepFM_lookup_Some Hlookup_tran with "retri'") as "[[tran'' re'] retri']".
    simpl. split;auto.
    rewrite Heq_retri.
    iDestruct (retri_split with "[$re $re']") as "re".

    assert (tran.1.1.2 ⊆ ps_mem_in_trans) as Hsubseteq_tran.
    {
      rewrite elem_of_subseteq.
      intros p Hin_p.
      rewrite /ps_mem_in_trans.
      rewrite elem_of_pages_in_trans.
      exists r1, tran.
      split;last auto.
      rewrite map_filter_lookup_Some;split;first done.
      simpl. left. split;auto. intros [? _]. rewrite H // in Heq_retri.
    }

    assert (p_rx ∈ ps_acc ∖ {[p_tx]}) as Hin_ps_acc_tx'. set_solver + Hsubset_mb Hneq_mb.
    (* assert (pages_in_trans (delete r1 trans) = pages_in_trans trans ∖ tran.1.1.2) as Hrewrite. *)
    (*   apply pages_in_trans_delete;auto. *)

    assert (accessible_in_trans_memory_pages i (delete r1 trans) = ps_mem_in_trans ∖ tran.1.1.2) as Hrewrite.
    {
      rewrite /accessible_in_trans_memory_pages.
      rewrite map_filter_delete.
      apply pages_in_trans_delete.
      rewrite map_filter_lookup_Some.
      split;first done.
      simpl. left. split;auto. intros [? _]. rewrite H // in Heq_retri.
      apply (trans_ps_disj_subseteq trans).
      done.
      apply map_filter_subseteq.
    }

    destruct (tran.1.2) eqn:Heq_tran_tt.
    { (* apply [mem_reclaim_donate] *)
    iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "mem_acc_tx") as "[mem_instr Hacc_mem_acc_tx]".
    iDestruct (big_sepFM_lookup_Some Hlookup_tran with "tran_pgt_transferred") as "[[tran' oe_tran] tran_pgt_transferred]".
    simpl. split;last done. eauto.
    rewrite Hrw_tran; clear Hrw_tran.

    iDestruct (trans_split with "[tran' tran'']") as "tran'".
    { rewrite -half_of_half. iFrame. }
    iDestruct (trans_split with "[$tran $tran']") as "tran".

    iApply (mem_reclaim_donate ai with "[$PC $mem_instr $R0 $R1 $tx $pgt_acc $re $tran $fresh_handles]");auto.
    iNext. simpl. iIntros "(PC & mem_instr & R0 & R1 & pgt_acc & tx & fresh_handles) _".

    iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
    iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".

    iApply ("IH" $! _ _ (delete r1 trans) _ Htotal_rxs Htotal_regs' with "[] [] [] [] regs tx pgt_tx rx pgt_acc [oe_tran pgt_tran pgt_owned]
                            [fresh_handles trans] [tran_pgt_transferred] [retri retri'] rx_state other_rx [tran_pgt_owned]
                             [retri_owned] [mem_rest mem_acc_tx mem_tx] [P]").
    {
      iPureIntro.
      set_solver + Hsubset_mb.
    }
    {
      iPureIntro.
      rewrite (currently_accessible_in_trans_memory_pages_delete_False i trans r1 _ Hlookup_tran) /=;auto.
      set_solver + Hsubset_acc.
      intros [[]|[]]. rewrite H0 in Heq_tran_tt. inversion Heq_tran_tt. rewrite H0 // in Heq_retri.
    }
    {
      iPureIntro.
      rewrite Hrewrite.
      rewrite union_comm_L.
      rewrite difference_union_distr_l_L.
      set_solver + Hsubseteq_tran Hnin_rx.
    }
    {
      iPureIntro.
      rewrite Hrewrite.
      rewrite union_comm_L.
      rewrite difference_union_distr_l_L.
      set_solver + Hsubseteq_tran Hnin_tx.
    }
    {
      assert (currently_accessible_in_trans_memory_pages i (delete r1 trans) = currently_accessible_in_trans_memory_pages i trans) as Hrewrite'.
      {
        rewrite (currently_accessible_in_trans_memory_pages_delete_False i trans r1 _ Hlookup_tran) /=;auto.
        intros [[]|[]]. rewrite H0 in Heq_tran_tt. inversion Heq_tran_tt. rewrite H0 // in Heq_retri.
      }
      rewrite Hrewrite'.
      rewrite (union_comm_L _ tran.1.1.2).
      rewrite (difference_union_distr_l_L tran.1.1.2).
      assert (tran.1.1.2 ∖ {[p_rx;p_tx]} = tran.1.1.2) as ->.
      set_solver + Hnin_rx Hnin_tx Hsubseteq_tran.
      rewrite (difference_union_distr_l_L tran.1.1.2).
      assert (tran.1.1.2 ∖ currently_accessible_in_trans_memory_pages i trans = tran.1.1.2) as ->.
      { feed pose proof (currently_accessible_in_trans_memory_pages_lookup_False i trans r1 _ Hlookup_tran).
        intros [[]|[]]. rewrite H0 in Heq_tran_tt. inversion Heq_tran_tt. rewrite H0 // in Heq_retri.
        done.
        set_solver + H.
      }
      case_bool_decide;last done.
      iDestruct (pgt_split_quarter with "[$oe_tran $pgt_tran]") as "pgt_tran".
      iApply (big_sepS_union_2 with "pgt_tran pgt_owned").
    }
    {
      iExists (hpool ∪ {[r1]}).
      iFrame "fresh_handles trans".
      iPureIntro.
      assert (r1 ∈ dom trans).
      {
        rewrite elem_of_dom.
        exists tran;done.
      }
      rewrite union_comm_L in Heq_hsall.
      rewrite -Heq_hsall.
      rewrite union_comm_L.
      rewrite (union_comm_L hpool).
      rewrite union_assoc_L.
      f_equal.
      rewrite dom_delete_L.
      rewrite difference_union_L.
      set_solver + H.
    }
    {
      rewrite /transaction_pagetable_entries_transferred.
      done.
    }
    {
      rewrite /retrievable_transaction_transferred.
      iFrame "retri retri'".
    }
    {
      rewrite /transaction_pagetable_entries_owned.
      rewrite (big_sepFM_delete_False Hlookup_tran).
      iFrame "tran_pgt_owned".
      simpl. intros [_ ?]. contradiction.
    }
    {
      rewrite /retrieved_transaction_owned.
      rewrite -big_sepFM_delete_False;auto.
      apply Hlookup_tran.
      simpl. intro; destruct H. rewrite Heq_retri // in H0.
    }
    {
      rewrite Hrewrite.
      rewrite -(union_assoc_L ps_acc tran.1.1.2).
      rewrite -(union_difference_L tran.1.1.2);last set_solver + Hsubseteq_tran.
      iApply (memory_pages_split_diff' _ ps_acc).
      set_solver +.
      iSplitL "mem_rest"; first done.
      iApply (memory_pages_split_singleton' p_tx with "[mem_acc_tx mem_tx]").
      set_solver + Hsubset_mb.
      iSplitL "mem_acc_tx";last done.
      iExists mem_acc_tx; iFrame "mem_acc_tx";done.
    }
    {
      iApply (P_eq with "P"). done.
      symmetry. eapply except_delete_False. done. left;done.
      intros.
      destruct (decide (x = tran.1.1.1.1)).
      subst x.
      split.
      rewrite map_filter_delete_not /=. done.
      intros ? ?.
      intros [_ ?].
      rewrite H0 in Hlookup_tran. inversion Hlookup_tran. subst y. auto.
      rewrite map_filter_delete_not /=. auto.
      intros ? ?.
      intros [? _].
      rewrite H0 in Hlookup_tran. inversion Hlookup_tran. subst y.
      auto.
      split.
      rewrite map_filter_delete_not /=. auto.
      intros ? ?.
      intros [_ ?]. rewrite H0 in Hlookup_tran. inversion Hlookup_tran. subst y. auto.
      rewrite map_filter_delete_not /=. auto.
      intros ? ?.
      intros [_ ?]. rewrite H0 in Hlookup_tran. inversion Hlookup_tran. subst y.
      rewrite Heq_retri in H1.  inversion H1.
    }
    }
    { (* apply [mem_reclaim_share] *)
    iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "mem_acc_tx") as "[mem_instr Hacc_mem_acc_tx]".
    iDestruct (big_sepFM_lookup_Some Hlookup_tran with "tran_pgt_owned") as "[[tran' oe_tran] tran_pgt_owned]".
    simpl. split;first done. rewrite Heq_tran_tt //.
    rewrite Hrw_tran; clear Hrw_tran.
    iDestruct (trans_split with "[tran' tran'']") as "tran'".
    { rewrite -half_of_half. iFrame. }
    iDestruct (trans_split with "[$tran $tran']") as "tran".
    simpl. case_bool_decide;first contradiction.

    iDestruct (pgt_split_quarter with "[$pgt_tran $oe_tran]") as "pgt_tran".
    iDestruct (big_sepS_sep with "pgt_tran") as "[own_tran excl_tran]".

    iApply (mem_reclaim_share ai r1 with "[$PC $mem_instr $R0 $R1 $pgt_acc $tx $excl_tran $re $tran $fresh_handles]");auto.
    iNext. simpl. iIntros "(PC & mem_instr & R0 & R1 & pgt_acc & excl_tran & tx & fresh_handles) _".

    iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
    iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".

    iApply ("IH" $! _ _ (delete r1 trans) _ Htotal_rxs Htotal_regs' with "[] [] [] [] regs tx pgt_tx rx pgt_acc [own_tran excl_tran pgt_owned] [fresh_handles trans]
                            [tran_pgt_transferred] [retri retri'] rx_state other_rx [tran_pgt_owned]
                            [retri_owned] [mem_rest mem_acc_tx mem_tx] [P]").
    {
      iPureIntro.
      set_solver + Hsubset_mb.
    }
    {
      iPureIntro.
      rewrite (currently_accessible_in_trans_memory_pages_delete_True i trans r1 _ Hlookup_tran) //=.
      feed pose proof (accessible_in_trans_memory_pages_lookup_True i trans r1 _ Hlookup_tran).
      left;split;auto. intros []. rewrite H0 // in Heq_retri.
      set_solver + Hsubset_acc Hnin_rx Hnin_tx H0.
      left;split;auto.
    }
    {
      iPureIntro.
      rewrite Hrewrite.
      set_solver + Hsubseteq_tran Hnin_rx.
    }
    {
      iPureIntro.
      rewrite Hrewrite.
      set_solver + Hsubseteq_tran Hnin_tx.
    }
    {
      assert (currently_accessible_in_trans_memory_pages i (delete r1 trans) = currently_accessible_in_trans_memory_pages i trans ∖ tran.1.1.2) as Hrewrite'.
      {
        rewrite (currently_accessible_in_trans_memory_pages_delete_True i trans r1 _ Hlookup_tran) //=.
        left;split;done.
      }
      rewrite Hrewrite'.
      rewrite (union_comm_L _ tran.1.1.2).
      rewrite (difference_union_distr_l_L tran.1.1.2).
      assert (tran.1.1.2 ∖ {[p_rx;p_tx]} = tran.1.1.2) as ->.
      set_solver + Hnin_rx Hnin_tx Hsubseteq_tran.
      assert ((tran.1.1.2 ∪ ps_acc ∖ {[p_rx; p_tx]}) ∖ (currently_accessible_in_trans_memory_pages i trans ∖ tran.1.1.2) =
             (tran.1.1.2 ∪ ps_acc ∖ {[p_rx; p_tx]}) ∖ (currently_accessible_in_trans_memory_pages i trans) ∪ tran.1.1.2) as ->.
      {
        rewrite difference_difference_union. done.
        set_solver +.
      }
      rewrite (difference_union_distr_l_L tran.1.1.2).
      assert (tran.1.1.2 ∖ (currently_accessible_in_trans_memory_pages i trans) = ∅) as ->.
      {
        feed pose proof (currently_accessible_in_trans_memory_pages_lookup_True i trans r1 _ Hlookup_tran).
        left;split;done.
        set_solver + H0.
      }
      rewrite union_empty_l_L.

      iDestruct (big_sepS_sep with "[$own_tran $excl_tran]") as "pgt_tran".
      iApply (big_sepS_union_2 with "pgt_owned pgt_tran").
    }
    {
      iExists (hpool ∪ {[r1]}).
      iFrame "fresh_handles trans".
      iPureIntro.
      assert (r1 ∈ dom trans).
      {
        rewrite elem_of_dom.
        exists tran;done.
      }
      rewrite union_comm_L in Heq_hsall.
      rewrite -Heq_hsall.
      rewrite union_comm_L.
      rewrite (union_comm_L hpool).
      rewrite union_assoc_L.
      f_equal.
      rewrite dom_delete_L.
      rewrite difference_union_L.
      set_solver + H0.
    }
    {
      rewrite /transaction_pagetable_entries_transferred.
      rewrite (big_sepFM_delete_False Hlookup_tran).
      iFrame "tran_pgt_transferred".
      simpl. intros [_ ?]. rewrite Heq_tran_tt in H0; inversion H0.
    }
    {
      rewrite /retrievable_transaction_transferred.
      iFrame "retri retri'".
    }
    {
      rewrite /transaction_pagetable_entries_owned.
      iFrame.
    }
    {
      rewrite /retrieved_transaction_owned.
      rewrite -big_sepFM_delete_False;auto.
      apply Hlookup_tran.
      simpl. intros [_ ?]. rewrite Heq_retri // in H0.
    }
    {
      rewrite Hrewrite.
      rewrite -(union_assoc_L ps_acc tran.1.1.2).
      rewrite -(union_difference_L tran.1.1.2);last set_solver + Hsubseteq_tran.
      iApply (memory_pages_split_diff' _ ps_acc).
      set_solver +.
      iSplitL "mem_rest"; first done.
      iApply (memory_pages_split_singleton' p_tx with "[mem_acc_tx mem_tx]").
      set_solver + Hsubset_mb.
      iSplitL "mem_acc_tx";last done.
      iExists mem_acc_tx; iFrame "mem_acc_tx";done.
    }
    {
      iApply (P_eq with "P"). done.
      symmetry. eapply except_delete_False. done. left;done.
      intros.
      destruct (decide (x = tran.1.1.1.1)).
      subst x.
      rewrite Heq_tran in H0.
      exfalso. apply H0. auto.
      split.
      rewrite map_filter_delete_not /=. auto.
      intros ? ?.
      intros [? _]. rewrite H1 in Hlookup_tran. inversion Hlookup_tran. subst y. auto.
      rewrite map_filter_delete_not /=. auto.
      intros ? ?.
      intros [_ ?]. rewrite H1 in Hlookup_tran. inversion Hlookup_tran. subst y.
      rewrite Heq_retri in H2.  inversion H2.
    }
    }
    { (* apply [mem_reclaim_lend] *)
    iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "mem_acc_tx") as "[mem_instr Hacc_mem_acc_tx]".
    iDestruct (big_sepFM_lookup_Some Hlookup_tran with "tran_pgt_owned") as "[[tran' oe_tran] tran_pgt_owned]".
    simpl. split;first done. rewrite Heq_tran_tt //.
    rewrite Hrw_tran; clear Hrw_tran.
    iDestruct (trans_split with "[tran' tran'']") as "tran'".
    { rewrite -half_of_half. iFrame. }
    iDestruct (trans_split with "[$tran $tran']") as "tran".
    simpl. case_bool_decide. 2: inversion H.

    iApply (mem_reclaim_lend ai r1 with "[$PC $mem_instr $R0 $R1 $pgt_acc $tx $re $tran $fresh_handles]");auto.
    iNext. simpl. iIntros "(PC & mem_instr & R0 & R1 & pgt_acc & tx & fresh_handles) _".

    iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
    iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".

    iApply ("IH" $! _ _ (delete r1 trans) _ Htotal_rxs Htotal_regs' with "[] [] [] [] regs tx pgt_tx rx pgt_acc [oe_tran pgt_tran pgt_owned] [fresh_handles trans]
                            [tran_pgt_transferred] [retri retri'] rx_state other_rx [tran_pgt_owned]
                            [retri_owned] [mem_rest mem_acc_tx mem_tx] [P]").
    {
      iPureIntro.
      set_solver + Hsubset_mb.
    }
    {
      iPureIntro.
      rewrite (currently_accessible_in_trans_memory_pages_delete_False i trans r1 _ Hlookup_tran) //=.
      feed pose proof (accessible_in_trans_memory_pages_lookup_True i trans r1 _ Hlookup_tran).
      left;split;auto. intros []. rewrite H0 // in Heq_retri.
      set_solver + Hsubset_acc Hnin_rx Hnin_tx H0.
      intros [[]|[]]. rewrite H1 in Heq_tran_tt. inversion Heq_tran_tt. rewrite H1 //in Heq_retri.
    }
    {
      iPureIntro.
      rewrite Hrewrite.
      set_solver + Hsubseteq_tran Hnin_rx.
    }
    {
      iPureIntro.
      rewrite Hrewrite.
      set_solver + Hsubseteq_tran Hnin_tx.
    }
    {
      rewrite (currently_accessible_in_trans_memory_pages_delete_False i trans r1 _ Hlookup_tran) //.
      2: { intros [[]|[]]. rewrite H1 in Heq_tran_tt. inversion Heq_tran_tt. rewrite H1 //in Heq_retri. }
      rewrite (union_comm_L _ tran.1.1.2).
      rewrite (difference_union_distr_l_L tran.1.1.2).
      assert (tran.1.1.2 ∖ {[p_rx;p_tx]} = tran.1.1.2) as ->.
      set_solver + Hnin_rx Hnin_tx Hsubseteq_tran.
      rewrite (difference_union_distr_l_L tran.1.1.2).
      assert (tran.1.1.2 ∖ currently_accessible_in_trans_memory_pages i trans = tran.1.1.2) as ->.
      {
        feed pose proof (currently_accessible_in_trans_memory_pages_lookup_False i trans r1 _ Hlookup_tran).
        intros [[]|[]]. rewrite H1 in Heq_tran_tt. inversion Heq_tran_tt. rewrite H1 //in Heq_retri.
        done.
        set_solver + H0.
      }
      iDestruct (pgt_split_quarter with "[$pgt_tran $oe_tran]") as "pgt_tran".
      iApply (big_sepS_union_2 with "pgt_tran pgt_owned").
    }
    {
      iExists (hpool ∪ {[r1]}).
      iFrame "fresh_handles trans".
      iPureIntro.
      assert (r1 ∈ dom trans).
      {
        rewrite elem_of_dom.
        exists tran;done.
      }
      rewrite union_comm_L in Heq_hsall.
      rewrite -Heq_hsall.
      rewrite union_comm_L.
      rewrite (union_comm_L hpool).
      rewrite union_assoc_L.
      f_equal.
      rewrite dom_delete_L.
      rewrite difference_union_L.
      set_solver + H0.
    }
    {
      rewrite /transaction_pagetable_entries_transferred.
      rewrite (big_sepFM_delete_False Hlookup_tran).
      iFrame "tran_pgt_transferred".
      simpl. intros [_ ?]. rewrite Heq_tran_tt in H0; inversion H0.
    }
    {
      rewrite /retrievable_transaction_transferred.
      iFrame "retri retri'".
    }
    {
      rewrite /transaction_pagetable_entries_owned.
      iFrame.
    }
    {
      rewrite /retrieved_transaction_owned.
      rewrite -big_sepFM_delete_False;auto.
      apply Hlookup_tran.
      simpl. intros [_ ?]. rewrite Heq_retri // in H0.
    }
    {
      rewrite Hrewrite.
      rewrite -(union_assoc_L ps_acc tran.1.1.2).
      rewrite -(union_difference_L tran.1.1.2);last set_solver + Hsubseteq_tran.
      iApply (memory_pages_split_diff' _ ps_acc).
      set_solver +.
      iSplitL "mem_rest"; first done.
      iApply (memory_pages_split_singleton' p_tx with "[mem_acc_tx mem_tx]").
      set_solver + Hsubset_mb.
      iSplitL "mem_acc_tx";last done.
      iExists mem_acc_tx; iFrame "mem_acc_tx";done.
    }
    {
      iApply (P_eq with "P"). done.
      symmetry. eapply except_delete_False. done. left;done.
      intros.
      destruct (decide (x = tran.1.1.1.1)).
      subst x.
      rewrite Heq_tran in H0.
      exfalso. apply H0. auto.
      split.
      rewrite map_filter_delete_not /=. auto.
      intros ? ?.
      intros [? _]. rewrite H1 in Hlookup_tran. inversion Hlookup_tran. subst y. auto.
      rewrite map_filter_delete_not /=. auto.
      intros ? ?.
      intros [_ ?]. rewrite H1 in Hlookup_tran. inversion Hlookup_tran. subst y.
      rewrite Heq_retri in H2.  inversion H2.
    }
    }
  Qed.

End ftlr_reclaim.
