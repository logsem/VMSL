From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang trans_extra.
From HypVeri.algebra Require Import base pagetable mem trans.
From HypVeri.rules Require Import mem_reclaim.
From HypVeri.logrel Require Import logrel logrel_extra.
From HypVeri Require Import proofmode stdpp_extra.
Import uPred.

Section ftlr_reclaim.
  Context `{hypconst:HypervisorConstants}.
  Context `{hypparams:!HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.

Lemma ftlr_reclaim {i trans' mem_acc_tx ai regs ps_acc p_tx p_rx ps_na instr trans rx_state r0}:
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
  decode_hvc_func r0 = Some Reclaim ->
  p_tx ≠ p_rx ->
  ⊢
  ▷ (∀ (a : gmap reg_name Addr) (a0 a1: gset PID) (a2 a3: gmap Addr transaction) (a4 : option (Addr * VMID)),
          ⌜base_extra.is_total_gmap a⌝
            → ⌜{[p_tx; p_rx]} ⊆ a1⌝
              → ⌜a0 ## a1 ∪ pages_in_trans (trans_memory_in_trans i a3)⌝
                → ⌜p_rx ∉ a1 ∖ {[p_rx; p_tx]} ∪ pages_in_trans (trans_memory_in_trans i a3)⌝
                  → ⌜p_tx ∉ a1 ∖ {[p_rx; p_tx]} ∪ pages_in_trans (trans_memory_in_trans i a3)⌝
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
                      ▷ VMProp V0 (vmprop_zero i p_tx p_rx) (1 / 2) -∗
                      VMProp i (vmprop_unknown i p_tx p_rx a2) 1 -∗
                      transaction_pagetable_entries_owned i a3 -∗
                      pagetable_entries_excl_owned i (a1 ∖ {[p_rx; p_tx]} ∖ (pages_in_trans (trans_memory_in_trans i a3))) -∗
                      retrieval_entries_owned i a3 -∗
                      (∃ mem : lang.mem, memory_pages (a1 ∪ pages_in_trans (trans_memory_in_trans i a3)) mem) -∗
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
   ▷ VMProp V0 (vmprop_zero i p_tx p_rx) (1 / 2) -∗
   VMProp i (vmprop_unknown i p_tx p_rx trans') 1 -∗
   transaction_pagetable_entries_owned i trans -∗
   pagetable_entries_excl_owned i (ps_acc ∖ {[p_rx; p_tx]} ∖ pages_in_trans (trans_memory_in_trans i trans)) -∗
   retrieval_entries_owned i trans -∗
   (∃ mem1 : mem, memory_pages ((ps_acc ∪ (pages_in_trans (trans_memory_in_trans i trans))) ∖ ps_acc) mem1) -∗
   ([∗ map] k↦v ∈ mem_acc_tx, k ->a v) -∗
   (∃ mem2 : mem, memory_page p_tx mem2) -∗
   SSWP ExecI @ i {{ bm, (if bm.1 then VMProp_holds i (1 / 2) else True) -∗ WP bm.2 @ i {{ _, True }} }}.
  Proof.
    iIntros (Htotal_regs Hsubset_mb Hdisj_na Hnin_rx Hnin_tx Hlookup_PC Hin_ps_acc Hneq_ptx Hdom_mem_acc_tx Hin_ps_acc_tx
                         Hlookup_mem_ai Heqn  Hlookup_reg_R0 Hdecode_hvc).
    iIntros (Hneq_mb) "IH regs tx pgt_tx pgt_acc pgt_acc' LB trans_hpool_global tran_pgt_transferred retri R0z R1z R2z rx_state rx other_rx prop0
             propi tran_pgt_owned pgt_owned retri_owned mem_rest mem_acc_tx mem_tx".
    set ps_mem_in_trans := (pages_in_trans (trans_memory_in_trans i trans)).
    pose proof (Htotal_regs R1) as[r1 Hlookup_reg_R1].
    pose proof (Htotal_regs R2) as[r2 Hlookup_reg_R2].
    iDestruct (reg_big_sepM_split_upd4 i Hlookup_PC Hlookup_reg_R0 Hlookup_reg_R1 Hlookup_reg_R2 with "[$regs]")
      as "(PC & R0 & R1 & R2 & Hacc_regs)";eauto.
    iDestruct (access_split with "[$pgt_acc $pgt_acc']") as "pgt_acc".
    iDestruct "trans_hpool_global" as (hpool) "(%Heq_hsall & fresh_handles & %Htrans_ps_disj & trans)".


    destruct (decide (r1 ∈ valid_handles)) as [Hin_hs_all |Hnotin_hs_all].
    2: { (* apply [mem_reclaim_invalid_handle] *)
      iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "mem_acc_tx") as "[mem_instr Hacc_mem_acc_tx]".

      iApply (mem_reclaim_invalid_handle ai with "[$PC $mem_instr $R0 $R1 $R2 $pgt_acc $tx]");auto.
      iNext.
      iIntros "(PC & mem_instr & R0 & R1 & R2 & pgt_acc & tx) _".

      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
      iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
      iDestruct (access_split with "pgt_acc") as "[pgt_acc pgt_acc']".

      iApply ("IH" $! _ _ _ _ trans _ Htotal_regs' with "[] [] [] [] regs tx pgt_tx pgt_acc pgt_acc' LB [fresh_handles trans]
                            tran_pgt_transferred retri R0z R1z R2z rx_state rx other_rx prop0 propi tran_pgt_owned
                            pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx]");auto.
      {
        iExists hpool.
        iSplitL "";auto.
        iFrame "fresh_handles".
        iSplitL "";auto.
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
      iNext.
      iIntros "(PC & mem_instr & R0 & R1 & R2 & pgt_acc & tx & fresh_handles) _".

      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
      iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
      iDestruct (access_split with "pgt_acc") as "[pgt_acc pgt_acc']".

      iApply ("IH" $! _ _ _ _ trans _ Htotal_regs' with "[] [] [] [] regs tx pgt_tx pgt_acc pgt_acc' LB [fresh_handles trans]
                            tran_pgt_transferred retri R0z R1z R2z rx_state rx other_rx prop0 propi tran_pgt_owned
                            pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx]");auto.
      {
        iExists hpool.
        iSplitL "";auto.
        iFrame "fresh_handles".
        iSplitL "";auto.
      }
      {
        iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx $mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
        iExists mem_acc_tx;by iFrame "mem_acc_tx".
        iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
        set_solver +.
      }
    }
    assert(r1 ∈ dom (gset _ ) trans) as Hin_trans_dom.
    {
      rewrite -Heq_hsall in Hin_hs_all.
      rewrite elem_of_union in Hin_hs_all.
      destruct Hin_hs_all;first contradiction.
      done.
    }
    apply elem_of_dom in Hin_trans_dom as [tran Hlookup_tran].
    iDestruct (big_sepM_delete _ trans _  _ Hlookup_tran with "trans") as "(tran & trans)".

    destruct(decide (tran.1.1.1.1 = i)) as [Heq_tran | Hneq_tran].
    2: { (*apply [mem_reclaim_invalid_trans]*)
      iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "mem_acc_tx") as "[mem_instr Hacc_mem_acc_tx]".

      iApply (mem_reclaim_invalid_trans ai with "[$PC $mem_instr $R0 $R1 $R2 $pgt_acc $tx $tran]");auto.
      iNext.
      iIntros "(PC & mem_instr & R0 & R1 & R2 & pgt_acc & tx & tran) _".

      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
      iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
      iDestruct (access_split with "pgt_acc") as "[pgt_acc pgt_acc']".

      iApply ("IH" $! _ _ _ _ trans _ Htotal_regs' with "[] [] [] [] regs tx pgt_tx pgt_acc pgt_acc' LB [fresh_handles tran trans]
                            tran_pgt_transferred retri R0z R1z R2z rx_state rx other_rx prop0 propi tran_pgt_owned
                            pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx]");auto.
      {
        iExists hpool.
        iSplitL "";auto.
        iFrame "fresh_handles".
        iSplitL "";auto.
        rewrite (big_sepM_delete _ trans).
        iSplitL "tran".
        iExact "tran".
        done.
        done.
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
    simpl;right;done.

    destruct (tran.2) eqn:Heq_retri.
    { (* apply [mem_reclaim_retrieved] *)
      iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "mem_acc_tx") as "[mem_instr Hacc_mem_acc_tx]".

      iApply (mem_reclaim_retrieved ai with "[$PC $mem_instr $R0 $R1 $R2 $pgt_acc $tx $re]");auto.
      iNext.
      iIntros "(PC & mem_instr & R0 & R1 & R2 & pgt_acc & tx & re) _".

      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
      iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
      iDestruct (access_split with "pgt_acc") as "[pgt_acc pgt_acc']".

      iApply ("IH" $! _ _ _ _ trans _ Htotal_regs' with "[] [] [] [] regs tx pgt_tx pgt_acc pgt_acc' LB [fresh_handles tran trans]
                            tran_pgt_transferred [re retri retri'] R0z R1z R2z rx_state rx other_rx prop0 propi tran_pgt_owned
                            pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx]");auto.
      {
        iExists hpool.
        iSplitL "";auto.
        iFrame "fresh_handles".
        iSplitL "";auto.
        rewrite (big_sepM_delete _ trans).
        iSplitL "tran".
        iExact "tran".
        done.
        done.
      }
      {
        rewrite /retrieval_entries_transferred.
        iDestruct (big_sepFM_delete_acc_True tran with "retri") as "retri".
        simpl. right;done.
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

    iDestruct (big_sepFM_lookup_Some Hlookup_tran with "retri'") as "[re' retri']".
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

    assert (pages_in_trans (trans_memory_in_trans i (delete r1 trans)) = ps_mem_in_trans ∖ tran.1.1.2) as Hrewrite.
    {
      rewrite /trans_memory_in_trans.
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
    iDestruct (big_sepFM_lookup_Some Hlookup_tran with "tran_pgt_transferred") as "[[tran' [own_tran excl_tran]] tran_pgt_transferred]".
    simpl. split;first done. eauto.
    rewrite Hrw_tran; clear Hrw_tran.
    iDestruct (trans_split with "[$tran $tran']") as "tran".

    iApply (mem_reclaim_donate ai with "[$PC $mem_instr $R0 $R1 $tx $pgt_acc $re $tran $fresh_handles]");auto.
    iNext. simpl.
    iIntros "(PC & mem_instr & R0 & R1 & pgt_acc & tx & fresh_handles) _".

    iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
    iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
    iDestruct (access_split with "pgt_acc") as "[pgt_acc pgt_acc']".

    iApply ("IH" $! _ _ _ _ (delete r1 trans) _ Htotal_regs' with "[] [] [] [] regs tx pgt_tx pgt_acc pgt_acc' LB [fresh_handles trans]
                            [tran_pgt_transferred] [retri retri'] R0z R1z R2z rx_state rx other_rx prop0 propi [tran_pgt_owned]
                            [own_tran excl_tran pgt_owned] [retri_owned] [mem_rest mem_acc_tx mem_tx]").
    {
      iPureIntro.
      set_solver + Hsubset_mb.
    }
    {
      iPureIntro.
      rewrite Hrewrite.
      rewrite union_comm_L.
      rewrite union_assoc_L.
      set_solver + Hdisj_na Hsubseteq_tran.
    }
    {
      iPureIntro.
      rewrite Hrewrite.
      rewrite union_comm_L.
      rewrite difference_union_distr_l_L.
      set_solver + Hdisj_na Hsubseteq_tran Hnin_rx.
    }
    {
      iPureIntro.
      rewrite Hrewrite.
      rewrite union_comm_L.
      rewrite difference_union_distr_l_L.
      set_solver + Hdisj_na Hsubseteq_tran Hnin_tx.
    }
    {
      iExists (hpool ∪ {[r1]}).
      iFrame "fresh_handles trans".
      iPureIntro.
      assert (r1 ∈ dom (gset _) trans).
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
      split.
      set_solver + H.
      apply (trans_ps_disj_subseteq trans).
      done.
      apply map_subseteq_delete.
    }
    {
      rewrite /transaction_pagetable_entries_transferred.
      done.
    }
    {
      rewrite /retrieval_entries_transferred.
      iFrame "retri retri'".
    }
    {
      rewrite /transaction_pagetable_entries_owned.
      rewrite (big_sepFM_delete_False Hlookup_tran).
      iFrame "tran_pgt_owned".
      simpl.
      intros [_ ?].
      contradiction.
    }
    {
      rewrite Hrewrite.
      rewrite (union_comm_L _ tran.1.1.2).
      rewrite (difference_union_distr_l_L tran.1.1.2).
      assert (tran.1.1.2 ∖ {[p_rx;p_tx]} = tran.1.1.2) as ->.
      set_solver + Hnin_rx Hnin_tx Hsubseteq_tran.
      rewrite (difference_union_distr_l_L tran.1.1.2).
      assert (tran.1.1.2 ∖ (ps_mem_in_trans ∖ tran.1.1.2) = tran.1.1.2) as ->.
      set_solver + Hsubseteq_tran.
      assert (tran.1.1.2 ∪ ps_acc ∖ {[p_rx; p_tx]} ∖ (ps_mem_in_trans ∖ tran.1.1.2) = tran.1.1.2 ∪ ps_acc ∖ {[p_rx; p_tx]} ∖ ps_mem_in_trans) as ->.
      set A := (ps_acc ∖ {[p_rx; p_tx]}).
      set G := (tran.1.1.2 ∪ A ∖ (ps_mem_in_trans ∖ tran.1.1.2)).

      rewrite (union_difference_L tran.1.1.2 ps_mem_in_trans).
      2: {
        set_solver + Hsubseteq_tran.
      }
      rewrite difference_union_distr_r_L.
      rewrite union_intersection_l_L.
      rewrite (union_comm_L tran.1.1.2).
      rewrite difference_union_L.
      rewrite intersection_comm_L.
      symmetry.
      rewrite /G.
      rewrite subseteq_intersection_1_L. done.
      set_solver +.
      iDestruct "pgt_owned" as "[own_owned excl_owned]".
      iSplitL "own_owned own_tran".
      iApply (big_sepS_union with "[$own_tran $own_owned]").
      set_solver + Hsubseteq_tran.
      iApply (big_sepS_union with "[$excl_tran $excl_owned]").
      set_solver + Hsubseteq_tran.
    }
    {
      rewrite /retrieval_entries_owned.
      rewrite -big_sepFM_delete_False;auto.
      apply Hlookup_tran.
      simpl.
      intro; destruct H. rewrite Heq_retri // in H0.
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
    }
    { (* apply [mem_reclaim_share] *)
    iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "mem_acc_tx") as "[mem_instr Hacc_mem_acc_tx]".
    iDestruct (big_sepFM_lookup_Some Hlookup_tran with "tran_pgt_owned") as "[[tran' [own_tran excl_tran]] tran_pgt_owned]".
    simpl. split;first done. rewrite Heq_tran_tt //.
    rewrite Hrw_tran; clear Hrw_tran.
    iDestruct (trans_split with "[$tran $tran']") as "tran".
    simpl.
    case_bool_decide;first contradiction.

    iApply (mem_reclaim_share ai r1 with "[$PC $mem_instr $R0 $R1 $pgt_acc $tx $excl_tran $re $tran $fresh_handles]");auto.
    iNext. simpl.
    iIntros "(PC & mem_instr & R0 & R1 & pgt_acc & excl_tran & tx & fresh_handles) _".

    iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
    iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
    iDestruct (access_split with "pgt_acc") as "[pgt_acc pgt_acc']".

    iApply ("IH" $! _ _ _ _ (delete r1 trans) _ Htotal_regs' with "[] [] [] [] regs tx pgt_tx pgt_acc pgt_acc' LB [fresh_handles trans]
                            [tran_pgt_transferred] [retri retri'] R0z R1z R2z rx_state rx other_rx prop0 propi [tran_pgt_owned]
                            [own_tran excl_tran pgt_owned] [retri_owned] [mem_rest mem_acc_tx mem_tx]").
    {
      iPureIntro.
      set_solver + Hsubset_mb.
    }
    {
      iPureIntro.
      rewrite Hrewrite.
      set_solver + Hdisj_na Hsubseteq_tran.
    }
    {
      iPureIntro.
      rewrite Hrewrite.
      set_solver + Hdisj_na Hsubseteq_tran Hnin_rx.
    }
    {
      iPureIntro.
      rewrite Hrewrite.
      set_solver + Hdisj_na Hsubseteq_tran Hnin_tx.
    }
    {
      iExists (hpool ∪ {[r1]}).
      iFrame "fresh_handles trans".
      iPureIntro.
      assert (r1 ∈ dom (gset _) trans).
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
      split.
      set_solver + H0.
      apply (trans_ps_disj_subseteq trans).
      done.
      apply map_subseteq_delete.
    }
    {
      rewrite /transaction_pagetable_entries_transferred.
      rewrite (big_sepFM_delete_False Hlookup_tran).
      iFrame "tran_pgt_transferred".
      simpl. intros [? _]. rewrite Heq_tran_tt in H0; inversion H0.
    }
    {
      rewrite /retrieval_entries_transferred.
      iFrame "retri retri'".
    }
    {
      rewrite /transaction_pagetable_entries_owned.
      iFrame.
    }
    {
      rewrite Hrewrite.
      rewrite (union_comm_L _ tran.1.1.2).
      rewrite (difference_union_distr_l_L tran.1.1.2).
      assert (tran.1.1.2 ∖ {[p_rx;p_tx]} = tran.1.1.2) as ->.
      set_solver + Hnin_rx Hnin_tx Hsubseteq_tran.
      rewrite (difference_union_distr_l_L tran.1.1.2).
      assert (tran.1.1.2 ∖ (ps_mem_in_trans ∖ tran.1.1.2) = tran.1.1.2) as ->.
      set_solver + Hsubseteq_tran.
      assert (tran.1.1.2 ∪ ps_acc ∖ {[p_rx; p_tx]} ∖ (ps_mem_in_trans ∖ tran.1.1.2) = tran.1.1.2 ∪ ps_acc ∖ {[p_rx; p_tx]} ∖ ps_mem_in_trans) as ->.
      set A := (ps_acc ∖ {[p_rx; p_tx]}).
      set G := (tran.1.1.2 ∪ A ∖ (ps_mem_in_trans ∖ tran.1.1.2)).

      rewrite (union_difference_L tran.1.1.2 ps_mem_in_trans).
      2: {
        set_solver + Hsubseteq_tran.
      }
      rewrite difference_union_distr_r_L.
      rewrite union_intersection_l_L.
      rewrite (union_comm_L tran.1.1.2).
      rewrite difference_union_L.
      rewrite intersection_comm_L.
      symmetry.
      rewrite /G.
      rewrite subseteq_intersection_1_L. done.
      set_solver +.
      iDestruct "pgt_owned" as "[own_owned excl_owned]".
      iSplitL "own_owned own_tran".
      iApply (big_sepS_union with "[$own_tran $own_owned]").
      set_solver + Hsubseteq_tran.
      iApply (big_sepS_union with "[$excl_tran $excl_owned]").
      set_solver + Hsubseteq_tran.
    }
    {
      rewrite /retrieval_entries_owned.
      rewrite -big_sepFM_delete_False;auto.
      apply Hlookup_tran.
      simpl.
      intros [_ ?]. rewrite Heq_retri // in H0.
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
    }
    { (* apply [mem_reclaim_lend] *)
    iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "mem_acc_tx") as "[mem_instr Hacc_mem_acc_tx]".
    iDestruct (big_sepFM_lookup_Some Hlookup_tran with "tran_pgt_owned") as "[[tran' [own_tran excl_tran]] tran_pgt_owned]".
    simpl. split;first done. rewrite Heq_tran_tt //.
    rewrite Hrw_tran; clear Hrw_tran.
    iDestruct (trans_split with "[$tran $tran']") as "tran".
    simpl.
    case_bool_decide. 2: inversion H.

    iApply (mem_reclaim_lend ai r1 with "[$PC $mem_instr $R0 $R1 $pgt_acc $tx $re $tran $fresh_handles]");auto.
    iNext. simpl.
    iIntros "(PC & mem_instr & R0 & R1 & pgt_acc & tx & fresh_handles) _".

    iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
    iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
    iDestruct (access_split with "pgt_acc") as "[pgt_acc pgt_acc']".

    iApply ("IH" $! _ _ _ _ (delete r1 trans) _ Htotal_regs' with "[] [] [] [] regs tx pgt_tx pgt_acc pgt_acc' LB [fresh_handles trans]
                            [tran_pgt_transferred] [retri retri'] R0z R1z R2z rx_state rx other_rx prop0 propi [tran_pgt_owned]
                            [own_tran excl_tran pgt_owned] [retri_owned] [mem_rest mem_acc_tx mem_tx]").
    {
      iPureIntro.
      set_solver + Hsubset_mb.
    }
    {
      iPureIntro.
      rewrite Hrewrite.
      set_solver + Hdisj_na Hsubseteq_tran.
    }
    {
      iPureIntro.
      rewrite Hrewrite.
      set_solver + Hdisj_na Hsubseteq_tran Hnin_rx.
    }
    {
      iPureIntro.
      rewrite Hrewrite.
      set_solver + Hdisj_na Hsubseteq_tran Hnin_tx.
    }
    {
      iExists (hpool ∪ {[r1]}).
      iFrame "fresh_handles trans".
      iPureIntro.
      assert (r1 ∈ dom (gset _) trans).
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
      split.
      set_solver + H0.
      apply (trans_ps_disj_subseteq trans).
      done.
      apply map_subseteq_delete.
    }
    {
      rewrite /transaction_pagetable_entries_transferred.
      rewrite (big_sepFM_delete_False Hlookup_tran).
      iFrame "tran_pgt_transferred".
      simpl. intros [? _]. rewrite Heq_tran_tt in H0; inversion H0.
    }
    {
      rewrite /retrieval_entries_transferred.
      iFrame "retri retri'".
    }
    {
      rewrite /transaction_pagetable_entries_owned.
      iFrame.
    }
    {
      rewrite Hrewrite.
      rewrite (union_comm_L _ tran.1.1.2).
      rewrite (difference_union_distr_l_L tran.1.1.2).
      assert (tran.1.1.2 ∖ {[p_rx;p_tx]} = tran.1.1.2) as ->.
      set_solver + Hnin_rx Hnin_tx Hsubseteq_tran.
      rewrite (difference_union_distr_l_L tran.1.1.2).
      assert (tran.1.1.2 ∖ (ps_mem_in_trans ∖ tran.1.1.2) = tran.1.1.2) as ->.
      set_solver + Hsubseteq_tran.
      assert (tran.1.1.2 ∪ ps_acc ∖ {[p_rx; p_tx]} ∖ (ps_mem_in_trans ∖ tran.1.1.2) = tran.1.1.2 ∪ ps_acc ∖ {[p_rx; p_tx]} ∖ ps_mem_in_trans) as ->.
      set A := (ps_acc ∖ {[p_rx; p_tx]}).
      set G := (tran.1.1.2 ∪ A ∖ (ps_mem_in_trans ∖ tran.1.1.2)).

      rewrite (union_difference_L tran.1.1.2 ps_mem_in_trans).
      2: {
        set_solver + Hsubseteq_tran.
      }
      rewrite difference_union_distr_r_L.
      rewrite union_intersection_l_L.
      rewrite (union_comm_L tran.1.1.2).
      rewrite difference_union_L.
      rewrite intersection_comm_L.
      symmetry.
      rewrite /G.
      rewrite subseteq_intersection_1_L. done.
      set_solver +.
      iDestruct "pgt_owned" as "[own_owned excl_owned]".
      iSplitL "own_owned own_tran".
      iApply (big_sepS_union with "[$own_tran $own_owned]").
      set_solver + Hsubseteq_tran.
      iApply (big_sepS_union with "[$excl_tran $excl_owned]").
      set_solver + Hsubseteq_tran.
    }
    {
      rewrite /retrieval_entries_owned.
      rewrite -big_sepFM_delete_False;auto.
      apply Hlookup_tran.
      simpl.
      intros [_ ?]. rewrite Heq_retri // in H0.
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
    }
  Qed.

End ftlr_reclaim.
