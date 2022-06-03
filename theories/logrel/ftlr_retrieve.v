From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang trans_extra.
From HypVeri.algebra Require Import base pagetable mem trans.
From HypVeri.rules Require Import mem_retrieve.
From HypVeri.logrel Require Import logrel logrel_extra.
From HypVeri Require Import proofmode stdpp_extra.
Import uPred.

Section ftlr_retrieve.
  Context `{hypconst:HypervisorConstants}.
  Context `{hypparams:!HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.

Lemma ftlr_retrieve {i mem_acc_tx ai regs rxs ps_acc p_tx p_rx instr trans r0} P:
  (∀ trans trans' rxs rxs', delete i rxs = delete i rxs' -> except i trans = except i trans' -> P trans rxs ⊣⊢ P trans' rxs') ->
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
  decode_instruction instr = Some Hvc ->
  regs !! R0 = Some r0 ->
  decode_hvc_func r0 = Some Retrieve ->
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
    iDestruct "rx" as "[rx pgt_rx]".

    iDestruct (get_trans_ps_disj with "trans_hpool_global") as %Htrans_disj.
    iDestruct "trans_hpool_global" as (hpool) "(%Heq_hsall & fresh_handles & trans)".

    destruct (decide (r1 ∈ valid_handles)) as [Hin_hs_all |Hnotin_hs_all].
    2: { (* apply [mem_retrieve_invalid_handle] *)
        iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "mem_acc_tx") as "[mem_instr Hacc_mem_acc_tx]".

        iApply (mem_retrieve_invalid_handle ai with "[$PC $mem_instr $tx $R0 $R1 $R2 $pgt_acc]");auto.
        iNext.
        iIntros "(PC & mem_instr & R0 & R1 & R2 & pgt_acc & tx) _".

        iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
        iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".

        iApply ("IH" $! _ _ trans _ Htotal_rxs Htotal_regs' with "[] [] [] [] regs tx pgt_tx [$rx $pgt_rx] pgt_acc pgt_owned [fresh_handles trans]
                            tran_pgt_transferred retri rx_state other_rx tran_pgt_owned
                             retri_owned [mem_rest mem_acc_tx mem_tx] P");auto.
        {
          iExists hpool. iSplitL "";auto. iFrame.
        }
        {
          iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx $mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
          iExists mem_acc_tx;by iFrame "mem_acc_tx".
          iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
          set_solver +.
        }
    }
    destruct (decide (r1 ∈ hpool)) as [Hin_hpool | Hnotin_hpool].
    { (* apply [mem_retrieve_fresh_handle] *)
      iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "mem_acc_tx") as "[mem_instr Hacc_mem_acc_tx]".

      iApply (mem_retrieve_fresh_handle ai with "[$PC $mem_instr $R0 $R1 $R2 $pgt_acc $tx $fresh_handles]");auto.
      iNext.
      iIntros "(PC & mem_instr & R0 & R1 & R2 & pgt_acc & tx & fresh_handles) _".

      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
      iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".

      iApply ("IH" $! _ _  trans _ Htotal_rxs Htotal_regs' with "[] [] [] [] regs tx pgt_tx [$rx $pgt_rx] pgt_acc pgt_owned [fresh_handles trans]
                            tran_pgt_transferred retri rx_state other_rx tran_pgt_owned
                            retri_owned [mem_rest mem_acc_tx mem_tx] P");auto.
      {
        iExists hpool. iSplitL "";auto. iFrame.
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
    iDestruct (big_sepM_delete _ trans _  _ Hlookup_tran with "trans") as "([tran pgt_tran] & trans)".

    destruct(decide (tran.1.1.1.2 = i)) as [Heq_tran | Hneq_tran].
    2: { (*apply [mem_retrieve_invalid_trans]*)
      iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "mem_acc_tx") as "[mem_instr Hacc_mem_acc_tx]".

      iApply (mem_retrieve_invalid_trans ai with "[$PC $mem_instr $R0 $R1 $R2 $pgt_acc $tx $tran]");auto.
      iNext.
      iIntros "(PC & mem_instr & R0 & R1 & R2 & pgt_acc & tx & tran) _".

      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
      iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".

      iApply ("IH" $! _ _ trans _ Htotal_rxs Htotal_regs' with "[] [] [] [] regs tx pgt_tx [$rx $pgt_rx] pgt_acc pgt_owned [fresh_handles tran pgt_tran trans]
                            tran_pgt_transferred retri rx_state other_rx tran_pgt_owned
                            retri_owned [mem_rest mem_acc_tx mem_tx] P");auto.
      {
        iExists hpool.
        iSplitL "";auto.
        iFrame "fresh_handles".
        rewrite (big_sepM_delete _ trans).
        iSplitL "tran pgt_tran". iFrame. iFrame.
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
    iDestruct (big_sepFM_lookup_Some Hlookup_tran with "retri") as "[re retri]". right;done.

    destruct (tran.2) eqn:Heq_retri.
    { (* apply [mem_retrieve_retrieved] *)
     iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "mem_acc_tx") as "[mem_instr Hacc_mem_acc_tx]".

     iApply (mem_retrieve_retrieved ai with "[$PC $mem_instr $R0 $R1 $R2 $pgt_acc $tx $re]");auto.
     iNext.
     iIntros "(PC & mem_instr & R0 & R1 & R2 & pgt_acc & tx & re) _".

     iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
     iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".

     iApply ("IH" $! _ _ trans _ Htotal_rxs Htotal_regs' with "[] [] [] [] regs tx pgt_tx [$rx $pgt_rx] pgt_acc pgt_owned
                            [fresh_handles tran pgt_tran trans] tran_pgt_transferred [re retri retri'] rx_state other_rx tran_pgt_owned
                            retri_owned [mem_rest mem_acc_tx mem_tx] P");auto.
     {
       iExists hpool.
       iSplitL "";auto.
       iFrame "fresh_handles".
       rewrite (big_sepM_delete _ trans).
       iSplitL "tran pgt_tran". iFrame. iFrame.
       done.
     }
     {
       rewrite /retrievable_transaction_transferred.
       iDestruct (big_sepFM_delete_acc_True tran with "retri") as "retri". right;done.
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

    assert(tran.1 = (tran.1.1.1.1, i, tran.1.1.2, tran.1.2)) as Hrw_tran.
    {
      rewrite -Heq_tran.
      repeat destruct tran as [tran ?]. simpl. done.
    }
    rewrite Hrw_tran.


    pose proof (Htotal_rxs i) as [rx_state Hlookup_rs].
    iDestruct ("rx_state" $! rx_state with "[]") as "rx_state".
    { iPureIntro. exact Hlookup_rs. }

    destruct (rx_state) eqn: Heq_rxstate.
    { (* apply [mem_retrieve_rx_full] *)
     iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "mem_acc_tx") as "[mem_instr Hacc_mem_acc_tx]".
     iApply (mem_retrieve_rx_full ai r1 with "[$PC $mem_instr $R0 $R1 $R2 $pgt_acc $tx $re $tran rx_state]").
     done. done. done. done. exists p;reflexivity. iFrame.
     iNext. iIntros "(PC & mem_instr & R0 & R1 & R2 & pgt_acc & tx & re & tran & rx_state) _".

     iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
     iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".

     iApply ("IH" $! _ _ trans _ Htotal_rxs Htotal_regs' with "[] [] [] [] regs tx pgt_tx [$rx $pgt_rx] pgt_acc pgt_owned
                            [fresh_handles tran pgt_tran trans] tran_pgt_transferred [re retri retri'] [rx_state] other_rx tran_pgt_owned
                            retri_owned [mem_rest mem_acc_tx mem_tx] P");auto.
     {
       iExists hpool.
       iSplitL "";auto.
       iFrame "fresh_handles".
       rewrite (big_sepM_delete _ trans).
       iSplitL "tran pgt_tran".
       rewrite -Hrw_tran. iFrame. iFrame.
       done.
     }
     {
       rewrite /retrievable_transaction_transferred.
       iDestruct (big_sepFM_delete_acc_True tran with "retri") as "retri". right;done.
       rewrite Heq_retri.
       iDestruct ("retri" with "re") as "retri".
       rewrite insert_id;auto.
       iFrame.
     }
     {
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
    }

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
      simpl. right;done.
    }

    assert (p_rx ∈ ps_acc ∖ {[p_tx]}) as Hin_ps_acc_tx'. set_solver + Hsubset_mb Hneq_mb.
    iDestruct (memory_pages_split_singleton p_rx _ Hin_ps_acc_tx') as "[Hsplit _]".
    iDestruct ("Hsplit" with "[mem_acc_tx]") as (mem_acc_tx_rx mem_rx) "[[%Hdom_mem_acc_tx_rx mem_acc_tx_rx] [mem_rx %Heq_mem_acc_tx_rx]]".
    {
      rewrite /memory_pages.
      iSplitL "".
      iPureIntro.
      apply Hdom_mem_acc_tx.
      iFrame.
    }
    iClear "Hsplit".
    rewrite -Heq_mem_acc_tx_rx in Hlookup_mem_ai.
    iAssert (⌜dom (gset _) mem_rx = set_of_addr {[p_rx]}⌝)%I as "%Hdom_mem_rx".
    {
      rewrite set_of_addr_singleton.
      iDestruct "mem_rx" as "[$ _]".
    }
    rewrite lookup_union_Some in Hlookup_mem_ai.
    2:{ apply map_disjoint_dom. rewrite Hdom_mem_acc_tx_rx Hdom_mem_rx.
        apply set_of_addr_disj.
        set_solver +.
    }

    destruct (tran.1.2) eqn:Heq_tran_tt.
    { (* retrieve donate*)
      iDestruct (big_sepFM_lookup_Some Hlookup_tran with "tran_pgt_transferred") as "[[tran' oe_tran] tran_pgt_transferred]".
      simpl. split;last done. right;done.
      rewrite Hrw_tran; clear Hrw_tran. 
      iDestruct (pgt_split_quarter with "[$oe_tran pgt_tran]") as "oe_tran".
      { case_bool_decide. iFrame. inversion H. }
      iDestruct (big_sepS_sep with "oe_tran") as "[own_tran excl_tran]".

      iDestruct (trans_split with "[tran' tran'']") as "tran'".
      { rewrite -half_of_half. iFrame. }
      iDestruct (trans_split with "[$tran $tran']") as "tran".

      assert (accessible_in_trans_memory_pages i (delete r1 trans) = ps_mem_in_trans ∖ tran.1.1.2) as Hrewrite.
      {
        rewrite /accessible_in_trans_memory_pages.
        rewrite map_filter_delete.
        apply pages_in_trans_delete.
        rewrite map_filter_lookup_Some.
        split;first done.
        simpl. right. done.
        apply (trans_ps_disj_subseteq trans).
        done.
        apply map_filter_subseteq.
      }

      destruct Hlookup_mem_ai as [Hlookup_mem_ai|Hlookup_mem_ai].
      { (* apply [mem_retrieve_donate]*)
        iDestruct (mem_big_sepM_split mem_acc_tx_rx Hlookup_mem_ai with "mem_acc_tx_rx") as "[mem_instr Hacc_mem_acc_tx_rx]".

        iApply (mem_retrieve_donate ai r1 with "[$PC $mem_instr $R0 $R1 $own_tran $pgt_acc $tx $re $tran $rx $rx_state $mem_rx $fresh_handles]");auto.
        iNext. simpl.
        iIntros "(PC & mem_instr & R0 & R1 & own_tran & pgt_acc & tx & rx & (%wl & %des & rx_state & _ & _ & mem_rx) & fresh_handles) _".

        iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
        iDestruct ("Hacc_mem_acc_tx_rx" with "[$mem_instr]") as "mem_acc_tx_rx".

        set rxs' := <[(i:VMID):= Some (wl, tran.1.1.1.1)]>rxs.

        iApply ("IH" $! _ _ (delete r1 trans) rxs' with "[] [] [] [] [] [] regs tx pgt_tx [$rx $pgt_rx]  pgt_acc [own_tran excl_tran pgt_owned]
                            [fresh_handles trans] [tran_pgt_transferred] [retri retri'] [rx_state] [other_rx] [tran_pgt_owned]
                            [retri_owned] [mem_rest mem_acc_tx_rx mem_rx mem_tx] [P]").
        {
          iPureIntro.
          intro.
          destruct (decide (k = i)).
          {
            exists (Some (wl, tran.1.1.1.1)).
            rewrite /rxs'.
            subst k. rewrite lookup_insert //.
          }
          specialize (Htotal_rxs k).
          rewrite /rxs' lookup_insert_ne //.
        }
        {
          done.
        }
        {
          iPureIntro.
          set_solver + Hsubset_mb.
        }
        {
          iPureIntro.
          erewrite currently_accessible_in_trans_memory_pages_delete_False;eauto.
          set_solver + Hsubset_acc.
          intros [[]|[]].
          rewrite H0 //in Heq_tran_tt.
          rewrite H0 // in Heq_retri.
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
          assert (Hrewrite': currently_accessible_in_trans_memory_pages i (delete r1 trans) = currently_accessible_in_trans_memory_pages i trans).
          {
            erewrite currently_accessible_in_trans_memory_pages_delete_False;eauto.
            intros [[]|[]].
            rewrite H0 //in Heq_tran_tt.
            rewrite H0 // in Heq_retri.
          }
          rewrite Hrewrite'.
          rewrite (difference_union_distr_l_L tran.1.1.2).
          assert (tran.1.1.2 ∖ {[p_rx;p_tx]} = tran.1.1.2) as ->.
          set_solver + Hnin_rx Hnin_tx Hsubseteq_tran.
          rewrite (difference_union_distr_l_L tran.1.1.2).
          assert (tran.1.1.2 ∖ currently_accessible_in_trans_memory_pages i trans = tran.1.1.2) as ->.
          {
            rewrite -Hrewrite'.
            pose proof (currently_accessible_accessible_memory_pages_subseteq i (delete r1 trans)) as Hs.
            set_solver + Hs Hsubseteq_tran Hrewrite.
          }
          iDestruct (big_sepS_sep with "[$own_tran $excl_tran]") as "oe_tran".
          iApply (big_sepS_union_2 with "oe_tran pgt_owned").
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
          rewrite (union_comm_L tran.1.1.2).
          rewrite -(union_assoc_L ps_acc tran.1.1.2).
          rewrite -(union_difference_L tran.1.1.2);last set_solver + Hsubseteq_tran.
          iApply (memory_pages_split_diff' _ ps_acc).
          set_solver +.
          iSplitL "mem_rest"; first done.
          iDestruct (memory_pages_split_singleton' p_rx with "[mem_acc_tx_rx mem_rx]") as "mem_acc_tx". set_solver + Hsubset_mb.
          iSplitL "mem_acc_tx_rx".
          iExists mem_acc_tx_rx; by iFrame "mem_acc_tx_rx".
          iExists (list_to_map (zip (finz.seq p_rx (length des)) des) ∪ mem_rx); by iFrame "mem_rx".
          iApply (memory_pages_split_singleton' p_tx with "[$mem_acc_tx $mem_tx]"). set_solver + Hsubset_mb.
        }
        {
          iApply (P_eq with "P").
          rewrite /rxs' delete_insert_delete //.
          symmetry. eapply except_delete_False. done. right;done.
        }
      }
      { (* apply [mem_retrieve_donate_rx]*)
        iDestruct (mem_big_sepM_split mem_rx Hlookup_mem_ai with "[mem_rx]") as "[mem_instr Hacc_mem_rx]".
        iDestruct "mem_rx" as "[? $]".
        rewrite set_of_addr_singleton in Hdom_mem_rx.

        assert (p_rx = (tpa ai)) as ->.
        {
          apply elem_of_dom_2 in Hlookup_mem_ai.
          rewrite Hdom_mem_rx in Hlookup_mem_ai.
          rewrite elem_of_list_to_set in Hlookup_mem_ai.
          apply elem_of_addr_of_page_iff in Hlookup_mem_ai.
          done.
        }

        iApply (mem_retrieve_donate_rx ai r1 with "[$PC $mem_instr $R0 $R1 $own_tran $pgt_acc $tx $re $tran $rx $rx_state Hacc_mem_rx $fresh_handles]");auto.
        iNext. iIntros "ai". iDestruct ("Hacc_mem_rx" with "ai") as "rx".
        iSplitL "". 2: iExact "rx". done.
        iNext. simpl.
        iIntros "(PC & R0 & R1 & own_tran & pgt_acc & tx & rx & (%wl & %des & rx_state & _ & _ & mem_rx) & fresh_handles) _".

        iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".

        set rxs' := <[(i:VMID):= Some (wl, tran.1.1.1.1)]>rxs.

        iApply ("IH" $! _ _ (delete r1 trans) rxs' with "[] [] [] [] [] [] regs tx pgt_tx [$rx $pgt_rx] pgt_acc [own_tran excl_tran pgt_owned]
                            [fresh_handles trans] [tran_pgt_transferred] [retri retri'] [rx_state] [other_rx] [tran_pgt_owned]
                            [retri_owned] [mem_rest mem_acc_tx_rx mem_rx mem_tx] [P]").
        {
          iPureIntro.
          intro.
          destruct (decide (k = i)).
          {
            exists (Some (wl, tran.1.1.1.1)).
            rewrite /rxs'.
            subst k. rewrite lookup_insert //.
          }
          specialize (Htotal_rxs k).
          rewrite /rxs' lookup_insert_ne //.
        }
        {
          done.
        }
        {
          iPureIntro.
          set_solver + Hsubset_mb.
        }
        {
          iPureIntro.
          erewrite currently_accessible_in_trans_memory_pages_delete_False;eauto.
          set_solver + Hsubset_acc.
          intros [[]|[]].
          rewrite H0 //in Heq_tran_tt.
          rewrite H0 // in Heq_retri.
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
          assert (Hrewrite': currently_accessible_in_trans_memory_pages i (delete r1 trans) = currently_accessible_in_trans_memory_pages i trans).
          {
            erewrite currently_accessible_in_trans_memory_pages_delete_False;eauto.
            intros [[]|[]].
            rewrite H0 //in Heq_tran_tt.
            rewrite H0 // in Heq_retri.
          }
          rewrite Hrewrite'.
          rewrite (difference_union_distr_l_L tran.1.1.2).
          set (p_rx := tpa ai).
          assert (tran.1.1.2 ∖ {[p_rx;p_tx]} = tran.1.1.2) as ->.
          set_solver + Hnin_rx Hnin_tx Hsubseteq_tran.
          rewrite (difference_union_distr_l_L tran.1.1.2).
          assert (tran.1.1.2 ∖ currently_accessible_in_trans_memory_pages i trans = tran.1.1.2) as ->.
          {
            rewrite -Hrewrite'.
            pose proof (currently_accessible_accessible_memory_pages_subseteq i (delete r1 trans)) as Hs.
            set_solver + Hs Hsubseteq_tran Hrewrite.
          }
          iDestruct (big_sepS_sep with "[$own_tran $excl_tran]") as "oe_tran".
          iApply (big_sepS_union_2 with "oe_tran pgt_owned").
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
          rewrite (union_comm_L tran.1.1.2).
          rewrite -(union_assoc_L ps_acc tran.1.1.2).
          rewrite -(union_difference_L tran.1.1.2);last set_solver + Hsubseteq_tran.
          iApply (memory_pages_split_diff' _ ps_acc).
          set_solver +.
          iSplitL "mem_rest"; first done.
          iDestruct (memory_pages_split_singleton' (tpa ai) with "[mem_acc_tx_rx mem_rx]") as "mem_acc_tx". set_solver + Hsubset_mb.
          iSplitL "mem_acc_tx_rx".
          iExists mem_acc_tx_rx; by iFrame "mem_acc_tx_rx".
          iExists (list_to_map (zip (finz.seq (tpa ai) (length des)) des) ∪ mem_rx); by iFrame "mem_rx".
          iApply (memory_pages_split_singleton' p_tx with "[$mem_acc_tx $mem_tx]"). set_solver + Hsubset_mb.
        }
        {
          iApply (P_eq with "P").
          rewrite /rxs' delete_insert_delete //.
          symmetry. eapply except_delete_False. done. right;done.
        }
      }
    }
    { (* retrieve share*)
      assert (accessible_in_trans_memory_pages i (<[r1 := (tran.1, true)]> trans)
              = accessible_in_trans_memory_pages i trans) as Hrewrite.
      {
        rewrite /accessible_in_trans_memory_pages.
        rewrite map_filter_insert_True.
        2: {
          simpl. right. done.
        }
        erewrite (pages_in_trans_insert' (tran:= tran) (tran' := (tran.1, true)));auto.
        rewrite map_filter_lookup_Some.
        split;auto.
      }

      destruct Hlookup_mem_ai as [Hlookup_mem_ai|Hlookup_mem_ai].
      { (* apply [mem_retrieve_share]*)
        iDestruct (mem_big_sepM_split mem_acc_tx_rx Hlookup_mem_ai with "mem_acc_tx_rx") as "[mem_instr Hacc_mem_acc_tx_rx]".

        iApply (mem_retrieve_share ai r1 with "[$PC $mem_instr $R0 $R1 $pgt_acc $tx $re $tran $rx $rx_state $mem_rx]");auto.
        iNext. simpl.
        iIntros "(PC & mem_instr & R0 & R1 & pgt_acc & tx & re & tran & rx & (%wl & %des & rx_state & _ & _ & mem_rx)) _".

        iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
        iDestruct ("Hacc_mem_acc_tx_rx" with "[$mem_instr]") as "mem_acc_tx_rx".
        iDestruct (retri_split with "re") as "[re re']".

        set rxs' := <[(i:VMID):= Some (wl, tran.1.1.1.1)]>rxs.

        iApply ("IH" $! _ _ (<[r1 := ((tran.1, true):transaction)]> trans) rxs' with "[] [] [] [] [] [] regs tx pgt_tx [$rx $pgt_rx] pgt_acc [pgt_owned]
                          [fresh_handles trans tran pgt_tran] [tran_pgt_transferred] [retri retri' re] [rx_state]
                          [other_rx] [tran_pgt_owned] [retri_owned re' tran''] [mem_rest mem_acc_tx_rx mem_rx mem_tx] [P]").
        {
          iPureIntro.
          intro.
          destruct (decide (k = i)).
          {
            exists (Some (wl, tran.1.1.1.1)).
            rewrite /rxs'.
            subst k. rewrite lookup_insert //.
          }
          specialize (Htotal_rxs k).
          rewrite /rxs' lookup_insert_ne //.
        }
        {
          done.
        }
        {
          iPureIntro.
          set_solver + Hsubset_mb.
        }
        {
          iPureIntro.
          rewrite (currently_accessible_in_trans_memory_pages_insert_True_Some i trans r1 _ _ Hlookup_tran) //.
          simpl.
          rewrite -Hrewrite in Hnin_rx Hnin_tx.
          rewrite (accessible_in_trans_memory_pages_insert_True_Some i trans r1 _ _ Hlookup_tran) //= in Hnin_rx Hnin_tx.
          simpl in Hnin_tx,Hnin_rx.
          set_solver + Hsubset_acc Hnin_rx Hnin_tx.
          right;done.
          right;done.
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
          rewrite /pagetable_entries_excl_owned /pgt.
          rewrite -2?big_sepS_sep.
          iApply (big_sepS_subseteq with "pgt_owned").
          assert (currently_accessible_in_trans_memory_pages i (<[r1:=(tran.1, true)]> trans)
                  = tran.1.1.2 ∪ currently_accessible_in_trans_memory_pages i trans) as Hrewrite'.
          {
            rewrite (currently_accessible_in_trans_memory_pages_insert_True_Some i trans r1 _ _ Hlookup_tran) //=.
            rewrite difference_union_L.
            set_solver +.
            right;done.
          }
          rewrite Hrewrite'.
          rewrite (difference_union_distr_l_L tran.1.1.2).
          assert (tran.1.1.2 ∖ {[p_rx;p_tx]} = tran.1.1.2) as ->.
          set_solver + Hnin_rx Hnin_tx Hsubseteq_tran.
          rewrite (difference_union_distr_l_L tran.1.1.2).
          assert (tran.1.1.2 ∖ (tran.1.1.2 ∪ currently_accessible_in_trans_memory_pages i trans) = ∅) as -> by set_solver +.
          set_solver +.
        }
        {
          iExists hpool.
          iSplitL "".
          rewrite dom_insert_lookup_L //.
          iFrame "fresh_handles".
          iApply (big_sepM_delete _ (<[r1:=(tran.1, true)]> trans) r1 (tran.1,true)).
          rewrite lookup_insert_Some.
          left. split;done.
          rewrite Hrw_tran /=. iFrame.
          rewrite delete_insert_delete //.
        }
        {
          rewrite /transaction_pagetable_entries_transferred.
          rewrite Hrw_tran /=.
          iApply (big_sepFM_update_False _ Hlookup_tran);auto.
          rewrite Heq_tran_tt. intros [_ ?]. done.
          intros [_ ?]. done.
        }
        {
          rewrite /retrievable_transaction_transferred.
          iDestruct (big_sepFM_delete_acc_True (tran.1, true) with "retri") as "retri".
          right;done.
          iDestruct (big_sepFM_delete_acc_False (tran.1, true) with "retri'") as "retri'".
          simpl. intro. destruct H;done.
          iDestruct ("retri" with "re") as "retri".
          iFrame.
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
          rewrite /transaction_pagetable_entries_owned.
          destruct (decide (tran.1.1.1.1 = i)).
          iApply (big_sepFM_update_True _ Hlookup_tran).
          simpl. split. done. rewrite Heq_tran_tt;done.
          simpl. split. done. rewrite Heq_tran_tt;done.
          simpl. iIntros "?";iFrame.
          iFrame.
          iApply (big_sepFM_update_False _ Hlookup_tran).
          simpl. intros [? _]. contradiction.
          simpl. intros [? _]. contradiction.
          iFrame.
        }
        {
          rewrite /retrieved_transaction_owned.
          iDestruct (big_sepFM_delete_False Hlookup_tran with "retri_owned") as "retri_owned".
          simpl. intros [_ ?]. rewrite H  // in Heq_retri.
          iApply (big_sepFM_delete_acc_True with "[$retri_owned]").
          simpl. split;done.
          simpl; iFrame.
        }
        {
          rewrite Hrewrite.
          rewrite (union_comm_L tran.1.1.2).
          rewrite -(union_assoc_L ps_acc tran.1.1.2).
          assert ((tran.1.1.2 ∪ accessible_in_trans_memory_pages i trans) = accessible_in_trans_memory_pages i trans) as ->.
          set_solver + Hsubseteq_tran.
          iApply (memory_pages_split_diff' _ ps_acc).
          set_solver +.
          iSplitL "mem_rest"; first done.
          iDestruct (memory_pages_split_singleton' p_rx with "[mem_acc_tx_rx mem_rx]") as "mem_acc_tx". set_solver + Hsubset_mb.
          iSplitL "mem_acc_tx_rx".
          iExists mem_acc_tx_rx; by iFrame "mem_acc_tx_rx".
          iExists (list_to_map (zip (finz.seq p_rx (length des)) des) ∪ mem_rx); by iFrame "mem_rx".
          iApply (memory_pages_split_singleton' p_tx with "[$mem_acc_tx $mem_tx]"). set_solver + Hsubset_mb.
        }
        {
          iApply (P_eq with "P").
          rewrite /rxs' delete_insert_delete //.
          symmetry. eapply except_insert_False. right;done.
        }
      }
      { (* apply [mem_retrieve_sharing_rx]*)
        iDestruct (mem_big_sepM_split mem_rx Hlookup_mem_ai with "[mem_rx]") as "[mem_instr Hacc_mem_rx]".
        iDestruct "mem_rx" as "[? $]".
        rewrite set_of_addr_singleton in Hdom_mem_rx.

        assert (p_rx = (tpa ai)) as ->.
        {
          apply elem_of_dom_2 in Hlookup_mem_ai.
          rewrite Hdom_mem_rx in Hlookup_mem_ai.
          rewrite elem_of_list_to_set in Hlookup_mem_ai.
          apply elem_of_addr_of_page_iff in Hlookup_mem_ai.
          done.
        }

        iApply (mem_retrieve_share_rx ai r1 with "[$PC $mem_instr $R0 $R1 $pgt_acc $tx $re $tran $rx $rx_state Hacc_mem_rx]");auto.
        iNext. iIntros "ai". iDestruct ("Hacc_mem_rx" with "ai") as "rx".
        iSplitL "". 2: iExact "rx". done.
        iNext. simpl. iIntros "(PC & R0 & R1 & pgt_acc & tx & re & tran & rx & (%wl & %des & rx_state & _ & _ & mem_rx)) _".

        iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
        iDestruct (retri_split with "re") as "[re re']".

        set rxs' := <[(i:VMID):= Some (wl, tran.1.1.1.1)]>rxs.
        iApply ("IH" $! _ _ (<[r1 := ((tran.1, true):transaction)]> trans) rxs' with "[] [] [] [] [] [] regs tx pgt_tx [$rx $pgt_rx] pgt_acc [pgt_owned]
                          [fresh_handles trans tran pgt_tran] [tran_pgt_transferred] [retri retri' re]  [rx_state]
                          [other_rx] [tran_pgt_owned] [retri_owned re' tran''] [mem_rest mem_acc_tx_rx mem_rx mem_tx] [P]").
        {
          iPureIntro.
          intro.
          destruct (decide (k = i)).
          {
            exists (Some (wl, tran.1.1.1.1)).
            rewrite /rxs'.
            subst k. rewrite lookup_insert //.
          }
          specialize (Htotal_rxs k).
          rewrite /rxs' lookup_insert_ne //.
        }
        {
          done.
        }
        {
          iPureIntro.
          set_solver + Hsubset_mb.
        }
        {
          iPureIntro.
          rewrite (currently_accessible_in_trans_memory_pages_insert_True_Some i trans r1 _ _ Hlookup_tran) /=;auto.
          rewrite -Hrewrite in Hnin_rx Hnin_tx.
          rewrite (accessible_in_trans_memory_pages_insert_True_Some i trans r1 _ _ Hlookup_tran) /= in Hnin_rx Hnin_tx.
          simpl in Hnin_tx,Hnin_rx.
          set_solver + Hsubset_acc Hnin_rx Hnin_tx.
          right;done.
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
          rewrite /pagetable_entries_excl_owned /pgt.
          rewrite -2?big_sepS_sep.
          iApply (big_sepS_subseteq with "pgt_owned").
          assert (currently_accessible_in_trans_memory_pages i (<[r1:=(tran.1, true)]> trans)
                  = tran.1.1.2 ∪ currently_accessible_in_trans_memory_pages i trans) as Hrewrite'.
          {
            rewrite (currently_accessible_in_trans_memory_pages_insert_True_Some i trans r1 _ _ Hlookup_tran) /=.
            rewrite difference_union_L.
            set_solver +.
            right;auto. auto.
          }
          rewrite Hrewrite'.
          rewrite (difference_union_distr_l_L tran.1.1.2).
          set p_rx := tpa ai.
          assert (tran.1.1.2 ∖ {[p_rx;p_tx]} = tran.1.1.2) as ->.
          set_solver + Hnin_rx Hnin_tx Hsubseteq_tran.
          rewrite (difference_union_distr_l_L tran.1.1.2).
          assert (tran.1.1.2 ∖ (tran.1.1.2 ∪ currently_accessible_in_trans_memory_pages i trans) = ∅) as -> by set_solver +.
          set_solver +.
        }
        {
          iExists hpool.
          iSplitL "".
          rewrite dom_insert_lookup_L //.
          iFrame "fresh_handles".
          iApply (big_sepM_delete _ (<[r1:=(tran.1, true)]> trans) r1 (tran.1,true)).
          rewrite lookup_insert_Some.
          left. split;auto.
          rewrite Hrw_tran /=. iFrame.
          rewrite delete_insert_delete //.
        }
        {
          rewrite /transaction_pagetable_entries_transferred.
          rewrite Hrw_tran /=.
          iApply (big_sepFM_update_False _ Hlookup_tran);auto.
          rewrite Heq_tran_tt. intros [_ ?]. done.
          intros [_ ?]. done.
        }
        {
          rewrite /retrievable_transaction_transferred.
          iDestruct (big_sepFM_delete_acc_True (tran.1, true) with "retri") as "retri".
          right;done.
          iDestruct (big_sepFM_delete_acc_False (tran.1, true) with "retri'") as "retri'".
          intro. destruct H;done.
          iDestruct ("retri" with "re") as "retri".
          iFrame.
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
          rewrite /transaction_pagetable_entries_owned.
          destruct (decide (tran.1.1.1.1 = i)).
          iApply (big_sepFM_update_True _ Hlookup_tran).
          simpl. split. done. rewrite Heq_tran_tt;done.
          simpl. split. done. rewrite Heq_tran_tt;done.
          simpl. iIntros "?";iFrame.
          iFrame.
          iApply (big_sepFM_update_False _ Hlookup_tran).
          simpl. intros [? _]. contradiction.
          simpl. intros [? _]. contradiction.
          iFrame.
        }
        {
          rewrite /retrieved_transaction_owned.
          iDestruct (big_sepFM_delete_False Hlookup_tran with "retri_owned") as "retri_owned".
          simpl. intros [_ ?]. rewrite H  // in Heq_retri.
          iApply (big_sepFM_delete_acc_True with "[$retri_owned]").
          simpl. split;done.
          simpl; iFrame.
        }
        {
          assert (accessible_in_trans_memory_pages i (<[r1 := (tran.1, true)]> trans) = accessible_in_trans_memory_pages i trans) as H.
          rewrite /accessible_in_trans_memory_pages.
          rewrite map_filter_insert_True.
          2: { simpl. right. done. }
          erewrite (pages_in_trans_insert' (tran:= tran) (tran' := (tran.1, true)));auto.
          rewrite map_filter_lookup_Some.
          split;auto.
          rewrite H;clear H.
          rewrite (union_comm_L tran.1.1.2).
          rewrite -(union_assoc_L ps_acc tran.1.1.2).
          assert ((tran.1.1.2 ∪ accessible_in_trans_memory_pages i trans) = accessible_in_trans_memory_pages i trans) as ->.
          set_solver + Hsubseteq_tran.
          iApply (memory_pages_split_diff' _ ps_acc).
          set_solver +.
          iSplitL "mem_rest"; first done.
          iDestruct (memory_pages_split_singleton' (tpa ai) with "[mem_acc_tx_rx mem_rx]") as "mem_acc_tx". set_solver + Hsubset_mb.
          iSplitL "mem_acc_tx_rx".
          iExists mem_acc_tx_rx; by iFrame "mem_acc_tx_rx".
          iExists (list_to_map (zip (finz.seq (tpa ai) (length des)) des) ∪ mem_rx); by iFrame "mem_rx".
          iApply (memory_pages_split_singleton' p_tx with "[$mem_acc_tx $mem_tx]"). set_solver + Hsubset_mb.
        }
        {
          iApply (P_eq with "P").
          rewrite /rxs' delete_insert_delete //.
          symmetry. eapply except_insert_False. right;done.
        }
      }
    }
    { (* retrieve lending*)
      assert (accessible_in_trans_memory_pages i (<[r1 := (tran.1, true)]> trans) = accessible_in_trans_memory_pages i trans) as Hrewrite.
      rewrite /accessible_in_trans_memory_pages.
      rewrite map_filter_insert_True.
      2: { simpl. right. done. }
      erewrite (pages_in_trans_insert' (tran:= tran) (tran' := (tran.1, true)));auto.
      rewrite map_filter_lookup_Some.
      split;auto.

      destruct Hlookup_mem_ai as [Hlookup_mem_ai|Hlookup_mem_ai].
      { (* apply [mem_retrieve_lend]*)
        iDestruct (mem_big_sepM_split mem_acc_tx_rx Hlookup_mem_ai with "mem_acc_tx_rx") as "[mem_instr Hacc_mem_acc_tx_rx]".

        iApply (mem_retrieve_lend ai r1 with "[$PC $mem_instr $R0 $R1 $pgt_acc $tx $re $tran $rx $rx_state $mem_rx]");auto.
        iNext. simpl.
        iIntros "(PC & mem_instr & R0 & R1 & pgt_acc & tx & re & tran & rx & (%wl & %des & rx_state & _ & _ & mem_rx)) _".

        iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
        iDestruct ("Hacc_mem_acc_tx_rx" with "[$mem_instr]") as "mem_acc_tx_rx".
        iDestruct (retri_split with "re") as "[re re']".

        set rxs' := <[(i:VMID):= Some (wl, tran.1.1.1.1)]>rxs.

        iApply ("IH" $! _ _ (<[r1 := ((tran.1, true):transaction)]> trans) rxs' with "[] [] [] [] [] [] regs tx pgt_tx [$rx $pgt_rx] pgt_acc [pgt_owned]
                          [fresh_handles trans tran pgt_tran] [tran_pgt_transferred] [retri retri' re] [rx_state]
                          [other_rx] [tran_pgt_owned] [retri_owned re' tran''] [mem_rest mem_acc_tx_rx mem_rx mem_tx] [P]").
        {
          iPureIntro.
          intro.
          destruct (decide (k = i)).
          {
            exists (Some (wl, tran.1.1.1.1)).
            rewrite /rxs'.
            subst k. rewrite lookup_insert //.
          }
          specialize (Htotal_rxs k).
          rewrite /rxs' lookup_insert_ne //.
        }
        {
          done.
        }
        {
          iPureIntro.
          set_solver + Hsubset_mb.
        }
        {
          iPureIntro.
          rewrite (currently_accessible_in_trans_memory_pages_insert_True_Some i trans r1 _ _ Hlookup_tran) /=;auto.
          simpl. rewrite -Hrewrite in Hnin_rx Hnin_tx.
          rewrite (accessible_in_trans_memory_pages_insert_True_Some i trans r1 _ _ Hlookup_tran) /= in Hnin_rx Hnin_tx.
          simpl in Hnin_tx,Hnin_rx.
          set_solver + Hsubset_acc Hnin_rx Hnin_tx.
          right;done.
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
          rewrite /pagetable_entries_excl_owned /pgt.
          rewrite -2?big_sepS_sep.
          iApply (big_sepS_subseteq with "pgt_owned").
          assert (currently_accessible_in_trans_memory_pages i (<[r1:=(tran.1, true)]> trans)
                  = tran.1.1.2 ∪ currently_accessible_in_trans_memory_pages i trans) as Hrewrite'.
          {
            rewrite (currently_accessible_in_trans_memory_pages_insert_True_Some i trans r1 _ _ Hlookup_tran) /=.
            rewrite difference_union_L.
            set_solver +.
            right;auto. auto.
          }
          rewrite Hrewrite'.
          rewrite (difference_union_distr_l_L tran.1.1.2).
          assert (tran.1.1.2 ∖ {[p_rx;p_tx]} = tran.1.1.2) as ->.
          set_solver + Hnin_rx Hnin_tx Hsubseteq_tran.
          rewrite (difference_union_distr_l_L tran.1.1.2).
          assert (tran.1.1.2 ∖ (tran.1.1.2 ∪ currently_accessible_in_trans_memory_pages i trans) = ∅) as -> by set_solver +.
          set_solver +.
        }
        {
          iExists hpool.
          iSplitL "".
          rewrite dom_insert_lookup_L //.
          iFrame "fresh_handles".
          iApply (big_sepM_delete _ (<[r1:=(tran.1, true)]> trans) r1 (tran.1,true)).
          rewrite lookup_insert_Some.
          left. split;done.
          rewrite Hrw_tran /=. iFrame.
          rewrite delete_insert_delete //.
        }
        {
          rewrite /transaction_pagetable_entries_transferred.
          rewrite Hrw_tran /=.
          iApply (big_sepFM_update_False _ Hlookup_tran);auto.
          rewrite Heq_tran_tt. intros [_ ?]. done.
          intros [_ ?]. done.
        }
        {
          rewrite /retrievable_transaction_transferred.
          iDestruct (big_sepFM_delete_acc_True (tran.1, true) with "retri") as "retri".
          right;done.
          iDestruct (big_sepFM_delete_acc_False (tran.1, true) with "retri'") as "retri'".
          simpl. intro. destruct H;done.
          iDestruct ("retri" with "re") as "retri".
          iFrame.
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
          rewrite /transaction_pagetable_entries_owned.
          destruct (decide (tran.1.1.1.1 = i)).
          iApply (big_sepFM_update_True _ Hlookup_tran).
          simpl. split. done. rewrite Heq_tran_tt;done.
          simpl. split. done. rewrite Heq_tran_tt;done.
          simpl. iIntros "?";iFrame.
          iFrame.
          iApply (big_sepFM_update_False _ Hlookup_tran).
          simpl. intros [? _]. contradiction.
          simpl. intros [? _]. contradiction.
          iFrame.
        }
        {
          rewrite /retrieved_transaction_owned.
          iDestruct (big_sepFM_delete_False Hlookup_tran with "retri_owned") as "retri_owned".
          simpl. intros [_ ?]. rewrite H  // in Heq_retri.
          iApply (big_sepFM_delete_acc_True with "[$retri_owned]").
          simpl. split;done.
          simpl; iFrame.
        }
        {
          assert (accessible_in_trans_memory_pages i (<[r1 := (tran.1, true)]> trans) = accessible_in_trans_memory_pages i trans) as H.
          rewrite /accessible_in_trans_memory_pages.
          rewrite map_filter_insert_True.
          2: { simpl. right. done. }
          erewrite (pages_in_trans_insert' (tran:= tran) (tran' := (tran.1, true)));auto.
          rewrite map_filter_lookup_Some.
          split;auto.
          rewrite H;clear H.
          rewrite (union_comm_L tran.1.1.2).
          rewrite -(union_assoc_L ps_acc tran.1.1.2).
          assert ((tran.1.1.2 ∪ accessible_in_trans_memory_pages i trans) = accessible_in_trans_memory_pages i trans) as ->.
          set_solver + Hsubseteq_tran.
          iApply (memory_pages_split_diff' _ ps_acc).
          set_solver +.
          iSplitL "mem_rest"; first done.
          iDestruct (memory_pages_split_singleton' p_rx with "[mem_acc_tx_rx mem_rx]") as "mem_acc_tx". set_solver + Hsubset_mb.
          iSplitL "mem_acc_tx_rx".
          iExists mem_acc_tx_rx; by iFrame "mem_acc_tx_rx".
          iExists (list_to_map (zip (finz.seq p_rx (length des)) des) ∪ mem_rx); by iFrame "mem_rx".
          iApply (memory_pages_split_singleton' p_tx with "[$mem_acc_tx $mem_tx]"). set_solver + Hsubset_mb.
        }
        {
          iApply (P_eq with "P").
          rewrite /rxs' delete_insert_delete //.
          symmetry. eapply except_insert_False. right;done.
        }
      }
      { (* apply [mem_retrieve_lend_rx]*)
        iDestruct (mem_big_sepM_split mem_rx Hlookup_mem_ai with "[mem_rx]") as "[mem_instr Hacc_mem_rx]".
        iDestruct "mem_rx" as "[? $]".
        rewrite set_of_addr_singleton in Hdom_mem_rx.

        assert (p_rx = (tpa ai)) as ->.
        {
          apply elem_of_dom_2 in Hlookup_mem_ai.
          rewrite Hdom_mem_rx in Hlookup_mem_ai.
          rewrite elem_of_list_to_set in Hlookup_mem_ai.
          apply elem_of_addr_of_page_iff in Hlookup_mem_ai.
          done.
        }

        iApply (mem_retrieve_lend_rx ai r1 with "[$PC $mem_instr $R0 $R1 $pgt_acc $tx $re $tran $rx $rx_state Hacc_mem_rx]");auto.
        iNext. iIntros "ai". iDestruct ("Hacc_mem_rx" with "ai") as "rx".
        iSplitL "". 2: iExact "rx". done.
        iNext. simpl. iIntros "(PC & R0 & R1 & pgt_acc & tx & re & tran & rx & (%wl & %des & rx_state & _ & _ & mem_rx)) _".

        iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
        iDestruct (retri_split with "re") as "[re re']".

        set rxs' := <[(i:VMID):= Some (wl, tran.1.1.1.1)]>rxs.
        iApply ("IH" $! _ _ (<[r1 := ((tran.1, true):transaction)]> trans) rxs' with "[] [] [] [] [] [] regs tx pgt_tx [$rx $pgt_rx] pgt_acc [pgt_owned]
                          [fresh_handles trans tran pgt_tran] [tran_pgt_transferred] [retri retri' re] [rx_state]
                          [other_rx] [tran_pgt_owned] [retri_owned re' tran''] [mem_rest mem_acc_tx_rx mem_rx mem_tx] [P]").
        {
          iPureIntro.
          intro.
          destruct (decide (k = i)).
          {
            exists (Some (wl, tran.1.1.1.1)).
            rewrite /rxs'.
            subst k. rewrite lookup_insert //.
          }
          specialize (Htotal_rxs k).
          rewrite /rxs' lookup_insert_ne //.
        }
        {
          done.
        }
        {
          iPureIntro.
          set_solver + Hsubset_mb.
        }
        {
          iPureIntro.
          rewrite (currently_accessible_in_trans_memory_pages_insert_True_Some i trans r1 _ _ Hlookup_tran) /=;auto.
          simpl. rewrite -Hrewrite in Hnin_rx Hnin_tx.
          rewrite (accessible_in_trans_memory_pages_insert_True_Some i trans r1 _ _ Hlookup_tran) /= in Hnin_rx Hnin_tx.
          simpl in Hnin_tx,Hnin_rx.
          set_solver + Hsubset_acc Hnin_rx Hnin_tx.
          right;done.
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
          rewrite /pagetable_entries_excl_owned /pgt.
          rewrite -2?big_sepS_sep.
          iApply (big_sepS_subseteq with "pgt_owned").
          assert (currently_accessible_in_trans_memory_pages i (<[r1:=(tran.1, true)]> trans)
                  = tran.1.1.2 ∪ currently_accessible_in_trans_memory_pages i trans) as Hrewrite'.
          {
            rewrite (currently_accessible_in_trans_memory_pages_insert_True_Some i trans r1 _ _ Hlookup_tran) /=.
            rewrite difference_union_L.
            set_solver +.
            right;auto. auto.
          }
          rewrite Hrewrite'.
          rewrite (difference_union_distr_l_L tran.1.1.2).
          set p_rx := tpa ai.
          assert (tran.1.1.2 ∖ {[p_rx;p_tx]} = tran.1.1.2) as ->.
          set_solver + Hnin_rx Hnin_tx Hsubseteq_tran.
          rewrite (difference_union_distr_l_L tran.1.1.2).
          assert (tran.1.1.2 ∖ (tran.1.1.2 ∪ currently_accessible_in_trans_memory_pages i trans) = ∅) as -> by set_solver +.
          set_solver +.
        }
        {
          iExists hpool.
          iSplitL "".
          rewrite dom_insert_lookup_L //.
          iFrame "fresh_handles".
          iApply (big_sepM_delete _ (<[r1:=(tran.1, true)]> trans) r1 (tran.1,true)).
          rewrite lookup_insert_Some.
          left. split;done.
          rewrite Hrw_tran /=. iFrame.
          rewrite delete_insert_delete //.
        }
        {
          rewrite /transaction_pagetable_entries_transferred.
          rewrite Hrw_tran /=.
          iApply (big_sepFM_update_False _ Hlookup_tran);auto.
          rewrite Heq_tran_tt. intros [_ ?]. done.
          intros [_ ?]. done.
        }
        {
          rewrite /retrievable_transaction_transferred.
          iDestruct (big_sepFM_delete_acc_True (tran.1, true) with "retri") as "retri".
          right;done.
          iDestruct (big_sepFM_delete_acc_False (tran.1, true) with "retri'") as "retri'".
          intro. destruct H;done.
          iDestruct ("retri" with "re") as "retri".
          iFrame.
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
          rewrite /transaction_pagetable_entries_owned.
          destruct (decide (tran.1.1.1.1 = i)).
          iApply (big_sepFM_update_True _ Hlookup_tran).
          simpl. split. done. rewrite Heq_tran_tt;done.
          simpl. split. done. rewrite Heq_tran_tt;done.
          simpl. iIntros "?";iFrame.
          iFrame.
          iApply (big_sepFM_update_False _ Hlookup_tran).
          simpl. intros [? _]. contradiction.
          simpl. intros [? _]. contradiction.
          iFrame.
        }
        {
          rewrite /retrieved_transaction_owned.
          iDestruct (big_sepFM_delete_False Hlookup_tran with "retri_owned") as "retri_owned".
          simpl. intros [_ ?]. rewrite H  // in Heq_retri.
          iApply (big_sepFM_delete_acc_True with "[$retri_owned]").
          simpl. split;done.
          simpl; iFrame.
        }
        {
          assert (accessible_in_trans_memory_pages i (<[r1 := (tran.1, true)]> trans) = accessible_in_trans_memory_pages i trans) as H.
          rewrite /accessible_in_trans_memory_pages.
          rewrite map_filter_insert_True.
          2: { simpl. right. done. }
          erewrite (pages_in_trans_insert' (tran:= tran) (tran' := (tran.1, true)));auto.
          rewrite map_filter_lookup_Some.
          split;auto.
          rewrite H;clear H.
          rewrite (union_comm_L tran.1.1.2).
          rewrite -(union_assoc_L ps_acc tran.1.1.2).
          assert ((tran.1.1.2 ∪ accessible_in_trans_memory_pages i trans) = accessible_in_trans_memory_pages i trans) as ->.
          set_solver + Hsubseteq_tran.
          iApply (memory_pages_split_diff' _ ps_acc).
          set_solver +.
          iSplitL "mem_rest"; first done.
          iDestruct (memory_pages_split_singleton' (tpa ai) with "[mem_acc_tx_rx mem_rx]") as "mem_acc_tx". set_solver + Hsubset_mb.
          iSplitL "mem_acc_tx_rx".
          iExists mem_acc_tx_rx; by iFrame "mem_acc_tx_rx".
          iExists (list_to_map (zip (finz.seq (tpa ai) (length des)) des) ∪ mem_rx); by iFrame "mem_rx".
          iApply (memory_pages_split_singleton' p_tx with "[$mem_acc_tx $mem_tx]"). set_solver + Hsubset_mb.
        }
        {
          iApply (P_eq with "P").
          rewrite /rxs' delete_insert_delete //.
          symmetry. eapply except_insert_False. right;done.
        }
      }
    }
  Qed.

End ftlr_retrieve.
