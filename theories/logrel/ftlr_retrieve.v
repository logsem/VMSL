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

Lemma ftlr_retrieve {i trans' mem_acc_tx ai regs ps_acc p_tx p_rx ps_na instr trans rx_state r0}:
  base_extra.is_total_gmap regs ->
  {[p_tx; p_rx]} ⊆ ps_acc ->
  i ≠ V0 ->
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
  decode_hvc_func r0 = Some Retrieve ->
  p_tx ≠ p_rx ->
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
    iIntros (Htotal_regs Hsubset_mb Hneq_0 Hdisj_na Hnin_rx Hnin_tx Hlookup_PC Hin_ps_acc Hneq_ptx Hdom_mem_acc_tx Hin_ps_acc_tx
                         Hlookup_mem_ai Heqn  Hlookup_reg_R0 Hdecode_hvc).
    iIntros (Hneq_mb) "IH regs tx pgt_tx pgt_acc pgt_acc' LB trans_hpool_global tran_pgt_transferred retri R0z R1z R2z rx_state rx other_rx prop0
             propi tran_pgt_owned pgt_owned retri_owned mem_rest mem_acc_tx mem_tx".
    set ps_mem_in_trans := (pages_in_trans (trans_memory_in_trans i trans)).
    pose proof (Htotal_regs R1) as[r1 Hlookup_reg_R1].
    pose proof (Htotal_regs R2) as[r2 Hlookup_reg_R2].
    iDestruct (reg_big_sepM_split_upd4 i Hlookup_PC Hlookup_reg_R0 Hlookup_reg_R1 Hlookup_reg_R2 with "[$regs]")
      as "(PC & R0 & R1 & R2 & Hacc_regs)";eauto.

    iDestruct "rx" as "[rx pgt_rx]".

    iDestruct (access_split with "[$pgt_acc $pgt_acc']") as "pgt_acc".

    iDestruct "trans_hpool_global" as (hpool) "(%Heq_hsall & fresh_handles & %Htrans_ps_disj & trans)".
    destruct (decide (r1 ∈ hs_all)) as [Hin_hs_all |Hnotin_hs_all].
    2: { (* apply [mem_retrieve_invalid_handle] *)
        iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "mem_acc_tx") as "[mem_instr Hacc_mem_acc_tx]".

        iApply (mem_retrieve_invalid_handle ai with "[$PC $mem_instr $R0 $R1 $R2 $pgt_acc]").
        set_solver + Hin_ps_acc_tx.
        done.
        done.
        done.
        iNext.
        iIntros "(PC & mem_instr & R0 & R1 & R2 & pgt_acc) _".

        iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
        iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
        iDestruct (access_split with "pgt_acc") as "[pgt_acc pgt_acc']".

        iApply ("IH" $! _ _ trans _ Htotal_regs' with "[] [] [] [] regs tx pgt_tx pgt_acc pgt_acc' LB [fresh_handles trans]
                            tran_pgt_transferred retri R0z R1z R2z rx_state [$rx $pgt_rx] other_rx prop0 propi tran_pgt_owned
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
    { (* apply [mem_retrieve_fresh_handle] *)
      iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "mem_acc_tx") as "[mem_instr Hacc_mem_acc_tx]".

      iApply (mem_retrieve_fresh_handle ai with "[$PC $mem_instr $R0 $R1 $R2 $pgt_acc $fresh_handles]").
      set_solver + Hin_ps_acc_tx.
      done.
      done.
      done.
      iNext.
      iIntros "(PC & mem_instr & R0 & R1 & R2 & pgt_acc & fresh_handles) _".

      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
      iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
      iDestruct (access_split with "pgt_acc") as "[pgt_acc pgt_acc']".

      iApply ("IH" $! _ _ trans _ Htotal_regs' with "[] [] [] [] regs tx pgt_tx pgt_acc pgt_acc' LB [fresh_handles trans]
                            tran_pgt_transferred retri R0z R1z R2z rx_state [$rx $pgt_rx] other_rx prop0 propi tran_pgt_owned
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

    destruct(decide (tran.1.1.1.2 = i)) as [Heq_tran | Hneq_tran].
    2: { (*apply [mem_retrieve_invalid_trans]*)
      iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "mem_acc_tx") as "[mem_instr Hacc_mem_acc_tx]".

      iApply (mem_retrieve_invalid_trans ai with "[$PC $mem_instr $R0 $R1 $R2 $pgt_acc $tran]").
      set_solver + Hin_ps_acc_tx.
      done.
      done.
      done.
      iNext.
      iIntros "(PC & mem_instr & R0 & R1 & R2 & pgt_acc & tran) _".

      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
      iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
      iDestruct (access_split with "pgt_acc") as "[pgt_acc pgt_acc']".

      iApply ("IH" $! _ _ trans _ Htotal_regs' with "[] [] [] [] regs tx pgt_tx pgt_acc pgt_acc' LB [fresh_handles tran trans]
                            tran_pgt_transferred retri R0z R1z R2z rx_state [$rx $pgt_rx] other_rx prop0 propi tran_pgt_owned
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
    simpl;left;done.

    destruct (tran.2) eqn:Heq_retri.
    { (* apply [mem_retrieve_retrieved] *)
     iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "mem_acc_tx") as "[mem_instr Hacc_mem_acc_tx]".

     iApply (mem_retrieve_retrieved ai with "[$PC $mem_instr $R0 $R1 $R2 $pgt_acc $re]").
     set_solver + Hin_ps_acc_tx.
     done.
     done.
     iNext.
     iIntros "(PC & mem_instr & R0 & R1 & R2 & pgt_acc & re) _".

     iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
     iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
     iDestruct (access_split with "pgt_acc") as "[pgt_acc pgt_acc']".

     iApply ("IH" $! _ _ trans _ Htotal_regs' with "[] [] [] [] regs tx pgt_tx pgt_acc pgt_acc' LB [fresh_handles tran trans]
                            tran_pgt_transferred [re retri retri'] R0z R1z R2z rx_state [$rx $pgt_rx] other_rx prop0 propi tran_pgt_owned
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
       simpl. left;done.
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


    destruct (rx_state)  eqn: Heq_rxstate.
    { (* apply [mem_retrieve_rx_full] *)
     iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "mem_acc_tx") as "[mem_instr Hacc_mem_acc_tx]".
     iApply (mem_retrieve_rx_full ai r1 with "[$PC $mem_instr $R0 $R1 $R2 $pgt_acc $re $tran $rx_state]").
     set_solver + Hin_ps_acc_tx.
     done.
     done.
     done.
     iNext.
     iIntros "(PC & mem_instr & R0 & R1 & R2 & pgt_acc & re & tran & rx_state) _".

     iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
     iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
     iDestruct (access_split with "pgt_acc") as "[pgt_acc pgt_acc']".

     iApply ("IH" $! _ _ trans _ Htotal_regs' with "[] [] [] [] regs tx pgt_tx pgt_acc pgt_acc' LB [fresh_handles tran trans]
                            tran_pgt_transferred [re retri retri'] R0z R1z R2z rx_state [$rx $pgt_rx] other_rx prop0 propi tran_pgt_owned
                            pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx]");auto.
     {
       iExists hpool.
       iSplitL "";auto.
       iFrame "fresh_handles".
       iSplitL "";auto.
       rewrite (big_sepM_delete _ trans).
       iSplitL "tran".
       rewrite -Hrw_tran.
       iExact "tran".
       done.
       done.
     }
     {
       rewrite /retrieval_entries_transferred.
       iDestruct (big_sepFM_delete_acc_True tran with "retri") as "retri".
       simpl. left;done.
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
      iDestruct (big_sepFM_lookup_Some Hlookup_tran with "tran_pgt_transferred") as "[[tran' [own_tran excl_tran]] tran_pgt_transferred]".
      simpl. split;first done. left;done.
      rewrite Hrw_tran; clear Hrw_tran.
      iDestruct (trans_split with "[$tran $tran']") as "tran".

      assert (pages_in_trans (trans_memory_in_trans i (delete r1 trans)) = ps_mem_in_trans ∖ tran.1.1.2) as Hrewrite.
      {
        rewrite /trans_memory_in_trans.
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

        iApply (mem_retrieve_donate ai r1 with "[$PC $mem_instr $R0 $R1 $own_tran $pgt_acc $re $tran $rx $rx_state $mem_rx $fresh_handles]").
        set_solver + Hin_ps_acc_tx.
        done.
        done.
        iNext.
        simpl.
        iIntros "(PC & mem_instr & R0 & R1 & own_tran & pgt_acc & rx & (%wl & %des & rx_state & _ & _ & mem_rx) & fresh_handles) _".

        iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
        iDestruct ("Hacc_mem_acc_tx_rx" with "[$mem_instr]") as "mem_acc_tx_rx".
        iDestruct (access_split with "pgt_acc") as "[pgt_acc pgt_acc']".

        iApply ("IH" $! _ _ (delete r1 trans) _ Htotal_regs' with "[] [] [] [] regs tx pgt_tx pgt_acc pgt_acc' LB [fresh_handles trans]
                            [tran_pgt_transferred] [retri retri'] R0z R1z R2z rx_state [$rx $pgt_rx] other_rx prop0 propi [tran_pgt_owned]
                            [own_tran excl_tran pgt_owned] [retri_owned] [mem_rest mem_acc_tx_rx mem_rx mem_tx]").
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
          assert (pages_in_trans (delete r1 trans) = pages_in_trans trans ∖ tran.1.1.2) as ->.
          {
            apply pages_in_trans_delete;auto.
          }
          rewrite (difference_union_distr_l_L tran.1.1.2).
          assert (tran.1.1.2 ∖ {[p_rx;p_tx]} = tran.1.1.2) as ->.
          set_solver + Hnin_rx Hnin_tx Hsubseteq_tran.
          rewrite (difference_union_distr_l_L tran.1.1.2).
          assert (tran.1.1.2 ∖ (pages_in_trans trans ∖ tran.1.1.2) = tran.1.1.2) as ->.
          set_solver + Hsubseteq_tran.
          assert (ps_mem_in_trans ⊆ pages_in_trans trans) as Hsub.
          apply pages_in_trans_subseteq.
          apply map_filter_subseteq.
          assert (tran.1.1.2 ∪ ps_acc ∖ {[p_rx; p_tx]} ∖ (pages_in_trans trans ∖ tran.1.1.2) = tran.1.1.2 ∪ ps_acc ∖ {[p_rx; p_tx]} ∖ pages_in_trans trans) as ->.
          set A := (ps_acc ∖ {[p_rx; p_tx]}).
          set G := (tran.1.1.2 ∪ A ∖ (pages_in_trans trans ∖ tran.1.1.2)).

          rewrite (union_difference_L tran.1.1.2 (pages_in_trans trans) ).
          2: {
            set_solver + Hsub Hsubseteq_tran.
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
          set_solver + Hsubseteq_tran Hsub.
          iApply (big_sepS_union with "[$excl_tran $excl_owned]").
          set_solver + Hsubseteq_tran Hsub.
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

        iApply (mem_retrieve_donate_rx ai r1 with "[$PC $mem_instr $R0 $R1 $own_tran $pgt_acc $re $tran $rx $rx_state Hacc_mem_rx $fresh_handles]").
        done.
        done.
        iNext. iIntros "ai". iDestruct ("Hacc_mem_rx" with "ai") as "rx".
        iSplitL "". 2: iExact "rx". done.
        iNext. simpl.
        iIntros "(PC & R0 & R1 & own_tran & pgt_acc & rx & (%wl & %des & rx_state & _ & _ & mem_rx) & fresh_handles) _".

        iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
        iDestruct (access_split with "pgt_acc") as "[pgt_acc pgt_acc']".

        iApply ("IH" $! _ _ (delete r1 trans) _ Htotal_regs' with "[] [] [] [] regs tx pgt_tx pgt_acc pgt_acc' LB [fresh_handles trans]
                            [tran_pgt_transferred] [retri retri'] R0z R1z R2z rx_state [$rx $pgt_rx] other_rx prop0 propi [tran_pgt_owned]
                            [own_tran excl_tran pgt_owned] [retri_owned] [mem_rest mem_acc_tx_rx mem_rx mem_tx]").
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
          simpl. intros [_ ?]. contradiction.
        }
        {
          assert (pages_in_trans (delete r1 trans) = pages_in_trans trans ∖ tran.1.1.2) as ->.
          {
            apply pages_in_trans_delete;auto.
          }
          rewrite (difference_union_distr_l_L tran.1.1.2).
          assert (tran.1.1.2 ∖ {[(tpa ai);p_tx]} = tran.1.1.2) as ->.
          set_solver + Hnin_rx Hnin_tx Hsubseteq_tran.
          rewrite (difference_union_distr_l_L tran.1.1.2).
          assert (tran.1.1.2 ∖ (pages_in_trans trans ∖ tran.1.1.2) = tran.1.1.2) as ->.
          set_solver + Hsubseteq_tran.
          assert (ps_mem_in_trans ⊆ pages_in_trans trans) as Hsub.
          apply pages_in_trans_subseteq.
          apply map_filter_subseteq.
          assert (tran.1.1.2 ∪ ps_acc ∖ {[(tpa ai); p_tx]} ∖ (pages_in_trans trans ∖ tran.1.1.2) = tran.1.1.2 ∪ ps_acc ∖ {[(tpa ai); p_tx]} ∖ pages_in_trans trans) as ->.
          set A := (ps_acc ∖ {[(tpa ai); p_tx]}).
          set G := (tran.1.1.2 ∪ A ∖ (pages_in_trans trans ∖ tran.1.1.2)).
          rewrite (union_difference_L tran.1.1.2 (pages_in_trans trans) ).
          2: {
            set_solver + Hsub Hsubseteq_tran.
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
          set_solver + Hsubseteq_tran Hsub.
          iApply (big_sepS_union with "[$excl_tran $excl_owned]").
          set_solver + Hsubseteq_tran Hsub.
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
      }
    }
    { (* retrieve share*)
      assert (pages_in_trans (trans_memory_in_trans i (<[r1 := (tran.1, true)]> trans)) = pages_in_trans (trans_memory_in_trans i trans)) as Hrewrite.
      rewrite /trans_memory_in_trans.
      rewrite map_filter_insert_True.
      2: {
        simpl.
        right.
        done.
      }
      erewrite (pages_in_trans_insert' (tran:= tran) (tran' := (tran.1, true)));auto.
      rewrite map_filter_lookup_Some.
      split;auto.

      destruct Hlookup_mem_ai as [Hlookup_mem_ai|Hlookup_mem_ai].
      { (* apply [mem_retrieve_share]*)
        iDestruct (mem_big_sepM_split mem_acc_tx_rx Hlookup_mem_ai with "mem_acc_tx_rx") as "[mem_instr Hacc_mem_acc_tx_rx]".

        iApply (mem_retrieve_share ai r1 with "[$PC $mem_instr $R0 $R1 $pgt_acc $re $tran $rx $rx_state $mem_rx]").
        set_solver + Hin_ps_acc_tx.
        done. done.
        iNext. simpl.
        iIntros "(PC & mem_instr & R0 & R1 & pgt_acc & re & tran & rx & (%wl & %des & rx_state & _ & _ & mem_rx)) _".

        iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
        iDestruct ("Hacc_mem_acc_tx_rx" with "[$mem_instr]") as "mem_acc_tx_rx".
        iDestruct (access_split with "pgt_acc") as "[pgt_acc pgt_acc']".
        iDestruct (retri_split with "re") as "[re re']".

        iApply ("IH" $! _ _ (<[r1 := ((tran.1, true):transaction)]> trans) _ Htotal_regs' with "[] [] [] [] regs tx pgt_tx pgt_acc pgt_acc' LB
                            [fresh_handles trans tran]
                            [tran_pgt_transferred] [retri retri' re] R0z R1z R2z rx_state [$rx $pgt_rx] other_rx prop0 propi [tran_pgt_owned]
                            [pgt_owned] [retri_owned re'] [mem_rest mem_acc_tx_rx mem_rx mem_tx]").
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
          iExists hpool.
          iSplitL "".
          rewrite dom_insert_lookup_L //.
          iFrame "fresh_handles".
          iSplitL "".
          iPureIntro.
          apply (trans_ps_disj_update Htrans_ps_disj Hlookup_tran).
          done.
          iApply (big_sepM_delete _ (<[r1:=(tran.1, true)]> trans) r1 (tran.1,true)).
          rewrite lookup_insert_Some.
          left. split;done.
          rewrite Hrw_tran /=.
          iSplitL "tran". iExact "tran".
          rewrite delete_insert_delete //.
        }
        {
          rewrite /transaction_pagetable_entries_transferred.
          rewrite Hrw_tran /=.
          iApply (big_sepFM_update_False _ Hlookup_tran);auto.
          simpl. rewrite Heq_tran_tt. intros [? _]. done.
          simpl. intros [? _]. done.
        }
        {
          rewrite /retrieval_entries_transferred.
          iDestruct (big_sepFM_delete_acc_True (tran.1, true) with "retri") as "retri".
          simpl. left;done.
          iDestruct (big_sepFM_delete_acc_False (tran.1, true) with "retri'") as "retri'".
          simpl. intro. destruct H;done.
          iDestruct ("retri" with "re") as "retri".
          iFrame.
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
          rewrite (pages_in_trans_insert' Hlookup_tran).
          assert ((tran.1.1.2 ∪ ps_acc) ∖ {[p_rx; p_tx]} ∖ pages_in_trans trans = ps_acc ∖ {[p_rx; p_tx]} ∖ pages_in_trans trans) as ->.
          {
            rewrite 2!difference_difference_L.
            rewrite difference_union_distr_l_L.
            assert (tran.1.1.2 ∖ ({[p_rx; p_tx]} ∪ pages_in_trans trans) = ∅) as ->.
            {
              rewrite difference_union_distr_r_L.
              assert (tran.1.1.2 ∖ pages_in_trans trans = ∅) as ->.
              {
                assert (ps_mem_in_trans ⊆ pages_in_trans trans) as Hsub.
                apply pages_in_trans_subseteq.
                apply map_filter_subseteq.
                set_solver + Hsub Hsubseteq_tran.
              }
              set_solver +.
            }
            set_solver +.
          }
          done.
          done.
        }
        {
          rewrite /retrieval_entries_owned.
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
          assert ((tran.1.1.2 ∪ pages_in_trans (trans_memory_in_trans i trans)) = pages_in_trans (trans_memory_in_trans i trans)) as ->.
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

        iApply (mem_retrieve_share_rx ai r1 with "[$PC $mem_instr $R0 $R1 $pgt_acc $re $tran $rx $rx_state Hacc_mem_rx]").
        done.
        done.
        iNext. iIntros "ai". iDestruct ("Hacc_mem_rx" with "ai") as "rx".
        iSplitL "". 2: iExact "rx". done.
        iNext.
        simpl.
        iIntros "(PC & mem_instr & R0 & R1 & pgt_acc & re & tran & rx & (%wl & %des & rx_state & _ & _ & mem_rx)) _".

        iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
        iDestruct (access_split with "pgt_acc") as "[pgt_acc pgt_acc']".
        iDestruct (retri_split with "re") as "[re re']".

        iApply ("IH" $! _ _ (<[r1 := ((tran.1, true):transaction)]> trans) _ Htotal_regs' with "[] [] [] []regs tx pgt_tx pgt_acc pgt_acc' LB
                            [fresh_handles trans tran]
                            [tran_pgt_transferred] [retri retri' re] R0z R1z R2z rx_state [$rx $pgt_rx] other_rx prop0 propi [tran_pgt_owned]
                            [pgt_owned] [retri_owned re'] [mem_rest mem_acc_tx_rx mem_rx mem_tx]").
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
          iExists hpool.
          iSplitL "".
          rewrite dom_insert_lookup_L //.
          iFrame "fresh_handles".
          iSplitL "".
          iPureIntro.
          apply (trans_ps_disj_update Htrans_ps_disj Hlookup_tran).
          done.
          iApply (big_sepM_delete _ (<[r1:=(tran.1, true)]> trans) r1 (tran.1,true)).
          rewrite lookup_insert_Some.
          left. split;done.
          rewrite Hrw_tran /=.
          iSplitL "tran". iExact "tran".
          rewrite delete_insert_delete //.
        }
        {
          rewrite /transaction_pagetable_entries_transferred.
          rewrite Hrw_tran /=.
          iApply (big_sepFM_update_False _ Hlookup_tran);auto.
          simpl. rewrite Heq_tran_tt. intros [? _]. done.
          simpl. intros [? _]. done.
        }
        {
          rewrite /retrieval_entries_transferred.
          iDestruct (big_sepFM_delete_acc_True (tran.1, true) with "retri") as "retri".
          simpl. left;done.
          iDestruct (big_sepFM_delete_acc_False (tran.1, true) with "retri'") as "retri'".
          simpl. intro. destruct H;done.
          iDestruct ("retri" with "re") as "retri".
          iFrame.
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
          rewrite (pages_in_trans_insert' Hlookup_tran).
          assert ((tran.1.1.2 ∪ ps_acc) ∖ {[(tpa ai); p_tx]} ∖ pages_in_trans trans = ps_acc ∖ {[tpa ai; p_tx]} ∖ pages_in_trans trans) as ->.
          {
            rewrite 2!difference_difference_L.
            rewrite difference_union_distr_l_L.
            assert (tran.1.1.2 ∖ ({[tpa ai; p_tx]} ∪ pages_in_trans trans) = ∅) as ->.
            {
              rewrite difference_union_distr_r_L.
              assert (tran.1.1.2 ∖ pages_in_trans trans = ∅) as ->.
              {
                assert (ps_mem_in_trans ⊆ pages_in_trans trans) as Hsub.
                apply pages_in_trans_subseteq.
                apply map_filter_subseteq.
                set_solver + Hsub Hsubseteq_tran.
              }
              set_solver +.
            }
            set_solver +.
          }
          done.
          done.
        }
        {
          rewrite /retrieval_entries_owned.
          iDestruct (big_sepFM_delete_False Hlookup_tran with "retri_owned") as "retri_owned".
          simpl. intros [_ ?]. rewrite H  // in Heq_retri.
          iApply (big_sepFM_delete_acc_True with "[$retri_owned]").
          simpl. split;done.
          simpl; iFrame.
        }
        {
          assert (pages_in_trans (trans_memory_in_trans i (<[r1 := (tran.1, true)]> trans)) = pages_in_trans (trans_memory_in_trans i trans)) as H.
          rewrite /trans_memory_in_trans.
          rewrite map_filter_insert_True.
          2: { simpl. right. done. }
          erewrite (pages_in_trans_insert' (tran:= tran) (tran' := (tran.1, true)));auto.
          rewrite map_filter_lookup_Some.
          split;auto.
          rewrite H;clear H.
          rewrite (union_comm_L tran.1.1.2).
          rewrite -(union_assoc_L ps_acc tran.1.1.2).
          assert ((tran.1.1.2 ∪ pages_in_trans (trans_memory_in_trans i trans)) = pages_in_trans (trans_memory_in_trans i trans)) as ->.
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
      }
    }
    { (* retrieve lending*)

      assert (pages_in_trans (trans_memory_in_trans i (<[r1 := (tran.1, true)]> trans)) = pages_in_trans (trans_memory_in_trans i trans)) as Hrewrite.
      rewrite /trans_memory_in_trans.
      rewrite map_filter_insert_True.
      2: { simpl. right. done. }
      erewrite (pages_in_trans_insert' (tran:= tran) (tran' := (tran.1, true)));auto.
      rewrite map_filter_lookup_Some.
      split;auto.

      destruct Hlookup_mem_ai as [Hlookup_mem_ai|Hlookup_mem_ai].
      { (* apply [mem_retrieve_lend]*)
        iDestruct (mem_big_sepM_split mem_acc_tx_rx Hlookup_mem_ai with "mem_acc_tx_rx") as "[mem_instr Hacc_mem_acc_tx_rx]".

        iApply (mem_retrieve_lend ai r1 with "[$PC $mem_instr $R0 $R1 $pgt_acc $re $tran $rx $rx_state $mem_rx]").
        set_solver + Hin_ps_acc_tx.
        done. done.
        iNext. simpl.
        iIntros "(PC & mem_instr & R0 & R1 & pgt_acc & re & tran & rx & (%wl & %des & rx_state & _ & _ & mem_rx)) _".

        iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
        iDestruct ("Hacc_mem_acc_tx_rx" with "[$mem_instr]") as "mem_acc_tx_rx".
        iDestruct (access_split with "pgt_acc") as "[pgt_acc pgt_acc']".
        iDestruct (retri_split with "re") as "[re re']".

        iApply ("IH" $! _ _ (<[r1 := ((tran.1, true):transaction)]> trans) _ Htotal_regs' with "[] [] [] [] regs tx pgt_tx pgt_acc pgt_acc' LB
                            [fresh_handles trans tran]
                            [tran_pgt_transferred] [retri retri' re] R0z R1z R2z rx_state [$rx $pgt_rx] other_rx prop0 propi [tran_pgt_owned]
                            [pgt_owned] [retri_owned re'] [mem_rest mem_acc_tx_rx mem_rx mem_tx]").
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
          iExists hpool.
          iSplitL "".
          rewrite dom_insert_lookup_L //.
          iFrame "fresh_handles".
          iSplitL "".
          iPureIntro.
          apply (trans_ps_disj_update Htrans_ps_disj Hlookup_tran).
          done.
          iApply (big_sepM_delete _ (<[r1:=(tran.1, true)]> trans) r1 (tran.1,true)).
          rewrite lookup_insert_Some.
          left. split;done.
          rewrite Hrw_tran /=.
          iSplitL "tran". iExact "tran".
          rewrite delete_insert_delete //.
        }
        {
          rewrite /transaction_pagetable_entries_transferred.
          rewrite Hrw_tran /=.
          iApply (big_sepFM_update_False _ Hlookup_tran);auto.
          simpl. rewrite Heq_tran_tt. intros [? _]. done.
          simpl. intros [? _]. done.
        }
        {
          rewrite /retrieval_entries_transferred.
          iDestruct (big_sepFM_delete_acc_True (tran.1, true) with "retri") as "retri".
          simpl. left;done.
          iDestruct (big_sepFM_delete_acc_False (tran.1, true) with "retri'") as "retri'".
          simpl. intro. destruct H;done.
          iDestruct ("retri" with "re") as "retri".
          iFrame.
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
          rewrite (pages_in_trans_insert' Hlookup_tran).
          assert ((tran.1.1.2 ∪ ps_acc) ∖ {[p_rx; p_tx]} ∖ pages_in_trans trans = ps_acc ∖ {[p_rx; p_tx]} ∖ pages_in_trans trans) as ->.
          {
            rewrite 2!difference_difference_L.
            rewrite difference_union_distr_l_L.
            assert (tran.1.1.2 ∖ ({[p_rx; p_tx]} ∪ pages_in_trans trans) = ∅) as ->.
            {
              rewrite difference_union_distr_r_L.
              assert (tran.1.1.2 ∖ pages_in_trans trans = ∅) as ->.
              {
                assert (ps_mem_in_trans ⊆ pages_in_trans trans) as Hsub.
                apply pages_in_trans_subseteq.
                apply map_filter_subseteq.
                set_solver + Hsub Hsubseteq_tran.
              }
              set_solver +.
            }
            set_solver +.
          }
          done.
          done.
        }
        {
          rewrite /retrieval_entries_owned.
          iDestruct (big_sepFM_delete_False Hlookup_tran with "retri_owned") as "retri_owned".
          simpl. intros [_ ?]. rewrite H  // in Heq_retri.
          iApply (big_sepFM_delete_acc_True with "[$retri_owned]").
          simpl. split;done.
          simpl; iFrame.
        }
        {
          assert (pages_in_trans (trans_memory_in_trans i (<[r1 := (tran.1, true)]> trans)) = pages_in_trans (trans_memory_in_trans i trans)) as H.
          rewrite /trans_memory_in_trans.
          rewrite map_filter_insert_True.
          2: { simpl. right. done. }
          erewrite (pages_in_trans_insert' (tran:= tran) (tran' := (tran.1, true)));auto.
          rewrite map_filter_lookup_Some.
          split;auto.
          rewrite H;clear H.
          rewrite (union_comm_L tran.1.1.2).
          rewrite -(union_assoc_L ps_acc tran.1.1.2).
          assert ((tran.1.1.2 ∪ pages_in_trans (trans_memory_in_trans i trans)) = pages_in_trans (trans_memory_in_trans i trans)) as ->.
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

        iApply (mem_retrieve_lend_rx ai r1 with "[$PC $mem_instr $R0 $R1 $pgt_acc $re $tran $rx $rx_state Hacc_mem_rx]").
        done.
        done.
        iNext. iIntros "ai". iDestruct ("Hacc_mem_rx" with "ai") as "rx".
        iSplitL "". 2: iExact "rx". done.
        iNext.
        simpl.
        iIntros "(PC & mem_instr & R0 & R1 & pgt_acc & re & tran & rx & (%wl & %des & rx_state & _ & _ & mem_rx)) _".

        iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
        iDestruct (access_split with "pgt_acc") as "[pgt_acc pgt_acc']".
        iDestruct (retri_split with "re") as "[re re']".

        iApply ("IH" $! _ _ (<[r1 := ((tran.1, true):transaction)]> trans) _ Htotal_regs' with "[] [] [] [] regs tx pgt_tx pgt_acc pgt_acc' LB
                            [fresh_handles trans tran]
                            [tran_pgt_transferred] [retri retri' re] R0z R1z R2z rx_state [$rx $pgt_rx] other_rx prop0 propi [tran_pgt_owned]
                            [pgt_owned] [retri_owned re'] [mem_rest mem_acc_tx_rx mem_rx mem_tx]").
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
          iExists hpool.
          iSplitL "".
          rewrite dom_insert_lookup_L //.
          iFrame "fresh_handles".
          iSplitL "".
          iPureIntro.
          apply (trans_ps_disj_update Htrans_ps_disj Hlookup_tran).
          done.
          iApply (big_sepM_delete _ (<[r1:=(tran.1, true)]> trans) r1 (tran.1,true)).
          rewrite lookup_insert_Some.
          left. split;done.
          rewrite Hrw_tran /=.
          iSplitL "tran". iExact "tran".
          rewrite delete_insert_delete //.
        }
        {
          rewrite /transaction_pagetable_entries_transferred.
          rewrite Hrw_tran /=.
          iApply (big_sepFM_update_False _ Hlookup_tran);auto.
          simpl. rewrite Heq_tran_tt. intros [? _]. done.
          simpl. intros [? _]. done.
        }
        {
          rewrite /retrieval_entries_transferred.
          iDestruct (big_sepFM_delete_acc_True (tran.1, true) with "retri") as "retri".
          simpl. left;done.
          iDestruct (big_sepFM_delete_acc_False (tran.1, true) with "retri'") as "retri'".
          simpl. intro. destruct H;done.
          iDestruct ("retri" with "re") as "retri".
          iFrame.
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
          rewrite (pages_in_trans_insert' Hlookup_tran).
          assert ((tran.1.1.2 ∪ ps_acc) ∖ {[(tpa ai); p_tx]} ∖ pages_in_trans trans = ps_acc ∖ {[tpa ai; p_tx]} ∖ pages_in_trans trans) as ->.
          {
            rewrite 2!difference_difference_L.
            rewrite difference_union_distr_l_L.
            assert (tran.1.1.2 ∖ ({[tpa ai; p_tx]} ∪ pages_in_trans trans) = ∅) as ->.
            {
              rewrite difference_union_distr_r_L.
              assert (tran.1.1.2 ∖ pages_in_trans trans = ∅) as ->.
              {
                assert (ps_mem_in_trans ⊆ pages_in_trans trans) as Hsub.
                apply pages_in_trans_subseteq.
                apply map_filter_subseteq.
                set_solver + Hsub Hsubseteq_tran.
              }
              set_solver +.
            }
            set_solver +.
          }
          done.
          done.
        }
        {
          rewrite /retrieval_entries_owned.
          iDestruct (big_sepFM_delete_False Hlookup_tran with "retri_owned") as "retri_owned".
          simpl. intros [_ ?]. rewrite H  // in Heq_retri.
          iApply (big_sepFM_delete_acc_True with "[$retri_owned]").
          simpl. split;done.
          simpl; iFrame.
        }
        {
          assert (pages_in_trans (trans_memory_in_trans i (<[r1 := (tran.1, true)]> trans)) = pages_in_trans (trans_memory_in_trans i trans)) as H.
          rewrite /trans_memory_in_trans.
          rewrite map_filter_insert_True.
          2: { simpl. right. done. }
          erewrite (pages_in_trans_insert' (tran:= tran) (tran' := (tran.1, true)));auto.
          rewrite map_filter_lookup_Some.
          split;auto.
          rewrite H;clear H.
          rewrite (union_comm_L tran.1.1.2).
          rewrite -(union_assoc_L ps_acc tran.1.1.2).
          assert ((tran.1.1.2 ∪ pages_in_trans (trans_memory_in_trans i trans)) = pages_in_trans (trans_memory_in_trans i trans)) as ->.
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
      }
    }
  Qed.

End ftlr_retrieve.
