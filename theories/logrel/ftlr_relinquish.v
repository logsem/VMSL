From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang trans_extra.
From HypVeri.algebra Require Import base pagetable mem trans.
From HypVeri.rules Require Import mem_relinquish.
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
  decode_hvc_func r0 = Some Relinquish ->
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
    iDestruct (access_split with "[$pgt_acc $pgt_acc']") as "pgt_acc".
    iDestruct "trans_hpool_global" as (hpool) "(%Heq_hsall & fresh_handles & %Htrans_ps_disj & trans)".

    destruct (decide (r1 ∈ hs_all)) as [Hin_hs_all |Hnotin_hs_all].
    2: { (* apply [mem_relinquish_invalid_handle] *)
      iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "mem_acc_tx") as "[mem_instr Hacc_mem_acc_tx]".

      iApply (mem_relinquish_invalid_handle ai with "[$PC $mem_instr $R0 $R1 $R2 $pgt_acc $tx]");auto.
      iNext.
      iIntros "(PC & mem_instr & R0 & R1 & R2 & pgt_acc & tx) _".

      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
      iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
      iDestruct (access_split with "pgt_acc") as "[pgt_acc pgt_acc']".

      iApply ("IH" $! _ _ trans _ Htotal_regs' with "[] [] [] [] regs tx pgt_tx pgt_acc pgt_acc' LB [fresh_handles trans]
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
    { (* apply [mem_relinquish_fresh_handle] *)
      iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "mem_acc_tx") as "[mem_instr Hacc_mem_acc_tx]".

      iApply (mem_relinquish_fresh_handle ai with "[$PC $mem_instr $R0 $R1 $R2 $pgt_acc $tx $fresh_handles]");auto.
      iNext.
      iIntros "(PC & mem_instr & R0 & R1 & R2 & pgt_acc & tx & fresh_handles) _".

      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
      iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
      iDestruct (access_split with "pgt_acc") as "[pgt_acc pgt_acc']".

      iApply ("IH" $! _ _ trans _ Htotal_regs' with "[] [] [] [] regs tx pgt_tx pgt_acc pgt_acc' LB [fresh_handles trans]
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

    destruct(decide (tran.1.1.1.2 = i)) as [Heq_tran | Hneq_tran].
    2: { (*apply [mem_relinquish_invalid_trans]*)
      iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "mem_acc_tx") as "[mem_instr Hacc_mem_acc_tx]".

      iApply (mem_relinquish_invalid_trans ai with "[$PC $mem_instr $R0 $R1 $R2 $pgt_acc $tx $tran]");auto.
      iNext.
      iIntros "(PC & mem_instr & R0 & R1 & R2 & pgt_acc & tx & tran) _".

      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
      iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
      iDestruct (access_split with "pgt_acc") as "[pgt_acc pgt_acc']".

      iApply ("IH" $! _ _ trans _ Htotal_regs' with "[] [] [] [] regs tx pgt_tx pgt_acc pgt_acc' LB [fresh_handles tran trans]
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
    simpl;left;done.

    destruct (tran.2) eqn:Heq_retri.
    2: { (* apply [mem_relinquish_not_retrieved] *)
      iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "mem_acc_tx") as "[mem_instr Hacc_mem_acc_tx]".

      iApply (mem_relinquish_not_retrieved ai with "[$PC $mem_instr $R0 $R1 $R2 $pgt_acc $tx $re]");auto.
      iNext.
      iIntros "(PC & mem_instr & R0 & R1 & R2 & pgt_acc & tx & re) _".

      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
      iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
      iDestruct (access_split with "pgt_acc") as "[pgt_acc pgt_acc']".

      iApply ("IH" $! _ _ trans _ Htotal_regs' with "[] [] [] [] regs tx pgt_tx pgt_acc pgt_acc' LB [fresh_handles tran trans]
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

    iDestruct (big_sepFM_lookup_Some Hlookup_tran with "retri_owned") as "[re' retri_owned]".
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
    assert (pages_in_trans (trans_memory_in_trans i (<[r1 := (tran.1, false)]> trans)) = pages_in_trans (trans_memory_in_trans i trans)) as Hrewrite.
    {
      rewrite /trans_memory_in_trans.
      rewrite map_filter_insert_True.
      2: {
        simpl. right. done.
      }
      erewrite (pages_in_trans_insert' (tran:= tran) (tran' := (tran.1, false)));auto.
      rewrite map_filter_lookup_Some.
      split;auto.
    }

    (* apply [mem_relinquish]*)
    iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "mem_acc_tx") as "[mem_instr Hacc_mem_acc_tx]".
    iApply (mem_relinquish ai with "[$PC $mem_instr $R0 $R1 $tx $pgt_acc $re $tran]");auto.
    iNext. simpl.
    iIntros "(PC & mem_instr & pgt_acc & R0 & R1 & tx & tran & re) _".

    iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
    iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
    iDestruct (access_split with "pgt_acc") as "[pgt_acc pgt_acc']".
    iDestruct (retri_split with "re") as "[re re']".

    iApply ("IH" $! _ _ (<[r1 := ((tran.1, false):transaction)]> trans) _ Htotal_regs' with "[] [] [] [] regs tx pgt_tx pgt_acc
                            pgt_acc' LB [fresh_handles trans tran]
                            [tran_pgt_transferred] [retri retri' re re'] R0z R1z R2z rx_state rx other_rx prop0 propi [tran_pgt_owned]
                            [pgt_owned] [retri_owned] [mem_rest mem_acc_tx mem_tx]").
    {
      iPureIntro.
      set_solver + Hsubset_mb Hsubseteq_tran Hnin_rx Hnin_tx.
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
      iExists hpool.
      iSplitL "".
      rewrite dom_insert_lookup_L //.
      iFrame "fresh_handles".
      iSplitL "".
      iPureIntro.
      apply (trans_ps_disj_update Htrans_ps_disj Hlookup_tran).
      done.
      iApply (big_sepM_delete _ (<[r1:=(tran.1, false)]> trans) r1 (tran.1,false)).
      rewrite lookup_insert_Some.
      left. split;done.
      rewrite Hrw_tran /=.
      iSplitL "tran". iExact "tran".
      rewrite delete_insert_delete //.
    }
    {
      rewrite /transaction_pagetable_entries_transferred.
      rewrite Hrw_tran /=.
      destruct (decide (tran.1.2 = Donation)).
      iApply big_sepFM_update_True.
      exact Hlookup_tran.
      simpl. split;auto.
      simpl. split;auto.
      iIntros "H". simpl. rewrite Hrw_tran. iFrame.
      iFrame.
      iApply (big_sepFM_update_False _ Hlookup_tran);auto.
      simpl. intros [? _]. contradiction.
      simpl. intros [? _]. contradiction.
    }
    {
      rewrite /retrieval_entries_transferred.
      iDestruct (big_sepFM_delete_acc_True (tran.1, false) with "retri") as "retri".
      simpl. left;done.
      iDestruct ("retri" with "re") as "retri".
      iFrame.
      iApply (big_sepFM_delete_acc_True with "[retri'] [re']").
      simpl. split;auto.
      rewrite big_sepFM_delete_False.
      iFrame "retri'".
      exact Hlookup_tran.
      simpl. intros [_ ?]. rewrite Heq_retri // in H.
      done.
    }
    {
      rewrite /transaction_pagetable_entries_owned.
      destruct (decide ((tran.1.1.1.1 = i ∧ tran.1.2 ≠ Donation))).
      iApply (big_sepFM_update_True _ Hlookup_tran).
      simpl. done.
      simpl. done.
      simpl. iIntros "?";iFrame.
      iFrame.
      iApply (big_sepFM_update_False _ Hlookup_tran).
      simpl. intros ?. contradiction.
      simpl. intros ?. contradiction.
      iFrame.
    }
    {
      rewrite (pages_in_trans_insert' Hlookup_tran);auto.
      assert ((ps_acc ∖ tran.1.1.2) ∖ {[p_rx; p_tx]} ∖ pages_in_trans trans = ps_acc ∖ {[p_rx; p_tx]} ∖ pages_in_trans trans) as ->.
      {
        rewrite 3!difference_difference_L.
        rewrite union_assoc_L.
        rewrite union_comm_L.
        rewrite union_assoc_L.
        assert ( pages_in_trans trans ∪ tran.1.1.2 = pages_in_trans trans) as ->.
        {
          assert (ps_mem_in_trans ⊆ pages_in_trans trans) as Hsub.
          apply pages_in_trans_subseteq.
          apply map_filter_subseteq.
          set_solver + Hsub Hsubseteq_tran.
        }
        set_solver +.
      }
      iFrame.
    }
    {
      rewrite /retrieval_entries_owned.
      iApply (big_sepFM_delete_acc_False _).
      simpl. intros [_ ?]. inversion H.
      done.
    }
    {
      rewrite Hrewrite.
      assert (ps_acc ∖ tran.1.1.2 ∪ pages_in_trans (trans_memory_in_trans i trans) = ps_acc ∪ pages_in_trans (trans_memory_in_trans i trans) ) as ->.
      {
        assert ((tran.1.1.2 ∪ pages_in_trans (trans_memory_in_trans i trans)) = pages_in_trans (trans_memory_in_trans i trans)) as <-.
        set_solver + Hsubseteq_tran.
        rewrite union_assoc_L.
        rewrite difference_union_L.
        set_solver +.
      }
      iApply (memory_pages_split_diff' _ ps_acc).
      set_solver +.
      iSplitL "mem_rest"; first done.
      iApply (memory_pages_split_singleton' p_tx with "[mem_acc_tx mem_tx]"). set_solver + Hsubset_mb.
      iSplitL "mem_acc_tx";last done.
      iExists mem_acc_tx; iFrame "mem_acc_tx";done.
    }
  Qed.
