From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.algebra Require Import base pagetable mem trans.
From HypVeri.rules Require Import yield.
From HypVeri.logrel Require Import logrel logrel_extra.
From HypVeri Require Import proofmode.
Import uPred.

Section ftlr_yield.
  Context `{hypconst:HypervisorConstants}.
  Context `{hypparams:!HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.

Lemma ftlr_yield {i mem_acc_tx ai regs ps_acc p_tx p_rx instr trans rx_state r0}:
  base_extra.is_total_gmap regs ->
  {[p_tx; p_rx]} ⊆ ps_acc ->
  i ≠ V0 ->
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
  decode_hvc_func r0 = Some Yield ->
  p_tx ≠ p_rx ->
  ⊢
▷ (∀ (a : gmap reg_name Addr) (a0 : gset PID) (a1 : gmap Addr transaction) (a2 : option (Addr * VMID)),
              ⌜base_extra.is_total_gmap a⌝
              → ⌜{[p_tx; p_rx]} ⊆ a0⌝
                → ⌜p_rx ∉ a0 ∖ {[p_rx; p_tx]} ∪ accessible_in_trans_memory_pages i a1⌝
                  → ⌜p_tx ∉ a0 ∖ {[p_rx; p_tx]} ∪ accessible_in_trans_memory_pages i a1⌝
                    → ([∗ map] r↦w ∈ a, r @@ i ->r w) -∗
                      TX@i:=p_tx -∗
                      p_tx -@O> - ∗ p_tx -@E> true -∗
                      i -@A> a0 -∗
                      pagetable_entries_excl_owned i (a0 ∖ {[p_rx; p_tx]} ∖ currently_accessible_in_trans_memory_pages i a1) -∗
                      transaction_hpool_global_transferred a1 -∗
                      transaction_pagetable_entries_transferred i a1 -∗
                      retrievable_transaction_transferred i a1 -∗
                      R0 @@ V0 ->r encode_hvc_func Run -∗
                      R1 @@ V0 ->r encode_vmid i -∗
                      (∃ r2 : Addr, R2 @@ V0 ->r r2) -∗
                      RX_state@i:= a2 -∗
                      mailbox.rx_page i p_rx -∗
                      rx_pages (list_to_set list_of_vmids ∖ {[i]}) -∗
                      ▷ VMProp V0 (vmprop_zero i p_tx p_rx) (1 / 2) -∗
                      VMProp i (vmprop_unknown i p_tx p_rx) 1 -∗
                      transaction_pagetable_entries_owned i a1 -∗
                      retrieved_transaction_owned i a1 -∗
                      (∃ mem : lang.mem, memory_pages (a0 ∪ (accessible_in_trans_memory_pages i a1)) mem) -∗
                      WP ExecI @ i {{ _, True }}) -∗
   ([∗ map] r↦w ∈ regs, r @@ i ->r w) -∗
   TX@i:=p_tx -∗
   p_tx -@O> - ∗ p_tx -@E> true -∗
   i -@A> ps_acc -∗
   pagetable_entries_excl_owned i (ps_acc ∖ {[p_rx; p_tx]} ∖ (currently_accessible_in_trans_memory_pages i trans)) -∗
   transaction_hpool_global_transferred trans -∗
   transaction_pagetable_entries_transferred i trans -∗
   retrievable_transaction_transferred i trans -∗
   R0 @@ V0 ->r encode_hvc_func Run -∗
   R1 @@ V0 ->r encode_vmid i -∗
   (∃ r2 : Addr, R2 @@ V0 ->r r2) -∗
   RX_state@i:= rx_state -∗
   mailbox.rx_page i p_rx -∗
   rx_pages (list_to_set list_of_vmids ∖ {[i]}) -∗
   ▷ VMProp V0 (vmprop_zero i p_tx p_rx) (1 / 2) -∗
   VMProp i (vmprop_unknown i p_tx p_rx) 1 -∗
   transaction_pagetable_entries_owned i trans -∗
   retrieved_transaction_owned i trans -∗
   (∃ mem1 : mem, memory_pages ((ps_acc ∪ (accessible_in_trans_memory_pages i trans)) ∖ ps_acc) mem1) -∗
   ([∗ map] k↦v ∈ mem_acc_tx, k ->a v) -∗
   (∃ mem2 : mem, memory_page p_tx mem2) -∗
   SSWP ExecI @ i {{ bm, (if bm.1 then VMProp_holds i (1 / 2) else True) -∗ WP bm.2 @ i {{ _, True }} }}.
  Proof.
    iIntros (Htotal_regs Hsubset_mb Hneq_0 Hnin_rx Hnin_tx Hlookup_PC Hin_ps_acc Hneq_ptx Hdom_mem_acc_tx Hin_ps_acc_tx
                         Hlookup_mem_ai Heqn Hlookup_reg_R0 Hdecode_hvc Hneq_mb).
    iIntros  "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri R0z R1z R2z rx_state rx other_rx prop0
             propi tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx".
    set ps_mem_in_trans := (accessible_in_trans_memory_pages i trans).
    iDestruct (reg_big_sepM_split_upd2 i Hlookup_PC Hlookup_reg_R0  with "[$regs]") as "(PC & R0 & Hacc_regs)";eauto.
    pose proof (union_split_difference_intersection_L (ps_acc∖ {[p_tx]}) ({[p_rx]} ∪ (transferred_memory_pages i trans))) as [Heq_ps_acc_tx Hdisj_ps_acc_tx].
    rewrite Heq_ps_acc_tx in Hdom_mem_acc_tx.
    rewrite set_of_addr_union in Hdom_mem_acc_tx;last auto.
    apply dom_union_inv_L in Hdom_mem_acc_tx;last apply set_of_addr_disj;auto.
    destruct Hdom_mem_acc_tx as (mem_oea & mem_inters & Heq_mem_acc_tx' & Hdisj_mem_oea_inters & Hdom_mem_oea & Hdom_mem_inters).
    rewrite Heq_mem_acc_tx'.
    iDestruct (big_sepM_union with "mem_acc_tx") as "[mem_oea mem_inters]";auto.

    (* for simplication *)
    assert (Heq_inter_diff_union: (ps_acc ∖ {[p_tx]}) ∩ ({[p_rx]} ∪ (transferred_memory_pages i trans)) ∪
                                    ((ps_acc ∪ (ps_mem_in_trans)) ∖ ps_acc)
                                  = {[p_rx]} ∪ (transferred_memory_pages i trans)).
    {
      assert ((ps_acc ∪ ps_mem_in_trans) ∖ ps_acc = ps_mem_in_trans ∖ (ps_acc∖ {[p_tx]})) as ->.
      {
        assert ((ps_acc ∪ ps_mem_in_trans) ∖ ps_acc = ps_mem_in_trans ∖ ps_acc) as ->.
        set_solver +.
        set_solver + Hnin_tx.
      }
      rewrite intersection_union_l_L.
      rewrite -union_assoc_L.
      rewrite intersection_comm_L.
      rewrite subseteq_intersection_1_L.
      2: { apply subseteq_difference_r. set_solver. set_solver + Hsubset_mb. }
      pose proof (union_split_difference_intersection_L (transferred_memory_pages i trans) (ps_acc∖ {[p_tx]})) as [Heq _].
      rewrite union_comm_L intersection_comm_L in Heq.
      f_equal.
      (* TODO: we need a new assertion in logrel: currently_accessible_in_tran_memory_pages ⊆ ps_acc ∖ {[p_rx; p_tx]},
         the question is do we need something even stronger?? *)
      admit.
    }

    (* we have this annoying case anlaysis because we need to know if the instruction is in the memory pages required by VMProp 0 *)
    destruct (decide ((tpa ai) ∈ ((ps_acc∖ {[p_tx]}) ∖ ({[p_rx]} ∪ transferred_memory_pages i trans)))) as [Hin_ps_oea | Hnin_ps_oea].
    { (* instruction is in ps_oea *)
      (* in this case, we don't need to transfer instruction *)
      assert (Hsubseteq_mem_acc: mem_oea ⊆ mem_acc_tx).
      rewrite Heq_mem_acc_tx'.
      apply map_union_subseteq_l.
      rewrite map_subseteq_spec in Hsubseteq_mem_acc.
      apply elem_of_set_of_addr_tpa in Hin_ps_oea.
      rewrite -Hdom_mem_oea in Hin_ps_oea.
      rewrite elem_of_dom in Hin_ps_oea.
      destruct Hin_ps_oea as [? Hlookup_mem_ai'].
      specialize (Hsubseteq_mem_acc ai _ Hlookup_mem_ai').
      rewrite Hlookup_mem_ai in Hsubseteq_mem_acc.
      inversion Hsubseteq_mem_acc.
      subst x. clear Hsubseteq_mem_acc.

      iAssert (memory_pages ((ps_acc ∖ {[p_tx]}) ∩ ({[p_rx]} ∪ (transferred_memory_pages i trans))) mem_inters)%I  with "[mem_inters]" as "mem_inters".
      { rewrite /memory_pages. iSplitL "";first done. iFrame. }

      (* merge [mem_inters] and [mem_rest] into [mem_trans] (including [mem_rx]) *)
      iDestruct (memory_pages_split_union'
                   ((ps_acc∖ {[p_tx]}) ∩ ({[p_rx]} ∪ (transferred_memory_pages i trans))) with "[mem_inters mem_rest]") as "mem_tran".
      2:{ iSplitL "mem_inters". iExists mem_inters. iFrame "mem_inters". iExact "mem_rest". }
      { set_solver +. }
      rewrite Heq_inter_diff_union.

      (* getting instruction from [mem_oea] *)
      iDestruct (mem_big_sepM_split mem_oea Hlookup_mem_ai' with "mem_oea") as "[mem_instr Hacc_mem]".
      iDestruct ("tx") as "#tx".
      iApply (yield ai (transaction_hpool_global_transferred trans ∗
                        transaction_pagetable_entries_transferred i trans ∗
                        retrievable_transaction_transferred i trans)%I _
               with "[PC R0 R0z R1z R2z pgt_acc $tx mem_instr other_rx prop0 propi trans_hpool_global tran_pgt_transferred mem_tran
                            retri rx_state rx]"); iFrameAutoSolve.
      {
        iSplitL "prop0". iFrame.
        iSplitL "propi". iFrame.
        iSplitR "trans_hpool_global tran_pgt_transferred retri".
        2:{ iFrame. }
        iNext.
        iIntros "((PC & mem_instr & pgt_acc & _ & R0i &R0z & R1z) & (trans_hpool_global & trans_pgt_transferred & retri) & propi)".
        iSplitL "trans_hpool_global trans_pgt_transferred retri R0z R1z R2z rx_state rx other_rx mem_tran propi".
        iExists trans. iFrame.
        (* split [mem_tran] into [mem_rx] and [mem_trans] *)
        iDestruct (memory_pages_split_union' with "mem_tran") as "[mem_rx mem_trans]".
        { pose proof (transferred_memory_pages_subseteq i trans) as Hs.
          set_solver + Hs Hnin_rx.
        }
        iFrame.
        rewrite memory_pages_singleton'. iFrame.
        iLeft. iFrame.
        iLeft. iFrame. iExists rx_state. iFrame.
        iCombine "PC mem_instr R0i pgt_acc" as "R'". iExact "R'".
      }
      iNext.
      iIntros "[(PC & mem_instr & R0i & pgt_acc) propi]".
      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f r0 with "[PC R0i]") as "[%regs' [%Htotal_regs' regs'']]"; iFrameAutoSolve.
      iDestruct ("Hacc_mem" with "[$mem_instr]") as "mem_oea".
      iSimpl. iIntros "Hholds".
      iDestruct (VMProp_holds_agree i with "[$Hholds $propi]") as "[Hres propi]".
      iEval (setoid_rewrite vmprop_unknown_eq) in "Hres".
      iEval (rewrite later_exist) in "Hres". iDestruct "Hres" as (trans') "Hres".
      iEval (rewrite later_exist) in "Hres". iDestruct "Hres" as (rx_state') "Hres".
      iEval (rewrite 11!later_sep) in "Hres".
      iDestruct "Hres" as "(>trans_hpool_global & >tran_pgt_transferred &
                         >retri & >mem_transferred & >R0z & >R1z & >R2z & >rx_state & >rx & >[% mem_rx] & >other_rx & prop0)".
      iDestruct (derive_trans_rel_secondary with "[$trans_hpool_global $retri $tran_pgt_owned $retri_owned]") as "%trans_rel".
      (* erewrite (trans_rel_secondary_retrieved_lending_memory_page);eauto. *)
      erewrite (trans_rel_secondary_currently_accessible_memory_pages);eauto.
      iDestruct (trans_rel_secondary_transaction_pagetable_entries_owned with "tran_pgt_owned") as "tran_pgt_owned";eauto.
      iDestruct (trans_rel_secondary_retrieved_transaction_owned with "retri_owned") as "retri_owned";eauto.
      clear trans_rel.

      iAssert (∃ mem_all : mem, memory_pages (ps_acc ∖ {[p_rx; p_tx]} ∪ accessible_in_trans_memory_pages i trans') mem_all)%I
        with "[mem_oea mem_transferred]" as (?) "mem".
      (* TODO: we need currently_accessible_in_tran_memory_pages ⊆ ps_acc ∖ {[p_rx; p_tx]} *)
      admit.

      iDestruct "mem_tx" as "[%mem_tx mem_tx]".
      iDestruct (memory_pages_disj_singleton with "[$mem $mem_rx]") as %Hnin_rx'.
      iDestruct (memory_pages_disj_singleton with "[$mem $mem_tx]") as %Hnin_tx'.
      iAssert (∃ mem, memory_pages (ps_acc ∪ accessible_in_trans_memory_pages i trans') mem)%I
        with "[mem mem_rx mem_tx]" as "mem".
      {
        iExists (mem_all ∪ mem_rx ∪ mem_tx).
        assert (accessible_in_trans_memory_pages i trans' ## {[p_tx]}) as Hdisj_ps_tx' by set_solver + Hnin_tx'.
        assert (accessible_in_trans_memory_pages i trans' ## {[p_rx]}) as Hdisj_ps_rx' by set_solver + Hnin_rx'.
        set ps_mem_in_trans' := (accessible_in_trans_memory_pages i trans').
        assert (ps_acc ∖ {[p_rx; p_tx]} ∪ ps_mem_in_trans' ∪ {[p_rx; p_tx]} = (ps_acc ∪ ps_mem_in_trans')) as <-.
        {
          rewrite -union_assoc_L.
          rewrite (union_comm_L _ {[p_rx; p_tx]}).
          rewrite union_assoc_L.
          rewrite difference_union_L.
          f_equal.
          rewrite union_comm_L.
          rewrite subseteq_union_1_L //.
          set_solver + Hsubset_mb.
        }
        iApply (memory_pages_split_union with "[mem mem_rx mem_tx]").
        { set_solver. }
        iDestruct (memory_page_neq with "[$mem_tx $mem_rx]") as %Hneq_tx_rx.
        iExists mem_all, (mem_rx ∪ mem_tx). iFrame "mem".
        rewrite memory_pages_split_union.
        iSplit.
        iExists mem_rx, mem_tx. rewrite 2!memory_pages_singleton. iFrame "mem_rx mem_tx".
        done.
        iPureIntro. rewrite map_union_assoc //. set_solver + Hneq_tx_rx.
      }
      iApply ("IH" $! _ ps_acc trans' _ Htotal_regs' Hsubset_mb Hnin_rx' Hnin_tx' with "regs'' tx pgt_tx pgt_acc pgt_owned
                       trans_hpool_global tran_pgt_transferred retri R0z R1z R2z rx_state rx other_rx prop0 propi
                           tran_pgt_owned  retri_owned mem").
    }
    { (* tpa ai ∉ ps_acc ∖ ({[p_rx]} ∪ ps_mem_in_trans) *)
      (* we don't need to touch [mem_oea]*)
      (* first show instr is in [mem_inters] *)
      assert (tpa ai ∈ (ps_acc∖ {[p_tx]}) ∩ ({[p_rx]} ∪ (transferred_memory_pages i trans) )) as Hin_ps_inters.
      {
        rewrite Heq_ps_acc_tx in Hin_ps_acc_tx.
        rewrite elem_of_union in Hin_ps_acc_tx.
        destruct Hin_ps_acc_tx;done.
      }
      assert (Hsubseteq_mem_acc: mem_inters ⊆ mem_acc_tx).
      { rewrite Heq_mem_acc_tx'. apply map_union_subseteq_r. done. }
      rewrite map_subseteq_spec in Hsubseteq_mem_acc.
      apply elem_of_set_of_addr_tpa in Hin_ps_inters.
      rewrite -Hdom_mem_inters in  Hin_ps_inters.
      rewrite elem_of_dom in Hin_ps_inters.
      destruct Hin_ps_inters as [? Hlookup_mem_ai'].
      specialize (Hsubseteq_mem_acc ai _ Hlookup_mem_ai').
      rewrite Hlookup_mem_ai in Hsubseteq_mem_acc.
      inversion Hsubseteq_mem_acc.
      subst x. clear Hsubseteq_mem_acc.

      (* get instruction *)
      iDestruct (mem_big_sepM_split mem_inters Hlookup_mem_ai' with "mem_inters") as "[mem_instr Hacc_mem_inters]".
      iDestruct ("tx") as "#tx".
      iApply (yield ai (transaction_hpool_global_transferred trans ∗
                        transaction_pagetable_entries_transferred i trans ∗
                        retrievable_transaction_transferred i trans) _
               with "[PC R0 R0z R1z R2z pgt_acc $tx mem_instr other_rx prop0 propi trans_hpool_global tran_pgt_transferred Hacc_mem_inters mem_rest
                            retri rx_state rx]"); iFrameAutoSolve.
      {
        iSplitL "prop0". iFrame.
        iSplitL "propi". iFrame.
        iSplitR "trans_hpool_global tran_pgt_transferred retri".
        2:{ iFrame. }
        iNext.
        iIntros "((PC & mem_instr & pgt_acc & _ & R0i &R0z & R1z) & (trans_hpool_global & trans_pgt_transferred & retri) & propi)".
        iDestruct ("Hacc_mem_inters" with "mem_instr") as "mem_inters".
        (* FIXME: copied proofs  *)
        iAssert (memory_pages ((ps_acc∖ {[p_tx]}) ∩ ({[p_rx]} ∪ (transferred_memory_pages i trans))) mem_inters)%I  with "[mem_inters]" as "mem_inters".
        { rewrite /memory_pages. iSplitL "";first done. iFrame. }
        (* [mem_inters] + [mem_rest] = [mem_tran] *)
        iDestruct (memory_pages_split_union'
                     ((ps_acc∖ {[p_tx]}) ∩ ({[p_rx]} ∪ (transferred_memory_pages i trans))) with "[mem_inters mem_rest]") as "mem_tran".
        2:{ iSplitL "mem_inters". iExists mem_inters. iFrame "mem_inters". iExact "mem_rest". }
        { set_solver +. }
        rewrite Heq_inter_diff_union.

        iSplitL "trans_hpool_global trans_pgt_transferred retri R0z R1z R2z rx_state rx other_rx mem_tran propi".
        iExists trans. iFrame "trans_hpool_global trans_pgt_transferred retri rx other_rx".
        (* split [mem_tran] into [mem_rx] and [mem_trans] *)
        iDestruct (memory_pages_split_union' with "mem_tran") as "[mem_rx mem_trans]".
        { pose proof (transferred_memory_pages_subseteq i trans) as Hs.
          set_solver + Hs Hnin_rx.
        }
        iFrame "mem_trans".
        rewrite memory_pages_singleton'. iFrame "mem_rx".
        iSplitR "propi".
        iLeft. iFrame.
        iLeft. iFrame. iExists rx_state. iFrame.
        iExact "propi".
        iCombine "PC R0i pgt_acc" as "R'". iExact "R'".
      }
      iNext.
      iIntros "[(PC & R0i & pgt_acc) propi]".
      iSimpl.
      iIntros "Hholds".
      iDestruct (VMProp_holds_agree i with "[$Hholds $propi]") as "[Hres propi]".
      iEval (setoid_rewrite vmprop_unknown_eq) in "Hres".
      iEval (rewrite later_exist) in "Hres". iDestruct "Hres" as (trans') "Hres".
      iEval (rewrite later_exist) in "Hres". iDestruct "Hres" as (rx_state') "Hres".
      iEval (rewrite 11!later_sep) in "Hres".
      iDestruct "Hres" as "(>trans_hpool_global & >tran_pgt_transferred &
                         >retri & >mem_transferred & >R0z & >R1z & >R2z & >rx_state & >rx & >[% mem_rx] & >other_rx & prop0)".
      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f r0 with "[PC R0i]") as "[%regs' [%Htotal_regs' regs'']]"; iFrameAutoSolve.
      iDestruct (derive_trans_rel_secondary with "[$trans_hpool_global $retri $tran_pgt_owned $retri_owned]") as "%trans_rel".
      (* erewrite (trans_rel_secondary_retrieved_lending_memory_page);eauto. *)
      erewrite (trans_rel_secondary_currently_accessible_memory_pages);eauto.
      iDestruct (trans_rel_secondary_transaction_pagetable_entries_owned with "tran_pgt_owned") as "tran_pgt_owned";eauto.
      iDestruct (trans_rel_secondary_retrieved_transaction_owned with "retri_owned") as "retri_owned";eauto.

      iAssert (∃ mem_all : mem, memory_pages (ps_acc ∖ {[p_rx; p_tx]} ∪ accessible_in_trans_memory_pages i trans') mem_all)%I
        with "[mem_oea mem_transferred]" as (?) "mem".
      (* TODO: we need currently_accessible_in_tran_memory_pages ⊆ ps_acc ∖ {[p_rx; p_tx]} *)
      admit.

      iDestruct "mem_tx" as "[%mem_tx mem_tx]".
      iDestruct (memory_pages_disj_singleton with "[$mem $mem_rx]") as %Hnin_rx'.
      iDestruct (memory_pages_disj_singleton with "[$mem $mem_tx]") as %Hnin_tx'.
      iAssert (∃ mem, memory_pages (ps_acc ∪ accessible_in_trans_memory_pages i trans') mem)%I
        with "[mem mem_rx mem_tx]" as "mem".
      {
        iExists (mem_all ∪ mem_rx ∪ mem_tx).
        assert (accessible_in_trans_memory_pages i trans' ## {[p_tx]}) as Hdisj_ps_tx' by set_solver + Hnin_tx'.
        assert (accessible_in_trans_memory_pages i trans' ## {[p_rx]}) as Hdisj_ps_rx' by set_solver + Hnin_rx'.
        set ps_mem_in_trans' := (accessible_in_trans_memory_pages i trans').
        assert (ps_acc ∖ {[p_rx; p_tx]} ∪ ps_mem_in_trans' ∪ {[p_rx; p_tx]} = (ps_acc ∪ ps_mem_in_trans')) as <-.
        {
          rewrite -union_assoc_L.
          rewrite (union_comm_L _ {[p_rx; p_tx]}).
          rewrite union_assoc_L.
          rewrite difference_union_L.
          f_equal.
          rewrite union_comm_L.
          rewrite subseteq_union_1_L //.
          set_solver + Hsubset_mb.
        }
        iApply (memory_pages_split_union with "[mem mem_rx mem_tx]").
        { set_solver. }
        iDestruct (memory_page_neq with "[$mem_tx $mem_rx]") as %Hneq_tx_rx.
        iExists mem_all, (mem_rx ∪ mem_tx). iFrame "mem".
        rewrite memory_pages_split_union.
        iSplit.
        iExists mem_rx, mem_tx. rewrite 2!memory_pages_singleton. iFrame "mem_rx mem_tx".
        done.
        iPureIntro. rewrite map_union_assoc //. set_solver + Hneq_tx_rx.
      }
      iApply ("IH" $! _ ps_acc trans' _ Htotal_regs' Hsubset_mb Hnin_rx' Hnin_tx' with "regs'' tx pgt_tx pgt_acc pgt_owned
                       trans_hpool_global tran_pgt_transferred retri R0z R1z R2z rx_state rx other_rx prop0 propi
                           tran_pgt_owned retri_owned mem").
    }
  Qed.

End ftlr_yield.
