From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.algebra Require Import base pagetable mem trans mailbox.
From HypVeri.rules Require Import msg_send.
From HypVeri.logrel Require Import logrel logrel_extra.
From HypVeri Require Import proofmode.
Import uPred.

Section ftlr_msg_send.
  Context `{hypconst:HypervisorConstants}.
  Context `{hypparams:!HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.

  Lemma ftlr_msg_send {i mem_acc_tx ai regs ps_acc p_tx p_rx instr trans rxs r0}:
    base_extra.is_total_gmap regs ->
    base_extra.is_total_gmap rxs ->
    i ≠ V0 ->
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
    decode_hvc_func r0 = Some Send ->
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
              ((∃ r0 : Addr, R0 @@ V0 ->r r0 ∗ ⌜decode_hvc_func r0 = Some Run⌝) ∗
              (∃ r1 : Addr, R1 @@ V0 ->r r1 ∗ ⌜decode_vmid r1 = Some i⌝) ∗ (∃ r2 : Addr, R2 @@ V0 ->r r2) ∗
              ▷ VMProp V0 (vmprop_zero i a1 a2) (1 / 2) ∗ VMProp i (vmprop_unknown i a1) 1) -∗
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
   ((∃ r0 : Addr, R0 @@ V0 ->r r0 ∗ ⌜decode_hvc_func r0 = Some Run⌝) ∗
    (∃ r1 : Addr, R1 @@ V0 ->r r1 ∗ ⌜decode_vmid r1 = Some i⌝) ∗ (∃ r2 : Addr, R2 @@ V0 ->r r2) ∗
    ▷ VMProp V0 (vmprop_zero i trans rxs) (1 / 2) ∗ VMProp i (vmprop_unknown i) 1) -∗
   SSWP ExecI @ i {{ bm, (if bm.1 then VMProp_holds i (1 / 2) else True) -∗ WP bm.2 @ i {{ _, True }} }}.
  Proof.
    iIntros (Htotal_regs Htotal_rxs Hneq_0 Hsubset_mb Hsubset_acc Hnin_rx Hnin_tx Hlookup_PC Hin_ps_acc Hneq_ptx Hdom_mem_acc_tx Hin_ps_acc_tx
                         Hlookup_mem_ai Heqn  Hlookup_reg_R0).
    iIntros (Hdecode_hvc Hneq_mb) "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri rx_state rx other_rx
             tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx ([%r00 [R0z %]]& [%r10 [R1z %]] & [%r20 R2z] & prop0 &propi)".
    set ps_mem_in_trans := accessible_in_trans_memory_pages i trans.
    pose proof (Htotal_regs R1) as[r1 Hlookup_reg_R1].
    pose proof (Htotal_regs R2) as[r2 Hlookup_reg_R2].
    iDestruct (reg_big_sepM_split_upd4 i Hlookup_PC Hlookup_reg_R0 Hlookup_reg_R1 Hlookup_reg_R2 with "[$regs]")
      as "(PC & R0 & R1 & R2 & Hacc_regs)";eauto.

    iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "mem_acc_tx") as "[mem_instr Hacc_mem_acc_tx]".
    destruct (decode_vmid r1) eqn:Heq_decode.
    2:{ (* apply [msg_send_invalid_receiver] *)
      iApply (msg_send_invalid_receiver ai with "[PC mem_instr pgt_acc R0 R1 R2 tx]");iFrameAutoSolve.
      iNext. iIntros "(PC & mem_instr & pgt_acc  & tx & R0 & R1 & R2) _".
      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".

      iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
      iApply ("IH" $! _ ps_acc trans _ Htotal_rxs Htotal_regs' Hsubset_mb Hsubset_acc Hnin_rx Hnin_tx with "regs tx pgt_tx rx pgt_acc pgt_owned trans_hpool_global
                            tran_pgt_transferred retri rx_state other_rx tran_pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx]
                            [R0z R1z R2z $propi $prop0]").
      {
        iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx $mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
        iExists mem_acc_tx;by iFrame "mem_acc_tx".
        iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
        set_solver +.
      }
      {
        iSplitL "R0z". iExists _; iFrame. done.
        iSplitL "R1z". iExists _; iFrame. done.
        iExists _. iFrame.
      }
    }

    destruct (decide (v = i)).
    { (* apply [msg_send_to_self] *)
      iApply (msg_send_to_self ai with "[PC mem_instr pgt_acc R0 R1 R2 tx]");iFrameAutoSolve.
      exact Heq_decode. done.
      iNext. iIntros "(PC & mem_instr & pgt_acc  & tx & R0 & R1 & R2) _".
      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".

      iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
      iApply ("IH" $! _ ps_acc trans _ Htotal_rxs Htotal_regs' Hsubset_mb Hsubset_acc Hnin_rx Hnin_tx with "regs tx pgt_tx rx pgt_acc pgt_owned trans_hpool_global
                            tran_pgt_transferred retri rx_state other_rx tran_pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx]
                            [R0z R1z R2z $propi $prop0]").
      {
        iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx $mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
        iExists mem_acc_tx;by iFrame "mem_acc_tx".
        iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
        set_solver +.
      }
      {
        iSplitL "R0z". iExists _; iFrame. done.
        iSplitL "R1z". iExists _; iFrame. done.
        iExists _. iFrame.
      }
    }

    destruct (decide (page_size < r2)%Z).
    { (*apply [msg_send_invalid_length]*)
      iApply (msg_send_invalid_length ai with "[PC mem_instr pgt_acc R0 R1 R2 tx]");iFrameAutoSolve.
      exact Heq_decode. done. lia.
      iNext. iIntros "(PC & mem_instr & pgt_acc  & tx & R0 & R1 & R2) _".
      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".

      iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
      iApply ("IH" $! _ ps_acc trans _ Htotal_rxs Htotal_regs' Hsubset_mb Hsubset_acc Hnin_rx Hnin_tx with "regs tx pgt_tx rx pgt_acc pgt_owned trans_hpool_global
                            tran_pgt_transferred retri rx_state other_rx tran_pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx]
                            [R0z R1z R2z $propi $prop0]").
      {
        iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx $mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
        iExists mem_acc_tx;by iFrame "mem_acc_tx".
        iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
        set_solver +.
      }
      {
        iSplitL "R0z". iExists _; iFrame. done.
        iSplitL "R1z". iExists _; iFrame. done.
        iExists _. iFrame.
      }
    }

    assert (is_Some((delete i rxs)!! v)) as Hin_v.
    {
      pose proof (Htotal_rxs v) as [? ?].
      exists x.
      rewrite lookup_delete_ne //.
    }

    destruct Hin_v as [rx_state_v Hin_v].
    iDestruct (big_sepM_delete with "other_rx") as "[rx_state_v other_rx]".
    exact Hin_v.

    destruct (rx_state_v).
    { (* apply [msg_send_full_rx] *)
      iEval (rewrite /rx_state_match /=) in "rx_state_v".
      iApply (msg_send_full_rx ai with "[PC mem_instr pgt_acc R0 R1 R2 tx rx_state_v]");iFrameAutoSolve.
      exact Heq_decode. done. lia. 2: { iDestruct "rx_state_v" as "[$ ?]". done. } done.
      iNext. iIntros "(PC & mem_instr & pgt_acc  & tx & R0 & R1 & R2 & rx_state_v ) _".
      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".

      iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
      iApply ("IH" $! _ ps_acc trans _ Htotal_rxs Htotal_regs' Hsubset_mb Hsubset_acc Hnin_rx Hnin_tx with "regs tx pgt_tx rx pgt_acc pgt_owned trans_hpool_global
                            tran_pgt_transferred retri rx_state [other_rx rx_state_v] tran_pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx]
                            [R0z R1z R2z $propi $prop0]").
      {
        iApply (big_sepM_delete with "[other_rx rx_state_v]").
        exact Hin_v.
        simpl. iFrame "other_rx".
        iFrame.
      }
      {
        iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx $mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
        iExists mem_acc_tx;by iFrame "mem_acc_tx".
        iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
        set_solver +.
      }
      {
        iSplitL "R0z". iExists _; iFrame. done.
        iSplitL "R1z". iExists _; iFrame. done.
        iExists _. iFrame.
      }
    }

    iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
    pose proof (union_split_difference_intersection_L (ps_acc∖ {[p_tx]}) ({[p_rx]} ∪ (transferred_memory_pages i trans))) as [Heq_ps_acc_tx Hdisj_ps_acc_tx].
    rewrite Heq_ps_acc_tx in Hdom_mem_acc_tx.
    rewrite set_of_addr_union in Hdom_mem_acc_tx;last auto.
    apply dom_union_inv_L in Hdom_mem_acc_tx;last apply set_of_addr_disj;auto.
    destruct Hdom_mem_acc_tx as (mem_oea & mem_inters & Heq_mem_acc_tx' & Hdisj_mem_oea_inters & Hdom_mem_oea & Hdom_mem_inters).
    rewrite Heq_mem_acc_tx'.
    iDestruct (big_sepM_union with "mem_acc_tx") as "[mem_oea mem_inters]";auto.

    iDestruct (get_trans_ps_disj with "trans_hpool_global") as %Hdisj.

    (* for simplication *)
    assert (Heq_inter_diff_union: (ps_acc ∖ {[p_tx]}) ∩ ({[p_rx]} ∪ (transferred_memory_pages i trans)) ∪ ((ps_acc ∪ ps_mem_in_trans) ∖ ps_acc)
                                  = {[p_rx]} ∪ transferred_memory_pages i trans).
    {
      assert ((ps_acc ∪ ps_mem_in_trans ) ∖ ps_acc = ps_mem_in_trans ∖ (ps_acc∖ {[p_tx]})) as ->.
      {
        assert ((ps_acc ∪ ps_mem_in_trans ) ∖ ps_acc = ps_mem_in_trans ∖ ps_acc) as ->.
        set_solver +.
        set_solver + Hnin_tx.
      }
      rewrite intersection_union_l_L.
      rewrite -union_assoc_L.
      rewrite intersection_comm_L.
      rewrite subseteq_intersection_1_L.
      2: { apply subseteq_difference_r. set_solver. set_solver + Hsubset_mb. }
      pose proof (union_split_difference_intersection_L ps_mem_in_trans (ps_acc∖ {[p_tx]})) as [Heq _].
      rewrite union_comm_L intersection_comm_L in Heq.
      f_equal.
      rewrite (accessible_retrieved_lending_memory_pages_difference i trans).
      rewrite union_intersection_r_L.
      rewrite union_comm_L difference_union_L.
      assert(ps_mem_in_trans ∖ retrieved_lending_memory_pages i trans ∪ ps_mem_in_trans ∖ (ps_acc ∖ {[p_tx]})=
               ps_mem_in_trans ∖ retrieved_lending_memory_pages i trans) as Hrewrite.
      rewrite union_comm_L.
      apply subseteq_union_1_L.
      pose proof (retrieved_lending_currently_accessible_memory_pages_subseteq i trans).
      set_solver + Hsubset_acc H1.
      rewrite Hrewrite.
      set_solver +.
      done.
    }

    iDestruct (get_valid_accessible_in_trans_memory_pages with "[$trans_hpool_global $pgt_owned]") as %Hvalid_acc_in_tran.
    set_solver + Hsubset_acc.

    iDestruct "mem_tx" as "[% mem_tx]".
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

      iAssert (memory_pages ((ps_acc ∖ {[p_tx]}) ∩ ({[p_rx]} ∪ transferred_memory_pages i trans)) mem_inters)%I  with "[mem_inters]" as "mem_inters".
      { rewrite /memory_pages. iSplitL "";first done. iFrame. }

      (* merge [mem_inters] and [mem_rest] into [mem_trans] (including [mem_rx]) *)
      iDestruct (memory_pages_split_union'
                   ((ps_acc∖ {[p_tx]}) ∩ ({[p_rx]} ∪ (transferred_memory_pages i trans))) with "[mem_inters mem_rest]") as "mem_tran".
      2:{ iSplitL "mem_inters". iExists mem_inters. iFrame "mem_inters". iExact "mem_rest". }
      { set_solver +. }
      rewrite Heq_inter_diff_union.

      iDestruct "rx_state_v" as "[rx_state_v [%p_rx_v [rx_v [%mem_rx_v mem_rx_v]]]]".

      iAssert (RX@i := p_rx)%I  with "[rx]" as "#rx'". iDestruct "rx" as "[$ ?]".
      (* getting instruction from [mem_oea] *)
      iDestruct (mem_big_sepM_split mem_oea Hlookup_mem_ai' with "mem_oea") as "[mem_instr Hacc_mem]".
      iApply (msg_send_secondary ai v (transaction_hpool_global_transferred trans ∗
                                                         transaction_pagetable_entries_transferred i trans ∗
                                                         retrievable_transaction_transferred i trans ∗
                                                         rx_states_global (delete v (delete i rxs)) )%I _
               with "[PC R0 R1 R2 R0z R1z R2z pgt_acc tx mem_tx mem_instr rx_v rx_state_v mem_rx_v other_rx prop0 propi
                    trans_hpool_global tran_pgt_transferred mem_tran retri rx_state]"); iFrameAutoSolve.
      { solve_finz + n0. }
      {
        iSplitL "prop0". iFrame.
        iSplitL "propi". iFrame.
        iSplitL "mem_tx". iFrame "mem_tx".
        iSplitL "mem_rx_v". iFrame "mem_rx_v".
        iSplitR "trans_hpool_global tran_pgt_transferred retri other_rx".
        2: { iFrame. }
        iNext. iIntros "((PC & mem_instr & pgt_acc & R0 & R1 & R2 & R0z & R1z & R2z & tx & #rx_v
                & rx_state_v & mem_tx & [% (_ & _ & mem_rx_v)])
                & (trans_hpool_global & trans_pgt_transferred & retri & other_rx) & propi)".
        iSplitL "trans_hpool_global trans_pgt_transferred retri R0z R1z R2z rx_state other_rx mem_tran mem_rx_v rx_v rx_state_v propi".
        pose proof (Htotal_rxs i) as [rs Hlookup_rs].
        iExists trans, rs.
        rewrite only_except_union.
        iFrame "trans_hpool_global trans_pgt_transferred retri".
        (* split [mem_tran] into [mem_rx] and [mem_trans] *)
        iDestruct (memory_pages_split_union' with "mem_tran") as "[mem_rx mem_trans]".
        { pose proof (transferred_accessible_memory_pages_subseteq i trans) as Hs.
          set_solver + Hs Hnin_rx.
        }
        rewrite memory_pages_singleton'. iFrame "mem_trans".
        iDestruct (rx_state_split with "rx_state_v") as "[rx_state_v rx_state_v']".
        iSplit. iPureIntro. apply only_except_disjoint.
        iSplitL "rx_state".
        iDestruct ("rx_state" $! rs with "[]") as "rx_state".
        done. iExact "rx_state".
        iSplitL "rx' mem_rx". iExists p_rx. iFrame "rx' mem_rx".
        iSplitR "propi".
        iRight. iFrame "R0z".
        iExists r2, v. iFrame "rx_state_v R2z".
        iSplitL "mem_rx_v". iExists p_rx_v. iFrame "rx_v". iExists (list_to_map (zip (finz.seq p_rx_v (length des)) des) ∪ mem_rx_v). iFrame.
        iSplitR "R1z".
        iApply (big_sepM_delete _ _ v with "[rx_v rx_state_v' other_rx]");auto.
        rewrite lookup_insert. reflexivity.
        rewrite delete_insert_delete.
        simpl. iFrame.
        iSplit. rewrite lookup_delete_ne in Hin_v. done. done.
        iExists r1. iFrame. done.
        iExact "propi".
        iCombine "PC mem_instr R0 R1 R2 pgt_acc tx mem_tx" as "R'". iExact "R'".
      }
      iNext. iIntros "[(PC & mem_instr & R0 & R1 & R2 & pgt_acc & tx & mem_tx) propi]".
      iIntros "Hholds". iSimpl in "Hholds".
      iDestruct (VMProp_holds_agree i with "[$Hholds $propi]") as "[Hres propi]".
      iEval (setoid_rewrite vmprop_unknown_eq) in "Hres".
      iEval (rewrite later_exist) in "Hres". iDestruct "Hres" as (trans') "Hres".
      iEval (rewrite later_exist) in "Hres". iDestruct "Hres" as (rx_state') "Hres".
      iEval (rewrite 11!later_sep) in "Hres".
      iDestruct "Hres" as "(>trans_hpool_global & >tran_pgt_transferred &
                         >retri & >mem_transferred & >R0z & >R1z & >R2z & (>rx_state & >[% [rx'' [% mem_rx]]]) & >other_rx & >%Htotal_rxs' & prop0)".
      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f r0 r1 r2 with "[PC R0 R1 R2]") as "[%regs' [%Htotal_regs' regs'']]"; iFrameAutoSolve.
      iDestruct (get_trans_rel_secondary with "[$trans_hpool_global $retri $tran_pgt_owned $retri_owned]") as "%trans_rel".
      erewrite (trans_rel_secondary_currently_accessible_memory_pages);eauto.
      erewrite (trans_rel_secondary_currently_accessible_memory_pages) in Hsubset_acc;eauto.
      iDestruct (trans_rel_secondary_transaction_pagetable_entries_owned with "tran_pgt_owned") as "tran_pgt_owned";eauto.
      iDestruct (trans_rel_secondary_retrieved_transaction_owned with "retri_owned") as "retri_owned";eauto.

      iDestruct (get_trans_ps_disj with "trans_hpool_global") as %Hdisj'.
      iAssert (⌜(ps_acc ∖ {[p_tx]} ∖ ({[p_rx]} ∪ transferred_memory_pages i trans)
                 = ps_acc ∖ {[p_rx; p_tx]} ∖ transferred_memory_pages i trans')⌝)%I as "%Hrewrite".
      {
        iDestruct (get_valid_accessible_in_trans_memory_pages with "[$trans_hpool_global $pgt_owned]") as %Hvalid_acc_in_tran'.
        set_solver + Hsubset_acc.
        iPureIntro.
        rewrite difference_difference_L.
        rewrite union_assoc_L (union_comm_L {[p_tx]}).
        rewrite -(difference_difference_L _ {[p_rx; p_tx]}).
        apply acc_transferred_memory_pages_difference;auto.
        erewrite <-(trans_rel_secondary_currently_accessible_memory_pages _ trans trans') in Hsubset_acc;eauto.
        rewrite union_comm_L.
        exact Hsubset_acc.
      }
      iDestruct ("Hacc_mem" with "mem_instr") as "mem_oea".
      iAssert (∃ mem_all : mem, memory_pages (ps_acc ∖ {[p_rx; p_tx]} ∪ accessible_in_trans_memory_pages i trans') mem_all)%I
        with "[mem_oea mem_transferred]" as (?) "mem".
      {
        iAssert(∃ m: mem, memory_pages (ps_acc ∖ {[p_tx]} ∖ ({[p_rx]} ∪ transferred_memory_pages i trans)) m)%I with "[mem_oea]" as "mem_oea".
        iExists _. iSplit; done.
        rewrite Hrewrite.
        iDestruct(memory_pages_union' with "[$mem_oea $mem_transferred]") as "mem". iFrame.
        rewrite acc_accessible_in_trans_memory_pages_union;auto.
        rewrite union_comm_L //.
      }

      iDestruct (mailbox.rx_agree with "rx'' rx'") as "%Heq". subst p_rx0.
      (* iDestruct "mem_tx" as "[%mem_tx mem_tx]". *)
      iDestruct (memory_pages_disj_singleton with "[$mem $mem_rx]") as %Hnin_rx'.
      iDestruct (memory_pages_disj_singleton with "[$mem $mem_tx]") as %Hnin_tx';auto.
      iAssert (∃ mem, memory_pages (ps_acc ∪ accessible_in_trans_memory_pages i trans') mem)%I
        with "[mem mem_rx mem_tx]" as "mem".
      {
        iExists (mem_all ∪ mem_rx ∪ mem2).
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
        iExists mem_all, (mem_rx ∪ mem2). iFrame "mem".
        rewrite memory_pages_split_union.
        iSplit.
        iExists mem_rx, mem2. rewrite 2!memory_pages_singleton. iFrame "mem_rx mem_tx". done.
        iPureIntro. rewrite map_union_assoc //. set_solver + Hneq_tx_rx.
      }
      iApply ("IH" $! _ ps_acc trans' _ Htotal_rxs' Htotal_regs' Hsubset_mb Hsubset_acc Hnin_rx' Hnin_tx' with "regs'' tx pgt_tx rx pgt_acc pgt_owned
                        trans_hpool_global tran_pgt_transferred retri rx_state other_rx
                           tran_pgt_owned retri_owned mem [$R0z $R1z $R2z $prop0 $propi]").
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

      iDestruct "rx_state_v" as "[rx_state_v [%p_rx_v [rx_v [%mem_rx_v mem_rx_v]]]]".
      iAssert (RX@i := p_rx)%I  with "[rx]" as "#rx'". iDestruct "rx" as "[$ ?]".
      iApply (msg_send_secondary ai v (transaction_hpool_global_transferred trans ∗ transaction_pagetable_entries_transferred i trans
                                       ∗ retrievable_transaction_transferred i trans ∗ rx_states_global (delete v (delete i rxs))) _
               with "[PC R0 R1 R2 R0z R1z R2z pgt_acc tx mem_tx mem_instr rx_v rx_state_v mem_rx_v other_rx prop0 propi
                    trans_hpool_global tran_pgt_transferred Hacc_mem_inters mem_rest retri rx_state]"); iFrameAutoSolve.
      { solve_finz + n0. }
      {
        iSplitL "prop0". iFrame.
        iSplitL "propi". iFrame.
        iSplitL "mem_tx". iFrame "mem_tx".
        iSplitL "mem_rx_v". iFrame "mem_rx_v".
        iSplitR "trans_hpool_global tran_pgt_transferred retri other_rx".
        2: { iFrame. }
        iNext. iIntros "((PC & mem_instr & pgt_acc & R0 & R1 & R2 & R0z & R1z & R2z & tx & #rx_v
                & rx_state_v & mem_tx & [% (_ & _ & mem_rx_v)]) & (trans_hpool_global & trans_pgt_transferred & retri& other_rx) & propi)".
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
        iSplitL "trans_hpool_global trans_pgt_transferred retri R0z R1z R2z rx_state other_rx mem_tran rx_v rx_state_v mem_rx_v propi".
        pose proof (Htotal_rxs i) as [rs Hlookup_rs].
        iExists trans,rs.
        rewrite only_except_union.
        iFrame "trans_hpool_global trans_pgt_transferred retri".
        iDestruct (memory_pages_split_union' with "mem_tran") as "[mem1 mem2]".
        { pose proof (transferred_accessible_memory_pages_subseteq i trans) as Hs.
          set_solver + Hs Hnin_rx.
        }
        iFrame "mem2".
        iSplit. iPureIntro. apply only_except_disjoint.
        rewrite memory_pages_singleton'.
        iDestruct (rx_state_split with "rx_state_v") as "[rx_state_v rx_state_v']".
        iSplitL "rx_state".
        iDestruct ("rx_state" $! rs with "[]") as "rx_state".
        done. iFrame.
        iSplitL "mem1".
        iExists _. iFrame " rx' mem1".
        iSplitR "propi".
        iRight. iFrame "R0z".
        iExists r2, v.
        iFrame "rx_state_v R2z".
        iSplitL "mem_rx_v".
        iExists p_rx_v. iFrame "rx_v". iExists (list_to_map (zip (finz.seq p_rx_v (length des)) des) ∪ mem_rx_v). iFrame "mem_rx_v".
        iSplitR "R1z".
        iApply (big_sepM_delete _ _ v with "[rx_v rx_state_v' other_rx]");auto.
        rewrite lookup_insert. reflexivity.
        rewrite delete_insert_delete.
        simpl. iFrame.
        iSplit. rewrite lookup_delete_ne in Hin_v. done. done.
        iExists r1. iFrame. done.
        iExact "propi".
        iCombine "PC R0 R1 R2 pgt_acc tx mem_tx" as "R'". iExact "R'".
      }
      iNext. iIntros "[(PC & R0 & R1 & R2 &  pgt_acc & tx & mem_tx) propi]".
      iSimpl. iIntros "Hholds".
      iDestruct (VMProp_holds_agree i with "[$Hholds $propi]") as "[Hres propi]".
      iEval (setoid_rewrite vmprop_unknown_eq) in "Hres".
      iEval (rewrite later_exist) in "Hres". iDestruct "Hres" as (trans') "Hres".
      iEval (rewrite later_exist) in "Hres". iDestruct "Hres" as (rx_state') "Hres".
      iEval (rewrite 11!later_sep) in "Hres".
      iDestruct "Hres" as "(>trans_hpool_global & >tran_pgt_transferred &
                         >retri & >mem_transferred & >R0z & >R1z & >R2z & (>rx_state & >[% [rx'' [% mem_rx]]]) & >other_rx & >%Htotal_rxs' & prop0)".
      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f r0 r1 r2 with "[PC R0 R1 R2]") as "[%regs' [%Htotal_regs' regs'']]"; iFrameAutoSolve.
      iDestruct (get_trans_rel_secondary with "[$trans_hpool_global $retri $tran_pgt_owned $retri_owned]") as "%trans_rel".
      erewrite (trans_rel_secondary_currently_accessible_memory_pages);eauto.
      erewrite (trans_rel_secondary_currently_accessible_memory_pages) in Hsubset_acc;eauto.
      iDestruct (trans_rel_secondary_transaction_pagetable_entries_owned with "tran_pgt_owned") as "tran_pgt_owned";eauto.
      iDestruct (trans_rel_secondary_retrieved_transaction_owned with "retri_owned") as "retri_owned";eauto.

      iDestruct (get_trans_ps_disj with "trans_hpool_global") as %Hdisj'.
      iAssert (⌜(ps_acc ∖ {[p_tx]} ∖ ({[p_rx]} ∪ transferred_memory_pages i trans)
                 = ps_acc ∖ {[p_rx; p_tx]} ∖ transferred_memory_pages i trans')⌝)%I as "%Hrewrite".
      {
        iDestruct (get_valid_accessible_in_trans_memory_pages with "[$trans_hpool_global $pgt_owned]") as %Hvalid_acc_in_tran'.
        set_solver + Hsubset_acc.
        iPureIntro.
        rewrite difference_difference_L.
        rewrite union_assoc_L (union_comm_L {[p_tx]}).
        rewrite -(difference_difference_L _ {[p_rx; p_tx]}).
        apply acc_transferred_memory_pages_difference;auto.
        erewrite <-(trans_rel_secondary_currently_accessible_memory_pages _ trans trans') in Hsubset_acc;eauto.
        rewrite union_comm_L.
        exact Hsubset_acc.
      }
      iAssert (∃ mem_all : mem, memory_pages (ps_acc ∖ {[p_rx; p_tx]} ∪ accessible_in_trans_memory_pages i trans') mem_all)%I
        with "[mem_oea mem_transferred]" as (?) "mem".
      {
        iAssert(∃ m: mem, memory_pages (ps_acc ∖ {[p_tx]} ∖ ({[p_rx]} ∪ transferred_memory_pages i trans)) m)%I with "[mem_oea]" as "mem_oea".
        iExists _. iSplit; done.
        rewrite Hrewrite.
        iDestruct(memory_pages_union' with "[$mem_oea $mem_transferred]") as "mem". iFrame.
        rewrite acc_accessible_in_trans_memory_pages_union;auto.
        rewrite union_comm_L //.
      }

      iDestruct (mailbox.rx_agree with "rx'' rx'") as "%Heq". subst p_rx0.
      iDestruct (memory_pages_disj_singleton with "[$mem $mem_rx]") as %Hnin_rx'.
      iDestruct (memory_pages_disj_singleton with "[$mem $mem_tx]") as %Hnin_tx'.
      iAssert (∃ mem, memory_pages (ps_acc ∪ accessible_in_trans_memory_pages i trans') mem)%I
        with "[mem mem_rx mem_tx]" as "mem".
      {
        iExists (mem_all ∪ mem_rx ∪ mem2).
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
        iExists mem_all, (mem_rx ∪ mem2). iFrame "mem".
        rewrite memory_pages_split_union.
        iSplit.
        iExists mem_rx, mem2. rewrite 2!memory_pages_singleton. iFrame "mem_rx mem_tx".
        done.
        iPureIntro. rewrite map_union_assoc //. set_solver + Hneq_tx_rx.
      }
      iApply ("IH" $! _ ps_acc trans' _ Htotal_rxs' Htotal_regs' Hsubset_mb Hsubset_acc Hnin_rx' Hnin_tx' with "regs'' tx pgt_tx rx pgt_acc pgt_owned
                        trans_hpool_global tran_pgt_transferred retri rx_state other_rx
                           tran_pgt_owned retri_owned mem [$R0z $R1z $R2z $prop0 $propi]").

    }
  Qed.

End ftlr_msg_send.
