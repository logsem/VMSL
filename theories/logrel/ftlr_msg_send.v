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

  Lemma ftlr_msg_send {i trans' mem_acc_tx ai regs ps_acc p_tx p_rx ps_na instr trans rx_state r0}:
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
    decode_hvc_func r0 = Some Send ->
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
   pagetable_entries_excl_owned i (ps_acc ∖ {[p_rx; p_tx]} ∖ (pages_in_trans (trans_memory_in_trans i trans))) -∗
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

    iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "mem_acc_tx") as "[mem_instr Hacc_mem_acc_tx]".
    destruct (decode_vmid r1) eqn:Heq_decode.
    2:{ (* apply [msg_send_invalid_receiver] *)
      iApply (msg_send_invalid_receiver ai with "[PC mem_instr pgt_acc' R0 R1 R2 tx]");iFrameAutoSolve.
      iNext.
      iIntros "(PC & mem_instr & pgt_acc'  & tx & R0 & R1 & R2) _".
      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".

      iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
      iApply ("IH" $! _ _ ps_acc _ trans _ Htotal_regs' Hsubset_mb Hdisj_na Hnin_rx Hnin_tx with "regs tx pgt_tx pgt_acc pgt_acc' LB trans_hpool_global
                            tran_pgt_transferred retri R0z R1z R2z rx_state rx other_rx prop0 propi tran_pgt_owned pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx]
                            ").
      {
        iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx $mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
        iExists mem_acc_tx;by iFrame "mem_acc_tx".
        iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
        set_solver +.
      }
    }

    destruct (decide (v = i)).
    { (* apply [msg_send_to_self] *)
      iApply (msg_send_to_self ai with "[PC mem_instr pgt_acc' R0 R1 R2 tx]");iFrameAutoSolve.
      exact Heq_decode.
      done.
      iNext.
      iIntros "(PC & mem_instr & pgt_acc'  & tx & R0 & R1 & R2) _".
      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".

      iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
      iApply ("IH" $! _ _ ps_acc _ trans _ Htotal_regs' Hsubset_mb Hdisj_na Hnin_rx Hnin_tx with "regs tx pgt_tx pgt_acc pgt_acc' LB trans_hpool_global
                            tran_pgt_transferred retri R0z R1z R2z rx_state rx other_rx prop0 propi tran_pgt_owned pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx]
                            ").
      {
        iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx $mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
        iExists mem_acc_tx;by iFrame "mem_acc_tx".
        iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
        set_solver +.
      }
    }

    destruct (decide (page_size < r2)%Z).
    { (*apply [msg_send_invalid_length]*)
      iApply (msg_send_invalid_length ai with "[PC mem_instr pgt_acc' R0 R1 R2 tx]");iFrameAutoSolve.
      exact Heq_decode.
      done.
      lia.
      iNext.
      iIntros "(PC & mem_instr & pgt_acc'  & tx & R0 & R1 & R2) _".
      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".

      iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
      iApply ("IH" $! _ _ ps_acc _ trans _ Htotal_regs' Hsubset_mb Hdisj_na Hnin_rx Hnin_tx with "regs tx pgt_tx pgt_acc pgt_acc' LB trans_hpool_global
                            tran_pgt_transferred retri R0z R1z R2z rx_state rx other_rx prop0 propi tran_pgt_owned pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx]
                            ").
      {
        iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx $mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
        iExists mem_acc_tx;by iFrame "mem_acc_tx".
        iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
        set_solver +.
      }
    }

    set all_vmids := (list_to_set (list_of_vmids)).
    assert (v ∈ (all_vmids ∖ {[i]})) as Hin_v.
    {
      pose proof (in_list_of_vmids v) as Hin_v.
      rewrite -elem_of_list_In in Hin_v.
      rewrite -(elem_of_list_to_set (C:= gset _)) in Hin_v.
      set_solver + Hin_v n.
    }

    iDestruct (big_sepS_delete with "other_rx") as "[(%p_rx_v & [rx_v [%rx_state_v [rx_state_v rx_state_v']]]) other_rx]".
    exact Hin_v.

    destruct (rx_state_v).
    { (* apply [msg_send_full_rx] *)
      iApply (msg_send_full_rx ai with "[PC mem_instr pgt_acc' R0 R1 R2 tx rx_state_v]");iFrameAutoSolve.
      exact Heq_decode.
      done.
      lia.
      2: { iFrame "rx_state_v". }
      done.
      iNext.
      iIntros "(PC & mem_instr & pgt_acc'  & tx & R0 & R1 & R2 & rx_state_v ) _".
      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".

      iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
      iApply ("IH" $! _ _ ps_acc _ trans _ Htotal_regs' Hsubset_mb Hdisj_na Hnin_rx Hnin_tx with "regs tx pgt_tx pgt_acc pgt_acc' LB trans_hpool_global
                            tran_pgt_transferred retri R0z R1z R2z rx_state rx [other_rx rx_v rx_state_v rx_state_v'] prop0 propi tran_pgt_owned pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx]
                            ").
      {
        iApply (big_sepS_delete with "[other_rx rx_v rx_state_v rx_state_v']").
        exact Hin_v.
        simpl.
        iFrame "other_rx".
        iExists p_rx_v.
        iFrame.
        iExists (Some p).
        iFrame.
      }
      {
        iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx $mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
        iExists mem_acc_tx;by iFrame "mem_acc_tx".
        iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
        set_solver +.
      }
    }
    iDestruct ("rx_state_v'" with "[]") as "[rx_state_v' [%mem_rx_v mem_rx_v]]";auto.
    iDestruct (rx_state_split with "[$rx_state_v $rx_state_v']") as "rx_state_v".

    iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
    pose proof (union_split_difference_intersection_L (ps_acc∖ {[p_tx]}) ({[p_rx]} ∪ ps_mem_in_trans)) as [Heq_ps_acc_tx Hdisj_ps_acc_tx].
    rewrite Heq_ps_acc_tx in Hdom_mem_acc_tx.
    rewrite set_of_addr_union in Hdom_mem_acc_tx;last auto.
    apply dom_union_inv_L in Hdom_mem_acc_tx;last apply set_of_addr_disj;auto.
    destruct Hdom_mem_acc_tx as (mem_oea & mem_inters & Heq_mem_acc_tx' & Hdisj_mem_oea_inters & Hdom_mem_oea & Hdom_mem_inters).
    rewrite Heq_mem_acc_tx'.
    iDestruct (big_sepM_union with "mem_acc_tx") as "[mem_oea mem_inters]";auto.

    (* for simplication *)
    assert (Heq_inter_diff_union: (ps_acc ∖ {[p_tx]}) ∩ ({[p_rx]} ∪ ps_mem_in_trans) ∪ ((ps_acc ∪ ps_mem_in_trans ) ∖ ps_acc)
                                  = {[p_rx]} ∪ ps_mem_in_trans).
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
      rewrite  -Heq //.
    }

    iDestruct "mem_tx" as "[% mem_tx]".
    iDestruct ("R2z") as "[% R2z]".
    (* we have this annoying case anlaysis because we need to know if the instruction is in the memory pages required by VMProp 0 *)
    destruct (decide ((tpa ai) ∈ ((ps_acc∖ {[p_tx]}) ∖ ({[p_rx]} ∪ ps_mem_in_trans)))) as [Hin_ps_oea | Hnin_ps_oea].
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

      iAssert (memory_pages ((ps_acc ∖ {[p_tx]}) ∩ ({[p_rx]} ∪ ps_mem_in_trans)) mem_inters)%I  with "[mem_inters]" as "mem_inters".
      { rewrite /memory_pages. iSplitL "";first done. iFrame. }

      (* merge [mem_inters] and [mem_rest] into [mem_trans] (including [mem_rx]) *)
      iDestruct (memory_pages_split_union'
                   ((ps_acc∖ {[p_tx]}) ∩ ({[p_rx]} ∪ ps_mem_in_trans)) with "[mem_inters mem_rest]") as "mem_tran".
      2:{ iSplitL "mem_inters". iExists mem_inters. iFrame "mem_inters". iExact "mem_rest". }
      { set_solver +. }
      rewrite Heq_inter_diff_union.

      (* getting instruction from [mem_oea] *)
      iDestruct (mem_big_sepM_split mem_oea Hlookup_mem_ai' with "mem_oea") as "[mem_instr Hacc_mem]".
      iApply (msg_send_secondary ai v (LB@ i := [ps_na] ∗ i -@{1/2}A> ps_acc ∗
                                                         transaction_hpool_global_transferred trans ∗
                                                         transaction_pagetable_entries_transferred i trans ∗
                                                         retrieval_entries_transferred i trans ∗
                                                         rx_pages (all_vmids ∖ {[i;v]}))%I _
               with "[PC R0 R1 R2 R0z R1z R2z pgt_acc tx mem_tx mem_instr rx_v rx_state_v mem_rx_v other_rx prop0 propi LB pgt_acc' trans_hpool_global tran_pgt_transferred mem_tran
                            retri rx_state rx]"); iFrameAutoSolve.
      { solve_finz + n0. }
      {
        iSplitL "prop0". iFrame.
        iSplitL "propi". iFrame.
        iSplitL "mem_tx". iFrame "mem_tx".
        iSplitL "mem_rx_v". iFrame "mem_rx_v".
        iSplitR "LB trans_hpool_global tran_pgt_transferred retri other_rx".
        2: {
          iFrame.
          rewrite /rx_pages.
          rewrite difference_difference_L.
          iFrame.
        }
        iNext.
        iIntros "((PC & mem_instr & pgt_acc & R0 & R1 & R2 & R0z & R1z & R2z & tx & #rx_v
                & rx_state_v & mem_tx & [% (_ & _ & mem_rx_v)])
                & (LB & pgt_acc' & trans_hpool_global & trans_pgt_transferred & retri & other_rx) & propi)".
        iSplitL "pgt_acc LB trans_hpool_global trans_pgt_transferred retri R0z R1z R2z rx_state rx other_rx mem_tran mem_rx_v rx_v rx_state_v propi".
        iExists ps_na, ps_acc, trans.
        iFrame "pgt_acc LB trans_hpool_global trans_pgt_transferred retri rx".
        iSplitL ""; first done.
        (* split [mem_tran] into [mem_rx] and [mem_trans] *)
        iDestruct (memory_pages_split_union' with "mem_tran") as "[mem_rx mem_trans]".
        set_solver + Hnin_rx.
        rewrite memory_pages_singleton'.
        iFrame "mem_rx mem_trans".
        iDestruct (rx_state_split with "rx_state_v") as "[rx_state_v rx_state_v']".
        iSplitL "other_rx rx_state_v".
        iApply (big_sepS_delete _ _ v with "[rx_v rx_state_v other_rx]");auto.
        simpl.
        rewrite difference_difference_L.
        iFrame "other_rx".
        iExists p_rx_v. iFrame "rx_v".
        iExists (Some (r2, i)). iFrame.
        iIntros "%". done.
        iSplitR "propi".
        iRight. iFrame "R0z".
        iSplitL "rx_state". iExists rx_state. iFrame.
        iExists v, p_rx_v, r2. iFrame.
        iSplitL "";auto. iFrame "rx_v".
        iSplitL "R1z". iExists r1. iFrame. done.
        iExists (list_to_map (zip (finz.seq p_rx_v (length des)) des) ∪ mem_rx_v).
        iFrame.
        iExact "propi".
        iCombine "PC mem_instr R0 R1 R2 pgt_acc' tx mem_tx" as "R'". iExact "R'".
      }
      iNext.
      iIntros "[(PC & mem_instr & R0 & R1 & R2 & pgt_acc' & tx & mem_tx) propi]".
      iIntros "Hholds". iSimpl in "Hholds".
      iDestruct (VMProp_holds_agree i with "[$Hholds $propi]") as "[Hres propi]".
      iEval (setoid_rewrite vmprop_unknown_eq) in "Hres".
      iEval (rewrite later_exist) in "Hres". iDestruct "Hres" as (ps_na') "Hres".
      iEval (rewrite later_exist) in "Hres". iDestruct "Hres" as (ps_acc') "Hres".
      iEval (rewrite later_exist) in "Hres". iDestruct "Hres" as (trans'') "Hres".
      iEval (rewrite later_exist) in "Hres". iDestruct "Hres" as (rx_state') "Hres".
      iEval (rewrite 15!later_sep) in "Hres".
      iDestruct "Hres" as  "( >pgt_acc & >LB & >%Hdisj_na' & >trans_hpool_global & >tran_pgt_transferred &
                         >retri & >mem_transferred & >R0z & >R1z & >R2z & >rx_state & >rx & >[% mem_rx] & >other_rx &
                          Himp_tran_pgt & Himp_pgt & Himp_retri & Himp_mem & prop0)".
      iDestruct (access_agree_eq with "[$pgt_acc $pgt_acc']") as %->.
      iDestruct (later_wand with "Himp_tran_pgt") as "Himp_tran_pgt".
      iDestruct ("Himp_tran_pgt" with "tran_pgt_owned") as ">tran_pgt_owned".
      iDestruct (later_wand with "Himp_pgt") as "Himp_pgt".
      iDestruct ("Himp_pgt" with "pgt_owned") as ">pgt_owned".
      iDestruct (later_wand with "Himp_retri") as "Himp_retri".
      iDestruct ("Himp_retri" with "retri_owned") as ">retri_owned".
      iDestruct (later_wand with "Himp_mem") as "Himp_mem".
      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f r0 r1 r2 with "[PC R0 R1 R2]") as "[%regs' [%Htotal_regs' regs'']]"; iFrameAutoSolve.
      iDestruct ("Hacc_mem" with "[$mem_instr]") as "mem_owned".
      iDestruct ("Himp_mem" with "[mem_owned $mem_transferred]") as  (?) ">mem".
      {
        iNext. iExists mem_oea. iFrame. iPureIntro.
        rewrite Hdom_mem_oea.
        f_equal. set_solver +.
      }

      iDestruct (memory_pages_disj_singleton with "[$mem $mem_rx]") as %Hnin_rx'.
      iDestruct (memory_pages_disj_singleton with "[$mem $mem_tx]") as %Hnin_tx'.
      iAssert (∃ mem, memory_pages (ps_acc ∪ pages_in_trans (trans_memory_in_trans i trans'')) mem)%I
        with "[mem mem_rx mem_tx]" as "mem".
      {
        iExists (mem_all ∪ mem_rx ∪ mem2).
        assert (pages_in_trans (trans_memory_in_trans i trans'') ## {[p_tx]}) as Hdisj_ps_tx'.
        set_solver + Hnin_tx'.
        assert (pages_in_trans (trans_memory_in_trans i trans'') ## {[p_rx]}) as Hdisj_ps_rx'.
        set_solver + Hnin_rx'.
        assert (ps_acc ∖ {[p_rx; p_tx]} ∪ pages_in_trans (trans_memory_in_trans i trans'') ∪ {[p_rx; p_tx]} =
                  (ps_acc ∪ pages_in_trans (trans_memory_in_trans i trans''))) as <-.
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
        iExists mem_all, (mem_rx ∪ mem2).
        iFrame "mem".
        rewrite memory_pages_split_union.
        iSplit.
        iExists mem_rx, mem2.
        rewrite 2!memory_pages_singleton.
        iFrame "mem_rx mem_tx".
        done.
        iPureIntro.
        rewrite map_union_assoc //.
        set_solver + Hneq_tx_rx.
      }
      iApply ("IH" $! _ _ ps_acc trans _ _ Htotal_regs' Hsubset_mb Hdisj_na' Hnin_rx' Hnin_tx' with "regs'' tx pgt_tx pgt_acc pgt_acc'
                       LB trans_hpool_global tran_pgt_transferred retri R0z R1z R2z rx_state rx other_rx prop0 propi
                           tran_pgt_owned pgt_owned retri_owned mem").
    }
    { (* tpa ai ∉ ps_acc ∖ ({[p_rx]} ∪ ps_mem_in_trans) *)
      (* we don't need to touch [mem_oea]*)
      (* first show instr is in [mem_inters] *)
      assert (tpa ai ∈ (ps_acc∖ {[p_tx]}) ∩ ({[p_rx]} ∪ ps_mem_in_trans )) as Hin_ps_inters.
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
      iApply (msg_send_secondary ai v (LB@ i := [ps_na] ∗ i -@{1/2}A> ps_acc ∗
                                                         transaction_hpool_global_transferred trans ∗
                                                         transaction_pagetable_entries_transferred i trans ∗ retrieval_entries_transferred i trans ∗ rx_pages (all_vmids ∖ {[i;v]})) _
               with "[PC R0 R1 R2 R0z R1z R2z pgt_acc tx mem_tx mem_instr rx_v rx_state_v mem_rx_v other_rx prop0 propi LB pgt_acc' trans_hpool_global tran_pgt_transferred Hacc_mem_inters mem_rest
                            retri rx_state rx]"); iFrameAutoSolve.
      { solve_finz + n0. }
      {
        iSplitL "prop0".
        iFrame.
        iSplitL "propi".
        iFrame.
        iSplitL "mem_tx".
        iFrame "mem_tx".
        iSplitL "mem_rx_v".
        iFrame "mem_rx_v".
        iSplitR "LB trans_hpool_global tran_pgt_transferred retri other_rx".
        2: {
          iFrame.
          rewrite /rx_pages.
          rewrite difference_difference_L.
          iFrame.
        }
        iNext.
        iIntros "((PC & mem_instr & pgt_acc & R0 & R1 & R2 & R0z & R1z & R2z & tx & #rx_v
                & rx_state_v & mem_tx & [% (_ & _ & mem_rx_v)]) & (LB & pgt_acc' & trans_hpool_global & trans_pgt_transferred & retri& other_rx) & propi)".
        iDestruct ("Hacc_mem_inters" with "mem_instr") as "mem_inters".
        (* FIXME: copied proofs  *)
        iAssert (memory_pages ((ps_acc∖ {[p_tx]}) ∩ ({[p_rx]} ∪ ps_mem_in_trans)) mem_inters)%I  with "[mem_inters]" as "mem_inters".
        { rewrite /memory_pages. iSplitL "";first done. iFrame. }
        (* [mem_inters] + [mem_rest] = [mem_tran] *)
        iDestruct (memory_pages_split_union'
                     ((ps_acc∖ {[p_tx]}) ∩ ({[p_rx]} ∪ ps_mem_in_trans)) with "[mem_inters mem_rest]") as "mem_tran".
        2:{ iSplitL "mem_inters". iExists mem_inters. iFrame "mem_inters". iExact "mem_rest". }
        { set_solver +. }
        rewrite Heq_inter_diff_union.
        iSplitL "pgt_acc LB trans_hpool_global trans_pgt_transferred retri R0z R1z R2z rx_state rx other_rx mem_tran rx_v rx_state_v mem_rx_v propi".
        iExists ps_na, ps_acc, trans.
        iFrame "pgt_acc LB trans_hpool_global trans_pgt_transferred retri rx".
        iSplitL ""; first done.
        iDestruct (memory_pages_split_union' with "mem_tran") as "[mem1 mem2]".
        set_solver + Hnin_rx.
        iFrame "mem2".
        rewrite memory_pages_singleton'. iFrame "mem1".
        iDestruct (rx_state_split with "rx_state_v") as "[rx_state_v rx_state_v']".
        iSplitL "other_rx rx_v rx_state_v".
        iApply (big_sepS_delete _ _ v with "[rx_v rx_state_v other_rx]");auto.
        simpl.
        rewrite difference_difference_L.
        iFrame "other_rx".
        iExists p_rx_v. iFrame "rx_v".
        iExists (Some (r2, i)). iFrame.
        iIntros "%". done.
        iSplitR "propi".
        iRight. iFrame.
        iSplitL "rx_state". iExists rx_state. iFrame.
        iExists v, p_rx_v, r2.
        iFrame.
        iSplitL "";auto.
        iFrame "rx_v".
        iSplitL "R1z". iExists r1. iFrame. done.
        iExists (list_to_map (zip (finz.seq p_rx_v (length des)) des) ∪ mem_rx_v).
        iFrame.
        iExact "propi".
        iCombine "PC R0 R1 R2 pgt_acc' tx mem_tx" as "R'". iExact "R'".
      }
      (*TODO *)
      iNext.
      iIntros "[(PC & R0 & R1 & R2 &  pgt_acc' & tx & mem_tx) propi]".
      iSimpl.
      iIntros "Hholds".
      iDestruct (VMProp_holds_agree i with "[$Hholds $propi]") as "[Hres propi]".
      iEval (setoid_rewrite vmprop_unknown_eq) in "Hres".
      iEval (rewrite later_exist) in "Hres". iDestruct "Hres" as (ps_na') "Hres".
      iEval (rewrite later_exist) in "Hres". iDestruct "Hres" as (ps_acc') "Hres".
      iEval (rewrite later_exist) in "Hres". iDestruct "Hres" as (trans'') "Hres".
      iEval (rewrite later_exist) in "Hres". iDestruct "Hres" as (rx_state') "Hres".
      iEval (rewrite 15!later_sep) in "Hres".
      iDestruct "Hres" as  "( >pgt_acc & >LB & >%Hdisj_na' & >trans_hpool_global & >tran_pgt_transferred &
                         >retri & >mem_transferred & >R0z & >R1z & >R2z & >rx_state & >rx & >[% mem_rx] & >other_rx &
                          Himp_tran_pgt & Himp_pgt & Himp_retri & Himp_mem & prop0)".
      iDestruct (access_agree_eq with "[$pgt_acc $pgt_acc']") as %->.
      iDestruct (later_wand with "Himp_tran_pgt") as "Himp_tran_pgt".
      iDestruct ("Himp_tran_pgt" with "tran_pgt_owned") as ">tran_pgt_owned".
      iDestruct (later_wand with "Himp_pgt") as "Himp_pgt".
      iDestruct ("Himp_pgt" with "pgt_owned") as ">pgt_owned".
      iDestruct (later_wand with "Himp_retri") as "Himp_retri".
      iDestruct ("Himp_retri" with "retri_owned") as ">retri_owned".
      iDestruct (later_wand with "Himp_mem") as "Himp_mem".
      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f r0 r1 r2 with "[PC R0 R1 R2]") as "[%regs' [%Htotal_regs' regs'']]"; iFrameAutoSolve.
      iDestruct ("Himp_mem" with "[mem_oea $mem_transferred]") as  (?) ">mem".
      {
        iNext. iExists mem_oea. iFrame. iPureIntro.
        rewrite Hdom_mem_oea.
        f_equal. set_solver +.
      }

      iDestruct (memory_pages_disj_singleton with "[$mem $mem_rx]") as %Hnin_rx'.
      iDestruct (memory_pages_disj_singleton with "[$mem $mem_tx]") as %Hnin_tx'.
      iAssert (∃ mem, memory_pages (ps_acc ∪ pages_in_trans (trans_memory_in_trans i trans'')) mem)%I
        with "[mem mem_rx mem_tx]" as "mem".
      {
        iExists (mem_all ∪ mem_rx ∪ mem2).
        assert (pages_in_trans (trans_memory_in_trans i trans'') ## {[p_tx]}) as Hdisj_ps_tx'.
        set_solver + Hnin_tx'.
        assert (pages_in_trans (trans_memory_in_trans i trans'') ## {[p_rx]}) as Hdisj_ps_rx'.
        set_solver + Hnin_rx'.
        assert (ps_acc ∖ {[p_rx; p_tx]} ∪ pages_in_trans (trans_memory_in_trans i trans'') ∪ {[p_rx; p_tx]} =
                  (ps_acc ∪ pages_in_trans (trans_memory_in_trans i trans''))) as <-.
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
        iExists mem_all, (mem_rx ∪ mem2).
        iFrame "mem".
        rewrite memory_pages_split_union.
        iSplit.
        iExists mem_rx, mem2.
        rewrite 2!memory_pages_singleton.
        iFrame "mem_rx mem_tx".
        done.
        iPureIntro.
        rewrite map_union_assoc //.
        set_solver + Hneq_tx_rx.
      }
      iApply ("IH" $! _ _ ps_acc trans _ _ Htotal_regs' Hsubset_mb Hdisj_na' Hnin_rx' Hnin_tx' with "regs'' tx pgt_tx pgt_acc pgt_acc'
                       LB trans_hpool_global tran_pgt_transferred retri R0z R1z R2z rx_state rx other_rx prop0 propi
                           tran_pgt_owned pgt_owned retri_owned mem").
    }
  Qed.

End ftlr_msg_send.
