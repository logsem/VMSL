From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang trans_extra.
From HypVeri.algebra Require Import base pagetable mem trans.
From HypVeri.rules Require Import mem_send.
From HypVeri.logrel Require Import logrel logrel_extra.
From HypVeri Require Import proofmode.
Import uPred.

Section ftlr_donate.
  Context `{hypconst:HypervisorConstants}.
  Context `{hypparams:!HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.

Lemma ftlr_donate {i mem_acc_tx ai regs ps_acc p_tx p_rx instr trans rxs r0} P:
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
  decode_hvc_func r0 = Some Donate ->
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
    set ps_mem_in_trans := (accessible_in_trans_memory_pages i trans).
    pose proof (Htotal_regs R1) as[r1 Hlookup_reg_R1].
    pose proof (Htotal_regs R2) as[r2 Hlookup_reg_R2].
    iDestruct (reg_big_sepM_split_upd4 i Hlookup_PC Hlookup_reg_R0 Hlookup_reg_R1 Hlookup_reg_R2 with "[$regs]")
      as "(PC & R0 & R1 & R2 & Hacc_regs)";eauto.
    iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "mem_acc_tx") as "[mem_instr Hacc_mem_acc_tx]".

    destruct (decide (page_size < r1)%Z).
    { (* the length of msg exceeds [page_size] *)
      iApply (mem_send_invalid_len ai with "[PC mem_instr pgt_acc R0 R1 R2 tx]");iFrameAutoSolve.
      exact Hdecode_hvc. simpl; reflexivity.
      iNext. iIntros "(PC & mem_instr & pgt_acc & R0 & R1 & R2 & tx) _".
      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".

      iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
      iApply ("IH" $! _ ps_acc trans _ Htotal_rxs Htotal_regs' Hsubset_mb Hsubset_acc Hnin_rx Hnin_tx with "regs tx pgt_tx rx pgt_acc pgt_owned trans_hpool_global
                            tran_pgt_transferred retri rx_state other_rx tran_pgt_owned  retri_owned [mem_rest mem_acc_tx mem_tx] P ").
      {
        iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx $mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
        iExists mem_acc_tx;by iFrame "mem_acc_tx".
        iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
        set_solver +.
      }
    }

    iDestruct "mem_tx" as (mem_tx) "mem_tx".
    destruct (parse_transaction_descriptor mem_tx p_tx (Z.to_nat r1))  as [tran_des|] eqn:Heq_parse_tran.
    2:{ (* cannot parse the msg as a descriptor *)
      iApply (mem_send_invalid_msg ai with "[PC mem_instr pgt_acc R0 R1 R2 tx mem_tx]");iFrameAutoSolve.
      exact Hdecode_hvc. simpl; reflexivity. lia. exact Heq_parse_tran. iFrame.
      iNext. iIntros "(PC & mem_instr & pgt_acc & R0 & R1 & R2 & tx & mem_tx) _".
      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".

      iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
      iApply ("IH" $! _ ps_acc trans _ Htotal_rxs Htotal_regs' Hsubset_mb Hsubset_acc Hnin_rx Hnin_tx with "regs tx pgt_tx rx pgt_acc pgt_owned trans_hpool_global
                            tran_pgt_transferred retri rx_state other_rx tran_pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx] P").
      {
        iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
        iSplitL "mem_acc_tx".
        iExists mem_acc_tx;by iFrame "mem_acc_tx".
        iExists mem_tx;by iFrame "mem_tx".
        iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
        set_solver +.
      }
    }

    destruct (validate_transaction_descriptor i tran_des) eqn:Hvalid_tran_des.
    2:{ (* validation of descriptor fails, apply [mem_send_invalid_des] *)
      iApply (mem_send_invalid_des ai with "[PC mem_instr pgt_acc R0 R1 R2 tx mem_tx]");iFrameAutoSolve.
      exact Hdecode_hvc. simpl; reflexivity. lia. exact Heq_parse_tran. done.
      iFrame. iNext.
      iIntros "(PC & mem_instr & pgt_acc & R0 & R1 & R2 & tx & mem_tx) _".
      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".

      iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
      iApply ("IH" $! _ ps_acc trans _ Htotal_rxs Htotal_regs' Hsubset_mb Hsubset_acc Hnin_rx Hnin_tx with "regs tx pgt_tx rx pgt_acc pgt_owned trans_hpool_global
                            tran_pgt_transferred retri rx_state other_rx tran_pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx] P").
      {
        iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
        iSplitL "mem_acc_tx".
        iExists mem_acc_tx;by iFrame "mem_acc_tx".
        iExists mem_tx;by iFrame "mem_tx".
        iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
        set_solver +.
      }
    }
    pose proof (Hvalid_tran_des) as Hvalid_trans_des'.
    apply validate_descriptor in Hvalid_tran_des as [j [ps_donate [-> Hneq_sr]]].
    destruct (decide (ps_donate ⊆ ps_acc)) as [Hsubseteq_donate | Hnsubseteq_donate].
    2:{ (* no access to at least one page in ps_donate, apply [mem_send_not_acc] *)
      apply not_subseteq in Hnsubseteq_donate as [p [Hin_p_share Hnin_p_acc]].
      iApply (mem_send_not_acc ai p with "[PC mem_instr pgt_acc R0 R1 R2 tx mem_tx]");iFrameAutoSolve.
      exact Hdecode_hvc. simpl; reflexivity. lia. exact Heq_parse_tran. done. simpl; exact Hin_p_share.
      iFrame. iNext.
      iIntros "(PC & mem_instr & R0 & R1 & R2 & tx & mem_tx & pgt_acc) _".
      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
      iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".

      iApply ("IH" $! _ ps_acc trans _ Htotal_rxs Htotal_regs' Hsubset_mb Hsubset_acc Hnin_rx Hnin_tx with "regs tx pgt_tx rx pgt_acc pgt_owned trans_hpool_global
                            tran_pgt_transferred retri rx_state other_rx tran_pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx] P").
      {
        iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
        iSplitL "mem_acc_tx".
        iExists mem_acc_tx;by iFrame "mem_acc_tx".
        iExists mem_tx;by iFrame "mem_tx".
        iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
        set_solver +.
      }
    }
    destruct (decide (p_tx ∈ ps_donate)) as [Hin_ptx_share | Hnin_ptx_share].
    { (* tx is not owned by i, apply [mem_send_not_owned] *)
      iDestruct "pgt_tx" as "[own_tx excl_tx]".
      iApply (mem_send_not_owned1 ai with "[PC mem_instr pgt_acc R0 R1 R2 tx mem_tx own_tx]");iFrameAutoSolve.
      exact Hdecode_hvc. simpl; reflexivity. lia. exact Heq_parse_tran. done. simpl; exact Hin_ptx_share. iFrame.
      iNext. iIntros "(PC & mem_instr & pgt_acc & R0 & R1 & R2 & tx & mem_tx & own_tx) _".
      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".

      iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
      iApply ("IH" $! _ ps_acc trans _ Htotal_rxs Htotal_regs' Hsubset_mb Hsubset_acc Hnin_rx Hnin_tx with "regs tx [$own_tx $excl_tx] rx pgt_acc pgt_owned trans_hpool_global
                            tran_pgt_transferred retri rx_state other_rx tran_pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx] P").
      {
        iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
        iSplitL "mem_acc_tx".
        iExists mem_acc_tx;by iFrame "mem_acc_tx".
        iExists mem_tx;by iFrame "mem_tx".
        iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
        set_solver +.
      }
    }

    destruct (decide (p_rx ∈ ps_donate)) as [Hin_prx_share | Hnin_prx_share].
    { (* rx is not owned by i, apply [mem_send_not_owned] *)
      iDestruct "rx" as "[rx [own_rx excl_rx]]".
      iApply (mem_send_not_owned1 ai with "[PC mem_instr pgt_acc R0 R1 R2 tx mem_tx own_rx]");iFrameAutoSolve.
      exact Hdecode_hvc. simpl; reflexivity. lia. exact Heq_parse_tran. done. simpl; exact Hin_prx_share. iFrame.
      iNext. iIntros "(PC & mem_instr & pgt_acc & R0 & R1 & R2 & tx & mem_tx & own_rx) _".
      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".

      iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
      iApply ("IH" $! _ ps_acc trans _ Htotal_rxs Htotal_regs' Hsubset_mb Hsubset_acc Hnin_rx Hnin_tx with "regs tx pgt_tx [$rx $own_rx $excl_rx] pgt_acc pgt_owned trans_hpool_global
                            tran_pgt_transferred retri rx_state other_rx tran_pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx] P").
      {
        iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
        iSplitL "mem_acc_tx".
        iExists mem_acc_tx;by iFrame "mem_acc_tx".
        iExists mem_tx;by iFrame "mem_tx".
        iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
        set_solver +.
      }
    }

    assert (Hsubseteq_donate' : ps_donate ⊆ ps_acc ∖ {[p_rx;p_tx]}).
    { set_solver + Hsubseteq_donate Hnin_ptx_share Hnin_prx_share. }
    clear Hsubseteq_donate Hnin_ptx_share Hnin_prx_share.

    iDestruct "trans_hpool_global" as (hpool) "(%Heq_hsall & fresh_handles & trans)".
    destruct (decide (ps_donate ⊆ ps_acc ∖ {[p_rx; p_tx]} ∖ (pages_in_trans trans))) as [Hsubseteq_donate'' | Hnsubseteq_donate].
    { (* all pages are exclusively owned, ok to perceed *)
      assert (ps_donate ⊆ ps_acc ∖ {[p_rx; p_tx]} ∖ currently_accessible_in_trans_memory_pages i trans) as Hsubseteq.
      {
        assert (currently_accessible_in_trans_memory_pages i trans ⊆ (pages_in_trans trans)).
        {
          rewrite /ps_mem_in_trans.
          apply pages_in_trans_subseteq.
          apply map_filter_subseteq.
        }
        set_solver + H Hsubseteq_donate''.
      }
      iDestruct (fresh_handles_disj with "[$fresh_handles trans]") as "%Hdisj_hpool".
      iDestruct (big_sepM_sep with "trans") as "[$ _]".
      iDestruct (big_sepS_union_acc _ ps_donate with "pgt_owned") as "[pgt_oe_donate Hacc_pgt_oe]";auto.
      destruct (decide (hpool = ∅)).
      { (* no avaiable fresh handles, apply [mem_send_no_fresh_handles] *)
        iApply (mem_send_no_fresh_handles ai hpool j mem_tx ps_donate with "[PC mem_instr pgt_acc pgt_oe_donate R0 R1 R2 fresh_handles tx mem_tx]");iFrameAutoSolve.
        exact Hdecode_hvc. simpl; reflexivity. lia. intro;apply Hneq_sr,symmetry;done. set_solver + Hsubseteq_donate'. iFrame.
        iNext. iIntros "(PC & mem_instr & pgt_oe_donate & pgt_acc & R0 & R1 & R2 & fresh_handles & tx & mem_tx ) _".
        iDestruct ("Hacc_pgt_oe" $! ps_donate with "[] pgt_oe_donate") as "pgt_owned".
        { iPureIntro;set_solver +. }

        iDestruct ("Hacc_regs" $! (ai ^+ 1)%f _ _ _ with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
        iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
        iApply ("IH" $! _ ps_acc trans _ Htotal_rxs Htotal_regs' Hsubset_mb Hsubset_acc Hnin_rx Hnin_tx with "regs tx pgt_tx rx pgt_acc [pgt_owned] [fresh_handles trans]
                            tran_pgt_transferred retri rx_state other_rx tran_pgt_owned  retri_owned [mem_rest mem_acc_tx mem_tx] P").
        pose proof (union_split_difference_intersection_subseteq_L _ _ Hsubseteq) as [<- _]. iFrame.
        iExists hpool. by iFrame.
        {
          iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
          iSplitL "mem_acc_tx".
          iExists mem_acc_tx;by iFrame "mem_acc_tx".
          iExists mem_tx;by iFrame "mem_tx".
          iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
          set_solver +.
        }
      }
      iApply (mem_donate ai j mem_tx hpool ps_donate with "[PC mem_instr pgt_acc pgt_oe_donate R0 R1 R2 fresh_handles tx mem_tx]");iFrameAutoSolve.
      exact Hdecode_hvc. simpl; reflexivity. lia. intro;apply Hneq_sr,symmetry;done. set_solver + Hsubseteq_donate'.
      iFrame. iNext.
      iIntros "(PC & mem_instr & pgt_oe_donate & pgt_acc & R0 & R1 & (%wh & %Hin_wh & R2 & tran_donate & retri_donate & fresh_handles) & tx & mem_tx ) _".
      iDestruct ("Hacc_pgt_oe" $! ∅ with "[] []") as "pgt_owned".
      { iPureIntro. set_solver +. }
      { rewrite big_sepS_empty //. }

      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f _ _ _ with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
      iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".

      (* we will specialize IH with the new [trans'] *)
      pose (<[wh := (i, j, ps_donate, Donation, false)]>trans) as trans'.
      assert (Hlookup_wh_None: trans !! wh = None).
      rewrite -not_elem_of_dom.
      set_solver + Hin_wh Hdisj_hpool.

      assert (ps_donate ∪ accessible_in_trans_memory_pages i trans = accessible_in_trans_memory_pages i trans') as Hrewrite.
      {
        rewrite /trans' /accessible_in_trans_memory_pages.
        rewrite map_filter_insert_True.
        rewrite pages_in_trans_insert //.
        rewrite map_filter_lookup_None. eauto.
        simpl. left. split;auto.
        intro. destruct H as [H []]. inversion H.
      }

      iDestruct (trans_split with "tran_donate") as "[tran_donate tran_donate']".
      iDestruct (trans_split with "tran_donate'") as "[tran_donate' tran_donate'']".
      rewrite half_of_half.
      iDestruct (pgt_split_quarter with "pgt_oe_donate") as "[pgt_donate_1 pgt_donate_3]".

      iApply ("IH" $! _ (ps_acc∖ ps_donate) trans' _ Htotal_rxs Htotal_regs' with "[] [] [] [] regs tx pgt_tx rx pgt_acc [pgt_owned]
                [fresh_handles tran_donate trans pgt_donate_3] [tran_pgt_transferred tran_donate' pgt_donate_1] [retri tran_donate'' retri_donate]
                rx_state other_rx [tran_pgt_owned] [retri_owned] [mem_rest mem_acc_tx mem_tx] [P]").
      { iPureIntro. set_solver + Hsubset_mb Hsubseteq_donate'. }
      { iPureIntro. rewrite (currently_accessible_in_trans_memory_pages_insert_False_None i trans wh) //=.
        2:{ intros [[]|[]];auto. inversion H0. }
        set_solver + Hsubseteq Hsubset_acc.
      }
      { iPureIntro. rewrite -Hrewrite. set_solver + Hsubseteq Hnin_rx. }
      { iPureIntro. rewrite -Hrewrite. set_solver + Hsubseteq Hnin_tx. }
      {
        rewrite union_empty_r_L.
        rewrite /pagetable_entries_excl_owned /pgt.
        rewrite !difference_difference_L.
        assert (currently_accessible_in_trans_memory_pages i trans ∪ ps_donate = (ps_donate ∪ currently_accessible_in_trans_memory_pages i trans')) as ->.
        {
          rewrite union_comm_L. f_equal.
          rewrite /currently_accessible_in_trans_memory_pages. f_equal.
          rewrite map_filter_insert_False.
          rewrite delete_notin //.
          simpl. intro. destruct H as [[_ H]| [_ H]];inversion H.
        }
        rewrite 2!union_assoc_L.
        rewrite (union_comm_L _ ps_donate).
        rewrite big_sepS_sep.
        iFrame "pgt_owned".
      }
      {
        iExists (hpool ∖ {[wh]}).
        iSplit.
        iPureIntro.
        rewrite dom_insert_L.
        rewrite union_assoc_L.
        rewrite -Heq_hsall.
        f_equal.
        rewrite difference_union_L.
        set_solver + Hin_wh.
        rewrite big_sepM_insert;auto.
        iFrame.
        simpl. case_bool_decide.
        done. inversion H.
      }
      {
        rewrite /transaction_pagetable_entries_transferred.
        iApply (big_sepFM_lookup_None_True with "tran_pgt_transferred"); auto.
        simpl. iFrame.
      }
      {
        rewrite /retrievable_transaction_transferred.
        iDestruct (retri_split with "retri_donate") as "[retri_donate retri_donate']".
        iDestruct "retri" as "[retri1 retri2]".
        iSplitL "retri1 retri_donate".
        iApply (big_sepFM_lookup_None_True with "retri1"); auto.
        simpl;eauto.
        iApply (big_sepFM_lookup_None_True with "retri2"); auto.
        simpl;eauto.
        iFrame.
      }
      {
        rewrite /transaction_pagetable_entries_owned.
        iApply (big_sepFM_lookup_None_False with "tran_pgt_owned"); auto.
        simpl;eauto.
        intros [_ ?];contradiction.
      }
      {
        rewrite /retrieved_transaction_owned.
        rewrite -big_sepFM_lookup_None_False;auto.
        simpl. intro. destruct H;contradiction.
      }
      {
        iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
        iSplitL "mem_acc_tx".
        iExists mem_acc_tx;by iFrame "mem_acc_tx".
        iExists mem_tx;by iFrame "mem_tx".
        assert ((ps_acc ∖ ps_donate ∪ accessible_in_trans_memory_pages i trans') = ps_acc ∪ accessible_in_trans_memory_pages i trans') as ->.
        {
          rewrite -Hrewrite.
          rewrite union_assoc_L.
          rewrite difference_union_L.
          set_solver +.
        }
        iApply (memory_pages_split_diff' _ ps_acc with "[mem_rest $mem_acc]").
        set_solver +.
        (* TODO: simplify *)
        assert ((ps_acc ∪ accessible_in_trans_memory_pages i trans') ∖ ps_acc
                = accessible_in_trans_memory_pages i trans' ∖ (ps_acc ∖ {[p_tx]})) as ->.
        {
          assert ((ps_acc ∪ accessible_in_trans_memory_pages i trans') ∖ ps_acc = accessible_in_trans_memory_pages i trans' ∖ ps_acc) as ->.
          set_solver +.
          rewrite -Hrewrite.
          set_solver + Hnin_tx Hsubseteq_donate'.
        }
        assert ((ps_acc ∪ ps_mem_in_trans ) ∖ ps_acc = ps_mem_in_trans ∖ (ps_acc∖ {[p_tx]})) as ->.
        {
          assert ((ps_acc ∪ ps_mem_in_trans ) ∖ ps_acc = ps_mem_in_trans ∖ ps_acc) as ->.
          set_solver +.
          set_solver + Hnin_tx.
        }
        rewrite -Hrewrite.
        rewrite difference_union_distr_l_L.
        assert (ps_donate ∖ (ps_acc ∖ {[p_tx]}) = ∅) as ->.
        set_solver + Hsubseteq_donate'.
        rewrite union_empty_l_L //.
      }
      {
        iApply (P_eq with "P"). done.
        symmetry. apply except_insert_False_None. done. left;done.
        intros.
        destruct (decide (x = j)).
        subst j.
        split.
        rewrite map_filter_insert_not' //=.
        intros [? _]. done.
        intros. rewrite H0 // in Hlookup_wh_None.
        rewrite map_filter_insert_not' //=.
        intros [_ ?]. done.
        intros. rewrite H0 // in Hlookup_wh_None.
        split.
        rewrite map_filter_insert_not' //=.
        intros [? _]. done.
        intros. rewrite H0 // in Hlookup_wh_None.
        rewrite map_filter_insert_not' //=.
        intros [_ ?]. done.
        intros. rewrite H0 // in Hlookup_wh_None.
      }
    }
    { (* at least one page is not exclusively owned by i (i.e. is involved in a transaction) *)
      assert (∃ p, p ∈ ps_donate ∧ p ∈ pages_in_trans trans) as [p [Hin_p_share Hin_p_mem_in_trans]].
      { apply (not_subseteq_diff _ (ps_acc ∖ {[p_rx; p_tx]}));auto. }
      apply elem_of_pages_in_trans in  Hin_p_mem_in_trans as [h [tran [Hlookup_tran Hin_p_tran]]].
      iDestruct (big_sepM_lookup_acc with "trans") as "[[tran_tran pgt_tran] Hacc_trans]";first exact Hlookup_tran.
      iApply (mem_send_in_trans ai p h with "[PC mem_instr pgt_acc R0 R1 R2 tx mem_tx tran_tran]");iFrameAutoSolve.
      exact Hdecode_hvc. simpl; reflexivity. lia. exact Heq_parse_tran. done. simpl; exact Hin_p_share.
      iFrame. iNext.
      iIntros "(PC & mem_instr & pgt_acc & R0 & R1 & R2 & tx & mem_tx & tran_tran) _".
      iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[%Htotal_regs' regs]".
      iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
      iDestruct ("Hacc_trans" with "[$ tran_tran $pgt_tran]") as "trans".

      iApply ("IH" $! _ ps_acc trans _ Htotal_rxs Htotal_regs' Hsubset_mb Hsubset_acc Hnin_rx Hnin_tx with "regs tx pgt_tx rx pgt_acc pgt_owned [fresh_handles trans]
                            tran_pgt_transferred retri rx_state other_rx tran_pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx] P").
      iExists hpool;by iFrame.
      {
        iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
        iSplitL "mem_acc_tx".
        iExists mem_acc_tx;by iFrame "mem_acc_tx".
        iExists mem_tx;by iFrame "mem_tx".
        iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
        set_solver +.
      }
    }
  Qed.

End ftlr_donate.
