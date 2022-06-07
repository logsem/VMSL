From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang trans_extra.
From HypVeri.algebra Require Import base pagetable mem trans mailbox.
From HypVeri.rules Require Import rules_base halt fail run.
From HypVeri.logrel Require Import logrel_prim_extra.
From HypVeri.logrel Require Import ftlr_nop ftlr_mov ftlr_ldr ftlr_str ftlr_cmp ftlr_add ftlr_sub ftlr_mult ftlr_bne ftlr_br.
(* From HypVeri.logrel Require Import ftlr_share ftlr_retrieve ftlr_relinquish ftlr_reclaim ftlr_donate ftlr_lend *)
(*  ftlr_msg_poll ftlr_invalid_hvc. *)
From HypVeri Require Import proofmode.
Import uPred.

Section fundamental_prim.
  Context `{hypconst:HypervisorConstants}.
  Context `{hypparams:!HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.

  Lemma ftlr_p Φ_t Φ_r `(!SliceTransWf Φ_t) `(!SliceRxsWf Φ_r):
  ∀ p_tx p_rx ps_acc trans rxs, interp_access_prim Φ_t Φ_r p_tx p_rx ps_acc trans rxs ⊢ interp_execute_prim.
  Proof.
    rewrite /interp_access_prim /=.
    iIntros (?????) "(%HΦt & %HΦr1 & %HΦr2 & %HΦr3 & %HΦr4 & (%regs & %Htotal_regs & regs) & (tx & [% mem_tx]) & rx & pgt_acc & %Hsubset_mb & %Hsubset_acc & pgt_owned & tran_pgt_owned &
                           retri_owned & mem_owned & VMProp & trans_hpool_global & %Htotal_rxs & rxs_global & rxs_transferred & transferred & VMProps)".

    iDestruct (big_sepSS_difference_singleton _ V0 with "transferred") as "[transferred_except transferred_only]";eauto.
    apply elem_of_set_of_vmids.
    iDestruct (get_trans_ps_disj with "trans_hpool_global") as %Htrans_disj.
    iDestruct (get_trans_neq with "trans_hpool_global") as %Htrans_neq.
    iDestruct (transferred_only_equiv with "transferred_only") as "(tran_pgt_transferred & retri & mem_transferred)";eauto.

    iDestruct (memory_pages_oea_transferred with "[$mem_owned $mem_transferred]") as (?) "mem";eauto.
    clear Htrans_disj Htrans_neq.

    iDestruct (rx_states_split_zero with "[$rxs_global $rxs_transferred]") as "(rxs_global & rxs_transferred
                                 & (rx_state & [% (#rx' & [% mem_rx])]))";auto.
    iAssert (⌜p_rx0 = p_rx⌝%I) with "[rx rx']" as %Hrx_eq.
    {
      iDestruct "rx" as "[rx ?]".
      iApply (rx_agree with "rx' rx").
    }
    subst p_rx0. iClear "rx'".

    (* HACK: adjust the order of assertions in the context, to get the right form of IH *)
    iAssert (rx_states_global (delete V0 rxs)) with "rxs_global" as "rxs_global".
    iAssert (transaction_pagetable_entries_owned V0 trans) with "tran_pgt_owned" as "tran_pgt_owned".
    iAssert (retrieved_transaction_owned V0 trans) with "retri_owned" as "retri_owned".

    set i := V0.
    set ps_mem_in_trans := (accessible_in_trans_memory_pages i trans).

    iDestruct (memory_pages_disj_singleton with "[$mem $mem_rx]") as %Hnin_rx.
    iDestruct (memory_pages_disj_singleton with "[$mem $mem_tx]") as %Hnin_tx.
    (* merge all memory pages together *)
    iDestruct (memory_pages_merge_mb with "[$mem mem_rx mem_tx]") as "mem";auto.
    iCombine "mem_tx mem_rx" as "mem". iExact "mem".
    iDestruct "tx" as "[tx pgt_tx]".
    clear mem_rx mem_tx mem_all; subst ps_mem_in_trans.

    iDestruct (later_intro with "VMProps") as "VMProps".
    rewrite big_sepS_later.

    iAssert (∃ P0 : iProp Σ, VMProp i P0 1)%I with "VMProp" as "VMProp".
    iAssert (big_sepSS_except set_of_vmids i (Φ_t trans)) with "transferred_except" as "transferred_except".
    iAssert (rx_states_transferred Φ_r (delete i rxs)) with "rxs_transferred" as "rxs_transferred".
    iCombine "VMProp VMProps transferred_except rxs_transferred" as "Running".

    iLöb as "IH" forall (regs ps_acc trans rxs Htotal_rxs Htotal_regs Hsubset_mb Hsubset_acc Hnin_rx Hnin_tx).
  (* "regs" : [∗ map] r↦w ∈ regs, r @@ i ->r w *)
  (* "tx" : TX@i:=p_tx *)
  (* "pgt_tx" : p_tx -@O> - ∗ p_tx -@E> true *)
  (* "rx" : rx_page i p_rx *)
  (* "pgt_acc" : i -@A> ps_acc *)
  (* "pgt_owned" : pagetable_entries_excl_owned i (ps_acc ∖ {[p_rx; p_tx]} ∖ currently_accessible_in_trans_memory_pages i trans) *)
  (* "trans_hpool_global" : transaction_hpool_global_transferred trans *)
  (* "tran_pgt_transferred" : transaction_pagetable_entries_transferred i trans *)
  (* "retri" : retrievable_transaction_transferred i trans *)
  (* "rx_state" : rx_state_get i rxs *)
  (* "rxs_global" : rx_states_global (delete i rxs) *)
  (* "tran_pgt_owned" : transaction_pagetable_entries_owned i trans *)
  (* "retri_owned" : retrieved_transaction_owned i trans *)
  (* "mem" : ∃ mem : lang.mem, memory_pages (ps_acc ∪ accessible_in_trans_memory_pages i trans) mem *)
  (* "Running" : (∃ P0 : iProp Σ, VMProp i P0 1) ∗ ([∗ set] y ∈ (set_of_vmids ∖ {[i]}), ▷ VMProp y (vmprop_unknown y Φ_t Φ_r) (1 / 2)) ∗ *)
  (*             big_sepSS_except set_of_vmids i (Φ_t trans) ∗ rx_states_transferred Φ_r (delete i rxs) *)

    set ps_mem_in_trans := (accessible_in_trans_memory_pages i trans).

    (* split memory pages into [mem_acc] and [mem_rest] *)
    iDestruct (memory_pages_split_diff' _ ps_acc with "mem") as "[mem_rest mem_acc]". set_solver.
    iDestruct (memory_pages_split_singleton' p_tx ps_acc with "mem_acc") as "[mem_acc_tx mem_tx]". set_solver + Hsubset_mb.
    iDestruct ("mem_acc_tx") as (mem_acc_tx) "mem_acc_tx".

    pose proof (Htotal_regs PC) as Hlookup_PC.
    destruct Hlookup_PC as [ai Hlookup_PC].
    (* sswp *)
    rewrite /interp_execute_prim. rewrite ->wp_sswp.
    destruct (decide ((tpa ai) ∈ ps_acc)) as [Hin_ps_acc | Hnotin_ps_acc].
    { (* i has access *)
      destruct (decide (tpa ai = p_tx)) as [Heq_ptx | Hneq_ptx].
      { (*invalid instruction location *)
        iDestruct (reg_big_sepM_split i Hlookup_PC with "[$regs]") as "[PC _]".
        iApply (invalid_pc_in_tx _ ai with "[PC tx]"); iFrameAutoSolve.
        iNext.
        iIntros "? _".
        by iApply wp_terminated.
      }
      assert (Hin_ps_acc_tx': (tpa ai) ∈ ps_acc ∖ {[p_tx]}).
      { set_solver + Hin_ps_acc Hneq_ptx. }
      iDestruct "mem_acc_tx" as "[%Hdom_mem_acc_tx mem_acc_tx]".
      pose proof Hin_ps_acc_tx' as Hin_ps_acc_tx.
      apply elem_of_set_of_addr_tpa in Hin_ps_acc_tx'.
      rewrite -Hdom_mem_acc_tx in Hin_ps_acc_tx'.
      rewrite elem_of_dom in Hin_ps_acc_tx'.
      destruct Hin_ps_acc_tx' as [instr Hlookup_mem_ai].
      destruct (decode_instruction instr) as [instr'|] eqn:Heqn.
      { (* valid instruction *)
        destruct instr'.
        { (* nop *)
          iApply (ftlr_nop with "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri
                 rx_state rx rxs_global tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx Running");iFrameAutoSolve.
          all:done.
        }
        {
          iApply (ftlr_mov with "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri
                 rx_state rx rxs_global tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx Running");iFrameAutoSolve.
          all:done.
        }
        {
          iApply (ftlr_ldr with "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri
                 rx_state rx rxs_global tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx Running");iFrameAutoSolve.
          all:done.
        }
        {
          iApply (ftlr_str with "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri
                 rx_state rx rxs_global tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx Running");iFrameAutoSolve.
          all:done.
        }
        {
          iApply (ftlr_cmp with "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri
                 rx_state rx rxs_global tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx Running");iFrameAutoSolve.
          all:done.
        }
        {
          iApply (ftlr_add with "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri
                 rx_state rx rxs_global tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx Running");iFrameAutoSolve.
          all:done.
        }
        {
          iApply (ftlr_sub with "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri
                 rx_state rx rxs_global tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx Running");iFrameAutoSolve.
          all:done.
        }
        {
          iApply (ftlr_mult with "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri
                 rx_state rx rxs_global tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx Running");iFrameAutoSolve.
          all:done.
        }
        {
          iApply (ftlr_bne with "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri
                 rx_state rx rxs_global tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx Running");iFrameAutoSolve.
          all:done.
        }
        {
          iApply (ftlr_br with "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri
                 rx_state rx rxs_global tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx Running");iFrameAutoSolve.
          all:done.
        }
        { (* halt *)
          pose proof Heqn as Hdecode.
          (* getting registers *)
          iDestruct ((reg_big_sepM_split_upd i Hlookup_PC)
                      with "[$regs]") as "(PC & Hacc_regs)"; [done|].
          (* we don't update memory *)
          iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "[$mem_acc_tx]")
            as "[mem_instr Hacc_mem_acc_tx]".
          iApply (halt (p_tx := p_tx) with "[PC pgt_acc mem_instr tx]"); iFrameAutoSolve.
          iNext. iIntros "? _".
          by iApply wp_terminated.
        }
        { (* fail *)
          pose proof Heqn as Hdecode.
          (* getting registers *)
          iDestruct ((reg_big_sepM_split_upd i Hlookup_PC)
                      with "[$regs]") as "(PC & Hacc_regs)"; [done|].
          (* we don't update memory *)
          iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "[$mem_acc_tx]")
            as "[mem_instr Hacc_mem_acc_tx]".
          iApply (fail with "[PC pgt_acc mem_instr tx]"); iFrameAutoSolve.
          iNext. iIntros "? _".
          by iApply wp_terminated.
        }
        {
          pose proof (Htotal_regs R0) as [r0 Hlookup_reg_R0].
          destruct (decode_hvc_func r0) as [hvc_f |] eqn:Hdecode_hvc .
          {
            iAssert (⌜p_tx ≠ p_rx⌝)%I as "%Hneq_mb".
            {
              iDestruct "rx" as "[_ [_ excl_rx]]".
              iDestruct "pgt_tx" as "[_ excl_tx]".
              iApply (excl_ne with "[$ excl_tx $ excl_rx]").
            }
            destruct (hvc_f).
            { (* RUN *)
              pose proof (Htotal_regs R1) as [r1 Hlookup_reg_R1].
              destruct (decode_vmid r1) as [v |] eqn:Hdecode_r1.
              {
                destruct (decide (v = V0)).
                { (* run_primary *)
                  iDestruct (reg_big_sepM_split_upd3 i Hlookup_PC Hlookup_reg_R0 Hlookup_reg_R1 with "[$regs]")
                    as "(PC & R0 & R1 & Hacc_regs)";eauto.
                  iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "mem_acc_tx") as "[mem_instr Hacc_mem_acc]".

                  iApply (run_primary ai with "[PC R0 R1 pgt_acc tx mem_instr]"); iFrameAutoSolve.
                  subst v. done.
                  iNext. iIntros "(PC & mem_instr & pgt_acc & tx & R0 & R1) _".
                  iDestruct ("Hacc_regs" $! (ai ^+ 1)%f _ _ with "[$PC $R0 $R1]") as "[%regs' [%Htotal_regs' regs]]".
                  iDestruct ("Hacc_mem_acc" with "[$mem_instr]") as "mem_acc_tx".
                    iApply ("IH" $! regs' ps_acc trans rxs Htotal_rxs Htotal_regs' Hsubset_mb Hsubset_acc Hnin_rx Hnin_tx with
                             "regs tx pgt_tx rx pgt_acc pgt_owned  trans_hpool_global tran_pgt_transferred retri rx_state rxs_global
                              tran_pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx] [Running]").
                    {
                      iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx $mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
                      iExists mem_acc_tx;by iFrame "mem_acc_tx".
                      iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
                      set_solver +.
                    }
                    { iDestruct "Running" as "($&?&$&$)". rewrite <-big_sepS_later. iFrame. }
                }
                {
                pose proof (Htotal_regs R2) as [r2 Hlookup_reg_R2].
                iDestruct (reg_big_sepM_split_upd4 i Hlookup_PC Hlookup_reg_R0 Hlookup_reg_R1 Hlookup_reg_R2 with "[$regs]")
                  as "(PC & R0 & R1 & R2 & Hacc_regs)";eauto.
                pose proof (union_split_difference_intersection_L (ps_acc∖ {[p_tx]}) ({[p_rx]} ∪ (transferred_memory_pages i trans)))
                  as [Heq_ps_acc_tx Hdisj_ps_acc_tx].
                rewrite Heq_ps_acc_tx in Hdom_mem_acc_tx.
                rewrite set_of_addr_union in Hdom_mem_acc_tx;last auto.
                apply dom_union_inv_L in Hdom_mem_acc_tx;last apply set_of_addr_disj;auto.
                destruct Hdom_mem_acc_tx as (mem_oea & mem_inters & Heq_mem_acc_tx' & Hdisj_mem_oea_inters & Hdom_mem_oea & Hdom_mem_inters).
                rewrite Heq_mem_acc_tx'.
                iDestruct (big_sepM_union with "mem_acc_tx") as "[mem_oea mem_inters]";auto.

                iDestruct (get_trans_ps_disj with "trans_hpool_global") as %Htrans_disj.
                iDestruct (get_trans_neq with "trans_hpool_global") as %Htrans_neq.

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
                  rewrite (accessible_retrieved_lending_memory_pages_difference i trans).
                  rewrite union_intersection_r_L.
                  rewrite union_comm_L difference_union_L.
                  assert(ps_mem_in_trans ∖ retrieved_lending_memory_pages i trans ∪ ps_mem_in_trans ∖ (ps_acc ∖ {[p_tx]})=
                           ps_mem_in_trans ∖ retrieved_lending_memory_pages i trans) as H.
                  rewrite union_comm_L.
                  apply subseteq_union_1_L.
                  pose proof (retrieved_lending_currently_accessible_memory_pages_subseteq i trans).
                  set_solver + Hsubset_acc H.
                  rewrite H.
                  set_solver +.
                  done.
                }

                iDestruct (get_valid_accessible_in_trans_memory_pages with "[$trans_hpool_global $pgt_owned]") as %Hvalid_acc_in_tran.
                set_solver + Hsubset_acc.

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

                  iDestruct (memory_pages_split_singleton' p_rx with "mem_tran") as "[mem_transferred mem_rx]".
                  set_solver +.
                  replace (({[p_rx]} ∪ transferred_memory_pages i trans) ∖ {[p_rx]}) with (transferred_memory_pages i trans).
                  2:{
                    pose proof (transferred_retrieved_lending_memory_pages_union i trans).
                    set_solver + H Hnin_rx.
                  }

                  (* organizing big_sepSS: merging i and splitting v *)
                  iDestruct (transferred_only_equiv with "[$tran_pgt_transferred $retri $mem_transferred]") as "transferred_only";eauto.
                  rewrite /big_sepSS_except.
                  assert (Hvmids_eq: set_of_vmids = (set_of_vmids ∖ {[i]} ∪ {[i]})).
                  {
                    pose proof (elem_of_set_of_vmids i).
                    rewrite union_comm_L.
                    apply union_difference_L.
                    set_solver + H.
                  }

                  iDestruct "Running" as "([% VMProp] & VMProps & transferred_except & rxs_transferred)".
                  iDestruct (big_sepSS_union_singleton _ i with "[$transferred_except transferred_only]") as "transferred";auto.
                  set_solver +. rewrite -Hvmids_eq. iFrame.
                  rewrite -Hvmids_eq.
                  iDestruct (big_sepSS_difference_singleton _ v with "transferred") as "[transferred_except transferred_only]";eauto.
                  apply elem_of_set_of_vmids.

                  (* organizing rx_states: merging i and splitting v *)
                  iAssert(RX@i := p_rx)%I  with "[rx]"  as "#rx'".
                  iDestruct "rx" as "[$ _]".
                  iDestruct (rx_state_merge_zero with "[$rxs_global $rxs_transferred rx_state mem_rx]") as "[rxs_global rxs_transferred]";auto.
                  iFrame "rx_state". iExists p_rx. iFrame "rx' mem_rx".
                  iDestruct (rx_states_split v with "[$rxs_global $rxs_transferred]") as "(rxs_global & rxs_transferred & rx_state_v)";auto.

                  (* split VMProp v *)
                  iDestruct (big_sepS_elem_of_acc _ _ v with "VMProps") as "[VMProp_v VMProps_acc]".
                  pose proof (elem_of_set_of_vmids v). set_solver + H n i.
                  
                  (* getting instruction from [mem_oea] *)
                  iDestruct (mem_big_sepM_split mem_oea Hlookup_mem_ai' with "mem_oea") as "[mem_instr Hacc_mem]".
                  iDestruct ("tx") as "#tx".

                  iApply (run ai v (transaction_hpool_global_transferred trans ∗
                                      big_sepSS_singleton set_of_vmids v (Φ_t trans) ∗
                                      rx_states_global (delete v rxs) ∗
                                      (∀ rs : option (Addr * VMID), ⌜rxs !! v = Some rs⌝ -∗ rx_state_match v rs ∗ Φ_r v rs v)
                            )%I (vmprop_zero v Φ_t Φ_r trans rxs)
                           with "[PC R0 R1 R2 pgt_acc $tx mem_instr rxs_global VMProp VMProp_v
                           trans_hpool_global transferred_only rx_state_v]"); iFrameAutoSolve.
                  {
                    iSplitL "VMProp_v". iNext. iExact "VMProp_v".
                    iSplitL "VMProp". iNext. iExact "VMProp".
                    iSplitL "R2".
                    {
                      iNext. iIntros "((PC & instr & pgt_acc & _ & R0 & R1) & (trans_hpool_global & trans_transferred & rxs_global
                      & rx_state_v) & vmprop0)".
                      rewrite vmprop_unknown_eq.
                      iSplitR "PC instr pgt_acc".
                      iExists trans, rxs.
                      iFrame "trans_hpool_global trans_transferred rx_state_v rxs_global vmprop0".
                      iSplitL "R0". iExists _. iSplitL. iExact "R0". done.
                      iSplitL "R1". iExists _. iSplitL. iExact "R1". done.
                      iSplitL "R2". iExists _. iExact "R2". done.
                      iCombine "PC instr pgt_acc" as "R". iExact "R".
                    }
                    {
                      iNext. iFrame "trans_hpool_global transferred_only". iFrame.
                    }
                  }
                  iNext. iIntros "[(PC & instr & pgt_acc) VMProp] HHolds". simpl.
                  iDestruct (VMProp_holds_agree i with "[$HHolds $VMProp]") as "[Hres VMProp]".
                  iEval (rewrite /vmprop_zero /vmprop_zero_pre) in "Hres".
                  iEval (rewrite later_exist) in "Hres". iDestruct "Hres" as (trans') "Hres".
                  iEval (rewrite later_exist) in "Hres". iDestruct "Hres" as (rx_state_v') "Hres".
                  iEval (rewrite 5!later_sep) in "Hres".
                  pose proof (slice_rxs_timeless Φ_r) as Htl1.
                  pose proof (slice_trans_timeless Φ_t) as Htl2.
                  iDestruct "Hres" as "(>trans_hpool_global & >transferred_only & >rx_state_v & >rx_transferred & >regs_rx & VMProp_v)".
                  clear Htl1 Htl2.
                  iDestruct (slice_preserve_except _ _ (except v trans) with "transferred_except") as "transferred_except".
                  symmetry. apply except_idemp.
                  iDestruct (slice_trans_unify with "[$transferred_only $transferred_except]") as "transferred".

                  iDestruct (big_sepSS_difference_singleton _ V0 with "transferred") as "[transferred_except transferred_only]";eauto.
                  apply elem_of_set_of_vmids.
                  iDestruct (get_trans_ps_disj with "trans_hpool_global") as %Htrans_disj'.
                  iDestruct (get_trans_neq with "trans_hpool_global") as %Htrans_neq'.
                  iDestruct (transferred_only_equiv with "transferred_only") as "(tran_pgt_transferred & retri & mem_transferred)";eauto.
                  iDestruct ("Hacc_mem" with "instr") as "mem_oea".

                  iDestruct (get_trans_rel_secondary with "[$trans_hpool_global $retri $tran_pgt_owned $retri_owned]") as "%trans_rel".
                  erewrite (trans_rel_secondary_currently_accessible_memory_pages);eauto.
                  erewrite (trans_rel_secondary_currently_accessible_memory_pages) in Hsubset_acc;eauto.
                  iDestruct (trans_rel_secondary_transaction_pagetable_entries_owned with "tran_pgt_owned") as "tran_pgt_owned";eauto.
                  iDestruct (trans_rel_secondary_retrieved_transaction_owned with "retri_owned") as "retri_owned";eauto.

                  set trans'' := (only v trans' ∪ (except v trans)).

                  iAssert (⌜(ps_acc ∖ {[p_tx]} ∖ ({[p_rx]} ∪ transferred_memory_pages i trans)
                             = ps_acc ∖ {[p_rx; p_tx]} ∖ transferred_memory_pages i trans'')⌝)%I as "%H".
                  {
                    iDestruct (get_valid_accessible_in_trans_memory_pages with "[$trans_hpool_global $pgt_owned]") as %Hvalid_acc_in_tran'.
                    set_solver + Hsubset_acc.
                    iPureIntro.
                    rewrite difference_difference_L.
                    rewrite union_assoc_L (union_comm_L {[p_tx]}).
                    rewrite -(difference_difference_L _ {[p_rx; p_tx]}).
                    apply acc_transferred_memory_pages_difference;auto.
                    erewrite <-(trans_rel_secondary_currently_accessible_memory_pages _ trans trans'') in Hsubset_acc;eauto.
                    rewrite union_comm_L.
                    exact Hsubset_acc.
                  }
                  iAssert (∃ mem_all : mem, memory_pages (ps_acc ∖ {[p_rx; p_tx]} ∪ accessible_in_trans_memory_pages i trans'') mem_all)%I
                    with "[mem_oea mem_transferred]" as (?) "mem".
                  {
                    iAssert(∃ m: mem, memory_pages (ps_acc ∖ {[p_tx]} ∖ ({[p_rx]} ∪ transferred_memory_pages i trans)) m)%I with "[mem_oea]" as "mem_oea".
                    iExists _. iSplit; done.
                    rewrite H.
                    iDestruct(memory_pages_union' with "[$mem_oea $mem_transferred]") as "mem". iFrame.
                    rewrite acc_accessible_in_trans_memory_pages_union;auto.
                    rewrite union_comm_L //.
                  }

                  clear Htrans_disj Htrans_neq.
                  iDestruct ("VMProps_acc" with "VMProp_v") as "VMProps".

                  iDestruct ("regs_rx") as "[([R0| [R0 %Hrxstate_eq]] & rxs_global & R1 & [% R2])
                            | (R0 & (%&%& Φjv & rxs_global & %Hlookup_rxs & (%& R1 & %Hdecode_r1') & R2))]";
                    iDestruct ("Hacc_regs" $! (ai ^+ 1)%f _ _ _ with "[PC R0 R1 R2]") as "[%regs' [%Htotal_regs' regs'']]"; iFrameAutoSolve.
                  { (* yield *)
                    iDestruct (rx_states_merge_yield with "[$rxs_global $rxs_transferred $rx_state_v $rx_transferred]") as
                      "(rxs_global & rxs_transferred)";auto.

                    pose proof (base_extra.is_total_gmap_insert rxs v rx_state_v' Htotal_rxs) as Htotal_rxs'.
                    iDestruct (rx_states_split_zero with "[$rxs_global $rxs_transferred]") as "(rxs_global & rxs_transferred
                                 & (rx_state & [% (#rx'' & [% mem_rx])]))";auto.
                    iAssert (⌜p_rx0 = p_rx⌝%I) with "[rx' rx'']" as %Hrx_eq. iApply (rx_agree with "rx'' rx'").
                    iClear "rx''". subst p_rx0.

                    set ps_mem_in_trans' := (accessible_in_trans_memory_pages i trans'').

                    iDestruct (memory_pages_disj_singleton with "[$mem $mem_rx]") as %Hnin_rx'.
                    iDestruct "mem_tx" as "[%mem_tx mem_tx]".
                    iDestruct (memory_pages_disj_singleton with "[$mem $mem_tx]") as %Hnin_tx'.

                    (* merge all memory pages together *)
                    iDestruct (memory_pages_merge_mb with "[$mem mem_rx mem_tx]") as "mem";auto.
                    iCombine "mem_tx mem_rx" as "mem". iExact "mem".
                    clear mem_rx mem_tx mem_all; subst ps_mem_in_trans.

                    set rxs' := (<[v:=rx_state_v']> rxs).
                    iApply ("IH" $! regs' ps_acc trans'' rxs' Htotal_rxs' Htotal_regs' Hsubset_mb Hsubset_acc Hnin_rx' Hnin_tx' with
                             "regs'' tx pgt_tx rx pgt_acc pgt_owned  trans_hpool_global tran_pgt_transferred retri rx_state rxs_global
                              tran_pgt_owned retri_owned mem [$transferred_except $rxs_transferred VMProp $VMProps]").
                    { iExists _. iExact "VMProp". }
                  }
                  { (* wait, same *)
                    iDestruct (rx_states_merge_yield with "[$rxs_global $rxs_transferred $rx_state_v $rx_transferred]") as
                      "(rxs_global & rxs_transferred)";auto.

                    pose proof (base_extra.is_total_gmap_insert rxs v rx_state_v' Htotal_rxs) as Htotal_rxs'.
                    iDestruct (rx_states_split_zero with "[$rxs_global $rxs_transferred]") as "(rxs_global & rxs_transferred
                                 & (rx_state & [% (#rx'' & [% mem_rx])]))";auto.
                    iAssert (⌜p_rx0 = p_rx⌝%I) with "[rx' rx'']" as %Hrx_eq. iApply (rx_agree with "rx'' rx'").
                    iClear "rx''". subst p_rx0.

                    set ps_mem_in_trans' := (accessible_in_trans_memory_pages i trans'').

                    iDestruct (memory_pages_disj_singleton with "[$mem $mem_rx]") as %Hnin_rx'.
                    iDestruct "mem_tx" as "[%mem_tx mem_tx]".
                    iDestruct (memory_pages_disj_singleton with "[$mem $mem_tx]") as %Hnin_tx'.

                    (* merge all memory pages together *)
                    iDestruct (memory_pages_merge_mb with "[$mem mem_rx mem_tx]") as "mem";auto.
                    iCombine "mem_tx mem_rx" as "mem". iExact "mem".
                    clear mem_rx mem_tx mem_all; subst ps_mem_in_trans.

                    set rxs' := (<[v:=rx_state_v']> rxs).
                    iApply ("IH" $! regs' ps_acc trans'' rxs' Htotal_rxs' Htotal_regs' Hsubset_mb Hsubset_acc Hnin_rx' Hnin_tx' with
                             "regs'' tx pgt_tx rx pgt_acc pgt_owned  trans_hpool_global tran_pgt_transferred retri rx_state rxs_global
                              tran_pgt_owned retri_owned mem [$transferred_except $rxs_transferred VMProp $VMProps]").
                    { iExists _. iExact "VMProp". }
                  }
                  { (* send *)
                    iDestruct (rx_states_merge_send with "[$rxs_global $rxs_transferred $rx_state_v $rx_transferred $Φjv]") as
                      "(rxs_global & rxs_transferred)";auto.

                    assert (Htotal_rxs': base_extra.is_total_gmap (<[j:= Some (l,v)]>(<[v := rx_state_v']> rxs))).
                    by repeat apply base_extra.is_total_gmap_insert.
                    iDestruct (rx_states_split_zero with "[$rxs_global $rxs_transferred]") as "(rxs_global & rxs_transferred
                                 & (rx_state & [% (#rx'' & [% mem_rx])]))";auto.

                    iAssert (⌜p_rx0 = p_rx⌝%I) with "[rx' rx'']" as %Hrx_eq. iApply (rx_agree with "rx'' rx'").
                    iClear "rx''". subst p_rx0.

                    set ps_mem_in_trans' := (accessible_in_trans_memory_pages i trans'').

                    iDestruct (memory_pages_disj_singleton with "[$mem $mem_rx]") as %Hnin_rx'.
                    iDestruct "mem_tx" as "[%mem_tx mem_tx]".
                    iDestruct (memory_pages_disj_singleton with "[$mem $mem_tx]") as %Hnin_tx'.

                    (* merge all memory pages together *)
                    iDestruct (memory_pages_merge_mb with "[$mem mem_rx mem_tx]") as "mem";auto.
                    iCombine "mem_tx mem_rx" as "mem". iExact "mem".
                    clear mem_rx mem_tx mem_all; subst ps_mem_in_trans.

                    set rxs' := (<[j:= Some (l,v)]>(<[v:=rx_state_v']> rxs)).
                    iApply ("IH" $! regs' ps_acc trans'' rxs' Htotal_rxs' Htotal_regs' Hsubset_mb Hsubset_acc Hnin_rx' Hnin_tx' with
                             "regs'' tx pgt_tx rx pgt_acc pgt_owned  trans_hpool_global tran_pgt_transferred retri rx_state rxs_global
                              tran_pgt_owned retri_owned mem [$transferred_except $rxs_transferred VMProp $VMProps]").
                    { iExists _. iExact "VMProp". }
                  }
                }
                { (* instruction is in rx *)

                (* iDestruct (memory_pages_union' with "[$mem_rest mem_inters]") as "mem_transferred";auto. *)
                (* iExists mem_inters. iSplit. iPureIntro. exact Hdom_mem_inters. iFrame "mem_inters". *)

                (* spliting rx from mem_inters *)
                assert (Hsplit_rx: ((ps_acc ∖ {[p_tx]}) ∩ ({[p_rx]} ∪ transferred_memory_pages i trans))
                    = {[p_rx]} ∪ ((ps_acc ∖ {[p_tx]} ∖ {[p_rx]}) ∩ (transferred_memory_pages i trans))).
                rewrite intersection_union_l_L.
                assert ((ps_acc ∖ {[p_tx]}) ∩ {[p_rx]} = {[p_rx]}) as ->. set_solver + Hneq_mb Hsubset_mb.
                f_equal.
                pose proof (transferred_accessible_memory_pages_subseteq i trans).
                set_solver + H Hnin_rx.

                rewrite Hsplit_rx in Hdom_mem_inters.

                assert (Hnin_rx' : {[p_rx]} ## transferred_memory_pages i trans).
                pose proof (transferred_accessible_memory_pages_subseteq i trans).
                set_solver + H Hnin_rx.
                iPoseProof (memory_pages_split_union {[p_rx]} ((ps_acc ∖ {[p_tx]} ∖ {[p_rx]}) ∩ transferred_memory_pages i trans))as "[Ht _]".
                set_solver + Hnin_rx'.

                iDestruct ("Ht" with "[mem_inters]") as "(%mem_rx & %mem_inters' & mem_rx & mem_inters & %Heq_mem_inters)".
                iSplit. iPureIntro. exact Hdom_mem_inters. iFrame "mem_inters".
                iClear "Ht". subst mem_inters.

                destruct (decide (tpa ai = p_rx)).
                { (* TODO: in rx, easy? *)
                  admit.
                }
                {

                assert (Hin_ps_inters : tpa ai ∈ (ps_acc ∖ {[p_tx]} ∖ {[p_rx]}) ∩ (transferred_memory_pages i trans)).
                {
                  rewrite Heq_ps_acc_tx in Hin_ps_acc_tx.
                  rewrite elem_of_union in Hin_ps_acc_tx.
                  destruct Hin_ps_acc_tx.
                  set_solver + H Hnin_ps_oea.
                  set_solver + H n0.
                }

                assert (Hsplit_trans: (transferred_memory_pages i trans) = (transferred_memory_pages i (only v trans))
                                                                        ∪ (transferred_memory_pages i (except v trans))).
                (* TODO:also disj *)
                admit.
                iEval (rewrite Hsplit_trans intersection_union_l_L) in "mem_inters".

                rewrite Hsplit_trans in Hin_ps_inters.

                assert (ps_acc ∪ ps_mem_in_trans = ps_acc ∪ (transferred_memory_pages i trans)) as ->.
                admit.

                iEval (rewrite /ps_mem_in_trans Hsplit_trans) in "mem_rest".
                assert (((ps_acc ∪ (transferred_memory_pages i (only v trans) ∪ transferred_memory_pages i (except v trans))) ∖ ps_acc) =
                       ((transferred_memory_pages i (only v trans) ∪ transferred_memory_pages i (except v trans)) ∖ ps_acc)) as ->.
                admit.

                rewrite difference_union_distr_l_L.
                iDestruct (memory_pages_split_union' with "mem_rest") as "[mem_rest_a mem_rest_b]".
                {
                  (* transferred_memory_pages i (only v trans) ∖ ps_acc ## transferred_memory_pages i (except v trans) ∖ ps_acc                  *)
                  admit.
                }

                assert(∀ trans_sub,
                         trans_sub ⊆ trans ->
                      (ps_acc ∖ {[p_tx]} ∖ {[p_rx]}) ∩ (transferred_memory_pages i trans_sub) ∪ (transferred_memory_pages i trans_sub) ∖ ps_acc =
                          transferred_memory_pages i trans_sub).
                {
                  intros ? Hsubset_trans.
                  rewrite intersection_comm_L.
                  assert (∀ trans trans', trans ⊆ trans' -> transferred_memory_pages i trans ⊆ transferred_memory_pages i trans').
                  admit.
                  specialize (H trans_sub trans Hsubset_trans).
                  pose proof (union_split_difference_intersection_L (transferred_memory_pages i trans_sub) ps_acc) as [Heq _].
                  assert (transferred_memory_pages i trans_sub ∩ (ps_acc ∖ {[p_tx]} ∖ {[p_rx]})
                          = transferred_memory_pages i trans_sub ∩ ps_acc) as ->.
                  {
                    assert (Hnin_tx' : {[p_tx]} ## transferred_memory_pages i trans).
                    pose proof (transferred_accessible_memory_pages_subseteq i trans).
                    set_solver + H0 Hnin_tx.
                    set_solver + H Hnin_tx' Hnin_rx'.
                  }
                  rewrite Heq. set_solver +.
                }

                iAssert (⌜mem_rx ##ₘ mem_inters'⌝%I )with "[mem_rx mem_inters]" as "%Hdisj_rx_inters'".
                {
                  iDestruct "mem_rx" as "[%Hdom_mem_rx _]".
                  iDestruct "mem_inters" as "[%Hdom_mem_inters' _]".
                  iPureIntro.
                  apply map_disjoint_dom.
                  rewrite Hdom_mem_inters' Hdom_mem_rx.
                  apply set_of_addr_disj.
                  set_solver +.
                }

                iPoseProof (memory_pages_split_union ((ps_acc ∖ {[p_tx]} ∖ {[p_rx]}) ∩ transferred_memory_pages i (only v trans))
                                                     ((ps_acc ∖ {[p_tx]} ∖ {[p_rx]}) ∩ transferred_memory_pages i (except v trans))
                             )as "[Ht _]".
                (* transferred_memory_pages i (only v trans) ## transferred_memory_pages i (except v trans) *)
                admit.

                iDestruct ("Ht" with "[mem_inters]") as "(%mem_inters_a & %mem_inters_b & mem_inters_a & mem_inters_b & %Heq_mem_inters)".
                iExact "mem_inters".
                iClear "Ht". subst mem_inters'.


                (* organizing big_sepSS: merging i and splitting v *)
                (* iDestruct (transferred_only_equiv with "[$tran_pgt_transferred $retri $mem_transferred]") as "transferred_only";eauto. *)
                (* rewrite /big_sepSS_except. *)
                (* assert (Hvmids_eq: set_of_vmids = (set_of_vmids ∖ {[i]} ∪ {[i]})). *)
                (* { *)
                (*   pose proof (elem_of_set_of_vmids i). *)
                (*   rewrite union_comm_L. *)
                (*   apply union_difference_L. *)
                (*   set_solver + H. *)
                (* } *)

                (* TODO split the following two *)
                (* "tran_pgt_transferred" : transaction_pagetable_entries_transferred i trans *)
                (* "retri" : retrievable_transaction_transferred i trans *)

                iDestruct "Running" as "([% VMProp] & VMProps & transferred_except & rxs_transferred)".
                (* iDestruct (big_sepSS_union_singleton _ i with "[$transferred_except transferred_only]") as "transferred";auto. *)
                (* set_solver +. rewrite -Hvmids_eq. iFrame. *)
                (* rewrite -Hvmids_eq. *)
                iDestruct (big_sepSS_difference_singleton _ v with "transferred_except") as "[transferred_except_v transferred_only_v]";eauto.
                pose proof (elem_of_set_of_vmids v). set_solver + H0 n.

                (* organizing rx_states: merging i and splitting v *)
                iAssert(RX@i := p_rx)%I  with "[rx]"  as "#rx'".
                iDestruct "rx" as "[$ _]".
                iDestruct (rx_state_merge_zero with "[$rxs_global $rxs_transferred rx_state mem_rx]") as "[rxs_global rxs_transferred]"; auto.
                iFrame "rx_state". iExists p_rx. iFrame "rx'". iExists mem_rx. rewrite memory_pages_singleton. iFrame "mem_rx".
                iDestruct (rx_states_split v with "[$rxs_global $rxs_transferred]") as "(rxs_global & rxs_transferred & rx_state_v)";auto.

                (* split VMProp v *)
                iDestruct (big_sepS_elem_of_acc _ _ v with "VMProps") as "[VMProp_v VMProps_acc]".
                pose proof (elem_of_set_of_vmids v). set_solver + H0 n i.

                iDestruct ("tx") as "#tx".

                rewrite intersection_union_l_L in Hin_ps_inters.
                apply elem_of_union in Hin_ps_inters.
                destruct Hin_ps_inters as [Hin_ps_only | Hnin_ps_only].
                {
                  assert (Hsubseteq_mem_acc: mem_inters_a ⊆ mem_acc_tx).
                  rewrite Heq_mem_acc_tx'.
                  apply map_union_subseteq_r'. done.
                  apply map_union_subseteq_r'. done.
                  apply map_union_subseteq_l.
                  rewrite map_subseteq_spec in Hsubseteq_mem_acc.
                  apply elem_of_set_of_addr_tpa in Hin_ps_only.
                  iDestruct "mem_inters_a" as "[%Hdom_mem_inters_a mem_inters_a]".
                  rewrite -Hdom_mem_inters_a in Hin_ps_only.
                  rewrite elem_of_dom in Hin_ps_only.
                  destruct Hin_ps_only as [? Hlookup_mem_ai'].
                  specialize (Hsubseteq_mem_acc ai _ Hlookup_mem_ai').
                  rewrite Hlookup_mem_ai in Hsubseteq_mem_acc.
                  inversion Hsubseteq_mem_acc.
                  subst x. clear Hsubseteq_mem_acc.

                  iDestruct (memory_pages_union' with "[mem_inters_b $mem_rest_b]") as "mem_b".
                  { iExists mem_inters_b. iExact "mem_inters_b". }
                  iEval (rewrite union_comm_L) in "mem_b".
                  rewrite (H (except v trans)). 2: (*except v trans ⊆ trans*) admit.

                  (* getting instruction from [mem_inters_a] *)
                  iDestruct (mem_big_sepM_split mem_inters_a Hlookup_mem_ai' with "mem_inters_a") as "[mem_instr Hacc_mem]".

                  iApply (run ai v (transaction_hpool_global_transferred trans ∗
                                      big_sepSS_singleton set_of_vmids v (Φ_t trans) ∗
                                      rx_states_global (delete v rxs) ∗
                                      (∀ rs : option (Addr * VMID), ⌜rxs !! v = Some rs⌝ -∗ rx_state_match v rs ∗ Φ_r v rs v)
                            )%I (vmprop_zero v Φ_t Φ_r trans rxs)
                           with "[PC R0 R1 R2 pgt_acc $tx mem_instr rxs_global VMProp VMProp_v
                           trans_hpool_global tran_pgt_transferred retri Hacc_mem mem_rest_a transferred_only_v rx_state_v]"); iFrameAutoSolve.
                {
                    iSplitL "VMProp_v". iNext. iExact "VMProp_v".
                    iSplitL "VMProp". iNext. iExact "VMProp".
                    iSplitL "R2".
                    {
                      iNext. iIntros "((PC & instr & pgt_acc & _ & R0 & R1) & (trans_hpool_global & trans_transferred & rxs_global
                      & rx_state_v) & vmprop0)".
                      rewrite vmprop_unknown_eq.
                      iSplitR "PC instr pgt_acc".
                      iExists trans, rxs.
                      iFrame "trans_hpool_global trans_transferred rx_state_v rxs_global vmprop0".
                      iSplitL "R0". iExists _. iSplitL. iExact "R0". done.
                      iSplitL "R1". iExists _. iSplitL. iExact "R1". done.
                      iSplitL "R2". iExists _. iExact "R2". done.
                      iCombine "PC instr pgt_acc" as "R". iExact "R".
                    }
                    {
                      iNext. iFrame "trans_hpool_global rxs_global rx_state_v".
                      rewrite /big_sepSS_singleton.
                      iApply (big_sepS_delete _ _ i).
                      apply elem_of_set_of_vmids.
                      iFrame "transferred_only_v".
                      rewrite 2?HΦt. 2: left;done. 2: right;done.
                      rewrite /slice_transfer_all.
                      (* TODO *)
                    }

                }

                (* organizing big_sepSS: merging i and splitting v *)
                (* iDestruct (transferred_only_equiv with "[$tran_pgt_transferred $retri $mem_transferred]") as "transferred_only";eauto. *)
                (* rewrite /big_sepSS_except. *)
                (* assert (Hvmids_eq: set_of_vmids = (set_of_vmids ∖ {[i]} ∪ {[i]})). *)
                (* { *)
                (*   pose proof (elem_of_set_of_vmids i). *)
                (*   rewrite union_comm_L. *)
                (*   apply union_difference_L. *)
                (*   set_solver + H. *)
                (* } *)
                  admit.
                }
                {
                  admit.
                }
                }
                }
                }
              }
            { admit. }
            { admit. }
            { admit. }
            { admit. }
            { admit. }
            { admit. }
            { admit. }
            { (* SEND *)
              admit. }
            { (* WAIT *)
              admit. }
            { admit. }
          }
          admit.
        }
      }
      admit.
    }
    admit.
  Admitted.

End fundamental_prim.
