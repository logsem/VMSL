From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang trans_extra.
From HypVeri.algebra Require Import base pagetable mem trans mailbox.
From HypVeri.rules Require Import rules_base halt fail run.
From HypVeri.logrel Require Import logrel_prim_extra.
From HypVeri.logrel Require Import ftlr_nop ftlr_mov ftlr_ldr ftlr_str ftlr_cmp ftlr_add ftlr_sub ftlr_mult ftlr_bne ftlr_br.
From HypVeri.logrel Require Import ftlr_run_prim ftlr_yield_prim ftlr_share. (*ftlr_retrieve ftlr_relinquish ftlr_reclaim ftlr_donate ftlr_lend *)
(*  ftlr_msg_wait_prim ftlr_msg_send_prim ftlr_msg_poll ftlr_invalid_hvc. *)
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

    iDestruct (later_intro with "VMProps") as "VMProps". rewrite big_sepS_later.
    iDestruct (later_intro with "transferred_except") as "transferred_except".
    iDestruct (later_intro with "rxs_transferred") as "rxs_transferred".

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
            assert (∀ (trans0 trans' : gmap Addr transaction) (rxs0 rxs' : gmap VMID (option (Addr * VMID))),
                      delete V0 rxs0 = delete V0 rxs'
                      → except V0 trans0 = except V0 trans'
                      -> (∀ (x:VMID), x ≠ V0 -> trans_rel_secondary x trans0 trans')
                      → (∃ P0 : iProp Σ, VMProp i P0 1) ∗ ([∗ set] y ∈ (set_of_vmids ∖ {[i]}), ▷ VMProp (y:VMID) (vmprop_unknown y Φ_t Φ_r trans0) (1 / 2)) ∗
                          ▷ (big_sepSS_except set_of_vmids i (Φ_t trans0) ∗ rx_states_transferred Φ_r (delete i rxs0)) ⊣⊢ (∃ P0 : iProp Σ, VMProp i P0 1) ∗
                      ([∗ set] y ∈ (set_of_vmids ∖ {[i]}), ▷ VMProp (y:VMID) (vmprop_unknown y Φ_t Φ_r trans') (1 / 2)) ∗
                      ▷ (big_sepSS_except set_of_vmids i (Φ_t trans') ∗ rx_states_transferred Φ_r (delete i rxs'))).
            {
              intros ? ? ? ? ? ? Hrel.
              do 2 f_equiv.
              iApply big_sepS_proper.
              intros.
              f_equiv.
              rewrite /VMProp /=.
              do 6 f_equiv.
              rewrite vmprop_unknown_eq. rewrite vmprop_unknown_eq.
              do 6 f_equiv.
              {
                specialize (Hrel x).
                feed specialize Hrel. set_solver + H1.
                rewrite /trans_rel_secondary.
                rewrite /trans_rel_secondary in Hrel.
                destruct Hrel as [-> ->].
                done.
              }
              f_equiv. f_equiv.
              rewrite /big_sepSS_except /big_sepSS.
              iApply big_sepS_proper.
              intros.
              iApply big_sepS_proper.
              intros.
              rewrite slice_trans_valid. reflexivity.
              rewrite /trans_preserve_slice.
              rewrite /except in H0.
              pose proof (map_filter_subseteq_ext (λ kv : Addr * (VMID * VMID * gset PID * transaction_type * bool), kv.2.1.1.1.1 = x ∧ kv.2.1.1.1.2 = x0)
                (λ kv : Addr * transaction, ¬ (kv.2.1.1.1.1 = V0 ∨ kv.2.1.1.1.2 = V0))).
              pose proof (H3 trans0) as [_ Hsub1].
              feed specialize Hsub1. simpl.
              intros ? ? ? [? ?].
              rewrite H5 H6.
              intros [H'|H']; [rewrite H' in H1 | rewrite H' in H2]. set_solver + H1. set_solver + H2.
              pose proof (H3 trans') as [_ Hsub2].
              feed specialize Hsub2. simpl.
              intros ? ? ? [? ?].
              rewrite H5 H6.
              intros [H'|H']; [rewrite H' in H1 | rewrite H' in H2]. set_solver + H1. set_solver + H2.
              apply map_eq.
              intros. rewrite map_subseteq_spec in Hsub1. rewrite map_subseteq_spec in Hsub2.
              destruct (filter (λ kv : Addr * (VMID * VMID * gset PID * transaction_type * bool), kv.2.1.1.1.1 = x ∧ kv.2.1.1.1.2 = x0) trans0 !! i0) eqn:Heqn'.
              specialize (Hsub1 i0 t Heqn').
              destruct (filter (λ kv : Addr * (VMID * VMID * gset PID * transaction_type * bool), kv.2.1.1.1.1 = x ∧ kv.2.1.1.1.2 = x0) trans' !! i0) eqn:Heqn''.
              specialize (Hsub2 i0 t0 Heqn'').
              rewrite H0 Hsub2 in Hsub1. done.
              rewrite H0 in Hsub1.
              rewrite map_filter_lookup_Some in Hsub1. destruct Hsub1.
              rewrite map_filter_lookup_Some in Heqn'.
              rewrite map_filter_lookup_None in Heqn''.
              destruct Heqn''. rewrite H4 // in H6. specialize (H6 t H4). destruct Heqn'. done.
              destruct (filter (λ kv : Addr * (VMID * VMID * gset PID * transaction_type * bool), kv.2.1.1.1.1 = x ∧ kv.2.1.1.1.2 = x0) trans' !! i0) eqn:Heqn''.
              specialize (Hsub2 i0 t Heqn'').
              rewrite -H0 in Hsub2.
              rewrite map_filter_lookup_Some in Hsub2. destruct Hsub2.
              rewrite map_filter_lookup_Some in Heqn''.
              rewrite map_filter_lookup_None in Heqn'.
              destruct Heqn'. rewrite H4 // in H6. specialize (H6 t H4). destruct Heqn''. done.
              done.
              f_equiv.
              done.
            }
            destruct (hvc_f).
            { (* RUN *)
              iApply (ftlr_run_prim with "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri
                 rx_state rx rxs_global tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx Running");iFrameAutoSolve.
              all:done.
            }
            {
              iApply (ftlr_yield_prim with "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri
                 rx_state rx rxs_global tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx Running");iFrameAutoSolve.
              all:done.
            }
            { (*Share*)
              iApply (ftlr_share with "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri
                 rx_state rx rxs_global tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx");iFrameAutoSolve.
              all:done.
            }
            { (*Lend*)
              iApply (ftlr_lend with "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri
                 rx_state rx rxs_global tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx");iFrameAutoSolve.
              all:done.
            }
            { (*Donate*)
              iApply (ftlr_donate with "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri
                 rx_state rx rxs_global tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx");iFrameAutoSolve.
              all:done.
            }
            { (*Retrieve*)
              iApply (ftlr_retrieve with "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri
                 rx_state rx rxs_global tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx");iFrameAutoSolve.
              all:done.
            }
            { (*Relinquish*)
              iApply (ftlr_relinquish with "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri
                 rx_state rx rxs_global tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx");iFrameAutoSolve.
              all:done.
            }
            { (*Reclaim*)
              iApply (ftlr_reclaim with "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri
                 rx_state rx rxs_global tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx");iFrameAutoSolve.
              all:done.
            }
            { (*Send*)
              iApply (ftlr_msg_send_prim with "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri
                 rx_state rx rxs_global tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx Running");iFrameAutoSolve.
              all:done.
            }
            { (*Wait*)
              iApply (ftlr_msg_wait_prim with "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri
                 rx_state rx rxs_global tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx");iFrameAutoSolve.
              all:done.
            }
            { (*Poll*)
              iApply (ftlr_msg_poll with "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri
                 rx_state rx rxs_global tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx");iFrameAutoSolve.
              all:done.
            }
          }
          { (* decode_hvc_func r0 = None *)
            iApply (ftlr_invalid_hvc with "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri
                 rx_state rx rxs_global tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx");iFrameAutoSolve.
            all:done.
          }
        }
      }
      { (*invalid instruction *)
        iDestruct (reg_big_sepM_split i Hlookup_PC with "[$regs]") as "[PC _]".
        (* we don't update pagetable *)
        (* getting mem *)
        iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "mem_acc_tx")
          as "[mem_instr Hacc_mem_acc]".
        iApply (not_valid_instr _ ai instr with "[PC pgt_acc tx mem_instr]"); iFrameAutoSolve.
        iNext. iIntros "? _".
        by iApply wp_terminated.
      }
    }
    { (* i doesn't have access *)
      iDestruct (reg_big_sepM_split i Hlookup_PC with "[$regs]") as "[PC _]".
      iApply (invalid_pc_not_accessible with "[PC pgt_acc]"); iFrameAutoSolve.
      iNext;simpl. iIntros "? _".
      by iApply wp_terminated.
    }
  Qed.

End fundamental_prim.
