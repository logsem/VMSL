From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang trans_extra.
From HypVeri.algebra Require Import base pagetable mem trans mailbox.
From HypVeri.rules Require Import rules_base halt fail.
From HypVeri.logrel Require Import logrel logrel_extra.
From HypVeri.logrel Require Import ftlr_nop ftlr_mov ftlr_ldr ftlr_str ftlr_cmp ftlr_add ftlr_sub ftlr_mult ftlr_bne ftlr_br
  ftlr_run ftlr_yield ftlr_share ftlr_lend ftlr_donate ftlr_retrieve ftlr_relinquish ftlr_reclaim.
  (* ftlr_msg_send ftlr_msg_wait ftlr_msg_poll ftlr_invalid_hvc. *)
From HypVeri Require Import proofmode.
Import uPred.

Section fundamental.
  Context `{hypconst:HypervisorConstants}.
  Context `{hypparams:!HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.

  Lemma ftlr (i:VMID) :
  ∀ p_tx p_rx ps_acc trans, interp_access i p_tx p_rx ps_acc trans ⊢ interp_execute i.
  Proof.
    rewrite /interp_access /=.
    iIntros (????) "((%regs & %Htotal_regs & regs) & (tx & [% mem_tx]) & rx & pgt_acc & %Hsubset_mb & %Hsubset_acc & pgt_owned & tran_pgt_owned &
                           retri_owned & mem_owned & VMProp) %Hneq_0 VMProp_holds".
    iDestruct (VMProp_holds_agree i with "[$VMProp_holds $VMProp]") as "[Hres propi]".
    iEval (rewrite vmprop_unknown_eq) in "Hres".
    iEval (rewrite later_exist) in "Hres". iDestruct "Hres" as (trans') "Hres".
    iEval (rewrite later_exist) in "Hres". iDestruct "Hres" as (rxs') "Hres".
    iEval (rewrite 11!later_sep) in "Hres".
    iDestruct "Hres" as "(>%trans_rel & >trans_hpool_global & >tran_pgt_transferred &
                         >retri & >mem_transferred & >R0z & >R1z & >R2z & (>rx_state & >[% [rx' [% mem_rx]]]) & >other_rx & >%Htotal_rxs & prop0)".
    erewrite (trans_rel_secondary_retrieved_lending_memory_pages);eauto.
    erewrite (trans_rel_secondary_currently_accessible_memory_pages);eauto.
    erewrite (trans_rel_secondary_currently_accessible_memory_pages) in Hsubset_acc;eauto.
    iDestruct (trans_rel_secondary_transaction_pagetable_entries_owned with "tran_pgt_owned") as "tran_pgt_owned";eauto.
    iDestruct (trans_rel_secondary_retrieved_transaction_owned with "retri_owned") as "retri_owned";eauto.
    iDestruct (get_trans_ps_disj with "[$trans_hpool_global]" ) as %Htrans_disj.
    iDestruct (memory_pages_oea_transferred with "[$mem_owned $mem_transferred]") as (?) "mem";eauto.
    clear Htrans_disj trans_rel.
    set ps_mem_in_trans := (accessible_in_trans_memory_pages i trans').

    iAssert (⌜p_rx0 = p_rx⌝%I) with "[rx rx']" as %Hrx_eq.
    {
      iDestruct "rx" as "[rx ?]".
      iApply (rx_agree with "rx' rx").
    }
    subst p_rx0. iClear "rx'".

    iDestruct (memory_pages_disj_singleton with "[$mem $mem_rx]") as %Hnin_rx.
    iDestruct (memory_pages_disj_singleton with "[$mem $mem_tx]") as %Hnin_tx.
    (* merge all memory pages together *)
    iAssert (∃ mem, memory_pages (ps_acc ∪ ps_mem_in_trans) mem)%I
      with "[mem mem_rx mem_tx]" as "mem".
    {
      iExists (mem_all ∪ mem_rx ∪ mem_tx).
      assert (accessible_in_trans_memory_pages i trans' ## {[p_tx]}) as Hdisj_ps_tx' by set_solver.
      assert (accessible_in_trans_memory_pages i trans' ## {[p_rx]}) as Hdisj_ps_rx' by set_solver.
      assert (ps_acc ∖ {[p_rx; p_tx]} ∪ ps_mem_in_trans ∪ {[p_rx; p_tx]} = (ps_acc ∪ ps_mem_in_trans)) as <-.
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
    iDestruct "tx" as "[tx pgt_tx]".
    clear mem_rx mem_tx mem_all; subst ps_mem_in_trans.
    iAssert (∃ (P: iProp Σ), VMProp i P (1%Qp))%I with "[propi]" as "propi".
    iExists _;done.
    iCombine "R0z R1z R2z prop0 propi" as "Yielding".

    iLöb as "IH" forall (regs ps_acc trans' rxs' Htotal_rxs Htotal_regs Hsubset_mb Hsubset_acc Hnin_rx Hnin_tx).

  (* "regs" : [∗ map] r↦w ∈ regs, r @@ i ->r w *)
  (* "tx" : TX@i:=p_tx *)
  (* "pgt_tx" : p_tx -@O> - ∗ p_tx -@E> true *)
  (* "rx" : rx_page i p_rx *)
  (* "pgt_acc" : i -@A> ps_acc *)
  (* "pgt_owned" : pagetable_entries_excl_owned i (ps_acc ∖ {[p_rx; p_tx]} ∖ currently_accessible_in_trans_memory_pages i trans') *)
  (* "trans_hpool_global" : transaction_hpool_global_transferred trans' *)
  (* "tran_pgt_transferred" : transaction_pagetable_entries_transferred i trans' *)
  (* "retri" : retrievable_transaction_transferred i trans' *)
  (* "rx_state" : rx_state_get i rxs' *)
  (* "other_rx" : rx_states_global (delete i rxs') *)
  (* "tran_pgt_owned" : transaction_pagetable_entries_owned i trans' *)
  (* "retri_owned" : retrieved_transaction_owned i trans' *)
  (* "mem" : ∃ mem : lang.mem, memory_pages (ps_acc ∪ accessible_in_trans_memory_pages i trans') mem *)
  (* "Yielding" : (∃ r0 : Addr, R0 @@ V0 ->r r0 ∗ ⌜decode_hvc_func r0 = Some Run⌝) ∗ *)
  (*              (∃ r1 : Addr, R1 @@ V0 ->r r1 ∗ ⌜decode_vmid r1 = Some i⌝) ∗ (∃ r2 : Addr, R2 @@ V0 ->r r2) ∗ *)
  (*              ▷ VMProp V0 (vmprop_zero i trans' rxs') (1 / 2) ∗ VMProp i (vmprop_unknown i) 1 *)

    set ps_mem_in_trans := (accessible_in_trans_memory_pages i trans').

    (* split memory pages into [mem_acc] and [mem_rest] *)
    iDestruct (memory_pages_split_diff' _ ps_acc with "mem") as "[mem_rest mem_acc]". set_solver.
    iDestruct (memory_pages_split_singleton' p_tx ps_acc with "mem_acc") as "[mem_acc_tx mem_tx]". set_solver + Hsubset_mb.
    iDestruct ("mem_acc_tx") as (mem_acc_tx) "mem_acc_tx".

    pose proof (Htotal_regs PC) as Hlookup_PC.
    destruct Hlookup_PC as [ai Hlookup_PC].
    (* sswp *)
    rewrite ->wp_sswp.
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
                 rx_state rx other_rx tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx Yielding");iFrameAutoSolve.
          all:done.
        }
        {
          iApply (ftlr_mov with "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri
                 rx_state rx other_rx tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx Yielding");iFrameAutoSolve.
          all:done.
        }
        {
          iApply (ftlr_ldr with "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri
                 rx_state rx other_rx tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx Yielding");iFrameAutoSolve.
          all:done.
        }
        {
          iApply (ftlr_str with "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri
                 rx_state rx other_rx tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx Yielding");iFrameAutoSolve.
          all:done.
        }
        {
          iApply (ftlr_cmp with "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri
                 rx_state rx other_rx tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx Yielding");iFrameAutoSolve.
          all:done.
        }
        {
          iApply (ftlr_add with "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri
                 rx_state rx other_rx tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx Yielding");iFrameAutoSolve.
          all:done.
        }
        {
          iApply (ftlr_sub with "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri
                 rx_state rx other_rx tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx Yielding");iFrameAutoSolve.
          all:done.
        }
        {
          iApply (ftlr_mult with "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri
                 rx_state rx other_rx tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx Yielding");iFrameAutoSolve.
          all:done.
        }
        {
          iApply (ftlr_bne with "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri
                 rx_state rx other_rx tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx Yielding");iFrameAutoSolve.
          all:done.
        }
        {
          iApply (ftlr_br with "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri
                 rx_state rx other_rx tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx Yielding");iFrameAutoSolve.
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
        { (* hvc *)
          pose proof (Htotal_regs R0) as [r0 Hlookup_reg_R0].
          destruct (decode_hvc_func r0) as [hvc_f |] eqn:Hdecode_hvc .
          {
            iAssert (⌜p_tx ≠ p_rx⌝)%I as "%Hneq_mb".
            {
              iDestruct "rx" as "[_ [_ excl_rx]]".
              iDestruct "pgt_tx" as "[_ excl_tx]".
              iApply (excl_ne with "[$ excl_tx $ excl_rx]").
            }
            assert (∀ (trans0 trans'0 : gmap Addr transaction) (rxs rxs'0 : gmap VMID (option (Addr * VMID))),
                      delete i rxs = delete i rxs'0
                      → except i trans0 = except i trans'0
                      → (∀ (x:VMID), x ≠ i -> trans_rel_secondary x trans0 trans'0)
                      → ((∃ r1 : Addr, R0 @@ V0 ->r r1 ∗ ⌜decode_hvc_func r1 = Some Run⌝) ∗ (∃ r1 : Addr, R1 @@ V0 ->r r1 ∗ ⌜decode_vmid r1 = Some i⌝) ∗
                          (∃ r2 : Addr, R2 @@ V0 ->r r2) ∗ ▷ VMProp V0 (vmprop_zero i trans0 rxs) (1 / 2) ∗ (∃ P, VMProp i P 1)
                        ⊣⊢ (∃ r1 : Addr, R0 @@ V0 ->r r1 ∗ ⌜decode_hvc_func r1 = Some Run⌝) ∗ (∃ r1 : Addr, R1 @@ V0 ->r r1 ∗ ⌜decode_vmid r1 = Some i⌝) ∗
                             (∃ r2 : Addr, R2 @@ V0 ->r r2) ∗ ▷ VMProp V0 (vmprop_zero i trans'0 rxs'0) (1 / 2) ∗ ∃ P, VMProp i P 1)%I).
            {
              intros.
              do 4 f_equiv.
              rewrite (vmprop_zero_equiv_trans trans0 trans'0);last auto.
              rewrite (vmprop_zero_equiv_rxs rxs rxs'0);last auto.
              done. done.
            }
            destruct (hvc_f).
            { (*RUN*)
              iApply (ftlr_run with "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri
                 rx_state rx other_rx tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx Yielding");iFrameAutoSolve.
              all:done.
            }
            { (*Yield*)
              iApply (ftlr_yield with "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri
                 rx_state rx other_rx tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx Yielding");iFrameAutoSolve.
              all:done.
            }
            { (*Share*)
              iApply (ftlr_share with "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri
                 rx_state rx other_rx tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx");iFrameAutoSolve.
              all:done.
            }
            { (*Lend*)
              iApply (ftlr_lend with "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri
                 rx_state rx other_rx tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx");iFrameAutoSolve.
              all:done.
            }
            { (*Donate*)
              iApply (ftlr_donate with "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri
                 rx_state rx other_rx tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx");iFrameAutoSolve.
              all:done.
            }
            { (*Retrieve*)
              iApply (ftlr_retrieve with "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri
                 rx_state rx other_rx tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx");iFrameAutoSolve.
              all:done.
            }
            { (*Relinquish*)
              iApply (ftlr_relinquish with "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri
                 rx_state rx other_rx tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx");iFrameAutoSolve.
              all:done.
            }
            { (*Reclaim*)
              iApply (ftlr_reclaim with "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri
                 rx_state rx other_rx tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx");iFrameAutoSolve.
              all:done.
            }
            { (*Send*)
              iApply (ftlr_msg_send with "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri
                 rx_state rx other_rx tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx");iFrameAutoSolve.
              all:done.
            }
            { (*Wait*)
              iApply (ftlr_msg_wait with "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri
                 rx_state rx other_rx tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx");iFrameAutoSolve.
              all:done.
            }
            { (*Poll*)
              iApply (ftlr_msg_poll with "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri
                 rx_state rx other_rx tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx");iFrameAutoSolve.
              all:done.
            }
          }
          { (* decode_hvc_func r0 = None *)
            iApply (ftlr_invalid_hvc with "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri
                 rx_state rx other_rx tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx");iFrameAutoSolve.
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

End fundamental.
