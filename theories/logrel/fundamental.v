From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang trans_extra.
From HypVeri.algebra Require Import base pagetable mem trans.
From HypVeri.rules Require Import rules_base nop mov yield mem_share mem_retrieve(* ldr str halt fail add sub mult cmp *).
From HypVeri.logrel Require Import logrel logrel_extra.
From HypVeri.logrel Require Import ftlr_nop ftlr_yield ftlr_share ftlr_retrieve.
From HypVeri Require Import proofmode stdpp_extra.
Import uPred.

Section fundamental.
  Context `{hypconst:HypervisorConstants}.
  Context `{hypparams:!HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.


  Lemma ftlr (i:VMID)  :
  ∀ p_tx p_rx ps_acc trans, interp_access i p_tx p_rx ps_acc trans ⊢ interp_execute i.
  Proof.
    rewrite /interp_access /=.
    iIntros (????) "((%regs & %Htotal_regs & regs) & (tx & [% mem_tx]) & pgt_acc & %Hsubset_mb & pgt_owned & tran_pgt_owned &
                            mem_owned & VMProp) %Hneq_0 VMProp_holds".
    iDestruct (VMProp_holds_agree i with "[$VMProp_holds $VMProp]") as "[Hres propi]".
    iEval (rewrite later_exist) in "Hres".
    iDestruct "Hres" as (ps_na') "Hres".
    iEval (rewrite later_exist) in "Hres".
    iDestruct "Hres" as (ps_acc') "Hres".
    iEval (rewrite later_exist) in "Hres".
    iDestruct "Hres" as (trans') "Hres".
    iEval (rewrite later_exist) in "Hres".
    iDestruct "Hres" as (rx_state') "Hres".
    iEval (rewrite 15!later_sep) in "Hres".
    iDestruct "Hres" as  "( >pgt_acc' & >LB & >%Hdisj_na & >trans_hpool_global & >tran_pgt_transferred &
                         >retri & >mem_transferred &  >R0z & >R1z & >rx_state & >rx & >[% mem_rx] &
                          Himp_tran_pgt & Himp_pgt & Himp_mem & prop0)".
    iDestruct (access_agree_eq with "[$pgt_acc $pgt_acc']") as %->.
    iDestruct (later_wand with "Himp_tran_pgt") as "Himp_tran_pgt".
    iDestruct ("Himp_tran_pgt" with "tran_pgt_owned") as ">tran_pgt_owned".
    iDestruct (later_wand with "Himp_pgt") as "Himp_pgt".
    iDestruct ("Himp_pgt" with "pgt_owned") as ">pgt_owned".
    iDestruct (later_wand with "Himp_mem") as "Himp_mem".
    iDestruct ("Himp_mem" with "[$mem_owned $mem_transferred]") as  (?) ">mem".

    set ps_mem_in_trans := (pages_in_trans (trans_memory_in_trans i trans')).
    iDestruct (memory_pages_disj_singleton with "[$mem $mem_rx]") as %Hnin_rx.
    iDestruct (memory_pages_disj_singleton with "[$mem $mem_tx]") as %Hnin_tx.

    (* merge all memory pages together *)
    iAssert (∃ mem, memory_pages (ps_acc' ∪ ps_mem_in_trans) mem)%I
      with "[mem mem_rx mem_tx]" as "mem".
    {
      iExists (mem_all ∪ mem_rx ∪ mem_tx).
      assert (pages_in_trans (trans_memory_in_trans i trans') ## {[p_tx]}) as Hdisj_ps_tx'.
      set_solver.
      assert (pages_in_trans (trans_memory_in_trans i trans') ## {[p_rx]}) as Hdisj_ps_rx'.
      set_solver.
      assert (ps_acc' ∖ {[p_rx; p_tx]} ∪ ps_mem_in_trans ∪ {[p_rx; p_tx]} =
                (ps_acc' ∪ ps_mem_in_trans)) as <-.
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
      iExists mem_all, (mem_rx ∪ mem_tx).
      iFrame "mem".
      rewrite memory_pages_split_union.
      iSplit.
      iExists mem_rx, mem_tx.
      rewrite 2!memory_pages_singleton.
      iFrame "mem_rx mem_tx".
      done.
      iPureIntro.
      rewrite map_union_assoc //.
      set_solver + Hneq_tx_rx.
    }
    iDestruct "tx" as "[tx pgt_tx]".
    clear mem_rx mem_tx mem_all; subst ps_mem_in_trans.

    iLöb as "IH" forall (regs ps_acc' trans' rx_state' Htotal_regs Hsubset_mb Hdisj_na Hnin_rx Hnin_tx).

    set ps_mem_in_trans := (pages_in_trans (trans_memory_in_trans i trans')).
    (* split memory pages into [mem_acc] and [mem_rest] *)
    iDestruct (memory_pages_split_diff' _ ps_acc' with "mem") as "[mem_rest mem_acc]".
    set_solver.
    iDestruct (memory_pages_split_singleton' p_tx ps_acc' with "mem_acc") as "[mem_acc_tx mem_tx]". set_solver + Hsubset_mb.
    iDestruct ("mem_acc_tx") as (mem_acc_tx) "mem_acc_tx".

    pose proof (Htotal_regs PC) as Hlookup_PC.
    destruct Hlookup_PC as [ai Hlookup_PC].
    (* sswp *)
    rewrite ->wp_sswp.
    destruct (decide ((tpa ai) ∈ ps_acc')) as [Hin_ps_acc | Hnotin_ps_acc].
    { (* i has access *)
      destruct (decide (tpa ai = p_tx)) as [Heq_ptx | Hneq_ptx].
      { (*invalid instruction location *)
        iDestruct (reg_big_sepM_split i Hlookup_PC with "[$regs]") as "[PC _]".
        iApply (invalid_pc_in_tx _ ai with "[PC tx]"); iFrameAutoSolve.
        iNext.
        iIntros "? _".
        by iApply wp_terminated.
      }
      assert (Hin_ps_acc_tx': (tpa ai) ∈ ps_acc' ∖ {[p_tx]}).
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
          iApply (ftlr_nop with "IH regs tx pgt_tx pgt_acc pgt_acc' LB trans_hpool_global tran_pgt_transferred retri R0z R1z
                 rx_state rx prop0 propi tran_pgt_owned pgt_owned mem_rest mem_acc_tx mem_tx");iFrameAutoSolve.
          all:done.
        }
        { (* mov *) admit. }
        { (* ldr *) admit. }
        { (* str *) admit. }
        { (* cmp: two cases *) admit. }
        { (* add *) admit. }
        { (* sub *) admit. }
        { (* mult *) admit. }
        { (* bne *) admit. }
        { (* br *) admit. }
        { (* halt *) admit. }
        { (* fail *) admit. }
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
            destruct (hvc_f).
            { (*RUN*) admit. }
            { (*Yield*)
              iApply (ftlr_yield with "IH regs tx pgt_tx pgt_acc pgt_acc' LB trans_hpool_global tran_pgt_transferred retri R0z R1z
                 rx_state rx prop0 propi tran_pgt_owned pgt_owned mem_rest mem_acc_tx mem_tx");iFrameAutoSolve.
              all:done.
            }
            { (*Share *)
              iApply (ftlr_share with "IH regs tx pgt_tx pgt_acc pgt_acc' LB trans_hpool_global tran_pgt_transferred retri R0z R1z
                 rx_state rx prop0 propi tran_pgt_owned pgt_owned mem_rest mem_acc_tx mem_tx");iFrameAutoSolve.
              all:done.
            }
            { (*Lend*) admit. }
            { (*Donate*) admit. }
            { (*WIP: Retrieve*)
              iApply (ftlr_retrieve with "IH regs tx pgt_tx pgt_acc pgt_acc' LB trans_hpool_global tran_pgt_transferred retri R0z R1z
                 rx_state rx prop0 propi tran_pgt_owned pgt_owned mem_rest mem_acc_tx mem_tx");iFrameAutoSolve.
              all:done.
            }
            { (*Relinquish*) admit. }
            { (*Reclaim*) admit. }
            { (*Send TODO*) admit. }
            { (*Wait*) admit. }
            { (*Poll*) admit. }
          }
          { (* decode_hvc_func r0 = None *) admit. }
        }
      }
      { (*invalid instruction *)
        iDestruct (reg_big_sepM_split i Hlookup_PC with "[$regs]") as "[PC _]".
        (* we don't update pagetable *)
        (* getting mem *)
        iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "mem_acc_tx")
          as "[mem_instr Hacc_mem_acc]".
        iApply (not_valid_instr _ ai instr with "[PC pgt_acc tx mem_instr]"); iFrameAutoSolve.
        iNext.
        iIntros "? _".
        by iApply wp_terminated.
      }
    }
    { (* i doesn't have access *)
      iDestruct (reg_big_sepM_split i Hlookup_PC with "[$regs]") as "[PC _]".
      iApply (invalid_pc_not_accessible with "[PC pgt_acc pgt_acc']"); iFrameAutoSolve.
      exact.
      {
        iNext.
        rewrite (access_split (q:=1)).
        iFrame.
      }
      iNext;simpl.
      iIntros "? _".
      by iApply wp_terminated.
    }
    Admitted.

End fundamental.
