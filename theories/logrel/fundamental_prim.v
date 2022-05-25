From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang trans_extra.
From HypVeri.algebra Require Import base pagetable mem trans.
From HypVeri.rules Require Import rules_base mov yield ldr halt fail add sub mult cmp br bne str run.
From HypVeri.logrel Require Import logrel_prim_extra.
(* From HypVeri.logrel Require Import ftlr_nop ftlr_run ftlr_yield ftlr_share ftlr_retrieve ftlr_relinquish ftlr_reclaim ftlr_donate ftlr_lend *)
(*   ftlr_msg_send ftlr_msg_wait ftlr_msg_poll ftlr_invalid_hvc. *)
From HypVeri Require Import proofmode.
Import uPred.

Section fundamental_prim.
  Context `{hypconst:HypervisorConstants}.
  Context `{hypparams:!HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.

  Lemma ftlr_p Φ `(!SliceWf Φ):
  ∀ p_tx p_rx ps_acc trans, interp_access_prim Φ p_tx p_rx ps_acc trans ⊢ interp_execute_prim.
  Proof.
    rewrite /interp_access_prim /=.
    iIntros (????) "(%HΦ & (%regs & %Htotal_regs & regs) & (tx & [% mem_tx]) & pgt_acc & %Hsubset_mb & %Hsubset_acc & pgt_owned & tran_pgt_owned &
                           retri_owned & mem_owned & VMProp & rx_state & rx & [% mem_rx] & trans_hpool_global & other_rx & transferred & VMProps)".

    iDestruct (big_sepSS_difference_singleton _ V0 with "transferred") as "[transferred_except transferred_only]";eauto.
    apply elem_of_set_of_vmids.
    iDestruct (get_trans_ps_disj with "trans_hpool_global") as %Htrans_disj.
    iDestruct (get_trans_neq with "trans_hpool_global") as %Htrans_neq.
    iDestruct (transferred_only_equiv with "transferred_only") as "(tran_pgt_transferred & retri & mem_transferred)";eauto.

    iDestruct (memory_pages_oea_transferred with "[$mem_owned $mem_transferred]") as (?) "mem";eauto.
    clear Htrans_disj Htrans_neq.

    set i := V0.
    set ps_mem_in_trans := (accessible_in_trans_memory_pages i trans).

    iDestruct (memory_pages_disj_singleton with "[$mem $mem_rx]") as %Hnin_rx.
    iDestruct (memory_pages_disj_singleton with "[$mem $mem_tx]") as %Hnin_tx.
    (* merge all memory pages together *)
    iDestruct (memory_pages_merge_mb with "[$mem mem_rx mem_tx]") as "mem";auto.
    iCombine "mem_tx mem_rx" as "mem". iExact "mem".
    iDestruct "tx" as "[tx pgt_tx]".
    clear mem_rx mem_tx mem_all; subst ps_mem_in_trans.

    iLöb as "IH" forall (regs ps_acc trans Htotal_regs Hsubset_mb Hsubset_acc Hnin_rx Hnin_tx).
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
        { admit. }
        { admit. }
        { admit. }
        { admit. }
        { admit. }
        { admit. }
        { admit. }
        { admit. }
        { admit. }
        { admit. }
        { admit. }
        { admit. }
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
              admit. }
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
