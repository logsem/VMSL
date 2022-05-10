From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang trans_extra.
From HypVeri.algebra Require Import base pagetable mem trans.
From HypVeri.rules Require Import rules_base mov yield ldr halt fail add sub mult cmp br bne str run.
From HypVeri.logrel Require Import logrel logrel_extra.
From HypVeri.logrel Require Import ftlr_nop ftlr_run.
(* From HypVeri.logrel Require Import  ftlr_yield ftlr_share ftlr_retrieve ftlr_msg_send *)
(*      ftlr_msg_wait ftlr_msg_poll ftlr_relinquish ftlr_reclaim ftlr_donate ftlr_lend ftlr_invalid_hvc. *)
From HypVeri Require Import proofmode stdpp_extra.
Import uPred.

Section fundamental.
  Context `{hypconst:HypervisorConstants}.
  Context `{hypparams:!HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.

  Lemma ftlr (i:VMID) :
  ∀ p_tx p_rx ps_acc trans, interp_access i p_tx p_rx ps_acc trans ⊢ interp_execute i.
  Proof.
    rewrite /interp_access /=.
    iIntros (????) "((%regs & %Htotal_regs & regs) & (tx & [% mem_tx]) & pgt_acc & %Hsubset_mb & pgt_owned & tran_pgt_owned &
                           retri_owned & mem_owned & VMProp) %Hneq_0 VMProp_holds".
    iDestruct (VMProp_holds_agree i with "[$VMProp_holds $VMProp]") as "[Hres propi]".
    iEval (setoid_rewrite vmprop_unknown_eq) in "Hres".
    iEval (rewrite later_exist) in "Hres". iDestruct "Hres" as (trans') "Hres".
    iEval (rewrite later_exist) in "Hres". iDestruct "Hres" as (rx_state') "Hres".
    iEval (rewrite 11!later_sep) in "Hres".
    iDestruct "Hres" as "(>trans_hpool_global & >tran_pgt_transferred &
                         >retri & >mem_transferred & >R0z & >R1z & >R2z & >rx_state & >rx & >[% mem_rx] & >other_rx & prop0)".

    iDestruct (derive_trans_rel_secondary with "[$trans_hpool_global $retri $tran_pgt_owned $retri_owned]") as "%trans_rel".
    erewrite (trans_rel_secondary_retrieved_lending_memory_page);eauto.
    erewrite (trans_rel_secondary_currently_accessible_memory_pages);eauto.
    iDestruct (trans_rel_secondary_transaction_pagetable_entries_owned with "tran_pgt_owned") as "tran_pgt_owned";eauto.
    iDestruct (trans_rel_secondary_retrieved_transaction_owned with "retri_owned") as "retri_owned";eauto.
    iAssert (⌜trans_ps_disj trans'⌝)%I as %Hdisj. { iDestruct "trans_hpool_global" as "[% (_ & _ & $ & _)]". }
    iDestruct (memory_pages_oea_transferred with "[$mem_owned $mem_transferred]") as (?) "mem";eauto.
    clear Hdisj trans_rel.
    (* not sure if we need trans_rel later *)

    set ps_mem_in_trans := (accessible_in_trans_memory_pages i trans').

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

    iLöb as "IH" forall (regs ps_acc trans' rx_state' Htotal_regs Hsubset_mb Hnin_rx Hnin_tx).

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
          iApply (ftlr_nop with "IH regs tx pgt_tx pgt_acc pgt_owned trans_hpool_global tran_pgt_transferred retri R0z R1z R2z
                 rx_state rx other_rx prop0 propi tran_pgt_owned retri_owned mem_rest mem_acc_tx mem_tx"); iFrameAutoSolve.
          all:done.
        }
        { (* mov *)
          destruct src as [imm | srcreg].
          { (* mov imm *)
            destruct dst.
            {
              apply decode_instruction_valid in Heqn.
              inversion Heqn.
              unfold reg_valid_cond in *.
              exfalso.
              naive_solver.
            }
            {
              apply decode_instruction_valid in Heqn.
              inversion Heqn.
              unfold reg_valid_cond in *.
              exfalso.
              naive_solver.
            }
            {
              pose proof (Htotal_regs (R n fin)) as [w Hlookup_R].
              (* getting regs *)
              iDestruct ((reg_big_sepM_split_upd2 i Hlookup_PC Hlookup_R)
                          with "[$regs]") as "(PC & R & Hacc_regs)"; [done | done |].
              (* getting mem *)
              iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "[mem_acc_tx]")
                as "[mem_instr Hacc_mem_acc_tx]"; first done.
              iApply (mov_word ai (w1 := instr) (w3 := w) imm (R n fin) with "[PC R pgt_acc tx mem_instr]"); iFrameAutoSolve.
              iNext.
              iIntros "(PC & mem_instr & pgt_acc & tx & R) _".
              iDestruct ("Hacc_regs" $! (ai ^+ 1)%f imm with "[PC R]") as "[%regs' [%Htotal_regs' regs'']]"; iFrameAutoSolve.
              iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
              (* split mem*)
              iApply ("IH" $! _ _ ps_acc trans trans' _ Htotal_regs' Hsubset_mb Hdisj_na Hnin_rx Hnin_tx with "regs'' tx pgt_tx pgt_acc pgt_acc'
                       LB trans_hpool_global tran_pgt_transferred retri R0z R1z R2z rx_state rx other_rx prop0 propi
                           tran_pgt_owned pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx]").
              {
                iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx $mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
                iExists mem_acc_tx;by iFrame "mem_acc_tx".
                iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
                set_solver +.
              }
            }
          }
          { (* mov reg *)
            destruct dst.
            {
              apply decode_instruction_valid in Heqn.
              inversion Heqn.
              unfold reg_valid_cond in *.
              exfalso.
              naive_solver.
            }
            {
              apply decode_instruction_valid in Heqn.
              inversion Heqn.
              unfold reg_valid_cond in *.
              exfalso.
              naive_solver.
            }
            destruct srcreg.
            {
              apply decode_instruction_valid in Heqn.
              inversion Heqn.
              unfold reg_valid_cond in *.
              exfalso.
              naive_solver.
            }
            {
              apply decode_instruction_valid in Heqn.
              inversion Heqn.
              unfold reg_valid_cond in *.
              exfalso.
              naive_solver.
            }
            {
              pose proof (Htotal_regs (R n fin)) as [w Hlookup_R].
              pose proof (Htotal_regs (R n0 fin0)) as [w' Hlookup_R0].
              (* getting regs *)
              iDestruct ((reg_big_sepM_split_upd3 i Hlookup_PC Hlookup_R Hlookup_R0)
                          with "[$regs]") as "(PC & R & R0 & Hacc_regs)"; [done | done | | done |].
              {
                apply decode_instruction_valid in Heqn.
                inversion Heqn.
                assumption.
              }
              (* getting mem *)
              iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "[mem_acc_tx]")
                as "[mem_instr Hacc_mem_acc_tx]"; first done.
              iApply (mov_reg ai w (R n fin) (R n0 fin0) with "[PC R R0 pgt_acc tx mem_instr]"); iFrameAutoSolve.
              iNext.
              iIntros "(PC & mem_instr & pgt_acc & tx & R & R0) _".
              iDestruct ("Hacc_regs" $! (ai ^+ 1)%f w' w' with "[PC R R0]") as "[%regs' [%Htotal_regs' regs'']]"; iFrameAutoSolve.
              iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
              iApply ("IH" $! _ _ ps_acc _ trans' _ Htotal_regs' Hsubset_mb Hdisj_na Hnin_rx Hnin_tx with "regs'' tx pgt_tx pgt_acc pgt_acc'
                       LB trans_hpool_global tran_pgt_transferred retri R0z R1z R2z rx_state rx other_rx prop0 propi
                           tran_pgt_owned pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx]").
              {
                iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx $mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
                iExists mem_acc_tx;by iFrame "mem_acc_tx".
                iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
                set_solver +.
              }
            }
          }
        }
        { (* ldr *)
          pose proof Heqn as Hdecode.
          apply decode_instruction_valid in Heqn.
          inversion Heqn as [| | ? ? Hvalid_dst Hvalid_src Hvalid_neq | | | | | | | | | ].
          subst dst0 src0.
          unfold reg_valid_cond in Hvalid_dst, Hvalid_src.
          pose proof (Htotal_regs src) as [a_src Hlookup_src].
          pose proof (Htotal_regs dst) as [w_dst Hlookup_dst].
          (* getting registers *)
          iDestruct ((reg_big_sepM_split_upd3 i Hlookup_PC Hlookup_src Hlookup_dst)
                      with "[$regs]") as "(PC & r_src & r_dst & Hacc_regs)"; [by destruct_and ! | by destruct_and ! | done | done |].
          (* case analysis on src  *)
          destruct (decide ((tpa a_src) ∈ ps_acc)) as [Hin' | Hin''].
          { (* has access to the page, more cases.. *)
            destruct (decide((tpa a_src) = p_tx)).
            { (* trying to read from tx page, fail *)
              (* getting mem *)
              iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "[mem_acc_tx]")
                as "[mem_instr Hacc_mem_acc_tx]"; first done.
              iApply (ldr_access_tx (w3 := w_dst) ai a_src dst src with "[PC pgt_acc tx mem_instr r_src r_dst]"); iFrameAutoSolve.
              iNext.
              iIntros "(tx & PC & a_instr & r_src & acc & r_dst) _".
              by iApply wp_terminated.
            }
            { (* normal case *)
              destruct (decide (a_src = ai)) as [|Hneq''].
              { (* exact same addr *)
                iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "[mem_acc_tx]")
                  as "[mem_instr Hacc_mem_acc_tx]"; first done.
                iApply (ldr_same_addr (q := (1 / 2)) (s := ps_acc) ai a_src dst src with "[PC mem_instr r_src r_dst tx pgt_acc']"); iFrameAutoSolve.
                { symmetry;done. }
                iNext.
                iIntros "(PC & mem_instr & r_src & r_dst & pgt_acc' & tx) _".
                iDestruct ("Hacc_regs" with "[$PC $r_src $r_dst]") as (regs') "[%Htotal_regs' regs]";iFrame.
                iDestruct ("Hacc_mem_acc_tx" with "mem_instr") as "mem_acc_tx".
                iApply ("IH" $! _ _ ps_acc _ trans' _ Htotal_regs' Hsubset_mb Hdisj_na Hnin_rx Hnin_tx with "regs tx pgt_tx pgt_acc pgt_acc'
                       LB trans_hpool_global tran_pgt_transferred retri R0z R1z R2z rx_state rx other_rx prop0 propi
                           tran_pgt_owned pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx]").
                {
                  iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx $mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
                  iExists mem_acc_tx;by iFrame "mem_acc_tx".
                  iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
                  set_solver +.
                }
              }
              { (* different addresses *)
                destruct (decide ((tpa a_src) = (tpa ai))) as [Heqn'|].
                { (* in same page *)
                  pose proof Hin_ps_acc as Hin_ps_acc.
                  rewrite <-Heqn' in Hin_ps_acc.
                  assert (tpa a_src ∈ ps_acc ∖ {[p_tx]}) as Hin_ps_acc'.
                  set_solver + Hin_ps_acc n.
                  pose proof (elem_of_memory_pages_lookup _ _ _ Hin_ps_acc' Hdom_mem_acc_tx) as [w_src Hlookup_a_src].
                  iDestruct (mem_big_sepM_split2 mem_acc_tx Hneq'' Hlookup_a_src Hlookup_mem_ai with "[$mem_acc_tx]")
                    as "[a_src [a_instr Hacc_mem_acc_tx]]".
                  iApply (ldr_same_page (s := ps_acc) ai a_src dst src with "[PC a_instr a_src r_src r_dst tx pgt_acc']"); iFrameAutoSolve.
                  { done. }
                  { symmetry;done. }
                  iNext.
                  iIntros "(PC & mem_instr & r_src & a_src & r_dst & pgt_acc' & tx) _".
                  iDestruct ("Hacc_regs" with "[$PC $r_src $r_dst]") as (regs') "[%Htotal_regs' regs]";iFrame.
                  iDestruct ("Hacc_mem_acc_tx" with "[a_src mem_instr]") as "mem_acc_tx"; iFrame.
                  iApply ("IH" $! _ _ ps_acc _ trans' _ Htotal_regs' Hsubset_mb Hdisj_na Hnin_rx Hnin_tx with "regs tx pgt_tx pgt_acc pgt_acc'
                       LB trans_hpool_global tran_pgt_transferred retri R0z R1z R2z rx_state rx other_rx prop0 propi
                           tran_pgt_owned pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx]").
                  {
                    iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx $mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
                    iExists mem_acc_tx;by iFrame "mem_acc_tx".
                    iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
                    set_solver +.
                  }
                }
                { (* in difference pages *)
                  (* getting mem *)
                  assert (tpa a_src ∈ ps_acc ∖ {[p_tx]}) as Hin_ps_acc.
                  set_solver + Hin' n.
                  pose proof (elem_of_memory_pages_lookup _ _ _ Hin_ps_acc Hdom_mem_acc_tx) as [w_src Hlookup_a_src].
                  iDestruct (mem_big_sepM_split2 mem_acc_tx Hneq'' Hlookup_a_src Hlookup_mem_ai with "[$mem_acc_tx]")
                    as "[a_src [mem_instr Hacc_mem_acc_tx]]".
                  iApply (ldr (s := ps_acc) ai a_src dst src with "[PC mem_instr a_src r_src r_dst tx pgt_acc']"); iFrameAutoSolve.
                  { set_solver. }
                  iNext.
                  iIntros "(PC & mem_instr & r_src & a_src & r_dst & pgt_acc' & tx) _".
                  iDestruct ("Hacc_regs" with "[$PC $r_src $r_dst]") as (regs') "[%Htotal_regs' regs]";iFrame.
                  iDestruct ("Hacc_mem_acc_tx" with "[a_src mem_instr]") as "mem_acc_tx"; iFrame.
                  iApply ("IH" $! _ _ ps_acc _ trans' _ Htotal_regs' Hsubset_mb Hdisj_na Hnin_rx Hnin_tx with "regs tx pgt_tx pgt_acc pgt_acc'
                       LB trans_hpool_global tran_pgt_transferred retri R0z R1z R2z rx_state rx other_rx prop0 propi
                           tran_pgt_owned pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx]").
                  {
                    iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx $mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
                    iExists mem_acc_tx;by iFrame "mem_acc_tx".
                    iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
                    set_solver +.
                  }
                }
              }
            }
          }
          { (* no access to the page, apply ldr_error *)
            (* getting mem *)
            (* we don't update memory *)
            iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "[mem_acc_tx]")
            as "[mem_instr Hacc_mem_acc_tx]"; first done.
            iDestruct (access_split with "[pgt_acc pgt_acc']") as "pgt_acc"; iFrame.
            iApply (ldr_no_access (s := ps_acc) ai a_src dst src with "[PC mem_instr r_src r_dst tx pgt_acc]"); iFrameAutoSolve.
            iNext.
            iIntros "(PC & mem_instr & r_src & pgt_acc & r_dst & tx) _".
            by iApply wp_terminated.
          }
        }
        { (* str *)
          pose proof Heqn as Hdecode.
          apply decode_instruction_valid in Heqn.
          inversion Heqn as [| | | ? ? Hvalid_dst Hvalid_src Hvalid_neq | | | | | | | | ].
          subst dst0 src0.
          unfold reg_valid_cond in Hvalid_dst, Hvalid_src.
          pose proof (Htotal_regs src) as [a_src Hlookup_src].
          pose proof (Htotal_regs dst) as [w_dst Hlookup_dst].
          (* getting registers *)
          iDestruct ((reg_big_sepM_split_upd3 i Hlookup_PC Hlookup_src Hlookup_dst)
                      with "[$regs]") as "(PC & r_src & r_dst & Hacc_regs)"; [by destruct_and ! | by destruct_and ! | done | done |].
          (* case analysis on src  *)
          destruct (decide ((tpa w_dst) ∈ ps_acc)) as [Hin' | Hin''].
          { (* has access to the page, more cases.. *)
            destruct (decide((tpa w_dst) = p_rx)).
            { (* trying to write to rx page, fail *)
              (* getting mem *)
              iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "[mem_acc_tx]")
                as "[mem_instr Hacc_mem_acc_tx]"; first done.
              iDestruct "rx" as "(rx & rx_own & rx_excl)".
              iApply (str_access_rx (p := p_rx) ai w_dst src dst with "[PC pgt_acc tx rx mem_instr r_src r_dst]"); iFrameAutoSolve.
              iNext.
              iIntros "(PC & mem_instr & r_dst & acc & r_src & tx & rx) _".
              by iApply wp_terminated.
            }
            { (* normal case *)
              destruct (decide (w_dst = ai)) as [|Hneq''].
              { (* exact same addr *)
                iDestruct (mem_big_sepM_split_upd mem_acc_tx Hlookup_mem_ai with "[mem_acc_tx]")
                  as "[mem_instr Hacc_mem_acc_tx]"; first done.
                iDestruct "rx" as "(rx & rx_own & rx_excl)".
                iApply (str_same_addr (p := p_rx) (q := (1 / 2)) (s := ps_acc) ai w_dst src dst with "[PC mem_instr r_src r_dst tx rx pgt_acc']"); iFrameAutoSolve.
                { symmetry;done. }
                iNext.
                iIntros "(PC & mem_instr & r_dst & r_src & pgt_acc' & tx & rx) _".
                iDestruct ("Hacc_regs" with "[$PC $r_src $r_dst]") as (regs') "[%Htotal_regs' regs]";iFrame.
                iDestruct ("Hacc_mem_acc_tx" with "mem_instr") as "mem_acc_tx".
                iCombine "rx rx_own rx_excl" as "rx".
                iApply ("IH" $! _ _ ps_acc _ trans' _ Htotal_regs' Hsubset_mb Hdisj_na Hnin_rx Hnin_tx with "regs tx pgt_tx pgt_acc pgt_acc'
                       LB trans_hpool_global tran_pgt_transferred retri R0z R1z R2z rx_state rx other_rx prop0 propi
                           tran_pgt_owned pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx]").
                {
                  iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx $mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
                  iExists (<[ai:=a_src]> mem_acc_tx);iFrame "mem_acc_tx". iPureIntro. rewrite dom_insert_lookup_L. set_solver + Hdom_mem_acc_tx. eauto.
                  iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
                  set_solver +.
                }
              }
              { (* different addresses *)
                destruct (decide ((tpa w_dst)=(tpa ai))) as [Heqn'|].
                { (* in same page *)
                  pose proof Hin_ps_acc_tx as Hin_ps_acc_tx'.
                  rewrite <-Heqn' in Hin_ps_acc_tx'.
                  pose proof (elem_of_memory_pages_lookup _ _ _ Hin_ps_acc_tx' Hdom_mem_acc_tx) as [w_src Hlookup_a_dst].
                  iDestruct (mem_big_sepM_split_upd2 mem_acc_tx Hneq'' Hlookup_a_dst Hlookup_mem_ai with "[$mem_acc_tx]")
                    as "[a_dst [mem_instr Hacc_mem_acc_tx]]".
                  iDestruct "rx" as "(rx & rx_own & rx_excl)".
                  iApply (str_same_page (s := ps_acc) (p := p_rx) ai w_dst src dst with "[PC mem_instr rx a_dst r_src r_dst tx pgt_acc']"); iFrameAutoSolve.
                  { done. }
                  iNext.
                  iIntros "(PC & mem_instr & r_dst & a_dst & r_src & pgt_acc' & tx & rx) _".
                  iDestruct ("Hacc_regs" with "[$PC $r_src $r_dst]") as (regs') "[%Htotal_regs' regs]";iFrame.
                  iDestruct ("Hacc_mem_acc_tx" with "[a_dst mem_instr]") as "mem_acc_tx"; iFrame.
                  iCombine "rx rx_own rx_excl" as "rx".
                  iApply ("IH" $! _ _ ps_acc _ trans' _ Htotal_regs' Hsubset_mb Hdisj_na Hnin_rx Hnin_tx with "regs tx pgt_tx pgt_acc pgt_acc'
                       LB trans_hpool_global tran_pgt_transferred retri R0z R1z R2z rx_state rx other_rx prop0 propi
                           tran_pgt_owned pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx]").
                  {
                    iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx $mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
                    iExists (<[w_dst:=a_src]> (<[ai:=instr]>mem_acc_tx)); iFrame "mem_acc_tx".
                    iPureIntro. rewrite !dom_insert_lookup_L;eauto. rewrite lookup_insert_is_Some. right;done.
                    iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
                    set_solver +.
                  }
                }
                { (* in difference pages *)
                  (* getting mem *)
                  destruct (decide (tpa w_dst = p_tx)).
                  {
                    iDestruct ("mem_tx") as "[%mem_tx [%Hdom_mem_tx mem_tx]]".
                    rewrite -set_of_addr_singleton in Hdom_mem_tx.
                    assert ( (tpa w_dst) ∈ ({[ p_tx ]}: gset _) ). set_solver + e.
                    epose proof (elem_of_memory_pages_lookup _ w_dst _ H Hdom_mem_tx) as [w_src Hlookup_a_src];auto.
                    iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "[$mem_acc_tx]") as "[mem_instr Hacc_mem_acc_tx]".
                    iDestruct (mem_big_sepM_split_upd mem_tx Hlookup_a_src with "[$mem_tx]") as "[a_src Hacc_mem_tx]".
                    iDestruct "rx" as "(rx & rx_own & rx_excl)".
                    iApply (str (s := ps_acc) (p := p_rx) ai w_dst src dst with "[PC mem_instr a_src r_src r_dst rx tx pgt_acc']"); iFrameAutoSolve.
                    { set_solver. }
                    iNext.
                    iIntros "(PC & mem_instr & r_dst & a_dst & r_src & pgt_acc' & tx & rx) _".
                    iCombine "rx rx_own rx_excl" as "rx".
                    iDestruct ("Hacc_regs" with "[$PC $r_src $r_dst]") as (regs') "[%Htotal_regs' regs]";iFrame.
                    iDestruct ("Hacc_mem_acc_tx" with "mem_instr") as "mem_acc_tx".
                    iDestruct ("Hacc_mem_tx" with "a_dst") as "mem_tx".
                    iApply ("IH" $! _ _ ps_acc _ trans' _ Htotal_regs' Hsubset_mb Hdisj_na Hnin_rx Hnin_tx with "regs tx pgt_tx pgt_acc pgt_acc'
                       LB trans_hpool_global tran_pgt_transferred retri R0z R1z R2z rx_state rx other_rx prop0 propi
                           tran_pgt_owned pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx]").
                    {
                      iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
                      iSplitL "mem_acc_tx".
                      iExists mem_acc_tx; iFrame "mem_acc_tx". done.
                      iExists (<[w_dst := a_src]> mem_tx). iFrame "mem_tx".
                      iPureIntro. rewrite !dom_insert_lookup_L;eauto. rewrite -set_of_addr_singleton //.
                      iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
                      set_solver +.
                    }
                  }
                  {
                    assert (tpa w_dst ∈ ps_acc ∖ {[p_tx]}). set_solver + n1 Hin'.
                    pose proof (elem_of_memory_pages_lookup _ _ _ H Hdom_mem_acc_tx) as [w_src Hlookup_a_src].
                    iDestruct (mem_big_sepM_split_upd2 mem_acc_tx Hneq'' Hlookup_a_src Hlookup_mem_ai with "[$mem_acc_tx]")
                      as "[a_src [mem_instr Hacc_mem_acc_tx]]".
                    iDestruct "rx" as "(rx & rx_own & rx_excl)".
                    iApply (str (s := ps_acc) (p := p_rx) ai w_dst src dst with "[PC mem_instr a_src r_src r_dst rx tx pgt_acc']"); iFrameAutoSolve.
                    { set_solver. }
                    iNext.
                    iIntros "(PC & mem_instr & r_dst & a_dst & r_src & pgt_acc' & tx & rx) _".
                    iCombine "rx rx_own rx_excl" as "rx".
                    iDestruct ("Hacc_regs" with "[$PC $r_src $r_dst]") as (regs') "[%Htotal_regs' regs]";iFrame.
                    iDestruct ("Hacc_mem_acc_tx" with "[a_dst mem_instr]") as "mem_acc_tx"; iFrame.

                    iApply ("IH" $! _ _ ps_acc _ trans' _ Htotal_regs' Hsubset_mb Hdisj_na Hnin_rx Hnin_tx with "regs tx pgt_tx pgt_acc pgt_acc'
                       LB trans_hpool_global tran_pgt_transferred retri R0z R1z R2z rx_state rx other_rx prop0 propi
                           tran_pgt_owned pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx]").
                    {
                      iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx $mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
                      iExists (<[w_dst:=a_src]> (<[ai:=instr]>mem_acc_tx)); iFrame "mem_acc_tx".
                      iPureIntro. rewrite !dom_insert_lookup_L;eauto. rewrite lookup_insert_is_Some. right;done.
                      iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
                      set_solver +.
                    }
                  }
                }
              }
            }
          }
          { (* no access to the page, apply str_error *)
            (* getting mem *)
            (* we don't update memory *)
            iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "[$mem_acc_tx]")
            as "[mem_instr Hacc_mem_acc_tx]".
            iDestruct (access_split with "[pgt_acc pgt_acc']") as "pgt_acc"; iFrame.
            iApply (str_no_access (s := ps_acc) ai w_dst src dst with "[PC mem_instr r_src r_dst tx pgt_acc]"); iFrameAutoSolve.
            iNext.
            iIntros "(PC & mem_instr & r_dst & pgt_acc & tx & r_src) _".
            by iApply wp_terminated.
          }
        }
        { (* cmp: two cases *)
          destruct arg2 as [arg2 | arg2].
          {
            (* cmp imm *)
            destruct arg1 as [| | n nle].
            {
              apply decode_instruction_valid in Heqn.
              inversion Heqn.
              unfold reg_valid_cond in *.
              exfalso.
              naive_solver.
            }
            {
              apply decode_instruction_valid in Heqn.
              inversion Heqn.
              unfold reg_valid_cond in *.
              exfalso.
              naive_solver.
            }
            pose proof (Htotal_regs (R n nle)) as [a_arg Hlookup_arg].
            pose proof (Htotal_regs NZ) as [a_nz Hlookup_nz].
            (* getting registers *)
            iDestruct ((reg_big_sepM_split_upd3 i Hlookup_PC Hlookup_arg Hlookup_nz)
                        with "[$regs]") as "(PC & r_arg & r_nz & Hacc_regs)"; [done | done | done | done |].
            (* getting mem *)
            iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "[$mem_acc_tx]")
              as "[mem_instr Hacc_mem_acc_tx]".
            iApply (cmp_word (w2 := arg2) (s := ps_acc) (p := p_tx) _ (R n nle) with "[PC tx pgt_acc' mem_instr r_arg r_nz]"); iFrameAutoSolve.
            iNext.
            iIntros "(PC & mem_instr & r_arg & pgt_acc' & r_nz & tx) _".
            iDestruct ("Hacc_regs" with "[$PC $r_arg $r_nz]") as (regs') "[%Htotal_regs' regs]";iFrame.
            iDestruct ("Hacc_mem_acc_tx" with "mem_instr") as "mem_acc_tx".
            iApply ("IH" $! _ _ ps_acc _ trans' _ Htotal_regs' Hsubset_mb Hdisj_na Hnin_rx Hnin_tx with "regs tx pgt_tx pgt_acc pgt_acc'
                       LB trans_hpool_global tran_pgt_transferred retri R0z R1z R2z rx_state rx other_rx prop0 propi
                           tran_pgt_owned pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx]").
            {
              iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx $mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
              iExists mem_acc_tx;by iFrame "mem_acc_tx".
              iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
              set_solver +.
            }
          }
          {
            (* cmp reg *)
            destruct arg1 as [| | n nle].
            {
              apply decode_instruction_valid in Heqn.
              inversion Heqn.
              unfold reg_valid_cond in *.
              exfalso.
              naive_solver.
            }
            {
              apply decode_instruction_valid in Heqn.
              inversion Heqn.
              unfold reg_valid_cond in *.
              exfalso.
              naive_solver.
            }
            destruct arg2 as [| | n' nle'].
            {
              apply decode_instruction_valid in Heqn.
              inversion Heqn.
              unfold reg_valid_cond in *.
              exfalso.
              naive_solver.
            }
            {
              apply decode_instruction_valid in Heqn.
              inversion Heqn.
              unfold reg_valid_cond in *.
              exfalso.
              naive_solver.
            }
            pose proof (Htotal_regs (R n nle)) as [a_arg1 Hlookup_arg1].
            pose proof (Htotal_regs (R n' nle')) as [a_arg2 Hlookup_arg2].
            pose proof (Htotal_regs NZ) as [a_nz Hlookup_nz].
            (* getting registers *)
            iDestruct ((reg_big_sepM_split_upd4 i Hlookup_PC Hlookup_arg1 Hlookup_arg2 Hlookup_nz)
                        with "[$regs]") as "(PC & r_arg1 & r_arg2 & r_nz & Hacc_regs)"; [done | done | | done | done | done | done |].
            apply decode_instruction_valid in Heqn.
            inversion Heqn.
            assumption.
            (* getting mem *)
            iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "[$mem_acc_tx]")
              as "[mem_instr Hacc_mem_acc_tx]".
            iApply (cmp_reg (s := ps_acc) (p := p_tx)  _ (R n nle) (R n' nle') with "[PC tx pgt_acc' mem_instr r_arg1 r_arg2 r_nz]"); iFrameAutoSolve.
            iNext.
            iIntros "(PC & mem_instr & r_arg1 & r_arg2 & pgt_acc' & r_nz & tx) _".
            iDestruct ("Hacc_regs" with "[$PC $r_arg1 $r_arg2 $r_nz]") as (regs') "[%Htotal_regs' regs]";iFrame.
            iDestruct ("Hacc_mem_acc_tx" with "[mem_instr]") as "mem_acc_tx"; iFrame.
            iApply ("IH" $! _ _ ps_acc _ trans' _ Htotal_regs' Hsubset_mb Hdisj_na Hnin_rx Hnin_tx with "regs tx pgt_tx pgt_acc pgt_acc'
                       LB trans_hpool_global tran_pgt_transferred retri R0z R1z R2z rx_state rx other_rx prop0 propi
                           tran_pgt_owned pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx]").
            {
              iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx $mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
              iExists mem_acc_tx;by iFrame "mem_acc_tx".
              iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
              set_solver +.
            }
          }
        }
        { (* add *)
          destruct op1 as [| | n nle].
          {
            apply decode_instruction_valid in Heqn.
            inversion Heqn.
            unfold reg_valid_cond in *.
            exfalso.
            naive_solver.
          }
          {
            apply decode_instruction_valid in Heqn.
            inversion Heqn.
            unfold reg_valid_cond in *.
            exfalso.
            naive_solver.
          }
          destruct op2 as [| | n' nle'].
          {
            apply decode_instruction_valid in Heqn.
            inversion Heqn.
            unfold reg_valid_cond in *.
            exfalso.
            naive_solver.
          }
          {
            apply decode_instruction_valid in Heqn.
            inversion Heqn.
            unfold reg_valid_cond in *.
            exfalso.
            naive_solver.
          }
          pose proof (Htotal_regs (R n nle)) as [a_arg1 Hlookup_arg1].
          pose proof (Htotal_regs (R n' nle')) as [a_arg2 Hlookup_arg2].
          (* getting registers *)
          iDestruct ((reg_big_sepM_split_upd3 i Hlookup_PC Hlookup_arg1 Hlookup_arg2)
                      with "[$regs]") as "(PC & r_arg1 & r_arg2 & Hacc_regs)"; [done | done | | done |].
          apply decode_instruction_valid in Heqn.
          inversion Heqn.
          done.
          (* getting mem *)
          iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "[$mem_acc_tx]")
            as "[mem_instr Hacc_mem_acc_tx]".
          iApply (add (p := p_tx)  _ (R n nle) (R n' nle') with "[PC tx pgt_acc' mem_instr r_arg1 r_arg2]"); iFrameAutoSolve.
          iNext.
          iIntros "(PC & mem_instr & r_arg1 & r_arg2 & pgt_acc' & tx) _".
          iDestruct ("Hacc_regs" with "[$PC $r_arg1 $r_arg2]") as (regs') "[%Htotal_regs' regs]";iFrame.
          iDestruct ("Hacc_mem_acc_tx" with "mem_instr") as "mem_acc_tx".
          iApply ("IH" $! _ _ ps_acc _ trans' _ Htotal_regs' Hsubset_mb Hdisj_na Hnin_rx Hnin_tx with "regs tx pgt_tx pgt_acc pgt_acc'
                       LB trans_hpool_global tran_pgt_transferred retri R0z R1z R2z rx_state rx other_rx prop0 propi
                           tran_pgt_owned pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx]").
          {
            iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx $mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
            iExists mem_acc_tx;by iFrame "mem_acc_tx".
            iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
            set_solver +.
          }
        }
        { (* sub *)
          destruct op1 as [| | n nle].
          {
            apply decode_instruction_valid in Heqn.
            inversion Heqn.
            unfold reg_valid_cond in *.
            exfalso.
            naive_solver.
          }
          {
            apply decode_instruction_valid in Heqn.
            inversion Heqn.
            unfold reg_valid_cond in *.
            exfalso.
            naive_solver.
          }
          destruct op2 as [| | n' nle'].
          {
            apply decode_instruction_valid in Heqn.
            inversion Heqn.
            unfold reg_valid_cond in *.
            exfalso.
            naive_solver.
          }
          {
            apply decode_instruction_valid in Heqn.
            inversion Heqn.
            unfold reg_valid_cond in *.
            exfalso.
            naive_solver.
          }
          pose proof (Htotal_regs (R n nle)) as [a_arg1 Hlookup_arg1].
          pose proof (Htotal_regs (R n' nle')) as [a_arg2 Hlookup_arg2].
          (* getting registers *)
          iDestruct ((reg_big_sepM_split_upd3 i Hlookup_PC Hlookup_arg1 Hlookup_arg2)
                      with "[$regs]") as "(PC & r_arg1 & r_arg2 & Hacc_regs)"; [done | done | | done |].
          apply decode_instruction_valid in Heqn.
          inversion Heqn.
          done.
          (* getting mem *)
          iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "[$mem_acc_tx]")
            as "[mem_instr Hacc_mem_acc_tx]".
          iApply (sub (p := p_tx)  _ (R n nle) (R n' nle') with "[PC tx pgt_acc' mem_instr r_arg1 r_arg2]"); iFrameAutoSolve.
          iNext.
          iIntros "(PC & mem_instr & r_arg1 & r_arg2 & pgt_acc' & tx) _".
          iDestruct ("Hacc_regs" with "[$PC $r_arg1 $r_arg2]") as (regs') "[%Htotal_regs' regs]";iFrame.
          iDestruct ("Hacc_mem_acc_tx" with "mem_instr") as "mem_acc_tx".
          iApply ("IH" $! _ _ ps_acc _ trans' _ Htotal_regs' Hsubset_mb Hdisj_na Hnin_rx Hnin_tx with "regs tx pgt_tx pgt_acc pgt_acc'
                       LB trans_hpool_global tran_pgt_transferred retri R0z R1z R2z rx_state rx other_rx prop0 propi
                           tran_pgt_owned pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx]").
          {
            iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx $mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
            iExists mem_acc_tx;by iFrame "mem_acc_tx".
            iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
            set_solver +.
          }
        }
        { (* mult *)
          destruct op1 as [| | n nle].
          {
            apply decode_instruction_valid in Heqn.
            inversion Heqn.
            unfold reg_valid_cond in *.
            exfalso.
            naive_solver.
          }
          {
            apply decode_instruction_valid in Heqn.
            inversion Heqn.
            unfold reg_valid_cond in *.
            exfalso.
            naive_solver.
          }
          pose proof (Htotal_regs (R n nle)) as [a_arg1 Hlookup_arg1].
          (* getting registers *)
          iDestruct ((reg_big_sepM_split_upd2 i Hlookup_PC Hlookup_arg1)
                      with "[$regs]") as "(PC & r_arg1 & Hacc_regs)"; [done | done |].
          (* getting mem *)
          iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "[$mem_acc_tx]")
            as "[mem_instr Hacc_mem_acc_tx]".
          iApply (mult_word _ op2 (R n nle) with "[PC tx pgt_acc' mem_instr r_arg1]"); iFrameAutoSolve.
          iNext.
          iIntros "(PC & mem_instr & pgt_acc' & r_arg1 & tx) _".
          iDestruct ("Hacc_regs" with "[$PC $r_arg1]") as (regs') "[%Htotal_regs' regs]";iFrame.
          iDestruct ("Hacc_mem_acc_tx" with "mem_instr") as "mem_acc_tx".
          iApply ("IH" $! _ _ ps_acc _ trans' _ Htotal_regs' Hsubset_mb Hdisj_na Hnin_rx Hnin_tx with "regs tx pgt_tx pgt_acc pgt_acc'
                       LB trans_hpool_global tran_pgt_transferred retri R0z R1z R2z rx_state rx other_rx prop0 propi
                           tran_pgt_owned pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx]").
          {
            iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx $mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
            iExists mem_acc_tx;by iFrame "mem_acc_tx".
            iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
            set_solver +.
          }
        }
        { (* bne *)
          destruct arg as [| | n nle].
          {
            apply decode_instruction_valid in Heqn.
            inversion Heqn.
            unfold reg_valid_cond in *.
            exfalso.
            naive_solver.
          }
          {
            apply decode_instruction_valid in Heqn.
            inversion Heqn.
            unfold reg_valid_cond in *.
            exfalso.
            naive_solver.
          }
          pose proof (Htotal_regs (R n nle)) as [a_arg1 Hlookup_arg1].
          pose proof (Htotal_regs NZ) as [a_nz Hlookup_nz].
          (* getting registers *)
          iDestruct ((reg_big_sepM_split_upd3 i Hlookup_PC Hlookup_arg1 Hlookup_nz)
                      with "[$regs]") as "(PC & r_arg1 & r_nz & Hacc_regs)"; [done | done | done | done |].
          (* getting mem *)
          iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "[$mem_acc_tx]")
            as "[mem_instr Hacc_mem_acc_tx]".
          iApply (bne _ (R n nle) with "[PC tx pgt_acc' mem_instr r_arg1 r_nz]"); iFrameAutoSolve.
          iNext.
          iIntros "(PC & mem_instr & r_arg1 & pgt_acc' & r_nz & tx) _".
          iDestruct ("Hacc_regs" with "[$PC $r_arg1 $r_nz]") as (regs') "[%Htotal_regs' regs]";iFrame.
          iDestruct ("Hacc_mem_acc_tx" with "mem_instr") as "mem_acc_tx".
          iApply ("IH" $! _ _ ps_acc _ trans' _ Htotal_regs' Hsubset_mb Hdisj_na Hnin_rx Hnin_tx with "regs tx pgt_tx pgt_acc pgt_acc'
                       LB trans_hpool_global tran_pgt_transferred retri R0z R1z R2z rx_state rx other_rx prop0 propi
                           tran_pgt_owned pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx]").
          {
            iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx $mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
            iExists mem_acc_tx;by iFrame "mem_acc_tx".
            iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
            set_solver +.
          }
        }
        { (* br *)
          destruct arg as [| | n nle].
          {
            apply decode_instruction_valid in Heqn.
            inversion Heqn.
            unfold reg_valid_cond in *.
            exfalso.
            naive_solver.
          }
          {
            apply decode_instruction_valid in Heqn.
            inversion Heqn.
            unfold reg_valid_cond in *.
            exfalso.
            naive_solver.
          }
          pose proof (Htotal_regs (R n nle)) as [a_arg1 Hlookup_arg1].
          (* getting registers *)
          iDestruct ((reg_big_sepM_split_upd2 i Hlookup_PC Hlookup_arg1)
                      with "[$regs]") as "(PC & r_arg1 & Hacc_regs)"; [done | done |].
          (* getting mem *)
          iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "[$mem_acc_tx]")
            as "[mem_instr Hacc_mem_acc_tx]".
          iApply (br _ (R n nle) with "[PC tx pgt_acc' mem_instr r_arg1]"); iFrameAutoSolve.
          iNext.
          iIntros "(PC & (mem_instr & r_arg1) & pgt_acc' & tx) _".
          iDestruct ("Hacc_regs" with "[$PC $r_arg1]") as (regs') "[%Htotal_regs' regs]";iFrame.
          iDestruct ("Hacc_mem_acc_tx" with "mem_instr") as "mem_acc_tx".
          iApply ("IH" $! _ _ ps_acc _ trans' _ Htotal_regs' Hsubset_mb Hdisj_na Hnin_rx Hnin_tx with "regs tx pgt_tx pgt_acc pgt_acc'
                       LB trans_hpool_global tran_pgt_transferred retri R0z R1z R2z rx_state rx other_rx prop0 propi
                           tran_pgt_owned pgt_owned retri_owned [mem_rest mem_acc_tx mem_tx]").
          {
            iDestruct (memory_pages_split_singleton' p_tx ps_acc with "[mem_acc_tx $mem_tx]") as "mem_acc". set_solver + Hsubset_mb.
            iExists mem_acc_tx;by iFrame "mem_acc_tx".
            iApply (memory_pages_split_diff' _ ps_acc with "[$mem_rest $mem_acc]").
            set_solver +.
          }
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
          iNext.
          iIntros "? _".
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
          iNext.
          iIntros "? _".
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
            destruct (hvc_f).
            { (*RUN*)
              iApply (ftlr_run with "IH regs tx pgt_tx pgt_acc pgt_acc' LB trans_hpool_global tran_pgt_transferred retri R0z R1z R2z
                 rx_state rx other_rx prop0 propi tran_pgt_owned pgt_owned retri_owned mem_rest mem_acc_tx mem_tx");iFrameAutoSolve.
              all:done.
            }
            { (*Yield*)
              iApply (ftlr_yield with "IH regs tx pgt_tx pgt_acc pgt_acc' LB trans_hpool_global tran_pgt_transferred retri R0z R1z R2z
                 rx_state rx other_rx prop0 propi tran_pgt_owned pgt_owned retri_owned mem_rest mem_acc_tx mem_tx");iFrameAutoSolve.
              all:done.
            }
            { (*Share*)
              iApply (ftlr_share with "IH regs tx pgt_tx pgt_acc pgt_acc' LB trans_hpool_global tran_pgt_transferred retri R0z R1z R2z
                 rx_state rx other_rx prop0 propi tran_pgt_owned pgt_owned retri_owned mem_rest mem_acc_tx mem_tx");iFrameAutoSolve.
              all:done.
            }
            { (*Lend*)
              iApply (ftlr_lend with "IH regs tx pgt_tx pgt_acc pgt_acc' LB trans_hpool_global tran_pgt_transferred retri R0z R1z R2z
                 rx_state rx other_rx prop0 propi tran_pgt_owned pgt_owned retri_owned mem_rest mem_acc_tx mem_tx");iFrameAutoSolve.
              all:done.
            }
            { (*Donate*)
              iApply (ftlr_donate with "IH regs tx pgt_tx pgt_acc pgt_acc' LB trans_hpool_global tran_pgt_transferred retri R0z R1z R2z
                 rx_state rx other_rx prop0 propi tran_pgt_owned pgt_owned retri_owned mem_rest mem_acc_tx mem_tx");iFrameAutoSolve.
              all:done.
            }
            { (*Retrieve*)
              iApply (ftlr_retrieve with "IH regs tx pgt_tx pgt_acc pgt_acc' LB trans_hpool_global tran_pgt_transferred retri R0z R1z R2z
                 rx_state rx other_rx prop0 propi tran_pgt_owned pgt_owned retri_owned mem_rest mem_acc_tx mem_tx");iFrameAutoSolve.
              all:done.
            }
            { (*Relinquish*)
              iApply (ftlr_relinquish with "IH regs tx pgt_tx pgt_acc pgt_acc' LB trans_hpool_global tran_pgt_transferred retri R0z R1z R2z
                 rx_state rx other_rx prop0 propi tran_pgt_owned pgt_owned retri_owned mem_rest mem_acc_tx mem_tx");iFrameAutoSolve.
              all:done.
            }
            { (*Reclaim*)
              iApply (ftlr_reclaim with "IH regs tx pgt_tx pgt_acc pgt_acc' LB trans_hpool_global tran_pgt_transferred retri R0z R1z R2z
                 rx_state rx other_rx prop0 propi tran_pgt_owned pgt_owned retri_owned mem_rest mem_acc_tx mem_tx");iFrameAutoSolve.
              all:done.
            }
            { (*Send*)
              iApply (ftlr_msg_send with "IH regs tx pgt_tx pgt_acc pgt_acc' LB trans_hpool_global tran_pgt_transferred retri R0z R1z R2z
                 rx_state rx other_rx prop0 propi tran_pgt_owned pgt_owned retri_owned mem_rest mem_acc_tx mem_tx");iFrameAutoSolve.
              all:done.
            }
            { (*Wait*)
              iApply (ftlr_msg_wait with "IH regs tx pgt_tx pgt_acc pgt_acc' LB trans_hpool_global tran_pgt_transferred retri R0z R1z R2z
                 rx_state rx other_rx prop0 propi tran_pgt_owned pgt_owned retri_owned mem_rest mem_acc_tx mem_tx");iFrameAutoSolve.
              all:done.
            }
            { (*Poll*)
              iApply (ftlr_msg_poll with "IH regs tx pgt_tx pgt_acc pgt_acc' LB trans_hpool_global tran_pgt_transferred retri R0z R1z R2z
                 rx_state rx other_rx prop0 propi tran_pgt_owned pgt_owned retri_owned mem_rest mem_acc_tx mem_tx");iFrameAutoSolve.
              all:done.
            }
          }
          { (* decode_hvc_func r0 = None *)
            iApply (ftlr_invalid_hvc with "IH regs tx pgt_tx pgt_acc pgt_acc' LB trans_hpool_global tran_pgt_transferred retri R0z R1z R2z
                 rx_state rx other_rx prop0 propi tran_pgt_owned pgt_owned retri_owned mem_rest mem_acc_tx mem_tx");iFrameAutoSolve.
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
  Qed.

End fundamental.
