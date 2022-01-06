From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang.
From HypVeri.algebra Require Import base pagetable.
From HypVeri.rules Require Import rules_base nop mov (* ldr str halt fail add sub mult cmp *).
From HypVeri.logrel Require Import logrel logrel_extra.
From HypVeri Require Import proofmode.
Import uPred.

Section fundamental.
  Context `{hypconst:HypervisorConstants}.
  Context `{hypparams:!HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.

  (* TODO:
   - [] new lemmas for updating VMProp (not necessary)
   - [] str
   - [] fix mem_send_nz.v
   - [] mem share *)

  (* TODO: separate into helper lemmas *)
  Lemma ftlr (i:VMID)  :
  ∀ ps_acc p_tx p_rx trans, interp_access i ps_acc p_tx p_rx trans ⊢ interp_execute i.
  Proof.
    rewrite /interp_access /=.
    (* iLöb as "IH". *)
    iIntros (ps_acc p_tx p_rx trans) "((%regs & #Htotal_regs & regs) & tx & pgt_acc & pgt_owned & trans_owned & #Hps_incl & mem_owned & VMProp) Hnotp VMProp_holds".
    iDestruct (VMProp_holds_agree i with "[$VMProp_holds $VMProp]") as "[Hres _]".
    iEval (rewrite later_sep) in "Hres".
    iDestruct "Hres" as "[>Hres1 Hres]".
    iLöb as "IH" forall (regs ps_acc trans) "Htotal_regs Hps_incl".
    (* we don't really need to get the resource of PC, but just the value *)
    iDestruct "Hres1" as (ps_na trans' hpool) "(%Heq_acc_trans & LB & %Hdisj_ps & %Hinv_trans & hp & trans_transferred &
                         pgt_transferred & mem_transferred & rx_state & rx & mem_rx)".
    iDestruct "Hps_incl" as %Hps_incl.
    iAssert (memory_cells ps_acc)%I with "[mem_owned mem_transferred mem_rx]" as "mem".
    {
      iDestruct (memory_cells_disj with "[$mem_rx $mem_transferred]") as %Hdisj_ps_rx.
      rewrite /memory_cells.
      rewrite Heq_acc_trans.
      assert (ps_acc = (ps_acc ∖ (ps_trans (accessible_trans i trans') ∪ {[p_rx]})) ∪ (ps_trans (accessible_trans i trans') ∪ {[p_rx]})) as Hps_eq.
      {
        rewrite -Heq_acc_trans.
        rewrite difference_union_L.
        rewrite union_comm_L.
        rewrite subseteq_union_1_L //.
      }
      iEval (rewrite Hps_eq).
      rewrite big_opS_union;last set_solver +.
      iFrame "mem_owned".
      rewrite big_opS_union; last set_solver + Hdisj_ps_rx.
      iFrame.
    }

    iDestruct "Htotal_regs" as %Htotal_regs.
    pose proof (Htotal_regs PC) as Hlookup_PC.
    destruct Hlookup_PC as [ai Hlookup_PC].
    (* sswp *)
    rewrite ->wp_sswp.
    destruct (decide ((tpa ai) ∈ ps_acc)).
    { (* i has access *)
      (* TODO: (tpa ai) ≠ tx *)
      iEval (rewrite /memory_cells ) in "mem".
      rewrite (big_sepS_delete _ ps_acc (tpa ai));last done.
      iDestruct "mem" as "[[%mem_g (%His_some_mem_g & mem_pi)] mem]".
      pose proof (His_some_mem_g ai) as His_some_mem_ai.
      feed specialize His_some_mem_ai;first apply tpa_addr_of_page.
      destruct His_some_mem_ai as [instr Hlookup_mem_ai].
      destruct (decode_instruction instr) as [instr'|] eqn:Heqn.
      { (* valid instruction *)
        destruct instr'.
        { (* nop *)
          (* getting the PC *)
          iDestruct (reg_big_sepM_split_upd regs i Hlookup_PC with "[$regs]")
            as "[PC Hacc_regs]";first done.
          (* getting mem *)
          iDestruct (mem_big_sepM_split mem_g Hlookup_mem_ai with "[$mem_pi]")
            as "[mem_instr mem_pi]".
          iApply (nop ai (w1 := instr) with "[PC pgt_acc mem_instr]"); iFrameAutoSolve.
          iNext.
          iIntros "(PC & mem_instr & pgt_acc) _".
          iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "PC") as "[#Htotal_regs' regs]".
          iDestruct ("mem_pi" with "[mem_instr]") as "mem_pi";  first iFrame.
          (*TODO :split mem*)
          iSpecialize ("IH" $! _ with "regs tx pgt_acc pgt_owned trans_owned [mem_pi mem] Hnotp
                             [LB hp trans_transferred pgt_transferred $rx_state $rx] [$Hres]").
          { admit. }
          { iExists ps_na, trans', hpool. iFrame. admit. }
          iApply "IH".
          done.
          done.
        }
        { (* mov *)
          admit.
          (* destruct src as [imm | srcreg]. *)
          (* { (* mov imm *) *)
          (*   destruct dst. *)
          (*   { *)
          (*     apply decode_instruction_valid in Heqn. *)
          (*     inversion Heqn. *)
          (*     unfold reg_valid_cond in *. *)
          (*     exfalso. *)
          (*     naive_solver. *)
          (*   } *)
          (*   { *)
          (*     apply decode_instruction_valid in Heqn. *)
          (*     inversion Heqn. *)
          (*     unfold reg_valid_cond in *. *)
          (*     exfalso. *)
          (*     naive_solver. *)
          (*   } *)
          (*   { *)
          (*     iPoseProof ("Htotal_regs" $! (R n fin)) as (w) "%Hlookup_R". *)
          (*     (* getting regs *) *)
          (*     iDestruct ((reg_big_sepM_split_upd2 regs i _ Hlookup_PC Hlookup_R) *)
          (*                 with "[$Htotal_regs $regs]") as "(PC & R & Hacc_regs)". *)
          (*     (* getting mem *) *)
          (*     rewrite /accessible_memory. *)
          (*     (* we don't update memory *) *)
          (*     iDestruct (mem_big_sepM_split mem Hlookup_instr with "[$mem]") *)
          (*       as "[instrm Hacc_mem]". *)
          (*     iDestruct ("instrm" with "[]") as "instrm". *)
          (*     { iPureIntro. exists (v,sacc).  split;done. } *)
          (*     (* getting pgt *) *)
          (*     (* we don't update pagetable *) *)
          (*     iDestruct (pgt_big_sepM_split pgt Hlookup_ai with "[$pgt]") *)
          (*       as "[[_ pi] Hacc_pgt]". *)
          (*     iDestruct ("pi" with "[]") as (q) "[pi p_instr_q]"; first done. *)
          (*     iApply (mov_word (w3 := w) _ imm (R n fin) with "[PC pi instrm R]"); iFrameAutoSolve. *)
          (*     iNext. *)
          (*     iIntros "(PC & instrm & pi & R) _". *)
          (*     iDestruct ("Hacc_regs" with "[$PC $R]") as (regs') "[#Htotal_regs' regs]";iFrame. *)
          (*     iDestruct ("Hacc_mem" with "[instrm]") as "mem". *)
          (*     { iIntros "_". iFrame "instrm". } *)
          (*     iDestruct ("Hacc_pgt" with "[pi p_instr_q]") as "pgt". *)
          (*     { iSplitL "". iIntros "%".  rewrite /= //in H. iIntros "_". iExists q. iFrame "pi p_instr_q". } *)
          (*     iDestruct (VMProp_split with "VMProp") as "[VMProp1 VMProp2]". *)
          (*     iSpecialize ("IH" $! pgt with "[regs Htotal_regs' rx tx VMProp1]"). *)
          (*     iExists regs'. *)
          (*     iFrame. *)
          (*     iFrame "#". *)
          (*     iSpecialize ("IH" with "Hnotp"). *)
          (*     iApply "IH". *)
          (*     set Pred := (X in VMProp i X _). *)
          (*     iExists Pred. *)
          (*     iFrame. *)
          (*     iNext. *)
          (*     iLeft. *)
          (*     iExists mem, shandle. *)
          (*     iFrame. *)
          (*     iFrame "#". *)
          (*   } *)
          (* } *)
          (* { (* mov reg *) *)
          (*   destruct dst. *)
          (*   { *)
          (*     apply decode_instruction_valid in Heqn. *)
          (*     inversion Heqn. *)
          (*     unfold reg_valid_cond in *. *)
          (*     exfalso. *)
          (*     naive_solver. *)
          (*   } *)
          (*   { *)
          (*     apply decode_instruction_valid in Heqn. *)
          (*     inversion Heqn. *)
          (*     unfold reg_valid_cond in *. *)
          (*     exfalso. *)
          (*     naive_solver. *)
          (*   } *)
          (*   destruct srcreg. *)
          (*   { *)
          (*     apply decode_instruction_valid in Heqn. *)
          (*     inversion Heqn. *)
          (*     unfold reg_valid_cond in *. *)
          (*     exfalso. *)
          (*     naive_solver. *)
          (*   } *)
          (*   { *)
          (*     apply decode_instruction_valid in Heqn. *)
          (*     inversion Heqn. *)
          (*     unfold reg_valid_cond in *. *)
          (*     exfalso. *)
          (*     naive_solver. *)
          (*   } *)
          (*   { *)
          (*     iPoseProof ("Htotal_regs" $! (R n fin)) as (w) "%Hlookup_R". *)
          (*     iPoseProof ("Htotal_regs" $! (R n0 fin0)) as (w') "%Hlookup_R'". *)
          (*     (* getting regs *) *)

          (*     iDestruct ((reg_big_sepM_split_upd3 regs i _ _ _ Hlookup_PC Hlookup_R Hlookup_R') *)
          (*                 with "[$Htotal_regs $regs]") as "(PC & R & R' & Hacc_regs)". *)
          (*     (* getting mem *) *)
          (*     rewrite /accessible_memory. *)
          (*     (* we don't update memory *) *)
          (*     iDestruct (mem_big_sepM_split mem Hlookup_instr with "[$mem]") *)
          (*       as "[instrm Hacc_mem]". *)
          (*     iDestruct ("instrm" with "[]") as "instrm". *)
          (*     { iPureIntro. exists (v,sacc).  split;done. } *)
          (*     (* getting pgt *) *)
          (*     (* we don't update pagetable *) *)
          (*     iDestruct (pgt_big_sepM_split pgt Hlookup_ai with "[$pgt]") *)
          (*       as "[[_ pi] Hacc_pgt]". *)
          (*     iDestruct ("pi" with "[]") as (q) "[pi p_instr_q]"; first done. *)
          (*     iApply (mov_reg (w3 := w') _ _ (R n fin) (R n0 fin0) with "[PC pi instrm R R']"); iFrameAutoSolve. *)
          (*     iNext. *)
          (*     iIntros "(PC & instrm & pi & R & R') _". *)
          (*     iDestruct ("Hacc_regs" with "[$PC $R $R']") as (regs') "[#Htotal_regs' regs]";iFrame. *)
          (*     iDestruct ("Hacc_mem" with "[instrm]") as "mem". *)
          (*     { iIntros "_". iFrame "instrm". } *)
          (*     iDestruct ("Hacc_pgt" with "[pi p_instr_q]") as "pgt". *)
          (*     { iSplitL "". iIntros "%".  rewrite /= //in H. iIntros "_". iExists q. iFrame "pi p_instr_q". } *)
          (*     iDestruct (VMProp_split with "VMProp") as "[VMProp1 VMProp2]". *)
          (*     iSpecialize ("IH" $! pgt with "[regs Htotal_regs' rx tx VMProp1]"). *)
          (*     iExists regs'. *)
          (*     iFrame. *)
          (*     iFrame "#". *)
          (*     iSpecialize ("IH" with "Hnotp"). *)
          (*     iApply "IH". *)
          (*     set Pred := (X in VMProp i X _). *)
          (*     iExists Pred. *)
          (*     iFrame. *)
          (*     iNext. *)
          (*     iLeft. *)
          (*     iExists mem, shandle. *)
          (*     iFrame. *)
          (*     iFrame "#". *)
          (*   } *)
          (* } *)
        }
        { (* ldr *)
          admit.
          (* pose proof Heqn as Hdecode. *)
          (* apply decode_instruction_valid in Heqn. *)
          (* inversion Heqn as [| | ? ? Hvalid_dst Hvalid_src Hvalid_neq | | | | | | | | | ]. *)
          (* subst dst0 src0. *)
          (* unfold reg_valid_cond in Hvalid_dst, Hvalid_src. *)
          (* iPoseProof ("Htotal_regs" $! src) as (a_src) "%Hlookup_src". *)
          (* iPoseProof ("Htotal_regs" $! dst) as (w_dst) "%Hlookup_dst". *)
          (* iPoseProof ("Htotal_pgt" $! (tpa a_src)) as (perm_src) "%Hlookup_p_src". *)
          (* iDestruct "tx" as (p_tx) "tx". *)
          (* (* getting registers *) *)
          (* iDestruct ((reg_big_sepM_split_upd3 regs i _ _ _ Hlookup_PC Hlookup_src Hlookup_dst) *)
          (*             with "[$Htotal_regs $regs]") as "(PC & r_src & r_dst & Hacc_regs)". *)
          (* (* case analysis on src  *) *)
          (* destruct (decide (i ∈ perm_src.2)). *)
          (* { (* has access to the page, more cases.. *) *)
          (*   destruct (decide((tpa a_src) = p_tx)). *)
          (*   { (* trying to read from tx page, fail *) *)
          (*     (* getting mem *) *)
          (*     rewrite /accessible_memory. *)
          (*     iDestruct (mem_big_sepM_split mem Hlookup_instr with "[$mem]") *)
          (*       as "[instrm Hacc_mem]". *)
          (*     iDestruct ("instrm" with "[]") as "a_instr". *)
          (*     { iPureIntro. exists (v,sacc).  split;done. } *)
          (*     (* getting pgt *) *)
          (*     iDestruct (pgt_big_sepM_split pgt Hlookup_ai with "[$pgt]") *)
          (*       as "[[_ pi] Hacc_pgt]". *)
          (*     iDestruct ("pi" with "[]") as (q) "[p_instr p_instr_q]"; first done. *)
          (*     iApply (ldr_access_tx ai a_src dst src with "[PC p_instr a_instr r_src r_dst tx]"); iFrameAutoSolve. *)
          (*     iNext. *)
          (*     iIntros "(tx & PC & a_instr & r_src & r_dst) _". *)
          (*     by iApply wp_terminated. *)
          (*   } *)
          (*   { (* normal case *) *)
          (*     destruct (decide ( a_src =ai)). *)
          (*     { (* exact same addr *) *)
          (*       iDestruct (pgt_big_sepM_split pgt Hlookup_ai with "[$pgt]") *)
          (*         as "[[_ pi] Hacc_pgt]". *)
          (*       iDestruct ("pi" with "[]") as (q) "[p_instr p_instr_q]"; first done. *)
          (*       iDestruct (mem_big_sepM_split mem Hlookup_instr with "[$mem]") *)
          (*         as "[instrm Hacc_mem]". *)
          (*       iDestruct ("instrm" with "[]") as "a_instr". *)
          (*       { iPureIntro. exists (v,sacc).  split;done. } *)
          (*       iApply (ldr_same_addr ai a_src dst src with "[PC p_instr a_instr r_src r_dst tx]"); iFrameAutoSolve. *)
          (*       { symmetry;done. } *)
          (*       iNext. *)
          (*       iIntros "(PC & a_instr & r_src & r_dst & p_instr & tx) _". *)
          (*       iDestruct ("Hacc_regs" with "[$PC $r_src $r_dst]") as (regs') "[#Htotal_regs' regs]";iFrame. *)
          (*       iDestruct ("Hacc_mem" with "[a_instr]") as "mem". *)
          (*       { iIntros "_". iFrame "a_instr". } *)
          (*       iDestruct ("Hacc_pgt" with "[p_instr p_instr_q]") as "pgt". *)
          (*       { iSplitL "". iIntros "%".  rewrite /= //in H. iIntros "_". iExists q. iFrame "p_instr p_instr_q". } *)
          (*       iDestruct (VMProp_split with "VMProp") as "[VMProp1 VMProp2]". *)
          (*       iSpecialize ("IH" $! pgt with "[regs Htotal_regs' rx tx VMProp1]"). *)
          (*       iExists regs'. *)
          (*       iFrame. *)
          (*       iFrame "#". *)
          (*       iExists p_tx. *)
          (*       iFrame. *)
          (*       iSpecialize ("IH" with "Hnotp"). *)
          (*       iApply "IH". *)
          (*       set Pred := (X in VMProp i X _). *)
          (*       iExists Pred. *)
          (*       iFrame. *)
          (*       iNext. *)
          (*       iLeft. *)
          (*       iExists mem, shandle. *)
          (*       iFrame. *)
          (*       iFrame "#". *)
          (*     } *)
          (*     { (* different addresses *) *)
          (*       iPoseProof ("Htotal_mem" $! a_src) as (w_src) "%Hlookup_a_src". *)
          (*       destruct (decide ((tpa a_src)=(tpa ai))). *)
          (*       { (* in same page *) *)
          (*         iDestruct (pgt_big_sepM_split pgt Hlookup_ai with "[$pgt]") *)
          (*           as "[[_ pi] Hacc_pgt]". *)
          (*         iDestruct ("pi" with "[]") as (q) "[p_instr p_instr_q]"; first done. *)
          (*         iDestruct (mem_big_sepM_split2 mem _ Hlookup_instr Hlookup_a_src with "[$mem]") *)
          (*           as "[a_instr [a_src Hacc_mem]]". *)
          (*         iDestruct ("a_instr" with "[]") as "a_instr". *)
          (*         { iPureIntro. exists (v,sacc).  split;done. } *)
          (*         iDestruct ("a_src" with "[]") as "a_src". *)
          (*         { iPureIntro. exists (v,sacc).  split. rewrite e1 //. simpl;done. } *)
          (*         iApply (ldr_same_page ai a_src dst src with "[PC p_instr a_instr a_src r_src r_dst tx]"); iFrameAutoSolve. *)
          (*         { symmetry;done. } *)
          (*         iNext. *)
          (*         iIntros "(PC & a_instr & r_src & a_src & r_dst & p_instr & tx) _". *)
          (*         iDestruct ("Hacc_regs" with "[$PC $r_src $r_dst]") as (regs') "[#Htotal_regs' regs]";iFrame. *)
          (*         iDestruct ("Hacc_mem" with "[a_instr a_src]") as "mem". *)
          (*         { iSplitL "a_instr". *)
          (*           iIntros "_". iFrame "a_instr". *)
          (*           iIntros "_". iFrame "a_src". *)
          (*         } *)
          (*         iDestruct ("Hacc_pgt" with "[p_instr p_instr_q]") as "pgt". *)
          (*         { iSplitL "". iIntros "%".  rewrite /= //in H. iIntros "_". iExists q. iFrame "p_instr p_instr_q". } *)
          (*         iDestruct (VMProp_split with "VMProp") as "[VMProp1 VMProp2]". *)
          (*         iSpecialize ("IH" $! pgt with "[regs Htotal_regs' rx tx VMProp1]"). *)
          (*         iExists regs'. *)
          (*         iFrame. *)
          (*         iFrame "#". *)
          (*         iExists p_tx. *)
          (*         iFrame. *)
          (*         iSpecialize ("IH" with "Hnotp"). *)
          (*         iApply "IH". *)
          (*         set Pred := (X in VMProp i X _). *)
          (*         iExists Pred. *)
          (*         iFrame. *)
          (*         iNext. *)
          (*         iLeft. *)
          (*         iExists mem, shandle. *)
          (*         iFrame. *)
          (*         iFrame "#". *)
          (*       } *)
          (*       { (* in difference pages *) *)
          (*         iDestruct (pgt_big_sepM_split2 pgt _ Hlookup_ai Hlookup_p_src with "[$pgt]") *)
          (*         as "([_ p_instr] & [_ p_src] & Hacc_pgt)". *)
          (*         iDestruct ("p_instr" with "[]") as (q_i) "[p_instr p_instr_q]";first done. *)
          (*         iDestruct ("p_src" with "[]") as (q_s) "[p_src p_src_q]";first done. *)
          (*         (* getting mem *) *)
          (*         rewrite /accessible_memory. *)
          (*         iDestruct (mem_big_sepM_split2 mem _ Hlookup_instr Hlookup_a_src with "[$mem]") *)
          (*           as "(a_instr & a_src & Hacc_mem)". *)
          (*         iDestruct ("a_instr" with "[]") as "a_instr". *)
          (*         { iPureIntro. exists (v,sacc).  split;done. } *)
          (*         iDestruct ("a_src" with "[]") as "a_src". *)
          (*         { iPureIntro. exists perm_src.  split;done. } *)
          (*         iApply (ldr ai a_src dst src with "[PC p_instr p_src a_instr a_src r_src r_dst tx]"); iFrameAutoSolve. *)
          (*         iNext. *)
          (*         iIntros "(PC & a_instr & r_src & a_src & r_dst & p_instr & p_src & tx) _". *)
          (*         iDestruct ("Hacc_regs" with "[$PC $r_src $r_dst]") as (regs') "[#Htotal_regs' regs]";iFrame. *)
          (*         iDestruct ("Hacc_mem" with "[a_instr a_src]") as "mem". *)
          (*         { iSplitL "a_instr". *)
          (*           iIntros "_". iFrame "a_instr". *)
          (*           iIntros "_". iFrame "a_src". *)
          (*         } *)
          (*         iDestruct ("Hacc_pgt" with "[p_instr p_src p_instr_q p_src_q]") as "pgt". *)
          (*         { iSplitL "p_instr p_instr_q". iSplitL "". iIntros "%".  rewrite /= //in H. iIntros "_". iExists q_i. iFrame "p_instr p_instr_q". *)
          (*           iSplitL "". iIntros "%".  rewrite /= //in H. iIntros "_". iExists q_s. iFrame "p_src p_src_q". } *)
          (*         iDestruct (VMProp_split with "VMProp") as "[VMProp1 VMProp2]". *)
          (*         iSpecialize ("IH" $! pgt with "[regs Htotal_regs' rx tx VMProp1]"). *)
          (*         iExists regs'. *)
          (*         iFrame. *)
          (*         iFrame "#". *)
          (*         iExists p_tx. *)
          (*         iFrame. *)
          (*         iSpecialize ("IH" with "Hnotp"). *)
          (*         iApply "IH". *)
          (*         set Pred := (X in VMProp i X _). *)
          (*         iExists Pred. *)
          (*         iFrame. *)
          (*         iNext. *)
          (*         iLeft. *)
          (*         iExists mem, shandle. *)
          (*         iFrame. *)
          (*         iFrame "#". *)
          (*       } *)
          (*     } *)
          (*   } *)
          (* } *)
          (* { (* no access to the page, apply ldr_error *) *)
          (*   (* getting mem *) *)
          (*   rewrite /accessible_memory. *)
          (*   (* we don't update memory *) *)
          (*   iDestruct (mem_big_sepM_split mem Hlookup_instr with "[$mem]") *)
          (*     as "[instrm Hacc_mem]". *)
          (*   iDestruct ("instrm" with "[]") as "a_instr". *)
          (*   { iPureIntro. exists (v,sacc).  split;done. } *)
          (*   (* getting pgt *) *)
          (*   (* we don't update pagetable *) *)
          (*   iDestruct (pgt_big_sepM_split2 pgt _ Hlookup_ai Hlookup_p_src with "[$pgt]") *)
          (*     as "([_ p_instr] & [p_src _] & Hacc_pgt)". *)
          (*   iDestruct ("p_instr" with "[]") as (q_i) "[p_instr p_instr_q]";first done. *)
          (*   iDestruct ("p_src" with "[]") as "p_src";first done. *)
          (*   iApply (ldr_no_access ai a_src dst src with "[PC p_instr a_instr r_src r_dst tx p_src]"); iFrameAutoSolve. *)
          (*   iNext. *)
          (*   iIntros "(tx & PC & a_instr & r_src & p_src & r_dst) _". *)
          (*   by iApply wp_terminated. *)
          (* } *)
        }
        { (* str *)
          admit.
          (* pose proof Heqn as Hdecode. *)
          (* apply decode_instruction_valid in Heqn. *)
          (* inversion Heqn as [| | | ? ? Hvalid_dst Hvalid_src Hvalid_neq | | | | | | | | ]. *)
          (* subst dst0 src0. *)
          (* unfold reg_valid_cond in Hvalid_dst, Hvalid_src. *)
          (* iPoseProof ("Htotal_regs" $! src) as (w_src) "%Hlookup_src". *)
          (* iPoseProof ("Htotal_regs" $! dst) as (a_dst) "%Hlookup_dst". *)
          (* iPoseProof ("Htotal_pgt" $! (tpa a_dst)) as (perm_dst) "%Hlookup_p_dst". *)
          (* iDestruct "rx" as (p_rx) "rx". *)
          (* (* getting registers *) *)
          (* iDestruct ((reg_big_sepM_split_upd3 regs i _ _ _ Hlookup_PC Hlookup_src Hlookup_dst) *)
          (*              with "[$Htotal_regs $regs]") as "(PC & r_src & r_dst & Hacc_regs)". *)
          (* (* case analysis on src  *) *)
          (* destruct (decide (i ∈ perm_dst.2)). *)
          (* { (* has access to the page, more cases.. *) *)
          (*   destruct (decide((tpa a_dst) = p_rx)). *)
          (*   { (* trying to write to rx page, fail *) *)
          (*     (* getting mem *) *)
          (*     rewrite /accessible_memory. *)
          (*     iDestruct (mem_big_sepM_split mem Hlookup_instr with "[$mem]") *)
          (*       as "[a_instr Hacc_mem]". *)
          (*     iDestruct ("a_instr" with "[]") as "a_instr". *)
          (*     { iPureIntro. exists (v,sacc). split;done. } *)
          (*     (* getting pgt *) *)
          (*     iDestruct (pgt_big_sepM_split pgt Hlookup_ai with "[$pgt]") *)
          (*         as "([_ p_instr] & Hacc_pgt)". *)
          (*     (* iDestruct (pgt_big_sepM_split2 pgt _ Hlookup_ai Hlookup_p_dst with "[$pgt]") *) *)
          (*     (*   as "([_ p_instr] & [_ p_src] & Hacc_pgt)". *) *)
          (*     iDestruct ("p_instr" with "[]") as (q_i) "[p_instr p_instr_q]";first done. *)
          (*     iApply (str_access_rx ai a_dst src dst with "[PC p_instr a_instr r_src r_dst rx]"); iFrameAutoSolve. *)
          (*     iNext. *)
          (*     iIntros "(rx & PC & a_instr & r_src & r_dst) _". *)
          (*     by iApply wp_terminated. *)
          (*   } *)
          (*   { (* normal case *) *)
          (*     destruct (decide (a_dst =ai)). *)
          (*     { (* exact same addr *) *)
          (*       iDestruct (pgt_big_sepM_split pgt Hlookup_ai with "[$pgt]") *)
          (*         as "([_ p_instr] & Hacc_pgt)". *)
          (*       iDestruct ("p_instr" with "[]") as (q_i) "[p_instr p_instr_q]";first done. *)
          (*       iDestruct (mem_big_sepM_split_upd mem Hlookup_instr with "[$mem $Htotal_mem]") *)
          (*         as "[instrm Hacc_mem]". *)
          (*       iDestruct ("instrm" with "[]") as "a_instr". *)
          (*       { iPureIntro. exists (v,sacc). split;done. } *)
          (*       iApply (str_same_addr ai a_dst src dst with "[PC p_instr a_instr r_src r_dst rx]"); iFrameAutoSolve. *)
          (*       { symmetry;done. } *)
          (*       iNext. *)
          (*       iIntros "(PC & a_instr & r_src & r_dst & p_instr & rx) _". *)
          (*       iDestruct ("Hacc_regs" with "[$PC $r_src $r_dst]") as (regs') "[#Htotal_regs' regs]";iFrame. *)
          (*       iDestruct ("Hacc_mem" with "[a_instr]") as "[#Htotal_mem' mem]". *)
          (*       { iIntros "_". iFrame "a_instr". } *)
          (*       iDestruct ("Hacc_pgt" with "[p_instr p_instr_q]") as "pgt". *)
          (*       { iSplitL "". iIntros "%".  rewrite /= //in H. iIntros "_". iExists q_i. iFrame "p_instr p_instr_q". } *)
          (*       iDestruct (VMProp_split with "VMProp") as "[VMProp1 VMProp2]". *)
          (*       iSpecialize ("IH" $! pgt with "[regs Htotal_regs' rx tx VMProp1]"). *)
          (*       iExists regs'. *)
          (*       iFrame. *)
          (*       iFrame "#". *)
          (*       iExists p_rx. *)
          (*       iFrame. *)
          (*       iSpecialize ("IH" with "Hnotp"). *)
          (*       iApply "IH". *)
          (*       set Pred := (X in VMProp i X _). *)
          (*       iExists Pred. *)
          (*       iFrame. *)
          (*       iNext. *)
          (*       iLeft. *)
          (*       iExists (<[ai:=w_src]>mem), shandle. *)
          (*       iFrame. *)
          (*       iFrame "#". *)
          (*     } *)
          (*     { (* different addresses *) *)
          (*       iPoseProof ("Htotal_mem" $! a_dst) as (w_dst) "%Hlookup_a_dst". *)
          (*       destruct (decide ((tpa a_dst)=(tpa ai))). *)
          (*       { (* in same page *) *)
          (*         iDestruct (pgt_big_sepM_split pgt Hlookup_ai with "[$pgt]") *)
          (*           as "([_ p_instr] & Hacc_pgt)". *)
          (*         iDestruct ("p_instr" with "[]") as (q_i) "[p_instr p_instr_q]";first done. *)
          (*         iDestruct (mem_big_sepM_split_upd2 mem _ Hlookup_instr Hlookup_a_dst with "[$mem $Htotal_mem]") *)
          (*           as "[a_instr [a_src Hacc_mem]]". *)
          (*         iDestruct ("a_instr" with "[]") as "a_instr". *)
          (*         { iPureIntro. exists (v, sacc).  split;done. } *)
          (*         iDestruct ("a_src" with "[]") as "a_src". *)
          (*         { iPureIntro. exists (v,sacc).  split. rewrite e1 //. simpl;done. } *)
          (*         iApply (str_same_page ai a_dst src dst with "[PC p_instr a_instr a_src r_src r_dst rx]"); iFrameAutoSolve. *)
          (*         { symmetry;done. } *)
          (*         iNext. *)
          (*         iIntros "(PC & a_instr & r_src & a_src & r_dst & p_instr & rx) _". *)
          (*         iDestruct ("Hacc_regs" with "[$PC $r_src $r_dst]") as (regs') "[#Htotal_regs' regs]";iFrame. *)
          (*         iDestruct ("Hacc_mem" with "[a_instr a_src]") as (mem') "[#Htotal_mem' mem]". *)
          (*         { iSplitL "a_instr". *)
          (*           iIntros "_". iFrame "a_instr". *)
          (*           iIntros "_". iFrame "a_src". *)
          (*         } *)
          (*         iDestruct ("Hacc_pgt" with "[p_instr p_instr_q]") as "pgt". *)
          (*         { iSplitL "". iIntros "%".  rewrite /= //in H. iIntros "_". iExists q_i. iFrame "p_instr p_instr_q". } *)
          (*         iDestruct (VMProp_split with "VMProp") as "[VMProp1 VMProp2]". *)
          (*         iSpecialize ("IH" $! pgt with "[regs Htotal_regs' rx tx VMProp1]"). *)
          (*         iExists regs'. *)
          (*         iFrame. *)
          (*         iFrame "#". *)
          (*         iExists p_rx. *)
          (*         iFrame. *)
          (*         iSpecialize ("IH" with "Hnotp"). *)
          (*         iApply "IH". *)
          (*         set Pred := (X in VMProp i X _). *)
          (*         iExists Pred. *)
          (*         iFrame. *)
          (*         iNext. *)
          (*         iLeft. *)
          (*         iExists mem', shandle. *)
          (*         iFrame. *)
          (*         iFrame "#". *)
          (*       } *)
          (*       { (* in different pages *) *)
          (*         (* getting pgt *) *)
          (*         iDestruct (pgt_big_sepM_split2 pgt _ Hlookup_ai Hlookup_p_dst with "[$pgt]") *)
          (*           as "([_ p_instr] & [_ p_src] & Hacc_pgt)". *)
          (*         iDestruct ("p_instr" with "[]") as (q_i) "[p_instr p_instr_q]";first done. *)
          (*         iDestruct ("p_src" with "[]") as (q_s) "[p_src p_src_q]";first done. *)
          (*         (* getting mem *) *)
          (*         rewrite /accessible_memory. *)
          (*         iDestruct (mem_big_sepM_split_upd2 mem _ Hlookup_instr Hlookup_a_dst with "[$mem $Htotal_mem]") *)
          (*           as "(a_instr & a_src & Hacc_mem)". *)
          (*         iDestruct ("a_instr" with "[]") as "a_instr". *)
          (*         { iPureIntro. exists (v,sacc).  split;done. } *)
          (*         iDestruct ("a_src" with "[]") as "a_src". *)
          (*         { iPureIntro. exists perm_dst.  split;done. } *)
          (*         iApply (str ai a_dst src dst with "[PC p_instr p_src a_instr a_src r_src r_dst rx]"); iFrameAutoSolve. *)
          (*         iNext. *)
          (*         iIntros "(PC & a_instr & r_src & a_dst & r_dst & p_instr & p_src & rx) _". *)
          (*         iDestruct ("Hacc_regs" with "[$PC $r_src $r_dst]") as (regs') "[#Htotal_regs' regs]";iFrame. *)
          (*         iDestruct ("Hacc_mem" with "[a_instr a_dst]") as (mem') "[#Htotal_mem' mem]". *)
          (*         { iSplitL "a_instr". *)
          (*           iIntros "_". iFrame "a_instr". *)
          (*           iIntros "_". iFrame "a_dst". *)
          (*         } *)
          (*         iDestruct ("Hacc_pgt" with "[p_instr p_instr_q p_src p_src_q]") as "pgt". *)
          (*         { iSplitL "p_instr p_instr_q". iSplitL "". iIntros "%".  rewrite /= //in H. iIntros "_". iExists q_i. iFrame "p_instr p_instr_q". *)
          (*           iSplitL "". iIntros "%".  rewrite /= //in H. iIntros "_". iExists q_s. iFrame "p_src p_src_q". } *)
          (*         iDestruct (VMProp_split with "VMProp") as "[VMProp1 VMProp2]". *)
          (*         iSpecialize ("IH" $! pgt with "[regs Htotal_regs' rx tx VMProp1]"). *)
          (*         iExists regs'. *)
          (*         iFrame. *)
          (*         iFrame "#". *)
          (*         iExists p_rx. *)
          (*         iFrame. *)
          (*         iSpecialize ("IH" with "Hnotp"). *)
          (*         iApply "IH". *)
          (*         set Pred := (X in VMProp i X _). *)
          (*         iExists Pred. *)
          (*         iFrame. *)
          (*         iNext. *)
          (*         iLeft. *)
          (*         iExists mem', shandle. *)
          (*         iFrame. *)
          (*         iFrame "#". *)
          (*       } *)
          (*     } *)
          (*   } *)
          (* } *)
          (* { (* no access to the page, apply ldr_error *) *)
          (*   (* getting mem *) *)
          (*   rewrite /accessible_memory. *)
          (*   (* we don't update memory *) *)
          (*   iDestruct (mem_big_sepM_split mem Hlookup_instr with "[$mem]") *)
          (*     as "[instrm Hacc_mem]". *)
          (*   iDestruct ("instrm" with "[]") as "a_instr". *)
          (*   { iPureIntro. exists (v,sacc).  split;done. } *)
          (*   (* getting pgt *) *)
          (*   (* we don't update pagetable *) *)
          (*   iDestruct (pgt_big_sepM_split2 pgt _ Hlookup_ai Hlookup_p_dst with "[$pgt]") *)
          (*     as "([_ p_instr] & [p_dst _] & Hacc_pgt)". *)
          (*   iDestruct ("p_instr" with "[]") as (q_i) "[p_instr p_instr_q]";first done. *)
          (*   iDestruct ("p_dst" with "[]") as "p_dst";first done. *)
          (*   iApply (str_no_access ai a_dst src dst with "[PC p_instr a_instr r_src r_dst p_dst]"); iFrameAutoSolve. *)
          (*   iNext. *)
          (*   iIntros "(PC & a_instr & r_src & p_src & r_dst) _". *)
          (*   by iApply wp_terminated.             *)
          (* } *)
        }
        { (* cmp: two cases *) admit. }
        { (* add *) admit. }
        { (* sub *) admit. }
        { (* mult *) admit. }
        { (* bne *) admit. }
        { (* br *) admit. }
        { (* halt *)
          admit.
          (* pose proof Heqn as Hdecode. *)
          (* (* getting registers *) *)
          (* iDestruct ((reg_big_sepM_split_upd regs i Hlookup_PC) *)
          (*              with "[$Htotal_regs $regs]") as "(PC & Hacc_regs)". *)
          (* iDestruct (pgt_big_sepM_split pgt Hlookup_ai with "[$pgt]") *)
          (*   as "[[_ p_instr] Hacc_pgt]". *)
          (* rewrite /accessible_memory. *)
          (* (* we don't update memory *) *)
          (* iDestruct (mem_big_sepM_split mem Hlookup_instr with "[$mem]") *)
          (*   as "[instrm Hacc_mem]". *)
          (* iDestruct ("instrm" with "[]") as "instrm". *)
          (* { iPureIntro. exists (v,sacc).  split;done. } *)
          (* iDestruct ("p_instr" with "[#]") as "(%q & p_instr & Hq)"; first done. *)
          (* iApply (halt (s := {[i]}) (q := q) with "[PC p_instr instrm]"); iFrameAutoSolve. *)
          (* set_solver. *)
          (* iNext. *)
          (* iIntros "? _". *)
          (* by iApply wp_terminated. *)
        }
        { (* fail *)
          admit.
          (* pose proof Heqn as Hdecode. *)
          (* (* getting registers *) *)
          (* iDestruct ((reg_big_sepM_split_upd regs i Hlookup_PC) *)
          (*              with "[$Htotal_regs $regs]") as "(PC & Hacc_regs)". *)
          (* iDestruct (pgt_big_sepM_split pgt Hlookup_ai with "[$pgt]") *)
          (*   as "[[_ p_instr] Hacc_pgt]". *)
          (* rewrite /accessible_memory. *)
          (* (* we don't update memory *) *)
          (* iDestruct (mem_big_sepM_split mem Hlookup_instr with "[$mem]") *)
          (*   as "[instrm Hacc_mem]". *)
          (* iDestruct ("instrm" with "[]") as "instrm". *)
          (* { iPureIntro. exists (v,sacc).  split;done. } *)
          (* iDestruct ("p_instr" with "[#]") as "(%q & p_instr & Hq)"; first done. *)
          (* iApply (fail (s := {[i]}) (q := q) with "[PC p_instr instrm]"); iFrameAutoSolve. *)
          (* set_solver. *)
          (* iNext. *)
          (* iIntros "? _". *)
          (* by iApply wp_terminated. *)
        }
        { (* hvc *)admit.
          (*TODO*)
        }
      }
      { (*invalid instruction *)
        iDestruct (reg_big_sepM_split regs i Hlookup_PC with "[$regs]") as "[PC _]".
        (* getting pgt *)
        (* we don't update pagetable *)
        iDestruct (pgt_big_sepM_split pgt Hlookup_ai with "[$pgt]")
          as "[[_ p_instr] Hacc_pgt]".
        iDestruct ("p_instr" with "[]") as (q_i) "[p_instr _]";first done.
        (* getting mem *)
        rewrite /accessible_memory.
        (* we don't update memory *)
        iDestruct (mem_big_sepM_split mem Hlookup_instr with "[$mem]")
          as "[instrm Hacc_mem]".
        iDestruct ("instrm" with "[]") as "instrm".
        { iPureIntro. exists (v,sacc).  split;done. }
        iApply (not_valid_instr _ ai instr with "[PC p_instr instrm]"); iFrameAutoSolve.
        iNext.
        iIntros "? _".
        by iApply wp_terminated.
      }
    }
    { (* i doesn't have access *)
      iClear "VMProp VMPropz".
      rewrite /pagetable.
      iEval (rewrite (big_opM_delete _ _ (to_pid_aligned ai) _ Hlookup_ai)) in "pgt".
      iDestruct ("pgt") as "[[pi _] pgt]".
      simpl.
      iDestruct ("pi" with "[]") as "pi"; first done.
      iDestruct (reg_big_sepM_split regs i Hlookup_PC with "[$regs]") as "[PC _]".
      iApply (not_valid_pc with "[PC pi]");
      [exact n|iFrame|].
      iNext;simpl.
      iIntros "? _".
      by iApply wp_terminated.
    }
    Unshelve.
    all: destruct_and ?; try done.
    {
      apply decode_instruction_valid in Heqn.
      inversion Heqn.
      auto.
    }
    {
      intros c.
      rewrite c in Hlookup_ai.
      rewrite Hlookup_ai in Hlookup_p_src.
      inversion Hlookup_p_src as [H'].
      rewrite <-H' in n.
      simpl in n.
      done.
    }
    {
      intros c.
      rewrite c in Hlookup_ai.
      rewrite Hlookup_ai in Hlookup_p_dst.
      inversion Hlookup_p_dst as [H'].
      rewrite <-H' in n.
      simpl in n.
      done.
    }    
  Admitted.

End fundamental.
