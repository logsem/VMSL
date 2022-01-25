From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang trans_extra.
From HypVeri.algebra Require Import base pagetable mem.
From HypVeri.rules Require Import rules_base nop mov yield mem_share (* ldr str halt fail add sub mult cmp *).
From HypVeri.logrel Require Import logrel logrel_extra.
From HypVeri Require Import proofmode.
Import uPred.

Section fundamental.
  Context `{hypconst:HypervisorConstants}.
  Context `{hypparams:!HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.

  (* TODO:
   - [] str
   - [] fix mem_send_nz.v
   - [] separate into helper lemmas
  *)

  Lemma ftlr (i:VMID)  :
  ∀  p_tx p_rx ps_acc trans, interp_access i p_tx p_rx ps_acc trans ⊢ interp_execute i.
  Proof.
    rewrite /interp_access /=.
    iIntros (????) "((%regs & #Htotal_regs & regs) & (tx & [% mem_tx]) & pgt_acc & %Hsubset_mb & pgt_owned & tran_pgt_owned & mem_owned & VMProp)
                             %Hneq_p VMProp_holds".
    iDestruct (VMProp_holds_agree i with "[$VMProp_holds $VMProp]") as "[Hres propi]".
    iEval (rewrite later_exist) in "Hres".
    iDestruct "Hres" as (ps_na') "Hres".
    iEval (rewrite later_exist) in "Hres".
    iDestruct "Hres" as (ps_acc') "Hres".
    iEval (rewrite later_exist) in "Hres".
    iDestruct "Hres" as (trans') "Hres".
    iEval (rewrite later_exist) in "Hres".
    iDestruct "Hres" as (hpool') "Hres".
    iEval (rewrite later_exist) in "Hres".
    iDestruct "Hres" as (rx_state') "Hres".
    iEval (rewrite 15!later_sep) in "Hres".
    iDestruct "Hres" as  "( >pgt_acc' & >LB & >%Hdisj_na & >trans_hpool_global & >tran_pgt_transferred &
                         >retri & >mem_transferred &  >R0z & >R1z & >rx_state & >rx & >[% mem_rx] &
                          Himp_tran_pgt & Himp_pgt & Himp_mem & prop0)".
    iDestruct (access_agree_eq with "[$pgt_acc $pgt_acc']") as %->.

    iDestruct (later_wand with "Himp_tran_pgt") as "Himp_tran_pgt".
    iDestruct ("Himp_tran_pgt" with "tran_pgt_owned") as "tran_pgt_owned".
    iDestruct (later_wand with "Himp_pgt") as "Himp_pgt".
    iDestruct ("Himp_pgt" with "pgt_owned") as ">pgt_owned".
    iDestruct (later_wand with "Himp_mem") as "Himp_mem".
    iDestruct ("Himp_mem" with "[$mem_owned $mem_transferred]") as  (?) ">mem".

    set ps_mem_in_trans := (pages_in_trans (trans_memory_in_trans i trans')).
    iDestruct (memory_pages_disj_singleton (ps_acc' ∖ {[p_rx; p_tx]} ∪ ps_mem_in_trans) p_rx with "[$mem $mem_rx]") as %Hdisj_rx.

    iAssert (memory_pages (ps_acc' ∪ ps_mem_in_trans) (mem_all ∪ mem_rx ∪ mem_tx))%I
      with "[mem mem_rx mem_tx]" as "mem".
    {
    iDestruct (memory_pages_disj_singleton with "[$mem $mem_tx]") as %Hdisj_tx.
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
    iFrame.
    rewrite memory_pages_split_union.
    iSplit.
    iExists mem_rx, mem_tx.
    rewrite 2!memory_pages_singleton.
    iFrame.
    done.
    iPureIntro.
    rewrite map_union_assoc //.
    set_solver + Hneq_tx_rx.
    }

    iDestruct (memory_pages_split_diff _ ps_acc' with "mem") as (mem_rest mem_acc) "[mem_rest [mem_acc %Hmem_eq]]".
    set_solver.
    assert ((ps_acc' ∪ ps_mem_in_trans ) ∖ ps_acc' = ps_mem_in_trans ∖ ps_acc') as ->.
    { set_solver +. }

    iDestruct "tx" as "[tx pgt_tx]".

    subst ps_mem_in_trans.
    iLöb as "IH" forall (regs ps_acc' Hsubset_mb trans' Hdisj_na Hdisj_rx) "Htotal_regs".
    set ps_mem_in_trans := (pages_in_trans (trans_memory_in_trans i trans')).

    (* we don't really need to get the resource of PC, but just the value *)
    iDestruct "Htotal_regs" as %Htotal_regs.
    pose proof (Htotal_regs PC) as Hlookup_PC.
    destruct Hlookup_PC as [ai Hlookup_PC].
    (* sswp *)
    rewrite ->wp_sswp.
    destruct (decide ((tpa ai) ∈ ps_acc')) as [Hin_ps_acc | Hnotin_ps_acc].
    { (* i has access *)
      destruct (decide (tpa ai = p_tx)) as [Heq_ptx|Hneq_ptx].
      { (*invalid instruction location *)
        iDestruct (reg_big_sepM_split i Hlookup_PC with "[$regs]") as "[PC _]".
        iApply (invalid_pc_in_tx _ ai with "[PC tx]"); iFrameAutoSolve.
        iNext.
        iIntros "? _".
        by iApply wp_terminated.
      }
      iEval (rewrite /memory_pages) in "mem_acc".
      iDestruct "mem_acc" as "[%Hdom_mem_acc mem_acc]".
      pose proof (elem_of_memory_pages_lookup _ _ _ Hin_ps_acc Hdom_mem_acc) as [instr Hlookup_mem_ai].
      destruct (decode_instruction instr) as [instr'|] eqn:Heqn.
      { (* valid instruction *)
        destruct instr'.
        { (* nop *)
          (* getting the PC *)
          iDestruct (reg_big_sepM_split_upd i Hlookup_PC with "[$regs]")
            as "[PC Hacc_regs]";first done.
          (* getting mem *)
          iDestruct (mem_big_sepM_split mem_acc Hlookup_mem_ai with "mem_acc")
            as "[mem_instr Hacc_mem_acc]".
          iApply (nop ai (w1 := instr) with "[PC pgt_acc tx mem_instr]"); iFrameAutoSolve.
          iNext.
          iIntros "(PC & mem_instr & pgt_acc & tx) _".
          iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "PC") as "[#Htotal_regs' regs]".
          iDestruct ("Hacc_mem_acc" with "[$mem_instr]") as "mem_acc".
          (* split mem*)
          iAssert (memory_pages ps_acc' mem_acc)%I with "[mem_acc]" as "mem_acc". { by iFrame. }
          iApply ("IH" $! _ ps_acc' Hsubset_mb trans' Hdisj_na Hdisj_rx with "regs tx pgt_tx pgt_acc pgt_acc' LB trans_hpool_global
                            tran_pgt_transferred retri R0z R1z rx_state rx prop0 propi tran_pgt_owned pgt_owned mem_rest mem_acc
                            Htotal_regs'").
        }
        { (* mov *) admit.
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
        { (* ldr *) admit.
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
        { (* str *) admit.
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
        { (* halt *) admit.
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
        { (* fail *) admit.
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
        { (* hvc *)
          pose proof (Htotal_regs R0) as [r0 Hlookup_reg_R0].
          destruct (decode_hvc_func r0) as [hvc_f |] eqn:Hdecode_hvc .
          {
            destruct (hvc_f).
            { (*RUN TODO: proof rule*) admit. }
            { (*Yield*)
              iDestruct (reg_big_sepM_split_upd2 i Hlookup_PC Hlookup_reg_R0  with "[$regs]") as "(PC & R0 & Hacc_regs)";eauto.
              (* getting mem *)
              pose proof (union_split_difference_intersection_L ps_acc' ({[p_rx]} ∪ ps_mem_in_trans)) as [Heq_ps_acc' Hdisj_ps_acc'].
              rewrite Heq_ps_acc' in Hdom_mem_acc.
              rewrite set_of_addr_union in Hdom_mem_acc;last auto.
              apply dom_union_inv_L in Hdom_mem_acc;last apply set_of_addr_disj;auto.
              destruct Hdom_mem_acc as (mem_oea & mem_inters & Heq_mem_acc & Hdisj_mem_oea_inters & Hdom_mem_oea & Hdom_mem_inters).
              rewrite Heq_mem_acc.
              iDestruct (big_sepM_union with "mem_acc") as "[mem_oea mem_inters]";auto.
              destruct (decide ((tpa ai) ∈ (ps_acc' ∖ ({[p_rx]} ∪ ps_mem_in_trans)))) as [Hin_ps_oea | Hnin_ps_oea].
              { (* instruction is in ps_oea *)
                assert (Hsubseteq_mem_acc: mem_oea ⊆ mem_acc).
                rewrite Heq_mem_acc.
                apply map_union_subseteq_l.
                rewrite map_subseteq_spec in Hsubseteq_mem_acc.
                apply elem_of_set_of_addr_tpa in Hin_ps_oea.
                rewrite -Hdom_mem_oea in Hin_ps_oea.
                rewrite elem_of_dom in Hin_ps_oea.
                destruct Hin_ps_oea as [? Hlookup_mem_ai'].
                specialize (Hsubseteq_mem_acc ai _ Hlookup_mem_ai').
                rewrite Hlookup_mem_ai in Hsubseteq_mem_acc.
                inversion Hsubseteq_mem_acc.
                subst x.
                clear Hsubseteq_mem_acc.

                iAssert (memory_pages (ps_acc'
                                         ∩ ({[p_rx]} ∪ ps_mem_in_trans)) mem_inters)%I  with "[mem_inters]" as "mem_inters".
                {
                  rewrite /memory_pages.
                  iSplitL "";first done.
                  iFrame.
                }

                iDestruct (memory_pages_split_union
                             (ps_acc' ∩ ({[p_rx]} ∪ ps_mem_in_trans)) with "[mem_inters mem_rest]") as "mem_tran".
                2:{ iExists mem_inters, mem_rest. iSplitL "mem_inters". iFrame "mem_inters". iSplit. iExact "mem_rest".
                    iPureIntro. reflexivity. }
                {
                  rewrite intersection_union_l_L.
                  set_solver.
                }
                assert (ps_acc' ∩ ({[p_rx]} ∪ ps_mem_in_trans) ∪ ps_mem_in_trans ∖ ps_acc'
                        = {[p_rx]} ∪ ps_mem_in_trans) as ->.
                {
                  rewrite intersection_union_l_L.
                  rewrite -union_assoc_L.
                  rewrite intersection_comm_L.
                  rewrite subseteq_intersection_1_L;last set_solver.
                  pose proof (union_split_difference_intersection_L ps_mem_in_trans ps_acc' ) as [Heq _].
                  rewrite union_comm_L in Heq.
                  rewrite intersection_comm_L -Heq //.
                }

                iDestruct (mem_big_sepM_split mem_oea Hlookup_mem_ai' with "mem_oea") as "[mem_instr Hacc_mem]".
                iApply (yield ai (LB@ i := [ps_na'] ∗ i -@{1/2}A> ps_acc' ∗
                                 transaction_hpool_global_transferred hpool' trans' ∗
                                 transaction_pagetable_entries_transferred i trans' ∗ retrieval_entries i trans') False
                         with "[PC R0 R0z R1z pgt_acc tx mem_instr prop0 propi LB pgt_acc' trans_hpool_global tran_pgt_transferred mem_tran
                            retri rx_state rx]"); iFrameAutoSolve.
                {
                  iSplitL "prop0".
                  iFrame.
                  iSplitL "propi".
                  iFrame.
                  iSplitR "LB trans_hpool_global tran_pgt_transferred retri".
                  2:{ iFrame. }
                  iNext.
                  iIntros "((PC & mem_instr & pgt_acc & tx & R0i &R0z & R1z) & (LB & pgt_acc' & trans_hpool_global & trans_pgt_transferred & retri) & propi)".
                  iSplitL "pgt_acc LB trans_hpool_global trans_pgt_transferred retri R0z R1z rx_state rx mem_tran".
                  iLeft.
                  iExists ps_na', ps_acc', trans', hpool'.
                  iFrame.
                  iSplitL ""; first done.
                  iDestruct (memory_pages_split_union with "mem_tran") as (? ?) "[mem_rx [mem_trans %Heq_mem']]".
                  set_solver + Hdisj_rx.
                  iFrame.
                  iSplitL "mem_trans". iExists mem2. iFrame.
                  iSplitR "mem_rx".
                  destruct rx_state'; iFrame "rx_state".
                  iExists mem1. rewrite memory_pages_singleton. iFrame.
                  iCombine "PC mem_instr R0i pgt_acc' propi" as "R'". iExact "R'".
                }
                iNext.
                iIntros "[(PC & mem_instr & R0i & pgt_acc' & propi) propi']".
                iSimpl.
                iIntros "Hholds".
                rewrite /VMProp_holds.
                iDestruct "Hholds" as (P) "( _ & propi'')".
                iDestruct (VMProp_split with "[$propi $propi']") as "propi".
                iExFalso.
                iApply (VMProp_invalid with "[$propi $propi'']").
               }
              { (* tpa ai ∉ ps_acc' ∖ ({[p_rx]} ∪ ps_mem_in_trans) *)
                assert (tpa ai ∈ ps_acc' ∩ ({[p_rx]} ∪ ps_mem_in_trans )) as Hin_ps_inters.
                {
                  rewrite Heq_ps_acc' in Hin_ps_acc.
                  rewrite elem_of_union in Hin_ps_acc.
                  destruct Hin_ps_acc;done.
                }
                assert (Hsubseteq_mem_acc: mem_inters ⊆ mem_acc).
                { rewrite Heq_mem_acc. apply map_union_subseteq_r. done. }
                rewrite map_subseteq_spec in Hsubseteq_mem_acc.
                apply elem_of_set_of_addr_tpa in Hin_ps_inters.
                rewrite -Hdom_mem_inters in  Hin_ps_inters.
                rewrite elem_of_dom in Hin_ps_inters.
                destruct Hin_ps_inters as [? Hlookup_mem_ai'].
                specialize (Hsubseteq_mem_acc ai _ Hlookup_mem_ai').
                rewrite Hlookup_mem_ai in Hsubseteq_mem_acc.
                inversion Hsubseteq_mem_acc.
                subst x.
                clear Hsubseteq_mem_acc.

                iDestruct (mem_big_sepM_split mem_inters Hlookup_mem_ai' with "mem_inters") as "[mem_instr Hacc_mem_inters]".
                iApply (yield ai (LB@ i := [ps_na'] ∗ i -@{1/2}A> ps_acc' ∗
                                                                    transaction_hpool_global_transferred hpool' trans' ∗
                                                                    transaction_pagetable_entries_transferred i trans' ∗ retrieval_entries i trans') False
                         with "[PC R0 R0z R1z pgt_acc tx mem_instr prop0 propi LB pgt_acc' trans_hpool_global tran_pgt_transferred Hacc_mem_inters mem_rest
                            retri rx_state rx]"); iFrameAutoSolve.
                {
                  iSplitL "prop0".
                  iFrame.
                  iSplitL "propi".
                  iFrame.
                  iSplitR "LB trans_hpool_global tran_pgt_transferred retri".
                  2:{ iFrame. }
                  iNext.
                  iIntros "((PC & mem_instr & pgt_acc & tx & R0i &R0z & R1z) & (LB & pgt_acc' & trans_hpool_global & trans_pgt_transferred & retri) & propi)".
                  iDestruct ("Hacc_mem_inters" with "mem_instr") as "mem_inters".
                  (* FIXME: copied proofs  *)
                  iAssert (memory_pages (ps_acc' ∩ ({[p_rx]} ∪ ps_mem_in_trans)) mem_inters)%I  with "[mem_inters]" as "mem_inters".
                  {
                    rewrite /memory_pages.
                    iSplitL "";first done.
                    iFrame.
                  }
                  iDestruct (memory_pages_split_union
                               (ps_acc' ∩ ({[p_rx]} ∪ ps_mem_in_trans)) with "[mem_inters mem_rest]") as "mem_tran".
                  2:{ iExists mem_inters, mem_rest. iSplitL "mem_inters". iFrame "mem_inters". iSplit. iExact "mem_rest".
                      iPureIntro. reflexivity.}
                  {
                    rewrite intersection_union_l_L.
                    set_solver.
                  }
                  (* TODO: move this assert upward *)
                  assert (ps_acc' ∩ ({[p_rx]} ∪ ps_mem_in_trans) ∪ ps_mem_in_trans ∖ ps_acc'
                          = {[p_rx]} ∪ ps_mem_in_trans) as ->.
                  {
                    rewrite intersection_union_l_L.
                    rewrite -union_assoc_L.
                    rewrite intersection_comm_L.
                    rewrite subseteq_intersection_1_L;last set_solver.
                    pose proof (union_split_difference_intersection_L ps_mem_in_trans ps_acc' ) as [Heq _].
                    rewrite union_comm_L in Heq.
                    rewrite intersection_comm_L -Heq //.
                  }
                  iSplitL "pgt_acc LB trans_hpool_global trans_pgt_transferred retri R0z R1z rx_state rx mem_tran".
                  iLeft.
                  iExists ps_na', ps_acc', trans', hpool'.
                  iFrame.
                  iSplitL ""; first done.
                  iDestruct (memory_pages_split_union with "mem_tran") as (? ? )"[mem1 [mem2 %Heq_mem']]".
                  set_solver + Hdisj_rx.
                  iFrame.
                  iSplitL "mem2". iExists mem2. iFrame.
                  iSplitR "mem1".
                  destruct rx_state'; iFrame "rx_state".
                  iExists mem1. rewrite memory_pages_singleton. iFrame.
                  iCombine "PC R0i pgt_acc' propi" as "R'". iExact "R'".
                }
                iNext.
                iIntros "[(PC & R0i & pgt_acc' & propi) propi']".
                iSimpl.
                iIntros "Hholds".
                rewrite /VMProp_holds.
                iDestruct "Hholds" as (P) "( _ & propi'')".
                iDestruct (VMProp_split with "[$propi $propi']") as "propi".
                iExFalso.
                iApply (VMProp_invalid with "[$propi $propi'']").
              }
            }
            { (*Share: WIP *)
              pose proof (Htotal_regs R1) as[r1 Hlookup_reg_R1].
              pose proof (Htotal_regs R2) as[r2 Hlookup_reg_R2].
              iDestruct (reg_big_sepM_split_upd4 i Hlookup_PC Hlookup_reg_R0 Hlookup_reg_R1 Hlookup_reg_R2 with "[$regs]")
                as "(PC & R0 & R1 & R2 & Hacc_regs)";eauto.

              iPoseProof (memory_pages_split_singleton p_tx ps_acc') as "[Hsplit _]". set_solver + Hsubset_mb.
              iDestruct ("Hsplit" with "[mem_acc]") as (mem_acc_tx mem_tx') "[[%Hdom_mem_acc_tx mem_acc_tx] [mem_tx %Heq_mem_acc]]".
              { rewrite /memory_pages. iSplit. 2:{ iExact "mem_acc". } done. }
              iClear "Hsplit".
              assert (Hsubseteq_mem_acc: mem_acc_tx ⊆ mem_acc ).
              { rewrite -Heq_mem_acc. apply map_union_subseteq_l. }
              rewrite map_subseteq_spec in Hsubseteq_mem_acc.
              assert (Hin_ps_acc_tx: (tpa ai) ∈ ps_acc' ∖ {[p_tx]}).
              { set_solver + Hin_ps_acc Hneq_ptx. }
              apply elem_of_set_of_addr_tpa in Hin_ps_acc_tx.
              rewrite -Hdom_mem_acc_tx in Hin_ps_acc_tx.
              rewrite elem_of_dom in Hin_ps_acc_tx.
              destruct Hin_ps_acc_tx as [? Hlookup_mem_ai'].
              specialize (Hsubseteq_mem_acc ai _ Hlookup_mem_ai').
              rewrite Hlookup_mem_ai in Hsubseteq_mem_acc.
              inversion Hsubseteq_mem_acc.
              subst x.
              clear Hsubseteq_mem_acc.

              iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai' with "mem_acc_tx") as "[mem_instr Hacc_mem_acc_tx]".
              destruct (decide (page_size < r1)%Z).
              { (* the length of msg exceeds [page_size] *)
                iApply (hvc_mem_send_invalid_len ai with "[PC mem_instr pgt_acc' R0 R1 R2 tx]");iFrameAutoSolve.
                exact Hdecode_hvc.
                simpl. reflexivity.
                iNext.
                iIntros "(? & ? & ? & ?) _".
                admit.
              }

              destruct (parse_transaction_descriptor mem_tx' p_tx (Z.to_nat r1))  as [tran_des|] eqn:Heq_parse_tran.
              2 :{ (* cannot parse the msg as a descriptor *)
                iApply (hvc_mem_send_invalid_msg ai with "[PC mem_instr pgt_acc' R0 R1 R2 tx mem_tx]");iFrameAutoSolve.
                exact Hdecode_hvc.
                simpl. reflexivity.
                lia.
                exact Heq_parse_tran.
                iNext.
                done.
                iNext.
                iIntros "(? & ? & ? & ? & ? & ? & ? & ?) _".
                admit.
              }

              destruct (validate_transaction_descriptor i Sharing tran_des) eqn:Hvalid_tran_des.
              2: { (* validation of descriptor fails, apply [hvc_mem_send_invalid_des] *)
                admit.
              }

              apply validate_descriptor_share in Hvalid_tran_des as [j [ps_share [-> Hneq_sr]]].
              destruct (decide (ps_share ⊆ ps_acc')) as [Hsubseteq_share | Hnsubseteq_share].
              2: { (* no access to at least one page in ps_share, apply [hvc_mem_send_not_acc] *)
                admit.
              }
              destruct (decide (p_tx ∈ ps_share)) as [Hin_ptx_share | Hnin_ptx_share].
              { (* tx is not owned by i, apply [hvc_mem_send_not_owned] *)
                admit.
              }

              destruct (decide (p_rx ∈ ps_share)) as [Hin_prx_share | Hnin_prx_share].
              { (* rx is not owned by i, apply [hvc_mem_send_not_owned] *)
                admit.
              }

              assert (Hsubseteq_share' : ps_share ⊆ ps_acc' ∖ {[p_rx;p_tx]}).
              {
                set_solver + Hsubseteq_share Hnin_ptx_share Hnin_prx_share.
              }
              clear Hsubseteq_share Hnin_ptx_share Hnin_prx_share.
              destruct (decide (ps_share ⊆ ps_acc' ∖ {[p_rx; p_tx]} ∖ ps_mem_in_trans)) as [Hsubseteq_share | Hnsubseteq_share].
              { (* all pages are exclusively owned, ok to perceed *)
                destruct (decide (hpool' = ∅)).
                { (* no avaiable fresh handles, apply [hvc_mem_share_no_fresh_handles] *)
                  admit.
                }
                (* succeed, apply [hvc_mem_share_nz] *)
                admit.
              }
              { (* at least one page is not exclusively owned by i (i.e. is involved in a transaction) *)
                assert (∃ p, p ∈ ps_share ∧ p ∈ ps_mem_in_trans) as [p [Hin_p_share Hin_p_mem_in_trans]].
                { (* apply [not_subseteq_diff]*) admit.  }
                (* apply [elem_of_pages_in_trans] *)
                (* apply [hvc_mem_send_in_trans] *)
                admit.
              }
            }
            { (*Lend*) admit. }
            { (*Donate*) admit. }
            { (*Retrieve*) admit. }
            { (*Relinquish*) admit. }
            { (*Reclaim*) admit. }
            { (*Send*) admit. }
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
        iDestruct (mem_big_sepM_split mem_acc Hlookup_mem_ai with "mem_acc")
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
