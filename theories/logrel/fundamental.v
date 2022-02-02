From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang trans_extra.
From HypVeri.algebra Require Import base pagetable mem trans.
From HypVeri.rules Require Import rules_base nop mov yield mem_share mem_retrieve(* ldr str halt fail add sub mult cmp *).
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
                             %Hneq_0 VMProp_holds".
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
    iAssert (memory_pages (ps_acc' ∪ ps_mem_in_trans) (mem_all ∪ mem_rx ∪ mem_tx))%I
      with "[mem mem_rx mem_tx]" as "mem".
    {
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

    (* split memory pages into [mem_acc] and [mem_rest] *)
    iDestruct (memory_pages_split_diff _ ps_acc' with "mem") as (mem_rest mem_acc) "[mem_rest [mem_acc _]]".
    set_solver.
    clear mem_rx mem_tx mem_all.
    assert ((ps_acc' ∪ ps_mem_in_trans ) ∖ ps_acc' = ps_mem_in_trans ∖ (ps_acc'∖ {[p_tx]})) as ->.
    {
      assert ((ps_acc' ∪ ps_mem_in_trans ) ∖ ps_acc' = ps_mem_in_trans ∖ ps_acc') as ->.
      set_solver +.
      set_solver.
    }

    iDestruct "tx" as "[tx pgt_tx]".
    iDestruct (memory_pages_split_singleton p_tx ps_acc' with "mem_acc") as (mem_acc_tx mem_tx) "[[%Hdom_mem_acc_tx mem_acc_tx] [mem_tx %Heq_mem_acc]]". set_solver + Hsubset_mb.

    subst ps_mem_in_trans.
    iLöb as "IH" forall (regs ps_acc' Hsubset_mb trans' Hdisj_na Hnin_rx Hnin_tx Hdom_mem_acc_tx) "Htotal_regs".
    set ps_mem_in_trans := (pages_in_trans (trans_memory_in_trans i trans')).

    iDestruct "Htotal_regs" as %Htotal_regs.
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
      pose proof Hin_ps_acc_tx' as Hin_ps_acc_tx.
      apply elem_of_set_of_addr_tpa in Hin_ps_acc_tx'.
      rewrite -Hdom_mem_acc_tx in Hin_ps_acc_tx'.
      rewrite elem_of_dom in Hin_ps_acc_tx'.
      destruct Hin_ps_acc_tx' as [instr Hlookup_mem_ai].
      destruct (decode_instruction instr) as [instr'|] eqn:Heqn.
      { (* valid instruction *)
        destruct instr'.
        { (* nop *)
          (* getting the PC *)
          iDestruct (reg_big_sepM_split_upd i Hlookup_PC with "[$regs]")
            as "[PC Hacc_regs]";first done.
          (* getting mem *)
          iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "mem_acc_tx")
            as "[mem_instr Hacc_mem_acc]".
          iApply (nop ai (w1 := instr) with "[PC pgt_acc tx mem_instr]"); iFrameAutoSolve.
          iNext.
          iIntros "(PC & mem_instr & pgt_acc & tx) _".
          iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "PC") as "[#Htotal_regs' regs]".
          iDestruct ("Hacc_mem_acc" with "[$mem_instr]") as "mem_acc_tx".
          iApply ("IH" $! _ ps_acc' Hsubset_mb trans' Hdisj_na Hnin_rx Hnin_tx Hdom_mem_acc_tx with "regs tx pgt_tx pgt_acc pgt_acc' LB trans_hpool_global
                            tran_pgt_transferred retri R0z R1z rx_state rx prop0 propi tran_pgt_owned pgt_owned mem_rest mem_acc_tx mem_tx
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
            iAssert (⌜p_tx ≠ p_rx⌝)%I as "%Hneq_mb".
            {
             iDestruct "rx" as "[_ [_ excl_rx]]".
             iDestruct "pgt_tx" as "[_ excl_tx]".
             iApply (excl_ne with "[$ excl_tx $ excl_rx]").
            }
            destruct (hvc_f).
            { (*RUN*) admit. }
            { (*Yield*)
              iDestruct (reg_big_sepM_split_upd2 i Hlookup_PC Hlookup_reg_R0  with "[$regs]") as "(PC & R0 & Hacc_regs)";eauto.
              pose proof (union_split_difference_intersection_L (ps_acc'∖ {[p_tx]}) ({[p_rx]} ∪ ps_mem_in_trans)) as [Heq_ps_acc_tx Hdisj_ps_acc_tx].
              rewrite Heq_ps_acc_tx in Hdom_mem_acc_tx.
              rewrite set_of_addr_union in Hdom_mem_acc_tx;last auto.
              apply dom_union_inv_L in Hdom_mem_acc_tx;last apply set_of_addr_disj;auto.
              destruct Hdom_mem_acc_tx as (mem_oea & mem_inters & Heq_mem_acc_tx & Hdisj_mem_oea_inters & Hdom_mem_oea & Hdom_mem_inters).
              rewrite Heq_mem_acc_tx.
              iDestruct (big_sepM_union with "mem_acc_tx") as "[mem_oea mem_inters]";auto.

              (* for simplication *)
              assert (Heq_inter_diff_union: (ps_acc'∖ {[p_tx]}) ∩ ({[p_rx]} ∪ ps_mem_in_trans) ∪ ps_mem_in_trans ∖ (ps_acc' ∖ {[p_tx]})
                          = {[p_rx]} ∪ ps_mem_in_trans).
              {
                rewrite intersection_union_l_L.
                rewrite -union_assoc_L.
                rewrite intersection_comm_L.
                rewrite subseteq_intersection_1_L.
                2: { apply subseteq_difference_r. set_solver. set_solver + Hsubset_mb. }
                pose proof (union_split_difference_intersection_L ps_mem_in_trans (ps_acc'∖ {[p_tx]})) as [Heq _].
                rewrite union_comm_L intersection_comm_L in Heq.
                rewrite  -Heq //.
              }

              (* we have this annoying case anlaysis because we need to know if the instruction is in the memory pages required by VMProp 0 *)
              destruct (decide ((tpa ai) ∈ ((ps_acc'∖ {[p_tx]}) ∖ ({[p_rx]} ∪ ps_mem_in_trans)))) as [Hin_ps_oea | Hnin_ps_oea].
              { (* instruction is in ps_oea *)
                (* in this case, we don't need to transfer instruction *)
                assert (Hsubseteq_mem_acc: mem_oea ⊆ mem_acc_tx).
                rewrite Heq_mem_acc_tx.
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

                iAssert (memory_pages ((ps_acc' ∖ {[p_tx]}) ∩ ({[p_rx]} ∪ ps_mem_in_trans)) mem_inters)%I  with "[mem_inters]" as "mem_inters".
                { rewrite /memory_pages. iSplitL "";first done. iFrame. }

                (* merge [mem_inters] and [mem_rest] into [mem_trans] (including [mem_rx]) *)
                iDestruct (memory_pages_split_union
                             ((ps_acc'∖ {[p_tx]}) ∩ ({[p_rx]} ∪ ps_mem_in_trans)) with "[mem_inters mem_rest]") as "mem_tran".
                2:{ iExists mem_inters, mem_rest. iSplitL "mem_inters". iFrame "mem_inters". iSplit. iExact "mem_rest".
                    iPureIntro. reflexivity. }
                { set_solver +. }
                rewrite Heq_inter_diff_union.

                (* getting instruction from [mem_oea] *)
                iDestruct (mem_big_sepM_split mem_oea Hlookup_mem_ai' with "mem_oea") as "[mem_instr Hacc_mem]".
                iApply (yield ai (LB@ i := [ps_na'] ∗ i -@{1/2}A> ps_acc' ∗
                                 transaction_hpool_global_transferred trans' ∗
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
                  iExists ps_na', ps_acc', trans'.
                  iFrame.
                  iSplitL ""; first done.
                  (* split [mem_tran] into [mem_rx] and [mem_trans] *)
                  iDestruct (memory_pages_split_union with "mem_tran") as (? ?) "[mem_rx [mem_trans %Heq_mem']]".
                  set_solver + Hnin_rx.
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
                (* we don't need to touch [mem_oea]*)
                (* first show instr is in [mem_inters] *)
                assert (tpa ai ∈ (ps_acc'∖ {[p_tx]}) ∩ ({[p_rx]} ∪ ps_mem_in_trans )) as Hin_ps_inters.
                {
                  rewrite Heq_ps_acc_tx in Hin_ps_acc_tx.
                  rewrite elem_of_union in Hin_ps_acc_tx.
                  destruct Hin_ps_acc_tx;done.
                }
                assert (Hsubseteq_mem_acc: mem_inters ⊆ mem_acc_tx).
                { rewrite Heq_mem_acc_tx. apply map_union_subseteq_r. done. }
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
                iApply (yield ai (LB@ i := [ps_na'] ∗ i -@{1/2}A> ps_acc' ∗
                                                                    transaction_hpool_global_transferred trans' ∗
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
                  iAssert (memory_pages ((ps_acc'∖ {[p_tx]}) ∩ ({[p_rx]} ∪ ps_mem_in_trans)) mem_inters)%I  with "[mem_inters]" as "mem_inters".
                  { rewrite /memory_pages. iSplitL "";first done. iFrame. }
                  (* [mem_inters] + [mem_rest] = [mem_tran] *)
                  iDestruct (memory_pages_split_union
                               ((ps_acc'∖ {[p_tx]}) ∩ ({[p_rx]} ∪ ps_mem_in_trans)) with "[mem_inters mem_rest]") as "mem_tran".
                  2:{ iExists mem_inters, mem_rest. iSplitL "mem_inters". iFrame "mem_inters". iSplit. iExact "mem_rest".
                      iPureIntro. reflexivity.}
                  { set_solver +. }
                  rewrite Heq_inter_diff_union.

                  iSplitL "pgt_acc LB trans_hpool_global trans_pgt_transferred retri R0z R1z rx_state rx mem_tran".
                  iLeft.
                  iExists ps_na', ps_acc', trans'.
                  iFrame.
                  iSplitL ""; first done.
                  iDestruct (memory_pages_split_union with "mem_tran") as (? ? )"[mem1 [mem2 %Heq_mem']]".
                  set_solver + Hnin_rx.
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
            { (*Share *)
              pose proof (Htotal_regs R1) as[r1 Hlookup_reg_R1].
              pose proof (Htotal_regs R2) as[r2 Hlookup_reg_R2].
              iDestruct (reg_big_sepM_split_upd4 i Hlookup_PC Hlookup_reg_R0 Hlookup_reg_R1 Hlookup_reg_R2 with "[$regs]")
                as "(PC & R0 & R1 & R2 & Hacc_regs)";eauto.
              iDestruct (mem_big_sepM_split mem_acc_tx Hlookup_mem_ai with "mem_acc_tx") as "[mem_instr Hacc_mem_acc_tx]".

              destruct (decide (page_size < r1)%Z).
              { (* the length of msg exceeds [page_size] *)
                iApply (hvc_mem_send_invalid_len ai with "[PC mem_instr pgt_acc' R0 R1 R2 tx]");iFrameAutoSolve.
                exact Hdecode_hvc.
                simpl; reflexivity.
                iNext.
                iIntros "(PC & mem_instr & pgt_acc' & R0 & R1 & R2 & tx) _".
                iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[#Htotal_regs' regs]".

                iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
                iApply ("IH" $! _ ps_acc' Hsubset_mb trans' Hdisj_na Hnin_rx Hnin_tx Hdom_mem_acc_tx with "regs tx pgt_tx pgt_acc pgt_acc' LB trans_hpool_global
                            tran_pgt_transferred retri R0z R1z rx_state rx prop0 propi tran_pgt_owned pgt_owned mem_rest mem_acc_tx mem_tx
                            Htotal_regs'").
                             }

              destruct (parse_transaction_descriptor mem_tx p_tx (Z.to_nat r1))  as [tran_des|] eqn:Heq_parse_tran.
              2:{ (* cannot parse the msg as a descriptor *)
                iApply (hvc_mem_send_invalid_msg ai with "[PC mem_instr pgt_acc' R0 R1 R2 tx mem_tx]");iFrameAutoSolve.
                exact Hdecode_hvc.
                simpl; reflexivity.
                lia.
                exact Heq_parse_tran.
                iFrame.
                iNext.
                iIntros "(PC & mem_instr & pgt_acc' & R0 & R1 & R2 & tx & mem_tx) _".
                iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[#Htotal_regs' regs]".

                iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
                iApply ("IH" $! _ ps_acc' Hsubset_mb trans' Hdisj_na Hnin_rx Hnin_tx Hdom_mem_acc_tx with "regs tx pgt_tx pgt_acc pgt_acc' LB trans_hpool_global
                            tran_pgt_transferred retri R0z R1z rx_state rx prop0 propi tran_pgt_owned pgt_owned mem_rest mem_acc_tx mem_tx Htotal_regs'").
              }

              destruct (validate_transaction_descriptor i Sharing tran_des) eqn:Hvalid_tran_des.
              2:{ (* validation of descriptor fails, apply [hvc_mem_send_invalid_des] *)
                iApply (hvc_mem_send_invalid_des ai with "[PC mem_instr pgt_acc' R0 R1 R2 tx mem_tx]");iFrameAutoSolve.
                exact Hdecode_hvc.
                simpl; reflexivity.
                lia.
                exact Heq_parse_tran.
                done.
                iFrame.
                iNext.
                iIntros "(PC & mem_instr & pgt_acc' & R0 & R1 & R2 & tx & mem_tx) _".
                iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[#Htotal_regs' regs]".

                iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
                iApply ("IH" $! _ ps_acc' Hsubset_mb trans' Hdisj_na Hnin_rx Hnin_tx Hdom_mem_acc_tx with "regs tx pgt_tx pgt_acc pgt_acc' LB trans_hpool_global
                            tran_pgt_transferred retri R0z R1z rx_state rx prop0 propi tran_pgt_owned pgt_owned mem_rest mem_acc_tx mem_tx Htotal_regs'").
              }

              pose proof (Hvalid_tran_des) as Hvalid_trans_des'.
              apply validate_descriptor_share in Hvalid_tran_des as [j [ps_share [-> Hneq_sr]]].
              destruct (decide (ps_share ⊆ ps_acc')) as [Hsubseteq_share | Hnsubseteq_share].
              2:{ (* no access to at least one page in ps_share, apply [hvc_mem_send_not_acc] *)
                apply not_subseteq in Hnsubseteq_share as [p [Hin_p_share Hnin_p_acc]].
                iDestruct (access_split with "[$ pgt_acc $ pgt_acc' ]") as "pgt_acc".
                iApply (hvc_mem_send_not_acc ai p with "[PC mem_instr pgt_acc R0 R1 R2 tx mem_tx]");iFrameAutoSolve.
                exact Hdecode_hvc.
                simpl; reflexivity.
                lia.
                exact Heq_parse_tran.
                done.
                simpl; exact Hin_p_share.
                iFrame.
                iNext.
                iIntros "(PC & mem_instr  & R0 & R1 & R2 & tx & mem_tx & pgt_acc) _".
                iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[#Htotal_regs' regs]".
                iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
                iDestruct (access_split with "pgt_acc") as "[pgt_acc pgt_acc']".

                iApply ("IH" $! _ ps_acc' Hsubset_mb trans' Hdisj_na Hnin_rx Hnin_tx Hdom_mem_acc_tx with "regs tx pgt_tx pgt_acc pgt_acc' LB trans_hpool_global
                            tran_pgt_transferred retri R0z R1z rx_state rx prop0 propi tran_pgt_owned pgt_owned mem_rest mem_acc_tx mem_tx Htotal_regs'").
              }
              destruct (decide (p_tx ∈ ps_share)) as [Hin_ptx_share | Hnin_ptx_share].
              { (* tx is not owned by i, apply [hvc_mem_send_not_owned] *)
                iDestruct "pgt_tx" as "[own_tx excl_tx]".
                iApply (hvc_mem_send_not_owned ai _ (p_tx -@O> -)%I with "[PC mem_instr pgt_acc' R0 R1 R2 tx mem_tx own_tx]");iFrameAutoSolve.
                exact Hdecode_hvc.
                simpl; reflexivity.
                lia.
                exact Heq_parse_tran.
                done.
                simpl; exact Hin_ptx_share.
                iFrame.
                iNext.
                iIntros "?".
                iLeft;done.
                iNext.
                iIntros "(PC & mem_instr & pgt_acc' & R0 & R1 & R2 & tx & mem_tx & own_tx) _".
                iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[#Htotal_regs' regs]".

                iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
                iApply ("IH" $! _ ps_acc' Hsubset_mb trans' Hdisj_na Hnin_rx Hnin_tx Hdom_mem_acc_tx with "regs tx [$own_tx $excl_tx] pgt_acc pgt_acc' LB trans_hpool_global
                            tran_pgt_transferred retri R0z R1z rx_state rx prop0 propi tran_pgt_owned pgt_owned mem_rest mem_acc_tx mem_tx Htotal_regs'").
              }

              destruct (decide (p_rx ∈ ps_share)) as [Hin_prx_share | Hnin_prx_share].
              { (* rx is not owned by i, apply [hvc_mem_send_not_owned] *)
                iDestruct "rx" as "[rx [own_rx excl_rx]]".
                iApply (hvc_mem_send_not_owned ai _ (p_rx -@O> -)%I with "[PC mem_instr pgt_acc' R0 R1 R2 tx mem_tx own_rx]");iFrameAutoSolve.
                exact Hdecode_hvc.
                simpl; reflexivity.
                lia.
                exact Heq_parse_tran.
                done.
                simpl; exact Hin_prx_share.
                iFrame.
                iNext.
                iIntros "?".
                iLeft;done.
                iNext.
                iIntros "(PC & mem_instr & pgt_acc' & R0 & R1 & R2 & tx & mem_tx & own_rx) _".
                iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[#Htotal_regs' regs]".

                iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
                iApply ("IH" $! _ ps_acc' Hsubset_mb trans' Hdisj_na Hnin_rx Hnin_tx Hdom_mem_acc_tx with "regs tx pgt_tx pgt_acc pgt_acc' LB trans_hpool_global
                            tran_pgt_transferred retri R0z R1z rx_state [$rx $own_rx $excl_rx] prop0 propi tran_pgt_owned pgt_owned mem_rest mem_acc_tx mem_tx Htotal_regs'").
              }

              assert (Hsubseteq_share' : ps_share ⊆ ps_acc' ∖ {[p_rx;p_tx]}).
              { set_solver + Hsubseteq_share Hnin_ptx_share Hnin_prx_share. }
              clear Hsubseteq_share Hnin_ptx_share Hnin_prx_share.

              iDestruct "trans_hpool_global" as (hpool) "(%Heq_hsall & fresh_handles & trans)".
              destruct (decide (ps_share ⊆ ps_acc' ∖ {[p_rx; p_tx]} ∖ ps_mem_in_trans)) as [Hsubseteq_share | Hnsubseteq_share].
              { (* all pages are exclusively owned, ok to perceed *)
                iDestruct (fresh_handles_disj with "[$fresh_handles trans]") as "%Hdisj_hpool".
                { iDestruct (big_sepM_sep with "trans") as "[$ _]". }
                iDestruct (access_split with "[$ pgt_acc $ pgt_acc' ]") as "pgt_acc".
                iDestruct (big_sepS_union_acc _ ps_share with "pgt_owned") as "[pgt_oe_share Hacc_pgt_oe]";auto.
                destruct (decide (hpool = ∅)).
                { (* no avaiable fresh handles, apply [hvc_mem_share_no_fresh_handles] *)
                  iApply (hvc_mem_share_no_fresh_handles ai hpool j mem_tx ps_share with "[PC mem_instr pgt_acc pgt_oe_share R0 R1 R2 fresh_handles tx mem_tx]");iFrameAutoSolve.
                  exact Hdecode_hvc.
                  simpl; reflexivity.
                  lia.
                  intro;apply Hneq_sr,symmetry;done.
                  set_solver + Hsubseteq_share'.
                  iFrame.
                  iNext. iIntros "(PC & mem_instr & pgt_oe_share & pgt_acc & R0 & R1 & R2 & fresh_handles & tx & mem_tx ) _".
                  iDestruct ("Hacc_pgt_oe" $! ps_share with "[] pgt_oe_share") as "pgt_owned".
                  { iPureIntro;set_solver +. }

                  iDestruct ("Hacc_regs" $! (ai ^+ 1)%f _ _ _ with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[#Htotal_regs' regs]".
                  iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
                  iDestruct (access_split with "pgt_acc") as "[pgt_acc pgt_acc']".
                  iApply ("IH" $! _ ps_acc' Hsubset_mb trans' Hdisj_na Hnin_rx Hnin_tx Hdom_mem_acc_tx with "regs tx pgt_tx pgt_acc pgt_acc' LB [fresh_handles trans]
                            tran_pgt_transferred retri R0z R1z rx_state rx prop0 propi tran_pgt_owned [pgt_owned] mem_rest mem_acc_tx mem_tx Htotal_regs'").
                  {
                    iExists hpool.
                    by iFrame.
                  }
                  {
                    pose proof (union_split_difference_intersection_subseteq_L _ _ Hsubseteq_share) as [<- _].
                    iFrame.
                  }
                }
                iApply (hvc_mem_share_nz ai j mem_tx hpool ps_share with "[PC mem_instr pgt_acc pgt_oe_share R0 R1 R2 fresh_handles tx mem_tx]");iFrameAutoSolve.
                exact Hdecode_hvc.
                simpl; reflexivity.
                lia.
                intro;apply Hneq_sr,symmetry;done.
                set_solver + Hsubseteq_share'.
                iFrame.
                iNext. iIntros "(PC & mem_instr & pgt_oe_share & pgt_acc & R0 & R1 & (%wh & %Hin_wh & R2 & tran_share & retri_share & fresh_handles) & tx & mem_tx ) _".
                iDestruct ("Hacc_pgt_oe" $! ∅ with "[] []") as "pgt_owned".
                { iPureIntro. set_solver +. }
                { rewrite big_sepS_empty //. }

                iDestruct ("Hacc_regs" $! (ai ^+ 1)%f _ _ _ with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[#Htotal_regs' regs]".
                iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
                iDestruct (access_split with "pgt_acc") as "[pgt_acc pgt_acc']".

                (* we will specialize IH with the new [trans''] *)
                pose (<[ wh := (i, W0, j, ps_share, Sharing, false) ]>trans') as trans''.
                assert (Hlookup_wh_None: trans' !! wh = None).
                rewrite -not_elem_of_dom.
                set_solver + Hin_wh Hdisj_hpool.

                assert (ps_share ∪ pages_in_trans (trans_memory_in_trans i trans') = pages_in_trans (trans_memory_in_trans i trans'')) as Hrewrite.
                {
                  rewrite /trans'' /trans_memory_in_trans.
                  rewrite map_filter_insert_True.
                  rewrite /pages_in_trans map_fold_insert_L /=.
                  f_equal.
                  intros.
                  set_solver +.
                  rewrite map_filter_lookup_None.
                  eauto.
                  simpl.
                  left.
                  split;auto.
                  intro.
                  destruct H as [H []].
                  inversion H.
                }

                iDestruct (trans_split with "tran_share") as "[tran_share tran_share']".
                iDestruct (pgt_split with "pgt_oe_share") as "[pgt_oe_share pgt_oe_share']".

                iApply ("IH" $! _ ps_acc' Hsubset_mb trans'' with "[] [] [] [] regs tx pgt_tx pgt_acc pgt_acc' LB [fresh_handles tran_share trans pgt_oe_share] [tran_pgt_transferred] [retri retri_share] R0z R1z rx_state rx prop0 propi [tran_pgt_owned tran_share' pgt_oe_share'] [pgt_owned] [mem_rest] mem_acc_tx mem_tx Htotal_regs'");iClear "IH".
                {
                  rewrite -Hrewrite.
                  rewrite union_assoc_L.
                  assert (ps_acc' ∪ ps_share = ps_acc') as ->.
                  symmetry.
                  rewrite union_comm_L.
                  rewrite subseteq_union_1_L;auto.
                  set_solver + Hsubseteq_share'.
                  done.
                }
                {
                  rewrite -Hrewrite.
                  rewrite union_assoc_L.
                  assert (ps_acc' ∖ {[p_rx; p_tx]} ∪ ps_share = ps_acc' ∖ {[p_rx; p_tx]}) as ->.
                  rewrite union_comm_L.
                  rewrite subseteq_union_1_L;auto.
                  done.
                }
                {
                  rewrite -Hrewrite.
                  rewrite union_assoc_L.
                  assert (ps_acc' ∖ {[p_rx; p_tx]} ∪ ps_share = ps_acc' ∖ {[p_rx; p_tx]}) as ->.
                  rewrite union_comm_L.
                  rewrite subseteq_union_1_L;auto.
                  done.
                }
                done.
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
                  simpl.
                  case_bool_decide;done.
                }
                {
                  rewrite /transaction_pagetable_entries_transferred.
                  iApply (big_sepFM_lookup_None_False with "tran_pgt_transferred"); auto.
                  simpl.
                  intros [H _];inversion H.
                }
                {
                  rewrite /retrieval_entries .
                  iDestruct (retri_split with "retri_share") as "[retri_share retri_share']".
                  iDestruct "retri" as "[retri1 retri2]".
                  iSplitL "retri1 retri_share".
                  iApply (big_sepFM_lookup_None_True with "retri1"); auto.
                  simpl;eauto.
                  iApply (big_sepFM_lookup_None_True with "retri2"); auto.
                  simpl;eauto.
                }
                {
                  rewrite /transaction_pagetable_entries_owned.
                  iApply (big_sepFM_lookup_None_True with "tran_pgt_owned"); auto.
                  simpl;eauto.
                  case_bool_decide.
                  simpl in H. done.
                  iFrame.
                }
                {
                  rewrite union_empty_r_L.
                  rewrite /pagetable_entries_excl_owned /pgt.
                  rewrite union_comm_L in Hrewrite.
                  rewrite -Hrewrite.
                  rewrite difference_difference_L.
                  iFrame.
                }
                {
                 rewrite -Hrewrite.
                 rewrite difference_union_distr_l_L.
                 assert (ps_share ∖ (ps_acc' ∖ {[p_tx]}) = ∅) as ->.
                 set_solver + Hsubseteq_share'.
                 rewrite union_empty_l_L //.
                }
              }
              { (* at least one page is not exclusively owned by i (i.e. is involved in a transaction) *)
                assert (∃ p, p ∈ ps_share ∧ p ∈ ps_mem_in_trans) as [p [Hin_p_share Hin_p_mem_in_trans]].
                { apply (not_subseteq_diff _ (ps_acc' ∖ {[p_rx; p_tx]}));auto. }
                apply elem_of_pages_in_trans in  Hin_p_mem_in_trans as [h [tran [Hlookup_tran Hin_p_tran]]].
                apply map_filter_lookup_Some in Hlookup_tran as [Hlookup_tran Htran_prop].
                iDestruct (big_sepM_lookup_acc with "trans") as "[[tran_tran pgt_tran] Hacc_trans]";first exact Hlookup_tran.
                (* XXX: Can we also apply [not_owned]/[not_excl]? this iApply is noticeable slow *)
                iApply (hvc_mem_send_in_trans ai p h with "[PC mem_instr pgt_acc' R0 R1 R2 tx mem_tx tran_tran]");iFrameAutoSolve.
                exact Hdecode_hvc.
                simpl; reflexivity.
                lia.
                exact Heq_parse_tran.
                done.
                simpl; exact Hin_p_share.
                iFrame.
                iNext.
                iIntros "(PC & mem_instr & pgt_acc' & R0 & R1 & R2 & tx & mem_tx & tran_tran) _".
                iDestruct ("Hacc_regs" $! (ai ^+ 1)%f with "[$ PC $ R0 $ R1 $ R2]") as (regs') "[#Htotal_regs' regs]".
                iDestruct ("Hacc_mem_acc_tx" with "[$mem_instr]") as "mem_acc_tx".
                iDestruct ("Hacc_trans" with "[$ tran_tran $ pgt_tran]") as "trans".

                iApply ("IH" $! _ ps_acc' Hsubset_mb trans' Hdisj_na Hnin_rx Hnin_tx Hdom_mem_acc_tx with "regs tx pgt_tx pgt_acc pgt_acc' LB [fresh_handles trans]
                            tran_pgt_transferred retri R0z R1z rx_state rx prop0 propi tran_pgt_owned pgt_owned mem_rest mem_acc_tx mem_tx Htotal_regs'").
                iExists hpool;by iFrame.
              }
            }
            { (*Lend*) admit. }
            { (*Donate*) admit. }
            { (*TODO: Retrieve*)
              pose proof (Htotal_regs R1) as[r1 Hlookup_reg_R1].
              pose proof (Htotal_regs R2) as[r2 Hlookup_reg_R2].
              iDestruct (reg_big_sepM_split_upd4 i Hlookup_PC Hlookup_reg_R0 Hlookup_reg_R1 Hlookup_reg_R2 with "[$regs]")
                as "(PC & R0 & R1 & R2 & Hacc_regs)";eauto.

              iDestruct "rx" as "[rx pgt_rx]".

              iDestruct (access_split with "[$pgt_acc $pgt_acc']") as "pgt_acc".
              
              iDestruct "trans_hpool_global" as (hpool) "(%Heq_hsall & fresh_handles & trans)".
              destruct (decide (r1 ∈ hs_all)) as [Hin_hs_all |Hnotin_hs_all].
              2: { (* apply [hvc_mem_retrieve_invalid_handle] *)
                admit.
              }
              destruct (decide (r1 ∈ hpool)) as [Hin_hpool | Hnotin_hpool].
              { (* apply [hvc_mem_retrieve_fresh_handle] *)
                admit.
              }
              assert(r1 ∈ dom (gset _ ) trans') as Hin_trans_dom.
              {
                rewrite -Heq_hsall in Hin_hs_all.
                rewrite elem_of_union in Hin_hs_all.
                destruct Hin_hs_all;first contradiction.
                done.
              }
              apply elem_of_dom in Hin_trans_dom as [tran Hlookup_tran].
              iDestruct (big_sepM_lookup_acc _ trans' _  _ Hlookup_tran with "trans") as "((tran & pgt_tran) & Hacc_trans)".

              destruct(decide (tran.1.1.1.2 = i)) as [Heq_tran | Hneq_tran].
              2: { (*apply [hvc_mem_retrieve_invalid_trans]*)
                admit.
              }

              iDestruct ("retri") as "[retri retri']".
              iDestruct (big_sepFM_lookup_Some_acc Hlookup_tran with "retri") as "[re Hacc_retri]".
              simpl;left;done.


              destruct (tran.2) eqn:Heq_retri.
              { (* apply [hvc_mem_retrieve_retrieved] *)
                admit.
              }

              iDestruct (big_sepFM_lookup_Some_acc Hlookup_tran with "retri'") as "[re' Hacc_retri']".
              simpl;left;split;done.
              rewrite Heq_retri.
              iDestruct (retri_split with "[$re $re']") as "re".
              destruct (rx_state')  eqn: Heq_rxstate.
              { (* apply [hvc_mem_retrieve_rx_full] *)
                admit.
              }

              assert (tran.1.1.2 ⊆ ps_mem_in_trans) as Hsubseteq_tran.
              {
                rewrite elem_of_subseteq.
                intros p Hin_p.
                rewrite /ps_mem_in_trans.
                rewrite elem_of_pages_in_trans.
                exists r1, tran.
                split;last auto.
                rewrite map_filter_lookup_Some;split;first done.
                simpl. right;done.
              }

              assert (p_rx ∈ ps_acc' ∖ {[p_tx]}) as Hin_ps_acc_tx'. set_solver + Hsubset_mb Hneq_mb.
              iDestruct (memory_pages_split_singleton p_rx _ Hin_ps_acc_tx') as "[Hsplit _]".
              iDestruct ("Hsplit" with "[mem_acc_tx]") as (mem_acc_tx_rx mem_rx) "[[%Hdom_mem_acc_tx_rx mem_acc_tx_rx] [mem_rx %Heq_mem_acc_tx]]".
              {
                rewrite /memory_pages.
                iSplitL "".
                iPureIntro.
                apply Hdom_mem_acc_tx.
                iFrame.
              }
              iClear "Hsplit".
              (* pose proof (union_split_difference_intersection_subseteq_L (ps_acc' ∖ {[p_tx]}) {[p_rx]}) as [Heq_ps_acc_tx Hdisj_ps_acc_tx]. *)
              (* set_solver + Hin_ps_acc_tx'. *)
              (* rewrite Heq_ps_acc_tx in Hin_ps_acc_tx. *)
              (* rewrite elem_of_union in Hin_ps_acc_tx. *)
              rewrite -Heq_mem_acc_tx in Hlookup_mem_ai.
              rewrite lookup_union_Some in Hlookup_mem_ai.

              destruct (tran.1.2) eqn:Heq_tran_tt.
              { (*apply [hvc_mem_retrieve_donate]*)
                iDestruct (big_sepFM_lookup_Some_acc Hlookup_tran with "tran_pgt_transferred") as "[[tran' pgt_tran'] Hacc_tran_pgt_transf]".
                simpl. split;first done. left;done.
                iDestruct (trans_split with "[$tran $tran']") as "tran".
                rewrite Heq_tran_tt.
                case_bool_decide;last done;clear H.
                iDestruct (pgt_split with "[$pgt_tran $pgt_tran']") as "pgt_tran".
                iDestruct (big_sepS_sep with "pgt_tran") as "[own_tran excl_tran]".

                destruct Hlookup_mem_ai as [Hlookup_mem_ai|Hlookup_mem_ai].
                {

                iDestruct (mem_big_sepM_split mem_acc_tx_rx Hlookup_mem_ai with "mem_acc_tx_rx") as "[mem_instr Hacc_mem_acc_tx]".

                assert(tran.1 = (tran.1.1.1.1.1, tran.1.1.1.1.2, i, tran.1.1.2, Donation)) as ?.
                {
                  rewrite -Heq_tran_tt.
                  rewrite -Heq_tran.
                  repeat destruct tran as [tran ?]. simpl. done.
                }
                rewrite H.

                iApply (hvc_mem_retrieve_donate ai r1 with "[$PC $mem_instr $R0 $R1 own_tran $pgt_acc $re $tran $rx $rx_state $mem_rx $fresh_handles]").
                set_solver + Hin_ps_acc_tx.
                done.

                iFrameAutoSolve.
                6: { rewrite H. simpl. iFrame. }
                6: { iFrame. }
                iFrameAutoSolve.
                }

                
                admit.
              }
              { (*apply [hvc_mem_retrieve_share]*)
                admit.
              }
              { (*apply [hvc_mem_retrieve_lend]*)
                admit.
              }
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
