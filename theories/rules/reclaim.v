From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base stdpp_extra.
From HypVeri.algebra Require Import base mem reg mailbox pagetable trans.
From HypVeri.lang Require Import lang_extra reg_extra mem_extra pagetable_extra trans_extra.

Section reclaim.

Context `{hypparams: HypervisorParameters}.
Context `{vmG: !gen_VMG Σ}.

Lemma hvc_reclaim wi sown qo sacc sexcl i j sh tt sacc' (spsd: gset PID)
      ai r0 wh wf (psd: list PID) :
  (* current instruction is hvc *)
  decode_instruction wi = Some(Hvc) ->
  (* the hvc call to invoke is relinquish *)
  decode_hvc_func r0 = Some(Reclaim) ->
  (* has access to the page which the instruction is in *)
  to_pid_aligned ai ∈ sacc ->
  (* the set of pids that are involved in this transaction *)
  spsd = (list_to_set psd) ->
  (* these pages are not owned *)
  spsd ⊆ sown ->
  (* these pages are not exclusively accessible *)
  spsd ## sexcl ->
  (* for lending, the sender get back access *)
  tt = Lending ∧ spsd ## sacc ∧ sacc' = sacc ∪ spsd
  (* for sharing, the sender already has access *)
  ∨ tt = Sharing ∧ spsd ⊆ sacc ∧ sacc' = sacc ->
  {SS{{(* the encoding of instruction wi is stored in location ai *)
       ▷(PC @@ i ->r ai) ∗ ▷ ai ->a wi∗
       (* the handle of transaction is stored in R1 *)
       ▷ (R0 @@ i ->r r0) ∗ ▷ (R1 @@ i ->r wh) ∗
       (* the pagetable *)
       ▷ O@i:={qo}[sown] ∗ ▷ E@i:={1}[sexcl] ∗ ▷ A@i:={1}[sacc] ∗
       (* the transaction has not been retrieved/has been relinquished *)
       ▷ wh ->re false ∗ ▷ wh ->t{1}(i, wf, j, psd, tt) ∗
       (* handle pool *)
       ▷ hp{ 1 }[ sh ] }}}
  ExecI @ i
  {{{ RET ExecI ;
      (* PC is incremented *)
      PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi ∗
      (* return Succ to R0, XXX: update R1 to 0? *)
      R0 @@ i ->r (encode_hvc_ret_code Succ) ∗ (R1 @@ i ->r wh) ∗
      (* gain access/ownership of those pages *)
      O@i:={qo}[sown] ∗ E@i:={1}[(sexcl ∪ spsd)] ∗ A@i:={1}[sacc'] ∗
      (* the transaction is deallocated, release the handle to the handle pool *)
      hp{ 1 }[ (sh ∪ {[wh]})] }}}.
Proof.
  iIntros (Hdecodei Hdecodef Hinsacc Heqpsd Hinown HHdisjexcl Htt Φ)
          "(>PC & >Hai & >R0 & >R1 & >Hown & >Hexcl & >Hacc & >Hretri & >Htrans & >Hhp) HΦ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [ Hcureq ]; clear Hsche.
  apply fin_to_nat_inj in Hcureq.
  iModIntro.
  iDestruct "Hσ" as "(Hcur & Hσmem & Hσreg & Hσtx & Hσrx1 & Hσrx2 & Hσowned & Hσaccess & Hσexcl &
                            Hσtrans & Hσhp & %Hdisj & %Hσpsdl & Hσretri)".
  (* valid regs *)
  iDestruct ((gen_reg_valid3 i PC ai R0 r0 R1 wh Hcureq) with "Hσreg PC R0 R1")
    as "(%HPC & %HR0 & %HR1)";eauto.
  (* valid pt *)
  iDestruct ((gen_access_valid_addr_elem ai sacc) with "Hσaccess Hacc") as %Haccai;eauto.
  iDestruct ((gen_access_valid_pure sacc) with "Hσaccess Hacc") as %Hacc;eauto.
  iDestruct ((gen_own_valid_pure sown) with "Hσowned Hown") as %Hown;eauto.
  iDestruct ((gen_excl_valid_pure sexcl) with "Hσexcl Hexcl") as %Hexcl;eauto.
  (* valid mem *)
  iDestruct (gen_mem_valid ai wi with "Hσmem Hai") as %Hai.
  (* valid trans *)
  iDestruct (gen_trans_valid with "Htrans Hσtrans") as %Htrans.
  (* valid hpool *)
  iDestruct (gen_hpool_valid_elem with "Hhp Hσhp") as %Hhp.
  iDestruct (gen_retri_valid with "Hretri Hσretri") as %Hretri.
  destruct Hretri as (? & Hlkwh & Hbool).
  destruct Htrans as (? & Hlkwh').
  rewrite Hlkwh in Hlkwh'.
  inversion Hlkwh';subst x;clear Hlkwh'.
  cbn in Hbool.
  subst x0.
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal i Hvc ai wi);eauto.
  - iModIntro.
    iIntros (m2 σ2) "%HstepP".
    apply (step_ExecI_normal i Hvc ai wi) in HstepP;eauto.
    remember (exec Hvc σ1) as c2 eqn:Heqc2.
    rewrite /exec /hvc HR0 Hdecodef /reclaim //= HR1 //=in Heqc2.
    rewrite /get_transaction Hlkwh //= in Heqc2.
    rewrite /no_borrowers /get_transaction Hlkwh //= in Heqc2.
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp /update_incr_PC /update_reg.
    rewrite_reg_pc.
    rewrite_reg_global.
    rewrite_access_all.
    rewrite_ownership_all.
    rewrite_trans_remove.
    iFrame "Hcur Hσmem Hσtx Hσrx1 Hσrx2".
    (* update regs *)
    rewrite -> (update_offset_PC_update_PC1 _ i ai 1);eauto.
    rewrite update_reg_global_update_reg update_access_batch_preserve_regs
             remove_transaction_preserve_regs;try solve_reg_lookup.
    2 : {
     rewrite update_reg_global_update_reg.
     rewrite update_access_batch_preserve_regs
             remove_transaction_preserve_regs;try solve_reg_lookup.
     rewrite lookup_insert_ne.
     solve_reg_lookup.
     done.
     exists r0.
     rewrite update_access_batch_preserve_regs
             remove_transaction_preserve_regs;try solve_reg_lookup.
    }
    rewrite Hcureq.
    iDestruct ((gen_reg_update2_global PC i _ (ai ^+ 1)%f R0 i _ (encode_hvc_ret_code Succ)) with "Hσreg PC R0")
      as ">[Hσreg [PC R0]]";eauto.
    iFrame "Hσreg".
    (* update pt *)
    rewrite update_access_batch_preserve_ownerships.
    rewrite remove_transaction_preserve_owned.
    iFrame "Hσowned".
    rewrite (@update_exclusive_batch_update_pagetable_union _ _ i sexcl spsd psd Heqpsd); f_equal;eauto.
    rewrite remove_transaction_preserve_excl.
    iDestruct ((gen_excl_update_union spsd) with "Hexcl Hσexcl") as ">[Hσexcl Hexcl]"; f_equal.
    { exact Heqpsd. }
    iFrame "Hσexcl".
    (* update trans *)
    rewrite remove_transaction_update_trans
            remove_transaction_update_retri remove_transaction_update_hpool.
    rewrite /remove_transaction //=.
    iDestruct (gen_trans_update_delete with "Htrans Hσtrans") as ">Hσtrans".
    iDestruct (gen_retri_update_delete with "Hretri Hσretri") as ">Hσretri".
    iFrame "Hσtrans Hσretri".
    assert (Hnotinwh: wh ∉ (get_transactions σ1).2).
    {
     assert (HisSomewh: is_Some((get_transactions σ1).1 !! wh)). eexists;exact Hlkwh.
     apply (elem_of_dom) in HisSomewh.
     set_solver.
    }
    iDestruct ((gen_hpool_update_union wh) with "Hhp Hσhp") as ">[Hσhp Hhp]".
    rewrite /get_hpool_gset //.
    iFrame.
    destruct Htt as [(-> & Hsacc & ->)|(-> & Hsacc & ->)].
    {
    rewrite (@update_access_batch_update_pagetable_union _ _ i sacc ExclusiveAccess spsd psd Heqpsd); f_equal;eauto.
    rewrite remove_transaction_preserve_access.
    iDestruct ((gen_access_update_union spsd) with "Hacc Hσaccess") as ">[Hσaccess Hacc]"; f_equal.
    { exact Heqpsd. }
    iFrame "Hσaccess".
    (* pure *)
    iModIntro.
    iSplitR.
    iPureIntro.
    split.
    set_solver.
    intro.
    intros ? Hdelete.
    apply lookup_delete_Some in Hdelete.
    destruct Hdelete as [_ Hlk].
    apply (Hσpsdl i0 _ Hlk).
    iApply "HΦ".
    iFrame.
    }
    {
     rewrite (@update_access_batch_update_pagetable_idempotent _ _ i sacc ExclusiveAccess spsd psd);auto.
     rewrite remove_transaction_preserve_access.
     iFrame "Hσaccess".
     (* pure *)
     iModIntro.
     iSplitR.
     iPureIntro.
     split.
     set_solver.
     intro.
     intros ? Hdelete.
     apply lookup_delete_Some in Hdelete.
     destruct Hdelete as [_ Hlk].
     apply (Hσpsdl i0 _ Hlk).
     iApply "HΦ".
     iFrame.
    }
Qed.


Lemma hvc_reclaim_lend {wi sown qo sexcl i j sh ai r0}
        sacc  wh wf (psd: list PID) (spsd: gset PID):
  decode_instruction wi = Some(Hvc) ->
  decode_hvc_func r0 = Some(Reclaim) ->
  to_pid_aligned ai ∈ sacc ->
  spsd = (list_to_set psd) ->
  spsd ⊆ sown ->
  spsd ## sacc ->
  spsd ## sexcl ->
  {SS{{ ▷(PC @@ i ->r ai) ∗ ▷ (R0 @@ i ->r r0) ∗ ▷ (R1 @@ i ->r wh)
  ∗ ▷ ai ->a wi ∗ ▷ hp{ 1 }[ sh ] 
  ∗ ▷ wh ->re false ∗ ▷ wh ->t{1}(i, wf, j, psd, Lending)
  ∗ ▷ O@i:={qo}[sown] ∗ ▷ E@i:={1}[sexcl] ∗ ▷ A@i:={1}[sacc] }}}
   ExecI @ i {{{ RET ExecI ; PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi
   ∗ R0 @@ i ->r (encode_hvc_ret_code Succ) ∗ R1 @@i ->r wh
  ∗ O@i:={qo}[sown] ∗ E@i:={1}[(sexcl ∪ spsd)] ∗ A@i:={1}[(sacc ∪ spsd)]
 ∗ hp{ 1 }[ (sh ∪ {[wh]})] }}}.
Proof.
  iIntros (Hdecodei Hdecodef Hinsacc Heqpsd Hdisjown Hdisjacc HHdisjexcl Φ)
          "(>PC & >R0 & >R1 & >Hai & >Hhp & >Hretri & >Htrans & >Hown & >Hexcl & >Hacc)".
  iApply (hvc_reclaim wi sown qo sacc sexcl i j sh Lending (sacc ∪ spsd) spsd ai r0 wh wf psd);auto.
  iFrame.
Qed.


Lemma hvc_reclaim_share {wi sown qo sexcl i j sh ai r0}
        sacc  wh wf (psd: list PID) (spsd: gset PID) :
  decode_instruction wi = Some(Hvc) ->
  decode_hvc_func r0 = Some(Reclaim) ->
  to_pid_aligned ai ∈ sacc ->
  spsd = (list_to_set psd) ->
  spsd ⊆ sown ->
  spsd ⊆ sacc ->
  spsd ## sexcl ->
  {SS{{ ▷(PC @@ i ->r ai) ∗ ▷ (R0 @@ i ->r r0) ∗ ▷ (R1 @@ i ->r wh)
  ∗ ▷ ai ->a wi ∗ ▷ hp{ 1 }[ sh ]
  ∗ ▷ wh ->re false ∗ ▷ wh ->t{1}(i, wf, j, psd, Sharing)
  ∗ ▷ O@i:={qo}[sown] ∗ ▷ E@i:={1}[sexcl] ∗ ▷ A@i:={1}[sacc] }}}
   ExecI @ i {{{ RET ExecI ; PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi
  ∗ R0 @@ i ->r (encode_hvc_ret_code Succ) ∗ R1 @@i ->r wh
  ∗ O@i:={qo}[sown] ∗ E@i:={1}[(sexcl ∪ spsd)] ∗ A@i:={1}[sacc]
  ∗ hp{ 1 }[ (sh ∪ {[wh]})] }}}.
Proof.
  iIntros (Hdecodei Hdecodef Hinsacc Heqpsd Hdisjown Hdisjacc HHdisjexcl Φ)
          "(>PC & >R0 & >R1 & >Hai & >Hhp & >Hretri & >Htrans & >Hown & >Hexcl & >Hacc)".
  iApply (hvc_reclaim wi sown qo sacc sexcl i j sh Sharing sacc spsd ai r0 wh wf psd);auto.
  iFrame.
Qed.

End reclaim.
