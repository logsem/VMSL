From machine_program_logic.program_logic Require Import machine weakestpre.
From HypVeri Require Import RAs transaction rule_misc lifting rules.rules_base.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import gset.
Require Import stdpp.fin.

Section donate.

Context `{vmG: !gen_VMG Σ}.

Lemma hvc_donate_nz {instr i wi r2 pi ptx sown q sacc sexcl q' des qh sh} {l :Word} {spsd: gset PID}
      ai r0 r1 j (psd: list PID) :
  (* the current instruction is hvc *)
  instr = Hvc ->
  (* the decoding of wi is correct *)
  decode_instruction wi = Some(instr) ->
  (* the instruction is in page pi *)
  addr_in_page ai pi ->
  (* the decoding of R0 is FFA_DONATE *)
  decode_hvc_func r0 = Some(Donate) ->
  (* caller is not the receiver *)
  i ≠ j ->
  (* l is the number of to-be-donated pages *)
  (finz.to_z l) = (Z.of_nat (length psd)) ->
  (* the descriptor, in list Word *)
  des = serialized_transaction_descriptor i j W0 l psd W0 ->
  (* the whole descriptor resides in the TX page *)
  seq_in_page (of_pid ptx) (length des) ptx ->
  (* r1 equals the length of the descriptor *)
  (finz.to_z r1) = (Z.of_nat (length des)) ->
  (* spsd is the gset of all to-be-donated pages *)
  spsd = (list_to_set psd) ->
  (* pi and pages in spsd are accessible for VM i *)
  {[pi]} ∪ spsd ⊆ sacc ->
  (* VM i owns pages in spsd *)
  spsd ⊆ sown ->
  (* pages in spsed are exclusive to VM i *)
  spsd ⊆ sexcl ->
  (* there are at least one free handles in the hpool *)
  sh ≠ ∅ ->
  {SS{{ ▷(PC @@ i ->r ai) ∗ ▷ ai ->a wi
  ∗ ▷ O@i:={q}[sown] ∗ ▷ A@i:={1}[sacc] ∗ ▷ E@i:={q'}[sexcl]
  ∗ ▷ (R0 @@ i ->r r0) ∗ ▷ (R1 @@ i ->r r1) ∗ ▷(R2 @@i ->r r2) ∗  ▷ TX@ i := ptx
  ∗ ▷ mem_region des ptx
  ∗ ▷ hp{ qh }[ (GSet sh)] }}}
   ExecI @ i {{{ RET ExecI ; PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi
  ∗ O@i:={q}[sown] ∗ A@i:={1}[sacc∖spsd] ∗ E@i:={q'}[sexcl∖spsd]
  ∗ R0 @@ i ->r (encode_hvc_ret_code Succ) ∗ R1 @@ i ->r r1  ∗ TX@ i := ptx
  ∗ ∃(wh: Word), ( ⌜ wh ∈ sh ⌝ ∗ R2 @@ i ->r wh ∗ wh ->t{1}(i,W0, j , psd,Donation)
  ∗ wh ->re false ∗ R2 @@ i ->r wh ∗ hp{qh}[(GSet (sh∖{[wh]}))] )
  ∗ mem_region des ptx}}}.
Proof.
  iIntros (Hinstr Hdecodei Hini Hdecodef Hneq Hlenpsd Hdesc Hindesc Hlenr1 Hspsd Hsacc Hsown Hsexcl Hshne Φ ).
  iIntros "(>PC & >Hai & >Hown & >Hacc & >Hexcl & >R0 & >R1 & >R2 & >TX & >Hadesc & >Hhp ) HΦ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [ Hcureq ]; clear Hsche.
  apply fin_to_nat_inj in Hcureq.
  iModIntro.
  iDestruct "Hσ" as "(Hcur & Hσmem & Hσreg & Hσtx & ? & Hσowned & Hσaccess & Hσexcl & Htrans & Hσhp & Hrcv)".
  (* valid regs *)
  iDestruct ((gen_reg_valid4 σ1 i PC ai R0 r0 R1 r1 R2 r2 Hcureq ) with "Hσreg PC R0 R1 R2 ")
    as "[%HPC [%HR0 [%HR1 %HR2]]]";eauto.
  (* valid pt *)
  iDestruct ((gen_access_valid_addr_elem ai sacc) with "Hσaccess Hacc") as %Haccai;eauto.
  { rewrite (to_pid_aligned_in_page _ pi);eauto. set_solver. }
  iDestruct ((gen_access_valid_lookup_Set _ _ _ sacc) with "Hσaccess Hacc") as %Hacc;eauto.
  iDestruct ((gen_own_valid_Set sown) with "Hσowned Hown") as %Hown;eauto.
  iDestruct ((gen_excl_valid_Set sexcl) with "Hσexcl Hexcl") as %Hexcl;eauto.
  (* valid mem *)
  iDestruct (gen_mem_valid σ1 ai wi with "Hσmem Hai") as %Hai.
  unfold mem_region.
  iDestruct (gen_mem_valid_SepL_pure _ des with "Hσmem Hadesc") as %Hadesc.
  { apply finz_seq_NoDup. destruct Hindesc as [? [HisSome ?]]. done. }
  (* valid tx *)
  iDestruct (gen_tx_valid with "TX Hσtx") as %Htx.
  (* valid hpool *)
  iDestruct (gen_hpool_valid with "Hhp Hσhp") as %Hhp.
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal i instr ai wi);eauto.
  - (* step *)
    iModIntro.
    iIntros (m2 σ2) "%HstepP".
    apply (step_ExecI_normal i instr ai wi) in HstepP;eauto.
    remember (exec instr σ1) as c2 eqn:Heqc2.
    assert (Hlendesclt :((Z.of_nat (length des)) <= (page_size-1))%Z).
    {  destruct Hindesc as [? [HisSome Hltpagesize]]. apply (finz_plus_Z_le (of_pid ptx));eauto.
       apply last_addr_in_bound.  apply Z.leb_le. destruct (((ptx ^+ length des)%f <=? (ptx ^+ (page_size - 1))%f)%Z). done. contradiction. }
    rewrite /exec Hinstr /hvc HR0 Hdecodef /mem_send //= HR1 /= in Heqc2.
    destruct (page_size <? r1)%Z eqn:Heqn;[lia|clear Heqn].
    rewrite Hcureq /get_tx_pid_global Htx (@transaction_descriptor_valid i j W0 l psd σ1 des) /= in Heqc2;eauto.
    assert (Hcheck : (i =? i) = true).
    { by apply   <- Nat.eqb_eq. }
    rewrite Hcureq Hcheck /= in Heqc2;clear Hcheck.
    assert (Hcheck:  negb (i =? j) = true).
       {apply negb_true_iff. apply  <- Nat.eqb_neq. intro. apply Hneq. by apply fin_to_nat_inj.  }
    rewrite Hcheck /= in Heqc2;clear Hcheck.
    destruct (forallb (λ v' : PID, check_perm_page σ1 i v' (Owned, ExclusiveAccess))
                                    psd) eqn:HCheck.
    2: {
      apply not_true_iff_false in HCheck.
      exfalso.
      apply HCheck.
      apply forallb_forall.
      intros.
      unfold check_perm_page.
      apply elem_of_list_In in H.
      apply (elem_of_list_to_set (C:= gset PID)) in H.
      rewrite <- Hspsd in H.
      assert (HxInown: x ∈ sown). { set_solver. }
      assert (HxInexcl: x ∈ sexcl). { set_solver. }
      pose proof (Hown x HxInown) as Hxown .
      simpl in Hxown.
      destruct Hxown as [perm [HSomeperm Hisowned]].
      rewrite /check_ownership_page  HSomeperm /=.
      destruct (decide (Owned = perm)). simpl.
      2: { exfalso. apply n. destruct perm;eauto. rewrite /is_owned //.  }
      pose proof (Hexcl x HxInexcl) as Hxexcl.
      simpl in Hxexcl.
      destruct Hxexcl as [perm' [HSomeperm' Hisexcl]].
      rewrite /check_access_page HSomeperm'.
      destruct (decide (ExclusiveAccess = perm')). done.
      exfalso. apply n. destruct perm';eauto; rewrite /is_exclusive //.
    }
    rewrite /new_transaction /fresh_handle in Heqc2.
    set (allfhs:= (get_fresh_handles (get_transactions σ1))) in *.
    destruct allfhs.
    { exfalso. apply Hshne. set_solver. }
    rewrite //=  in Heqc2.
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp /update_incr_PC /update_reg.
    (* unchanged part *)
    rewrite_reg_all.
    rewrite update_access_batch_preserve_current_vm insert_transaction_preserve_current_vm.
    rewrite_reg_all.
    rewrite_access_all.
    rewrite_trans_all.
    iFrame.
    (* update regs *)
     rewrite -> (update_offset_PC_update_PC1 _ i ai 1);eauto.
     rewrite !update_reg_global_update_reg;rewrite ?update_access_batch_preserve_regs ?insert_transaction_preserve_regs;try solve_reg_lookup.
     2 : {
        exists r2.
        rewrite lookup_insert_ne.
        solve_reg_lookup.
        done.
     }
     2 : {
        rewrite !update_reg_global_update_reg.
        rewrite ?update_access_batch_preserve_regs ?insert_transaction_preserve_regs;try solve_reg_lookup.
        rewrite !lookup_insert_ne;[solve_reg_lookup|done|done].
        rewrite ?update_access_batch_preserve_regs ?insert_transaction_preserve_regs;try solve_reg_lookup.
        rewrite ?update_access_batch_preserve_regs ?insert_transaction_preserve_regs.
        exists r2.
        rewrite lookup_insert_ne;[solve_reg_lookup|done].
        rewrite ?update_access_batch_preserve_regs ?insert_transaction_preserve_regs.
        solve_reg_lookup.
     }
     iDestruct ((gen_reg_update3_global PC i (ai ^+ 1)%f R2 i h R0 i (encode_hvc_ret_code Succ) ) with "Hσreg PC R2 R0") as ">[Hσreg [PC [R2 R0]]]";eauto.
     rewrite Hcureq.
     iFrame.
     (* update page table *)
     rewrite (@update_access_batch_noaccess _ i sacc spsd psd);eauto.
     rewrite_trans_all.
     iDestruct ((gen_access_update_noaccess spsd) with "Hacc Hσaccess") as ">[Hσaccess Hacc]";eauto.
     set_solver.
     rewrite Hcureq.
     iFrame.
     rewrite update_access_batch_preserve_ownerships insert_transaction_preserve_owned.
     iFrame.
Admitted.

End donate.
