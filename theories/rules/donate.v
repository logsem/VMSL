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
      rewrite HSomeperm.
      pose proof (Hexcl x HxInexcl) as Hxexcl.
      simpl in Hxexcl.
      destruct Hxexcl as [perm' [HSomeperm' Hisexcl]].
      rewrite HSomeperm in HSomeperm'.
      inversion HSomeperm'.
      subst perm'.
      clear HSomeperm HSomeperm'.
      destruct (decide ((Owned, ExclusiveAccess) = perm)) eqn:Heqn.
      rewrite Heqn //.
      rewrite /is_owned in Hisowned.
      rewrite /is_exclusive in Hisexcl.
      exfalso.
      apply n.
      destruct perm.
      destruct o, a;try done.
    }
    rewrite /new_transaction /fresh_handle in Heqc2.
    set (allfhs:= (get_fresh_handles (get_transactions σ1))) in *.
    destruct allfhs.
    { exfalso. apply Hshne. set_solver. }
    rewrite //=  /update_page_table in Heqc2.
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp /update_incr_PC /update_reg.    (* unchanged part *)
    rewrite_reg_all.
    rewrite Hcur.
    iFrame.
    (* updated part *)
Admitted.

End donate.
