From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base stdpp_extra.
From HypVeri.algebra Require Import base mem reg pagetable mailbox trans.
From HypVeri.lang Require Import lang_extra reg_extra mem_extra pagetable_extra trans_extra.

Section retrieve.

Context `{vmG: !gen_VMG Σ}.

Lemma hvc_retrieve_donate_nz {wi sown sacc pi sexcl i j des ptx rxp l sh} {spsd: gset PID}
      ai r0 r1 wh wf (psd: list PID) :
  (* the current instruction is hvc *)
  (* the decoding of wi is correct *)
  decode_instruction wi = Some(Hvc) ->
  (* the instruction is in page pi *)
  addr_in_page ai pi ->
  (* the decoding of R0 is FFA_DONATE *)
  decode_hvc_func r0 = Some(Retrieve) ->
  (* pi page in spsd is accessible for VM i *)
  pi ∈ sacc ->
  (* spsd is the gset of all to-be-donated pages *)
  spsd = (list_to_set psd) ->
  spsd ## sacc ->
  spsd ## sown ->
  spsd ## sexcl ->
  (finz.to_z l) = (Z.of_nat (length psd)) ->
  des = ([of_imm (encode_vmid j); wf; wh; l; of_imm (encode_vmid i)] ++ map of_pid psd) ->
  (finz.to_z r1) = (Z.of_nat (length des)) ->
  seq_in_page (of_pid ptx) (length des) ptx ->
  {SS{{ ▷(PC @@ i ->r ai) ∗ ▷ ai ->a wi ∗ ▷ A@i:={1}[sacc]
  ∗ ▷ (R0 @@ i ->r r0) ∗ ▷ wh ->re false
  ∗ ▷ (R1 @@ i ->r r1) ∗ ▷ wh ->t{1}(j, wf, i, psd, Donation)
  ∗ ▷ O@i:={1}[sown] ∗ ▷ E@i:={1}[sexcl] ∗ ▷ TX@ i := ptx
  ∗ ▷ mem_region des ptx ∗ ▷ RX@ i :=( rxp !) ∗ ▷ (∃l, mem_region l rxp ∗ ⌜ length l = length des ⌝)
  ∗ ▷ hp{ 1 }[ sh ] }}}
   ExecI @ i {{{ RET ExecI ; PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi
  ∗ O@i:={1}[(sown ∪ spsd)] ∗ E@i:={1}[(sexcl ∪ spsd)] ∗ A@i:={1}[(sacc ∪ spsd)]
  ∗ R0 @@ i ->r (encode_hvc_ret_code Succ) ∗ R1 @@ i ->r r1
  ∗ TX@ i := ptx ∗ RX@ i :=( rxp ! r1, i)
  ∗ mem_region des ptx ∗ mem_region des rxp
  ∗ hp{ 1 }[ sh ∪ {[wh]} ] }}}.
Proof.
  iIntros (Hdecodei Hinpi Hdecodef Hpiacc Hpsd Hsown Hsacc Hsexcl Hlenl Hdes Hdesl Hseq Φ).
  iIntros "(>PC & >Hai & >HA & >Hr0 & >Hwhf & >Hr1 & >Hwh & >HO & >HE & >HTX & >Hmemr & >HRX & >HRXCont & >Hpool) HΦ".
  iApply (sswp_lift_atomic_step ExecI); [done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [Hcureq]; clear Hsche.
  apply fin_to_nat_inj in Hcureq.
  iModIntro.
  iDestruct "Hσ" as "(Hcur & Hσmem & Hσreg & Hσtx & Hσrx1 & Hσrx2 & Hσowned & Hσaccess & Hσexcl & Htrans & Hσhp & %Hdisj & %Hlen & Hrcv)".
  iDestruct ((gen_reg_valid3 i PC ai R0 r0 R1 r1 Hcureq) with "Hσreg PC Hr0 Hr1")
    as "[%HPC [%HR0 %HR1]]"; eauto.
  iDestruct ((gen_access_valid_addr_elem ai sacc) with "Hσaccess HA") as %Haccai; eauto.
  { rewrite (to_pid_aligned_in_page _ pi); eauto. }
  iDestruct ((gen_access_valid_pure sacc) with "Hσaccess HA") as %Hacc; eauto.
  iDestruct (gen_mem_valid ai wi with "Hσmem Hai") as %Hai.
  iDestruct (gen_trans_valid with "Hwh Htrans") as %Htrans.
  destruct Htrans as [b Htrans].
  iDestruct (gen_retri_valid with "Hwhf Hrcv") as %Hretri.
  destruct Hretri as [t [Hretri1 Hretri2]].
  iDestruct (gen_mem_valid_SepL_pure _ des with "Hσmem Hmemr") as %Hadesc.
  { apply finz_seq_NoDup. destruct Hseq as [? [HisSome ?]]. done. }
  iDestruct (gen_tx_valid with "HTX Hσtx") as %Htx.
  iDestruct (gen_rx_valid_none with "HRX Hσrx2") as %Hrx2.
  iDestruct "HRX" as "(HRX1 & HRX2)".
  iDestruct (gen_rx_pid_valid with "HRX1 Hσrx1") as %Hrx1.
  iDestruct ((gen_own_valid_pure sown) with "Hσowned HO") as %Hown; eauto.
  iDestruct ((gen_excl_valid_pure sexcl) with "Hσexcl HE") as %Hexcl; eauto.
  iDestruct ((gen_hpool_valid_elem sh) with "Hpool Hσhp") as %Hpool; eauto.
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal i Hvc ai wi); eauto.
  - (* step *)
    iModIntro.
    iIntros (m2 σ2) "%HstepP".
    apply (step_ExecI_normal i Hvc ai wi) in HstepP; eauto.
    remember (exec Hvc σ1) as c2 eqn:Heqc2.
    rewrite /exec /hvc HR0 Hdecodef /retrieve /get_transaction HR1 //= in Heqc2.
    assert (Hlendesclt :((Z.of_nat (length des)) <= (page_size-1))%Z).
    {
      destruct Hseq as [? [HisSome Hltpagesize]].
      apply (finz_plus_Z_le (of_pid ptx)); eauto.
      apply last_addr_in_bound.
      apply Z.leb_le.
      destruct (((ptx ^+ length des)%f <=? (ptx ^+ (page_size - 1))%f)%Z).
      done.
      contradiction.
    }
    destruct (page_size <? r1)%Z eqn:Hr1ps; [lia|].
    rewrite /get_tx_pid_global Hcureq Htx in Heqc2.
    rewrite (@transaction_retrieve_descriptor_valid j wh wf l psd σ1 des ptx) /= in Heqc2; eauto.    
    2: { rewrite Hcureq; auto. }
    rewrite Htrans /= in Heqc2.
    rewrite /transfer_msg /transfer_msg_unsafe Hr1ps //= /get_current_vm //= /get_vm_mail_box /get_mail_boxes //in Heqc2.
    rewrite /get_vm_mail_box /get_mail_boxes in Htx Hrx2.
    pose proof (surjective_pairing (σ1.1.1.1.1.2 !!! i)) as Hpair.
    rewrite (surjective_pairing (σ1.1.1.1.1.2 !!! i).2) in Hpair.
    rewrite Htx Hrx1 Hrx2 in Hpair.
    rewrite //= /fill_rx /get_vm_mail_box /get_mail_boxes // /get_mail_boxes // in Heqc2.
    rewrite Hpair //= in Heqc2.
    destruct HstepP; subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp /update_incr_PC /update_reg.
    rewrite update_offset_PC_preserve_current_vm
            update_access_batch_preserve_current_vm
            update_ownership_batch_preserve_current_vm
            update_reg_global_preserve_current_vm
            remove_transaction_preserve_current_vm
            fill_rx_unsafe_preserve_current_vm
            copy_page_segment_unsafe_preserve_current_vm.
    cbn.
    iFrame "Hcur".
    rewrite update_offset_PC_preserve_tx
            update_access_batch_preserve_tx
            update_ownership_batch_preserve_tx
            update_reg_global_preserve_tx
            remove_transaction_preserve_tx
            fill_rx_unsafe_preserve_tx.
    2 : {
      rewrite /get_tx_pid_global /get_vm_mail_box //= /get_mail_boxes.
    }
    rewrite copy_page_segment_unsafe_preserve_tx.
    rewrite /get_tx_agree.
    iFrame "Hσtx".
    rewrite update_offset_PC_preserve_rx1
            update_access_batch_preserve_rx1
            update_ownership_batch_preserve_rx1
            update_reg_global_preserve_rx1
            remove_transaction_preserve_rx1
            fill_rx_unsafe_preserve_rx1.
    rewrite copy_page_segment_unsafe_preserve_rx1.
    iFrame "Hσrx1".
    (* update regs *)
    rewrite (update_offset_PC_update_PC1 _ i ai 1).
    rewrite update_access_batch_preserve_regs update_ownership_batch_preserve_regs update_reg_global_update_reg.
    rewrite remove_transaction_preserve_regs fill_rx_unsafe_preserve_regs copy_page_segment_unsafe_preserve_regs;
      try solve_reg_lookup.
    2 : {
      exists r0.
      rewrite get_reg_gmap_get_reg_Some.
      rewrite /get_reg /get_reg_global /get_vm_reg_file /get_reg_files //= Hcureq /get_current_vm //= in HR0 *.
      f_equal.
    }
    2 : {
      rewrite update_access_batch_preserve_current_vm
              update_ownership_batch_preserve_current_vm
              update_reg_global_preserve_current_vm
              remove_transaction_preserve_current_vm
              fill_rx_unsafe_preserve_current_vm
              copy_page_segment_unsafe_preserve_current_vm.
      rewrite Hcureq.
      reflexivity.
    }
    2: {
      rewrite update_access_batch_preserve_regs update_ownership_batch_preserve_regs update_reg_global_update_reg.
      (* try solve_reg_lookup. *)
      rewrite !lookup_insert_ne; [|done].
      rewrite get_reg_gmap_get_reg_Some.
      rewrite /get_reg /get_reg_global /get_vm_reg_file /get_reg_files //= ?Hcureq /get_current_vm //= in HPC *.
      rewrite <-Hcureq.
      f_equal.
      exists r0.
      rewrite get_reg_gmap_get_reg_Some; auto.
    }
    2 : {
      rewrite /copy_page_segment_unsafe /get_rx_pid_global /copy_from_addr_to_addr_unsafe /write_mem_segment_unsafe
              /update_memory_global_batch /get_vm_mail_box /get_mail_boxes.
      cbn.
      rewrite Hpair.
      reflexivity.
    }
     iDestruct ((gen_reg_update2_global PC i _ (ai ^+ 1)%f R0 i _ (encode_hvc_ret_code Succ)) with "Hσreg PC Hr0")
      as ">[Hσreg [PC Hr0]]";try f_equal.
    { left; done. }
    rewrite Hcureq.
     iFrame "Hσreg".
    (* update page table *)
    rewrite update_offset_PC_preserve_owned
            update_access_batch_preserve_ownerships.
    rewrite update_offset_PC_preserve_access.
    rewrite (@update_ownership_batch_update_pagetable_union _ i sown spsd psd Hpsd); f_equal;eauto.
    iDestruct ((gen_own_update_union spsd) with "HO Hσowned") as ">[Hσown' HO']"; f_equal.
    { exact Hpsd. }
    iFrame "Hσown'".
    rewrite (@update_access_batch_update_pagetable_union _ i sacc ExclusiveAccess spsd psd Hpsd); f_equal;eauto.
    iDestruct ((gen_access_update_union spsd) with "HA Hσaccess") as ">[Hσaccess' HA']";f_equal.
    { exact Hpsd. }
    rewrite update_ownership_batch_preserve_access update_reg_global_preserve_access remove_transaction_preserve_access
            fill_rx_unsafe_preserve_access copy_page_segment_unsafe_preserve_access.
    iFrame "Hσaccess'".
    2 : {
        by rewrite update_ownership_batch_preserve_access
                   update_reg_global_preserve_access remove_transaction_preserve_access
                   fill_rx_unsafe_preserve_access copy_page_segment_unsafe_preserve_access.
    }
    rewrite update_offset_PC_preserve_excl.
    rewrite (@update_exclusive_batch_update_pagetable_union _ i sexcl spsd psd Hpsd); f_equal; eauto.
    iDestruct ((gen_excl_update_union spsd) with "HE Hσexcl") as ">[Hσexcl' HE']"; f_equal.
    { exact Hpsd. }
    rewrite update_ownership_batch_preserve_excl update_reg_global_preserve_excl remove_transaction_preserve_excl
            fill_rx_unsafe_preserve_excl copy_page_segment_unsafe_preserve_excl.
    iFrame "Hσexcl'".
    2 : {
        by rewrite update_ownership_batch_preserve_excl update_reg_global_preserve_excl remove_transaction_preserve_excl
                   fill_rx_unsafe_preserve_excl copy_page_segment_unsafe_preserve_excl.
     }
    (* update transactions *)
    rewrite update_offset_PC_preserve_trans
            update_access_batch_preserve_trans update_ownership_batch_preserve_trans
            update_reg_global_preserve_trans.
    rewrite remove_transaction_update_trans.
    rewrite fill_rx_unsafe_preserve_trans copy_page_segment_unsafe_preserve_trans.
    iDestruct (gen_trans_update_delete with "Hwh Htrans") as ">Htrans".
    iFrame "Htrans".
     (* update rx *)
    iCombine "HRX1 HRX2" as "HRX".
    iEval (rewrite -Hcureq) in "HRX".
    iDestruct ((gen_rx_gmap_update_global_None (get_current_vm σ1) r1 (get_current_vm σ1) rxp) with "Hσrx2 HRX") as ">[Hσrx' [HRX1 HRX2]]".
    rewrite update_offset_PC_preserve_rx2
            update_access_batch_preserve_rx2
            update_ownership_batch_preserve_rx2
            update_reg_global_preserve_rx2
            remove_transaction_preserve_rx2.
    rewrite fill_rx_unsafe_update_mailbox.
    rewrite copy_page_segment_unsafe_preserve_rx2.
    iEval (rewrite -Hcureq /get_current_vm) in "Hσrx'".
    rewrite -Hcureq.
    iFrame "Hσrx'".
    (* update mem *)
    rewrite update_offset_PC_preserve_mem update_access_batch_preserve_mem
            update_ownership_batch_preserve_mem update_reg_global_preserve_mem
            remove_transaction_preserve_mem fill_rx_unsafe_preserve_mem.
    rewrite /copy_page_segment_unsafe /copy_from_addr_to_addr_unsafe.
    rewrite /get_tx_pid_global /get_vm_mail_box /get_mail_boxes //=.
    rewrite -Hcureq /get_current_vm in Htx.
    rewrite Htx.
    rewrite /mem_region.
    assert (Hlength: ((read_mem_segment_unsafe σ1 ptx r1)) = des).
    {
      rewrite /read_mem_segment_unsafe.
      rewrite /get_mem in Hadesc.
      apply (f_equal Z.to_nat) in Hdesl.
      rewrite Hdesl.
      rewrite Nat2Z.id.
      clear Hdes Hdesl Hseq Hlendesclt Htx Hpair.
      generalize dependent (of_pid ptx).
      induction des; first done.
      simpl in IHdes.
      simpl.
      intros.
      rewrite /get_memory_unsafe.
      rewrite (Hadesc 0 f a).
      simpl.
      f_equal.
      rewrite /get_memory_unsafe in IHdes.
      rewrite (IHdes (f ^+ 1)%f).
      reflexivity.
      intros k y1 y2 H1 H2.
      apply Hadesc with (S k); auto.
      reflexivity.
      reflexivity.
    }
    iDestruct "HRXCont" as "[%l0 [HRXCont' %Hlen']]".
    rewrite Hlength.
    rewrite /write_mem_segment_unsafe //.
    rewrite /get_rx_pid_global /get_vm_mail_box /get_mail_boxes.
    rewrite -Hcureq in Hpair.
    rewrite Hpair.
    cbn.
    iDestruct ((gen_mem_update_SepL2 (finz.seq rxp (length l0)) l0 des) with "Hσmem HRXCont'") as ">[Hmemupd1 Hmemupd2]".
    rewrite Hlen'.
    apply finz_seq_NoDup'.
    pose proof last_addr_in_bound as Hbound.
    specialize (Hbound rxp).
    solve_finz.
    assumption.
    assert ((zip (finz.seq rxp (length l0)) des) = (zip (finz.seq rxp (Z.to_nat 1000)) des)) as  -> .
    {
      rewrite -finz_seq_zip_page;auto.
      rewrite Hlen' //.
      lia.
    }
    iFrame "Hmemupd1".
    rewrite update_offset_PC_preserve_retri update_access_batch_preserve_retri
            update_ownership_batch_preserve_retri update_reg_global_preserve_retri.
    iDestruct ((gen_retri_update_delete wh) with "Hwhf Hrcv") as ">Hrcv".
    rewrite remove_transaction_update_retri.
    rewrite fill_rx_unsafe_preserve_receivers.
    assert (∀ σ l, get_retri_gmap (update_memory_global_batch σ l) = get_retri_gmap σ) as ->. f_equal.
    iFrame "Hrcv".
    iCombine "Hpool Hσhp" as "Hhp".
    iDestruct ((@gen_hpool_update_union _ _ σ1 sh 1 wh) with "Hhp") as ">[Hσhp' Hpool']".
    {
      rewrite /get_hpool_gset.
      rewrite /get_fresh_handles in Hpool.
      intros contra.
      assert (contra' : wh ∉ dom (gset handle) (get_transactions σ1).1).
      {
        symmetry in Hdisj.
        rewrite ->elem_of_disjoint in Hdisj.
        specialize (Hdisj wh contra).
        auto.
      }
      apply contra'.
      apply elem_of_dom.
      exists t.
      auto.
    }
    rewrite update_offset_PC_preserve_hpool update_access_batch_preserve_hpool
            update_ownership_batch_preserve_hpool update_reg_global_preserve_hpool.
    rewrite remove_transaction_update_hpool.
    rewrite fill_rx_unsafe_preserve_hpool.
    assert (∀ σ l, get_hpool_gset (update_memory_global_batch σ l) = get_hpool_gset σ) as ->. f_equal.
    iFrame "Hσhp'".
    iSplitR.
    iPureIntro.
    rewrite update_offset_PC_preserve_trans'
            update_access_batch_preserve_trans'
            update_ownership_batch_preserve_trans'
            update_reg_global_preserve_trans'.
    rewrite /get_transactions.
    cbn.
    split.
    rewrite dom_delete.
    rewrite disjoint_union_r.
    split.
    apply disjoint_difference_l2; auto.
    apply disjoint_difference_l1; auto.
    apply map_Forall_delete; auto.
    iApply "HΦ".
    rewrite Hlen'.
    by iFrame.
Qed.

Lemma hvc_retrieve_lend_nz {wi sown sacc pi sexcl i j des ptx rxp l} {spsd: gset PID}
      ai r0 r1 wh wf (psd: list PID) :
  (* the current instruction is hvc *)
  (* the decoding of wi is correct *)
  decode_instruction wi = Some(Hvc) ->
  (* the instruction is in page pi *)
  addr_in_page ai pi ->
  (* the decoding of R0 is FFA_LEND *)
  decode_hvc_func r0 = Some(Retrieve) ->
  (* pi page in spsd is accessible for VM i *)
  pi ∈ sacc ->
  (* spsd is the gset of all to-be-donated pages *)
  spsd = (list_to_set psd) ->
  spsd ## sacc ->
  spsd ## sown ->
  spsd ## sexcl ->
  (finz.to_z l) = (Z.of_nat (length psd)) ->
  des = ([of_imm (encode_vmid j); wf; wh; l; of_imm (encode_vmid i)] ++ map of_pid psd) ->
  (finz.to_z r1) = (Z.of_nat (length des)) ->
  seq_in_page (of_pid ptx) (length des) ptx ->
  {SS{{ ▷(PC @@ i ->r ai) ∗ ▷ ai ->a wi ∗ ▷ A@i:={1}[sacc]
  ∗ ▷ (R0 @@ i ->r r0) ∗ ▷ wh ->re false
  ∗ ▷ (R1 @@ i ->r r1) ∗ ▷ wh ->t{1}(j, wf, i, psd, Lending)
  ∗ ▷ O@i:={1}[sown] ∗ ▷ E@i:={1}[sexcl] ∗ ▷ TX@ i := ptx
  ∗ ▷ mem_region des ptx ∗ ▷ RX@ i :=( rxp !) ∗ ▷ (∃l, mem_region l rxp ∗ ⌜ length l = length des ⌝)}}}
   ExecI @ i {{{ RET ExecI ; PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi
  ∗ O@i:={1}[(sown)] ∗ E@i:={1}[(sexcl ∪ spsd)] ∗ A@i:={1}[(sacc ∪ spsd)]
  ∗ R0 @@ i ->r (encode_hvc_ret_code Succ) ∗ R1 @@ i ->r r1 ∗ wh ->t{1}(j, wf, i, psd, Lending)
  ∗ wh ->re true ∗ TX@ i := ptx ∗ RX@ i :=( rxp ! r1, i)
  ∗ mem_region des ptx ∗ mem_region des rxp }}}.
Proof.
  iIntros (Hdecodei Hinpi Hdecodef Hpiacc Hpsd Hsown Hsacc Hsexcl Hlenl Hdes Hdesl Hseq Φ).
  iIntros "(>PC & >Hai & >HA & >Hr0 & >Hwhf & >Hr1 & >Hwh & >HO & >HE & >HTX & >Hmemr & >HRX & >HRXCont) HΦ".
  iApply (sswp_lift_atomic_step ExecI); [done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [Hcureq]; clear Hsche.
  apply fin_to_nat_inj in Hcureq.
  iModIntro.
  iDestruct "Hσ" as "(Hcur & Hσmem & Hσreg & Hσtx & Hσrx1 & Hσrx2 & Hσowned & Hσaccess & Hσexcl & Htrans & Hσhp & %Hdisj & %Hlen & Hrcv)".
  iDestruct ((gen_reg_valid3 i PC ai R0 r0 R1 r1 Hcureq) with "Hσreg PC Hr0 Hr1")
    as "[%HPC [%HR0 %HR1]]"; eauto.
  iDestruct ((gen_access_valid_addr_elem ai sacc) with "Hσaccess HA") as %Haccai; eauto.
  { rewrite (to_pid_aligned_in_page _ pi); eauto. }
  iDestruct ((gen_access_valid_pure sacc) with "Hσaccess HA") as %Hacc; eauto.
  iDestruct (gen_mem_valid ai wi with "Hσmem Hai") as %Hai.
  iDestruct (gen_trans_valid with "Hwh Htrans") as %Htrans.
  destruct Htrans as [b Htrans].
  iDestruct (gen_retri_valid with "Hwhf Hrcv") as %Hretri.
  destruct Hretri as [t [Hretri1 Hretri2]].
  iDestruct (gen_mem_valid_SepL_pure _ des with "Hσmem Hmemr") as %Hadesc.
  { apply finz_seq_NoDup. destruct Hseq as [? [HisSome ?]]. done. }
  iDestruct (gen_tx_valid with "HTX Hσtx") as %Htx.
  iDestruct (gen_rx_valid_none with "HRX Hσrx2") as %Hrx2.
  iDestruct "HRX" as "(HRX1 & HRX2)".
  iDestruct (gen_rx_pid_valid with "HRX1 Hσrx1") as %Hrx1.
  iDestruct ((gen_own_valid_pure sown) with "Hσowned HO") as %Hown; eauto.
  iDestruct ((gen_excl_valid_pure sexcl) with "Hσexcl HE") as %Hexcl; eauto.
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal i Hvc ai wi); eauto.
  - (* step *)
    iModIntro.
    iIntros (m2 σ2) "%HstepP".
    apply (step_ExecI_normal i Hvc ai wi) in HstepP; eauto.
    remember (exec Hvc σ1) as c2 eqn:Heqc2.
    rewrite /exec /hvc HR0 Hdecodef /retrieve /get_transaction HR1 //= in Heqc2.
    assert (Hlendesclt :((Z.of_nat (length des)) <= (page_size-1))%Z).
    {
      destruct Hseq as [? [HisSome Hltpagesize]].
      apply (finz_plus_Z_le (of_pid ptx)); eauto.
      apply last_addr_in_bound.
      apply Z.leb_le.
      destruct (((ptx ^+ length des)%f <=? (ptx ^+ (page_size - 1))%f)%Z).
      done.
      contradiction.
    }
    destruct (page_size <? r1)%Z eqn:Hr1ps; [lia|].
    rewrite /get_tx_pid_global Hcureq Htx in Heqc2.
    rewrite (@transaction_retrieve_descriptor_valid j wh wf l psd σ1 des ptx) /= in Heqc2; eauto.    
    2: { rewrite Hcureq; auto. }
    rewrite Htrans /= in Heqc2.
    rewrite /transfer_msg Hcureq in Heqc2.
    rewrite /transfer_msg_unsafe Hr1ps in Heqc2.
    rewrite /fill_rx in Heqc2.
    assert (Htemp : ∀ σ t r r1 i, get_vm_mail_box (copy_page_segment_unsafe σ t r r1) i =
                                  get_vm_mail_box σ i).
    f_equal.
    rewrite Htemp in Heqc2; clear Htemp.
    assert (Hmb :  get_vm_mail_box σ1 i = (ptx, (rxp,None))).
    { destruct (get_vm_mail_box σ1 i).
    destruct r.
    cbn in Htx ,Hrx2, Hrx1.
    subst t0 o p.
    reflexivity.
    }
    rewrite /get_tx_pid_global /get_rx_pid_global Hmb /=  in Heqc2.
    rewrite fill_rx_unsafe_preserve_current_vm in Heqc2.
    rewrite copy_page_segment_unsafe_preserve_current_vm in Heqc2.
    rewrite Hcureq in Heqc2.
    assert (Hcheck : (i =? i)%nat = true).
    { by apply <- Nat.eqb_eq. }
    rewrite Hcheck in Heqc2.
    pose proof Hretri1 as Hretri1''.
    pose proof Hretri2 as Hretri2''.
    rewrite Htrans in Hretri1.
    inversion Hretri1 as [Hretri1'].
    rewrite -Hretri1' //= in Hretri2.
    rewrite Hretri2 //= /transaction_write_rx /transaction_to_list_words /transaction_to_transaction_descriptor in Heqc2.
    destruct c2 as [c21 c22].
    destruct HstepP; subst m2 σ2; rewrite Heqc2.
    simpl;clear Heqc2.
    rewrite /gen_vm_interp /update_incr_PC /update_reg.
    rewrite update_offset_PC_preserve_hpool update_access_batch_preserve_hpool
            update_reg_global_preserve_hpool update_transaction_preserve_hpool fill_rx_unsafe_preserve_hpool
            copy_page_segment_unsafe_preserve_hpool.
    iFrame "Hσhp".
    rewrite update_offset_PC_preserve_tx update_access_batch_preserve_tx
            update_reg_global_preserve_tx update_transaction_preserve_tx fill_rx_unsafe_preserve_tx.
    2 : {
      rewrite /get_tx_pid_global /get_vm_mail_box //= /get_mail_boxes.
    }
    rewrite copy_page_segment_unsafe_preserve_tx.
    rewrite /get_tx_agree.
    iFrame "Hσtx".
    rewrite update_offset_PC_preserve_current_vm update_access_batch_preserve_current_vm
            update_reg_global_preserve_current_vm update_transaction_preserve_current_vm
            fill_rx_unsafe_preserve_current_vm copy_page_segment_unsafe_preserve_current_vm.
    rewrite Hcureq.
    iFrame "Hcur".
    rewrite update_offset_PC_preserve_rx1 update_access_batch_preserve_rx1
            update_reg_global_preserve_rx1 update_transaction_preserve_rx1.
    rewrite fill_rx_unsafe_preserve_rx1.
     2 : {
       rewrite /get_rx_pid_global /get_vm_mail_box /get_mail_boxes //=.
     }
     rewrite copy_page_segment_unsafe_preserve_rx1.
     iFrame "Hσrx1".
    (* update regs *)
    rewrite (update_offset_PC_update_PC1 _ i ai 1).
    rewrite update_access_batch_preserve_regs update_reg_global_update_reg update_transaction_preserve_regs
             fill_rx_unsafe_preserve_regs copy_page_segment_unsafe_preserve_regs; try solve_reg_lookup.
    2:{
      rewrite update_access_batch_preserve_current_vm update_reg_global_preserve_current_vm
      update_transaction_preserve_current_vm fill_rx_unsafe_preserve_current_vm
      copy_page_segment_unsafe_preserve_current_vm //.
    }
    2: {
      rewrite update_access_batch_preserve_regs update_reg_global_update_reg.
      rewrite update_transaction_preserve_regs
             fill_rx_unsafe_preserve_regs copy_page_segment_unsafe_preserve_regs; try solve_reg_lookup.
      rewrite lookup_insert_ne; [solve_reg_lookup|done].
      exists r0.
      rewrite update_transaction_preserve_regs
             fill_rx_unsafe_preserve_regs copy_page_segment_unsafe_preserve_regs; try solve_reg_lookup.
    }
     iDestruct ((gen_reg_update2_global PC i _ (ai ^+ 1)%f R0 i _ (encode_hvc_ret_code Succ)) with "Hσreg PC Hr0")
      as ">[Hσreg [PC Hr0]]";try f_equal.
    { left;done. }
     iFrame "Hσreg".
    (* update page table *)
    rewrite update_offset_PC_preserve_owned update_access_batch_preserve_ownerships
            update_reg_global_preserve_owned update_transaction_preserve_owned
            fill_rx_unsafe_preserve_owned copy_page_segment_unsafe_preserve_owned.
    iFrame "Hσowned".
    rewrite update_offset_PC_preserve_access.
    rewrite (@update_access_batch_update_pagetable_union _ i sacc ExclusiveAccess spsd psd Hpsd); f_equal;eauto.
    iDestruct ((gen_access_update_union spsd) with "HA Hσaccess") as ">[Hσaccess' HA']";f_equal.
    {exact Hpsd. }
    rewrite update_reg_global_preserve_access update_transaction_preserve_access
    fill_rx_unsafe_preserve_access copy_page_segment_unsafe_preserve_access.
    iFrame "Hσaccess'".
    rewrite update_offset_PC_preserve_excl.
    rewrite (@update_exclusive_batch_update_pagetable_union _ i sexcl spsd psd Hpsd);f_equal; eauto.
    iDestruct ((gen_excl_update_union spsd) with "HE Hσexcl") as ">[Hσexcl' HE']"; f_equal.
    { exact Hpsd. }
    rewrite update_reg_global_preserve_excl update_transaction_preserve_excl
    fill_rx_unsafe_preserve_excl copy_page_segment_unsafe_preserve_excl.
    iFrame "Hσexcl'".
    (* update transactions *)
    rewrite -get_trans_gmap_preserve_dom.
    rewrite update_offset_PC_preserve_trans update_access_batch_preserve_trans
            update_reg_global_preserve_trans.
    rewrite (@toggle_transaction_unsafe_preserve_trans _ _ b).
    2 : {
      cbn.
      assumption.
    }
    rewrite fill_rx_unsafe_preserve_trans copy_page_segment_unsafe_preserve_trans.
    iFrame "Htrans".
      (* update rx *)
    iCombine "HRX1 HRX2" as "HRX".
    rewrite update_offset_PC_preserve_rx2 update_access_batch_preserve_rx2
            update_reg_global_preserve_rx2 update_transaction_preserve_rx2.
    iDestruct ((gen_rx_gmap_update_global_None i r1 i rxp) with "Hσrx2 HRX") as ">[Hσrx' [HRX1 HRX2]]".
    rewrite fill_rx_unsafe_update_mailbox.
    iFrame "Hσrx'".
    (* update retri *)
    rewrite update_offset_PC_preserve_mem update_access_batch_preserve_mem
            update_reg_global_preserve_mem update_transaction_preserve_mem fill_rx_unsafe_preserve_mem.
    iDestruct ((@gen_retri_update _ _ _ false true wh) with "Hwhf Hrcv") as ">[Hrcv' Hwhf']".
    { subst b t.
      eapply get_retri_gmap_lookup.
      exact Hretri1''.
    }
    rewrite update_offset_PC_preserve_retri update_access_batch_preserve_retri
    update_reg_global_preserve_retri /update_transaction /insert_transaction.
    rewrite -get_retri_gmap_to_get_transaction fill_rx_unsafe_preserve_receivers
    copy_page_segment_unsafe_preserve_receivers.
    iFrame "Hrcv'".
    rewrite update_offset_PC_preserve_trans' update_access_batch_preserve_trans'
            update_reg_global_preserve_trans' /get_transactions /=.
    (* update mem *)
    rewrite /copy_page_segment_unsafe /copy_from_addr_to_addr_unsafe.
    rewrite /mem_region.
    assert (Hlength: ((read_mem_segment_unsafe σ1 ptx r1)) = des).
    {
      rewrite /read_mem_segment_unsafe.
      rewrite /get_mem in Hadesc.
      apply (f_equal Z.to_nat) in Hdesl.
      rewrite Hdesl.
      rewrite Nat2Z.id.
      clear Hdes Hdesl Hseq Hlendesclt Hmb.
      generalize dependent (of_pid ptx).
      induction des; first done.
      simpl in IHdes.
      simpl.
      intros.
      rewrite /get_memory_unsafe.
      rewrite (Hadesc 0 f a).
      simpl.
      f_equal.
      rewrite /get_memory_unsafe in IHdes.
      rewrite (IHdes (f ^+ 1)%f).
      reflexivity.
      intros k y1 y2 H1 H2.
      apply Hadesc with (S k); auto.
      reflexivity.
      reflexivity.
    }
    iDestruct "HRXCont" as "[%l0 [HRXCont' %Hlen']]".
    rewrite Hlength.
    rewrite /write_mem_segment_unsafe //.
    cbn.
    iDestruct ((gen_mem_update_SepL2 (finz.seq rxp (length l0)) l0 des) with "Hσmem HRXCont'")
      as ">[Hσmem Hmem]".
    { rewrite Hlen'.
      apply finz_seq_NoDup'.
      pose proof last_addr_in_bound as Hbound.
      specialize (Hbound rxp).
      solve_finz.
    }
    assumption.
    assert ((zip (finz.seq rxp (length l0)) des) = (zip (finz.seq rxp (Z.to_nat 1000)) des)) as ->.
    {
      rewrite -finz_seq_zip_page;auto.
      rewrite Hlen' //.
      lia.
    }
    iFrame "Hσmem".
    iSplitR.
    iPureIntro.
    split;[rewrite get_trans_gmap_preserve_dom // |].
    apply map_Forall_insert_2; auto.
    simpl.
    rewrite <-Hlenl.
    destruct (finz_spec word_size l) as [H _].
    rewrite ->(reflect_iff _ _ (Z.ltb_spec0 l word_size)) in H.
    assumption.
    iApply "HΦ".
    rewrite Hlen'.
    by iFrame.
Qed.

(* TODO hvc_retreive_share *)

End retrieve.
