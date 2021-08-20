From machine_program_logic.program_logic Require Import machine weakestpre.
From HypVeri Require Import RAs rule_misc lifting rules.rules_base transaction utils.
From iris.proofmode Require Import tactics.
Require Import iris.base_logic.lib.ghost_map.
Require Import stdpp.fin.

Section retrieve.

Context `{vmG: !gen_VMG Σ}.

Lemma hvc_retrieve_donate_nz {wi sown sacc pi sexcl i j des ptx rxp l} {spsd: gset PID}
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
  ∗ ▷ mem_region des ptx ∗ ▷ RX@ i :=( rxp !) ∗ ▷ (∃l, mem_region l rxp ∗ ⌜ length l = length des ⌝)}}}
   ExecI @ i {{{ RET ExecI ; PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi
  ∗ O@i:={1}[(sown ∪ spsd)] ∗ E@i:={1}[(sexcl ∪ spsd)] ∗ A@i:={1}[(sacc ∪ spsd)]
  ∗ R0 @@ i ->r (encode_hvc_ret_code Succ) ∗ R1 @@ i ->r r1 ∗ wh ->t{1}(j, wf, i, psd, Donation)
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
  iDestruct ((gen_reg_valid3 σ1 i PC ai R0 r0 R1 r1 Hcureq) with "Hσreg PC Hr0 Hr1")
    as "[%HPC [%HR0 %HR1]]"; eauto.
  iDestruct ((gen_access_valid_addr_elem ai sacc) with "Hσaccess HA") as %Haccai; eauto.
  { rewrite (to_pid_aligned_in_page _ pi); eauto. }
  iDestruct ((gen_access_valid_lookup_Set _ _ _ sacc) with "Hσaccess HA") as %Hacc; eauto.
  iDestruct (gen_mem_valid σ1 ai wi with "Hσmem Hai") as %Hai.
  iDestruct (gen_trans_valid with "Hwh Htrans") as %Htrans.
  destruct Htrans as [b Htrans].
  iDestruct (gen_retri_valid with "Hwhf Hrcv") as %Hretri.
  destruct Hretri as [t [Hretri1 Hretri2]].
  iDestruct (gen_mem_valid_SepL_pure _ des with "Hσmem Hmemr") as %Hadesc.
  { apply finz_seq_NoDup. destruct Hseq as [? [HisSome ?]]. done. }
  iDestruct (gen_tx_valid with "HTX Hσtx") as %Htx.
  iDestruct (gen_rx_none_valid with "HRX Hσrx2") as %Hrx2.
  iDestruct "HRX" as "(HRX1 & HRX2)".
  iDestruct (gen_rx_pid_valid with "HRX1 Hσrx1") as %Hrx1.
  iDestruct ((gen_own_valid_lookup_Set σ1 i 1%Qp sown) with "Hσowned HO") as %Hown; eauto.
  iDestruct ((gen_excl_valid_lookup_Set σ1 i 1%Qp sexcl) with "Hσexcl HE") as %Hexcl; eauto.
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
    rewrite Htrans /= Hcureq in Heqc2.    
    assert (Hcheck : (i =? i) = true).
    { by apply <- Nat.eqb_eq. }
    rewrite Hcheck in Heqc2.
    pose proof Hretri1 as Hretri1''.
    pose proof Hretri2 as Hretri2''.
    rewrite Htrans in Hretri1.
    inversion Hretri1 as [Hretri1'].
    rewrite <-Hretri1' in Hretri2.
    simpl in Hretri2.
    rewrite Hretri2 //= /transaction_write_rx /transaction_to_list_words /transaction_to_transaction_descriptor in Heqc2.
    pose proof (finz_of_z_to_z word_size l) as Htemp.
    rewrite Hlenl in Htemp.
    rewrite /transfer_msg /transfer_msg_unsafe Hr1ps //= /get_current_vm //= /get_vm_mail_box /get_mail_boxes in Heqc2.
    simpl in Heqc2.
    rewrite /get_vm_mail_box /get_mail_boxes in Htx Hrx2.
    pose proof (surjective_pairing (σ1.1.1.1.1.2 !!! i)) as Hpair.
    rewrite (surjective_pairing (σ1.1.1.1.1.2 !!! i).2) in Hpair.
    rewrite Htx Hrx1 Hrx2 in Hpair.
    rewrite //= /fill_rx in Heqc2.
    rewrite /get_vm_mail_box /get_mail_boxes in Heqc2.
    simpl in Heqc2.
    rewrite /get_mail_boxes in Heqc2.
    simpl in Heqc2.
    rewrite Hpair in Heqc2.
    simpl in Heqc2.
    destruct HstepP; subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp /update_incr_PC /update_reg.
    rewrite_reg_all.
    rewrite update_access_batch_preserve_current_vm.
    rewrite update_ownership_batch_preserve_current_vm.
    rewrite_reg_all.
    rewrite_access_all.
    rewrite fill_rx_unsafe_preserve_current_vm.
    rewrite copy_page_segment_unsafe_preserve_current_vm.
    rewrite /get_current_vm.
    iSimpl.
    iFrame "Hσhp".
    rewrite update_ownership_batch_preserve_tx.
    rewrite_reg_all.
    rewrite fill_rx_unsafe_preserve_tx.
    2 : {
      rewrite /get_tx_pid_global /get_vm_mail_box //= /get_mail_boxes.
    }
    rewrite copy_page_segment_unsafe_preserve_tx.
    rewrite /get_tx_agree.
    iSimpl.
    iFrame "Hσtx".
    (* update regs *)
     rewrite -> (update_offset_PC_update_PC1 _ i ai 1); eauto.
     rewrite ?update_access_batch_preserve_regs ?update_ownership_batch_preserve_regs !update_reg_global_update_reg
             ?fill_rx_unsafe_preserve_regs ?copy_page_segment_unsafe_preserve_regs; try solve_reg_lookup.
     2 : {
       exists r0.
       rewrite get_reg_gmap_get_reg_Some; auto.
       rewrite /get_reg /get_reg_global /get_vm_reg_file /get_reg_files //= ?Hcureq /get_current_vm //= in HR0 *.
     }
     2 : {
       rewrite ?update_access_batch_preserve_regs ?update_ownership_batch_preserve_regs !update_reg_global_update_reg
               ?fill_rx_unsafe_preserve_regs ?copy_page_segment_unsafe_preserve_regs;
       try solve_reg_lookup.
       rewrite !lookup_insert_ne; [|done].
       rewrite get_reg_gmap_get_reg_Some; auto.
       rewrite /get_reg /get_reg_global /get_vm_reg_file /get_reg_files //= ?Hcureq /get_current_vm //= in HPC *.
       exists r0.
       rewrite get_reg_gmap_get_reg_Some; auto.
       rewrite /get_reg /get_reg_global /get_vm_reg_file /get_reg_files //= ?Hcureq /get_current_vm //= in HR0 *.
     }
     iDestruct ((gen_reg_update2_global σ1 PC i _ (ai ^+ 1)%f R0 i _ (encode_hvc_ret_code Succ)) with "Hσreg PC Hr0") as ">[Hσreg [PC Hr0]]"; eauto.
     iFrame "Hσreg".
     (* update page table *)
     rewrite update_access_batch_preserve_ownerships.
     rewrite (@update_ownership_batch_update_pagetable_union _ i sown spsd psd Hpsd); eauto.
     iSimpl.
     iDestruct ((gen_own_update_union spsd) with "HO Hσowned") as ">[Hσown' HO']"; eauto.
     iFrame "Hσown'".
     rewrite (@update_access_batch_update_pagetable_union _ i sacc ExclusiveAccess spsd psd Hpsd); eauto.
     iSimpl.
     iDestruct ((gen_access_update_union spsd) with "HA Hσaccess") as ">[Hσaccess' HA']"; eauto.
     rewrite update_ownership_batch_preserve_access update_reg_global_preserve_access
             fill_rx_unsafe_preserve_access copy_page_segment_unsafe_preserve_access.
     iFrame "Hσaccess'".
     2 : {
       by rewrite update_ownership_batch_preserve_access update_reg_global_preserve_access
               fill_rx_unsafe_preserve_access copy_page_segment_unsafe_preserve_access.
     }
     rewrite (@update_exclusive_batch_update_pagetable_union _ i sexcl spsd psd Hpsd); eauto.
     iDestruct ((gen_excl_update_union spsd) with "HE Hσexcl") as ">[Hσexcl' HE']"; eauto.
     rewrite update_ownership_batch_preserve_excl update_reg_global_preserve_excl
             fill_rx_unsafe_preserve_excl copy_page_segment_unsafe_preserve_excl.
     iFrame "Hσexcl'".
     2 : {
       by rewrite update_ownership_batch_preserve_excl update_reg_global_preserve_excl
               fill_rx_unsafe_preserve_excl copy_page_segment_unsafe_preserve_excl.
     }     
     (* update transactions *)
     rewrite update_ownership_batch_preserve_trans update_reg_global_preserve_trans
             fill_rx_unsafe_preserve_trans copy_page_segment_unsafe_preserve_trans.
     rewrite <-Hcureq.
     rewrite (@toggle_transaction_unsafe_preserve_trans _ _ b).
     2 : {
       rewrite Hcureq.
       assumption.
     }
     iFrame "Htrans".
     (* update retri *)
     rewrite update_ownership_batch_preserve_retri update_reg_global_preserve_retri
             fill_rx_unsafe_preserve_receivers copy_page_segment_unsafe_preserve_receivers.
     assert (HTemp : (get_retri_gmap σ1) !! wh = Some false).
     {
       rewrite /get_retri_gmap /get_transactions_gmap.
       apply elem_of_list_to_map_1'.
       intros y Hy.
       apply elem_of_list_In in Hy.
       apply in_map_iff in Hy.
       destruct Hy as [y' [Hy1 Hy2]].
       inversion Hy1; subst; clear Hy1.
       apply elem_of_list_In in Hy2.
       apply elem_of_map_to_list' in Hy2.
       rewrite Hretri1'' in Hy2.
       inversion Hy2; subst; clear Hy2.
       reflexivity.
       apply elem_of_list_In.
       apply in_map_iff.
       exists (wh, t).
       split.
       inversion Hretri1'; subst.
       reflexivity.
       apply elem_of_list_In.
       apply elem_of_map_to_list'.
       simpl.
       assumption.
     }
     iDestruct ((@gen_retri_update _ _ _ false true wh HTemp) with "Hwhf Hrcv") as ">[Hrcv' Hwhf']".
     assert (HTemp' : σ1.1.1.1.1.2 = get_mail_boxes σ1).
     {
       rewrite /get_mail_boxes.
       reflexivity.
     }
     rewrite HTemp'.
     rewrite <-(@get_retri_gmap_to_get_transaction σ1 wh j wf true (get_current_vm σ1) psd Donation).
     iFrame "Hrcv'".
     (* update rx *)
     rewrite update_ownership_batch_preserve_rx1 update_reg_global_preserve_rx1.
     rewrite fill_rx_unsafe_preserve_rx1. 
     2 : {
       rewrite /get_rx_pid_global /get_vm_mail_box /get_mail_boxes //=.
       rewrite /get_mail_boxes //=.
       rewrite Hcureq Hpair.
       reflexivity.
     }
     rewrite copy_page_segment_unsafe_preserve_rx1.
     iFrame "Hσrx1".
     rewrite update_ownership_batch_preserve_rx2 update_reg_global_preserve_rx2.
     rewrite fill_rx_unsafe_update_mailbox.
     rewrite copy_page_segment_unsafe_preserve_rx2.
     iCombine "HRX1 HRX2" as "HRX". 
     iDestruct ((gen_rx_gmap_update_global_None σ1 (get_current_vm σ1) r1 (get_current_vm σ1) rxp) with "Hσrx2 HRX") as ">[Hσrx' [HRX1 HRX2]]".
     iFrame "Hσrx'".
     (* update mem *)
     rewrite update_ownership_batch_preserve_mem update_reg_global_preserve_mem fill_rx_unsafe_preserve_mem.
     rewrite /copy_page_segment_unsafe /copy_from_addr_to_addr_unsafe //=.
     rewrite /get_tx_pid_global /get_vm_mail_box /get_mail_boxes //=.
     rewrite <-Hcureq in Htx.
     rewrite Htx.
     rewrite /mem_region.
     assert (Hlength: ((read_mem_segment_unsafe
                          (get_reg_files σ1, σ1.1.1.1.1.2, get_page_tables σ1, get_current_vm σ1, get_mem σ1,
                           (<[wh := (j, wf, true, get_current_vm σ1, psd, Donation)]> (get_transactions σ1).1,
                            (get_transactions σ1).2)) ptx r1)) = des).
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
     assert (Heq1 : (get_reg_files σ1, σ1.1.1.1.1.2, get_page_tables σ1, get_current_vm σ1, 
                     get_mem σ1,
                     (<[wh := (j, wf, true, get_current_vm σ1, psd, Donation)]> (get_transactions σ1).1,
                      (get_transactions σ1).2)).1.1.1.1.2 = σ1.1.1.1.1.2).
     auto.
     rewrite Heq1.
     rewrite <-Hcureq in Hpair.
     rewrite Hpair.
     cbn.
     iDestruct ((gen_mem_update_Sep_list (finz.seq rxp (length l0)) l0 des) with "Hσmem HRXCont'") as "Hmemupd".
     rewrite Hlen'.
     apply finz_seq_NoDup'.
     pose proof last_addr_in_bound as Hbound.
     specialize (Hbound rxp).
     solve_finz.
     assumption.
     assert (Hzipeq : (zip (finz.seq rxp (length l0)) des) = (zip (finz.seq rxp (Z.to_nat 1000)) des)).
     {
       rewrite <-(zip_fst_snd (zip (finz.seq rxp (Z.to_nat 1000)) des)).
       rewrite !snd_zip; auto.
       f_equal.
       rewrite Hlen'.
       clear Hdes Hdesl Hseq Hadesc Hlength Hlen'.
       generalize dependent (of_pid rxp).
       induction des; first done.
       cbn.
       destruct (Z.to_nat 1000) eqn:Heqn1000; first done.
       simpl.
       intros f.
       f_equal.
       assert (Hn : n = 999).
       lia.
       subst n.
       rewrite (@zip_length_le _ _ des (finz.seq (f ^+ 1)%f 999) (finz.seq (f ^+ 1)%f 1000) [(f ^+ 1000)%f]).
       simpl in Hlendesclt.
       rewrite IHdes.
       reflexivity.
       lia.
       simpl in Hlendesclt.
       rewrite finz_seq_length.
       lia.
       rewrite (finz_seq_decomposition _ 1000 _ 999).
       f_equal.
       simpl.
       f_equal.
       rewrite Unnamed_thm12.
       rewrite Z.add_comm.
       assert (H999_1 : Z.add (Z.of_nat 999%nat) 1%Z = 1000%Z).
       reflexivity.
       rewrite H999_1.
       reflexivity.
       lia.
       lia.
       lia.
       rewrite finz_seq_length.
       lia.
     }
     rewrite Hzipeq.
     iDestruct "Hmemupd" as ">[Hmemupd1 Hmemupd2]".
     iFrame "Hmemupd1".
     rewrite /get_current_vm.
     iFrame "Hcur".
     iSplitR.
     iPureIntro.
     rewrite dom_insert_lookup_L; eauto.
     split; [set_solver|].
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

End retrieve.
