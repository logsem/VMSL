From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base stdpp_extra.
From HypVeri.algebra Require Import base reg mem pagetable mailbox.
From HypVeri.lang Require Import lang_extra mem_extra reg_extra current_extra.
Require Import stdpp.fin.

Section send.

  Context `{vmG: !gen_VMG Σ}.
 (* TODO we forgot passing the control to vm0 *)
Lemma hvc_send {wi r0 w sacc pi i j des ptx rxp l ai} :
  decode_instruction wi = Some(Hvc) ->
  addr_in_page ai pi ->
  decode_hvc_func r0 = Some(Send) ->
  decode_vmid w = Some j ->
  pi ∈ sacc ->
  (finz.to_z l) = (Z.of_nat (length des)) ->
  ((length des) < page_size)%Z ->
  {SS{{ ▷(PC @@ i ->r ai) ∗ ▷ ai ->a wi ∗ ▷ A@i:={1}[sacc]
  ∗ ▷ (R0 @@ i ->r r0) ∗ ▷ (R1 @@ i ->r w) ∗ ▷ (R2 @@ i ->r l)
  ∗ ▷ TX@ i := ptx ∗ ▷ mem_region des ptx ∗ ▷ RX@ j :=( rxp !)
  ∗ ▷ (∃l', mem_region l' rxp ∗ ⌜length l' = length des⌝)}}}
   ExecI @ i {{{ RET ExecI ; PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi
  ∗ A@i:={1}[(sacc)]
  ∗ R0 @@ i ->r (encode_hvc_ret_code Succ) ∗ R1 @@ i ->r w ∗ R2 @@ i ->r l
  ∗ TX@ i := ptx ∗ RX@ j :=( rxp ! l, i)
  ∗ mem_region des ptx ∗ mem_region des rxp }}}.
Proof.
  iIntros (Hdecodei Hinpi Hdecodef Hdecvmid Hpiacc Hlenl Hsize Φ).
  iIntros "(>PC & >Hai & >HA & >Hr0 & >Hr1 & >Hr2 & >HTX & >Hmemr & >HRX & >Hmemr') HΦ".
  iDestruct "Hmemr'" as "[%l' [Hmemr' %Hlen']]".
  iApply (sswp_lift_atomic_step ExecI); [done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [Hcureq]; clear Hsche.
  apply fin_to_nat_inj in Hcureq.
  iModIntro.
  iDestruct "Hσ" as "(Hcur & Hσmem & Hσreg & Hσtx & Hσrx1 & Hσrx2 & Hσowned & Hσaccess & Hσexcl & Htrans & Hσhp & %Hdisj & %Hlen & Hrcv)".
  iDestruct ((gen_reg_valid4 i PC ai R0 r0 R1 w R2 l Hcureq) with "Hσreg PC Hr0 Hr1 Hr2")
    as "[%HPC [%HR0 [%HR1 %HR2]]]"; eauto.
  iDestruct ((gen_access_valid_addr_elem ai sacc) with "Hσaccess HA") as %Haccai; eauto.
  { rewrite (to_pid_aligned_in_page _ pi); eauto. }
  iDestruct ((gen_access_valid_pure sacc) with "Hσaccess HA") as %Hacc; eauto.
  iDestruct (gen_mem_valid ai wi with "Hσmem Hai") as %Hai.
  iDestruct (gen_mem_valid_SepL_pure _ des with "Hσmem Hmemr") as %Hadesc.
  {
    apply finz_seq_NoDup.
    pose proof last_addr_in_bound as Hlaib.
    specialize (Hlaib ptx).
    solve_finz.
  }
  iDestruct (gen_tx_valid with "HTX Hσtx") as %Htx.
  iDestruct (gen_rx_valid_none with "HRX Hσrx2") as %Hrx2.
  iDestruct "HRX" as "(HRX1 & HRX2)".
  iDestruct (gen_rx_pid_valid with "HRX1 Hσrx1") as %Hrx1.
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal i Hvc ai wi); eauto.
  - (* step *)
    iModIntro.
    iIntros (m2 σ2) "%HstepP".
    apply (step_ExecI_normal i Hvc ai wi) in HstepP; eauto.
    remember (exec Hvc σ1) as c2 eqn:Heqc2.
    rewrite /exec /hvc HR0 Hdecodef /send HR1 /= Hdecvmid /= HR2 /= /transfer_msg /transfer_msg_unsafe in Heqc2.
    assert (Hlendesclt :((Z.of_nat (length des)) <= (page_size-1))%Z).
    {
      apply (finz_plus_Z_le (of_pid ptx)); eauto.
      pose proof last_addr_in_bound as Hlaib.
      specialize (Hlaib ptx).
      solve_finz.
      apply last_addr_in_bound.
      solve_finz.
    }
    destruct (page_size <? l)%Z eqn:Hr1ps; [lia|].
    rewrite /get_tx_pid_global Hcureq Htx /get_rx_pid_global /fill_rx Hrx1 in Heqc2.
    assert (Hpreserve : get_vm_mail_box (copy_page_segment_unsafe σ1 ptx rxp l) j = get_vm_mail_box σ1 j).
    f_equal.
    rewrite Hpreserve in Heqc2.
    destruct (get_vm_mail_box σ1 j) as [? [? rx]].
    simpl in Hrx2.
    rewrite Hrx2 /= in Heqc2.
    destruct HstepP; subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp /update_incr_PC /update_reg.
    rewrite_reg_pc.
    rewrite_reg_global.
    rewrite fill_rx_unsafe_preserve_current_vm fill_rx_unsafe_preserve_mem
            fill_rx_unsafe_preserve_rx1.
    2 : {
      rewrite /get_rx_pid_global Hpreserve.
      reflexivity.
    }
    rewrite fill_rx_unsafe_preserve_tx.
    2 : {
      rewrite /get_tx_pid_global Hpreserve.
      reflexivity.
    }
    rewrite fill_rx_unsafe_preserve_owned.
    rewrite fill_rx_unsafe_preserve_access fill_rx_unsafe_preserve_excl.
    rewrite fill_rx_unsafe_preserve_trans fill_rx_unsafe_preserve_hpool
            fill_rx_unsafe_preserve_receivers.
    rewrite copy_page_segment_unsafe_preserve_current_vm copy_page_segment_unsafe_preserve_tx
            copy_page_segment_unsafe_preserve_rx1 copy_page_segment_unsafe_preserve_owned
            copy_page_segment_unsafe_preserve_access copy_page_segment_unsafe_preserve_excl
            copy_page_segment_unsafe_preserve_trans copy_page_segment_unsafe_preserve_hpool
            copy_page_segment_unsafe_preserve_receivers.
    iFrame "Hcur Hσtx Hσrx1 Hσowned Hσaccess Hσexcl Htrans Hσhp Hrcv".
    (* update regs *)
    rewrite -> (update_offset_PC_update_PC1 _ i ai 1); eauto.
    2 : {
      rewrite !update_reg_global_update_reg fill_rx_unsafe_preserve_regs copy_page_segment_unsafe_preserve_regs;
      try solve_reg_lookup.
      rewrite !lookup_insert_ne; [|done].
      rewrite get_reg_gmap_get_reg_Some; auto.
    }
    rewrite update_reg_global_update_reg.
    2 : {
      rewrite fill_rx_unsafe_preserve_regs copy_page_segment_unsafe_preserve_regs;
      try solve_reg_lookup.
    }
    iDestruct ((gen_reg_update2_global PC i _ (ai ^+ 1)%f R0 i _ (encode_hvc_ret_code Succ)) with "Hσreg PC Hr0") as ">[Hσreg [PC Hr0]]"; eauto.
    rewrite fill_rx_unsafe_preserve_regs copy_page_segment_unsafe_preserve_regs.
    rewrite Hcureq.
    iFrame "Hσreg".
    (* update rx *)
    rewrite fill_rx_unsafe_update_mailbox.
    rewrite copy_page_segment_unsafe_preserve_rx2.
    iCombine "HRX1 HRX2" as "HRX". 
    iDestruct ((gen_rx_gmap_update_global_None j l (get_current_vm σ1) rxp) with "Hσrx2 HRX") as ">[Hσrx' [HRX1 HRX2]]".
    rewrite Hcureq.
    iFrame "Hσrx'".
    (* update mem *)
    rewrite /copy_page_segment_unsafe /copy_from_addr_to_addr_unsafe //=.
    assert (Hlist: read_mem_segment_unsafe σ1 ptx l = des).
    {
      rewrite /read_mem_segment_unsafe.
      rewrite /get_mem in Hadesc.
      apply (f_equal Z.to_nat) in Hlenl.
      rewrite Hlenl.
      rewrite Nat2Z.id.
      clear Hlenl Hlendesclt Htx Hpreserve Hlen' Hsize.
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
    rewrite Hlist.
    rewrite /write_mem_segment_unsafe //.
    iDestruct ((gen_mem_update_SepL2 (finz.seq rxp (length l')) l' des) with "Hσmem Hmemr'") as "Hmemupd".
    rewrite Hlen'.
    apply finz_seq_NoDup'.
    pose proof last_addr_in_bound as Hbound.
    specialize (Hbound rxp).
    solve_finz.
    assumption.
    (* TODO make a general lemma in lang_extra *)
    assert (Hzipeq : (zip (finz.seq rxp (length l')) des) = (zip (finz.seq rxp (Z.to_nat 1000)) des)).
    {
      rewrite <-(zip_fst_snd (zip (finz.seq rxp (Z.to_nat 1000)) des)).
      rewrite !snd_zip; auto.
      f_equal.
      rewrite Hlen'.
      clear Hlenl Hadesc Hlist Hlen' Hsize.
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
    iSplitR.
    iPureIntro.
    split; auto.
    iApply "HΦ".
    rewrite Hlen'.
    by iFrame.
Qed.

End send.
