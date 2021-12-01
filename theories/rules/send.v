From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base stdpp_extra.
From HypVeri.algebra Require Import base reg mem pagetable mailbox.
From HypVeri.lang Require Import lang_extra mem_extra reg_extra current_extra.
Require Import stdpp.fin.

Section send.
  Context `{hypparams: HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.

Lemma hvc_send_primary {wi r0 w sacc i j des ptx rxp l ai} :
  decode_instruction wi = Some(Hvc) ->
  decode_hvc_func r0 = Some(Send) ->
  decode_vmid w = Some j ->
  to_pid_aligned ai ∈ sacc ->
  (finz.to_z l) = (Z.of_nat (length des)) ->
  ((length des) < page_size)%Z ->
  fin_to_nat i = 0 -> 
  {SS{{ ▷(PC @@ i ->r ai) ∗ ▷ ai ->a wi ∗ ▷ A@i:={1}[sacc]
  ∗ ▷ (R0 @@ i ->r r0) ∗ ▷ (R1 @@ i ->r w) ∗ ▷ (R2 @@ i ->r l)
  ∗ ▷ TX@ i := ptx ∗ ▷ mem_region des ptx ∗ ▷ RX@ j := rxp ∗ ▷ RX@ j :=()
  ∗ ▷ (∃l', mem_region l' rxp ∗ ⌜length l' = length des⌝)}}}
   ExecI @ i {{{ RET ExecI ; PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi
  ∗ A@i:={1}[(sacc)] 
  ∗ R0 @@ i ->r r0 ∗ R1 @@ i ->r w ∗ R2 @@ i ->r l
  ∗ TX@ i := ptx ∗ RX@ j := rxp ∗ RX@ j :=(l, i)
  ∗ mem_region des ptx ∗ mem_region des rxp }}}.
Proof.
  iIntros (Hdecodei Hdecodef Hdecvmid Hinacc Hlenl Hsize Hz Φ).
  iIntros "(>PC & >Hai & >HA & >Hr0 & >Hr1 & >Hr2 & >HTX & >Hmemr & >HRX1 & >HRX2 & >Hmemr') HΦ".
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
  iDestruct (gen_rx_valid_none with "HRX2 Hσrx2") as %Hrx2.
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
    assert (Hzeq : i = nat_to_fin vm_count_pos).
    {
      apply fin_to_nat_inj.
      rewrite fin_to_nat_to_fin; auto.
    }
    rewrite /exec /hvc HR0 Hdecodef /send HR1 -Hzeq /= Hdecvmid /= HR2 /= /transfer_msg /transfer_msg_unsafe in Heqc2.
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
    rewrite /is_primary /= in Heqc2.
    rewrite fill_rx_unsafe_preserve_current_vm copy_page_segment_unsafe_preserve_current_vm Hcureq Hz in Heqc2.
    destruct (0 =? 0) eqn:Hvmz; [|done].
    rewrite /= in Heqc2.
    rewrite -Hcureq in Heqc2.
    assert (Htemp : forall σ σ', (get_current_vm σ) = (get_current_vm σ') ->
                                 update_current_vmid σ (get_current_vm σ') = σ).
    intros σ σ' Hcureq'.
    rewrite -Hcureq' /update_current_vmid
            /get_reg_files /get_mail_boxes
            /get_page_tables /get_current_vm
            /get_mem /get_transactions.
    by rewrite -!surjective_pairing.
    rewrite Htemp in Heqc2; clear Htemp.
    2 : {
      rewrite /update_incr_PC /update_reg.
      rewrite_reg_pc.
      rewrite_reg_global.
      by rewrite fill_rx_unsafe_preserve_current_vm copy_page_segment_unsafe_preserve_current_vm.
    }
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
      rewrite fill_rx_unsafe_preserve_regs copy_page_segment_unsafe_preserve_regs;
      try solve_reg_lookup.
    }
    iDestruct ((gen_reg_update1_global PC i _ (ai ^+ 1)%f) with "Hσreg PC") as ">[Hσreg PC]"; eauto.
    rewrite fill_rx_unsafe_preserve_regs copy_page_segment_unsafe_preserve_regs.
    rewrite Hcureq.    
    iFrame "Hσreg".
    (* update rx *)
    rewrite fill_rx_unsafe_update_mailbox.
    rewrite copy_page_segment_unsafe_preserve_rx2.
    iDestruct ((gen_rx_gmap_update_global_None j l (get_current_vm σ1)) with "Hσrx2 HRX2") as ">[Hσrx' HRX2]".
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
    assert ((zip (finz.seq rxp (length l')) des) = (zip (finz.seq rxp (Z.to_nat 1000)) des)) as ->.
    {
      rewrite <- (finz_seq_zip_page rxp).
      rewrite Hlen' //.
      lia.
    }
    iDestruct "Hmemupd" as ">[Hmemupd1 Hmemupd2]".
    iFrame "Hmemupd1".
    iSplitR.
    iPureIntro.
    split; auto.
    iApply "HΦ".
    rewrite Hlen'.
    by iFrame.
Qed.

Lemma hvc_send_secondary {wi r0 w sacc i j des ptx rxp l ai z a b c} :
  decode_instruction wi = Some(Hvc) ->
  decode_hvc_func r0 = Some(Send) ->
  decode_vmid w = Some j ->
  to_pid_aligned ai ∈ sacc ->
  (finz.to_z l) = (Z.of_nat (length des)) ->
  ((length des) < page_size)%Z ->
  fin_to_nat z = 0 ->
  i ≠ z ->
  {SS{{ ▷(PC @@ i ->r ai) ∗ ▷ ai ->a wi ∗ ▷ A@i:={1}[sacc] ∗ ▷ (<<i>>{ 1%Qp })
  ∗ ▷ (R0 @@ i ->r r0) ∗ ▷ (R1 @@ i ->r w) ∗ ▷ (R2 @@ i ->r l)
  ∗ ▷ (R0 @@ z ->r a) ∗ ▷ (R1 @@ z ->r b) ∗ ▷ (R2 @@ z ->r c)
  ∗ ▷ TX@ i := ptx ∗ ▷ mem_region des ptx ∗ ▷ RX@ j := rxp ∗ ▷ RX@ j :=()
  ∗ ▷ (∃l', mem_region l' rxp ∗ ⌜length l' = length des⌝)}}}
   ExecI @ i {{{ RET ExecI ; PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi
  ∗ A@i:={1}[(sacc)] ∗ <<z>>{ 1%Qp }
  ∗ R0 @@ i ->r r0 ∗ R1 @@ i ->r w ∗ R2 @@ i ->r l
  ∗ R0 @@ z ->r (encode_hvc_func Send) ∗ R1 @@ z ->r w ∗ R2 @@ z ->r l                     
  ∗ TX@ i := ptx ∗ RX@ j := rxp ∗ RX@j :=(l, i)
  ∗ mem_region des ptx ∗ mem_region des rxp }}}.
Proof.
  iIntros (Hdecodei Hdecodef Hdecvmid Hinacc Hlenl Hsize Hz Hzine Φ).
  iIntros "(>PC & >Hai & >HA & >Htoki & >Hr0 & >Hr1 & >Hr2 & >Hr0' & >Hr1' & >Hr2' & >HTX & >Hmemr & >HRX1 & >HRX2 & >Hmemr') HΦ".
  iDestruct "Hmemr'" as "[%l' [Hmemr' %Hlen']]".
  iApply (sswp_lift_atomic_step ExecI); [done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [Hcureq]; clear Hsche.
  apply fin_to_nat_inj in Hcureq.
  iModIntro.
  iDestruct "Hσ" as "(Hcur & Hσmem & Hσreg & Hσtx & Hσrx1 & Hσrx2 & Hσowned & Hσaccess & Hσexcl & Htrans & Hσhp & %Hdisj & %Hlen & Hrcv)".
  iDestruct ((gen_reg_valid4 i PC ai R0 r0 R1 w R2 l Hcureq) with "Hσreg PC Hr0 Hr1 Hr2")
    as "[%HPC [%HR0 [%HR1 %HR2]]]"; eauto.
  iDestruct ((gen_reg_valid_global1 R0 z a) with "Hσreg Hr0'") as %HR0'.
  iDestruct ((gen_reg_valid_global1 R1 z b) with "Hσreg Hr1'") as %HR1'.
  iDestruct ((gen_reg_valid_global1 R2 z c) with "Hσreg Hr2'") as %HR2'.
  iDestruct ((gen_access_valid_addr_elem ai sacc) with "Hσaccess HA") as %Haccai; eauto.
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
  iDestruct (gen_rx_valid_none with "HRX2 Hσrx2") as %Hrx2.
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
    assert (Hzeq : z = nat_to_fin vm_count_pos).
    {
      apply fin_to_nat_inj.
      rewrite fin_to_nat_to_fin; auto.
    }
    rewrite /exec /hvc HR0 Hdecodef /send HR1 -Hzeq /= Hdecvmid /= HR2 /= /transfer_msg /transfer_msg_unsafe in Heqc2.
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
    rewrite /is_primary /= in Heqc2.
    rewrite fill_rx_unsafe_preserve_current_vm copy_page_segment_unsafe_preserve_current_vm Hcureq in Heqc2.
    destruct (i =? 0) eqn:Hi0.
    rewrite <-(reflect_iff (fin_to_nat i = 0) (i =? 0) (Nat.eqb_spec (fin_to_nat i) 0)) in Hi0.
    exfalso.
    apply Hzine.
    apply fin_to_nat_inj.
    rewrite Hz Hi0.
    reflexivity.
    rewrite /= in Heqc2.
    rewrite -Hcureq in Heqc2.
    destruct HstepP; subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp /update_incr_PC /update_reg.
    rewrite_vmid_all.
    rewrite_reg_pc.
    do 3 rewrite_reg_global.
    rewrite fill_rx_unsafe_preserve_mem
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
    rewrite copy_page_segment_unsafe_preserve_tx
            copy_page_segment_unsafe_preserve_rx1 copy_page_segment_unsafe_preserve_owned
            copy_page_segment_unsafe_preserve_access copy_page_segment_unsafe_preserve_excl
            copy_page_segment_unsafe_preserve_trans copy_page_segment_unsafe_preserve_hpool
            copy_page_segment_unsafe_preserve_receivers.
    iFrame "Hσtx Hσrx1 Hσowned Hσaccess Hσexcl Htrans Hσhp Hrcv".
    iEval (rewrite -Hcureq) in "Htoki".
    iDestruct (token_update (get_current_vm σ1) (get_current_vm σ1) z with "Htoki") as "HtokUpd".
    iDestruct ("HtokUpd" with "Hcur") as ">[Htokz Hcur]". 
    rewrite /get_current_vm /update_current_vmid.
    simpl.
    iFrame "Hcur".
    (* update regs *)
    rewrite -> (update_offset_PC_update_PC1 _ i ai 1); eauto.
    2 : {
      rewrite get_reg_gmap_get_reg_Some; auto.
      rewrite /get_reg //=.
      do 3 rewrite_reg_global.
      rewrite fill_rx_unsafe_preserve_current_vm copy_page_segment_unsafe_preserve_current_vm.
      assert (Htemp : z ≠ get_current_vm σ1).
      {
        rewrite Hcureq.
        intros Hcontra.
        apply Hzine.
        symmetry; auto.
      }
      do 3 (apply get_reg_global_update_reg_global_ne_vmid; auto).
    }
    rewrite update_reg_global_update_reg.
    2 : {
      exists c.
      rewrite update_reg_global_update_reg.
      rewrite lookup_insert_ne; auto.
      rewrite update_reg_global_update_reg.
      rewrite lookup_insert_ne; auto.
      rewrite fill_rx_unsafe_preserve_regs copy_page_segment_unsafe_preserve_regs.
      rewrite get_reg_gmap_lookup_Some.
      rewrite /get_reg_global in HR2'.
      assumption.
      exists a.
      rewrite fill_rx_unsafe_preserve_regs copy_page_segment_unsafe_preserve_regs.
      rewrite get_reg_gmap_lookup_Some.
      rewrite /get_reg_global in HR0'.
      assumption.
      exists b.
      rewrite update_reg_global_update_reg.
      rewrite lookup_insert_ne; auto.
      rewrite fill_rx_unsafe_preserve_regs copy_page_segment_unsafe_preserve_regs.
      rewrite get_reg_gmap_lookup_Some.
      rewrite /get_reg_global in HR0'.
      assumption.
      exists a.
      rewrite fill_rx_unsafe_preserve_regs copy_page_segment_unsafe_preserve_regs.
      rewrite get_reg_gmap_lookup_Some.
      rewrite /get_reg_global in HR0'.
      assumption.
    }
    rewrite update_reg_global_update_reg.
    2 : {
      exists b.
      rewrite update_reg_global_update_reg.
      rewrite lookup_insert_ne; auto.
      rewrite fill_rx_unsafe_preserve_regs copy_page_segment_unsafe_preserve_regs.
      rewrite get_reg_gmap_lookup_Some.
      rewrite /get_reg_global in HR0'.
      assumption.
      exists a.
      rewrite fill_rx_unsafe_preserve_regs copy_page_segment_unsafe_preserve_regs.
      rewrite get_reg_gmap_lookup_Some.
      rewrite /get_reg_global in HR0'.
      assumption.
    }
    rewrite update_reg_global_update_reg.
    2 : {
      exists a.
      rewrite fill_rx_unsafe_preserve_regs copy_page_segment_unsafe_preserve_regs.
      rewrite get_reg_gmap_lookup_Some.
      rewrite /get_reg_global in HR0'.
      assumption.
    }
    iDestruct ((gen_reg_update4_global PC i (ai ^+ 1)%f R2 z l R1 z w R0 z (encode_hvc_func Send)) with "Hσreg PC Hr2' Hr1' Hr0'") as ">[Hσreg [PC [Hr2' [Hr1' Hr0']]]]"; eauto.
    rewrite fill_rx_unsafe_preserve_regs copy_page_segment_unsafe_preserve_regs.    
    iFrame "Hσreg".
    (* update rx *)
    rewrite fill_rx_unsafe_update_mailbox.
    rewrite copy_page_segment_unsafe_preserve_rx2.
    iDestruct ((gen_rx_gmap_update_global_None j l (get_current_vm σ1)) with "Hσrx2 HRX2") as ">[Hσrx' HRX2]".
    iEval (rewrite /get_current_vm) in "Hσrx'".
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
      rewrite (Hadesc 0 f a0).
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
    assert ((zip (finz.seq rxp (length l')) des) = (zip (finz.seq rxp (Z.to_nat 1000)) des)) as ->.
    {
      rewrite <- (finz_seq_zip_page rxp).
      rewrite Hlen' //.
      lia.
    }
    iDestruct "Hmemupd" as ">[Hmemupd1 Hmemupd2]".
    iFrame "Hmemupd1".
    iSplitR.
    iPureIntro.
    split; auto.
    iApply "HΦ".
    rewrite Hlen'.
    rewrite -Hcureq.
    by iFrame.
Qed.

End send.
