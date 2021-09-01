From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base stdpp_extra.
From HypVeri.algebra Require Import base mem reg pagetable mailbox trans.
From HypVeri.lang Require Import lang_extra reg_extra mem_extra pagetable_extra trans_extra.

Section retrieve.

Context `{vmG: !gen_VMG Σ}.

Lemma hvc_retrieve_donate_nz {wi sown sacc pi sexcl i j destx wf' desrx ptx prx l sh} {spsd: gset PID}
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
  (finz.to_z l) = Z.of_nat (length psd) ->
  destx = ([of_imm (encode_vmid j); wf'; wh ;of_imm (encode_vmid i)] ) ->
  desrx = ([of_imm (encode_vmid j); wf; wh; encode_transaction_type Donation;l] ++ map of_pid psd) ->
  (finz.to_z r1) = (Z.of_nat (length destx)) ->
  seq_in_page (of_pid ptx) (length destx) ptx ->
  seq_in_page (of_pid prx) (length desrx) prx ->
  {SS{{ ▷(PC @@ i ->r ai) ∗ ▷ ai ->a wi ∗ ▷ A@i:={1}[sacc]
  ∗ ▷ (R0 @@ i ->r r0) ∗ ▷ wh ->re false
  ∗ ▷ (R1 @@ i ->r r1) ∗ ▷ wh ->t{1}(j, wf, i, psd, Donation)
  ∗ ▷ O@i:={1}[sown] ∗ ▷ E@i:={1}[sexcl] ∗ ▷ TX@ i := ptx
  ∗ ▷ mem_region destx ptx ∗ ▷ RX@ i :=( prx !) ∗ ▷ (∃l, mem_region l prx ∗ ⌜ length l = length desrx ⌝)
  ∗ ▷ hp{ 1 }[ sh ] }}}
   ExecI @ i {{{ RET ExecI ; PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi
  ∗ O@i:={1}[(sown ∪ spsd)] ∗ E@i:={1}[(sexcl ∪ spsd)] ∗ A@i:={1}[(sacc ∪ spsd)]
  ∗ R0 @@ i ->r (encode_hvc_ret_code Succ) ∗ R1 @@ i ->r r1
  ∗ TX@ i := ptx ∗ RX@ i :=( prx ! (l ^+ 5)%f, i)
  ∗ mem_region destx ptx ∗ mem_region desrx prx
  ∗ hp{ 1 }[ sh ∪ {[wh]} ] }}}.
Proof.
  iIntros (Hdecodei Hinpi Hdecodef Hpiacc Hpsd Hsown Hsacc Hsexcl Hlenl Hdestx Hdesrx Hdestxl Hseqtx Hseqrx Φ).
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
  iDestruct (gen_mem_valid_SepL_pure _ destx with "Hσmem Hmemr") as %Hadesc.
  { apply finz_seq_NoDup. destruct Hseqtx as [? [HisSome ?]]. done. }
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
    assert (Hlendesclt :((Z.of_nat (length destx)) <= (page_size-1))%Z).
    {
      destruct Hseqtx as [? [HisSome Hltpagesize]].
      apply (finz_plus_Z_le (of_pid ptx)); eauto.
      apply last_addr_in_bound.
      apply Z.leb_le.
      destruct (((ptx ^+ length destx)%f <=? (ptx ^+ (page_size - 1))%f)%Z).
      done.
      contradiction.
    }
    assert (Hlendesclt' :((Z.of_nat (length desrx)) <= (page_size-1))%Z).
    {
      destruct Hseqrx as [? [HisSome Hltpagesize]].
      apply (finz_plus_Z_le (of_pid prx)); eauto.
      apply last_addr_in_bound.
      apply Z.leb_le.
      destruct (((prx ^+ length desrx)%f <=? (prx ^+ (page_size - 1))%f)%Z).
      done.
      contradiction.
    }
    destruct (page_size <? r1)%Z eqn:Hr1ps; [lia|].
    rewrite /get_tx_pid_global Hcureq Htx in Heqc2.
    rewrite (@transaction_retrieve_descriptor_valid j wh wf' σ1 destx ptx) /= in Heqc2; eauto.
    2: { rewrite Hcureq; auto. }
    rewrite Htrans /= in Heqc2.
    rewrite -Hlenl finz_of_z_to_z in Heqc2.
    assert (finz.of_z (Z.of_nat (S (S (S (S (S (length (map of_pid psd)))))))) = Some (l ^+ 5%Z)%f).
    {  rewrite Hdesrx in Hseqrx. destruct Hseqrx as [_ [HisSome Hltpagesize]]. cbn in HisSome, Hltpagesize.
       assert (Heq: Z.of_nat(S (S (S (S (S (length (map of_pid psd)))))))
                    = ((Z.of_nat (length (map of_pid psd))) + 5%Z)%Z).
       lia.
       rewrite Heq map_length.
       rewrite -Hlenl.
       rewrite Heq map_length -Hlenl in Hltpagesize.
       rewrite Heq map_length -Hlenl in HisSome.
       pose proof (last_addr_in_bound prx).
       assert (Hle:( (finz.to_z l + 5)%Z <= (page_size-1)%Z)%Z).
       apply (finz_plus_Z_le (of_pid prx));auto.
       apply Z.leb_le.
       destruct ((((of_pid prx) ^+ (finz.to_z l + 5)%Z)%f <=?((of_pid prx) ^+ (page_size-1)%Z)%f)%Z)
                eqn:Heqn;[done|contradiction].
       unfold finz.of_z.
       destruct (decide (finz.to_z l + 5 < word_size)%Z) eqn:Hdecide.
       unfold decide  in Hdecide.
       unfold decide_rel in Hdecide.
       rewrite Hdecide.
       2: {  lia. }
       clear Hdecide.
       destruct (decide (0<= finz.to_z l + 5 )%Z) eqn:Hdecide.
       unfold decide  in Hdecide.
       unfold decide_rel in Hdecide.
       rewrite Hdecide /=.
       2: {  lia. }
       f_equal.
       apply finz_to_z_eq.
       cbn.
       solve_finz.
    }
    rewrite H in Heqc2. clear H.
    rewrite /fill_rx in Heqc2.
    assert (Htemp : ∀ σ dst ws i, get_vm_mail_box (write_mem_segment_unsafe σ dst ws) i =
                                  get_vm_mail_box σ i).
    f_equal.
    rewrite Htemp in Heqc2; clear Htemp.
    assert (Hmb :  get_vm_mail_box σ1 i = (ptx, (prx,None))).
    { destruct (get_vm_mail_box σ1 i).
      destruct r.
      cbn in Htx ,Hrx2, Hrx1.
      subst t0 o p.
      reflexivity.
    }
    rewrite /get_tx_pid_global /get_rx_pid_global Hmb /=  in Heqc2.
    assert (Hcheck: (i =? i)%nat = true).
    { apply <- Nat.eqb_eq. reflexivity. }
    rewrite Hcheck in Heqc2.
    pose proof Hretri1 as Hretri1'.
    pose proof Hretri2 as Hretri2'.
    rewrite Htrans in Hretri1.
    inversion Hretri1 as [Hretri1''].
    rewrite -Hretri1'' //= in Hretri2.
    subst b t.
    clear Hretri2' Hretri1.
    destruct c2 as [c21 c22].
    destruct HstepP; subst m2 σ2; rewrite Heqc2.
    simpl;clear Heqc2.
    rewrite /gen_vm_interp /update_incr_PC /update_reg.
    rewrite update_offset_PC_preserve_tx update_access_batch_preserve_tx update_ownership_batch_preserve_tx
            update_reg_global_preserve_tx remove_transaction_preserve_tx fill_rx_unsafe_preserve_tx.
    rewrite  write_mem_segment_unsafe_preserve_tx.
    2 : {
      rewrite /get_tx_pid_global /get_vm_mail_box //= /get_mail_boxes.
    }
    iFrame "Hσtx".
    rewrite update_offset_PC_preserve_current_vm update_access_batch_preserve_current_vm
            update_ownership_batch_preserve_current_vm
            update_reg_global_preserve_current_vm remove_transaction_preserve_current_vm
            fill_rx_unsafe_preserve_current_vm write_mem_segment_unsafe_preserve_current_vm.
    rewrite Hcureq.
    iFrame "Hcur".
    rewrite update_offset_PC_preserve_rx1 update_access_batch_preserve_rx1 update_ownership_batch_preserve_rx1
            update_reg_global_preserve_rx1 remove_transaction_preserve_rx1 fill_rx_unsafe_preserve_rx1.
    rewrite  write_mem_segment_unsafe_preserve_rx1.
    2 : {
      rewrite /get_rx_pid_global /get_vm_mail_box /get_mail_boxes //=.
    }
    iFrame "Hσrx1".
    (* update regs *)
    rewrite (update_offset_PC_update_PC1 _ i ai 1).
    rewrite update_access_batch_preserve_regs update_ownership_batch_preserve_regs
            update_reg_global_update_reg remove_transaction_preserve_regs
            fill_rx_unsafe_preserve_regs write_mem_segment_unsafe_preserve_regs; try solve_reg_lookup.
    2:{
      rewrite update_access_batch_preserve_current_vm update_ownership_batch_preserve_current_vm
              update_reg_global_preserve_current_vm remove_transaction_preserve_current_vm
              fill_rx_unsafe_preserve_current_vm write_mem_segment_unsafe_preserve_current_vm //.
    }
    2: {
      rewrite update_access_batch_preserve_regs update_ownership_batch_preserve_regs
              update_reg_global_update_reg remove_transaction_preserve_regs
              fill_rx_unsafe_preserve_regs write_mem_segment_unsafe_preserve_regs; try solve_reg_lookup.
      rewrite lookup_insert_ne; [solve_reg_lookup|done].
    }
    iDestruct ((gen_reg_update2_global PC i _ (ai ^+ 1)%f R0 i _ (encode_hvc_ret_code Succ)) with "Hσreg PC Hr0")
      as ">[Hσreg [PC Hr0]]";try f_equal.
    { left;done. }
    iFrame "Hσreg".
    (* update page table *)
    rewrite update_offset_PC_preserve_owned update_access_batch_preserve_ownerships.
    rewrite (@update_ownership_batch_update_pagetable_union _ i sown spsd psd Hpsd); f_equal;eauto.
    iDestruct ((gen_own_update_union spsd) with "HO Hσowned") as ">[Hσowned HO]";f_equal.
    exact Hpsd.
    rewrite update_reg_global_preserve_owned remove_transaction_preserve_owned
            fill_rx_unsafe_preserve_owned write_mem_segment_unsafe_preserve_owned.
    iFrame "Hσowned".
    rewrite update_offset_PC_preserve_access.
    rewrite (@update_access_batch_update_pagetable_union _ i sacc ExclusiveAccess spsd psd Hpsd); f_equal;eauto.
    iDestruct ((gen_access_update_union spsd) with "HA Hσaccess") as ">[Hσaccess HA]";f_equal.
    {exact Hpsd. }
    rewrite update_ownership_batch_preserve_access update_reg_global_preserve_access remove_transaction_preserve_access
    fill_rx_unsafe_preserve_access write_mem_segment_unsafe_preserve_access.
    2: { rewrite update_ownership_batch_preserve_access update_reg_global_preserve_access remove_transaction_preserve_access
                 fill_rx_unsafe_preserve_access write_mem_segment_unsafe_preserve_access. done. }
    iFrame "Hσaccess".
    rewrite update_offset_PC_preserve_excl.
    rewrite (@update_exclusive_batch_update_pagetable_union _ i sexcl spsd psd Hpsd);f_equal; eauto.
    iDestruct ((gen_excl_update_union spsd) with "HE Hσexcl") as ">[Hσexcl HE]"; f_equal.
    { exact Hpsd. }
    rewrite update_ownership_batch_preserve_excl update_reg_global_preserve_excl remove_transaction_preserve_excl
    fill_rx_unsafe_preserve_excl write_mem_segment_unsafe_preserve_excl.
    2: { rewrite update_ownership_batch_preserve_excl update_reg_global_preserve_excl remove_transaction_preserve_excl
                 fill_rx_unsafe_preserve_excl write_mem_segment_unsafe_preserve_excl. done. }
    iFrame "Hσexcl".
    (* update rx *)
    rewrite update_offset_PC_preserve_rx2 update_access_batch_preserve_rx2 update_ownership_batch_preserve_rx2
            update_reg_global_preserve_rx2 remove_transaction_preserve_rx2.
    iDestruct ((gen_rx_gmap_update_global_None i (l ^+ 5)%f i prx) with "Hσrx2 [HRX1 HRX2]") as ">[Hσrx' [HRX1 HRX2]]".
    { iFrame. }
    rewrite fill_rx_unsafe_update_mailbox write_mem_segment_unsafe_preserve_rx2.
    iFrame "Hσrx'".
    (* update transactions *)
    rewrite -get_trans_gmap_preserve_dom.
    rewrite update_offset_PC_preserve_trans update_access_batch_preserve_trans
            update_ownership_batch_preserve_trans update_reg_global_preserve_trans
            remove_transaction_update_trans fill_rx_unsafe_preserve_trans
            write_mem_segment_unsafe_preserve_trans.
    iDestruct (gen_trans_update_delete with "Hwh Htrans") as ">Htrans".
    iFrame "Htrans".
    (* update hpool *)
    rewrite update_offset_PC_preserve_hpool update_access_batch_preserve_hpool
            update_ownership_batch_preserve_hpool update_reg_global_preserve_hpool
            remove_transaction_update_hpool fill_rx_unsafe_preserve_hpool
            write_mem_segment_unsafe_preserve_hpool.
    iDestruct ((gen_hpool_update_union wh) with "Hpool Hσhp") as ">[Hσhp Hpool]".
    {
      rewrite /get_hpool_gset.
      unfold get_fresh_handles in Hpool.
      assert (Hwhin : wh ∈ dom (gset handle) (get_transactions σ1).1).
      {
        apply elem_of_dom.
        eexists.
        done.
      }
      set_solver.
    }
    iFrame "Hσhp".
    (* update retri *)
    rewrite update_offset_PC_preserve_mem update_access_batch_preserve_mem
            update_ownership_batch_preserve_mem update_reg_global_preserve_mem
            remove_transaction_preserve_mem fill_rx_unsafe_preserve_mem.
    iDestruct ((gen_retri_update_delete wh) with "Hwhf Hrcv") as ">Hrcv";auto.
    rewrite update_offset_PC_preserve_trans' update_access_batch_preserve_trans'
            update_ownership_batch_preserve_trans'
            update_reg_global_preserve_trans' /get_transactions /=.
    rewrite update_offset_PC_preserve_retri update_access_batch_preserve_retri
            update_ownership_batch_preserve_retri update_reg_global_preserve_retri
            remove_transaction_update_retri fill_rx_unsafe_preserve_receivers
            write_mem_segment_unsafe_preserve_receivers.
    iFrame "Hrcv".
    (* update mem *)
    rewrite /write_mem_segment_unsafe /mem_region.
    iDestruct "HRXCont" as "[%l0 [HRXCont' %Hlen']]".
    cbn.
    iDestruct ((gen_mem_update_SepL2 (finz.seq prx (length l0)) l0 desrx) with "Hσmem HRXCont'")
      as ">[Hσmem Hmem]".
    { rewrite Hlen'.
      apply finz_seq_NoDup'.
      pose proof (last_addr_in_bound prx).
      solve_finz.
    }
    assumption.
    assert ((zip (finz.seq prx (length l0)) desrx) = (zip (finz.seq prx (Z.to_nat 1000)) desrx)) as ->.
    {
      rewrite -finz_seq_zip_page;auto.
      rewrite Hlen' //.
      lia.
    }
    cbn in Hdesrx.
    rewrite -Hdesrx.
    iFrame "Hσmem".
    iSplitR.
    iPureIntro.
    split;[rewrite dom_delete get_trans_gmap_preserve_dom;set_solver |].
    apply map_Forall_delete; auto.
    iApply "HΦ".
    rewrite Hlen'.
    by iFrame.
Qed.


Lemma retrieve_lend_share {sacc sexcl j desrx ptx prx l ai r0 wh wf} σ1 i tt sexcl' acc (spsd: gset PID)
       (psd: list PID):
  tt = Lending ∧ sexcl' = sexcl ∪ spsd ∧ acc = ExclusiveAccess ∨ tt = Sharing ∧ sexcl' = sexcl ∧ acc = SharedAccess ->
  spsd = list_to_set psd ->
  finz.to_z l = Z.of_nat (length psd) ->
  desrx = [of_imm (encode_vmid j); wf; wh; encode_transaction_type tt; l] ++ map of_pid psd ->
  seq_in_page (of_pid prx) (length desrx) prx ->
  (get_vm_mail_box σ1 i).1 = ptx ->
  (get_vm_mail_box σ1 i).2.1 = prx ->
  (get_current_vm σ1) = i ->
  get_reg σ1 PC = Some ai ->
  get_reg σ1 R0 = Some r0 ->
  spsd ## sacc ->
  spsd ## sexcl ->
  (get_transactions σ1).1 !! wh = Some (j, wf, false, i, psd, tt) ->
  PC @@ i ->r ai -∗
  A@i:={1}[sacc] -∗
  E@i:={1}[sexcl] -∗
  R0 @@ i ->r r0 -∗
  wh->t{1}(j,wf,i,psd,tt) -∗
  wh->refalse -∗
  RX@i:=prx -∗
  rx_option_mapsto i None -∗
  (∃ l0 : list handle, mem_region l0 prx ∗ ⌜length l0 = length desrx⌝) -∗
  gen_vm_interp σ1 ={⊤}=∗
  gen_vm_interp (update_incr_PC
            (update_access_batch
               (update_reg
                  (update_transaction
                     (fill_rx_unsafe
                        (write_mem_segment_unsafe σ1 (of_pid prx)
                           ( of_imm (encode_vmid j) :: wf :: wh :: encode_transaction_type tt :: l :: map of_pid psd))
                        (l ^+ 5)%f i i ptx prx) wh (j, wf, true, i, psd, tt)) R0
                  (encode_hvc_ret_code Succ)) psd acc))
  ∗ wh->t{1}(j,wf,i,psd,tt)
  ∗ PC @@ i ->r (ai ^+ 1)%f
  ∗ R0 @@ i ->r encode_hvc_ret_code Succ
  ∗ RX@i:=prx
  ∗ rx_option_mapsto i (Some ((l ^+ 5)%f, i))
  ∗ wh->retrue
  ∗ ([∗ list] a;w' ∈ finz.seq prx (length desrx);(of_imm (encode_vmid j) :: wf :: wh :: encode_transaction_type tt
                                                              :: l :: map of_pid psd), a ->a w')
  ∗ A@i:={1}[sacc ∪ spsd]
  ∗ E@i:={1}[sexcl'].
Proof.
  iIntros (Htt Hpsd Hlenl Hdesrx Hseqrx Htx Hrx1 Hcureq HPC HR1 Hsacc Hsexcl Htrans) "PC Hacc Hexcl R0 Htrans Hretri Hrx1 Hrx2 Hmemdesrx Hσ".
  iDestruct "Hσ" as "(Hcur & Hσmem & Hσreg & Hσtx & Hσrx1 & Hσrx2 & Hσowned & Hσaccess & Hσexcl
          & Hσtrans & Hσhp & %Hdisj & %Hlen & Hσretri)".
  iDestruct ((gen_access_valid_pure sacc) with "Hσaccess Hacc") as %Hacc; eauto.
  iDestruct ((gen_excl_valid_pure sexcl) with "Hσexcl Hexcl") as %Hexcl; eauto.
  rewrite /gen_vm_interp /update_incr_PC /update_reg.
  rewrite update_offset_PC_preserve_hpool update_access_batch_preserve_hpool
          update_reg_global_preserve_hpool update_transaction_preserve_hpool fill_rx_unsafe_preserve_hpool
          write_mem_segment_unsafe_preserve_hpool.
  iFrame "Hσhp".
  rewrite update_offset_PC_preserve_tx update_access_batch_preserve_tx
          update_reg_global_preserve_tx update_transaction_preserve_tx fill_rx_unsafe_preserve_tx.
  2 : {
    rewrite /get_tx_pid_global /get_vm_mail_box //= /get_mail_boxes.
  }
  rewrite write_mem_segment_unsafe_preserve_tx.
  rewrite /get_tx_agree.
  iFrame "Hσtx".
  rewrite update_offset_PC_preserve_current_vm update_access_batch_preserve_current_vm
          update_reg_global_preserve_current_vm update_transaction_preserve_current_vm
          fill_rx_unsafe_preserve_current_vm write_mem_segment_unsafe_preserve_current_vm.
  rewrite Hcureq.
  iFrame "Hcur".
  rewrite update_offset_PC_preserve_rx1 update_access_batch_preserve_rx1
          update_reg_global_preserve_rx1 update_transaction_preserve_rx1.
  rewrite fill_rx_unsafe_preserve_rx1.
  2 : {
    rewrite /get_rx_pid_global /get_vm_mail_box /get_mail_boxes //=.
  }
  rewrite write_mem_segment_unsafe_preserve_rx1.
  iFrame "Hσrx1".
  (* update regs *)
  rewrite (update_offset_PC_update_PC1 _ i ai 1).
  rewrite update_access_batch_preserve_regs update_reg_global_update_reg update_transaction_preserve_regs
          fill_rx_unsafe_preserve_regs write_mem_segment_unsafe_preserve_regs; try solve_reg_lookup.
  2:{
    rewrite update_access_batch_preserve_current_vm update_reg_global_preserve_current_vm
            update_transaction_preserve_current_vm fill_rx_unsafe_preserve_current_vm
            write_mem_segment_unsafe_preserve_current_vm //.
  }
  2: {
    rewrite update_access_batch_preserve_regs update_reg_global_update_reg.
    rewrite update_transaction_preserve_regs
            fill_rx_unsafe_preserve_regs write_mem_segment_unsafe_preserve_regs; try solve_reg_lookup.
    rewrite lookup_insert_ne; [solve_reg_lookup|done].
    exists r0.
    rewrite update_transaction_preserve_regs
            fill_rx_unsafe_preserve_regs write_mem_segment_unsafe_preserve_regs; try solve_reg_lookup.
  }
  iDestruct ((gen_reg_update2_global PC i _ (ai ^+ 1)%f R0 i _ (encode_hvc_ret_code Succ)) with "Hσreg PC R0")
    as ">[Hσreg [PC R0]]";try f_equal.
  { left;done. }
  iFrame "Hσreg".
  (* update transactions *)
  rewrite -get_trans_gmap_preserve_dom.
  rewrite update_offset_PC_preserve_trans update_access_batch_preserve_trans
          update_reg_global_preserve_trans (update_transaction_preserve_trans _ _ false).
  2 : { cbn. assumption. }
  rewrite fill_rx_unsafe_preserve_trans write_mem_segment_unsafe_preserve_trans.
  iFrame "Hσtrans".
  (* update rx *)
  iCombine "Hrx1 Hrx2" as "Hrx".
  rewrite update_offset_PC_preserve_rx2 update_access_batch_preserve_rx2
          update_reg_global_preserve_rx2 update_transaction_preserve_rx2.
  iDestruct ((gen_rx_gmap_update_global_None i (l ^+ 5)%f i prx) with "Hσrx2 Hrx") as ">[Hσrx [Hrx1 Hrx2]]".
  rewrite fill_rx_unsafe_update_mailbox.
  iFrame "Hσrx".
  (* update retri *)
  rewrite update_offset_PC_preserve_mem update_access_batch_preserve_mem
          update_reg_global_preserve_mem update_transaction_preserve_mem fill_rx_unsafe_preserve_mem.
  iDestruct ((@gen_retri_update _ _ _ false true wh) with "Hretri Hσretri") as ">[Hσretri Hretri]".
  {
    eapply get_retri_gmap_lookup.
    exact Htrans.
  }
  rewrite update_offset_PC_preserve_retri update_access_batch_preserve_retri
  update_reg_global_preserve_retri update_transaction_update_retri
  fill_rx_unsafe_preserve_receivers write_mem_segment_unsafe_preserve_receivers.
  iFrame "Hσretri".
  rewrite update_offset_PC_preserve_trans' update_access_batch_preserve_trans'
          update_reg_global_preserve_trans' /get_transactions /=.
  (* update mem *)
  rewrite /write_mem_segment_unsafe /mem_region.
  iDestruct "Hmemdesrx" as "[%l0 [Hmemdesrx %Hlen']]".
  cbn.
   assert (Hlendesrxle: ((Z.of_nat (length desrx)) <= (page_size-1))%Z).
    {
      destruct Hseqrx as [? [HisSome Hltpagesize]].
      apply (finz_plus_Z_le (of_pid prx)); eauto.
      apply last_addr_in_bound.
      apply Z.leb_le.
      destruct (((prx ^+ length desrx)%f <=? (prx ^+ (page_size - 1))%f)%Z).
      done.
      contradiction.
    }
  iDestruct ((gen_mem_update_SepL2 (finz.seq prx (length l0)) l0 desrx) with "Hσmem Hmemdesrx")
    as ">[Hσmem Hmem]".
  { rewrite Hlen'.
    apply finz_seq_NoDup'.
    pose proof (last_addr_in_bound prx).
        solve_finz.
  }
  assumption.
  assert ((zip (finz.seq prx (length l0)) desrx) = (zip (finz.seq prx (Z.to_nat 1000)) desrx)) as ->.
  {
    rewrite -finz_seq_zip_page;auto.
    rewrite Hlen' //.
    lia.
  }
  cbn in Hdesrx.
  rewrite Hdesrx.
  iFrame "Hσmem".
  (* update page table *)
  rewrite update_offset_PC_preserve_owned update_access_batch_preserve_ownerships
          update_reg_global_preserve_owned update_transaction_preserve_owned
          fill_rx_unsafe_preserve_owned write_mem_segment_unsafe_preserve_owned.
  iFrame "Hσowned".
  rewrite update_offset_PC_preserve_access.
  destruct Htt as [(-> & ->& ->)|(-> & ->& ->)].
  {
    rewrite (@update_access_batch_update_pagetable_union _ i sacc ExclusiveAccess spsd psd Hpsd); f_equal;eauto.
    iDestruct ((gen_access_update_union spsd) with "Hacc Hσaccess") as ">[Hσaccess Hacc]";f_equal.
    {exact Hpsd. }
    rewrite update_reg_global_preserve_access update_transaction_preserve_access
    fill_rx_unsafe_preserve_access write_mem_segment_unsafe_preserve_access.
    iFrame "Hσaccess".
    rewrite update_offset_PC_preserve_excl.
    rewrite (@update_exclusive_batch_update_pagetable_union _ i sexcl spsd psd Hpsd);f_equal; eauto.
    iDestruct ((gen_excl_update_union spsd) with "Hexcl Hσexcl") as ">[Hσexcl Hexcl]"; f_equal.
    { exact Hpsd. }
    rewrite update_reg_global_preserve_excl update_transaction_preserve_excl
    fill_rx_unsafe_preserve_excl write_mem_segment_unsafe_preserve_excl.
    iFrame "Hσexcl".
    rewrite Hlen' -Hdesrx.
    iFrame "Htrans PC R0 Hrx1 Hrx2 Hretri Hmem Hacc Hexcl".
    iPureIntro.
    split;[rewrite get_trans_gmap_preserve_dom // |].
    apply map_Forall_insert_2; auto.
    simpl.
    rewrite <-Hlenl.
    destruct (finz_spec word_size l) as [H _].
    rewrite ->(reflect_iff _ _ (Z.ltb_spec0 l word_size)) in H.
    assumption.
  }
  {
    rewrite (@update_access_batch_update_pagetable_union _ i sacc SharedAccess spsd psd Hpsd); f_equal;eauto.
    iDestruct ((gen_access_update_union spsd) with "Hacc Hσaccess") as ">[Hσaccess Hacc]";f_equal.
    {exact Hpsd. }
    rewrite update_reg_global_preserve_access update_transaction_preserve_access
    fill_rx_unsafe_preserve_access write_mem_segment_unsafe_preserve_access.
    iFrame "Hσaccess".
    rewrite update_offset_PC_preserve_excl (@update_access_batch_preserve_excl spsd sexcl);auto.
    2: { rewrite update_reg_global_preserve_excl update_transaction_preserve_excl
    fill_rx_unsafe_preserve_excl write_mem_segment_unsafe_preserve_excl.
     rewrite update_reg_global_preserve_current_vm update_transaction_preserve_current_vm
    fill_rx_unsafe_preserve_current_vm write_mem_segment_unsafe_preserve_current_vm Hcureq //.
     }
    rewrite update_reg_global_preserve_excl update_transaction_preserve_excl
    fill_rx_unsafe_preserve_excl write_mem_segment_unsafe_preserve_excl.
    iFrame "Hσexcl".
    rewrite Hlen' -Hdesrx.
    iFrame "Htrans PC R0 Hrx1 Hrx2 Hretri Hmem Hacc Hexcl".
    iPureIntro.
    split;[rewrite get_trans_gmap_preserve_dom // |].
    apply map_Forall_insert_2; auto.
    simpl.
    rewrite <-Hlenl.
    destruct (finz_spec word_size l) as [H _].
    rewrite ->(reflect_iff _ _ (Z.ltb_spec0 l word_size)) in H.
    assumption.
  }
Qed.


Lemma hvc_retrieve_lend_share {tt sexcl' wi sown sacc pi sexcl i j destx wf' desrx ptx prx l} {spsd: gset PID}
      ai r0 r1 wh wf (psd: list PID) :
  (* the current instruction is hvc *)
  (* the decoding of wi is correct *)
  decode_instruction wi = Some(Hvc) ->
  tt = Lending ∧ sexcl' = (sexcl ∪ spsd) ∨ tt = Sharing ∧ sexcl' = sexcl->
  (* the instruction is in page pi *)
  addr_in_page ai pi ->
  (* the decoding of R0 is FFA_RETRIEVE *)
  decode_hvc_func r0 = Some(Retrieve) ->
  (* pi page in spsd is accessible for VM i *)
  pi ∈ sacc ->
  (* spsd is the gset of all to-be-donated pages *)
  spsd = (list_to_set psd) ->
  spsd ## sacc ->
  spsd ## sown ->
  spsd ## sexcl ->
  (finz.to_z l) = (Z.of_nat (length psd)) ->
  destx = ([of_imm (encode_vmid j); wf'; wh ;of_imm (encode_vmid i)] ) ->
  desrx = ([of_imm (encode_vmid j); wf; wh; encode_transaction_type tt;l] ++ map of_pid psd) ->
  (finz.to_z r1) = (Z.of_nat (length destx)) ->
  seq_in_page (of_pid ptx) (length destx) ptx ->
  seq_in_page (of_pid prx) (length desrx) prx ->
  {SS{{ ▷(PC @@ i ->r ai) ∗ ▷ ai ->a wi ∗ ▷ A@i:={1}[sacc]
  ∗ ▷ (R0 @@ i ->r r0) ∗ ▷ wh ->re false
  ∗ ▷ (R1 @@ i ->r r1) ∗ ▷ wh ->t{1}(j, wf, i, psd, tt)
  ∗ ▷ O@i:={1}[sown] ∗ ▷ E@i:={1}[sexcl] ∗ ▷ TX@ i := ptx
  ∗ ▷ mem_region destx ptx ∗ ▷ RX@ i :=( prx !) ∗ ▷ (∃l, mem_region l prx ∗ ⌜ length l = length desrx ⌝)}}}
   ExecI @ i {{{ RET ExecI ; PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi
  ∗ O@i:={1}[(sown)] ∗ E@i:={1}[sexcl'] ∗ A@i:={1}[(sacc ∪ spsd)]
  ∗ R0 @@ i ->r (encode_hvc_ret_code Succ) ∗ R1 @@ i ->r r1 ∗ wh ->t{1}(j, wf, i, psd, tt)
  ∗ wh ->re true ∗ TX@ i := ptx ∗ RX@ i :=( prx ! (l ^+ 5)%f, i)
  ∗ mem_region destx ptx ∗ mem_region desrx prx }}}.
Proof.
  iIntros (Hdecodei Htt Hinpi Hdecodef Hpiacc Hpsd Hsown Hsacc Hsexcl Hlenl Hdestx Hdesrx Hdestxl Hseqtx Hseqrx).
  iIntros (Φ) "(>PC & >Hai & >HA & >Hr0 & >Hwhf & >Hr1 & >Hwh & >HO & >HE & >HTX & >Hmemr & >HRX & >HRXCont) HΦ".
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
  iDestruct (gen_mem_valid_SepL_pure _ destx with "Hσmem Hmemr") as %Hadesc.
  { apply finz_seq_NoDup. destruct Hseqtx as [? [HisSome ?]]. done. }
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
    assert (Hlendesclt :((Z.of_nat (length destx)) <= (page_size-1))%Z).
    {
      destruct Hseqtx as [? [HisSome Hltpagesize]].
      apply (finz_plus_Z_le (of_pid ptx)); eauto.
      apply last_addr_in_bound.
      apply Z.leb_le.
      destruct (((ptx ^+ length destx)%f <=? (ptx ^+ (page_size - 1))%f)%Z).
      done.
      contradiction.
    }
    assert (Hlendesclt' :((Z.of_nat (length desrx)) <= (page_size-1))%Z).
    {
      destruct Hseqrx as [? [HisSome Hltpagesize]].
      apply (finz_plus_Z_le (of_pid prx)); eauto.
      apply last_addr_in_bound.
      apply Z.leb_le.
      destruct (((prx ^+ length desrx)%f <=? (prx ^+ (page_size - 1))%f)%Z).
      done.
      contradiction.
    }
    destruct (page_size <? r1)%Z eqn:Hr1ps; [lia|].
    rewrite /get_tx_pid_global Hcureq Htx in Heqc2.
    rewrite (@transaction_retrieve_descriptor_valid j wh wf' σ1 destx ptx) /= in Heqc2; eauto.
    2: { rewrite Hcureq; auto. }
    rewrite Htrans /= in Heqc2.
    rewrite -Hlenl finz_of_z_to_z in Heqc2.
    assert (finz.of_z (Z.of_nat (S (S (S (S (S (length (map of_pid psd)))))))) = Some (l ^+ 5%Z)%f).
    {  rewrite Hdesrx in Hseqrx. destruct Hseqrx as [_ [HisSome Hltpagesize]]. cbn in HisSome, Hltpagesize.
       assert (Heq: Z.of_nat(S (S (S (S (S (length (map of_pid psd)))))))
                    = ((Z.of_nat (length (map of_pid psd))) + 5%Z)%Z).
       lia.
       rewrite Heq map_length.
       rewrite -Hlenl.
       rewrite Heq map_length -Hlenl in Hltpagesize.
       rewrite Heq map_length -Hlenl in HisSome.
       pose proof (last_addr_in_bound prx).
       assert (Hle:( (finz.to_z l + 5)%Z <= (page_size-1)%Z)%Z).
       apply (finz_plus_Z_le (of_pid prx));auto.
       apply Z.leb_le.
       destruct ((((of_pid prx) ^+ (finz.to_z l + 5)%Z)%f <=?((of_pid prx) ^+ (page_size-1)%Z)%f)%Z)
                eqn:Heqn;[done|contradiction].
       unfold finz.of_z.
       destruct (decide (finz.to_z l + 5 < word_size)%Z) eqn:Hdecide.
       unfold decide  in Hdecide.
       unfold decide_rel in Hdecide.
       rewrite Hdecide.
       2: {  lia. }
       clear Hdecide.
       destruct (decide (0<= finz.to_z l + 5 )%Z) eqn:Hdecide.
       unfold decide  in Hdecide.
       unfold decide_rel in Hdecide.
       rewrite Hdecide /=.
       2: {  lia. }
       f_equal.
       apply finz_to_z_eq.
       cbn.
       solve_finz.
    }
    rewrite H in Heqc2. clear H.
    rewrite /fill_rx in Heqc2.
    assert (Htemp : ∀ σ dst ws i, get_vm_mail_box (write_mem_segment_unsafe σ dst ws) i =
                                  get_vm_mail_box σ i).
    f_equal.
    rewrite Htemp in Heqc2; clear Htemp.
    assert (Hmb :  get_vm_mail_box σ1 i = (ptx, (prx,None))).
    { destruct (get_vm_mail_box σ1 i).
      destruct r.
      cbn in Htx ,Hrx2, Hrx1.
      subst t0 o p.
      reflexivity.
    }
    rewrite /get_tx_pid_global /get_rx_pid_global Hmb /=  in Heqc2.
    assert (Hcheck: (i =? i)%nat = true).
    { apply <- Nat.eqb_eq. reflexivity. }
    rewrite Hcheck in Heqc2.
    pose proof Hretri1 as Hretri1'.
    pose proof Hretri2 as Hretri2'.
    rewrite Htrans in Hretri1.
    inversion Hretri1 as [Hretri1''].
    rewrite -Hretri1'' //= in Hretri2.
    subst b.
    rewrite -Hretri1 in Hretri1'.
    clear Hretri1.
    destruct c2 as [c21 c22].
    destruct Htt as [[Htt ->]|[Htt ->]];subst tt;
    rewrite/= in Heqc2;
    destruct HstepP; subst m2 σ2; rewrite Heqc2;
    simpl;clear Heqc2.
    {
    iDestruct ((retrieve_lend_share σ1 i Lending (sexcl ∪ spsd) ExclusiveAccess spsd psd)
                 with "PC HA HE Hr0 Hwh Hwhf HRX1 HRX2 HRXCont [Hcur Hσmem Hσreg Hσtx Hσrx1 Hσrx2 Hσowned Hσaccess Hσexcl Htrans Hσhp Hrcv]") as ">[Hσ Hres]";try done.
    left.
    repeat split;done.
    iFrame.
    done.
    iFrame "Hσ".
    iApply "HΦ".
    iFrame.
    iDestruct "Hres" as "(?&?&?&?&?&?&?&?&?)".
    rewrite Hdesrx.
    by iFrame.
    }
    {
    iDestruct ((retrieve_lend_share σ1 i Sharing sexcl SharedAccess spsd psd)
                 with "PC HA HE Hr0 Hwh Hwhf HRX1 HRX2 HRXCont [Hcur Hσmem Hσreg Hσtx Hσrx1 Hσrx2 Hσowned Hσaccess Hσexcl Htrans Hσhp Hrcv]") as ">[Hσ Hres]";try done.
    right;done.
    iFrame.
    done.
    iFrame "Hσ".
    iApply "HΦ".
    iFrame.
    iDestruct "Hres" as "(?&?&?&?&?&?&?&?&?)".
    rewrite Hdesrx.
    by iFrame.
    }
Qed.


Lemma hvc_retrieve_lend {wi sown sacc pi sexcl i j destx wf' desrx ptx prx l} {spsd: gset PID}
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
  destx = ([of_imm (encode_vmid j); wf'; wh ;of_imm (encode_vmid i)] ) ->
  desrx = ([of_imm (encode_vmid j); wf; wh; encode_transaction_type Lending;l] ++ map of_pid psd) ->
  (finz.to_z r1) = (Z.of_nat (length destx)) ->
  seq_in_page (of_pid ptx) (length destx) ptx ->
  seq_in_page (of_pid prx) (length desrx) prx ->
  {SS{{ ▷(PC @@ i ->r ai) ∗ ▷ ai ->a wi ∗ ▷ A@i:={1}[sacc]
  ∗ ▷ (R0 @@ i ->r r0) ∗ ▷ wh ->re false
  ∗ ▷ (R1 @@ i ->r r1) ∗ ▷ wh ->t{1}(j, wf, i, psd, Lending)
  ∗ ▷ O@i:={1}[sown] ∗ ▷ E@i:={1}[sexcl] ∗ ▷ TX@ i := ptx
  ∗ ▷ mem_region destx ptx ∗ ▷ RX@ i :=( prx !) ∗ ▷ (∃l, mem_region l prx ∗ ⌜ length l = length desrx ⌝)}}}
   ExecI @ i {{{ RET ExecI ; PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi
  ∗ O@i:={1}[(sown)] ∗ E@i:={1}[(sexcl ∪ spsd)] ∗ A@i:={1}[(sacc ∪ spsd)]
  ∗ R0 @@ i ->r (encode_hvc_ret_code Succ) ∗ R1 @@ i ->r r1 ∗ wh ->t{1}(j, wf, i, psd, Lending)
  ∗ wh ->re true ∗ TX@ i := ptx ∗ RX@ i :=( prx ! (l ^+ 5)%f, i)
  ∗ mem_region destx ptx ∗ mem_region desrx prx }}}.
Proof.
  iIntros (???????????????).
  iIntros "(?&?&?&?&?&?&?&?&?&?&?&?&?)".
  iApply hvc_retrieve_lend_share;auto.
  exact H0.
  exact H1.
  exact H2.
  exact H8.
  iFrame.
Qed.

Lemma hvc_retrieve_share { wi sown sacc pi sexcl i j destx wf' desrx ptx prx l} {spsd: gset PID}
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
  destx = ([of_imm (encode_vmid j); wf'; wh ;of_imm (encode_vmid i)] ) ->
  desrx = ([of_imm (encode_vmid j); wf; wh; encode_transaction_type Sharing;l] ++ map of_pid psd) ->
  (finz.to_z r1) = (Z.of_nat (length destx)) ->
  seq_in_page (of_pid ptx) (length destx) ptx ->
  seq_in_page (of_pid prx) (length desrx) prx ->
  {SS{{ ▷(PC @@ i ->r ai) ∗ ▷ ai ->a wi ∗ ▷ A@i:={1}[sacc]
  ∗ ▷ (R0 @@ i ->r r0) ∗ ▷ wh ->re false
  ∗ ▷ (R1 @@ i ->r r1) ∗ ▷ wh ->t{1}(j, wf, i, psd, Sharing)
  ∗ ▷ O@i:={1}[sown] ∗ ▷ E@i:={1}[sexcl] ∗ ▷ TX@ i := ptx
  ∗ ▷ mem_region destx ptx ∗ ▷ RX@ i :=( prx !) ∗ ▷ (∃l, mem_region l prx ∗ ⌜ length l = length desrx ⌝)}}}
   ExecI @ i {{{ RET ExecI ; PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi
  ∗ O@i:={1}[(sown)] ∗ E@i:={1}[sexcl] ∗ A@i:={1}[(sacc ∪ spsd)]
  ∗ R0 @@ i ->r (encode_hvc_ret_code Succ) ∗ R1 @@ i ->r r1 ∗ wh ->t{1}(j, wf, i, psd, Sharing)
  ∗ wh ->re true ∗ TX@ i := ptx ∗ RX@ i :=( prx ! (l ^+ 5)%f, i)
  ∗ mem_region destx ptx ∗ mem_region desrx prx }}}.
Proof.
  iIntros (???????????????).
  iIntros "(?&?&?&?&?&?&?&?&?&?&?&?&?)".
  iApply hvc_retrieve_lend_share;auto.
  exact H0.
  exact H1.
  exact H2.
  exact H8.
  iFrame.
Qed.

End retrieve.
