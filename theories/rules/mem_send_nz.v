From machine_program_logic.program_logic Require Import weakestpre.
From iris.algebra Require Import gset.
From HypVeri Require Import lifting rules.rules_base machine_extra.
From HypVeri.algebra Require Import base mem reg pagetable mailbox trans.
From HypVeri.lang Require Import lang_extra reg_extra mem_extra pagetable_extra trans_extra.

Section mem_send_nz.

Context `{hypparams: HypervisorParameters}.
Context `{vmG: !gen_VMG Σ}.

Lemma  mem_send_nz_not_share_update{i ai wi sown sacc sexcl r0 r1 r2 ptx sh q h fhs j psd spsd } {l:Word}  σ1 tt:
  get_current_vm σ1 = i ->
  (get_vm_mail_box σ1 i).1 = ptx ->
  (finz.to_z l) = (Z.of_nat (length psd)) ->
  spsd = ((list_to_set psd): gset PID) ->
  (elements sh) = h :: fhs ->
  (elements sh) = elements (get_transactions σ1).2 ->
  PC @@ i ->r ai -∗
  ai ->a wi -∗
  O@i:={q}[sown] -∗
  A@i:={1}[sacc] -∗
  E@i:={1}[sexcl] -∗
  R0 @@ i ->r r0-∗
  R1 @@ i ->r r1-∗
  R2 @@ i ->r r2-∗
  hp{1}[sh]-∗
  gen_vm_interp σ1 ={⊤}=∗
  gen_vm_interp
    (update_incr_PC (update_reg (update_reg
      (update_access_batch (alloc_transaction σ1 h (i, W0, false, j, psd, tt)) psd NoAccess) R0
      (encode_hvc_ret_code Succ)) R2 h))
  ∗ PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi
  ∗ O@i:={q}[sown] ∗ A@i:={1}[sacc∖spsd] ∗ E@i:={1}[sexcl∖spsd]
  ∗ R0 @@ i ->r (encode_hvc_ret_code Succ) ∗ R1 @@ i ->r r1
  ∗ ⌜h ∈ sh⌝ ∗ R2 @@ i ->r h ∗ h ->t{1}(i,W0,j , psd,tt)
  ∗ h ->re false  ∗ hp{1}[ (sh∖{[h]})].
Proof.
  iIntros (Hcur Htx Hlenpsd Hspsd Hfhs Hhp).
  iIntros "PC Hai Hown Hacc Hexcl R0 R1 R2 Hhp".
  iIntros "(Hcur & Hσmem & Hσreg & Hσtx & Hσrx1 & Hσrx2 & Hσowned & Hσaccess & Hσexcl & Htrans & Hσhp & %Hdisj & %Hσpsdl & Hrcv)".
  (* valid regs *)
  iDestruct ((gen_reg_valid1  R0 i r0 Hcur) with "Hσreg R0") as "%HR0";eauto.
  iDestruct ((gen_reg_valid1  R1 i r1 Hcur) with "Hσreg R1") as "%HR1";eauto.
  iDestruct ((gen_reg_valid1  R2 i r2 Hcur) with "Hσreg R2") as "%HR2";eauto.
  iDestruct ((gen_reg_valid1  PC i ai Hcur) with "Hσreg PC") as "%HPC";eauto.
  (* valid pt *)
  iDestruct ((gen_access_valid_pure sacc) with "Hσaccess Hacc") as %Hacc;eauto.
  iDestruct ((gen_excl_valid_pure sexcl) with "Hσexcl Hexcl") as %Hexcl';eauto.
  rewrite /gen_vm_interp /update_incr_PC /update_reg.
    (* unchanged part *)
    rewrite_reg_pc;
    rewrite_reg_global.
    rewrite update_access_batch_preserve_current_vm alloc_transaction_preserve_current_vm.
    rewrite_reg_global;
    rewrite_access_all;
    rewrite_trans_alloc.
    iFrame "Hcur Hσmem Hσtx Hσrx1 Hσrx2".
    rewrite Hcur.
    (* update regs *)
    rewrite (update_offset_PC_update_PC1 _ i ai 1);auto.
    rewrite !update_reg_global_update_reg update_access_batch_preserve_regs
            alloc_transaction_preserve_regs;try solve_reg_lookup.
    2 : {
      exists r2.
      rewrite lookup_insert_ne.
      solve_reg_lookup.
      done.
    }
    2 : {
      rewrite !update_reg_global_update_reg update_access_batch_preserve_regs
            alloc_transaction_preserve_regs;try solve_reg_lookup.
      rewrite !lookup_insert_ne; [solve_reg_lookup|done|done].
      exists r2.
      rewrite lookup_insert_ne;[solve_reg_lookup|done].
    }
     iDestruct ((gen_reg_update3_global PC i (ai ^+ 1)%f R2 i h R0 i (encode_hvc_ret_code Succ))
                  with "Hσreg PC R2 R0") as ">[Hσreg [PC [R2 R0]]]";eauto.
     iFrame "Hσreg".
     (* update page table *)
     rewrite (@update_access_batch_update_access_diff _ _ i sacc spsd psd);eauto.
     rewrite_trans_alloc.
     iDestruct ((gen_access_update_diff spsd) with "Hacc Hσaccess") as ">[Hσaccess Hacc]";eauto.
     rewrite Hcur.
     iFrame "Hσaccess".
     rewrite update_access_batch_preserve_ownerships alloc_transaction_preserve_owned.
     iFrame "Hσowned".
     rewrite (@update_access_batch_update_excl_diff _ _ i sexcl _ spsd psd);eauto.
     rewrite_trans_alloc.
     iDestruct ((gen_excl_update_diff spsd) with "Hexcl Hσexcl") as ">[Hσexcl Hexcl]";eauto.
     rewrite Hcur.
     iFrame "Hσexcl".
     (* update transactions *)
     rewrite alloc_transaction_update_trans /=.
     rewrite alloc_transaction_update_hpool /=.
     rewrite alloc_transaction_update_retri /=.
     assert (HhInfhs: h ∈ (get_transactions σ1).2). {
        rewrite /get_fresh_handles in Hhp.
        apply elem_of_elements.
        rewrite -Hhp Hfhs.
        apply <- (elem_of_cons fhs h h).
        left;done.
     }
     iDestruct ((gen_trans_update_insert h i W0 j psd tt) with "Htrans") as ">[Hσtrans Htran]".
     { apply not_elem_of_dom.
       rewrite get_trans_gmap_preserve_dom.
       set_solver.
     }
     assert (HhIn: h ∈ sh).
      { apply elem_of_elements.
       rewrite Hfhs.
       apply <- (elem_of_cons fhs h h).
       left;done.
     }
     iDestruct ((gen_hpool_update_diff h HhIn) with "Hhp Hσhp") as ">[Hσhp Hhp]".
     iDestruct ((gen_retri_update_insert h) with "Hrcv") as ">[Hσrtrv Hrtrv]".
     { apply not_elem_of_dom.
       rewrite get_retri_gmap_preserve_dom.
       set_solver.
     }
     iFrame "Hσrtrv Hσhp Hσtrans".
     iModIntro.
     iSplitR.
     iPureIntro.
     split.
     set_solver.
     apply map_Forall_insert_2; auto.
     simpl.
     rewrite -Hlenpsd.
     destruct (finz_spec l) as [Hf _].
     rewrite ->(reflect_iff _ _ (Z.ltb_spec0 l word_size)) in Hf.
     assumption.
     iFrame.
     done.
Qed.

Lemma  mem_send_nz_share_update{i ai wi sown sacc sexcl r0 r1 r2 ptx sh q h fhs j psd spsd } {l:Word}  σ1 tt:
  get_current_vm σ1 = i ->
  (get_vm_mail_box σ1 i).1 = ptx ->
  (finz.to_z l) = (Z.of_nat (length psd)) ->
  spsd = ((list_to_set psd): gset PID) ->
  (elements sh) = h :: fhs ->
  (elements sh) = elements (get_transactions σ1).2 ->
  spsd ⊆ sacc ->
  PC @@ i ->r ai -∗
  ai ->a wi -∗
  O@i:={q}[sown] -∗
  A@i:={1}[sacc] -∗
  E@i:={1}[sexcl] -∗
  R0 @@ i ->r r0-∗
  R1 @@ i ->r r1-∗
  R2 @@ i ->r r2-∗
  hp{1}[sh]-∗
  gen_vm_interp σ1 ={⊤}=∗
  gen_vm_interp
    (update_incr_PC (update_reg (update_reg
      (update_access_batch (alloc_transaction σ1 h (i, W0, false, j, psd, tt)) psd SharedAccess) R0
      (encode_hvc_ret_code Succ)) R2 h))
  ∗ PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi
  ∗ O@i:={q}[sown] ∗ A@i:={1}[sacc] ∗ E@i:={1}[sexcl∖spsd]
  ∗ R0 @@ i ->r (encode_hvc_ret_code Succ) ∗ R1 @@ i ->r r1
  ∗ ⌜h ∈ sh⌝ ∗ R2 @@ i ->r h ∗ h ->t{1}(i,W0,j , psd,tt)
  ∗ h ->re false  ∗ hp{1}[ (sh∖{[h]})].
Proof.
  iIntros (Hcur Htx Hlenpsd Hspsd Hfhs Hhp Hspsdacc).
  iIntros "PC Hai Hown Hacc Hexcl R0 R1 R2 Hhp".
  iIntros "(Hcur & Hσmem & Hσreg & Hσtx & Hσrx1 & Hσrx2 & Hσowned & Hσaccess & Hσexcl & Htrans & Hσhp & %Hdisj & %Hσpsdl & Hrcv)".
  (* valid regs *)
  iDestruct ((gen_reg_valid1  R0 i r0 Hcur) with "Hσreg R0") as "%HR0";eauto.
  iDestruct ((gen_reg_valid1  R1 i r1 Hcur) with "Hσreg R1") as "%HR1";eauto.
  iDestruct ((gen_reg_valid1  R2 i r2 Hcur) with "Hσreg R2") as "%HR2";eauto.
  iDestruct ((gen_reg_valid1  PC i ai Hcur) with "Hσreg PC") as "%HPC";eauto.
  (* valid pt *)
  iDestruct ((gen_access_valid_pure sacc) with "Hσaccess Hacc") as %Hacc;eauto.
  iDestruct ((gen_excl_valid_pure sexcl) with "Hσexcl Hexcl") as %Hexcl';eauto.
  rewrite /gen_vm_interp /update_incr_PC /update_reg.
    (* unchanged part *)
    rewrite_reg_pc;
    rewrite_reg_global.
    rewrite update_access_batch_preserve_current_vm alloc_transaction_preserve_current_vm.
    rewrite_reg_global;
    rewrite_access_all;
    rewrite_trans_alloc.
    iFrame "Hcur Hσmem Hσtx Hσrx1 Hσrx2".
    rewrite Hcur.
    (* update regs *)
    rewrite (update_offset_PC_update_PC1 _ i ai 1);auto.
    rewrite !update_reg_global_update_reg update_access_batch_preserve_regs
            alloc_transaction_preserve_regs;try solve_reg_lookup.
    2 : {
      exists r2.
      rewrite lookup_insert_ne.
      solve_reg_lookup.
      done.
    }
    2 : {
      rewrite !update_reg_global_update_reg update_access_batch_preserve_regs
            alloc_transaction_preserve_regs;try solve_reg_lookup.
      rewrite !lookup_insert_ne; [solve_reg_lookup|done|done].
      exists r2.
      rewrite lookup_insert_ne;[solve_reg_lookup|done].
    }
     iDestruct ((gen_reg_update3_global PC i (ai ^+ 1)%f R2 i h R0 i (encode_hvc_ret_code Succ))
                  with "Hσreg PC R2 R0") as ">[Hσreg [PC [R2 R0]]]";eauto.
     iFrame "Hσreg".
     (* update page table *)
     iFrame "Hacc".
     rewrite update_access_batch_preserve_ownerships alloc_transaction_preserve_owned.
     iFrame "Hσowned".
     rewrite (@update_access_batch_update_excl_diff _ _ i sexcl SharedAccess spsd psd);eauto.
     rewrite_trans_alloc.
     iDestruct ((gen_excl_update_diff spsd) with "Hexcl Hσexcl") as ">[Hσexcl Hexcl]";eauto.
     rewrite Hcur.
     iFrame "Hσexcl".
     (* update transactions *)
     rewrite alloc_transaction_update_trans /=.
     rewrite alloc_transaction_update_hpool /=.
     rewrite alloc_transaction_update_retri /=.
     assert (HhInfhs: h ∈ (get_transactions σ1).2). {
        rewrite /get_fresh_handles in Hhp.
        apply elem_of_elements.
        rewrite -Hhp Hfhs.
        apply <- (elem_of_cons fhs h h).
        left;done.
     }
     iDestruct ((gen_trans_update_insert h i W0 j psd tt) with "Htrans") as ">[Hσtrans Htran]".
     { apply not_elem_of_dom.
       rewrite get_trans_gmap_preserve_dom.
       set_solver.
     }
     assert (HhIn: h ∈ sh).
      { apply elem_of_elements.
       rewrite Hfhs.
       apply <- (elem_of_cons fhs h h).
       left;done.
     }
     iDestruct ((gen_hpool_update_diff h HhIn) with "Hhp Hσhp") as ">[Hσhp Hhp]".
     iDestruct ((gen_retri_update_insert h) with "Hrcv") as ">[Hσrtrv Hrtrv]".
     { apply not_elem_of_dom.
       rewrite get_retri_gmap_preserve_dom.
       set_solver.
     }
     iFrame "Hσrtrv Hσhp Hσtrans".
     iModIntro.
     rewrite (@update_access_batch_update_pagetable_idempotent _ (alloc_transaction σ1 h (i, W0, false, j, psd, tt)) i sacc SharedAccess spsd); eauto.
     rewrite_trans_alloc.
     iFrame "Hσaccess".
     iSplitR.
     iPureIntro.
     split.
     set_solver.
     apply map_Forall_insert_2; auto.
     simpl.
     rewrite -Hlenpsd.
     destruct (finz_spec l) as [Hf _].
     rewrite ->(reflect_iff _ _ (Z.ltb_spec0 l word_size)) in Hf.
     assumption.
     iFrame.
     done.
Qed.

Inductive not_share_view_spec : transaction_type -> Type :=
| NotShareP t : t = Lending \/ t = Donation -> not_share_view_spec t
| ShareP t : t = Sharing -> not_share_view_spec t.

Lemma not_share_viewP z : not_share_view_spec z.
Proof. destruct z; [ constructor | constructor 2 | constructor ]; auto. Qed.

Lemma hvc_mem_send_not_share_nz tt i wi r2 ptx sown q sacc sexcl des sh hvcf  (l :Word) (spsd: gset PID)
      ai r0 r1 j (psd: list PID) :
  tt ≠ Sharing ->
  (* the decoding of wi is correct *)
  decode_instruction wi = Some(Hvc) ->
  (* the decoding of R0 is a FFA mem send *)
  decode_hvc_func r0 = Some(hvcf) ->
  hvcf_to_tt hvcf = Some tt ->
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
  {[to_pid_aligned ai]} ∪ spsd ⊆ sacc ->
  (* VM i owns pages in spsd *)
  spsd ⊆ sown ->
  (* pages in spsed are exclusive to VM i *)
  spsd ⊆ sexcl ->
  (* there is at least one free handle in the hpool *)
  sh ≠ ∅ ->
  {SS{{ ▷(PC @@ i ->r ai) ∗ ▷ ai ->a wi
  ∗ ▷ O@i:={q}[sown] ∗ ▷ A@i:={1}[sacc] ∗ ▷ E@i:={1}[sexcl]
  ∗ ▷ (R0 @@ i ->r r0) ∗ ▷ (R1 @@ i ->r r1) ∗ ▷(R2 @@i ->r r2) ∗  ▷ TX@ i := ptx
  ∗ ▷ mem_region des ptx
  ∗ ▷ hp{ 1 }[ sh ] }}}
   ExecI @ i {{{ RET ExecI ; PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi
  ∗ O@i:={q}[sown] ∗ A@i:={1}[sacc∖spsd] ∗ E@i:={1}[sexcl∖spsd]
  ∗ R0 @@ i ->r (encode_hvc_ret_code Succ) ∗ R1 @@ i ->r r1  ∗ TX@ i := ptx
  ∗ ∃(wh: Word), ( ⌜ wh ∈ sh ⌝ ∗ R2 @@ i ->r wh ∗ wh ->t{1}(i,W0,j , psd,tt)
  ∗ wh ->re false  ∗ hp{1}[ (sh∖{[wh]})] )
  ∗ mem_region des ptx}}}.
Proof.
  iIntros (Hnshar Hdecodei Hdecodef Hismemsend Hneq Hlenpsd Hdesc Hindesc Hlenr1 Hspsd Hsacc Hsown Hsexcl Hshne).
  iIntros (Φ) "(>PC & >Hai & >Hown & >Hacc & >Hexcl & >R0 & >R1 & >R2 & >TX & >Hadesc & >Hhp ) HΦ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [ Hcureq ]; clear Hsche.
  apply fin_to_nat_inj in Hcureq.
  iModIntro.
  iDestruct "Hσ" as "(Hcur & Hσmem & Hσreg & Hσtx & Hσrx1 & Hσrx2 & Hσowned & Hσaccess & Hσexcl & Htrans & Hσhp & %Hdisj & %Hσpsdl & Hrcv)".
  (* valid regs *)
  iDestruct ((gen_reg_valid3 i PC ai R0 r0 R1 r1 Hcureq) with "Hσreg PC R0 R1") as "(%HPC & %HR0 & %HR1)";eauto.
  (* valid pt *)
  iDestruct ((gen_access_valid_addr_elem ai sacc) with "Hσaccess Hacc") as %Haccai;eauto.
  { set_solver. }
  iDestruct ((gen_own_valid_SepS_pure sown) with "Hσowned Hown") as %Hown;eauto.
  iDestruct ((gen_excl_valid_SepS_pure sexcl) with "Hσexcl Hexcl") as %Hexcl;eauto.
  (* valid mem *)
  iDestruct (gen_mem_valid ai wi with "Hσmem Hai") as %Hai.
  unfold mem_region.
  iDestruct (gen_mem_valid_SepL_pure _ des with "Hσmem Hadesc") as %Hadesc.
  { apply finz_seq_NoDup'. destruct Hindesc as [_ [_ [HisSome _]]]. solve_finz. }
  (* valid tx *)
  iDestruct (gen_tx_valid with "TX Hσtx") as %Htx.
  (* valid hpool *)
  iDestruct (gen_hpool_valid_elem with "Hhp Hσhp") as %Hhp.
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal i Hvc ai wi);eauto.
  - (* step *)
    iModIntro.
    iIntros (m2 σ2) "%HstepP".
    apply (step_ExecI_normal i Hvc ai wi) in HstepP;eauto.
    remember (exec Hvc σ1) as c2 eqn:Heqc2.
    assert (Hlendesclt :((Z.of_nat (length des) -1) <= (page_size-1))%Z).
    {  destruct Hindesc as [? [? [HisSome Hltpagesize]]].
       apply (finz_plus_Z_le (of_pid ptx));eauto.
       apply last_addr_in_bound.
       rewrite /Is_true in Hltpagesize.
       case_match;[|done].
       apply Z.leb_le in Heqb.
       done.
    }
    rewrite /exec /hvc HR0 Hdecodef /mem_send //= HR1 /= in Heqc2.
    destruct (page_size <? r1)%Z eqn:Heqn;[lia|clear Heqn].
    rewrite Hcureq /get_tx_pid_global Htx (@transaction_descriptor_valid _ _ i j W0 l psd σ1 des) /= in Heqc2;eauto.
    assert (Hcheck : (i =? i)%nat = true).
    { by apply   <- Nat.eqb_eq. }
    rewrite Hcureq Hcheck /= in Heqc2;clear Hcheck.
    assert (Hcheck:  negb (i =? j)%nat = true).
       {apply negb_true_iff. apply  <- Nat.eqb_neq. intro. apply Hneq. by apply fin_to_nat_inj.  }
    rewrite Hcheck /= in Heqc2;clear Hcheck.
    destruct (forallb (λ v' : PID, check_perm_page σ1 i v' (Owned, ExclusiveAccess))
                                    psd) eqn:HCheck.
    2: {
      apply not_true_iff_false in HCheck.
      exfalso.
      apply HCheck.
      apply forallb_forall.
      intros ? HxIn.
      unfold check_perm_page.
      apply elem_of_list_In in HxIn.
      apply (elem_of_list_to_set (C:= gset PID)) in HxIn.
      rewrite <- Hspsd in HxIn.
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
    destruct (elements sh) as [| h fhs] eqn:Hfhs .
    { exfalso. rewrite -elements_empty in Hfhs.  apply Hshne. apply set_eq.
     intro. rewrite -elem_of_elements Hfhs elem_of_elements.   split;intro;set_solver. }
    rewrite -Hhp //=  in Heqc2.
    destruct (not_share_viewP tt) as [? o | ? o]; [| done].
    destruct hvcf; try inversion Hismemsend; subst t;
      destruct HstepP;subst m2 σ2; subst c2; simpl; try done; destruct o; try done.
    { iDestruct (mem_send_nz_not_share_update with "PC Hai Hown Hacc Hexcl R0 R1 R2 Hhp
        [Hcur Hσmem Hσreg Hσtx Hσrx1 Hσrx2 Hσowned Hσaccess Hσexcl Htrans Hσhp Hrcv]")
          as ">[Hσ' (? &?&?&?&?&?&?&?&?&?&?&?)]";eauto.
      rewrite Hfhs //.
      rewrite /gen_vm_interp.
      iFrame.
      done.
      iModIntro.
      iSplitL "Hσ'".
      iExact "Hσ'".
      iApply "HΦ".
      iFrame.
      iExists h.
      iFrame.
    }
    { iDestruct (mem_send_nz_not_share_update with "PC Hai Hown Hacc Hexcl R0 R1 R2 Hhp
        [Hcur Hσmem Hσreg Hσtx Hσrx1 Hσrx2 Hσowned Hσaccess Hσexcl Htrans Hσhp Hrcv]")
          as ">[Hσ' (? &?&?&?&?&?&?&?&?&?&?&?)]";eauto.
      rewrite Hfhs //.
      rewrite /gen_vm_interp.
      iFrame.
      done.
      iModIntro.
      iSplitL "Hσ'".
      iExact "Hσ'".
      iApply "HΦ".
      iFrame.
      iExists h.
      iFrame.
    }
Qed.

Lemma hvc_mem_send_share_nz tt i wi r2 ptx sown q sacc sexcl des sh hvcf  (l :Word) (spsd: gset PID)
      ai r0 r1 j (psd: list PID) :
  tt = Sharing ->
  (* the decoding of wi is correct *)
  decode_instruction wi = Some(Hvc) ->
  (* the decoding of R0 is a FFA mem send *)
  decode_hvc_func r0 = Some(hvcf) ->
  hvcf_to_tt hvcf = Some tt ->
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
  {[to_pid_aligned ai]} ∪ spsd ⊆ sacc ->
  (* VM i owns pages in spsd *)
  spsd ⊆ sown ->
  (* pages in spsed are exclusive to VM i *)
  spsd ⊆ sexcl ->
  (* there is at least one free handle in the hpool *)
  sh ≠ ∅ ->
  {SS{{ ▷(PC @@ i ->r ai) ∗ ▷ ai ->a wi
  ∗ ▷ O@i:={q}[sown] ∗ ▷ A@i:={1}[sacc] ∗ ▷ E@i:={1}[sexcl]
  ∗ ▷ (R0 @@ i ->r r0) ∗ ▷ (R1 @@ i ->r r1) ∗ ▷(R2 @@i ->r r2) ∗  ▷ TX@ i := ptx
  ∗ ▷ mem_region des ptx
  ∗ ▷ hp{ 1 }[ sh ] }}}
   ExecI @ i {{{ RET ExecI ; PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi
  ∗ O@i:={q}[sown] ∗ A@i:={1}[sacc] ∗ E@i:={1}[sexcl∖spsd]
  ∗ R0 @@ i ->r (encode_hvc_ret_code Succ) ∗ R1 @@ i ->r r1  ∗ TX@ i := ptx
  ∗ ∃(wh: Word), ( ⌜ wh ∈ sh ⌝ ∗ R2 @@ i ->r wh ∗ wh ->t{1}(i,W0,j , psd,tt)
  ∗ wh ->re false  ∗ hp{1}[ (sh∖{[wh]})] )
  ∗ mem_region des ptx}}}.
Proof.
  iIntros (Hnshar Hdecodei Hdecodef Hismemsend Hneq Hlenpsd Hdesc Hindesc Hlenr1 Hspsd Hsacc Hsown Hsexcl Hshne).
  iIntros (Φ) "(>PC & >Hai & >Hown & >Hacc & >Hexcl & >R0 & >R1 & >R2 & >TX & >Hadesc & >Hhp ) HΦ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [ Hcureq ]; clear Hsche.
  apply fin_to_nat_inj in Hcureq.
  iModIntro.
  iDestruct "Hσ" as "(Hcur & Hσmem & Hσreg & Hσtx & Hσrx1 & Hσrx2 & Hσowned & Hσaccess & Hσexcl & Htrans & Hσhp & %Hdisj & %Hσpsdl & Hrcv)".
  (* valid regs *)
  iDestruct ((gen_reg_valid3 i PC ai R0 r0 R1 r1 Hcureq) with "Hσreg PC R0 R1") as "(%HPC & %HR0 & %HR1)";eauto.
  (* valid pt *)
  iDestruct ((gen_access_valid_addr_elem ai sacc) with "Hσaccess Hacc") as %Haccai;eauto.
  { set_solver. }
  iDestruct ((gen_own_valid_SepS_pure sown) with "Hσowned Hown") as %Hown;eauto.
  iDestruct ((gen_excl_valid_SepS_pure sexcl) with "Hσexcl Hexcl") as %Hexcl;eauto.
  (* valid mem *)
  iDestruct (gen_mem_valid ai wi with "Hσmem Hai") as %Hai.
  unfold mem_region.
  iDestruct (gen_mem_valid_SepL_pure _ des with "Hσmem Hadesc") as %Hadesc.
  { apply finz_seq_NoDup'. destruct Hindesc as [_ [_ [HisSome _]]]. solve_finz. }
  (* valid tx *)
  iDestruct (gen_tx_valid with "TX Hσtx") as %Htx.
  (* valid hpool *)
  iDestruct (gen_hpool_valid_elem with "Hhp Hσhp") as %Hhp.
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal i Hvc ai wi);eauto.
  - (* step *)
    iModIntro.
    iIntros (m2 σ2) "%HstepP".
    apply (step_ExecI_normal i Hvc ai wi) in HstepP;eauto.
    remember (exec Hvc σ1) as c2 eqn:Heqc2.
    assert (Hlendesclt :((Z.of_nat (length des) -1) <= (page_size-1))%Z).
    {  destruct Hindesc as [? [? [HisSome Hltpagesize]]].
       apply (finz_plus_Z_le (of_pid ptx));eauto.
       apply last_addr_in_bound.
       rewrite /Is_true in Hltpagesize.
       case_match;[|done].
       apply Z.leb_le in Heqb.
       done.
    }
    rewrite /exec /hvc HR0 Hdecodef /mem_send //= HR1 /= in Heqc2.
    destruct (page_size <? r1)%Z eqn:Heqn;[lia|clear Heqn].
    rewrite Hcureq /get_tx_pid_global Htx (@transaction_descriptor_valid _ _ i j W0 l psd σ1 des) /= in Heqc2;eauto.
    assert (Hcheck : (i =? i)%nat = true).
    { by apply   <- Nat.eqb_eq. }
    rewrite Hcureq Hcheck /= in Heqc2;clear Hcheck.
    assert (Hcheck:  negb (i =? j)%nat = true).
    { apply negb_true_iff. apply  <- Nat.eqb_neq. intro. apply Hneq. by apply fin_to_nat_inj. }
    rewrite Hcheck /= in Heqc2;clear Hcheck.
    destruct (forallb (λ v' : PID, check_perm_page σ1 i v' (Owned, ExclusiveAccess)) psd) eqn:HCheck.
    2: {
      apply not_true_iff_false in HCheck.
      exfalso.
      apply HCheck.
      apply forallb_forall.
      intros ? HxIn.
      unfold check_perm_page.
      apply elem_of_list_In in HxIn.
      apply (elem_of_list_to_set (C:= gset PID)) in HxIn.
      rewrite <- Hspsd in HxIn.
      assert (HxInown: x ∈ sown). { set_solver. }
      assert (HxInexcl: x ∈ sexcl). { set_solver. }
      pose proof (Hown x HxInown) as Hxown.
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
    destruct (elements sh) as [| h fhs] eqn:Hfhs .
    { exfalso. rewrite -elements_empty in Hfhs.  apply Hshne. apply set_eq.
    intro. rewrite -elem_of_elements Hfhs elem_of_elements.   split;intro;set_solver. }
    rewrite -Hhp //=  in Heqc2.
    destruct (not_share_viewP tt) as [? o | ? o]; [destruct o; simplify_eq; discriminate|].
    destruct hvcf; try inversion Hismemsend; subst t;
      destruct HstepP;subst m2 σ2; subst c2; simpl; try done; destruct o; try done.
    iDestruct (mem_send_nz_share_update with "PC Hai Hown Hacc Hexcl R0 R1 R2 Hhp
        [Hcur Hσmem Hσreg Hσtx Hσrx1 Hσrx2 Hσowned Hσaccess Hσexcl Htrans Hσhp Hrcv]")
          as ">[Hσ' (? &?&?&?&?&?&?&?&?&?&?&?)]";eauto.
    rewrite Hfhs //.
    rewrite ->union_subseteq in Hsacc; destruct Hsacc; auto.
    rewrite /gen_vm_interp.
    iFrame.
    done.
    iModIntro.
    iSplitL "Hσ'".
    iExact "Hσ'".
    iApply "HΦ".
    iFrame.
    iExists h.
    iFrame.
Qed.


Lemma hvc_donate_nz {i ai wi r2 ptx sown q sacc sexcl des sh}
      {r0 r1} j (l :Word) (psd: list PID) (spsd: gset PID):
  (* the decoding of wi is correct *)
  decode_instruction wi = Some(Hvc) ->
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
  {[to_pid_aligned ai]} ∪ spsd ⊆ sacc ->
  (* VM i owns pages in spsd *)
  spsd ⊆ sown ->
  (* pages in spsed are exclusive to VM i *)
  spsd ⊆ sexcl ->
  (* there are at least one free handles in the hpool *)
  sh ≠ ∅ ->
  {SS{{ ▷(PC @@ i ->r ai) ∗ ▷ ai ->a wi
  ∗ ▷ O@i:={q}[sown] ∗ ▷ A@i:={1}[sacc] ∗ ▷ E@i:={1}[sexcl]
  ∗ ▷ (R0 @@ i ->r r0) ∗ ▷ (R1 @@ i ->r r1) ∗ ▷(R2 @@i ->r r2) ∗  ▷ TX@ i := ptx
  ∗ ▷ mem_region des ptx
  ∗ ▷ hp{ 1 }[ sh ] }}}
   ExecI @ i {{{ RET ExecI ; PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi
  ∗ O@i:={q}[sown] ∗ A@i:={1}[sacc∖spsd] ∗ E@i:={1}[sexcl∖spsd]
  ∗ R0 @@ i ->r (encode_hvc_ret_code Succ) ∗ R1 @@ i ->r r1  ∗ TX@ i := ptx
  ∗ ∃(wh: Word), ( ⌜ wh ∈ sh ⌝ ∗ R2 @@ i ->r wh ∗ wh ->t{1}(i,W0, j , psd,Donation)
  ∗ wh ->re false  ∗ hp{1}[ (sh∖{[wh]})] )
  ∗ mem_region des ptx}}}.
Proof.
  iIntros (Hdecodei Hdecodef Hneq Hlenpsd Hdesc Hindesc Hlenr1 Hspsd Hsacc Hsown Hsexcl Hshne Φ).
  iApply ((hvc_mem_send_not_share_nz Donation i wi r2 ptx sown q sacc sexcl des sh Donate l spsd ai r0 r1 j psd));auto.
Qed.

Lemma hvc_share_nz {i ai wi r2 ptx sown q sacc sexcl des sh}
      {r0 r1} j (l :Word) (psd: list PID) (spsd: gset PID):
  (* the decoding of wi is correct *)
  decode_instruction wi = Some(Hvc) ->
  (* the decoding of R0 is FFA_SHARE *)
  decode_hvc_func r0 = Some(Share) ->
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
  {[to_pid_aligned ai]} ∪ spsd ⊆ sacc ->
  (* VM i owns pages in spsd *)
  spsd ⊆ sown ->
  (* pages in spsed are exclusive to VM i *)
  spsd ⊆ sexcl ->
  (* there are at least one free handles in the hpool *)
  sh ≠ ∅ ->
  {SS{{ ▷(PC @@ i ->r ai) ∗ ▷ ai ->a wi
  ∗ ▷ O@i:={q}[sown] ∗ ▷ A@i:={1}[sacc] ∗ ▷ E@i:={1}[sexcl]
  ∗ ▷ (R0 @@ i ->r r0) ∗ ▷ (R1 @@ i ->r r1) ∗ ▷(R2 @@i ->r r2) ∗  ▷ TX@ i := ptx
  ∗ ▷ mem_region des ptx
  ∗ ▷ hp{ 1 }[ sh ] }}}
   ExecI @ i {{{ RET ExecI ; PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi
  ∗ O@i:={q}[sown] ∗ A@i:={1}[sacc] ∗ E@i:={1}[sexcl∖spsd]
  ∗ R0 @@ i ->r (encode_hvc_ret_code Succ) ∗ R1 @@ i ->r r1  ∗ TX@ i := ptx
  ∗ ∃(wh: Word), ( ⌜ wh ∈ sh ⌝ ∗ R2 @@ i ->r wh ∗ wh ->t{1}(i,W0, j , psd,Sharing)
  ∗ wh ->re false  ∗ hp{1}[ (sh∖{[wh]})] )
  ∗ mem_region des ptx}}}.
Proof.
  iIntros (Hdecodei Hdecodef Hneq Hlenpsd Hdesc Hindesc Hlenr1 Hspsd Hsacc Hsown Hsexcl Hshne Φ ).
  iApply ((hvc_mem_send_share_nz Sharing i wi r2 ptx sown q sacc sexcl des sh Share l spsd ai r0 r1 j psd));auto.
Qed.

Lemma hvc_lend_nz {i ai wi r2 ptx sown q sacc sexcl des sh}
      {r0 r1} j (l :Word) (psd: list PID) (spsd: gset PID):
  (* the decoding of wi is correct *)
  decode_instruction wi = Some(Hvc) ->
  (* the decoding of R0 is FFA_LEND *)
  decode_hvc_func r0 = Some(Lend) ->
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
  {[to_pid_aligned ai]} ∪ spsd ⊆ sacc ->
  (* VM i owns pages in spsd *)
  spsd ⊆ sown ->
  (* pages in spsed are exclusive to VM i *)
  spsd ⊆ sexcl ->
  (* there are at least one free handles in the hpool *)
  sh ≠ ∅ ->
  {SS{{ ▷(PC @@ i ->r ai) ∗ ▷ ai ->a wi
  ∗ ▷ O@i:={q}[sown] ∗ ▷ A@i:={1}[sacc] ∗ ▷ E@i:={1}[sexcl]
  ∗ ▷ (R0 @@ i ->r r0) ∗ ▷ (R1 @@ i ->r r1) ∗ ▷(R2 @@i ->r r2) ∗  ▷ TX@ i := ptx
  ∗ ▷ mem_region des ptx
  ∗ ▷ hp{ 1 }[ sh ] }}}
   ExecI @ i {{{ RET ExecI ; PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi
  ∗ O@i:={q}[sown] ∗ A@i:={1}[sacc∖spsd] ∗ E@i:={1}[sexcl∖spsd]
  ∗ R0 @@ i ->r (encode_hvc_ret_code Succ) ∗ R1 @@ i ->r r1  ∗ TX@ i := ptx
  ∗ ∃(wh: Word), ( ⌜ wh ∈ sh ⌝ ∗ R2 @@ i ->r wh ∗ wh ->t{1}(i,W0, j , psd,Lending)
  ∗ wh ->re false  ∗ hp{1}[ (sh∖{[wh]})] )
  ∗ mem_region des ptx}}}.
Proof.
  iIntros (Hdecodei Hdecodef Hneq Hlenpsd Hdesc Hindesc Hlenr1 Hspsd Hsacc Hsown Hsexcl Hshne Φ ).
  iApply ((hvc_mem_send_not_share_nz Lending i wi r2 ptx sown q sacc sexcl des sh Lend l spsd ai r0 r1 j psd));auto.
Qed.


End mem_send_nz.
