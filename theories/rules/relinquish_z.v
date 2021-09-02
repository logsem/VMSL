From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base stdpp_extra.
From HypVeri.algebra Require Import base reg mem pagetable trans mailbox.
From HypVeri.lang Require Import lang_extra mem_extra reg_extra pagetable_extra trans_extra.

Section relinquish_z.

Context `{vmG: !gen_VMG Σ}.

Lemma hvc_relinquish_z {tt wi sacc pi sexcl i j des ptx} {spsd: gset PID}
      ai r0 wh wf (psd: list PID) :
  (* current instruction is hvc *)
  decode_instruction wi = Some(Hvc) ->
  (* the location of instruction is in page pi *)
  addr_in_page ai pi ->
  (* the hvc call to invoke is relinquish *)
  decode_hvc_func r0 = Some(Relinquish) ->
  (* has access to the page which the instruction is in *)
  pi ∈ sacc ->
  (* the descriptor contains a handle and a zero-flag which is set *)
  des = [wh; W1] ->
  (* the whole descriptor resides in the TX page *)
  seq_in_page (of_pid ptx) (length des) ptx ->
  (* the set of pids that are involved in this transaction *)
  spsd = (list_to_set psd) ->
  (* XXX: do we need spsd ## sown ? *)
  (* must have access to these involved pages *)
  spsd ⊆ sacc ->
  (* for lending, has *exclusive* access *)
  tt = Lending ∧ spsd ⊆ sexcl
  (* for sharing, has *shared* access *)
   ∨ tt = Sharing ∧ spsd ## sexcl ->
  {SS{{(* the encoding of instruction wi is stored in location ai *)
       ▷(PC @@ i ->r ai) ∗ ▷ (R0 @@ i ->r r0) ∗ ▷ ai ->a wi ∗
       (* the pagetable, the owership ra is not required *)
       ▷ A@i:={1}[sacc] ∗ ▷ E@i:={1}[sexcl] ∗
       (* the descriptor is ready in the tx page *)
       ▷ TX@ i := ptx ∗ ▷ mem_region des ptx ∗
       (* is the receiver and the transaction has been retrieved *)
       ▷ wh ->t{1}(j, wf, i, psd, tt) ∗ ▷ wh ->re true ∗
       (* involved pages *)
       (▷ ∃ wss, ([∗ list] p;ws ∈ psd;wss, mem_page ws p))}}}
  ExecI @ i
  {{{ RET ExecI ;
      (* PC is incremented *)
      PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi ∗
      (* donesn't have access to psd anymore *)
      E@i:={1}[sexcl∖spsd] ∗ A@i:={1}[sacc∖spsd] ∗
      (* return Succ to R0 *)
      R0 @@ i ->r (encode_hvc_ret_code Succ) ∗
      (* the transaction is marked as unretrieved *)
      wh ->t{1}(j, wf, i, psd, tt) ∗ wh ->re false ∗
      (* the same tx *)
      TX@ i := ptx ∗ mem_region des ptx ∗
      (* all involved pages are zeroed *)
      ([∗ list] p;ws ∈ psd;(pages_of_W0 (length psd)), mem_page ws p)}}}.
Proof.
  iIntros (Hdecodei Hinpi Hdecodef Hinai Hdesc Hindesc Hspsd Hsacc Hsexcl Φ).
  iIntros "(>PC & >R0 & >Hai & >Hacc & >Hexcl & >TX & >Hadesc & >Htrans & >Hretri & Hpgs) HΦ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [ Hcureq ]; clear Hsche.
  apply fin_to_nat_inj in Hcureq.
  iModIntro.
  iDestruct "Hσ" as "(Hcur & Hσmem & Hσreg & Hσtx & Hσrx1 & Hσrx2 & Hσowned
         & Hσaccess & Hσexcl & Hσtrans & Hσhp & %Hdisj & %Hσpsdl & Hσretri)".
  (* valid regs *)
  iDestruct ((gen_reg_valid2 i PC ai R0 r0 Hcureq) with "Hσreg PC R0 ") as "(%HPC & %HR0)";eauto.
  (* valid pt *)
  iDestruct ((gen_access_valid_addr_elem ai sacc) with "Hσaccess Hacc") as %Haccai;eauto.
  { rewrite (to_pid_aligned_in_page _ pi);eauto. }
  (* iDestruct ((gen_own_valid_SepS_pure sown) with "Hσowned Hown") as %Hown;eauto. *)
  iDestruct ((gen_access_valid_pure sacc) with "Hσaccess Hacc") as %Hacc;eauto.
  iDestruct ((gen_excl_valid_pure sexcl) with "Hσexcl Hexcl") as %Hexcl;eauto.
  (* valid mem *)
  iDestruct (gen_mem_valid ai wi with "Hσmem Hai") as %Hai.
  unfold mem_region.
  iDestruct (gen_mem_valid_SepL_pure _ des with "Hσmem Hadesc") as %Hadesc.
  { apply finz_seq_NoDup. destruct Hindesc as [? [HisSome ?]]. done. }
  (* valid tx *)
  iDestruct (gen_tx_valid with "TX Hσtx") as %Htx.
  (* valid hpool *)
  iDestruct (gen_trans_valid with "Htrans Hσtrans") as %[? Htrans].
  iDestruct (gen_retri_valid with "Hretri Hσretri") as %[? [Hretri Hretrieved]].
  rewrite Hretri in Htrans.
  destruct x.
  2: { inversion Htrans. rewrite H0 in Hretrieved. done. }
  rewrite Htrans in Hretri.
  clear x0 Hretrieved Htrans.
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal i Hvc ai wi);eauto.
  - (* step *)
    iModIntro.
    iIntros (m2 σ2) "%HstepP".
    apply (step_ExecI_normal i Hvc ai wi) in HstepP;eauto.
    remember (exec Hvc σ1) as c2 eqn:Hexec.
    rewrite /exec /hvc HR0 Hdecodef /relinquish /= Hcureq /get_tx_pid_global Htx in Hexec.
    assert (Hlkwh:  (get_memory_with_offset σ1 ptx 0) = Some wh).
    {
    rewrite /get_memory_with_offset /=.
    assert (((of_pid ptx) + 0)%f = Some (of_pid ptx)) as ->. solve_finz.
    eapply (Hadesc 0).
    destruct Hindesc as [_ [HisSome Hltdeslen]].
    apply finz_seq_lookup;try lia.
    destruct des;[done|simpl;lia].
    solve_finz.
    by simplify_list_eq.
    }
    assert (Hlkwf: (get_memory_with_offset σ1 ptx 1) = Some W1).
    {
    rewrite /get_memory_with_offset /=.
    pose proof (last_addr_in_bound ptx).
    assert (((of_pid ptx) + 1)%f = Some (of_pid ptx ^+ 1)%f) as ->.
    destruct Hindesc as [_ [HisSome Hltdeslen]].
    solve_finz.
    eapply (Hadesc 1).
    apply finz_seq_lookup;try lia.
    assert (length des = 2) as ->. rewrite Hdesc. compute_done.
    lia.
    solve_finz.
    by simplify_list_eq.
    }
    rewrite Hlkwh Hlkwf /= /get_transaction Hretri /relinquish_transaction
    /toggle_transaction_relinquish /get_transaction Hretri Hcureq /=in Hexec.
    assert (Hcheck: ( i =? i )%nat = true).
    { apply <- Nat.eqb_eq. reflexivity. }
    rewrite Hcheck /= in Hexec. clear Hcheck.
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp /update_incr_PC /update_reg.
    rewrite_reg_pc.
    rewrite_access_all.
    rewrite update_access_batch_preserve_ownerships.
    rewrite (@update_access_batch_update_access_diff _ i sacc spsd psd);auto.
    rewrite (@update_access_batch_update_excl_diff _ i sexcl NoAccess spsd psd);auto.
    rewrite_reg_global.
    rewrite_mem_zero.
    rewrite_trans_update.
    iFrame "Hcur Hσrx1 Hσrx2 Hσtx".
    (* update regs *)
    rewrite (update_offset_PC_update_PC1 _ i ai 1);auto.
    rewrite update_access_batch_preserve_regs update_reg_global_update_reg zero_pages_preserve_reg
            update_transaction_preserve_regs;try solve_reg_lookup.
    2 : {
      rewrite  update_access_batch_preserve_regs update_reg_global_update_reg zero_pages_preserve_reg
            update_transaction_preserve_regs;try solve_reg_lookup.
      rewrite !lookup_insert_ne; [solve_reg_lookup|done].
    }
    iDestruct ((gen_reg_update2_global PC i _ (ai ^+ 1)%f R0 i _ (encode_hvc_ret_code Succ))
                  with "Hσreg PC R0") as ">[Hσreg [PC R0]]";eauto.
    rewrite Hcureq.
    iFrame "Hσreg".
     (* update page table *)
    rewrite_trans_alloc.
    iDestruct ((gen_access_update_diff spsd) with "Hacc Hσaccess") as ">[Hσaccess Hacc]";eauto.
    iDestruct ((gen_excl_update_diff spsd) with "Hexcl Hσexcl") as ">[Hσexcl Hexcl]";eauto.
    iFrame "Hσaccess Hσowned Hσexcl".
    (* update mem *)
    iDestruct "Hpgs" as (?) "Hpgs".
    iDestruct ((gen_mem_update_pages psd (pages_of_W0 (length psd))) with "Hσmem Hpgs") as ">[Hσmem Hpgs]";eauto.
     { apply length_pages_of_W0_forall. }
     { rewrite length_pages_of_W0 //. }
    rewrite -zero_pages_update_mem update_transaction_preserve_mem.
    iFrame "Hσmem".
    (* update transactions *)
    rewrite -get_trans_gmap_preserve_dom.
    rewrite (update_transaction_preserve_trans _ _ true false);auto.
    rewrite -get_retri_gmap_to_get_transaction get_trans_gmap_preserve_dom.
    iDestruct ((@gen_retri_update _ _ _ true false) with "Hretri Hσretri") as ">[Hσretri Hretri]".
    {
     eapply get_retri_gmap_lookup.
     exact Hretri.
    }
    iFrame "Hσretri Hσhp Hσtrans".
    iSplitR.
    iPureIntro.
    split.
    rewrite /get_transactions /update_transaction /insert_transaction //=.
    intro.
    rewrite /get_transactions /update_transaction /insert_transaction //=.
    intros.
    apply lookup_insert_Some in H.
    destruct H as [[_ <-] | [? ?]].
    cbn.
    pose proof (Hσpsdl wh (j, wf, true, i, psd, tt) Hretri) as Hlt.
    cbn in Hlt.
    assumption.
    apply (Hσpsdl i0).
    done.
    iApply "HΦ".
    by iFrame.
Qed.

Lemma hvc_relinquish_lend_z {wi sacc pi sexcl i j des ptx} {spsd: gset PID}
      ai r0 wh wf (psd: list PID) :
  decode_instruction wi = Some(Hvc) ->
  addr_in_page ai pi ->
  decode_hvc_func r0 = Some(Relinquish) ->
  pi ∈ sacc ->
  des = [wh; W1] ->
  seq_in_page (of_pid ptx) (length des) ptx ->
  spsd = (list_to_set psd) ->
  spsd ⊆ sacc ->
  spsd ⊆ sexcl ->
  {SS{{ ▷(PC @@ i ->r ai) ∗ ▷ (R0 @@ i ->r r0) ∗ ▷ ai ->a wi
  ∗ ▷ A@i:={1}[sacc] ∗ ▷ E@i:={1}[sexcl]
  ∗ ▷ TX@ i := ptx ∗ ▷ mem_region des ptx
  ∗ ▷ wh ->t{1}(j, wf, i, psd, Lending) ∗ ▷ wh ->re true
  ∗ (▷ ∃ wss, ([∗ list] p;ws ∈ psd;wss, mem_page ws p))}}}
   ExecI @ i {{{ RET ExecI ; PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi
  ∗ E@i:={1}[sexcl∖spsd] ∗ A@i:={1}[sacc∖spsd]
  ∗ R0 @@ i ->r (encode_hvc_ret_code Succ) ∗ wh ->t{1}(j, wf, i, psd, Lending)
  ∗ wh ->re false ∗ TX@ i := ptx ∗ mem_region des ptx
  ∗ ([∗ list] p;ws ∈ psd;(pages_of_W0 (length psd)), mem_page ws p)}}}.
Proof.
  iIntros (Hdecodei Hinpi Hdecodef Hinai Hdesc Hindesc Hspsd Hsacc Hsexcl Φ).
  iApply hvc_relinquish_z;auto.
  exact Hinpi.
  exact Hinai.
Qed.

Lemma hvc_relinquish_share_z {wi sacc pi sexcl i j des ptx} {spsd: gset PID}
      ai r0 wh wf (psd: list PID) :
  decode_instruction wi = Some(Hvc) ->
  addr_in_page ai pi ->
  decode_hvc_func r0 = Some(Relinquish) ->
  pi ∈ sacc ->
  des = [wh; W1] ->
  seq_in_page (of_pid ptx) (length des) ptx ->
  spsd = (list_to_set psd) ->
  spsd ⊆ sacc ->
  spsd ## sexcl ->
  {SS{{ ▷(PC @@ i ->r ai) ∗ ▷ (R0 @@ i ->r r0) ∗ ▷ ai ->a wi
  ∗ ▷ A@i:={1}[sacc] ∗ ▷ E@i:={1}[sexcl]
  ∗ ▷ TX@ i := ptx ∗ ▷ mem_region des ptx
  ∗ ▷ wh ->t{1}(j, wf, i, psd, Sharing) ∗ ▷ wh ->re true
  ∗ (▷ ∃ wss, ([∗ list] p;ws ∈ psd;wss, mem_page ws p))}}}
   ExecI @ i {{{ RET ExecI ; PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi
  ∗ E@i:={1}[sexcl] ∗ A@i:={1}[sacc∖spsd]
  ∗ R0 @@ i ->r (encode_hvc_ret_code Succ) ∗ wh ->t{1}(j, wf, i, psd, Sharing)
  ∗ wh ->re false ∗ TX@ i := ptx ∗ mem_region des ptx
  ∗ ([∗ list] p;ws ∈ psd;(pages_of_W0 (length psd)), mem_page ws p)}}}.
Proof.
  iIntros (Hdecodei Hinpi Hdecodef Hinai Hdesc Hindesc Hspsd Hsacc Hsexcl Φ).
   assert (sexcl ∖ spsd = sexcl) as Hexcleq.
    { set_solver.  }
    rewrite -Hexcleq.
  iIntros "(>PC & >R0 & >Hai & >Hacc & >Hexcl & >TX & >Hadesc & >Htrans & >Hretri & Hpgs)".
  iApply hvc_relinquish_z;auto.
  exact Hinpi.
  exact Hdecodef.
  exact Hinai.
  rewrite Hexcleq.
  iFrame.
Qed.

End relinquish_z.
