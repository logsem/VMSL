From machine_program_logic.program_logic Require Import weakestpre.
(* From iris.algebra Require Import gset. *)
From HypVeri Require Import lifting rules.rules_base machine_extra.
From HypVeri.algebra Require Import base mem reg pagetable mailbox trans base_extra.
From HypVeri.lang Require Import lang_extra reg_extra mem_extra pagetable_extra trans_extra.

Section mem_send_nz.

Context `{hypparams: HypervisorParameters}.
Context `{vmG: !gen_VMG Σ}.

Lemma  mem_send_nz_not_share_update{n i ai r0 r1 r2 ptx sh h fhs spsd} {l:Word} σ1 j (tt: transaction_type):
  tt = Lending ∨ tt = Donation ->
  get_current_vm σ1 = i ->
  (get_mail_box σ1 @ i).1 = ptx ->
  (finz.to_z l) = (Z.of_nat (size spsd)) ->
  (elements sh) = h :: fhs ->
  (elements sh) = elements (get_transactions σ1).2 ->
  PC @@ i ->r ai -∗
  ([∗ set] p ∈ spsd, p -@O> i) -∗
  ([∗ set] p ∈ spsd, p -@A> i) -∗
  R0 @@ i ->r r0-∗
  R1 @@ i ->r r1-∗
  R2 @@ i ->r r2-∗
  hp[ sh ]-∗
  gen_vm_interp n σ1 ={⊤}=∗
  gen_vm_interp n
    (update_incr_PC
         (update_reg
            (update_reg (revoke_access_global
                          (alloc_transaction σ1 h (i, W0, j, spsd, tt , false))
                          (get_current_vm σ1) spsd) R0 (encode_hvc_ret_code Succ))
            R2 h))
  ∗ PC @@ i ->r (ai ^+ 1)%f
  ∗ ([∗ set] p ∈ spsd, p -@O> i)
  ∗ ([∗ set] p ∈ spsd, p -@A> -)
  ∗ R0 @@ i ->r (encode_hvc_ret_code Succ) ∗ R1 @@ i ->r r1
  ∗ ⌜h ∈ sh⌝ ∗ R2 @@ i ->r h ∗ h ->t (i,W0,j,spsd,tt)
  ∗ h ->re false  ∗ hp[ sh∖{[h]} ].
Proof.
  iIntros (Htt Hcur Htx Hsz_psd Hfhs Hhp).
  iIntros "PC Hown Hacc R0 R1 R2 Hhp".
  iIntros "(Hcur & Hσmem & Hσreg & Hσmb & Hσrxs & Hσown & Hσaccess & Hσtrans & Hσhp & Hσretri
                 & %Inv_trans_hpool & %Inv_trans_wf & %Inv_trans_pgt & %Inv_pgt_mb)".
  (* valid regs *)
  iDestruct ((gen_reg_valid1 R0 i r0 Hcur) with "Hσreg R0") as "%HR0";eauto.
  iDestruct ((gen_reg_valid1 R1 i r1 Hcur) with "Hσreg R1") as "%HR1";eauto.
  iDestruct ((gen_reg_valid1 R2 i r2 Hcur) with "Hσreg R2") as "%HR2";eauto.
  iDestruct ((gen_reg_valid1 PC i ai Hcur) with "Hσreg PC") as "%HPC";eauto.
  (* valid pt *)
  iDestruct (access_agree_1_excl_check_true_bigS spsd with "Hσaccess Hacc") as %Hacc.
  iDestruct (ownership_agree_Some_lookup_bigS spsd with "Hσown Hown") as %Hown_lookup.
  iDestruct (access_agree_1_lookup_bigS spsd with "Hσaccess Hacc") as %Hacc_lookup.
  rewrite /gen_vm_interp /update_incr_PC /update_reg.
    (* unchanged part *)
  rewrite ?p_upd_reg_current_vm p_rvk_acc_current_vm p_alloc_trans_current_vm.
  rewrite (preserve_get_mb_gmap _ σ1).
  rewrite (preserve_get_rx_gmap _ σ1).
  2,3: rewrite p_upd_pc_mb !p_upd_reg_mb p_rvk_acc_mb p_alloc_trans_mb //.
  rewrite p_upd_pc_mem !p_upd_reg_mem p_rvk_acc_mem p_alloc_trans_mem //.
  iFrame "Hcur Hσmem Hσmb Hσrxs".
  (* update regs *)
  rewrite (update_offset_PC_update_PC1 _ i ai 1);auto.
  rewrite !update_reg_global_update_reg;try solve_reg_lookup.
  2 : {
   exists r0.
   rewrite (preserve_get_reg_gmap _ σ1).
   solve_reg_lookup.
   rewrite p_rvk_acc_regs p_alloc_trans_regs //.
  }
  2 : {
   exists r2.
   rewrite (preserve_get_reg_gmap _ σ1).
   rewrite lookup_insert_ne.
   solve_reg_lookup.
   done.
   rewrite p_rvk_acc_regs p_alloc_trans_regs //.
  }
  2 : {
   exists r0.
   rewrite (preserve_get_reg_gmap _ σ1).
   solve_reg_lookup.
   rewrite p_rvk_acc_regs p_alloc_trans_regs //.
  }
  2 : {
   rewrite !update_reg_global_update_reg.
   all: rewrite (preserve_get_reg_gmap _ σ1).
   all: try rewrite p_rvk_acc_regs p_alloc_trans_regs //.
   rewrite !lookup_insert_ne; [solve_reg_lookup|done|done].
   exists r0.
   solve_reg_lookup.
   exists r2.
   rewrite lookup_insert_ne; [solve_reg_lookup|done].
   exists r0.
   solve_reg_lookup.
  }
  iDestruct ((gen_reg_update3_global PC i (ai ^+ 1)%f R2 i h R0 i (encode_hvc_ret_code Succ))
              with "Hσreg PC R2 R0") as ">[Hσreg [PC [R2 R0]]]";eauto.
  rewrite (preserve_get_reg_gmap _ σ1);last rewrite p_rvk_acc_regs p_alloc_trans_regs //.
  rewrite Hcur.
  iFrame "Hσreg".
  (* update page table *)
  set σ1' := (update_offset_PC
             (update_reg_global
                (update_reg_global (revoke_access_global (alloc_transaction σ1 h (i, W0, j, spsd, tt, false)) i spsd) i R0
                   (encode_hvc_ret_code Succ)) i R2 h) 1).
  rewrite (preserve_get_owned_gmap σ1' (revoke_access_global (alloc_transaction σ1 h (i, W0, j, spsd, tt, false)) i spsd)).
  2: {
   rewrite p_upd_pc_pgt !p_upd_reg_pgt //.
  }
  rewrite p_rvk_acc_ownerships.
  rewrite (preserve_get_owned_gmap _ σ1).
  2: rewrite p_alloc_trans_pgt //.
  iFrame "Hσown".
  rewrite (preserve_get_access_gmap σ1' (revoke_access_global (alloc_transaction σ1 h (i, W0, j, spsd, tt, false)) i spsd)).
  2: rewrite p_upd_pc_pgt !p_upd_reg_pgt //.
  rewrite (u_rvk_acc_acc).
  rewrite (preserve_get_access_gmap _ σ1).
  2: rewrite p_alloc_trans_pgt //.
  iDestruct (access_update_revoke with "Hσaccess Hacc") as ">[Hσaccess Hacc]";eauto.
  { apply elem_of_singleton. reflexivity. }
  assert ({[i]} ∖ {[i]} = ∅) as ->.
  set_solver +.
  iFrame "Hσaccess".
  (* update transactions *)
  rewrite (preserve_get_trans_gmap σ1' (alloc_transaction σ1 h (i, W0, j, spsd, tt, false))).
  2: rewrite p_upd_pc_trans !p_upd_reg_trans p_rvk_acc_trans //.
  iDestruct (trans_update_insert h (i,W0,j,spsd,tt) with "Hσtrans") as ">[Hσtrans Htran]".
  { admit. }
  rewrite u_alloc_trans_trans.
  rewrite (preserve_get_retri_gmap σ1' (alloc_transaction σ1 h (i, W0, j, spsd, tt, false))).
  2: rewrite p_upd_pc_trans !p_upd_reg_trans p_rvk_acc_trans //.
  rewrite u_alloc_trans_retri.

  rewrite (preserve_get_hpool_gset σ1' (alloc_transaction σ1 h (i, W0, j, spsd, tt, false))).
  2: rewrite p_upd_pc_trans !p_upd_reg_trans p_rvk_acc_trans //.
  rewrite u_alloc_trans_hpool.
  assert (Hin_sh : h ∈ sh).
  { apply elem_of_elements.
    rewrite Hfhs.
    apply <- (elem_of_cons fhs h h).
    left;done.
  }
  iDestruct ((hpool_update_minus h ) with "Hhp Hσhp") as ">[Hσhp Hhp]";auto.
  iDestruct ((retri_update_insert h) with "Hσretri") as ">[Hσretri Hretri]".
  { admit. }
  simpl.
  iFrame "Hσretri Hσhp Hσtrans".
  (* invariants  *)
  (* rewrite (preserve_inv_trans_pg_num_ub _ (alloc_transaction σ1 h (i, W0, j, spsd, tt, false))). *)
  (* 2: rewrite p_upd_pc_trans !p_upd_reg_trans p_rvk_acc_trans //. *)
  rewrite (preserve_inv_trans_hpool_consistent _ (alloc_transaction σ1 h (i, W0, j, spsd, tt, false))).
  2: rewrite p_upd_pc_trans !p_upd_reg_trans p_rvk_acc_trans //.
  rewrite (preserve_inv_trans_pgt_consistent _ (revoke_access_global (alloc_transaction σ1 h (i, W0, j, spsd, tt, false)) i spsd)).
  2: rewrite p_upd_pc_trans !p_upd_reg_trans //.
  2: rewrite p_upd_pc_pgt !p_upd_reg_pgt //.
  assert (Inv_trans_pgt' : inv_trans_pgt_consistent (revoke_access_global (alloc_transaction σ1 h (i, W0, j, spsd, tt, false)) i spsd)).
  {
    rewrite /inv_trans_pgt_consistent.
    rewrite /revoke_access_global.
    rewrite /update_page_table_global /=.
    rewrite /inv_trans_pgt_consistent' /=.
    apply map_Forall_lookup_2.
    intros.
    destruct (decide (h = i0)).
    { subst i0.
      rewrite lookup_insert in H0.
      inversion H0;subst x.
      clear H0.
      simpl.
      rewrite (update_page_table_lookup_elem_of (perm:= (Some i, {[i]}))).
      simpl.
      assert ({[i]} ∖ {[i]} = ∅) as ->.
      set_solver +.
      simpl in H1.
      destruct Htt;subst tt;eauto.
      done.
      specialize (Hacc p).
      feed specialize Hacc.
      done.
      simpl in H1.
      specialize (Hown_lookup p).
      feed specialize Hown_lookup;auto.
      specialize (Hacc_lookup p).
      feed specialize Hacc_lookup;auto.
      simpl in Hown_lookup, Hacc_lookup.
      destruct Hown_lookup as [? Hlookup_pgt].
      destruct Hacc_lookup as [? Hlookup_pgt'].
      rewrite Hlookup_pgt in Hlookup_pgt'.
      inversion Hlookup_pgt'.
      subst x x0.
      done.
    }
    {
    rewrite lookup_insert_ne in H0.
    2: done.
    rewrite /inv_trans_pgt_consistent /inv_trans_pgt_consistent' in Inv_trans_pgt.
    apply (map_Forall_lookup_1 _ _ i0 x) in Inv_trans_pgt.
    2: done.
    rewrite /= in Inv_trans_pgt.
    specialize (Inv_trans_pgt p).
    feed specialize Inv_trans_pgt.
    done.
    assert (p ∉ spsd).
    {
      intro Hin_p.
      specialize (Hown_lookup p).
      feed specialize Hown_lookup;auto.
      specialize (Hacc_lookup p).
      feed specialize Hacc_lookup;auto.
      simpl in Hown_lookup, Hacc_lookup.
      destruct Hown_lookup as [? Hlookup_pgt].
      destruct Hacc_lookup as [? Hlookup_pgt'].
      rewrite Hlookup_pgt in Hlookup_pgt'.
      inversion Hlookup_pgt'.
      subst x1 x0.
      clear Hlookup_pgt'.
      rewrite Hlookup_pgt /= in Inv_trans_pgt.
      destruct x.1.2, x.2;admit.
        (* TODO: to prove this, we have to establish a new invariant that shows either the sender can not also be the receiver in any transactions,
         or one page can not be involved in any two transactions.
         the new invariant can be combined with inv_trans_pg_num_ub to express the wellformedness of transactions.
       *)
       }
    destruct x.1.2;
    destruct x.2 eqn:Heq_retri;eauto;
    apply update_page_table_lookup_not_elem_of;eauto.
    }
  }
  assert (Inv_trans_hpool' : inv_trans_hpool_consistent (alloc_transaction σ1 h (i, W0, j, spsd, tt, false))).
  { apply p_alloc_trans_inv_trans_hpool.
    apply elem_of_elements.
    rewrite -Hhp.
    rewrite Hfhs.
    set_solver +.
    done.
  }
  (* assert (Inv_trans_psdl' :inv_trans_pg_num_ub (alloc_transaction σ1 h (i, W0, j, spsd, tt, false))). *)
  (* { (* TODO : use Hsz_psd and the fact that l is a word *) *)
  (*   admit. *)
  (* } *)
  (* framing out everything  *)
  iModIntro.
  iSplitL "".
  iPureIntro.
  split;auto.
  split;admit.
  iFrame.
  iPureIntro.
  done.
  Admitted.


(* Lemma  mem_send_nz_share_update{i ai wi sown sacc sexcl r0 r1 r2 ptx sh q h fhs j psd spsd } {l:Word}  σ1 tt: *)
(*   get_current_vm σ1 = i -> *)
(*   (get_vm_mail_box σ1 i).1 = ptx -> *)
(*   (finz.to_z l) = (Z.of_nat (length psd)) -> *)
(*   spsd = ((list_to_set psd): gset PID) -> *)
(*   (elements sh) = h :: fhs -> *)
(*   (elements sh) = elements (get_transactions σ1).2 -> *)
(*   spsd ⊆ sacc -> *)
(*   PC @@ i ->r ai -∗ *)
(*   ai ->a wi -∗ *)
(*   O@i:={q}[sown] -∗ *)
(*   A@i:={1}[sacc] -∗ *)
(*   E@i:={1}[sexcl] -∗ *)
(*   R0 @@ i ->r r0-∗ *)
(*   R1 @@ i ->r r1-∗ *)
(*   R2 @@ i ->r r2-∗ *)
(*   hp{1}[sh]-∗ *)
(*   gen_vm_interp σ1 ={⊤}=∗ *)
(*   gen_vm_interp *)
(*     (update_incr_PC (update_reg (update_reg *)
(*       (update_access_batch (alloc_transaction σ1 h (i, W0, false, j, psd, tt)) psd SharedAccess) R0 *)
(*       (encode_hvc_ret_code Succ)) R2 h)) *)
(*   ∗ PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi *)
(*   ∗ O@i:={q}[sown] ∗ A@i:={1}[sacc] ∗ E@i:={1}[sexcl∖spsd] *)
(*   ∗ R0 @@ i ->r (encode_hvc_ret_code Succ) ∗ R1 @@ i ->r r1 *)
(*   ∗ ⌜h ∈ sh⌝ ∗ R2 @@ i ->r h ∗ h ->t{1}(i,W0,j , psd,tt) *)
(*   ∗ h ->re false  ∗ hp{1}[ (sh∖{[h]})]. *)
(* Proof. *)
(*   iIntros (Hcur Htx Hlenpsd Hspsd Hfhs Hhp Hspsdacc). *)
(*   iIntros "PC Hai Hown Hacc Hexcl R0 R1 R2 Hhp". *)
(*   iIntros "(Hcur & Hσmem & Hσreg & Hσtx & Hσrx1 & Hσrx2 & Hσowned & Hσaccess & Hσexcl & Htrans & Hσhp & %Hdisj & %Hσpsdl & Hrcv)". *)
(*   (* valid regs *) *)
(*   iDestruct ((gen_reg_valid1  R0 i r0 Hcur) with "Hσreg R0") as "%HR0";eauto. *)
(*   iDestruct ((gen_reg_valid1  R1 i r1 Hcur) with "Hσreg R1") as "%HR1";eauto. *)
(*   iDestruct ((gen_reg_valid1  R2 i r2 Hcur) with "Hσreg R2") as "%HR2";eauto. *)
(*   iDestruct ((gen_reg_valid1  PC i ai Hcur) with "Hσreg PC") as "%HPC";eauto. *)
(*   (* valid pt *) *)
(*   iDestruct ((gen_access_valid_pure sacc) with "Hσaccess Hacc") as %Hacc;eauto. *)
(*   iDestruct ((gen_excl_valid_pure sexcl) with "Hσexcl Hexcl") as %Hexcl';eauto. *)
(*   rewrite /gen_vm_interp /update_incr_PC /update_reg. *)
(*     (* unchanged part *) *)
(*     rewrite_reg_pc; *)
(*     rewrite_reg_global. *)
(*     rewrite update_access_batch_preserve_current_vm alloc_transaction_preserve_current_vm. *)
(*     rewrite_reg_global; *)
(*     rewrite_access_all; *)
(*     rewrite_trans_alloc. *)
(*     iFrame "Hcur Hσmem Hσtx Hσrx1 Hσrx2". *)
(*     rewrite Hcur. *)
(*     (* update regs *) *)
(*     rewrite (update_offset_PC_update_PC1 _ i ai 1);auto. *)
(*     rewrite !update_reg_global_update_reg update_access_batch_preserve_regs *)
(*             alloc_transaction_preserve_regs;try solve_reg_lookup. *)
(*     2 : { *)
(*       exists r2. *)
(*       rewrite lookup_insert_ne. *)
(*       solve_reg_lookup. *)
(*       done. *)
(*     } *)
(*     2 : { *)
(*       rewrite !update_reg_global_update_reg update_access_batch_preserve_regs *)
(*             alloc_transaction_preserve_regs;try solve_reg_lookup. *)
(*       rewrite !lookup_insert_ne; [solve_reg_lookup|done|done]. *)
(*       exists r2. *)
(*       rewrite lookup_insert_ne;[solve_reg_lookup|done]. *)
(*     } *)
(*      iDestruct ((gen_reg_update3_global PC i (ai ^+ 1)%f R2 i h R0 i (encode_hvc_ret_code Succ)) *)
(*                   with "Hσreg PC R2 R0") as ">[Hσreg [PC [R2 R0]]]";eauto. *)
(*      iFrame "Hσreg". *)
(*      (* update page table *) *)
(*      iFrame "Hacc". *)
(*      rewrite update_access_batch_preserve_ownerships alloc_transaction_preserve_owned. *)
(*      iFrame "Hσowned". *)
(*      rewrite (@update_access_batch_update_excl_diff _ _ i sexcl SharedAccess spsd psd);eauto. *)
(*      rewrite_trans_alloc. *)
(*      iDestruct ((gen_excl_update_diff spsd) with "Hexcl Hσexcl") as ">[Hσexcl Hexcl]";eauto. *)
(*      rewrite Hcur. *)
(*      iFrame "Hσexcl". *)
(*      (* update transactions *) *)
(*      rewrite alloc_transaction_update_trans /=. *)
(*      rewrite alloc_transaction_update_hpool /=. *)
(*      rewrite alloc_transaction_update_retri /=. *)
(*      assert (HhInfhs: h ∈ (get_transactions σ1).2). { *)
(*         rewrite /get_fresh_handles in Hhp. *)
(*         apply elem_of_elements. *)
(*         rewrite -Hhp Hfhs. *)
(*         apply <- (elem_of_cons fhs h h). *)
(*         left;done. *)
(*      } *)
(*      iDestruct ((gen_trans_update_insert h i W0 j psd tt) with "Htrans") as ">[Hσtrans Htran]". *)
(*      { apply not_elem_of_dom. *)
(*        rewrite get_trans_gmap_preserve_dom. *)
(*        set_solver. *)
(*      } *)
(*      assert (HhIn: h ∈ sh). *)
(*       { apply elem_of_elements. *)
(*        rewrite Hfhs. *)
(*        apply <- (elem_of_cons fhs h h). *)
(*        left;done. *)
(*      } *)
(*      iDestruct ((gen_hpool_update_diff h HhIn) with "Hhp Hσhp") as ">[Hσhp Hhp]". *)
(*      iDestruct ((gen_retri_update_insert h) with "Hrcv") as ">[Hσrtrv Hrtrv]". *)
(*      { apply not_elem_of_dom. *)
(*        rewrite get_retri_gmap_preserve_dom. *)
(*        set_solver. *)
(*      } *)
(*      iFrame "Hσrtrv Hσhp Hσtrans". *)
(*      iModIntro. *)
(*      rewrite (@update_access_batch_update_pagetable_idempotent _ (alloc_transaction σ1 h (i, W0, false, j, psd, tt)) i sacc SharedAccess spsd); eauto. *)
(*      rewrite_trans_alloc. *)
(*      iFrame "Hσaccess". *)
(*      iSplitR. *)
(*      iPureIntro. *)
(*      split. *)
(*      set_solver. *)
(*      apply map_Forall_insert_2; auto. *)
(*      simpl. *)
(*      rewrite -Hlenpsd. *)
(*      destruct (finz_spec l) as [Hf _]. *)
(*      rewrite ->(reflect_iff _ _ (Z.ltb_spec0 l word_size)) in Hf. *)
(*      assumption. *)
(*      iFrame. *)
(*      done. *)
(* Qed. *)

Inductive not_share_view_spec : transaction_type -> Type :=
| NotShareP t : t = Lending \/ t = Donation -> not_share_view_spec t
| ShareP t : t = Sharing -> not_share_view_spec t.

Lemma not_share_viewP z : not_share_view_spec z.
Proof. destruct z; [ constructor | constructor 2 | constructor ]; auto. Qed.


Lemma hvc_mem_send_not_share_nz tt i wi r2 ptx q des sh hvcf (l :Word) (spsd: gset PID)
      ai r0 r1 j :
  tt ≠ Sharing ->
  (* the decoding of wi is correct *)
  decode_instruction wi = Some(Hvc) ->
  (* the decoding of R0 is a FFA mem send *)
  decode_hvc_func r0 = Some(hvcf) ->
  hvcf_to_tt hvcf = Some tt ->
  (* caller is not the receiver *)
  i ≠ j ->
  (* l is the number of to-be-donated pages *)
  (finz.to_z l) = (Z.of_nat (size spsd)) ->
  (* the descriptor, in list Word *)
  des = serialized_transaction_descriptor i j W0 l (elements spsd) W0 ->
  (* the whole descriptor resides in the TX page *)
  seq_in_page (of_pid ptx) (length des) ptx ->
  (* r1 equals the length of the descriptor *)
  (finz.to_z r1) = (Z.of_nat (length des)) ->
  (* there is at least one free handle in the hpool *)
  sh ≠ ∅ ->
  {SS{{ ▷(PC @@ i ->r ai) ∗
      ▷ ai ->a wi ∗
  (* VM i owns pages in spsd *)
      ▷ ([∗ set] p ∈ spsd, p -@O> i) ∗
  (* pages in spsed are exclusive to VM i *)
      ▷ ([∗ set] p ∈ spsd, p -@A> i) ∗
      (* and the page which the instruction is in is not being shared, i.e. (tpa ai) ∉ spsd *)
      (* TODO: to prove ftlr, we may need a separate rule to cover the other case. - No we don't need!  *)
      ▷ ((tpa ai) -@{q}A> i) ∗
      ▷ (R0 @@ i ->r r0) ∗
      ▷ (R1 @@ i ->r r1) ∗
      ▷ (R2 @@i ->r r2) ∗
      ▷ hp [ sh ] ∗
      ▷ TX@ i := ptx ∗
      ▷ mem_region des ptx
       }}}
   ExecI @ i {{{ RET (false,ExecI) ;
                 PC @@ i ->r (ai ^+ 1)%f ∗
                 ai ->a wi ∗
                 ([∗ set] p ∈ spsd, p -@O> i ) ∗
                 ([∗ set] p ∈ spsd, p -@A> - ) ∗
                 R0 @@ i ->r (encode_hvc_ret_code Succ) ∗
                 R1 @@ i ->r r1 ∗
                 (∃ (wh: Word), ⌜wh ∈ sh⌝ ∗
                 R2 @@ i ->r wh ∗
                 wh ->t (i,W0,j,spsd,tt) ∗
                 wh ->re false ∗
                 hp [ sh∖{[wh]} ]) ∗
                 TX@ i := ptx ∗
                 mem_region des ptx}}}.
Proof.
  iIntros (Hnshar Hdecodei Hdecodef Hismemsend Hneq Hzs_spsd Hdesc Hindesc Hlen_des Hshne).
  iIntros (Φ) "(>PC & >Hai & >Hown & >Hacc & >Hacc_i & >R0 & >R1 & >R2 & >Hhp & >TX & >Hadesc) HΦ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (n σ1) "%Hsche Hσ".
  rewrite /scheduled in Hsche.
  simpl in Hsche.
  rewrite /scheduler in Hsche.
  apply bool_decide_unpack in Hsche as Hcur.
  clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(Hcur & Hσmem & Hσreg & Hσmb & Hσrxs & Hσown & Hσaccess & Hσtrans & Hσhpool & Hσretri
    & %Hinv_trans_hpool & %Hinv_trans_pgnum & %Hinv_trans_pgt)".
  (* valid regs *)
  iDestruct ((gen_reg_valid3 i PC ai R0 r0 R1 r1 Hcur) with "Hσreg PC R0 R1") as "(%HPC & %HR0 & %HR1)";eauto.
  (* valid pt *)
  iDestruct (access_agree_check_true (tpa ai)  with "Hσaccess Hacc_i") as %Hacc_i;eauto.
  { apply elem_of_singleton. apply eq_refl. }
  iDestruct (access_agree_1_excl_check_true_bigS spsd with "Hσaccess Hacc") as %Hacc.
  iDestruct (ownership_agree_check_true_bigS spsd with "Hσown Hown") as %Hown.
  (* valid mem *)
  iDestruct (gen_mem_valid ai wi with "Hσmem Hai") as %Hai.
  unfold mem_region.
  iDestruct (gen_mem_valid_SepL_pure _ des with "Hσmem Hadesc") as %Hadesc.
  { apply finz_seq_NoDup'. destruct Hindesc as [_ [_ [HisSome _]]]. solve_finz. }
  (* valid tx *)
  iDestruct (gen_tx_valid with "TX Hσmb") as %Htx.
  (* valid hpool *)
  iDestruct (hpool_valid with "Hhp Hσhpool") as %Hhp.
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal i Hvc ai wi);eauto.
  - (* step *)
    iModIntro.
    iIntros (m2 σ2) "[%P PAuth] %HstepP".
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
    rewrite Hcur /=  Htx (@transaction_descriptor_valid _ _ i j W0 l (elements spsd) σ1 des) /= in Heqc2;eauto.
    assert (Hcheck : (i =? i)%nat = true).
    { by apply   <- Nat.eqb_eq. }
    rewrite Hcur Hcheck /= in Heqc2;clear Hcheck.
    assert (Hcheck:  negb (i =? j)%nat = true).
       {apply negb_true_iff. apply  <- Nat.eqb_neq. intro. apply Hneq. by apply fin_to_nat_inj. }
    rewrite Hcheck /= in Heqc2;clear Hcheck.
    rewrite bool_decide_eq_true_2 in Heqc2.
    2: {
      intros p HpIn.
      rewrite list_to_set_elements_L in HpIn.
      apply andb_true_iff.
      split.
      by apply Hacc.
      by apply Hown.
    }
    rewrite /new_transaction /fresh_handle in Heqc2.
    destruct (elements sh) as [| h fhs] eqn:Hfhs.
    { exfalso. rewrite -elements_empty in Hfhs.  apply Hshne. apply set_eq.
     intro. rewrite -elem_of_elements Hfhs elem_of_elements. split;intro;set_solver. }
    rewrite /get_fresh_handles -Hhp Hfhs //= in Heqc2.
    destruct (not_share_viewP tt) as [? o | ? o]; [| done].
    destruct hvcf; try inversion Hismemsend; subst t;
      destruct HstepP;subst m2 σ2; subst c2; simpl; try done; destruct o; try done.
    { iDestruct (mem_send_nz_not_share_update σ1 j Lending with "PC Hown Hacc R0 R1 R2 Hhp
        [Hcur Hσmem Hσreg Hσmb Hσrxs Hσown Hσaccess Hσtrans Hσhpool Hσretri]")
          as ">[Hσ' (?&?&?&?&?&?&?&?&?&?)]";eauto.
      rewrite Hhp //.
      rewrite /gen_vm_interp.
      iSplitL "Hcur". iFrame "Hcur".
      iFrame "Hσmem Hσreg Hσmb Hσrxs Hσown Hσaccess Hσtrans Hσhpool Hσretri".
      iPureIntro.
      split;auto.
      iModIntro.
      iSplitL "PAuth".
      iExists P. iFrame.
      iSplitL "Hσ'".
      rewrite list_to_set_elements_L.
      iFrame "Hσ'".
      iSplitL "".
      { (*TODO: just_scheduled *)  admit. }
      set scheduled_b := (X in negb X).
      assert (negb scheduled_b = false) as ->.
      { admit. }
      iApply "HΦ".
      iFrame.
      iExists h.
      iFrame.
    }
    { iDestruct (mem_send_nz_not_share_update σ1 j Donation with "PC Hown Hacc R0 R1 R2 Hhp
        [Hcur Hσmem Hσreg Hσmb Hσrxs Hσown Hσaccess Hσtrans Hσhpool Hσretri]")
          as ">[Hσ' (?&?&?&?&?&?&?&?&?&?)]";eauto.
      rewrite Hhp //.
      rewrite /gen_vm_interp.
      iSplitL "Hcur". iFrame "Hcur".
      iFrame "Hσmem Hσreg Hσmb Hσrxs Hσown Hσaccess Hσtrans Hσhpool Hσretri".
      iPureIntro.
      split;auto.
      iModIntro.
      iSplitL "PAuth".
      iExists P. iFrame.
      iSplitL "Hσ'".
      rewrite list_to_set_elements_L.
      iFrame "Hσ'".
      iSplitL "".
      { (*TODO: just_scheduled *)  admit. }
      set scheduled_b := (X in negb X).
      assert (negb scheduled_b = false) as ->.
      { admit. }
      iApply "HΦ".
      iFrame.
      iExists h.
      iFrame.
    }
Admitted.

(* Lemma hvc_mem_send_share_nz tt i wi r2 ptx sown q sacc sexcl des sh hvcf  (l :Word) (spsd: gset PID) *)
(*       ai r0 r1 j (psd: list PID) : *)
(*   tt = Sharing -> *)
(*   (* the decoding of wi is correct *) *)
(*   decode_instruction wi = Some(Hvc) -> *)
(*   (* the decoding of R0 is a FFA mem send *) *)
(*   decode_hvc_func r0 = Some(hvcf) -> *)
(*   hvcf_to_tt hvcf = Some tt -> *)
(*   (* caller is not the receiver *) *)
(*   i ≠ j -> *)
(*   (* l is the number of to-be-donated pages *) *)
(*   (finz.to_z l) = (Z.of_nat (length psd)) -> *)
(*   (* the descriptor, in list Word *) *)
(*   des = serialized_transaction_descriptor i j W0 l psd W0 -> *)
(*   (* the whole descriptor resides in the TX page *) *)
(*   seq_in_page (of_pid ptx) (length des) ptx -> *)
(*   (* r1 equals the length of the descriptor *) *)
(*   (finz.to_z r1) = (Z.of_nat (length des)) -> *)
(*   (* spsd is the gset of all to-be-donated pages *) *)
(*   spsd = (list_to_set psd) -> *)
(*   (* pi and pages in spsd are accessible for VM i *) *)
(*   {[to_pid_aligned ai]} ∪ spsd ⊆ sacc -> *)
(*   (* VM i owns pages in spsd *) *)
(*   spsd ⊆ sown -> *)
(*   (* pages in spsed are exclusive to VM i *) *)
(*   spsd ⊆ sexcl -> *)
(*   (* there is at least one free handle in the hpool *) *)
(*   sh ≠ ∅ -> *)
(*   {SS{{ ▷(PC @@ i ->r ai) ∗ ▷ ai ->a wi *)
(*   ∗ ▷ O@i:={q}[sown] ∗ ▷ A@i:={1}[sacc] ∗ ▷ E@i:={1}[sexcl] *)
(*   ∗ ▷ (R0 @@ i ->r r0) ∗ ▷ (R1 @@ i ->r r1) ∗ ▷(R2 @@i ->r r2) ∗  ▷ TX@ i := ptx *)
(*   ∗ ▷ mem_region des ptx *)
(*   ∗ ▷ hp{ 1 }[ sh ] }}} *)
(*    ExecI @ i {{{ RET ExecI ; PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi *)
(*   ∗ O@i:={q}[sown] ∗ A@i:={1}[sacc] ∗ E@i:={1}[sexcl∖spsd] *)
(*   ∗ R0 @@ i ->r (encode_hvc_ret_code Succ) ∗ R1 @@ i ->r r1  ∗ TX@ i := ptx *)
(*   ∗ ∃(wh: Word), ( ⌜ wh ∈ sh ⌝ ∗ R2 @@ i ->r wh ∗ wh ->t{1}(i,W0,j , psd,tt) *)
(*   ∗ wh ->re false  ∗ hp{1}[ (sh∖{[wh]})] ) *)
(*   ∗ mem_region des ptx}}}. *)
(* Proof. *)
(*   iIntros (Hnshar Hdecodei Hdecodef Hismemsend Hneq Hlenpsd Hdesc Hindesc Hlenr1 Hspsd Hsacc Hsown Hsexcl Hshne). *)
(*   iIntros (Φ) "(>PC & >Hai & >Hown & >Hacc & >Hexcl & >R0 & >R1 & >R2 & >TX & >Hadesc & >Hhp ) HΦ". *)
(*   iApply (sswp_lift_atomic_step ExecI);[done|]. *)
(*   iIntros (σ1) "%Hsche Hσ". *)
(*   inversion Hsche as [ Hcureq ]; clear Hsche. *)
(*   apply fin_to_nat_inj in Hcureq. *)
(*   iModIntro. *)
(*   iDestruct "Hσ" as "(Hcur & Hσmem & Hσreg & Hσtx & Hσrx1 & Hσrx2 & Hσowned & Hσaccess & Hσexcl & Htrans & Hσhp & %Hdisj & %Hσpsdl & Hrcv)". *)
(*   (* valid regs *) *)
(*   iDestruct ((gen_reg_valid3 i PC ai R0 r0 R1 r1 Hcureq) with "Hσreg PC R0 R1") as "(%HPC & %HR0 & %HR1)";eauto. *)
(*   (* valid pt *) *)
(*   iDestruct ((gen_access_valid_addr_elem ai sacc) with "Hσaccess Hacc") as %Haccai;eauto. *)
(*   { set_solver. } *)
(*   iDestruct ((gen_own_valid_SepS_pure sown) with "Hσowned Hown") as %Hown;eauto. *)
(*   iDestruct ((gen_excl_valid_SepS_pure sexcl) with "Hσexcl Hexcl") as %Hexcl;eauto. *)
(*   (* valid mem *) *)
(*   iDestruct (gen_mem_valid ai wi with "Hσmem Hai") as %Hai. *)
(*   unfold mem_region. *)
(*   iDestruct (gen_mem_valid_SepL_pure _ des with "Hσmem Hadesc") as %Hadesc. *)
(*   { apply finz_seq_NoDup'. destruct Hindesc as [_ [_ [HisSome _]]]. solve_finz. } *)
(*   (* valid tx *) *)
(*   iDestruct (gen_tx_valid with "TX Hσtx") as %Htx. *)
(*   (* valid hpool *) *)
(*   iDestruct (gen_hpool_valid_elem with "Hhp Hσhp") as %Hhp. *)
(*   iSplit. *)
(*   - (* reducible *) *)
(*     iPureIntro. *)
(*     apply (reducible_normal i Hvc ai wi);eauto. *)
(*   - (* step *) *)
(*     iModIntro. *)
(*     iIntros (m2 σ2) "%HstepP". *)
(*     apply (step_ExecI_normal i Hvc ai wi) in HstepP;eauto. *)
(*     remember (exec Hvc σ1) as c2 eqn:Heqc2. *)
(*     assert (Hlendesclt :((Z.of_nat (length des) -1) <= (page_size-1))%Z). *)
(*     {  destruct Hindesc as [? [? [HisSome Hltpagesize]]]. *)
(*        apply (finz_plus_Z_le (of_pid ptx));eauto. *)
(*        apply last_addr_in_bound. *)
(*        rewrite /Is_true in Hltpagesize. *)
(*        case_match;[|done]. *)
(*        apply Z.leb_le in Heqb. *)
(*        done. *)
(*     } *)
(*     rewrite /exec /hvc HR0 Hdecodef /mem_send //= HR1 /= in Heqc2. *)
(*     destruct (page_size <? r1)%Z eqn:Heqn;[lia|clear Heqn]. *)
(*     rewrite Hcureq /get_tx_pid_global Htx (@transaction_descriptor_valid _ _ i j W0 l psd σ1 des) /= in Heqc2;eauto. *)
(*     assert (Hcheck : (i =? i)%nat = true). *)
(*     { by apply   <- Nat.eqb_eq. } *)
(*     rewrite Hcureq Hcheck /= in Heqc2;clear Hcheck. *)
(*     assert (Hcheck:  negb (i =? j)%nat = true). *)
(*     { apply negb_true_iff. apply  <- Nat.eqb_neq. intro. apply Hneq. by apply fin_to_nat_inj. } *)
(*     rewrite Hcheck /= in Heqc2;clear Hcheck. *)
(*     destruct (forallb (λ v' : PID, check_perm_page σ1 i v' (Owned, ExclusiveAccess)) psd) eqn:HCheck. *)
(*     2: { *)
(*       apply not_true_iff_false in HCheck. *)
(*       exfalso. *)
(*       apply HCheck. *)
(*       apply forallb_forall. *)
(*       intros ? HxIn. *)
(*       unfold check_perm_page. *)
(*       apply elem_of_list_In in HxIn. *)
(*       apply (elem_of_list_to_set (C:= gset PID)) in HxIn. *)
(*       rewrite <- Hspsd in HxIn. *)
(*       assert (HxInown: x ∈ sown). { set_solver. } *)
(*       assert (HxInexcl: x ∈ sexcl). { set_solver. } *)
(*       pose proof (Hown x HxInown) as Hxown. *)
(*       simpl in Hxown. *)
(*       destruct Hxown as [perm [HSomeperm Hisowned]]. *)
(*       rewrite /check_ownership_page  HSomeperm /=. *)
(*       destruct (decide (Owned = perm)). simpl. *)
(*       2: { exfalso. apply n. destruct perm;eauto. rewrite /is_owned //.  } *)
(*       pose proof (Hexcl x HxInexcl) as Hxexcl. *)
(*       simpl in Hxexcl. *)
(*       destruct Hxexcl as [perm' [HSomeperm' Hisexcl]]. *)
(*       rewrite /check_access_page HSomeperm'. *)
(*       destruct (decide (ExclusiveAccess = perm')). done. *)
(*       exfalso. apply n. destruct perm';eauto; rewrite /is_exclusive //. *)
(*     } *)
(*     rewrite /new_transaction /fresh_handle in Heqc2. *)
(*     destruct (elements sh) as [| h fhs] eqn:Hfhs . *)
(*     { exfalso. rewrite -elements_empty in Hfhs.  apply Hshne. apply set_eq. *)
(*     intro. rewrite -elem_of_elements Hfhs elem_of_elements.   split;intro;set_solver. } *)
(*     rewrite -Hhp //=  in Heqc2. *)
(*     destruct (not_share_viewP tt) as [? o | ? o]; [destruct o; simplify_eq; discriminate|]. *)
(*     destruct hvcf; try inversion Hismemsend; subst t; *)
(*       destruct HstepP;subst m2 σ2; subst c2; simpl; try done; destruct o; try done. *)
(*     iDestruct (mem_send_nz_share_update with "PC Hai Hown Hacc Hexcl R0 R1 R2 Hhp *)
(*         [Hcur Hσmem Hσreg Hσtx Hσrx1 Hσrx2 Hσowned Hσaccess Hσexcl Htrans Hσhp Hrcv]") *)
(*           as ">[Hσ' (? &?&?&?&?&?&?&?&?&?&?&?)]";eauto. *)
(*     rewrite Hfhs //. *)
(*     rewrite ->union_subseteq in Hsacc; destruct Hsacc; auto. *)
(*     rewrite /gen_vm_interp. *)
(*     iFrame. *)
(*     done. *)
(*     iModIntro. *)
(*     iSplitL "Hσ'". *)
(*     iExact "Hσ'". *)
(*     iApply "HΦ". *)
(*     iFrame. *)
(*     iExists h. *)
(*     iFrame. *)
(* Qed. *)


Lemma hvc_donate_nz {i ai wi r2 ptx q des sh} {r0 r1} j (l :Word) (spsd: gset PID):
  (* the decoding of wi is correct *)
  decode_instruction wi = Some(Hvc) ->
  (* the decoding of R0 is FFA_DONATE *)
  decode_hvc_func r0 = Some(Donate) ->
  (* caller is not the receiver *)
  i ≠ j ->
  (* l is the number of to-be-donated pages *)
  (finz.to_z l) = (Z.of_nat (size spsd)) ->
  (* the descriptor, in list Word *)
  des = serialized_transaction_descriptor i j W0 l (elements spsd) W0 ->
  (* the whole descriptor resides in the TX page *)
  seq_in_page (of_pid ptx) (length des) ptx ->
  (* r1 equals the length of the descriptor *)
  (finz.to_z r1) = (Z.of_nat (length des)) ->
  (* there is at least one free handle in the hpool *)
  sh ≠ ∅ ->
  {SS{{  ▷(PC @@ i ->r ai) ∗
      ▷ ai ->a wi ∗
  (* VM i owns pages in spsd *)
      ▷ ([∗ set] p ∈ spsd, p -@O> i) ∗
  (* pages in spsed are exclusive to VM i *)
      ▷ ([∗ set] p ∈ spsd, p -@A> i) ∗
      (* and the page which the instruction is in is not being shared, i.e. (tpa ai) ∉ spsd *)
      (* TODO: to prove ftlr, we may need a seperate rule to cover the other case *)
      ▷ ((tpa ai) -@{q}A> i) ∗
      ▷ (R0 @@ i ->r r0) ∗
      ▷ (R1 @@ i ->r r1) ∗
      ▷ (R2 @@i ->r r2) ∗
      ▷ hp [ sh ] ∗
      ▷ TX@ i := ptx ∗
      ▷ mem_region des ptx }}}
   ExecI @ i {{{ RET (false,ExecI) ;
                 PC @@ i ->r (ai ^+ 1)%f ∗
                 ai ->a wi ∗
                 ([∗ set] p ∈ spsd, p -@O> i ) ∗
                 ([∗ set] p ∈ spsd, p -@A> - ) ∗
                 R0 @@ i ->r (encode_hvc_ret_code Succ) ∗
                 R1 @@ i ->r r1 ∗
                 (∃ (wh: Word), ⌜wh ∈ sh⌝ ∗
                 R2 @@ i ->r wh ∗
                 wh ->t (i,W0,j,spsd,Donation) ∗
                 wh ->re false ∗
                 hp [ sh∖{[wh]} ]) ∗
                 TX@ i := ptx ∗
                 mem_region des ptx}}}.
Proof.
  iIntros (Hdecodei Hdecodef Hneq Hlenpsd Hdesc Hindesc Hlen_r1 Hshne Φ).
  iApply ((hvc_mem_send_not_share_nz Donation i wi r2 ptx q des sh Donate l spsd ai r0 r1 j));auto.
Qed.

Lemma hvc_lend_nz {i ai wi r2 ptx q des sh} {r0 r1} j (l :Word) (spsd: gset PID):
  (* the decoding of wi is correct *)
  decode_instruction wi = Some(Hvc) ->
  (* the decoding of R0 is FFA_DONATE *)
  decode_hvc_func r0 = Some(Lend) ->
  (* caller is not the receiver *)
  i ≠ j ->
  (* l is the number of to-be-donated pages *)
  (finz.to_z l) = (Z.of_nat (size spsd)) ->
  (* the descriptor, in list Word *)
  des = serialized_transaction_descriptor i j W0 l (elements spsd) W0 ->
  (* the whole descriptor resides in the TX page *)
  seq_in_page (of_pid ptx) (length des) ptx ->
  (* r1 equals the length of the descriptor *)
  (finz.to_z r1) = (Z.of_nat (length des)) ->
  (* there is at least one free handle in the hpool *)
  sh ≠ ∅ ->
  {SS{{  ▷(PC @@ i ->r ai) ∗
      ▷ ai ->a wi ∗
  (* VM i owns pages in spsd *)
      ▷ ([∗ set] p ∈ spsd, p -@O> i) ∗
  (* pages in spsed are exclusive to VM i *)
      ▷ ([∗ set] p ∈ spsd, p -@A> i) ∗
      (* and the page which the instruction is in is not being shared, i.e. (tpa ai) ∉ spsd *)
      (* TODO: to prove ftlr, we may need a seperate rule to cover the other case *)
      ▷ ((tpa ai) -@{q}A> i) ∗
      ▷ (R0 @@ i ->r r0) ∗
      ▷ (R1 @@ i ->r r1) ∗
      ▷ (R2 @@i ->r r2) ∗
      ▷ hp [ sh ] ∗
      ▷ TX@ i := ptx ∗
      ▷ mem_region des ptx }}}
   ExecI @ i {{{ RET (false,ExecI) ;
                 PC @@ i ->r (ai ^+ 1)%f ∗
                 ai ->a wi ∗
                 ([∗ set] p ∈ spsd, p -@O> i ) ∗
                 ([∗ set] p ∈ spsd, p -@A> - ) ∗
                 R0 @@ i ->r (encode_hvc_ret_code Succ) ∗
                 R1 @@ i ->r r1 ∗
                 (∃ (wh: Word), ⌜wh ∈ sh⌝ ∗
                 R2 @@ i ->r wh ∗
                 wh ->t (i,W0,j,spsd,Lending) ∗
                 wh ->re false ∗
                 hp [ sh∖{[wh]} ]) ∗
                 TX@ i := ptx ∗
                 mem_region des ptx}}}.
Proof.
  iIntros (Hdecodei Hdecodef Hneq Hlenpsd Hdesc Hindesc Hlen_r1 Hshne Φ).
  iApply ((hvc_mem_send_not_share_nz Lending i wi r2 ptx q des sh Lend l spsd ai r0 r1 j));auto.
Qed.


(* Lemma hvc_share_nz {i ai wi r2 ptx sown q sacc sexcl des sh} *)
(*       {r0 r1} j (l :Word) (psd: list PID) (spsd: gset PID): *)
(*   (* the decoding of wi is correct *) *)
(*   decode_instruction wi = Some(Hvc) -> *)
(*   (* the decoding of R0 is FFA_SHARE *) *)
(*   decode_hvc_func r0 = Some(Share) -> *)
(*   (* caller is not the receiver *) *)
(*   i ≠ j -> *)
(*   (* l is the number of to-be-donated pages *) *)
(*   (finz.to_z l) = (Z.of_nat (length psd)) -> *)
(*   (* the descriptor, in list Word *) *)
(*   des = serialized_transaction_descriptor i j W0 l psd W0 -> *)
(*   (* the whole descriptor resides in the TX page *) *)
(*   seq_in_page (of_pid ptx) (length des) ptx -> *)
(*   (* r1 equals the length of the descriptor *) *)
(*   (finz.to_z r1) = (Z.of_nat (length des)) -> *)
(*   (* spsd is the gset of all to-be-donated pages *) *)
(*   spsd = (list_to_set psd) -> *)
(*   (* pi and pages in spsd are accessible for VM i *) *)
(*   {[to_pid_aligned ai]} ∪ spsd ⊆ sacc -> *)
(*   (* VM i owns pages in spsd *) *)
(*   spsd ⊆ sown -> *)
(*   (* pages in spsed are exclusive to VM i *) *)
(*   spsd ⊆ sexcl -> *)
(*   (* there are at least one free handles in the hpool *) *)
(*   sh ≠ ∅ -> *)
(*   {SS{{ ▷(PC @@ i ->r ai) ∗ ▷ ai ->a wi *)
(*   ∗ ▷ O@i:={q}[sown] ∗ ▷ A@i:={1}[sacc] ∗ ▷ E@i:={1}[sexcl] *)
(*   ∗ ▷ (R0 @@ i ->r r0) ∗ ▷ (R1 @@ i ->r r1) ∗ ▷(R2 @@i ->r r2) ∗  ▷ TX@ i := ptx *)
(*   ∗ ▷ mem_region des ptx *)
(*   ∗ ▷ hp{ 1 }[ sh ] }}} *)
(*    ExecI @ i {{{ RET ExecI ; PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi *)
(*   ∗ O@i:={q}[sown] ∗ A@i:={1}[sacc] ∗ E@i:={1}[sexcl∖spsd] *)
(*   ∗ R0 @@ i ->r (encode_hvc_ret_code Succ) ∗ R1 @@ i ->r r1  ∗ TX@ i := ptx *)
(*   ∗ ∃(wh: Word), ( ⌜ wh ∈ sh ⌝ ∗ R2 @@ i ->r wh ∗ wh ->t{1}(i,W0, j , psd,Sharing) *)
(*   ∗ wh ->re false  ∗ hp{1}[ (sh∖{[wh]})] ) *)
(*   ∗ mem_region des ptx}}}. *)
(* Proof. *)
(*   iIntros (Hdecodei Hdecodef Hneq Hlenpsd Hdesc Hindesc Hlenr1 Hspsd Hsacc Hsown Hsexcl Hshne Φ ). *)
(*   iApply ((hvc_mem_send_share_nz Sharing i wi r2 ptx sown q sacc sexcl des sh Share l spsd ai r0 r1 j psd));auto. *)
(* Qed. *)


End mem_send_nz.
