From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base stdpp_extra.
From HypVeri.algebra Require Import base reg mem pagetable trans mailbox base_extra.
From HypVeri.lang Require Import lang_extra mem_extra reg_extra pagetable_extra trans_extra.

Section mem_relinquish.

Context `{hypparams: HypervisorParameters}.
Context `{vmG: !gen_VMG Σ}.

Lemma p_relinquish_inv_consist σ h i j ps tt:
  inv_trans_pgt_consistent σ ->
  inv_trans_ps_disj σ ->
  σ.2 !! h = Some (Some (j, i, ps, tt, true)) ->
  j ≠ i ->
  inv_trans_pgt_consistent (update_page_table_global revoke_access (update_transaction σ h (j, i, ps, tt, false)) i ps).
Proof.
  intros Hinv_con Hinv_disj Hlk Hneq_i.
  rewrite /inv_trans_pgt_consistent /inv_trans_pgt_consistent' /=.
  rewrite map_Forall_lookup.
  intros h' meta Hlookup'.
  rewrite lookup_insert_Some in Hlookup'.
  destruct Hlookup' as [[<- <-]|[Hneq Hlookup']].
  {
    intros p Hin.
    specialize (Hinv_con h _ Hlk p Hin).
    simpl in Hinv_con.
    generalize dependent σ.1.1.1.2.
    generalize dependent σ.2.
    induction ps using set_ind_L .
    - set_solver + Hin.
    - intros tran Htran pgt Hpgt.
      simpl.
      rewrite set_fold_disj_union_strong.
      {
        rewrite set_fold_singleton.
        destruct (decide (x = p)).
        {
          subst.
          destruct tt;first done.
          rewrite Hpgt.
          apply p_upd_pgt_pgt_not_elem.
          done.
          rewrite lookup_insert_Some.
          left. split;auto.
          assert (Hrw: {[j;i]} ∖ {[i]} = ({[j]} : gset _)).
          set_solver + Hneq_i.
          rewrite /revoke_access Hrw //.
          rewrite Hpgt.
          apply p_upd_pgt_pgt_not_elem.
          done.
          rewrite lookup_insert_Some.
          left. split;auto.
          assert (Hrw: {[i]} ∖ {[i]} = (∅ : gset _)).
          set_solver +.
          rewrite /revoke_access Hrw //.
        }
        {
          destruct (pgt !! x).
          {
            feed specialize IHps.
            set_solver + Hin n.
            apply (IHps (<[h := Some (j, i, X, tt, true)]>tran));eauto.
            rewrite lookup_insert //.
            rewrite lookup_insert_ne //.
          }
          {
            feed specialize IHps.
            set_solver + Hin n.
            apply (IHps (<[h := Some (j, i, X, tt, true)]>tran));eauto.
            rewrite lookup_insert //.
          }
        }
      }
      apply upd_is_strong_assoc_comm.
      set_solver + H0.
  }
  {
    rewrite /inv_trans_pgt_consistent /inv_trans_pgt_consistent' /= in Hinv_con.
    specialize (Hinv_con h' meta Hlookup').
    simpl in Hinv_con.
    destruct meta as [[[[[sv rv] ps'] tt'] b]|];last done.
    simpl in *.
    intros p Hin.
    specialize (Hinv_con p Hin).
    assert (p ∉ ps).
    {
      intro.
      specialize (Hinv_disj h' _ Hlookup').
      simpl in Hinv_disj.
      pose proof (elem_of_pages_in_trans' p (delete h' σ.2)) as [_ Hin'].
      feed specialize Hin'.
      exists h.
      eexists.
      split.
      rewrite lookup_delete_ne //.
      done.
      set_solver + Hin H0 Hin' Hinv_disj.
    }
    destruct tt',b;auto;try apply p_upd_pgt_pgt_not_elem;auto.
  }
Qed.


Lemma mem_relinquish {tt wi sacc i j q p_tx} {ps: gset PID}
      ai r0 wh:
  (* has access to the page which the instruction is in *)
  tpa ai ≠ p_tx ->
  tpa ai ∈ sacc ->
  (* current instruction is hvc *)
  decode_instruction wi = Some(Hvc) ->
  (* the hvc call to invoke is relinquish *)
  decode_hvc_func r0 = Some(Relinquish) ->
  {SS{{(* the encoding of instruction wi is stored in location ai *)
       ▷(PC @@ i ->r ai) ∗  ▷ ai ->a wi ∗
       ▷ (R0 @@ i ->r r0) ∗
       ▷ (R1 @@ i ->r wh) ∗
       (* the pagetable, the owership ra is not required *)
       ▷ i -@A> sacc ∗
       (* the descriptor is ready in the tx page *)
       ▷ TX@ i := p_tx ∗
       (* is the receiver and the transaction has been retrieved *)
       ▷ wh -{q}>t (j, i, ps, tt) ∗ ▷ wh ->re true }}}
  ExecI @ i
  {{{ RET (false, ExecI) ;
      (* PC is incremented *)
      PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi ∗
      (* donesn't have access to psd anymore *)
      i -@A> (sacc ∖ ps) ∗
      (* return Succ to R0 *)
      R0 @@ i ->r (encode_hvc_ret_code Succ) ∗
      R1 @@ i ->r wh ∗
      (* the same tx *)
      TX@ i := p_tx ∗
      (* the transaction is marked as unretrieved *)
      wh -{q}>t(j, i, ps, tt) ∗ wh ->re false
      }}}.
Proof.
  iIntros (Hneq_tx Hin_acc Hdecode_i Hdecode_f Φ) "(>PC & >mem_ins & >R0 & >R1 & >acc & >tx & >tran & >re) HΦ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (n σ1) "%Hsche state".
  rewrite /scheduled /= /scheduler in Hsche.
  assert (σ1.1.1.2 = i) as Heq_cur. { case_bool_decide;last done. by apply fin_to_nat_inj. }
  clear Hsche.
  iModIntro.
  iDestruct "state" as "(Hnum & mem & regs & mb & rx_state & pgt_owned & pgt_acc & pgt_excl &
                            trans & hpool & retri & %Hwf & %Hdisj & %Hconsis)".
  (* valid regs *)
  iDestruct ((gen_reg_valid3 i PC ai R0 r0 R1 wh Heq_cur) with "regs PC R0 R1")
    as "(%Hlookup_PC & %Hlookup_R0 & %Hlookup_R1)";eauto.
  (* valid pt *)
  iDestruct (access_agree_check_true (tpa ai) i with "pgt_acc acc") as %Hcheckpg_ai;eauto.
  (* valid mem *)
  iDestruct (gen_mem_valid ai wi with "mem mem_ins") as %Hlookup_ai.
  (* valid tx rx *)
  iDestruct (mb_valid_tx i p_tx with "mb tx") as %Heq_tx.
  (* valid trans *)
  iDestruct (trans_valid_Some with "trans tran") as %[re Hlookup_tran].
  iDestruct (trans_valid_handle_Some with "tran") as %Hvalid_handle.
  iDestruct (retri_valid_Some with "retri re") as %[meta Hlookup_tran'].
  rewrite Hlookup_tran in Hlookup_tran'.
  inversion Hlookup_tran'. subst re. clear meta Hlookup_tran' H1.
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal i Hvc ai wi);eauto.
    rewrite Heq_tx //.
  - iModIntro.
    iIntros (m2 σ2) "vmprop_auth %HstepP".
    iFrame "vmprop_auth".
    apply (step_ExecI_normal i Hvc ai wi) in HstepP;eauto.
    2: rewrite Heq_tx //.
    remember (exec Hvc σ1) as c2 eqn:Heqc2.
    rewrite /exec /hvc Hlookup_R0 /= Hdecode_f /relinquish Hlookup_R1 /get_transaction /= Hlookup_tran Heq_cur /= in Heqc2.
    case_bool_decide;last done. clear H0. simpl in Heqc2.
    case_bool_decide;last done. clear H0.
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    (* unchanged part *)
    rewrite (preserve_get_rx_gmap σ1).
    2: rewrite p_upd_pc_mb //.
    rewrite (preserve_get_mb_gmap σ1).
    2: rewrite p_upd_pc_mb //.
    rewrite p_upd_pc_mem p_upd_reg_mem p_rvk_acc_mem p_upd_tran_mem.
    iFrame "Hnum mem mb rx_state".
    (* upd regs *)
    rewrite (u_upd_pc_regs _ i ai). 2: done.
    2: { rewrite u_upd_reg_regs p_rvk_acc_current_vm p_upd_tran_current_vm.
         rewrite (preserve_get_reg_gmap σ1). rewrite lookup_insert_ne. solve_reg_lookup. done. f_equal.
    }
    rewrite u_upd_reg_regs p_rvk_acc_current_vm p_upd_tran_current_vm Heq_cur.
    rewrite (preserve_get_reg_gmap σ1);last done.
    iDestruct ((gen_reg_update2_global PC i _ (ai ^+ 1)%f R0 i _ (encode_hvc_ret_code Succ)) with "regs PC R0")
      as ">[$ [PC R0]]";eauto.
    (* upd pgt *)
    rewrite (preserve_get_own_gmap (update_page_table_global revoke_access (update_transaction σ1 wh (j, i, ps, tt, false)) i ps) (update_incr_PC _)).
    2: rewrite p_upd_pc_pgt p_upd_reg_pgt //.
    rewrite p_rvk_acc_own. rewrite (preserve_get_own_gmap σ1);last done.
    iFrame "pgt_owned".
    rewrite (preserve_get_access_gmap (update_page_table_global revoke_access (update_transaction σ1 wh (j, i, ps, tt, true)) i ps) (update_incr_PC _)).
    2: rewrite p_upd_pc_pgt p_upd_reg_pgt //.
    iDestruct (access_agree with "pgt_acc acc") as %Hlookup_pgt_acc.
    rewrite (u_rvk_acc_acc _ _ _ sacc).
    2: {
      rewrite p_upd_tran_pgt.
      intros p Hin_p.
      specialize (Hconsis wh _ Hlookup_tran p Hin_p).
      simpl in Hconsis.
      destruct tt.
      done.
      eexists;eauto.
      eexists;eauto.
    }
    2: rewrite (preserve_get_access_gmap σ1);done.
    rewrite (preserve_get_access_gmap σ1);last done.
    iDestruct (access_update (sacc∖ ps) with "pgt_acc acc") as ">[$ acc]". done.
    rewrite (preserve_get_excl_gmap (update_page_table_global revoke_access (update_transaction σ1 wh (j, i, ps, tt, false)) i ps) (update_incr_PC _)).
    2: rewrite p_upd_pc_pgt p_upd_reg_pgt //.
    rewrite (p_rvk_acc_excl _ _ j tt).
    2: {
      intros p Hin.
      specialize (Hconsis wh _ Hlookup_tran p Hin).
      destruct tt; simpl in Hconsis.
      done.
      rewrite p_upd_tran_pgt //.
      rewrite p_upd_tran_pgt //.
    }
    rewrite (preserve_get_excl_gmap σ1);last done.
    iFrame "pgt_excl".
    (* upd tran *)
    rewrite (preserve_get_trans_gmap (update_transaction σ1 wh (j, i, ps, tt, false)) (update_incr_PC _)).
    2: rewrite p_upd_pc_trans p_upd_reg_trans //.
    rewrite u_upd_tran_trans.
    rewrite insert_id.
    2: rewrite /get_trans_gmap /get_transactions_gmap lookup_fmap Hlookup_tran //=.
    iFrame "trans".
    (* upd hp *)
    rewrite (preserve_get_hpool_gset (update_transaction σ1 wh (j, i, ps, tt, false)) (update_incr_PC _)).
    2: rewrite p_upd_pc_trans p_upd_reg_trans //. rewrite p_upd_tran_hp.
    iFrame "hpool".
    (* upd retri *)
    rewrite (preserve_get_retri_gmap (update_transaction σ1 wh (j, i, ps, tt, false)) (update_incr_PC _)).
    2: rewrite p_upd_pc_trans p_upd_reg_trans //.
    2: { exists (Some (j, i, ps, tt, true)). split;eauto. }
    rewrite u_upd_tran_retri.
    iDestruct (retri_update_flip with "retri re") as ">[$ re]".
    (* inv_trans_wellformed *)
    rewrite (preserve_inv_trans_wellformed (update_transaction σ1 wh (j, i, ps, tt, false))).
    2: rewrite p_upd_pc_trans p_upd_reg_trans //.
    iAssert (⌜inv_trans_wellformed (update_transaction σ1 wh (j, i, ps, tt, false))⌝%I) as "$". iPureIntro.
    apply (p_upd_tran_inv_wf σ1 wh);eauto.
    (* inv_trans_pgt_consistent *)
    rewrite (preserve_inv_trans_pgt_consistent (update_page_table_global revoke_access (update_transaction σ1 wh (j, i, ps, tt, false)) i ps) (update_incr_PC _)).
    2: rewrite p_upd_pc_trans p_upd_reg_trans //.
    2: rewrite p_upd_pc_pgt p_upd_reg_pgt //.
    iAssert (⌜inv_trans_pgt_consistent (update_page_table_global revoke_access (update_transaction σ1 wh (j, i, ps, tt, false)) i ps)⌝%I) as "$". iPureIntro.
    apply p_relinquish_inv_consist;auto.
    { destruct Hwf as [_ [Hwf _]]. specialize (Hwf wh _ Hlookup_tran). done. }
    (* inv_trans_ps_disj *)
    rewrite (preserve_inv_trans_ps_disj (update_transaction σ1 wh (j, i, ps, tt, false))).
    2: rewrite p_upd_pc_trans p_upd_reg_trans //.
    iAssert (⌜inv_trans_ps_disj (update_transaction σ1 wh (j, i, ps, tt, false))⌝%I) as "$". iPureIntro.
    eapply p_upd_tran_inv_disj.
    apply Hdisj.
    exact Hlookup_tran.
    done.
    (* just_scheduled *)
    iModIntro.
    rewrite /just_scheduled_vms /just_scheduled.
    rewrite /scheduled /machine.scheduler /= /scheduler.
    rewrite p_upd_pc_current_vm p_upd_reg_current_vm p_rvk_acc_current_vm p_upd_tran_current_vm.
    rewrite Heq_cur.
    iSplitL "".
    set fl := (filter _ _).
    assert (fl = []) as ->.
    {
      rewrite /fl.
      induction n.
      - simpl.
        rewrite filter_nil //=.
      - rewrite seq_S.
        rewrite filter_app.
        rewrite IHn.
        simpl.
        rewrite filter_cons_False /=. rewrite filter_nil //.
        rewrite andb_negb_l //.
    }
    by iSimpl.
    (* Φ *)
    case_bool_decide;last contradiction.
    simpl. iApply "HΦ".
    rewrite /fresh_handles. iFrame.
Qed.

Lemma mem_relinquish_invalid_handle {E i wi sacc r0 r2 wh p_tx} ai:
  tpa ai ≠ p_tx ->
  (tpa ai) ∈ sacc ->
  (* the current instruction is hvc *)
  (* the decoding of wi is correct *)
  decode_instruction wi = Some(Hvc) ->
  (* the hvc call to invoke is retrieve *)
  decode_hvc_func r0 = Some(Relinquish) ->
  wh ∉ valid_handles ->
  {SS{{(* the encoding of instruction wi is stored in location ai *)
       ▷ (PC @@ i ->r ai) ∗ ▷ ai ->a wi ∗
       (* registers *)
       ▷ (R0 @@ i ->r r0) ∗
       ▷ (R1 @@ i ->r wh) ∗
       ▷ (R2 @@ i ->r r2) ∗
       ▷ i -@A> sacc ∗
       ▷ TX@ i := p_tx}}}
   ExecI @ i; E
   {{{ RET (false, ExecI) ;
       (* PC is incremented *)
       PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi ∗
       R0 @@ i ->r (encode_hvc_ret_code Error) ∗
       R1 @@ i ->r wh ∗
       R2 @@ i ->r (encode_hvc_error InvParam) ∗
       i -@A> sacc ∗
       TX@ i := p_tx
   }}}.
Proof.
  iIntros (Hneq_tx Hin_acc Hdecode_i Hdecode_f Hnin_wh Φ)
          "(>PC & >mem_ins & >R0 & >R1 & >R2 & >acc & >tx) HΦ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (n σ1) "%Hsche state".
  rewrite /scheduled /= /scheduler in Hsche.
  assert (σ1.1.1.2 = i) as Heq_cur. { case_bool_decide;last done. by apply fin_to_nat_inj. }
  clear Hsche.
  iModIntro.
  iDestruct "state" as "(Hnum & mem & regs & mb & rx_state & pgt_owned & pgt_acc & pgt_excl &
                            trans & hpool & retri & %Hwf & %Hdisj & %Hconsis)".
  (* valid regs *)
  iDestruct ((gen_reg_valid4 i PC ai R0 r0 R1 wh R2 r2 Heq_cur) with "regs PC R0 R1 R2")
    as "(%Hlookup_PC & %Hlookup_R0 & %Hlookup_R1 & %Hlookup_R2)";eauto.
  (* valid pt *)
  iDestruct (access_agree_check_true (tpa ai) i with "pgt_acc acc") as %Hcheckpg_ai;eauto.
  (* valid mem *)
  iDestruct (gen_mem_valid ai wi with "mem mem_ins") as %Hlookup_ai.
  (* valid tx *)
  iDestruct (mb_valid_tx i p_tx with "mb tx") as %Heq_tx.
  (* valid tran *)
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal i Hvc ai wi);auto.
    rewrite Heq_tx //.
  - iModIntro.
    iIntros (m2 σ2) "vmprop_auth %HstepP".
    iFrame "vmprop_auth".
    apply (step_ExecI_normal i Hvc ai wi) in HstepP;eauto.
    2: rewrite Heq_tx //.
    remember (exec Hvc σ1) as c2 eqn:Heqc2.
    rewrite /exec /hvc Hlookup_R0 /= Hdecode_f /relinquish Hlookup_R1 /= in Heqc2.
    assert (Hwh_None: get_transaction σ1 wh = None).
    {
      destruct Hwf as [_ [_ Hwf]].
      rewrite /inv_finite_handles in Hwf.
      rewrite Hwf in Hnin_wh.
      rewrite not_elem_of_dom in Hnin_wh.
      rewrite /get_transaction Hnin_wh //.
      case_bool_decide;done.
    }
    rewrite Hwh_None /= in Heqc2.
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    iDestruct (hvc_error_update (E:= E) InvParam with "PC R0 R2 [$Hnum $mem $regs $mb $rx_state $pgt_owned $pgt_acc $pgt_excl $ trans $hpool $retri]")
    as ">[[$ $] ?]". 1-4: auto. iPureIntro. auto.
    rewrite /scheduled /machine.scheduler /= /scheduler.
    rewrite p_upd_pc_current_vm 2!p_upd_reg_current_vm Heq_cur.
    case_bool_decide;last contradiction.
    simpl. iApply "HΦ".
    iFrame.
    by iFrame.
Qed.

Lemma mem_relinquish_fresh_handle {E i wi sacc r0 r2 wh sh q p_tx} ai:
  tpa ai ≠ p_tx ->
  (tpa ai) ∈ sacc ->
  decode_instruction wi = Some(Hvc) ->
  decode_hvc_func r0 = Some(Relinquish) ->
  wh ∈ sh ->
  {SS{{▷ (PC @@ i ->r ai) ∗ ▷ ai ->a wi ∗
       ▷ (R0 @@ i ->r r0) ∗
       ▷ (R1 @@ i ->r wh) ∗
       ▷ (R2 @@ i ->r r2) ∗
       ▷ i -@A> sacc ∗
       ▷ TX@ i := p_tx ∗
       ▷ fresh_handles q sh}}}
   ExecI @ i; E
   {{{ RET (false, ExecI) ;
       PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi ∗
       R0 @@ i ->r (encode_hvc_ret_code Error) ∗
       R1 @@ i ->r wh ∗
       R2 @@ i ->r (encode_hvc_error InvParam) ∗
       i -@A> sacc ∗
       TX@ i := p_tx ∗
       fresh_handles q sh
   }}}.
Proof.
  iIntros (Hneq_tx Hin_acc Hdecode_i Hdecode_f Hin_wh Φ)
          "(>PC & >mem_ins & >R0 & >R1 & >R2 & >acc & >tx & >[hp handles]) HΦ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (n σ1) "%Hsche state".
  rewrite /scheduled /= /scheduler in Hsche.
  assert (σ1.1.1.2 = i) as Heq_cur. { case_bool_decide;last done. by apply fin_to_nat_inj. }
  clear Hsche.
  iModIntro.
  iDestruct "state" as "(Hnum & mem & regs & mb & rx_state & pgt_owned & pgt_acc & pgt_excl &
                            trans & hpool & retri & %Hwf & %Hdisj & %Hconsis)".
  (* valid regs *)
  iDestruct ((gen_reg_valid4 i PC ai R0 r0 R1 wh R2 r2 Heq_cur) with "regs PC R0 R1 R2")
    as "(%Hlookup_PC & %Hlookup_R0 & %Hlookup_R1 & %Hlookup_R2)";eauto.
  (* valid pt *)
  iDestruct (access_agree_check_true (tpa ai) i with "pgt_acc acc") as %Hcheckpg_ai;eauto.
  (* valid mem *)
  iDestruct (gen_mem_valid ai wi with "mem mem_ins") as %Hlookup_ai.
  (* valid tx *)
  iDestruct (mb_valid_tx i p_tx with "mb tx") as %Heq_tx.
  (* valid hpool *)
  iDestruct (hpool_valid with "hpool hp") as %Heq_hp.
  (* valid tran *)
  iAssert (⌜get_transaction σ1 wh = None⌝%I) as %Hwh_None.
  {
    iDestruct (big_sepS_elem_of _ _ wh with "handles") as "[tran _]".
    done.
    iDestruct (trans_valid_None with "trans tran") as %Hlookup_tran.
    iPureIntro.
    rewrite /get_transaction Hlookup_tran //.
    case_bool_decide;done.
  }
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal i Hvc ai wi);auto.
    rewrite Heq_tx //.
  - iModIntro.
    iIntros (m2 σ2) "vmprop_auth %HstepP".
    iFrame "vmprop_auth".
    apply (step_ExecI_normal i Hvc ai wi) in HstepP;eauto.
    2: rewrite Heq_tx //.
    remember (exec Hvc σ1) as c2 eqn:Heqc2.
    rewrite /exec /hvc Hlookup_R0 /= Hdecode_f /relinquish Hlookup_R1 /= in Heqc2.
    rewrite Hwh_None /= in Heqc2.
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    iDestruct (hvc_error_update (E:= E) InvParam with "PC R0 R2 [$Hnum $mem $regs $mb $rx_state $pgt_owned $pgt_acc $pgt_excl $ trans $hpool $retri]")
    as ">[[$ $] ?]". 1-4: auto. iPureIntro. auto.
    rewrite /scheduled /machine.scheduler /= /scheduler.
    rewrite p_upd_pc_current_vm 2!p_upd_reg_current_vm Heq_cur.
    case_bool_decide;last contradiction.
    simpl. iApply "HΦ".
    iFrame.
    by iFrame.
Qed.

Lemma mem_relinquish_invalid_trans {E i wi sacc r0 r2 wh meta q p_tx} ai:
  tpa ai ≠ p_tx ->
  (tpa ai) ∈ sacc ->
  decode_instruction wi = Some(Hvc) ->
  decode_hvc_func r0 = Some(Relinquish) ->
  meta.1.1.2 ≠ i ->
  {SS{{▷ (PC @@ i ->r ai) ∗ ▷ ai ->a wi ∗
       ▷ (R0 @@ i ->r r0) ∗
       ▷ (R1 @@ i ->r wh) ∗
       ▷ (R2 @@ i ->r r2) ∗
       ▷ i -@A> sacc ∗
       ▷ TX@ i := p_tx ∗
       ▷ wh -{q}>t (meta)
       }}}
   ExecI @ i; E
   {{{ RET (false, ExecI) ;
       PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi ∗
       R0 @@ i ->r (encode_hvc_ret_code Error) ∗
       R1 @@ i ->r wh ∗
       R2 @@ i ->r (encode_hvc_error Denied) ∗
       i -@A> sacc ∗
       TX@ i := p_tx ∗
       wh -{q}>t (meta)
   }}}.
Proof.
  iIntros (Hneq_tx Hin_acc Hdecode_i Hdecode_f Hin_wh Φ)
          "(>PC & >mem_ins & >R0 & >R1 & >R2 & >acc & >tx & >tran) HΦ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (n σ1) "%Hsche state".
  rewrite /scheduled /= /scheduler in Hsche.
  assert (σ1.1.1.2 = i) as Heq_cur. { case_bool_decide;last done. by apply fin_to_nat_inj. }
  clear Hsche.
  iModIntro.
  iDestruct "state" as "(Hnum & mem & regs & mb & rx_state & pgt_owned & pgt_acc & pgt_excl &
                            trans & hpool & retri & %Hwf & %Hdisj & %Hconsis)".
  (* valid regs *)
  iDestruct ((gen_reg_valid4 i PC ai R0 r0 R1 wh R2 r2 Heq_cur) with "regs PC R0 R1 R2")
    as "(%Hlookup_PC & %Hlookup_R0 & %Hlookup_R1 & %Hlookup_R2)";eauto.
  (* valid pt *)
  iDestruct (access_agree_check_true (tpa ai) i with "pgt_acc acc") as %Hcheckpg_ai;eauto.
  (* valid mem *)
  iDestruct (gen_mem_valid ai wi with "mem mem_ins") as %Hlookup_ai.
  (* valid tx *)
  iDestruct (mb_valid_tx i p_tx with "mb tx") as %Heq_tx.
  (* valid tran *)
  iDestruct (trans_valid_Some with "trans tran") as %[? Hlookup_tran].
  iDestruct (trans_valid_handle_Some with "tran") as %Hvalid_handle.
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal i Hvc ai wi);auto.
    rewrite Heq_tx //.
  - iModIntro.
    iIntros (m2 σ2) "vmprop_auth %HstepP".
    iFrame "vmprop_auth".
    apply (step_ExecI_normal i Hvc ai wi) in HstepP;eauto.
    2: rewrite Heq_tx //.
    remember (exec Hvc σ1) as c2 eqn:Heqc2.
    rewrite /exec /hvc Hlookup_R0 /= Hdecode_f /relinquish Hlookup_R1 /= in Heqc2.
    rewrite /get_transaction Hlookup_tran /= in Heqc2.
    destruct meta as [[[? ?] ?] ?].
    case_bool_decide;last contradiction. clear H0. simpl in Heqc2.
    case_bool_decide;rewrite Heq_cur // in H0.
    rewrite andb_false_r /= in Heqc2.
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    iDestruct (hvc_error_update (E:= E) Denied with "PC R0 R2 [$Hnum $mem $regs $mb $rx_state $pgt_owned $pgt_acc $pgt_excl $ trans $hpool $retri]")
    as ">[[$ $] ?]". 1-4: auto. iPureIntro. auto.
    rewrite /scheduled /machine.scheduler /= /scheduler.
    rewrite p_upd_pc_current_vm 2!p_upd_reg_current_vm Heq_cur.
    case_bool_decide;last contradiction.
    simpl. iApply "HΦ".
    iFrame.
    by iFrame.
Qed.

Lemma mem_relinquish_not_retrieved{E i wi sacc r0 r2 wh q p_tx} ai:
  tpa ai ≠ p_tx ->
  (tpa ai) ∈ sacc ->
  decode_instruction wi = Some(Hvc) ->
  decode_hvc_func r0 = Some(Relinquish) ->
  {SS{{▷ (PC @@ i ->r ai) ∗ ▷ ai ->a wi ∗
       ▷ (R0 @@ i ->r r0) ∗
       ▷ (R1 @@ i ->r wh) ∗
       ▷ (R2 @@ i ->r r2) ∗
       ▷ i -@A> sacc ∗
       ▷ TX@ i := p_tx ∗
       ▷ wh -{q}>re false
       }}}
   ExecI @ i; E
   {{{ RET (false, ExecI) ;
       PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi ∗
       R0 @@ i ->r (encode_hvc_ret_code Error) ∗
       R1 @@ i ->r wh ∗
       R2 @@ i ->r (encode_hvc_error Denied) ∗
       i -@A> sacc ∗
       TX@ i := p_tx ∗
       wh -{q}>re false
   }}}.
Proof.
  iIntros (Hneq_tx Hin_acc Hdecode_i Hdecode_f Φ)
          "(>PC & >mem_ins & >R0 & >R1 & >R2 & >acc & >tx & >re) HΦ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (n σ1) "%Hsche state".
  rewrite /scheduled /= /scheduler in Hsche.
  assert (σ1.1.1.2 = i) as Heq_cur. { case_bool_decide;last done. by apply fin_to_nat_inj. }
  clear Hsche.
  iModIntro.
  iDestruct "state" as "(Hnum & mem & regs & mb & rx_state & pgt_owned & pgt_acc & pgt_excl &
                            trans & hpool & retri & %Hwf & %Hdisj & %Hconsis)".
  (* valid regs *)
  iDestruct ((gen_reg_valid4 i PC ai R0 r0 R1 wh R2 r2 Heq_cur) with "regs PC R0 R1 R2")
    as "(%Hlookup_PC & %Hlookup_R0 & %Hlookup_R1 & %Hlookup_R2)";eauto.
  (* valid pt *)
  iDestruct (access_agree_check_true (tpa ai) i with "pgt_acc acc") as %Hcheckpg_ai;eauto.
  (* valid mem *)
  iDestruct (gen_mem_valid ai wi with "mem mem_ins") as %Hlookup_ai.
  (* valid tx *)
  iDestruct (mb_valid_tx i p_tx with "mb tx") as %Heq_tx.
  (* valid tran *)
  iDestruct (retri_valid_Some with "retri re") as %[? Hlookup_re].
  iDestruct (retri_valid_handle_Some with "re") as %Hvalid_handle.
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal i Hvc ai wi);auto.
    rewrite Heq_tx //.
  - iModIntro.
    iIntros (m2 σ2) "vmprop_auth %HstepP".
    iFrame "vmprop_auth".
    apply (step_ExecI_normal i Hvc ai wi) in HstepP;eauto.
    2: rewrite Heq_tx //.
    remember (exec Hvc σ1) as c2 eqn:Heqc2.
    rewrite /exec /hvc Hlookup_R0 /= Hdecode_f /relinquish Hlookup_R1 /= in Heqc2.
    rewrite /get_transaction Hlookup_re /= in Heqc2.
    destruct x as [[[? ?] ?] ?].
    assert (Heq_c2 : (m2,σ2) = (ExecI, update_incr_PC (update_reg (update_reg σ1 R0 (encode_hvc_ret_code Error)) R2 (encode_hvc_error Denied)))).
    {
      case_bool_decide;last contradiction.
      destruct HstepP;subst m2 σ2; subst c2; done.
    }
    inversion Heq_c2. clear H1 H2 Heq_c2 Heqc2.
    iDestruct (hvc_error_update (E:= E) Denied with "PC R0 R2 [$Hnum $mem $regs $mb $rx_state $pgt_owned $pgt_acc $pgt_excl $ trans $hpool $retri]")
    as ">[[$ $] ?]". 1-4: auto. iPureIntro. auto.
    rewrite /scheduled /machine.scheduler /= /scheduler.
    rewrite p_upd_pc_current_vm 2!p_upd_reg_current_vm Heq_cur.
    case_bool_decide;last contradiction.
    simpl. iApply "HΦ".
    iFrame.
    by iFrame.
Qed.

End mem_relinquish.
