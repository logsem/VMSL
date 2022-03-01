From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base stdpp_extra.
From HypVeri.algebra Require Import base reg mem pagetable trans mailbox base_extra.
From HypVeri.lang Require Import lang_extra mem_extra reg_extra pagetable_extra trans_extra.

Section mem_reclaim.

Context `{hypparams: HypervisorParameters}.
Context `{vmG: !gen_VMG Σ}.


Lemma p_reclaim_inv_consist σ h v ps :
  inv_trans_pgt_consistent σ ->
  inv_trans_ps_disj σ ->
  (∃ meta, get_trans_gmap σ !! h = Some (Some meta) ∧ meta.1.1.1 = v ∧ meta.1.2 = ps) ->
  inv_trans_pgt_consistent (remove_transaction (update_page_table_global grant_access σ v ps) h).
Proof.
  intros Hinv_con Hinv_disj (? & Hlookup & <- & <-).
  rewrite /inv_trans_pgt_consistent /inv_trans_pgt_consistent' /=.
  rewrite map_Forall_lookup.
  intros h' meta Hlookup'.
  destruct (decide (h = h')).
  subst h'.
  rewrite lookup_insert_Some in Hlookup'.
  destruct Hlookup' as [[_ <-]|[? _]];done.
  rewrite lookup_insert_ne //in Hlookup'.
  rewrite /inv_trans_pgt_consistent /inv_trans_pgt_consistent' /= in Hinv_con.
  specialize (Hinv_con h' meta Hlookup').
  destruct meta as [[[[[sv rv] ps] tt] b]|];last done.
  intros p Hin.
  specialize (Hinv_con p Hin).
  rewrite /inv_trans_ps_disj /inv_trans_ps_disj' /= in Hinv_disj.
  simpl in *.
  assert (p ∉ x.1.2).
  {
    rewrite /get_trans_gmap /get_transactions_gmap in Hlookup.
    rewrite lookup_fmap_Some in Hlookup.
    destruct Hlookup as [otrans [Heq Hlookup]].
    destruct otrans;last inversion Heq.
    inversion_clear Heq.
    specialize (Hinv_disj h (Some t) Hlookup).
    simpl in Hinv_disj.
    assert (p ∈ pages_in_trans' (delete h σ.2)).
    {
      rewrite elem_of_pages_in_trans'.
      exists h' , (sv, rv, ps, tt, b).
      split;last done.
      rewrite lookup_delete_ne //.
    }
    set_solver + Hinv_disj H0.
  }
  destruct tt,b;auto;try apply p_upd_pgt_pgt_not_elem;auto.
Qed.

Lemma mem_reclaim_lend {E i wi sacc j sh r0 p_tx} {spsd: gset PID}
      ai wh:
  tpa ai ≠ p_tx ->
  tpa ai ∈ sacc ->
  (* current instruction is hvc *)
  decode_instruction wi = Some(Hvc) ->
  (* the hvc call to invoke is relinquish *)
  decode_hvc_func r0 = Some(Reclaim) ->
  {SS{{(* the encoding of instruction wi is stored in location ai *)
       ▷(PC @@ i ->r ai) ∗ ▷ ai ->a wi ∗
       (* the handle of transaction is stored in R1 *)
       ▷ (R0 @@ i ->r r0) ∗ ▷ (R1 @@ i ->r wh) ∗
       (* the pagetable *)
       ▷ i -@A> sacc ∗
       ▷ TX@ i := p_tx ∗
       (* the transaction has not been retrieved/has been relinquished *)
       ▷ wh ->re false ∗ ▷ wh ->t (i, j, spsd, Lending) ∗
       (* handle pool *)
       ▷ fresh_handles 1 sh}}}
  ExecI @ i; E
  {{{ RET (false, ExecI) ;
      (* PC is incremented *)
      PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi ∗
      (* return Succ to R0*)
      R0 @@ i ->r (encode_hvc_ret_code Succ) ∗ (R1 @@ i ->r wh) ∗
      (* gain access/ownership of those pages *)
      i -@A> (sacc ∪ spsd) ∗
      TX@ i := p_tx ∗
      (* the transaction is deallocated, release the handle to the handle pool *)
      fresh_handles 1 (sh ∪ {[wh]}) }}}.
Proof.
  iIntros (Hneq_tx Hin_acc Hdecode_i Hdecode_f Φ)
          "(>PC & >mem_ins & >R0 & >R1 & >acc & >tx & >re & >tran & >[hp handles]) HΦ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (n σ1) "%Hsche state".
  rewrite /scheduled /= /scheduler in Hsche.
  assert (σ1.1.1.2 = i) as Heq_cur. { case_bool_decide;last done. by apply fin_to_nat_inj. }
  clear Hsche.
  iModIntro.
  iDestruct "state" as "(Hnum & mem & regs & mb & rx_state & pgt_owned & pgt_acc & pgt_excl &
                            trans & hpool & retri & %Hwf & %Hconsis & %Hdisj)".
  (* valid regs *)
  iDestruct ((gen_reg_valid3 i PC ai R0 r0 R1 wh Heq_cur) with "regs PC R0 R1")
    as "(%Hlookup_PC & %Hlookup_R0 & %Hlookup_R1)";eauto.
  (* valid pt *)
  iDestruct (access_agree_check_true (tpa ai) i with "pgt_acc acc") as %Hcheckpg_ai;eauto.
  (* valid mem *)
  iDestruct (gen_mem_valid ai wi with "mem mem_ins") as %Hlookup_ai.
  (* valid tx *)
  iDestruct (mb_valid_tx i p_tx with "mb tx") as %Heq_tx.
  (* valid trans *)
  iDestruct (trans_valid_Some with "trans tran") as %[re Hlookup_tran].
  iDestruct (retri_valid_Some with "retri re") as %[meta Hlookup_tran'].
  rewrite Hlookup_tran in Hlookup_tran'.
  inversion Hlookup_tran'. subst re. clear meta Hlookup_tran' H1.
  (* valid hpool *)
  iDestruct (hpool_valid with "hpool hp") as %Heq_hp.
  iAssert ( ⌜wh ∉ sh⌝)%I as %Hnin.
  {
    iApply not_elem_of_fresh_handles. iFrame.
  }
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
    rewrite /exec /hvc Hlookup_R0 /= Hdecode_f /reclaim //= Hlookup_R1 //= in Heqc2.
    rewrite /get_transaction Hlookup_tran //= in Heqc2.
    case_bool_decide;last done. clear H0.
    rewrite andb_true_l /= in Heqc2.
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    (* unchanged part *)
    rewrite (preserve_get_mb_gmap σ1).
    rewrite (preserve_get_rx_gmap σ1).
    all: try rewrite p_upd_pc_mb //.
    rewrite p_upd_pc_mem p_upd_reg_mem p_rm_tran_mem p_grnt_acc_mem.
    iFrame "Hnum mem rx_state mb".
    (* upd regs *)
    rewrite (u_upd_pc_regs _ i ai) //.
    2: { rewrite u_upd_reg_regs p_rm_tran_current_vm  p_grnt_acc_current_vm.
         rewrite (preserve_get_reg_gmap σ1). rewrite lookup_insert_ne //. solve_reg_lookup. done.
    }
    rewrite u_upd_reg_regs p_rm_tran_current_vm p_grnt_acc_current_vm  Heq_cur.
    rewrite (preserve_get_reg_gmap σ1) //.
    iDestruct ((gen_reg_update2_global PC i _ (ai ^+ 1)%f R0 i _ (encode_hvc_ret_code Succ)) with "regs PC R0")
      as ">[$ [PC R0]]";eauto.
    (* upd pgt *)
    rewrite (preserve_get_own_gmap (update_page_table_global grant_access (remove_transaction σ1 wh) i spsd) (update_incr_PC _)).
    2: rewrite p_upd_pc_pgt p_upd_reg_pgt //.
    rewrite p_grnt_acc_own. rewrite (preserve_get_own_gmap σ1) //.
    iFrame "pgt_owned".
    rewrite (preserve_get_access_gmap (update_page_table_global grant_access (remove_transaction σ1 wh) i spsd) (update_incr_PC _)).
    2: rewrite p_upd_pc_pgt p_upd_reg_pgt //.
    iDestruct (access_agree with "pgt_acc acc") as %Hlookup_pgt_acc.
    rewrite (u_grnt_acc_acc _ _ _ sacc ). 2: rewrite (preserve_get_access_gmap σ1) //.
    rewrite (preserve_get_access_gmap σ1) //.
    iDestruct (access_update (spsd ∪ sacc) with "pgt_acc acc") as ">[pgt_acc acc]". done.
    iFrame "pgt_acc".
    rewrite (preserve_get_excl_gmap (update_page_table_global grant_access (remove_transaction σ1 wh) i spsd) (update_incr_PC _)).
    2: rewrite p_upd_pc_pgt p_upd_reg_pgt //.
    rewrite p_grnt_acc_excl. rewrite (preserve_get_excl_gmap σ1) //.
    iFrame "pgt_excl".
    (* upd tran *)
    rewrite (preserve_get_trans_gmap (remove_transaction σ1 wh) (update_incr_PC _)).
    2: rewrite p_upd_pc_trans p_upd_reg_trans  //.
    rewrite u_rm_tran_tran.
    iDestruct (trans_update_delete with "trans tran") as ">[trans tran]".
    iFrame "trans".
    (* upd hp *)
    rewrite (preserve_get_hpool_gset (remove_transaction σ1 wh) (update_incr_PC _)).
    2: rewrite p_upd_pc_trans p_upd_reg_trans //. rewrite u_rm_tran_hp.
    iDestruct (hpool_update_union wh with "hpool hp") as ">[hpool hp]".
    iFrame "hpool".
    (* upd retri *)
    rewrite (preserve_get_retri_gmap (remove_transaction σ1 wh) (update_incr_PC _)).
    2: rewrite p_upd_pc_trans p_upd_reg_trans //. rewrite u_rm_tran_retri.
    iDestruct (retri_update_delete with "retri re") as ">[retri re]".
    iFrame "retri".
    (* inv_trans_wellformed *)
    rewrite (preserve_inv_trans_wellformed (remove_transaction σ1 wh)).
    2: rewrite p_upd_pc_trans p_upd_reg_trans //.
    iAssert (⌜inv_trans_wellformed (remove_transaction σ1 wh)⌝%I) as "$". iPureIntro. by apply (p_rm_tran_inv_wf σ1 wh).
    (* inv_trans_pgt_consistent *)
    rewrite (preserve_inv_trans_pgt_consistent (remove_transaction (update_page_table_global grant_access σ1 i spsd) wh) (update_incr_PC _)).
    2: rewrite p_upd_pc_trans p_upd_reg_trans //.
    2: rewrite p_upd_pc_pgt p_upd_reg_pgt //.
    iAssert (⌜inv_trans_pgt_consistent (remove_transaction (update_page_table_global grant_access σ1 i spsd) wh)⌝%I) as "$". iPureIntro. 
    apply p_reclaim_inv_consist;auto.
    exists (i, j, spsd, Lending). split;auto.
    rewrite /get_trans_gmap /get_transactions_gmap.
    rewrite lookup_fmap Hlookup_tran //.
    (* inv_trans_ps_disj *)
    rewrite (preserve_inv_trans_ps_disj (remove_transaction (update_page_table_global grant_access σ1 i spsd) wh)).
    2: rewrite p_upd_pc_trans p_upd_reg_trans //.
    iAssert (⌜inv_trans_ps_disj (remove_transaction (update_page_table_global grant_access σ1 i spsd) wh)⌝%I) as "$". iPureIntro.
    apply p_rm_tran_inv_disj.
    rewrite (preserve_inv_trans_ps_disj σ1) //.
    (* just_scheduled *)
    iModIntro.
    rewrite /just_scheduled_vms /just_scheduled.
    rewrite /scheduled /machine.scheduler /= /scheduler.
    rewrite p_upd_pc_current_vm p_upd_reg_current_vm p_rm_tran_current_vm p_grnt_acc_current_vm.
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
        rewrite filter_cons_False //=.
        rewrite andb_negb_l.
        done.
    }
    by iSimpl.
    (* Φ *)
    case_bool_decide;last done.
    simpl.
    iApply "HΦ".
    rewrite union_comm_L.
    rewrite /fresh_handles. iFrame.
    rewrite union_comm_L. iFrame.
    rewrite big_sepS_union. rewrite big_sepS_singleton. iFrame.
    set_solver + Hnin.
Qed.

Lemma mem_reclaim_donate {E i wi sacc j sh r0 p_tx} {spsd: gset PID}
      ai wh:
  tpa ai ≠ p_tx ->
  tpa ai ∈ sacc ->
  (* current instruction is hvc *)
  decode_instruction wi = Some(Hvc) ->
  (* the hvc call to invoke is relinquish *)
  decode_hvc_func r0 = Some(Reclaim) ->
  {SS{{(* the encoding of instruction wi is stored in location ai *)
       ▷(PC @@ i ->r ai) ∗ ▷ ai ->a wi ∗
       (* the handle of transaction is stored in R1 *)
       ▷ (R0 @@ i ->r r0) ∗ ▷ (R1 @@ i ->r wh) ∗
       (* the pagetable *)
       ▷ i -@A> sacc ∗
       ▷ TX@ i := p_tx ∗
       (* the transaction has not been retrieved/has been relinquished *)
       ▷ wh ->re false ∗ ▷ wh ->t (i, j, spsd, Donation) ∗
       (* handle pool *)
       ▷ fresh_handles 1 sh}}}
  ExecI @ i; E
  {{{ RET (false, ExecI) ;
      (* PC is incremented *)
      PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi ∗
      (* return Succ to R0*)
      R0 @@ i ->r (encode_hvc_ret_code Succ) ∗ (R1 @@ i ->r wh) ∗
      (* gain access/ownership of those pages *)
      i -@A> (sacc ∪ spsd) ∗
      TX@ i := p_tx ∗
      (* the transaction is deallocated, release the handle to the handle pool *)
      fresh_handles 1 (sh ∪ {[wh]}) }}}.
Proof.
Admitted.

Lemma mem_reclaim_share {E i wi sacc j sh r0 p_tx} {spsd: gset PID}
      ai wh:
  tpa ai ≠ p_tx ->
  tpa ai ∈ sacc ->
  (* current instruction is hvc *)
  decode_instruction wi = Some(Hvc) ->
  (* the hvc call to invoke is relinquish *)
  decode_hvc_func r0 = Some(Reclaim) ->
  {SS{{(* the encoding of instruction wi is stored in location ai *)
       ▷(PC @@ i ->r ai) ∗ ▷ ai ->a wi ∗
       (* the handle of transaction is stored in R1 *)
       ▷ (R0 @@ i ->r r0) ∗ ▷ (R1 @@ i ->r wh) ∗
       (* the pagetable *)
       ▷ i -@A> sacc ∗
       ▷ ([∗ set] p ∈ spsd, p -@E> false) ∗
       ▷ TX@ i := p_tx ∗
       (* the transaction has not been retrieved/has been relinquished *)
       ▷ wh ->re false ∗ ▷ wh ->t (i, j, spsd, Sharing) ∗
       (* handle pool *)
       ▷ fresh_handles 1 sh}}}
  ExecI @ i; E
  {{{ RET (false, ExecI) ;
      (* PC is incremented *)
      PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi ∗
      (* return Succ to R0*)
      R0 @@ i ->r (encode_hvc_ret_code Succ) ∗ (R1 @@ i ->r wh) ∗
      (* gain access/ownership of those pages *)
      i -@A> (sacc ∪ spsd) ∗
      ([∗ set] p ∈ spsd, p -@E> true) ∗
      TX@ i := p_tx ∗
      (* the transaction is deallocated, release the handle to the handle pool *)
      fresh_handles 1 (sh ∪ {[wh]}) }}}.
Proof.
Admitted.

Lemma mem_reclaim_invalid_handle {E i wi sacc r0 r2 wh p_tx} ai:
  tpa ai ≠ p_tx ->
  (tpa ai) ∈ sacc ->
  (* the current instruction is hvc *)
  (* the decoding of wi is correct *)
  decode_instruction wi = Some(Hvc) ->
  (* the hvc call to invoke is retrieve *)
  decode_hvc_func r0 = Some(Reclaim) ->
  wh ∉ hs_all ->
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
Admitted.

Lemma mem_reclaim_fresh_handle {E i wi sacc r0 r2 wh sh q p_tx} ai:
  tpa ai ≠ p_tx ->
  (tpa ai) ∈ sacc ->
  decode_instruction wi = Some(Hvc) ->
  decode_hvc_func r0 = Some(Reclaim) ->
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
Admitted.

Lemma mem_reclaim_invalid_trans {E i wi sacc r0 r2 wh meta q p_tx} ai:
  tpa ai ≠ p_tx ->
  (tpa ai) ∈ sacc ->
  decode_instruction wi = Some(Hvc) ->
  decode_hvc_func r0 = Some(Reclaim) ->
  meta.1.1.1 ≠ i ->
  {SS{{▷ (PC @@ i ->r ai) ∗ ▷ ai ->a wi ∗
       ▷ (R0 @@ i ->r r0) ∗
       ▷ (R1 @@ i ->r wh) ∗
       ▷ (R2 @@ i ->r r2) ∗
       ▷ i -@A> sacc ∗
       ▷ TX@ i := p_tx ∗
       ▷ wh -{q}>t meta
       }}}
   ExecI @ i; E
   {{{ RET (false, ExecI) ;
       PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi ∗
       R0 @@ i ->r (encode_hvc_ret_code Error) ∗
       R1 @@ i ->r wh ∗
       R2 @@ i ->r (encode_hvc_error Denied) ∗
       i -@A> sacc ∗
       TX@ i := p_tx ∗
       wh -{q}>t meta
   }}}.
Proof.
Admitted.

Lemma mem_reclaim_retrieved{E i wi sacc r0 r2 wh q p_tx} ai:
  tpa ai ≠ p_tx ->
  (tpa ai) ∈ sacc ->
  decode_instruction wi = Some(Hvc) ->
  decode_hvc_func r0 = Some(Reclaim) ->
  {SS{{▷ (PC @@ i ->r ai) ∗ ▷ ai ->a wi ∗
       ▷ (R0 @@ i ->r r0) ∗
       ▷ (R1 @@ i ->r wh) ∗
       ▷ (R2 @@ i ->r r2) ∗
       ▷ i -@A> sacc ∗
       ▷ TX@ i := p_tx ∗
       ▷ wh -{q}>re true
       }}}
   ExecI @ i; E
   {{{ RET (false, ExecI) ;
       PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi ∗
       R0 @@ i ->r (encode_hvc_ret_code Error) ∗
       R1 @@ i ->r wh ∗
       R2 @@ i ->r (encode_hvc_error Denied) ∗
       i -@A> sacc ∗
       TX@ i := p_tx ∗
       wh -{q}>re true
   }}}.
Proof.
Admitted.

End mem_reclaim.
