From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.algebra Require Import base reg pagetable mem mailbox base_extra.
From HypVeri.lang Require Import lang_extra reg_extra.
Require Import stdpp.fin.

Section rules_base.

Context `{hypconst: HypervisorConstants}.
Context `{hypparams: !HypervisorParameters}.
Context `{vmG: !gen_VMG Σ}.

Implicit Type a : Addr.
Implicit Type i : VMID.
Implicit Type ra rb : reg_name.
Implicit Type w: Word.
Implicit Type q : Qp.
Implicit Type σ : state.

Lemma just_scheduled_no_step_false σ (i:nat) : just_scheduled σ σ i = false.
Proof.
  rewrite /just_scheduled /scheduled /= /scheduler.
  apply andb_negb_l.
Qed.

Lemma just_scheduled_vms_no_step_empty σ n: just_scheduled_vms n σ σ = [].
Proof.
  unfold just_scheduled_vms.
  induction (seq 0 n);[done|].
  rewrite filter_cons_False.
  apply IHl.
  rewrite just_scheduled_no_step_false //.
Qed.

Lemma update_offset_PC_preserve_just_scheduled_vms {σ σ' n} o:
  just_scheduled_vms n σ (update_offset_PC σ' o) = just_scheduled_vms n σ σ'.
Proof.
  unfold just_scheduled_vms, just_scheduled.
  rewrite /scheduled /machine.scheduler //= /scheduler.
  rewrite p_upd_pc_current_vm.
  done.
Qed.

Lemma update_reg_global_preserve_just_scheduled_vms {σ σ' n} i r w:
  just_scheduled_vms n σ (update_reg_global σ' i r w) = just_scheduled_vms n σ σ'.
Proof.
  unfold just_scheduled_vms, just_scheduled.
  rewrite /scheduled /machine.scheduler //= /scheduler.
Qed.

Lemma update_memory_preserve_just_scheduled_vms {σ σ' n} a w:
  just_scheduled_vms n σ (update_memory σ' a w) = just_scheduled_vms n σ σ'.
Proof.
  unfold just_scheduled_vms, just_scheduled.
  rewrite /scheduled /machine.scheduler //= /scheduler.
Qed.

Lemma scheduled_true {σ: state} i:
  get_current_vm σ = i ->  (scheduled σ i) = true.
Proof.
  intros.
  rewrite /scheduled /machine.scheduler //= /scheduler.
  case_bool_decide.
  done.
  rewrite H in H0.
  done.
Qed.

Lemma update_offset_PC_preserve_scheduled {σ} o:
  scheduled (update_offset_PC σ o) = scheduled σ.
Proof.
  rewrite /scheduled /machine.scheduler //= /scheduler.
  rewrite p_upd_pc_current_vm //.
Qed.

Lemma update_reg_global_preserve_scheduled {σ} i r w:
  scheduled (update_reg_global σ i r w) = scheduled σ.
Proof.
  rewrite /scheduled /machine.scheduler //= /scheduler.
Qed.

Lemma update_memory_preserve_scheduled {σ} a w:
  scheduled (update_memory σ a w) = scheduled σ.
Proof.
  rewrite /scheduled /machine.scheduler //= /scheduler.
Qed.

Lemma invalid_pc_not_accessible {s} i a :
  (tpa a) ∉ s ->
  {SS{{ ▷ (PC @@ i ->r a) ∗ ▷ i -@A> s }}}
  ExecI @ i
  {{{ RET (false, FailI); PC @@ i ->r a ∗ i -@A> s}}}.
Proof.
  iIntros (Hmm ϕ) "(>Hpc & >Ha) Hϕ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (n σ1) "%Hsche Hσ1".
  rewrite /scheduled /= /scheduler /Is_true in Hsche.
  case_match;[|done]. 
  apply bool_decide_eq_true in Heqb.
  apply fin_to_nat_inj in Heqb.
  rename Heqb into Hcur.
  iModIntro.
  iDestruct "Hσ1" as "( ? & ? & Hreg & ? & ? & ? & Haccess & ?)".
  iDestruct (gen_reg_valid1 PC i a Hcur with "Hreg Hpc") as "%Hpc".
  iDestruct (access_agree_check_false (to_pid_aligned a) s Hmm with "Haccess Ha") as "%Hnacc".
  iSplit.
  - iPureIntro.
    rewrite /reducible.
    exists FailI, σ1.
    eapply step_exec_fail_invalid_pc.
    exact Hpc.
    rewrite /read_memory /check_read_access_addr /check_read_access_page.
    rewrite Hcur Hnacc.
    rewrite andb_false_l //.
  - iModIntro.
    iIntros (m2 σ2) "? %HstepP".
    iModIntro.
    inversion HstepP; simplify_eq.
    + simpl.
      rewrite /gen_vm_interp.
      iFrame.
      rewrite just_scheduled_vms_no_step_empty.
      iSplitR;[done|].
      rewrite andb_false_intro2;auto.
      iApply "Hϕ".
      iFrame.
    + simplify_eq.
      rewrite /read_memory /check_read_access_addr /check_read_access_page in H0.
      rewrite Hnacc andb_false_l // in H0.
    + simplify_eq.
      rewrite /read_memory /check_read_access_addr /check_read_access_page in H0.
      rewrite Hnacc andb_false_l // in H0.
Qed.

Lemma invalid_pc_in_tx {p_tx} i a :
  (tpa a) = p_tx ->
  {SS{{ ▷ (PC @@ i ->r a) ∗ ▷ TX@i := p_tx }}}
  ExecI @ i
  {{{ RET (false, FailI); PC @@ i ->r a ∗ TX@i := p_tx}}}.
Proof.
  iIntros (Hmm ϕ) "(>Hpc & >Htx) Hϕ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (n σ1) "%Hsche Hσ1".
  rewrite /scheduled /= /scheduler /Is_true in Hsche.
  case_match;[|done].
  apply bool_decide_eq_true in Heqb.
  apply fin_to_nat_inj in Heqb.
  rename Heqb into Hcur.
  iModIntro.
  iDestruct "Hσ1" as "( ? & ? & Hreg & Hmb & ? & ? & Haccess & ?)".
  iDestruct (gen_reg_valid1 PC i a Hcur with "Hreg Hpc") as "%Hpc".
  iDestruct (mb_valid_tx i p_tx with "Hmb Htx") as "%Heq_tx".
  iSplit.
  - iPureIntro.
    rewrite /reducible.
    exists FailI, σ1.
    eapply step_exec_fail_invalid_pc.
    exact Hpc.
    rewrite /read_memory /check_read_access_addr /check_read_access_page.
    rewrite Hcur Hmm.
    case_bool_decide;first done.
    rewrite andb_false_r //.
  - iModIntro.
    iIntros (m2 σ2) "? %HstepP".
    iModIntro.
    inversion HstepP; simplify_eq.
    + simpl.
      rewrite /gen_vm_interp.
      iFrame.
      rewrite just_scheduled_vms_no_step_empty.
      iSplitR;[done|].
      rewrite andb_false_intro2;auto.
      iApply "Hϕ".
      iFrame.
    + simplify_eq.
      rewrite /read_memory /check_read_access_addr /check_read_access_page in H0.
      case_bool_decide;first done.
      rewrite andb_false_r // in H0.
    + simplify_eq.
      rewrite /read_memory /check_read_access_addr /check_read_access_page in H0.
      case_bool_decide;first done.
      rewrite andb_false_r // in H0.
Qed.


Lemma not_valid_instr {q s p_tx} i a wi :
  decode_instruction wi = None ->
  (tpa a) ∈ s ->
  (tpa a) ≠ p_tx ->
  {SS{{ ▷ (PC @@ i ->r a)
        ∗ ▷ i -@{q}A> s
        ∗ ▷ TX@i := p_tx
        ∗ ▷ a ->a wi}}}
  ExecI @ i
  {{{ RET (false, FailI);
    PC @@ i ->r a
    ∗ i -@{q}A> s
    ∗ TX@i := p_tx
    ∗ a ->a wi
  }}}.
Proof.
  iIntros (Hdecode_none Hin Hneq ϕ) "(>Hpc & >Ha & >tx & >Hw) Hϕ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (n σ1) "%Hsche Hσ1".
  rewrite /scheduled /= /scheduler /Is_true in Hsche.
  case_match;[|done].
  apply bool_decide_eq_true in Heqb.
  apply fin_to_nat_inj in Heqb.
  rename Heqb into Hcur.
  iModIntro.
  iDestruct "Hσ1" as "( ? & Hmem & Hreg & Hmb & ? & ? & Haccess & ?)".
  iDestruct (gen_reg_valid1 PC i a Hcur with "Hreg Hpc") as "%Hpc".
  iDestruct (access_agree_check_true (tpa a) i with "Haccess Ha") as "%Hacc";first auto.
  iDestruct (gen_mem_valid with "Hmem Hw") as "%Hlookup_w".
  iDestruct (mb_valid_tx i p_tx with "Hmb tx") as "%Heq_tx".
  iSplit.
  - iPureIntro.
    rewrite /reducible.
    exists FailI, σ1.
    eapply step_exec_fail_invalid_instr;eauto.
    rewrite /read_memory /check_read_access_addr /check_read_access_page Hcur Hacc.
    rewrite andb_true_l.
    rewrite -Heq_tx in Hneq.
    case_bool_decide; done.
  - iModIntro.
    iIntros (m2 σ2) "? %HstepP".
    iModIntro.
    inversion HstepP; subst.
    + simplify_eq.
      rewrite /read_memory /check_read_access_addr /check_read_access_page Hacc andb_true_l in H0.
      case_bool_decide.
      rewrite H0 // in Hlookup_w.
      rewrite H // in Hneq.
    + simpl. rewrite /gen_vm_interp.
      iFrame.
      rewrite just_scheduled_vms_no_step_empty.
      iSplitR;[done|].
      rewrite andb_false_intro2;auto.
      iApply "Hϕ".
      iFrame.
    + simplify_eq.
      rewrite /read_memory /check_read_access_addr /check_read_access_page Hacc andb_true_l in H0.
      case_bool_decide.
      rewrite H0 in Hlookup_w.
      inversion Hlookup_w.
      subst w.
      rewrite H1 //in Hdecode_none.
      rewrite H // in Hneq.
Qed.

Lemma hvc_error_update {E n i ai r0 r2} {σ1: state} err :
  σ1.1.1.2 = i ->
  get_reg σ1 PC = Some ai ->
  get_reg σ1 R0 = Some r0 ->
  get_reg σ1 R2 = Some r2 ->
  PC @@ i ->r ai -∗
  R0 @@ i ->r r0 -∗
  R2 @@ i ->r r2 -∗
  gen_vm_interp n σ1 ={E}=∗ (gen_vm_interp n (update_incr_PC (update_reg (update_reg σ1 R0 (encode_hvc_ret_code Error)) R2 (encode_hvc_error err))) ∗
    ([∗ list] vmid ∈ just_scheduled_vms n σ1
                       (update_incr_PC (update_reg (update_reg σ1 R0 (encode_hvc_ret_code Error)) R2 (encode_hvc_error err))),
     VMProp_holds vmid (1 / 2))) ∗
                 PC @@ i ->r (ai ^+ 1)%f ∗
                 R0 @@ i ->r (encode_hvc_ret_code Error) ∗
                 R2 @@ i ->r (encode_hvc_error err).
Proof.
  iIntros (Heq_cur Hlookup_PC Hlookup_R0 Hlookup_R2) "PC R0 R2 (Hnum & mem & regs & mb & rx_state & pgt_owned & pgt_acc & pgt_excl &
                            trans & hpool & retri & %Hwf & %Hdisj & %Hconsis)".
  rewrite /gen_vm_interp.
  (* unchanged part *)
  rewrite (preserve_get_mb_gmap σ1).
  rewrite (preserve_get_rx_gmap σ1).
  all: try rewrite p_upd_pc_mb //.
  rewrite p_upd_pc_mem 2!p_upd_reg_mem.
  rewrite (preserve_get_own_gmap σ1).
  2: rewrite p_upd_pc_pgt 2!p_upd_reg_pgt //.
  rewrite (preserve_get_access_gmap σ1).
  2: rewrite p_upd_pc_pgt 2!p_upd_reg_pgt //.
  rewrite (preserve_get_excl_gmap σ1).
  2: rewrite p_upd_pc_pgt 2!p_upd_reg_pgt //.
  rewrite (preserve_get_trans_gmap σ1).
  2: rewrite p_upd_pc_trans 2!p_upd_reg_trans //.
  rewrite (preserve_get_retri_gmap σ1).
  2: rewrite p_upd_pc_trans 2!p_upd_reg_trans //.
  rewrite (preserve_get_hpool_gset σ1).
  2: rewrite p_upd_pc_trans 2!p_upd_reg_trans //.
  iFrame "Hnum mem rx_state mb pgt_owned pgt_acc pgt_excl trans retri hpool".
  (* upd regs *)
  rewrite (u_upd_pc_regs _ i ai);auto.
  2: { rewrite 2!u_upd_reg_regs.
       rewrite lookup_insert_ne;auto.  rewrite lookup_insert_ne;auto.  solve_reg_lookup.
  }
  rewrite u_upd_reg_regs p_upd_reg_current_vm Heq_cur.
  rewrite u_upd_reg_regs Heq_cur.
  iDestruct ((gen_reg_update3_global PC i (ai ^+ 1)%f R2 i (encode_hvc_error err) R0 i (encode_hvc_ret_code Error)) with "regs PC R2 R0")
    as ">[$ [PC [R2 R0]]]".
  (* inv_trans_wellformed *)
  rewrite (preserve_inv_trans_wellformed σ1).
  2: rewrite p_upd_pc_trans 2!p_upd_reg_trans //.
  (* inv_trans_pgt_consistent *)
  rewrite (preserve_inv_trans_pgt_consistent σ1).
  2: rewrite p_upd_pc_trans 2!p_upd_reg_trans //.
  2: rewrite p_upd_pc_pgt 2!p_upd_reg_pgt //.
  (* inv_trans_ps_disj *)
  rewrite (preserve_inv_trans_ps_disj σ1).
  2: rewrite p_upd_pc_trans p_upd_reg_trans //.
  iModIntro.
  iFrame.
  iSplitR. iPureIntro. auto.
  (* just_scheduled *)
  rewrite /just_scheduled_vms /just_scheduled.
  rewrite /scheduled /machine.scheduler /= /scheduler.
  rewrite p_upd_pc_current_vm 2!p_upd_reg_current_vm Heq_cur.
  set fl := (filter _ _).
  assert (fl = []) as ->.
  {
    rewrite /fl.
    induction n.
    - simpl.
      rewrite filter_nil //=.
    - rewrite seq_S.
      rewrite list.filter_app.
      rewrite IHn.
      simpl.
      rewrite filter_cons_False /=.
      rewrite filter_nil. auto.
      rewrite andb_negb_l.
      done.
  }
  by iSimpl.
Qed.

Lemma invalid_hvc_func {q s r0 r2 p_tx} i a wi :
  (tpa a) ≠ p_tx ->
  (tpa a) ∈ s ->
  decode_instruction wi = Some Hvc ->
  decode_hvc_func r0 = None ->
  {SS{{ ▷ (PC @@ i ->r a) ∗ ▷ a ->a wi
        ∗ ▷ i -@{q}A> s
        ∗ ▷ TX@i := p_tx
        ∗ ▷ (R0 @@ i ->r r0)
        ∗ ▷ (R2 @@ i ->r r2)
        }}}
  ExecI @ i
  {{{ RET (false, ExecI);
    PC @@ i ->r (a ^+ 1)%f
    ∗ a ->a wi
    ∗ i -@{q}A> s
    ∗ TX@i := p_tx
    ∗ R0 @@ i ->r encode_hvc_ret_code Error
    ∗ R2 @@ i ->r encode_hvc_error InvParam
  }}}.
Proof.
Admitted.



End rules_base.
