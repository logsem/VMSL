From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.algebra Require Import base reg pagetable mem mailbox.
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

End rules_base.
