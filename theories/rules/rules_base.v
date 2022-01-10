From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.algebra Require Import base reg pagetable mem.
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

Lemma update_memory_unsafe_preserve_just_scheduled_vms {σ σ' n} a w:
  just_scheduled_vms n σ (update_memory_unsafe σ' a w) = just_scheduled_vms n σ σ'.
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

Lemma update_memory_unsafe_preserve_scheduled {σ} a w:
  scheduled (update_memory_unsafe σ a w) = scheduled σ.
Proof.
  rewrite /scheduled /machine.scheduler //= /scheduler.
Qed.

(* TODO: we don't necessarily need full acc *)
Lemma not_valid_pc {s} i a :
  (tpa a) ∉ s ->
  {SS{{ ▷ (PC @@ i ->r a) ∗ ▷ i -@A> [s] }}}
  ExecI @ i
  {{{ RET (false, FailI); PC @@ i ->r a ∗ i -@A> [s] }}}.
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
    apply step_exec_fail_invalid_pc.
    rewrite /is_valid_PC Hpc Hcur /=.
    rewrite check_access_page_mem_eq in Hnacc.
    rewrite Hnacc //.
  - iModIntro.
    iIntros (m2 σ2) "? %HstepP".
    iModIntro.
    inversion HstepP; subst.
    + simpl.
      rewrite /gen_vm_interp.
      iFrame.
      rewrite just_scheduled_vms_no_step_empty.
      iSplitR;[done|].
      rewrite andb_false_intro2;auto.
      iApply "Hϕ".
      iFrame.
    + simplify_eq.
      rewrite /is_valid_PC Hpc in H.      
      simpl in H.
      rewrite check_access_page_mem_eq in Hnacc.
      rewrite Hnacc in H.
      inversion H.
    + simplify_eq.
      rewrite /is_valid_PC Hpc in H.
      simpl in H.
      rewrite check_access_page_mem_eq in Hnacc.
      rewrite Hnacc in H.
      inversion H.
Qed.

Lemma not_valid_instr {q s} i a wi :
  decode_instruction wi = None ->
  (tpa a) ∈ s ->
  {SS{{ ▷ (PC @@ i ->r a)
        ∗ ▷ i -@{q}A> [s]
        ∗ ▷ a ->a wi}}}
  ExecI @ i
  {{{ RET (false, FailI);
    PC @@ i ->r a
    ∗ i -@{q}A> [s]
    ∗ a ->a wi
  }}}.
Proof.
  iIntros (Hdecode_none Hin ϕ) "(>Hpc & >Ha & >Hw) Hϕ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (n σ1) "%Hsche Hσ1".
  rewrite /scheduled /= /scheduler /Is_true in Hsche.
  case_match;[|done].
  apply bool_decide_eq_true in Heqb.
  apply fin_to_nat_inj in Heqb.
  rename Heqb into Hcur.
  iModIntro.
  iDestruct "Hσ1" as "( ? & Hmem & Hreg & ? & ? & ? & Haccess & ?)".
  iDestruct (gen_reg_valid1 PC i a Hcur with "Hreg Hpc") as "%Hpc".
  iDestruct (access_agree_check_true (tpa a) i with "Haccess Ha") as "%Hacc";first auto.
  iDestruct (gen_mem_valid with "Hmem Hw") as "%Hlookup_w".
  iSplit.
  - iPureIntro.
    rewrite /reducible.
    exists FailI, σ1.
    rewrite check_access_page_mem_eq in Hacc.
    eapply step_exec_fail_invalid_instr;eauto.
    rewrite /is_valid_PC Hpc Hcur /=.
    rewrite Hacc //.
    rewrite /get_memory Hcur Hacc //.
  - iModIntro.
    iIntros (m2 σ2) "? %HstepP".
    iModIntro.
    inversion HstepP; subst.
    + simplify_eq.
      rewrite /is_valid_PC Hpc in H.
      simpl in H.
      rewrite check_access_page_mem_eq in Hacc.
      rewrite Hacc in H.
      contradiction.
    + simpl. rewrite /gen_vm_interp.
      iFrame.
      rewrite just_scheduled_vms_no_step_empty.
      iSplitR;[done|].
      rewrite andb_false_intro2;auto.
      iApply "Hϕ".
      iFrame.
    + rewrite /get_memory in H1.
      case_match.
      rewrite H0 in Hpc.
      inversion Hpc;subst.
      rewrite Hlookup_w in H1.
      inversion H1;subst w.
      rewrite H2 // in Hdecode_none.
      rewrite check_access_page_mem_eq // in Hacc.
Qed.

End rules_base.
