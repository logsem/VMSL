From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.algebra Require Import base reg pagetable.
From HypVeri Require Import lifting.
From HypVeri.lang Require Import lang_extra.
Require Import stdpp.fin.

Global Instance hyp_irisG `{HypervisorParameters} `{!gen_VMG Σ} :
  irisG hyp_machine Σ:=
  {
  iris_invG := gen_invG;
  irisG_saved_prop := gen_saved_propG;
  irisG_prop_name := gen_prop_nameG;
  irisG_name_map := gen_name_mapG;
  irisG_name_map_name := gen_name_map_name;
  state_interp :=gen_vm_interp
  }.

Section rules_base.

Context `{hypconst: HypervisorConstants}.
Context `{hypparams: !HypervisorParameters}.
Context `{vmG: !gen_VMG Σ}.

Implicit Type a : Addr.
Implicit Type i : VMID.
Implicit Type ra rb : reg_name.
Implicit Type w: Word.
Implicit Type q : Qp.


(* why cannot coq figure out hyp_machine itself? *)
Lemma just_scheduled_no_step_false{M} σ (i:nat) : @just_scheduled M σ σ i = false.
Proof.
  rewrite /just_scheduled /scheduled /= /scheduler.
  apply andb_negb_l.
Qed.

Lemma just_scheduled_vms_no_step_empty{M} σ n: @just_scheduled_vms M n σ σ = [].
Proof.
  unfold just_scheduled_vms.
  induction (seq 0 n);[done|].
  rewrite filter_cons_False.
  apply IHl.
  rewrite just_scheduled_no_step_false //.
Qed.

Lemma not_valid_pc {q s} i a :
  i ∉ s ->
  {SS{{ ▷ (PC @@ i ->r a) ∗ ▷ (to_pid_aligned a) -@{1}A> [s] }}}
  ExecI @ i
  {{{ RET (false, FailI); PC @@ i ->r a ∗ (to_pid_aligned a) -@{1}A> [s] }}}.
Proof.
  simpl.
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
  iDestruct (access_agree_check_noaccess (to_pid_aligned a) s Hmm with "Haccess Ha") as "%Hnacc".
  iSplit.
  - iPureIntro.
    rewrite /reducible.
    exists FailI, σ1.
    apply step_exec_fail.
    rewrite /is_valid_PC Hpc Hcur.
    simpl.
    rewrite check_access_page_mem_eq in Hnacc.
    rewrite Hnacc.
    done.
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
Qed.

End rules_base.
