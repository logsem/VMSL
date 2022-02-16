From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base.
From HypVeri.algebra Require Import base reg mem pagetable mailbox.
From HypVeri.lang Require Import lang_extra.

Section fail.

Context `{hypparams:HypervisorParameters}.
Context `{vmG: !gen_VMG Σ}.
  
Lemma fail {i w1 q E s p} ai :
  decode_instruction w1 = Some(Fail) ->
  tpa ai ∈ s ->
  (tpa ai) ≠ p ->
  {SS{{ ▷ (PC @@ i ->r ai)
        ∗ ▷ (ai ->a w1)
        ∗ ▷ (i -@{ q }A> s)
        ∗ ▷ (TX@ i := p) }}} ExecI @ i; E
        {{{ RET (false, FailI); PC @@ i ->r ai  ∗ ai ->a w1
                                               ∗ (i -@{ q }A> s)
                                               ∗ TX@ i := p
                                             }}}.
Proof.
  iIntros (Hdecode Hin Hneq ϕ) "(>Hpc & >Hapc & >Hacc & >HTX) Hϕ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (n σ1) "%Hsche Hσ".  
  rewrite /scheduled in Hsche.
  simpl in Hsche.
  rewrite /scheduler in Hsche.
  apply bool_decide_unpack in Hsche as Hcur.
  clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(#Hneq & Hmem & Hreg & Hmb & Hrx & Hown & Haccess & Hrest)".
  (* valid regs *)
  iDestruct ((gen_reg_valid1 PC i ai Hcur ) with "Hreg Hpc") as "%HPC";eauto.
  (* valid pt *)
  iDestruct (access_agree_check_true (tpa ai) i with "Haccess Hacc") as "%Hai"; first set_solver.
  (* valid mem *)
  iDestruct (gen_mem_valid ai w1  with "Hmem Hapc") as %Hmem.
  iDestruct (mb_valid_tx i p with "Hmb HTX") as %Htx.
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal i Fail ai w1);eauto.
    rewrite Htx.
    done.
  - (* step *)
    iModIntro.
    iIntros (m2 σ2) "[%P PAuth] %HstepP".
    apply (step_ExecI_normal i Fail ai w1 ) in HstepP;eauto.
    remember (exec Fail σ1) as c2 eqn:Heqc2.
    rewrite /exec /fail /update_incr_PC in Heqc2;eauto.
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    iFrame "Hreg Hneq Hmem Hrx Hown Hmb Haccess Hrest".
    iSplitL "PAuth".
    by iExists P.
    rewrite just_scheduled_vms_no_step_empty.
    rewrite scheduled_true /=;last done.
    iModIntro.
    iSplit; first done.
    iApply ("Hϕ" with "[Hpc Hapc Hacc HTX]").
    iFrame.
    by rewrite Htx.
Qed.
End fail.
