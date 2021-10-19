From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.algebra Require Import base reg mem pagetable.
From HypVeri Require Import machine_extra lifting rules.rules_base.
From HypVeri.lang Require Import lang_extra reg_extra.

Section nop.

Context `{hypparams: HypervisorParameters}.
Context `{vmG: !gen_VMG Σ}.

Lemma nop {E i w1 q s} a :
  decode_instruction w1 = Some Nop ->
  to_pid_aligned a ∈ s ->
  {SS{{ ▷ (PC @@ i ->r a)
          ∗ ▷ (a ->a w1) ∗ ▷ (A@i:={q}[s])}}}
    ExecI @ i ; E
  {{{ RET ExecI;  PC @@ i ->r (a ^+ 1)%f
                   ∗ a ->a w1
                   ∗ A@i:={q}[s] }}}.
Proof.
  iIntros (Hdecode Hin ϕ) "(>Hpc & >Hapc & >Hacc) Hϕ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [ Hcur ]; clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(H1 & Hmem & Hreg & ? & ? & ? & ? & Haccess & H2)".
  pose proof (decode_instruction_valid w1 _ Hdecode) as Hvalidinstr.
  inversion Hvalidinstr as [| | | | | | | | | | |].
  (* valid regs *)
  iDestruct ((gen_reg_valid1 PC i a Hcur) with "Hreg Hpc") as "%HPC".
  (* valid pt *)
  iDestruct (gen_access_valid_addr_Set a with "Haccess Hacc") as %Hacc; eauto.
  (* valid mem *)
  iDestruct (gen_mem_valid a w1 with "Hmem Hapc") as "%Hmem".
  iSplit.
  - (* reducible *)
    iPureIntro.
    eapply (reducible_normal i _ a w1); eauto.
  - (* step *)
    iModIntro.
    iIntros (m2 σ2) "%HstepP".
    eapply (step_ExecI_normal i _ a w1) in HstepP;eauto.
    remember (exec _ σ1) as c2 eqn:Heqc2.
    rewrite /exec /nop /update_incr_PC in Heqc2.
    destruct HstepP; subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    (* unchanged part *)
    rewrite_reg_pc.
    rewrite Hcur. iFrame.
    (* updated part *)
    rewrite -> (update_offset_PC_update_PC1 _ i a 1); eauto.
    + iDestruct ((gen_reg_update1_global PC i a (a ^+ 1)%f) with "Hreg Hpc") as ">[Hσ Hreg]"; eauto.
      iModIntro.
      iFrame "Hσ".
      iApply "Hϕ".
      iFrame "Hapc Hacc Hreg".
    + solve_reg_lookup.
Qed.

End nop.
