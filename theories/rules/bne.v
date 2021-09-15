From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base.
From HypVeri Require Import base mem reg pagetable.
From HypVeri.lang Require Import lang_extra reg_extra.

Section bne.

Context `{vmG: !gen_VMG Σ}.
  
Lemma bne {instr i w1 w2 w3 q} ai ra :
  instr = Bne ra ->
  decode_instruction w1 = Some(instr) ->
  addr_in_page ai (to_pid_aligned ai) ->
  {SS{{ ▷ (PC @@ i ->r ai) ∗ ▷ (ai ->a w1) ∗ ▷ (ra @@ i ->r w2) ∗ ▷ (A@i:={q} (to_pid_aligned ai)%f) ∗ ▷ (NZ @@ i ->r w3)}}} ExecI @ i
                                  {{{ RET ExecI; PC @@ i ->r (if (w3 =? W1)%f then  (ai ^+ 1)%f else w2 ) ∗ ai ->a w1 ∗ ra @@ i ->r w2
                       ∗ A@i:={q} (to_pid_aligned ai) ∗ NZ @@ i ->r w3 }}}.
Proof.
  iIntros (Hinstr Hdecode HIn ϕ) "(>Hpc & >Hapc & >Hra & >Hacc & >Hnz ) Hϕ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [ Hcur ]; clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(Htok & Hmem & Hreg & Htx & Hrxagree & Hrxoption & Howned & Haccess & Hrest)".
  pose proof (decode_instruction_valid w1 instr Hdecode) as Hvalidinstr.
  rewrite Hinstr in Hvalidinstr.
  inversion Hvalidinstr as [ | | | | | | | | src Hvalidra|] .
  subst src .
  inversion Hvalidra as [ HneqPCa HneqNZa ].
  (* valid regs *)
  iDestruct ((gen_reg_valid3 i PC ai ra w2 NZ w3 Hcur) with "Hreg Hpc Hra Hnz") as "[%HPC [%Hra %HNZ]]";eauto.
  (* valid pt *)
  iDestruct ((gen_access_valid_addr ai) with "Haccess Hacc") as %Hacc;eauto.
  (* valid mem *)
  iDestruct (gen_mem_valid ai w1  with "Hmem Hapc") as %Hmem.
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal i instr ai w1);eauto.
  - (* step *)
    iModIntro.
    iIntros (m2 σ2) "%HstepP".
    apply (step_ExecI_normal i instr ai w1 ) in HstepP;eauto.
    remember (exec instr σ1) as c2 eqn:Heqc2.
    rewrite /exec Hinstr (bne_ExecI σ1 w3 ra w2 HneqPCa HneqNZa) /update_incr_PC /update_reg in Heqc2;eauto.
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    (* branch here*)
    destruct  (w3 =? W1)%f;
    (* unchanged part *)
    [rewrite_reg_pc| rewrite_reg_global];
    rewrite Hcur;
    iFrame "Htok Htx Hrxagree Hrxoption Howned Hrest".
    (* updated part *)
    + rewrite -> (update_offset_PC_update_PC1 _ i ai 1);eauto.
      iDestruct ((gen_reg_update1_global PC i ai (ai ^+ 1)%f) with "Hreg Hpc") as ">[Hreg Hpc]";eauto.
      iModIntro.
      iFrame "Hmem Hreg Haccess".
      iApply "Hϕ".
      by iFrame "Hpc Hra Hacc Hnz".
      apply (get_reg_gmap_get_reg_Some _ _ _ i) in HPC;eauto.
    + rewrite ->update_reg_global_update_reg; [|solve_reg_lookup].
      iDestruct ((gen_reg_update1_global PC i ai w2 ) with "Hreg Hpc") as ">[Hreg Hpc]";eauto.
      iModIntro.
      iFrame "Hmem Haccess Hreg".
      iApply "Hϕ".
      by iFrame "Hapc Hra Hacc Hnz Hpc".
Qed.

End bne.
