From machine_program_logic.program_logic Require Import machine weakestpre.
From HypVeri Require Import RAs rule_misc lifting rules.rules_base.
From iris.proofmode Require Import tactics.
Require Import iris.base_logic.lib.ghost_map.
Require Import stdpp.fin.

Lemma br {instr i w1 w2 q} ai  ra :
  instr = Br ra ->
  decode_instruction w1 = Some(instr) ->
  <<i>> ∗ PC @@ i ->r ai ∗ ai ->a w1 ∗ ra @@ i ->r w2 ∗ A@i:={q} (mm_translation ai)
    ⊢ SSWP ExecI @ i {{ (λ m, ⌜m = ExecI ⌝ ∗ <<i>> ∗ PC @@ i ->r  w2  ∗ ai ->a w1 ∗ ra @@ i ->r w2
                       ∗ A@i:={q} (mm_translation ai) ) }}%I.
Proof.
  iIntros (Hinstr Hdecode) "(? & Hpc & Hapc & Hra & Hacc)".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [ Hcur ]; clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(? & Hmem & Hreg & ? & ? & ? & Haccess & ?)".
  pose proof (decode_instruction_valid w1 instr Hdecode) as Hvalidinstr.
  rewrite Hinstr in Hvalidinstr.
  inversion Hvalidinstr as [ | | | | | | |src Hvalidra] .
  subst src .
  inversion Hvalidra as [ HneqPCa HneqNZa ].
  (* valid regs *)
  iDestruct ((gen_reg_valid2 σ1 i PC ai ra w2 Hcur HneqPCa) with "Hreg Hpc Hra") as "[%HPC %Hra]";eauto.
  (* valid pt *)
  iDestruct ((gen_access_valid_addr σ1 i q ai) with "Haccess Hacc") as %Hacc.
  (* valid mem *)
  iDestruct (gen_mem_valid σ1 ai w1  with "Hmem Hapc") as %Hmem.
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal i instr ai w1);eauto.
  - (* step *)
    iModIntro.
    iIntros (m2 σ2) "%HstepP".
    apply (step_ExecI_normal i instr ai w1 ) in HstepP;eauto.
    remember (exec instr σ1) as c2 eqn:Heqc2.
    rewrite /exec Hinstr (br_ExecI σ1 ra w2 ) /update_incr_PC /update_reg in Heqc2;eauto.
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    (* unchanged part *)
    rewrite_reg_all.
    rewrite Hcur.
    iFrame.
    (* updated part *)
    rewrite update_reg_global_update_reg;[|solve_reg_lookup].
    iDestruct ((gen_reg_update1_global σ1 PC i ai w2 ) with "Hreg Hpc") as ">[Hreg Hpc]";eauto.
    by iFrame.
Qed.
