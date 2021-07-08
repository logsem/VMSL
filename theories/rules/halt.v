From machine_program_logic.program_logic Require Import machine weakestpre.
From HypVeri Require Import RAs rule_misc lifting rules.rules_base.
From iris.proofmode Require Import tactics.
Require Import iris.base_logic.lib.ghost_map.
Require Import stdpp.fin.

Lemma halt {instr i w1 q} ai :
  instr = Halt ->
  decode_instruction w1 = Some(instr) ->
  <<i>> ∗ PC @@ i ->r ai ∗ ai ->a w1 ∗ A@i:={q} (to_pid_aligned ai)
    ⊢ SSWP ExecI @ i {{ (λ m, ⌜m = HaltI ⌝ ∗ <<i>> ∗ PC @@ i ->r (ai ^+ 1)%f  ∗ ai ->a w1
                       ∗ A@i:={q} (to_pid_aligned ai) ) }}%I.
Proof.
  iIntros (Hinstr Hdecode) "(? & Hpc & Hapc & Hacc)".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [ Hcur ]; clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(? & Hmem & Hreg & ? & ? & ? & Haccess & ?)".
  (* valid regs *)
  iDestruct ((gen_reg_valid1 σ1 PC i ai Hcur ) with "Hreg Hpc") as "%HPC";eauto.
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
    rewrite /exec Hinstr /halt /update_incr_PC in Heqc2;eauto.
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    (* unchanged part *)
    rewrite_reg_all.
    rewrite Hcur.
    iFrame.
    (* updated part *)
    iDestruct ((gen_reg_update1_global σ1 PC i ai (ai ^+ 1)%f) with "Hreg Hpc") as ">[Hreg Hpc]";eauto.
    rewrite -> (update_offset_PC_update_PC1 _ i ai 1);eauto.
    by iFrame.
    apply (get_reg_gmap_get_reg_Some _ _ _ i) in HPC;eauto.
Qed.
