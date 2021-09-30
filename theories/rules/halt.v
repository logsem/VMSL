From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base.
From HypVeri.algebra Require Import base reg mem pagetable.
From HypVeri.lang Require Import lang_extra reg_extra.

Section halt.

Context `{hypparams: HypervisorParameters}.
Context `{vmG: !gen_VMG Σ}.
  
Lemma halt {E instr i w1 q p s} ai :
  instr = Halt ->
  decode_instruction w1 = Some(instr) ->
  addr_in_page ai p ->
  p ∈ s ->
  {SS{{▷ (PC @@ i ->r ai)
          ∗ ▷ (ai ->a w1)
          ∗ ▷ (A@i:={q}[s])}}}
    ExecI @ i ;E
 {{{ RET HaltI;  PC @@ i ->r (ai ^+ 1)%f
                  ∗ ai ->a w1
                  ∗ A@i:={q}[s] }}}.
Proof.
  iIntros (Hinstr Hdecode Hin HpIn ϕ) "(>Hpc & >Hapc & >Hacc) Hϕ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [ Hcur ]; clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(Htok & Hmem & Hreg & Htx & Hrx1 & Hrx2 & Hown & Haccess & Hrest)".
  (* valid regs *)
  iDestruct ((gen_reg_valid1 PC i ai Hcur ) with "Hreg Hpc") as "%HPC";eauto.
  (* valid pt *)
  iDestruct ((gen_access_valid_addr_Set ai p s) with "Haccess Hacc") as %Hacc;eauto.
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
    rewrite /exec Hinstr /halt /update_incr_PC in Heqc2;eauto.
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    (* unchanged part *)
    rewrite_reg_pc.
    rewrite_reg_global.
    rewrite Hcur.
    iFrame "Htok Hmem Htx Hrx1 Hrx2 Hown Haccess Hrest".
    (* updated part *)
    iDestruct ((gen_reg_update1_global PC i ai (ai ^+ 1)%f) with "Hreg Hpc") as ">[Hreg Hpc]";eauto.
    rewrite -> (update_offset_PC_update_PC1 _ i ai 1);eauto.
    iModIntro.
    iFrame "Hreg".
    iApply "Hϕ".
    by iFrame "Hpc Hapc Hacc".
    apply (get_reg_gmap_get_reg_Some _ _ _ i) in HPC;eauto.
Qed.
End halt.
