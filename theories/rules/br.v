From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base.
From HypVeri.algebra Require Import base reg mem pagetable.
From HypVeri.lang Require Import lang_extra reg_extra.

Section br.

Context `{vmG: !gen_VMG Σ}.
  
Lemma br {instr i w1 w2 q} ai  ra :
  instr = Br ra ->
  decode_instruction w1 = Some(instr) ->
  addr_in_page ai (to_pid_aligned ai) ->
  {SS{{  ▷ (PC @@ i ->r ai) ∗ ▷ (ai ->a w1) ∗ ▷ (ra @@ i ->r w2) ∗ ▷ (A@i:={q} (to_pid_aligned ai))}}} ExecI @ i
                                  {{{ RET ExecI;  PC @@ i ->r  w2  ∗ ai ->a w1 ∗ ra @@ i ->r w2
                       ∗ A@i:={q} (to_pid_aligned ai) }}}.
Proof.
  iIntros (Hinstr Hdecode HIn ϕ) "( >Hpc & >Hapc & >Hra & >Hacc) Hϕ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [ Hcur ]; clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(Htok & Hmem & Hreg & Htx & Hrxagree & Hrxoption & Howned & Haccess & Hres)".
  pose proof (decode_instruction_valid w1 instr Hdecode) as Hvalidinstr.
  rewrite Hinstr in Hvalidinstr.
  inversion Hvalidinstr as [ | | | | | | | | |src Hvalidra] .
  subst src .
  inversion Hvalidra as [ HneqPCa HneqNZa ].
  (* valid regs *)
  iDestruct ((gen_reg_valid2 i PC ai ra w2 Hcur) with "Hreg Hpc Hra") as "[%HPC %Hra]";eauto.
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
    rewrite /exec Hinstr (br_ExecI σ1 ra w2 ) /update_incr_PC /update_reg in Heqc2;eauto.
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    (* unchanged part *)
    rewrite_reg_pc.
    rewrite_reg_global.
    rewrite Hcur.
    iFrame "Htok Hmem Htx Hrxagree Hrxoption Howned Haccess Hres".
    (* updated part *)
    rewrite ->update_reg_global_update_reg;[|solve_reg_lookup].
    iDestruct ((gen_reg_update1_global PC i ai w2 ) with "Hreg Hpc") as ">[Hreg Hpc]";eauto.
    iModIntro.
    iFrame "Hreg".
    iApply "Hϕ".
    by iFrame "Hapc Hra Hacc Hpc".
Qed.
End br.
