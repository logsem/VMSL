From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base.
From HypVeri.algebra Require Import base mem reg pagetable.
From HypVeri.lang Require Import lang_extra reg_extra.

Section cmp.

Context `{hypparams: HypervisorParameters}.
Context `{vmG: !gen_VMG Σ}.
  
Lemma cmp_word {i w1 w2 w3 w4 q sacc} ai ra :
  decode_instruction w1 = Some(Cmp ra (inl w2)) ->
  to_pid_aligned ai ∈ sacc ->
  {SS{{ ▷ (PC @@ i ->r ai) ∗ ▷ (ai ->a w1) ∗
        ▷ (ra @@ i ->r w3) ∗ ▷ (A@i:={q}[sacc]) ∗ ▷ (NZ @@ i ->r w4)}}}
    ExecI @ i
    {{{ RET ExecI; PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a w1 ∗ ra @@ i ->r w3 ∗
        A@i:={q}[sacc] ∗ NZ @@ i ->r (if (w3 <? (of_imm w2))%f then W2 else if ((of_imm w2) <? w3)%f then W0 else W1) }}}.
Proof.
  iIntros (Hdecode Hin ϕ) "(>Hpc & >Hapc & >Hra & >Hacc & >Hnz ) Hϕ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  set (instr:= Cmp ra (inl w2)).
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [ Hcur ]; clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(Htok & Hmem & Hreg & Htx & Hrxagree & Hrxoption & Howned & Haccess & Hrest)".
  pose proof (decode_instruction_valid w1 instr Hdecode) as Hvalidinstr.
  inversion Hvalidinstr as [ | | | | src dst Hvalidra | | | | | |] .
  subst src dst.
  inversion Hvalidra as [ HneqPCa HneqNZa ].
  (* valid regs *)
  iDestruct ((gen_reg_valid3 i PC ai ra w3 NZ w4 Hcur) with "Hreg Hpc Hra Hnz") as "[%HPC [%Hra %HNZ]]";eauto.
  (* valid pt *)
  iDestruct ((gen_access_valid_addr_Set ai) with "Haccess Hacc") as %Hacc;eauto.
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
    rewrite /exec /instr (cmp_word_ExecI σ1 ra w3 w2 HneqPCa HneqNZa Hra) /update_incr_PC /update_reg in Heqc2.
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    (* unchanged part *)
    rewrite_reg_pc.
    rewrite_reg_global.
    rewrite Hcur.
    iFrame "Htok Htx Hrxagree Hrxoption Howned Hrest".
    (* updated part *)
    rewrite -> (update_offset_PC_update_PC1 _ i ai 1);eauto.
    rewrite update_reg_global_update_reg;[|solve_reg_lookup].
    + destruct (w3 <? (of_imm w2))%f,  ((of_imm w2) <? w3)%f.
      iDestruct ((gen_reg_update2_global PC i ai (ai ^+ 1)%f NZ i w4 W2 ) with "Hreg Hpc Hnz") as ">[Hreg [Hpc Hnz]]";eauto.
      iModIntro.
      iFrame "Hmem Hreg Haccess".
      iApply "Hϕ".
      by iFrame "Hapc Hra Hpc Hnz".
      iDestruct ((gen_reg_update2_global PC i ai (ai ^+ 1)%f NZ i w4 W2 ) with "Hreg Hpc Hnz") as ">[Hreg [Hpc Hnz]]";eauto.
      iModIntro.
      iFrame "Hmem Hreg Haccess".
      iApply "Hϕ".
      by iFrame "Hapc Hra Hpc Hnz".
      iDestruct ((gen_reg_update2_global PC i ai (ai ^+ 1)%f NZ i w4 W0 ) with "Hreg Hpc Hnz") as ">[Hreg [Hpc Hnz]]";eauto.      iModIntro.
      iFrame "Hmem Hreg Haccess".
      iApply "Hϕ".
      by iFrame "Hapc Hra Hpc Hnz".
      iDestruct ((gen_reg_update2_global PC i ai (ai ^+ 1)%f NZ i w4 W1 ) with "Hreg Hpc Hnz") as ">[Hreg [Hpc Hnz]]";eauto.
      iModIntro.
      iFrame "Hmem Hreg Haccess".
      iApply "Hϕ".
      by iFrame "Hapc Hra Hpc Hnz".
    + rewrite update_reg_global_update_reg;[|solve_reg_lookup].
      apply (get_reg_gmap_get_reg_Some _ _ _ i) in HPC;eauto.
      by simplify_map_eq /=.
Qed.

Lemma cmp_reg {i w1 w2 w3 w4 q sacc} ai ra rb :
  decode_instruction w1 = Some(Cmp ra (inr rb)) ->
  to_pid_aligned ai ∈ sacc ->
  {SS{{ ▷ (PC @@ i ->r ai) ∗ ▷ (ai ->a w1) ∗
        ▷ (ra @@ i ->r w2) ∗ ▷ (rb @@ i ->r w3) ∗
        ▷ (A@i:={q}[sacc]) ∗ ▷ (NZ @@ i ->r w4)}}}
    ExecI @ i
    {{{ RET ExecI;  PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a w1 ∗ ra @@ i ->r w2 ∗ rb @@ i ->r w3 ∗
              A@i:={q}[sacc] ∗ NZ @@ i ->r (if (w2 <? w3)%f then W2 else if (w3 <? w2)%f then W0 else W1) }}}.
Proof.
  iIntros (Hdecode Hin ϕ) "( >Hpc & >Hapc & >Hra & >Hrb & >Hacc & >Hnz ) Hϕ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [ Hcur ]; clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(Htok & Hmem & Hreg & Htx & Hrxagree & Hrxoption & Howned & Haccess & Hrest)".
  set (instr:= Cmp ra (inr rb)).
  pose proof (decode_instruction_valid w1 instr Hdecode) as Hvalidinstr.
  inversion Hvalidinstr as [ | | | | | src dst Hvalidra Hvalidrb Hneqrarb | | | | |] .
  subst src dst.
  destruct  Hvalidra as [ HneqPCa HneqNZa ].
  destruct  Hvalidrb as [ HneqPCb HneqNZb ].
  (* valid regs *)
  iDestruct ((gen_reg_valid4 i PC ai ra w2 rb w3 NZ w4 Hcur) with "Hreg Hpc Hra Hrb Hnz") as "[%HPC [%Hra [%Hrb %HNZ]]]";auto.
  (* valid pt *)
  iDestruct ((gen_access_valid_addr_Set ai ) with "Haccess Hacc") as %Hacc;eauto.
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
    rewrite /exec /instr (cmp_reg_ExecI σ1 ra w2 rb w3) /update_incr_PC /update_reg in Heqc2;eauto.
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    (* unchanged part *)
    rewrite_reg_pc.
    rewrite_reg_global.
    rewrite Hcur.
    iFrame "Htok Htx Hrxagree Hrxoption Howned Hrest".
    (* updated part *)
    rewrite -> (update_offset_PC_update_PC1 _ i ai 1);eauto.
    rewrite update_reg_global_update_reg;[|solve_reg_lookup].
    + destruct (w2 <? w3)%f,  (w3 <? w2)%f.
      iDestruct ((gen_reg_update2_global PC i ai (ai ^+ 1)%f NZ i w4 W2 ) with "Hreg Hpc Hnz") as ">[Hreg [Hpc Hnz]]";eauto.
      iModIntro.
      iFrame "Hmem Hreg Haccess".
      iApply "Hϕ".
      by iFrame "Hpc Hapc Hra Hrb Hnz".
      iDestruct ((gen_reg_update2_global PC i ai (ai ^+ 1)%f NZ i w4 W2 ) with "Hreg Hpc Hnz") as ">[Hreg [Hpc Hnz]]";eauto.
      iModIntro.
      iFrame "Hmem Hreg Haccess".
      iApply "Hϕ".
      by iFrame "Hpc Hapc Hra Hrb Hnz".
      iDestruct ((gen_reg_update2_global PC i ai (ai ^+ 1)%f NZ i w4 W0 ) with "Hreg Hpc Hnz") as ">[Hreg [Hpc Hnz]]";eauto.
      iModIntro.
      iFrame "Hmem Hreg Haccess".
      iApply "Hϕ".
      by iFrame "Hpc Hapc Hra Hrb Hnz".
      iDestruct ((gen_reg_update2_global PC i ai (ai ^+ 1)%f NZ i w4 W1 ) with "Hreg Hpc Hnz") as ">[Hreg [Hpc Hnz]]";eauto.
      iModIntro.
      iFrame "Hmem Hreg Haccess".
      iApply "Hϕ".
      by iFrame "Hpc Hapc Hra Hrb Hnz".
    + rewrite update_reg_global_update_reg;[|solve_reg_lookup].
      apply (get_reg_gmap_get_reg_Some _ _ _ i) in HPC;eauto.
      by simplify_map_eq /=.
Qed.
End cmp.
