From machine_program_logic.program_logic Require Import machine weakestpre.
From HypVeri Require Import RAs rule_misc lifting rules.rules_base.
From iris.proofmode Require Import tactics.
Require Import iris.base_logic.lib.ghost_map.
Require Import stdpp.fin.

Section mov.

Context `{vmG: !gen_VMG Σ}.
  
Lemma mov_word {E instr i w1 w3 q p} a w2 ra :
  instr = Mov ra (inl w2) ->
  decode_instruction w1 = Some(instr) ->
  addr_in_page a p ->
  {SS{{  ▷ (PC @@ i ->r a)
          ∗ ▷ (a ->a w1) ∗ ▷ (A@i:={q} p)
          ∗ ▷ (ra @@ i ->r w3)}}}
    ExecI @ i ; E
  {{{ RET ExecI;  PC @@ i ->r (a ^+ 1)%f
                   ∗ a ->a w1
                   ∗ A@i:={q} p
                   ∗ ra @@ i ->r w2 }}}.
Proof.
  iIntros (Hinstr Hdecode Hin ϕ) "( >Hpc & >Hapc & >Hacc & >Hra) Hϕ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [ Hcur ]; clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(H1 & Hmem & Hreg & ? & ? & ? & ? & Haccess & H2)".
  pose proof (decode_instruction_valid w1 instr Hdecode) as Hvalidinstr.
  rewrite Hinstr in Hvalidinstr.
  inversion Hvalidinstr as [imm dst Hvalidra | | | | | | | ].
  subst imm dst.
  inversion Hvalidra as [HneqPC HneqNZ].
  (* valid regs *)
  iDestruct ((gen_reg_valid2 σ1 i PC a ra w3 Hcur HneqPC) with "Hreg Hpc Hra") as "[%HPC %Hra]".
  (* valid pt *)
  iDestruct (gen_access_valid_addr a _ Hin with "Haccess Hacc") as %Hacc.
  (* valid mem *)
  iDestruct (gen_mem_valid σ1 a w1 with "Hmem Hapc") as "%Hmem".
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal i instr a w1);eauto.
  - (* step *)
    iModIntro.
    iIntros (m2 σ2) "%HstepP".
    apply (step_ExecI_normal i instr a w1) in HstepP;eauto.
    remember (exec instr σ1) as c2 eqn:Heqc2.
    rewrite /exec Hinstr (mov_word_ExecI σ1 ra _ HneqPC HneqNZ)  /update_incr_PC /update_reg  in Heqc2.
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    (* unchanged part *)
    rewrite_reg_all.
    rewrite Hcur. iFrame.
    (* updated part *)
    rewrite -> (update_offset_PC_update_PC1 _ i a 1);eauto.
    + rewrite  update_reg_global_update_reg; [|eexists; rewrite get_reg_gmap_get_reg_Some; eauto ].
      iDestruct ((gen_reg_update2_global σ1 PC i a (a ^+ 1)%f ra i w3 w2 ) with "Hreg Hpc Hra") as ">[Hσ Hreg]";eauto.
      iModIntro.
      iFrame.
      iApply "Hϕ".
      iFrame.
      iFrame.
    + rewrite update_reg_global_update_reg;[|solve_reg_lookup].
      repeat solve_reg_lookup.
      intros P; symmetry in P;inversion P; contradiction.
    Qed.

Lemma mov_reg {E instr i qi w1 w3 q p} a w2 ra rb :
  instr = Mov ra (inr rb)->
  decode_instruction w1 = Some(instr) ->
  addr_in_page a p ->
  {SS{{ ▷ (<<i>>{ qi }) ∗ ▷ (PC @@ i ->r a)
          ∗ ▷ (a ->a w1) ∗ ▷ (A@i:={q} p)
          ∗ ▷ (ra @@ i ->r w2)
          ∗ ▷ (rb @@ i ->r w3) }}}
    ExecI @ i ;E
  {{{ RET ExecI; <<i>>{ qi }
                   ∗ PC @@ i ->r (a ^+ 1)%f
                   ∗ a ->a w1
                   ∗ A@i:={q} p
                   ∗ ra @@ i ->r w3
                   ∗ rb @@ i ->r w3}}}.
Proof.
  iIntros (Hinstr Hdecode Hin ϕ) "(? & >Hpc & >Hapc & >Hacc & >Hra & >Hrb) Hϕ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [ Hcur ]; clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  pose proof (decode_instruction_valid w1 instr Hdecode) as Hvalidinstr.
  rewrite Hinstr in Hvalidinstr.
  inversion Hvalidinstr as [ | src dst Hvalidra Hvalidrb Hneqrarb  | | | | | |] .
  subst src dst.
  inversion Hvalidra as [ HneqPCa HneqNZa ].
  inversion Hvalidrb as [ HneqPCb HneqNZb ].
  iDestruct "Hσ" as "(? & Hmem & Hreg & ? & ? & ? & ? & Haccess & H2)".
  (* valid regs *)
  iDestruct ((gen_reg_valid3 σ1 i PC a ra w2 rb w3 Hcur HneqPCa HneqPCb Hneqrarb) with "Hreg Hpc Hra Hrb") as "[%HPC [%Hra %Hrb]]".
  (* valid pt *)
  iDestruct (gen_access_valid_addr a _ Hin with "Haccess Hacc") as %Hacc.
  (* valid mem *)
  iDestruct (gen_mem_valid σ1 a w1 with "Hmem Hapc") as "%Hmem".
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal i instr a w1);eauto.
  - (* step *)
    iModIntro.
    iIntros (m2 σ2) "%HstepP".
    apply (step_ExecI_normal i instr a w1) in HstepP;eauto.
    remember (exec instr σ1) as c2 eqn:Heqc2.
    rewrite /exec Hinstr (mov_reg_ExecI σ1 ra rb w3 HneqPCa HneqNZa HneqPCb HneqNZb Hrb)  /update_incr_PC /update_reg  in Heqc2.
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.    (* unchanged part *)
    rewrite_reg_all.
    rewrite Hcur.
    iFrame.
    (* updated part *)
    rewrite -> (update_offset_PC_update_PC1 _ i a 1);eauto.
    + rewrite  update_reg_global_update_reg; [|eexists; rewrite get_reg_gmap_get_reg_Some; eauto ].
      iDestruct ((gen_reg_update2_global σ1 PC i a (a ^+ 1)%f ra i w2 w3 ) with "Hreg Hpc Hra") as ">[Hσ Hreg]";eauto.
      iModIntro.
      iFrame.
      iApply "Hϕ".
      by iFrame.
    + rewrite update_reg_global_update_reg;[|solve_reg_lookup].
      repeat solve_reg_lookup.
      intros P; symmetry in P;inversion P; contradiction.
Qed.
End mov.
