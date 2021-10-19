From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.algebra Require Import base reg mem pagetable.
From HypVeri Require Import machine_extra lifting rules.rules_base.
From HypVeri.lang Require Import lang_extra reg_extra.

Section mov.

Context `{hypparams: HypervisorParameters}.
Context `{vmG: !gen_VMG Σ}.

Lemma mov_word {E i w1 w3 q s} a w2 ra :
  decode_instruction w1 = Some (Mov ra (inl w2)) ->
  to_pid_aligned a ∈ s ->
  {SS{{ ▷ (PC @@ i ->r a)
          ∗ ▷ (a ->a w1) ∗ ▷ (A@i:={q}[s])
          ∗ ▷ (ra @@ i ->r w3)}}}
    ExecI @ i ; E
  {{{ RET ExecI;  PC @@ i ->r (a ^+ 1)%f
                   ∗ a ->a w1
                   ∗ A@i:={q}[s]
                   ∗ ra @@ i ->r w2 }}}.
Proof.
  iIntros (Hdecode Hin ϕ) "( >Hpc & >Hapc & >Hacc & >Hra) Hϕ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [ Hcur ]; clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(H1 & Hmem & Hreg & ? & ? & ? & ? & Haccess & H2)".
  pose proof (decode_instruction_valid w1 _ Hdecode) as Hvalidinstr.
  inversion Hvalidinstr as [imm dst Hvalidra | | | | | | | | | | |].
  subst imm dst.
  inversion Hvalidra as [HneqPC HneqNZ].
  (* valid regs *)
  iDestruct ((gen_reg_valid2 i PC a ra w3 Hcur) with "Hreg Hpc Hra") as "[%HPC %Hra]".
  (* valid pt *)
  iDestruct (gen_access_valid_addr_Set a with "Haccess Hacc") as %Hacc;eauto.
  (* valid mem *)
  iDestruct (gen_mem_valid a w1 with "Hmem Hapc") as "%Hmem".
  iSplit.
  - (* reducible *)
    iPureIntro.
    eapply (reducible_normal i _ a w1);eauto.
  - (* step *)
    iModIntro.
    iIntros (m2 σ2) "%HstepP".
    eapply (step_ExecI_normal i _ a w1) in HstepP;eauto.
    remember (exec _ σ1) as c2 eqn:Heqc2.
    rewrite /exec (mov_word_ExecI σ1 ra _ HneqPC HneqNZ) /update_incr_PC /update_reg  in Heqc2.
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    (* unchanged part *)
    rewrite_reg_pc.
    rewrite_reg_global.
    rewrite Hcur. iFrame.
    (* updated part *)
    rewrite -> (update_offset_PC_update_PC1 _ i a 1);eauto.
    + rewrite  update_reg_global_update_reg; [|eexists; rewrite get_reg_gmap_get_reg_Some; eauto ].
      iDestruct ((gen_reg_update2_global PC i a (a ^+ 1)%f ra i w3 w2 ) with "Hreg Hpc Hra") as ">[Hσ Hreg]";eauto.
      iModIntro.
      iFrame "Hσ".
      iApply "Hϕ".
      iFrame "Hapc Hacc Hreg".
    + rewrite update_reg_global_update_reg;[|solve_reg_lookup].
      repeat solve_reg_lookup.
      intros P; symmetry in P;inversion P; contradiction.
    Qed.

Lemma mov_reg {E i w1 w3 q s} a w2 ra rb :
  decode_instruction w1 = Some (Mov ra (inr rb)) ->
  to_pid_aligned a ∈ s ->
  {SS{{  ▷ (PC @@ i ->r a)
          ∗ ▷ (a ->a w1) ∗ ▷ (A@i:={q}[s])
          ∗ ▷ (ra @@ i ->r w2)
          ∗ ▷ (rb @@ i ->r w3) }}}
    ExecI @ i ;E
  {{{ RET ExecI; PC @@ i ->r (a ^+ 1)%f
                   ∗ a ->a w1
                   ∗ A@i:={q}[s]
                   ∗ ra @@ i ->r w3
                   ∗ rb @@ i ->r w3}}}.
Proof.
  iIntros (Hdecode Hin ϕ) "(>Hpc & >Hapc & >Hacc & >Hra & >Hrb) Hϕ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [ Hcur ]; clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  pose proof (decode_instruction_valid w1 _ Hdecode) as Hvalidinstr.
  inversion Hvalidinstr as [ | src dst Hvalidra Hvalidrb Hneqrarb | | | | | | | | | |] .
  subst src dst.
  inversion Hvalidra as [ HneqPCa HneqNZa ].
  inversion Hvalidrb as [ HneqPCb HneqNZb ].
  iDestruct "Hσ" as "(Htok & Hmem & Hreg & Htx & Hrx1 & Hrx2 & Hown & Haccess & H2)".
  (* valid regs *)
  iDestruct ((gen_reg_valid3 i PC a ra w2 rb w3 Hcur) with "Hreg Hpc Hra Hrb") as "[%HPC [%Hra %Hrb]]".
  (* valid pt *)
  iDestruct (gen_access_valid_addr_Set a s with "Haccess Hacc") as %Hacc;eauto.
  (* valid mem *)
  iDestruct (gen_mem_valid a w1 with "Hmem Hapc") as "%Hmem".
  iSplit.
  - (* reducible *)
    iPureIntro.
    eapply (reducible_normal i _ a w1);eauto.
  - (* step *)
    iModIntro.
    iIntros (m2 σ2) "%HstepP".
    eapply (step_ExecI_normal i _ a w1) in HstepP;eauto.
    remember (exec _ σ1) as c2 eqn:Heqc2.
    rewrite /exec (mov_reg_ExecI σ1 ra rb w3 HneqPCa HneqNZa HneqPCb HneqNZb Hrb)  /update_incr_PC /update_reg  in Heqc2.
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.    (* unchanged part *)
    rewrite_reg_pc.
    rewrite_reg_global.
    rewrite Hcur.
    iFrame "Htok Hmem Htx Hrx1 Hrx2 Hown Haccess H2".
    (* updated part *)
    rewrite -> (update_offset_PC_update_PC1 _ i a 1);eauto.
    + rewrite  update_reg_global_update_reg; [|eexists; rewrite get_reg_gmap_get_reg_Some; eauto ].
      iDestruct ((gen_reg_update2_global PC i a (a ^+ 1)%f ra i w2 w3 ) with "Hreg Hpc Hra") as ">[Hσ Hreg]";eauto.
      iModIntro.
      iFrame "Hσ".
      iApply "Hϕ".
      by iFrame "Hapc Hacc Hrb Hreg".
    + rewrite update_reg_global_update_reg;[|solve_reg_lookup].
      repeat solve_reg_lookup.
      intros P; symmetry in P;inversion P; contradiction.
Qed.
End mov.
