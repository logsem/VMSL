From machine_program_logic.program_logic Require Import machine weakestpre.
From HypVeri Require Import RAs rule_misc lifting rules.rules_base.
From iris.proofmode Require Import tactics.
Require Import iris.base_logic.lib.ghost_map.
Require Import stdpp.fin.

Lemma ldr {instr i w1 w2 w3 q s p} ai a ra rb :
  instr = Ldr ra rb ->
  decode_instruction w1 = Some(instr) ->
  ai ≠ a ->
  (mm_translation a) ≠ p -> 
  {[(mm_translation ai);(mm_translation a)]} ⊆ s ->
  TX@ i := p ∗ <<i>> ∗ PC @@ i ->r ai ∗ ai ->a w1 ∗ rb @@ i ->r a ∗ a ->a w2 ∗ A@i:={q}[s] ∗ ra @@ i ->r w3
    ⊢ SSWP ExecI @ i {{ (λ m, ⌜m = ExecI ⌝ ∗ TX@ i := p ∗ <<i>> ∗ PC @@ i ->r (ai +w 1) ∗ ai ->a w1 ∗ rb @@ i ->r a ∗ a ->a w2
                                      ∗ A@i:={q}[s] ∗ ra @@ i ->r w2 ) }}%I.
Proof.
  iIntros (Hinstr Hdecode Hneqaia Hmm Hs) "(Htx & Htok & Hpc & Hapc & Hrb & Harb & Hacc & Hra )".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [ Hcur ]; clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(? & Hmem & Hreg & Htxown & ? & ? & Haccess & ?)".
  pose proof (decode_instruction_valid w1 instr Hdecode) as Hvalidinstr.
  rewrite Hinstr in Hvalidinstr.
  inversion Hvalidinstr as [| | src dst H3' H4' Hneqrarb | | | | |]; subst src dst; clear Hvalidinstr.
  destruct H3' as [HneqPCa HneqNZa].
  destruct H4' as [HneqPCb HneqNZb].
  iDestruct ((gen_reg_valid3 σ1 i PC ai ra w3 rb a Hcur HneqPCa HneqPCb Hneqrarb) with "Hreg Hpc Hra Hrb") as "[%HPC [%Hra %Hrb]]".
  (* valid pt *)
  assert (Hais : mm_translation ai ∈ s). set_solver.
  assert (Has : mm_translation a ∈ s). set_solver.
  iDestruct ((gen_access_valid_addr_elem σ1 i q s a Has) with "Haccess Hacc") as "%Ha".
  iDestruct ((gen_access_valid_addr_elem σ1 i q s ai Hais) with "Haccess Hacc") as "%Hai".
  (* valid mem *)
  iDestruct (gen_mem_valid2 σ1 ai w1 a w2 Hneqaia with "Hmem Hapc Harb ") as "[%Hmemai %Hmema]".
  iDestruct (gen_tx_valid σ1 i p with "Htx Htxown") as %Htx.
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal i instr ai w1);eauto.
  - (* step *)
    iModIntro.
    iIntros (m2 σ2) "%HstepP".
    apply (step_ExecI_normal i instr ai w1 ) in HstepP;eauto.
    remember (exec instr σ1) as c2 eqn:Heqc2.
    rewrite /exec Hinstr (ldr_ExecI σ1 ra rb a w2 HneqPCa HneqNZa HneqPCb HneqNZb _ Hrb)
            /update_incr_PC /update_reg in Heqc2.
    2: {
      rewrite /get_vm_mail_box -Hcur in Htx.
        by rewrite Htx.
    }
    2: {
      unfold get_memory.
        by rewrite Hcur Ha.
    }
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    (* unchanged part *)
    rewrite_reg_all.
    iFrame.
    rewrite Hcur.
    (* updated part *)
    rewrite -> (update_offset_PC_update_PC1 _ i ai 1);eauto.
    + rewrite  update_reg_global_update_reg; [|eexists; rewrite get_reg_gmap_get_reg_Some; eauto ].
      iDestruct ((gen_reg_update2_global σ1 PC i ai (ai +w 1) ra i w3 w2 ) with "Hreg Hpc Hra") as ">[Hσ [Hreg Hra]]";eauto.
      apply (get_reg_gmap_get_reg_Some _ _ _ i) in Hra;eauto.
        by iFrame.
    + rewrite update_reg_global_update_reg;[|solve_reg_lookup].
      repeat solve_reg_lookup.
      intros P; symmetry in P;inversion P; contradiction.
Qed.


Lemma ldr_error {instr i w1 w2 w3 s p} ai a ra rb :
  instr = Ldr ra rb ->
  decode_instruction w1 = Some(instr) ->
  (mm_translation a ∉ s \/ (mm_translation a) = p) ->
  mm_translation ai ∈ s ->
  TX@ i := p ∗ PC @@ i ->r ai ∗ ai ->a w1 ∗ rb @@ i ->r a ∗ a ->a w2 ∗ A@i:={1}[s]∗ ra @@ i ->r w3
    ⊢ SSWP ExecI @ i {{ (λ m, ⌜m = FailPageFaultI⌝ ∗ TX@ i := p ∗ PC @@ i ->r ai  ∗ ai ->a w1 ∗ rb @@ i ->r a ∗ a ->a w2
                             ∗ A@i:={1}[s] ∗ ra @@ i ->r w3 ) }}%I.
Proof.
  iIntros (Hinstr Hdecode Hs Hais) "(Htx & Hpc & Hapc & Hrb & Harb & Hacc & Hra )".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [ Hcur ]; clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(? & Hmem & Hreg & Htxown & ? & ? & Haccess & ?)".
  pose proof (decode_instruction_valid w1 instr Hdecode) as Hvalidinstr.
  rewrite Hinstr in Hvalidinstr.
  inversion Hvalidinstr as [| | src dst H3' H4' Hneqrarb | | | | |]; subst src dst; clear Hvalidinstr.
  destruct H3' as [HneqPCa HneqNZa].
  destruct H4' as [HneqPCb HneqNZb].
  iDestruct ((gen_reg_valid3 σ1 i PC ai ra w3 rb a Hcur HneqPCa HneqPCb Hneqrarb) with "Hreg Hpc Hra Hrb") as "[%HPC [%Hra %Hrb]]".
  iDestruct ((gen_mem_valid σ1 ai w1) with "Hmem Hapc") as "%Hpc".
  iDestruct ((gen_access_valid_addr_elem σ1 i 1 s ai Hais) with "Haccess Hacc") as "%Hai".
  iDestruct (gen_tx_valid σ1 i p with "Htx Htxown") as %Htx.
  destruct Hs as [Hs | Hs]; [
    iDestruct ((gen_no_access_valid σ1 i (mm_translation a) s Hs) with "Haccess Hacc") as "%Ha" |].
  - iSplit.
    + iPureIntro.
      rewrite /reducible.
      exists FailPageFaultI, σ1.
      simplify_eq.
      apply (step_exec_normal σ1 ai w1 (Ldr ra rb) (FailPageFaultI, σ1)); auto.
      * rewrite /is_valid_PC HPC /=.
        rewrite check_access_page_mem_eq in Ha.
        rewrite Hai //.
      * rewrite /get_memory Hai /get_memory_unsafe //.
      * rewrite /exec /lang.ldr.
        destruct ra; try done.
        destruct rb; try done.
        rewrite Hrb.
        rewrite /get_vm_mail_box in Hs.
        destruct (get_mail_boxes σ1 !!! get_current_vm σ1) as [t r].
        simpl in *.
        destruct (decide (mm_translation a = t)); try done.
        rewrite /get_memory.
        rewrite check_access_page_mem_eq in Ha.
        by rewrite Ha.
    + iModIntro.
      iIntros (m2 σ2) "%HstepP".
      iModIntro.
      inversion HstepP; subst.
      * rewrite /is_valid_PC HPC /= in H.
        by rewrite Hai in H.
      * simplify_eq.
        iFrame.
        rewrite /get_memory Hai /get_memory_unsafe in H1.
        simplify_eq.
        rewrite /exec /lang.ldr.
        destruct ra; try done.
        destruct rb; try done.
        rewrite Hrb.
        rewrite /get_vm_mail_box in Hs.
        destruct (get_mail_boxes σ1 !!! get_current_vm σ1).
        simpl in *.
        rewrite check_access_page_mem_eq in Ha.
        destruct (decide (mm_translation a = t));
          rewrite /get_memory;          
          try (rewrite Ha);
          simpl;
          iFrame;
          done.
  - iSplit.
    + iPureIntro.
      rewrite /reducible.
      exists FailPageFaultI, σ1.
      simplify_eq.
      apply (step_exec_normal σ1 ai w1 (Ldr ra rb) (FailPageFaultI, σ1)); auto.
      * rewrite /is_valid_PC HPC /= Hai //.
      * rewrite /get_memory Hai /get_memory_unsafe; done.
      * rewrite /exec /lang.ldr.
        destruct ra; try done.
        destruct rb; try done.
        rewrite Hrb.
        rewrite /get_vm_mail_box in Htx.
        destruct (get_mail_boxes σ1 !!! get_current_vm σ1) as [t r].
        simpl in *.
        destruct (decide (mm_translation a = t)); done.        
    + iModIntro.
      iIntros (m2 σ2) "%HstepP".
      iModIntro.
      inversion HstepP; subst.
      * rewrite /is_valid_PC HPC /= Hai // in H.
      * simplify_eq.
        iFrame.
        rewrite /get_memory Hai /get_memory_unsafe in H1.
        simplify_eq.
        rewrite /exec /lang.ldr.
        destruct ra; try done.
        destruct rb; try done.
        rewrite Hrb.
        rewrite /get_vm_mail_box in Htx.
        destruct (get_mail_boxes σ1 !!! get_current_vm σ1).
        simpl in *.
        destruct (decide (mm_translation a = t));
          rewrite /get_memory;          
          try (rewrite Ha);
          simpl;
          iFrame;
          done.
Qed.
