From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base.
From HypVeri.algebra Require Import base reg mem mailbox pagetable.
From HypVeri.lang Require Import lang_extra reg_extra mem_extra.

Section ldr.

Context `{hypparams: HypervisorParameters}.
Context `{vmG: !gen_VMG Σ}.
  
Lemma ldr {i w1 w2 w3 q p} ai a ra rb s:
  decode_instruction w1 = Some (Ldr ra rb) ->
  (to_pid_aligned a) ≠ p ->
  {[(to_pid_aligned ai);(to_pid_aligned a)]} ⊆ s ->
  {SS{{ ▷ (PC @@ i ->r ai) ∗
        ▷ (ai ->a w1) ∗
        ▷ (rb @@ i ->r a) ∗
        ▷ (a ->a w2) ∗
        ▷ (ra @@ i ->r w3) ∗
        ▷ (A@i:={q}[s]) ∗
        ▷ (TX@ i := p)}}}
    ExecI @ i
    {{{ RET ExecI;
        PC @@ i ->r (ai ^+ 1)%f ∗
        ai ->a w1 ∗
        rb @@ i ->r a ∗
        a ->a w2 ∗
        ra @@ i ->r w2 ∗
        A@i:={q}[s] ∗
        TX@ i := p }}}.
Proof.
  iIntros (Hdecode Hmm Hs ϕ) "(>Hpc & >Hapc & >Hrb & >Harb & >Hra & >Hacc & >Htx) Hϕ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [ Hcur ]; clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(Hσtok & Hmem & Hreg & Htxown & Hrx1 & Hrx2 & Hown & Haccess & Hrest)".
  pose proof (decode_instruction_valid w1 _ Hdecode) as Hvalidinstr.
  inversion Hvalidinstr as [| | src dst H3' H4' Hneqrarb | | | | | | | |]; subst src dst; clear Hvalidinstr.
  destruct H3' as [HneqPCa HneqNZa].
  destruct H4' as [HneqPCb HneqNZb].
  iDestruct ((gen_reg_valid3 i PC ai ra w3 rb a Hcur) with "Hreg Hpc Hra Hrb") as "[%HPC [%Hra %Hrb]]".
  (* valid pt *)
  assert (Hais : to_pid_aligned ai ∈ s). set_solver.
  assert (Has : to_pid_aligned a ∈ s). set_solver.
  iDestruct ((gen_access_valid_addr_elem a s Has) with "Haccess Hacc") as "%Ha".
  iDestruct ((gen_access_valid_addr_elem ai s Hais) with "Haccess Hacc") as "%Hai".
  (* valid mem *)
  iDestruct (gen_mem_valid2 ai w1 a w2 with "Hmem Hapc Harb") as "[%Hmemai %Hmema]".
  iDestruct (gen_tx_valid i p with "Htx Htxown") as %Htx.
  iSplit.
  - (* reducible *)
    iPureIntro.
    eapply (reducible_normal i _ ai w1);eauto.
  - (* step *)
    iModIntro.
    iIntros (m2 σ2) "%HstepP".
    eapply (step_ExecI_normal i _ ai w1 ) in HstepP;eauto.
    remember (exec _ σ1) as c2 eqn:Heqc2.
    rewrite /exec (ldr_ExecI σ1 ra rb a w2 HneqPCa HneqNZa HneqPCb HneqNZb _ Hrb)
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
    rewrite_reg_pc.
    rewrite_reg_global.
    iFrame "Hσtok Hmem Htxown Hrx1 Hrx2 Hown Haccess Hrest".
    rewrite Hcur.
    (* updated part *)
    rewrite -> (update_offset_PC_update_PC1 _ i ai 1);eauto.
    + rewrite  update_reg_global_update_reg; [|eexists; rewrite get_reg_gmap_get_reg_Some; eauto ].
      iDestruct ((gen_reg_update2_global PC i ai (ai ^+ 1)%f ra i w3 w2 ) with "Hreg Hpc Hra") as ">[Hσ [Hreg Hra]]";eauto.
      apply (get_reg_gmap_get_reg_Some _ _ _ i) in Hra;eauto.
      iModIntro.
      iFrame "Hσ".
      iApply "Hϕ".
      iFrame "Hreg Hapc Harb Hra Hrb Hacc Htx".
    + rewrite update_reg_global_update_reg;[|solve_reg_lookup].
      repeat solve_reg_lookup.
      intros P; symmetry in P;inversion P; contradiction.
Qed.

Lemma ldr_error {i w1 w2 w3 s p} ai a ra rb :
  decode_instruction w1 = Some (Ldr ra rb) ->
  (to_pid_aligned a ∉ s \/ (to_pid_aligned a) = p) ->
  to_pid_aligned ai ∈ s ->
  {SS{{ ▷ (TX@ i := p) ∗ ▷ (PC @@ i ->r ai) ∗ ▷ (ai ->a w1) ∗ ▷ (rb @@ i ->r a)
          ∗ ▷ (a ->a w2) ∗ ▷ (A@i:={1}[s]) ∗ ▷ (ra @@ i ->r w3)}}} ExecI @ i
    {{{ RET FailPageFaultI; TX@ i := p ∗ PC @@ i ->r ai ∗ ai ->a w1
       ∗ rb @@ i ->r a ∗ a ->a w2 ∗ A@i:={1}[s] ∗ ra @@ i ->r w3 }}}.
Proof.
  iIntros (Hdecode Hs Hais ϕ) "(>Htx & >Hpc & >Hapc & >Hrb & >Harb & >Hacc & >Hra ) Hϕ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [ Hcur ]; clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(Htok & Hmem & Hreg & Htxown & Hrx1 & Hrx2 & Hown & Haccess & Hrest)".
  pose proof (decode_instruction_valid w1 _ Hdecode) as Hvalidinstr.
  inversion Hvalidinstr as [| | src dst H3' H4' Hneqrarb | | | | | | | |]; subst src dst; clear Hvalidinstr.
  destruct H3' as [HneqPCa HneqNZa].
  destruct H4' as [HneqPCb HneqNZb].
  iDestruct ((gen_reg_valid3 i PC ai ra w3 rb a Hcur) with "Hreg Hpc Hra Hrb") as "[%HPC [%Hra %Hrb]]".
  iDestruct ((gen_mem_valid ai w1) with "Hmem Hapc") as "%Hpc".
  iDestruct ((gen_access_valid_addr_elem ai s Hais) with "Haccess Hacc") as "%Hai".
  iDestruct (gen_tx_valid i p with "Htx Htxown") as %Htx.
  destruct Hs as [Hs | Hs]; [
    iDestruct ((gen_access_valid_not (to_pid_aligned a) s Hs) with "Haccess Hacc") as "%Ha" |].
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
        destruct (decide (to_pid_aligned a = t)); try done.
        rewrite /get_memory.
        rewrite check_access_page_mem_eq in Ha.
        by rewrite Ha.
    + iModIntro.
      iIntros (m2 σ2) "%HstepP".
      iModIntro.
      inversion HstepP as [? Hnvalid |Hnvalid ? ? ? ? Hvalid HPC' Ha0 Hdecode']; subst.
      * rewrite /is_valid_PC HPC /= Hai // in Hnvalid.
      * simplify_eq.
        rewrite /get_memory Hai /get_memory_unsafe in Ha0.
        rewrite Hpc in Ha0.
        inversion Ha0;subst;clear Ha0.
        rewrite Hdecode in Hdecode'.
        inversion Hdecode';subst;clear Hdecode'.
        rewrite /exec /lang.ldr /=.
        destruct ra; try done.
        destruct rb; try done.
        rewrite Hrb.
        rewrite /get_vm_mail_box in Hs.
        destruct (get_mail_boxes σ1 !!! get_current_vm σ1).
        simpl in HstepP.
        rewrite check_access_page_mem_eq in Ha.
        destruct (decide (to_pid_aligned a = p));
          rewrite /get_memory;          
          try (rewrite Ha);
          simpl;
          iFrame; iApply "Hϕ"; iFrame.
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
        destruct (decide (to_pid_aligned a = t)); done.
    + iModIntro.
      iIntros (m2 σ2) "%HstepP".
      iModIntro.
      inversion HstepP as [? Hnvalid |Hnvalid ? ? ? ? Hvalid HPC' Ha0 Hdecode']; subst.
      * rewrite /is_valid_PC HPC /= Hai // in Hnvalid.
      * simplify_eq.
        rewrite /get_memory Hai /get_memory_unsafe in Ha0.
        simplify_eq.
        rewrite /exec /lang.ldr.
        destruct ra; try done.
        destruct rb; try done.
        rewrite Hrb.
        rewrite /get_vm_mail_box in Htx.
        destruct (get_mail_boxes σ1 !!! get_current_vm σ1).
        simpl in HstepP.
        destruct (decide (to_pid_aligned a = p));
          rewrite /get_memory;          
          try (rewrite Ha);
          simpl.
        -- iFrame "Htok Hmem Hreg Htxown Hrx1 Hrx2 Hown Haccess Hrest".
           iApply "Hϕ".
           iFrame "Htx Hpc Hapc Hrb Harb Hacc Hra".
        -- simplify_eq.
Qed.
End ldr.
