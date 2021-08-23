From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base.
From HypVeri.algebra Require Import base mem reg pagetable mailbox.
From HypVeri.lang Require Import lang_extra reg_extra mem_extra.

Section str.

Context `{vmG: !gen_VMG Σ}.
  
Lemma str {instr i qi w1 w2 w3 q s prx} ai a ra rb :
  instr = Str ra rb ->
  decode_instruction w1 = Some(instr) ->
  ai ≠ a ->
  prx ≠ (to_pid_aligned a) ->
  {[(to_pid_aligned ai);(to_pid_aligned a)]} ⊆ s ->
  {SS{{ ▷ (<<i>>{ qi }) ∗ ▷ (PC @@ i ->r ai) ∗ ▷ (ai ->a w1) ∗ ▷ (rb @@ i ->r a) ∗ ▷ (a ->a w3) ∗ ▷ (A@i:={q}[s]) ∗ ▷ (ra @@ i ->r w2) ∗ ▷ (RX@ i := prx)}}} ExecI @ i
                                  {{{ RET ExecI; <<i>>{ qi } ∗ PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a w1 ∗ rb @@ i ->r a ∗ a ->a w2
                                      ∗ A@i:={q}[s] ∗ ra @@ i ->r w2 ∗ RX@i := prx }}}.
Proof.
  iIntros (Hinstr Hdecode Hneqaia Hnotrx Hs ϕ) "(? & >Hpc & >Hapc & >Hrb & >Harb & >Hacc & >Hra & >HRX) Hϕ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [ Hcur ]; clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(? & Hmem & Hreg & ? & Hrxpage & ? & ? & Haccess & ?)".
  pose proof (decode_instruction_valid w1 instr Hdecode) as Hvalidinstr.
  rewrite Hinstr in Hvalidinstr.
  inversion Hvalidinstr as [ | | | src dst Hvalidra Hvalidrb Hneqrarb | | | |] .
  subst src dst.
  inversion Hvalidra as [ HneqPCa HneqNZa ].
  inversion Hvalidrb as [ HneqPCb HneqNZb ].
  (* valid regs *)
  iDestruct ((gen_reg_valid3 i PC ai ra w2 rb a Hcur HneqPCa HneqPCb Hneqrarb ) with "Hreg Hpc Hra Hrb") as "[%HPC [%Hra %Hrb]]".
  (* valid pt *)
  assert (Hais : to_pid_aligned ai ∈ s). set_solver.
  assert (Has : to_pid_aligned a ∈ s). set_solver.
  iDestruct ((gen_access_valid_addr_elem a s Has) with "Haccess Hacc") as "%Ha".
  iDestruct ((gen_access_valid_addr_elem ai s Hais) with "Haccess Hacc") as "%Hai".
  (* valid mem *)
  iDestruct (gen_mem_valid2 ai w1 a w3 Hneqaia with "Hmem Hapc Harb ") as "[%Hmemai %Hmema]".
  (* valid rx *)
  iDestruct (gen_rx_pid_valid i prx with "HRX Hrxpage") as %Hprx.
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal i instr ai w1);eauto.
  - (* step *)
    iModIntro.
    iIntros (m2 σ2) "%HstepP".
    apply (step_ExecI_normal i instr ai w1 ) in HstepP;eauto.
    remember (exec instr σ1) as c2 eqn:Heqc2.
    rewrite /exec Hinstr (str_ExecI σ1 ra rb w2 a HneqPCa HneqNZa HneqPCb HneqNZb _ Hra Hrb) /update_incr_PC in Heqc2.
    2: {
      rewrite /get_vm_mail_box -Hcur in Hprx.
      by rewrite Hprx.
    }
    2: {
      by rewrite Hcur Ha.
    }
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    (* unchanged part *)
    rewrite_mem_all.
    rewrite_reg_all.
    rewrite Hcur.
    iFrame.
    (* updated part *)
    rewrite update_memory_unsafe_preserve_current_vm.
    iDestruct ((gen_reg_update1_global PC i ai (ai ^+ 1)%f) with "Hreg Hpc") as ">[Hreg Hpc]";eauto.
    iDestruct ((gen_mem_update1 a w3 w2) with "Hmem Harb") as ">[Hmem Harb]";eauto.
    rewrite -> (update_offset_PC_update_PC1 _ i ai 1);eauto.
    rewrite Hcur.
    iModIntro.
    iFrame.
    iApply "Hϕ".
    iFrame.
    apply (get_reg_gmap_get_reg_Some _ _ _ i) in HPC;eauto.
Qed.

Lemma str_error {instr i w1 w2 w3 s p} ai a ra rb :
  instr = Str ra rb ->
  decode_instruction w1 = Some(instr) ->
  (to_pid_aligned a) ≠ p ->
  (to_pid_aligned a ∉ s \/ (to_pid_aligned a) = p) ->
  to_pid_aligned ai ∈ s ->
  {SS{{ ▷ (RX@ i := p) ∗ ▷ (PC @@ i ->r ai) ∗ ▷ (ai ->a w1) ∗ ▷ (rb @@ i ->r a) ∗ ▷ (a ->a w3) ∗ ▷ (A@i:={1}[s]) ∗ ▷ (ra @@ i ->r w2)}}} ExecI @ i
                                  {{{ RET FailPageFaultI; RX@ i := p ∗ PC @@ i ->r ai ∗ ai ->a w1 ∗ rb @@ i ->r a ∗ a ->a w3
                             ∗ A@i:={1}[s] ∗ ra @@ i ->r w2 }}}.
Proof.
  iIntros (Hinstr Hdecode Hs Has Hais ϕ) "(>Hrx & >Hpc & >Hapc & >Hrb & >Harb & >Hacc & >Hra ) Hϕ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [ Hcur ]; clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(? & Hmem & Hreg & ? & Hrxown & ? & ? & Haccess & ?)".
  pose proof (decode_instruction_valid w1 instr Hdecode) as Hvalidinstr.
  rewrite Hinstr in Hvalidinstr.
  inversion Hvalidinstr as [| | | src dst H3' H4' Hneqrarb | | | |]; subst src dst; clear Hvalidinstr.
  destruct H3' as [HneqPCa HneqNZa].
  destruct H4' as [HneqPCb HneqNZb].
  iDestruct ((gen_reg_valid3 i PC ai ra w2 rb a Hcur HneqPCa HneqPCb Hneqrarb) with "Hreg Hpc Hra Hrb") as "[%HPC [%Hra %Hrb]]".
  iDestruct ((gen_mem_valid ai w1) with "Hmem Hapc") as "%Hpc".
  iDestruct ((gen_access_valid_addr_elem ai s Hais) with "Haccess Hacc") as "%Hai".
  iDestruct (gen_rx_pid_valid i p with "Hrx Hrxown") as %Hrx.
  destruct Has as [Has | Has].
  - iDestruct ((gen_access_valid_not (to_pid_aligned a) s Has) with "Haccess Hacc") as "%Ha".
    iSplit.
    + iPureIntro.
      rewrite /reducible.
      exists FailPageFaultI, σ1.
      simplify_eq.
      apply (step_exec_normal σ1 ai w1 (Str ra rb) (FailPageFaultI, σ1)); auto.
      * rewrite /is_valid_PC HPC.
        simpl.
        rewrite check_access_page_mem_eq in Ha.
        rewrite Hai.
        reflexivity.
      * rewrite /get_memory Hai /get_memory_unsafe; done.
      * rewrite /exec /lang.str.
        destruct ra; try done.
        destruct rb; try done.
        rewrite Hra.
        simpl.
        rewrite Hrb.
        rewrite /get_vm_mail_box in Hs.
        destruct (get_mail_boxes σ1 !!! get_current_vm σ1) as [t [r1 r2]].
        simpl in *.
        destruct (decide (to_pid_aligned a = r1)); try done.
        rewrite check_access_page_mem_eq in Ha.
        rewrite /update_memory Ha.
        reflexivity.
    + iModIntro.
      iIntros (m2 σ2) "%HstepP".
      iModIntro.
      inversion HstepP; subst.
      * rewrite /is_valid_PC HPC in H.
        simpl in H.
        rewrite Hai in H.
        done.
      * simplify_eq.
        iFrame.
        rewrite /get_memory Hai /get_memory_unsafe in H1.
        simplify_eq.
        rewrite /exec /lang.str Hra.
        simpl.
        rewrite Hrb.
        rewrite /get_vm_mail_box in Hs.
        destruct (get_mail_boxes σ1 !!! get_current_vm σ1) as [t [r1 r2]].
        destruct (decide (to_pid_aligned a = r1)); try done.
        rewrite /update_memory.
        rewrite check_access_page_mem_eq in Ha.
        rewrite /update_memory Ha.
        simpl.
        iFrame.
        iApply "Hϕ".
        by iFrame.
  - iSplit.
    + iPureIntro.
      exists FailPageFaultI, σ1.
      simplify_eq.
    + iModIntro.
      iIntros (m2 σ2) "%HstepP".
      iModIntro.
      inversion HstepP; subst; simplify_eq.
Qed.
End str.
