From machine_program_logic.program_logic Require Import machine weakestpre.
From HypVeri Require Import RAs rule_base lifting.
From iris.proofmode Require Import tactics.
Require Import iris.base_logic.lib.ghost_map.

Section rules.

Global Instance hyp_irisG `{gen_VMG Σ}: irisG hyp_machine Σ:=
  {
  iris_invG := gen_invG;
  state_interp := gen_vm_interp
  }.

Context `{vmG: !gen_VMG Σ}.
Implicit Type a : addr.
Implicit Type i : vmid.
Implicit Type ra rb : reg_name.
Implicit Type w: word.
Implicit Type q : Qp.


Ltac rewrite_reg_all :=
  match goal with
  | |- _ =>
    try rewrite -> update_offset_PC_preserve_current_vm; try rewrite -> update_reg_global_preserve_current_vm;
    try rewrite -> update_offset_PC_preserve_mem ; try rewrite -> update_reg_global_preserve_mem;
    try rewrite -> update_offset_PC_preserve_tx ; try rewrite -> update_reg_global_preserve_tx;
    try rewrite -> update_offset_PC_preserve_rx ; try rewrite  -> update_reg_global_preserve_rx;
    try rewrite -> update_offset_PC_preserve_owned  ; try rewrite -> update_reg_global_preserve_owned;
    try rewrite -> update_offset_PC_preserve_access  ; try rewrite -> update_reg_global_preserve_access;
    try rewrite -> update_offset_PC_preserve_trans  ; try rewrite -> update_reg_global_preserve_trans;
    try rewrite -> update_offset_PC_preserve_receivers  ; try rewrite -> update_reg_global_preserve_receivers
  end.


Ltac rewrite_mem_all :=
  match goal with
  | |- _ =>
    try rewrite -> update_memory_unsafe_preserve_current_vm;
    try rewrite -> update_reg_global_preserve_mem;
    try rewrite -> update_memory_unsafe_preserve_tx;
    try rewrite -> update_memory_unsafe_preserve_rx;
    try rewrite -> update_memory_unsafe_preserve_owned;
    try rewrite -> update_memory_unsafe_preserve_access;
    try rewrite -> update_memory_unsafe_preserve_trans;
    try rewrite -> update_memory_unsafe_preserve_receivers
  end.

Ltac solve_reg_lookup :=
  match goal with
  | _ : get_reg ?σ ?r = Some ?w |- get_reg_gmap ?σ !! (?r, ?i) = Some ?w => rewrite get_reg_gmap_get_reg_Some;eauto
  | _ : get_reg ?σ ?r = Some ?w |- is_Some (get_reg_gmap ?σ !! (?r, ?i)) => eexists;rewrite get_reg_gmap_get_reg_Some;eauto
  | _ : get_reg ?σ ?r1 = Some ?w, _ : ?r1 ≠ ?r2 |- <[(?r2, ?i):= ?w2]>(get_reg_gmap ?σ) !! (?r1, ?i) = Some ?w =>
    rewrite lookup_insert_ne; eauto
  end.
  

Lemma check_access_page_mem_eq {σ i a} :
  check_access_page σ i (mm_translation a) =
  check_access_addr σ i a.
Proof.
  rewrite /check_access_addr; done.
Qed.

    
Lemma not_valid_pc {a i s} :
  (mm_translation a) ∉ s ->
  PC @@ i ->r a ∗ A@i:={1}[s]
  ⊢ SSWP ExecI @ i {{ (λ m, ⌜m = FailI⌝ ∗ PC @@ i ->r a ∗ A@i:={1}[s]) }}%I.
Proof.
  iIntros (Hmm) "(Hpc & Ha)".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (σ1) "%Hsche Hσ1".
  inversion Hsche as [ Hcur ]; clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ1" as "(? & ? & Hreg & ? & ? & ? & Haccess & ?)".
  iDestruct (gen_reg_valid1 σ1 PC i a Hcur with "Hreg Hpc") as "%Hpc".
  iDestruct (gen_no_access_valid σ1 i (mm_translation a) s Hmm with "Haccess Ha") as "%Hnacc".
  iSplit.
  - iPureIntro.
    rewrite /reducible.
    exists FailI, σ1.
    apply step_exec_fail.
    rewrite /is_valid_PC Hpc Hcur.
    simpl.
    rewrite check_access_page_mem_eq in Hnacc.
    rewrite Hnacc.
    done.
  - iModIntro.
    iIntros (m2 σ2) "%HstepP".
    iModIntro.
    inversion HstepP; subst.
    + simpl.
      rewrite /gen_vm_interp.
      iFrame.
      iPureIntro.
      done.
    + simplify_eq.
      rewrite /is_valid_PC Hpc in H.      
      simpl in H.
      rewrite check_access_page_mem_eq in Hnacc.
      rewrite Hnacc in H.
      inversion H.
Qed.

                                      
Lemma mov_word {instr i w1 w3 q} a w2 ra :
  instr = Mov ra (inl w2) ->
  decode_instruction w1 = Some(instr) ->
  <<i>> ∗ PC @@ i ->r a ∗ a ->a w1 ∗ A@i:={q} (mm_translation a) ∗ ra @@ i ->r w3
    ⊢ SSWP ExecI @ i {{ (λ m, ⌜m = ExecI ⌝ ∗ <<i>> ∗ PC @@ i ->r (a +w 1)∗ a ->a w1 ∗ A@i:={q} (mm_translation a) ∗ ra @@ i ->r w2) }}%I.
Proof.
  iIntros (Hinstr Hdecode) "(? & Hpc & Hapc & Hacc & Hra)".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [ Hcur ]; clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(H1 & Hmem & Hreg & ? & ? & ? & Haccess & H2)".
  pose proof (decode_instruction_valid w1 instr Hdecode) as Hvalidinstr.
  rewrite Hinstr in Hvalidinstr.
  inversion Hvalidinstr as [imm dst Hvalidra | | | | | | | ].
  subst imm dst.
  inversion Hvalidra as [HneqPC HneqNZ].
  (* valid regs *)
  iDestruct ((gen_reg_valid2 σ1 i PC a ra w3 Hcur HneqPC) with "Hreg Hpc Hra") as "[%HPC %Hra]".
  (* valid pt *)
  iDestruct (gen_access_valid_addr σ1 i q a with "Haccess Hacc") as %Hacc.
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
      iDestruct ((gen_reg_update2_global σ1 PC i a (a +w 1) ra i w3 w2 ) with "Hreg Hpc Hra") as ">[Hσ Hreg]";eauto.
        by iFrame.
    + rewrite update_reg_global_update_reg;[|solve_reg_lookup].
      repeat solve_reg_lookup.
      intros P; symmetry in P;inversion P; contradiction.
    Qed.

Lemma mov_reg {instr i w1 w3 q} a w2 ra rb :
  instr = Mov ra (inr rb)->
  decode_instruction w1 = Some(instr) ->
  <<i>> ∗ PC @@ i ->r a ∗ a ->a w1 ∗ A@i:={q} (mm_translation a) ∗ ra @@ i ->r w2 ∗ rb @@ i ->r w3
    ⊢ SSWP ExecI @ i {{ (λ m, ⌜m = ExecI ⌝ ∗ <<i>> ∗ PC @@ i ->r (a +w 1)∗ a ->a w1 ∗ A@i:={q} (mm_translation a) ∗ ra @@ i ->r w3 ∗ rb @@ i ->r w3) }}%I.
Proof.
  iIntros (Hinstr Hdecode) "(? & Hpc & Hapc & Hacc & Hra & Hrb)".
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
  iDestruct "Hσ" as "(? & Hmem & Hreg & ? & ? & ? & Haccess & H2)".
  (* valid regs *)
  iDestruct ((gen_reg_valid3 σ1 i PC a ra w2 rb w3 Hcur HneqPCa HneqPCb Hneqrarb) with "Hreg Hpc Hra Hrb") as "[%HPC [%Hra %Hrb]]".
  (* valid pt *)
  iDestruct (gen_access_valid_addr σ1 i q a with "Haccess Hacc") as %Hacc.
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
      iDestruct ((gen_reg_update2_global σ1 PC i a (a +w 1) ra i w2 w3 ) with "Hreg Hpc Hra") as ">[Hσ Hreg]";eauto.
      by iFrame.
    + rewrite update_reg_global_update_reg;[|solve_reg_lookup].
      repeat solve_reg_lookup.
      intros P; symmetry in P;inversion P; contradiction.
    Qed.


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
    ⊢ SSWP ExecI @ i {{ (λ m, ⌜m = FailPageFaultI⌝ ∗ TX@ i := p ∗ PC @@ i ->r ai                                               ∗ ai ->a w1 ∗ rb @@ i ->r a ∗ a ->a w2
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
      * rewrite /is_valid_PC HPC.
        simpl.
        rewrite check_access_page_mem_eq in Ha.
        rewrite Hai.
        reflexivity.
      * rewrite /get_memory Hai /get_memory_unsafe; done.
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
        rewrite Ha.
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
      * rewrite /is_valid_PC HPC.
        simpl.
        rewrite Hai.
        reflexivity.
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
      * rewrite /is_valid_PC HPC in H.
        simpl in H.
        rewrite Hai in H.
        done.
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


Lemma str {instr i w1 w2 w3 q s prx} ai a ra rb :
  instr = Str ra rb ->
  decode_instruction w1 = Some(instr) ->
  ai ≠ a ->
  prx ≠ (mm_translation a) ->
  {[(mm_translation ai);(mm_translation a)]} ⊆ s ->
  <<i>> ∗ PC @@ i ->r ai ∗ ai ->a w1 ∗ rb @@ i ->r a ∗ a ->a w3 ∗ A@i:={q}[s] ∗ ra @@ i ->r w2 ∗ RX@ i := prx
    ⊢ SSWP ExecI @ i {{ (λ m, ⌜m = ExecI ⌝ ∗ <<i>> ∗ PC @@ i ->r (ai +w 1) ∗ ai ->a w1 ∗ rb @@ i ->r a ∗ a ->a w2
                                      ∗ A@i:={q}[s] ∗ ra @@ i ->r w2 ∗ RX@i := prx ) }}%I.
Proof.
  iIntros (Hinstr Hdecode Hneqaia Hnotrx Hs) "(? & Hpc & Hapc & Hrb & Harb & Hacc & Hra & HRX)".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [ Hcur ]; clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(? & Hmem & Hreg & ? & Hrxpage & ? & Haccess & ?)".
  pose proof (decode_instruction_valid w1 instr Hdecode) as Hvalidinstr.
  rewrite Hinstr in Hvalidinstr.
  inversion Hvalidinstr as [ | | | src dst Hvalidra Hvalidrb Hneqrarb | | | |] .
  subst src dst.
  inversion Hvalidra as [ HneqPCa HneqNZa ].
  inversion Hvalidrb as [ HneqPCb HneqNZb ].
  (* valid regs *)
  iDestruct ((gen_reg_valid3 σ1 i PC ai ra w2 rb a Hcur HneqPCa HneqPCb Hneqrarb ) with "Hreg Hpc Hra Hrb") as "[%HPC [%Hra %Hrb]]".
  (* valid pt *)
  assert (Hais : mm_translation ai ∈ s). set_solver.
  assert (Has : mm_translation a ∈ s). set_solver.
  iDestruct ((gen_access_valid_addr_elem σ1 i q s a Has) with "Haccess Hacc") as "%Ha".
  iDestruct ((gen_access_valid_addr_elem σ1 i q s ai Hais) with "Haccess Hacc") as "%Hai".
  (* valid mem *)
  iDestruct (gen_mem_valid2 σ1 ai w1 a w3 Hneqaia with "Hmem Hapc Harb ") as "[%Hmemai %Hmema]".
  (* valid rx *)
  iDestruct (gen_rx_pid_valid σ1 i prx with "HRX Hrxpage") as %Hprx.
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
    iDestruct ((gen_reg_update1_global σ1 PC i ai (ai +w 1)) with "Hreg Hpc") as ">[Hreg Hpc]";eauto.
    iDestruct ((gen_mem_update1 σ1 a w3 w2) with "Hmem Harb") as ">[Hmem Harb]";eauto.    
    rewrite -> (update_offset_PC_update_PC1 _ i ai 1);eauto.
    rewrite Hcur.
    by iFrame.
    apply (get_reg_gmap_get_reg_Some _ _ _ i) in HPC;eauto.
Qed.


Lemma str_error {instr i w1 w2 w3 s p} ai a ra rb :
  instr = Str ra rb ->
  decode_instruction w1 = Some(instr) ->
  (mm_translation a) ≠ p ->
  (mm_translation a ∉ s \/ (mm_translation a) = p) ->
  mm_translation ai ∈ s ->
  RX@ i := p ∗ PC @@ i ->r ai ∗ ai ->a w1 ∗ rb @@ i ->r a ∗ a ->a w3 ∗ A@i:={1}[s]∗ ra @@ i ->r w2
    ⊢ SSWP ExecI @ i {{ (λ m, ⌜m = FailPageFaultI⌝ ∗ RX@ i := p ∗ PC @@ i ->r ai                                               ∗ ai ->a w1 ∗ rb @@ i ->r a ∗ a ->a w3
                             ∗ A@i:={1}[s] ∗ ra @@ i ->r w2 ) }}%I.
Proof.
  iIntros (Hinstr Hdecode Hs Has Hais) "(Hrx & Hpc & Hapc & Hrb & Harb & Hacc & Hra )".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [ Hcur ]; clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(? & Hmem & Hreg & ? & Hrxown & ? & Haccess & ?)".
  pose proof (decode_instruction_valid w1 instr Hdecode) as Hvalidinstr.
  rewrite Hinstr in Hvalidinstr.
  inversion Hvalidinstr as [| | | src dst H3' H4' Hneqrarb | | | |]; subst src dst; clear Hvalidinstr.
  destruct H3' as [HneqPCa HneqNZa].
  destruct H4' as [HneqPCb HneqNZb].
  iDestruct ((gen_reg_valid3 σ1 i PC ai ra w2 rb a Hcur HneqPCa HneqPCb Hneqrarb) with "Hreg Hpc Hra Hrb") as "[%HPC [%Hra %Hrb]]".
  iDestruct ((gen_mem_valid σ1 ai w1) with "Hmem Hapc") as "%Hpc".
  iDestruct ((gen_access_valid_addr_elem σ1 i 1 s ai Hais) with "Haccess Hacc") as "%Hai".
  iDestruct (gen_rx_pid_valid σ1 i p with "Hrx Hrxown") as %Hrx.
  destruct Has as [Has | Has].
  - iDestruct ((gen_no_access_valid σ1 i (mm_translation a) s Has) with "Haccess Hacc") as "%Ha".
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
        destruct (decide (mm_translation a = r1)); try done.
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
        destruct (decide (mm_translation a = r1)); try done.
        rewrite /update_memory.
        rewrite check_access_page_mem_eq in Ha.
        rewrite /update_memory Ha.
        simpl.
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


Lemma cmp_word {instr i w1 w2 w3 w4 q} ai ra :
  instr = Cmp ra (inl w2) ->
  decode_instruction w1 = Some(instr) ->
  <<i>> ∗ PC @@ i ->r ai ∗ ai ->a w1 ∗ ra @@ i ->r w3 ∗ A@i:={q} (mm_translation ai) ∗ NZ @@ i ->r w4
    ⊢ SSWP ExecI @ i {{ (λ m, ⌜m = ExecI ⌝ ∗ <<i>> ∗ PC @@ i ->r (ai +w 1) ∗ ai ->a w1 ∗ ra @@ i ->r w3
                       ∗ A@i:={q} (mm_translation ai)
                       ∗ NZ @@ i ->r (if (w3 <? w2) then two_word else if (w2 <? w3) then zero_word else one_word)) }}%I.
Proof.
  iIntros (Hinstr Hdecode) "(? & Hpc & Hapc & Hra & Hacc & Hnz )".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [ Hcur ]; clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(? & Hmem & Hreg & ? & ? & ? & Haccess & ?)".
  pose proof (decode_instruction_valid w1 instr Hdecode) as Hvalidinstr.
  rewrite Hinstr in Hvalidinstr.
  inversion Hvalidinstr as [ | | | | src dst Hvalidra | | |] .
  subst src dst.
  inversion Hvalidra as [ HneqPCa HneqNZa ].
  (* valid regs *)
  iDestruct ((gen_reg_valid3 σ1 i PC ai ra w3 NZ w4 Hcur HneqPCa) with "Hreg Hpc Hra Hnz") as "[%HPC [%Hra %HNZ]]";eauto.
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
    rewrite /exec Hinstr (cmp_word_ExecI σ1 ra w3 w2 HneqPCa HneqNZa Hra) /update_incr_PC /update_reg in Heqc2.
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    (* unchanged part *)
    rewrite_reg_all.
    rewrite Hcur.
    iFrame.
    (* updated part *)
    rewrite -> (update_offset_PC_update_PC1 _ i ai 1);eauto.
    rewrite update_reg_global_update_reg;[|solve_reg_lookup].
    + destruct (w3 <? w2),  (w2 <? w3).
      iDestruct ((gen_reg_update2_global σ1 PC i ai (ai +w 1) NZ i w4 two_word ) with "Hreg Hpc Hnz") as ">[Hreg [Hpc Hnz]]";eauto.
      by iFrame.
      iDestruct ((gen_reg_update2_global σ1 PC i ai (ai +w 1) NZ i w4 two_word ) with "Hreg Hpc Hnz") as ">[Hreg [Hpc Hnz]]";eauto.
      by iFrame.
      iDestruct ((gen_reg_update2_global σ1 PC i ai (ai +w 1) NZ i w4 zero_word ) with "Hreg Hpc Hnz") as ">[Hreg [Hpc Hnz]]";eauto.
      by iFrame.
      iDestruct ((gen_reg_update2_global σ1 PC i ai (ai +w 1) NZ i w4 one_word ) with "Hreg Hpc Hnz") as ">[Hreg [Hpc Hnz]]";eauto.
      by iFrame.
    + rewrite update_reg_global_update_reg;[|solve_reg_lookup].
      apply (get_reg_gmap_get_reg_Some _ _ _ i) in HPC;eauto.
      by simplify_map_eq /=.
Qed.

Lemma cmp_reg {instr i w1 w2 w3 w4 q} ai ra rb :
  instr = Cmp ra (inr rb) ->
  decode_instruction w1 = Some(instr) ->
  <<i>> ∗ PC @@ i ->r ai ∗ ai ->a w1 ∗ ra @@ i ->r w2 ∗ rb @@ i ->r w3 ∗ A@i:={q} (mm_translation ai) ∗ NZ @@ i ->r w4
    ⊢ SSWP ExecI @ i {{ (λ m, ⌜m = ExecI ⌝ ∗ <<i>> ∗ PC @@ i ->r (ai +w 1) ∗ ai ->a w1 ∗ ra @@ i ->r w2 ∗ rb @@ i ->r w3
                       ∗ A@i:={q} (mm_translation ai)
                       ∗ NZ @@ i ->r (if (w2 <? w3) then two_word else if (w3 <? w2) then zero_word else one_word)) }}%I.
Proof.
  iIntros (Hinstr Hdecode) "(? & Hpc & Hapc & Hra & Hrb & Hacc & Hnz )".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [ Hcur ]; clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(? & Hmem & Hreg & ? & ? & ? & Haccess & ?)".
  pose proof (decode_instruction_valid w1 instr Hdecode) as Hvalidinstr.
  rewrite Hinstr in Hvalidinstr.
  inversion Hvalidinstr as [ | | | | | src dst Hvalidra Hvalidrb Hneqrarb | |] .
  subst src dst.
  destruct  Hvalidra as [ HneqPCa HneqNZa ].
  destruct  Hvalidrb as [ HneqPCb HneqNZb ].
  (* valid regs *)
  iDestruct ((gen_reg_valid4 σ1 i PC ai ra w2 rb w3 NZ w4 Hcur) with "Hreg Hpc Hra Hrb Hnz") as "[%HPC [%Hra [%Hrb %HNZ]]]";eauto.
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
    rewrite /exec Hinstr (cmp_reg_ExecI σ1 ra w2 rb w3) /update_incr_PC /update_reg in Heqc2;eauto.
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    (* unchanged part *)
    rewrite_reg_all.
    rewrite Hcur.
    iFrame.
    (* updated part *)
    rewrite -> (update_offset_PC_update_PC1 _ i ai 1);eauto.
    rewrite update_reg_global_update_reg;[|solve_reg_lookup].
    + destruct (w2 <? w3),  (w3 <? w2).
      iDestruct ((gen_reg_update2_global σ1 PC i ai (ai +w 1) NZ i w4 two_word ) with "Hreg Hpc Hnz") as ">[Hreg [Hpc Hnz]]";eauto.
      by iFrame.
      iDestruct ((gen_reg_update2_global σ1 PC i ai (ai +w 1) NZ i w4 two_word ) with "Hreg Hpc Hnz") as ">[Hreg [Hpc Hnz]]";eauto.
      by iFrame.
      iDestruct ((gen_reg_update2_global σ1 PC i ai (ai +w 1) NZ i w4 zero_word ) with "Hreg Hpc Hnz") as ">[Hreg [Hpc Hnz]]";eauto.
      by iFrame.
      iDestruct ((gen_reg_update2_global σ1 PC i ai (ai +w 1) NZ i w4 one_word ) with "Hreg Hpc Hnz") as ">[Hreg [Hpc Hnz]]";eauto.
      by iFrame.
    + rewrite update_reg_global_update_reg;[|solve_reg_lookup].
      apply (get_reg_gmap_get_reg_Some _ _ _ i) in HPC;eauto.
      by simplify_map_eq /=.
Qed.

Lemma bne {instr i w1 w2 w3 q} ai ra :
  instr = Bne ra ->
  decode_instruction w1 = Some(instr) ->
  <<i>> ∗ PC @@ i ->r ai ∗ ai ->a w1 ∗ ra @@ i ->r w2 ∗ A@i:={q} (mm_translation ai) ∗ NZ @@ i ->r w3
    ⊢ SSWP ExecI @ i {{ (λ m, ⌜m = ExecI ⌝ ∗ <<i>> ∗ PC @@ i ->r (if w3 =? 1 then  (ai +w 1) else w2 ) ∗ ai ->a w1 ∗ ra @@ i ->r w2
                       ∗ A@i:={q} (mm_translation ai) ∗ NZ @@ i ->r w3 ) }}%I.
Proof.
  iIntros (Hinstr Hdecode) "(? & Hpc & Hapc & Hra & Hacc & Hnz )".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [ Hcur ]; clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(? & Hmem & Hreg & ? & ? & ? & Haccess & ?)".
  pose proof (decode_instruction_valid w1 instr Hdecode) as Hvalidinstr.
  rewrite Hinstr in Hvalidinstr.
  inversion Hvalidinstr as [ | | | | | | src Hvalidra|] .
  subst src .
  inversion Hvalidra as [ HneqPCa HneqNZa ].
  (* valid regs *)
  iDestruct ((gen_reg_valid3 σ1 i PC ai ra w2 NZ w3 Hcur HneqPCa) with "Hreg Hpc Hra Hnz") as "[%HPC [%Hra %HNZ]]";eauto.
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
    rewrite /exec Hinstr (bne_ExecI σ1 w3 ra w2 HneqPCa HneqNZa) /update_incr_PC /update_reg in Heqc2;eauto.
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    (* branch here*)
    destruct (decide ((fin_to_nat w3) = 1)) as [Heqb|Heqb];
      [apply <- Nat.eqb_eq in Heqb|apply <- Nat.eqb_neq in Heqb];
      rewrite Heqb;
    (* unchanged part *)
    rewrite_reg_all;
    rewrite Hcur;
    iFrame.
    (* updated part *)
    + rewrite -> (update_offset_PC_update_PC1 _ i ai 1);eauto.
      iDestruct ((gen_reg_update1_global σ1 PC i ai (ai +w 1)) with "Hreg Hpc") as ">[Hreg Hpc]";eauto.
      by iFrame.
      apply (get_reg_gmap_get_reg_Some _ _ _ i) in HPC;eauto.
    + rewrite update_reg_global_update_reg;[|solve_reg_lookup].
      iDestruct ((gen_reg_update1_global σ1 PC i ai w2 ) with "Hreg Hpc") as ">[Hreg Hpc]";eauto.
      by iFrame.
Qed.

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

Lemma halt {instr i w1 q} ai :
  instr = Halt ->
  decode_instruction w1 = Some(instr) ->
  <<i>> ∗ PC @@ i ->r ai ∗ ai ->a w1 ∗ A@i:={q} (mm_translation ai)
    ⊢ SSWP ExecI @ i {{ (λ m, ⌜m = HaltI ⌝ ∗ <<i>> ∗ PC @@ i ->r (ai +w 1)  ∗ ai ->a w1
                       ∗ A@i:={q} (mm_translation ai) ) }}%I.
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
    iDestruct ((gen_reg_update1_global σ1 PC i ai (ai +w 1)) with "Hreg Hpc") as ">[Hreg Hpc]";eauto.
    rewrite -> (update_offset_PC_update_PC1 _ i ai 1);eauto.
    by iFrame.
    apply (get_reg_gmap_get_reg_Some _ _ _ i) in HPC;eauto.
Qed.

Lemma fail {instr i w1 q} ai :
  instr = Fail ->
  decode_instruction w1 = Some(instr) ->
  <<i>> ∗ PC @@ i ->r ai ∗ ai ->a w1 ∗ A@i:={q} (mm_translation ai)
    ⊢ SSWP ExecI @ i {{ (λ m, ⌜m = FailI ⌝ ∗ <<i>> ∗ PC @@ i ->r ai  ∗ ai ->a w1
                       ∗ A@i:={q} (mm_translation ai) ) }}%I.
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
    rewrite /exec Hinstr /fail in Heqc2;eauto.
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    (* unchanged part *)
    by iFrame.
Qed.
Search fin.


Lemma eliminate_wrong_token {i j} :
  j ≠ i ->
  <<j>> ⊢ SSWP ExecI @ i {{ (λ m, ⌜False⌝) }}%I.
Proof.
  iIntros (Hne) "Htok".
  iApply (sswp_lift_atomic_step ExecI) ;[done|].
  iIntros (σ1) "%Hsche Hσ".
  iDestruct "Hσ" as "(Htokown & ? & ? & ? & ? & ? & ? & ?)".
  iDestruct (gen_token_valid_neq j i Hne with "Htok Htokown") as "%Hnsch".
  by exfalso.
Qed.


Lemma R0Av : 0 < reg_count.
Proof.
  solveRegCount.
Qed.

Lemma R1Av : 1 < reg_count.
Proof.
  solveRegCount.
Qed.

Lemma R2Av : 2 < reg_count.
Proof.
  solveRegCount.
Qed.

Lemma run {z i w1 w2 w3 q} ai :
  decode_instruction w1 = Some Hvc ->
  fin_to_nat z = 0 -> 
  decode_hvc_func w2 = Some Run ->
  decode_vmid w3 = Some i ->
  <<z>> ∗ PC @@ z ->r ai ∗ ai ->a w1 ∗ A@z :={q} (mm_translation ai)
  ∗ R 0 R0Av @@ z ->r w2
  ∗ R 1 R1Av @@ z ->r w3
  ⊢ SSWP ExecI @ z {{ (λ m, ⌜m = ExecI⌝ ∗
  <<i>> ∗ PC @@ z ->r (ai +w 1) ∗ ai ->a w1 ∗ A@z :={q} (mm_translation ai)
  ∗ R 0 R0Av @@ z ->r w2
  ∗ R 1 R1Av @@ z ->r w3) }}%I.
Proof.
  iIntros (Hinstr Hz Hhvc Hvmid) "(Htok & Hpc & Hapc & Hacc & Hr0 & Hr1)".
  iApply (sswp_lift_atomic_step ExecI); [done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [ Hcur ]; clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(Htokown & Hmemown & Hregown & ? & ? & ? & Haccessown & ?)".
  (* valid regs *)
  iDestruct (gen_reg_valid1 σ1 PC z ai Hcur with "Hregown Hpc") as "%Hpc".
  iDestruct (gen_reg_valid1 σ1 (R 0 R0Av) z w2 Hcur with "Hregown Hr0") as "%Hr0".
  iDestruct (gen_reg_valid1 σ1 (R 1 R1Av) z w3 Hcur with "Hregown Hr1") as "%Hr1".
  (* valid pt *)
  iDestruct (gen_access_valid_addr σ1 z q ai with "Haccessown Hacc") as %Hacc.
  (* valid mem *)
  iDestruct (gen_mem_valid σ1 ai w1 with "Hmemown Hapc") as "%Hmem".
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal z Hvc ai w1);eauto.
  - iModIntro.
    iIntros (m2 σ2 Hstep).
    apply (step_ExecI_normal z Hvc ai w1) in Hstep; eauto.
    remember (exec Hvc σ1) as c2 eqn:Heqc2.
    rewrite /exec /hvc in Heqc2; eauto.
    rewrite (nat_lt_pi 0 reg_count lang.hvc_obligation_1 R0Av) Hr0 Hhvc /run
      (nat_lt_pi 1 reg_count lang.run_obligation_1 R1Av) Hr1 in Heqc2.
    simpl in Heqc2.
    rewrite /unpack_hvc_result_yield Hvmid in Heqc2.
    simpl in Heqc2.
    rewrite /is_primary Hcur Hz in Heqc2.
    destruct (0 =? 0) eqn:Hvmz; [|done].
    destruct Hstep as [Hstep1 Hstep2].
    simplify_eq.
    simpl.
    rewrite /gen_vm_interp.
    rewrite update_current_vmid_preserve_mem update_current_vmid_preserve_reg update_current_vmid_preserve_tx update_current_vmid_preserve_rx update_current_vmid_preserve_owned update_current_vmid_preserve_access update_current_vmid_preserve_trans update_current_vmid_preserve_receivers.
    rewrite update_offset_PC_preserve_mem update_offset_PC_preserve_tx update_offset_PC_preserve_rx update_offset_PC_preserve_owned update_offset_PC_preserve_access update_offset_PC_preserve_trans update_offset_PC_preserve_receivers.
    iFrame.
    iDestruct ((gen_reg_update1_global σ1 PC (get_current_vm σ1) ai (ai +w 1)) with "Hregown Hpc") as "HpcUpd".
    iDestruct (token_update (get_current_vm σ1) i with "Htok") as "HtokUpd".
    rewrite token_agree_eq /token_agree_def.
    iDestruct ("HtokUpd" with "Htokown") as "Htok'". 
    rewrite /get_current_vm /update_current_vmid /update_incr_PC.
    simpl.
    rewrite ->(update_offset_PC_update_PC1 _ (get_current_vm σ1) ai 1); auto.
    + iMod "HpcUpd".
      iMod "Htok'".
      iModIntro.
      iDestruct "Htok'" as "[Htok1 Htok2]".
      iDestruct "HpcUpd" as "[? ?]".
      by iFrame.
    + apply get_reg_gmap_get_reg_Some; auto.
Qed.


Lemma yield {z i w1 w2 a_ b_ q} ai :
  decode_instruction w1 = Some Hvc ->
  fin_to_nat z = 0 -> 
  z ≠ i ->
  decode_hvc_func w2 = Some Yield ->
  <<i>> ∗ PC @@ i ->r ai ∗ ai ->a w1 ∗ A@i :={q} (mm_translation ai)
  ∗ R 0 R0Av @@ i ->r w2
  ∗ R 0 R0Av @@ z ->r a_
  ∗ R 1 R1Av @@ z ->r b_                                       
  ⊢ SSWP ExecI @ i {{ (λ m, ⌜m = ExecI⌝ ∗
  <<z>> ∗ PC @@ i ->r (ai +w 1) ∗ ai ->a w1 ∗ A@i :={q} (mm_translation ai)
  ∗ R 0 R0Av @@ i ->r w2
  ∗ R 0 R0Av @@ z ->r w2
  ∗ R 1 R1Av @@ z ->r (encode_vmid i)) }}%I.
Proof.
  iIntros (Hinstr Hz Hzi Hhvc) "(Htok & Hpc & Hapc & Hacc & Hr0 & Hr1' & Hr2')".
  iApply (sswp_lift_atomic_step ExecI); [done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [ Hcur ]; clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(Htokown & Hmemown & Hregown & ? & ? & ? & Haccessown & ?)".
  (* valid regs *)
  iDestruct (gen_reg_valid1 σ1 PC i ai Hcur with "Hregown Hpc") as "%Hpc".
  iDestruct (gen_reg_valid1 σ1 (R 0 R0Av) i w2 Hcur with "Hregown Hr0") as "%Hr0".
  (* valid pt *)
  iDestruct (gen_access_valid_addr σ1 i q ai with "Haccessown Hacc") as %Hacc.
  (* valid mem *)
  iDestruct (gen_mem_valid σ1 ai w1 with "Hmemown Hapc") as "%Hmem".
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal i Hvc ai w1);eauto.
  - iModIntro.
    iIntros (m2 σ2 Hstep).
    apply (step_ExecI_normal i Hvc ai w1) in Hstep; eauto.
    remember (exec Hvc σ1) as c2 eqn:Heqc2.
    rewrite /exec /hvc in Heqc2; eauto.
    rewrite (nat_lt_pi 0 reg_count lang.hvc_obligation_1 R0Av) Hr0 Hhvc /yield
      in Heqc2.
    rewrite (nat_lt_pi 0 reg_count lang.yield_obligation_1 R0Av)
            (nat_lt_pi 1 reg_count lang.yield_obligation_2 R1Av) in Heqc2.
    rewrite /is_primary /update_reg update_reg_global_preserve_current_vm Hcur in Heqc2.
    destruct (i =? 0) eqn:Hi0.
    + rewrite <-(reflect_iff (fin_to_nat i = 0) (i =? 0) (Nat.eqb_spec (fin_to_nat i) 0)) in Hi0.
      exfalso.
      apply Hzi.
      apply fin_to_nat_inj.
      rewrite Hz Hi0.
      reflexivity.
    + destruct Hstep as [Hstep1 Hstep2].
      simplify_eq.
      simpl.
      rewrite /gen_vm_interp.
      rewrite update_current_vmid_preserve_mem update_current_vmid_preserve_reg update_current_vmid_preserve_tx update_current_vmid_preserve_rx update_current_vmid_preserve_owned update_current_vmid_preserve_access update_current_vmid_preserve_trans update_current_vmid_preserve_receivers.
      rewrite update_offset_PC_preserve_mem update_offset_PC_preserve_tx update_offset_PC_preserve_rx update_offset_PC_preserve_owned update_offset_PC_preserve_access update_offset_PC_preserve_trans update_offset_PC_preserve_receivers.
      iFrame.
      iDestruct ((gen_reg_update1_global σ1 PC (get_current_vm σ1) ai (ai +w 1)) with "Hregown Hpc") as "HpcUpd".
      iDestruct (token_update (get_current_vm σ1) z with "Htok") as "HtokUpd".
      rewrite token_agree_eq /token_agree_def.
      iDestruct ("HtokUpd" with "Htokown") as "Htok'". 
      rewrite /get_current_vm /update_current_vmid /update_incr_PC.
      simpl.
      rewrite ->(update_offset_PC_update_PC1 _ (get_current_vm σ1) ai 1); auto.
      * iMod "HpcUpd".
        iMod "Htok'".
        iModIntro.
        iDestruct "Htok'" as "[Htok1 Htok2]".
        iDestruct "HpcUpd" as "[? ?]".
        admit.
      * apply get_reg_gmap_get_reg_Some; auto.
        admit.
Admitted.

End rules.
