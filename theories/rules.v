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
  

Lemma not_valid_pc {a i s} :
  (mm_translation a) ∉ s ->
  PC @@ i ->r a ∗ A@i:={1}[s]
  ⊢ SSWP ExecI @ i {{ (λ m, ⌜m = FailI⌝ ∗ PC @@ i ->r a ∗ (A@i:={q}[s] -∗ False)) }}%I.
Proof.
  iIntros (Hmm) "(Hpc & Ha)".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (σ1) "%Hsche Hσ1".
  inversion Hsche as [ Hcur ]; clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ1" as "(? & ? & Hreg & ? & ? & ? & Haccess & ?)".
  iDestruct (gen_reg_valid1 σ1 PC i a Hcur with "Hreg Hpc") as "%Hpc".
  (* TODO
  iDestruct (gen_access_valid_addr σ1 i q a with "Haccess Ha") as "%Hacc".
  iSplit.
  - iPureIntro.
    apply (reducible_normal i instr a w1);eauto.
*)
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
  s = {[(mm_translation ai);(mm_translation a)]} ->
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
  iDestruct ((gen_access_valid_addr2 σ1 i q s ai a Hs) with "Haccess Hacc") as "[%Hai %Ha]".
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


Lemma str {instr i w1 w2 w3 q s prx} ai a ra rb :
  instr = Str ra rb ->
  decode_instruction w1 = Some(instr) ->
  ai ≠ a ->
  prx ≠ (mm_translation a) ->
  s = {[(mm_translation ai);(mm_translation a)]} ->
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
  iDestruct ((gen_access_valid_addr2 σ1 i q s ai a Hs) with "Haccess Hacc") as "[%Hai %Ha]".
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
    rewrite update_memory_unsafe_preserve_reg.
    iDestruct ((gen_reg_update1_global σ1 PC i ai (ai +w 1)) with "Hreg Hpc") as ">[Hreg Hpc]";eauto.
    iDestruct ((gen_mem_update1 σ1 a w3 w2) with "Hmem Harb") as ">[Hmem Harb]";eauto.
    rewrite (update_memory_unsafe_update_mem _ a w2);eauto;
    rewrite update_offset_PC_preserve_mem;eauto.
    rewrite -> (update_offset_PC_update_PC1 _ i ai 1);eauto.
    by iFrame.
    apply (get_reg_gmap_get_reg_Some _ _ _ i) in HPC;eauto.
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


End rules.
