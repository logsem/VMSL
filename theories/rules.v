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
  inversion Hvalidinstr as [imm dst Hvalidra | | | | | | ].
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
  inversion Hvalidinstr as [ | src dst Hvalidra Hvalidrb Hneqrarb  | | | | |] .
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

(* TODO: do we need a separate rule for reading from rx with ldr?
        - no we don't, just add TX@i = p and p ≠ (mm_translation a) *)
(* Lemma ldr_neq {i w1 w2 w3 q s p} ai a ra rb : *)
(*   decode_instruction w1 = Some(Ldr ra rb) -> *)
(*   ai ≠ a -> *)
(*   (mm_translation a) ≠ p ->  *)
(*   s = {[(mm_translation ai);(mm_translation a)]} -> *)
(*   TX@ i := p ∗ <<i>> ∗ PC @@ i ->r ai ∗ ai ->a w1 ∗ rb @@ i ->r a ∗ a ->a w2 ∗ A@i:={q}[s] ∗ ra @@ i ->r w3 *)
(*     ⊢ SSWP ExecI @ i {{ (λ m, ⌜m = ExecI ⌝ ∗ TX@ i := p ∗ <<i>> ∗ PC @@ i ->r (ai +w 1) ∗ ai ->a w1 ∗ rb @@ i ->r a ∗ a ->a w2 *)
(*                                       ∗ A@i:={q}[s] ∗ ra @@ i ->r w2 ) }}%I. *)
(* Proof. *)
(*   iIntros (Hinstr Hdecode HneqPCa HneqNZa HneqPCb HneqNZb Hneqab Hneqaia Hs) "(? & Hpc & Hapc & Hrb & Harb & Hacc & Hra )". *)
(*   iApply (sswp_lift_atomic_step ExecI);[done|]. *)
(*   iIntros (σ1) "%Hsche Hσ". *)
(*   inversion Hsche as [ Hcur ]; clear Hsche. *)
(*   apply fin_to_nat_inj in Hcur. *)
(*   iModIntro. *)
(*   iDestruct "Hσ" as "(? & Hmem & Hreg & ? & ? & ? & Haccess & ?)". *)
(*   (* valid regs *) *)
(*   iDestruct ((gen_reg_valid3 σ1 i PC ai ra w3 rb a Hcur HneqPCa HneqPCb Hneqab ) with "Hreg Hpc Hra Hrb") as "[%HPC [%Hra %Hrb]]". *)
(*   (* valid pt *) *)
(*   iDestruct ((gen_access_valid_addr2 σ1 i q s ai a Hs) with "Haccess Hacc") as "[%Hai %Ha]". *)
(*   (* valid mem *) *)
(*   iDestruct (gen_mem_valid2 σ1 ai w1 a w2 Hneqaia with "Hmem Hapc Harb ") as "[%Hmemai %Hmema]". *)
(*   iSplit. *)
(*   - (* reducible *) *)
(*     iPureIntro. *)
(*     apply (reducible_normal i instr ai w1);eauto. *)
(*   - (* step *) *)
(*     iModIntro. *)
(*     iIntros (m2 σ2) "%HstepP". *)
(*     apply (step_ExecI_normal i instr ai w1 ) in HstepP;eauto. *)
(*     remember (exec instr σ1) as c2 eqn:Heqc2. *)
(*     rewrite /exec Hinstr (ldr_ExecI σ1 ra rb a w2 HneqPCa HneqNZa HneqPCb HneqNZb Hrb _) /update_incr_PC /update_reg in Heqc2. *)
(*     2: { *)
(*       unfold get_memory. *)
(*       by rewrite Hcur Ha. *)
(*     } *)
(*     destruct HstepP;subst m2 σ2; subst c2; simpl. *)
(*     rewrite /gen_vm_interp. *)
(*     (* unchanged part *) *)
(*     rewrite_reg_all. *)
(*     rewrite Hcur. *)
(*     iFrame. *)
(*     (* updated part *) *)
(*     rewrite -> (update_offset_PC_update_PC1 _ i ai 1);eauto. *)
(*     + rewrite  update_reg_global_update_reg; [|eexists; rewrite get_reg_gmap_get_reg_Some; eauto ]. *)
(*       iDestruct ((gen_reg_update2_global σ1 PC i ai (ai +w 1) ra i w3 w2 ) with "Hreg Hpc Hra") as ">[Hσ [Hreg Hra]]";eauto. *)
(*       apply (get_reg_gmap_get_reg_Some _ _ _ i) in Hra;eauto. *)
(*       by iFrame. *)
(*     + rewrite update_reg_global_update_reg;[|solve_reg_lookup]. *)
(*       repeat solve_reg_lookup. *)
(*       intros P; symmetry in P;inversion P; contradiction. *)
(* Qed. *)

(* Lemma ldr_eq {i w1 w2 w3 q s instr} ai a ra: *)
(*   instr = Ldr ra ra -> *)
(*   decode_instruction w1 = Some(instr) -> *)
(*   PC ≠ ra -> *)
(*   NZ ≠ ra -> *)
(*   ai ≠ a -> *)
(*   s = {[(mm_translation ai);(mm_translation a)]} -> *)
(*   <<i>> ∗ PC @@ i ->r ai ∗ ai ->a w1 ∗ ra @@ i ->r a ∗ a ->a w2 ∗ A@i:={q}[s] *)
(*     ⊢ SSWP ExecI @ i {{ (λ m, ⌜m = ExecI ⌝ ∗ <<i>> ∗ PC @@ i ->r (ai +w 1) ∗ ai ->a w1 ∗ ra @@ i ->r w2 ∗ a ->a w2 *)
(*                                       ∗ A@i:={q}[s] ) }}%I. *)
(* Proof. *)
(*   iIntros (Hinstr Hdecode HneqPCa HneqNZa Hneqaia Hs) "(? & Hpc & Hapc & Hra & Hara & Hacc)". *)
(*   iApply (sswp_lift_atomic_step ExecI);[done|]. *)
(*   iIntros (σ1) "%Hsche Hσ". *)
(*   inversion Hsche as [ Hcur ]; clear Hsche. *)
(*   apply fin_to_nat_inj in Hcur. *)
(*   iModIntro. *)
(*   iDestruct "Hσ" as "(? & Hmem & Hreg & ? & ? & ? & Haccess & ?)". *)
(*   (* valid regs *) *)
(*   iDestruct ((gen_reg_valid2 σ1 i PC ai ra a Hcur HneqPCa) with "Hreg Hpc Hra ") as "[%HPC %Hra]". *)
(*   (* valid pt *) *)
(*   iDestruct ((gen_access_valid_addr2 σ1 i q s ai a Hs) with "Haccess Hacc") as "[%Hai %Ha]". *)
(*   (* valid mem *) *)
(*   iDestruct (gen_mem_valid2 σ1 ai w1 a w2 Hneqaia with "Hmem Hapc Hara ") as "[%Hmemai %Hmema]". *)
(*   iSplit. *)
(*   - (* reducible *) *)
(*     iPureIntro. *)
(*     apply (reducible_normal i instr ai w1);eauto. *)
(*   - (* step *) *)
(*     iModIntro. *)
(*     iIntros (m2 σ2) "%HstepP". *)
(*     apply (step_ExecI_normal i instr ai w1 ) in HstepP;eauto. *)
(*     remember (exec instr σ1) as c2 eqn:Heqc2. *)
(*     rewrite /exec Hinstr (ldr_ExecI σ1 ra ra a w2 HneqPCa HneqNZa HneqPCa HneqNZa Hra _) /update_incr_PC /update_reg in Heqc2. *)
(*     2: { *)
(*       unfold get_memory. *)
(*       by rewrite Hcur Ha. *)
(*     } *)
(*     destruct HstepP;subst m2 σ2; subst c2; simpl. *)
(*     rewrite /gen_vm_interp. *)
(*     (* unchanged part *) *)
(*     rewrite_reg_all. *)
(*     rewrite Hcur. *)
(*     iFrame. *)
(*     (* updated part *) *)
(*     rewrite -> (update_offset_PC_update_PC1 _ i ai 1);eauto. *)
(*     + rewrite  update_reg_global_update_reg; [|eexists; rewrite get_reg_gmap_get_reg_Some; eauto ]. *)
(*       iDestruct ((gen_reg_update2_global σ1 PC i ai (ai +w 1) ra i a w2 ) with "Hreg Hpc Hra") as ">[Hσ [Hreg Hra]]";eauto. *)
(*       apply (get_reg_gmap_get_reg_Some _ _ _ i) in Hra;eauto. *)
(*       by iFrame. *)
(*     + rewrite update_reg_global_update_reg;[|solve_reg_lookup]. *)
(*       repeat solve_reg_lookup. *)
(*       intros P; symmetry in P;inversion P; contradiction. *)
(* Qed. *)

(* TODO : add RX@i p and p ≠ (mm_translation a)*)
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
  inversion Hvalidinstr as [ |  | | src dst Hvalidra Hvalidrb Hneqrarb | | |] .
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

End rules.
