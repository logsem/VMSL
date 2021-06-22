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
    rewrite -> update_offset_PC_preserve_current_vm , -> update_reg_global_preserve_current_vm;
    rewrite -> update_offset_PC_preserve_mem , -> update_reg_global_preserve_mem;
      rewrite -> update_offset_PC_preserve_tx , -> update_reg_global_preserve_tx;
      rewrite -> update_offset_PC_preserve_rx , -> update_reg_global_preserve_rx;
      rewrite -> update_offset_PC_preserve_owned , -> update_reg_global_preserve_owned;
      rewrite -> update_offset_PC_preserve_access , -> update_reg_global_preserve_access;
      rewrite -> update_offset_PC_preserve_trans , -> update_reg_global_preserve_trans;
      rewrite -> update_offset_PC_preserve_receivers , -> update_reg_global_preserve_receivers
  end.

Ltac solve_reg_lookup :=
  match goal with
  | _ : get_reg ?σ ?r = Some ?w |- get_reg_gmap ?σ !! (?r, ?i) = Some ?w => rewrite get_reg_gmap_get_reg_Some;eauto
  | _ : get_reg ?σ ?r = Some ?w |- is_Some (get_reg_gmap ?σ !! (?r, ?i)) => eexists;rewrite get_reg_gmap_get_reg_Some;eauto
  | _ : get_reg ?σ ?r1 = Some ?w, _ : ?r1 ≠ ?r2 |- <[(?r2, ?i):= ?w2]>(get_reg_gmap ?σ) !! (?r1, ?i) = Some ?w =>
    rewrite lookup_insert_ne; eauto
  end.


Lemma mov_word {i w1 w3 q} a w2 ra :
  decode_instruction w1 = Some(Mov ra (inl w2)) ->
  <<i>> ∗ PC @@ i ->r a ∗ a ->a w1 ∗ A@i:={q} (mm_translation a) ∗ ra @@ i ->r w3
    ⊢ SSWP ExecI @ i {{ (λ m, ⌜m = ExecI ⌝ ∗ <<i>> ∗ PC @@ i ->r (a +w 1)∗ a ->a w1 ∗ A@i:={q} (mm_translation a) ∗ ra @@ i ->r w2) }}%I.
Proof.
  iIntros (Hdecode) "(? & Hpc & Hapc & Hacc & Hra)".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [ Hcur ]; clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(H1 & Hmem & Hreg & ? & ? & ? & Haccess & H2)".
  pose proof (decode_instruction_valid w1 (Mov ra (inl w2)) Hdecode) as H.
  inversion H as [| ? ? H' | | | | |].
  inversion H; subst; clear H.
  destruct H' as [H1' H2'].
  (* valid regs *)
  assert (PCne : PC ≠ ra); auto.
  assert (NZne : NZ ≠ ra); auto.
  iDestruct ((gen_reg_valid2 σ1 (get_current_vm σ1) PC a ra w3 eq_refl PCne) with "Hreg Hpc Hra") as "[%HPC %Hra]".
  (* valid pt *)
  iDestruct (gen_access_valid_addr σ1 (get_current_vm σ1) q a with "Haccess Hacc") as %Hacc.
  (* valid mem *)
  iDestruct (gen_mem_valid σ1 a w1 with "Hmem Hapc") as "%Hmem".
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal (get_current_vm σ1) (Mov ra (inl w2)) a w1);eauto.
  - (* step *)
    iModIntro.
    iIntros (m2 σ2) "%HstepP".
    apply (step_ExecI_normal (get_current_vm σ1) (Mov ra (inl w2)) a w1) in HstepP;eauto.
    remember (exec (Mov ra (inl w2)) σ1) as c2 eqn:Heqc2.
    rewrite /exec (mov_word_ExecI σ1 ra _ PCne NZne)  /update_incr_PC /update_reg  in Heqc2.
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    (* unchanged part *)
    rewrite_reg_all.
    iFrame.
    (* updated part *)
    rewrite -> (update_offset_PC_update_PC1 _ (get_current_vm σ1) a 1);eauto.
    + rewrite  update_reg_global_update_reg; [|eexists; rewrite get_reg_gmap_get_reg_Some; eauto ].
      iDestruct ((gen_reg_update2_global σ1 PC (get_current_vm σ1) a (a +w 1) ra (get_current_vm σ1) w3 w2 ) with "Hreg Hpc Hra") as ">[Hσ Hreg]";eauto.
        by iFrame.
    + rewrite update_reg_global_update_reg;[|solve_reg_lookup].
      repeat solve_reg_lookup.
      intros P; symmetry in P;inversion P; contradiction.
    Qed.

Lemma mov_reg_neq {i w1 w3 q} a w2 ra rb :
  decode_instruction w1 = Some(Mov ra (inr rb)) ->
  <<i>> ∗ PC @@ i ->r a ∗ a ->a w1 ∗ A@i:={q} (mm_translation a) ∗ ra @@ i ->r w2 ∗ rb @@ i ->r w3
    ⊢ SSWP ExecI @ i {{ (λ m, ⌜m = ExecI ⌝ ∗ <<i>> ∗ PC @@ i ->r (a +w 1)∗ a ->a w1 ∗ A@i:={q} (mm_translation a) ∗ ra @@ i ->r w3 ∗ rb @@ i ->r w3) }}%I.
Proof.
  iIntros (Hdecode) "(? & Hpc & Hapc & Hacc & Hra & Hrb)".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [ Hcur ]; clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  pose proof (decode_instruction_valid w1 (Mov ra (inr rb)) Hdecode) as H.
  inversion H as [H' H'' H1 H2 H3 H''' | | | | | |]; subst; clear H.
  inversion H1; subst; clear H1.
  inversion H2; subst; clear H2.
  iDestruct "Hσ" as "(? & Hmem & Hreg & ? & ? & ? & Haccess & H2)".
  (* valid regs *)
  assert (PCne : PC ≠ ra); auto.
  assert (NZne : NZ ≠ ra); auto.
  assert (PCne' : PC ≠ rb); auto.
  assert (NZne' : NZ ≠ rb); auto.
  assert (Hneqab : ra ≠ rb); auto.
  iDestruct ((gen_reg_valid3 σ1 (get_current_vm σ1) PC a ra w2 rb w3 eq_refl PCne PCne' Hneqab) with "Hreg Hpc Hra Hrb") as "[%HPC [%Hra %Hrb]]".
  (* valid pt *)
  iDestruct (gen_access_valid_addr σ1 (get_current_vm σ1) q a with "Haccess Hacc") as %Hacc.
  (* valid mem *)
  iDestruct (gen_mem_valid σ1 a w1 with "Hmem Hapc") as "%Hmem".
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal (get_current_vm σ1) (Mov ra (inr rb)) a w1);eauto.
  - (* step *)
    iModIntro.
    iIntros (m2 σ2) "%HstepP".
    apply (step_ExecI_normal (get_current_vm σ1) (Mov ra (inr rb)) a w1) in HstepP;eauto.
    remember (exec (Mov ra (inr rb)) σ1) as c2 eqn:Heqc2.
    rewrite /exec (mov_reg_ExecI σ1 ra rb w3 PCne NZne PCne' NZne' Hrb)  /update_incr_PC /update_reg  in Heqc2.
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    (* unchanged part *)
    rewrite_reg_all.
    iFrame.
    (* updated part *)
    rewrite -> (update_offset_PC_update_PC1 _ (get_current_vm σ1) a 1);eauto.
    + rewrite  update_reg_global_update_reg; [|eexists; rewrite get_reg_gmap_get_reg_Some; eauto ].
      iDestruct ((gen_reg_update2_global σ1 PC (get_current_vm σ1) a (a +w 1) ra (get_current_vm σ1) w2 w3 ) with "Hreg Hpc Hra") as ">[Hσ Hreg]";eauto.
      by iFrame.
    + rewrite update_reg_global_update_reg;[|solve_reg_lookup].
      repeat solve_reg_lookup.
      intros P; symmetry in P;inversion P; contradiction.
    Qed.

(* XXX: do we need a separate rule for reading from rx with ldr?
        - no we don't, just add TX@i = p and p ≠ (mm_translation a) *)
Lemma ldr_neq {i w1 w2 w3 q s p} ai a ra rb :
  decode_instruction w1 = Some(Ldr ra rb) ->
  ai ≠ a ->
  (mm_translation a) ≠ p -> 
  s = {[(mm_translation ai);(mm_translation a)]} ->
  TX@ i := p ∗ <<i>> ∗ PC @@ i ->r ai ∗ ai ->a w1 ∗ rb @@ i ->r a ∗ a ->a w2 ∗ A@i:={q}[s] ∗ ra @@ i ->r w3
    ⊢ SSWP ExecI @ i {{ (λ m, ⌜m = ExecI ⌝ ∗ TX@ i := p ∗ <<i>> ∗ PC @@ i ->r (ai +w 1) ∗ ai ->a w1 ∗ rb @@ i ->r a ∗ a ->a w2
                                      ∗ A@i:={q}[s] ∗ ra @@ i ->r w2 ) }}%I.
Proof.
  iIntros (Hinstr Hdecode HneqPCa HneqNZa HneqPCb HneqNZb Hneqab Hneqaia Hs) "(? & Hpc & Hapc & Hrb & Harb & Hacc & Hra )".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [ Hcur ]; clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(? & Hmem & Hreg & ? & ? & ? & Haccess & ?)".
  (* valid regs *)
  iDestruct ((gen_reg_valid3 σ1 i PC ai ra w3 rb a Hcur HneqPCa HneqPCb Hneqab ) with "Hreg Hpc Hra Hrb") as "[%HPC [%Hra %Hrb]]".
  (* valid pt *)
  iDestruct ((gen_access_valid_addr2 σ1 i q s ai a Hs) with "Haccess Hacc") as "[%Hai %Ha]".
  (* valid mem *)
  iDestruct (gen_mem_valid2 σ1 ai w1 a w2 Hneqaia with "Hmem Hapc Harb ") as "[%Hmemai %Hmema]".
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal i instr ai w1);eauto.
  - (* step *)
    iModIntro.
    iIntros (m2 σ2) "%HstepP".
    apply (step_ExecI_normal i instr ai w1 ) in HstepP;eauto.
    remember (exec instr σ1) as c2 eqn:Heqc2.
    rewrite /exec Hinstr (ldr_ExecI σ1 ra rb a w2 HneqPCa HneqNZa HneqPCb HneqNZb Hrb _) /update_incr_PC /update_reg in Heqc2.
    2: {
      unfold get_memory.
      by rewrite Hcur Ha.
    }
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    (* unchanged part *)
    rewrite_reg_all.
    rewrite Hcur.
    iFrame.
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

Lemma ldr_eq {i w1 w2 w3 q s instr} ai a ra:
  instr = Ldr ra ra ->
  decode_instruction w1 = Some(instr) ->
  PC ≠ ra ->
  NZ ≠ ra ->
  ai ≠ a ->
  s = {[(mm_translation ai);(mm_translation a)]} ->
  <<i>> ∗ PC @@ i ->r ai ∗ ai ->a w1 ∗ ra @@ i ->r a ∗ a ->a w2 ∗ A@i:={q}[s]
    ⊢ SSWP ExecI @ i {{ (λ m, ⌜m = ExecI ⌝ ∗ <<i>> ∗ PC @@ i ->r (ai +w 1) ∗ ai ->a w1 ∗ ra @@ i ->r w2 ∗ a ->a w2
                                      ∗ A@i:={q}[s] ) }}%I.
Proof.
  iIntros (Hinstr Hdecode HneqPCa HneqNZa Hneqaia Hs) "(? & Hpc & Hapc & Hra & Hara & Hacc)".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [ Hcur ]; clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(? & Hmem & Hreg & ? & ? & ? & Haccess & ?)".
  (* valid regs *)
  iDestruct ((gen_reg_valid2 σ1 i PC ai ra a Hcur HneqPCa) with "Hreg Hpc Hra ") as "[%HPC %Hra]".
  (* valid pt *)
  iDestruct ((gen_access_valid_addr2 σ1 i q s ai a Hs) with "Haccess Hacc") as "[%Hai %Ha]".
  (* valid mem *)
  iDestruct (gen_mem_valid2 σ1 ai w1 a w2 Hneqaia with "Hmem Hapc Hara ") as "[%Hmemai %Hmema]".
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal i instr ai w1);eauto.
  - (* step *)
    iModIntro.
    iIntros (m2 σ2) "%HstepP".
    apply (step_ExecI_normal i instr ai w1 ) in HstepP;eauto.
    remember (exec instr σ1) as c2 eqn:Heqc2.
    rewrite /exec Hinstr (ldr_ExecI σ1 ra ra a w2 HneqPCa HneqNZa HneqPCa HneqNZa Hra _) /update_incr_PC /update_reg in Heqc2.
    2: {
      unfold get_memory.
      by rewrite Hcur Ha.
    }
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    (* unchanged part *)
    rewrite_reg_all.
    rewrite Hcur.
    iFrame.
    (* updated part *)
    rewrite -> (update_offset_PC_update_PC1 _ i ai 1);eauto.
    + rewrite  update_reg_global_update_reg; [|eexists; rewrite get_reg_gmap_get_reg_Some; eauto ].
      iDestruct ((gen_reg_update2_global σ1 PC i ai (ai +w 1) ra i a w2 ) with "Hreg Hpc Hra") as ">[Hσ [Hreg Hra]]";eauto.
      apply (get_reg_gmap_get_reg_Some _ _ _ i) in Hra;eauto.
      by iFrame.
    + rewrite update_reg_global_update_reg;[|solve_reg_lookup].
      repeat solve_reg_lookup.
      intros P; symmetry in P;inversion P; contradiction.
Qed.



End rules.
