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
  PC ≠ ra ->
  NZ ≠ ra ->
  <<i>> ∗ PC @@ i ->r a ∗ a ->a w1 ∗ A@i:={q} (mm_translation a) ∗ ra @@ i ->r w3
    ⊢ SSWP ExecI @ i {{ (λ m, ⌜m = ExecI ⌝ ∗ <<i>> ∗ PC @@ i ->r (a +w 1)∗ a ->a w1 ∗ A@i:={q} (mm_translation a) ∗ ra @@ i ->r w2) }}%I.
Proof.
  iIntros (Hdecode HneqPC HneqNZ) "(? & Hpc & Hapc & Hacc & Hra)".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [ Hcur ]; clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(H1 & Hmem & Hreg & ? & ? & ? & Haccess & H2)".
  (* valid regs *)
  iDestruct ((gen_reg_valid2 σ1 i PC a ra w3 Hcur HneqPC) with "Hreg Hpc Hra") as "[%HPC %Hra]".
  (* valid pt *)
  iDestruct (gen_access_valid_addr σ1 i q a with "Haccess Hacc") as %Hacc.
  (* valid mem *)
  iDestruct (gen_mem_valid σ1 a w1 with "Hmem Hapc") as "%Hmem".
  iSplit.
  - (* reducible *)
    iPureIntro.
    remember (exec (Mov ra (inl w2)) σ1) as ex.
    exists ex.1, ex.2.
    unfold prim_step.
    apply step_exec_normal with a w1 (Mov ra (inl w2));subst i;eauto.
    + rewrite /is_valid_PC HPC /=.
      by rewrite Hacc.
    + by rewrite /get_memory Hacc.
  - (* step *)
    iModIntro.
    iIntros (m2 σ2) "%HstepP".
    inversion HstepP as
        [ σ1' Hnotvalid
        | σ1'  ? ? ? ? Hvalid Hreg2 Hmem2 Hdecode2 Hexec Hcontrol];
      simplify_eq /=;[| remember (get_current_vm σ1) as i eqn: Heqi].
    + (*Fail*)
      by rewrite /is_valid_PC //= HPC Hacc in  Hnotvalid.
    + (* Normal. *)
      (* eliminate Hmem2 *)
      rewrite /get_memory -Heqi Hacc /get_memory_unsafe Hmem in Hmem2 .
      inversion Hmem2;subst w1; clear Hmem2.
      (* eliminate Hdecode2 *)
      rewrite Hdecode in Hdecode2;inversion Hdecode2;subst i0; clear Hdecode2.
      remember (exec (Mov ra (inl w2)) σ1) as c2 eqn:Heqc2.
      rewrite /gen_vm_interp.
      rewrite /exec (mov_word_ExecI σ1 ra _ HneqPC HneqNZ)  /update_incr_PC /update_reg  in Heqc2.
      subst c2; simpl.
      (* unchanged part *)
      rewrite_reg_all.
      rewrite -Heqi.
      iFrame.
      (* updated part *)
      rewrite -> (update_offset_PC_update_PC1 _ i a 1);eauto.
      * rewrite  update_reg_global_update_reg; [|eexists; rewrite get_reg_gmap_get_reg_Some; eauto ].
        iDestruct ((gen_reg_update2_global σ1 PC i a (a +w 1) ra i w3 w2 ) with "Hreg Hpc Hra") as ">[Hσ Hreg]";eauto.
         by iFrame.
      * rewrite update_reg_global_update_reg;[|solve_reg_lookup].
        repeat solve_reg_lookup.
        intros P; symmetry in P;inversion P; contradiction.
    Qed.

Lemma mov_reg_neq {i w1 w3 q} a w2 ra rb :
  decode_instruction w1 = Some(Mov ra (inr rb)) ->
  PC ≠ ra ->
  NZ ≠ ra ->
  PC ≠ rb ->
  NZ ≠ rb ->
  ra ≠ rb ->
  <<i>> ∗ PC @@ i ->r a ∗ a ->a w1 ∗ A@i:={q} (mm_translation a) ∗ ra @@ i ->r w2 ∗ rb @@ i ->r w3
    ⊢ SSWP ExecI @ i {{ (λ m, ⌜m = ExecI ⌝ ∗ <<i>> ∗ PC @@ i ->r (a +w 1)∗ a ->a w1 ∗ A@i:={q} (mm_translation a) ∗ ra @@ i ->r w3 ∗ rb @@ i ->r w3) }}%I.
Proof.
  iIntros (Hdecode HneqPCa HneqNZa HneqPCb HneqNZb Hneqab) "(? & Hpc & Hapc & Hacc & Hra & Hrb)".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [ Hcur ]; clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(? & Hmem & Hreg & ? & ? & ? & Haccess & H2)".
  (* valid regs *)
  iDestruct ((gen_reg_valid3 σ1 i PC a ra w2 rb w3 Hcur HneqPCa HneqPCb Hneqab) with "Hreg Hpc Hra Hrb") as "[%HPC [%Hra %Hrb]]".
  (* valid pt *)
  iDestruct (gen_access_valid_addr σ1 i q a with "Haccess Hacc") as %Hacc.
  (* valid mem *)
  iDestruct (gen_mem_valid σ1 a w1 with "Hmem Hapc") as "%Hmem".
  iSplit.
  - (* reducible *)
    iPureIntro.
    remember (exec (Mov ra (inr rb)) σ1) as ex.
    exists ex.1, ex.2.
    unfold prim_step.
    apply step_exec_normal with a w1 (Mov ra (inr rb));subst i;eauto.
    + rewrite /is_valid_PC HPC /=.
      by rewrite Hacc.
    + by rewrite /get_memory Hacc.
  - (* step *)
    iModIntro.
    iIntros (m2 σ2) "%HstepP".
    inversion HstepP as
        [ σ1' Hnotvalid
        | σ1'  ? ? ? ? Hvalid Hreg2 Hmem2 Hdecode2 Hexec Hcontrol];
      simplify_eq /=;[| remember (get_current_vm σ1) as i eqn: Heqi].
    + (*Fail*)
      by rewrite /is_valid_PC //= HPC Hacc in  Hnotvalid.
    + (* Normal. *)
      (* eliminate Hmem2 *)
      rewrite /get_memory -Heqi Hacc /get_memory_unsafe Hmem in Hmem2 .
      inversion Hmem2;subst w1; clear Hmem2.
      (* eliminate Hdecode2 *)
      rewrite Hdecode in Hdecode2;inversion Hdecode2;subst i0; clear Hdecode2.
      remember (exec (Mov ra (inr rb)) σ1) as c2 eqn:Heqc2.
      rewrite /gen_vm_interp.
      rewrite /exec (mov_reg_ExecI σ1 ra rb w3 HneqPCa HneqNZa HneqPCb HneqNZb Hrb)  /update_incr_PC /update_reg  in Heqc2.
      subst c2; simpl.
      (* unchanged part *)
      rewrite_reg_all.
      rewrite -Heqi.
      iFrame.
      (* updated part *)
      rewrite -> (update_offset_PC_update_PC1 _ i a 1);eauto.
      * rewrite  update_reg_global_update_reg; [|eexists; rewrite get_reg_gmap_get_reg_Some; eauto ].
        iDestruct ((gen_reg_update2_global σ1 PC i a (a +w 1) ra i w2 w3 ) with "Hreg Hpc Hra") as ">[Hσ Hreg]";eauto.
         by iFrame.
      * rewrite update_reg_global_update_reg;[|solve_reg_lookup].
        repeat solve_reg_lookup.
        intros P; symmetry in P;inversion P; contradiction.
    Qed.

Lemma mov_reg_eq {i w1 w3 q} a w2 ra :
  decode_instruction w1 = Some(Mov ra (inr ra)) ->
  PC ≠ ra ->
  NZ ≠ ra ->
  <<i>> ∗ PC @@ i ->r a ∗ a ->a w1 ∗ A@i:={q} (mm_translation a) ∗ ra @@ i ->r w2
    ⊢ SSWP ExecI @ i {{ (λ m, ⌜m = ExecI ⌝ ∗ <<i>> ∗ PC @@ i ->r (a +w 1)∗ a ->a w1 ∗ A@i:={q} (mm_translation a) ∗ ra @@ i ->r w2 ) }}%I.
Proof.
  iIntros (Hdecode HneqPCa HneqNZa) "(? & Hpc & Hapc & Hacc & Hra )".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [ Hcur ]; clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(? & Hmem & Hreg & ? & ? & ? & Haccess & H2)".
  (* valid regs *)
  iDestruct ((gen_reg_valid2 σ1 i PC a ra w2  Hcur HneqPCa ) with "Hreg Hpc Hra") as "[%HPC %Hra]".
  (* valid pt *)
  iDestruct (gen_access_valid_addr σ1 i q a with "Haccess Hacc") as %Hacc.
  (* valid mem *)
  iDestruct (gen_mem_valid σ1 a w1 with "Hmem Hapc") as "%Hmem".
  iSplit.
  - (* reducible *)
    iPureIntro.
    remember (exec (Mov ra (inr ra)) σ1) as ex.
    exists ex.1, ex.2.
    unfold prim_step.
    apply step_exec_normal with a w1 (Mov ra (inr ra));subst i;eauto.
    + rewrite /is_valid_PC HPC /=.
      by rewrite Hacc.
    + by rewrite /get_memory Hacc.
  - (* step *)
    iModIntro.
    iIntros (m2 σ2) "%HstepP".
    inversion HstepP as
        [ σ1' Hnotvalid
        | σ1'  ? ? ? ? Hvalid Hreg2 Hmem2 Hdecode2 Hexec Hcontrol];
      simplify_eq /=;[| remember (get_current_vm σ1) as i eqn: Heqi].
    + (*Fail*)
      by rewrite /is_valid_PC //= HPC Hacc in  Hnotvalid.
    + (* Normal. *)
      (* eliminate Hmem2 *)
      rewrite /get_memory -Heqi Hacc /get_memory_unsafe Hmem in Hmem2 .
      inversion Hmem2;subst w1; clear Hmem2.
      (* eliminate Hdecode2 *)
      rewrite Hdecode in Hdecode2;inversion Hdecode2;subst i0; clear Hdecode2.
      remember (exec (Mov ra (inr ra)) σ1) as c2 eqn:Heqc2.
      rewrite /gen_vm_interp.
      rewrite /exec (mov_reg_ExecI σ1 ra ra w2 HneqPCa HneqNZa HneqPCa HneqNZa Hra)  /update_incr_PC /update_reg  in Heqc2.
      subst c2; simpl.
      (* unchanged part *)
      rewrite_reg_all.
      rewrite -Heqi.
      iFrame.
      (* updated part *)
      rewrite -> (update_offset_PC_update_PC1 _ i a 1);eauto.
      * rewrite  update_reg_global_update_reg; [|eexists; rewrite get_reg_gmap_get_reg_Some; eauto ].
        iDestruct ((gen_reg_update1_global σ1 PC i a (a +w 1) ) with "Hreg Hpc") as ">[Hσ Hreg]";eauto.
        apply (get_reg_gmap_get_reg_Some _ _ _ i Heqi) in Hra.
        rewrite (insert_id _ (ra,i) w2 Hra).
          by iFrame.
      * rewrite update_reg_global_update_reg;[|solve_reg_lookup].
        repeat solve_reg_lookup.
        intros P; symmetry in P;inversion P; contradiction.
    Qed.


(* XXX: do we need a separate rule for reading from rx with ldr? *)
Lemma ldr_neq_norm {i w1 w2 w3 q s} ai a ra rb :
  decode_instruction w1 = Some(Ldr ra rb) ->
  PC ≠ ra ->
  NZ ≠ ra ->
  PC ≠ rb ->
  NZ ≠ rb ->
  ra ≠ rb ->
  s = {[(mm_translation ai);(mm_translation a)]} ->
  <<i>> ∗ PC @@ i ->r ai ∗ ai ->a w1 ∗ rb @@ i ->r a ∗ a ->a w2 ∗ A@i:={q}[s] ∗ ra @@ i ->r w3
    ⊢ SSWP ExecI @ i {{ (λ m, ⌜m = ExecI ⌝ ∗ <<i>> ∗ PC @@ i ->r (ai +w 1) ∗ ai ->a w1 ∗ rb @@ i ->r a ∗ a ->a w2
                                      ∗ A@i:={q}[s] ∗ ra @@ i ->r w2 ) }}%I.
Proof.
  iIntros (Hdecode HneqPCa HneqNZa HneqPCb HneqNZb Hneqab Hs) "(? & Hpc & Hapc & Hrb & Harb & Hacc & Hra )".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [ Hcur ]; clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(? & Hmem & Hreg & ? & ? & ? & Haccess & ?)".
  (* valid regs *)
  iDestruct ((gen_reg_valid3 σ1 i PC ai ra w3 rb a Hcur HneqPCa HneqPCb Hneqab ) with "Hreg Hpc Hra Hrb") as "[%HPC [%Hra %Hrb]]".
  (* valid pt *)
  Admitted.
  (* TODO: gen_access_valid_addr2, ai =? a doesn't matter? *))



End rules.
