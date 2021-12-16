From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.algebra Require Import base reg mem pagetable.
From HypVeri Require Import lifting rules.rules_base.
From HypVeri.lang Require Import lang_extra reg_extra.

Section mult.

Context `{hypparams:HypervisorParameters}.
Context `{vmG: !gen_VMG Σ}.

Lemma mult_word {E i w1 w3 q s} a w2 ra :
  decode_instruction w1 = Some(Mult ra w2) ->
  i ∈ s ->
  {SS{{  ▷ (PC @@ i ->r a)
         ∗ ▷ (a ->a w1)
         ∗ ▷ ((tpa a) -@{q}A> [s])
         ∗ ▷ (ra @@ i ->r w3)}}}
    ExecI @ i ; E
  {{{ RET (false, ExecI);  (PC @@ i ->r (a ^+ 1)%f)
                           ∗ (a ->a w1)
                           ∗ ((tpa a) -@{q}A> [s])
                           ∗ ra @@ i ->r (w3 ^* w2)%f }}}.
Proof.
  iIntros (Hdecode Hin ϕ) "( >Hpc & >Hapc & >Hacc & >Hra) Hϕ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (n σ1) "%Hsche Hσ".
  rewrite /scheduled in Hsche.
  simpl in Hsche.
  rewrite /scheduler in Hsche.
  apply bool_decide_unpack in Hsche as Hcur.
  clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(Hn & Hmem & Hreg & Hrx & Hown & Hownmb & Haccess & Hres)".
  set (instr := Mult ra w2).
  pose proof (decode_instruction_valid w1 instr Hdecode) as Hvalidinstr.
  inversion Hvalidinstr as [| | | | | | | |imm dst Hvalidra  | | |].
  subst imm dst.
  inversion Hvalidra as [HneqPC HneqNZ].
  (* valid regs *)
  iDestruct ((gen_reg_valid2 i PC a ra w3 Hcur) with "Hreg Hpc Hra") as "[%HPC %Hra]".
  (* valid pt *)
  iDestruct (access_agree_check_true (tpa a) i with "Haccess Hacc") as %Hacc;first set_solver + Hin.
  (* valid mem *)
  iDestruct (gen_mem_valid a w1 with "Hmem Hapc") as %Hmem.
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal i instr a w1);eauto.
  - (* step *)
    iModIntro.
    iIntros (m2 σ2) "[%P PAuth] %HstepP".
    apply (step_ExecI_normal i instr a w1) in HstepP;eauto.
    remember (exec instr σ1) as c2 eqn:Heqc2.
    subst instr.
    rewrite /exec (mult_word_ExecI σ1 ra w3 w2 HneqPC HneqNZ) /update_incr_PC /update_reg  in Heqc2.
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    (* unchanged part *)
    rewrite_reg_pc.
    rewrite_reg_global.
    rewrite Hcur. iFrame.
    (* updated part *)
    rewrite -> (update_offset_PC_update_PC1 _ i a 1);eauto.
    + rewrite  update_reg_global_update_reg; [|eexists; rewrite get_reg_gmap_get_reg_Some; eauto ].
      iDestruct ((gen_reg_update2_global PC i a (a ^+ 1)%f ra i w3 (w3 ^* w2)%f ) with "Hreg Hpc Hra") as ">[Hσ Hreg]";eauto.
      iModIntro.
      iSplitL "PAuth".
      by iExists P.
      rewrite /just_scheduled_vms.
      rewrite /just_scheduled.
      assert (filter
                (λ id : vmid,
                        base.negb (scheduled σ1 id) && scheduled (update_offset_PC (update_reg_global σ1 i ra (w3 ^* w2)%f) 1) id = true)
                (seq 0 n) = []) as ->.
      {
        rewrite /scheduled /machine.scheduler //= /scheduler Hcur.        
        rewrite update_offset_PC_preserve_current_vm.
        rewrite update_reg_global_preserve_current_vm.
        rewrite Hcur.
        induction n.
        - simpl.
          rewrite filter_nil //=.
        - rewrite seq_S.
          rewrite filter_app.
          rewrite IHn.
          simpl.
          rewrite filter_cons_False //=.
          rewrite andb_negb_l.
          done.
      }
      iSimpl.
      iFrame.
      iSplit; first done.
      assert ((scheduled (update_offset_PC (update_reg_global σ1 i ra (w3 ^* w2)%f) 1) i) = true) as ->.
      rewrite /scheduled.
      simpl.
      rewrite /scheduler.
      rewrite update_offset_PC_preserve_current_vm.
      rewrite update_reg_global_preserve_current_vm.
      rewrite Hcur.
      rewrite bool_decide_eq_true.
      reflexivity.
      simpl.
      iApply ("Hϕ" with "[Hapc Hacc Hreg]").
      iFrame.
      iFrame.
    + rewrite update_reg_global_update_reg;[|solve_reg_lookup].
      repeat solve_reg_lookup.
      intros P'; symmetry in P';inversion P'; contradiction.
    + done.
Qed.
End mult.
