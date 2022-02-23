From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.algebra Require Import base reg mem pagetable mailbox base_extra.
From HypVeri Require Import machine_extra lifting rules.rules_base.
From HypVeri.lang Require Import lang_extra reg_extra.

Section mov.

Context `{hypparams: HypervisorParameters}.
Context `{vmG: !gen_VMG Σ}.

Lemma mov_word {E i w1 w3 q s p_tx} a w2 ra :
  decode_instruction w1 = Some (Mov ra (inl w2)) ->
  (tpa a) ∈ s ->
  (tpa a) ≠ p_tx ->
  {SS{{ ▷ (PC @@ i ->r a)
        ∗ ▷ (a ->a w1)
        ∗ ▷ (i -@{ q }A> s)
        ∗ ▷ TX@ i := p_tx
        ∗ ▷ (ra @@ i ->r w3)}}}
    ExecI @ i ; E
  {{{ RET (false, ExecI);  (PC @@ i ->r (a ^+ 1)%f)
                           ∗ (a ->a w1)
                           ∗ (i -@{ q }A> s)
                           ∗ TX@ i := p_tx
                           ∗ ra @@ i ->r w2 }}}.
Proof.
  iIntros (Hdecode Hin Hnottx ϕ) "( >Hpc & >Hapc & >Hacc & >Htx & >Hra) Hϕ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (n σ1) "%Hsche Hσ".
  rewrite /scheduled in Hsche.
  simpl in Hsche.
  rewrite /scheduler in Hsche.
  apply bool_decide_unpack in Hsche as Hcur.
  clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(H1 & Hmem & Hreg & Hmb & ? & ? & Haccess & H2)".
  pose proof (decode_instruction_valid w1 _ Hdecode) as Hvalidinstr.
  inversion Hvalidinstr as [imm dst Hvalidra | | | | | | | | | | |].
  subst imm dst.
  inversion Hvalidra as [HneqPC HneqNZ].
  (* valid regs *)
  iDestruct ((gen_reg_valid2 i PC a ra w3 Hcur) with "Hreg Hpc Hra") as "[%HPC %Hra]".
  (* valid pt *)  
  iDestruct (access_agree_check_true _ i with "Haccess Hacc") as %Hacc;eauto.
  iDestruct (mb_valid_tx i p_tx with "Hmb Htx") as %Htx.
  subst p_tx.
  (* valid mem *)
  iDestruct (gen_mem_valid a w1 with "Hmem Hapc") as "%Hmem".
  iSplit.
  - (* reducible *)
    iPureIntro.
    eapply (reducible_normal i _ a w1); eauto.
  - (* step *)
    iModIntro.
    iIntros (m2 σ2) "[%P PAuth] %HstepP".
    eapply (step_ExecI_normal i _ a w1) in HstepP;eauto.
    remember (exec _ σ1) as c2 eqn:Heqc2.
    rewrite /exec (mov_word_ExecI σ1 ra _ HneqPC HneqNZ) /update_incr_PC /update_reg in Heqc2.
    destruct HstepP; subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    (* unchanged part *)
    rewrite (preserve_get_mb_gmap σ1).
    rewrite (preserve_get_rx_gmap σ1).
    rewrite (preserve_get_own_gmap σ1).
    rewrite (preserve_get_access_gmap σ1).
    rewrite (preserve_get_excl_gmap σ1).
    rewrite (preserve_get_trans_gmap σ1).
    rewrite (preserve_get_hpool_gset σ1).
    rewrite (preserve_get_retri_gmap σ1).
    rewrite (preserve_inv_trans_pgt_consistent σ1).
    rewrite (preserve_inv_trans_wellformed σ1).
    rewrite p_upd_pc_mem p_upd_reg_mem.
    all: try rewrite p_upd_pc_pgt p_upd_reg_pgt //.
    all: try rewrite p_upd_pc_trans p_upd_reg_trans //.
    all: try rewrite p_upd_pc_mb p_upd_reg_mb //.
    rewrite Hcur. iFrame.
    (* updated part *)
    rewrite -> (u_upd_pc_regs _ i a 1); eauto.
    + rewrite u_upd_reg_regs.
      iDestruct ((gen_reg_update2_global PC i a (a ^+ 1)%f ra i w3 w2 ) with "Hreg Hpc Hra") as ">[Hreg [pc ra]]"; eauto.
      iModIntro.
      iFrame "Hreg".
      iSplitL "PAuth".
      by iExists P.
      rewrite /just_scheduled_vms /just_scheduled.
      assert (filter
                (λ id : vmid,
                        base.negb (scheduled σ1 id) &&
                        scheduled (update_offset_PC (update_reg_global σ1 i ra w2) 1) id = true)
                (seq 0 n) = []) as ->.
      {
        rewrite /scheduled /machine.scheduler //= /scheduler Hcur.
        rewrite p_upd_pc_current_vm p_upd_reg_current_vm.
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
      iSplitL "";first done.
      assert ((scheduled (update_offset_PC (update_reg_global σ1 i ra w2) 1) i) = true) as ->.
      {
        rewrite /scheduled /machine.scheduler //= /scheduler.
        rewrite p_upd_pc_current_vm p_upd_reg_current_vm.
        rewrite Hcur.
        by case_bool_decide.
      }
      simpl.
      iApply "Hϕ".
      iFrame "Hapc Hacc pc ra Htx".
    + rewrite u_upd_reg_regs.
      repeat solve_reg_lookup.
      intros Q; symmetry in Q; inversion Q; contradiction.
    Qed.

Lemma mov_reg {E i w1 w3 q s p_tx} a w2 ra rb :
  decode_instruction w1 = Some (Mov ra (inr rb)) ->
  (tpa a) ∈ s ->
  (tpa a) ≠ p_tx ->
  {SS{{  ▷ (PC @@ i ->r a)
         ∗ ▷ (a ->a w1)
         ∗ ▷ (i -@{ q }A> s)
         ∗ ▷ (TX@ i := p_tx)
         ∗ ▷ (ra @@ i ->r w2)
         ∗ ▷ (rb @@ i ->r w3) }}}
    ExecI @ i ;E
  {{{ RET (false, ExecI); PC @@ i ->r (a ^+ 1)%f
                   ∗ a ->a w1
                   ∗ i -@{ q }A> s
                   ∗ TX@ i := p_tx
                   ∗ ra @@ i ->r w3
                   ∗ rb @@ i ->r w3}}}.
Proof.
  iIntros (Hdecode Hin Hnottx ϕ) "(>Hpc & >Hapc & >Hacc & >tx & >Hra & >Hrb) Hϕ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (n σ1) "%Hsche Hσ".
  rewrite /scheduled in Hsche.
  simpl in Hsche.
  rewrite /scheduler in Hsche.
  apply bool_decide_unpack in Hsche as Hcur.
  clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  pose proof (decode_instruction_valid w1 _ Hdecode) as Hvalidinstr.
  inversion Hvalidinstr as [ | src dst Hvalidra Hvalidrb Hneqrarb | | | | | | | | | |] .
  subst src dst.
  inversion Hvalidra as [ HneqPCa HneqNZa ].
  inversion Hvalidrb as [ HneqPCb HneqNZb ].
  iDestruct "Hσ" as "(Htok & Hmem & Hreg & Hmb & ? & ? & Haccess & ?)".
  (* valid regs *)
  iDestruct ((gen_reg_valid3 i PC a ra w2 rb w3 Hcur) with "Hreg Hpc Hra Hrb") as "[%HPC [%Hra %Hrb]]".
  (* valid pt *)
  iDestruct (access_agree_check_true _ i with "Haccess Hacc") as %Hacc;eauto.
  iDestruct (mb_valid_tx i p_tx with "Hmb tx") as %Htx.
  subst p_tx.
  (* valid mem *)
  iDestruct (gen_mem_valid a w1 with "Hmem Hapc") as "%Hmem".
  iSplit.
  - (* reducible *)
    iPureIntro.
    eapply (reducible_normal i _ a w1);eauto.
  - (* step *)
    iModIntro.
    iIntros (m2 σ2) "[%P PAuth] %HstepP".
    eapply (step_ExecI_normal i _ a w1) in HstepP;eauto.
    remember (exec _ σ1) as c2 eqn:Heqc2.
    rewrite /exec (mov_reg_ExecI σ1 ra rb w3 HneqPCa HneqNZa HneqPCb HneqNZb Hrb)  /update_incr_PC /update_reg  in Heqc2.
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    (* unchanged part *)
    rewrite (preserve_get_mb_gmap σ1).
    rewrite (preserve_get_rx_gmap σ1).
    rewrite (preserve_get_own_gmap σ1).
    rewrite (preserve_get_access_gmap σ1).
    rewrite (preserve_get_excl_gmap σ1).
    rewrite (preserve_get_trans_gmap σ1).
    rewrite (preserve_get_hpool_gset σ1).
    rewrite (preserve_get_retri_gmap σ1).
    rewrite (preserve_inv_trans_pgt_consistent σ1).
    rewrite (preserve_inv_trans_wellformed σ1).
    rewrite p_upd_pc_mem p_upd_reg_mem.
    all: try rewrite p_upd_pc_pgt p_upd_reg_pgt //.
    all: try rewrite p_upd_pc_trans p_upd_reg_trans //.
    all: try rewrite p_upd_pc_mb p_upd_reg_mb //.
    rewrite Hcur. iFrame.
    (* updated part *)
    rewrite -> (u_upd_pc_regs _ i a 1);eauto.
    + rewrite u_upd_reg_regs.
      iDestruct ((gen_reg_update2_global PC i a (a ^+ 1)%f ra i w2 w3 ) with "Hreg Hpc Hra") as ">(Hreg & pc & ra)";eauto.
      iModIntro.
      iFrame "Hreg".
      iSplitL "PAuth".
      by iExists P.
      iSplitL "".
      rewrite /just_scheduled_vms /just_scheduled.
      assert (filter
                (λ id : vmid,
                        base.negb (scheduled σ1 id) &&
                        scheduled (update_offset_PC (update_reg_global σ1 i ra w3) 1) id = true)
                (seq 0 n) = []) as ->.
      {
        rewrite /scheduled /machine.scheduler //= /scheduler Hcur.
        rewrite p_upd_pc_current_vm p_upd_reg_current_vm.
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
      by iSimpl.
      assert ((scheduled (update_offset_PC (update_reg_global σ1 i ra w3) 1) i) = true) as ->.
      {
        rewrite /scheduled /machine.scheduler //= /scheduler.
        rewrite p_upd_pc_current_vm p_upd_reg_current_vm.
        rewrite Hcur.
        by case_bool_decide.
      }
      simpl.
      iApply "Hϕ".
      by iFrame "Hapc Hacc Hrb ra pc".
    + rewrite u_upd_reg_regs.
      repeat solve_reg_lookup.
      intros P'; symmetry in P';inversion P'; contradiction.
Qed.

End mov.
