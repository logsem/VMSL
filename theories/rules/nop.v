From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.algebra Require Import base base_extra reg mem pagetable mailbox.
From HypVeri Require Import machine_extra lifting rules.rules_base.
From HypVeri.lang Require Import lang_extra reg_extra.

Section nop.

Context `{hypparams: HypervisorParameters}.
Context `{vmG: !gen_VMG Σ}.

Lemma nop {E i w1 q s p_tx} a :
  decode_instruction w1 = Some Nop ->
  (tpa a) ∈ s ->
  (tpa a) ≠ p_tx ->
  {SS{{ ▷ (PC @@ i ->r a)
        ∗ ▷ (a ->a w1)
        ∗ ▷ (i -@{ q }A> s)
        ∗ ▷ (TX@ i := p_tx)}}}
    ExecI @ i ; E
  {{{ RET (false, ExecI); PC @@ i ->r (a ^+ 1)%f
                  ∗ a ->a w1
                  ∗ i -@{ q }A> s
                  ∗ TX@ i := p_tx}}}.
Proof.
  iIntros (Hdecode Hin Hnottx ϕ) "(>Hpc & >Hapc & >Hacc & >tx) Hϕ".
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
  inversion Hvalidinstr as [| | | | | | | | | | |].
  (* valid regs *)
  iDestruct ((gen_reg_valid1 PC i a Hcur) with "Hreg Hpc") as "%HPC".
  (* valid pt *)
  iDestruct (access_agree_check_true with "Haccess Hacc") as %Hacc;first exact Hin.
  iDestruct (mb_valid_tx with "Hmb tx") as %Htx.
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
    rewrite /exec /nop /update_incr_PC in Heqc2.
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
    rewrite p_upd_pc_mem.
    all: try rewrite p_upd_pc_pgt //.
    all: try rewrite p_upd_pc_trans //.
    all: try rewrite p_upd_pc_mb //.
    iFrame.
    (* updated part *)
    rewrite -> (u_upd_pc_regs _ i a 1); eauto.
    + iDestruct ((gen_reg_update1_global PC i a (a ^+ 1)%f) with "Hreg Hpc") as ">[Hσ Hreg]"; eauto.
      iModIntro.
      iFrame "Hσ".
      iSplitL "PAuth".
      * by iExists P.
      * iSplitL "".
        rewrite /just_scheduled_vms /just_scheduled.
        assert (filter
                  (λ id : vmid,
                          base.negb (scheduled σ1 id) &&
                          scheduled (update_offset_PC σ1 1) id = true)
                  (seq 0 n) = []) as ->.
        {
          rewrite /scheduled /machine.scheduler //= /scheduler Hcur.
          rewrite p_upd_pc_current_vm.
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
        assert ((scheduled (update_offset_PC σ1 1) i) = true) as ->.
        {
          rewrite /scheduled /machine.scheduler //= /scheduler.
          rewrite p_upd_pc_current_vm.
          rewrite Hcur.
          by case_bool_decide.
        }
        simpl.
        iApply "Hϕ".
        iFrame.
    + solve_reg_lookup.
Qed.

End nop.
