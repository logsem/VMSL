From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base machine_extra.
From HypVeri.algebra Require Import base mem reg pagetable mailbox base_extra.
From HypVeri.lang Require Import lang_extra reg_extra.

Section sub.

Context `{hypparams: HypervisorParameters}.
Context `{vmG: !gen_VMG Σ}.

Lemma sub {i wi w1 w2 q p} ai ra rb s :
  decode_instruction wi = Some(Sub ra rb) ->
  tpa ai ∈ s ->
  tpa ai ≠ p ->
  {SS{{ ▷ (PC @@ i ->r ai) ∗
        ▷ (ai ->a wi) ∗
        ▷ (ra @@ i ->r w1) ∗
        ▷ (rb @@ i ->r w2) ∗
        ▷ (i -@{ q }A> s) ∗
        ▷ (TX@ i := p)}}}
    ExecI @ i
    {{{ RET (false, ExecI);
        PC @@ i ->r (ai ^+ 1)%f ∗
        ai ->a wi ∗
        ra @@ i ->r (w1 ^- (finz.to_z w2))%f ∗
        rb @@ i ->r w2 ∗
        (i -@{ q }A> s) ∗
        (TX@ i := p) }}}.
Proof.
  iIntros (Hdecode Hin Hne ϕ) "(>Hpc & >Hai & >Hra & >Hrb & >Hacc & >HTX) Hϕ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (n σ1) "%Hsche Hσ".
  rewrite /scheduled in Hsche.
  simpl in Hsche.
  rewrite /scheduler in Hsche.
  apply bool_decide_unpack in Hsche as Hcur.
  clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(#Hneq & Hmem & Hreg & Hmb & Hrx & Hown & Haccess & Hrest)".
  (* valid regs *)
  iDestruct ((gen_reg_valid3 i PC ai ra w1 rb w2 Hcur) with "Hreg Hpc Hra Hrb") as "[%HPC [%Hra %Hrb]]";eauto.
  (* valid pt *)
  iDestruct (access_agree_check_true (tpa ai) i with "Haccess Hacc") as "%Hai"; first set_solver.
  (* valid mem *)
  iDestruct (gen_mem_valid ai wi with "Hmem Hai") as %Hmem.
  iDestruct (mb_valid_tx i p with "Hmb HTX") as %Htx.
  set (instr := Sub ra rb).
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal i instr ai wi);eauto.
    by rewrite Htx.
  - (* step *)
    iModIntro.
    iIntros (m2 σ2) "[%P PAuth] %HstepP".
    apply (step_ExecI_normal i instr ai wi ) in HstepP;eauto.
    remember (exec instr σ1) as c2 eqn:Heqc2.
    pose proof (decode_instruction_valid wi _ Hdecode) as Hvalidinstr.
    inversion Hvalidinstr as [| | | | | | | ra' rb' Hvalidrb Hvalidra | | | |] .
    subst ra' rb'.
    inversion Hvalidra as [ HneqPCa HneqNZa ].
    inversion Hvalidrb as [ HneqPCb HneqNZb ].
    subst instr.
    rewrite /exec (sub_ExecI σ1 ra w1 rb w2) /update_incr_PC /update_reg in Heqc2;auto.
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
    rewrite (preserve_inv_trans_ps_disj σ1).
    rewrite p_upd_pc_mem p_upd_reg_mem.
    all: try rewrite p_upd_pc_pgt p_upd_reg_pgt //.
    all: try rewrite p_upd_pc_trans p_upd_reg_trans //.
    all: try rewrite p_upd_pc_mb p_upd_reg_mb //.
    rewrite Hcur. iFrame.
    (* updated part *)
    rewrite -> (u_upd_pc_regs _ i ai 1);eauto.
    rewrite u_upd_reg_regs.
    + iDestruct ((gen_reg_update2_global PC i ai (ai ^+ 1)%f ra i w1 (w1 ^- (finz.to_z w2))%f)
                   with "Hreg Hpc Hra") as ">[Hreg [Hpc Hra]]";eauto.
      iModIntro.
      iFrame.
      iSplitL "PAuth".
      by iExists P.
      rewrite /just_scheduled_vms.
      rewrite /just_scheduled.
      assert (filter
                (λ id : vmid,
                        base.negb (scheduled σ1 id) && scheduled (update_offset_PC (update_reg_global σ1 i ra (w1 ^- w2)%f) 1) id = true)
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
      iSimpl.
      iSplit; first done.
      iSplit; first done.
      assert ((scheduled (update_offset_PC (update_reg_global σ1 i ra (w1 ^- w2)%f) 1) i) = true) as ->.
      rewrite /scheduled.
      simpl.
      rewrite /scheduler.
      rewrite p_upd_pc_current_vm p_upd_reg_current_vm.
      rewrite Hcur.
      rewrite bool_decide_eq_true.
      reflexivity.
      simpl.
      iApply ("Hϕ" with "[Hpc Hai Hacc Hra Hrb HTX]").
      iFrame.
    + rewrite u_upd_reg_regs.
      apply (get_reg_gmap_get_reg_Some _ _ _ i) in HPC;eauto.
      rewrite lookup_insert_ne.
      by simplify_map_eq /=.
      congruence.
    + by rewrite Htx.
Qed.

End sub.
