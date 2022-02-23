From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base machine_extra.
From HypVeri Require Import base mem reg pagetable mailbox base_extra.
From HypVeri.lang Require Import lang_extra reg_extra.

Section bne.

Context `{hypparams: HypervisorParameters}.
Context `{vmG: !gen_VMG Σ}.

Lemma bne {E i w1 w2 w3 q s p} ai ra :
  decode_instruction w1 = Some(Bne ra) ->
  tpa ai ∈ s ->
  tpa ai ≠ p ->
  {SS{{ ▷ (PC @@ i ->r ai) ∗
        ▷ (ai ->a w1) ∗
        ▷ (ra @@ i ->r w2) ∗
        ▷ (i -@{q}A> s) ∗
        ▷ (NZ @@ i ->r w3) ∗
        ▷ (TX@ i := p)
  }}} ExecI @ i; E
                   {{{ RET (false, ExecI); (PC @@ i ->r (if (w3 =? W1)%f then  (ai ^+ 1)%f else w2))
                                           ∗ (ai ->a w1)
                                           ∗ (ra @@ i ->r w2)
                                           ∗ (i -@{q}A> s)
                                           ∗ NZ @@ i ->r w3
                                           ∗ (TX@ i := p)}}}.
Proof.
  iIntros (Hdecode Hin Hne ϕ) "(>Hpc & >Hapc & >Hra & >Hacc & >Hnz & >HTX) Hϕ".
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
  set (instr:= Bne ra).
  pose proof (decode_instruction_valid w1 instr Hdecode) as Hvalidinstr.
  inversion Hvalidinstr as [| | | | | | | | | src Hvalidra| |].
  subst src .
  inversion Hvalidra as [ HneqPCa HneqNZa ].
  (* valid regs *)
  iDestruct ((gen_reg_valid3 i PC ai ra w2 NZ w3 Hcur) with "Hreg Hpc Hra Hnz") as "[%HPC [%Hra %HNZ]]";eauto.
  (* valid pt *)
  iDestruct (access_agree_check_true (tpa ai) i with "Haccess Hacc") as %Hacc;first set_solver + Hin.
  (* valid mem *)
  iDestruct (gen_mem_valid ai w1  with "Hmem Hapc") as %Hmem.
  iDestruct (mb_valid_tx i p with "Hmb HTX") as %Htx.
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal i instr ai w1);eauto.
    by rewrite Htx.
  - (* step *)
    iModIntro.
    iIntros (m2 σ2) "[%P PAuth] %HstepP".
    apply (step_ExecI_normal i instr ai w1 ) in HstepP;eauto.
    remember (exec (Bne ra) σ1) as c2 eqn:Heqc2.
    rewrite /exec /instr (bne_ExecI σ1 w3 ra w2 HneqPCa HneqNZa) /update_incr_PC /update_reg in Heqc2;eauto.    
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    rewrite /bne //=.
    rewrite Hra.
    rewrite HNZ.
    rewrite /update_incr_PC /update_reg.
    (* branch here*)
    destruct ra; try done; simpl.
    destruct  (w3 =? W1)%f; simpl.
    (* updated part *)
    + rewrite (preserve_get_mb_gmap σ1).
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
      all: try rewrite p_upd_pc_trans //.    
      all: try rewrite p_upd_pc_pgt //.    
      all: try rewrite p_upd_pc_mb //.
      iFrame.
      rewrite -> (u_upd_pc_regs _ i ai 1);eauto.
      iDestruct ((gen_reg_update1_global PC i ai (ai ^+ 1)%f) with "Hreg Hpc") as ">[Hreg Hpc]";eauto.
      iModIntro.      
      iFrame.
      iSplitL "PAuth".
      by iExists P.
      rewrite /just_scheduled_vms.
      rewrite /just_scheduled.
      assert (filter
                (λ id : vmid,
                        base.negb (scheduled σ1 id) && scheduled (update_offset_PC σ1 1) id = true)
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
      iSimpl.
      iSplit; first done.
      iSplit; first done.
      assert ((scheduled (update_offset_PC σ1 1) i) = true) as ->.
      rewrite /scheduled.
      simpl.
      rewrite /scheduler.
      rewrite p_upd_pc_current_vm.
      rewrite Hcur.
      rewrite bool_decide_eq_true.
      reflexivity.
      simpl.
      iApply ("Hϕ" with "[Hpc Hapc Hacc Hra Hnz HTX]").
      iFrame.
      apply (get_reg_gmap_get_reg_Some _ _ _ i) in HPC;eauto.
    + rewrite (preserve_get_mb_gmap σ1).
      rewrite (preserve_get_rx_gmap σ1).
      rewrite (preserve_get_own_gmap σ1).
      rewrite (preserve_get_access_gmap σ1).
      rewrite (preserve_get_excl_gmap σ1).
      rewrite (preserve_get_trans_gmap σ1).
      rewrite (preserve_get_hpool_gset σ1).
      rewrite (preserve_get_retri_gmap σ1).
      rewrite (preserve_inv_trans_pgt_consistent σ1).
      rewrite (preserve_inv_trans_wellformed σ1).
      all: try rewrite p_upd_reg_pgt //.
      all: try rewrite p_upd_reg_trans //.
      all: try rewrite p_upd_reg_mb //.
      iFrame.
      rewrite ->u_upd_reg_regs.
      iDestruct ((gen_reg_update1_global PC i ai w2 ) with "Hreg Hpc") as ">[Hreg Hpc]";eauto.
      iModIntro.
      rewrite /update_reg.
      rewrite Hcur.
      iFrame.
      iSplitL "PAuth".
      by iExists P.
      rewrite /just_scheduled_vms.
      rewrite /just_scheduled.
      assert (filter
                (λ id : vmid,
                        base.negb (scheduled σ1 id) && scheduled (update_reg_global σ1 i PC w2) id = true)
                (seq 0 n) = []) as ->.
      {
        rewrite /scheduled /machine.scheduler //= /scheduler Hcur.
        rewrite p_upd_reg_current_vm.
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
      assert ((scheduled (update_reg_global σ1 i PC w2) i) = true) as ->.
      rewrite /scheduled.
      simpl.
      rewrite /scheduler.
      rewrite p_upd_reg_current_vm.
      rewrite Hcur.
      rewrite bool_decide_eq_true.
      reflexivity.
      simpl.
      iApply ("Hϕ" with "[Hpc Hapc Hacc Hra Hnz HTX]").
      iFrame.
    + by rewrite Htx.
Qed.

End bne.
