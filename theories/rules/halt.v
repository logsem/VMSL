From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base.
From HypVeri.algebra Require Import base reg mem pagetable mailbox base_extra.
From HypVeri.lang Require Import lang_extra reg_extra.

Section halt.

Context `{hypparams: HypervisorParameters}.
Context `{vmG: !gen_VMG Σ}.
  
Lemma halt {E i w1 q s p_tx} ai :
  decode_instruction w1 = Some(Halt) ->
  (tpa ai) ∈ s ->
  (tpa ai) ≠ p_tx ->
  {SS{{▷ (PC @@ i ->r ai)
          ∗ ▷ (ai ->a w1)
          ∗ ▷ (i -@{q}A> s)
          ∗ ▷ (TX@i := p_tx)}}}
    ExecI @ i ;E
 {{{ RET (false, HaltI);  PC @@ i ->r (ai ^+ 1)%f
                  ∗ ai ->a w1
                  ∗ i -@{q}A> s
                  ∗ TX@i := p_tx}}}.
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
  iDestruct "Hσ" as "(#Hneq & Hmem & Hreg & Hmb & ? & Hown & Haccess & Hrest)".
  (* valid regs *)
  iDestruct ((gen_reg_valid1 PC i ai Hcur ) with "Hreg Hpc") as "%HPC";eauto.
  (* valid pt *)
  iDestruct (access_agree_check_true (tpa ai) i with "Haccess Hacc") as %Hacc;first auto.
  iDestruct (mb_valid_tx with "Hmb tx") as %Htx.
  subst p_tx.
  (* valid mem *)
  iDestruct (gen_mem_valid ai w1 with "Hmem Hapc") as %Hmem.
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal i Halt ai w1);eauto.
  - (* step *)
    iModIntro.
    iIntros (m2 σ2) "[%P PAuth] %HstepP".
    apply (step_ExecI_normal i Halt ai w1 ) in HstepP;eauto.
    remember (exec Halt σ1) as c2 eqn:Heqc2.
    rewrite /exec /halt /update_incr_PC in Heqc2;eauto.
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
    all: try rewrite p_upd_pc_pgt //.
    all: try rewrite p_upd_pc_trans //.
    all: try rewrite p_upd_pc_mb //.
    rewrite p_upd_pc_mem.
    iFrame.
    (* updated part *)
    iDestruct ((gen_reg_update1_global PC i ai (ai ^+ 1)%f) with "Hreg Hpc") as ">[Hreg Hpc]";eauto.
    rewrite -> (u_upd_pc_regs _ i ai 1);eauto.
    iModIntro.
    iFrame "Hreg".
    iSplitL "PAuth".
    by iExists P.
    iFrame.
    iSplit; first done.
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
    assert ((scheduled (update_offset_PC σ1 1) i) = true) as ->.
    rewrite /scheduled.
    simpl.
    rewrite /scheduler.
    rewrite p_upd_pc_current_vm.
    rewrite Hcur.
    rewrite bool_decide_eq_true.
    reflexivity.
    simpl.
    iApply "Hϕ".
    iFrame.
    apply (get_reg_gmap_get_reg_Some _ _ _ i) in HPC;eauto.
Qed.
End halt.
