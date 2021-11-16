From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base.
From HypVeri.algebra Require Import base reg mem pagetable.
From HypVeri.lang Require Import lang_extra reg_extra.

Section halt.

Context `{hypparams: HypervisorParameters}.
Context `{vmG: !gen_VMG Σ}.
  
Lemma halt {E i w1 q s} ai :
  decode_instruction w1 = Some(Halt) ->
  to_pid_aligned ai ∈ s ->
  {SS{{▷ (PC @@ i ->r ai)
          ∗ ▷ (ai ->a w1)
          ∗ ▷ (A@i:={q}[s])}}}
    ExecI @ i ;E
 {{{ RET (false, HaltI);  PC @@ i ->r (ai ^+ 1)%f
                  ∗ ai ->a w1
                  ∗ A@i:={q}[s] }}}.
Proof.
  iIntros (Hdecode Hin ϕ) "(>Hpc & >Hapc & >Hacc) Hϕ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (n σ1) "%Hsche Hσ".
  rewrite /scheduled in Hsche.
  simpl in Hsche.
  rewrite /scheduler in Hsche.
  apply bool_decide_unpack in Hsche as Hcur.
  clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(#Hneq & Hmem & Hreg & Htx & Hrx1 & Hrx2 & Hown & Haccess & Hrest)".
  (* valid regs *)
  iDestruct ((gen_reg_valid1 PC i ai Hcur ) with "Hreg Hpc") as "%HPC";eauto.
  (* valid pt *)
  iDestruct ((gen_access_valid_addr_Set ai s) with "Haccess Hacc") as %Hacc;eauto.
  (* valid mem *)
  iDestruct (gen_mem_valid ai w1  with "Hmem Hapc") as %Hmem.
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
    rewrite_reg_pc.
    rewrite_reg_global.
    iFrame "Hmem Htx Hrx1 Hrx2 Hown Haccess Hrest".
    (* updated part *)
    iDestruct ((gen_reg_update1_global PC i ai (ai ^+ 1)%f) with "Hreg Hpc") as ">[Hreg Hpc]";eauto.
    rewrite -> (update_offset_PC_update_PC1 _ i ai 1);eauto.
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
      rewrite update_offset_PC_preserve_current_vm.
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
    rewrite update_offset_PC_preserve_current_vm.
    rewrite Hcur.
    rewrite bool_decide_eq_true.
    reflexivity.
    simpl.
    iApply ("Hϕ" with "[Hpc Hapc Hacc]").
    iFrame.
    apply (get_reg_gmap_get_reg_Some _ _ _ i) in HPC;eauto.
Qed.
End halt.
