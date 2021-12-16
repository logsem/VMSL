From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base.
From HypVeri Require Import base mem reg pagetable.
From HypVeri.lang Require Import lang_extra reg_extra.

Section bne.

Context `{hypparams: HypervisorParameters}.
Context `{vmG: !gen_VMG Σ}.

Lemma bne {E i w1 w2 w3 q s} ai ra :
  decode_instruction w1 = Some(Bne ra) ->
  i ∈ s ->
  {SS{{ ▷ (PC @@ i ->r ai) ∗
        ▷ (ai ->a w1) ∗
        ▷ (ra @@ i ->r w2) ∗
        ▷ ((tpa ai) -@{q}A> [s]) ∗
        ▷ (NZ @@ i ->r w3)
  }}} ExecI @ i; E
                   {{{ RET (false, ExecI); (PC @@ i ->r (if (w3 =? W1)%f then  (ai ^+ 1)%f else w2))
                                           ∗ (ai ->a w1)
                                           ∗ (ra @@ i ->r w2)
                                           ∗ ((tpa ai) -@{q}A> [s])
                                           ∗ NZ @@ i ->r w3 }}}.
Proof.
  iIntros (Hdecode Hin ϕ) "(>Hpc & >Hapc & >Hra & >Hacc & >Hnz ) Hϕ".
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
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal i instr ai w1);eauto.
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
    destruct  (w3 =? W1)%f;
      simpl;
    (* unchanged part *)
      [rewrite_reg_pc| rewrite_reg_global];
      simpl;
    (* rewrite Hcur; *)
    iFrame.
    (* updated part *)
    + rewrite -> (update_offset_PC_update_PC1 _ i ai 1);eauto.
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
      iApply ("Hϕ" with "[Hpc Hapc Hacc Hra Hnz]").
      iFrame.
      apply (get_reg_gmap_get_reg_Some _ _ _ i) in HPC;eauto.
    + rewrite ->update_reg_global_update_reg; [|solve_reg_lookup].
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
      iSplit; first done.
      assert ((scheduled (update_reg_global σ1 i PC w2) i) = true) as ->.
      rewrite /scheduled.
      simpl.
      rewrite /scheduler.
      rewrite update_reg_global_preserve_current_vm.
      rewrite Hcur.
      rewrite bool_decide_eq_true.
      reflexivity.
      simpl.
      iApply ("Hϕ" with "[Hpc Hapc Hacc Hra Hnz]").
      iFrame.
Qed.

End bne.
