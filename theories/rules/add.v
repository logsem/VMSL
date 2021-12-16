From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base.
From HypVeri.algebra Require Import base mem reg pagetable.
From HypVeri.lang Require Import lang_extra reg_extra.

Section add.

Context `{hypparams:HypervisorParameters}.
Context `{vmG: !gen_VMG Σ}.

Lemma add {E i wi w1 w2 q} ai ra rb s :
  decode_instruction wi = Some(Add ra rb) ->
  i ∈ s ->
  {SS{{ ▷ (PC @@ i ->r ai) ∗
        ▷ (ai ->a wi) ∗
        ▷ (ra @@ i ->r w1) ∗
        ▷ (rb @@ i ->r w2) ∗
        ▷ ((tpa ai) -@{q}A> [s])}}}
    ExecI @ i; E
    {{{ RET (false, ExecI);
        PC @@ i ->r (ai ^+ 1)%f ∗
        ai ->a wi ∗
        ra @@ i ->r (w1 ^+ (finz.to_z w2))%f ∗
        rb @@ i ->r w2 ∗
        ((tpa ai) -@{q}A> [s]) }}}.
Proof.
  iIntros (Hdecode Hin ϕ) "(>Hpc & >Hai & >Hra & >Hrb & >Hacc) Hϕ".
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
  (* valid regs *)
  iDestruct ((gen_reg_valid3 i PC ai ra w1 rb w2 Hcur) with "Hreg Hpc Hra Hrb") as "[%HPC [%Hra %Hrb]]";eauto.
  (* valid pt *)
  iDestruct (access_agree_check_true (tpa ai) i with "Haccess Hacc") as %Hacc;first set_solver + Hin.
  (* valid mem *)
  iDestruct (gen_mem_valid ai wi with "Hmem Hai") as %Hmem.
  set (instr := Add ra rb).
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal i instr ai wi);eauto.
  - (* step *)
    iModIntro.
    iIntros (m2 σ2) "[%P PAuth] %HstepP".
    apply (step_ExecI_normal i instr ai wi ) in HstepP;eauto.
    remember (exec instr σ1) as c2 eqn:Heqc2.
    pose proof (decode_instruction_valid wi instr Hdecode) as Hvalidinstr.
    inversion Hvalidinstr as [| | | | | | ra' rb' Hvalidrb Hvalidra | | | | |] .
    subst ra' rb'.
    inversion Hvalidra as [ HneqPCa HneqNZa ].
    inversion Hvalidrb as [ HneqPCb HneqNZb ].
    subst instr.
    rewrite /exec (add_ExecI σ1 ra w1 rb w2) /update_incr_PC /update_reg in Heqc2;auto.
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    (* unchanged part *)
    rewrite_reg_pc.
    rewrite_reg_global.
    rewrite Hcur.
    iFrame.
    (* updated part *)
    rewrite -> (update_offset_PC_update_PC1 _ i ai 1);eauto.
    rewrite update_reg_global_update_reg;[|solve_reg_lookup].
    + iDestruct ((gen_reg_update2_global PC i ai (ai ^+ 1)%f ra i w1 (w1 ^+ (finz.to_z w2))%f)
                   with "Hreg Hpc Hra") as ">[Hreg [Hpc Hra]]";eauto.
      iModIntro.
      iSplitL "PAuth".
      by iExists P.
      rewrite /just_scheduled_vms.
      rewrite /just_scheduled.
      assert (filter
                (λ id : vmid,
                        base.negb (scheduled σ1 id) && scheduled (update_offset_PC (update_reg_global σ1 i ra (w1 ^+ w2)%f) 1) id = true)
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
      assert ((scheduled (update_offset_PC (update_reg_global σ1 i ra (w1 ^+ w2)%f) 1) i) = true) as ->.
      rewrite /scheduled.
      simpl.
      rewrite /scheduler.
      rewrite update_offset_PC_preserve_current_vm.
      rewrite update_reg_global_preserve_current_vm.
      rewrite Hcur.
      rewrite bool_decide_eq_true.
      reflexivity.
      simpl.
      iApply ("Hϕ" with "[Hpc Hai Hacc Hra Hrb]").
      iFrame.
    + rewrite update_reg_global_update_reg;[|solve_reg_lookup].
      apply (get_reg_gmap_get_reg_Some _ _ _ i) in HPC;eauto.
      rewrite lookup_insert_ne.
      by simplify_map_eq /=.
      congruence.
Qed.

End add.
