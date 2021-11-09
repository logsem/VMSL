From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base.
From HypVeri.algebra Require Import base reg mem pagetable.
From HypVeri.lang Require Import lang_extra reg_extra current_extra.
Require Import stdpp.fin.

Section run.

Context `{hypparams:HypervisorParameters}.
  
Context `{vmG: !gen_VMG Σ}.
  
Lemma run {z w1 w2 w3 q s E R R' Q P P'} ai i :
  let T := (▷ (PC @@ z ->r ai)
            ∗ ▷ (ai ->a w1)
            ∗ ▷ (A@z :={q}[s] )
            ∗ ▷ (R0 @@ z ->r w2)
            ∗ ▷ (R1 @@ z ->r w3))%I
  in
  let T' := ((PC @@ z ->r (ai ^+ 1)%f)
               ∗ (ai ->a w1)
               ∗ (A@z :={q}[s])
               ∗ (R0 @@ z ->r w2)
               ∗ (R1 @@ z ->r w3))%I
  in
  decode_instruction w1 = Some Hvc ->
  to_pid_aligned ai ∈ s ->
  fin_to_nat z = 0 -> 
  decode_hvc_func w2 = Some Run ->
  decode_vmid w3 = Some i ->
  {SS{{ T ∗ ▷ (VMProp i (Q ∗ VMProp z P' (1/2)%Qp) (1/2)%Qp)
          ∗ ▷ (VMProp z P 1%Qp)
          ∗ ▷ (T' ∗ R -∗ (Q ∗ R')) 
          ∗ ▷ R }}}
    ExecI @ z ;E
    {{{ RET (true, ExecI); R' ∗ VMProp z P' (1/2)%Qp}}}.
Proof.
  simpl.
  iIntros (Hdecode Hin Hz Hhvc Hvmid ϕ) "[(>Hpc & >Hapc & >Hacc & >Hr0 & >Hr1) (HPropi & HPropz & Himpl & HR)] Hϕ".
  iApply (sswp_lift_atomic_step ExecI); [done|].
  iIntros (n σ1) "%Hsche Hσ".
  rewrite /scheduled in Hsche.
  simpl in Hsche.
  rewrite /scheduler in Hsche.
  apply bool_decide_unpack in Hsche as Hcur.
  clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(%Hneq & Hmemown & Hregown & Htx & Hrx1 & Hrx2 & Hown & Haccessown & Hrest)".
  (* valid regs *)
  iDestruct (gen_reg_valid1 PC z ai Hcur with "Hregown Hpc") as "%Hpc".
  iDestruct (gen_reg_valid1 R0 z w2 Hcur with "Hregown Hr0") as "%Hr0".
  iDestruct (gen_reg_valid1 R1 z w3 Hcur with "Hregown Hr1") as "%Hr1".
  (* valid pt *)
  iDestruct (gen_access_valid_addr_Set ai s with "Haccessown Hacc") as %Hacc;eauto.
  (* valid mem *)
  iDestruct (gen_mem_valid ai w1 with "Hmemown Hapc") as "%Hmem".
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal z Hvc ai w1);eauto.
  - iModIntro.
    iIntros (m2 σ2) "[%U PAuth] %HstepP".
    apply (step_ExecI_normal z Hvc ai w1) in HstepP; eauto.
    remember (exec Hvc σ1) as c2 eqn:Heqc2.
    rewrite /exec /hvc in Heqc2; eauto.
    rewrite  Hr0 Hhvc /run Hr1 in Heqc2.
    simpl in Heqc2.
    rewrite /unpack_hvc_result_yield Hvmid in Heqc2.
    simpl in Heqc2.
    rewrite /is_primary Hcur Hz in Heqc2.
    destruct (0 =? 0) eqn:Hvmz; [|done].
    destruct HstepP as [Hstep1 Hstep2].
    simplify_eq.
    simpl.
    rewrite /gen_vm_interp /update_incr_PC.
    rewrite_vmid_all.
    rewrite_reg_pc.
    iFrame "Hrest Htx Hrx1 Hrx2 Hmemown Haccessown Hown".
    iDestruct ((gen_reg_update1_global PC (get_current_vm σ1) ai (ai ^+ 1)%f) with "Hregown Hpc") as "HpcUpd".
    rewrite ->(update_offset_PC_update_PC1 _ (get_current_vm σ1) ai 1); auto.
    + rewrite Hz.
      iDestruct (VMProp_update 0 U P P' with "PAuth HPropz") as "HTemp".
      iMod "HpcUpd".
      iMod "HTemp".
      iDestruct "HTemp" as "[PAuth HPropz]".
      iModIntro.
      iDestruct "HpcUpd" as "[? Hpc]".
      iFrame.      
      iSplitL "PAuth".
      by iExists P'.
      iSplit; first done.
      rewrite /just_scheduled_vms /just_scheduled.
      assert (filter
                (λ id : vmid,
                        base.negb (scheduled σ1 id) &&
                        scheduled (update_current_vmid (update_offset_PC σ1 1) i) id = true)
                (seq 0 vm_count) = [fin_to_nat i]) as ->.
      admit.
      iSimpl.
      assert ((negb (scheduled (update_current_vmid (update_offset_PC σ1 1) i) 0) && true = true)) as ->.
      admit.
      iDestruct (VMProp_split with "HPropz") as "[HPropz1 HPropz2]".
      iDestruct ("Himpl" with "[Hpc Hapc Hacc Hr0 Hr1 HR]") as "[Q R']".
      iFrame.
      iSplitR "Hϕ R' HPropz1".
      iSplit; last done.
      iExists (Q ∗ VMProp 0 P' (1 / 2))%I.      
      iFrame "HPropi".
      iNext.
      iFrame "HPropz2 Q".
      iApply ("Hϕ" with "[R' HPropz1]").
      iFrame.
    + apply get_reg_gmap_get_reg_Some; auto.
Admitted.
End run.
