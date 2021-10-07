From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base.
From HypVeri.algebra Require Import base reg mem token pagetable.
From HypVeri.lang Require Import lang_extra reg_extra current_extra.
Require Import stdpp.fin.

Section run.

Context `{hypparams:HypervisorParameters}.
Context `{vmG: !gen_VMG Σ}.
  
Lemma run {z w1 w2 w3 q s E} ai i :
  decode_instruction w1 = Some Hvc ->
  to_pid_aligned ai ∈ s ->
  fin_to_nat z = 0 -> 
  decode_hvc_func w2 = Some Run ->
  decode_vmid w3 = Some i ->
  {SS{{ ▷ (<<z>>{ 1%Qp })
          ∗ ▷ (PC @@ z ->r ai)
          ∗ ▷ (ai ->a w1)
          ∗ ▷ (A@z :={q}[s] )
          ∗ ▷ (R0 @@ z ->r w2)
          ∗ ▷ (R1 @@ z ->r w3)}}}
    ExecI @ z ;E
    {{{ RET ExecI; <<i>>{ 1%Qp }
                     ∗ PC @@ z ->r (ai ^+ 1)%f
                     ∗ ai ->a w1
                     ∗ A@z :={q}[s]
                     ∗ R0 @@ z ->r w2
                     ∗ R1 @@ z ->r w3 }}}.
Proof.
  iIntros (Hdecode Hin Hz Hhvc Hvmid ϕ) "(>Htok & >Hpc & >Hapc & >Hacc & >Hr0 & >Hr1) Hϕ".
  iApply (sswp_lift_atomic_step ExecI); [done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [ Hcur ]; clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(Htokown & Hmemown & Hregown & Htx & Hrx1 & Hrx2 & Hown & Haccessown & Hrest)".
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
    iIntros (m2 σ2 Hstep).
    apply (step_ExecI_normal z Hvc ai w1) in Hstep; eauto.
    remember (exec Hvc σ1) as c2 eqn:Heqc2.
    rewrite /exec /hvc in Heqc2; eauto.
    rewrite  Hr0 Hhvc /run Hr1 in Heqc2.
    simpl in Heqc2.
    rewrite /unpack_hvc_result_yield Hvmid in Heqc2.
    simpl in Heqc2.
    rewrite /is_primary Hcur Hz in Heqc2.
    destruct (0 =? 0) eqn:Hvmz; [|done].
    destruct Hstep as [Hstep1 Hstep2].
    simplify_eq.
    simpl.
    rewrite /gen_vm_interp /update_incr_PC.
    rewrite_vmid_all.
    rewrite_reg_pc.
    iFrame "Hrest Htx Hrx1 Hrx2 Hmemown Haccessown".
    iDestruct ((gen_reg_update1_global PC (get_current_vm σ1) ai (ai ^+ 1)%f) with "Hregown Hpc") as "HpcUpd".
    iDestruct (token_update (get_current_vm σ1) (get_current_vm σ1) i with "Htok") as "HtokUpd".
    rewrite token_agree_eq /token_agree_def.
    iDestruct ("HtokUpd" with "Htokown") as "Htok'". 
    rewrite /get_current_vm /update_current_vmid.
    simpl.
    rewrite ->(update_offset_PC_update_PC1 _ (get_current_vm σ1) ai 1); auto.
    + iMod "HpcUpd".
      iMod "Htok'".
      iModIntro.
      iDestruct "Htok'" as "[Htok1 Htok2]".
      iDestruct "HpcUpd" as "[? ?]".
      iFrame.
      iApply "Hϕ".
      by iFrame.
    + apply get_reg_gmap_get_reg_Some; auto.
Qed.
End run.
