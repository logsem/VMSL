From machine_program_logic.program_logic Require Import machine weakestpre.
From HypVeri Require Import RAs rule_misc lifting rules.rules_base.
From iris.proofmode Require Import tactics.
Require Import iris.base_logic.lib.ghost_map.
Require Import stdpp.fin.

Lemma run {z i w1 w2 w3 q} ai :
  decode_instruction w1 = Some Hvc ->
  fin_to_nat z = 0 -> 
  decode_hvc_func w2 = Some Run ->
  decode_vmid w3 = Some i ->
  <<z>> ∗ PC @@ z ->r ai ∗ ai ->a w1 ∗ A@z :={q} (to_pid_aligned ai)
  ∗ R0 @@ z ->r w2
  ∗ R1 @@ z ->r w3
  ⊢ SSWP ExecI @ z {{ (λ m, ⌜m = ExecI⌝ ∗
  <<i>> ∗ PC @@ z ->r (ai ^+ 1)%f ∗ ai ->a w1 ∗ A@z :={q} (to_pid_aligned ai)
  ∗ R0 @@ z ->r w2
  ∗ R1 @@ z ->r w3) }}%I.
Proof.
  iIntros (Hinstr Hz Hhvc Hvmid) "(Htok & Hpc & Hapc & Hacc & Hr0 & Hr1)".
  iApply (sswp_lift_atomic_step ExecI); [done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [ Hcur ]; clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(Htokown & Hmemown & Hregown & ? & ? & ? & Haccessown & ?)".
  (* valid regs *)
  iDestruct (gen_reg_valid1 σ1 PC z ai Hcur with "Hregown Hpc") as "%Hpc".
  iDestruct (gen_reg_valid1 σ1 R0 z w2 Hcur with "Hregown Hr0") as "%Hr0".
  iDestruct (gen_reg_valid1 σ1 R1 z w3 Hcur with "Hregown Hr1") as "%Hr1".
  (* valid pt *)
  iDestruct (gen_access_valid_addr σ1 z q ai with "Haccessown Hacc") as %Hacc.
  (* valid mem *)
  iDestruct (gen_mem_valid σ1 ai w1 with "Hmemown Hapc") as "%Hmem".
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
    rewrite /gen_vm_interp.
    rewrite update_current_vmid_preserve_mem update_current_vmid_preserve_reg update_current_vmid_preserve_tx update_current_vmid_preserve_rx update_current_vmid_preserve_owned update_current_vmid_preserve_access update_current_vmid_preserve_trans update_current_vmid_preserve_hpool update_current_vmid_preserve_receivers.
    rewrite update_offset_PC_preserve_mem update_offset_PC_preserve_tx update_offset_PC_preserve_rx update_offset_PC_preserve_owned update_offset_PC_preserve_access update_offset_PC_preserve_trans update_offset_PC_preserve_hpool update_offset_PC_preserve_receivers.
    rewrite_reg_all.
    iFrame.
    iDestruct ((gen_reg_update1_global σ1 PC (get_current_vm σ1) ai (ai ^+ 1)%f) with "Hregown Hpc") as "HpcUpd".
    iDestruct (token_update (get_current_vm σ1) i with "Htok") as "HtokUpd".
    rewrite token_agree_eq /token_agree_def.
    iDestruct ("HtokUpd" with "Htokown") as "Htok'". 
    rewrite /get_current_vm /update_current_vmid /update_incr_PC.
    simpl.
    rewrite ->(update_offset_PC_update_PC1 _ (get_current_vm σ1) ai 1); auto.
    + iMod "HpcUpd".
      iMod "Htok'".
      iModIntro.
      iDestruct "Htok'" as "[Htok1 Htok2]".
      iDestruct "HpcUpd" as "[? ?]".
      by iFrame.
    + apply get_reg_gmap_get_reg_Some; auto.
Qed.
