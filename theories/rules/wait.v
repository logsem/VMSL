From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base.
From HypVeri.algebra Require Import base reg mem token pagetable mailbox.
From HypVeri.lang Require Import lang_extra reg_extra current_extra.
Require Import stdpp.fin.

Section wait.
Context `{hypparams: HypervisorParameters}.
Context `{vmG: !gen_VMG Σ}.
  
Lemma wait_filled {w1 r0 q p s E l j} ai i :
  decode_instruction w1 = Some Hvc ->
  decode_hvc_func r0 = Some Wait ->
  addr_in_page ai p ->
  p ∈ s ->
  {SS{{ ▷ (<<i>>{ 1%Qp })
          ∗ ▷ (PC @@ i ->r ai)
          ∗ ▷ (R0 @@ i ->r r0)
          ∗ ▷ (ai ->a w1)
          ∗ ▷ (A@i :={q}[s] )
          ∗ ▷ (RX@ i :=(l, j))}}}
    ExecI @ i ;E
    {{{ RET ExecI; <<i>>{ 1%Qp }
                     ∗ PC @@ i ->r (ai ^+ 1)%f
                     ∗ R0 @@ i ->r r0
                     ∗ ai ->a w1
                     ∗ A@i :={q}[s]
                     ∗ RX@ i :=(l, j)}}}.
Proof.
  iIntros (Hdecinstr Hdechvc Haddr Hins ϕ) "(>Htok & >HPC & >HR0 & >Hai & >Hacc & >Hrx) Hϕ".
  iApply (sswp_lift_atomic_step ExecI); [done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [ Hcur ]; clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(Htokown & Hmemown & Hregown & Htx & Hrx1 & Hrx2 & Hown & Haccessown & Hrest)".
  (* valid regs *)
  iDestruct (gen_reg_valid1 PC i ai Hcur with "Hregown HPC") as "%HPC".
  iDestruct (gen_reg_valid1 R0 i r0 Hcur with "Hregown HR0") as "%HR0".
  (* valid pt *)
  iDestruct (gen_access_valid_addr_Set ai s with "Haccessown Hacc") as %Hacc; eauto.
  rewrite (to_pid_aligned_in_page _ p); auto.
  (* valid mem *)
  iDestruct (gen_mem_valid ai w1 with "Hmemown Hai") as "%Hmem".
  (* valid rx *)
  iDestruct (gen_rx_valid_some i l j with "Hrx Hrx2") as %Hrx.
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal i Hvc ai w1);eauto.
  - iModIntro.
    iIntros (m2 σ2 Hstep).
    apply (step_ExecI_normal i Hvc ai w1) in Hstep; eauto.
    remember (exec Hvc σ1) as c2 eqn:Heqc2.
    rewrite /exec /hvc in Heqc2; eauto.
    rewrite  HR0 Hdechvc /wait in Heqc2.
    rewrite /is_rx_ready in Heqc2.
    rewrite /is_rx_ready_global in Heqc2.
    destruct (get_vm_mail_box σ1 (get_current_vm σ1)) as [tx rx] eqn:Heqmb.
    destruct rx as [rxaddr rxstatus] eqn:Heqrx.
    rewrite Hcur in Heqmb.
    rewrite (surjective_pairing (get_vm_mail_box σ1 i)) in Heqmb.
    rewrite (surjective_pairing ((get_vm_mail_box σ1 i).2)) in Heqmb.
    rewrite Hrx in Heqmb.
    inversion Heqmb.
    subst rxstatus.
    simpl in Heqc2.
    assert (Hpreserve : ∀ σ σ', get_current_vm σ' = get_current_vm σ ->
                                update_current_vmid σ' (get_current_vm σ) = σ').
    {
      intros σ σ' Hcureq'.
      by rewrite /update_current_vmid -Hcureq' -!surjective_pairing.
    }
    rewrite Hpreserve in Heqc2.
    2 : {
      by rewrite /update_incr_PC update_offset_PC_preserve_current_vm.
    }
    destruct Hstep as [Hstep1 Hstep2].
    simplify_eq.
    simpl.
    rewrite /gen_vm_interp /update_incr_PC.
    rewrite_reg_pc.
    iFrame "Hrest Htx Hrx1 Hrx2 Hmemown Haccessown Hown Htokown".
    iDestruct ((gen_reg_update1_global PC (get_current_vm σ1) ai (ai ^+ 1)%f) with "Hregown HPC") as "HpcUpd".
    rewrite ->(update_offset_PC_update_PC1 _ (get_current_vm σ1) ai 1); auto.
    2 : {
      apply get_reg_gmap_get_reg_Some; auto.
    }
    iMod "HpcUpd".
    iModIntro.
    iDestruct "HpcUpd" as "[? ?]".
    iFrame.
    iApply "Hϕ".
    by iFrame.
Qed.

Lemma wait_empty {w1 r0 q p s E z b_} ai i :
  decode_instruction w1 = Some Hvc ->
  decode_hvc_func r0 = Some Wait ->
  addr_in_page ai p ->
  p ∈ s ->
  fin_to_nat z = 0 -> 
  {SS{{ ▷ (<<i>>{ 1%Qp })
          ∗ ▷ (PC @@ i ->r ai)
          ∗ ▷ (R0 @@ i ->r r0)
          ∗ ▷ (ai ->a w1)
          ∗ ▷ (A@i :={q}[s] )
          ∗ ▷ (RX@ i :=())
          ∗ ▷ (R1 @@ z ->r b_)}}}
    ExecI @ i ;E
    {{{ RET ExecI; <<z>>{ 1%Qp }
                     ∗ PC @@ i ->r (ai ^+ 1)%f
                     ∗ R0 @@ i ->r r0
                     ∗ ai ->a w1
                     ∗ A@i :={q}[s]
                     ∗ RX@ i :=()
                     ∗ R1 @@ z ->r (encode_vmid i)}}}.
Proof.
  iIntros (Hdecinstr Hdechvc Haddr Hins Heqz ϕ) "(>Htok & >HPC & >HR0 & >Hai & >Hacc & >Hrx & >HR1') Hϕ".
  iApply (sswp_lift_atomic_step ExecI); [done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [ Hcur ]; clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(Htokown & Hmemown & Hregown & Htx & Hrx1 & Hrx2 & Hown & Haccessown & Hrest)".
  (* valid regs *)
  iDestruct (gen_reg_valid1 PC i ai Hcur with "Hregown HPC") as "%HPC".
  iDestruct (gen_reg_valid1 R0 i r0 Hcur with "Hregown HR0") as "%HR0".
  iDestruct (gen_reg_valid_global1 R1 z b_ with "Hregown HR1'") as "%HR1'".
  (* valid pt *)
  iDestruct (gen_access_valid_addr_Set ai s with "Haccessown Hacc") as %Hacc; eauto.
  rewrite (to_pid_aligned_in_page _ p); auto.
  (* valid mem *)
  iDestruct (gen_mem_valid ai w1 with "Hmemown Hai") as "%Hmem".
  (* valid rx *)
  iDestruct (gen_rx_valid_none i with "Hrx Hrx2") as %Hrx.
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal i Hvc ai w1);eauto.
  - iModIntro.
    iIntros (m2 σ2 Hstep).
    apply (step_ExecI_normal i Hvc ai w1) in Hstep; eauto.
    remember (exec Hvc σ1) as c2 eqn:Heqc2.
    rewrite /exec /hvc in Heqc2; eauto.
    rewrite  HR0 Hdechvc /wait in Heqc2.
    rewrite /is_rx_ready in Heqc2.
    rewrite /is_rx_ready_global in Heqc2.
    destruct (get_vm_mail_box σ1 (get_current_vm σ1)) as [tx rx] eqn:Heqmb.
    destruct rx as [rxaddr rxstatus] eqn:Heqrx.
    rewrite Hcur in Heqmb.
    rewrite (surjective_pairing (get_vm_mail_box σ1 i)) in Heqmb.
    rewrite (surjective_pairing ((get_vm_mail_box σ1 i).2)) in Heqmb.
    rewrite Hrx in Heqmb.
    inversion Heqmb.
    subst rxstatus.
    assert (Hzeq : z = nat_to_fin vm_count_pos).
    {
      apply fin_to_nat_inj.
      rewrite fin_to_nat_to_fin; auto.
    }
    rewrite <-Hzeq in Heqc2.
    clear Hzeq.
    simpl in Heqc2.
    destruct Hstep as [Hstep1 Hstep2].
    simplify_eq.
    simpl.
    rewrite /gen_vm_interp /update_incr_PC.
    simpl.
    rewrite_vmid_all.    
    rewrite_reg_pc.
    rewrite_reg_global.
    iFrame "Hmemown Htx Hrx1 Hrx2 Hown Haccessown Hrest".
    rewrite /get_current_vm /update_current_vmid.
    simpl.
    iDestruct (token_update (get_current_vm σ1) (get_current_vm σ1) z with "Htok") as "HtokUpd".
    rewrite token_agree_eq /token_agree_def.
    iDestruct ("HtokUpd" with "Htokown") as "Htok'".
    iDestruct (gen_reg_update2_global PC σ1.1.1.2 ai (ai ^+ 1)%f R1 z b_ (encode_vmid σ1.1.1.2)
                 with "Hregown HPC HR1'") as ">[Hregown [PC R1]]"; eauto.
    rewrite ->(update_offset_PC_update_PC1 _ (get_current_vm σ1) ai 1); auto.
    2 : {
      rewrite update_reg_global_update_reg.
      rewrite lookup_insert_ne;[solve_reg_lookup|done].
      exists b_.
      rewrite /get_reg in HR1'.
      rewrite get_reg_gmap_lookup_Some.
      rewrite /get_reg_global in HR1'.
      assumption.
    }
    rewrite update_reg_global_update_reg.
    2 : {
      exists b_.
      rewrite /get_reg in HR1'.
      rewrite get_reg_gmap_lookup_Some.
      rewrite /get_reg_global in HR1'.
      assumption.
    }
    iMod "Htok'".
    iDestruct "Htok'" as "[? Htok]".
    iFrame.
    iApply "Hϕ".
    by iFrame.
Qed.

End wait.
