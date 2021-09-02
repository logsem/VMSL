From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base.
From HypVeri.algebra Require Import base reg mem token pagetable mailbox.
From HypVeri.lang Require Import lang_extra reg_extra current_extra mailbox_extra.
Require Import stdpp.fin.

Section poll.

Context `{vmG: !gen_VMG Σ}.
  
Lemma poll {w1 r0 q p s E rxp l j} ai i :
  decode_instruction w1 = Some Hvc ->
  decode_hvc_func r0 = Some Poll ->
  addr_in_page ai p ->
  p ∈ s ->
  {SS{{ ▷ (PC @@ i ->r ai)
          ∗ ▷ (R0 @@ i ->r r0)
          ∗ ▷ (ai ->a w1)
          ∗ ▷ (A@i :={q}[s] )
          ∗ ▷ (RX@ i :=( rxp ! l, j))}}}
    ExecI @ i ;E
    {{{ RET ExecI; PC @@ i ->r (ai ^+ 1)%f
                     ∗ R0 @@ i ->r r0
                     ∗ ai ->a w1
                     ∗ A@i :={q}[s]
                     ∗ RX@ i :=( rxp !)}}}.
Proof.
  iIntros (Hdecinstr Hdechvc Haddr Hins ϕ) "(>HPC & >HR0 & >Hai & >Hacc & >Hrx) Hϕ".
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
  iDestruct (gen_access_valid_addr_Set ai p s with "Haccessown Hacc") as %Hacc; eauto.
  (* valid mem *)
  iDestruct (gen_mem_valid ai w1 with "Hmemown Hai") as "%Hmem".
  (* valid rx *)
  iDestruct (gen_rx_valid_some i rxp l j with "Hrx Hrx2") as %Hrx.    
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal i Hvc ai w1);eauto.
  - iModIntro.
    iIntros (m2 σ2 Hstep).
    apply (step_ExecI_normal i Hvc ai w1) in Hstep; eauto.
    remember (exec Hvc σ1) as c2 eqn:Heqc2.
    rewrite /exec /hvc in Heqc2; eauto.
    rewrite  HR0 Hdechvc /poll in Heqc2.
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
    destruct Hstep as [Hstep1 Hstep2].
    simplify_eq.
    simpl.
    rewrite /gen_vm_interp /update_incr_PC.
    rewrite_reg_pc.
    rewrite /empty_rx.
    rewrite_empty_rx_global.
    iFrame "Hrest Htx Hrx1 Hmemown Haccessown Hown Htokown".
    iDestruct ((gen_reg_update1_global PC (get_current_vm σ1) ai (ai ^+ 1)%f) with "Hregown HPC") as "HpcUpd".
    rewrite ->(update_offset_PC_update_PC1 _ (get_current_vm σ1) ai 1); auto.
    2 : {
      by rewrite empty_rx_global_preserve_current_vm.
    }
    2 : {
      apply get_reg_gmap_get_reg_Some; auto.
      by rewrite empty_rx_global_preserve_current_vm.
      rewrite /empty_rx_global.
      rewrite /get_current_vm.
      rewrite (surjective_pairing (get_vm_mail_box σ1 σ1.1.1.2)).
      rewrite (surjective_pairing (get_vm_mail_box σ1 σ1.1.1.2).2).
      rewrite /get_reg.
      rewrite /get_reg_global.
      rewrite /get_vm_reg_file.
      rewrite /get_reg_files.
      simpl.
      rewrite /get_current_vm.
      simpl.
      by rewrite /get_reg /get_reg_global /get_current_vm /get_vm_reg_file /get_reg_files in HPC.
    }
    iMod "HpcUpd".
    iDestruct (gen_rx_gmap_update_empty_global_Some (get_current_vm σ1) rxp with "Hrx2 Hrx") as "Hrx'".
    iMod "Hrx'".
    iDestruct "Hrx'" as "[? ?]".
    iModIntro.
    iDestruct "HpcUpd" as "[? ?]".
    rewrite empty_rx_global_preserve_regs.
    iFrame.
    rewrite empty_rx_global_update_mailbox.
    iFrame.
    iApply "Hϕ".
    by iFrame.
Qed.

End poll.
