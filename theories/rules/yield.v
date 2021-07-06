From machine_program_logic.program_logic Require Import machine weakestpre.
From HypVeri Require Import RAs rule_misc lifting rules.rules_base.
From iris.proofmode Require Import tactics.
Require Import iris.base_logic.lib.ghost_map.
Require Import stdpp.fin.

Lemma yield {z i w1 w2 a_ b_ q} ai :
  decode_instruction w1 = Some Hvc ->
  fin_to_nat z = 0 -> 
  z ≠ i ->
  decode_hvc_func w2 = Some Yield ->
  <<i>> ∗ PC @@ i ->r ai ∗ ai ->a w1 ∗ A@i :={q} (mm_translation ai)
  ∗ R0 @@ i ->r w2
  ∗ R0 @@ z ->r a_
  ∗ R1 @@ z ->r b_
  ⊢ SSWP ExecI @ i {{ (λ m, ⌜m = ExecI⌝ ∗
  <<z>> ∗ PC @@ i ->r (ai +w 1) ∗ ai ->a w1 ∗ A@i :={q} (mm_translation ai)
  ∗ R0 @@ i ->r w2
  ∗ R0 @@ z ->r (encode_hvc_ret_code Succ)
  ∗ R1 @@ z ->r (encode_vmid i)) }}%I.
Proof.
  iIntros (Hinstr Hz Hzi Hhvc) "(Htok & Hpc & Hapc & Hacc & Hr0 & Hr1' & Hr2')".
  iApply (sswp_lift_atomic_step ExecI); [done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [ Hcur ]; clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(Htokown & Hmemown & Hregown & ? & ? & ? & Haccessown & ?)".
  (* valid regs *)
  iDestruct (gen_reg_valid1 σ1 PC i ai Hcur with "Hregown Hpc") as "%Hpc".
  iDestruct (gen_reg_valid1 σ1 R0 i w2 Hcur with "Hregown Hr0") as "%Hr0".
  iDestruct (gen_reg_valid_global1 σ1 R0 z a_ with "Hregown Hr1'") as "%Hr1'".
  iDestruct (gen_reg_valid_global1 σ1 R1 z b_ with "Hregown Hr2'") as "%Hr2'".
  (* valid pt *)
  iDestruct (gen_access_valid_addr σ1 i q ai with "Haccessown Hacc") as %Hacc.
  (* valid mem *)
  iDestruct (gen_mem_valid σ1 ai w1 with "Hmemown Hapc") as "%Hmem".
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal i Hvc ai w1);eauto.
  - iModIntro.
    iIntros (m2 σ2 Hstep).
    apply (step_ExecI_normal i Hvc ai w1) in Hstep; eauto.
    remember (exec Hvc σ1) as c2 eqn:Heqc2.
    rewrite /exec /hvc in Heqc2; eauto.
    rewrite  Hr0 Hhvc /yield in Heqc2.
    rewrite /is_primary /update_reg update_reg_global_preserve_current_vm Hcur in Heqc2.
    destruct (i =? 0) eqn:Hi0.
    + rewrite <-(reflect_iff (fin_to_nat i = 0) (i =? 0) (Nat.eqb_spec (fin_to_nat i) 0)) in Hi0.
      exfalso.
      apply Hzi.
      apply fin_to_nat_inj.
      rewrite Hz Hi0.
      reflexivity.
    + destruct Hstep as [Hstep1 Hstep2].
      simplify_eq.
      assert (Hzeq : z = nat_to_fin vm_count_pos).
      {
        apply fin_to_nat_inj.
        rewrite fin_to_nat_to_fin; auto.
      }
      rewrite <-Hzeq.
      simpl.
      rewrite /gen_vm_interp.
      rewrite update_current_vmid_preserve_mem update_current_vmid_preserve_reg update_current_vmid_preserve_tx update_current_vmid_preserve_rx update_current_vmid_preserve_owned update_current_vmid_preserve_access update_current_vmid_preserve_trans update_current_vmid_preserve_receivers.
      rewrite update_offset_PC_preserve_mem update_offset_PC_preserve_tx update_offset_PC_preserve_rx update_offset_PC_preserve_owned update_offset_PC_preserve_access update_offset_PC_preserve_trans update_offset_PC_preserve_receivers.
      iFrame.
      iDestruct (gen_reg_update_Sep σ1
                                    {[(R0 , z) := a_;
                                      (R1, z):= b_;
                                      (PC, get_current_vm σ1) := ai]}
                                    {[(R0, z):= encode_hvc_ret_code Succ;
                                      (R1, z):= (encode_vmid (get_current_vm σ1));
                                      (PC, get_current_vm σ1) := ai +w 1]} with "Hregown [Hr1' Hr2' Hpc]") as ">[Hreg Hr12pc]"; [set_solver | |].
      * rewrite !big_sepM_insert ?big_sepM_empty; eauto; [iFrame | |].
        apply lookup_insert_None; split; eauto; intros P; by inversion P.
        apply lookup_insert_None. split; [apply lookup_insert_None; split; eauto; intros P; by inversion P |]; eauto; intros P; by inversion P.
      * rewrite !big_sepM_insert ?big_sepM_empty; eauto.
        iDestruct "Hr12pc" as "(? & ? & ? & _)".
        iDestruct (token_update (get_current_vm σ1) z with "Htok") as "HtokUpd".
        rewrite token_agree_eq /token_agree_def.
        iDestruct ("HtokUpd" with "Htokown") as "Htok'". 
        rewrite /get_current_vm /update_current_vmid /update_incr_PC.
        simpl.
        rewrite ->(update_offset_PC_update_PC1 _ (get_current_vm σ1) ai 1); auto.
        -- iMod "Htok'".
           iModIntro.
           iDestruct "Htok'" as "[Htok1 Htok2]".
           iFrame.
           iSplit; [| done].
           rewrite 2!update_reg_global_update_reg.
           rewrite !insert_union_singleton_l.
           rewrite (map_union_comm {[(R1, z) := encode_vmid σ1.1.1.2]} {[(PC, σ1.1.1.2) := ai +w 1]}).
           rewrite map_union_assoc.
           rewrite (map_union_comm {[(R0, z) := encode_hvc_ret_code Succ]} {[(PC, σ1.1.1.2) := ai +w 1]}).
           rewrite <-(map_union_assoc {[(PC, σ1.1.1.2) := ai +w 1]}
                                      {[(R0 , z) := encode_hvc_ret_code Succ]}
                                      {[(R1 , z) := encode_vmid σ1.1.1.2]}).
           rewrite (map_union_comm {[(R0, z) := encode_hvc_ret_code Succ]}
                                   {[(R1 , z) := encode_vmid σ1.1.1.2]}).
           rewrite !map_union_assoc.
           iAssumption.
           by rewrite map_disjoint_singleton_r lookup_singleton_None.
           by rewrite map_disjoint_singleton_r lookup_singleton_None.
           by rewrite map_disjoint_singleton_r lookup_singleton_None.
           eapply mk_is_Some; rewrite get_reg_gmap_lookup_Some; eauto.
           eapply mk_is_Some; rewrite lookup_insert_Some;
             right; split; [done | rewrite get_reg_gmap_lookup_Some; eauto].
           eapply mk_is_Some; rewrite get_reg_gmap_lookup_Some; eauto.
        -- apply get_reg_gmap_get_reg_Some; auto.
           apply get_reg_global_update_reg_global_ne_vmid.
           rewrite update_reg_global_preserve_current_vm; auto.
           apply get_reg_global_update_reg_global_ne_vmid.
           rewrite update_reg_global_preserve_current_vm; auto.
           rewrite 2!update_reg_global_preserve_current_vm; auto.
        -- apply lookup_insert_None; split; eauto; intros P; by inversion P.
        -- apply lookup_insert_None. split; [apply lookup_insert_None; split; eauto; intros P; by inversion P |]; eauto; intros P; by inversion P.
Qed.
