From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base.
From HypVeri Require Import base reg mem pagetable.
From HypVeri.lang Require Import lang_extra reg_extra current_extra.
Require Import stdpp.fin.

Section yield.

Context `{hypparams:HypervisorParameters}.
Context `{vmG: !gen_VMG Σ}.

Lemma yield {E z i w1 w2 a_ b_ q s R U} ai :
  let T := (▷ (PC @@ i ->r ai)
              ∗ ▷ (ai ->a w1)
              ∗ ▷ (A@i :={q}[s])
              ∗ ▷ (R0 @@ i ->r w2)
              ∗ ▷ (R0 @@ z ->r a_)
              ∗ ▷ (R1 @@ z ->r b_))%I
  in
  let T' := ((PC @@ i ->r (ai ^+ 1)%f)
               ∗ (ai ->a w1)
               ∗ (A@i :={q}[s])
               ∗ (R0 @@ i ->r w2)
               ∗ (R0 @@ z ->r (encode_hvc_func Yield))
               ∗ (R1 @@ z ->r (encode_vmid i)))%I
  in
  decode_instruction w1 = Some Hvc ->
  to_pid_aligned ai ∈ s ->
  fin_to_nat z = 0 -> 
  z ≠ i ->
  decode_hvc_func w2 = Some Yield ->
  {SS{{ T ∗ ▷ (VMProp 0 U (1/2)%Qp)
          ∗ ▷ (T' -∗ (R ∗ ▷ U)) }}}
    ExecI @ i;E
    {{{ RET (true, ExecI); R }}}.
Proof.
  simpl.
  iIntros (Hdecode Hin Hz Hzi Hhvc ϕ) "[(>Hpc & >Hapc & >Hacc & >Hr0 & >Hr1' & >Hr2') [HProp Himpl]] Hϕ".
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
  iDestruct (gen_reg_valid1 PC i ai Hcur with "Hregown Hpc") as "%Hpc".
  iDestruct (gen_reg_valid1 R0 i w2 Hcur with "Hregown Hr0") as "%Hr0".
  iDestruct (gen_reg_valid_global1 R0 z a_ with "Hregown Hr1'") as "%Hr1'".
  iDestruct (gen_reg_valid_global1 R1 z b_ with "Hregown Hr2'") as "%Hr2'".
  (* valid pt *)
  iDestruct (gen_access_valid_addr_Set ai s with "Haccessown Hacc") as %Hacc;eauto.
  (* valid mem *)
  iDestruct (gen_mem_valid ai w1 with "Hmemown Hapc") as "%Hmem".
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal i Hvc ai w1);eauto.
  - iModIntro.
    iIntros (m2 σ2) "[%P PAuth] %HstepP".
    apply (step_ExecI_normal i Hvc ai w1) in HstepP; eauto.
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
    + destruct HstepP as [Hstep1 Hstep2].
      simplify_eq.
      assert (Hzeq : z = nat_to_fin vm_count_pos).
      {
        apply fin_to_nat_inj.
        rewrite fin_to_nat_to_fin; auto.
      }
      rewrite <-Hzeq.
      simpl.
      rewrite /gen_vm_interp /update_incr_PC.
      rewrite_vmid_all.
      rewrite_reg_pc.
      rewrite_reg_global.
      iFrame "Htx Hrx1 Hrx2 Hown Hrest".
      iDestruct (gen_reg_update_Sep
                  {[(R0, z):= a_;
                    (R1, z):= b_;
                    (PC, get_current_vm σ1) := ai]}
                  {[(R0, z):= of_imm (encode_hvc_func Yield);
                    (R1, z):= of_imm (encode_vmid (get_current_vm σ1));
                    (PC, get_current_vm σ1) := (ai ^+ 1)%f]} with "Hregown [Hr1' Hr2' Hpc]") as ">[Hreg Hr12pc]"; [set_solver | |].
      * rewrite !big_sepM_insert ?big_sepM_empty; eauto; [iFrame | |].
        apply lookup_insert_None; split; eauto; intros P; by inversion P.
        apply lookup_insert_None. split; [apply lookup_insert_None; split; eauto; intros P; by inversion P |]; eauto; intros P; by inversion P.
      * rewrite !big_sepM_insert ?big_sepM_empty; eauto.
        iDestruct "Hr12pc" as "(Hr0' & Hr1' & Hpc' & _)".
        rewrite /get_current_vm /update_current_vmid /update_incr_PC.
        simpl.
        rewrite ->(update_offset_PC_update_PC1 _ (get_current_vm σ1) ai 1); auto.
        -- iModIntro.           
           iFrame.
           iSplitL "PAuth".
           iExists P.
           iFrame.
           iSplitL "Hreg".
           2 : {
             rewrite /scheduled.
             iSimpl.
             rewrite /scheduler.
             rewrite /get_current_vm.
             iSimpl.
             rewrite /bool_decide.
             rewrite /decide_rel.
             rewrite /nat_eq_dec.
             assert (z ≠ σ1.1.1.2) as p.
             solve_finz.
             assert ((if PeanoNat.Nat.eq_dec z σ1.1.1.2 then true else false) = false) as ->.
             case_match.
             exfalso.
             apply p.
             admit.
             reflexivity.
             iSimpl.
             rewrite /just_scheduled_vms.
             rewrite /just_scheduled.
             rewrite /scheduled.
             iSimpl.
             rewrite /scheduler.
             iSimpl.
             rewrite /vmid.
             rewrite /get_current_vm.
             iSimpl.
             assert (filter
                     (λ id : nat,
                        base.negb (bool_decide (fin_to_nat σ1.1.1.2 = id)) && bool_decide (fin_to_nat z = id) = true)
                     (seq 0 vm_count) = [fin_to_nat z]) as ->.
             admit.
             iSimpl.
             iDestruct ("Himpl" with "[Hpc' Hr0 Hapc Hacc Hr0' Hr1']") as "[R U]".
             iFrame.
             iSplitL "HProp U".
             iSplit; last done.
             iExists U.
             rewrite Hz.
             iFrame.             
             iApply ("Hϕ" with "R").
           }
           iSplit; first done.
           rewrite 2!update_reg_global_update_reg.
           rewrite !insert_union_singleton_l.
           rewrite (map_union_comm {[(R1, z) := of_imm (encode_vmid σ1.1.1.2)]} {[(PC, σ1.1.1.2) := (ai ^+ 1)%f]}).
           rewrite map_union_assoc.
           rewrite (map_union_comm {[(R0, z) := of_imm (encode_hvc_func Yield)]} {[(PC, σ1.1.1.2) := (ai ^+ 1)%f]}).
           rewrite <-(map_union_assoc {[(PC, σ1.1.1.2) := (ai ^+ 1)%f]}
                                      {[(R0, z) := of_imm (encode_hvc_func Yield)]}
                                      {[(R1, z) := of_imm (encode_vmid σ1.1.1.2)]}).
           rewrite (map_union_comm {[(R0, z) := of_imm (encode_hvc_func Yield )]}
                                   {[(R1, z) := of_imm (encode_vmid σ1.1.1.2)]}).
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
           Admitted.
End yield.
