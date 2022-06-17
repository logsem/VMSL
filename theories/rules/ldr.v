From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import machine_extra lifting rules.rules_base.
From HypVeri.algebra Require Import base reg mem mailbox pagetable base_extra.
From HypVeri.lang Require Import lang_extra reg_extra mem_extra.

Section ldr.

Context `{hypparams: HypervisorParameters}.
Context `{vmG: !gen_VMG Σ}.
  
Lemma ldr {E i w1 w2 w3 q p s} ai a ra rb:
  decode_instruction w1 = Some (Ldr ra rb) ->
  {[tpa ai; tpa a]} ⊆ s ->
  (tpa a) ≠ p ->
  (tpa ai) ≠ p ->
  {SS{{ ▷ (PC @@ i ->r ai) ∗
        ▷ (ai ->a w1) ∗
        ▷ (rb @@ i ->r a) ∗
        ▷ (a ->a w2) ∗
        ▷ (ra @@ i ->r w3) ∗
        ▷ (i -@{ q }A> s) ∗
        ▷ (TX@ i := p)}}}
    ExecI @ i; E
    {{{ RET (false,ExecI);
        PC @@ i ->r (ai ^+ 1)%f ∗
        ai ->a w1 ∗
        rb @@ i ->r a ∗
        a ->a w2 ∗
        ra @@ i ->r w2 ∗
        i -@{ q }A> s ∗            
        TX@ i := p }}}.
Proof.
  iIntros (Hdecode Hsubset Hne_p Hne_p' ϕ) "(>Hpc & >Hapc & >Hrb & >Harb & >Hra & >Hacc & >Htx) Hϕ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (n σ1) "%Hsche Hσ".
  rewrite /scheduled  /= /scheduler in Hsche.
  apply bool_decide_unpack in Hsche as Hcur.
  clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(Hnum & Hmem & Hreg & Hmb & Hrx & Hown & Haccess & Hrest)".
  pose proof (decode_instruction_valid w1 _ Hdecode) as Hvalidinstr.
  inversion Hvalidinstr as [| | src dst H3' H4' Hneqrarb | | | | | | | | |]; subst src dst; clear Hvalidinstr.
  destruct H3' as [HneqPCa HneqNZa].
  destruct H4' as [HneqPCb HneqNZb].
  iDestruct ((gen_reg_valid3 i PC ai ra w3 rb a Hcur) with "Hreg Hpc Hra Hrb") as "[%HPC [%Hra %Hrb]]".
  (* valid pt *)
  iDestruct (access_agree_check_true (tpa a) i with "Haccess Hacc") as "%Ha"; first set_solver.
  iDestruct (access_agree_check_true (tpa ai) i with "Haccess Hacc") as "%Hai"; first set_solver.
  (* valid mem *)
  iDestruct (gen_mem_valid2 ai w1 a w2 with "Hmem Hapc Harb") as "[%Hmemai %Hmema]".
  iDestruct (mb_valid_tx i p with "Hmb Htx") as %Htx.
  subst p.
  iSplit.
  - (* reducible *)
    iPureIntro.
    eapply (reducible_normal i _ ai w1); eauto.    
  - (* step *)
    iModIntro.
    iIntros (m2 σ2) "HpropA %HstepP".
    iSplitL "HpropA"; first (iFrame; done).
    eapply (step_ExecI_normal i _ ai w1 ) in HstepP;eauto.
    remember (exec _ σ1) as c2 eqn:Heqc2.
    rewrite <-Hcur in Ha.
    rewrite /exec (ldr_ExecI σ1 ra rb a w2 HneqPCa HneqNZa HneqPCb HneqNZb _ Ha)
            /update_incr_PC /update_reg in Heqc2; [| subst i; done | subst i; done | subst i; done].
    destruct HstepP; subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    (* unchanged part *)
    rewrite (preserve_get_mb_gmap σ1).
    rewrite (preserve_get_rx_gmap σ1).
    rewrite (preserve_get_own_gmap σ1).
    rewrite (preserve_get_access_gmap σ1).
    rewrite (preserve_get_excl_gmap σ1).
    rewrite (preserve_get_trans_gmap σ1).
    rewrite (preserve_get_hpool_gset σ1).
    rewrite (preserve_get_retri_gmap σ1).
    rewrite (preserve_inv_trans_pgt_consistent σ1).
    rewrite (preserve_inv_trans_wellformed σ1).
    rewrite (preserve_inv_trans_ps_disj σ1).
    rewrite p_upd_pc_mem p_upd_reg_mem.
    all: try rewrite p_upd_pc_pgt p_upd_reg_pgt //.
    all: try rewrite p_upd_pc_trans p_upd_reg_trans //.
    all: try rewrite p_upd_pc_mb p_upd_reg_mb //.
    iFrame.
    rewrite Hcur.
    (* updated part *)
    rewrite -> (u_upd_pc_regs _ i ai 1);eauto.
    + rewrite u_upd_reg_regs.
      iDestruct ((gen_reg_update2_global PC i ai (ai ^+ 1)%f ra i w3 w2 ) with "Hreg Hpc Hra") as ">[Hσ [Hreg Hra]]";eauto.
      apply (get_reg_gmap_get_reg_Some _ _ _ i) in Hra;eauto.
      iModIntro.
      iFrame "Hσ".
      iSplitL "".
      rewrite update_offset_PC_preserve_just_scheduled_vms.
      rewrite update_reg_global_preserve_just_scheduled_vms.
      rewrite just_scheduled_vms_no_step_empty.
      by iSimpl.
      rewrite update_offset_PC_preserve_scheduled.
      rewrite update_reg_global_preserve_scheduled.
      rewrite scheduled_true /=;last done.
      iApply "Hϕ".
      iFrame "Hreg Hapc Harb Hra Hrb Hacc Htx".
    + rewrite u_upd_reg_regs.
      repeat solve_reg_lookup.
      intros P; symmetry in P;inversion P; contradiction.
Qed.

Lemma ldr_same_page {E i w1 w2 w3 q p s} ai a ra rb:
  decode_instruction w1 = Some (Ldr ra rb) ->
  (tpa a) ≠ p ->
  tpa ai ∈ s ->
  ai ≠ a ->
  (tpa ai) = (tpa a) ->
  {SS{{ ▷ (PC @@ i ->r ai) ∗
        ▷ (ai ->a w1) ∗
        ▷ (rb @@ i ->r a) ∗
        ▷ (a ->a w2) ∗
        ▷ (ra @@ i ->r w3) ∗
        ▷ (i -@{ q }A> s) ∗
        ▷ (TX@ i := p)}}}
    ExecI @ i; E
    {{{ RET (false,ExecI);
        PC @@ i ->r (ai ^+ 1)%f ∗
        ai ->a w1 ∗
        rb @@ i ->r a ∗
        a ->a w2 ∗
        ra @@ i ->r w2 ∗
        (i -@{ q }A> s) ∗
        TX@ i := p }}}.
Proof.
  iIntros (Hdecode Hne_p Hin Hneq Heq_p ϕ) "(>Hpc & >Hapc & >Hrb & >Harb & >Hra & >Hacc & >Htx) Hϕ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (n σ1) "%Hsche Hσ".
  rewrite /scheduled  /= /scheduler in Hsche.
  apply bool_decide_unpack in Hsche as Hcur.
  clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(Hnum & Hmem & Hreg & Hmb & Hrx & Hown & Haccess & Hrest)".
  pose proof (decode_instruction_valid w1 _ Hdecode) as Hvalidinstr.
  inversion Hvalidinstr as [| | src dst H3' H4' Hneqrarb | | | | | | | | |]; subst src dst; clear Hvalidinstr.
  destruct H3' as [HneqPCa HneqNZa].
  destruct H4' as [HneqPCb HneqNZb].
  iDestruct ((gen_reg_valid3 i PC ai ra w3 rb a Hcur) with "Hreg Hpc Hra Hrb") as "[%HPC [%Hra %Hrb]]".
  (* valid pt *)
  iDestruct (access_agree_check_true (tpa ai) i with "Haccess Hacc") as "%Hai"; first set_solver.
  (* valid mem *)
  iDestruct (gen_mem_valid2 ai w1 a w2 with "Hmem Hapc Harb") as "[%Hmemai %Hmema]".
  iDestruct (mb_valid_tx i p with "Hmb Htx") as %Htx.
  iSplit.
  - (* reducible *)
    iPureIntro.
    eapply (reducible_normal i _ ai w1);eauto.
    rewrite <-Heq_p in Hne_p.
    rewrite <-Htx in Hne_p.
    done.
  - (* step *)
    iModIntro.
    iIntros (m2 σ2) "HpropA %HstepP".
    iSplitL "HpropA";first (iFrame;done).
    eapply (step_ExecI_normal i _ ai w1 ) in HstepP;eauto.
    2 : {
      rewrite <-Heq_p in Hne_p.
      rewrite <-Htx in Hne_p.
      done.
    }
    remember (exec _ σ1) as c2 eqn:Heqc2.    
    rewrite /exec (ldr_ExecI σ1 ra rb a w2 HneqPCa HneqNZa HneqPCb HneqNZb _)
            /update_incr_PC /update_reg in Heqc2; [| subst i; by rewrite <-Htx in Hne_p | subst i; rewrite <-Heq_p; assumption | subst i; done | done].
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    (* unchanged part *)
    rewrite (preserve_get_mb_gmap σ1).
    rewrite (preserve_get_rx_gmap σ1).
    rewrite (preserve_get_own_gmap σ1).
    rewrite (preserve_get_access_gmap σ1).
    rewrite (preserve_get_excl_gmap σ1).
    rewrite (preserve_get_trans_gmap σ1).
    rewrite (preserve_get_hpool_gset σ1).
    rewrite (preserve_get_retri_gmap σ1).
    rewrite (preserve_inv_trans_pgt_consistent σ1).
    rewrite (preserve_inv_trans_wellformed σ1).
    rewrite (preserve_inv_trans_ps_disj σ1).
    rewrite p_upd_pc_mem p_upd_reg_mem.
    all: try rewrite p_upd_pc_pgt p_upd_reg_pgt //.
    all: try rewrite p_upd_pc_trans p_upd_reg_trans //.
    all: try rewrite p_upd_pc_mb p_upd_reg_mb //.
    iFrame.
    rewrite Hcur.
    (* updated part *)
    rewrite -> (u_upd_pc_regs _ i ai 1);eauto.
    + rewrite u_upd_reg_regs.
      iDestruct ((gen_reg_update2_global PC i ai (ai ^+ 1)%f ra i w3 w2 ) with "Hreg Hpc Hra") as ">[Hσ [Hreg Hra]]";eauto.
      apply (get_reg_gmap_get_reg_Some _ _ _ i) in Hra;eauto.
      iModIntro.
      iFrame "Hσ".
      iSplitL "".
      rewrite update_offset_PC_preserve_just_scheduled_vms.
      rewrite update_reg_global_preserve_just_scheduled_vms.
      rewrite just_scheduled_vms_no_step_empty.
      by iSimpl.
      rewrite update_offset_PC_preserve_scheduled.
      rewrite update_reg_global_preserve_scheduled.
      rewrite scheduled_true /=;last done.
      iApply "Hϕ".
      iFrame "Hreg Hapc Harb Hra Hrb Hacc Htx".
    + rewrite u_upd_reg_regs.
      repeat solve_reg_lookup.
      intros P; symmetry in P;inversion P; contradiction.
Qed.

Lemma ldr_same_addr {E i w1 w2 q p s} ai a ra rb:
  decode_instruction w1 = Some (Ldr ra rb) ->
  (tpa a) ≠ p ->
  tpa ai ∈ s ->
  ai = a ->
  {SS{{ ▷ (PC @@ i ->r ai) ∗
        ▷ (ai ->a w1) ∗
        ▷ (rb @@ i ->r a) ∗
        ▷ (ra @@ i ->r w2) ∗
        ▷ (i -@{ q }A> s) ∗
        ▷ (TX@ i := p)}}}
    ExecI @ i; E
    {{{ RET (false,ExecI);
        PC @@ i ->r (ai ^+ 1)%f ∗
        ai ->a w1 ∗
        rb @@ i ->r a ∗
        ra @@ i ->r w1 ∗
        (i -@{ q }A> s) ∗
        TX@ i := p }}}.
Proof.
  iIntros (Hdecode Hne_p Hin Heq_p ϕ) "(>Hpc & >Hapc & >Hrb & >Hra & >Hacc & >Htx) Hϕ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (n σ1) "%Hsche Hσ".
  rewrite /scheduled  /= /scheduler in Hsche.
  apply bool_decide_unpack in Hsche as Hcur.
  clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(Hnum & Hmem & Hreg & Hmb & Hrx & Hown & Haccess & Hrest)".
  pose proof (decode_instruction_valid w1 _ Hdecode) as Hvalidinstr.
  inversion Hvalidinstr as [| | src dst H3' H4' Hneqrarb | | | | | | | | |]; subst src dst; clear Hvalidinstr.
  destruct H3' as [HneqPCa HneqNZa].
  destruct H4' as [HneqPCb HneqNZb].
  iDestruct ((gen_reg_valid3 i PC ai ra w2 rb a Hcur) with "Hreg Hpc Hra Hrb") as "[%HPC [%Hra %Hrb]]".
  (* valid pt *)
  iDestruct (access_agree_check_true (tpa ai) i with "Haccess Hacc") as "%Hai"; first set_solver.
  iDestruct (mb_valid_tx i p with "Hmb Htx") as %Htx.
  (* valid mem *)
  iDestruct (gen_mem_valid ai w1 with "Hmem Hapc") as "%Hmemai".
  iSplit.
  - (* reducible *)
    iPureIntro.
    eapply (reducible_normal i _ ai w1);eauto.
    by rewrite Heq_p Htx.
  - (* step *)
    iModIntro.
    iIntros (m2 σ2) "HpropA %HstepP".
    iSplitL "HpropA";first (iFrame;done).
    eapply (step_ExecI_normal i _ ai w1 ) in HstepP;eauto.
    2: by rewrite Heq_p Htx.
    remember (exec _ σ1) as c2 eqn:Heqc2.
    rewrite /exec (ldr_ExecI σ1 ra rb a w1 HneqPCa HneqNZa HneqPCb HneqNZb _ _ Hrb)
            /update_incr_PC /update_reg in Heqc2.
    2: {
      rewrite Hcur.
      rewrite Htx.
      done.
    }
    2: {
      rewrite Hcur.
      rewrite <-Heq_p.
      done.
    }
    2: {
      rewrite <-Heq_p.
      done.
    }
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    (* unchanged part *)
    rewrite (preserve_get_mb_gmap σ1).
    rewrite (preserve_get_rx_gmap σ1).
    rewrite (preserve_get_own_gmap σ1).
    rewrite (preserve_get_access_gmap σ1).
    rewrite (preserve_get_excl_gmap σ1).
    rewrite (preserve_get_trans_gmap σ1).
    rewrite (preserve_get_hpool_gset σ1).
    rewrite (preserve_get_retri_gmap σ1).
    rewrite (preserve_inv_trans_pgt_consistent σ1).
    rewrite (preserve_inv_trans_wellformed σ1).
    rewrite (preserve_inv_trans_ps_disj σ1).
    rewrite p_upd_pc_mem p_upd_reg_mem.
    all: try rewrite p_upd_pc_pgt p_upd_reg_pgt //.
    all: try rewrite p_upd_pc_trans p_upd_reg_trans //.
    all: try rewrite p_upd_pc_mb p_upd_reg_mb //.
    iFrame.
    rewrite Hcur.
    (* updated part *)
    rewrite -> (u_upd_pc_regs _ i ai 1);eauto.
    + rewrite u_upd_reg_regs.
      iDestruct ((gen_reg_update2_global PC i ai (ai ^+ 1)%f ra i w2 w1 ) with "Hreg Hpc Hra") as ">[Hσ [Hreg Hra]]";eauto.
      apply (get_reg_gmap_get_reg_Some _ _ _ i) in Hra;eauto.
      iModIntro.
      iFrame "Hσ".
      iSplitL "".
      rewrite update_offset_PC_preserve_just_scheduled_vms.
      rewrite update_reg_global_preserve_just_scheduled_vms.
      rewrite just_scheduled_vms_no_step_empty.
      by iSimpl.
      rewrite update_offset_PC_preserve_scheduled.
      rewrite update_reg_global_preserve_scheduled.
      rewrite scheduled_true /=;last done.
      iApply "Hϕ".
      iFrame "Hreg Hapc Hra Hrb Hacc Htx".
    + rewrite u_upd_reg_regs.
      repeat solve_reg_lookup.
      intros P; symmetry in P;inversion P; contradiction.
Qed.

Lemma ldr_no_access{i w1 w3 s p} ai a ra rb :
  decode_instruction w1 = Some (Ldr ra rb) ->
  tpa ai ∈ s ->
  tpa a ∉ s ->
  (tpa ai) ≠ p ->
  {SS{{ ▷ (PC @@ i ->r ai) ∗
        ▷ (ai ->a w1) ∗
        ▷ (rb @@ i ->r a) ∗
        ▷ (ra @@ i ->r w3) ∗
        ▷ (i -@{ 1 }A> s) ∗
        ▷ (TX@ i := p)
      }}} ExecI @ i
    {{{ RET (false,FailPageFaultI);
        PC @@ i ->r ai ∗
        ai ->a w1 ∗
        rb @@ i ->r a ∗
        (i -@{ 1 }A> s) ∗
        ra @@ i ->r w3 ∗
        (TX@ i := p) }}}.
Proof.
  iIntros (Hdecode Hin Hnotin Hne ϕ) "(>Hpc & >Hapc & >Hrb & >Hra & >Hacc & >HTX) Hϕ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (n σ1) "%Hsche Hσ".
  rewrite /scheduled  /= /scheduler in Hsche.
  apply bool_decide_unpack in Hsche as Hcur.
  clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(Hnum & Hmem & Hreg & Hmb & Hrx & Hown & Haccess & Hrest)".
  pose proof (decode_instruction_valid w1 _ Hdecode) as Hvalidinstr.
  inversion Hvalidinstr as [| | src dst H3' H4' Hneqrarb | | | | | | | | |]; subst src dst; clear Hvalidinstr.
  destruct H3' as [HneqPCa HneqNZa].
  destruct H4' as [HneqPCb HneqNZb].
  iDestruct ((gen_reg_valid3 i PC ai ra w3 rb a Hcur) with "Hreg Hpc Hra Hrb") as "[%HPC [%Hra %Hrb]]".
  iDestruct ((gen_mem_valid ai w1) with "Hmem Hapc") as "%Hpc".
  iDestruct (access_agree_check_true (tpa ai) i with "Haccess Hacc") as "%Hai"; first set_solver.
  iDestruct (access_agree_check_false (tpa a) s Hnotin with "Haccess Hacc") as "%Ha".
  iDestruct (mb_valid_tx i p with "Hmb HTX") as %Htx.
  iSplit.
  + iPureIntro.
    rewrite /reducible.
    exists FailPageFaultI, σ1.
    simplify_eq.
    apply (step_exec_normal σ1 ai w1 (Ldr ra rb) (FailPageFaultI, σ1)); auto.
    * unfold read_memory.
      unfold check_read_access_addr.
      unfold check_read_access_page.
      rewrite Hai.
      simpl.
      case_bool_decide as Hcase; auto.
      exfalso.
      apply Hne.
      rewrite Hcase; reflexivity.
    * simpl.
      rewrite /lang.ldr.
      rewrite Hrb.
      rewrite /read_memory /check_read_access_addr /check_read_access_page Ha.
      simpl.
      repeat case_match; try done.
  + iModIntro.
    iIntros (m2 σ2) "HpropA %HstepP".
    iModIntro.
    iSplitL "HpropA";first (iFrame;done).
    eapply (step_ExecI_normal i _ ai w1 ) in HstepP;eauto.
    remember (exec _ σ1) as c2 eqn:Heqc2.
    rewrite /exec
            (ldr_FailPageFaultI_ldr_from_page σ1 ra rb a HneqPCa HneqNZa HneqPCb HneqNZb _ Hrb)
            /update_incr_PC /update_reg in Heqc2.
    2: {
      subst.
      done.
    }
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    iFrame.
    iSplitL "".
    rewrite just_scheduled_vms_no_step_empty.
    done.
    rewrite scheduled_true /=;last done.
    iApply "Hϕ"; iFrame.
    intros c.
    simplify_eq.
Qed.


Lemma ldr_access_tx{i w1 w3 p q s} ai a ra rb :
  decode_instruction w1 = Some (Ldr ra rb) ->
  tpa ai ∈ s ->
  (tpa a) = p ->
  (tpa ai) ≠ p ->
  {SS{{ ▷ (PC @@ i ->r ai) ∗
        ▷ (ai ->a w1) ∗
        ▷ (rb @@ i ->r a) ∗
        ▷ (ra @@ i ->r w3) ∗
        ▷ (i -@{ q }A> s) ∗
        ▷ (TX@ i := p)
      }}} ExecI @ i
    {{{ RET (false,FailPageFaultI);
        TX@ i := p ∗
        PC @@ i ->r ai ∗
        ai ->a w1 ∗
        rb @@ i ->r a ∗
        (i -@{ q }A> s) ∗
        ra @@ i ->r w3 }}}.
Proof.
  iIntros (Hdecode Hin Heq Hneq ϕ) "(>Hpc & >Hapc & >Hrb & >Hra & >Hacc & >Htx) Hϕ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (n σ1) "%Hsche Hσ".
  rewrite /scheduled  /= /scheduler in Hsche.
  apply bool_decide_unpack in Hsche as Hcur.
  clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(Hnum & Hmem & Hreg & Hmb & Hrx & Hown & Haccess & Hrest)".
  pose proof (decode_instruction_valid w1 _ Hdecode) as Hvalidinstr.
  inversion Hvalidinstr as [| | src dst H3' H4' Hneqrarb | | | | | | | | |]; subst src dst; clear Hvalidinstr.
  destruct H3' as [HneqPCa HneqNZa].
  destruct H4' as [HneqPCb HneqNZb].
  iDestruct ((gen_reg_valid3 i PC ai ra w3 rb a Hcur) with "Hreg Hpc Hra Hrb") as "[%HPC [%Hra %Hrb]]".
  iDestruct ((gen_mem_valid ai w1) with "Hmem Hapc") as "%Hpc".
  iDestruct (access_agree_check_true (tpa ai) i with "Haccess Hacc") as "%Hai"; first set_solver.
  iDestruct (mb_valid_tx i p with "Hmb Htx") as %Htx.
  iSplit.
  + iPureIntro.
    rewrite /reducible.
    exists FailPageFaultI, σ1.    
    apply (step_exec_normal σ1 ai w1 (Ldr ra rb) (FailPageFaultI, σ1)); auto.
    * rewrite /read_memory /check_read_access_addr /check_read_access_page.
      subst i.
      rewrite Hai.
      simpl.
      case_bool_decide as Heqb; try done.
      exfalso.
      apply Hneq.
      rewrite <-Heqb.
      assumption.
    * rewrite /exec /lang.ldr.
      destruct ra; try done.
      destruct rb; try done.
      rewrite Hrb.
      rewrite /read_memory /check_read_access_addr /check_read_access_page.
      subst i.
      rewrite Htx.
      rewrite Heq.
      destruct (bool_decide (p ≠ p)) eqn:Heq'; [by apply bool_decide_eq_true_1 in Heq'|].
      rewrite andb_false_r.
      reflexivity.
  + iModIntro.
    iIntros (m2 σ2) "HpropA %HstepP".
    iModIntro.
    iSplitL "HpropA";first (iFrame;done).
    eapply (step_ExecI_normal i _ ai w1 ) in HstepP;eauto.
    remember (exec _ σ1) as c2 eqn:Heqc2.
    rewrite /exec
            (ldr_FailPageFaultI_ldr_from_tx σ1 ra rb a HneqPCa HneqNZa HneqPCb HneqNZb _ Hrb)
            /update_incr_PC /update_reg in Heqc2.
    2: {
      subst.
      done.
    }
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    iFrame.
    iSplitL "".
    rewrite just_scheduled_vms_no_step_empty.
    done.
    rewrite scheduled_true /=;last done.
    iApply "Hϕ"; iFrame.
    rewrite <-Htx in Hneq.
    intros c.
    apply Hneq.
    done.
Qed.

End ldr.
