From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base.
From HypVeri.algebra Require Import base reg mem mailbox pagetable.
From HypVeri.lang Require Import lang_extra reg_extra mem_extra.

Section ldr.

Context `{hypparams: HypervisorParameters}.
Context `{vmG: !gen_VMG Σ}.
  
Lemma ldr {E i w1 w2 w3 q1 q2 p} ai a ra rb:
  decode_instruction w1 = Some (Ldr ra rb) ->
  (tpa a) ≠ p ->
  {SS{{ ▷ (PC @@ i ->r ai) ∗
        ▷ (ai ->a w1) ∗
        ▷ (rb @@ i ->r a) ∗
        ▷ (a ->a w2) ∗
        ▷ (ra @@ i ->r w3) ∗
        ▷ ((tpa ai) -@{q1}A> [{[i]}]) ∗
        ▷ ((tpa a) -@{q2}A> [{[i]}]) ∗
        ▷ (TX@ i := p)}}}
    ExecI @ i; E
    {{{ RET (false,ExecI);
        PC @@ i ->r (ai ^+ 1)%f ∗
        ai ->a w1 ∗
        rb @@ i ->r a ∗
        a ->a w2 ∗
        ra @@ i ->r w2 ∗
        (tpa ai) -@{q1}A> [{[i]}] ∗
        (tpa a) -@{q2}A> [{[i]}] ∗
        TX@ i := p }}}.
Proof.
  iIntros (Hdecode Hne_p ϕ) "(>Hpc & >Hapc & >Hrb & >Harb & >Hra & >Hacc_ai & >Hacc_a & >Htx) Hϕ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (n σ1) "%Hsche Hσ".
  rewrite /scheduled  /= /scheduler in Hsche.
  apply bool_decide_unpack in Hsche as Hcur.
  clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(Hnum & Hmem & Hreg & Hrx & Hown & Hmb & Haccess & Hrest)".
  pose proof (decode_instruction_valid w1 _ Hdecode) as Hvalidinstr.
  inversion Hvalidinstr as [| | src dst H3' H4' Hneqrarb | | | | | | | | |]; subst src dst; clear Hvalidinstr.
  destruct H3' as [HneqPCa HneqNZa].
  destruct H4' as [HneqPCb HneqNZb].
  iDestruct ((gen_reg_valid3 i PC ai ra w3 rb a Hcur) with "Hreg Hpc Hra Hrb") as "[%HPC [%Hra %Hrb]]".
  (* valid pt *)
  iDestruct (access_agree_check_true (tpa a) i with "Haccess Hacc_a") as "%Ha"; first set_solver + .
  iDestruct (access_agree_check_true (tpa ai) i with "Haccess Hacc_ai") as "%Hai"; first set_solver + .
  (* valid mem *)
  iDestruct (gen_mem_valid2 ai w1 a w2 with "Hmem Hapc Harb") as "[%Hmemai %Hmema]".
  iDestruct (gen_tx_valid i p with "Htx Hmb") as %Htx.
  iSplit.
  - (* reducible *)
    iPureIntro.
    eapply (reducible_normal i _ ai w1);eauto.
  - (* step *)
    iModIntro.
    iIntros (m2 σ2) "HpropA %HstepP".
    iSplitL "HpropA";first (iFrame;done).
    eapply (step_ExecI_normal i _ ai w1 ) in HstepP;eauto.
    remember (exec _ σ1) as c2 eqn:Heqc2.
    rewrite /exec (ldr_ExecI σ1 ra rb a w2 HneqPCa HneqNZa HneqPCb HneqNZb _ Hrb)
            /update_incr_PC /update_reg in Heqc2.
    2: {
      subst.
      done.
    }
    2: {
      rewrite /get_memory /check_access_addr.
      subst.
      by rewrite Ha.
    }
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    (* unchanged part *)
    rewrite_reg_pc.
    rewrite_reg_global.
    iFrame "Hnum Hmem Hown Hrx Hmb Haccess Hrest".
    rewrite Hcur.
    (* updated part *)
    rewrite -> (update_offset_PC_update_PC1 _ i ai 1);eauto.
    + rewrite  update_reg_global_update_reg; [|eexists; rewrite get_reg_gmap_get_reg_Some; eauto ].
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
      iFrame "Hreg Hapc Harb Hra Hrb Hacc_a Hacc_ai Htx".
    + rewrite update_reg_global_update_reg;[|solve_reg_lookup].
      repeat solve_reg_lookup.
      intros P; symmetry in P;inversion P; contradiction.
Qed.

Lemma ldr_same_page {E i w1 w2 w3 q1 p} ai a ra rb:
  decode_instruction w1 = Some (Ldr ra rb) ->
  (tpa a) ≠ p ->
  (tpa ai) = (tpa a) ->
  {SS{{ ▷ (PC @@ i ->r ai) ∗
        ▷ (ai ->a w1) ∗
        ▷ (rb @@ i ->r a) ∗
        ▷ (a ->a w2) ∗
        ▷ (ra @@ i ->r w3) ∗
        ▷ ((tpa ai) -@{q1}A> [{[i]}]) ∗
        ▷ (TX@ i := p)}}}
    ExecI @ i; E
    {{{ RET (false,ExecI);
        PC @@ i ->r (ai ^+ 1)%f ∗
        ai ->a w1 ∗
        rb @@ i ->r a ∗
        a ->a w2 ∗
        ra @@ i ->r w2 ∗
        (tpa ai) -@{q1}A> [{[i]}] ∗
        TX@ i := p }}}.
Proof.
  iIntros (Hdecode Hne_p Heq_p ϕ) "(>Hpc & >Hapc & >Hrb & >Harb & >Hra & >Hacc & >Htx) Hϕ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (n σ1) "%Hsche Hσ".
  rewrite /scheduled  /= /scheduler in Hsche.
  apply bool_decide_unpack in Hsche as Hcur.
  clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(Hnum & Hmem & Hreg & Hrx & Hown & Hmb & Haccess & Hrest)".
  pose proof (decode_instruction_valid w1 _ Hdecode) as Hvalidinstr.
  inversion Hvalidinstr as [| | src dst H3' H4' Hneqrarb | | | | | | | | |]; subst src dst; clear Hvalidinstr.
  destruct H3' as [HneqPCa HneqNZa].
  destruct H4' as [HneqPCb HneqNZb].
  iDestruct ((gen_reg_valid3 i PC ai ra w3 rb a Hcur) with "Hreg Hpc Hra Hrb") as "[%HPC [%Hra %Hrb]]".
  (* valid pt *)
  iDestruct (access_agree_check_true (tpa ai) i with "Haccess Hacc") as "%Hai"; first set_solver + .
  (* valid mem *)
  iDestruct (gen_mem_valid2 ai w1 a w2 with "Hmem Hapc Harb") as "[%Hmemai %Hmema]".
  iDestruct (gen_tx_valid i p with "Htx Hmb") as %Htx.
  iSplit.
  - (* reducible *)
    iPureIntro.
    eapply (reducible_normal i _ ai w1);eauto.
  - (* step *)
    iModIntro.
    iIntros (m2 σ2) "HpropA %HstepP".
    iSplitL "HpropA";first (iFrame;done).
    eapply (step_ExecI_normal i _ ai w1 ) in HstepP;eauto.
    remember (exec _ σ1) as c2 eqn:Heqc2.
    rewrite /exec (ldr_ExecI σ1 ra rb a w2 HneqPCa HneqNZa HneqPCb HneqNZb _ Hrb)
            /update_incr_PC /update_reg in Heqc2.
    2: {
      subst.
      done.
    }
    2: {
      rewrite /get_memory /check_access_addr.
      subst.
      rewrite -Heq_p Hai //.
    }
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    (* unchanged part *)
    rewrite_reg_pc.
    rewrite_reg_global.
    iFrame "Hnum Hmem Hown Hrx Hmb Haccess Hrest".
    rewrite Hcur.
    (* updated part *)
    rewrite -> (update_offset_PC_update_PC1 _ i ai 1);eauto.
    + rewrite  update_reg_global_update_reg; [|eexists; rewrite get_reg_gmap_get_reg_Some; eauto ].
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
    + rewrite update_reg_global_update_reg;[|solve_reg_lookup].
      repeat solve_reg_lookup.
      intros P; symmetry in P;inversion P; contradiction.
Qed.


Lemma ldr_same_addr {E i w1 w2 q1 p} ai a ra rb:
  decode_instruction w1 = Some (Ldr ra rb) ->
  (tpa a) ≠ p ->
  ai = a ->
  {SS{{ ▷ (PC @@ i ->r ai) ∗
        ▷ (ai ->a w1) ∗
        ▷ (rb @@ i ->r a) ∗
        ▷ (ra @@ i ->r w2) ∗
        ▷ ((tpa ai) -@{q1}A> [{[i]}]) ∗
        ▷ (TX@ i := p)}}}
    ExecI @ i; E
    {{{ RET (false,ExecI);
        PC @@ i ->r (ai ^+ 1)%f ∗
        ai ->a w1 ∗
        rb @@ i ->r a ∗
        ra @@ i ->r w1 ∗
        (tpa ai) -@{q1}A> [{[i]}] ∗
        TX@ i := p }}}.
Proof.
  iIntros (Hdecode Hne_p Heq_a ϕ) "(>Hpc & >Ha & >Hrb & >Hra & >Hacc & >Htx) Hϕ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (n σ1) "%Hsche Hσ".
  rewrite /scheduled  /= /scheduler in Hsche.
  apply bool_decide_unpack in Hsche as Hcur.
  clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(Hnum & Hmem & Hreg & Hrx & Hown & Hmb & Haccess & Hrest)".
  pose proof (decode_instruction_valid w1 _ Hdecode) as Hvalidinstr.
  inversion Hvalidinstr as [| | src dst H3' H4' Hneqrarb | | | | | | | | |]; subst src dst; clear Hvalidinstr.
  destruct H3' as [HneqPCa HneqNZa].
  destruct H4' as [HneqPCb HneqNZb].
  iDestruct ((gen_reg_valid3 i PC ai ra w2 rb a Hcur) with "Hreg Hpc Hra Hrb") as "[%HPC [%Hra %Hrb]]".
  (* valid pt *)
  iDestruct (access_agree_check_true (tpa ai) i with "Haccess Hacc") as "%Hai"; first set_solver + .
  (* valid mem *)
  iDestruct (gen_mem_valid ai w1 with "Hmem Ha") as "%Hmemai".
  iDestruct (gen_tx_valid i p with "Htx Hmb") as %Htx.
  iSplit.
  - (* reducible *)
    iPureIntro.
    eapply (reducible_normal i _ ai w1);eauto.
  - (* step *)
    iModIntro.
    iIntros (m2 σ2) "HpropA %HstepP".
    iSplitL "HpropA";first (iFrame;done).
    eapply (step_ExecI_normal i _ ai w1 ) in HstepP;eauto.
    remember (exec _ σ1) as c2 eqn:Heqc2.
    rewrite /exec (ldr_ExecI σ1 ra rb a w1 HneqPCa HneqNZa HneqPCb HneqNZb _ Hrb)
            /update_incr_PC /update_reg in Heqc2.
    2: {
      subst.
      done.
    }
    2: {
      rewrite /get_memory /check_access_addr.
      subst.
      rewrite Hai //.
    }
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    (* unchanged part *)
    rewrite_reg_pc.
    rewrite_reg_global.
    iFrame "Hnum Hmem Hown Hrx Hmb Haccess Hrest".
    rewrite Hcur.
    (* updated part *)
    rewrite -> (update_offset_PC_update_PC1 _ i ai 1);eauto.
    + rewrite  update_reg_global_update_reg; [|eexists; rewrite get_reg_gmap_get_reg_Some; eauto ].
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
      iFrame "Hreg Ha Hra Hrb Hacc Htx".
    + rewrite update_reg_global_update_reg;[|solve_reg_lookup].
      repeat solve_reg_lookup.
      intros P; symmetry in P;inversion P; contradiction.
Qed.

Lemma ldr_no_access{i w1 w3 s q} ai a ra rb :
  decode_instruction w1 = Some (Ldr ra rb) ->
  i ∉ s ->
  {SS{{ ▷ (PC @@ i ->r ai) ∗
        ▷ (ai ->a w1) ∗
        ▷ (rb @@ i ->r a) ∗
        ▷ (ra @@ i ->r w3) ∗
        ▷ ((tpa ai) -@{q}A> [{[i]}]) ∗
        ▷ ((tpa a) -@{1}A> [s]) 
      }}} ExecI @ i
    {{{ RET (false,FailPageFaultI);
        PC @@ i ->r ai ∗
        ai ->a w1 ∗
        rb @@ i ->r a ∗
        (tpa a) -@{1}A> [s] ∗
        (tpa ai) -@{q}A> [{[i]}] ∗
        ra @@ i ->r w3 }}}.
Proof.
  iIntros (Hdecode Hnotin ϕ) "(>Hpc & >Hapc & >Hrb & >Hra & >Hacc_ai & >Hacc_a) Hϕ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (n σ1) "%Hsche Hσ".
  rewrite /scheduled  /= /scheduler in Hsche.
  apply bool_decide_unpack in Hsche as Hcur.
  clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(Hnum & Hmem & Hreg & Hrx & Hown & Hmb & Haccess & Hrest)".
  pose proof (decode_instruction_valid w1 _ Hdecode) as Hvalidinstr.
  inversion Hvalidinstr as [| | src dst H3' H4' Hneqrarb | | | | | | | | |]; subst src dst; clear Hvalidinstr.
  destruct H3' as [HneqPCa HneqNZa].
  destruct H4' as [HneqPCb HneqNZb].
  iDestruct ((gen_reg_valid3 i PC ai ra w3 rb a Hcur) with "Hreg Hpc Hra Hrb") as "[%HPC [%Hra %Hrb]]".
  iDestruct ((gen_mem_valid ai w1) with "Hmem Hapc") as "%Hpc".
  iDestruct (access_agree_check_true (tpa ai) i with "Haccess Hacc_ai") as "%Hai"; first set_solver + .
  iDestruct ((access_agree_check_false (tpa a) s Hnotin) with "Haccess Hacc_a") as "%Ha".
  iSplit.
  + iPureIntro.
    rewrite /reducible.
    exists FailPageFaultI, σ1.
    simplify_eq.
    rewrite check_access_page_mem_eq in Hai.
    apply (step_exec_normal σ1 ai w1 (Ldr ra rb) (FailPageFaultI, σ1)); auto.
    * rewrite /is_valid_PC HPC /=.
      rewrite Hai //.
    * rewrite /get_memory Hai //.
    * rewrite /exec .
      destruct ra; try done.
      destruct rb; try done.
      rewrite /lang.ldr /= Hrb.
      destruct (get_mail_boxes σ1 !!! get_current_vm σ1) as [t r].
      simpl in *.
      destruct (decide (to_pid_aligned a = t)); try done.
      rewrite /get_memory.
      rewrite check_access_page_mem_eq in Ha.
      by rewrite Ha.
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
Qed.


Lemma ldr_access_tx{i w1 w3 p q} ai a ra rb :
  decode_instruction w1 = Some (Ldr ra rb) ->
   (tpa a) = p ->
  {SS{{ ▷ (PC @@ i ->r ai) ∗
        ▷ (ai ->a w1) ∗
        ▷ (rb @@ i ->r a) ∗
        ▷ (ra @@ i ->r w3) ∗
        ▷ ((tpa ai) -@{q}A> [{[i]}]) ∗
        ▷ (TX@ i := p)
      }}} ExecI @ i
    {{{ RET (false,FailPageFaultI);
        TX@ i := p ∗
        PC @@ i ->r ai ∗
        ai ->a w1 ∗
        rb @@ i ->r a ∗
        (tpa ai) -@{q}A> [{[i]}] ∗
        ra @@ i ->r w3 }}}.
Proof.
  iIntros (Hdecode Heq ϕ) "(>Hpc & >Hapc & >Hrb & >Hra & >Hacc_ai & >Htx) Hϕ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (n σ1) "%Hsche Hσ".
  rewrite /scheduled  /= /scheduler in Hsche.
  apply bool_decide_unpack in Hsche as Hcur.
  clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(Hnum & Hmem & Hreg & Hrx & Hown & Hmb & Haccess & Hrest)".
  pose proof (decode_instruction_valid w1 _ Hdecode) as Hvalidinstr.
  inversion Hvalidinstr as [| | src dst H3' H4' Hneqrarb | | | | | | | | |]; subst src dst; clear Hvalidinstr.
  destruct H3' as [HneqPCa HneqNZa].
  destruct H4' as [HneqPCb HneqNZb].
  iDestruct ((gen_reg_valid3 i PC ai ra w3 rb a Hcur) with "Hreg Hpc Hra Hrb") as "[%HPC [%Hra %Hrb]]".
  iDestruct ((gen_mem_valid ai w1) with "Hmem Hapc") as "%Hpc".
  iDestruct (access_agree_check_true (tpa ai) i with "Haccess Hacc_ai") as "%Hai"; first set_solver + .
  iDestruct (gen_tx_valid i p with "Htx Hmb") as %Htx.
  iSplit.
  + iPureIntro.
    rewrite /reducible.
    exists FailPageFaultI, σ1.
    simplify_eq.
    rewrite check_access_page_mem_eq in Hai.
    apply (step_exec_normal σ1 ai w1 (Ldr ra rb) (FailPageFaultI, σ1)); auto.
    * rewrite /is_valid_PC HPC /= Hai //.
    * rewrite /get_memory Hai; done.
    * rewrite /exec /lang.ldr.
      destruct ra; try done.
      destruct rb; try done.
      rewrite Hrb.
      destruct (get_mail_boxes σ1 !!! get_current_vm σ1) as [t r].
      simpl in *.
      destruct (decide (to_pid_aligned a = t)); done.
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
Qed.


End ldr.
