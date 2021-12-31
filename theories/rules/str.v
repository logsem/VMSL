From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base.
From HypVeri.algebra Require Import base mem reg pagetable mailbox.
From HypVeri.lang Require Import lang_extra reg_extra mem_extra.

Section str.

Context `{hypparams: HypervisorParameters}.
Context `{vmG: !gen_VMG Σ}.
  
Lemma str {E i w1 w2 w3 q1 q2 p} ai a ra rb:
  decode_instruction w1 = Some (Str ra rb) ->
  (tpa a) ≠ p ->
  {SS{{ ▷ (PC @@ i ->r ai) ∗
        ▷ (ai ->a w1) ∗
        ▷ (rb @@ i ->r a) ∗
        ▷ (a ->a w3) ∗
        ▷ (ra @@ i ->r w2) ∗
        ▷ ((tpa ai) -@{q1}A> [{[i]}]) ∗
        ▷ ((tpa a) -@{q2}A> [{[i]}]) ∗
        ▷ (RX@ i := p)}}}
    ExecI @ i; E
    {{{ RET (false, ExecI);
        PC @@ i ->r (ai ^+ 1)%f ∗
        ai ->a w1 ∗
        rb @@ i ->r a ∗
        a ->a w2 ∗
        ra @@ i ->r w2 ∗
        (tpa ai) -@{q1}A> [{[i]}] ∗
        (tpa a) -@{q2}A> [{[i]}] ∗
        RX@i := p }}}.
Proof.
  iIntros (Hdecode Hne_p ϕ) "(>Hpc & >Hapc & >Hrb & >Harb & >Hra & >Hacc_ai & >Hacc_a & >Hrx) Hϕ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (n σ1) "%Hsche Hσ".
  rewrite /scheduled  /= /scheduler in Hsche.
  apply bool_decide_unpack in Hsche as Hcur.
  clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(Hnum & Hmem & Hreg & Hmb & Hrxs & Hown & Haccess & Hrest)".
  pose proof (decode_instruction_valid w1 _ Hdecode) as Hvalidinstr.
  inversion Hvalidinstr as [| | | src dst Hvalidra Hvalidrb Hneqrarb | | | | | | | |] .
  subst src dst.
  inversion Hvalidra as [ HneqPCa HneqNZa ].
  inversion Hvalidrb as [ HneqPCb HneqNZb ].
  (* valid regs *)
  iDestruct ((gen_reg_valid3 i PC ai ra w2 rb a Hcur) with "Hreg Hpc Hra Hrb") as "[%HPC [%Hra %Hrb]]".
  (* valid pt *)
  iDestruct (access_agree_check_true (tpa a) i with "Haccess Hacc_a") as "%Ha"; first set_solver + .
  iDestruct (access_agree_check_true (tpa ai) i with "Haccess Hacc_ai") as "%Hai"; first set_solver + .
  (* valid mem *)
  iDestruct (gen_mem_valid2 ai w1 a w3 with "Hmem Hapc Harb") as "[%Hmemai %Hmema]".
  (* valid rx *)
  iDestruct (gen_rx_valid i p with "Hrx Hmb") as %Htx.
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
    rewrite /exec (str_ExecI σ1 ra rb w2 a HneqPCa HneqNZa HneqPCb HneqNZb _ Hra Hrb) /update_incr_PC in Heqc2.
    2: {
      subst.
      done.
    }
    2: {
      rewrite /check_access_addr.
      subst.
      by rewrite Ha.
    }
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    (* unchanged part *)
    rewrite_mem_unsafe.
    rewrite_reg_pc.
    rewrite_reg_global.
    iFrame "Hnum Hrxs Hmb Hown Haccess Hrest".
    (* updated part *)
    iDestruct ((gen_reg_update1_global PC i ai (ai ^+ 1)%f) with "Hreg Hpc") as ">[Hreg Hpc]";eauto.
    iDestruct ((gen_mem_update1 a w3 w2) with "Hmem Harb") as ">[Hmem Harb]";eauto.
    rewrite -> (update_offset_PC_update_PC1 _ i ai 1);eauto.
    iModIntro.
    iFrame "Hmem Hreg".
     iSplitL "".
    rewrite update_offset_PC_preserve_just_scheduled_vms.
    rewrite update_memory_unsafe_preserve_just_scheduled_vms.
    rewrite just_scheduled_vms_no_step_empty.
    by iSimpl.
    rewrite update_offset_PC_preserve_scheduled.
    rewrite update_memory_unsafe_preserve_scheduled.
    rewrite scheduled_true /=;last done.
    iApply "Hϕ".
    iFrame "Hpc Hapc Hrb Harb Hra Hacc_a Hacc_ai Hrx".
    apply (get_reg_gmap_get_reg_Some _ _ _ i) in HPC;eauto.
Qed.

Lemma str_same_page {E i w1 w2 w3 q p} ai a ra rb:
  decode_instruction w1 = Some (Str ra rb) ->
  (tpa a) ≠ p ->
  (tpa ai) = (tpa a) ->
  {SS{{ ▷ (PC @@ i ->r ai) ∗
        ▷ (ai ->a w1) ∗
        ▷ (rb @@ i ->r a) ∗
        ▷ (a ->a w3) ∗
        ▷ (ra @@ i ->r w2) ∗
        ▷ ((tpa ai) -@{q}A> [{[i]}]) ∗
        ▷ (RX@ i := p)}}}
    ExecI @ i; E
    {{{ RET (false, ExecI);
        PC @@ i ->r (ai ^+ 1)%f ∗
        ai ->a w1 ∗
        rb @@ i ->r a ∗
        a ->a w2 ∗
        ra @@ i ->r w2 ∗
        (tpa ai) -@{q}A> [{[i]}] ∗
        RX@i := p }}}.
Proof.
  iIntros (Hdecode Hne_p Heq ϕ) "(>Hpc & >Hapc & >Hrb & >Harb & >Hra & >Hacc_ai & >Hrx) Hϕ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (n σ1) "%Hsche Hσ".
  rewrite /scheduled  /= /scheduler in Hsche.
  apply bool_decide_unpack in Hsche as Hcur.
  clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(Hnum & Hmem & Hreg & Hmb & Hrxs & Hown & Haccess & Hrest)".
  pose proof (decode_instruction_valid w1 _ Hdecode) as Hvalidinstr.
  inversion Hvalidinstr as [| | | src dst Hvalidra Hvalidrb Hneqrarb | | | | | | | |] .
  subst src dst.
  inversion Hvalidra as [ HneqPCa HneqNZa ].
  inversion Hvalidrb as [ HneqPCb HneqNZb ].
  (* valid regs *)
  iDestruct ((gen_reg_valid3 i PC ai ra w2 rb a Hcur) with "Hreg Hpc Hra Hrb") as "[%HPC [%Hra %Hrb]]".
  (* valid pt *)
  iDestruct (access_agree_check_true (tpa ai) i with "Haccess Hacc_ai") as "%Hai"; first set_solver + .
  (* valid mem *)
  iDestruct (gen_mem_valid2 ai w1 a w3 with "Hmem Hapc Harb") as "[%Hmemai %Hmema]".
  (* valid rx *)
  iDestruct (gen_rx_valid i p with "Hrx Hmb") as %Htx.
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
    rewrite /exec (str_ExecI σ1 ra rb w2 a HneqPCa HneqNZa HneqPCb HneqNZb _ Hra Hrb) /update_incr_PC in Heqc2.
    2: {
      subst.
      done.
    }
    2: {
      rewrite /check_access_addr.
      subst.
      rewrite -Heq //.
    }
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    (* unchanged part *)
    rewrite_mem_unsafe.
    rewrite_reg_pc.
    rewrite_reg_global.
    iFrame "Hnum Hrxs Hmb Hown Haccess Hrest".
    (* updated part *)
    iDestruct ((gen_reg_update1_global PC i ai (ai ^+ 1)%f) with "Hreg Hpc") as ">[Hreg Hpc]";eauto.
    iDestruct ((gen_mem_update1 a w3 w2) with "Hmem Harb") as ">[Hmem Harb]";eauto.
    rewrite -> (update_offset_PC_update_PC1 _ i ai 1);eauto.
    iModIntro.
    iFrame "Hmem Hreg".
     iSplitL "".
    rewrite update_offset_PC_preserve_just_scheduled_vms.
    rewrite update_memory_unsafe_preserve_just_scheduled_vms.
    rewrite just_scheduled_vms_no_step_empty.
    by iSimpl.
    rewrite update_offset_PC_preserve_scheduled.
    rewrite update_memory_unsafe_preserve_scheduled.
    rewrite scheduled_true /=;last done.
    iApply "Hϕ".
    iFrame "Hpc Hapc Hrb Harb Hra Hacc_ai Hrx".
    apply (get_reg_gmap_get_reg_Some _ _ _ i) in HPC;eauto.
Qed.

Lemma str_same_addr {E i w1 w2 q p} ai a ra rb:
  decode_instruction w1 = Some (Str ra rb) ->
  (tpa a) ≠ p ->
  ai = a ->
  {SS{{ ▷ (PC @@ i ->r ai) ∗
        ▷ (ai ->a w1) ∗
        ▷ (rb @@ i ->r a) ∗
        ▷ (ra @@ i ->r w2) ∗
        ▷ ((tpa ai) -@{q}A> [{[i]}]) ∗
        ▷ (RX@ i := p)}}}
    ExecI @ i; E
    {{{ RET (false, ExecI);
        PC @@ i ->r (ai ^+ 1)%f ∗
        ai ->a w2 ∗
        rb @@ i ->r a ∗
        ra @@ i ->r w2 ∗
        (tpa ai) -@{q}A> [{[i]}] ∗
        RX@i := p }}}.
Proof.
  iIntros (Hdecode Hne_p Heq ϕ) "(>Hpc & >Hapc & >Hrb & >Hra & >Hacc_ai & >Hrx) Hϕ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (n σ1) "%Hsche Hσ".
  rewrite /scheduled  /= /scheduler in Hsche.
  apply bool_decide_unpack in Hsche as Hcur.
  clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(Hnum & Hmem & Hreg & Hmb & Hrxs & Hown & Haccess & Hrest)".
  pose proof (decode_instruction_valid w1 _ Hdecode) as Hvalidinstr.
  inversion Hvalidinstr as [| | | src dst Hvalidra Hvalidrb Hneqrarb | | | | | | | |] .
  subst src dst.
  inversion Hvalidra as [ HneqPCa HneqNZa ].
  inversion Hvalidrb as [ HneqPCb HneqNZb ].
  (* valid regs *)
  iDestruct ((gen_reg_valid3 i PC ai ra w2 rb a Hcur) with "Hreg Hpc Hra Hrb") as "[%HPC [%Hra %Hrb]]".
  (* valid pt *)
  iDestruct (access_agree_check_true (tpa ai) i with "Haccess Hacc_ai") as "%Hai"; first set_solver + .
  (* valid mem *)
  iDestruct (gen_mem_valid ai w1 with "Hmem Hapc ") as "%Hmemai".
  (* valid rx *)
  iDestruct (gen_rx_valid i p with "Hrx Hmb") as %Htx.
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
    rewrite /exec (str_ExecI σ1 ra rb w2 a HneqPCa HneqNZa HneqPCb HneqNZb _ Hra Hrb) /update_incr_PC in Heqc2.
    2: {
      subst.
      done.
    }
    2: {
      rewrite /check_access_addr.
      subst.
      done.
    }
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    (* unchanged part *)
    rewrite_mem_unsafe.
    rewrite_reg_pc.
    rewrite_reg_global.
    iFrame "Hnum Hrxs Hmb Hown Haccess Hrest".
    (* updated part *)
    iDestruct ((gen_reg_update1_global PC i ai (ai ^+ 1)%f) with "Hreg Hpc") as ">[Hreg Hpc]";eauto.
    iDestruct ((gen_mem_update1 ai w1 w2) with "Hmem Hapc") as ">[Hmem Harb]";eauto.
    rewrite -> (update_offset_PC_update_PC1 _ i ai 1);eauto.
    iModIntro.
    subst a.
    iFrame "Hmem Hreg".
    iSplitL "".
    rewrite update_offset_PC_preserve_just_scheduled_vms.
    rewrite update_memory_unsafe_preserve_just_scheduled_vms.
    rewrite just_scheduled_vms_no_step_empty.
    by iSimpl.
    rewrite update_offset_PC_preserve_scheduled.
    rewrite update_memory_unsafe_preserve_scheduled.
    rewrite scheduled_true /=;last done.
    iApply "Hϕ".
    iFrame "Hpc Harb Hrb Hra Hacc_ai Hrx".
    apply (get_reg_gmap_get_reg_Some _ _ _ i) in HPC;eauto.
Qed.

Lemma str_access_rx {i w1 w2 p q} ai a ra rb :
  decode_instruction w1 = Some (Str ra rb) ->
  (tpa a) = p ->
  {SS{{  ▷ (PC @@ i ->r ai) ∗
         ▷ (ai ->a w1) ∗
         ▷ (rb @@ i ->r a) ∗
         ▷ (ra @@ i ->r w2) ∗
         ▷ ((tpa ai) -@{q}A> [{[i]}]) ∗
         ▷ (RX@ i := p) }}}
    ExecI @ i
    {{{ RET (false,FailPageFaultI);
        PC @@ i ->r ai ∗
        ai ->a w1 ∗
        rb @@ i ->r a ∗
        (tpa ai) -@{q}A> [{[i]}] ∗
        ra @@ i ->r w2 ∗
        RX@ i := p
    }}}.
Proof.
  iIntros (Hdecode Heq ϕ) "(>Hpc & >Hapc & >Hrb & >Hra & >Hacc_ai & >Hrx) Hϕ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (n σ1) "%Hsche Hσ".
  rewrite /scheduled  /= /scheduler in Hsche.
  apply bool_decide_unpack in Hsche as Hcur.
  clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(Hnum & Hmem & Hreg & Hmb & Hrxs & Hown & Haccess & Hrest)".
  pose proof (decode_instruction_valid w1 _ Hdecode) as Hvalidinstr.
  inversion Hvalidinstr as [| | | src dst H3' H4' Hneqrarb | | | | | | | |]; subst src dst; clear Hvalidinstr.
  destruct H3' as [HneqPCa HneqNZa].
  destruct H4' as [HneqPCb HneqNZb].
  iDestruct ((gen_reg_valid3 i PC ai ra w2 rb a Hcur) with "Hreg Hpc Hra Hrb") as "[%HPC [%Hra %Hrb]]".
  iDestruct ((gen_mem_valid ai w1) with "Hmem Hapc") as "%Hpc".
  iDestruct (access_agree_check_true (tpa ai) i with "Haccess Hacc_ai") as "%Hai"; first set_solver + .
  iDestruct (gen_rx_valid i p with "Hrx Hmb") as %Hrx.
  iSplit.
    + iPureIntro.
      eapply (reducible_normal i _ ai w1);eauto.
    + iModIntro.
      iIntros (m2 σ2) "HpropA %HstepP".
      iSplitL "HpropA";first (iFrame;done).
      iModIntro.
      eapply (step_ExecI_normal i _ ai w1 ) in HstepP;eauto.
      remember (exec _ σ1) as c2 eqn:Heqc2.
      rewrite /exec
      (str_FailPageFaultI_str_to_rx σ1 ra rb w2 a HneqPCa HneqNZa HneqPCb HneqNZb _ Hra Hrb)
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

Lemma str_no_access {i w1 w2 s q} ai a ra rb :
  decode_instruction w1 = Some (Str ra rb) ->
  i ∉ s ->
  {SS{{  ▷ (PC @@ i ->r ai) ∗
         ▷ (ai ->a w1) ∗
         ▷ (rb @@ i ->r a) ∗
         ▷ (ra @@ i ->r w2) ∗
         ▷ ((tpa ai) -@{q}A> [{[i]}]) ∗
         ▷ ((tpa a) -@{1}A> [s])}}}
    ExecI @ i
    {{{ RET (false,FailPageFaultI);
        PC @@ i ->r ai ∗
        ai ->a w1 ∗
        rb @@ i ->r a ∗
        (tpa ai) -@{q}A> [{[i]}] ∗
        ra @@ i ->r w2 }}}.
Proof.
  iIntros (Hdecode Hnotin ϕ) "(>Hpc & >Hapc & >Hrb & >Hra & >Hacc_ai & >Hacc_a) Hϕ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (n σ1) "%Hsche Hσ".
  rewrite /scheduled  /= /scheduler in Hsche.
  apply bool_decide_unpack in Hsche as Hcur.
  clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(Hnum & Hmem & Hreg & Hmb & Hrxs & Hown & Haccess & Hrest)".
  pose proof (decode_instruction_valid w1 _ Hdecode) as Hvalidinstr.
  inversion Hvalidinstr as [| | | src dst H3' H4' Hneqrarb | | | | | | | |]; subst src dst; clear Hvalidinstr.
  destruct H3' as [HneqPCa HneqNZa].
  destruct H4' as [HneqPCb HneqNZb].
  iDestruct ((gen_reg_valid3 i PC ai ra w2 rb a Hcur) with "Hreg Hpc Hra Hrb") as "[%HPC [%Hra %Hrb]]".
  iDestruct ((gen_mem_valid ai w1) with "Hmem Hapc") as "%Hpc".
  iDestruct (access_agree_check_true (tpa ai) i with "Haccess Hacc_ai") as "%Hai"; first set_solver + .
  iDestruct ((access_agree_check_false (tpa a) s Hnotin) with "Haccess Hacc_a") as "%Ha".
  iSplit.
  + iPureIntro.
    rewrite /reducible.
    exists FailPageFaultI, σ1.
    simplify_eq.
    rewrite check_access_page_mem_eq in Hai.
    apply (step_exec_normal σ1 ai w1 (Str ra rb) (FailPageFaultI, σ1)); auto.
    * rewrite /is_valid_PC HPC.
      simpl.
      rewrite Hai //.
    * rewrite /get_memory Hai ; done.
    * rewrite /exec /lang.str.
      destruct ra; try done.
      destruct rb; try done.
      rewrite Hra.
      simpl.
      rewrite Hrb.
      destruct (get_mail_boxes σ1 !!! get_current_vm σ1) as [t [r1 r2]].
      simpl in *.
      destruct (decide (to_pid_aligned a = r1)); try done.
      rewrite check_access_page_mem_eq in Ha.
      rewrite /update_memory Ha //.
  + iModIntro.
    iIntros (m2 σ2) "HpropA %HstepP".
    iModIntro.
    iSplitL "HpropA";first (iFrame;done).
    eapply (step_ExecI_normal i _ ai w1 ) in HstepP;eauto.
    remember (exec _ σ1) as c2 eqn:Heqc2.
    rewrite /exec
            (str_FailPageFaultI_str_to_page σ1 ra rb w2 a HneqPCa HneqNZa HneqPCb HneqNZb _ Hra Hrb)
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

End str.
