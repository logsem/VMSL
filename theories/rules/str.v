From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base machine_extra.
From HypVeri.algebra Require Import base mem reg pagetable mailbox base_extra.
From HypVeri.lang Require Import lang_extra reg_extra mem_extra.

Section str.

Context `{hypparams: HypervisorParameters}.
Context `{vmG: !gen_VMG Σ}.
  
Lemma str {E i w1 w2 w3 q p p' s} ai a ra rb:
  decode_instruction w1 = Some (Str ra rb) ->
  {[ tpa a; tpa ai ]} ⊆ s ->
  tpa ai ≠ p' ->
  (tpa a) ≠ p ->
  {SS{{ ▷ (PC @@ i ->r ai) ∗
        ▷ (ai ->a w1) ∗
        ▷ (rb @@ i ->r a) ∗
        ▷ (a ->a w3) ∗
        ▷ (ra @@ i ->r w2) ∗
        ▷ (i -@{q}A> s) ∗
        ▷ (TX@ i := p') ∗
        ▷ (RX@ i := p)}}}
    ExecI @ i; E
    {{{ RET (false, ExecI);
        PC @@ i ->r (ai ^+ 1)%f ∗
        ai ->a w1 ∗
        rb @@ i ->r a ∗
        a ->a w2 ∗
        ra @@ i ->r w2 ∗
        i -@{q}A> s ∗
        (TX@ i := p') ∗
        RX@i := p }}}.
Proof.
  iIntros (Hdecode Hin Hne Hne' ϕ) "(>Hpc & >Hapc & >Hrb & >Harb & >Hra & >Hacc & >HTX & >Hrx) Hϕ".
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
  iDestruct (access_agree_check_true (tpa a) i with "Haccess Hacc") as "%Ha"; first set_solver.
  iDestruct (access_agree_check_true (tpa ai) i with "Haccess Hacc") as "%Hai"; first set_solver.
  (* valid mem *)
  iDestruct (gen_mem_valid2 ai w1 a w3 with "Hmem Hapc Harb") as "[%Hmemai %Hmema]".
  (* valid rx/tx *)
  iDestruct (mb_valid_tx i p' with "Hmb HTX") as %Htx.
  iDestruct (mb_valid_rx i p with "Hmb Hrx") as %Hrx.
  iSplit.
  - (* reducible *)
    iPureIntro.
    eapply (reducible_normal i _ ai w1);eauto.
    by rewrite Htx.
  - (* step *)
    iModIntro.
    iIntros (m2 σ2) "HpropA %HstepP".
    iSplitL "HpropA";first (iFrame;done).
    eapply (step_ExecI_normal i _ ai w1 ) in HstepP; eauto.
    2 : by rewrite Htx.
    remember (exec _ σ1) as c2 eqn:Heqc2.
    rewrite /exec (str_ExecI σ1 ra rb w2 a HneqPCa HneqNZa HneqPCb HneqNZb _ _ Hra Hrb) /update_incr_PC in Heqc2.
    2: by rewrite Hcur Hrx.
    2: by rewrite Hcur Ha.
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
    rewrite p_upd_pc_mem.
    all: try rewrite p_upd_pc_pgt //.
    all: try rewrite p_upd_pc_trans //.
    all: try rewrite p_upd_pc_mb //.
    iFrame "Hnum Hrxs Hmb Hown Haccess Hrest".
    (* updated part *)
    iDestruct ((gen_reg_update1_global PC i ai (ai ^+ 1)%f) with "Hreg Hpc") as ">[Hreg Hpc]";eauto.
    iDestruct ((gen_mem_update1 a w3 w2) with "Hmem Harb") as ">[Hmem Harb]";eauto.
    rewrite -> (u_upd_pc_regs _ i ai 1);eauto.
    iModIntro.
    iFrame "Hmem Hreg".
    iSplitL "".
    rewrite update_offset_PC_preserve_just_scheduled_vms.
    rewrite update_memory_preserve_just_scheduled_vms.
    rewrite just_scheduled_vms_no_step_empty.
    by iSimpl.
    rewrite update_offset_PC_preserve_scheduled.
    rewrite update_memory_preserve_scheduled.
    rewrite scheduled_true /=;last done.
    iApply "Hϕ".
    iFrame "Hpc Hapc Hrb Harb Hra Hacc Hrx HTX".
    apply (get_reg_gmap_get_reg_Some _ _ _ i) in HPC;eauto.
Qed.

Lemma str_same_page {E i w1 w2 w3 q p p' s} ai a ra rb:
  decode_instruction w1 = Some (Str ra rb) ->
  tpa ai ∈ s ->
  (tpa a) ≠ p ->
  (tpa ai) ≠ p' ->
  (tpa ai) = (tpa a) ->
  {SS{{ ▷ (PC @@ i ->r ai) ∗
        ▷ (ai ->a w1) ∗
        ▷ (rb @@ i ->r a) ∗
        ▷ (a ->a w3) ∗
        ▷ (ra @@ i ->r w2) ∗
        ▷ (i -@{q}A> s) ∗
        ▷ TX@ i := p' ∗
        ▷ (RX@ i := p)}}}
    ExecI @ i; E
    {{{ RET (false, ExecI);
        PC @@ i ->r (ai ^+ 1)%f ∗
        ai ->a w1 ∗
        rb @@ i ->r a ∗
        a ->a w2 ∗
        ra @@ i ->r w2 ∗
        i -@{q}A> s ∗
        TX@ i := p' ∗                   
        RX@i := p }}}.
Proof.
  iIntros (Hdecode Hin Hne_p Hne Heq ϕ) "(>Hpc & >Hapc & >Hrb & >Harb & >Hra & >Hacc & >HTX & >Hrx) Hϕ".
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
  iDestruct (access_agree_check_true (tpa ai) i with "Haccess Hacc") as "%Hai"; first set_solver.
  (* valid mem *)
  iDestruct (gen_mem_valid2 ai w1 a w3 with "Hmem Hapc Harb") as "[%Hmemai %Hmema]".
  (* valid rx *)
  iDestruct (mb_valid_rx i p with "Hmb Hrx") as %Hrx.
  iDestruct (mb_valid_tx i p' with "Hmb HTX") as %Htx.
  iSplit.
  - (* reducible *)
    iPureIntro.
    eapply (reducible_normal i _ ai w1);eauto.
    by rewrite Htx.
  - (* step *)
    iModIntro.
    iIntros (m2 σ2) "HpropA %HstepP".
    iSplitL "HpropA";first (iFrame;done).
    eapply (step_ExecI_normal i _ ai w1 ) in HstepP;eauto.
    2 : by rewrite Htx.
    remember (exec _ σ1) as c2 eqn:Heqc2.
    rewrite /exec (str_ExecI σ1 ra rb w2 a HneqPCa HneqNZa HneqPCb HneqNZb _ _ Hra Hrb) /update_incr_PC in Heqc2.
    2: by rewrite Hcur Hrx.
    2: {
      rewrite Hcur /check_access_addr.
      rewrite <-Heq.
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
    rewrite p_upd_pc_mem.
    all: try rewrite p_upd_pc_pgt //.
    all: try rewrite p_upd_pc_trans //.
    all: try rewrite p_upd_pc_mb //.
    iFrame "Hnum Hrxs Hmb Hown Haccess Hrest".
    (* updated part *)
    iDestruct ((gen_reg_update1_global PC i ai (ai ^+ 1)%f) with "Hreg Hpc") as ">[Hreg Hpc]";eauto.
    iDestruct ((gen_mem_update1 a w3 w2) with "Hmem Harb") as ">[Hmem Harb]";eauto.
    rewrite -> (u_upd_pc_regs _ i ai 1);eauto.
    iModIntro.
    iFrame "Hmem Hreg".
    iSplitL "".
    rewrite update_offset_PC_preserve_just_scheduled_vms.
    rewrite update_memory_preserve_just_scheduled_vms.
    rewrite just_scheduled_vms_no_step_empty.
    by iSimpl.
    rewrite update_offset_PC_preserve_scheduled.
    rewrite update_memory_preserve_scheduled.
    rewrite scheduled_true /=;last done.
    iApply "Hϕ".
    iFrame "Hpc Hapc Hrb Harb Hra Hacc Hrx HTX".
    apply (get_reg_gmap_get_reg_Some _ _ _ i) in HPC;eauto.
Qed.

Lemma str_same_addr {E i w1 w2 q p p' s} ai a ra rb:
  decode_instruction w1 = Some (Str ra rb) ->
  tpa ai ∈ s ->
  (tpa a) ≠ p ->
  (tpa ai) ≠ p' ->
  ai = a ->
  {SS{{ ▷ (PC @@ i ->r ai) ∗
        ▷ (ai ->a w1) ∗
        ▷ (rb @@ i ->r a) ∗
        ▷ (ra @@ i ->r w2) ∗
        ▷ (i -@{q}A> s) ∗
        ▷ TX@ i := p' ∗
        ▷ (RX@ i := p)}}}
    ExecI @ i; E
    {{{ RET (false, ExecI);
        PC @@ i ->r (ai ^+ 1)%f ∗
        ai ->a w2 ∗
        rb @@ i ->r a ∗
        ra @@ i ->r w2 ∗
        i -@{q}A> s ∗
        TX@ i := p' ∗                   
        RX@i := p }}}.
Proof.
  iIntros (Hdecode Hin Hne_p Hne Heq ϕ) "(>Hpc & >Hapc & >Hrb & >Hra & >Hacc & >HTX & >Hrx) Hϕ".
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
  iDestruct (access_agree_check_true (tpa ai) i with "Haccess Hacc") as "%Hai"; first set_solver.
  (* valid mem *)
  iDestruct (gen_mem_valid ai w1 with "Hmem Hapc ") as "%Hmemai".
  (* valid rx *)
  iDestruct (mb_valid_rx i p with "Hmb Hrx") as %Hrx.
  iDestruct (mb_valid_tx i p' with "Hmb HTX") as %Htx.
  iSplit.
  - (* reducible *)
    iPureIntro.
    eapply (reducible_normal i _ ai w1);eauto.
    rewrite Htx.
    done.
  - (* step *)
    iModIntro.
    iIntros (m2 σ2) "HpropA %HstepP".
    iSplitL "HpropA";first (iFrame;done).
    eapply (step_ExecI_normal i _ ai w1 ) in HstepP;eauto.
    2: by rewrite Htx.
    remember (exec _ σ1) as c2 eqn:Heqc2.
    rewrite /exec (str_ExecI σ1 ra rb w2 a HneqPCa HneqNZa HneqPCb HneqNZb _ _ Hra Hrb) /update_incr_PC in Heqc2.
    2: {
      rewrite Hcur.
      rewrite Hrx.
      done.
    }
    2: {
      rewrite Hcur.
      rewrite <-Heq.
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
    rewrite p_upd_pc_mem.
    all: try rewrite p_upd_pc_pgt //.
    all: try rewrite p_upd_pc_trans //.
    all: try rewrite p_upd_pc_mb //.
    iFrame "Hnum Hrxs Hmb Hown Haccess Hrest".
    (* updated part *)
    iDestruct ((gen_reg_update1_global PC i ai (ai ^+ 1)%f) with "Hreg Hpc") as ">[Hreg Hpc]";eauto.
    iDestruct ((gen_mem_update1 ai w1 w2) with "Hmem Hapc") as ">[Hmem Harb]";eauto.
    rewrite -> (u_upd_pc_regs _ i ai 1);eauto.
    iModIntro.
    subst a.
    iFrame "Hmem Hreg".
    iSplitL "".
    rewrite update_offset_PC_preserve_just_scheduled_vms.
    rewrite update_memory_preserve_just_scheduled_vms.
    rewrite just_scheduled_vms_no_step_empty.
    by iSimpl.
    rewrite update_offset_PC_preserve_scheduled.
    rewrite update_memory_preserve_scheduled.
    rewrite scheduled_true /=;last done.
    iApply "Hϕ".
    iFrame "Hpc Hrb Harb Hra Hacc Hrx HTX".
    apply (get_reg_gmap_get_reg_Some _ _ _ i) in HPC;eauto.
Qed.

Lemma str_access_rx {i w1 w2 p p' s q} ai a ra rb :
  decode_instruction w1 = Some (Str ra rb) ->
  tpa ai ∈ s ->
  tpa ai ≠ p' ->
  (tpa a) = p ->
  {SS{{  ▷ (PC @@ i ->r ai) ∗
         ▷ (ai ->a w1) ∗
         ▷ (rb @@ i ->r a) ∗
         ▷ (ra @@ i ->r w2) ∗
         ▷ (i -@{q}A> s) ∗
         ▷ TX@ i := p' ∗
         ▷ (RX@ i := p) }}}
    ExecI @ i
    {{{ RET (false,FailPageFaultI);
        PC @@ i ->r ai ∗
        ai ->a w1 ∗
        rb @@ i ->r a ∗
        i -@{q}A> s ∗
        ra @@ i ->r w2 ∗
        TX@ i := p' ∗                   
        RX@ i := p
    }}}.
Proof.
  iIntros (Hdecode Hin Hneq Heq ϕ) "(>Hpc & >Hapc & >Hrb & >Hra & >Hacc & >HTX & >Hrx) Hϕ".
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
  iDestruct (access_agree_check_true (tpa ai) i with "Haccess Hacc") as "%Ha"; first set_solver.
  iDestruct (mb_valid_rx i p with "Hmb Hrx") as %Hrx.
  iDestruct (mb_valid_tx i p' with "Hmb HTX") as %Htx.
  iSplit.
    + iPureIntro.
      eapply (reducible_normal i _ ai w1);eauto.
      by rewrite Htx.
    + iModIntro.
      iIntros (m2 σ2) "HpropA %HstepP".
      iSplitL "HpropA";first (iFrame;done).
      iModIntro.
      eapply (step_ExecI_normal i _ ai w1 ) in HstepP;eauto.
      2: by rewrite Htx.
      remember (exec _ σ1) as c2 eqn:Heqc2.
      rewrite /exec
      (str_FailPageFaultI_str_to_rx σ1 ra rb w2 a HneqPCa HneqNZa HneqPCb HneqNZb _ Hra Hrb)
              /update_incr_PC /update_reg in Heqc2.
      2: by rewrite Hcur Hrx.
      destruct HstepP;subst m2 σ2; subst c2; simpl.
      rewrite /gen_vm_interp.
      iFrame.
      iSplitL "".
      rewrite just_scheduled_vms_no_step_empty.
      done.
      rewrite scheduled_true /=;last done.
      iApply "Hϕ"; iFrame.
Qed.

Lemma str_no_access {i w1 w2 s p} ai a ra rb :
  decode_instruction w1 = Some (Str ra rb) ->
  tpa ai ∈ s ->
  tpa ai ≠ p ->
  tpa a ∉ s ->
  {SS{{  ▷ (PC @@ i ->r ai) ∗
         ▷ (ai ->a w1) ∗
         ▷ (rb @@ i ->r a) ∗
         ▷ (ra @@ i ->r w2) ∗
         ▷ TX@ i := p ∗
         ▷ (i -@{1}A> s)}}}
    ExecI @ i
    {{{ RET (false,FailPageFaultI);
        PC @@ i ->r ai ∗
        ai ->a w1 ∗
        rb @@ i ->r a ∗
        i -@{1}A> s ∗
        TX@ i := p ∗                   
        ra @@ i ->r w2 }}}.
Proof.
  iIntros (Hdecode Hin Hne Hnotin ϕ) "(>Hpc & >Hapc & >Hrb & >Hra & >HTX & >Hacc) Hϕ".
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
  iDestruct (access_agree_check_true (tpa ai) i with "Haccess Hacc") as "%Hai"; first set_solver.
  iDestruct (access_agree_check_false (tpa a) s Hnotin with "Haccess Hacc") as "%Ha".
  iDestruct (mb_valid_tx i p with "Hmb HTX") as %Htx.
  iSplit.
  + iPureIntro.
    rewrite /reducible.
    exists FailPageFaultI, σ1.
    simplify_eq.
    apply (step_exec_normal σ1 ai w1 (Str ra rb) (FailPageFaultI, σ1)); auto.
    * unfold read_memory.
      unfold check_read_access_addr.
      unfold check_read_access_page.
      rewrite Hai.
      simpl.
      case_bool_decide as Hcase; auto.
      exfalso.
      apply Hne.
      auto.
    * rewrite /exec /lang.str.
      destruct ra; try done.
      destruct rb; try done.
      rewrite Hra.
      simpl.
      rewrite Hrb.
      destruct (get_mail_boxes σ1 !!! get_current_vm σ1) as [t [r1 r2]].
      simpl in *.
      rewrite /write_memory /check_write_access_addr /check_write_access_page Ha.
      simpl.
      reflexivity.
  + iModIntro.
    iIntros (m2 σ2) "HpropA %HstepP".
    iModIntro.
    iSplitL "HpropA";first (iFrame;done).
    eapply (step_ExecI_normal i _ ai w1 ) in HstepP;eauto.
    2: by rewrite Htx.
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
