From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base.
From HypVeri.algebra Require Import base mem reg pagetable.
From HypVeri.lang Require Import lang_extra reg_extra.

Section sub.

Context `{hypparams: HypervisorParameters}.
Context `{vmG: !gen_VMG Σ}.

Lemma sub {instr i wi w1 w2 q pi} ai ra rb sacc :
  instr = Sub ra rb ->
  decode_instruction wi = Some(instr) ->
  addr_in_page ai pi ->
  pi ∈ sacc ->
  {SS{{ ▷ (PC @@ i ->r ai) ∗
        ▷ (ai ->a wi) ∗
        ▷ (ra @@ i ->r w1) ∗
        ▷ (rb @@ i ->r w2) ∗
        ▷ (A@i:={q}[sacc] )}}}
    ExecI @ i
    {{{ RET ExecI;
        PC @@ i ->r (ai ^+ 1)%f ∗
        ai ->a wi ∗
        ra @@ i ->r (w1 ^- (finz.to_z w2))%f ∗
        rb @@ i ->r w2 ∗
        A@i:={q}[sacc] }}}.
Proof.
  iIntros (Hinstr Hdecode Hin HpIn ϕ) "(>Hpc & >Hai & >Hra & >Hrb & >Hacc) Hϕ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [ Hcur ]; clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(Htok & Hmem & Hreg & Htx & Hrxagree & Hrxoption & Howned & Haccess & Hrest)".
  (* valid regs *)
  iDestruct ((gen_reg_valid3 i PC ai ra w1 rb w2 Hcur) with "Hreg Hpc Hra Hrb") as "[%HPC [%Hra %Hrb]]";eauto.
  (* valid pt *)
  iDestruct ((gen_access_valid_addr_Set ai pi) with "Haccess Hacc") as %Hacc;eauto.
  (* valid mem *)
  iDestruct (gen_mem_valid ai wi with "Hmem Hai") as %Hmem.
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal i instr ai wi);eauto.
  - (* step *)
    iModIntro.
    iIntros (m2 σ2) "%HstepP".
    apply (step_ExecI_normal i instr ai wi ) in HstepP;eauto.
    remember (exec instr σ1) as c2 eqn:Heqc2.
    pose proof (decode_instruction_valid wi instr Hdecode) as Hvalidinstr.
    rewrite Hinstr in Hvalidinstr.
    inversion Hvalidinstr as [ | | | | | | | ra' rb' Hvalidrb Hvalidra | | |] .
    subst ra' rb'.
    inversion Hvalidra as [ HneqPCa HneqNZa ].
    inversion Hvalidrb as [ HneqPCb HneqNZb ].
    rewrite /exec Hinstr (sub_ExecI σ1 ra w1 rb w2) /update_incr_PC /update_reg in Heqc2;auto.
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    (* unchanged part *)
    rewrite_reg_pc.
    rewrite_reg_global.
    rewrite Hcur.
    iFrame "Htok Htx Hrxagree Hrxoption Howned Hrest".
    (* updated part *)
    rewrite -> (update_offset_PC_update_PC1 _ i ai 1);eauto.
    rewrite update_reg_global_update_reg;[|solve_reg_lookup].
    + iDestruct ((gen_reg_update2_global PC i ai (ai ^+ 1)%f ra i w1 (w1 ^- (finz.to_z w2))%f)
                   with "Hreg Hpc Hra") as ">[Hreg [Hpc Hra]]";eauto.
      iModIntro.
      iFrame "Hmem Hreg Haccess".
      iApply "Hϕ".
      by iFrame "Hai Hra Hpc Hrb".
    + rewrite update_reg_global_update_reg;[|solve_reg_lookup].
      apply (get_reg_gmap_get_reg_Some _ _ _ i) in HPC;eauto.
      rewrite lookup_insert_ne.
      by simplify_map_eq /=.
      congruence.
Qed.

End sub.
