From machine_program_logic.program_logic Require Import machine weakestpre.
From HypVeri Require Import RAs rule_misc lifting rules.rules_base.
From iris.proofmode Require Import tactics.
Require Import iris.base_logic.lib.ghost_map.
Require Import stdpp.fin.

Lemma hvc_mem_donate11 {instr i wi r2 ptx so q sa wf wt} ai r0 r1 j pd :
  instr = Hvc ->
  decode_instruction wi = Some(instr) ->
  decode_hvc_func r0 = Some(Donate) ->
  (fin_to_nat r1) ≤ page_size ->
  {[pd; (mm_translation ai)]} ⊆ sa ->
  pd ∈ so ->
  <<i>> ∗ PC @@ i ->r ai ∗ ai ->a wi
  ∗ O@i:={q}[so] ∗ A@i:={1}[sa]
  ∗ R0 @@ i ->r r0 ∗ R1 @@ i ->r r1 ∗ R2 @@i ->r r2 ∗ TX@ i := ptx
  ∗ new_transaction_descriptor11 ptx i wf zero_word wt one_word j pd
    ⊢ SSWP ExecI @ i {{ (λ m, ⌜m = HaltI ⌝ ∗ <<i>> ∗ PC @@ i ->r (ai +w 1) ∗ ai ->a wi
  ∗ O@i:={q}[so] ∗ A@i:={1}[sa∖{[pd]}]
  ∗ R0 @@ i ->r (encode_hvc_ret_code Succ) ∗ R1 @@ i ->r r1 ∗ TX@ i := ptx
  ∗ ∃wh, (R2 @@ i ->r wh ∗ wh ->t{1}(i,wf, wt, {[j := {[pd]}]},Donation) ∗ wh ->re j)
  ∗ new_transaction_descriptor11 ptx i zero_word zero_word zero_word one_word j pd)}}%I.
Proof.
  iIntros (Hinstr Hdecodei Hdecodef Hvalidlen Hsa Hso) "(Htok & HPC & Hai & Hown & Haccess & HR0 & HR1 & HR2 & HTX & Htd)".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [ Hcureq ]; clear Hsche.
  apply fin_to_nat_inj in Hcureq.
  iModIntro.
  iDestruct "Hσ" as "(Hcur & Hmem & Hreg & Htxpage & ? & Hownedpt & Haccesspt & Htrans & Hrcv)".
  (* valid regs *)
  iDestruct ((gen_reg_valid4 σ1 i PC ai R0 r0 R1 r1 R2 r2 Hcureq ) with "Hreg HPC HR0 HR1 HR2 ")
    as "[%HPC [%HR0 [%HR1 %HR2]]]";eauto.
  (* valid pt *)
  iDestruct ((gen_access_valid2 σ1 i 1 sa pd (mm_translation ai)) with "Haccesspt Haccess") as %[Haccpd Haccai];eauto.
  (* valid mem *)
  iDestruct (gen_mem_valid σ1 ai wi with "Hmem Hai") as %Hmem.
  iDestruct (gen_mem_valid_td11 σ1 _ _ _ _ _ _ with "Htd Hmem") as %Htd.
  iSplit.
  - admit.
  - admit.
 Admitted.
