From machine_program_logic.program_logic Require Import machine weakestpre.
From HypVeri Require Import RAs rule_misc lifting rules.rules_base.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import gset.
Require Import stdpp.fin.

Section donate.

Context `{vmG: !gen_VMG Σ}.

Lemma hvc_donate {instr i wi r2 pi ptx sown q sacc sexcl q' wf wt des qh sh} {l :Word} {spsd: gset PID}
      ai r0 r1 j (psd: list PID) :
  (* the current instruction is hvc *)
  instr = Hvc ->
  (* the decoding of wi is correct *)
  decode_instruction wi = Some(instr) ->
  (* the instruction is in page pi *)
  addr_in_page ai pi ->
  (* the decoding of R0 is FFA_DONATE *)
  decode_hvc_func r0 = Some(Donate) ->
  (* l is the number of to-be-donated pages *)
  (finz.to_z l) = (Z.of_nat (length psd)) ->
  (* the descriptor, in list Word *)
  des = serialized_transaction_descriptor i j wf wt l psd W0 ->
  (* the whole descriptor resides in the TX page *)
  seq_in_page (of_pid ptx) (length des) ptx ->
  (* spsd is the gset of all to-be-donated pages *)
  spsd = (list_to_set psd) ->
  (* pi and pages in spsd are accessible for VM i *)
  {[pi]} ∪ spsd ⊆ sacc ->
  (* VM i owns pages in spsd *)
  spsd ⊆ sown ->
  (* pages in spsed are exclusive to VM i *)
  spsd ⊆ sexcl ->
  (* there are at least one free handles in the hpool *)
  sh ≠ ∅ ->
  {SS{{ ▷(PC @@ i ->r ai) ∗ ▷ ai ->a wi
  ∗ ▷ O@i:={q}[sown] ∗ ▷ A@i:={1}[sacc] ∗ ▷ E@i:={q'}[sexcl]
  ∗ ▷ (R0 @@ i ->r r0) ∗ ▷ (R1 @@ i ->r r1) ∗ ▷(R2 @@i ->r r2) ∗  ▷ TX@ i := ptx
  ∗ ▷ mem_region des ptx
  ∗ ▷ hp{ qh }[ (GSet sh)] }}}
   ExecI @ i {{{ RET ExecI ; PC @@ i ->r (ai ^+ 1)%f ∗ ai ->a wi
  ∗ O@i:={q}[sown] ∗ A@i:={1}[sacc∖spsd] ∗ E@i:={q'}[sexcl]
  ∗ R0 @@ i ->r (encode_hvc_ret_code Succ) ∗ R1 @@ i ->r r1  ∗ TX@ i := ptx
  ∗ ∃(wh: Word), ( ⌜ wh ∈ sh ⌝ ∗ R2 @@ i ->r wh ∗ wh ->t{1}(i,wf, wt, {[j := spsd]},Donation)
  ∗ wh ->re j ∗ R2 @@ i ->r wh ∗ hp{qh}[(GSet (sh∖{[wh]}))] )
  ∗ mem_region des ptx}}}.
Proof.
  iIntros (Hinstr Hdecodei Hini Hdecodef Hlenpsd Hdesc Hindesc Hspsd Hsacc Hsown Hsexcl Hshne Φ ).
  iIntros "(>PC & >Hai & >Hown & >Hacc & >Hexcl & >R0 & >R1 & >R2 & >TX & >Hadesc & >Hhp ) HΦ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (σ1) "%Hsche Hσ".
  inversion Hsche as [ Hcureq ]; clear Hsche.
  apply fin_to_nat_inj in Hcureq.
  iModIntro.
  iDestruct "Hσ" as "(Hcur & Hσmem & Hσreg & Hσtx & ? & Hσowned & Hσaccess & Hσexcl & Htrans & Hσhp & Hrcv)".
  (* valid regs *)
  iDestruct ((gen_reg_valid4 σ1 i PC ai R0 r0 R1 r1 R2 r2 Hcureq ) with "Hσreg PC R0 R1 R2 ")
    as "[%HPC [%HR0 [%HR1 %HR2]]]";eauto.
  (* valid pt *)
  iDestruct ((gen_access_valid_addr_elem ai sacc) with "Hσaccess Hacc") as %Haccai;eauto.
  { rewrite (to_pid_aligned_in_page _ pi);eauto. set_solver. }
  (* valid mem *)
  iDestruct (gen_mem_valid σ1 ai wi with "Hσmem Hai") as %Hai.
  unfold mem_region.
  iDestruct (gen_mem_valid_SepL_pure _ des with "Hσmem Hadesc") as %Hadesc.
  { apply finz_seq_NoDup. destruct Hindesc as [? [HisSome ?]]. done. }
  Admitted.

End donate.
