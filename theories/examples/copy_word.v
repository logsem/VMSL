From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.algebra Require Import base mem.
From HypVeri.rules Require Import rules_base mov ldr str sub cmp bne.
From HypVeri.examples Require Import instr loop_macro.
From HypVeri Require Import proofmode.

Section copy_word.

  Definition code src dst :=
    encode_instructions
    [
      Mov R2 (inr R5); (* move the # of iterations to R2 *)
      Mov R3 (inl I0);
      Sub R2 R3; (* R5 - 1 = R2 (offset) *)
      Mov R3 (inr R2); (* copy R2 to R3 *)
      Mov R0 (inl src);
      Add R2 R0;  (* src = src_base (R0) + offset (R2) *)
      Ldr R1 R2;
      Mov R0 (inl dst);
      Add R3 R0;  (* dst = dst_base (R0) + offset (R3) *)
      Str R3 R1
    ].

  Context `{hypparams:HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.

  Lemma copy_word {ptx prx progpage: PID} {sacc: gset PID} {ws ws' : list Word}
        {w r0_ r1_ r2_ r3_:Word} {i q}{iprx iptx: Imm}
        (progaddr:Addr) (len noff :nat) (off:Word):
    0 < noff ->
    noff <= len ->
    seq_in_page progaddr (length (code iprx iptx)) progpage ->
    of_imm iprx = of_pid prx ->
    of_imm iptx = of_pid ptx ->
    {[progpage; prx; ptx]} ⊆ sacc ->
    length ws = length ws' ->
    length ws = len ->
    (∀ i, i<= (len - noff) -> ws !! i = ws' !! i) ->
    program (code iprx iptx) progaddr
    ∗ A@i :={q}[sacc]
    ∗ PC @@ i ->r progaddr
    ∗ (R0 @@ i ->r r0_)
    ∗ (R1 @@ i ->r r1_)
    ∗ (R2 @@ i ->r r2_)
    ∗ (R3 @@ i ->r r3_)
    ∗ (R5 @@ i ->r off)
    ∗ (RX@ i := prx)
    ∗ mem_region ws prx
    ∗ (TX@ i := ptx)
    ∗ mem_region ws' ptx
    ⊢ (PARWP ExecI @ i
          {{ (λ m, ⌜m = ExecI⌝
          ∗ program (code iprx iptx) progaddr
          ∗ A@i :={q}[sacc]
          ∗ PC @@ i ->r (progaddr ^+ (length (code iprx iptx)))%f
          ∗ (∃ r0_, R0 @@ i ->r r0_)
          ∗ (∃ r1_, R1 @@ i ->r r1_)
          ∗ (∃ r2_, R2 @@ i ->r r2_)
          ∗ (∃ r3_, R3 @@ i ->r r3_)
          ∗ (R5 @@ i ->r off)
          ∗ (RX@ i := prx)
          ∗ (mem_region ws prx)
          ∗ (TX@ i := ptx)
          ∗ (∃ ws', mem_region ws' ptx ∗ ⌜ ∀ i, i <= (len - (noff-1)) -> ws !! i = ws' !! i ⌝))}}%I).
  Proof.
  Admitted.

  (* TODO: prove another spec that combine loop and the program above together, shouldn't be difficult *)


  (* proof of the four-instruction copy word program *)
  (* Proof. *)
  (*   iIntros (Hneq Hneq' Hseqp Hnin Hnin' Hsrcp Hdstp Hprpain Hsrcpain Hdstpain) "(Hbstar & Hai & Hpc & Hsrc & Hdst & Hr0 & Hr1 & HTX & HRX)". *)
  (*   pose proof (seq_in_page_forall1 _ _ _ Hseqp) as Hseq. *)
  (*   rewrite <-parwp_sswp. *)
  (*   iDestruct "Hbstar" as "(p_start & Hbstar)".  *)
  (*   iApply ((mov_word progaddr src R0) with "[Hpc Hai Hr0 p_start]") ;iFrameAutoSolve. *)
  (*   2 : { apply Hprpain. } *)
  (*   apply Hseq. *)
  (*   set_solver. *)
  (*   iModIntro. *)
  (*   iIntros "(Hpc & Hinstr1 & Hacc & Hr0)". *)
  (*   rewrite <-parwp_sswp. *)
  (*   iDestruct "Hbstar" as "(p_start & Hbstar)". *)
  (*   iApply ((ldr (progaddr ^+ 1)%f src R1 R0) with "[Hpc Hacc Hr0 Hr1 Hsrc p_start HTX]");iFrameAutoSolve. *)
  (*   intros C. *)
  (*   apply to_pid_aligned_in_page in Hsrcp. *)
  (*   rewrite <-Hsrcp in Hneq. *)
  (*   rewrite C in Hneq. *)
  (*   apply Hneq. *)
  (*   reflexivity. *)
  (*   apply to_pid_aligned_in_page in Hsrcp. *)
  (*   subst srcpage. *)
  (*   assert (Hp : (progaddr ^+ 1)%f ∈ finz.seq progaddr (length (code src dst))). *)
  (*   set_solver. *)
  (*   specialize (Hseq _ Hp). *)
  (*   apply to_pid_aligned_in_page in Hseq. *)
  (*   rewrite Hseq. *)
  (*   set_solver. *)
  (*   iModIntro. *)
  (*   iIntros "(Hpc & Hinstr2 & Hr0 & Hsrc & Hr1 & Hacc & HTX)". *)
  (*   rewrite <-parwp_sswp. *)
  (*   iDestruct "Hbstar" as "(p_start & Hbstar)". *)
  (*   iApply ((mov_word ((progaddr ^+ 1) ^+ 1)%f dst R0) with "[Hpc Hacc Hr0 p_start]");iFrameAutoSolve. *)
  (*   apply Hseq. set_solver. *)
  (*   apply Hprpain. *)
  (*   iModIntro. *)
  (*   iIntros "(Hpc & Hinstr3 & Hacc & Hr0)". *)
  (*   rewrite <-parwp_sswp. *)
  (*   iDestruct "Hbstar" as "(p_start & Hbstar)". *)
  (*   iApply ((str (((progaddr ^+ 1) ^+ 1) ^+ 1)%f dst R1 R0) with "[Hpc Hacc Hr0 p_start Hdst Hr1 HRX]") *)
  (*          ;iFrameAutoSolve. *)
  (*   intros C. *)
  (*   rewrite C in Hneq'. *)
  (*   apply Hneq'. *)
  (*   apply to_pid_aligned_in_page in Hdstp. *)
  (*   assumption. *)
  (*   apply to_pid_aligned_in_page in Hdstp. *)
  (*   subst dstpage. *)
  (*   specialize (Hseq (((progaddr ^+ 1) ^+ 1) ^+ 1)%f). *)
  (*   pose proof (to_pid_aligned_in_page (((progaddr ^+ 1) ^+ 1) ^+ 1)%f progpage) as Hp. *)
  (*   assert (Hq : (((progaddr ^+ 1) ^+ 1) ^+ 1)%f ∈ finz.seq progaddr (length (code src dst))). *)
  (*   set_solver. *)
  (*   rewrite (Hp (Hseq Hq)). *)
  (*   set_solver. *)
  (*   iModIntro. *)
  (*   iIntros "(Hpc & Hinstr4 & Hr0 & Hdst & Hr1 & Hacc & HRX)". *)
  (*   iApply parwp_finish. *)
  (*   iFrame. *)
  (*   iSplit; auto. *)
  (*   assert ((progaddr ^+ length (code src dst))%f = ((((progaddr ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f) as ->. *)
  (*   assert (Z.of_nat (length (code src dst)) = 4%Z) as ->. by compute. *)
  (*   solve_finz. *)
  (*   iFrame. *)
  (* Qed. *)

  End copy_word.
