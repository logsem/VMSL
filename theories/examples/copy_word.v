From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.algebra Require Import base.
From HypVeri.rules Require Import rules_base mov ldr str sub cmp bne.
From HypVeri.examples Require Import instr.
From HypVeri Require Import proofmode.

Section copy_word.

  Definition code src dst :=
    encode_instructions
    [
      Mov R0 (inl src);
      Ldr R1 R0;
      Mov R0 (inl dst);
      Str R1 R0
    ].

  Context `{gen_VMG Σ}.

  Lemma copy_word {ptx prx progpage srcpage dstpage sacc i q w w_ r0_ r1_} progaddr src dst :
    ptx ≠ srcpage ->
    prx ≠ dstpage ->
    seq_in_page progaddr (length (code src dst)) progpage ->
    not (addr_in_page src progpage) ->
    not (addr_in_page dst progpage) ->
    addr_in_page src srcpage ->
    addr_in_page dst dstpage ->
    progpage ∈ sacc ->
    srcpage ∈ sacc ->
    dstpage ∈ sacc ->
    program (code src dst) progaddr
    ∗ A@i :={q}[sacc]
    ∗ PC @@ i ->r progaddr
    ∗ (src ->a w)
    ∗ (dst ->a w_)
    ∗ (R0 @@ i ->r r0_)
    ∗ (R1 @@ i ->r r1_)
    ∗ (TX@ i := ptx)
    ∗ (RX@ i := prx)
    ⊢ (PARWP ExecI @ i
          {{ (λ m, ⌜m = ExecI⌝
          ∗ program (code src dst) progaddr
          ∗ A@i :={q}[sacc]
          ∗ PC @@ i ->r (progaddr ^+ (length (code src dst)))%f
          ∗ src ->a w
          ∗ dst ->a w
          ∗ R0 @@ i ->r dst
          ∗ R1 @@ i ->r w
          ∗ (RX@ i := prx)
          ∗ (TX@ i := ptx))}}%I).
  Proof.
    iIntros (Hneq Hneq' Hseqp Hnin Hnin' Hsrcp Hdstp Hprpain Hsrcpain Hdstpain) "(Hbstar & Hai & Hpc & Hsrc & Hdst & Hr0 & Hr1 & HTX & HRX)".
    pose proof (seq_in_page_forall1 _ _ _ Hseqp) as Hseq.
    rewrite <-parwp_sswp.
    iDestruct "Hbstar" as "(p_start & Hbstar)". 
    iApply ((mov_word progaddr src R0) with "[Hpc Hai Hr0 p_start]") ;iFrameAutoSolve.
    2 : { apply Hprpain. }
    apply Hseq.
    set_solver.
    iModIntro.
    iIntros "(Hpc & Hinstr1 & Hacc & Hr0)".
    rewrite <-parwp_sswp.
    iDestruct "Hbstar" as "(p_start & Hbstar)".
    iApply ((ldr (progaddr ^+ 1)%f src R1 R0) with "[Hpc Hacc Hr0 Hr1 Hsrc p_start HTX]");iFrameAutoSolve.
    intros C.
    apply to_pid_aligned_in_page in Hsrcp.
    rewrite <-Hsrcp in Hneq.
    rewrite C in Hneq.
    apply Hneq.
    reflexivity.
    apply to_pid_aligned_in_page in Hsrcp.
    subst srcpage.
    assert (Hp : (progaddr ^+ 1)%f ∈ finz.seq progaddr (length (code src dst))).
    set_solver.
    specialize (Hseq _ Hp).
    apply to_pid_aligned_in_page in Hseq.
    rewrite Hseq.
    set_solver.
    iModIntro.
    iIntros "(Hpc & Hinstr2 & Hr0 & Hsrc & Hr1 & Hacc & HTX)".
    rewrite <-parwp_sswp.
    iDestruct "Hbstar" as "(p_start & Hbstar)".
    iApply ((mov_word ((progaddr ^+ 1) ^+ 1)%f dst R0) with "[Hpc Hacc Hr0 p_start]");iFrameAutoSolve.
    apply Hseq. set_solver.
    apply Hprpain.
    iModIntro.
    iIntros "(Hpc & Hinstr3 & Hacc & Hr0)".
    rewrite <-parwp_sswp.
    iDestruct "Hbstar" as "(p_start & Hbstar)".
    iApply ((str (((progaddr ^+ 1) ^+ 1) ^+ 1)%f dst R1 R0) with "[Hpc Hacc Hr0 p_start Hdst Hr1 HRX]")
           ;iFrameAutoSolve.
    intros C.
    rewrite C in Hneq'.
    apply Hneq'.
    apply to_pid_aligned_in_page in Hdstp.
    assumption.
    apply to_pid_aligned_in_page in Hdstp.
    subst dstpage.
    specialize (Hseq (((progaddr ^+ 1) ^+ 1) ^+ 1)%f).
    pose proof (to_pid_aligned_in_page (((progaddr ^+ 1) ^+ 1) ^+ 1)%f progpage) as Hp.
    assert (Hq : (((progaddr ^+ 1) ^+ 1) ^+ 1)%f ∈ finz.seq progaddr (length (code src dst))).
    set_solver.
    rewrite (Hp (Hseq Hq)).
    set_solver.
    iModIntro.
    iIntros "(Hpc & Hinstr4 & Hr0 & Hdst & Hr1 & Hacc & HRX)".
    iApply parwp_finish.
    iFrame.
    iSplit; auto.
    assert ((progaddr ^+ length (code src dst))%f = ((((progaddr ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f) as ->.
    assert (Z.of_nat (length (code src dst)) = 4%Z) as ->. by compute.
    solve_finz.
    iFrame.
  Qed.

  Definition copy_word_loop step src dst :=
    [
    mov_word_I R5 step; (* remaining runs *)
    mov_word_I R6 I0;    (* counter *)
    mov_reg_I R7 PC;    (* program base address *)
    mov_word_I R8 I2;
    add_reg_I R7 R8;         (* loop base address *)    
    (* loop body begin *)
    (* loop may depend on step and counter
       it should restore PC, R5, R6
       perhaps, we could try to write a special rule for loops
     *)
    (* ldr data from src + counter to R1 *)
    mov_word_I R8 src;
    add_reg_I R8 R6;
    ldr_I R9 R8;
    (* str data from R1 to dst + counter *)
    mov_word_I R8 dst;
    add_reg_I R8 R6;
    str_I R9 R8;
    (* loop body end *)    
    (* incr counter *)
    mov_word_I R8 I1;
    add_reg_I R6 R8;
    (* decr remaining runs *)
    sub_reg_I R5 R8;
    (* conditional jump *)
    (* might be a good idea to have a separate rule for branches *)
    cmp_I R5 I0;
    bne_I R7
    ].

  Lemma copy_words {ptx prx progpage srcpage dstpage sacc i q qi w w_ r0_ r1_} step src dst :
    step < page_size ->
    length mem = step ->
    ptx ≠ srcpage ->
    prx ≠ dstpage ->
    seq_in_page (of_pid progpage) (length (program_c step src dst)) progpage ->
    not (addr_in_page src progpage) ->
    not (addr_in_page dst progpage) ->
    addr_in_page src srcpage ->
    addr_in_page dst dstpage ->
    progpage ∈ sacc ->
    srcpage ∈ sacc ->
    dstpage ∈ sacc ->
    program' (program_c step src dst) (of_pid progpage)
    ∗ A@i :={q}[sacc]
    ∗ PC @@ i ->r (of_pid progpage)
    ∗ mem_region mem srcpage
    ∗ (∃ m, mem_region m dstpage)
    ∗ (R0 @@ i ->r r0_)
    ∗ (R1 @@ i ->r r1_)
    ∗ (TX@ i := ptx)
    ∗ (<<i>>{ qi })
    ∗ (RX@ i := prx)
    ⊢ (PARWP ExecI @ i
          {{ (λ m, ⌜m = ExecI⌝
          ∗ program' (program_c step src dst) (of_pid progpage)
          ∗ A@i :={q}[sacc]
          ∗ PC @@ i ->r ((of_pid progpage) ^+ (length (program src dst)))%f
          ∗ mem_region mem srcpage
          ∗ mem_region mem dstpage
          ∗ R0 @@ i ->r dst
          ∗ R1 @@ i ->r w
          ∗ (<<i>>{ qi })
          ∗ (RX@ i := prx)
          ∗ (TX@ i := ptx))}}%I).
  Admitted.
End copy_word.
