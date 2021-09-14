From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.algebra Require Import base.
From HypVeri.rules Require Import rules_base mov ldr str.

Section copy_word.
  Definition mov_word_I ra w := encode_instruction (Mov ra (inl w)).
  Definition str_I ra rb := encode_instruction (Str ra rb).
  Definition ldr_I ra rb := encode_instruction (Ldr ra rb).
  
  Definition program src dst :=
    [ mov_word_I R0 src; ldr_I R1 R0; mov_word_I R0 dst; str_I R1 R0 ].

  Context `{gen_VMG Σ} (N : namespace).
  
  Definition program' (instr: list Word) (b:Addr):=
    ([∗ list] a;w ∈ (finz.seq b (length instr));instr, (a ->a w))%I.
  
  Lemma copy_word {ptx prx progpage srcpage dstpage sacc i q qi w w_ r0_ r1_} src dst :
    ptx ≠ srcpage ->
    prx ≠ dstpage ->
    seq_in_page (of_pid progpage) (length (program src dst)) progpage ->
    not (addr_in_page src progpage) ->
    not (addr_in_page dst progpage) ->
    addr_in_page src srcpage ->
    addr_in_page dst dstpage ->
    progpage ∈ sacc ->
    srcpage ∈ sacc ->
    dstpage ∈ sacc ->
    program' (program src dst) (of_pid progpage)
    ∗ A@i :={q}[sacc]
    ∗ PC @@ i ->r (of_pid progpage)
    ∗ (src ->a w)
    ∗ (dst ->a w_)
    ∗ (R0 @@ i ->r r0_)
    ∗ (R1 @@ i ->r r1_)
    ∗ (TX@ i := ptx)
    ∗ (<<i>>{ qi })
    ∗ (RX@ i := prx)
    ⊢ (PARWP ExecI @ i
          {{ (λ m, ⌜m = ExecI⌝
          ∗ program' (program src dst) (of_pid progpage)
          ∗ A@i :={q}[sacc]
          ∗ PC @@ i ->r ((of_pid progpage) ^+ (length (program src dst)))%f
          ∗ src ->a w
          ∗ dst ->a w
          ∗ R0 @@ i ->r dst
          ∗ R1 @@ i ->r w
          ∗ (<<i>>{ qi })
          ∗ (RX@ i := prx)
          ∗ (TX@ i := ptx))}}%I).
  Proof.
    iIntros (Hneq Hneq' Hseqp Hnin Hnin' Hsrcp Hdstp Hprpain Hsrcpain Hdstpain) "(Hbstar & Hai & Hpc & Hsrc & Hdst & Hr0 & Hr1 & HTX & Hi & HRX)".
    apply seq_in_page_forall in Hseqp.
    rewrite <-parwp_sswp.
    iDestruct "Hbstar" as "(p_start & Hbstar)".
    iDestruct ((mov_word (of_pid progpage) src R0) with "[Hpc Hai Hr0 p_start]") as "J".
    3 : { rewrite ->Forall_forall in Hseqp. apply Hseqp. set_solver. }
    3 : { apply Hprpain. }
    3 : { iFrame. }
    auto.
    by rewrite decode_encode_instruction.
    iApply "J".
    iModIntro.
    iIntros "(Hpc & Hinstr1 & Hacc & Hr0)".
    rewrite <-parwp_sswp.
    iDestruct "Hbstar" as "(p_start & Hbstar)".
    iDestruct ((ldr (of_pid progpage ^+ 1)%f src R1 R0) with "[Hpc Hacc Hr0 Hr1 Hsrc p_start HTX Hi]") as "J".
    3 : { intros C.
          rewrite ->Forall_forall in Hseqp.
          specialize (Hseqp (progpage ^+ 1)%f).
          rewrite C in Hseqp.
          apply Hnin.
          apply Hseqp.
          rewrite <-C.
          rewrite finz_seq_cons.
          set_solver.
          rewrite /program.
          simpl.
          lia.
    }
    instantiate (1 := Ldr R1 R0).
    reflexivity.
    instantiate (1 := encode_instruction (Ldr R1 R0)).
    by rewrite decode_encode_instruction.
    instantiate (1 := ptx).
    intros C.
    apply to_pid_aligned_in_page in Hsrcp.
    rewrite <-Hsrcp in Hneq.
    rewrite C in Hneq.
    apply Hneq.
    reflexivity.
    rewrite ->Forall_forall in Hseqp.
    specialize (Hseqp (progpage ^+ 1)%f).
    instantiate (1 := sacc).
    apply to_pid_aligned_in_page in Hsrcp.
    subst srcpage.
    assert (Hp : (progpage ^+ 1)%f ∈ finz.seq progpage (length (program src dst))).
    set_solver.
    specialize (Hseqp Hp).
    apply to_pid_aligned_in_page in Hseqp.
    rewrite Hseqp.
    set_solver.
    iFrame.
    iApply "J".
    iModIntro.
    iIntros "(HTX & Hi & Hpc & Hinstr2 & Hr0 & Hsrc & Hacc & Hr1)".
    rewrite <-parwp_sswp.
    iDestruct "Hbstar" as "(p_start & Hbstar)".
    iDestruct ((mov_word ((of_pid progpage ^+ 1) ^+ 1)%f dst R0) with "[Hpc Hacc Hr0 p_start]") as "J".
    3 : { rewrite ->Forall_forall in Hseqp. apply Hseqp. set_solver. }
    3 : { apply Hprpain. }
    3 : { iFrame. }
    auto.
    by rewrite decode_encode_instruction.
    iApply "J".
    iModIntro.
    iIntros "(Hpc & Hinstr3 & Hacc & Hr0)".
    rewrite <-parwp_sswp.
    iDestruct "Hbstar" as "(p_start & Hbstar)".
    iDestruct ((str (((of_pid progpage ^+ 1) ^+ 1) ^+ 1)%f dst R1 R0) with "[Hpc Hacc Hr0 p_start Hdst Hr1 HRX]") as "J".
    instantiate (1 := Str R1 R0).
    reflexivity.
    instantiate (1 := encode_instruction (Str R1 R0)).
    by rewrite decode_encode_instruction.
    intros C.
    rewrite ->Forall_forall in Hseqp.
    specialize (Hseqp (((progpage ^+ 1) ^+ 1) ^+ 1)%f).
    rewrite C in Hseqp.
    apply Hnin'.
    apply Hseqp.
    rewrite <-C.
    rewrite finz_seq_cons.
    set_solver.
    rewrite /program.
    simpl.
    lia.
    instantiate (1 := prx).
    intros C.
    rewrite C in Hneq'.
    apply Hneq'.
    apply to_pid_aligned_in_page in Hdstp.
    assumption.
    instantiate (1 := sacc).
    apply to_pid_aligned_in_page in Hdstp.
    subst dstpage.
    rewrite ->Forall_forall in Hseqp.
    specialize (Hseqp (((progpage ^+ 1) ^+ 1) ^+ 1)%f).
    pose proof (to_pid_aligned_in_page (((progpage ^+ 1) ^+ 1) ^+ 1)%f progpage) as Hp.
    assert (Hq : (((progpage ^+ 1) ^+ 1) ^+ 1)%f ∈ finz.seq progpage (length (program src dst))).
    set_solver.
    specialize (Hseqp Hq).
    specialize (Hp Hseqp).
    rewrite Hp.
    set_solver.
    iFrame.
    iApply "J".
    iModIntro.
    iIntros "(Hpc & Hinstr4 & Hr0 & Hdst & Hacc & Hr1 & HRX)".
    iApply parwp_finish.
    iFrame.
    iSplit; auto.
    assert (Hp : (progpage ^+ length (program src dst))%f = ((((progpage ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f).
    assert (Hq : Z.of_nat (length (program src dst)) = 4%Z). by compute.
    rewrite Hq.
    solve_finz.
    rewrite Hp.
    iFrame.
  Qed.

  (* TODOs:
     - sub and add
     - loop rule ???
     - branch rule ???
   *)
  (*
  Definition cmp_I ra := encode_instruction (Cmp ra).
  Definition bne_I ra := encode_instruction (Bne ra).
  Definition sub_word_I ra w := encode_instruction (Sub ra (inl w)).
  Definition add_word_I ra w := encode_instruction (Add ra (inl w)).
  Definition sub_reg_I ra rb := encode_instruction (Sub ra (inr rb)).
  Definition add_reg_I ra rb := encode_instruction (Add ra (inr rb)).
  Definition mov_reg_I ra rb := encode_instruction (Mov ra (inr rb)).
  
  Definition program_c step src dst :=
    [
    mov_word_I R2 step; (* remaining runs *)
    mov_word_I R4 0;    (* counter *)
    mov_reg_I R3 PC;    (* program base address *)
    add_I R3 2;         (* loop base address *)
    (* loop body begin *)
    (* loop may depend on step and counter
       it should restore PC, R2, R4
       perhaps, we could try to write a special rule for loops
     *)
    (* ldr data from src + counter to R1 *)
    mov_word_I R0 src;
    add_I R0 R4;
    ldr_I R1 R0;
    (* str data from R1 to dst + counter *)
    mov_word_I R0 dst;
    add_I R0 R4;
    str_I R1 R0;
    (* loop body end *)
    (* incr counter *)
    add_I R4 1;
    (* decr remaining runs *)
    sub_I R2 1;
    (* conditional jump *)
    (* might be a good idea to have a separate rule for branches *)
    cmp_I R2;
    bne_I R3
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
  *)
End copy_word.
