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
  
  Lemma copy_word {ptx prx progpage srcpage dstpage sacc i q w w_ r0_ r1_} src dst :
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
          ∗ (RX@ i := prx)
          ∗ (TX@ i := ptx))}}%I).
  Proof.
    iIntros (Hneq Hneq' Hseqp Hnin Hnin' Hsrcp Hdstp Hprpain Hsrcpain Hdstpain) "(Hbstar & Hai & Hpc & Hsrc & Hdst & Hr0 & Hr1 & HTX & HRX)".
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
    iDestruct ((ldr (of_pid progpage ^+ 1)%f src R1 R0) with "[Hpc Hacc Hr0 Hr1 Hsrc p_start HTX]") as "J".
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
    iIntros "(Hpc & Hinstr2 & Hr0 & Hsrc & Hr1 & Hacc & HTX)".
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
    iIntros "(Hpc & Hinstr4 & Hr0 & Hdst & Hr1 & Hacc & HRX)".
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
  
  Definition cmp_I ra v := encode_instruction (Cmp ra (inr v)).
  Definition bne_I ra := encode_instruction (Bne ra).
  Definition sub_reg_I ra rb := encode_instruction (Sub ra rb).
  Definition add_reg_I ra rb := encode_instruction (Add ra rb).
  Definition mov_reg_I ra rb := encode_instruction (Mov ra (inr rb)).

  Program Definition I0 : Imm := (I (finz.FinZ 0 _ _) _).
  Solve Obligations with (try lia; solve_finz).

  Program Definition I1 : Imm := (I (finz.FinZ 1 _ _) _).
  Solve Obligations with (try lia; solve_finz).

  Program Definition I2 : Imm := (I (finz.FinZ 2 _ _) _).
  Solve Obligations with (try lia; solve_finz).

  Definition c_pre step :=
    [
    mov_word_I R5 step; (* remaining runs *)
    mov_word_I R6 I0;    (* counter *)
(*    mov_word_I R7 base    (* program base address *) *)
    ].

  Definition c_post :=
    [
    (* incr counter *)
    mov_word_I R8 I1;
    add_reg_I R6 R8;
    (* conditional jump *)
    (* might be a good idea to have a separate rule for branches *)
    cmp_I R6 R5;
    bne_I R7
    ].

  Definition cycle prog step := c_pre step ++ prog ++ c_post.

  Lemma c_loop {progpage sacc i q} {n : nat} (body : list Word) step prog (P : Word -> iProp Σ) :
    n = Z.to_nat (finz.to_z (of_imm step)) ->
    (1 <= step)%Z ->
    progpage ∈ sacc ->
    seq_in_page (of_pid progpage) (length (cycle prog step)) progpage ->
    (∀ v, ⌜(v <= step)%f⌝ -∗ {PAR{{ (P v) ∗ PC @@ i ->r ((of_pid progpage) ^+ 3)%f
                         ∗ R6 @@ i ->r v
                         ∗ R5 @@ i ->r step
                         ∗ R7 @@ i ->r ((of_pid progpage) ^+ 2)%f
                         ∗ R8 @@ i ->r I2                     
                         ∗ A@i :={q}[sacc]
                         ∗ (program' (cycle prog step) (of_pid progpage))
            }}} ExecI @ i
    {{{ RET ExecI; (P (v ^+ 1)%f) ∗ PC @@ i ->r (((of_pid progpage) ^+ 2)%f ^+ (length prog))%f
                         ∗ R6 @@ i ->r v
                         ∗ R5 @@ i ->r step
                         ∗ R7 @@ i ->r ((of_pid progpage) ^+ 2)%f
                         ∗ (∃ r, R8 @@ i ->r r)
                         ∗ A@i :={q}[sacc]
                         ∗ (program' (cycle prog step) (of_pid progpage))
    }}}%I)
    ⊢  {PAR{{ (P I0) ∗ PC @@ i ->r (of_pid progpage)
                       ∗ (∃ r5, R5 @@ i ->r r5)
                       ∗ (∃ r6, R6 @@ i ->r r6)
                       ∗ (∃ r7, R7 @@ i ->r r7)
                       ∗ (∃ r8, R8 @@ i ->r r8)
                       ∗ A@i :={q}[sacc]
                       ∗ program' (cycle prog step) (of_pid progpage)
       }}} ExecI @ i
    {{{ RET ExecI; (P step) ∗ PC @@ i ->r (of_pid progpage ^+ (length (cycle prog step)))%f
                          ∗ R5 @@ i ->r step
                          ∗ R6 @@ i ->r step
                          ∗ R7 @@ i ->r ((of_pid progpage) ^+ 2)%f
                          ∗ R8 @@ i ->r I2               
                          ∗ A@i :={q}[sacc]
                          ∗ program' (cycle prog step ((of_pid progpage) ^+ 2)%f) (of_pid progpage)
    }}}%I.
  Proof.
    iIntros (Hn Hle Hprpain Hseq) "#Htriple".
    generalize dependent step.
    induction n.
    - intros step eq c.
      lia.
    - intros step eq c seq.
      iIntros (Φ).
      iModIntro.
      iIntros "(HPstep & Hpc & [% Hr5] & [% Hr6] & [% Hr7] & [% Hr8] & Hacc & Hprog)".
      assert (Hn : n = Z.to_nat (step ^- 1)%f).
      {
        rewrite /decr_default.
        rewrite /decr.
        destruct (Z_le_dec 0%Z (step - 1)%Z) eqn:heq; [|lia].
        destruct (Z_lt_dec (step - 1)%Z 2000000%Z).
        - simpl.
          lia.
        - exfalso.
          apply n0.
          destruct step.
          simpl.
          destruct (decide ((w < 1000000)%Z)); [|lia].
          lia.
      } 
      iIntros "Hϕ".
    apply seq_in_page_forall in seq.
    rewrite <-parwp_sswp.
    iDestruct "Hprog" as "(p_start & Hprog)".
    iDestruct ((mov_word (of_pid progpage) step R5) with "[Hpc Hacc Hr5 p_start]") as "J".
    3 : { rewrite ->Forall_forall in seq. apply seq. set_solver. }
    3 : { apply Hprpain. }
    3 : { iFrame. }
    auto.
    by rewrite decode_encode_instruction.
    iApply "J".
    iModIntro.
    iIntros "(Hpc & Hinstr1 & Hacc & Hr5)".
    rewrite <-parwp_sswp.
    iDestruct "Hprog" as "(p_start & Hprog)".
    iDestruct ((mov_word ((of_pid progpage ^+ 1)%f) I0 R6) with "[Hpc Hacc Hr6 p_start]") as "J".
    3 : { rewrite ->Forall_forall in seq. apply seq. set_solver. }
    3 : { apply Hprpain. }
    3 : { iFrame. }
    auto.
    by rewrite decode_encode_instruction.
    iApply "J".
    iModIntro.
    iIntros "(Hpc & Hinstr2 & Hacc & Hr6)".
    rewrite <-parwp_sswp.
    iDestruct "Hprog" as "(p_start & Hprog)".
    iDestruct ((mov_reg (((of_pid progpage ^+ 1) ^+ 1)%f) ((of_pid progpage ^+ 1) ^+ 1)%f PC R7) with "[Hpc Hacc Hr7 p_start]") as "J".
    3 : { rewrite ->Forall_forall in seq. apply seq. set_solver. }
    3 : { apply Hprpain. }
    3 : { iFrame. }
    auto.
    by rewrite decode_encode_instruction.
    iApply "J".
    iModIntro.
    iDestruct ((ldr (of_pid progpage ^+ 1)%f src R1 R0) with "[Hpc Hacc Hr0 Hr1 Hsrc p_start HTX]") as "J".
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
    iIntros "(Hpc & Hinstr2 & Hr0 & Hsrc & Hr1 & Hacc & HTX)".
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
    iIntros "(Hpc & Hinstr4 & Hr0 & Hdst & Hr1 & Hacc & HRX)".
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
  
  Definition program_c step src dst :=
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
  *)
End copy_word.
