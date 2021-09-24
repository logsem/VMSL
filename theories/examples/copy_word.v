From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.algebra Require Import base.
From HypVeri.rules Require Import rules_base mov ldr str sub cmp bne.

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
    pose proof (seq_in_page_forall1 _ _ _ Hseqp) as Hseq.
    rewrite <-parwp_sswp.
    iDestruct "Hbstar" as "(p_start & Hbstar)". 
    iDestruct ((mov_word (of_pid progpage) src R0) with "[Hpc Hai Hr0 p_start]") as "J".
    2 : {  apply Hseq. set_solver. }
    2 : { apply Hprpain. }
    2 : { iFrame. }
    auto.
    by rewrite decode_encode_instruction.
    iApply "J".
    iModIntro.
    iIntros "(Hpc & Hinstr1 & Hacc & Hr0)".
    rewrite <-parwp_sswp.
    iDestruct "Hbstar" as "(p_start & Hbstar)".
    iDestruct ((ldr (of_pid progpage ^+ 1)%f src R1 R0) with "[Hpc Hacc Hr0 Hr1 Hsrc p_start HTX]") as "J".
    instantiate (1 := encode_instruction (Ldr R1 R0)).
    by rewrite decode_encode_instruction.
    instantiate (1 := ptx).
    intros C.
    apply to_pid_aligned_in_page in Hsrcp.
    rewrite <-Hsrcp in Hneq.
    rewrite C in Hneq.
    apply Hneq.
    reflexivity.
    specialize (Hseq (progpage ^+ 1)%f).
    instantiate (1 := sacc).
    apply to_pid_aligned_in_page in Hsrcp.
    subst srcpage.
    assert (Hp : (progpage ^+ 1)%f ∈ finz.seq progpage (length (program src dst))).
    set_solver.
    specialize (Hseq Hp).
    apply to_pid_aligned_in_page in Hseq.
    rewrite Hseq.
    set_solver.
    iFrame.
    iApply "J".
    iModIntro.
    iIntros "(Hpc & Hinstr2 & Hr0 & Hsrc & Hr1 & Hacc & HTX)".
    rewrite <-parwp_sswp.
    iDestruct "Hbstar" as "(p_start & Hbstar)".
    iDestruct ((mov_word ((of_pid progpage ^+ 1) ^+ 1)%f dst R0) with "[Hpc Hacc Hr0 p_start]") as "J".
    2 : { apply Hseq. set_solver. }
    2 : { apply Hprpain. }
    2 : { iFrame. }
    auto.
    by rewrite decode_encode_instruction.
    iApply "J".
    iModIntro.
    iIntros "(Hpc & Hinstr3 & Hacc & Hr0)".
    rewrite <-parwp_sswp.
    iDestruct "Hbstar" as "(p_start & Hbstar)".
    iDestruct ((str (((of_pid progpage ^+ 1) ^+ 1) ^+ 1)%f dst R1 R0) with "[Hpc Hacc Hr0 p_start Hdst Hr1 HRX]") as "J".
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
    specialize (Hseq (((progpage ^+ 1) ^+ 1) ^+ 1)%f).
    pose proof (to_pid_aligned_in_page (((progpage ^+ 1) ^+ 1) ^+ 1)%f progpage) as Hp.
    assert (Hq : (((progpage ^+ 1) ^+ 1) ^+ 1)%f ∈ finz.seq progpage (length (program src dst))).
    set_solver.
    specialize (Hseq Hq).
    specialize (Hp Hseq).
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

  Definition c_pre step base :=
    [
    mov_word_I R5 step; (* remaining runs *)
    mov_word_I R6 I0;    (* counter *)
    mov_word_I R7 base    (* program base address *)
    ].

  Definition c_post :=
    [
    (* incr counter *)
    mov_word_I R8 I1;
    sub_reg_I R5 R8;
    (* conditional jump *)
    (* might be a good idea to have a separate rule for branches *)
    cmp_I R6 R5;
    bne_I R7
    ].

  Definition c_loop prog := prog ++ c_post.
  Definition cycle prog step base := c_pre step base ++ c_loop prog.

Lemma c_loop_ind_spec {progaddr progpage sacc i q} {n : nat} step prog (P : Word -> iProp Σ) :
  length prog >0 ->
  S n = Z.to_nat (finz.to_z (of_imm step)) ->
  addr_in_page progaddr progpage ->
  progpage∈ sacc ->
  seq_in_page progaddr (length (c_loop prog)) progpage ->
  (∀ v (v' : Word) ,
      ⌜ v = Z.to_nat (finz.to_z v') ⌝ -∗
      ⌜ v <= S n ⌝-∗
      ⌜ seq_in_page progaddr (length prog) progpage ⌝ -∗
      {PAR{{ (P (v' ^+ 1)%f) ∗ PC @@ i ->r progaddr
             ∗ R6 @@ i ->r I0
             ∗ R5 @@ i ->r (v' ^+ 1)%f
             ∗ R7 @@ i ->r progaddr
             ∗ (∃ r, R8 @@ i ->r r)
             ∗ (∃ nz, NZ @@ i ->r nz)
             ∗ A@i :={q}[sacc]
             ∗ (program' prog progaddr)
      }}} ExecI @ i
      {{{ RET ExecI; (P v') ∗ PC @@ i ->r (progaddr ^+ (length prog))%f
          ∗ R6 @@ i ->r I0
          ∗ R5 @@ i ->r (v' ^+ 1)%f
          ∗ R7 @@ i ->r progaddr
          ∗ (∃ r, R8 @@ i ->r r)
          ∗ (∃ nz, NZ @@ i ->r nz)
          ∗ A@i :={q}[sacc]
          ∗ (program' prog progaddr)
      }}}%I)%I
  ⊢  {PAR{{ (P step) ∗ PC @@ i ->r progaddr
            ∗ R5 @@ i ->r step
            ∗ R6 @@ i ->r I0
            ∗ R7 @@ i ->r progaddr
            ∗ (∃ r8, R8 @@ i ->r r8)
            ∗ (∃ nz, NZ @@ i ->r nz)
            ∗ A@i :={q}[sacc]
            ∗ program' (c_loop prog) progaddr
      }}} ExecI @ i
      {{{ RET ExecI; (P I0) ∗ PC @@ i ->r (progaddr ^+ (length (c_loop prog )))%f
          ∗ R5 @@ i ->r (step ^- (S n))%f
          ∗ R6 @@ i ->r I0
          ∗ R7 @@ i ->r progaddr
          ∗ R8 @@ i ->r I1
          ∗ (∃ nz, NZ @@ i ->r nz)
          ∗ A@i :={q}[sacc]
          ∗ program' (c_loop prog) progaddr
      }}}%I.
Proof.
  iIntros (Hprogl Hn Hprogaddrin Hprpain Hseq) "#Htriple".
  rename Hn into eq.
  iIntros (Φ).
  iModIntro.
  iIntros "(HPstep & Hpc & Hr5 & Hr6 & Hr7 & Hr8 & Hnz & Hacc & Hprog) HΦ".
  iInduction n as [| n] "IH" forall (step eq Hseq).
  - pose proof (seq_in_page_forall1 _ _ _ Hseq) as c.
    iDestruct ("Htriple" $! 0 I0 with "") as "#HprogSpec".
    iSpecialize ("HprogSpec"   with "[//] [] []").
    iPureIntro;lia.
    { iPureIntro.
      apply (seq_in_page_append1 progaddr (length prog) (length (c_loop prog)) progpage).
      lia.
      rewrite /c_loop.
      rewrite app_length.
      apply Nat.lt_add_pos_r.
      rewrite /c_post.
      simpl.
      lia.
      assumption.
    }
    assert (Htemp : (finz.seq progaddr (length prog)  ++ finz.seq (progaddr ^+ (length prog))%f 4) = finz.seq progaddr (length (prog ++ c_post))).
    { rewrite app_length.
      assert (length c_post = 4) as ->.
      done.
      rewrite (finz_seq_decomposition ((length prog) + 4) progaddr (length prog)).
      rewrite minus_plus.
      reflexivity.
      lia.
    }
    rewrite /program' /c_loop .
    rewrite -Htemp.
    iDestruct (big_sepL2_app_inv with "Hprog") as "(Hprog & Hcpost)".
    { rewrite finz_seq_length.  left;done. }
    iDestruct ("HprogSpec" with "[HPstep Hpc Hr5 Hr6 Hr7 Hr8 Hnz Hacc Hprog ]") as "J".
    iFrame.
    assert ( (I0 ^+ 1)%f = step) as ->.
    rewrite /I0 //.
    simpl.
    apply finz_to_z_eq.
    simpl.
    lia.
    iFrame.
    iApply parwp_parwp.
    iApply (parwp_strong_mono with "[J]").
    instantiate (1 := ⊤).
    set_solver.
    instantiate (3:=
    (fun k => (⌜k = ExecI⌝ ∗ P I0
               ∗ PC @@ i ->r (progaddr ^+ (length prog))%f
               ∗ R5 @@ i ->r (I0 ^+ 1)%f
               ∗ R6 @@ i ->r I0
               ∗ R7 @@ i ->r progaddr
               ∗ (∃ r : handle, R8 @@ i ->r r)
               ∗ (∃ nz, NZ @@ i ->r nz)
               ∗ A@i:={q}[sacc]
               ∗ program' prog  progaddr )%I)).
    iApply "J".
    iModIntro.
    iIntros "(? & ? & ? & ? & ? & ? & ? & ? & ?)".
    iFrame.
    done.
    iIntros (k) "(%Heq & HP & Hpc & Hr5 & Hr6 & Hr7 & [%r8' Hr8] & [%nz' Hnz] & Hacc & Hprog)".
    subst k.
    iModIntro.
    iDestruct "Hcpost" as "(p_start & Hcpost)".
    iDestruct ((mov_word (progaddr ^+ length prog )%f I1 R8) with "[Hpc Hacc Hr8 p_start]") as "J".
    4:{ iFrame. }
    2:{ instantiate (1:= progpage). apply c. rewrite /c_loop. rewrite elem_of_list_In.
          rewrite -Htemp.
          apply in_or_app.
          right.
          rewrite <-elem_of_list_In.
          set_solver.
    }
    2:{ apply Hprpain. }
    auto.
    rewrite decode_encode_instruction //.
    iApply parwp_sswp.
    iApply "J".
    iModIntro.
    iIntros "(Hpc & Hinstr4 & Hacc & Hr8)".
    iApply parwp_sswp.
    iDestruct "Hcpost" as "(p_start & Hcpost)".
    iDestruct ((sub ((progaddr ^+ length prog ) ^+ 1)%f R5 R8) with "[Hpc Hacc Hr5 Hr8 p_start]") as "J".
    5:{ iFrame. }
    3:{ instantiate (1:= progpage).
          apply c. rewrite /c_loop. rewrite elem_of_list_In.
          rewrite -Htemp.
          apply in_or_app.
          right.
          rewrite <-elem_of_list_In.
          set_solver.
    }
    3:{ apply Hprpain. }
    auto.
    rewrite decode_encode_instruction //.
    iApply "J".
    iModIntro.
    iIntros "(Hpc & Hinstr5 & Hr5 & Hr8 & Hacc)".
    iApply parwp_sswp.
    iDestruct "Hcpost" as "(p_start & Hcpost)".
    iDestruct ((cmp_reg (((progaddr ^+ length prog ) ^+ 1) ^+ 1)%f R6 R5) with "[Hpc Hacc Hr5 Hr6 Hnz p_start]") as "J".
    5:{ iFrame. }
    3:{ instantiate (1:= progpage). apply c. rewrite /c_loop. rewrite elem_of_list_In.
          rewrite -Htemp.
          apply in_or_app.
          right.
          rewrite <-elem_of_list_In.
          set_solver.
    }
    reflexivity.
    apply decode_encode_instruction.
    apply Hprpain.
    iFrame.
    iApply "J".
    iModIntro.
    iIntros "(Hpc & Hinstr6 & Hr6 & Hr5 & Hacc & Hnz)".
    assert ((I0 <? I0 ^+ 1 ^- I1)%f = false) as ->.
    {
      rewrite /I0 /I1.
      simpl.
      solve_finz.
    }
    assert ((I0 ^+ 1 ^- I1 <? I0)%f = false) as ->.
    {
      rewrite /I0 /I1.
      simpl.
      solve_finz.
    }
    iApply parwp_sswp.
    iDestruct "Hcpost" as "(p_start & Hcpost)".
    iDestruct ((bne ((((progaddr ^+ length prog ) ^+ 1) ^+ 1) ^+ 1)%f R7) with "[Hpc Hacc Hr7 Hnz p_start]") as "J".
    5:{ iFrame. }
    3:{ instantiate (1:= progpage). apply c. rewrite /c_loop. rewrite elem_of_list_In.
          rewrite -Htemp.
          apply in_or_app.
          right.
          rewrite <-elem_of_list_In.
          set_solver.
    }
    reflexivity.
    apply decode_encode_instruction.
    apply Hprpain.
    iApply "J".
    iModIntro.
    iSimpl.
    iIntros "(Hpc & Hinstr7 & Hr7 & Hacc & Hnz)".
    iApply parwp_finish.
    iApply "HΦ".
    iFrame.
    assert ((I0 ^+ 1)%f = step) as ->.
    rewrite /I0.
    simpl.
    solve_finz.
    iFrame.
    iSplitR "Hnz";
      last (iExists W1; iFrame).
    assert ((((((progaddr ^+ length prog) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f =
            (progaddr ^+ (length (prog ++ c_post)))%f) as ->.
    rewrite app_length.
    rewrite /c_post.
    solve_finz.
    iFrame.
  - pose proof (seq_in_page_forall1 _ _ _ Hseq) as c.
    assert (Hstep : S n = Z.to_nat (step ^- 1)%f).
    solve_finz.
    assert (Htemp' : exists (im : Imm), (step ^- 1)%f = im).
    destruct step.
    simpl in eq.
    simpl.
    simpl in Hstep.
    eexists (I (w ^- 1)%f ?[a]).
    f_equal.
    [a]: lia.
    destruct Htemp' as [im Himeq].
    rewrite Himeq in Hstep.
    iDestruct ("Htriple" $! (S n) im ?[b] with "") as "#HprogSpec".
    [b]: solve_finz.
    assert (Htemp : (finz.seq progaddr (length prog)  ++ finz.seq (progaddr ^+ (length prog))%f 4) = finz.seq progaddr (length (prog ++ c_post))).
    { rewrite app_length.
      assert (length c_post = 4) as ->.
      done.
      rewrite (finz_seq_decomposition ((length prog) + 4) progaddr (length prog)).
      rewrite minus_plus.
      reflexivity.
      lia.
    }
    iSpecialize ("HprogSpec"   with "[] [] ").
    iPureIntro;lia.
    { iPureIntro.
      apply (seq_in_page_append1 progaddr (length prog) (length (c_loop prog)) progpage).
      lia.
      rewrite /c_loop.
      rewrite app_length.
      apply Nat.lt_add_pos_r.
      rewrite /c_post.
      simpl.
      lia.
      assumption.
    }
    rewrite /program' /c_loop .
    rewrite -Htemp.
    iDestruct (big_sepL2_app_inv with "Hprog") as "(Hprog & Hcpost)".
    { rewrite finz_seq_length.  left;done. }
    iDestruct ("HprogSpec" with "[HPstep Hpc Hr5 Hr6 Hr7 Hr8 Hnz Hacc Hprog ]") as "J".
    iFrame.
    assert (of_imm step = (im ^+ 1)%f) as ->.
    { rewrite -Himeq.
      solve_finz.
    }
    iFrame.
    iApply parwp_parwp.
    iApply (parwp_strong_mono with "[J]").
    instantiate (1 := ⊤).
    set_solver.
    instantiate (2:=
    (fun k => (⌜k = ExecI⌝ ∗ P im
               ∗ PC @@ i ->r (progaddr ^+ (length prog))%f
               ∗ R5 @@ i ->r (im ^+ 1)%f
               ∗ R6 @@ i ->r I0
               ∗ R7 @@ i ->r progaddr
               ∗ (∃ r : handle, R8 @@ i ->r r)
               ∗ (∃ nz, NZ @@ i ->r nz)
               ∗ A@i:={q}[sacc]
               ∗ program' prog  progaddr )%I)).
    iClear "HprogSpec".
    instantiate (1 :=
    (fun k => (⌜k = ExecI⌝ ∗ P im
               ∗ PC @@ i ->r (progaddr ^+ (length prog))%f
               ∗ R5 @@ i ->r (im ^+ 1)%f
               ∗ R6 @@ i ->r I0
               ∗ R7 @@ i ->r progaddr
               ∗ (∃ r : handle, R8 @@ i ->r r)
               ∗ (∃ nz, NZ @@ i ->r nz)
               ∗ A@i:={q}[sacc]
               ∗ program' prog  progaddr )%I)).
    iApply "J".
    iModIntro.
    iIntros "(? & ? & ? & ? & ? & ? & ? & ? & ?)".
    iFrame.
    done.
    iIntros (k) "(%Heq & HP & Hpc & Hr5 & Hr6 & Hr7 & [%r8' Hr8] & [%nz' Hnz] & Hacc & Hprog)".
    subst k.
    iModIntro.
    iDestruct "Hcpost" as "(p_start & Hcpost)".
    iDestruct ((mov_word (progaddr ^+ length prog )%f I1 R8) with "[Hpc Hacc Hr8 p_start]") as "J".
    4: { iFrame. }
    2: { instantiate (1:= progpage).  apply c. rewrite /c_loop. rewrite elem_of_list_In.
          rewrite -Htemp.
          apply in_or_app.
          right.
          rewrite <-elem_of_list_In.
          set_solver.
    }
    2 : { apply Hprpain. }
    auto.
      by rewrite decode_encode_instruction.
      instantiate (1 := (fun m' => (PARWP m' @ i {{ v, Φ v }})%I )).
      instantiate (1 := ⊤).
      iApply parwp_sswp.
      iApply "J".
      iModIntro.
      iIntros "(Hpc & Hinstr4 & Hacc & Hr8)".
      iApply parwp_sswp.
      iDestruct "Hcpost" as "(p_start & Hcpost)".
      iDestruct ((sub ((progaddr ^+ length prog ) ^+ 1)%f R5 R8) with "[Hpc Hacc Hr5 Hr8 p_start]") as "J".
      5: { iFrame. }
      3 : { instantiate (1:= progpage). apply c. rewrite /c_loop. rewrite elem_of_list_In.
            rewrite -Htemp.
            apply in_or_app.
            right.
            rewrite <-elem_of_list_In.
            set_solver.
      }
      3 : { apply Hprpain. }
      auto.
        by rewrite decode_encode_instruction.
        instantiate (1 := (fun m' => (PARWP m' @ i {{ v, Φ v }})%I )).
        iApply "J".
        iModIntro.
        iIntros "(Hpc & Hinstr5 & Hr5 & Hr8 & Hacc)".
        iApply parwp_sswp.
        iDestruct "Hcpost" as "(p_start & Hcpost)".
        iDestruct ((cmp_reg (((progaddr ^+ length prog ) ^+ 1) ^+ 1)%f R6 R5) with "[Hpc Hacc Hr5 Hr6 Hnz p_start]") as "J".
        5: {iFrame. }
        3 : { instantiate (1:= progpage).  apply c. rewrite /c_loop. rewrite elem_of_list_In.
              rewrite -Htemp.
              apply in_or_app.
              right.
              rewrite <-elem_of_list_In.
              set_solver.
        }
        reflexivity.
        apply decode_encode_instruction.
        apply Hprpain.
        iFrame.
        instantiate (1 := (fun m' => (PARWP m' @ i {{ v, Φ v }})%I )).
        iApply "J".
        iModIntro.
        iIntros "(Hpc & Hinstr6 & Hr6 & Hr5 & Hacc & Hnz)".
        assert ((I0 <? im ^+ 1 ^- I1)%f = true) as ->.
        {
          rewrite /I0 /I1 -Himeq /= .
          solve_finz.
        }
        iApply parwp_sswp.
        iDestruct "Hcpost" as "(p_start & Hcpost)".
        iDestruct ((bne ((((progaddr ^+ length prog ) ^+ 1) ^+ 1) ^+ 1)%f R7) with "[Hpc Hacc Hr7 Hnz p_start]") as "J".
        5 : { iFrame. }
        3 : { instantiate (1:= progpage). apply c. rewrite /c_loop. rewrite elem_of_list_In.
              rewrite -Htemp.
              apply in_or_app.
              right.
              rewrite <-elem_of_list_In.
              set_solver.
        }
        reflexivity.
        apply decode_encode_instruction.
        apply Hprpain.
        instantiate (1 := (fun m' => (PARWP m' @ i {{ v, Φ v }})%I )).
        iApply "J".
        iModIntro.
        iSimpl.
        iIntros "(Hpc & Hinstr7 & Hr7 & Hacc & Hnz)".
        assert ((im ^+ 1 ^- I1)%f = im) as ->.
        {
          rewrite /I1 /=.
          solve_finz.
        }
        iApply ("IH" $! im with "[] [] [] HP Hpc Hr5 Hr6 Hr7 [Hr8] [Hnz] Hacc [Hprog Hinstr4 Hinstr5 Hinstr6 Hinstr7]  [HΦ]").
        {
          iPureIntro.
          rewrite -Himeq.
          solve_finz.
        }
        {
          done.
        }
        iModIntro.
        iIntros (v_ v'_ ) "%Hv_ %Hv'_".
        iApply ("Htriple" $! v_ v'_ ).
        { iPureIntro.
          lia.
        }
        { iPureIntro.
          lia.
        }
        iExists I1;iFrame.
        iExists W2;iFrame.
        iFrame.
        done.
        assert ((step ^- S (S n))%f = (im ^- S n)%f) as ->.
        solve_finz.
        iFrame.
Qed.

Lemma c_loop_spec {progpage sacc i q} {base : Imm} {n : nat} step prog (P : Word -> iProp Σ) :
  length prog > 0 ->
  of_imm base = ((of_pid progpage) ^+ 3)%f ->
  S n = Z.to_nat (finz.to_z (of_imm step)) ->
  progpage ∈ sacc ->
  seq_in_page (of_pid progpage) (length (cycle prog step base)) progpage ->
  (forall l step, length (cycle prog l base) = length (cycle prog step base)) ->
  (∀ v (v' : Word) progaddr,
     ⌜v = Z.to_nat (finz.to_z v')⌝ -∗
     ⌜v <= S n⌝-∗
     ⌜seq_in_page progaddr (length prog) progpage⌝ -∗
     {PAR{{ (P (v' ^+ 1)%f) ∗ PC @@ i ->r progaddr
            ∗ R6 @@ i ->r I0
            ∗ R5 @@ i ->r (v' ^+ 1)%f
            ∗ R7 @@ i ->r progaddr
            ∗ (∃ r, R8 @@ i ->r r)
            ∗ (∃ nz, NZ @@ i ->r nz)
            ∗ A@i :={q}[sacc]
            ∗ (program' prog progaddr)
     }}} ExecI @ i
     {{{ RET ExecI; (P v') ∗ PC @@ i ->r (progaddr ^+ (length prog))%f
         ∗ R6 @@ i ->r I0
         ∗ R5 @@ i ->r (v' ^+ 1)%f
         ∗ R7 @@ i ->r progaddr
         ∗ (∃ r, R8 @@ i ->r r)
         ∗ (∃ nz, NZ @@ i ->r nz)
         ∗ A@i :={q}[sacc]
         ∗ (program' prog progaddr)
     }}}%I)%I
  ⊢ {PAR{{ (P step) ∗ PC @@ i ->r (of_pid progpage)
           ∗ (∃ r5, R5 @@ i ->r r5)
           ∗ (∃ r6, R6 @@ i ->r r6)
           ∗ (∃ r7, R7 @@ i ->r r7)
           ∗ (∃ r8, R8 @@ i ->r r8)
           ∗ (∃ nz, NZ @@ i ->r nz)
           ∗ A@i :={q}[sacc]
           ∗ program' (cycle prog step base) (of_pid progpage)
    }}} ExecI @ i
    {{{ RET ExecI; (P I0) ∗ PC @@ i ->r (of_pid progpage ^+ (length (cycle prog step base)))%f
        ∗ R5 @@ i ->r (step ^- (S n))%f
        ∗ R6 @@ i ->r I0
        ∗ R7 @@ i ->r ((of_pid progpage) ^+ 3)%f
        ∗ R8 @@ i ->r I1
        ∗ (∃ nz, NZ @@ i ->r nz)
        ∗ A@i :={q}[sacc]
        ∗ program' (cycle prog step base) (of_pid progpage)
    }}}%I.
Proof.
  iIntros (Hprogl Hbase Hn Hprpain Hseq Hlen) "#Htriple".
  rename Hn into eq.
  pose proof (seq_in_page_forall1 _ _ _ Hseq) as  c.
  iIntros (Φ).
  iModIntro.
  iIntros "(HPstep & Hpc & [% Hr5] & [% Hr6] & [% Hr7] & Hr8 & Hnz & Hacc & Hprog) HΦ".
  rewrite <-parwp_sswp.
  rewrite /program' /cycle.
  assert (Htemp : (finz.seq (of_pid progpage) 3 ++ finz.seq ((of_pid progpage) ^+ 3)%f (length (c_loop prog)) = finz.seq (of_pid progpage) (length (c_pre step base ++ c_loop prog)))).
  { rewrite app_length.
    assert (length (c_pre step base) = 3) as ->.
    done.
    rewrite (finz_seq_decomposition (3+ length(c_loop prog)) (of_pid progpage) 3).
    rewrite minus_plus.
    reflexivity.
    lia.
  }
  rewrite -Htemp.
  iDestruct (big_sepL2_app_inv with "Hprog") as "(Hcpre & Hcloop)".
  { rewrite finz_seq_length.  left;done. }
  iDestruct "Hcpre" as "(p_start & Hprog)".
  iDestruct ((mov_word (of_pid progpage) step R5) with "[Hpc Hacc Hr5 p_start]") as "J".
  2:{ apply c. set_solver. }
  2:{ apply Hprpain. }
  2:{ iFrame. }
  auto.
  rewrite decode_encode_instruction //.
  iApply "J".
  iModIntro.
  iIntros "(Hpc & Hinstr1 & Hacc & Hr5)".
  rewrite <-parwp_sswp.
  iDestruct "Hprog" as "(p_start & Hprog)".
  iDestruct ((mov_word (of_pid progpage ^+ 1)%f I0 R6) with "[Hpc Hacc Hr6 p_start]") as "J".
  2:{ apply c. set_solver. }
  2:{ apply Hprpain. }
  2:{ iFrame. }
  auto.
  rewrite decode_encode_instruction //.
  iApply "J".
  iModIntro.
  iIntros "(Hpc & Hinstr2 & Hacc & Hr6)".
  rewrite <-parwp_sswp.
  iDestruct "Hprog" as "(p_start & Hprog)".
  iDestruct ((mov_word ((of_pid progpage ^+ 1) ^+ 1)%f base R7) with "[Hpc Hacc Hr7 p_start]") as "J".
  2:{ apply c. set_solver. }
  2:{ apply Hprpain. }
  2:{ iFrame. }
  auto.
  rewrite decode_encode_instruction //.
  iApply "J".
  iModIntro.
  iIntros "(Hpc & Hinstr3 & Hacc & Hr7)".
  iApply parwp_parwp.
  iApply (c_loop_ind_spec step prog P with "[] [HPstep Hpc Hr5 Hr6 Hr7 Hr8 Hnz Hacc Hcloop]").
  done.
  exact eq.
  2:{ exact Hprpain. }
  4:{ iFrame. rewrite Hbase. assert ((((progpage ^+ 1) ^+ 1) ^+ 1)%f = (progpage ^+ 3)%f) as ->.
       solve_finz.
       iFrame. }
  { apply c.
    rewrite /cycle -Htemp.
    apply elem_of_list_In.
    apply in_or_app.
    right.
    apply elem_of_list_In.
    rewrite finz_seq_cons.
    set_solver.
    rewrite /c_loop.
    rewrite app_length /=.
    lia.
  }
  { assert (length (c_loop prog) = (length (cycle prog step base)) - 3) as ->.
    rewrite /cycle app_length.
    simpl.
    lia.
    apply (seq_in_page_append2 (of_pid progpage) (length (cycle prog step base)) 3 progpage).
    rewrite /cycle /c_loop !app_length.
    simpl.
    lia.
    pose proof (last_addr_in_bound progpage).
    solve_finz.
    done.
  }
  iIntros (v v').
  iApply "Htriple".
  iNext.
  iIntros "(? & ? & ? & ? & ? & ? & ?)".
  iApply parwp_finish.
  iApply "HΦ".
  iFrame.
  rewrite app_length.
  iFrame.
  assert (((progpage ^+ 3) ^+ length (c_loop prog))%f = (progpage ^+ (length (c_pre step base) + length (c_loop prog))%nat)%f) as ->.
  solve_finz.
  iFrame.
Qed.


  (*
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
