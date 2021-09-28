From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.algebra Require Import base.
From HypVeri.rules Require Import rules_base mov sub cmp bne.
From HypVeri.examples Require Import instr.

Section loop_macro.
  (* TODOs:
     - branch rule ???
   *)

  Context `{gen_VMG Σ}.

  Definition l_pre step base :=
    [
    Mov R5 (inl step); (* remaining runs *)
    Mov R6 (inl I0);    (* counter *)
    Mov R7 (inl base)    (* program base address *)
    ].

  Definition l_post :=
    [
    (* incr counter *)
    Mov R8 (inl I1);
    Sub R5 R8;
    (* conditional jump *)
    (* might be a good idea to have a separate rule for branches *)
    Cmp R6 (inr R5);
    Bne R7
    ].

  Definition cycle prog := prog ++ encode_instructions (l_post).
  Definition loop prog step base := encode_instructions (l_pre step base) ++ cycle prog.

Lemma cycle_spec {progaddr progpage sacc i q} {n : nat} step prog (P : Word -> iProp Σ) :
  length prog >0 ->
  S n = Z.to_nat (finz.to_z (of_imm step)) ->
  addr_in_page progaddr progpage ->
  progpage∈ sacc ->
  seq_in_page progaddr (length (cycle prog)) progpage ->
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
             ∗ (program prog progaddr)
      }}} ExecI @ i
      {{{ RET ExecI; (P v') ∗ PC @@ i ->r (progaddr ^+ (length prog))%f
          ∗ R6 @@ i ->r I0
          ∗ R5 @@ i ->r (v' ^+ 1)%f
          ∗ R7 @@ i ->r progaddr
          ∗ (∃ r, R8 @@ i ->r r)
          ∗ (∃ nz, NZ @@ i ->r nz)
          ∗ A@i :={q}[sacc]
          ∗ (program prog progaddr)
      }}}%I)%I
  ⊢  {PAR{{ (P step) ∗ PC @@ i ->r progaddr
            ∗ R5 @@ i ->r step
            ∗ R6 @@ i ->r I0
            ∗ R7 @@ i ->r progaddr
            ∗ (∃ r8, R8 @@ i ->r r8)
            ∗ (∃ nz, NZ @@ i ->r nz)
            ∗ A@i :={q}[sacc]
            ∗ program (cycle prog) progaddr
      }}} ExecI @ i
      {{{ RET ExecI; (P I0) ∗ PC @@ i ->r (progaddr ^+ (length (cycle prog )))%f
          ∗ R5 @@ i ->r (step ^- (S n))%f
          ∗ R6 @@ i ->r I0
          ∗ R7 @@ i ->r progaddr
          ∗ R8 @@ i ->r I1
          ∗ (∃ nz, NZ @@ i ->r nz)
          ∗ A@i :={q}[sacc]
          ∗ program (cycle prog) progaddr
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
      apply (seq_in_page_append1 progaddr (length prog) (length (cycle prog)) progpage).
      lia.
      rewrite /cycle.
      rewrite app_length.
      apply Nat.lt_add_pos_r.
      rewrite /l_post.
      simpl.
      lia.
      assumption.
    }
    assert (Htemp : (finz.seq progaddr (length prog)  ++ finz.seq (progaddr ^+ (length prog))%f 4)
                    = finz.seq progaddr (length (cycle prog))).
    { rewrite app_length encode_instructions_length.
      assert (length l_post = 4) as ->.
      done.
      rewrite (finz_seq_decomposition ((length prog) + 4) progaddr (length prog)).
      rewrite minus_plus.
      reflexivity.
      lia.
    }
    rewrite /program /loop.
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
               ∗ program prog progaddr))%I).
    instantiate (1:=
    (fun k => (⌜k = ExecI⌝ ∗ P I0
               ∗ PC @@ i ->r (progaddr ^+ (length prog))%f
               ∗ R5 @@ i ->r (I0 ^+ 1)%f
               ∗ R6 @@ i ->r I0
               ∗ R7 @@ i ->r progaddr
               ∗ (∃ r : handle, R8 @@ i ->r r)
               ∗ (∃ nz, NZ @@ i ->r nz)
               ∗ A@i:={q}[sacc]
               ∗ program prog progaddr))%I).
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
    2:{ instantiate (1:= progpage). apply c. rewrite /cycle. rewrite elem_of_list_In.
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
    iApply ((sub ((progaddr ^+ length prog ) ^+ 1)%f R5 R8) with "[Hpc Hacc Hr5 Hr8 p_start]").
    5:{ iFrame. }
    3:{ instantiate (1:= progpage).
          apply c. rewrite /cycle. rewrite elem_of_list_In.
          rewrite -Htemp.
          apply in_or_app.
          right.
          rewrite <-elem_of_list_In.
          set_solver.
    }
    3:{ apply Hprpain. }
    auto.
    rewrite decode_encode_instruction //.
    iModIntro.
    iIntros "(Hpc & Hinstr5 & Hr5 & Hr8 & Hacc)".
    iApply parwp_sswp.
    iDestruct "Hcpost" as "(p_start & Hcpost)".
    iApply ((cmp_reg (((progaddr ^+ length prog ) ^+ 1) ^+ 1)%f R6 R5) with "[Hpc Hacc Hr5 Hr6 Hnz p_start]").
    5:{ iFrame. }
    3:{ instantiate (1:= progpage). apply c. rewrite /cycle. rewrite elem_of_list_In.
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
    iApply ((bne ((((progaddr ^+ length prog ) ^+ 1) ^+ 1) ^+ 1)%f R7) with "[Hpc Hacc Hr7 Hnz p_start]").
    5:{ iFrame. }
    3:{ instantiate (1:= progpage). apply c. rewrite /cycle. rewrite elem_of_list_In.
          rewrite -Htemp.
          apply in_or_app.
          right.
          rewrite <-elem_of_list_In.
          set_solver.
    }
    reflexivity.
    apply decode_encode_instruction.
    apply Hprpain.
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
            (progaddr ^+ (length (cycle prog)))%f) as ->.
    rewrite app_length.
    rewrite /l_post.
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
    assert (Htemp : (finz.seq progaddr (length prog)  ++ finz.seq (progaddr ^+ (length prog))%f 4)
                    = finz.seq progaddr (length (cycle prog))).
    { rewrite app_length encode_instructions_length.
      assert (length l_post = 4) as ->.
      done.
      rewrite (finz_seq_decomposition ((length prog) + 4) progaddr (length prog)).
      rewrite minus_plus.
      reflexivity.
      lia.
    }
    iSpecialize ("HprogSpec" with "[] [] ").
    iPureIntro;lia.
    { iPureIntro.
      apply (seq_in_page_append1 progaddr (length prog) (length (cycle prog)) progpage).
      lia.
      rewrite /cycle.
      rewrite app_length.
      apply Nat.lt_add_pos_r.
      rewrite /l_post.
      simpl.
      lia.
      assumption.
    }
    rewrite /program /cycle.
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
               ∗ program prog  progaddr )%I)).
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
               ∗ program prog  progaddr )%I)).
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
    2: { instantiate (1:= progpage).  apply c. rewrite /cycle. rewrite elem_of_list_In.
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
      3 : { instantiate (1:= progpage). apply c. rewrite /cycle. rewrite elem_of_list_In.
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
        3 : { instantiate (1:= progpage).  apply c. rewrite /cycle. rewrite elem_of_list_In.
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
        3 : { instantiate (1:= progpage). apply c. rewrite /cycle. rewrite elem_of_list_In.
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

Lemma loop_spec {progpage sacc i q} {base : Imm} {n : nat} step prog (P : Word -> iProp Σ) :
  length prog > 0 ->
  of_imm base = ((of_pid progpage) ^+ 3)%f ->
  S n = Z.to_nat (finz.to_z (of_imm step)) ->
  progpage ∈ sacc ->
  seq_in_page (of_pid progpage) (length (loop prog step base)) progpage ->
  (forall l step, length (loop prog l base) = length (loop prog step base)) ->
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
            ∗ (program prog progaddr)
     }}} ExecI @ i
     {{{ RET ExecI; (P v') ∗ PC @@ i ->r (progaddr ^+ (length prog))%f
         ∗ R6 @@ i ->r I0
         ∗ R5 @@ i ->r (v' ^+ 1)%f
         ∗ R7 @@ i ->r progaddr
         ∗ (∃ r, R8 @@ i ->r r)
         ∗ (∃ nz, NZ @@ i ->r nz)
         ∗ A@i :={q}[sacc]
         ∗ (program prog progaddr)
     }}}%I)%I
  ⊢ {PAR{{ (P step) ∗ PC @@ i ->r (of_pid progpage)
           ∗ (∃ r5, R5 @@ i ->r r5)
           ∗ (∃ r6, R6 @@ i ->r r6)
           ∗ (∃ r7, R7 @@ i ->r r7)
           ∗ (∃ r8, R8 @@ i ->r r8)
           ∗ (∃ nz, NZ @@ i ->r nz)
           ∗ A@i :={q}[sacc]
           ∗ program (loop prog step base) (of_pid progpage)
    }}} ExecI @ i
    {{{ RET ExecI; (P I0) ∗ PC @@ i ->r (of_pid progpage ^+ (length (loop prog step base)))%f
        ∗ R5 @@ i ->r (step ^- (S n))%f
        ∗ R6 @@ i ->r I0
        ∗ R7 @@ i ->r ((of_pid progpage) ^+ 3)%f
        ∗ R8 @@ i ->r I1
        ∗ (∃ nz, NZ @@ i ->r nz)
        ∗ A@i :={q}[sacc]
        ∗ program (loop prog step base) (of_pid progpage)
    }}}%I.
Proof.
  iIntros (Hprogl Hbase Hn Hprpain Hseq Hlen) "#Htriple".
  rename Hn into eq.
  pose proof (seq_in_page_forall1 _ _ _ Hseq) as  c.
  iIntros (Φ).
  iModIntro.
  iIntros "(HPstep & Hpc & [% Hr5] & [% Hr6] & [% Hr7] & Hr8 & Hnz & Hacc & Hprog) HΦ".
  rewrite <-parwp_sswp.
  rewrite /program.
  assert (Htemp : (finz.seq (of_pid progpage) 3 ++ finz.seq ((of_pid progpage) ^+ 3)%f (length (cycle prog)) = finz.seq (of_pid progpage) (length (loop prog step base)))).
  { rewrite /loop app_length encode_instructions_length.
    assert (length (l_pre step base) = 3) as ->.
    done.
    rewrite (finz_seq_decomposition (3+ length(cycle prog)) (of_pid progpage) 3).
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
  iApply (cycle_spec step prog P with "[] [HPstep Hpc Hr5 Hr6 Hr7 Hr8 Hnz Hacc Hcloop]").
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
    rewrite /cycle.
    rewrite app_length /=.
    lia.
  }
  { assert (length (cycle prog) = (length (loop prog step base)) - 3) as ->.
    rewrite /loop app_length.
    simpl.
    lia.
    apply (seq_in_page_append2 (of_pid progpage) (length (loop prog step base)) 3 progpage).
    rewrite /cycle /cycle !app_length.
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
  assert (((progpage ^+ 3) ^+ length (cycle prog))%f = (progpage ^+ (length (loop prog step base))%nat)%f) as ->.
  solve_finz.
  rewrite app_length.
  iFrame.
Qed.

End loop_macro .
