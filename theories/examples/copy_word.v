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

  Definition cycle prog step base := c_pre step base ++ (prog step) ++ c_post.

  Lemma c_loop {progpage sacc i q} {base : Imm} {n : nat} (body : list Word) step prog (P : Word -> iProp Σ) :
    of_imm base = ((of_pid progpage) ^+ 3)%f ->
    S n = Z.to_nat (finz.to_z (of_imm step)) ->
    progpage ∈ sacc ->
    seq_in_page (of_pid progpage) (length (cycle prog step base)) progpage ->
    (forall l step, length (cycle prog l base) = length (cycle prog step base)) ->
    (∀ v (v' : Word) v'' (step : Imm), ⌜v = Z.to_nat (finz.to_z v') ∧ (v <= S n)⌝ -∗ {PAR{{ (P (v' ^+ 1)%f) ∗ PC @@ i ->r ((of_pid progpage) ^+ 3)%f
                         ∗ R6 @@ i ->r v''
                         ∗ R5 @@ i ->r step
                         ∗ R7 @@ i ->r ((of_pid progpage) ^+ 3)%f
                         ∗ (∃ r, R8 @@ i ->r r)
                         ∗ (∃ nz, NZ @@ i ->r nz)             
                         ∗ A@i :={q}[sacc]
                         ∗ (program' (cycle prog step base) (of_pid progpage))
            }}} ExecI @ i
    {{{ RET ExecI; (P v') ∗ PC @@ i ->r (((of_pid progpage) ^+ 3)%f ^+ (length (prog step)))%f
                         ∗ R6 @@ i ->r v''
                         ∗ R5 @@ i ->r step
                         ∗ R7 @@ i ->r ((of_pid progpage) ^+ 3)%f
                         ∗ (∃ r, R8 @@ i ->r r)
                         ∗ (∃ nz, NZ @@ i ->r nz)  
                         ∗ A@i :={q}[sacc]
                         ∗ (program' (cycle prog step base) (of_pid progpage))
    }}}%I)
    ⊢  {PAR{{ (P step) ∗ PC @@ i ->r (of_pid progpage)
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
    iIntros (Hbase Hn Hprpain Hseq Hlen) "#Htriple".
    iInduction n as [| n] "IH" forall (step Hn Hseq Hlen).
    - rename Hn into eq.
      rename Hseq into c.
      apply seq_in_page_forall in c.
      iIntros (Φ).
      iModIntro.
      iIntros "(HPstep & Hpc & [% Hr5] & [% Hr6] & [% Hr7] & [% Hr8] &[% Hnz] & Hacc & Hprog) HΦ".
      rewrite <-parwp_sswp.
      iDestruct "Hprog" as "(p_start & Hprog)". 
      iDestruct ((mov_word (of_pid progpage) step R5) with "[Hpc Hacc Hr5 p_start]") as "J".
      3 : { rewrite ->Forall_forall in c. apply c. set_solver. }
      3 : { apply Hprpain. }
      3 : { iFrame. }
      auto.
      by rewrite decode_encode_instruction.
      iApply "J".
      iModIntro.
      iIntros "(Hpc & Hinstr1 & Hacc & Hr5)".
      rewrite <-parwp_sswp.
      iDestruct "Hprog" as "(p_start & Hprog)".
      iDestruct ((mov_word (of_pid progpage ^+ 1)%f I0 R6) with "[Hpc Hacc Hr6 p_start]") as "J".
      3 : { rewrite ->Forall_forall in c. apply c. set_solver. }
      3 : { apply Hprpain. }
      3 : { iFrame. }
      auto.
      by rewrite decode_encode_instruction.
      iApply "J".
      iModIntro.
      iIntros "(Hpc & Hinstr2 & Hacc & Hr6)".
      rewrite <-parwp_sswp.
      iDestruct "Hprog" as "(p_start & Hprog)".
      iDestruct ((mov_word ((of_pid progpage ^+ 1) ^+ 1)%f base R7) with "[Hpc Hacc Hr7 p_start]") as "J".
      3 : { rewrite ->Forall_forall in c. apply c. set_solver. }
      3 : { apply Hprpain. }
      3 : { iFrame. }
      auto.
      by rewrite decode_encode_instruction.
      iApply "J".
      iModIntro.
      iIntros "(Hpc & Hinstr3 & Hacc & Hr7)".
      iDestruct ("Htriple" $! 0 I0 I0 step _ with "") as "#HprogSpec".
      Unshelve.
      2 : {
        split.
        rewrite /I0.
        simpl.
        lia.
        solve_finz.
      }
      iSpecialize ("HprogSpec" $! (fun k => (⌜k = ExecI⌝
                                     ∗ P I0
                                            ∗ PC @@ i ->r ((progpage ^+ 3) ^+ length (prog step))%f
                                            ∗ R5 @@ i ->r step
                                            ∗ R6 @@ i ->r I0
                                            ∗ R7 @@ i ->r (progpage ^+ 3)%f
                                            ∗ (∃ r : handle, R8 @@ i ->r r)
                                            ∗ (∃ nz, NZ @@ i ->r nz)             
                                            ∗ A@i:={q}[sacc]
                                            ∗ program' (cycle prog step base) progpage)%I) with "").
      iDestruct ("HprogSpec" with "[HPstep Hpc Hr5 Hr6 Hr7 Hr8 Hnz Hacc Hprog Hinstr1 Hinstr2 Hinstr3]") as "J".
      iFrame.
      rewrite Hbase.
      assert (Hn : (progpage ^+ 3)%f = (((progpage ^+ 1) ^+ 1) ^+ 1)%f).
      solve_finz.
      rewrite Hn.
      clear Hn.
      iFrame.
      assert (Htemp : (I0 ^+ 1)%f = step).
      rewrite /I0 //.
      simpl.
      apply finz_to_z_eq.
      simpl.
      lia.
      rewrite Htemp. clear Htemp.
      iFrame.
      iSplitL "Hr8".
      iExists r8.
      iFrame.
      iExists nz.
      iFrame.
      iApply parwp_parwp.
      iApply (parwp_strong_mono with "[J]").
      instantiate (1 := ⊤).
      set_solver.
      iApply "J".
      iModIntro.
      iIntros "(? & ? & ? & ? & ? & ? & ? & ? & ?)".
      iFrame.
      done.
      iIntros (k) "(%Heq & HP & Hpc & Hr5 & Hr6 & Hr7 & [%r8' Hr8] & [%nz' Hnz] & Hacc & Hprog)".
      subst k.
      iModIntro.
      assert (Hn : cycle prog step base = (c_pre step base ++ (prog step)) ++ c_post).
      auto.
      rewrite /program'.
      assert (Hn' : finz.seq progpage (length (cycle prog step base)) = (finz.seq progpage 3 ++ finz.seq (progpage ^+ 3)%f (length (prog step))) ++ finz.seq ((progpage ^+ 3) ^+ (length (prog step)))%f 4).
      {
        assert (Htemp : (finz.seq progpage 3 ++ finz.seq (progpage ^+ 3)%f (length (prog step) + 3 - 3)) = finz.seq progpage (length (prog step) + 3)).
        {
          rewrite (finz_seq_decomposition ((length (prog step)) + 3) progpage 3).
          reflexivity.
          lia.
        }
        assert (Htemp' : length (prog step) = (length (prog step) + 3 - 3)).
        lia.
        rewrite <-Htemp' in Htemp.
        clear Htemp'.
        rewrite Htemp.
        clear Htemp.
        assert (Htemp : (finz.seq progpage (length (prog step) + 3) ++ finz.seq ((progpage ^+ 3) ^+ length (prog step))%f 4) = finz.seq progpage (length (cycle prog step base))).
        {
          rewrite (finz_seq_decomposition (length (cycle prog step base)) progpage (length (prog step) + 3)).
          f_equal.
          assert (Htemp' : ((progpage ^+ 3) ^+ length (prog step))%f = (progpage ^+ (length (prog step) + 3)%nat)%f).
          solve_finz.
          rewrite Htemp'.
          clear Htemp'.
          assert (Htemp' : (length (cycle prog step base) - (length (prog step) + 3)) = 4).
          rewrite /cycle.
          simpl.
          rewrite Nat.add_comm.
          simpl.
          rewrite app_length.
          rewrite minus_plus.
          rewrite /c_post.
          reflexivity.
          rewrite Htemp'.
          clear Htemp'.
          reflexivity.
          rewrite /cycle.
          do 2 (rewrite app_length).
          rewrite PeanoNat.Nat.add_assoc.          
          rewrite (Nat.add_comm (length (c_pre step base))).
          rewrite <-PeanoNat.Nat.add_assoc.
          apply plus_le_compat_l.
          simpl.
          lia.
        }
        rewrite <-Htemp.
        clear Htemp.
        reflexivity.
      }
      rewrite Hn'.
      rewrite /cycle.
      rewrite (app_assoc (c_pre step base)).
      iDestruct (big_sepL2_app_inv with "Hprog") as "(Uold & U)".
      simpl.
      by right.      
      iDestruct "U" as "(p_start & U)".
      iDestruct ((mov_word ((progpage ^+ 3) ^+ length (prog step))%f I1 R8) with "[Hpc Hacc Hr8 p_start]") as "J".
      3 : { rewrite ->Forall_forall in c. apply c. rewrite /cycle. rewrite elem_of_list_In. rewrite (app_assoc (c_pre step base)). do 2 (rewrite app_length).  simpl.
            do 3 right.
            assert (Htemp : (((progpage ^+ 1) ^+ 1) ^+ 1)%f = (progpage ^+ 3)%f).
            solve_finz.
            rewrite Htemp.
            clear Htemp.
            rewrite (finz_seq_decomposition (length (prog step) + 4) (progpage ^+ 3)%f (length (prog step))); [|lia].           
            apply in_or_app.
            right.
            rewrite <-elem_of_list_In.
            rewrite minus_plus.
            set_solver.
      }
      3 : { apply Hprpain. }
      3 : { iFrame. }
      auto.
      by rewrite decode_encode_instruction.
      iApply parwp_sswp.
      iApply "J".
      iModIntro.
      iIntros "(Hpc & Hinstr4 & Hacc & Hr8)".
      iApply parwp_sswp.
      iDestruct "U" as "(p_start & U)".
      iDestruct ((sub (((progpage ^+ 3) ^+ length (prog step)) ^+ 1)%f R5 R8) with "[Hpc Hacc Hr5 Hr8 p_start]") as "J".
      3 : { rewrite ->Forall_forall in c. apply c. rewrite /cycle. rewrite elem_of_list_In. rewrite (app_assoc (c_pre step base)). do 2 (rewrite app_length).  simpl.
            do 3 right.
            assert (Htemp : (((progpage ^+ 1) ^+ 1) ^+ 1)%f = (progpage ^+ 3)%f).
            solve_finz.
            rewrite Htemp.
            clear Htemp.
            rewrite (finz_seq_decomposition (length (prog step) + 4) (progpage ^+ 3)%f (length (prog step))); [|lia].           
            apply in_or_app.
            right.
            rewrite <-elem_of_list_In.
            rewrite minus_plus.
            set_solver.
      }
      3 : { apply Hprpain. }
      3 : { iFrame. }
      auto.
      by rewrite decode_encode_instruction.
      iApply "J".
      iModIntro.
      iIntros "(Hpc & Hinstr5 & Hr5 & Hr8 & Hacc)".
      iApply parwp_sswp.
      iDestruct "U" as "(p_start & U)".
      iDestruct ((cmp_reg ((((progpage ^+ 3) ^+ length (prog step)) ^+ 1) ^+ 1)%f R6 R5) with "[Hpc Hacc Hr5 Hr6 Hnz p_start]") as "J".
      3 : { rewrite ->Forall_forall in c. apply c. rewrite /cycle. rewrite elem_of_list_In. rewrite (app_assoc (c_pre step base)). do 2 (rewrite app_length).  simpl.
            do 3 right.
            assert (Htemp : (((progpage ^+ 1) ^+ 1) ^+ 1)%f = (progpage ^+ 3)%f).
            solve_finz.
            rewrite Htemp.
            clear Htemp.
            rewrite (finz_seq_decomposition (length (prog step) + 4) (progpage ^+ 3)%f (length (prog step))); [|lia].           
            apply in_or_app.
            right.
            rewrite <-elem_of_list_In.
            rewrite minus_plus.
            set_solver.
      }
      reflexivity.
      apply decode_encode_instruction.
      apply Hprpain.
      iFrame.
      iApply "J".
      iModIntro.
      iIntros "(Hpc & Hinstr6 & Hr6 & Hr5 & Hacc & Hnz)".
      assert (Htemp : (I0 <? step ^- I1)%f = false).
      {
        assert ((step ^- I1)%f = I0) as ->.
        rewrite /I0.
        simpl.
        solve_finz.
        solve_finz.     
      }
      rewrite Htemp.
      clear Htemp.
      assert (Htemp : (step ^- I1 <? I0)%f = false).
      {
        assert ((step ^- I1)%f = I0) as ->.
        rewrite /I0.
        simpl.
        solve_finz.
        solve_finz.
      }
      rewrite Htemp.
      clear Htemp.
      iApply parwp_sswp.
      iDestruct "U" as "(p_start & U)".      
      iDestruct ((bne (((((progpage ^+ 3) ^+ length (prog step)) ^+ 1) ^+ 1) ^+ 1)%f R7) with "[Hpc Hacc Hr7 Hnz p_start]") as "J".
      3 : { rewrite ->Forall_forall in c. apply c. rewrite /cycle. rewrite elem_of_list_In. rewrite (app_assoc (c_pre step base)). do 2 (rewrite app_length). simpl.
            do 3 right.
            assert (Htemp : (((progpage ^+ 1) ^+ 1) ^+ 1)%f = (progpage ^+ 3)%f).
            solve_finz.
            rewrite Htemp.
            clear Htemp.
            rewrite (finz_seq_decomposition (length (prog step) + 4) (progpage ^+ 3)%f (length (prog step))); [|lia].           
            apply in_or_app.
            right.
            rewrite <-elem_of_list_In.
            rewrite minus_plus.
            set_solver.
      }
      reflexivity.
      apply decode_encode_instruction.
      apply Hprpain.
      iFrame.
      iApply "J".
      iModIntro.
      iSimpl.
      iIntros "(Hpc & Hinstr7 & Hr7 & Hacc & Hnz)".
      iApply parwp_finish.
      iApply "HΦ".
      iFrame.
      assert (Htemp : (I0 ^+ 1)%f = step).
      rewrite /I0.
      simpl.
      solve_finz.
      rewrite Htemp. clear Htemp.
      iFrame.
      iDestruct (big_sepL2_app_inv with "Uold") as "(Hpre & Hprog)".
      simpl.
      by left.
      iFrame.
      rewrite /c_pre.
      iSimpl.
      iDestruct "Hpre" as "(Hinstr1 & Hinstr2 & Hinstr3 & _)".
      iFrame.
      iSplitR "Hnz";
        last (iExists W1; iFrame).
      assert (Htemp : ((((((progpage ^+ 3) ^+ length (prog step)) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f =
                      (progpage ^+ S (S (S (length (prog step ++ c_post)))))%f).
      admit.
      rewrite Htemp. clear Htemp.
      iFrame.
    - rename Hn into eq.
      rename Hseq into c.
      pose proof c as Hseq.
      apply seq_in_page_forall in c. 
      assert (Htemp : S n = Z.to_nat (step ^- 1)%f).
      solve_finz.
      assert (Htemp' : exists (im : Imm), (step ^- 1)%f = im).
      destruct step.
      eexists (I (w ^- 1)%f _).
      simpl.
      reflexivity.
      Unshelve.
      2 : {
        admit.
      }
      destruct Htemp' as [im Himeq].
      rewrite Himeq in Htemp.
      iIntros (Φ').
      iModIntro.
      iIntros "(HPstep & Hpc & [% Hr5] & [% Hr6] & [% Hr7] & [% Hr8] &[% Hnz] & Hacc & Hprog) HΦ".
      rewrite <-parwp_sswp.
      iDestruct "Hprog" as "(p_start & Hprog)". 
      iDestruct ((mov_word (of_pid progpage) step R5) with "[Hpc Hacc Hr5 p_start]") as "J".
      3 : { rewrite ->Forall_forall in c. apply c. set_solver. }
      3 : { apply Hprpain. }
      3 : { iFrame. }
      auto.
      by rewrite decode_encode_instruction.
      iApply "J".
      iModIntro.
      iIntros "(Hpc & Hinstr1 & Hacc & Hr5)".
      rewrite <-parwp_sswp.
      iDestruct "Hprog" as "(p_start & Hprog)".
      iDestruct ((mov_word (of_pid progpage ^+ 1)%f I0 R6) with "[Hpc Hacc Hr6 p_start]") as "J".
      3 : { rewrite ->Forall_forall in c. apply c. set_solver. }
      3 : { apply Hprpain. }
      3 : { iFrame. }
      auto.
      by rewrite decode_encode_instruction.
      iApply "J".
      iModIntro.
      iIntros "(Hpc & Hinstr2 & Hacc & Hr6)".
      rewrite <-parwp_sswp.
      iDestruct "Hprog" as "(p_start & Hprog)".
      iDestruct ((mov_word ((of_pid progpage ^+ 1) ^+ 1)%f base R7) with "[Hpc Hacc Hr7 p_start]") as "J".
      3 : { rewrite ->Forall_forall in c. apply c. set_solver. }
      3 : { apply Hprpain. }
      3 : { iFrame. }
      auto.
      by rewrite decode_encode_instruction.
      iApply "J".
      iModIntro.
      iIntros "(Hpc & Hinstr3 & Hacc & Hr7)".
      iDestruct ("Htriple" $! (S n) im I0 step _ with "") as "#HprogSpec".
      Unshelve.
      2 : {
        split.
        assumption.
        simpl.
        lia.
      }
      iSpecialize ("HprogSpec" $! (fun k => (⌜k = ExecI⌝
                                     ∗ P im
                                            ∗ PC @@ i ->r ((progpage ^+ 3) ^+ length (prog step))%f
                                            ∗ R5 @@ i ->r step
                                            ∗ R6 @@ i ->r I0
                                            ∗ R7 @@ i ->r (progpage ^+ 3)%f
                                            ∗ (∃ r : handle, R8 @@ i ->r r)
                                            ∗ (∃ nz, NZ @@ i ->r nz)             
                                            ∗ A@i:={q}[sacc]
                                            ∗ program' (cycle prog step base) progpage)%I) with "").
      iDestruct ("HprogSpec" with "[HPstep Hpc Hr5 Hr6 Hr7 Hr8 Hnz Hacc Hprog Hinstr1 Hinstr2 Hinstr3]") as "J".
      iFrame.
      rewrite Hbase.
      assert (Hn : (progpage ^+ 3)%f = (((progpage ^+ 1) ^+ 1) ^+ 1)%f).
      solve_finz.
      assert (of_imm step = (im ^+ 1)%f) as ->.
      admit.
      rewrite Hn.
      clear Hn.
      iFrame.
      iSplitL "Hr8".
      iExists r8.
      iFrame.
      iExists nz.
      iFrame.
      iApply parwp_parwp.
      iApply (parwp_strong_mono with "[J]").
      instantiate (1 := ⊤).
      set_solver.
      iApply "J".
      iModIntro.
      iIntros "(? & ? & ? & ? & ? & ? & ? & ? & ?)".
      iFrame.
      done.
      iIntros (k) "(%Heq & HP & Hpc & Hr5 & Hr6 & Hr7 & [%r8' Hr8] & [%nz' Hnz] & Hacc & Hprog)".
      subst k.
      iModIntro.
      assert (Hn : cycle prog step base = (c_pre step base ++ (prog step)) ++ c_post).
      auto.
      rewrite /program'.
      clear Htemp.
      assert (Hn' : finz.seq progpage (length (cycle prog step base)) = (finz.seq progpage 3 ++ finz.seq (progpage ^+ 3)%f (length (prog step))) ++ finz.seq ((progpage ^+ 3) ^+ (length (prog step)))%f 4).
      {
        assert (Htemp : (finz.seq progpage 3 ++ finz.seq (progpage ^+ 3)%f (length (prog step) + 3 - 3)) = finz.seq progpage (length (prog step) + 3)).
        {
          rewrite (finz_seq_decomposition ((length (prog step)) + 3) progpage 3).
          reflexivity.
          lia.
        }
        assert (Htemp' : length (prog step) = (length (prog step) + 3 - 3)).
        lia.
        rewrite <-Htemp' in Htemp.
        clear Htemp'.
        rewrite Htemp.
        clear Htemp.
        assert (Htemp : (finz.seq progpage (length (prog step) + 3) ++ finz.seq ((progpage ^+ 3) ^+ length (prog step))%f 4) = finz.seq progpage (length (cycle prog step base))).
        {
          rewrite (finz_seq_decomposition (length (cycle prog step base)) progpage (length (prog step) + 3)).
          f_equal.
          assert (Htemp' : ((progpage ^+ 3) ^+ length (prog step))%f = (progpage ^+ (length (prog step) + 3)%nat)%f).
          solve_finz.
          rewrite Htemp'.
          clear Htemp'.
          assert (Htemp' : (length (cycle prog step base) - (length (prog step) + 3)) = 4).
          rewrite /cycle.
          simpl.
          rewrite Nat.add_comm.
          simpl.
          rewrite app_length.
          rewrite minus_plus.
          rewrite /c_post.
          reflexivity.
          rewrite Htemp'.
          clear Htemp'.
          reflexivity.
          rewrite /cycle.
          do 2 (rewrite app_length).
          rewrite PeanoNat.Nat.add_assoc.          
          rewrite (Nat.add_comm (length (c_pre step base))).
          rewrite <-PeanoNat.Nat.add_assoc.
          apply plus_le_compat_l.
          simpl.
          lia.
        }
        rewrite <-Htemp.
        clear Htemp.
        reflexivity.
      }
      rewrite Hn'.
      rewrite /cycle.
      rewrite (app_assoc (c_pre step base)).
      iDestruct (big_sepL2_app_inv with "Hprog") as "(Uold & U)".
      simpl.
      by right.      
      iDestruct "U" as "(p_start & U)".
      iDestruct ((mov_word ((progpage ^+ 3) ^+ length (prog step))%f I1 R8) with "[Hpc Hacc Hr8 p_start]") as "J".
      3 : { rewrite ->Forall_forall in c. apply c. rewrite /cycle. rewrite elem_of_list_In. rewrite (app_assoc (c_pre step base)). do 2 (rewrite app_length).  simpl.
            do 3 right.
            assert (Htemp : (((progpage ^+ 1) ^+ 1) ^+ 1)%f = (progpage ^+ 3)%f).
            solve_finz.
            rewrite Htemp.
            clear Htemp.
            rewrite (finz_seq_decomposition (length (prog step) + 4) (progpage ^+ 3)%f (length (prog step))); [|lia].           
            apply in_or_app.
            right.
            rewrite <-elem_of_list_In.
            rewrite minus_plus.
            set_solver.
      }
      3 : { apply Hprpain. }
      3 : { iFrame. }
      auto.
      by rewrite decode_encode_instruction.
      iApply parwp_sswp.
      iApply "J".
      iModIntro.
      iIntros "(Hpc & Hinstr4 & Hacc & Hr8)".
      iApply parwp_sswp.
      iDestruct "U" as "(p_start & U)".
      iDestruct ((sub (((progpage ^+ 3) ^+ length (prog step)) ^+ 1)%f R5 R8) with "[Hpc Hacc Hr5 Hr8 p_start]") as "J".
      3 : { rewrite ->Forall_forall in c. apply c. rewrite /cycle. rewrite elem_of_list_In. rewrite (app_assoc (c_pre step base)). do 2 (rewrite app_length).  simpl.
            do 3 right.
            assert (Htemp : (((progpage ^+ 1) ^+ 1) ^+ 1)%f = (progpage ^+ 3)%f).
            solve_finz.
            rewrite Htemp.
            clear Htemp.
            rewrite (finz_seq_decomposition (length (prog step) + 4) (progpage ^+ 3)%f (length (prog step))); [|lia].           
            apply in_or_app.
            right.
            rewrite <-elem_of_list_In.
            rewrite minus_plus.
            set_solver.
      }
      3 : { apply Hprpain. }
      3 : { iFrame. }
      auto.
      by rewrite decode_encode_instruction.
      iApply "J".
      iModIntro.
      iIntros "(Hpc & Hinstr5 & Hr5 & Hr8 & Hacc)".
      iApply parwp_sswp.
      iDestruct "U" as "(p_start & U)".
      iDestruct ((cmp_reg ((((progpage ^+ 3) ^+ length (prog step)) ^+ 1) ^+ 1)%f R6 R5) with "[Hpc Hacc Hr5 Hr6 Hnz p_start]") as "J".
      3 : { rewrite ->Forall_forall in c. apply c. rewrite /cycle. rewrite elem_of_list_In. rewrite (app_assoc (c_pre step base)). do 2 (rewrite app_length).  simpl.
            do 3 right.
            assert (Htemp : (((progpage ^+ 1) ^+ 1) ^+ 1)%f = (progpage ^+ 3)%f).
            solve_finz.
            rewrite Htemp.
            clear Htemp.
            rewrite (finz_seq_decomposition (length (prog step) + 4) (progpage ^+ 3)%f (length (prog step))); [|lia].           
            apply in_or_app.
            right.
            rewrite <-elem_of_list_In.
            rewrite minus_plus.
            set_solver.
      }
      reflexivity.
      apply decode_encode_instruction.
      apply Hprpain.
      iFrame.
      iApply "J".
      iModIntro.
      iIntros "(Hpc & Hinstr6 & Hr6 & Hr5 & Hacc & Hnz)".
      assert ((I0 <? step ^- I1)%f = true) as ->.
      {
        admit.
      }
      iApply parwp_sswp.
      iDestruct "U" as "(p_start & U)".      
      iDestruct ((bne (((((progpage ^+ 3) ^+ length (prog step)) ^+ 1) ^+ 1) ^+ 1)%f R7) with "[Hpc Hacc Hr7 Hnz p_start]") as "J".
      3 : { rewrite ->Forall_forall in c. apply c. rewrite /cycle. rewrite elem_of_list_In. rewrite (app_assoc (c_pre step base)). do 2 (rewrite app_length). simpl.
            do 3 right.
            assert (Htemp : (((progpage ^+ 1) ^+ 1) ^+ 1)%f = (progpage ^+ 3)%f).
            solve_finz.
            rewrite Htemp.
            clear Htemp.
            rewrite (finz_seq_decomposition (length (prog step) + 4) (progpage ^+ 3)%f (length (prog step))); [|lia].           
            apply in_or_app.
            right.
            rewrite <-elem_of_list_In.
            rewrite minus_plus.
            set_solver.
      }
      reflexivity.
      apply decode_encode_instruction.
      apply Hprpain.
      iFrame.
      iApply "J".
      iModIntro.
      iSimpl.
      iIntros "(Hpc & Hinstr7 & Hr7 & Hacc & Hnz)".
      iApply ("IH" $! im with "[] [] [] [] [HP Hpc Hr5 Hr6 Hr7 Hr8 Hnz Hacc Uold Hinstr4 Hinstr5 Hinstr6 Hinstr7]").
      {
      iPureIntro.
      rewrite -Himeq.
        solve_finz.
      }
      {
        iPureIntro.
        rewrite (Hlen im step).
        assumption.
      }
      {
      done.
      }
      iModIntro.
      iIntros (v_ v'_ v''_ step0_) "%Hv_".
      iApply ("Htriple" $! v_ v'_ v''_ step0_).
      { iPureIntro.
        split;lia.
      }
      iFrame.
  Admitted.
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
