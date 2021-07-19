From Coq Require Import ssreflect Eqdep_dec ZArith.
From HypVeri Require Import machine monad.
From stdpp Require Import fin_maps list countable fin vector.

Ltac solveWordSize :=
  pose proof word_size;
  unfold word_size;
  lia.

Ltac solveRegCount :=
  pose proof reg_count;
  unfold reg_count;
  lia.

Program Definition W0 : Word := (finz.FinZ 0 _ _).
Solve Obligations with solveWordSize.

Program Definition W1 : Word := (finz.FinZ 1 _ _).
Solve Obligations with solveWordSize.

Program Definition W2 : Word := (finz.FinZ 2 _ _).
Solve Obligations with solveWordSize.

Program Definition R0 :reg_name := (R 0 _).
Solve Obligations with solveRegCount.

Program Definition R1 :reg_name := (R 1 _).
Solve Obligations with solveRegCount.

Program Definition R2 :reg_name := (R 2 _).
Solve Obligations with solveRegCount.


  (** predicates and lemmas for checking if addresses/regions are in a page *)
  Definition addr_in_page (a: Addr ) (p:PID):=
    ((of_pid p) <=? a)%f ∧ (a <=? ((of_pid p) ^+ (page_size -1 )))%f.

  Definition seq_in_page (b :Addr) (l: nat) (p:PID) :=
    ((of_pid p) <=? b)%Z ∧ is_Some (b + (Z.of_nat l))%f ∧ ((b ^+ (Z.of_nat l))%f <=? ((of_pid p) ^+ (page_size-1))%f)%Z.

  Lemma last_addr_in_bound (p:PID):
    is_Some ((of_pid p) + (page_size -1)%Z)%f.
    Proof.
      destruct p.
      destruct z.
      simplify_eq /=.
      assert (Hy : exists y, (y * page_size = word_size)%Z).
      exists 2000%Z.
      unfold page_size, word_size.
      lia.
      destruct Hy.
      assert (Hlt: (z + page_size -1 < word_size)%Z).
      {
       apply Z.ltb_lt in finz_lt.
       apply Z.leb_le in finz_nonneg.
       assert (Hlt': (z  < word_size - page_size + 1 )%Z).
       {
         destruct (decide (z  < word_size - page_size + 1)%Z).
         lia.
         assert(H': ( (x -1 ) * page_size < z )%Z).
         lia.
         apply Z.rem_divide in align;[|unfold page_size;lia].
         destruct align.
         subst z.
         rewrite -H in finz_lt.
         apply Zmult_gt_0_lt_reg_r in finz_lt;[|unfold page_size;lia].
         apply Zmult_gt_0_lt_reg_r in H';[|unfold page_size;lia].
         lia.
       }
       lia.
       }
      unfold finz.incr.
      simpl.
      destruct (Z_lt_dec (z + (page_size - 1))%Z word_size).
      destruct (Z_le_dec 0%Z (z + (page_size - 1))%Z).
      eauto.
      exfalso.
      apply n.
      unfold page_size.
      lia.
      exfalso.
      apply n.
      lia.
  Qed.

    Lemma last_addr_in_bound' p f : ((of_pid p) + (page_size -1)%Z)%f = Some f ->
                                    ((of_pid p) ^+ (page_size -1)%Z)%f = f.
      Proof.
        intro.
        unfold finz.incr_default.
        by rewrite H.
      Qed.


  Lemma to_pid_aligned_in_page (a:Addr) (p:PID) :
    addr_in_page a p -> (to_pid_aligned a ) = p.
    Proof.
      intro.
      unfold to_pid_aligned.
      unfold addr_in_page in H.
      destruct H.
      pose proof (last_addr_in_bound p).
      destruct H1.
      rewrite (last_addr_in_bound' p x) in H0;eauto.
      destruct p.
      destruct z.
      f_equal /=.
      assert (Heq : z = (page_size * (a / page_size))%Z).
      {
        destruct a.
        simplify_eq /=.
        destruct (decide (z = z0 )%Z);eauto.
        rewrite -e.
         apply Z.rem_mod_eq_0 in align.
          apply Z_div_exact_2.
          unfold page_size;lia.
          lia.
          unfold page_size;lia.

        unfold finz.leb in H.
        simpl in H.
        unfold finz.ltb in H0.
        simpl in H0.
        apply Is_true_eq_true in H, H0.
        apply Z.leb_le in H.
        assert (Heq : (z < z0)%Z).
        {
          lia.
        }
        apply Z.leb_le in H0.
        simpl in H0 ,H1 .
        apply Z.rem_divide in align;[|unfold page_size;lia].
        admit.
      }
      subst z.
      remember (machine.to_pid_aligned_obligation_3 a) as Ha'.
      simpl in Ha'.
      assert (Heqiv : Ha' = align).
      apply eq_proofs_unicity; decide equality; decide equality.
      rewrite Heqiv.
      repeat f_equal /=.
      remember (machine.to_pid_aligned_obligation_1 a) as Ha''.
      simpl in  Ha''.
      remember (machine.to_pid_aligned_obligation_2 a) as Ha'''.
      simpl in  Ha'''.
      assert (Heqiv' : Ha'' = finz_lt).
      apply eq_proofs_unicity; decide equality; decide equality.
      rewrite Heqiv'.
      assert (Heqiv'' : Ha''' = finz_nonneg).
      apply eq_proofs_unicity; decide equality; decide equality.
      rewrite Heqiv''.
      done.
Qed.
