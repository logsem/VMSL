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

  Lemma incr_default_incr{fb} (f1 f2: finz.finz fb) z : (f1 + z)%f = Some f2 ->
                                    (f1 ^+ z)%f = f2.
  Proof.
    intro.
    solve_finz.
  Qed.

  Lemma finz_incr_z_plus{b} (f1 f2 : (finz.finz b)) z : (f1 + z)%f = Some f2 <->
                                                        (f1 + z)%Z = (finz.to_z f2).
  Proof.
    split;solve_finz.
  Qed.

  Lemma finz_incr_z_plus'{b} (f1 : (finz.finz b)) z : (f1 + z)%f = None <->
                                                      (b <= (f1 + z))%Z ∨ ((f1 +z) < 0)%Z .
  Proof.
    split; solve_finz.
  Qed.

  Lemma finz_plus_Z_lt{b} (f: (finz.finz b)) z1 z2:
    (is_Some (f + z1)%f) -> (is_Some (f + z2)%f) ->
  ((f ^+ z1)%f < (f ^+ z2)%f)%Z -> (z1 < z2)%Z.
    Proof.
      intros H1 H2 Hlt.
      destruct H1 as [f1 H1].
      destruct H2 as [f2 H2].
      rewrite (incr_default_incr f f1 z1) in Hlt;eauto.
      rewrite (incr_default_incr f f2 z2) in Hlt;eauto.
      solve_finz.
    Qed.

  Lemma finz_plus_Z_le{b} (f: (finz.finz b)) z1 z2:
    (is_Some (f + z1)%f) -> (is_Some (f + z2)%f) ->
  ((f ^+ z1)%f <= (f ^+ z2)%f)%Z -> (z1 <= z2)%Z.
    Proof.
      intros H1 H2 Hlt.
      destruct H1 as [f1 H1].
      destruct H2 as [f2 H2].
      rewrite (incr_default_incr f f1 z1) in Hlt;eauto.
      rewrite (incr_default_incr f f2 z2) in Hlt;eauto.
      solve_finz.
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
      rewrite (incr_default_incr (of_pid p) x (page_size -1)%Z) in H0;eauto.
      destruct p.
      destruct z.
      f_equal /=.
      assert (Heq : z = (page_size * (a / page_size))%Z).
      {
        destruct a.
        simplify_eq /=.
        unfold finz.leb in H.
        simpl in H.
        unfold finz.ltb in H0.
        simpl in H0.
        apply Is_true_eq_true in H, H0.
        apply Z.leb_le in H.
        apply Z.leb_le in H0.
        apply finz_incr_z_plus in H1.
        simpl in H1.
        rewrite -H1 in H0.
        simpl in H0.
        apply Z.rem_divide in align;[|unfold page_size;lia].
        destruct align.
        subst z.
       apply (fast_Zmult_comm page_size x0) in H.
        apply Z.quot_le_lower_bound in H;[|unfold page_size;lia].
       assert (H0': (z0 < page_size* (x0+1) )%Z).
       lia.
       apply Z.quot_lt_upper_bound in H0';[|lia|unfold page_size;lia].
       assert (Heq: (z0 `quot` page_size = x0)%Z).
       lia.
       rewrite Z.quot_div_nonneg in Heq;[lia|unfold page_size;lia| ].
       solve_finz.
      }
      subst z.
      remember (machine.to_pid_aligned_obligation_3 a) as Ha'.
      simpl in Ha'.
      assert (Heqiv : Ha' = align).
      apply eq_proofs_unicity; decide equality; decide equality.
      rewrite Heqiv.
      remember (machine.to_pid_aligned_obligation_1 a) as Ha''.
      simpl in  Ha''.
      remember (machine.to_pid_aligned_obligation_2 a) as Ha'''.
      simpl in  Ha'''.
      assert (Heqiv' : Ha'' = finz_lt).
      apply eq_proofs_unicity; decide equality; decide equality.
      rewrite Heqiv'.
      assert (Heqiv'' : Ha''' = finz_nonneg).
      apply eq_proofs_unicity; decide equality; decide equality.
      rewrite Heqiv'' // .
Qed.

    Lemma finz_seq_notin2{b} (f f' : finz.finz b) n :
      (f' ^+ ((Z.of_nat n)-1) < f)%f -> f ∉ finz.seq f' n.
    Proof.
      revert f f'. induction n; cbn.
      { intros. inversion 1. }
      { intros. apply not_elem_of_cons. split. solve_finz. eapply IHn. solve_finz. }
     Qed.

    Lemma finz_seq_in2{b} (f f' : finz.finz b) n :
     f ∈ finz.seq f' n ->  (f <= f' ^+ ((Z.of_nat n)-1))%f.
    Proof.
      revert f f'. induction n; cbn.
      { intros. inversion H. }
      { intros. apply  elem_of_cons in H.
        destruct H.
        solve_finz.
        eapply IHn in H. solve_finz. }
     Qed.

    Definition seq_in_page_forall (b: Addr) (l:nat) (p:PID) :
    seq_in_page b l p -> Forall  (λ a, addr_in_page a p) (finz.seq b l).
    Proof.
      intros.
      apply Forall_forall.
      intros a H0.
      unfold addr_in_page.
      destruct H.
      split.
      - unfold finz.leb.
        unfold Is_true.
        destruct (decide (b <= a)%f).
        unfold Is_true in H.
        assert (Hap: ((of_pid p) <= a)%Z).
        destruct ((((of_pid p) <=? b))%Z) eqn:Heqn.
        apply Z.leb_le in Heqn.
        solve_finz.
        congruence.
        apply Z.leb_le in Hap.
        rewrite Hap //=.
        exfalso.
        assert (Hlt: (a < b )%f).
        solve_finz.
        apply (finz_seq_notin _ _ _ l )in Hlt.
        contradiction.
      - destruct l.
        inversion H0.
        destruct H1.
        destruct H1.
        rewrite (incr_default_incr b x _ ) in H2;eauto.
        pose proof (last_addr_in_bound p).
        destruct H3.
        rewrite (incr_default_incr (of_pid p) x0 _ ) in H2;eauto.
        rewrite (incr_default_incr (of_pid p) x0 _ );eauto.
        apply  finz_incr_z_plus in H3.
        apply finz_seq_in2 in H0.
        apply  finz_incr_z_plus in H1.
        assert (H1': (b + (Z.of_nat l))%Z = (x-1)%Z ). by lia.
        assert(Hl : ((Z.of_nat (S l) - 1)%Z = (Z.of_nat l))%Z).  by lia.
        rewrite Hl  in H0 H1.
        rewrite -H3 in H2.
        rewrite -H1 in H2.
        unfold finz.leb.
        rewrite -H3.
        assert (H0': (a <= b + (Z.of_nat l))%Z).
        solve_finz.
        rewrite -H1 in H1'.
        destruct (decide (a <= (of_pid p) + (page_size - 1)))%Z.
        apply Z.leb_le in l0.
        solve_finz.
        exfalso.
        destruct ((b + Z.of_nat (S l) <=? (of_pid p) + (page_size - 1))%Z) eqn:Heqn.
        apply Z.leb_le in Heqn.
        lia.
        contradiction.
Qed.


Lemma finz_seq_lookup'{b} (f0 fi:(finz.finz b)) (i n : nat) :
   is_Some(f0 + (Z.of_nat n))%f ->
   finz.seq f0 n !! i = Some fi ->
  i < n ∧ (f0 + (Z.of_nat i))%f = Some fi.
Proof using.
  revert i fi f0. induction n.
  { intros. done. }
  { intros i fi f0 Hsafe HSome.
    destruct i as [|i].
    { split. solve_finz. simpl in HSome. inversion HSome. solve_finz. }
    { simpl in HSome.
      apply IHn in HSome.
      destruct HSome.
      split.
      lia. rewrite -H0. solve_finz. solve_finz. } }
Qed.
