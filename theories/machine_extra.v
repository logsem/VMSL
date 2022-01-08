(* this file contains basic definitions and lemmas about registers and addresses *)
From Coq Require Import ssreflect Eqdep_dec ZArith.
From HypVeri Require Import machine monad stdpp_extra.
From stdpp Require Import fin_maps list countable fin vector gmap.

(* these definitions are frequently used *)
Program Definition W0 : Word := (finz.FinZ 0 _ _).
Solve Obligations with lia.

Program Definition W1 : Word := (finz.FinZ 1 _ _).
Solve Obligations with lia.

Program Definition W2 : Word := (finz.FinZ 2 _ _).
Solve Obligations with lia.

Program Definition W6 : Word := (finz.FinZ 6 _ _).
Solve Obligations with lia.

Program Definition I0 : Imm := (I W0 _).
Solve Obligations with try lia;solve_finz.

Program Definition I1 : Imm := (I W1 _).
Solve Obligations with try lia; solve_finz.

Program Definition I2 : Imm := (I W2 _).
Solve Obligations with try lia; solve_finz.

Program Definition I6 : Imm := (I W6 _).
Solve Obligations with try lia; solve_finz.

Program Definition R0 :reg_name := (R 0 _).
Solve Obligations with lia.

Program Definition R1 :reg_name := (R 1 _).
Solve Obligations with lia.

Program Definition R2 :reg_name := (R 2 _).
Solve Obligations with lia.

Program Definition R3 :reg_name := (R 3 _).
Solve Obligations with lia.

Program Definition R4 :reg_name := (R 4 _).
Solve Obligations with lia.

Program Definition R5 :reg_name := (R 5 _).
Solve Obligations with lia.

Program Definition R6 :reg_name := (R 6 _).
Solve Obligations with lia.

Program Definition R7 :reg_name := (R 7 _).
Solve Obligations with lia.

Program Definition R8 :reg_name := (R 8 _).
Solve Obligations with lia.

Program Definition R9 :reg_name := (R 9 _).
Solve Obligations with lia.

Program Definition R10 :reg_name := (R 10 _).
Solve Obligations with lia.

Definition page_of_W0: list Word:=
  map (λ _, W0) (seq 0 (Z.to_nat page_size)).

Definition pages_of_W0 (n:nat): list (list Word):=
  map (λ _, page_of_W0) (seq 0 n).

Lemma length_page_of_W0 : length (page_of_W0) = (Z.to_nat page_size).
Proof.
  rewrite /page_of_W0 map_length seq_length //.
Qed.

Lemma length_pages_of_W0 n : length (pages_of_W0 n) = n.
Proof.
  rewrite /pages_of_W0 map_length seq_length //.
Qed.

Lemma length_pages_of_W0_forall n : forall ws, ws ∈  (pages_of_W0 n) -> length ws = (Z.to_nat page_size).
Proof.
  intros.
  apply elem_of_list_In in H.
  rewrite /pages_of_W0 in H.
  apply in_map_iff in H.
  destruct H.
  destruct H.
  rewrite -H length_page_of_W0 //.
Qed.

Definition hvcf_to_tt hvcf:=
  match hvcf with
    | Donate => Some Donation
    | Lend => Some Lending
    | Share => Some Sharing
    | _ => None
  end.


Section list_of_vmids.
Context `{HypervisorConstants}.

(* list of all valid vmids, heavily used in state_interp *)
Definition list_of_vmids  := vec_to_list (fun_to_vec (λ v: fin vm_count, v)).

Lemma length_list_of_vmids : length list_of_vmids = vm_count.
Proof.
  rewrite /list_of_vmids.
  apply vec_to_list_length.
Qed.

Lemma in_list_of_vmids v: In v list_of_vmids.
Proof.
  apply elem_of_list_In.
  apply elem_of_vlookup.
  exists v.
  apply lookup_fun_to_vec.
Qed.

Lemma NoDup_list_of_vmids : NoDup list_of_vmids.
Proof.
  apply NoDup_alt.
  rewrite /list_of_vmids.
  intros ??? Hlk1 Hlk2.
  rewrite <-vlookup_lookup' in Hlk1.
  rewrite <-vlookup_lookup' in Hlk2.
  destruct Hlk1 as [Hlt1 Hlk1], Hlk2 as [Hlt2 Hlk2].
  rewrite lookup_fun_to_vec in Hlk1.
  rewrite lookup_fun_to_vec in Hlk2.
  rewrite -Hlk2 in Hlk1.
  rewrite <-(fin_to_nat_to_fin i vm_count Hlt1).
  rewrite <-(fin_to_nat_to_fin j vm_count Hlt2).
  rewrite Hlk1 //.
Qed.

Lemma lookup_list_of_vmids i (Hlt: i < vm_count):
  list_of_vmids !! i = Some (nat_to_fin Hlt).
Proof.
  unfold list_of_vmids.
  set (f := (nat_to_fin Hlt)).
  assert ( i = fin_to_nat f ).
  subst f.
  rewrite fin_to_nat_to_fin //.
  rewrite H0.
  apply -> (@vlookup_lookup VMID).
  apply lookup_fun_to_vec.
Qed.

End list_of_vmids.

(* an address is in the range of the page with PID p *)
Definition addr_in_page (a: Addr ) (p:PID):=
  ((of_pid p) <=? a)%f ∧ (a <=? ((of_pid p) ^+ (page_size -1 )))%f.

(* a sequence of addresses is in the range of the page with PID p *)
Definition seq_in_page (b :Addr) (l: nat) (p:PID) :=
  l > 0 ∧
  (* the starting address b is greater than the base addr of the page *)
  ((of_pid p) <=? b)%Z
  (* the ending address doesn't excess the boundary of address space *)
  ∧ is_Some (b + (Z.of_nat l - 1))%f
  (* the ending address is less than or equal to the last address of the page *)
  ∧ ((b ^+ (Z.of_nat l -1))%f <=? ((of_pid p) ^+ (page_size-1))%f)%Z.

(* we can always get the last address of a page *)
Lemma last_addr_in_bound (p:PID):
  is_Some ((of_pid p) + (page_size -1)%Z)%f.
Proof.
  destruct p.
  destruct z.
  simplify_eq /=.
  assert (Hy : exists y, (y * page_size = word_size)%Z).
  exists 2000%Z.
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
      apply Z.eqb_eq in align.
      apply Z.rem_divide in align;[|lia].
      destruct align.
      subst z.
      rewrite -H in finz_lt.
      apply Zmult_gt_0_lt_reg_r in finz_lt;[|lia].
      apply Zmult_gt_0_lt_reg_r in H';[|lia].
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
  lia.
  exfalso.
  apply n.
  lia.
Qed.

(* complementing lemmas for finz *)
Lemma incr_default_incr{fb} (f1 f2: finz.finz fb) z :
  (f1 + z)%f = Some f2 -> (f1 ^+ z)%f = f2.
Proof.
  intro.
  solve_finz.
Qed.

Lemma finz_incr_z_plus{b} (f1 f2 : (finz.finz b)) z :
  (f1 + z)%f = Some f2 <-> (f1 + z)%Z = (finz.to_z f2).
Proof.
  split;solve_finz.
Qed.

Lemma finz_incr_z_plus'{b} (f1 : (finz.finz b)) z :
  (f1 + z)%f = None <-> (b <= (f1 + z))%Z ∨ ((f1 +z) < 0)%Z .
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
  (is_Some (f + z1)%f) ->
  (is_Some (f + z2)%f) ->
  ((f ^+ z1)%f <= (f ^+ z2)%f)%Z ->
  (z1 <= z2)%Z.
Proof.
  intros H1 H2 Hlt.
  destruct H1 as [f1 H1].
  destruct H2 as [f2 H2].
  rewrite (incr_default_incr f f1 z1) in Hlt;eauto.
  rewrite (incr_default_incr f f2 z2) in Hlt;eauto.
  solve_finz.
Qed.

(*  relation between to_pid_aligned and addr_in_page *)
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
    apply Z.eqb_eq in align.
    apply Z.rem_divide in align;[|lia].
    destruct align.
    subst z.
    apply (fast_Zmult_comm page_size x0) in H.
    apply Z.quot_le_lower_bound in H;[|lia].
    assert (H0': (z0 < page_size* (x0+1) )%Z).
    lia.
    apply Z.quot_lt_upper_bound in H0';[|lia|lia].
    assert (Heq: (z0 `quot` page_size = x0)%Z).
    lia.
    rewrite Z.quot_div_nonneg in Heq;[lia|lia| ].
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

Lemma in_page_to_pid_aligned a: addr_in_page a (to_pid_aligned a).
Proof.
  unfold addr_in_page, to_pid_aligned.
  split.
  - simpl.
    unfold finz.leb.
    simpl.
    unfold Is_true.
    case_match;[done|].
    apply Z.leb_nle in Heqb.
    apply Heqb.
    apply Z.mul_div_le.
    lia.
  - unfold finz.leb.
    simpl.
    pose proof (last_addr_in_bound (to_pid_aligned a)) as Hplus.
    destruct Hplus as [? Hplus].
    unfold finz.incr_default.
    unfold to_pid_aligned in Hplus.
    rewrite Hplus.
    simpl in Hplus.
    destruct x.
    simpl.
    assert (1000 * a `div` 1000 + (1000 - 1) = z)%Z as <-.
    { solve_finz. }
    pose proof (Z.div_mod a 1000).
    rewrite ->H at 1.
    2: {lia. }
    unfold Is_true.
    case_match;[done|].
    apply Z.leb_nle in Heqb.
    apply Heqb.
    apply Zplus_le_compat_l.
    rewrite -Z.rem_mod_nonneg;[lia|lia|].
    assert (a `rem` 1000 < 1000)%Z.
    {
      pose proof (Z.rem_bound_pos_pos a 1000).
      apply H0;lia.
    }
    lia.
Qed.

Lemma to_pid_aligned_eq (p:PID) : to_pid_aligned p = p.
Proof.
  unfold to_pid_aligned.
  destruct p.
  apply of_pid_eq.
  simpl.
  destruct z.
  apply finz_to_z_eq.
  simplify_eq /=.
  unfold finz.leb in finz_lt.
  unfold finz.ltb in finz_nonneg.
  apply Z.ltb_lt in finz_lt.
  apply Z.leb_le in finz_nonneg.
  apply Z.eqb_eq in align.
  apply Z.rem_divide in align;[|lia].
  destruct align.
  subst z.
  rewrite Z_div_mult;[lia|].
  apply (fast_Zmult_comm page_size x).
  lia.
Qed.

Lemma finz_plus_assoc {fb} (a : finz fb) (n m : Z):
  (0 <= n)%Z ->
  (0 <= m)%Z ->
  ((a ^+ n) ^+ m)%f = (a ^+ (n + m)%Z)%f.
Proof. solve_finz. Qed.

(* complementing lemmas for finz.seq *)
Lemma finz_seq_notin2{b} (f f' : finz.finz b) n :
  (f' ^+ ((Z.of_nat n)-1) < f)%f -> f ∉ finz.seq f' n.
Proof.
  revert f f'. induction n; cbn.
  { intros. inversion 1. }
  { intros. apply not_elem_of_cons. split. solve_finz. eapply IHn. solve_finz. }
Qed.

Lemma finz_seq_in1{b} (f f' : finz.finz b) n :
  f ∈ finz.seq f' n ->  (f' <= f )%f.
Proof.
  revert f f'. induction n; cbn.
  { intros. inversion H. }
  { intros. apply  elem_of_cons in H.
    destruct H.
    solve_finz.
    eapply IHn in H. solve_finz. }
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

(* if the sequcence is included in a page,
then every address in the sequcence is in the page *)
Definition seq_in_page_forall1 (b: Addr) (l:nat) (p:PID) :
  seq_in_page b l p -> (∀ a, a ∈ (finz.seq b l) -> addr_in_page a p).
Proof.
  intros.
  (* apply Forall_forall. *)
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
    destruct H1.
    inversion H1.
    apply Z.leb_le in Hap.
    rewrite Hap //=.
    exfalso.
    assert (Hlt: (a < b )%f).
    solve_finz.
    apply (finz_seq_notin _ _ l)in Hlt.
    contradiction.
  - destruct l.
    inversion H.
    destruct H1.
    destruct H2.
    destruct H2.
    rewrite (incr_default_incr b x _ ) in H3;eauto.
    pose proof (last_addr_in_bound p).
    destruct H4.
    rewrite (incr_default_incr (of_pid p) x0 _ ) in H3;eauto.
    rewrite (incr_default_incr (of_pid p) x0 _ );eauto.
    apply  finz_incr_z_plus in H4.
    apply finz_seq_in2 in H0.
    apply  finz_incr_z_plus in H2.
    assert (H1': (b + (Z.of_nat l -1))%Z = (x-1)%Z ). by lia.
    assert(Hl : ((Z.of_nat (S l) - 1)%Z = (Z.of_nat l))%Z).  by lia.
    rewrite Hl  in H0 H1.
    rewrite -H4 in H3.
    rewrite -H2 in H3.
    unfold finz.leb.
    rewrite -H4.
    assert (H0': (a <= b + (Z.of_nat l))%Z).
    solve_finz.
    rewrite -H2 in H1'.
    destruct (decide (a <= (of_pid p) + (page_size - 1)))%Z.
    apply Z.leb_le in l0.
    solve_finz.
    exfalso.
    destruct ((b + Z.of_nat l <=? (of_pid p) + (page_size - 1))%Z) eqn:Heqn.
    apply Z.leb_le in Heqn.
    lia.
    rewrite Hl in H3.
    rewrite Heqn in H3.
    contradiction.
Qed.


Lemma finz_seq_lookup'{b} (f0 fi:(finz.finz b)) (i n : nat) :
  is_Some(f0 + (Z.of_nat n - 1))%f ->
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
      lia. rewrite -H0. solve_finz.
      assert (Hlt: i < n).
      {
        apply lookup_lt_Some in HSome.
        rewrite finz_seq_length in HSome.
        done.
      }
      solve_finz.
    }
    }
Qed.

Lemma finz_seq_cons {b} (f: finz.finz b) (l:nat) :
  (l > 0) ->
  (finz.seq f l) = f :: (finz.seq (f ^+ 1)%f (l-1)).
Proof.
  intro.
  destruct l;[lia|].
  cbn.
  repeat f_equal.
  lia.
Qed.

Definition seq_in_page_forall2 (b: Addr) (l:nat) (p:PID) :
  seq_in_page b l p -> (∀ a, a ∈ (finz.seq b l) -> to_pid_aligned a = p).
Proof.
  intros.
  apply to_pid_aligned_in_page.
  by apply (seq_in_page_forall1 b l p H a).
Qed.


(* Definition seq_in_page_forall2 (b: Addr) (l:nat) (p:PID) : *)
(*    l > 0 -> (∀ a, a ∈ (finz.seq b l) -> addr_in_page a p) -> seq_in_page b l p. *)
(* Proof. *)
(*   intros Hl Hforall. *)
(*   rewrite /seq_in_page. *)
(*   assert (b ∈ finz.seq b l) as Hb. *)
(*   rewrite finz_seq_cons;auto. *)
(*   set_solver. *)
(*   apply (Hforall b) in Hb. *)
(*   rewrite /addr_in_page in Hb. *)
(*   destruct Hb as [Hbge Hble]. *)
(*   split. *)
(*   solve_finz. *)
(*   assert ((b ^+ (Z.of_nat l -1 ))%f ∈ finz.seq b l) as Hbl. *)
(*   admit. *)
(*   pose proof Hbl as Hbl'. *)
(*   apply (Hforall (b ^+ (Z.of_nat l -1 ))%f) in Hbl. *)
(*   rewrite /addr_in_page in Hbl. *)
(*   destruct Hbl. *)
(*   split;[|solve_finz]. *)
(*   pose proof (last_addr_in_bound p). *)
(*   (* don't know how to prove it ... seems the def of addr_in_page need to be changed. *) *)
(*   Admitted. *)

(* fin_to_nat vec_to_list of_imm of_pid finz.to_z NonPropType.frame Is_true NonPropType.callee *)
Lemma seq_in_page_append1 (b:Word) (l l' : nat) p:
  (0 < l) -> (l < l') -> seq_in_page b l' p -> seq_in_page b l p.
Proof.
  intros Hlpos Hlt Hseq.
  rewrite /seq_in_page.
  split;[done|].
  rewrite /seq_in_page in Hseq.
  destruct Hseq as (Hl'pos & Hple & Hbl'isSome & Hbl'le).
  split; auto.
  split.
  solve_finz.
  assert (Hllt: ((Z.of_nat l - 1) < (Z.of_nat l' -1))%Z).
  solve_finz.
  assert (((b ^+ (Z.of_nat l - 1))%f < (b ^+ (Z.of_nat l' - 1)))%f).
  solve_finz.
  rewrite /Is_true in Hbl'le.
  case_match.
  apply Z.leb_le in Heqb0.
  rewrite /Is_true.
  case_match.
  done.
  solve_finz.
  done.
Qed.


Lemma seq_in_page_append2 (b :Word) (l o : nat) p:
  o<l ->
  is_Some (b + (Z.of_nat o))%f->
  seq_in_page b l p ->
  seq_in_page (b ^+ (Z.of_nat o))%f (l - o) p.
Proof.
  intros Holt Hb'in Hseq.
  rewrite /seq_in_page.
  rewrite /seq_in_page in Hseq.
  destruct Hseq as (Hlpos & Hple & HblisSome & Hblle).
  split.
  lia.
  split.
  rewrite /Is_true in Hple.
  case_match;[|done].
  apply Z.leb_le in Heqb0.
  rewrite /Is_true.
  case_match;[done|].
  solve_finz.
  split.
  solve_finz.
  rewrite /Is_true in Hblle.
  case_match;[|done].
  apply Z.leb_le in Heqb0.
  rewrite /Is_true.
  case_match;[done|].
  solve_finz.
Qed.

(* an alternative definition, not sure which is better *)
(* Definition addr_of_page' (p: PID) := map (λ off, ((of_pid p) + off)%f) (seqZ 0%Z page_size). *)

Lemma finz_seq_lookup0{b} n (f : finz.finz b) x :
   is_Some(f + 1)%f ->
   finz.seq f n !! x = Some f -> x=0.
Proof.
  revert f. destruct n; cbn.
  { intros. inversion H0. }
  { intros.
    destruct (decide (x=0)).
    done.
    rewrite lookup_cons_ne_0 in H0;eauto.
    apply elem_of_list_lookup_2 in H0.
    pose proof (finz_seq_notin f (f ^+ 1)%f n).
    assert ( (f < f ^+ 1)%f) as Hlt.
    solve_finz.
    apply H1 in Hlt.
    done.
  }
Qed.


Lemma finz_seq_NoDup'{b} (f : finz.finz b) (n : nat) :
  is_Some (f + (Z.of_nat (n-1)))%f →
  NoDup (finz.seq f n).
Proof using.
  revert f. induction n; intros f Hfn.
  { apply NoDup_nil_2. }
  { cbn.
    destruct n; intros;simpl.
    { apply NoDup_singleton. }
    { apply NoDup_cons_2.
      apply not_elem_of_cons.
      split.
      solve_finz.
      apply finz_seq_notin.
      solve_finz.
      eapply IHn.
      solve_finz. } }
Qed.

Lemma finz_seq_in_inv{b} (f f' : finz.finz b) n:
    (f' <= f )%f -> (f <= f' ^+ (Z.of_nat n))%f ->
    f ∈ finz.seq f' (n+1).
 Proof.
   revert f f'. induction n; cbn.
   { intros.
     assert (f = f')%f as ->.
     {
       solve_finz.
     }
     set_solver +.
   }
   {
     intros.
     destruct (decide (f = f')).
     {
       rewrite e.
       apply elem_of_list_here.
     }
     apply elem_of_list_further.
     apply IHn.
     solve_finz.
     solve_finz.
   }
 Qed.


 Definition addr_of_page (p: PID) := (finz.seq (of_pid p) (Z.to_nat page_size)).

 Lemma elem_of_addr_of_page_tpa (a:Addr) : a ∈ (addr_of_page (tpa a)).
 Proof.
   rewrite /addr_of_page.
   pose proof (in_page_to_pid_aligned a) as [H1 H2].
   assert ((Z.to_nat 1000) = (Z.to_nat 999) + 1) as ->.
   { done. }
   apply finz_seq_in_inv.
   {
     rewrite /Is_true in H1.
     case_match;last done.
     solve_finz.
   }
   {
     rewrite /Is_true in H2.
     case_match;last done.
     solve_finz.
   }
 Qed.

Lemma elem_of_addr_of_page_of_pid (a : Addr) : of_pid (tpa a) ∈ addr_of_page (tpa a).
Proof.
  unfold addr_of_page.
  unfold tpa.
  rewrite finz_seq_cons; first lia.
  apply elem_of_list_here.            
Qed.

Lemma elem_of_addr_of_page_iff (a:Addr) (p : PID) : a ∈ (addr_of_page p) <-> p = (tpa a).
Proof.
  split.
  {
     rewrite /addr_of_page.
     intro Hin.
     symmetry.
     apply to_pid_aligned_in_page.
     rewrite /addr_in_page.
     split.
     apply finz_seq_in1 in Hin.
     rewrite Is_true_true.
     solve_finz.
     apply finz_seq_in2 in Hin.
     rewrite Is_true_true.
     solve_finz.
  }
  intros ->.
  apply elem_of_addr_of_page_tpa.
Qed.

Lemma addr_of_page_not_empty_exists (p : PID) : ∃a, a ∈ addr_of_page p.
Proof.
  exists (of_pid p).
  apply elem_of_addr_of_page_iff.
  rewrite to_pid_aligned_eq //.
Qed.

Lemma addr_of_page_not_empty_set (p : PID) : list_to_set (addr_of_page p) ≠ (∅: gset _) .
Proof.
  pose proof (addr_of_page_not_empty_exists p) as H.
  destruct H as [a H].
  intro Heq.
  rewrite -(elem_of_list_to_set (C:= gset Addr) a (addr_of_page p)) in H.
  rewrite Heq in H.
  set_solver + H.
Qed.

Lemma addr_of_page_NoDup (p:PID) : NoDup (addr_of_page p).
Proof.
  rewrite /addr_of_page.
  apply finz_seq_NoDup'.
  apply last_addr_in_bound.
Qed.

Lemma addr_of_page_disj (p1 p2 :PID) :
  p1 ≠ p2 ->
  ((list_to_set (addr_of_page p1)) : gset Addr) ## list_to_set (addr_of_page p2).
Proof.
  intro Hneq.
  apply elem_of_disjoint.
  intros a.
  rewrite !elem_of_list_to_set.
  rewrite !elem_of_addr_of_page_iff.
  intros -> Hin2.
  done.
Qed.

Lemma pid_lt_lt (p1 p2:PID):
  ((of_pid p1) < (of_pid p2))%f -> (p1 ^+ (page_size - 1) < p2)%f.
Proof.
  intro.
  pose proof (last_addr_in_bound p1).
  destruct H0.
  rewrite (incr_default_incr (of_pid p1) x);eauto.
  destruct p1,p2.
  destruct z,z0.
  simpl in *.
  apply Z.eqb_eq in align, align0.
  apply Z.rem_divide in align,align0;try lia.
  destruct align, align0.
  assert ( z < z0 )%Z.
  solve_finz.
  subst z.
  subst z0.
  destruct x.
  simpl in H0.
  assert (z = x0 * 1000 + 1000 -1)%Z.
  solve_finz.
  subst z.
  solve_finz.
Qed.

Lemma finz_seq_nonempty_length {b} (x f :finz.finz b) (l:nat):
  x ∈ finz.seq f l-> l >0.
Proof.
  intros.
  destruct l.
  inversion H.
  lia.
Qed.

Lemma addr_in_notin (p1 p2 : PID) (x: Addr) (l1 : nat) :
  ((Z.of_nat l1) < page_size)%Z ->
  p1 ≠ p2 ->
  x ∈ finz.seq (of_pid p1) l1 ->
  ∀ l2 , ((Z.of_nat l2) < page_size)%Z -> x ∉ finz.seq (of_pid p2) l2.
Proof.
  intros.
  pose proof H1.
  apply finz_seq_nonempty_length in H3.
  destruct (decide ((of_pid p1) <= (of_pid p2))%f).
  - assert ( (of_pid p1) ≠ (of_pid p2))%f.
    { intro. apply H0. by apply of_pid_eq. }
    assert ( (of_pid p1) < (of_pid p2))%f. solve_finz.
    apply  finz_seq_notin.
    apply pid_lt_lt in H5.
    apply finz_seq_in2 in H1.
    solve_finz.
  - destruct l2.
    apply not_elem_of_nil.
    assert ( (of_pid p2) < (of_pid p1))%f. solve_finz.
    apply  finz_seq_notin2.
    apply finz_seq_in1 in H1.
    apply pid_lt_lt in H4.
    solve_finz.
Qed.

Lemma finz_seq_zip_page (p: PID) (ws: list Word):
  (length ws) <= (Z.to_nat page_size) ->
  ((zip (finz.seq (of_pid p) (length ws)) ws) = (zip (finz.seq (of_pid p) (Z.to_nat page_size)) ws)).
Proof.
  intro Hlen.
  rewrite <-(zip_fst_snd (zip (finz.seq _ (Z.to_nat page_size)) ws)).
  rewrite !snd_zip; auto.
  f_equal.
  generalize dependent (of_pid p).
  induction ws; first done.
  cbn.
  destruct (Z.to_nat page_size) eqn:Heqn; first done.
  cbn.
  intros f.
  f_equal.
  assert (Hn : n = ((Z.to_nat page_size) - 1)).
  lia.
  subst n.
  rewrite (@zip_length_le _ _ ws
                          (finz.seq (f ^+ 1)%f ((Z.to_nat page_size) -1))
                          (finz.seq (f ^+ 1)%f (Z.to_nat page_size))
                          [(f ^+ page_size)%f]).
  simpl in Hlen.
  rewrite finz_seq_length.
  lia.
  rewrite (finz_seq_decomposition (Z.to_nat page_size) _ ((Z.to_nat page_size) -1)).
  lia.
  f_equal.
  simpl.
  f_equal.
  rewrite Unnamed_thm12.
  lia.
  lia.
  rewrite Z.add_comm.
  assert (H999_1 : Z.add (page_size - 1)%Z 1%Z = 1000%Z).
  reflexivity.
  rewrite H999_1.
  reflexivity.
  rewrite IHws.
  simpl in Hlen.
  lia.
  rewrite -Heqn.
  reflexivity.
Qed.
