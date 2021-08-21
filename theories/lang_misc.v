(* This file contains some lemmas only about functions in the operational semantics (lang.v) *)
From HypVeri Require Import reg_addr lang.
From stdpp Require Import list.
Require Import ssreflect.

Lemma list_pid_to_addr_NoDup (ps:list PID):
  NoDup ps ->
  NoDup (list_pid_to_addr ps).
Proof.
  intro Hnd.
  rewrite /list_pid_to_addr.
  induction ps.
  - simpl. by apply NoDup_nil.
  - cbn.  apply  NoDup_app.
    split.
    { apply finz_seq_NoDup'. apply last_addr_in_bound. }
    split.
    { intros. apply NoDup_cons in Hnd. destruct Hnd as [ Hnotin Hnd].
      pose proof (finz_seq_in2 _ _ _ H) as Halt.
      pose proof (finz_seq_in1 _ _ _ H) as Hagt.
      clear IHps.
      induction ps.
      cbn.
      apply not_elem_of_nil.
      cbn.
      apply not_elem_of_app.
      split.
      { intro.
        pose proof (finz_seq_in2 _ _ _ H0) as Ha0lt.
        pose proof (finz_seq_in1 _ _ _ H0) as Ha0gt.
        assert (Hne: a ≠ a0).
        apply not_elem_of_cons in Hnotin.
        destruct Hnotin;eauto.
        destruct (decide ((of_pid a)<= (of_pid a0))%f).
        assert (Hlt: ((of_pid a)< (of_pid a0))%f).
        assert (Hne': ((of_pid a) ≠ (of_pid a0))%f).
        intro.
        apply Hne.
        apply of_pid_eq;eauto.
        solve_finz.
        clear l Hne.
        assert ((a ^+ (Z.of_nat (Z.to_nat page_size) - 1)) < a0 )%f.
        apply pid_lt_lt;eauto.
        solve_finz.
        assert (a0<a)%f.
        solve_finz.
        assert ((a0 ^+ (Z.of_nat (Z.to_nat page_size) - 1)) < a )%f.
        apply pid_lt_lt;eauto.
        solve_finz.
      }
      apply IHps.
      { apply not_elem_of_cons in Hnotin;destruct Hnotin;done. }
      { apply NoDup_cons in Hnd;destruct Hnd;done. }
    }
    apply IHps.
    apply NoDup_cons in Hnd;destruct Hnd;done.
Qed.

Lemma flat_list_list_word_length_eq wss wss':
  length wss = length wss'->
  (forall ws, ws ∈ wss -> length ws = (Z.to_nat page_size)) ->
  (forall ws', ws' ∈ wss' -> length ws' = (Z.to_nat page_size)) ->
  length (flat_list_list_word wss) = length (flat_list_list_word wss').
Proof.
  intro Heqlen.
  rewrite /flat_list_list_word.
  generalize dependent wss'.
  induction wss;destruct wss';cbn;
  intros Heqlen' Hws Hws'; try inversion Heqle;eauto.
  inversion Heqlen'.
  inversion Heqlen'.
  rewrite !app_length.
  rewrite (IHwss wss');eauto.
  {
    intros ws Hin.
    apply Hws.
    apply elem_of_cons;right;done.
  }
  {
    intros ws' Hin.
    apply Hws'.
    apply elem_of_cons;right;done.
  }
  f_equal.
  rewrite (Hws a).
  apply elem_of_cons;left;done.
  rewrite (Hws' l) //.
  apply elem_of_cons;left;done.
Qed.
