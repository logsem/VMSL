From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base machine_extra.
From HypVeri.algebra Require Import base mem reg pagetable mailbox trans base_extra.
From HypVeri.lang Require Import lang_extra reg_extra mem_extra pagetable_extra trans_extra.

Section mem_send.

Context `{hypparams: HypervisorParameters}.
Context `{vmG: !gen_VMG Σ}.

Lemma size_singleton_le `{Countable K}  (i:K) (s: gset K):
  i ∈ s -> size s ≤ 1 -> s = {[i]}.
Proof.
  intros Hin Hle.
  assert (size s = 1) as Hsize.
  {
    assert (size s ≠ 0).
    intro.
    destruct (decide (s = ∅)).
    set_solver.
    apply size_empty_inv in H1.
    set_solver + H1 n.
    lia.
  }
  assert (s = {[i]}) as ->.
  {
    rewrite set_eq.
    intro. split. intros.
    apply (size_singleton_inv _ i x) in Hsize.
    subst x. set_solver +.
    done. done. intro.
    rewrite elem_of_singleton in H1.
    subst x. done.
  }
  done.
Qed.

Lemma parse_transaction_descriptor_tx mem_tx mem p_tx len tran:
 parse_transaction_descriptor mem_tx (of_pid p_tx) len = Some tran ->
 map_Forall (λ k v, mem !! k = Some v) mem_tx ->
 parse_transaction_descriptor mem (of_pid p_tx) len = Some tran.
Proof.
  rewrite /parse_transaction_descriptor.
  rewrite /parse_list_of_Word.
  intros Hparse Hforall.
  destruct (sequence_a (map (λ v : Addr, mem_tx !! v) (finz.seq p_tx len))) eqn:Heqn;last done.
  assert (sequence_a (map (λ v : Addr, mem !! v) (finz.seq p_tx len)) = Some l) as ->.
  {
    apply (sequence_a_map_subseteq _ _ _ mem_tx). done.
    rewrite map_subseteq_spec.
    intros.
    apply Hforall.
    done.
  }
  done.
Qed.

Lemma parse_list_of_Word_length mem p len l:
  parse_list_of_Word mem p len = Some l ->
length l = len.
Proof.
  rewrite /parse_list_of_Word.
  revert p l.
  induction len.
  -  intros p l H0. simpl in H0.
     rewrite /monad.List.sequence_a_list /= in H0.
     inversion H0.
     done.
  -  intros p l H0. simpl in H0.
     destruct (mem !! p).
     {
     rewrite /monad.List.sequence_a_list /= in H0.
     destruct (list.foldr _) eqn:Heqn.
     inversion H0.
     simpl.
     rewrite (IHlen (p ^+ 1)%f) //.
     rewrite /sequence_a /= /monad.List.sequence_a_list /=.
     done.
     }
     rewrite /monad.List.sequence_a_list /= in H0.
     done.
Qed.
Lemma parse_list_of_pids_length l f3 l0:
  parse_list_of_pids l f3 = Some l0->
  length l = length l0.
Proof.
  revert l0 f3.
  induction l.
  - intros l0 f3 Hparse.
    rewrite /parse_list_of_pids /=in Hparse.
    destruct (Option.bool_check_option (Z.to_nat f3 =? 0)%nat).
    2: done.
    rewrite /monad.List.sequence_a_list /= in Hparse.
    inversion Hparse.
    done.
  - intros l0 f3 Hparse.
    rewrite /parse_list_of_pids /=in Hparse.
    destruct (Option.bool_check_option (Z.to_nat f3 =? S (length l))%nat) eqn:Heq_f3.
    2: done.
    rewrite /monad.List.sequence_a_list /= in Hparse.
    destruct (to_pid a).
    2: done.
    destruct ( list.foldr
                 (λ (val : option PID) (acc : option (list PID)),
                   match match val with
                         | Some x' => Some (cons x')
                         | None => None
                         end with
                   | Some f' => match acc with
                                | Some a' => Some (f' a')
                                | None => None
                                end
                   | None => None
                   end)) eqn:Heq_fold.
    inversion Hparse.
    simpl.
    erewrite (IHl l1 (f3 ^- 1)%f).
    done.
    rewrite /parse_list_of_pids.
    destruct ((Option.bool_check_option (Z.to_nat (f3 ^- 1)%f =? length l)%nat)) eqn:Heq_f3'.
    simpl.
    rewrite /monad.List.sequence_a_list /=.
    rewrite Heq_fold //.
    assert ((Z.to_nat (f3 ^- 1)%f =? length l)%nat = true).
    {
      rewrite Nat.eqb_eq.
      destruct ((Z.to_nat f3 =? S (length l))%nat) eqn: Heq_f3''.
      2: { simpl in Heq_f3. done. }
      rewrite Nat.eqb_eq in Heq_f3''.
      solve_finz.
    }
    rewrite H0 in Heq_f3'.
    done.
    done.
Qed.

Lemma size_list_to_set' `{Countable A} (l: list A):
  size (list_to_set (C:= gset _) l) <= length l.
Proof.
  unfold size, set_size. simpl.
  induction l.
  simpl.
  rewrite elements_empty.
  rewrite nil_length.
  lia.
  simpl.
  destruct (decide (a ∈(list_to_set (C:= gset _) l))).
  {
    assert ({[a]} ∪ list_to_set l = list_to_set (C:= gset _) l) as ->.
    set_solver +e.
    lia.
  }
  rewrite elements_union_singleton //.
  simpl.
  lia.
Qed.

Lemma parse_transaction_descriptor_length mem p_tx len tran:
 parse_transaction_descriptor mem (of_pid p_tx) len = Some tran ->
 (size (tran.2) + 4 <= len)%Z.
Proof.
  rewrite /parse_transaction_descriptor.
  intros Hparse.
  destruct (parse_list_of_Word mem p_tx len) eqn:Heqn.
  simpl in Hparse.
  2:{ rewrite //= in Hparse. }
  destruct (l !! 0) as [f1|];
  destruct (l !! 1) as [f2|];
  destruct (l !! 2) as [f3|];
  destruct (l !! 3) as [f4|] eqn:Hlk4; try destruct (decode_vmid f1);rewrite //= in Hparse;
  destruct (decode_vmid f4);rewrite //= in Hparse.
  destruct (parse_list_of_pids (drop 4 l) f3) eqn:Hl0.
  inversion Hparse.
  simpl.
  apply parse_list_of_pids_length in Hl0.
  rewrite drop_length in Hl0.
  pose proof (size_list_to_set' l0).
  rewrite -Hl0 in H0.
  apply parse_list_of_Word_length in Heqn.
  rewrite -Heqn.
  assert (length l >= 4).
  { pose proof (lookup_lt_is_Some_1 l 3).
    feed specialize H2.
    eauto.
    lia.
  }
  lia.
  done.
Qed.

Lemma p_share_inv_consist σ1 h i j ps:
  inv_trans_pgt_consistent σ1->
  inv_trans_sndr_rcvr_neq σ1.2 ->
  σ1.2 !! h = Some None ->
  set_Forall (λ p, get_page_table σ1 !! p = Some (Some i, true, {[i]})) ps ->
  inv_trans_pgt_consistent (update_page_table_global flip_excl (alloc_transaction σ1 h (i, j, ps, Sharing, false)) i ps).
Proof.
  intros Hinv_con Hinv_neq Hlk Hforall.
  rewrite /inv_trans_pgt_consistent /inv_trans_pgt_consistent' /=.
  rewrite map_Forall_lookup.
  intros h' meta Hlookup'.
  rewrite lookup_insert_Some in Hlookup'.
  destruct Hlookup' as [[<- <-]|[Hneq Hlookup']].
  { (* FIXED: cannot prove access is a singleton set. changed the excl RA to size acc && excl *)
    intros p Hin.
    simpl in *.
    generalize dependent σ1.1.1.1.2.
    induction ps using set_ind_L.
    - set_solver + Hin.
    - intros pgt Hforall.
      rewrite set_fold_disj_union_strong.
      {
        rewrite set_fold_singleton.
        destruct (decide (x = p)).
        {
          subst.
          specialize (Hforall  p).
          feed specialize Hforall. set_solver +.
          rewrite Hforall /=.
          apply p_upd_pgt_pgt_not_elem.
          done.
          rewrite lookup_insert_Some.
          left;done.
        }
        {
          destruct ( pgt !! x).
          {
            rewrite IHps //.
            set_solver + n Hin.
            intros p' Hin'.
            rewrite lookup_insert_ne.
            apply Hforall.
            set_solver + Hin'.
            set_solver + Hin' H0.
          }
          {
            rewrite IHps //.
            set_solver + n Hin.
            intros p' Hin'.
            apply Hforall.
            set_solver + Hin'.
          }
        }
      }
      apply upd_is_strong_assoc_comm.
      set_solver + H0.
  }
  {
  rewrite /inv_trans_pgt_consistent /inv_trans_pgt_consistent' /= in Hinv_con.
  specialize (Hinv_con h' meta Hlookup').
  simpl in Hinv_con.
  destruct meta as [[[[[sv rv] ps'] tt] b]|];last done.
  simpl in *.
  intros p Hin.
  specialize (Hinv_con p Hin).
  assert (p ∉ ps).
  {
    intro.
    specialize (Hforall p H0).
    rewrite Hforall in Hinv_con.
    destruct tt; destruct b;auto;
      try set_solver + Hinv_con.
    specialize (Hinv_neq h' _ Hlookup').
    simpl in Hinv_neq.
    set_solver.
  }
  destruct tt,b;auto; try apply p_upd_pgt_pgt_not_elem;auto.
  }
Qed.


Lemma mem_send_invalid_len {i wi r0 r1 r2 hvcf tt q sacc p_tx} ai :
  (tpa ai) ∈ sacc ->
  (tpa ai) ≠ p_tx ->
  let len := (finz.to_z r1) in
  decode_instruction wi = Some(Hvc) ->
  decode_hvc_func r0 = Some(hvcf) ->
  hvcf_to_tt hvcf = Some tt ->
  (page_size < len)%Z ->
  {SS{{ ▷(PC @@ i ->r ai) ∗
      ▷ ai ->a wi ∗
      ▷ (i -@{q}A> sacc) ∗
      ▷ (R0 @@ i ->r r0) ∗
      ▷ (R1 @@ i ->r r1) ∗
      ▷ (R2 @@ i ->r r2) ∗
      ▷ TX@ i := p_tx
       }}}
   ExecI @ i {{{ RET (false, ExecI) ;
                 PC @@ i ->r (ai ^+ 1)%f ∗
                 ai ->a wi ∗
                 i -@{q}A> sacc ∗
                 R0 @@ i ->r (encode_hvc_ret_code Error) ∗
                 R1 @@ i ->r r1 ∗
                 R2 @@ i ->r (encode_hvc_error InvParam) ∗
                 TX@ i := p_tx}}}.
Proof.
Admitted.

Lemma mem_send_invalid_msg {i wi r0 r1 r2 hvcf tt p_tx q sacc} ai mem_tx :
  (tpa ai) ∈ sacc ->
  (tpa ai) ≠ p_tx ->
  let len := (Z.to_nat (finz.to_z r1)) in
  decode_instruction wi = Some(Hvc) ->
  decode_hvc_func r0 = Some(hvcf) ->
  hvcf_to_tt hvcf = Some tt ->
  (len <= page_size)%Z ->
  parse_transaction_descriptor mem_tx (of_pid p_tx) len = None ->
  {SS{{ ▷(PC @@ i ->r ai) ∗
      ▷ ai ->a wi ∗
      ▷ (i -@{q}A> sacc) ∗
      ▷ (R0 @@ i ->r r0) ∗
      ▷ (R1 @@ i ->r r1) ∗
      ▷ (R2 @@ i ->r r2) ∗
      ▷ (TX@ i := p_tx) ∗
      ▷ (memory_page p_tx mem_tx)
       }}}
   ExecI @ i {{{ RET (false, ExecI) ;
                 PC @@ i ->r (ai ^+ 1)%f ∗
                 ai ->a wi ∗
                 i -@{q}A> sacc ∗
                 R0 @@ i ->r (encode_hvc_ret_code Error) ∗
                 R1 @@ i ->r r1 ∗
                 R2 @@ i ->r (encode_hvc_error InvParam) ∗
                 TX@ i := p_tx ∗
                 memory_page p_tx mem_tx
    }}}.
Proof.
Admitted.

Lemma mem_send_invalid_des {i wi r0 r1 r2 hvcf p_tx tt q sacc} ai mem_tx tran :
  (tpa ai) ∈ sacc ->
  (tpa ai) ≠ p_tx ->
  let len := (Z.to_nat (finz.to_z r1)) in
  decode_instruction wi = Some(Hvc) ->
  decode_hvc_func r0 = Some(hvcf) ->
  hvcf_to_tt hvcf = Some tt ->
  (len <= page_size)%Z ->
  parse_transaction_descriptor mem_tx (of_pid p_tx) len = Some tran ->
  validate_transaction_descriptor i tran = false ->
  {SS{{ ▷(PC @@ i ->r ai) ∗
      ▷ ai ->a wi ∗
      ▷ i -@{q}A> sacc ∗
      ▷ (R0 @@ i ->r r0) ∗
      ▷ (R1 @@ i ->r r1) ∗
      ▷ (R2 @@ i ->r r2) ∗
      ▷ (TX@ i := p_tx) ∗
      ▷ (memory_page p_tx mem_tx)
       }}}
   ExecI @ i {{{ RET (false, ExecI) ;
                 PC @@ i ->r (ai ^+ 1)%f ∗
                 ai ->a wi ∗
                 i -@{q}A> sacc ∗
                 R0 @@ i ->r (encode_hvc_ret_code Error) ∗
                 R1 @@ i ->r r1 ∗
                 R2 @@ i ->r (encode_hvc_error InvParam) ∗
                 TX@ i := p_tx ∗
                 memory_page p_tx mem_tx
    }}}.
Proof.
Admitted.

Lemma mem_send_not_owned {i wi r0 r1 r2 hvcf p_tx tt q sacc} ai p O mem_tx tran :
  (tpa ai) ∈ sacc ->
  (tpa ai) ≠ p_tx ->
  let len := (Z.to_nat (finz.to_z r1)) in
  decode_instruction wi = Some(Hvc) ->
  decode_hvc_func r0 = Some(hvcf) ->
  hvcf_to_tt hvcf = Some tt ->
  (len <= page_size)%Z ->
  parse_transaction_descriptor mem_tx (of_pid p_tx) len = Some tran ->
  validate_transaction_descriptor i tran = true ->
  p ∈ tran.2 ->
  {SS{{ ▷(PC @@ i ->r ai) ∗
      ▷ ai ->a wi ∗
      ▷ i -@{q}A> sacc ∗
      ▷ (R0 @@ i ->r r0) ∗
      ▷ (R1 @@ i ->r r1) ∗
      ▷ (R2 @@ i ->r r2) ∗
      ▷ (TX@ i := p_tx) ∗
      ▷ (memory_page p_tx mem_tx) ∗
      ▷ O ∗
      ▷ (O -∗ (p -@O> - ∨ (∃j, p -@O> j ∗ ⌜j ≠ i⌝)))
       }}}
   ExecI @ i {{{ RET (false, ExecI) ;
                 PC @@ i ->r (ai ^+ 1)%f ∗
                 ai ->a wi ∗
                 i -@{q}A> sacc ∗
                 R0 @@ i ->r (encode_hvc_ret_code Error) ∗
                 R1 @@ i ->r r1 ∗
                 R2 @@ i ->r (encode_hvc_error Denied) ∗
                 TX@ i := p_tx ∗
                 memory_page p_tx mem_tx ∗
                 O
    }}}.
Proof.
Admitted.

Lemma mem_send_not_excl {i wi r0 r1 r2 hvcf p_tx tt q sacc} ai p mem_tx tran :
  (tpa ai) ∈ sacc ->
  (tpa ai) ≠ p_tx ->
  let len := (Z.to_nat (finz.to_z r1)) in
  decode_instruction wi = Some(Hvc) ->
  decode_hvc_func r0 = Some(hvcf) ->
  hvcf_to_tt hvcf = Some tt ->
  (len <= page_size)%Z ->
  parse_transaction_descriptor mem_tx (of_pid p_tx) len = Some tran ->
  validate_transaction_descriptor i tran = true ->
  p ∈ tran.2 ->
  {SS{{ ▷(PC @@ i ->r ai) ∗
      ▷ ai ->a wi ∗
      ▷ i -@{q}A> sacc ∗
      ▷ (R0 @@ i ->r r0) ∗
      ▷ (R1 @@ i ->r r1) ∗
      ▷ (R2 @@ i ->r r2) ∗
      ▷ (TX@ i := p_tx) ∗
      ▷ (memory_page p_tx mem_tx) ∗
      ▷ (p -@E> false)
       }}}
   ExecI @ i {{{ RET (false, ExecI) ;
                 PC @@ i ->r (ai ^+ 1)%f ∗
                 ai ->a wi ∗
                 i -@{q}A> sacc ∗
                 R0 @@ i ->r (encode_hvc_ret_code Error) ∗
                 R1 @@ i ->r r1 ∗
                 R2 @@ i ->r (encode_hvc_error Denied) ∗
                 TX@ i := p_tx ∗
                 memory_page p_tx mem_tx ∗
                 p -@E> false
    }}}.
Proof.
Admitted.

Lemma mem_send_not_acc {i wi r0 r1 r2 hvcf p_tx tt sacc} ai p mem_tx tran:
  (tpa ai) ∈ sacc ->
  (tpa ai) ≠ p_tx ->
  let len := (Z.to_nat (finz.to_z r1)) in
  decode_instruction wi = Some(Hvc) ->
  decode_hvc_func r0 = Some(hvcf) ->
  hvcf_to_tt hvcf = Some tt ->
  (len <= page_size)%Z ->
  parse_transaction_descriptor mem_tx (of_pid p_tx) len = Some tran ->
  validate_transaction_descriptor i tran = true ->
  p ∈ tran.2 ->
  p ∉ sacc ->
  {SS{{ ▷(PC @@ i ->r ai) ∗
      ▷ ai ->a wi ∗
      ▷ (R0 @@ i ->r r0) ∗
      ▷ (R1 @@ i ->r r1) ∗
      ▷ (R2 @@ i ->r r2) ∗
      ▷ (TX@ i := p_tx) ∗
      ▷ (memory_page p_tx mem_tx) ∗
      ▷ (i -@A> sacc)
       }}}
   ExecI @ i {{{ RET (false, ExecI) ;
                 PC @@ i ->r (ai ^+ 1)%f ∗
                 ai ->a wi ∗
                 R0 @@ i ->r (encode_hvc_ret_code Error) ∗
                 R1 @@ i ->r r1 ∗
                 R2 @@ i ->r (encode_hvc_error Denied) ∗
                 TX@ i := p_tx ∗
                 memory_page p_tx mem_tx ∗
                 i -@A> sacc
    }}}.
Proof.
Admitted.

Lemma mem_send_in_trans {i wi r0 r1 r2 hvcf p_tx tt tran q tran' q' sacc} ai p wh mem_tx:
  (tpa ai) ∈ sacc ->
  (tpa ai) ≠ p_tx ->
  let len := (Z.to_nat (finz.to_z r1)) in
  decode_instruction wi = Some(Hvc) ->
  decode_hvc_func r0 = Some(hvcf) ->
  hvcf_to_tt hvcf = Some tt ->
  (len <= page_size)%Z ->
  parse_transaction_descriptor mem_tx (of_pid p_tx) len = Some tran ->
  validate_transaction_descriptor i tran = true ->
  p ∈ tran.2 ->
  p ∈ tran'.1.2 ->
  {SS{{ ▷(PC @@ i ->r ai) ∗
      ▷ ai ->a wi ∗
      ▷ i -@{q'}A> sacc ∗
      ▷ (R0 @@ i ->r r0) ∗
      ▷ (R1 @@ i ->r r1) ∗
      ▷ (R2 @@ i ->r r2) ∗
      ▷ (TX@ i := p_tx) ∗
      ▷ (memory_page p_tx mem_tx) ∗
      ▷ (wh -{q}>t tran')
       }}}
   ExecI @ i {{{ RET (false, ExecI) ;
                 PC @@ i ->r (ai ^+ 1)%f ∗
                 ai ->a wi ∗
                 i -@{q'}A> sacc ∗
                 R0 @@ i ->r (encode_hvc_ret_code Error) ∗
                 R1 @@ i ->r r1 ∗
                 R2 @@ i ->r (encode_hvc_error Denied) ∗
                 TX@ i := p_tx ∗
                 memory_page p_tx mem_tx ∗
                 wh -{q}>t tran'
    }}}.
Proof.
Admitted.

Lemma mem_send_no_fresh_handles {i wi r0 r1 r2 hvcf tt p_tx sacc} ai sh j mem_tx (ps: gset PID):
  (tpa ai) ∈ sacc ->
  (tpa ai) ≠ p_tx ->
  let len := (Z.to_nat (finz.to_z r1)) in
  decode_instruction wi = Some(Hvc) ->
  decode_hvc_func r0 = Some(hvcf) ->
  hvcf_to_tt hvcf = Some tt ->
  (len <= page_size)%Z ->
  parse_transaction_descriptor mem_tx (of_pid p_tx) len = Some (i, None, j, ps) ->
  i ≠ j ->
  ps ⊆ sacc ->
  sh = ∅ ->
  {SS{{ ▷(PC @@ i ->r ai) ∗
      ▷ ai ->a wi ∗
      ▷ ([∗ set] p ∈ ps, p -@O> i ∗ p -@E> true) ∗
      ▷ (i -@A> sacc) ∗
      ▷ (R0 @@ i ->r r0) ∗
      ▷ (R1 @@ i ->r r1) ∗
      ▷ (R2 @@i ->r r2) ∗
      ▷ (fresh_handles 1 sh) ∗
      ▷ TX@ i := p_tx ∗
      ▷ memory_page p_tx mem_tx
       }}}
   ExecI @ i {{{ RET (false, ExecI) ;
                 PC @@ i ->r (ai ^+ 1)%f ∗
                 ai ->a wi ∗
                 ([∗ set] p ∈ ps, p -@O> i ∗ p -@E> true) ∗
                 i -@A> sacc ∗
                 R0 @@ i ->r (encode_hvc_ret_code Error) ∗
                 R1 @@ i ->r r1 ∗
                 R2 @@ i ->r (encode_hvc_error NoMem) ∗
                 fresh_handles 1 sh ∗
                 TX@ i := p_tx ∗
                 memory_page p_tx mem_tx}}}.
Proof.
Admitted.

Lemma mem_share {i wi r0 r1 r2 hvcf p_tx sacc} ai j mem_tx sh (ps: gset PID) :
  (tpa ai) ∈ sacc ->
  (tpa ai) ≠ p_tx ->
  (* len is the length of the msg *)
  let len := (Z.to_nat (finz.to_z r1)) in
  (* the decoding of wi is correct *)
  decode_instruction wi = Some(Hvc) ->
  (* the decoding of R0 is a FFA mem_share *)
  decode_hvc_func r0 = Some(hvcf) ->
  hvcf_to_tt hvcf = Some Sharing ->
  (* the whole descriptor resides in the TX page *)
  (len <= page_size)%Z ->
  (* the descriptor *)
  parse_transaction_descriptor mem_tx (of_pid p_tx) len = Some (i, None, j, ps) ->
  (* caller is not the receiver *)
  i ≠ j ->
  ps ⊆ sacc ->
  (* there is at least one free handle in the hpool *)
  sh ≠ ∅ ->
  {SS{{ ▷(PC @@ i ->r ai) ∗
      ▷ ai ->a wi ∗
      (* VM i exclusively owns pages in ps *)
      ▷ ([∗ set] p ∈ ps, p -@O> i ∗ p -@E> true) ∗
      ▷ (i -@A> sacc) ∗
      ▷ (R0 @@ i ->r r0) ∗
      ▷ (R1 @@ i ->r r1) ∗
      ▷ (R2 @@i ->r r2) ∗
      ▷ (fresh_handles 1 sh) ∗
      ▷ TX@ i := p_tx ∗
      ▷ memory_page p_tx mem_tx
       }}}
   ExecI @ i {{{ RET (false, ExecI) ;
                 PC @@ i ->r (ai ^+ 1)%f ∗
                 ai ->a wi ∗
                 ([∗ set] p ∈ ps, p -@O> i ∗ p -@E> false) ∗
                 i -@A> sacc ∗
                 R0 @@ i ->r (encode_hvc_ret_code Succ) ∗
                 R1 @@ i ->r r1 ∗
                 (∃ (wh: Word), ⌜wh ∈ sh⌝ ∗
                 R2 @@ i ->r wh ∗
                 wh ->t (i, j, ps, Sharing) ∗
                 wh ->re false ∗
                 fresh_handles 1 (sh∖{[wh]})) ∗
                 TX@ i := p_tx ∗
                 memory_page p_tx mem_tx}}}.
Proof.
  iIntros (Hin_acc Hneq_tx len Hdecode_i Hdecode_f Htt Hle_ps Hparse Hneq_vmid Hsubseteq_acc Hneq_hp Φ)
          "(>PC & >mem_ins & >oe & >acc & >R0 & >R1 & >R2 & >[hp handles] & >tx & >mem_tx) HΦ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (n σ1) "%Hsche state".
  rewrite /scheduled /= /scheduler in Hsche.
  assert (σ1.1.1.2 = i) as Heq_cur. { case_bool_decide;last done. by apply fin_to_nat_inj. }
  clear Hsche.
  iModIntro.
  iDestruct "state" as "(Hnum & mem & regs & mb & rx_state & pgt_owned & pgt_acc & pgt_excl &
                            trans & hpool & retri & %Hwf & %Hdisj & %Hconsis)".
  (* valid regs *)
  iDestruct ((gen_reg_valid4 i PC ai R0 r0 R1 r1 R2 r2 Heq_cur) with "regs PC R0 R1 R2")
    as "(%Hlookup_PC & %Hlookup_R0 & %Hlookup_R1 & %Hlookup_R2)";eauto.
  (* valid pt *)
  iDestruct (access_agree_check_true (tpa ai) i with "pgt_acc acc") as %Hcheckpg_ai;eauto.
  iDestruct (access_agree_check_true_forall with "pgt_acc acc") as %Hcheckpg_acc;eauto.
  iDestruct (big_sepS_sep with "oe") as "[own excl]".
  iDestruct (excl_agree_Some_check_true_bigS with "pgt_excl excl") as %Hcheckpg_excl;eauto.
  iDestruct (excl_agree_Some_lookup_bigS with "pgt_excl excl") as %Hvalid_excl;eauto.
  iDestruct (own_agree_Some_check_true_bigS with "pgt_owned own") as %Hcheckpg_own;eauto.
  (* valid mem *)
  iDestruct (gen_mem_valid ai wi with "mem mem_ins") as %Hlookup_ai.
  iDestruct (gen_mem_valid_SepM with "mem [mem_tx]") as %Hlookup_mem_tx.
  { iDestruct "mem_tx" as "[% mem_tx]". iExact "mem_tx". }
  (* valid tx *)
  iDestruct (mb_valid_tx i p_tx with "mb tx") as %Heq_tx.
  (* valid hpool *)
  iDestruct (hpool_valid with "hpool hp") as %Heq_hp.
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal i Hvc ai wi);eauto.
    rewrite Heq_tx //.
  - iModIntro.
    iIntros (m2 σ2) "vmprop_auth %HstepP".
    iFrame "vmprop_auth".
    apply (step_ExecI_normal i Hvc ai wi) in HstepP;eauto.
    2: rewrite Heq_tx //.
    remember (exec Hvc σ1) as c2 eqn:Heqc2.
    destruct hvcf; inversion Htt.
    rewrite /exec /hvc Hlookup_R0 /= Hdecode_f /mem_send Hlookup_R1 /= in Heqc2.
    case_bool_decide;first lia.
    pose proof (parse_transaction_descriptor_length _ _ _ _ Hparse) as Hlt_pg.
    rewrite -Heq_tx -Heq_cur /len in Hparse.
    apply (parse_transaction_descriptor_tx _ σ1.1.2) in Hparse;last done.
    rewrite Hparse //= in Heqc2.
    case_bool_decide.
    2: { destruct H1. split;auto. split;eauto. rewrite Heq_cur //. }
    case_bool_decide.
    2: { destruct H2. intros s Hin.
         rewrite Heq_cur.
         rewrite andb_true_iff. split.
         rewrite /check_excl_access_page.
         rewrite andb_true_iff. split.
         apply Hcheckpg_acc.
         set_solver + Hsubseteq_acc Hin.
         by apply Hcheckpg_excl.
         by apply Hcheckpg_own.
    }
    clear H1 H2.
    rewrite /new_transaction /= /fresh_handle /= -Heq_hp in Heqc2.
    destruct (elements sh) as [| h fhs] eqn:Hfhs.
    { exfalso. rewrite -elements_empty in Hfhs.  apply Hneq_hp. apply set_eq.
      intro. rewrite -elem_of_elements Hfhs elem_of_elements. split;intro;set_solver. }
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    (* unchanged part *)
    rewrite (preserve_get_mb_gmap σ1).
    rewrite (preserve_get_rx_gmap σ1).
    all: try rewrite p_upd_pc_mb //.
    rewrite p_upd_pc_mem 2!p_upd_reg_mem p_flip_excl_mem p_alloc_tran_mem.
    iFrame "Hnum mem rx_state mb".
    (* upd regs *)
    rewrite Heq_cur.
    rewrite (u_upd_pc_regs _ i ai) //.
    2: { rewrite 2!u_upd_reg_regs.
         rewrite (preserve_get_reg_gmap σ1). rewrite lookup_insert_ne //.  rewrite lookup_insert_ne //. solve_reg_lookup. done.
    }
    rewrite u_upd_reg_regs p_upd_reg_current_vm p_flip_excl_current_vm p_alloc_tran_current_vm  Heq_cur.
    rewrite u_upd_reg_regs p_flip_excl_current_vm p_alloc_tran_current_vm  Heq_cur.
    rewrite (preserve_get_reg_gmap σ1) //.
    iDestruct ((gen_reg_update3_global PC i (ai ^+ 1)%f R2 i h R0 i (encode_hvc_ret_code Succ)) with "regs PC R2 R0")
      as ">[$ [PC [R2 R0]]]";eauto.
    (* upd pgt *)
    rewrite (preserve_get_own_gmap (update_page_table_global flip_excl (alloc_transaction σ1 h (i, j, ps, Sharing, false)) i ps) (update_incr_PC _)).
    2: rewrite p_upd_pc_pgt !p_upd_reg_pgt //.
    rewrite p_flip_excl_own. rewrite (preserve_get_own_gmap σ1) //.
    iFrame "pgt_owned".
    rewrite (preserve_get_access_gmap (update_page_table_global flip_excl (alloc_transaction σ1 h (i, j, ps, Sharing, false)) i ps) (update_incr_PC _)).
    2: rewrite p_upd_pc_pgt p_upd_reg_pgt //.
    rewrite p_flip_excl_acc. rewrite (preserve_get_access_gmap σ1) //.
    iFrame "pgt_acc".
    rewrite (preserve_get_excl_gmap (update_page_table_global flip_excl (alloc_transaction σ1 h (i, j, ps, Sharing, false)) i ps) (update_incr_PC _)).
    2: rewrite p_upd_pc_pgt p_upd_reg_pgt //.
    assert (Hvalid_acc: set_Forall (λ p : PID,
      ∃ e : option VMID * bool * gset VMID, σ1.1.1.1.2 !! p = Some e ∧ e.2 = {[i]}) ps).
    {
      intros p Hin.
      specialize (Hcheckpg_acc p).
      feed specialize Hcheckpg_acc. set_solver + Hin Hsubseteq_acc.
      specialize (Hvalid_excl p Hin).
      destruct Hvalid_excl as [o [b [s [Hlk Htrue]]]].
      symmetry in Htrue.
      rewrite andb_true_iff in Htrue.
      destruct Htrue as [-> Hsize].
      rewrite /check_access_page /= in Hcheckpg_acc.
      rewrite Hlk in Hcheckpg_acc.
      destruct (decide (i ∈ s)); last done.
      case_bool_decide;last done.
      exists (o, true, s). split;auto.
      apply size_singleton_le;auto.
    }
    rewrite u_flip_excl_excl //.
    iDestruct (excl_update_flip with "pgt_excl excl") as ">[$ excl]".
    (* upd tran *)
    rewrite (preserve_get_trans_gmap (alloc_transaction σ1 h (i, j, ps, Sharing, false)) (update_incr_PC _)).
    2: rewrite p_upd_pc_trans p_upd_reg_trans  //.
    rewrite u_alloc_tran_trans.
    assert (sh = {[h]} ∪ sh ∖ {[h]}) as Heq_sh.
    { assert (h ∈ sh).
      rewrite -elem_of_elements. rewrite Hfhs. set_solver +.
      rewrite union_comm_L.
      rewrite difference_union_L.
      set_solver + H1.
    }
    iPoseProof (big_sepS_union _ {[h]} (sh ∖ {[h]})) as "[H _]".
    set_solver +.
    iDestruct ("H" with "[handles]") as "[h handles]".
    rewrite -Heq_sh. iExact "handles".
    rewrite big_sepS_singleton. iDestruct "h" as "[tran re]". iClear "H".
    iDestruct (trans_valid_None with "trans tran") as %Hlookup_tran.
    iDestruct (trans_update_insert h (i, j, ps, Sharing) with "trans tran") as ">[$ tran]".
    (* upd hp *)
    rewrite (preserve_get_hpool_gset (alloc_transaction σ1 h (i, j, ps, Sharing, false)) (update_incr_PC _)).
    2: rewrite p_upd_pc_trans p_upd_reg_trans //. rewrite u_alloc_tran_hpool.
    iDestruct (hpool_update_diff h with "hpool hp") as ">[$ hp]".
    (* upd retri *)
    rewrite (preserve_get_retri_gmap (alloc_transaction σ1 h (i, j, ps, Sharing, false)) (update_incr_PC _)).
    2: rewrite p_upd_pc_trans p_upd_reg_trans //. rewrite u_alloc_tran_retri.
    iDestruct (retri_update_insert with "retri re") as ">[$ re]".
    (* inv_trans_wellformed *)
    rewrite (preserve_inv_trans_wellformed (alloc_transaction σ1 h (i, j, ps, Sharing, false))).
    2: rewrite p_upd_pc_trans p_upd_reg_trans //.
    iAssert (⌜inv_trans_wellformed (alloc_transaction σ1 h (i, j, ps, Sharing, false))⌝%I) as "$".
    iPureIntro.
    apply (p_alloc_tran_inv_wf h (i, j, ps, Sharing, false));auto.
    simpl. simpl in Hlt_pg. rewrite Z.leb_le. lia.
    (* inv_trans_pgt_consistent *)
    rewrite (preserve_inv_trans_pgt_consistent (update_page_table_global flip_excl (alloc_transaction σ1 h (i, j, ps, Sharing, false)) i ps) (update_incr_PC _)).
    2: rewrite p_upd_pc_trans p_upd_reg_trans //.
    2: rewrite p_upd_pc_pgt p_upd_reg_pgt //.
    iAssert (⌜inv_trans_pgt_consistent (update_page_table_global flip_excl (alloc_transaction σ1 h (i, j, ps, Sharing, false)) i ps)⌝%I) as "$".
    iPureIntro.
    apply p_share_inv_consist;auto.
    { destruct Hwf as [_ [? _]]. done. }
    {
      intros p Hin.
      specialize (Hvalid_excl p Hin).
      specialize (Hcheckpg_own p Hin).
      specialize (Hvalid_acc p Hin).
      destruct Hvalid_excl as [o [b [s [Hlk Htrue]]]].
      symmetry in Htrue.
      rewrite andb_true_iff in Htrue.
      destruct Htrue as [-> Hsize].
      rewrite /check_ownership_page /= in Hcheckpg_own.
      rewrite Hlk in Hcheckpg_own.
      destruct o;last done.
      destruct (decide (i = v));last done.
      subst v.
      rewrite Hlk in Hvalid_acc.
      destruct Hvalid_acc as [? [? ?]].
      inversion H1. subst x.
      rewrite /= in H2. subst s. done.
    }
    (* inv_trans_ps_disj *)
    rewrite (preserve_inv_trans_ps_disj (alloc_transaction σ1 h (i, j, ps, Sharing, false))).
    2: rewrite p_upd_pc_trans p_upd_reg_trans //.
    iAssert (⌜inv_trans_ps_disj (alloc_transaction σ1 h (i, j, ps, Sharing, false))⌝%I) as "$". iPureIntro.
    apply p_alloc_tran_inv_disj;auto.
    {
      rewrite /= elem_of_disjoint.
      intros.
      apply elem_of_pages_in_trans' in H2.
      destruct H2 as [h' [tran' [Hlk Hin_h']]].
      specialize (Hconsis h' (Some tran') Hlk x Hin_h').
      specialize (Hvalid_acc x H1).
      destruct Hvalid_acc as [e [Hlk' He]].
      destruct Hwf as [_ [Hneq _]].
      specialize (Hneq h' _ Hlk).
      destruct (tran'.1.2);destruct tran'.2;auto.
      - rewrite Hlk' in Hconsis.
        inversion Hconsis.
        subst e. set_solver + He.
      - rewrite Hlk' in Hconsis.
        inversion Hconsis.
        subst e. simpl in He.
        set_solver + He Hneq.
      - specialize (Hvalid_excl x H1).
        destruct Hvalid_excl as [? [? [? [Hlk'' Htrue]]]].
        symmetry in Htrue.
        rewrite andb_true_iff in Htrue.
        destruct Htrue  as [-> _].
        rewrite Hlk'' in Hconsis.
        inversion Hconsis.
      - specialize (Hcheckpg_own x H1).
        rewrite /check_ownership_page /= in Hcheckpg_own.
        rewrite Hlk' in Hcheckpg_own.
        rewrite Hlk' in Hconsis.
        inversion Hconsis.
        subst e.
        destruct (decide (i = tran'.1.1.1.1));last done.
        set_solver + e He Hneq.
      - rewrite Hlk' in Hconsis.
        inversion Hconsis.
        subst e. set_solver + He.
    }
    (* just_scheduled *)
    iModIntro.
    rewrite /just_scheduled_vms /just_scheduled.
    rewrite /scheduled /machine.scheduler /= /scheduler.
    rewrite p_upd_pc_current_vm 2!p_upd_reg_current_vm p_flip_excl_current_vm  p_alloc_tran_current_vm.
    rewrite Heq_cur.
    iSplitL "".
    set fl := (filter _ _).
    assert (fl = []) as ->.
    {
      rewrite /fl.
      induction n.
      - simpl.
        rewrite filter_nil //=.
      - rewrite seq_S.
        rewrite filter_app.
        rewrite IHn.
        simpl.
        rewrite filter_cons_False //=.
        rewrite andb_negb_l.
        done.
    }
    by iSimpl.
    (* Φ *)
    case_bool_decide;last done.
    simpl. iApply "HΦ".
    rewrite /fresh_handles. iFrame.
    iSplitL "own excl".
    rewrite big_sepS_sep. iFrame.
    iExists h. iFrame.
    rewrite Heq_sh.
    iPureIntro. set_solver +.
Qed.

Lemma mem_lend {i wi r0 r1 r2 hvcf p_tx sacc} ai j mem_tx sh (ps: gset PID) :
  (tpa ai) ∈ sacc ->
  (tpa ai) ≠ p_tx ->
  (* len is the length of the msg *)
  let len := (Z.to_nat (finz.to_z r1)) in
  (* the decoding of wi is correct *)
  decode_instruction wi = Some(Hvc) ->
  (* the decoding of R0 is a FFA mem_share *)
  decode_hvc_func r0 = Some(hvcf) ->
  hvcf_to_tt hvcf = Some Lending ->
  (* the whole descriptor resides in the TX page *)
  (len <= page_size)%Z ->
  (* the descriptor *)
  parse_transaction_descriptor mem_tx (of_pid p_tx) len = Some (i, None, j, ps) ->
  (* caller is not the receiver *)
  i ≠ j ->
  ps ⊆ sacc ->
  (* there is at least one free handle in the hpool *)
  sh ≠ ∅ ->
  {SS{{ ▷(PC @@ i ->r ai) ∗
      ▷ ai ->a wi ∗
      (* VM i exclusively owns pages in ps *)
      ▷ ([∗ set] p ∈ ps, p -@O> i ∗ p -@E> true) ∗
      ▷ (i -@A> sacc) ∗
      ▷ (R0 @@ i ->r r0) ∗
      ▷ (R1 @@ i ->r r1) ∗
      ▷ (R2 @@i ->r r2) ∗
      ▷ (fresh_handles 1 sh) ∗
      ▷ TX@ i := p_tx ∗
      ▷ memory_page p_tx mem_tx
       }}}
   ExecI @ i {{{ RET (false, ExecI) ;
                 PC @@ i ->r (ai ^+ 1)%f ∗
                 ai ->a wi ∗
                 ([∗ set] p ∈ ps, p -@O> i ∗ p -@E> true) ∗
                 i -@A> (sacc ∖ ps) ∗
                 R0 @@ i ->r (encode_hvc_ret_code Succ) ∗
                 R1 @@ i ->r r1 ∗
                 (∃ (wh: Word), ⌜wh ∈ sh⌝ ∗
                 R2 @@ i ->r wh ∗
                 wh ->t (i, j, ps, Lending) ∗
                 wh ->re false ∗
                 fresh_handles 1 (sh∖{[wh]})) ∗
                 TX@ i := p_tx ∗
                 memory_page p_tx mem_tx}}}.
Proof.
Admitted.

Lemma mem_donate {i wi r0 r1 r2 hvcf p_tx sacc} ai j mem_tx sh (ps: gset PID) :
  (tpa ai) ∈ sacc ->
  (tpa ai) ≠ p_tx ->
  (* len is the length of the msg *)
  let len := (Z.to_nat (finz.to_z r1)) in
  (* the decoding of wi is correct *)
  decode_instruction wi = Some(Hvc) ->
  (* the decoding of R0 is a FFA mem_share *)
  decode_hvc_func r0 = Some(hvcf) ->
  hvcf_to_tt hvcf = Some Donation ->
  (* the whole descriptor resides in the TX page *)
  (len <= page_size)%Z ->
  (* the descriptor *)
  parse_transaction_descriptor mem_tx (of_pid p_tx) len = Some (i, None, j, ps) ->
  (* caller is not the receiver *)
  i ≠ j ->
  ps ⊆ sacc ->
  (* there is at least one free handle in the hpool *)
  sh ≠ ∅ ->
  {SS{{ ▷(PC @@ i ->r ai) ∗
      ▷ ai ->a wi ∗
      (* VM i exclusively owns pages in ps *)
      ▷ ([∗ set] p ∈ ps, p -@O> i ∗ p -@E> true) ∗
      ▷ (i -@A> sacc) ∗
      ▷ (R0 @@ i ->r r0) ∗
      ▷ (R1 @@ i ->r r1) ∗
      ▷ (R2 @@i ->r r2) ∗
      ▷ (fresh_handles 1 sh) ∗
      ▷ TX@ i := p_tx ∗
      ▷ memory_page p_tx mem_tx
       }}}
   ExecI @ i {{{ RET (false, ExecI) ;
                 PC @@ i ->r (ai ^+ 1)%f ∗
                 ai ->a wi ∗
                 ([∗ set] p ∈ ps, p -@O> i ∗ p -@E> true) ∗
                 i -@A> (sacc ∖ ps) ∗
                 R0 @@ i ->r (encode_hvc_ret_code Succ) ∗
                 R1 @@ i ->r r1 ∗
                 (∃ (wh: Word), ⌜wh ∈ sh⌝ ∗
                 R2 @@ i ->r wh ∗
                 wh ->t (i, j, ps, Donation) ∗
                 wh ->re false ∗
                 fresh_handles 1 (sh∖{[wh]})) ∗
                 TX@ i := p_tx ∗
                 memory_page p_tx mem_tx}}}.
Proof.
Admitted.

End mem_send.
