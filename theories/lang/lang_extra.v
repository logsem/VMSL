(* This file contains some lemmas only about functions in the operational semantics (lang.v) *)
From HypVeri Require Import machine machine_extra lang.lang.
From iris.algebra Require Import auth gmap gset.
From iris.proofmode Require Import tactics.
From stdpp Require Import list.

Section lang_extra.

  Context `{HyperConst : !HypervisorConstants}.
  Context `{HyperParams : !HypervisorParameters}.

  Implicit Type σ : state.

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

  Lemma sequence_a_map_unit{A} (l:list A) :
    @sequence_a list _ _ _ A option _ _ (map (λ e , Some e ) l) = Some l.
  Proof.
    unfold sequence_a.
    simpl.
    unfold monad.List.sequence_a_list.
    induction l.
    done.
    simpl.
    simpl in IHl.
    rewrite IHl //.
  Qed.

  Lemma sequence_a_map_subseteq {A: Type} (l:list A) len p (m1 m2 :gmap _ A):
    sequence_a (map (λ v : Addr, m1 !! v) (finz.seq p len)) = Some l ->
    m1 ⊆ m2 ->
    sequence_a (map (λ v : Addr, m2 !! v) (finz.seq p len)) = Some l.
  Proof.
    unfold sequence_a. simpl.
    unfold monad.List.sequence_a_list.
    intros.
    generalize dependent p.
    generalize dependent l.
    induction len.
    done.
    destruct l.
    simpl.
    simpl in IHlen.
    intros.
    destruct (m1 !! p)  eqn:Hlk.
    2 : {
      rewrite //= in H.
    }
    destruct ( foldr
                 (λ (val : option A) (acc : option (list A)),
                   match match val with
                         | Some x' => Some (cons x')
                         | None => None
                         end with
                   | Some f' => match acc with
                                | Some a' => Some (f' a')
                                | None => None
                                end
                   | None => None
                   end) (Some []) (map (λ v : Addr, m1 !! v) (finz.seq (p ^+ 1)%f len))
             );
      inversion H.
    simpl.
    simpl in IHlen.
    intros.
    destruct (m1 !! p)  eqn:Hlk.
    2 : {
      rewrite //= in H.
    }
    rewrite /= in H.
    rewrite /=.
    destruct ( foldr
                 (λ (val : option A) (acc : option (list A)),
                   match match val with
                         | Some x' => Some (cons x')
                         | None => None
                         end with
                   | Some f' => match acc with
                                | Some a' => Some (f' a')
                                | None => None
                                end
                   | None => None
                   end) (Some []) (map (λ v : Addr, m1 !! v) (finz.seq (p ^+ 1)%f len))
             ) eqn:Heqn;
      inversion H.
    subst.
    assert (m2 !! p = Some a) as ->.
    {
      rewrite map_subseteq_spec in H0.
      apply H0.
      apply Hlk.
    }
    rewrite (IHlen l) //.
  Qed.

   Lemma sequence_a_map_Forall_Some {A: Type} len p (m1 :gmap _ A):
     (list_to_set (finz.seq p len)) ⊆ dom (gset _) m1 ->
     is_Some (sequence_a (map (λ v : Addr, m1 !! v) (finz.seq p len))).
  Proof.
    intros.
    unfold sequence_a. simpl.
    unfold monad.List.sequence_a_list.
    intros.
    generalize dependent p.
    induction len.
    intros.
    exists [].
    done.
    simpl.
    simpl in IHlen.
    intros.
    assert (p ∈ dom (gset _) m1). set_solver + H.
    rewrite elem_of_dom in H0.
    destruct H0 as [? ?].
    rewrite H0.
    specialize (IHlen (p^+1)%f ).
    feed specialize IHlen.
    {
      set_solver + H.
    }
    destruct IHlen.
    rewrite H1.
    auto.
  Qed.


  (** lemmas about taking a step *)

  Lemma reducible_normal{σ} i instr ai wi :
   (get_current_vm σ) = i ->
   check_access_page σ i (tpa ai) = true ->
   (get_mail_box σ @ i).1 ≠ (tpa ai) ->
   get_reg σ PC = Some ai ->
   get_mem σ !! ai = Some wi ->
   decode_instruction wi = Some (instr) ->
   ∃ m' σ', step ExecI σ m' σ'.
  Proof.
    intros Hi Hcheck Hneq Hpc Hai Hdecode.
    remember (exec instr σ) as ex.
    exists ex.1 ,ex.2 .
    apply step_exec_normal with ai wi instr;subst i ;eauto.
    rewrite /read_memory /check_read_access_addr /check_read_access_page.
    rewrite Hcheck.
    rewrite andb_true_l.
    case_match.
    done.
    apply bool_decide_eq_false in Heqb.
    done.
   Qed.

  Lemma step_ExecI_normal {σ m' σ' } i instr ai wi  :
   step ExecI σ m' σ'->
   (get_current_vm σ) = i ->
   check_access_page σ i (tpa ai) = true ->
   (get_mail_box σ @ i).1 ≠ (tpa ai) ->
   get_reg σ PC = Some ai ->
   get_mem σ !! ai = Some wi ->
   decode_instruction wi = Some (instr) ->
   (exec instr σ).1 = m' ∧ (exec instr σ).2 = σ'.
  Proof.
    intros HstepP Heqi Hcheck Hneq HPC Hmem Hdecode.
    inversion HstepP as
        [ σ1' a Hcheck' Hread
        | σ1' a w Hpc' Hread Hdecode' Hinvalid_ins
        | σ1'  ? ? ? ? Hreg2 Hread Hdecode2 Hexec Hcontrol];
      simplify_eq /=.
    + rewrite /read_memory Hmem /check_read_access_addr /check_read_access_page Hcheck andb_true_l /= in Hread.
      case_bool_decide;done.
    + rewrite /read_memory /check_read_access_addr /check_read_access_page Hcheck andb_true_l /= in Hread.
      case_bool_decide;last done.
      rewrite Hread in Hmem.
      inversion Hmem;subst.
      rewrite Hdecode // in Hdecode'.
    + rewrite /read_memory /check_read_access_addr /check_read_access_page Hcheck andb_true_l /= in Hread.
      case_bool_decide;last done.
      rewrite Hread in Hmem.
      inversion Hmem;subst.
      by rewrite Hdecode in Hdecode2;inversion Hdecode2;subst i0.
  Qed.

  Lemma option_state_unpack_preserve_state_Some σ1 σ2 (σ2': option state) :
    σ2' = Some σ2 -> (ExecI, σ2) = (option_state_unpack σ1 σ2').
  Proof.
    intros.
    destruct σ2' eqn:Heqn.
    inversion H; subst.
    done.
    done.
  Qed.

  Lemma mov_word_ExecI σ1 r w :
    PC ≠ r -> NZ ≠ r ->
    (mov_word σ1 r w) = (ExecI, (update_incr_PC (update_reg σ1 r w))).
  Proof.
    intros.
    unfold mov_word .
    destruct r;[contradiction|contradiction|].
    rewrite <- (option_state_unpack_preserve_state_Some
                  σ1 (update_incr_PC (update_reg σ1 (R n fin) w))
                  (Some (update_incr_PC (update_reg σ1 (R n fin) w))));eauto.
  Qed.

  Lemma mov_reg_ExecI σ1 r1 r2 w:
    PC ≠ r1 -> NZ ≠ r1 ->
    PC ≠ r2 -> NZ ≠ r2 ->
    (get_reg σ1 r2) = Some w ->
    (mov_reg σ1 r1 r2) = (ExecI, (update_incr_PC (update_reg σ1 r1 w))).
  Proof.
    intros.
    unfold mov_reg.
    destruct r1 eqn:Heqn1,r2 eqn:Heqn2 ;try contradiction.
    unfold bind.
    simpl.
    rewrite H3.
    rewrite <- (option_state_unpack_preserve_state_Some
                  σ1 (update_incr_PC (update_reg σ1 (R n fin) w))
                  (Some (update_incr_PC (update_reg σ1 (R n fin) w))));eauto.
  Qed.

  Lemma ldr_ExecI σ r1 r2 a w:
    PC ≠ r1 -> NZ ≠ r1 ->
    PC ≠ r2 -> NZ ≠ r2 ->
    (get_mail_box σ @ (get_current_vm σ)).1 ≠ (tpa a) ->
    check_access_page σ (get_current_vm σ) (tpa a) = true ->
    get_reg σ r2 = Some a ->
    get_memory σ a = Some w ->
    (ldr σ r1 r2) = (ExecI, (update_incr_PC (update_reg σ r1 w))).
  Proof.
    intros ? ? ? ? Hneq Hcheck Hreg Hmem.
    unfold ldr.
    destruct r1 eqn:Heqn1,r2 eqn:Heqn2 ;try contradiction.
    rewrite /bind /=.
    rewrite Hreg.
    rewrite /read_memory /check_read_access_addr /check_read_access_page Hcheck andb_true_l /=.
    case_bool_decide;last done.
    rewrite /get_memory in Hmem.
    rewrite Hmem //.
  Qed.

  Lemma ldr_FailPageFaultI_ldr_from_tx σ r1 r2 a :
    PC ≠ r1 -> NZ ≠ r1 ->
    PC ≠ r2 -> NZ ≠ r2 ->
    (get_mail_box σ @ (get_current_vm σ)).1 = (tpa a) ->
    get_reg σ r2 = Some a ->
    (ldr σ r1 r2) = (FailPageFaultI, σ).
  Proof.
    intros ? ? ? ? Heq Hreg.
    unfold ldr.
    destruct r1 eqn:Heqn1,r2 eqn:Heqn2 ;try contradiction.
    rewrite Hreg.
    rewrite /read_memory /check_read_access_addr /check_read_access_page.
    case_bool_decide;first done.
    rewrite andb_false_r //.
  Qed.

  Lemma ldr_FailPageFaultI_ldr_from_page σ1 r1 r2 a :
    PC ≠ r1 -> NZ ≠ r1 ->
    PC ≠ r2 -> NZ ≠ r2 ->
    check_access_page σ1 (get_current_vm σ1) (tpa a) = false->
    get_reg σ1 r2 = Some a ->
    (ldr σ1 r1 r2) = (FailPageFaultI, σ1).
  Proof.
    intros ? ? ? ? Hcheck Hreg.
    unfold ldr.
    destruct r1 eqn:Heqn1,r2 eqn:Heqn2 ;try contradiction.
    rewrite Hreg.
    rewrite /read_memory /check_read_access_addr /check_read_access_page Hcheck.
    rewrite andb_false_l //.
  Qed.

  Lemma str_ExecI σ r1 r2 w a:
    PC ≠ r1 -> NZ ≠ r1 ->
    PC ≠ r2 -> NZ ≠ r2 ->
    (get_mail_box σ @ (get_current_vm σ)).2.1 ≠ (tpa a) ->
    check_access_page σ (get_current_vm σ) (tpa a) = true ->
    get_reg σ r1 = Some w ->
    get_reg σ r2 = Some a ->
    (str σ r1 r2) = (ExecI, (update_offset_PC (update_memory σ a w) 1)).
  Proof.
    intros ? ? ? ? Hneq Hcheck Hreg1 Hreg2.
    unfold str.
    destruct r1 eqn:Heqn1,r2 eqn:Heqn2 ;try contradiction.
    rewrite /bind /=.
    rewrite Hreg1 Hreg2.
    rewrite /write_memory /check_write_access_addr /check_write_access_page Hcheck.
    rewrite andb_true_l.
    case_bool_decide;last done.
    done.
  Qed.

  Lemma str_FailPageFaultI_str_to_rx σ r1 r2 w a :
    PC ≠ r1 -> NZ ≠ r1 ->
    PC ≠ r2 -> NZ ≠ r2 ->
    (get_mail_box σ @ (get_current_vm σ)).2.1 = (tpa a) ->
    get_reg σ r1 = Some w ->
    get_reg σ r2 = Some a ->
    (str σ r1 r2) = (FailPageFaultI, σ).
  Proof.
    intros ? ? ? ? Heq Hreg1 Hreg2.
    unfold str.
    destruct r1 eqn:Heqn1,r2 eqn:Heqn2 ;try contradiction.
    rewrite Hreg1 Hreg2.
    rewrite /bind /=.
    rewrite /write_memory /check_write_access_addr /check_write_access_page.
    case_bool_decide;first done.
    rewrite andb_false_r //.
  Qed.

  Lemma str_FailPageFaultI_str_to_page σ r1 r2 w a :
    PC ≠ r1 -> NZ ≠ r1 ->
    PC ≠ r2 -> NZ ≠ r2 ->
    check_access_page σ (get_current_vm σ) (tpa a) = false ->
    get_reg σ r1 = Some w ->
    get_reg σ r2 = Some a ->
    (str σ r1 r2) = (FailPageFaultI, σ).
  Proof.
    intros ? ? ? ? Hcheck Hreg1 Hreg2.
    unfold str.
    destruct r1 eqn:Heqn1,r2 eqn:Heqn2 ;try contradiction.
    rewrite Hreg1 Hreg2.
    rewrite /bind /=.
    rewrite /write_memory /check_write_access_addr /check_write_access_page.
    rewrite Hcheck andb_false_l //.
  Qed.

  Lemma cmp_word_ExecI σ1 r w1 w2:
    PC ≠ r -> NZ ≠ r ->
    get_reg σ1 r = Some w1 ->
    (cmp_word σ1 r w2) =
      (ExecI, (update_incr_PC (update_reg σ1 NZ (if (w1 <? w2)%f then W2 else if (w2 <? w1)%f then W0 else W1)))).
  Proof.
    intros.
    unfold cmp_word .
    destruct r;[contradiction|contradiction|].
    rewrite H1.
    simpl.
    destruct ((w1 <? w2)%f).
    rewrite <- (option_state_unpack_preserve_state_Some σ1
                 (update_incr_PC (update_reg σ1 NZ W2)));eauto.
    destruct (w2 <? w1)%f.
    rewrite <- (option_state_unpack_preserve_state_Some σ1
                 (update_incr_PC (update_reg σ1 NZ W0)));eauto.
    done.
  Qed.


  Lemma cmp_reg_ExecI σ1 r1 w1 r2 w2:
    PC ≠ r1 -> NZ ≠ r1 ->
    PC ≠ r2 -> NZ ≠ r2 ->
    get_reg σ1 r1 = Some w1 ->
    get_reg σ1 r2 = Some w2 ->
    (cmp_reg σ1 r1 r2) =
      (ExecI, (update_incr_PC (update_reg σ1 NZ (if (w1 <? w2)%f then W2 else if (w2 <? w1)%f then W0 else W1)))).
  Proof.
    intros.
    unfold cmp_reg.
    destruct r1;[contradiction|contradiction|].
    destruct r2; [contradiction|contradiction|].
    rewrite H3 H4.
    simpl.
    destruct ((w1 <? w2)%f).
    rewrite <- (option_state_unpack_preserve_state_Some σ1
                                                        (update_incr_PC (update_reg σ1 NZ W2)));eauto.
    destruct (w2 <? w1)%f.
    rewrite <- (option_state_unpack_preserve_state_Some σ1
                                                        (update_incr_PC (update_reg σ1 NZ W0)));eauto.
    done.
  Qed.

  Lemma add_ExecI σ1 r1 w1 r2 w2:
    PC ≠ r1 -> NZ ≠ r1 ->
    PC ≠ r2 -> NZ ≠ r2 ->
    get_reg σ1 r1 = Some w1 ->
    get_reg σ1 r2 = Some w2 ->
    (add σ1 r1 r2) = (ExecI, (update_incr_PC (update_reg σ1 r1 (w1 ^+ (finz.to_z w2))%f))).
  Proof.
    intros.
    unfold add.
    destruct r1;[contradiction|contradiction|].
    destruct r2; [contradiction|contradiction|].
    rewrite H3 H4.
    done.
  Qed.

  Lemma sub_ExecI σ1 r1 w1 r2 w2:
    PC ≠ r1 -> NZ ≠ r1 ->
    PC ≠ r2 -> NZ ≠ r2 ->
    get_reg σ1 r1 = Some w1 ->
    get_reg σ1 r2 = Some w2 ->
    (sub σ1 r1 r2) = (ExecI, (update_incr_PC (update_reg σ1 r1 (w1 ^- (finz.to_z w2))%f))).
  Proof.
    intros.
    unfold sub.
    destruct r1;[contradiction|contradiction|].
    destruct r2; [contradiction|contradiction|].
    rewrite H3 H4.
    done.
  Qed.

  Lemma mult_word_ExecI σ1 r1 w1 w2:
    PC ≠ r1 -> NZ ≠ r1 ->
    get_reg σ1 r1 = Some w1 ->
    (lang.mult σ1 r1 w2) = (ExecI, (update_incr_PC (update_reg σ1 r1 (w1 ^* (finz.to_z w2))%f))).
  Proof.
    intros.
    unfold lang.mult.
    destruct r1;[contradiction|contradiction|].
    rewrite H1.
    done.
  Qed.

  Lemma bne_ExecI σ1 w1 r w2:
    PC ≠ r -> NZ ≠ r ->
    (get_reg σ1 r) = Some w2 ->
    (get_reg σ1 NZ) = Some w1 ->
    (bne σ1 r)= (ExecI, if (w1 =? W1)%f then (update_incr_PC σ1) else (update_reg σ1 PC w2)).
  Proof.
    intros.
    unfold bne .
    destruct r;[contradiction|contradiction|].
    rewrite H1 H2.
    simpl.
    destruct (w1 =? W1)%f;eauto.
  Qed.

  Lemma br_ExecI σ1 r w1:
    PC ≠ r -> NZ ≠ r ->
    (get_reg σ1 r) = Some w1 ->
    (br σ1 r) = (ExecI, (update_reg σ1 PC w1)).
  Proof.
    intros.
    unfold br.
    destruct r;[contradiction|contradiction|].
    rewrite H1 //.
  Qed.

End lang_extra.
