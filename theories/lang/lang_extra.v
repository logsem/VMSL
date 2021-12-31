(* This file contains some lemmas only about functions in the operational semantics (lang.v) *)
From HypVeri Require Import machine machine_extra lang.lang.
From iris.algebra Require Import auth gmap gset.
From iris.proofmode Require Import tactics.
From stdpp Require Import list.

Section lang_extra.

Context `{HyperConst : !HypervisorConstants}.
Context `{HyperParams : !HypervisorParameters}.

Implicit Type σ : state.

Lemma check_access_page_mem_eq {σ i a} :
  check_access_page σ i (to_pid_aligned a) =
  check_access_addr σ i a.
Proof.
  rewrite /check_access_addr; done.
Qed.

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
  2:{
    intros ws Hin.
    apply Hws.
    apply elem_of_cons;right;done.
  }
  2:{
    intros ws' Hin.
    apply Hws'.
    apply elem_of_cons;right;done.
  }
  f_equal.
  rewrite (Hws a).
  rewrite (Hws' l) //.
  apply elem_of_cons;left;done.
  apply elem_of_cons;left;done.
Qed.


(* lemmas about transactions *)

  Definition serialized_memory_descirptor l (r:VMID) ps := [l; (of_imm (encode_vmid r))]++ (map (λ pid, (of_pid pid)) ps).

  Definition serialized_transaction_descriptor (v r:VMID) (wf  l : Word) (ps: list PID) (h : Word): list Word :=
    [(of_imm (encode_vmid v)); wf; h] ++ (serialized_memory_descirptor l r ps).

  Lemma trans_desc_length{i j wf l ps wh} des :
    des = serialized_transaction_descriptor i j wf  l ps wh ->
    (finz.to_z l) = (Z.of_nat (length ps)) ->
    ((Z.of_nat (length des)) = 5 + (finz.to_z l))%Z.
  Proof.
    intros.
    rewrite H /serialized_transaction_descriptor /serialized_memory_descirptor H0.
    simpl.
    rewrite fmap_length.
    lia.
  Qed.

  Lemma mem_desc_valid{ b psd σ} l (ps : list PID):
   l =  (length ps) ->
   psd =  (map (λ pid, (of_pid pid)) ps) ->
   (∀ (k : nat) (y1 y2 : Addr),
            finz.seq b (length psd) !! k = Some y1 → psd !! k = Some y2 → get_mem σ !! y1 = Some y2) ->
   map (λ v : Addr,(bind ((get_mem σ) !! v) to_pid )) (finz.seq b l)
   = map (λ pid, Some pid) ps.
  Proof.
    intros.
    generalize dependent b.
    generalize dependent ps.
    generalize dependent psd.
    induction l.
    intros.
    destruct ps .
    rewrite H //=.
    simplify_eq.
    intros.
    destruct ps .
    done.
    simpl in H.
    inversion H.
    simpl.
    destruct psd.
    done.
    rewrite -(IHl psd _ _ _ (b^+1)%f).
    pose proof (H1 0 b (of_pid p)).
    rewrite H2.
    rewrite H3 to_of_pid //.
    done.
    rewrite H0.
    rewrite -> list_lookup_fmap.
    done.
    done.
    rewrite -> fmap_cons in H0.
    inversion H0.
    done.
    intros.
    apply (H1 (k+1)).
    simpl.
    rewrite lookup_cons_ne_0.
    rewrite -H2 //=.
    f_equal.
    lia.
    lia.
    rewrite -H4.
    rewrite lookup_cons_ne_0.
    f_equal.
    lia.
    lia.
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

  Lemma transaction_descriptor_valid{i j wf l psd σ} des p :
    (finz.to_z l) = (Z.of_nat (length psd)) ->
    des = serialized_transaction_descriptor i j wf l psd W0 ->
    seq_in_page (of_pid p) (length des) p ->
    (∀ (k : nat) (y1 y2 : Addr),
             finz.seq (of_pid p) (length des) !! k = Some y1 → des !! k = Some y2 → get_mem σ !! y1 = Some y2) ->
   parse_transaction_descriptor σ p = Some (i , None, wf,  j , list_to_set psd).
  Proof.
    intros.
    rewrite /parse_transaction_descriptor /get_memory_with_offset.
    destruct H1 as [_ [_ [? _]]].
    pose proof (trans_desc_length des H0 H) as Hlen.
    assert (HpSome: ((of_pid p) + 0)%f = Some ((of_pid p) ^+ 0)%f).
    solve_finz.
    rewrite HpSome //=;clear HpSome.
    rewrite (H2 0 ((of_pid p) ^+ 0)%f (encode_vmid i)).
    2: { apply finz_seq_lookup. lia. solve_finz. }
    2: { rewrite H0 /serialized_transaction_descriptor. by list_simplifier. }
    assert (HpSome: ((of_pid p) + 1)%f = Some ((of_pid p) ^+ 1)%f).
    solve_finz.
    rewrite HpSome //=;clear HpSome.
    rewrite (H2 1 ((of_pid p) ^+ 1)%f wf).
    2: { apply finz_seq_lookup. lia. solve_finz. }
    2: { rewrite H0 /serialized_transaction_descriptor. by list_simplifier. }
    assert (HpSome: ((of_pid p) + 2)%f = Some ((of_pid p) ^+ 2)%f).
    solve_finz.
    rewrite HpSome //=;clear HpSome.
    rewrite (H2 2 ((of_pid p) ^+ 2)%f W0).
    2: { apply finz_seq_lookup. lia. solve_finz. }
    2: { rewrite H0 /serialized_transaction_descriptor. by list_simplifier. }
    rewrite  /parse_memory_region_descriptor /get_memory_with_offset.
    assert (HpSome: ((of_pid p) ^+ 3 + 0)%f = Some ((of_pid p) ^+ 3)%f).
    solve_finz.
    rewrite HpSome //=;clear HpSome.
    rewrite (H2 3 ((of_pid p) ^+ 3)%f l).
    2: { apply finz_seq_lookup. lia. solve_finz. }
    2: { rewrite H0 /serialized_transaction_descriptor. by list_simplifier. }
    assert (HpSome: ((of_pid p) ^+ 3 + 1)%f = Some ((of_pid p) ^+ 4)%f).
    solve_finz.
    rewrite HpSome //=;clear HpSome.
    rewrite (H2 4 ((of_pid p) ^+ 4)%f (encode_vmid j)).
    2: { apply finz_seq_lookup. lia. solve_finz. }
    2: { rewrite H0 /serialized_transaction_descriptor. by list_simplifier. }
    rewrite !decode_encode_vmid /parse_list_of_pids /= .
    rewrite (@mem_desc_valid _ (map (λ pid, (of_pid pid)) psd) _ _ psd );eauto.
    2: { lia. }
    2: { intros.
         apply (H2 (k+5) _).
         assert (Hlenmapeq: length ( map (λ pid : PID, (of_pid pid)) psd) = length psd).
        apply fmap_length.
         apply (finz_seq_lookup _ y1).
         assert (Hklt: k < length ( map (λ pid : PID, (of_pid pid)) psd)).
         rewrite <-(finz_seq_length ((p ^+ 3) ^+ 2)%f).
         apply lookup_lt_is_Some.
         by exists y1.
        rewrite Hlenmapeq in Hklt.
        lia.
        apply (finz_seq_lookup' _ y1 k _ ) in H3.
        2: { rewrite Hlenmapeq. solve_finz. }
        destruct H3.
        solve_finz.
        rewrite H0 /serialized_transaction_descriptor.
        simpl.
        rewrite !lookup_cons_ne_0; try lia.
        rewrite -H4.
        f_equal.
        lia.
       }
    rewrite -> sequence_a_map_unit.
    done.
  Qed.

  Lemma transaction_retrieve_descriptor_valid {j handle wf σ} des p :
    des = [of_imm (encode_vmid j); wf; handle; of_imm (encode_vmid (get_current_vm σ))]->
    seq_in_page (of_pid p) (length des) p ->
    (∀ (k : nat) (y1 y2 : Addr),
             finz.seq (of_pid p) (length des) !! k = Some y1 → des !! k = Some y2 → get_mem σ !! y1 = Some y2) ->
    parse_transaction_descriptor_retrieve σ p = Some (j, Some handle, wf, (get_current_vm σ), ∅).
  Proof.
    intros H H0 H1.
    rewrite /parse_transaction_descriptor_retrieve /get_memory_with_offset.
    destruct H0 as [_ [? _]].
    simpl.
    pose proof (last_addr_in_bound p) as HSome.
    assert ( ((of_pid p) + 0)%f = Some ((of_pid p) ^+ 0)%f) as ->.
    solve_finz.
    rewrite (H1 0 ((of_pid p) ^+ 0)%f (encode_vmid j)).
    2: { apply finz_seq_lookup. rewrite H /=. lia. solve_finz. }
    2: { rewrite H. by list_simplifier. }
    assert (((of_pid p) + 1)%f = Some ((of_pid p) ^+ 1)%f) as ->.
    solve_finz.
    rewrite (H1 1 ((of_pid p) ^+ 1)%f wf).
    2: { apply finz_seq_lookup. rewrite H /=. lia. solve_finz. }
    2: { rewrite H . by list_simplifier. }
    assert (((of_pid p) + 2)%f = Some ((of_pid p) ^+ 2)%f) as ->.
    solve_finz.
    rewrite (H1 2 ((of_pid p) ^+ 2)%f handle).
    2: { apply finz_seq_lookup. rewrite H /=. lia. solve_finz. }
    2: { rewrite H. by list_simplifier. }
    rewrite !decode_encode_vmid /=.
    reflexivity.
  Qed.


  (* lemmas about taking a step *)


  Lemma reducible_normal{σ} i instr ai wi :
   (get_current_vm σ) = i ->
   check_access_addr σ i ai = true ->
   get_reg σ PC = Some ai ->
   get_mem σ !! ai = Some wi ->
   decode_instruction wi = Some (instr) ->
   ∃ m' σ', step ExecI σ m' σ'.
  Proof.
    intros.
    remember (exec instr σ) as ex.
    exists ex.1 ,ex.2 .
    apply step_exec_normal with ai wi instr;subst i ;eauto.
    + by rewrite /is_valid_PC H1 /= H0.
    + by rewrite /get_memory H0.
   Qed.

  Lemma step_ExecI_normal {σ m' σ' } i instr ai wi  :
   step ExecI σ m' σ'->
   (get_current_vm σ) = i ->
   check_access_addr σ i ai = true ->
   get_reg σ PC = Some ai ->
   get_mem σ !! ai = Some wi ->
   decode_instruction wi = Some (instr) ->
   (exec instr σ).1 = m' ∧ (exec instr σ).2 = σ'.
  Proof.
    intros HstepP Heqi Hacc HPC Hmem Hdecode.
    inversion HstepP as
        [ σ1' Hinvalid
        | σ1' Ha w _ Hdecode' Hmem' Hinvalid_ins
        | σ1'  ? ? ? ? Hvalid Hreg2 Hmem2 Hdecode2 Hexec Hcontrol];
      simplify_eq /=.
    + (*Fail*)
      by rewrite /is_valid_PC //= HPC Hacc in Hinvalid.
    + rewrite /get_memory Hacc Hmem in Hmem'.
      inversion Hmem';subst.
      rewrite Hdecode // in Hinvalid_ins.
    + (* Normal. *)
      (* eliminate Hmem2 *)
      rewrite /get_memory  Hacc Hmem in Hmem2 .
      inversion Hmem2;subst wi; clear Hmem2.
      (* eliminate Hdecode2 *)
      by rewrite Hdecode in Hdecode2;inversion Hdecode2;subst i0.
  Qed.

 Lemma option_state_unpack_preserve_state_Some σ1 σ2 (σ2': option state) :
   σ2' = Some σ2 ->  (ExecI, σ2) = (option_state_unpack σ1 σ2').
  Proof.
    intros.
    destruct σ2' eqn:Heqn.
    inversion H; subst.
    done.
    done.
  Qed.

  Lemma mov_word_ExecI σ1 r w :
   PC ≠ r -> NZ ≠ r -> (mov_word σ1 r w)= (ExecI, (update_incr_PC (update_reg σ1 r w))).
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
   (mov_reg σ1 r1 r2)= (ExecI, (update_incr_PC (update_reg σ1 r1 w))).
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

  Lemma ldr_ExecI σ1 r1 r2 a w:
   PC ≠ r1 -> NZ ≠ r1 ->
   PC ≠ r2 -> NZ ≠ r2 ->
   (get_mail_boxes σ1 !!! get_current_vm σ1).1 ≠ (to_pid_aligned a) ->
   (get_reg σ1 r2) = Some a ->
   get_memory σ1 a = Some w ->
   (ldr σ1 r1 r2)= (ExecI, (update_incr_PC (update_reg σ1 r1 w))).
  Proof.
    intros.
    unfold ldr.
    destruct r1 eqn:Heqn1,r2 eqn:Heqn2 ;try contradiction.
    unfold bind.
    simpl.
    rewrite H4 H5.
    destruct (get_mail_boxes σ1 !!! get_current_vm σ1).
    simpl in H3.
    destruct (decide (to_pid_aligned a = p)).
    done.
    done.
  Qed.

  Lemma ldr_FailPageFaultI_ldr_from_tx σ1 r1 r2 a :
   PC ≠ r1 -> NZ ≠ r1 ->
   PC ≠ r2 -> NZ ≠ r2 ->
   (get_mail_boxes σ1 !!! get_current_vm σ1).1 = (to_pid_aligned a) ->
   (get_reg σ1 r2) = Some a ->
   (ldr σ1 r1 r2)= (FailPageFaultI, σ1).
  Proof.
    intros.
    unfold ldr.
    destruct r1 eqn:Heqn1,r2 eqn:Heqn2 ;try contradiction.
    rewrite H4.
    destruct (get_mail_boxes σ1 !!! get_current_vm σ1).
    simpl in H3.
    destruct (decide (to_pid_aligned a = p)).
    done.
    done.
  Qed.

 Lemma ldr_FailPageFaultI_ldr_from_page σ1 r1 r2 a :
   PC ≠ r1 -> NZ ≠ r1 ->
   PC ≠ r2 -> NZ ≠ r2 ->
   check_access_page σ1 (get_current_vm σ1) (tpa a) = false->
   (get_reg σ1 r2) = Some a ->
   (ldr σ1 r1 r2)= (FailPageFaultI, σ1).
  Proof.
    intros.
    unfold ldr.
    destruct r1 eqn:Heqn1,r2 eqn:Heqn2 ;try contradiction.
    rewrite H4.
    destruct (get_mail_boxes σ1 !!! get_current_vm σ1).
    simpl in H3.
    destruct (decide (to_pid_aligned a = p)).
    done.
    rewrite /get_memory /check_access_addr H3.
    done.
  Qed.

  Lemma str_ExecI σ1 r1 r2 w a:
   PC ≠ r1 -> NZ ≠ r1 ->
   PC ≠ r2 -> NZ ≠ r2 ->
   (get_mail_boxes σ1 !!! get_current_vm σ1).2.1 ≠ (to_pid_aligned a) ->
   (get_reg σ1 r1) = Some w ->
   (get_reg σ1 r2) = Some a ->
   check_access_addr σ1 (get_current_vm σ1) a = true ->
   (str σ1 r1 r2)= (ExecI, (update_offset_PC (update_memory_unsafe σ1 a w) 1)).
  Proof.
    intros.
    unfold str.
    destruct r1 eqn:Heqn1,r2 eqn:Heqn2 ;try contradiction.
    unfold bind.
    simpl.
    rewrite H4 H5.
    destruct ((get_mail_boxes σ1 !!! get_current_vm σ1)).
    destruct p.
    simpl in H3.
    destruct (decide(to_pid_aligned a = p)).
    done.
    rewrite /update_memory /update_incr_PC /update_memory H6.
    done.
  Qed.

  Lemma str_FailPageFaultI_str_to_rx σ1 r1 r2 w a :
   PC ≠ r1 -> NZ ≠ r1 ->
   PC ≠ r2 -> NZ ≠ r2 ->
   (get_mail_boxes σ1 !!! get_current_vm σ1).2.1 = (to_pid_aligned a) ->
   (get_reg σ1 r1) = Some w ->
   (get_reg σ1 r2) = Some a ->
   (str σ1 r1 r2)= (FailPageFaultI, σ1).
  Proof.
    intros.
    unfold str.
    destruct r1 eqn:Heqn1,r2 eqn:Heqn2 ;try contradiction.
    rewrite H4 H5.
    destruct (get_mail_boxes σ1 !!! get_current_vm σ1).
    simpl in H3.
    unfold bind.
    simpl.
    destruct p.
    destruct (decide (tpa a = p)).
    done.
    done.
  Qed.

 Lemma str_FailPageFaultI_str_to_page σ1 r1 r2 w a :
   PC ≠ r1 -> NZ ≠ r1 ->
   PC ≠ r2 -> NZ ≠ r2 ->
   check_access_page σ1 (get_current_vm σ1) (tpa a) = false->
   (get_reg σ1 r1) = Some w ->
   (get_reg σ1 r2) = Some a ->
   (str σ1 r1 r2)= (FailPageFaultI, σ1).
  Proof.
    intros.
    unfold str.
    destruct r1 eqn:Heqn1,r2 eqn:Heqn2 ;try contradiction.
    rewrite H4 H5.
    destruct (get_mail_boxes σ1 !!! get_current_vm σ1).
    simpl in H3.
    rewrite /bind /=.
    destruct p.
    destruct (decide (to_pid_aligned a = p)).
    done.
    rewrite /update_memory  /check_access_addr H3 //.
  Qed.

  Lemma cmp_word_ExecI σ1 r w1 w2:
   PC ≠ r -> NZ ≠ r ->
   (get_reg σ1 r) = Some w1 ->
   (cmp_word σ1 r w2)= (ExecI, (update_incr_PC (update_reg σ1 NZ
            (if (w1 <? w2)%f then W2 else if (w2 <? w1)%f then W0 else W1)))).
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
   (get_reg σ1 r1) = Some w1 ->
   (get_reg σ1 r2) = Some w2 ->
   (cmp_reg σ1 r1 r2)= (ExecI, (update_incr_PC (update_reg σ1 NZ
            (if (w1 <? w2)%f then W2 else if (w2 <? w1)%f then W0 else W1)))).
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
   (get_reg σ1 r1) = Some w1 ->
   (get_reg σ1 r2) = Some w2 ->
   (add σ1 r1 r2)= (ExecI, (update_incr_PC (update_reg σ1 r1 (w1 ^+ (finz.to_z w2))%f))).
  Proof.
    intros.
    unfold add.
    (* destruct r1;[contradiction|contradiction|]. *)
    (* destruct r2; [contradiction|contradiction|]. *)
    (* TODO: add validity check of regs in opsem *)
    rewrite H3 H4.
    done.
  Qed.

  Lemma sub_ExecI σ1 r1 w1 r2 w2:
   PC ≠ r1 -> NZ ≠ r1 ->
   PC ≠ r2 -> NZ ≠ r2 ->
   (get_reg σ1 r1) = Some w1 ->
   (get_reg σ1 r2) = Some w2 ->
   (sub σ1 r1 r2)= (ExecI, (update_incr_PC (update_reg σ1 r1 (w1 ^- (finz.to_z w2))%f))).
  Proof.
    intros.
    unfold sub.
    (* destruct r1;[contradiction|contradiction|]. *)
    (* destruct r2; [contradiction|contradiction|]. *)
    (* TODO: add validity check of regs in opsem *)
    rewrite H3 H4.
    done.
  Qed.

  Lemma mult_word_ExecI σ1 r1 w1 w2:
   PC ≠ r1 -> NZ ≠ r1 ->
   (get_reg σ1 r1) = Some w1 ->
   (lang.mult σ1 r1 w2)= (ExecI, (update_incr_PC (update_reg σ1 r1 (w1 ^* (finz.to_z w2))%f))).
  Proof.
    intros.
    unfold lang.mult.
    (* destruct r1;[contradiction|contradiction|]. *)
    (* destruct r2; [contradiction|contradiction|]. *)
    (* TODO: add validity check of regs in opsem *)
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
   (br σ1 r)= (ExecI,  (update_reg σ1 PC w1)).
  Proof.
    intros.
    unfold br.
    destruct r;[contradiction|contradiction|].
    rewrite H1 //.
  Qed.

End lang_extra.
