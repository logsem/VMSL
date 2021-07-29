From iris.algebra Require Import auth gmap gset.
From iris.proofmode Require Import tactics.
From HypVeri Require Import monad.
From HypVeri Require Export lang machine RAs.


  Definition serialized_memory_descirptor l (r:VMID) ps := [l; (of_imm (encode_vmid r))]++ (map (λ pid, (of_pid pid)) ps).

  Definition serialized_transaction_descriptor (v r:VMID) (wf  l : Word) (ps: list PID) (h : handle ): list Word :=
    [(of_imm (encode_vmid v)); wf; h] ++ (serialized_memory_descirptor l r ps).

  Lemma trans_desc_length{i j wf l ps} des :
    des = serialized_transaction_descriptor i j wf  l ps W0 ->
    (finz.to_z l) = (Z.of_nat (length ps)) ->
    ((Z.of_nat (length des)) = 5 + (finz.to_z l))%Z.
  Proof.
    intros.
    rewrite H /serialized_transaction_descriptor /serialized_memory_descirptor H0.
    simpl.
    rewrite fmap_length.
    lia.
  Qed.


  Lemma mem_desc_valid{ b psd σ}l ps:
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

  Definition transaction_l (v :VMID) (wf: Word) (r:  VMID) (ps: list PID) : transaction_descriptor :=
    (v,None ,wf,r , ps).

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
   parse_transaction_descriptor σ p = Some (i , None, wf,  j , psd).
  Proof.
    intros.
    rewrite /parse_transaction_descriptor /get_memory_with_offset.
    destruct H1 as [_ [? _]].
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
         apply (finz_seq_lookup _ _ y1).
         assert (Hklt: k < length ( map (λ pid : PID, (of_pid pid)) psd)).
         rewrite <-(finz_seq_length _ ((p ^+ 3) ^+ 2)%f).
         apply lookup_lt_is_Some.
         by exists y1.
        rewrite Hlenmapeq in Hklt.
        lia.
        apply (finz_seq_lookup'  _ y1 k _ ) in H3.
        2: { rewrite Hlenmapeq. solve_finz. }
        destruct H3.
        rewrite Hlenmapeq in H3.
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
