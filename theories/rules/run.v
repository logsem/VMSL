From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import machine_extra lifting rules.rules_base.
From HypVeri.algebra Require Import base reg mem pagetable mailbox base_extra.
From HypVeri.lang Require Import lang_extra reg_extra current_extra.
Require Import stdpp.fin.
Require Import stdpp.listset_nodup.

Section run.

Context `{hypparams:HypervisorParameters}.
  
Context `{vmG: !gen_VMG Σ}.

Lemma run {E w1 w2 w3 q s p_tx R R' Q P P'} ai i :
  let T := (▷ (PC @@ V0 ->r ai)
            ∗ ▷ (ai ->a w1)
            ∗ ▷ (V0 -@{q}A> s)
            ∗ ▷ (TX@ V0 := p_tx)
            ∗ ▷ (R0 @@ V0 ->r w2)
            ∗ ▷ (R1 @@ V0 ->r w3))%I
  in
  let T' := ((PC @@ V0 ->r (ai ^+ 1)%f)
               ∗ ai ->a w1
               ∗ V0 -@{q}A> s
               ∗ TX@ V0 := p_tx
               ∗ R0 @@ V0 ->r w2
               ∗ R1 @@ V0 ->r w3)%I
  in
  (tpa ai) ∈ s ->
  (tpa ai) ≠ p_tx ->
  i ≠ V0 ->
  decode_instruction w1 = Some Hvc ->
  decode_hvc_func w2 = Some Run ->
  decode_vmid w3 = Some i ->
  {SS{{ T ∗ ▷ (VMProp i (Q) (1/2)%Qp)
          ∗ ▷ (VMProp V0 P 1%Qp)
          ∗ ▷ (T' ∗ R ∗ VMProp V0 P' (1/2)%Qp -∗ (Q ∗ R'))
          ∗ ▷ R }}}
    ExecI @ V0 ;E
    {{{ RET (true, ExecI); R' ∗ VMProp V0 P' (1/2)%Qp}}}.
Proof.
  simpl.
  iIntros (Hin Hnottx Hneq_v Hdecode Hhvc Hvmid ϕ) "[(>Hpc & >Hapc & >Hacc & >tx & >Hr0 & >Hr1) (HPropi & HPropz & Himpl & HR)] Hϕ".
  iApply (sswp_lift_atomic_step ExecI); [done|].
  iIntros (n σ1) "%Hsche Hσ".
  rewrite /scheduled in Hsche.
  simpl in Hsche.
  rewrite /scheduler in Hsche.
  apply bool_decide_unpack in Hsche as Hcur.
  clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(%Hneq & Hmemown & Hreg & Hmb & ? & Hown & Haccessown & Hrest)".
  (* valid regs *)
  iDestruct (gen_reg_valid1 PC V0 ai Hcur with "Hreg Hpc") as "%Hpc".
  iDestruct (gen_reg_valid1 R0 V0 w2 Hcur with "Hreg Hr0") as "%Hr0".
  iDestruct (gen_reg_valid1 R1 V0 w3 Hcur with "Hreg Hr1") as "%Hr1".
  (* valid pt *)
  iDestruct (access_agree_check_true (tpa ai)  with "Haccessown Hacc") as %Hacc;first exact Hin.
  iDestruct (mb_valid_tx with "Hmb tx") as %Htx.
  subst p_tx.
  (* valid mem *)
  iDestruct (gen_mem_valid ai w1 with "Hmemown Hapc") as "%Hmem".
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal V0 Hvc ai w1);eauto.
  - iModIntro.
    iIntros (m2 σ2) "[%U PAuth] %HstepP".
    apply (step_ExecI_normal V0 Hvc ai w1) in HstepP; eauto.
    remember (exec Hvc σ1) as c2 eqn:Heqc2.
    rewrite /exec /hvc in Heqc2; eauto.
    rewrite  Hr0 /= Hhvc /run Hr1 in Heqc2.
    simpl in Heqc2.
    rewrite /unpack_hvc_result_yield Hvmid in Heqc2.
    simpl in Heqc2.
    rewrite /is_primary Hcur in Heqc2.
    destruct HstepP as [Hstep1 Hstep2].
    case_bool_decide;last done.
    subst c2.
    simpl in Hstep1, Hstep2.
    subst σ2 m2.
    simpl.
    rewrite /gen_vm_interp /update_incr_PC.
    rewrite (preserve_get_mb_gmap σ1).
    rewrite (preserve_get_rx_gmap σ1).
    rewrite (preserve_get_own_gmap σ1).
    rewrite (preserve_get_access_gmap σ1).
    rewrite (preserve_get_excl_gmap σ1).
    rewrite (preserve_get_trans_gmap σ1).
    rewrite (preserve_get_hpool_gset σ1).
    rewrite (preserve_get_retri_gmap σ1).
    rewrite (preserve_inv_trans_pgt_consistent σ1).
    rewrite (preserve_inv_trans_wellformed σ1).
    all: try rewrite p_upd_id_mb p_upd_pc_mb //.
    all: try rewrite p_upd_id_pgt p_upd_pc_pgt //.
    all: try rewrite p_upd_id_trans p_upd_pc_trans //.
    rewrite p_upd_id_mem p_upd_pc_mem.
    iFrame.
    iDestruct ((gen_reg_update1_global PC V0 ai (ai ^+ 1)%f) with "Hreg Hpc") as "HpcUpd".
    rewrite (preserve_get_reg_gmap (update_offset_PC σ1 1) (update_current_vmid _ _));last rewrite p_upd_id_reg //.
    rewrite ->(update_offset_PC_update_PC1 _ V0 ai 1); auto.
    + iDestruct (VMProp_update V0 U P P' with "PAuth HPropz") as "HTemp".
      iMod "HpcUpd".
      iMod "HTemp".
      iDestruct "HTemp" as "[PAuth HPropz]".
      iModIntro.
      iDestruct "HpcUpd" as "[? Hpc]".
      iFrame.      
      iSplitL "PAuth".
      by iExists P'.
      iSplit; first done.
      rewrite /just_scheduled_vms /just_scheduled.
      assert (filter
                (λ id : vmid,
                        base.negb (scheduled σ1 id) &&
                        scheduled (update_current_vmid (update_offset_PC σ1 1) i) id = true)
                (seq 0 n) = [fin_to_nat i]) as ->.
      {
        rewrite /scheduled /machine.scheduler Hneq //= /scheduler.
        rewrite /update_current_vmid //=.
        pose proof (NoDup_seq 0 vm_count) as ND.
        pose proof (NoDup_singleton ((@fin_to_nat (@vm_count H) i))) as ND'.
        set f := (λ id : nat, base.negb (bool_decide ((@fin_to_nat (@vm_count H) σ1.1.1.2) = id)) && bool_decide ((@fin_to_nat (@vm_count H) i) = id) = true).
        pose proof (NoDup_filter f _ ND) as ND''.
        assert (f i) as Prf.
        {
          subst f.
          simpl.
          unfold base.negb.
          repeat case_bool_decide; eauto.
          rewrite Hcur in H1.
          exfalso.
          apply Hneq_v.
          symmetry.
          apply fin_to_nat_inj.
          done.
        }
        assert (In (@fin_to_nat (@vm_count H) i) (seq 0 vm_count)) as Prf'.
        {
          rewrite <-elem_of_list_In.
          rewrite elem_of_seq.
          split.
          - solve_finz.
          - rewrite plus_O_n.
            pose proof (fin_to_nat_lt i).
            auto.
        }
        rewrite <-elem_of_list_In in Prf'.
        assert (In (@fin_to_nat (@vm_count H) i) (filter f (seq 0 vm_count))) as Prf''.
        {
          rewrite <-elem_of_list_In.
          by apply (iffRL (elem_of_list_filter f (seq 0 vm_count) i)).
        }
        rewrite <-elem_of_list_In in Prf''.
        assert (forall x, x ≠ (@fin_to_nat (@vm_count H) i) -> not (In x (filter f (seq 0 vm_count)))) as excl.
        {
          intros x neq c.
          rewrite <-elem_of_list_In in c.
          rewrite ->elem_of_list_filter in c.
          destruct c as [c' _].
          subst f.
          simpl in c'.
          unfold base.negb in c'.
          case_match.
          - by rewrite andb_false_l in c'.
          - rewrite andb_true_l in c'.
            apply neq.
            rewrite ->bool_decide_eq_true in c'.
            by symmetry.
        }
        apply Permutation_length_1_inv.
        apply NoDup_Permutation; auto.
        intros x'.
        split.
        - intros T.
          rewrite ->elem_of_list_singleton in T.
          rewrite T; auto.
        - intros T.
          rewrite ->elem_of_list_singleton.
          rewrite ->elem_of_list_In in T.
          destruct (decide (x' = i)) as [? | n']; auto.
          exfalso.
          by apply (excl x' n').
      }
      iSimpl.
      assert ((negb (scheduled (update_current_vmid (update_offset_PC σ1 1) i) V0) && true = true)) as ->.
      {
        rewrite andb_true_r.
        rewrite /scheduled /machine.scheduler //= /scheduler.
        rewrite /update_current_vmid //=.
        apply eq_true_not_negb.
        intros c.
        rewrite ->bool_decide_eq_true in c.
        apply Hneq_v.
        apply fin_to_nat_inj.
        done.
      }
      iDestruct (VMProp_split with "HPropz") as "[HPropz1 HPropz2]".
      iDestruct ("Himpl" with "[Hpc Hapc Hacc Hr0 Hr1 HR HPropz1 tx]") as "[Q R']".
      iFrame.
      iSplitR "Hϕ R' HPropz2".
      iSplit; last done.
      iExists (Q)%I.
      iFrame.
      iApply ("Hϕ" with "[R' HPropz2]").
      iFrame.
    + apply get_reg_gmap_get_reg_Some; auto.
Qed.

Lemma run_not_primary {E w1 w2 q s p_tx } ai i :
  (tpa ai) ∈ s ->
  (tpa ai) ≠ p_tx ->
  i ≠ V0 ->
  decode_instruction w1 = Some Hvc ->
  decode_hvc_func w2 = Some Run ->
  {SS{{ ▷ (PC @@ i ->r ai)
            ∗ ▷ (ai ->a w1)
            ∗ ▷ (i -@{q}A> s)
            ∗ ▷ (TX@ i := p_tx)
            ∗ ▷ (R0 @@ i ->r w2)
            ∗ ▷ (∃r, R2 @@ i ->r r)
            }}}
    ExecI @ i ;E
    {{{ RET (false, ExecI); PC @@ i ->r (ai ^+ 1)%f
               ∗ ai ->a w1
               ∗ i -@{q}A> s
               ∗ TX@ i := p_tx
               ∗ R0 @@ i ->r (encode_hvc_ret_code Error)
               ∗ R2 @@ i ->r (encode_hvc_error Denied) }}}.
  Admitted.


Lemma run_invalid_vmid {E w1 w2 w3 q s p_tx } ai i :
  (tpa ai) ∈ s ->
  (tpa ai) ≠ p_tx ->
  i ≠ V0 ->
  decode_instruction w1 = Some Hvc ->
  decode_hvc_func w2 = Some Run ->
  decode_vmid w3 = None ->
  {SS{{ ▷ (PC @@ V0 ->r ai)
            ∗ ▷ (ai ->a w1)
            ∗ ▷ (V0 -@{q}A> s)
            ∗ ▷ (TX@ V0 := p_tx)
            ∗ ▷ (R0 @@ V0 ->r w2)
            ∗ ▷ (R1 @@ V0 ->r w3)
            ∗ ▷ (∃r, R2 @@ V0 ->r r)
            }}}
    ExecI @ V0 ;E
    {{{ RET (false, ExecI); PC @@ V0 ->r (ai ^+ 1)%f
               ∗ ai ->a w1
               ∗ V0 -@{q}A> s
               ∗ TX@ V0 := p_tx
               ∗ R0 @@ V0 ->r (encode_hvc_ret_code Error)
               ∗ R1 @@ V0 ->r w3
               ∗ R2 @@ V0 ->r (encode_hvc_error InvParam) }}}.
  Admitted.

Lemma run_primay {E w1 w2 w3 q s p_tx} ai :
  (tpa ai) ∈ s ->
  (tpa ai) ≠ p_tx ->
  decode_instruction w1 = Some Hvc ->
  decode_hvc_func w2 = Some Run ->
  decode_vmid w3 = Some V0 ->
  {SS{{ ▷ (PC @@ V0 ->r ai)
            ∗ ▷ (ai ->a w1)
            ∗ ▷ (V0 -@{q}A> s)
            ∗ ▷ (TX@ V0 := p_tx)
            ∗ ▷ (R0 @@ V0 ->r w2)}}}
    ExecI @ V0 ;E
    {{{ RET (false, ExecI); PC @@ V0 ->r (ai ^+ 1)%f
               ∗ ai ->a w1
               ∗ V0 -@{q}A> s
               ∗ TX@ V0 := p_tx
               ∗ R0 @@ V0 ->r w2}}}.
  Admitted.


End run.
