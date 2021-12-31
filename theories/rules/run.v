From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import lifting rules.rules_base.
From HypVeri.algebra Require Import base reg mem pagetable base_extra.
From HypVeri.lang Require Import lang_extra reg_extra current_extra.
Require Import stdpp.fin.
Require Import stdpp.listset_nodup.

Section run.

Context `{hypparams:HypervisorParameters}.
  
Context `{vmG: !gen_VMG Σ}.

Lemma run {z w1 w2 w3 q s E R R' Q P P' i'} ai i :
  let T := (▷ (PC @@ z ->r ai)
            ∗ ▷ (ai ->a w1)
            ∗ ▷ ((tpa ai) -@{q}A> [s])
            ∗ ▷ (R0 @@ z ->r w2)
            ∗ ▷ (R1 @@ z ->r w3))%I
  in
  let T' := ((PC @@ z ->r (ai ^+ 1)%f)
               ∗ (ai ->a w1)
               ∗ ((tpa ai) -@{q}A> [s])
               ∗ (R0 @@ z ->r w2)
               ∗ (R1 @@ z ->r w3))%I
  in
  decode_instruction w1 = Some Hvc ->
  z ∈ s ->
  fin_to_nat z = 0 ->
  fin_to_nat i = i' ->
  i' ≠ 0 ->
  decode_hvc_func w2 = Some Run ->
  decode_vmid w3 = Some i ->
  {SS{{ T ∗ ▷ (VMProp i (Q ∗ VMProp z P' (1/2)%Qp) (1/2)%Qp)
          ∗ ▷ (VMProp z P 1%Qp)
          ∗ ▷ (T' ∗ R -∗ (Q ∗ R')) 
          ∗ ▷ R }}}
    ExecI @ z ;E
    {{{ RET (true, ExecI); R' ∗ VMProp z P' (1/2)%Qp}}}.
Proof.
  simpl.
  iIntros (Hdecode Hin Hz Hi Hiz Hhvc Hvmid ϕ) "[(>Hpc & >Hapc & >Hacc & >Hr0 & >Hr1) (HPropi & HPropz & Himpl & HR)] Hϕ".
  iApply (sswp_lift_atomic_step ExecI); [done|].
  iIntros (n σ1) "%Hsche Hσ".
  rewrite /scheduled in Hsche.
  simpl in Hsche.
  rewrite /scheduler in Hsche.
  apply bool_decide_unpack in Hsche as Hcur.
  clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(%Hneq & Hmemown & Hregown & Hrx & Hown & Hmb & Haccessown & Hrest)".
  (* valid regs *)
  iDestruct (gen_reg_valid1 PC z ai Hcur with "Hregown Hpc") as "%Hpc".
  iDestruct (gen_reg_valid1 R0 z w2 Hcur with "Hregown Hr0") as "%Hr0".
  iDestruct (gen_reg_valid1 R1 z w3 Hcur with "Hregown Hr1") as "%Hr1".
  (* valid pt *)
  iDestruct (access_agree_check_true (tpa ai)  with "Haccessown Hacc") as %Hacc;eauto.
  (* valid mem *)
  iDestruct (gen_mem_valid ai w1 with "Hmemown Hapc") as "%Hmem".
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal z Hvc ai w1);eauto.
  - iModIntro.
    iIntros (m2 σ2) "[%U PAuth] %HstepP".
    apply (step_ExecI_normal z Hvc ai w1) in HstepP; eauto.
    remember (exec Hvc σ1) as c2 eqn:Heqc2.
    rewrite /exec /hvc in Heqc2; eauto.
    rewrite  Hr0 Hhvc /run Hr1 in Heqc2.
    simpl in Heqc2.
    rewrite /unpack_hvc_result_yield Hvmid in Heqc2.
    simpl in Heqc2.
    rewrite /is_primary Hcur Hz in Heqc2.
    destruct (0 =? 0) eqn:Hvmz; [|done].
    destruct HstepP as [Hstep1 Hstep2].
    simplify_eq.
    simpl.
    rewrite /gen_vm_interp /update_incr_PC.
    rewrite (preserve_get_mb_gmap _ σ1).
    rewrite (preserve_get_rx_gmap _ σ1).
    all: try rewrite update_current_vmid_preserve_mb update_offset_PC_preserve_mb //.
    rewrite (preserve_get_owned_gmap _ σ1).
    rewrite (preserve_get_access_gmap _ σ1).
    rewrite (preserve_get_trans_gmap _ σ1).
    rewrite (preserve_get_hpool_gset _ σ1).
    rewrite (preserve_get_retri_gmap _ σ1).
    rewrite (preserve_inv_trans_hpool_consistent _ σ1).
    rewrite (preserve_inv_trans_pgt_consistent _ σ1).
    rewrite (preserve_inv_trans_pg_num_ub _ σ1).
    all: try rewrite update_current_vmid_preserve_pgt update_offset_PC_preserve_pgt //.
    all: try rewrite update_current_vmid_preserve_trans update_offset_PC_preserve_trans //.
    rewrite update_current_vmid_preserve_mem update_offset_PC_preserve_mem.
    iFrame "Hrest Hrx Hmb Hmemown Haccessown Hown".
    iDestruct ((gen_reg_update1_global PC (get_current_vm σ1) ai (ai ^+ 1)%f) with "Hregown Hpc") as "HpcUpd".
    rewrite (preserve_get_reg_gmap (update_current_vmid _ _) (update_offset_PC σ1 1));last rewrite update_current_vmid_preserve_reg //.
    rewrite ->(update_offset_PC_update_PC1 _ (get_current_vm σ1) ai 1); auto.
    + rewrite Hz.
      iDestruct (VMProp_update 0 U P P' with "PAuth HPropz") as "HTemp".
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
                (seq 0 vm_count) = [fin_to_nat i]) as ->.
      {
        rewrite /scheduled /machine.scheduler //= /scheduler Hz.
        rewrite /update_current_vmid //=.
        pose proof (NoDup_seq 0 vm_count) as ND.
        pose proof (NoDup_singleton ((@fin_to_nat (@vm_count H) i))) as ND'.
        set f := (λ id : nat, base.negb (bool_decide (0 = id)) && bool_decide ((@fin_to_nat (@vm_count H) i) = id) = true).
        pose proof (NoDup_filter f _ ND) as ND''.
        assert (f i) as Prf.
        {
          subst f.
          simpl.
          unfold base.negb.
          repeat case_bool_decide; done.
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
          destruct (decide (x' = i)) as [? | n]; auto.
          exfalso.
          by apply (excl x' n).
      }
      iSimpl.
      assert ((negb (scheduled (update_current_vmid (update_offset_PC σ1 1) i) 0) && true = true)) as ->.
      {
        rewrite andb_true_r.
        rewrite /scheduled /machine.scheduler //= /scheduler.
        rewrite /update_current_vmid //=.
        apply eq_true_not_negb.
        intros c.
        rewrite ->bool_decide_eq_true in c.
        by apply Hiz.
      }
      iDestruct (VMProp_split with "HPropz") as "[HPropz1 HPropz2]".
      iDestruct ("Himpl" with "[Hpc Hapc Hacc Hr0 Hr1 HR]") as "[Q R']".
      iFrame.
      iSplitR "Hϕ R' HPropz1".
      iSplit; last done.
      iExists (Q ∗ VMProp 0 P' (1 / 2))%I.      
      iFrame "HPropi".
      iNext.
      iFrame "HPropz2 Q".
      iApply ("Hϕ" with "[R' HPropz1]").
      iFrame.
    + apply get_reg_gmap_get_reg_Some; auto.
Qed.
End run.
