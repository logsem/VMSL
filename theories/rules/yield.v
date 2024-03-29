From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Import machine_extra lifting rules.rules_base.
From HypVeri.algebra Require Import base reg mem pagetable mailbox base_extra.
From HypVeri.lang Require Import lang_extra reg_extra current_extra.
Require Import stdpp.fin.
Require Import stdpp.listset_nodup.

Section yield.

Context `{hypparams:HypervisorParameters}.
Context `{vmG: !gen_VMG Σ}.

Lemma yield {E w1 w2 a_ b_ q s p_tx R' Q P i} ai R P':
  let T := (▷ (PC @@ i ->r ai)
              ∗ ▷ (ai ->a w1)
              ∗ ▷ (i -@{q}A> s)
              ∗ ▷ (TX@ i := p_tx)
              ∗ ▷ (R0 @@ i ->r w2)
              ∗ ▷ (R0 @@ V0 ->r a_)
              ∗ ▷ (R1 @@ V0 ->r b_))%I
  in
  let T' := (PC @@ i ->r (ai ^+ 1)%f
               ∗ ai ->a w1
               ∗ i -@{q}A> s
               ∗ TX@ i := p_tx
               ∗ R0 @@ i ->r w2
               ∗ R0 @@ V0 ->r (encode_hvc_func Yield)
               ∗ R1 @@ V0 ->r (encode_vmid i))%I
  in
  (tpa ai) ∈ s ->
  (tpa ai) ≠ p_tx ->
  i ≠ V0 ->
  decode_instruction w1 = Some Hvc ->
  decode_hvc_func w2 = Some Yield ->
  {SS{{ T ∗ ▷ (VMProp V0 Q (1/2)%Qp)
          ∗ ▷ (VMProp i P 1%Qp)
          ∗ ▷ (T' ∗ R ∗ VMProp i P' (1/2)%Qp -∗ (Q ∗ R'))
          ∗ ▷ R }}}
    ExecI @ i;E
    {{{ RET (true, ExecI); R' ∗ VMProp i P' (1/2)%Qp }}}.
Proof.
  simpl.
  iIntros (Hin Hnottx Hneq_v Hdecode Hhvc ϕ) "[(>Hpc & >Hapc & >Hacc & >tx & >Hr0 & >Hr0' & >Hr1) (HPropz & HPropi & Himpl & HR)] Hϕ".
  iApply (sswp_lift_atomic_step ExecI); [done|].
  iIntros (n σ1) "%Hsche Hσ".
  rewrite /scheduled in Hsche.
  simpl in Hsche.
  rewrite /scheduler in Hsche.
  apply bool_decide_unpack in Hsche as Hcur.
  clear Hsche.
  apply fin_to_nat_inj in Hcur.
  iModIntro.
  iDestruct "Hσ" as "(%Hneq & Hmemown & Hregown & Hmb & ? & Hown & Haccessown & Hrest)".
  (* valid regs *)
  iDestruct (gen_reg_valid1 PC i ai Hcur with "Hregown Hpc") as "%Hpc".
  iDestruct (gen_reg_valid1 R0 i w2 Hcur with "Hregown Hr0") as "%Hr0".
  iDestruct (gen_reg_valid_global1 R0 V0 a_ with "Hregown Hr0'") as "%Hr0'".
  iDestruct (gen_reg_valid_global1 R1 V0 b_ with "Hregown Hr1") as "%Hr1".
  (* valid pt *)
  iDestruct (access_agree_check_true with "Haccessown Hacc") as %Hacc;first exact Hin.
  iDestruct (mb_valid_tx with "Hmb tx") as %Htx.
  subst p_tx.
  (* valid mem *)
  iDestruct (gen_mem_valid ai w1 with "Hmemown Hapc") as "%Hmem".
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal i Hvc ai w1);eauto.
  - iModIntro.
    iIntros (m2 σ2) "[%U PAuth] %HstepP".
    apply (step_ExecI_normal i Hvc ai w1) in HstepP; eauto.
    remember (exec Hvc σ1) as c2 eqn:Heqc2.
    rewrite /exec /hvc in Heqc2; eauto.
    rewrite Hr0 /= Hhvc /= /yield in Heqc2.
    rewrite /is_primary /update_reg p_upd_reg_current_vm Hcur in Heqc2.
    destruct (decide (i = V0)).
    + exfalso.
      by apply Hneq_v.
    + destruct HstepP as [Hstep1 Hstep2].
      simplify_eq.
      assert (bool_decide (σ1.1.1.2 = V0) = false) as ->.
      {
        rewrite bool_decide_eq_false //.
      }
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
      rewrite (preserve_inv_trans_ps_disj σ1).
      all: try rewrite p_upd_id_mb p_upd_pc_mb //.
      all: try rewrite p_upd_id_pgt p_upd_pc_pgt //.
      all: try rewrite p_upd_id_trans p_upd_pc_trans //.
      rewrite p_upd_id_mem p_upd_pc_mem.
      iFrame.
      iDestruct (gen_reg_update_Sep
                  {[(R0, V0):= a_;
                    (R1, V0):= b_;
                    (PC, get_current_vm σ1) := ai]}
                  {[(R0, V0):= of_imm (encode_hvc_func Yield);
                    (R1, V0):= of_imm (encode_vmid (get_current_vm σ1));
                    (PC, get_current_vm σ1) := (ai ^+ 1)%f]} with "Hregown [Hr0' Hr1 Hpc]") as ">[Hreg Hr01pc]"; [set_solver | |].
      * rewrite !big_sepM_insert ?big_sepM_empty; eauto; [iFrame | |].
        apply lookup_insert_None; split; eauto; intros P; by inversion P.
        apply lookup_insert_None. split; [apply lookup_insert_None; split; eauto; intros P; by inversion P |]; eauto; intros P; by inversion P.
      * rewrite !big_sepM_insert ?big_sepM_empty; eauto.
        iDestruct "Hr01pc" as "(Hr0' & Hr1' & Hpc' & _)".
        assert ((negb (scheduled (update_current_vmid (update_offset_PC (update_reg_global (update_reg_global σ1 V0 R0 (encode_hvc_func Yield)) V0 R1 (encode_vmid (get_current_vm σ1))) 1) V0) (get_current_vm σ1)) && true = true)) as ->.
        {
          rewrite andb_true_r.
          rewrite /scheduled /machine.scheduler //= /scheduler.
          rewrite /update_current_vmid //=.
          apply eq_true_not_negb.
          intros c.
          rewrite ->bool_decide_eq_true in c.
          inversion c.
          apply n0.
          symmetry.
          apply fin_to_nat_inj.
          done.
        }
        rewrite /just_scheduled_vms /just_scheduled.
        assert (filter
                  (λ id : vmid,
                          base.negb (scheduled σ1 id) && scheduled (update_current_vmid (update_offset_PC (update_reg_global (update_reg_global σ1 V0 R0 (encode_hvc_func Yield)) V0 R1 (encode_vmid (get_current_vm σ1))) 1) V0) id = true)
                  (seq 0 vm_count) = [0]) as ->.
        {
        rewrite /scheduled /machine.scheduler //= /scheduler.
        rewrite /update_current_vmid //=.
        pose proof (NoDup_seq 0 vm_count) as ND.
        pose proof (NoDup_singleton 0) as ND'.
        set f := (λ id : nat, base.negb (bool_decide ((@fin_to_nat (@vm_count H) σ1.1.1.2) = id)) && bool_decide (fin_to_nat V0 = id) = true).
        pose proof (NoDup_filter f _ ND) as ND''.
        assert (f 0) as Prf.
        {
          subst f.
          simpl.
          unfold base.negb.
          repeat case_bool_decide;eauto.
          exfalso.
          apply n0.
          apply fin_to_nat_inj.
          rewrite H0.
          symmetry.
          done.
          exfalso.
          apply H1.
          apply V0eq.
          exfalso.
          apply H1.
          apply V0eq.
        }
        assert (In 0 (seq 0 vm_count)) as Prf'.
        {
          rewrite <-elem_of_list_In.
          rewrite elem_of_seq.
          split.
          - solve_finz.
          - rewrite plus_O_n.
            apply vm_count_pos.
        }
        rewrite <-elem_of_list_In in Prf'.
        assert (In 0 (filter f (seq 0 vm_count))) as Prf''.
        {
          rewrite <-elem_of_list_In.
          by apply (iffRL (elem_of_list_filter f (seq 0 vm_count) 0)).
        }
        rewrite <-elem_of_list_In in Prf''.
        assert (forall x, x ≠ 0 -> not (In x (filter f (seq 0 vm_count)))) as excl.
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
            rewrite <-c'.
            apply V0eq.
        }
        apply Permutation_length_1_inv.
        apply NoDup_Permutation; auto.
        intros x'.
        split.
        - intros T.
          rewrite ->elem_of_list_singleton in T.
          by rewrite T.
        - intros T.
          rewrite ->elem_of_list_singleton.
          rewrite ->elem_of_list_In in T.
          destruct (decide (x' = 0)) as [? | n].
          done.
          exfalso.
          by apply (excl x' n).
      }
        set σ1' := (X in (update_current_vmid X V0)).
        rewrite (preserve_get_reg_gmap σ1' (update_current_vmid _ _)); last rewrite p_upd_id_reg //.
        rewrite /σ1'.
        rewrite ->(u_upd_pc_regs _ (get_current_vm σ1) ai 1); auto.
        -- iDestruct (VMProp_update σ1.1.1.2 U P P' with "PAuth HPropi") as "HTemp".
           iMod "HTemp".
           iDestruct "HTemp" as "[PAuth HPropi]".
           iModIntro.           
           iFrame.
           iSplitL "PAuth".
           by iExists P'.
           iSplitL "Hreg".
           iSplit; first done.
           rewrite 2!u_upd_reg_regs.
           rewrite !insert_union_singleton_l.
           rewrite (map_union_comm {[(R1, V0) := of_imm (encode_vmid σ1.1.1.2)]} {[(PC, σ1.1.1.2) := (ai ^+ 1)%f]}).
           rewrite map_union_assoc.
           rewrite (map_union_comm {[(R0, V0) := of_imm (encode_hvc_func Yield)]} {[(PC, σ1.1.1.2) := (ai ^+ 1)%f]}).
           rewrite <-(map_union_assoc {[(PC, σ1.1.1.2) := (ai ^+ 1)%f]}
                                      {[(R0, V0) := of_imm (encode_hvc_func Yield)]}
                                      {[(R1, V0) := of_imm (encode_vmid σ1.1.1.2)]}).
           rewrite (map_union_comm {[(R0, V0) := of_imm (encode_hvc_func Yield )]}
                                   {[(R1, V0) := of_imm (encode_vmid σ1.1.1.2)]}).
           rewrite !map_union_assoc.
           iAssumption.
           by rewrite map_disjoint_singleton_r lookup_singleton_None.
           by rewrite map_disjoint_singleton_r lookup_singleton_None.
           by rewrite map_disjoint_singleton_r lookup_singleton_None.
           iDestruct (VMProp_split with "HPropi") as "[HPropi1 HPropi2]".
           iDestruct ("Himpl" with "[Hpc' Hapc Hacc Hr0 Hr0' Hr1' HR HPropi1 tx]") as "[Q R']".
           iFrame.
           iSplitR "Hϕ R' HPropi2".
           simpl.
           iSplit; last done.
           iExists (Q)%I.
           rewrite V0eq.
           iFrame.
           iApply ("Hϕ" with "[R' HPropi2]").
           iFrame.
        -- apply get_reg_gmap_get_reg_Some; auto.
           apply get_reg_global_update_reg_global_ne_vmid.
           rewrite p_upd_reg_current_vm; auto.
           rewrite p_upd_reg_current_vm; auto.
           apply get_reg_global_update_reg_global_ne_vmid.
           rewrite p_upd_reg_current_vm; auto.
           rewrite p_upd_reg_current_vm; auto.
        -- apply lookup_insert_None; split; eauto; intros P; by inversion P.
        -- apply lookup_insert_None. split; [apply lookup_insert_None; split; eauto; intros P; by inversion P |]; eauto; intros P; by inversion P.
Qed.

Lemma yield_primary {E wi r0 q s p_tx} ai:
  (tpa ai) ∈ s ->
  (tpa ai) ≠ p_tx ->
  decode_instruction wi = Some Hvc ->
  decode_hvc_func r0 = Some Yield ->
  {SS{{ ▷ (PC @@ V0 ->r ai)
              ∗ ▷ (ai ->a wi)
              ∗ ▷ (V0 -@{q}A> s)
              ∗ ▷ (TX@ V0:= p_tx)
              ∗ ▷ (R0 @@ V0 ->r r0)}}}
    ExecI @ V0;E
    {{{ RET (false, ExecI); PC @@ V0 ->r (ai ^+ 1)%f
               ∗ ai ->a wi
               ∗ V0 -@{q}A> s
               ∗ TX@ V0 := p_tx
               ∗ R0 @@ V0 ->r (encode_hvc_func Yield)}}}.
  Proof.
  iIntros (Hin_acc Hneq_tx Hdecode_i Hdecode_f Φ)
          "(>PC & >mem_ins & >acc & >tx & > R0) HΦ".
  iApply (sswp_lift_atomic_step ExecI);[done|].
  iIntros (n σ1) "%Hsche state".
  rewrite /scheduled /= /scheduler in Hsche.
  assert (σ1.1.1.2 = V0) as Heq_cur. { case_bool_decide;last done. by apply fin_to_nat_inj. }
  clear Hsche.
  iModIntro.
  iDestruct "state" as "(Hnum & mem & regs & mb & rx_state & pgt_owned & pgt_acc & pgt_excl &
                            trans & hpool & retri & %Hwf & %Hdisj & %Hconsis)".
  (* valid regs *)
  iDestruct ((gen_reg_valid2 V0 PC ai R0 r0 Heq_cur) with "regs PC R0")
    as "(%Hlookup_PC & %Hlookup_R0 )";eauto.
  (* valid pt *)
  iDestruct (access_agree_check_true (tpa ai) V0 with "pgt_acc acc") as %Hcheckpg_ai;eauto.
  (* valid mem *)
  iDestruct (gen_mem_valid ai wi with "mem mem_ins") as %Hlookup_ai.
  (* valid tx rx *)
  iDestruct (mb_valid_tx V0 p_tx with "mb tx") as %Heq_tx.
  iSplit.
  - (* reducible *)
    iPureIntro.
    apply (reducible_normal V0 Hvc ai wi);eauto.
    rewrite Heq_tx //.
  - iModIntro.
    iIntros (m2 σ2) "vmprop_auth %HstepP".
    iFrame "vmprop_auth".
    apply (step_ExecI_normal V0 Hvc ai wi) in HstepP;eauto.
    2: rewrite Heq_tx //.
    remember (exec Hvc σ1) as c2 eqn:Heqc2.
    rewrite /exec /hvc Hlookup_R0 /= Hdecode_f /= /lang.yield /is_primary in Heqc2.
    case_bool_decide. 2: contradiction.
    rewrite /= in Heqc2.
    destruct HstepP;subst m2 σ2; subst c2; simpl.
    rewrite /gen_vm_interp.
    rewrite (preserve_get_own_gmap σ1).
    rewrite (preserve_get_access_gmap σ1).
    rewrite (preserve_get_excl_gmap σ1).
    2-4: rewrite p_upd_id_pgt p_upd_pc_pgt p_upd_reg_pgt //.
    rewrite (preserve_get_trans_gmap σ1).
    rewrite (preserve_get_hpool_gset σ1).
    rewrite (preserve_get_retri_gmap σ1).
    2-4: rewrite p_upd_id_trans p_upd_pc_trans p_upd_reg_trans //.
    rewrite (preserve_inv_trans_pgt_consistent σ1).
    rewrite (preserve_inv_trans_wellformed σ1).
    rewrite (preserve_inv_trans_ps_disj σ1).
    2-4: rewrite p_upd_id_trans p_upd_pc_trans p_upd_reg_trans //.
    2: rewrite p_upd_id_pgt p_upd_pc_pgt p_upd_reg_pgt //.
    rewrite (preserve_get_mb_gmap σ1 (update_current_vmid _ _)).
    2: rewrite p_upd_id_mb p_upd_pc_mb p_upd_reg_mb //.
    rewrite p_upd_id_mem p_upd_pc_mem p_upd_reg_mem.
    rewrite (preserve_get_rx_gmap σ1).
    2: rewrite p_upd_id_mb p_upd_pc_mb p_upd_reg_mb //.
    iFrame "Hnum mem mb rx_state pgt_owned pgt_acc pgt_excl trans hpool retri".
    rewrite (preserve_get_reg_gmap (update_incr_PC (update_reg_global σ1 V0 R0 (encode_hvc_func Yield))) (update_current_vmid _ _)).
    2: rewrite p_upd_id_reg //.
    rewrite (u_upd_pc_regs _ V0 ai).
    2: rewrite p_upd_reg_current_vm //.
    2: { rewrite u_upd_reg_regs.
         rewrite lookup_insert_ne;last done.
         solve_reg_lookup.
    }
    rewrite u_upd_reg_regs.
    iDestruct ((gen_reg_update2_global PC V0 _ (ai ^+ 1)%f R0 V0 _ (encode_hvc_func Yield)) with "regs PC R0")
      as ">($ & PC & R0)";eauto.
    iModIntro.
    iSplit. iPureIntro. auto.
    (* just_schedule *)
    rewrite /just_scheduled_vms /just_scheduled.
    rewrite /scheduled /machine.scheduler /= /scheduler.
    rewrite /update_current_vmid /= Heq_cur.
    set fl := (filter _ _).
    assert (fl = []) as ->.
    {
      rewrite /fl.
      induction n.
      - simpl.
        rewrite filter_nil //=.
      - rewrite seq_S.
        rewrite list.filter_app.
        rewrite IHn.
        simpl.
        rewrite filter_cons_False /=.
        rewrite filter_nil. auto.
        rewrite andb_negb_l.
        done.
    }
    iSplitR;first done.
    case_bool_decide; last contradiction.
    simpl.
    iApply "HΦ".
    iFrame.
  Qed.


End yield.
