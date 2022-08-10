From machine_program_logic.program_logic Require Import machine weakestpre adequacy.
From iris.algebra Require Import big_op.
From HypVeri Require Import machine_extra lifting.
From HypVeri.algebra Require Import base mailbox pagetable mem.
From HypVeri.lang Require Import reg_extra.
From HypVeri.examples Require Import instr utils.
From HypVeri.logrel Require Import logrel logrel_prim.
From HypVeri.examples.unknown_primary Require Import proof.
Require Import Setoid.

Section up_adequacy.
  Context `{hypparams: !HypervisorParameters}.
  Context (p_prog0 p_prog1 p_prog2 p_prog3 p_tx0 p_tx1 p_tx2 p_tx3 p_rx0 p_rx1 p_rx2 p_rx3 p_share : PID).
  Context (Hps_nd: NoDup [p_prog0;p_prog1;p_prog2;p_prog3;p_share;p_tx0;p_tx1;p_tx2;p_tx3;p_rx0;p_rx1;p_rx2;p_rx3]).
  Context (σ : state).
  Context (i_jump : Imm) (Hjump_eq: of_imm (i_jump) = (p_prog1 ^+ 4)%f).
  Context (i_pshare: Imm) (Hpshare_eq: of_pid p_share = i_pshare).

  Definition pgt :=
    access_layout σ {[V0 := to_dfrac_agree (DfracOwn 1) {[p_prog0; p_tx0; p_rx0]};
                     V1 := to_dfrac_agree (DfracOwn 1) {[p_prog1; p_share; p_tx1; p_rx1]};
                     V2 := to_dfrac_agree (DfracOwn 1) {[p_prog2; p_tx2; p_rx2]};
                     V3 := to_dfrac_agree (DfracOwn 1) {[p_prog3; p_share; p_tx3; p_rx3]}]} ∧
    excl_layout σ {[p_share:= false;p_rx0 := true; p_rx1 := true; p_rx2 := true; p_rx3 := true;
                    p_tx0 := true; p_tx1 := true; p_tx2 := true; p_tx3 := true;
                    p_prog0 := true; p_prog1 := true; p_prog2 := true; p_prog3 := true]} ∧
    own_layout σ {[p_share:= Some V1;
                   p_rx0 := None; p_rx1 := None; p_rx2 := None; p_rx3 := None;
                   p_tx0 := None; p_tx1 := None; p_tx2 := None; p_tx3 := None;
                   p_prog0 := Some V0; p_prog1 := Some V1;p_prog2 := Some V2; p_prog3 := Some V3]} ∧
  σ.1.1.1.2 !! p_share = Some (Some V1, false, {[V1; V3]}).

  Program Definition mem :=
    let mem := ((get_mem σ): gmap Addr Word)  in
    (∀ (m : gmap Addr Addr), dom m = set_of_addr {[p_prog1]} -> m ⊆ mem -> m = mem_page_program p_prog1 (up_program1 i_pshare i_jump) _) ∧
    (∀ (m : gmap Addr Addr), dom m = set_of_addr {[p_prog3]} -> m ⊆ mem -> m = mem_page_program p_prog3 (up_program3 i_pshare) _) ∧
    ((set_of_addr {[p_prog0;p_prog1;p_prog2;p_prog3;p_share;p_tx0;p_tx1;p_tx2;p_tx3;p_rx0;p_rx1;p_rx2;p_rx3]}) ⊆ dom mem).
  Next Obligation. lia. Qed.
  Next Obligation. lia. Qed.

  Definition regs :=
    reg_layout σ ({[PC:= of_pid p_prog1]}) V1 ∧
    reg_layout σ ({[PC:=of_pid p_prog3]}) V3 ∧
    ∀ i, base_extra.is_total_gmap ((get_reg_files σ) !!! i).

  Definition mailbox :=
    mailbox_layout σ {[(V0, TX) := p_tx0; (V1, TX) := p_tx1; (V2, TX) := p_tx2; (V3, TX) := p_tx3;
                      (V0, RX) := p_rx0; (V1, RX) := p_rx1; (V2, RX) := p_rx2; (V3, RX) := p_rx3]} ∧
    rx_layout σ {[V0 := None; V1 := None; V2 := None; V3 := None]}.

  Definition transactions:=
    (get_transactions σ) = {[W0 := Some (V1, V3, {[p_share]}, Sharing, true)]}.

  Definition initial_config (ms: list exec_mode) (φs : list (exec_mode -> Prop )):=
                  (get_current_vm σ) = V0 ∧
                  φs = [(λ _, True); (λ _, False); (λ _, True); (λ m, m = HaltI)] ∧
                  ms = [ExecI;ExecI;ExecI;ExecI] ∧
                  pgt ∧ mem ∧ regs ∧ mailbox ∧ transactions.

  Context {vm_preG: gen_VMPreG Addr VMID Word reg_name PID transaction_type irisΣ}.

  Lemma memory_list_gmap (pid : PID) (mem_list : list Word) (Hle: length mem_list < (Z.to_nat page_size))
        (mem_gmap : gmap Addr Word)
        (H : NoDup (zip (finz.seq pid (length mem_list)) mem_list).*1)
        (G : mem_gmap = mem_page_program pid mem_list Hle)
        γ :
    (([∗ list] xk ∈ map_to_list mem_gmap, xk.1 ↪[γ] xk.2) -∗
       [∗ list] xy ∈ zip (finz.seq pid (length mem_list)) mem_list, xy.1 ↪[γ] xy.2).
  Proof.
    rewrite G /mem_page_program //.
    rewrite map_to_list_to_map; first done.
    rewrite fst_zip.
    - apply finz_seq_NoDup'.
      simpl.
      pose proof (last_addr_in_bound pid).
      solve_finz.
    - rewrite finz_seq_length.
      lia.
  Qed.

  Lemma get_reg_gmap_split γ:
    ([∗ map] p↦w ∈ (get_reg_gmap σ) , p ↪[γ] w)%I
    ⊢ [∗ list] i ∈ ((list_of_vmids): list VMID), [∗ map] p↦w ∈ get_reg_gmap_vm σ i, p ↪[γ] w.
  Proof.
    iIntros "Hmap".
    rewrite /get_reg_gmap.
    pose proof (NoDup_list_of_vmids) as Hnodup.
    iInduction (list_of_vmids) as [ | i l] "IH".
    done.
    rewrite list_to_map_app.
    rewrite big_sepM_union.
    iDestruct "Hmap" as "[Hsub Hmap]".
    iSplitL "Hsub".
    {
      rewrite /get_reg_gmap_vm.
      iFrame "Hsub".
    }
    iApply "IH".
    { iPureIntro. apply NoDup_cons in Hnodup. destruct Hnodup;auto. }
    iFrame "Hmap".
    apply  map_disjoint_list_to_map_l.
    apply Forall_forall.
    intros.
    assert (∀ (v: VMID) x, x ∈ map (λ p : reg_name * Addr, (p.1, v, p.2)) (map_to_list (σ.1.1.1.1.1 !!! v)) -> x.1.2 = v).
    {
      intros.
      apply elem_of_list_In in H0.
      apply in_map_iff in H0.
      destruct H0 as [? [Heq Hin]].
      destruct x0.
      destruct p.
      simpl.
      simplify_eq /=.
      done.
    }
    apply H0 in H.
    destruct (x.1).
    simpl in H.
    subst v.
    apply  not_elem_of_list_to_map_1.
    intro.
    apply elem_of_list_In in H.
    apply in_map_iff in H.
    destruct H as [p].
    destruct H as [Heqn H1].
    apply in_flat_map in H1.
    destruct H1 as [i'].
    destruct H as [HIn H].
    apply elem_of_list_In in H.
    apply H0 in H.
    rewrite Heqn in H.
    simpl in H.
    subst i'.
    apply NoDup_cons in Hnodup as [Hnotin ?].
    rewrite -elem_of_list_In in HIn.
    contradiction.
  Qed.

  (* exec_mode of all VMs *)
  Lemma adequacy (ms : list exec_mode) φs:
    (* we need assumptions to be able to allocate resources *)
    (* with these resources, we apply the specification and get the wptp *)
    (* along with some other stuff, then it should be enough to apply the adequacy theorem *)
    (initial_config ms φs) ->
    adequate ms σ ((λ φ, λ v _, φ v)<$> φs).
    (* φ : vm 0 is scheduled but halted *)
  Proof.
    intros Hinit.
    set (saved_props := (let (_, x, _, _) := iris_subG irisΣ (subG_refl irisΣ) in x)).
    set (prop_name := (let (_, _, x, _) := iris_subG irisΣ (subG_refl irisΣ) in x)).
    set (name_map := (let (_, _, _, x) := iris_subG irisΣ (subG_refl irisΣ) in x)).
    destruct Hinit as (Hcur & -> & -> & Hpgt & Hmem & Hreg & Hmb & Htrans).
    eapply (wp_adequacy irisΣ); auto.
    intro Hinv.
    iIntros.
    iMod (gen_mem_alloc σ) as (mem_gname) "[Hσmem Hmem]".
    iMod (gen_reg_alloc σ) as (reg_gname) "[Hσreg Hreg]".
    iMod (gen_mb_alloc σ) as (mb_gname) "[Hσmb Hmb]".
    iMod (gen_rx_state_alloc σ) as (rx_state_gname) "[Hσrxs Hrxs]".
    iMod (gen_own_alloc σ) as (own_gname) "[Hσown Hown]".
    iMod (gen_access_alloc σ) as (access_gname) "[Hσaccess Haccess]".
    iMod (gen_excl_alloc σ) as (excl_gname) "[Hσexcl Hexcl]".
    iMod (gen_trans_alloc σ) as (trans_gname) "[Hσtrans Htrans]".
    iMod (gen_hpool_alloc σ) as (hpool_gname) "[Hσhpool Hhpool]".
    iMod (gen_retri_alloc σ) as (retri_gname) "[Hσretri Hretri]".

    iModIntro. iIntros (name_map_name).
    pose ((GenVMG irisΣ vm_preG Hinv _ _ _ name_map_name mem_gname reg_gname mb_gname rx_state_gname
                  own_gname access_gname excl_gname trans_gname hpool_gname retri_gname)) as VMG.
    iExists (gen_vm_interp (Σ := irisΣ)).

    (* use assumptions to extract resources *)
    (** extract regs  **)
    destruct Hreg as (Hlookup_reg1 & Hlookup_reg3 & Htotal_reg).
    iDestruct (get_reg_gmap_split with "Hreg") as "(Hreg0 & Hreg1 & Hreg2 & Hreg3 & _)".
    (* TODO: move, do the same for other resources *)
    assert (∀ σ f, ([∗ map] p↦w ∈ get_reg_gmap_vm σ f, p ↪[reg_gname] w)%I =
                   ([∗ map] p↦w ∈ get_reg_gmap_vm σ f, p.1 @@ p.2 ->r w)%I) as sepM_reg_def.
    {
      intros σ' f'.
      apply big_opM_ext.
      intros k x H.
      destruct k as [k1 k2].
      rewrite /= reg_mapsto_eq /reg_mapsto_def //.
    }
    iEval (rewrite sepM_reg_def) in "Hreg0 Hreg1 Hreg2 Hreg3". clear sepM_reg_def.

    (* extract regs of VM1 *)
    pose proof (Htotal_reg V1 R0) as [r0_ Hlookup_reg1_r0].
    pose proof (Htotal_reg V1 R1) as [r1_ Hlookup_reg1_r1].
    pose proof (Htotal_reg V1 R2) as [r2_ Hlookup_reg1_r2].

    iDestruct (big_sepM_subseteq _ (get_reg_gmap_vm σ V1) {[(PC, V1):= (of_pid p_prog1); (R0, V1) := r0_;
                                 (R1,V1):= r1_; (R2,V1):= r2_]} with "Hreg1") as "Hreg1";eauto.
    {
      apply (λ x, reg_layout_extend σ _ _ x R2 r2_ Hlookup_reg1_r2) in Hlookup_reg1.
      apply (λ x, reg_layout_extend σ _ _ x R1 r1_ Hlookup_reg1_r1) in Hlookup_reg1.
      apply (λ x, reg_layout_extend σ _ _ x R0 r0_ Hlookup_reg1_r0) in Hlookup_reg1.
      apply reg_layout_get_reg_gmap in Hlookup_reg1; last assumption.
      clear -Hlookup_reg1.
      rewrite !kmap_insert in Hlookup_reg1.
      rewrite kmap_empty in Hlookup_reg1.
      rewrite insert_empty in Hlookup_reg1.
      rewrite (insert_commute _ (R2, V1) (PC, V1)) in Hlookup_reg1.
      rewrite (insert_commute _ (R1, V1) (PC, V1)) in Hlookup_reg1.
      rewrite (insert_commute _ (R0, V1) (PC, V1)) in Hlookup_reg1.
      assumption. 1-3: done.
    }
    clear Hlookup_reg1_r0 Hlookup_reg1_r1 Hlookup_reg1_r2 Hlookup_reg1.

    iDestruct (big_sepM_insert with "Hreg1") as "(PC1 & Hreg1)".
    { rewrite !lookup_insert_None; repeat (split; eauto). }
    iDestruct (big_sepM_insert with "Hreg1") as "(R01 & Hreg1)".
    { rewrite !lookup_insert_None; repeat (split; eauto). }
    iDestruct (big_sepM_insert with "Hreg1") as "(R11 & Hreg1)".
    { rewrite !lookup_insert_None; repeat (split; eauto). }
    iDestruct (big_sepM_insert with "Hreg1") as "(R21 & Hreg1)".
    { rewrite lookup_empty; eauto. }

    (* extract regs of VM3 *)
    pose proof (Htotal_reg V3 R0) as [r0__ Hlookup_reg3_r0].
    pose proof (Htotal_reg V3 R1) as [r1__ Hlookup_reg3_r1].
    pose proof (Htotal_reg V3 R2) as [r2__ Hlookup_reg3_r2].
    iDestruct (big_sepM_subseteq _ (get_reg_gmap_vm σ V3) {[(PC, V3):= (of_pid p_prog3); (R0, V3) := r0__;
                      (R1, V3) := r1__; (R2, V3) := r2__]} with "Hreg3") as "Hreg3";eauto.
    {
      apply (λ x, reg_layout_extend σ _ _ x R2 r2__ Hlookup_reg3_r2) in Hlookup_reg3.
      apply (λ x, reg_layout_extend σ _ _ x R1 r1__ Hlookup_reg3_r1) in Hlookup_reg3.
      apply (λ x, reg_layout_extend σ _ _ x R0 r0__ Hlookup_reg3_r0) in Hlookup_reg3.
      apply reg_layout_get_reg_gmap in Hlookup_reg3; last assumption.
      clear -Hlookup_reg3.
      rewrite !kmap_insert in Hlookup_reg3.
      rewrite kmap_empty in Hlookup_reg3.
      rewrite insert_empty in Hlookup_reg3.

      rewrite (insert_commute _ (R2, V3) (PC, V3)) in Hlookup_reg3.
      rewrite (insert_commute _ (R1, V3) (PC, V3)) in Hlookup_reg3.
      rewrite (insert_commute _ (R0, V3) (PC, V3)) in Hlookup_reg3.
      assumption. 1-3: done.
    }
    clear Hlookup_reg3_r0 Hlookup_reg3_r1 Hlookup_reg3_r2 Hlookup_reg3.

    iDestruct (big_sepM_insert with "Hreg3") as "(PC3 & Hreg3)".
    { rewrite !lookup_insert_None; repeat (split; eauto). }
    iDestruct (big_sepM_insert with "Hreg3") as "(R03 & Hreg3)".
    { rewrite !lookup_insert_None; repeat (split; eauto). }
    iDestruct (big_sepM_insert with "Hreg3") as "(R13 & Hreg3)".
    { rewrite !lookup_insert_None; repeat (split; eauto). }
    iDestruct (big_sepM_insert with "Hreg3") as "(R23 & Hreg3)".
    { rewrite lookup_empty; eauto. }

    (** extract mb **)
    iDestruct (big_sepM_subseteq _ (get_mb_gmap σ) {[(V0, TX):= p_tx0; (V1, TX) := (p_tx1); (V2, TX) := (p_tx2); (V3, TX) := p_tx3;
                                          (V0, RX) := p_rx0; (V1, RX) := p_rx1; (V2, RX) := p_rx2; (V3, RX) := p_rx3]} with "Hmb") as "Hmb";eauto.
    apply mailbox_layout_get_mb_gmap. apply Hmb.
    iDestruct (big_sepM_insert with "Hmb") as "(mb0TX & Hmb)".
    { rewrite !lookup_insert_None; split; try split; done. }
    iDestruct (big_sepM_insert with "Hmb") as "(mb1TX & Hmb)".
    { rewrite !lookup_insert_None; split; try split; eauto. }
    iDestruct (big_sepM_insert with "Hmb") as "(mb2TX & Hmb)".
    { rewrite !lookup_insert_None; split; try split; eauto. }
    iDestruct (big_sepM_insert with "Hmb") as "(mb3TX & Hmb)".
    { rewrite !lookup_insert_None; split; try split; eauto. }
    iDestruct (big_sepM_insert with "Hmb") as "(mb0RX & Hmb)".
    { rewrite !lookup_insert_None; split; try split; eauto. }
    iDestruct (big_sepM_insert with "Hmb") as "(mb1RX & Hmb)".
    { rewrite !lookup_insert_None; split; try split; eauto. }
    iDestruct (big_sepM_insert with "Hmb") as "(mb2RX & Hmb)".
    { rewrite !lookup_insert_None; split; try split; eauto. }
    iDestruct (big_sepM_insert with "Hmb") as "(mb3RX & _)".
    { rewrite lookup_empty; eauto. }

    iDestruct (big_sepM_subseteq _ (get_rx_gmap σ) {[V0:= None; V1 := None; V2 := None; V3 := None]} with "Hrxs") as "Hrxs";eauto.
    apply rx_layout_get_rx_gmap. apply Hmb.
    iDestruct (big_sepM_insert with "Hrxs") as "(RX0St & Hrxs)".
    { rewrite !lookup_insert_None; split; eauto. }
    iDestruct (big_sepM_insert with "Hrxs") as "(RX1St & Hrxs)".
    { rewrite !lookup_insert_None; split; eauto. }
    iDestruct (big_sepM_insert with "Hrxs") as "(RX2St & Hrxs)".
    { rewrite !lookup_insert_None; split; eauto. }
    iDestruct (big_sepM_insert with "Hrxs") as "(RX3St & _)".
    { rewrite lookup_empty; eauto. }

    (** extract mem **)
    destruct Hmem as (HmemH1 & HmemH3 & Hdom_mem).
    destruct Hpgt as (pgt_acc & pgt_excl & pgt_own & pgt_share).
    pose proof (union_split_difference_intersection_subseteq_L _ _ Hdom_mem) as [Hdom_mem_union Hdom_mem_disj].
    pose proof (dom_union_inv_L _ _ _ Hdom_mem_disj Hdom_mem_union) as (mem' & mem2 & Hunion_mem' & Hdisj_mem' & _ & Hdom_mem2).

    iDestruct (big_sepM_subseteq _ (get_mem σ) mem2 with "Hmem") as "Hmem"; eauto.
    {
      rewrite Hunion_mem'.
      apply map_union_subseteq_r.
      done.
    }

    pose proof (union_split_difference_intersection_subseteq_L
                  {[p_prog0; p_prog1; p_prog2; p_prog3; p_share; p_tx0; p_tx1; p_tx2; p_tx3; p_rx0; p_rx1; p_rx2; p_rx3]} {[p_prog1]}) as [Heq Hdisj].
    set_solver +.
    rewrite Heq in Hdom_mem2.
    rewrite set_of_addr_union in Hdom_mem2.
    2 : { set_solver +. }
    clear Heq.
    apply dom_union_inv_L in Hdom_mem2.
    2 : { apply set_of_addr_disj. done. }
    destruct Hdom_mem2 as (mem1 & mem_p_prog1 & -> & Hmem1_disj  & Hdom_mem1 & Hdom_mem_p_prog1).
    iDestruct ((big_sepM_union _ _) with "Hmem") as "(Hmem1 & mem_p_prog1)";auto.
    clear Hdisj.
    pose proof (union_split_difference_intersection_subseteq_L ({[p_prog0; p_prog1; p_prog2; p_prog3; p_share; p_tx0; p_tx1; p_tx2; p_tx3; p_rx0; p_rx1; p_rx2; p_rx3]} ∖ {[p_prog1]}) {[p_prog3]}) as [Heq Hdisj].
    assert (p_prog3 ≠ p_prog1) as Hneq.
    {
      intro.
      feed pose proof (NoDup_lookup _ 1 3 p_prog3 Hps_nd).
      simplify_eq /=. done.
      simplify_eq /=. done.
      lia.
    }
    set_solver + Hneq.

    rewrite Heq in Hdom_mem1.
    rewrite set_of_addr_union in Hdom_mem1.
    2 : { set_solver. }
    clear Heq.
    apply dom_union_inv_L in Hdom_mem1.
    2 : { apply set_of_addr_disj. done. }
    destruct Hdom_mem1 as (mem2 & mem_p_prog2 &  -> & Hmem2_disj  & Hdom_mem2 & Hdom_mem_p_prog2).
    clear Hdisj.
    iDestruct ((big_sepM_union _ _) with "Hmem1") as "(Hmem2 & mem_p_prog2)";auto.
    pose proof (union_split_difference_intersection_subseteq_L (({[p_prog0; p_prog1; p_prog2; p_prog3; p_share; p_tx0; p_tx1; p_tx2; p_tx3; p_rx0; p_rx1; p_rx2; p_rx3]} ∖ {[p_prog1]}) ∖ {[p_prog3]}) {[p_share]}) as [Heq Hdisj].
    assert (p_share ≠ p_prog1) as Hneq.
    {
      intro.
      feed pose proof (NoDup_lookup _ 1 4 p_prog1 Hps_nd).
      simplify_eq /=. done.
      simplify_eq /=. done.
      lia.
    }
    assert (p_share ≠ p_prog3) as Hneq'.
    {
      intro.
      feed pose proof (NoDup_lookup _ 3 4 p_prog3 Hps_nd).
      simplify_eq /=. done.
      simplify_eq /=. done.
      lia.
    }
    set_solver + Hneq Hneq'.
    rewrite Heq in Hdom_mem2.
    rewrite set_of_addr_union in Hdom_mem2.
    2 : { set_solver +. }
    clear Heq.
    apply dom_union_inv_L in Hdom_mem2.
    2 : { apply set_of_addr_disj. done. }
    destruct Hdom_mem2 as (mem_p & mem & -> & Hmem_disj  & Hdom_mem' & Hdom_mem_p).
    iDestruct ((big_sepM_union _ _) with "Hmem2") as "(Hmem & mem_p)";auto.
    clear Hdisj.

    match goal with
      | [ H : context G [?a ∖ ?b ∖ ?c ∖ ?d] |- _ ] => set p := a; set q := b; set r := c; set t := d
    end.
    assert (NoDup' [p_prog0; p_prog1; p_prog2; p_prog3; p_share; p_tx0; p_tx1; p_tx2; p_tx3; p_rx0; p_rx1; p_rx2; p_rx3]).
    {
      rewrite /NoDup'.
      intros. intro.
      apply H1.
      pose proof Hps_nd as Hps_nd'.
      rewrite NoDup_alt in Hps_nd'.
      apply lookup_lt_is_Some_2 in H.
      apply lookup_lt_is_Some_2 in H0.
      destruct H, H0.
      rewrite H2 in H. rewrite H in H0. inversion H0;subst x0;clear H0.
      eapply Hps_nd';eauto.
      rewrite H2;done.
    }

    change {[p_prog0; p_prog1; p_prog2; p_prog3; p_share; p_tx0; p_tx1; p_tx2; p_tx3; p_rx0; p_rx1; p_rx2; p_rx3]} with p in Hdom_mem'.
    change {[p_prog1]} with q in Hdom_mem'.
    change {[p_prog3]} with r in Hdom_mem'.
    change {[p_share]} with t in Hdom_mem'.
    assert (p ∖ q ∖ r ∖ t = {[p_prog0; p_prog2; p_tx0; p_tx1; p_tx2; p_tx3; p_rx0; p_rx1; p_rx2; p_rx3]}) as Heq.
    {
      assert (p ∖ q ∖ r = {[p_prog0; p_prog2; p_share; p_tx0; p_tx1; p_tx2; p_tx3; p_rx0; p_rx1; p_rx2; p_rx3]}) as ->.
      {
        assert (p ∖ q = {[p_prog0; p_prog2; p_prog3; p_share; p_tx0; p_tx1; p_tx2; p_tx3; p_rx0; p_rx1; p_rx2; p_rx3]}) as ->.
        {
          subst p q.
          rewrite !difference_union_distr_l_L.
          rewrite difference_diag_L.
          rewrite union_empty_r_L.
          rewrite <-!difference_union_distr_l_L.
          rewrite difference_disjoint_L.
          - reflexivity.
          - solve_NoDup 1.
        }
        subst r.
        rewrite !difference_union_distr_l_L.
        rewrite difference_diag_L.
        rewrite union_empty_r_L.
        rewrite <-!difference_union_distr_l_L.
        rewrite difference_disjoint_L.
        - reflexivity.
        - solve_NoDup 3.
      }
      subst t.
      rewrite !difference_union_distr_l_L.
      rewrite difference_diag_L.
      rewrite union_empty_r_L.
      rewrite <-!difference_union_distr_l_L.
      rewrite difference_disjoint_L.
      - reflexivity.
      - solve_NoDup 4.
    }
    rewrite Heq in Hdom_mem'. clear Heq.
    rewrite set_of_addr_union in Hdom_mem'.
    2 : {
      solve_NoDup 12.
    }
    apply dom_union_inv_L in Hdom_mem'.
    2 : {
      apply set_of_addr_disj.
      solve_NoDup 12.
    }
    destruct Hdom_mem' as (mem3 & mem_p_rx3 &  -> & Hmem3_disj  & Hdom_mem1 & Hdom_mem_p_rx3).
    iDestruct ((big_sepM_union _ _) with "Hmem") as "(Hmem2 & p_rx3)";auto.
    rewrite set_of_addr_union in Hdom_mem1.
    2 : solve_NoDup 11.
    apply dom_union_inv_L in Hdom_mem1.
    2 : {
      apply set_of_addr_disj.
      solve_NoDup 11.
    }
    destruct Hdom_mem1 as (mem4 & mem_p_rx2 &  -> & Hmem4_disj  & Hdom_mem2 & Hdom_mem_p_rx2).
    iDestruct ((big_sepM_union _ _) with "Hmem2") as "(Hmem2 & p_rx2)";auto.
    rewrite set_of_addr_union in Hdom_mem2.
    2 : solve_NoDup 10.
    apply dom_union_inv_L in Hdom_mem2.
    2 : {
      apply set_of_addr_disj.
      solve_NoDup 10.
    }
    destruct Hdom_mem2 as (mem5 & mem_p_rx1 &  -> & Hmem5_disj  & Hdom_mem1 & Hdom_mem_p_rx1).
    iDestruct ((big_sepM_union _ _) with "Hmem2") as "(Hmem2 & p_rx1)";auto.
    rewrite set_of_addr_union in Hdom_mem1.
    2 : solve_NoDup 9.
    apply dom_union_inv_L in Hdom_mem1.
    2 : {
      apply set_of_addr_disj.
      solve_NoDup 9.
    }
    destruct Hdom_mem1 as (mem3 & mem_p_rx0 & -> & Hmem6_disj  & Hdom_mem2 & Hdom_mem_p_rx0).
    iDestruct ((big_sepM_union _ _) with "Hmem2") as "(Hmem2 & p_rx0)";auto.
    rewrite set_of_addr_union in Hdom_mem2.
    2 : solve_NoDup 8.
    apply dom_union_inv_L in Hdom_mem2.
    2 : {
      apply set_of_addr_disj.
      solve_NoDup 8.
    }
    destruct Hdom_mem2 as (mem4 & mem_p_tx3 & -> & Hmem7_disj  & Hdom_mem2 & Hdom_mem_p_tx3).
    iDestruct ((big_sepM_union _ _) with "Hmem2") as "(Hmem2 & p_tx3)";auto.
    rewrite set_of_addr_union in Hdom_mem2.
    2 : solve_NoDup 7.
    apply dom_union_inv_L in Hdom_mem2.
    2 : {
      apply set_of_addr_disj.
      solve_NoDup 7.
    }
    destruct Hdom_mem2 as (mem5 & mem_p_tx2 & -> & Hmem8_disj  & Hdom_mem2 & Hdom_mem_p_tx2).
    iDestruct ((big_sepM_union _ _) with "Hmem2") as "(Hmem2 & p_tx2)";auto.
    rewrite set_of_addr_union in Hdom_mem2.
    2 : solve_NoDup 6.
    apply dom_union_inv_L in Hdom_mem2.
    2 : {
      apply set_of_addr_disj.
      solve_NoDup 6.
    }
    destruct Hdom_mem2 as (mem6 & mem_p_tx1 & -> & Hmem9_disj  & Hdom_mem2 & Hdom_mem_p_tx1).
    iDestruct ((big_sepM_union _ _) with "Hmem2") as "(Hmem2 & p_tx1)";auto.
    rewrite set_of_addr_union in Hdom_mem2.
    2 : solve_NoDup 5.
    apply dom_union_inv_L in Hdom_mem2.
    2 : {
      apply set_of_addr_disj.
      solve_NoDup 5.
    }
    destruct Hdom_mem2 as (mem7 & mem_p_tx0 & -> & Hmem10_disj  & Hdom_mem2 & Hdom_mem_p_tx0).
    iDestruct ((big_sepM_union _ _) with "Hmem2") as "(Hmem2 & p_tx0)";auto.

    subst p q r t.

    (* clear Hmem10_disj Hmem9_disj Hmem8_disj Hmem7_disj Hmem6_disj Hmem5_disj Hmem4_disj Hmem3_disj. *)
    clear Hmem10_disj Hmem8_disj Hmem6_disj Hmem5_disj Hmem4_disj Hmem3_disj.

    iAssert (trans.fresh_handles 1 ∅)%I with "[Hhpool]" as "Hp".
    {
      unfold trans.fresh_handles.
      unfold get_hpool_gset.
      unfold get_fresh_handles.
      rewrite Htrans.
      rewrite map_filter_singleton_False;auto.
      rewrite dom_empty_L. rewrite intersection_empty_l_L.
      rewrite big_sepS_empty.
      rewrite hpool_mapsto_eq /hpool_mapsto_def /=.
      iSplitL;done.
    }
    (*   simpl. *)
    (*   iSplitR;. *)
    (*   assert ((filter (λ (kv : Addr * option transaction), kv.2 = None) σ.2) = σ.2) as Heq. *)
    (*   { *)
    (*     rewrite map_eq_iff. *)
    (*     intros i. *)
    (*     rewrite map_filter_lookup. *)
    (*     rewrite map_Forall_lookup in Htrans2. *)
    (*     specialize (Htrans2 i). *)
    (*     destruct (σ.2 !! i) eqn:Heqn. *)
    (*     - rewrite Heqn. *)
    (*       simpl. *)
    (*       specialize (Htrans2 o Heqn). *)
    (*       rewrite Htrans2. *)
    (*       simpl. *)
    (*       reflexivity. *)
    (*     - rewrite Heqn. *)
    (*       reflexivity. *)
    (*   } *)
    (*   rewrite Heq. *)
    (*   assert ((dom σ.2 ∩ {[W0]}) = (dom σ.2)) as ->. *)
    (*   { *)
    (*     rewrite Htrans1. *)
    (*     set_solver +. *)
    (*   } *)
    (*   iFrame "Hhpool". *)

    (*   rewrite big_sepS_sep. *)
    (*   iSplitL "Htrans". *)
    (*   - unfold get_trans_gmap. *)
    (*     unfold get_transactions_gmap. *)
    (*     rewrite trans_mapsto_eq /trans_mapsto_def. *)
    (*     match goal with *)
    (*     | |- context G [?f <$> σ.2] => set g := f *)
    (*     end. *)
    (*     assert (∀ (m : gmap Addr (option transaction)) *)
    (*               (f : option transaction -> option meta_info), map_Forall (λ _ v, v = None) m -> (f None = None) -> (∀ i j, (f <$> m) !! i = Some j -> j = None)) as Heq'. *)
    (*     { *)
    (*       intros m f Hm Hf. *)
    (*       intros i j. *)
    (*       rewrite map_Forall_lookup in Hm. *)
    (*       specialize (Hm i). *)
    (*       rewrite lookup_fmap. *)
    (*       destruct (m !! i) eqn:Heqn. *)
    (*       - intros eq. *)
    (*         specialize (Hm o eq_refl). *)
    (*         rewrite Hm in eq. *)
    (*         simpl in eq. *)
    (*         rewrite Hf in eq. *)
    (*         inversion eq. *)
    (*         reflexivity. *)
    (*       - intros eq. *)
    (*         simpl in eq. *)
    (*         discriminate. *)
    (*     } *)
    (*     specialize (Heq' σ.2 g Htrans2). *)
    (*     feed specialize Heq'. *)
    (*     { *)
    (*       subst g. *)
    (*       simpl. *)
    (*       reflexivity. *)
    (*     } *)
    (*     simpl. *)
    (*     assert (map_Forall (λ (_ : Addr) (v : option (@meta_info rywu_vmconfig)), v = None) (g <$> σ.2)) as Htrans3. *)
    (*     { *)
    (*       intros i j He. *)
    (*       by apply (Heq' i). *)
    (*     } *)
    (*     pose proof (big_opM_dom (fun (y : finz.finz 2000000) => ghost_map_elem trans_gname y (DfracOwn (pos_to_Qp 1)) None) σ.2) as Hrew. *)
    (*     simpl in Hrew. *)
    (*     rewrite big_sepS_sep. *)
    (*     rewrite <-Hrew. *)
    (*     clear Hrew. *)
    (*     rewrite big_opM_fmap. *)
    (*     rewrite big_op.big_opM_unseal /big_op.big_opM_def. *)
    (*     rewrite (big_opL_ext (λ _, uncurry *)
    (*                                  (λ (k : Addr) (_ : option transaction), *)
    (*                                   (k ↪[trans_gname] None)%I)) *)
    (*                          (λ _, uncurry (λ (k : Addr) (y : option transaction), *)
    (*                                         (k ↪[trans_gname] g y)%I)) *)
    (*                          (map_to_list σ.2)). *)
    (*     iFrame "Htrans". *)
    (*     { *)
    (*       iPureIntro. *)
    (*       rewrite Htrans1. *)
    (*       intro. *)
    (*       set_solver +. *)
    (*     } *)
    (*     intros k (y1 & y2) eq'. *)
    (*     simpl. subst g. *)
    (*     assert (y2 = None) as ->. *)
    (*     { *)
    (*       rewrite map_Forall_to_list in Htrans2. *)
    (*       apply (Forall_lookup_1 _ _ k (pair y1 y2)) in Htrans2; last done. *)
    (*       simpl in Htrans2. *)
    (*       assumption. *)
    (*     } *)
    (*     reflexivity. *)
    (*   - unfold get_retri_gmap. *)
    (*     unfold get_transactions_gmap. *)
    (*     rewrite retri_mapsto_eq /retri_mapsto_def. *)
    (*     match goal with *)
    (*     | |- context G [?f <$> σ.2] => set g := f *)
    (*     end. *)
    (*     rewrite big_opM_fmap. *)
    (*     simpl. *)
    (*     set f := (λ k v, (k ↪[retri_gname] g v)%I). *)
    (*     pose f' := (λ k _, f k None). *)
    (*     rewrite (big_opM_ext f *)
    (*                          (λ k v, f' (option transaction) k v) *)
    (*                          σ.2). *)
    (*     2: { *)
    (*       intros k x G. *)
    (*       subst f f' g. simpl. *)
    (*       rewrite map_Forall_lookup in Htrans2. *)
    (*       specialize (Htrans2 k x G). *)
    (*       rewrite Htrans2 //=. *)
    (*     } *)
    (*     subst f'. simpl. *)
    (*     subst f. simpl. *)
    (*     rewrite big_opM_dom. *)
    (*     rewrite big_sepS_sep. *)
    (*     iFrame "Hretri". *)
    (*     { *)
    (*       iPureIntro. *)
    (*       rewrite Htrans1. *)
    (*       intro. *)
    (*       set_solver +. *)
    (*     } *)
    (* } *)

    (* TODO more? *)

    (** extract pgt **)
    iDestruct (big_sepM_subseteq _ (get_access_gmap σ)
                 {[V0 := (to_dfrac_agree (DfracOwn 1) ({[p_prog0; p_tx0; p_rx0]}));
                   V1 := (to_dfrac_agree (DfracOwn 1) ({[p_prog1; p_share; p_tx1; p_rx1]}));
                   V2 := (to_dfrac_agree (DfracOwn 1) ({[p_prog2; p_tx2; p_rx2]}));
                   V3 := (to_dfrac_agree (DfracOwn 1) ({[p_prog3; p_share; p_tx3; p_rx3]}))]} with "Haccess") as "access".
    {
      apply access_layout_get_access_gmap.
      apply pgt_acc.
    }
    iEval (rewrite big_opM_insert_delete) in "access".
    match goal with
    | |- context G [delete _ ?p] => set P := p
    end.
    assert (delete V0 P = P) as ->.
    {
      subst P. clear.
      apply delete_notin.
      by simplify_map_eq /=.
    }
    subst P.
    iEval (rewrite big_opM_insert_delete) in "access".
    match goal with
    | |- context G [delete _ ?p] => set P := p
    end.
    assert (delete V1 P = P) as ->.
    {
      subst P. clear.
      apply delete_notin.
      by simplify_map_eq /=.
    }
    subst P.
    iEval (rewrite big_opM_insert_delete) in "access".
    match goal with
    | |- context G [delete _ ?p] => set P := p
    end.
    assert (delete V2 P = P) as ->.
    {
      subst P. clear.
      apply delete_notin.
      by simplify_map_eq /=.
    }
    subst P.
    iEval (rewrite big_sepM_singleton) in "access".
    iDestruct "access" as "(access0 & access1 & access2 & access3)".

    iDestruct (big_sepM_subseteq _ (get_excl_gmap σ) {[p_share := false;
                     p_rx0 := true; p_rx1 := true; p_rx2 := true; p_rx3 := true;
                     p_tx0 := true; p_tx1 := true; p_tx2 := true; p_tx3 := true;
                     p_prog0:= true; p_prog1 := true; p_prog2 := true; p_prog3 := true]} with "Hexcl") as "excl".
    {
      apply excl_layout_get_excl_gmap.
      apply pgt_excl.
    }
    iEval (rewrite big_opM_insert_delete) in "excl".
    match goal with
    | |- context G [delete _ ?p] => set P := p
    end.
    assert (delete p_share P = P) as ->.
    {
      subst P.
      apply delete_notin.
      rewrite <-not_elem_of_dom.
      rewrite !dom_insert_L.
      rewrite !union_assoc_L.
      rewrite dom_empty_L.
      rewrite union_empty_r.
      solve_NoDup 4.
    }
    subst P.
    iEval (rewrite big_opM_insert_delete) in "excl".
    match goal with
    | |- context G [delete _ ?p] => set P := p
    end.
    assert (delete p_rx0 P = P) as ->.
    {
      subst P.
      apply delete_notin.
      rewrite <-not_elem_of_dom.
      rewrite !dom_insert_L.
      rewrite !union_assoc_L.
      rewrite dom_empty_L.
      rewrite union_empty_r.
      solve_NoDup 9.
    }
    subst P.
    iEval (rewrite big_opM_insert_delete) in "excl".
    match goal with
    | |- context G [delete _ ?p] => set P := p
    end.
    assert (delete p_rx1 P = P) as ->.
    {
      subst P.
      apply delete_notin.
      rewrite <-not_elem_of_dom.
      rewrite !dom_insert_L.
      rewrite !union_assoc_L.
      rewrite dom_empty_L.
      rewrite union_empty_r.
      solve_NoDup 10.
    }
    subst P.
    iEval (rewrite big_opM_insert_delete) in "excl".
    match goal with
    | |- context G [delete _ ?p] => set P := p
    end.
    assert (delete p_rx2 P = P) as ->.
    {
      subst P.
      apply delete_notin.
      rewrite <-not_elem_of_dom.
      rewrite !dom_insert_L.
      rewrite !union_assoc_L.
      rewrite dom_empty_L.
      rewrite union_empty_r.
      solve_NoDup 11.
    }
    subst P.
    iEval (rewrite big_opM_insert_delete) in "excl".
    match goal with
    | |- context G [delete _ ?p] => set P := p
    end.
    assert (delete p_rx3 P = P) as ->.
    {
      subst P.
      apply delete_notin.
      rewrite <-not_elem_of_dom.
      rewrite !dom_insert_L.
      rewrite !union_assoc_L.
      rewrite dom_empty_L.
      rewrite union_empty_r.
      solve_NoDup 12.
    }
    subst P.
    iEval (rewrite big_opM_insert_delete) in "excl".
    match goal with
    | |- context G [delete _ ?p] => set P := p
    end.
    assert (delete p_tx0 P = P) as ->.
    {
      subst P.
      apply delete_notin.
      rewrite <-not_elem_of_dom.
      rewrite !dom_insert_L.
      rewrite !union_assoc_L.
      rewrite dom_empty_L.
      rewrite union_empty_r.
      solve_NoDup 5.
    }
    subst P.
    iEval (rewrite big_opM_insert_delete) in "excl".
    match goal with
    | |- context G [delete _ ?p] => set P := p
    end.
    assert (delete p_tx1 P = P) as ->.
    {
      subst P.
      apply delete_notin.
      rewrite <-not_elem_of_dom.
      rewrite !dom_insert_L.
      rewrite !union_assoc_L.
      rewrite dom_empty_L.
      rewrite union_empty_r.
      solve_NoDup 6.
    }
    subst P.
    iEval (rewrite big_opM_insert_delete) in "excl".
    match goal with
    | |- context G [delete _ ?p] => set P := p
    end.
    assert (delete p_tx2 P = P) as ->.
    {
      subst P.
      apply delete_notin.
      rewrite <-not_elem_of_dom.
      rewrite !dom_insert_L.
      rewrite !union_assoc_L.
      rewrite dom_empty_L.
      rewrite union_empty_r.
      solve_NoDup 7.
    }
    subst P.
    iEval (rewrite big_opM_insert_delete) in "excl".
    match goal with
    | |- context G [delete _ ?p] => set P := p
    end.
    assert (delete p_tx3 P = P) as ->.
    {
      subst P.
      apply delete_notin.
      rewrite <-not_elem_of_dom.
      rewrite !dom_insert_L.
      rewrite !union_assoc_L.
      rewrite dom_empty_L.
      rewrite union_empty_r.
      solve_NoDup 8.
    }
    subst P.
    iEval (rewrite big_opM_insert_delete) in "excl".
    match goal with
    | |- context G [delete _ ?p] => set P := p
    end.
    assert (delete p_prog0 P = P) as ->.
    {
      subst P.
      apply delete_notin.
      rewrite <-not_elem_of_dom.
      rewrite !dom_insert_L.
      rewrite !union_assoc_L.
      rewrite dom_empty_L.
      rewrite union_empty_r.
      solve_NoDup 0.
    }
    subst P.
    iEval (rewrite big_opM_insert_delete) in "excl".
    match goal with
    | |- context G [delete _ ?p] => set P := p
    end.
    assert (delete p_prog1 P = P) as ->.
    {
      subst P.
      apply delete_notin.
      rewrite <-not_elem_of_dom.
      rewrite !dom_insert_L.
      rewrite !union_assoc_L.
      rewrite dom_empty_L.
      rewrite union_empty_r.
      solve_NoDup 1.
    }
    subst P.
    iEval (rewrite big_opM_insert_delete) in "excl".
    match goal with
    | |- context G [delete _ ?p] => set P := p
    end.
    assert (delete p_prog2 P = P) as ->.
    {
      subst P.
      apply delete_notin.
      rewrite <-not_elem_of_dom.
      rewrite !dom_insert_L.
      rewrite dom_empty_L.
      rewrite union_empty_r.
      solve_NoDup 2.
    }
    subst P.
    iEval (rewrite big_sepM_singleton) in "excl".
    iDestruct "excl" as "(exclpshare & exclrx0 & exclrx1 & exclrx2 & exclex3 & excltx0 & excltx1 & excltx2 & excltx3 & exclp0 & exclp1 & exclp2 & exclp3)".

    iDestruct (big_sepM_subseteq _ (get_own_gmap σ)
                {[p_share := Some V1; p_rx0 := None ; p_rx1 := None; p_rx2 := None; p_rx3 := None;
                  p_tx0 := None ; p_tx1 := None; p_tx2 := None; p_tx3 := None;
                  p_prog0 := Some V0; p_prog1 := Some V1; p_prog2 := Some V2; p_prog3 := Some V3]} with "Hown") as "own".
    {
      apply own_layout_get_own_gmap.
      apply pgt_own.
    }
    iEval (rewrite big_opM_insert_delete) in "own".
    match goal with
    | |- context G [delete _ ?p] => set P := p
    end.
    assert (delete p_share P = P) as ->.
    {
      subst P.
      apply delete_notin.
      rewrite <-not_elem_of_dom.
      rewrite !dom_insert_L.
      rewrite !union_assoc_L.
      rewrite dom_empty_L.
      rewrite union_empty_r.
      solve_NoDup 4.
    }
    subst P.
    iEval (rewrite big_opM_insert_delete) in "own".
    match goal with
    | |- context G [delete _ ?p] => set P := p
    end.
    assert (delete p_rx0 P = P) as ->.
    {
      subst P.
      apply delete_notin.
      rewrite <-not_elem_of_dom.
      rewrite !dom_insert_L.
      rewrite !union_assoc_L.
      rewrite dom_empty_L.
      rewrite union_empty_r.
      solve_NoDup 9.
    }
    subst P.
    iEval (rewrite big_opM_insert_delete) in "own".
    match goal with
    | |- context G [delete _ ?p] => set P := p
    end.
    assert (delete p_rx1 P = P) as ->.
    {
      subst P.
      apply delete_notin.
      rewrite <-not_elem_of_dom.
      rewrite !dom_insert_L.
      rewrite !union_assoc_L.
      rewrite dom_empty_L.
      rewrite union_empty_r.
      solve_NoDup 10.
    }
    subst P.
    iEval (rewrite big_opM_insert_delete) in "own".
    match goal with
    | |- context G [delete _ ?p] => set P := p
    end.
    assert (delete p_rx2 P = P) as ->.
    {
      subst P.
      apply delete_notin.
      rewrite <-not_elem_of_dom.
      rewrite !dom_insert_L.
      rewrite !union_assoc_L.
      rewrite dom_empty_L.
      rewrite union_empty_r.
      solve_NoDup 11.
    }
    subst P.
    iEval (rewrite big_opM_insert_delete) in "own".
    match goal with
    | |- context G [delete _ ?p] => set P := p
    end.
    assert (delete p_rx3 P = P) as ->.
    {
      subst P.
      apply delete_notin.
      rewrite <-not_elem_of_dom.
      rewrite !dom_insert_L.
      rewrite !union_assoc_L.
      rewrite dom_empty_L.
      rewrite union_empty_r.
      solve_NoDup 12.
    }
    subst P.
    iEval (rewrite big_opM_insert_delete) in "own".
    match goal with
    | |- context G [delete _ ?p] => set P := p
    end.
    assert (delete p_tx0 P = P) as ->.
    {
      subst P.
      apply delete_notin.
      rewrite <-not_elem_of_dom.
      rewrite !dom_insert_L.
      rewrite !union_assoc_L.
      rewrite dom_empty_L.
      rewrite union_empty_r.
      solve_NoDup 5.
    }
    subst P.
    iEval (rewrite big_opM_insert_delete) in "own".
    match goal with
    | |- context G [delete _ ?p] => set P := p
    end.
    assert (delete p_tx1 P = P) as ->.
    {
      subst P.
      apply delete_notin.
      rewrite <-not_elem_of_dom.
      rewrite !dom_insert_L.
      rewrite !union_assoc_L.
      rewrite dom_empty_L.
      rewrite union_empty_r.
      solve_NoDup 6.
    }
    subst P.
    iEval (rewrite big_opM_insert_delete) in "own".
    match goal with
    | |- context G [delete _ ?p] => set P := p
    end.
    assert (delete p_tx2 P = P) as ->.
    {
      subst P.
      apply delete_notin.
      rewrite <-not_elem_of_dom.
      rewrite !dom_insert_L.
      rewrite !union_assoc_L.
      rewrite dom_empty_L.
      rewrite union_empty_r.
      solve_NoDup 7.
    }
    subst P.
    iEval (rewrite big_opM_insert_delete) in "own".
    match goal with
    | |- context G [delete _ ?p] => set P := p
    end.
    assert (delete p_tx3 P = P) as ->.
    {
      subst P.
      apply delete_notin.
      rewrite <-not_elem_of_dom.
      rewrite !dom_insert_L.
      rewrite !union_assoc_L.
      rewrite dom_empty_L.
      rewrite union_empty_r.
      solve_NoDup 8.
    }
    subst P.
    iEval (rewrite big_opM_insert_delete) in "own".
    match goal with
    | |- context G [delete _ ?p] => set P := p
    end.
    assert (delete p_prog0 P = P) as ->.
    {
      subst P.
      apply delete_notin.
      rewrite <-not_elem_of_dom.
      rewrite !dom_insert_L.
      rewrite !union_assoc_L.
      rewrite dom_empty_L.
      rewrite union_empty_r.
      solve_NoDup 0.
    }
    subst P.
    iEval (rewrite big_opM_insert_delete) in "own".
    match goal with
    | |- context G [delete _ ?p] => set P := p
    end.
    assert (delete p_prog1 P = P) as ->.
    {
      subst P.
      apply delete_notin.
      rewrite <-not_elem_of_dom.
      rewrite !dom_insert_L.
      rewrite !union_assoc_L.
      rewrite dom_empty_L.
      rewrite union_empty_r.
      solve_NoDup 1.
    }
    subst P.
    iEval (rewrite big_opM_insert_delete) in "own".
    match goal with
    | |- context G [delete _ ?p] => set P := p
    end.
    assert (delete p_prog2 P = P) as ->.
    {
      subst P.
      apply delete_notin.
      rewrite <-not_elem_of_dom.
      rewrite !dom_insert_L.
      rewrite dom_empty_L.
      rewrite union_empty_r.
      solve_NoDup 2.
    }
    subst P.
    iEval (rewrite big_sepM_singleton) in "own".
    iDestruct "own" as "(ownpshare & ownrx0 & ownrx1 & ownrx2 & ownex3 & owntx0 & owntx1 & owntx2 & owntx3 & ownp0 & ownp1 & ownp2 & ownp3)".

    (** extract mb **)
    iDestruct (ghost_map_elem_persist with "mb0TX") as ">mb0TX".
    iDestruct (ghost_map_elem_persist with "mb1TX") as ">mb1TX".
    iDestruct (ghost_map_elem_persist with "mb2TX") as ">mb2TX".
    iDestruct (ghost_map_elem_persist with "mb3TX") as ">mb3TX".
    iDestruct (ghost_map_elem_persist with "mb0RX") as ">mb0RX".
    iDestruct (ghost_map_elem_persist with "mb1RX") as ">mb1RX".
    iDestruct (ghost_map_elem_persist with "mb2RX") as ">mb2RX".
    iDestruct (ghost_map_elem_persist with "mb3RX") as ">mb3RX".

    iModIntro.

    (* allocate VMProps *)
    set pgt := (get_page_table σ).
    iExists [True%I;
             (vmprop_unknown V1 up_slice_trans up_slice_rxs {[W0 := (V1, V3, {[p_share]}, Sharing, true)]});
             (vmprop_unknown V2 up_slice_trans up_slice_rxs {[W0 := (V1, V3, {[p_share]}, Sharing, true)]});
             (vmprop_unknown V3 up_slice_trans up_slice_rxs {[W0 := (V1, V3, {[p_share]}, Sharing, true)]})].
    iSimpl.
    iSplit; first done.

    (* frame state_interp *)
    iSplitL "Hσmem Hσreg Hσaccess Hσown Hσexcl Hσrxs Hσmb Hσhpool Hσtrans Hσretri".
    iFrame.
    rewrite /inv_trans_wellformed /inv_trans_wellformed'.
    rewrite /inv_trans_pgt_consistent /inv_trans_pgt_consistent'.
    rewrite Htrans /=.
    repeat iSplit.
    done.
    {
      rewrite /inv_trans_pg_num_ub.
      iPureIntro.
      rewrite map_Forall_singleton.
      rewrite size_singleton.
      solve_finz +.
    }
    {
      rewrite /inv_trans_sndr_rcvr_neq.
      iPureIntro.
      rewrite map_Forall_singleton.
      simpl.
      solve_finz +.
    }
    {
      rewrite /inv_finite_handles.
      iPureIntro.
      rewrite dom_singleton_L //.
    }
    {
      iPureIntro.
      rewrite /inv_trans_ps_disj Htrans /inv_trans_ps_disj' /=.
      rewrite map_Forall_singleton /=.
      rewrite delete_singleton.
      rewrite /pages_in_trans'. rewrite map_fold_empty.
      set_solver +.
    }
    {
      iPureIntro.
      rewrite map_Forall_singleton /=.
      intros ? Hlk.
      rewrite elem_of_singleton in Hlk.
      subst p.
      apply pgt_share.
    }

    iIntros "(VMProp0 & VMProp1 & VMProp2 & VMProp3 & _)".
    rewrite /scheduled /machine.scheduler //= /scheduler Hcur //=.

    iDestruct (VMProp_split with "VMProp1") as "[VMProp1_half VMProp1_half']".
    iDestruct (VMProp_split with "VMProp2") as "[VMProp2_half VMProp2_half']".
    iDestruct (VMProp_split with "VMProp3") as "[VMProp3_half VMProp3_half']".

    (* pose proof (@access_split rywu_vmconfig irisΣ VMG 1 V2) as Hsplit. *)
    (* rewrite access_mapsto_eq /access_mapsto_def in Hsplit. *)
    (* iDestruct "access3" as "(access3 & access3')". *)
    iAssert ((V2, RX) ↪[ mb_gname ]□ p_rx2 ∗ (V2, RX) ↪[ mb_gname ]□ p_rx2)%I with "[mb2RX]" as "(mb2RX & mb2RX')".
    {
      iDestruct "mb2RX" as "#mb2RX".
      iFrame "mb2RX".
    }
    iAssert ((V3, RX) ↪[ mb_gname ]□ p_rx3 ∗ (V3, RX) ↪[ mb_gname ]□ p_rx3)%I with "[mb3RX]" as "(mb3RX & mb3RX')".
    {
      iDestruct "mb3RX" as "#mb3RX".
      iFrame "mb3RX".
    }

    iSplitL "Hreg0 Htrans Hp p_tx0 p_rx0 p_rx1 p_rx2 p_rx3 VMProp0 VMProp1_half' VMProp2_half' VMProp3_half'
            mb0RX mb1RX mb2RX mb3RX RX0St RX1St RX2St RX3St mb0TX access0 exclp0 exclrx0 excltx0 ownp0 ownrx0 owntx0".
    iIntros "_".
    iPoseProof (up_ftlr0 p_share p_prog0 p_tx0 p_rx0
                {[V0 := None; V1 := None; V2 := None; V3 := None]}) as "wp0".
    rewrite /interp_execute_prim.
    iSimpl in "wp0".
    iApply "wp0". iClear "wp0".
    rewrite /up_interp_access0. rewrite /interp_access_prim.
    repeat iSplit;try iPureIntro.
    apply trans_wf_prim.
    apply rxs_wf_prim_diag.
    apply rxs_wf_prim_eq.
    apply rxs_wf_prim_none.
    apply rxs_wf_prim_zero.
    {
      iSplitL "Hreg0".
      iExists (get_reg_files σ !!! V0).
      unfold get_reg_gmap_vm.
      iSplit.
      iPureIntro.
      unfold base_extra.is_total_gmap.
      apply Htotal_reg.
      simpl.
      {
        set g := (λ p0 : reg_name * Addr, (p0.1, 0%fin, p0.2)).
        unfold V0. simpl.
        set l := (σ.1.1.1.1.1 !!! 0%fin).
        iEval (rewrite big_opM_map_to_list) in "Hreg0".
        rewrite map_to_list_to_map.
        rewrite big_opL_fmap.
        subst g.
        simpl.
        rewrite big_opM_map_to_list.
        iFrame "Hreg0".
        subst g.
        apply NoDup_fmap_fst.
        intros [x1 x2] y1 y2 Hh Hh'.
        rewrite elem_of_list_In in Hh.
        rewrite elem_of_list_In in Hh'.
        rewrite in_map_iff in Hh.
        rewrite in_map_iff in Hh'.
        destruct Hh as [(x & x') [Hheq Hh]].
        destruct Hh' as [(t & t') [Hh'eq Hh']].
        simpl in Hheq.
        simpl in Hh'eq.
        inversion Hheq.
        inversion Hh'eq.
        simplify_eq.
        clear Hheq Hh'eq.
        rewrite <-elem_of_list_In in Hh.
        rewrite <-elem_of_list_In in Hh'.
        apply map_to_list_unique with l x1; auto.
        apply NoDup_fmap_2.
        intros a b abeq.
        inversion abeq.
        destruct a, b; simpl in *.
        by simplify_eq.
        apply NoDup_map_to_list.
      }
      iSplitL "mb0TX p_tx0 excltx0 owntx0".
      unfold tx_page.
      iSplitR "p_tx0".
      rewrite mb_mapsto_eq /mb_mapsto_def.
      rewrite excl_mapsto_eq own_mapsto_eq /excl_mapsto_def /own_mapsto_def.
      iSimpl. iFrame.
      iExists mem_p_tx0.
      (* rewrite difference_empty_L. *)
      (* unfold transaction_pagetable_entries_owned. *)
      (* unfold retrieved_transaction_owned. *)
      (* unfold big_sepFM. simpl. *)
      (* rewrite map_filter_singleton. *)
      (* jj *)
      (* rewrite !big_sepM_empty. *)
      (* assert (({[p_prog3; p_tx3; p_rx3]} ∖ {[p_rx3; p_tx3]}) = {[p_prog3]}) as ->. *)
      (* { *)
      (*   rewrite !difference_union_distr_l_L. *)
      (*   rewrite difference_disjoint_L. *)
      (*   assert ({[p_tx3]} ∖ {[p_rx3; p_tx3]} = ∅) as ->. *)
      (*   { set_solver +. } *)
      (*   assert ({[p_rx3]} ∖ {[p_rx3; p_tx3]} = ∅) as ->. *)
      (*   { set_solver +. } *)
      (*   set_solver +. *)
      (*   apply disjoint_singleton_l. *)
      (*   intros contra. *)
      (*   rewrite elem_of_union in contra. *)
      (*   rewrite !elem_of_singleton in contra. *)
      (*   solve_NoDup_pre'. *)
      (*   solve_NoDup_pre'' 2 8. *)
      (*   solve_NoDup_pre'' 2 5. *)
      (* } *)
      (* unfold pagetable_entries_excl_owned. *)
      (* unfold logrel.pgt. *)
      (* rewrite !big_sepS_singleton. *)
      unfold memory_page. iSplit. iPureIntro.
      (* TODO *)
   (*    rewrite Hdom_mem_p_tx0. *)
   (*    apply set_of_addr_singleton. *)
   (*    rewrite mem_mapsto_eq /mem_mapsto_def. *)
   (*    iFrame "p_tx3". *)
   (*    rewrite access_mapsto_eq /access_mapsto_def /=. *)
   (*    assert ({[p_tx3; p_rx3; p_prog3]} = {[p_prog3; p_tx3; p_rx3]}) as -> by set_solver +. *)
   (*    iFrame "access3". *)
   (*    unfold rx_page. *)

   (*    iSplitL "mb2RX' excl3 own3". *)
   (*    { *)
   (*      rewrite excl_mapsto_eq /excl_mapsto_def. *)
   (*      rewrite own_mapsto_eq /own_mapsto_def. *)
   (*      rewrite mb_mapsto_eq /mb_mapsto_def. *)
   (*      iFrame. *)
   (*    } *)

   (*    iSplit. iPureIntro. set_solver +. *)
   (*    iSplit. iPureIntro. set_solver +. *)

   (*    iSplitL "excl5 own5". *)
   (*    { *)
   (*      rewrite excl_mapsto_eq /excl_mapsto_def. *)
   (*      rewrite own_mapsto_eq /own_mapsto_def. *)
   (*      iFrame. *)
   (*    } *)

   (*    iSplit; first done. *)
   (*    iSplit; first done. *)

   (*    iExists mem5. unfold memory_pages. iSplit. *)
   (*    iPureIntro. *)
   (*    rewrite /retrieved_lending_memory_pages. *)
   (*    rewrite map_filter_empty pages_in_trans_empty union_empty_r_L //. *)
   (*    rewrite mem_mapsto_eq /mem_mapsto_def. *)
   (*    iFrame "Hmem2". *)
   (*  } *)

   (*  iDestruct (lending_machine0 p_prog1 p_tx1 p_prog3 p_tx3 p_rx1 p_rx2 p_rx3 addr txbase rxbase with "[-]") as "HWP". *)
   (*  { *)
   (*    assumption. *)
   (*  } *)
   (*  { *)
   (*    assumption. *)
   (*  } *)
   (*  { *)
   (*    assumption. *)
   (*  } *)
   (*  { *)
   (*    solve_NoDup 0. *)
   (*  } *)
   (*  { *)
   (*    clear -Hnodup_p. *)
   (*    intros <-. *)
   (*    solve_NoDup_pre'' 6 9. *)
   (*  } *)
   (*  { *)
   (*    clear -Hnodup_p. *)
   (*    intros <-. *)
   (*    solve_NoDup_pre'' 0 9. *)
   (*  } *)
   (*  { *)
   (*    clear -Hnodup_p. *)
   (*    intros <-. *)
   (*    solve_NoDup_pre'' 3 9. *)
   (*  } *)
   (*  { *)
   (*    clear -Hnodup_p. *)
   (*    intros <-. *)
   (*    solve_NoDup_pre'' 3 6. *)
   (*  } *)
   (*  { *)
   (*    program_in_seq. *)
   (*  } *)
   (*  { *)
   (*    iSplitL "mem_p_prog1". *)
   (*    { *)
   (*      unfold program. *)
   (*      iEval (rewrite big_opM_map_to_list) in "mem_p_prog1". *)
   (*      rewrite big_sepL2_alt. *)
   (*      iSplitR "mem_p_prog1". *)
   (*      { *)
   (*        simpl. *)
   (*        by iPureIntro. *)
   (*      } *)
   (*      { *)
   (*        rewrite mem_mapsto_eq /mem_mapsto_def. *)
   (*        assert (mem_p_prog1 ⊆ σ.1.2) as Hsubseteq. *)
   (*        { *)
   (*          rewrite Hunion_mem'. *)
   (*          apply map_union_subseteq_r'. *)
   (*          assumption. *)
   (*          apply map_union_subseteq_r'. *)
   (*          assumption. *)
   (*          done. *)
   (*        } *)
   (*        iApply (memory_list_gmap _ _ _ mem_p_prog1 σ). *)
   (*        - rewrite fst_zip. *)
   (*          + apply finz_seq_NoDup'. *)
   (*            simpl. *)
   (*            pose proof (last_addr_in_bound p_prog1). *)
   (*            solve_finz. *)
   (*          + simpl. *)
   (*            lia. *)
   (*        - apply HmemH1; done. *)
   (*        - by iFrame. *)
   (*      } *)
   (*    } *)
   (*    iSplitL "mem_p". *)
   (*    { *)
   (*      rewrite mem_mapsto_eq /mem_mapsto_def. *)
   (*      assert (mem ⊆ σ.1.2) as Hsubseteq. *)
   (*      { *)
   (*        rewrite Hunion_mem'. *)
   (*        apply map_union_subseteq_r'. *)
   (*        assumption. *)
   (*        apply map_union_subseteq_l'. *)
   (*        apply map_union_subseteq_l'. *)
   (*        apply map_union_subseteq_r'. *)
   (*        assumption. *)
   (*        done. *)
   (*      } *)
   (*      assert (of_imm addr ∈ set_of_addr {[tpa addr]}) as H. *)
   (*      { *)
   (*        apply elem_of_set_of_addr with (tpa addr). *)
   (*        apply elem_of_addr_of_page_tpa. *)
   (*        set_solver +. *)
   (*      } *)
   (*      rewrite <-Hdom_mem_p in H. *)
   (*      rewrite elem_of_dom in H. *)
   (*      destruct H as [waddr Hwaddr]. *)
   (*      iDestruct (big_sepM_delete _ mem addr waddr with "mem_p") as "(mem & memacc)". *)
   (*      assumption. *)
   (*      iExists waddr. *)
   (*      iFrame. *)
   (*    } *)
   (*    iSplitL "p_tx1". *)
   (*    { *)
   (*      unfold memory_page. *)
   (*      iExists mem_p_tx1. iSplit. rewrite Hdom_mem_p_tx1. iPureIntro. *)
   (*      rewrite set_of_addr_singleton. *)
   (*      rewrite to_pid_aligned_eq. *)
   (*      reflexivity. *)
   (*      rewrite mem_mapsto_eq /mem_mapsto_def /=. *)
   (*      iFrame. *)
   (*    } *)
   (*    rewrite rx_state_mapsto_eq /rx_state_mapsto_def /=. *)
   (*    iFrame "RX0St RX1St RX2St". *)
   (*    unfold rx_page. *)
   (*    rewrite mb_mapsto_eq /mb_mapsto_def /=. *)
   (*    rewrite to_pid_aligned_eq. *)
   (*    iFrame "mb0TX". *)
   (*    iFrame "PCz". *)
   (*    rewrite access_mapsto_eq /access_mapsto_def /=. *)
   (*    rewrite big_sepS_singleton. *)
   (*    iSplitL "excl6 own6". *)
   (*    { *)
   (*      rewrite excl_mapsto_eq own_mapsto_eq /excl_mapsto_def /own_mapsto_def /=. *)
   (*      iFrame. *)
   (*    } *)
   (*    iSplitL "access1". *)
   (*    { *)
   (*      assert ({[tpa addr; p_prog1; p_tx1]} = {[tpa addr]} ∪ {[p_prog1; p_tx1]}) as ->. *)
   (*      { *)
   (*        set_solver +. *)
   (*      } *)
   (*      iFrame. *)
   (*    } *)
   (*    iSplitL "R0z". *)
   (*    iExists r0_; iFrame. *)
   (*    iSplitL "R1z". *)
   (*    iExists r1_; iFrame. *)
   (*    iSplitL "R2z". *)
   (*    iExists r2_; iFrame. *)
   (*    iSplitL "R3z". *)
   (*    iExists r3_; iFrame. *)
   (*    iSplitL "R4z". *)
   (*    iExists r4_; iFrame. *)
   (*    iSplitL "R5z". *)
   (*    iExists r5_; iFrame. *)
   (*    iFrame "VMProp0". *)
   (*    iFrame "VMProp1_half'". *)
   (*    iFrame "VMProp2_half'". *)
   (*    iFrame "Hp". *)
   (*    iFrame. *)

   (*    iSplitL "p_rx1 excl1 own1". *)
   (*    iSplitR "p_rx1". *)
   (*    rewrite excl_mapsto_eq own_mapsto_eq /excl_mapsto_def /own_mapsto_def /=. *)
   (*    iFrame. *)
   (*    unfold memory_page. *)
   (*    iExists mem_p_rx1. iSplit. rewrite Hdom_mem_p_rx1. iPureIntro. *)
   (*    apply set_of_addr_singleton. *)
   (*    rewrite mem_mapsto_eq /mem_mapsto_def /=. *)
   (*    iFrame "p_rx1". *)
   (*    iSplitL "p_rx2 excl2 own2". *)
   (*    iSplitR "p_rx2". *)
   (*    rewrite excl_mapsto_eq own_mapsto_eq /excl_mapsto_def /own_mapsto_def /=. *)
   (*    iFrame. *)
   (*    unfold memory_page. *)
   (*    iExists mem_p_rx2. iSplit. rewrite Hdom_mem_p_rx2. iPureIntro. *)
   (*    apply set_of_addr_singleton. *)
   (*    rewrite mem_mapsto_eq /mem_mapsto_def /=. *)
   (*    iFrame "p_rx2". *)

   (*    unfold memory_page. *)
   (*    iExists mem_p_rx3. iSplit. rewrite Hdom_mem_p_rx3. iPureIntro. *)
   (*    apply set_of_addr_singleton. *)
   (*    rewrite mem_mapsto_eq /mem_mapsto_def /=. *)
   (*    iFrame "p_rx3". *)
   (*  } *)

   (*  iApply (wp_mono with "HWP"). *)
   (*  intros k. *)
   (*  simpl. *)
   (*  iIntros "[$ _]". *)

   (*  iSplitL "VMProp1_half PC1 R01 R11 R21 R31 R41 R51 mem_p_prog2 p_tx2 mb1TX access2". *)
   (*  iApply (lending_machine1 p_prog2 p_tx2 p_rx2 addr rxbase). *)
   (*  { *)
   (*    assumption. *)
   (*  } *)
   (*  { *)
   (*    assumption. *)
   (*  } *)
   (*  { *)
   (*    clear -Hnodup_p. *)
   (*    intros contra. *)
   (*    rewrite !elem_of_union in contra. *)
   (*    rewrite !elem_of_singleton in contra. *)
   (*    destruct contra as [[H | H] | H]; subst. *)
   (*    solve_NoDup_pre'' 1 9. *)
   (*    solve_NoDup_pre'' 1 4. *)
   (*    solve_NoDup_pre'' 1 7. *)
   (*  } *)
   (*  { *)
   (*    clear -Hnodup_p. *)
   (*    intros contra. *)
   (*    subst. *)
   (*    solve_NoDup_pre'' 7 9. *)
   (*  } *)
   (*  { *)
   (*    clear -Hnodup_p. *)
   (*    intros contra. *)
   (*    subst. *)
   (*    solve_NoDup_pre'' 1 9. *)
   (*  } *)
   (*  { *)
   (*    clear -Hnodup_p. *)
   (*    intros contra. *)
   (*    subst. *)
   (*    solve_NoDup_pre'' 4 9. *)
   (*  } *)
   (*  { *)
   (*    clear -Hnodup_p. *)
   (*    intros contra. *)
   (*    subst. *)
   (*    solve_NoDup_pre'' 4 7. *)
   (*  } *)
   (*  { *)
   (*    program_in_seq. *)
   (*  } *)
   (*  iFrame. *)
   (*  iSplitL "mem_p_prog2". *)
   (*  unfold program. *)
   (*  iEval (rewrite big_opM_map_to_list) in "mem_p_prog2". *)
   (*  rewrite big_sepL2_alt. *)
   (*  iSplit; first done. *)
   (*  rewrite mem_mapsto_eq /mem_mapsto_def. *)
   (*  { *)
   (*    assert (mem_p_prog2 ⊆ σ.1.2) as Hsubseteq. *)
   (*    { *)
   (*      rewrite Hunion_mem'. *)
   (*      apply map_union_subseteq_r'. *)
   (*      assumption. *)
   (*      apply map_union_subseteq_l'. *)
   (*      apply map_union_subseteq_r'. *)
   (*      assumption. *)
   (*      done. *)
   (*    } *)
   (*    iApply (memory_list_gmap _ _ _ mem_p_prog2 σ). *)
   (*    - rewrite fst_zip. *)
   (*      + apply finz_seq_NoDup'. *)
   (*        simpl. *)
   (*        pose proof (last_addr_in_bound p_prog2). *)
   (*        solve_finz. *)
   (*      + simpl. *)
   (*        lia. *)
   (*    - apply HmemH2; done. *)
   (*    - by iFrame. *)
   (*  } *)
   (*  iSplitL "p_tx2". *)
   (*  { *)
   (*    unfold memory_page. *)
   (*    iExists mem_p_tx2. iSplit. rewrite Hdom_mem_p_tx2. iPureIntro. *)
   (*    rewrite set_of_addr_singleton. *)
   (*    rewrite to_pid_aligned_eq. *)
   (*    reflexivity. *)
   (*    rewrite mem_mapsto_eq /mem_mapsto_def /=. *)
   (*    iFrame. *)
   (*  } *)

   (*  iSplitL "access2". *)
   (*  { *)
   (*    rewrite access_mapsto_eq /access_mapsto_def. *)
   (*    simpl. *)
   (*    rewrite !to_pid_aligned_eq. *)
   (*    iFrame "access2". *)
   (*  } *)

   (*  iSplitL "mb1TX". *)
   (*  { *)
   (*    rewrite mb_mapsto_eq /mb_mapsto_def /=. *)
   (*    rewrite to_pid_aligned_eq. *)
   (*    iFrame. *)
   (*  } *)

   (*  iSplitL "R01". *)
   (*  iExists r0__. *)
   (*  iFrame. *)
   (*  iSplitL "R11". *)
   (*  iExists r1__. *)
   (*  iFrame. *)
   (*  iSplitL "R21". *)
   (*  iExists r2__. *)
   (*  iFrame. *)
   (*  iSplitL "R31". *)
   (*  iExists r3__. *)
   (*  iFrame. *)
   (*  iSplitL "R41". *)
   (*  iExists r4__. *)
   (*  iFrame. *)
   (*  iExists r5__. *)
   (*  iFrame. *)

   (*  iSplitR ""; last done. *)
   (*  iApply (mtms_ftlr p_prog3 p_tx3 p_rx3 with "[-] []"). *)
   (*  2: { iPureIntro. cbn. done. } *)
   (*  { rewrite /mtms_interp_access /interp_access. *)
   (*    iSplitL "Hreg2". *)
   (*    iExists (get_reg_files σ !!! V2). *)
   (*    unfold get_reg_gmap_vm. *)
   (*    iSplit. *)
   (*    iPureIntro. *)
   (*    unfold base_extra.is_total_gmap. *)
   (*    apply Htotal_reg. *)
   (*    simpl. *)
   (*    { *)
   (*      set g := (λ p0 : reg_name * Addr, (p0.1, 2%fin, p0.2)). *)
   (*      unfold V2. *)
   (*      simpl. *)
   (*      set l := (σ.1.1.1.1.1 !!! 2%fin). *)
   (*      iEval (rewrite big_opM_map_to_list) in "Hreg2". *)
   (*      rewrite map_to_list_to_map. *)
   (*      rewrite big_opL_fmap. *)
   (*      subst g. *)
   (*      simpl. *)
   (*      rewrite big_opM_map_to_list. *)
   (*      iFrame "Hreg2". *)
   (*      subst g. *)
   (*      apply NoDup_fmap_fst. *)
   (*      intros [x1 x2] y1 y2 Hh Hh'. *)
   (*      rewrite elem_of_list_In in Hh. *)
   (*      rewrite elem_of_list_In in Hh'. *)
   (*      rewrite in_map_iff in Hh. *)
   (*      rewrite in_map_iff in Hh'. *)
   (*      destruct Hh as [(x & x') [Hheq Hh]]. *)
   (*      destruct Hh' as [(t & t') [Hh'eq Hh']]. *)
   (*      simpl in Hheq. *)
   (*      simpl in Hh'eq. *)
   (*      inversion Hheq. *)
   (*      inversion Hh'eq. *)
   (*      simplify_eq. *)
   (*      clear Hheq Hh'eq. *)
   (*      rewrite <-elem_of_list_In in Hh. *)
   (*      rewrite <-elem_of_list_In in Hh'. *)
   (*      apply map_to_list_unique with l x1; auto. *)
   (*      apply NoDup_fmap_2. *)
   (*      intros a b abeq. *)
   (*      inversion abeq. *)
   (*      destruct a, b; simpl in *. *)
   (*      by simplify_eq. *)
   (*      apply NoDup_map_to_list. *)
   (*    } *)
   (*    iFrame "VMProp2_half". *)
   (*    rewrite difference_empty_L. *)
   (*    unfold transaction_pagetable_entries_owned. *)
   (*    unfold retrieved_transaction_owned. *)
   (*    unfold big_sepFM. simpl. *)
   (*    rewrite map_filter_empty. *)
   (*    rewrite !big_sepM_empty. *)
   (*    assert (({[p_prog3; p_tx3; p_rx3]} ∖ {[p_rx3; p_tx3]}) = {[p_prog3]}) as ->. *)
   (*    { *)
   (*      rewrite !difference_union_distr_l_L. *)
   (*      rewrite difference_disjoint_L. *)
   (*      assert ({[p_tx3]} ∖ {[p_rx3; p_tx3]} = ∅) as ->. *)
   (*      { set_solver +. } *)
   (*      assert ({[p_rx3]} ∖ {[p_rx3; p_tx3]} = ∅) as ->. *)
   (*      { set_solver +. } *)
   (*      set_solver +. *)
   (*      apply disjoint_singleton_l. *)
   (*      intros contra. *)
   (*      rewrite elem_of_union in contra. *)
   (*      rewrite !elem_of_singleton in contra. *)
   (*      solve_NoDup_pre'. *)
   (*      solve_NoDup_pre'' 2 8. *)
   (*      solve_NoDup_pre'' 2 5. *)
   (*    } *)
   (*    unfold pagetable_entries_excl_owned. *)
   (*    unfold logrel.pgt. *)
   (*    rewrite !big_sepS_singleton. *)
   (*    unfold tx_page. *)
   (*    iSplitL "mb2TX p_tx3 excl4 own4". *)
   (*    iSplitR "p_tx3". *)
   (*    rewrite mb_mapsto_eq /mb_mapsto_def. *)
   (*    rewrite excl_mapsto_eq own_mapsto_eq /excl_mapsto_def /own_mapsto_def. *)
   (*    iFrame. *)
   (*    iExists mem_p_tx3. unfold memory_page. iSplit. iPureIntro. *)
   (*    rewrite Hdom_mem_p_tx3. *)
   (*    apply set_of_addr_singleton. *)
   (*    rewrite mem_mapsto_eq /mem_mapsto_def. *)
   (*    iFrame "p_tx3". *)
   (*    rewrite access_mapsto_eq /access_mapsto_def /=. *)
   (*    assert ({[p_tx3; p_rx3; p_prog3]} = {[p_prog3; p_tx3; p_rx3]}) as -> by set_solver +. *)
   (*    iFrame "access3". *)
   (*    unfold rx_page. *)

   (*    iSplitL "mb2RX' excl3 own3". *)
   (*    { *)
   (*      rewrite excl_mapsto_eq /excl_mapsto_def. *)
   (*      rewrite own_mapsto_eq /own_mapsto_def. *)
   (*      rewrite mb_mapsto_eq /mb_mapsto_def. *)
   (*      iFrame. *)
   (*    } *)

   (*    iSplit. iPureIntro. set_solver +. *)
   (*    iSplit. iPureIntro. set_solver +. *)

   (*    iSplitL "excl5 own5". *)
   (*    { *)
   (*      rewrite excl_mapsto_eq /excl_mapsto_def. *)
   (*      rewrite own_mapsto_eq /own_mapsto_def. *)
   (*      iFrame. *)
   (*    } *)

   (*    iSplit; first done. *)
   (*    iSplit; first done. *)

   (*    iExists mem5. unfold memory_pages. iSplit. *)
   (*    iPureIntro. *)
   (*    rewrite /retrieved_lending_memory_pages. *)
   (*    rewrite map_filter_empty pages_in_trans_empty union_empty_r_L //. *)
   (*    rewrite mem_mapsto_eq /mem_mapsto_def. *)
   (*    iFrame "Hmem2". *)
   (*  } *)
   (* Qed. *)

End up_adequacy.
