From machine_program_logic.program_logic Require Import machine weakestpre adequacy.
From iris.algebra Require Import big_op.
From HypVeri Require Import machine_extra lifting.
From HypVeri.algebra Require Import base mailbox pagetable mem.
From HypVeri.lang Require Import reg_extra.
From HypVeri.examples Require Import instr utils.
From HypVeri.logrel Require Import logrel logrel_extra.
From HypVeri.examples.mem_trans_msg_send Require Import proof.
From HypVeri.examples.mem_trans_msg_send Require Import ftlr.
Require Import Setoid.

Section mtms_adequacy.
  Context `{hypparams: !HypervisorParameters}.
  
  Definition pgt (σ : state) (p_prog1 p_prog2 p_prog3 p_tx1 p_tx2 p_tx3 p_rx1 p_rx2 p_rx3 p : PID) :=    
    access_layout σ {[V0 := to_dfrac_agree (DfracOwn 1) {[p; p_prog1; p_tx1]};
                     V1 := to_dfrac_agree (DfracOwn 1) {[p_prog2; p_tx2; p_rx2]};
                     V2 := to_dfrac_agree (DfracOwn 1) {[p_tx3; p_rx3; p_prog3]}]} ∧
    excl_layout σ {[p_rx1 := true; p_rx2 := true; p_rx3 := true; p_tx3 := true; p_prog3 := true; p:= true]} ∧
    own_layout σ {[p_rx1 := None; p_rx2 := None; p_rx3 := None; p_tx3 := None; p_prog3 := Some V2; p:= Some V0]}.  

  Program Definition mem (σ : state) (p_prog1 p_prog2 p_prog3 p_tx1 p_tx2 p_tx3 p_rx1 p_rx2 p_rx3 : PID) (addr txbase rxbase : Imm) :=
    let mem := ((get_mem σ): gmap Addr Word)  in
    (∀ (m : gmap Addr Addr), dom m = set_of_addr {[p_prog1]} -> m ⊆ mem -> m = mem_page_program p_prog1 (lending_program0 addr txbase) _) ∧
    (∀ (m : gmap Addr Addr), dom m = set_of_addr {[p_prog2]} -> m ⊆ mem -> m = mem_page_program p_prog2 (lending_program1 addr rxbase) _) ∧
    ((set_of_addr {[p_prog1;p_prog2; tpa addr; p_prog3;p_tx1; p_tx2; p_tx3;p_rx1;p_rx2;p_rx3]}) ⊆ dom mem).
  Next Obligation. lia. Qed.
  Next Obligation. lia. Qed.  
  
  Definition regs (σ : state) (p_prog1 p_prog2 : PID)
    := reg_layout σ ({[PC:=of_pid p_prog1]}) V0
       ∧ reg_layout σ ({[PC:=of_pid p_prog2]}) V1
       ∧ ∀ i rn, is_Some (((get_reg_files σ) !!! i) !! rn).
  
  Definition mailbox (σ: state) (p_tx1 p_tx2 p_tx3 p_rx1 p_rx2 p_rx3 : PID):=
    mailbox_layout σ {[(V0, TX) := p_tx1; (V1, TX) := p_tx2; (V2, TX) := p_tx3;
                      (V0, RX) := p_rx1; (V1, RX) := p_rx2; (V2, RX) := p_rx3]} ∧
    rx_layout σ {[V0 := None; V1 := None; V2 := None]}.
  
  Definition transactions (σ: state):=
    dom (get_transactions σ) = valid_handles ∧
    map_Forall (λ k v, v = None) (get_transactions σ).  

  Definition initial_config (σ: state) (ms: list exec_mode) (φs : list (exec_mode -> Prop )):=
                  (get_current_vm σ) = V0 ∧
                  φs = [(λ m , m = HaltI); (λ _, False); (λ _, True)] ∧
                  ms = [ExecI;ExecI;ExecI] ∧
                    (∃ (p_prog1 p_prog2 p_prog3 p_tx1 p_tx2 p_tx3 p_rx1 p_rx2 p_rx3 : PID) (addr txbase rxbase : Imm),
                    of_pid p_tx1 = of_imm txbase ∧ of_pid p_rx2 = of_imm rxbase ∧ of_pid (tpa addr) = (of_imm addr) ∧    
                    NoDup' [p_prog1;p_prog2;p_prog3;p_tx1;p_tx2;p_tx3;p_rx1;p_rx2;p_rx3; tpa addr] ∧
                    (pgt σ p_prog1 p_prog2 p_prog3 p_tx1 p_tx2 p_tx3 p_rx1 p_rx2 p_rx3 (tpa addr)) ∧
                    (mem σ p_prog1 p_prog2 p_prog3 p_tx1 p_tx2 p_tx3 p_rx1 p_rx2 p_rx3 addr txbase rxbase) ∧
                    (regs σ p_prog1 p_prog2) ∧
                    (mailbox σ p_tx1 p_tx2 p_tx3 p_rx1 p_rx2 p_rx3)
                  ) ∧
                  transactions σ.
  
  Context {vm_preG: gen_VMPreG Addr VMID Word reg_name PID transaction_type irisΣ}.      

  Lemma memory_list_gmap (pid : PID) (mem_list : list Word) (Hle: length mem_list < (Z.to_nat page_size))
        (mem_gmap : gmap Addr Word) (σ : state)
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

  Lemma get_reg_gmap_split σ γ:
    ([∗ map] p↦w ∈ (get_reg_gmap σ) , p ↪[γ] w)%I ⊢ [∗ list] i ∈ ((list_of_vmids): list VMID), [∗ map] p↦w ∈ get_reg_gmap_vm σ i, p ↪[γ] w.
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
  Lemma adequacy (σ : state) (ms : list exec_mode) φs:
    (* we need assumptions to be able to allocate resources *)
    (* with these resources, we apply the specification and get the wptp *)
    (* along with some other stuff, then it should be enough to apply the adequacy theorem *)
    (initial_config σ ms φs) ->
    adequate ms σ ((λ φ, λ v _, φ v)<$> φs).
    (* φ : vm 0 is scheduled but halted *)
  Proof.
    intros Hinit.
    set (saved_props := (let (_, x, _, _) := iris_subG irisΣ (subG_refl irisΣ) in x)).
    set (prop_name := (let (_, _, x, _) := iris_subG irisΣ (subG_refl irisΣ) in x)).

    set (name_map := (let (_, _, _, x) := iris_subG irisΣ (subG_refl irisΣ) in x)).
    eapply (wp_adequacy irisΣ); auto.
    destruct Hinit as (Hcur & -> & -> & (p1 & p2 & p1p2ne & Hpgt & Hmem & Hreg) & Htrans).
    by simpl.
    intro Hinv.
    iIntros.
    destruct Hinit as ( Hcur & Hinit).
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

    iModIntro.
    iIntros (name_map_name).
    pose ((GenVMG irisΣ vm_preG Hinv _ _ _ name_map_name mem_gname reg_gname mb_gname rx_state_gname
                  own_gname access_gname excl_gname trans_gname hpool_gname retri_gname)) as VMG.
    iExists (gen_vm_interp (Σ := irisΣ)).
    
    destruct Hinit as (-> & -> & (p_prog1 & p_prog2 & p_prog3 & p_tx1 & p_tx2 & p_tx3 & p_rx1 & p_rx2 & p_rx3 & addr & txbase & rxbase & Heqtx & Heqrx & Heqaddr & Hnodup_p & Hpgt & Hmem & Hreg & (Hmb & Hrx)) & Htrans).
    destruct Hreg as (Hlookup_reg0 & Hlookup_reg1 & Htotal_reg).
    
    (* use assumptions to extract resources *)
    (** extract regs  **)
    iDestruct (get_reg_gmap_split with "Hreg") as "(Hreg0 & Hreg1 & Hreg2 & _)".
    (* TODO: move, do the same for other resources *)
    assert (∀ σ f, ([∗ map] p↦w ∈ get_reg_gmap_vm σ f, p ↪[reg_gname] w)%I =
                   ([∗ map] p↦w ∈ get_reg_gmap_vm σ f, p.1 @@ p.2 ->r w)%I) as sepM_reg_def.
    {
      intros σ' f'.
      apply big_opM_ext.
      intros k x H.
      destruct k as [k1 k2].
      simpl.
      rewrite reg_mapsto_eq /reg_mapsto_def //.
    }
    iEval (rewrite sepM_reg_def) in "Hreg0 Hreg1 Hreg2".
    clear sepM_reg_def.
    
    (* extract regs of VM0 *)
    pose proof (Htotal_reg V0 R0) as [r0_ Hlookup_reg0_r0].
    pose proof (Htotal_reg V0 R1) as [r1_ Hlookup_reg0_r1].
    pose proof (Htotal_reg V0 R2) as [r2_ Hlookup_reg0_r2].
    pose proof (Htotal_reg V0 R3) as [r3_ Hlookup_reg0_r3].
    pose proof (Htotal_reg V0 R4) as [r4_ Hlookup_reg0_r4].
    pose proof (Htotal_reg V0 R5) as [r5_ Hlookup_reg0_r5].
      
    iDestruct (big_sepM_subseteq _ (get_reg_gmap_vm σ V0) {[(PC, V0):= (of_pid p_prog1); (R0, V0) := r0_;
                                 (R1,V0):= r1_; (R2,V0):= r2_; (R3,V0):= r3_; (R4,V0):= r4_; (R5,V0):= r5_]} with "Hreg0") as "Hreg0";eauto.
    {
      apply (λ x, reg_layout_extend σ _ _ x R5 r5_ Hlookup_reg0_r5) in Hlookup_reg0.
      apply (λ x, reg_layout_extend σ _ _ x R4 r4_ Hlookup_reg0_r4) in Hlookup_reg0.
      apply (λ x, reg_layout_extend σ _ _ x R3 r3_ Hlookup_reg0_r3) in Hlookup_reg0.
      apply (λ x, reg_layout_extend σ _ _ x R2 r2_ Hlookup_reg0_r2) in Hlookup_reg0.
      apply (λ x, reg_layout_extend σ _ _ x R1 r1_ Hlookup_reg0_r1) in Hlookup_reg0.
      apply (λ x, reg_layout_extend σ _ _ x R0 r0_ Hlookup_reg0_r0) in Hlookup_reg0.            
      
      apply reg_layout_get_reg_gmap in Hlookup_reg0; last assumption.
      
      clear -Hlookup_reg0.
      
      rewrite !kmap_insert in Hlookup_reg0.
      rewrite kmap_empty in Hlookup_reg0.
      rewrite insert_empty in Hlookup_reg0.

      rewrite (insert_commute _ (R5, V0) (PC, V0)) in Hlookup_reg0.
      rewrite (insert_commute _ (R4, V0) (PC, V0)) in Hlookup_reg0.
      rewrite (insert_commute _ (R3, V0) (PC, V0)) in Hlookup_reg0.
      rewrite (insert_commute _ (R2, V0) (PC, V0)) in Hlookup_reg0.
      rewrite (insert_commute _ (R1, V0) (PC, V0)) in Hlookup_reg0.
      rewrite (insert_commute _ (R0, V0) (PC, V0)) in Hlookup_reg0.
      assumption.
      1-6: done.
    }
    clear Hlookup_reg0_r0 Hlookup_reg0_r1 Hlookup_reg0_r2 Hlookup_reg0_r3 Hlookup_reg0_r4 Hlookup_reg0_r5 Hlookup_reg0.
    iDestruct (big_sepM_insert with "Hreg0") as "(PCz & Hreg0)".
    { rewrite !lookup_insert_None; repeat (split; eauto). }
    iDestruct (big_sepM_insert with "Hreg0") as "(R0z & Hreg0)".
    { rewrite !lookup_insert_None; repeat (split; eauto). }
    iDestruct (big_sepM_insert with "Hreg0") as "(R1z & Hreg0)".
    { rewrite !lookup_insert_None; repeat (split; eauto). }
    iDestruct (big_sepM_insert with "Hreg0") as "(R2z & Hreg0)".
    { rewrite !lookup_insert_None; repeat (split; eauto). }
    iDestruct (big_sepM_insert with "Hreg0") as "(R3z & Hreg0)".
    { rewrite !lookup_insert_None; repeat (split; eauto). }
    iDestruct (big_sepM_insert with "Hreg0") as "(R4z & Hreg0)".
    { rewrite !lookup_insert_None; repeat (split; eauto). }
    iDestruct (big_sepM_insert with "Hreg0") as "(R5z & _)".
    { rewrite lookup_empty; eauto. }
    
    (* extract regs of VM1 *)
    pose proof (Htotal_reg V1 R0) as [r0__ Hlookup_reg1_r0].
    pose proof (Htotal_reg V1 R1) as [r1__ Hlookup_reg1_r1].
    pose proof (Htotal_reg V1 R2) as [r2__ Hlookup_reg1_r2].
    pose proof (Htotal_reg V1 R3) as [r3__ Hlookup_reg1_r3].
    pose proof (Htotal_reg V1 R4) as [r4__ Hlookup_reg1_r4].
    pose proof (Htotal_reg V1 R5) as [r5__ Hlookup_reg1_r5].
    iDestruct (big_sepM_subseteq _ (get_reg_gmap_vm σ V1) {[(PC, V1):= (of_pid p_prog2); (R0, V1) := r0__; (R1, V1) := r1__; (R2, V1) := r2__; (R3, V1) := r3__; (R4, V1) := r4__; (R5, V1) := r5__]} with "Hreg1") as "Hreg1";eauto.
    {
      apply (λ x, reg_layout_extend σ _ _ x R5 r5__ Hlookup_reg1_r5) in Hlookup_reg1.
      apply (λ x, reg_layout_extend σ _ _ x R4 r4__ Hlookup_reg1_r4) in Hlookup_reg1.
      apply (λ x, reg_layout_extend σ _ _ x R3 r3__ Hlookup_reg1_r3) in Hlookup_reg1.
      apply (λ x, reg_layout_extend σ _ _ x R2 r2__ Hlookup_reg1_r2) in Hlookup_reg1.
      apply (λ x, reg_layout_extend σ _ _ x R1 r1__ Hlookup_reg1_r1) in Hlookup_reg1.
      apply (λ x, reg_layout_extend σ _ _ x R0 r0__ Hlookup_reg1_r0) in Hlookup_reg1.
      apply reg_layout_get_reg_gmap in Hlookup_reg1; last assumption.
      clear -Hlookup_reg1.
      rewrite !kmap_insert in Hlookup_reg1.
      rewrite kmap_empty in Hlookup_reg1.
      rewrite insert_empty in Hlookup_reg1.

      rewrite (insert_commute _ (R5, V1) (PC, V1)) in Hlookup_reg1.
      rewrite (insert_commute _ (R4, V1) (PC, V1)) in Hlookup_reg1.
      rewrite (insert_commute _ (R3, V1) (PC, V1)) in Hlookup_reg1.
      rewrite (insert_commute _ (R2, V1) (PC, V1)) in Hlookup_reg1.
      rewrite (insert_commute _ (R1, V1) (PC, V1)) in Hlookup_reg1.
      rewrite (insert_commute _ (R0, V1) (PC, V1)) in Hlookup_reg1.
      assumption.
      1-6: done.
    }
    clear Hlookup_reg1_r0 Hlookup_reg1_r1 Hlookup_reg1_r2 Hlookup_reg1_r3 Hlookup_reg1_r4 Hlookup_reg1_r5 Hlookup_reg1.
    iDestruct (big_sepM_insert with "Hreg1") as "(PC1 & Hreg1)".
    { rewrite !lookup_insert_None; repeat (split; eauto). }
    iDestruct (big_sepM_insert with "Hreg1") as "(R01 & Hreg1)".
    { rewrite !lookup_insert_None; repeat (split; eauto). }
    iDestruct (big_sepM_insert with "Hreg1") as "(R11 & Hreg1)".
    { rewrite !lookup_insert_None; repeat (split; eauto). }
    iDestruct (big_sepM_insert with "Hreg1") as "(R21 & Hreg1)".
    { rewrite !lookup_insert_None; repeat (split; eauto). }
    iDestruct (big_sepM_insert with "Hreg1") as "(R31 & Hreg1)".
    { rewrite !lookup_insert_None; repeat (split; eauto). }
    iDestruct (big_sepM_insert with "Hreg1") as "(R41 & Hreg1)".
    { rewrite !lookup_insert_None; repeat (split; eauto). }
    iDestruct (big_sepM_insert with "Hreg1") as "(R51 & _)".
    { rewrite lookup_empty; eauto. }

    iDestruct (big_sepM_subseteq _ (get_mb_gmap σ) {[(V0, TX):= p_tx1; (V1, TX) := (p_tx2); (V2, TX) := (p_tx3); (V0, RX) := p_rx1; (V1, RX) := p_rx2; (V2, RX) := p_rx3]} with "Hmb") as "Hmb";eauto.
    {
      apply mailbox_layout_get_mb_gmap.
      assumption.
    }
    iDestruct (big_sepM_insert with "Hmb") as "(mb0TX & Hmb)".
    { rewrite !lookup_insert_None; split; eauto. }
    iDestruct (big_sepM_insert with "Hmb") as "(mb1TX & Hmb)".
    { rewrite !lookup_insert_None; split; eauto. }
    iDestruct (big_sepM_insert with "Hmb") as "(mb2TX & Hmb)".
    { rewrite !lookup_insert_None; split; eauto. }
    iDestruct (big_sepM_insert with "Hmb") as "(mb0RX & Hmb)".
    { rewrite !lookup_insert_None; split; eauto. }
    iDestruct (big_sepM_insert with "Hmb") as "(mb1RX & Hmb)".
    { rewrite !lookup_insert_None; split; eauto. }
    iDestruct (big_sepM_insert with "Hmb") as "(mb2RX & _)".
    { rewrite lookup_empty; eauto. }    

    iDestruct (big_sepM_subseteq _ (get_rx_gmap σ) {[V0:= None; V1 := None; V2 := None]} with "Hrxs") as "Hrxs";eauto.
    {
      apply rx_layout_get_rx_gmap.
      assumption.
    } 
    iDestruct (big_sepM_insert with "Hrxs") as "(RX0St & Hrxs)".
    { rewrite !lookup_insert_None; split; eauto. }
    iDestruct (big_sepM_insert with "Hrxs") as "(RX1St & Hrxs)".
    { rewrite !lookup_insert_None; split; eauto. }
    iDestruct (big_sepM_insert with "Hrxs") as "(RX2St & _)".
    { rewrite lookup_empty; eauto. }
    
    (** extract mem **)
    destruct Hmem as ( HmemH1 & HmemH2 & Hdom_mem).
    destruct Hpgt as (pgt_acc & pgt_excl & pgt_own).
    pose proof (union_split_difference_intersection_subseteq_L _ _ Hdom_mem) as [Hdom_mem_union Hdom_mem_disj].
    pose proof (dom_union_inv_L _ _ _ Hdom_mem_disj Hdom_mem_union) as (mem' & mem2 & Hunion_mem' & Hdisj_mem' & _ & Hdom_mem2).

    iDestruct (big_sepM_subseteq _ (get_mem σ) mem2 with "Hmem") as "Hmem"; eauto.
    {
      rewrite Hunion_mem'.
      apply map_union_subseteq_r.
      done.
    }    
    
    pose proof (union_split_difference_intersection_subseteq_L {[p_prog1; p_prog2; tpa addr; p_prog3; p_tx1; p_tx2; p_tx3; p_rx1; p_rx2; p_rx3]} {[p_prog1]}) as [Heq Hdisj].
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
    pose proof (union_split_difference_intersection_subseteq_L ({[p_prog1; p_prog2; tpa addr; p_prog3; p_tx1; p_tx2; p_tx3; p_rx1; p_rx2; p_rx3]} ∖ {[p_prog1]}) {[p_prog2]}) as [Heq Hdisj].
    apply singleton_subseteq_l.
    rewrite !difference_union_distr_l_L.
    rewrite difference_diag_L.
    rewrite union_empty_l_L.
    rewrite <-!difference_union_distr_l_L.
    rewrite difference_disjoint_L.
    set_solver +.
    solve_NoDup 0.
       
    rewrite Heq in Hdom_mem1.
    rewrite set_of_addr_union in Hdom_mem1.
    2 : { set_solver. }
    clear Heq.
    apply dom_union_inv_L in Hdom_mem1.
    2 : { apply set_of_addr_disj. done. }
    destruct Hdom_mem1 as (mem2 & mem_p_prog2 &  -> & Hmem2_disj  & Hdom_mem2 & Hdom_mem_p_prog2).
    clear Hdisj.
    iDestruct ((big_sepM_union _ _) with "Hmem1") as "(Hmem2 & mem_p_prog2)";auto.

    pose proof (union_split_difference_intersection_subseteq_L (({[p_prog1; p_prog2; tpa addr; p_prog3; p_tx1; p_tx2; p_tx3; p_rx1; p_rx2; p_rx3]} ∖ {[p_prog1]}) ∖ {[p_prog2]}) {[tpa addr]}) as [Heq Hdisj].
    apply singleton_subseteq_l.
    rewrite !difference_union_distr_l_L.
    rewrite !difference_diag_L.
    do 7 (rewrite elem_of_union; left).
    rewrite elem_of_union; right.
    rewrite ->2elem_of_difference.
    split; [split; first set_solver + |].
    solve_NoDup 0.
    solve_NoDup 1.
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

    change {[p_prog1; p_prog2; p_prog3; p_tx1; p_tx2; p_tx3; p_rx1; p_rx2; p_rx3]} with p in Hdom_mem'.
    change {[p_prog1]} with q in Hdom_mem'.
    change {[p_prog2]} with r in Hdom_mem'.
    change {[tpa addr]} with t in Hdom_mem'.
    assert (p ∖ q ∖ r ∖ t = {[p_prog3; p_tx1; p_tx2; p_tx3; p_rx1; p_rx2; p_rx3]}) as Heq.
    {
      assert (p ∖ q ∖ r = {[tpa addr; p_prog3; p_tx1; p_tx2; p_tx3; p_rx1; p_rx2; p_rx3]}) as ->.
      {
        assert (p ∖ q = {[p_prog2; tpa addr; p_prog3; p_tx1; p_tx2; p_tx3; p_rx1; p_rx2; p_rx3]}) as ->.
        {
          subst p q.
          rewrite !difference_union_distr_l_L.
          rewrite difference_diag_L.
          rewrite union_empty_l_L.
          rewrite <-!difference_union_distr_l_L.
          rewrite difference_disjoint_L.
          - reflexivity.
          - solve_NoDup 0.
        }
        subst r.
        rewrite !difference_union_distr_l_L.
        rewrite difference_diag_L.
        rewrite union_empty_l_L.
        rewrite <-!difference_union_distr_l_L.
        rewrite difference_disjoint_L.
        - reflexivity.
        - solve_NoDup 1.
      }
      subst t.
      rewrite !difference_union_distr_l_L.
      rewrite difference_diag_L.
      rewrite union_empty_l_L.
      rewrite <-!difference_union_distr_l_L.
      rewrite difference_disjoint_L.
      - reflexivity.
      - solve_NoDup 9.
    }    
    rewrite Heq in Hdom_mem'.
    clear Heq.
    rewrite set_of_addr_union in Hdom_mem'.
    2 : {
      solve_NoDup 8.
    }
    apply dom_union_inv_L in Hdom_mem'.
    2 : {
      apply set_of_addr_disj.
      solve_NoDup 8.
    }
    destruct Hdom_mem' as (mem3 & mem_p_rx3 &  -> & Hmem3_disj  & Hdom_mem1 & Hdom_mem_p_rx3).
    iDestruct ((big_sepM_union _ _) with "Hmem") as "(Hmem2 & p_rx3)";auto.
    rewrite set_of_addr_union in Hdom_mem1.
    2 : {
      solve_NoDup 7.
    }
    apply dom_union_inv_L in Hdom_mem1.
    2 : {
      apply set_of_addr_disj.
      solve_NoDup 7.
    }
    destruct Hdom_mem1 as (mem4 & mem_p_rx2 &  -> & Hmem4_disj  & Hdom_mem2 & Hdom_mem_p_rx2).
    iDestruct ((big_sepM_union _ _) with "Hmem2") as "(Hmem2 & p_rx2)";auto.
    rewrite set_of_addr_union in Hdom_mem2.
    2 : {
      solve_NoDup 6.
    }
    apply dom_union_inv_L in Hdom_mem2.
    2 : {
      apply set_of_addr_disj.
      solve_NoDup 6.
    }
    destruct Hdom_mem2 as (mem5 & mem_p_rx1 &  -> & Hmem5_disj  & Hdom_mem1 & Hdom_mem_p_rx1).
    iDestruct ((big_sepM_union _ _) with "Hmem2") as "(Hmem2 & p_rx1)";auto.
    rewrite set_of_addr_union in Hdom_mem1.
    2 : {
      solve_NoDup 5.
    }
    apply dom_union_inv_L in Hdom_mem1.
    2 : {
      apply set_of_addr_disj.
      solve_NoDup 5.
    }
    destruct Hdom_mem1 as (mem3 & mem_p_tx3 & -> & Hmem6_disj  & Hdom_mem2 & Hdom_mem_p_tx3).    
    iDestruct ((big_sepM_union _ _) with "Hmem2") as "(Hmem2 & p_tx3)";auto.
    rewrite set_of_addr_union in Hdom_mem2.
    2 : {
      solve_NoDup 4.
    }
    apply dom_union_inv_L in Hdom_mem2.
    2 : {
      apply set_of_addr_disj.
      solve_NoDup 4.
    }
    destruct Hdom_mem2 as (mem4 & mem_p_tx2 & -> & Hmem7_disj  & Hdom_mem2 & Hdom_mem_p_tx2).    
    iDestruct ((big_sepM_union _ _) with "Hmem2") as "(Hmem2 & p_tx2)";auto.
    rewrite set_of_addr_union in Hdom_mem2.
    2 : {
      solve_NoDup 3.
    }
    apply dom_union_inv_L in Hdom_mem2.
    2 : {
      apply set_of_addr_disj.
      solve_NoDup 3.
    }
    destruct Hdom_mem2 as (mem5 & mem_p_tx1 & -> & Hmem8_disj  & Hdom_mem3 & Hdom_mem_p_tx1).    
    iDestruct ((big_sepM_union _ _) with "Hmem2") as "(Hmem2 & p_tx1)";auto.
    
    subst p q r t.
    
    clear Hmem8_disj Hmem7_disj Hmem6_disj Hmem5_disj Hmem4_disj Hmem3_disj.

    iAssert (trans.fresh_handles 1 valid_handles)%I with "[Hhpool Htrans Hretri]" as "Hp".
    {
      destruct Htrans as [Htrans1 Htrans2].
      rewrite <-Htrans1.
      unfold trans.fresh_handles.
      unfold get_hpool_gset.
      unfold get_fresh_handles.
      rewrite hpool_mapsto_eq /hpool_mapsto_def.
      simpl.
      assert ((filter (λ (kv : Addr * option transaction), kv.2 = None) σ.2) = σ.2) as Heq.
      {
        rewrite map_eq_iff.
        intros i.
        rewrite map_filter_lookup.
        rewrite map_Forall_lookup in Htrans2.
        specialize (Htrans2 i).
        destruct (σ.2 !! i) eqn:Heqn.
        - rewrite Heqn.
          simpl.
          specialize (Htrans2 o Heqn).
          rewrite Htrans2.
          simpl.
          reflexivity.
        - rewrite Heqn.
          reflexivity.
      }
      rewrite Heq.
      assert ((dom σ.2 ∩ {[W0]}) = (dom σ.2)) as ->.
      {
        rewrite Htrans1.
        set_solver +.
      }
      iFrame "Hhpool".
      
      rewrite big_sepS_sep.
      iSplitL "Htrans".      
      - unfold get_trans_gmap.
        unfold get_transactions_gmap.
        rewrite trans_mapsto_eq /trans_mapsto_def.
        match goal with
        | |- context G [?f <$> σ.2] => set g := f
        end.
        assert (∀ (m : gmap Addr (option transaction))
                  (f : option transaction -> option meta_info), map_Forall (λ _ v, v = None) m -> (f None = None) -> (∀ i j, (f <$> m) !! i = Some j -> j = None)) as Heq'.
        {
          intros m f Hm Hf.
          intros i j.
          rewrite map_Forall_lookup in Hm.
          specialize (Hm i).
          rewrite lookup_fmap.
          destruct (m !! i) eqn:Heqn.
          - intros eq.
            specialize (Hm o eq_refl).
            rewrite Hm in eq.
            simpl in eq.
            rewrite Hf in eq.
            inversion eq.
            reflexivity.
          - intros eq.
            simpl in eq.
            discriminate.
        }
        specialize (Heq' σ.2 g Htrans2).
        feed specialize Heq'.
        {
          subst g.
          simpl.
          reflexivity.
        }
        simpl.
        assert (map_Forall (λ (_ : Addr) (v : option (@meta_info rywu_vmconfig)), v = None) (g <$> σ.2)) as Htrans3.
        {
          intros i j He.
          by apply (Heq' i).
        }
        pose proof (big_opM_dom (fun (y : finz.finz 2000000) => ghost_map_elem trans_gname y (DfracOwn (pos_to_Qp 1)) None) σ.2) as Hrew.
        simpl in Hrew.
        rewrite big_sepS_sep.
        rewrite <-Hrew.
        clear Hrew.
        rewrite big_opM_fmap.
        rewrite big_op.big_opM_unseal /big_op.big_opM_def.        
        rewrite (big_opL_ext (λ _, uncurry
                                     (λ (k : Addr) (_ : option transaction),
                                      (k ↪[trans_gname] None)%I))
                             (λ _, uncurry (λ (k : Addr) (y : option transaction),
                                            (k ↪[trans_gname] g y)%I))
                             (map_to_list σ.2)).
        iFrame "Htrans".
        {
          iPureIntro.
          rewrite Htrans1.
          intro.
          set_solver +.
        }
        intros k (y1 & y2) eq'.
        simpl. subst g.
        assert (y2 = None) as ->.
        {
          rewrite map_Forall_to_list in Htrans2.
          apply (Forall_lookup_1 _ _ k (pair y1 y2)) in Htrans2; last done.
          simpl in Htrans2.
          assumption.
        }
        reflexivity.
      - unfold get_retri_gmap.
        unfold get_transactions_gmap.
        rewrite retri_mapsto_eq /retri_mapsto_def.
        match goal with
        | |- context G [?f <$> σ.2] => set g := f
        end.
        rewrite big_opM_fmap.
        simpl.
        set f := (λ k v, (k ↪[retri_gname] g v)%I).
        pose f' := (λ k _, f k None).
        rewrite (big_opM_ext f
                             (λ k v, f' (option transaction) k v)
                             σ.2).
        2: {
          intros k x G.
          subst f f' g. simpl.
          rewrite map_Forall_lookup in Htrans2.
          specialize (Htrans2 k x G).
          rewrite Htrans2 //=.
        }
        subst f'. simpl.
        subst f. simpl.
        rewrite big_opM_dom.
        rewrite big_sepS_sep.
        iFrame "Hretri".
        {
          iPureIntro.
          rewrite Htrans1.
          intro.
          set_solver +.
        }
    }
    
    iDestruct (big_sepM_subseteq _ (get_access_gmap σ) {[V0 := (to_dfrac_agree (DfracOwn 1) ({[tpa addr; p_prog1; p_tx1]})); V1 := (to_dfrac_agree (DfracOwn 1) ({[p_prog2; p_tx2; p_rx2]})); V2 := (to_dfrac_agree (DfracOwn 1) ({[p_tx3;p_rx3;p_prog3]}))]} with "Haccess") as "access"; eauto.
    {
      apply access_layout_get_access_gmap.
      assumption.
    }
    iEval (rewrite big_opM_insert_delete) in "access".
    match goal with
    | |- context G [delete _ ?p] => set P := p
    end.
    assert (delete V0 P = P) as ->.
    {
      subst P.
      clear.      
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
      subst P.
      clear.      
      apply delete_notin.
      by simplify_map_eq /=.
    }
    subst P.
    iEval (rewrite big_sepM_singleton) in "access".
    iDestruct "access" as "(access1 & access2 & access3)".
    
    iDestruct (big_sepM_subseteq _ (get_excl_gmap σ) {[p_rx1 := true; p_rx2 := true; p_rx3 := true; p_tx3 := true; p_prog3 := true; tpa addr := true]} with "Hexcl") as "excl"; eauto.
    {
      apply excl_layout_get_excl_gmap.
      assumption.
    }
    iEval (rewrite big_opM_insert_delete) in "excl".
    match goal with
    | |- context G [delete _ ?p] => set P := p
    end.
    assert (delete p_rx1 P = P) as ->.
    {
      subst P.      
      clear -Hnodup_p.      
      apply delete_notin.
      rewrite <-not_elem_of_dom.      
      rewrite !dom_insert_L.
      rewrite dom_empty_L.
      rewrite union_empty_r.      
      rewrite !elem_of_union.      
      rewrite !elem_of_singleton.
      intros contra.      
      solve_NoDup_pre'.
      solve_NoDup_pre'' 6 7.
      solve_NoDup_pre'.
      solve_NoDup_pre'' 6 8.
      solve_NoDup_pre'' 5 6.
      solve_NoDup_pre'' 2 6.
      solve_NoDup_pre'' 6 9.
    }
    subst P.
    iEval (rewrite big_opM_insert_delete) in "excl".
    match goal with
    | |- context G [delete _ ?p] => set P := p
    end.
    assert (delete p_rx2 P = P) as ->.
    {
      subst P.
      clear -Hnodup_p.      
      apply delete_notin.
      rewrite <-not_elem_of_dom.
      rewrite !dom_insert_L.
      rewrite dom_empty_L.
      rewrite union_empty_r.      
      rewrite !elem_of_union.
      rewrite !elem_of_singleton.
      intros contra.
      solve_NoDup_pre'.
      solve_NoDup_pre'' 7 8.
      solve_NoDup_pre'.
      solve_NoDup_pre'' 5 7.
      solve_NoDup_pre'' 2 7.
      solve_NoDup_pre'' 7 9.
    }
    subst P.
    iEval (rewrite big_opM_insert_delete) in "excl".
    match goal with
    | |- context G [delete _ ?p] => set P := p
    end.
    assert (delete p_rx3 P = P) as ->.
    {
      subst P.
      clear -Hnodup_p.      
      apply delete_notin.
      rewrite <-not_elem_of_dom.
      rewrite !dom_insert_L.
      rewrite dom_empty_L.
      rewrite union_empty_r.      
      rewrite !elem_of_union.
      rewrite !elem_of_singleton.
      intros contra.
      solve_NoDup_pre'.
      solve_NoDup_pre'' 5 8.
      destruct eq as [-> | ->].
      solve_NoDup_pre'' 2 8.
      solve_NoDup_pre'' 8 9.
    }
    subst P.
    iEval (rewrite big_opM_insert_delete) in "excl".
    match goal with
    | |- context G [delete _ ?p] => set P := p
    end.
    assert (delete p_tx3 P = P) as ->.
    {
      subst P.
      clear -Hnodup_p.      
      apply delete_notin.
      rewrite <-not_elem_of_dom.
      rewrite !dom_insert_L.
      rewrite dom_empty_L.
      rewrite union_empty_r.
      rewrite !elem_of_union.
      rewrite !elem_of_singleton.
      intros contra.
      destruct contra as [-> | ->].
      solve_NoDup_pre'' 2 5.
      solve_NoDup_pre'' 5 9.
    }
    subst P.
    iEval (rewrite big_opM_insert_delete) in "excl".
    match goal with
    | |- context G [delete _ ?p] => set P := p
    end.
    assert (delete p_prog3 P = P) as ->.
    {
      subst P.
      clear -Hnodup_p.      
      apply delete_notin.
      rewrite <-not_elem_of_dom.
      rewrite !dom_insert_L.
      rewrite dom_empty_L.
      rewrite union_empty_r.
      rewrite !elem_of_singleton.
      intros ->.
      solve_NoDup_pre'' 2 9.
    }
    subst P.
      
    iEval (rewrite big_sepM_singleton) in "excl".
    iDestruct "excl" as "(excl1 & excl2 & excl3 & excl4 & excl5 & excl6)".

    iDestruct (big_sepM_subseteq _ (get_own_gmap σ) {[p_rx1 := None; p_rx2 := None; p_rx3 := None; p_tx3 := None; p_prog3 := Some V2; tpa addr := Some V0]} with "Hown") as "own"; eauto.
    {
      apply own_layout_get_own_gmap.
      assumption.      
    }
    iEval (rewrite big_opM_insert_delete) in "own".
    match goal with
    | |- context G [delete _ ?p] => set P := p
    end.
    assert (delete p_rx1 P = P) as ->.
    {
      subst P.
      clear -Hnodup_p.      
      apply delete_notin.
      rewrite <-not_elem_of_dom.
      rewrite !dom_insert_L.
      rewrite dom_empty_L.
      rewrite union_empty_r.
      rewrite !elem_of_union.
      rewrite !elem_of_singleton.
      intros contra.
      solve_NoDup_pre'.
      solve_NoDup_pre'' 6 7.
      solve_NoDup_pre'.
      solve_NoDup_pre'' 6 8.
      solve_NoDup_pre'' 5 6.
      solve_NoDup_pre'' 2 6.
      solve_NoDup_pre'' 6 9.
    }
    subst P.
    iEval (rewrite big_opM_insert_delete) in "own".
    match goal with
    | |- context G [delete _ ?p] => set P := p
    end.
    assert (delete p_rx2 P = P) as ->.
    {
      subst P.
      clear -Hnodup_p.      
      apply delete_notin.
      rewrite <-not_elem_of_dom.
      rewrite !dom_insert_L.
      rewrite dom_empty_L.
      rewrite union_empty_r.
      rewrite !elem_of_union.
      rewrite !elem_of_singleton.
      intros contra.
      solve_NoDup_pre'.
      solve_NoDup_pre'' 7 8.
      solve_NoDup_pre'.
      solve_NoDup_pre'' 5 7.
      solve_NoDup_pre'' 2 7.
      solve_NoDup_pre'' 7 9.
    }
    subst P.
    iEval (rewrite big_opM_insert_delete) in "own".
    match goal with
    | |- context G [delete _ ?p] => set P := p
    end.
    assert (delete p_rx3 P = P) as ->.
    {
      subst P.
      clear -Hnodup_p.      
      apply delete_notin.
      rewrite <-not_elem_of_dom.
      rewrite !dom_insert_L.
      rewrite dom_empty_L.
      rewrite union_empty_r.
      rewrite !elem_of_union.
      rewrite !elem_of_singleton.
      intros contra.
      solve_NoDup_pre'.
      solve_NoDup_pre'' 5 8.
      solve_NoDup_pre'.
      solve_NoDup_pre'' 2 8.
      solve_NoDup_pre'' 8 9.
    }
    subst P.
    iEval (rewrite big_opM_insert_delete) in "own".
    match goal with
    | |- context G [delete _ ?p] => set P := p
    end.
    assert (delete p_tx3 P = P) as ->.
    {
      subst P.
      clear -Hnodup_p.      
      apply delete_notin.
      rewrite <-not_elem_of_dom.
      rewrite !dom_insert_L.
      rewrite dom_empty_L.
      rewrite union_empty_r.
      rewrite !elem_of_union.
      rewrite !elem_of_singleton.  
      intros contra.
      solve_NoDup_pre'.
      solve_NoDup_pre'' 2 5.
      solve_NoDup_pre'' 5 9.
    }
    subst P.
    iEval (rewrite big_opM_insert_delete) in "own".
    match goal with
    | |- context G [delete _ ?p] => set P := p
    end.
    assert (delete p_prog3 P = P) as ->.
    {
      subst P.
      clear -Hnodup_p.      
      apply delete_notin.
      rewrite <-not_elem_of_dom.
      rewrite !dom_insert_L.
      rewrite dom_empty_L.
      rewrite union_empty_r.
      rewrite !elem_of_singleton.  
      intros contra.
      solve_NoDup_pre'.
      solve_NoDup_pre'' 2 5.
    }
    subst P.
    iEval (rewrite big_sepM_singleton) in "own".
    iDestruct "own" as "(own1 & own2 & own3 & own4 & own5 & own6)".
    
    iDestruct (ghost_map_elem_persist with "mb0TX") as ">mb0TX".
    iDestruct (ghost_map_elem_persist with "mb1TX") as ">mb1TX".
    iDestruct (ghost_map_elem_persist with "mb2TX") as ">mb2TX".
    iDestruct (ghost_map_elem_persist with "mb0RX") as ">mb0RX".
    iDestruct (ghost_map_elem_persist with "mb1RX") as ">mb1RX".
    iDestruct (ghost_map_elem_persist with "mb2RX") as ">mb2RX".

    iModIntro.

    (* allocate VMProps *)
    set pgt := (get_page_table σ).    
    iExists [True%I;
      (R0 @@ V0 ->r run_I ∗ R1 @@ V0 ->r encode_vmid V1 ∗ addr ->a two  ∗ (∃ (wh : Addr), (∃ (β : lang.mem), wh ->t (V0, V1, {[tpa addr]}, Sharing) ∗
                                                                                    wh ->re false ∗ RX_state@V1 := Some (of_imm one, V0) ∗ RX@V1:=p_rx2 ∗ memory_page p_rx2 β ∗ ⌜β !! (of_imm rxbase) = Some wh⌝) ∗
                    VMProp V0 ((R0 @@ V0 ->r yield_I ∗ R1 @@ V0 ->r encode_vmid V1 ∗ addr ->a four ∗ wh ->t (V0, V1, {[tpa addr]}, Sharing) ∗ RX@V1:=p_rx2 ∗ RX_state@V1 := None ∗ (∃ mem_rx, memory_page p_rx2 mem_rx)) ∗
                                 VMProp V1 False%I (1/2)%Qp) (1/2)%Qp))%I;
      (vmprop_unknown V2 (* p_tx p_rx  *) ∅)].
    iSimpl.
    iSplit; first done.

    (* frame state_interp *)
    iSplitL "Hσmem Hσreg Hσaccess Hσown Hσexcl Hσrxs Hσmb Hσhpool Hσtrans Hσretri".
    iFrame.
    rewrite /inv_trans_wellformed /inv_trans_wellformed'.
    rewrite /inv_trans_pgt_consistent /inv_trans_pgt_consistent'.
    destruct Htrans as [Hdom_trans Hempty_trans].
    repeat iSplit.
    done.
    {
      rewrite /inv_trans_pg_num_ub.
      iPureIntro.
      eapply (map_Forall_impl (K:=Word) (M:= gmap Word)).
      apply Hempty_trans.
      intros h tran Hnone.
      simpl in Hnone.
      subst tran.
      done.
    }
    {
      rewrite /inv_trans_sndr_rcvr_neq.
      iPureIntro.
      eapply (map_Forall_impl (K:=Word) (M:= gmap Word)).
      apply Hempty_trans.
      intros h tran Hnone.
      simpl in Hnone.
      subst tran.
      done.
    }
    {
      rewrite /inv_finite_handles.
      iPureIntro.
      rewrite -Hdom_trans //.
    }
    {
      iPureIntro.
      eapply (map_Forall_impl (K:=Word) (M:= gmap Word)).
      apply Hempty_trans.
      intros h tran Hnone.
      simpl in Hnone.
      subst tran.
      done.
    }
    {
      iPureIntro.
      intros ? ? Hlk.
      specialize (Hempty_trans _ _ Hlk).
      simpl in Hempty_trans.
      subst x. done.
    }

    iIntros "(VMProp0 & VMProp1 & VMProp2 & _)".
    rewrite /scheduled /machine.scheduler //= /scheduler Hcur //=.
      
    iDestruct (VMProp_split with "VMProp1") as "[VMProp1_half VMProp1_half']".
    iDestruct (VMProp_split with "VMProp2") as "[VMProp2_half VMProp2_half']".
    
    pose proof (@access_split rywu_vmconfig irisΣ VMG 1 V2) as Hsplit.
    rewrite access_mapsto_eq /access_mapsto_def in Hsplit.
    (* iDestruct "access3" as "(access3 & access3')". *)
    iAssert ((V2, RX) ↪[ mb_gname ]□ p_rx3 ∗ (V2, RX) ↪[ mb_gname ]□ p_rx3)%I with "[mb2RX]" as "(mb2RX & mb2RX')".
    {
      iDestruct "mb2RX" as "#mb2RX".
      iFrame "mb2RX".
    }
    
    iSplitL "PCz R0z R1z R2z R3z R4z R5z mem_p_prog1 p_tx1 mem_p Hp VMProp0 VMProp1_half' VMProp2_half' mb0RX mb1RX RX0St RX1St RX2St p_rx1 p_rx2 p_rx3 mb0TX mb2RX access1 excl1 excl2 excl6 own1 own2 own6".
    iIntros "_".
    iDestruct (lending_machine0 p_prog1 p_tx1 p_prog3 p_tx3 p_rx1 p_rx2 p_rx3 addr txbase rxbase with "[-]") as "HWP".
    {
      assumption.
    }
    {
      assumption.
    }
    {
      assumption.
    }
    {
      solve_NoDup 0.
    }
    {
      clear -Hnodup_p.
      intros <-.
      solve_NoDup_pre'' 6 9.
    }
    {
      clear -Hnodup_p.
      intros <-.
      solve_NoDup_pre'' 0 9.
    }
    {
      clear -Hnodup_p.
      intros <-.
      solve_NoDup_pre'' 3 9.
    }
    {
      clear -Hnodup_p.
      intros <-.
      solve_NoDup_pre'' 3 6.
    }
    {      
      program_in_seq.     
    }
    {
      iSplitL "mem_p_prog1".
      {      
        unfold program.
        iEval (rewrite big_opM_map_to_list) in "mem_p_prog1".
        rewrite big_sepL2_alt.
        iSplitR "mem_p_prog1".
        {
          simpl.
          by iPureIntro.
        }
        {
          rewrite mem_mapsto_eq /mem_mapsto_def.
          assert (mem_p_prog1 ⊆ σ.1.2) as Hsubseteq.
          {
            rewrite Hunion_mem'.
            apply map_union_subseteq_r'.
            assumption.
            apply map_union_subseteq_r'.
            assumption.
            done.
          }
          iApply (memory_list_gmap _ _ _ mem_p_prog1 σ).
          - rewrite fst_zip.
            + apply finz_seq_NoDup'.
              simpl.
              pose proof (last_addr_in_bound p_prog1).
              solve_finz.
            + simpl.
              lia.
          - apply HmemH1; done.
          - by iFrame.
        }
      }
      iSplitL "mem_p".
      {
        rewrite mem_mapsto_eq /mem_mapsto_def.
        assert (mem ⊆ σ.1.2) as Hsubseteq.
        {
          rewrite Hunion_mem'.
          apply map_union_subseteq_r'.
          assumption.
          apply map_union_subseteq_l'.
          apply map_union_subseteq_l'.
          apply map_union_subseteq_r'.
          assumption.
          done.
        }
        assert (of_imm addr ∈ set_of_addr {[tpa addr]}) as H.
        {
          apply elem_of_set_of_addr with (tpa addr).
          apply elem_of_addr_of_page_tpa.
          set_solver +.
        }
        rewrite <-Hdom_mem_p in H.
        rewrite elem_of_dom in H.
        destruct H as [waddr Hwaddr].
        iDestruct (big_sepM_delete _ mem addr waddr with "mem_p") as "(mem & memacc)". 
        assumption.
        iExists waddr.
        iFrame.        
      }
      iSplitL "p_tx1".
      {
        unfold memory_page.
        iExists mem_p_tx1. iSplit. rewrite Hdom_mem_p_tx1. iPureIntro.
        rewrite set_of_addr_singleton.
        rewrite to_pid_aligned_eq.
        reflexivity.
        rewrite mem_mapsto_eq /mem_mapsto_def /=.
        iFrame.
      }
      rewrite rx_state_mapsto_eq /rx_state_mapsto_def /=.
      iFrame "RX0St RX1St RX2St".
      unfold rx_page.
      rewrite mb_mapsto_eq /mb_mapsto_def /=.
      rewrite to_pid_aligned_eq.
      iFrame "mb0TX".
      iFrame "PCz".
      rewrite access_mapsto_eq /access_mapsto_def /=.
      rewrite big_sepS_singleton.
      iSplitL "excl6 own6".
      {
        rewrite excl_mapsto_eq own_mapsto_eq /excl_mapsto_def /own_mapsto_def /=.
        iFrame.
      }
      iSplitL "access1".
      {
        assert ({[tpa addr; p_prog1; p_tx1]} = {[tpa addr]} ∪ {[p_prog1; p_tx1]}) as ->.
        {
          set_solver +.
        }
        iFrame.
      }      
      iSplitL "R0z".
      iExists r0_; iFrame.
      iSplitL "R1z".
      iExists r1_; iFrame.
      iSplitL "R2z".
      iExists r2_; iFrame.
      iSplitL "R3z".
      iExists r3_; iFrame.
      iSplitL "R4z".
      iExists r4_; iFrame.
      iSplitL "R5z".
      iExists r5_; iFrame.
      iFrame "VMProp0".
      iFrame "VMProp1_half'".
      iFrame "VMProp2_half'".
      iFrame "Hp".
      iFrame.      

      iSplitL "p_rx1 excl1 own1".      
      iSplitR "p_rx1".
      rewrite excl_mapsto_eq own_mapsto_eq /excl_mapsto_def /own_mapsto_def /=.
      iFrame.
      unfold memory_page.
      iExists mem_p_rx1. iSplit. rewrite Hdom_mem_p_rx1. iPureIntro.
      apply set_of_addr_singleton.
      rewrite mem_mapsto_eq /mem_mapsto_def /=.
      iFrame "p_rx1".
      iSplitL "p_rx2 excl2 own2".      
      iSplitR "p_rx2".
      rewrite excl_mapsto_eq own_mapsto_eq /excl_mapsto_def /own_mapsto_def /=.
      iFrame.
      unfold memory_page.
      iExists mem_p_rx2. iSplit. rewrite Hdom_mem_p_rx2. iPureIntro.
      apply set_of_addr_singleton.
      rewrite mem_mapsto_eq /mem_mapsto_def /=.
      iFrame "p_rx2".

      unfold memory_page.
      iExists mem_p_rx3. iSplit. rewrite Hdom_mem_p_rx3. iPureIntro.
      apply set_of_addr_singleton.
      rewrite mem_mapsto_eq /mem_mapsto_def /=.
      iFrame "p_rx3".
    }
    
    iApply (wp_mono with "HWP").
    intros k.
    simpl.
    iIntros "[$ _]".

    iSplitL "VMProp1_half PC1 R01 R11 R21 R31 R41 R51 mem_p_prog2 p_tx2 mb1TX access2".
    iApply (lending_machine1 p_prog2 p_tx2 p_rx2 addr rxbase).
    {
      assumption.
    }
    {
      assumption.
    }
    {      
      clear -Hnodup_p.
      intros contra.
      rewrite !elem_of_union in contra.
      rewrite !elem_of_singleton in contra.
      destruct contra as [[H | H] | H]; subst.
      solve_NoDup_pre'' 1 9.
      solve_NoDup_pre'' 1 4.
      solve_NoDup_pre'' 1 7.
    }
    {
      clear -Hnodup_p.
      intros contra.
      subst.
      solve_NoDup_pre'' 7 9.
    }
    {
      clear -Hnodup_p.
      intros contra.
      subst.
      solve_NoDup_pre'' 1 9.
    }
    {
      clear -Hnodup_p.
      intros contra.
      subst.
      solve_NoDup_pre'' 4 9.
    }
    {
      clear -Hnodup_p.
      intros contra.
      subst.
      solve_NoDup_pre'' 4 7.
    }
    {
      program_in_seq.
    }
    iFrame.        
    iSplitL "mem_p_prog2".
    unfold program.
    iEval (rewrite big_opM_map_to_list) in "mem_p_prog2".
    rewrite big_sepL2_alt.
    iSplit; first done.
    rewrite mem_mapsto_eq /mem_mapsto_def.    
    {
      assert (mem_p_prog2 ⊆ σ.1.2) as Hsubseteq.
      {
        rewrite Hunion_mem'.
        apply map_union_subseteq_r'.
        assumption.
        apply map_union_subseteq_l'.
        apply map_union_subseteq_r'.
        assumption.
        done.
      }
      iApply (memory_list_gmap _ _ _ mem_p_prog2 σ).
      - rewrite fst_zip.
        + apply finz_seq_NoDup'.
          simpl.
          pose proof (last_addr_in_bound p_prog2).
          solve_finz.
        + simpl.
          lia.
      - apply HmemH2; done.
      - by iFrame.
    }
    iSplitL "p_tx2".
    {
      unfold memory_page.
      iExists mem_p_tx2. iSplit. rewrite Hdom_mem_p_tx2. iPureIntro.
      rewrite set_of_addr_singleton.
      rewrite to_pid_aligned_eq.
      reflexivity.
      rewrite mem_mapsto_eq /mem_mapsto_def /=.
      iFrame.
    }
    
    iSplitL "access2".
    {
      rewrite access_mapsto_eq /access_mapsto_def.
      simpl.
      rewrite !to_pid_aligned_eq.
      iFrame "access2".
    }
    
    iSplitL "mb1TX".
    {
      rewrite mb_mapsto_eq /mb_mapsto_def /=.
      rewrite to_pid_aligned_eq.
      iFrame.
    }

    iSplitL "R01".
    iExists r0__.
    iFrame.
    iSplitL "R11".
    iExists r1__.
    iFrame.
    iSplitL "R21".
    iExists r2__.
    iFrame.
    iSplitL "R31".
    iExists r3__.
    iFrame.
    iSplitL "R41".
    iExists r4__.
    iFrame.
    iExists r5__.
    iFrame.

    iSplitR ""; last done.
    iApply (mtms_ftlr p_prog3 p_tx3 p_rx3 with "[-] []").
    2: { iPureIntro. cbn. done. }
    { rewrite /mtms_interp_access /interp_access.
      iSplitL "Hreg2".
      iExists (get_reg_files σ !!! V2).
      unfold get_reg_gmap_vm.
      iSplit.
      iPureIntro.
      unfold base_extra.is_total_gmap.
      apply Htotal_reg.
      simpl.
      {
        set g := (λ p0 : reg_name * Addr, (p0.1, 2%fin, p0.2)).
        unfold V2.
        simpl.
        set l := (σ.1.1.1.1.1 !!! 2%fin).
        iEval (rewrite big_opM_map_to_list) in "Hreg2".
        rewrite map_to_list_to_map.
        rewrite big_opL_fmap.
        subst g.
        simpl.
        rewrite big_opM_map_to_list.
        iFrame "Hreg2".
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
      iFrame "VMProp2_half".
      rewrite difference_empty_L.
      unfold transaction_pagetable_entries_owned.
      unfold retrieved_transaction_owned.
      unfold big_sepFM. simpl.
      rewrite map_filter_empty.
      rewrite !big_sepM_empty.
      assert (({[p_prog3; p_tx3; p_rx3]} ∖ {[p_rx3; p_tx3]}) = {[p_prog3]}) as ->.
      {
        rewrite !difference_union_distr_l_L.        
        rewrite difference_disjoint_L.
        assert ({[p_tx3]} ∖ {[p_rx3; p_tx3]} = ∅) as ->.
        { set_solver +. }
        assert ({[p_rx3]} ∖ {[p_rx3; p_tx3]} = ∅) as ->.
        { set_solver +. }
        set_solver +.
        apply disjoint_singleton_l.
        intros contra.
        rewrite elem_of_union in contra.
        rewrite !elem_of_singleton in contra.
        solve_NoDup_pre'.
        solve_NoDup_pre'' 2 8.
        solve_NoDup_pre'' 2 5.
      }
      unfold pagetable_entries_excl_owned.
      unfold logrel.pgt.
      rewrite !big_sepS_singleton.
      unfold tx_page.
      iSplitL "mb2TX p_tx3 excl4 own4".
      iSplitR "p_tx3".      
      rewrite mb_mapsto_eq /mb_mapsto_def.
      rewrite excl_mapsto_eq own_mapsto_eq /excl_mapsto_def /own_mapsto_def.
      iFrame.
      iExists mem_p_tx3. unfold memory_page. iSplit. iPureIntro.
      rewrite Hdom_mem_p_tx3.
      apply set_of_addr_singleton.
      rewrite mem_mapsto_eq /mem_mapsto_def.
      iFrame "p_tx3".
      rewrite access_mapsto_eq /access_mapsto_def /=.
      assert ({[p_tx3; p_rx3; p_prog3]} = {[p_prog3; p_tx3; p_rx3]}) as -> by set_solver +.
      iFrame "access3".
      unfold rx_page.

      iSplitL "mb2RX' excl3 own3".
      {
        rewrite excl_mapsto_eq /excl_mapsto_def.
        rewrite own_mapsto_eq /own_mapsto_def.
        rewrite mb_mapsto_eq /mb_mapsto_def.
        iFrame.
      }
      
      iSplit. iPureIntro. set_solver +.
      iSplit. iPureIntro. set_solver +.

      iSplitL "excl5 own5".
      {
        rewrite excl_mapsto_eq /excl_mapsto_def.
        rewrite own_mapsto_eq /own_mapsto_def.
        iFrame.
      }

      iSplit; first done.
      iSplit; first done.
      
      iExists mem5. unfold memory_pages. iSplit.
      iPureIntro.
      rewrite /retrieved_lending_memory_pages.
      rewrite map_filter_empty pages_in_trans_empty union_empty_r_L //.
      rewrite mem_mapsto_eq /mem_mapsto_def.
      iFrame "Hmem2".
    }
   Qed.

End mtms_adequacy.
