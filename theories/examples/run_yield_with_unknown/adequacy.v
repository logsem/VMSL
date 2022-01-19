From machine_program_logic.program_logic Require Import machine weakestpre adequacy.
From iris.algebra Require Import big_op.
From HypVeri Require Import machine_extra lifting.
From HypVeri.algebra Require Import base mailbox pagetable.
From HypVeri.lang Require Import reg_extra.
From HypVeri.examples Require Import instr.
From HypVeri.logrel Require Import logrel.
From HypVeri.examples.run_yield_with_unknown Require Import proof ftlr.
Require Import Setoid.
(* Require Import Coq.Program.Equality. *)

Section rywu_adequacy.
    
  Context `{hypparams: !HypervisorParameters}.

  Definition mk_region (p:PID) (ws: list Word) : gmap Addr Word:=
    (list_to_map (zip (finz.seq (of_pid p) (length ws)) ws)).

  Definition pgt_layout (σ : state) (p_prog1 p_prog2 p_prog3 p_tx3 p_rx3 : PID) :=
    (* pvm has exclusive access to prog pg 1 *)
    ((get_page_table σ) !! p_prog1 = Some (Some V0,true, {[V0]})) ∧
    (* VM1 has exclusive access to prog pg 2 *)
    ((get_page_table σ) !! p_prog2 = Some (Some V1,true, {[V1]})) ∧
    ((get_page_table σ) !! p_prog3 = Some (Some V2, true, {[V2]})) ∧
    ((get_page_table σ) !! p_tx3 = Some (None, true, {[V2]})) ∧
    ((get_page_table σ) !! p_rx3 = Some (None, true, {[V2]}))
    (* Have no other assumptions on the pagetable.
       Namely, other irrelavant pages can be owned/accessible by anyone *)
    .


  Definition mem_layout (σ : state) (p_prog1 p_prog2 p_prog3 p_tx3 p_rx3 : PID) :=
    let mem := ((get_mem σ): gmap Addr Word)  in
    (* prog 1 is in prog pg 1 *)
    (∀ (a w: Word), (a,w) ∈ (zip (finz.seq (of_pid p_prog1) (length rywu_program1)) rywu_program1) -> (mem !! a) = Some w) ∧
    (* prog 2 is in prog pg 2 *)
    (∀ (a w: Word), (a,w) ∈ (zip (finz.seq (of_pid p_prog2) (length rywu_program2)) rywu_program2) -> (mem !! a) = Some w) ∧
    ((set_of_addr {[p_prog1;p_prog2;p_prog3;p_tx3;p_rx3]}) ⊆ dom (gset _) mem).

  Definition reg_layout (σ : state) (p_prog1 p_prog2 : PID):=
    (get_reg_files σ)!!!V0 !! PC = Some (of_pid p_prog1) ∧
    (get_reg_files σ)!!!V1 !! PC = Some (of_pid p_prog2) ∧
    (* is total *)
    ∀ i rn, is_Some (((get_reg_files σ) !!! i) !! rn).

  Definition mailbox (σ: state) (p_tx3 p_rx3 : PID):=
    (get_mail_box σ @ V2) = (p_tx3, (p_rx3, None)).

  Definition transactions (σ: state):=
    (* no transactions! *)
    dom (gset _ ) (get_transactions σ) = hs_all ∧
    map_Forall (λ k v, v = None) (get_transactions σ).

  Definition initial_config (σ: state) (ms: list exec_mode) (φs : list (exec_mode -> Prop )):=
                  (get_current_vm σ) = V0 ∧
                  (* post conditions *)
                  φs = [(λ m , m = HaltI); (λ _, False); (λ _, True)] ∧
                  ms = [ExecI;ExecI;ExecI] ∧
                  (∃ (p_prog1 p_prog2 p_prog3 p_tx3 p_rx3: PID),
                      NoDup [p_prog1;p_prog2;p_prog3;p_tx3;p_rx3 ] ∧
                      (pgt_layout σ p_prog1 p_prog2 p_prog3 p_tx3 p_rx3) ∧
                      (mem_layout σ p_prog1 p_prog2 p_prog3 p_tx3 p_rx3) ∧
                      (reg_layout σ p_prog1 p_prog2) ∧
                        (mailbox σ  p_tx3 p_rx3)
                  ) ∧
                  transactions σ.

  (* Definition irisΣ := *)
  (*   #[gen_VMΣ; invΣ; savedPropΣ; GFunctor (authUR (optionUR (dfrac_agreeR gnameO))); *)
  (*    GFunctor (authUR (gmapUR nat (agreeR gnameO)))]. *)

  (* Local Instance iris_subG Σ : subG irisΣ Σ → irisPreGS Σ. *)
  (* Proof. solve_inG. Qed. *)

  Context {vm_preG: gen_VMPreG Addr VMID Word reg_name PID transaction_type irisΣ}.

  Definition get_reg_gmap_vm (σ:state) (v:VMID) : gmap (reg_name * VMID) Word :=
    (list_to_map (map (λ p, ((p.1,v),p.2)) (map_to_list ((get_reg_files σ !!! v))))).

  (* Definition get_mem_gmap_vm (σ:state) (pgt: page_table) (v:VMID) : gmap Addr Word := *)
  (*   (filter (λ (m: Addr * Word),  (match pgt !! (tpa m.1) with *)
  (*                                  | Some perm => v ∈ perm.2 *)
  (*                                  | None => True *)
  (*                                  end)) σ.1.2). *)


  (* Lemma get_mem_gmap_vm_noaccess_disj (σ:state) (pgt: page_table) (p: PID) (v:VMID): *)
  (*   (∃ perm, pgt !! p = Some perm ∧ v ∉ perm.2) -> get_mem_gmap_page σ p ##ₘ get_mem_gmap_vm σ pgt v. *)
  (* Proof. *)
  (*   intros. *)
  (*   Admitted. *)

  Lemma get_reg_gmap_vm_lookup_eq σ i i' r:
    is_Some ((get_reg_gmap_vm σ i) !! (r,i')) -> i = i'.
  Proof.
    intros [? Hlookup].
    rewrite /get_reg_gmap_vm in Hlookup.
    apply elem_of_list_to_map_2 in Hlookup.
    apply elem_of_list_In in Hlookup.
    apply in_map_iff in Hlookup.
    destruct Hlookup as [p].
    destruct H as [Heqn].
    inversion Heqn ;subst;clear Heqn.
    done.
  Qed.

  Lemma get_reg_gmap_vm_lookup_Some σ (i:VMID) r w :
    (get_reg_gmap_vm σ i) !! (r,i) = Some w <-> get_reg_file σ @ i !! r = Some w.
  Proof.
    split.
    - unfold get_reg_gmap_vm.
      intro HSome.
      apply elem_of_list_to_map_2 in HSome.
      apply elem_of_list_In in HSome.
      apply in_map_iff in HSome.
      destruct HSome as [p].
      destruct H as [Heqn].
      inversion Heqn ;subst;clear Heqn.
      apply elem_of_list_In in H.
      by apply elem_of_map_to_list' in H.
    - intro HSome.
      apply  elem_of_list_to_map_1'.
      + intros.
        apply elem_of_list_In in H.
        apply in_map_iff in H.
        destruct H as [p].
        destruct H as [Heqn H].
        apply elem_of_list_In in H.
        apply elem_of_map_to_list' in H.
        inversion Heqn;subst;clear Heqn.
        rewrite H in HSome.
        by inversion HSome.
      + apply elem_of_list_In.
        apply in_map_iff.
        exists (r,w).
        split;[done|].
        apply elem_of_list_In.
        apply elem_of_map_to_list'.
        done.
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


  (* Definition irisΣ := *)
  (*   #[gen_VMΣ; invΣ; savedPropΣ; GFunctor (authUR (optionUR (dfrac_agreeR gnameO))); *)
  (*    GFunctor (authUR (gmapUR nat (agreeR gnameO)))]. *)

  (* Local Instance iris_subG Σ : subG irisΣ Σ → irisPreGS Σ. *)
  (* Proof. solve_inG. Qed. *)

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
    iMod (gen_trans_alloc σ) as (trans_gname) "[Hσtrans _]".
    iMod (gen_hpool_alloc σ) as (hpool_gname) "[Hσhpool Hhpool]".
    iMod (gen_retri_alloc σ) as (retri_gname) "[Hσretri _]".
    iMod (gen_lower_bound_alloc ∅) as (lb_gname) "[HLB_auth _]".

    iModIntro.
    iIntros (name_map_name).
    pose ((GenVMG irisΣ vm_preG Hinv _ (* nainv_gname *) _ _ (* _ *) name_map_name mem_gname reg_gname mb_gname rx_state_gname
                  own_gname access_gname excl_gname trans_gname hpool_gname retri_gname lb_gname)) as VMG.
    iExists (gen_vm_interp (Σ := irisΣ)).
    
    destruct Hinit as (-> & -> & (p_prog1 & p_prog2 & p_prog3 & p_tx3 & p_rx3 & Hnodup_p & Hpgt & Hmem & Hreg & Hmb) & Htrans).
    (* FIXME: the two rewriting above are slow *)
    destruct Hreg as (Hlookup_reg0_pc & Hlookup_reg1_pc & Htotal_reg).

    iModIntro.

    (* allocate VMProps *)
    set pgt := (get_page_table σ).
    iExists [True%I;
      ((R0 @@ V0 ->r run_I ∗ R1 @@ V0 ->r encode_vmid V1 ∗ V1 -@A> {[p_prog2]}) ∗
         VMProp V0 ((R0 @@ V0 ->r yield_I ∗ R1 @@ V0 ->r encode_vmid V1 ∗ V1 -@A> {[p_prog2]}) ∗ VMProp V1 False%I (1/2)%Qp) (1/2)%Qp)%I;
      (VMProp_unknown V2 p_tx3 p_rx3 ∅)%I].
    iSimpl.
    iSplit; first done.

    (* frame state_interp *)
    iSplitR "Hmem Hreg Haccess Hown Hexcl Hrxs Hmb Hhpool".
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

    iIntros "(VMProp0 & VMProp1 & VMProp2)".
    rewrite /scheduled /machine.scheduler //= /scheduler Hcur //=.
    
    (* use assumptions to extract resources *)

    (** extract regs  **)
    iDestruct (get_reg_gmap_split with "Hreg") as "(Hreg0 & Hreg1 & Hreg2 & _)".
    (* extrac regs of VM0 *)
    pose proof (Htotal_reg V0 R0) as [r0_ Hlookup_reg0_r0].
    pose proof (Htotal_reg V0 R1) as [r1_ Hlookup_reg0_r1].
    iDestruct (big_sepM_subseteq _ (get_reg_gmap_vm σ V0) {[(PC, V0):= (of_pid p_prog1); (R0, V0) := r0_;
                                 (R1,V0):= r1_]} with "Hreg0") as "Hreg0";eauto.
    {
      apply map_subseteq_spec.
      intros [r i] w Hlookup.
      assert (i = V0) as ->.
      {
        destruct (decide (i = V0));auto.
        apply elem_of_dom_2 in Hlookup.
        set_solver.
      }
      rewrite get_reg_gmap_vm_lookup_Some.
      simpl in Hlookup.
      destruct r;
      simplify_map_eq.
      (* stuff about Rn = (R n fin_n) *)
      admit.
      admit.
    }
    iDestruct (big_sepM_insert with "Hreg0") as "(PCz & Hreg0)".
    (* iDestruct "Hreg" as "(PCz & R0z & R1z & PCi & R0i & _)". *)
    { rewrite !lookup_insert_None; split;eauto. }
    iDestruct (big_sepM_insert with "Hreg0") as "(R0z & Hreg0)".
    { rewrite !lookup_insert_None; split;eauto. }
    iDestruct (big_sepM_insert with "Hreg0") as "(R1z & _)".
    { rewrite lookup_empty; eauto. }


    (* extract regs of VM1 *)
    pose proof (Htotal_reg V1 R0) as [r0__ Hlookup_reg1_r0].
    iDestruct (big_sepM_subseteq _ (get_reg_gmap_vm σ V1) {[(PC, V1):= (of_pid p_prog2); (R0, V1) := r0__]} with "Hreg1") as "Hreg1";eauto.
    {
      apply map_subseteq_spec.
      intros [r i] w Hlookup.
      assert (i = V1) as ->.
      {
        destruct (decide (i = V1));auto.
        apply elem_of_dom_2 in Hlookup.
        set_solver.
      }
      rewrite get_reg_gmap_vm_lookup_Some.
      simpl in Hlookup.
      destruct r;
      simplify_map_eq.
      (* stuff about Rn = (R n fin_n) *)
      admit.
      admit.
    }
    iDestruct (big_sepM_insert with "Hreg1") as "(PC1 & Hreg1)".
    { rewrite !lookup_insert_None; split;eauto. }
    iDestruct (big_sepM_insert with "Hreg1") as "(R01 & _)".
    { rewrite lookup_empty; eauto. }

    (* TODO: regs of VM2 in logrel are in another notation *)

    (** extract mem **)

    destruct Hmem as ( ? & ? & Hdom_mem).
    destruct Hpgt as ( Hlookup_pgt_p1 & Hlookup_pgt_p2 & Hlookup_pgt_p3 & Hlookup_pgt_tx3 & Hlookup_pgt_rx3).
    pose proof (logrel_extra.union_split_difference_intersection_subseteq_L _ _ Hdom_mem) as [Hdom_mem_union Hdom_mem_disj].
    pose proof (dom_union_inv_L _ _ _ Hdom_mem_disj Hdom_mem_union) as (mem1 & mem2 & Hunion_mem & Hdisj_mem & _ & Hdom_mem2).

    iDestruct (big_sepM_subseteq _ (get_mem σ) mem2 with "Hmem") as "Hmem"; eauto.
    {
      rewrite Hunion_mem.
      apply map_union_subseteq_r.
      done.
    }

    clear Hunion_mem Hdisj_mem mem1.

    (* TODO: WIP *)

    iDestruct ((big_sepM_union _ _) with "Hmem") as "(Hprog12 & Hmem2)".
    {
      apply map_disjoint_union_l.
      split.
      apply get_mem_gmap_vm_noaccess_disj.
      destruct Hlookup_pgt_p1 as [perm [Hlookup_pgt_p1 Hin_p1]].
      exists perm.
      split;eauto.
      set_solver + Hin_p1.
      apply get_mem_gmap_vm_noaccess_disj.
      destruct Hlookup_pgt_p2 as [perm [Hlookup_pgt_p2 Hin_p2]].
      exists perm.
      split;eauto.
      set_solver + Hin_p2.
    }

    iDestruct ((big_sepM_union _ _) with "Hprog12") as "(Hprog1 & Hprog2)".
    {
      admit.
    }

    iDestruct (VMProp_split with "VMProp1") as "[VMProp1_half VMProp1_half']".
    iDestruct (VMProp_split with "[VMProp2]") as "[VMProp2_half VMProp2_half']".
    iDestruct "VMProp2" as "[$ _]".

    iSplitL "PCz R0z R1z Hprog1 Haccess Hhpool VMProp0 VMProp1_half' VMProp2_half'".
    iIntros "_".
    iDestruct (rywu_machine0 (prog1page := p1) (prog2page := p2) pgt _ with "[-]") as "HWP".
    { admit. }
    { admit. }
    admit.

    iSplitL "Hprog2 VMProp1_half PC1 R01".
    iApply (rywu_machine1 (prog2page:= p2)).
    { admit. }
    { admit. }

    iSplitR ""; last done.
    iApply (rywu_ftlr V2 pgt with "[-] []").
    { iExists (σ.1.1.1.1.1 !!! V2) , σ.1.2.
      iSplitL "Hreg2".
      admit.
      admit.
    }
    iPureIntro.
    simpl.
    lia.

   Admitted.

End rywu_adequacy.
