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

  Definition pgt_layout (σ : state) (p1 p2 : PID) :=
    (* pvm has exclusive access to prog pg 1 *)
    (∃ (e:VMID * gset VMID), (get_page_table σ) !! p1 = Some e ∧ {[V0]} = e.2) ∧
    (* VM1 has exclusive access to prog pg 2 *)
    (∃ (e:VMID * gset VMID), (get_page_table σ) !! p2 = Some e ∧ {[V1]} = e.2) ∧
    (* pgt is total *)
    (* Have no other assumptions on the pagetable.
       Namely, other irrelavant pages can be owned/accessible by anyone *)
    (∀ p, is_Some ((get_page_table σ) !! p)).

  Definition mem_layout (σ : state) (p1 p2 : PID) :=
    let mem := ((get_mem σ): gmap Addr Word)  in
    (* prog 1 is in prog pg 1 *)
    (∀ (a w: Word), (a,w) ∈ (zip (finz.seq (of_pid p1) (length rywu_program1)) rywu_program1) -> (mem !! a) = Some w) ∧
    (* prog 2 is in prog pg 2 *)
    (∀ (a w: Word), (a,w) ∈ (zip (finz.seq (of_pid p2) (length rywu_program2)) rywu_program2) -> (mem !! a) = Some w) ∧
    (* is total *)
    (∀ (a: Addr), is_Some (mem !! a)).

  Definition reg_layout (σ : state) (p1 p2 : PID):=
    (get_reg_files σ)!!!V0 !! PC = Some (of_pid p1) ∧
    (get_reg_files σ)!!!V1 !! PC = Some (of_pid p2) ∧
    (* is total *)
    ∀ i rn, is_Some (((get_reg_files σ) !!! i) !! rn).

  (* Definition mem_inv (σ : state) (p1 : PID) := (∃ a, is_owned a = true ∧ (get_vm_page_table σ V0).1 !! p1 = Some a). *)

  Definition transactions (σ: state):=
    (* no transactions! *)
    (get_transactions σ).1 = ∅ ∧
    (∀ h, h ∈ (get_transactions σ).2).

  Definition initial_config (σ: state) (ms: list exec_mode) (φs : list (exec_mode -> Prop )):=
                  (get_current_vm σ) = V0 ∧
                  (* post conditions *)
                  φs = [(λ m , m = HaltI); (λ _, False); (λ _, True)] ∧
                  ms = [ExecI;ExecI;ExecI] ∧
                  (∃ (p1 p2: PID),
                      p1 ≠ p2 ∧
                      (pgt_layout σ p1 p2) ∧
                      (mem_layout σ p1 p2) ∧
                      (reg_layout σ p1 p2)) ∧
                  transactions σ ∧
                  inv_trans_hpool_consistent σ ∧
                  inv_trans_pgt_consistent σ ∧
                  inv_trans_pg_num_ub σ.
  
  Definition irisΣ :=
    #[gen_VMΣ; invΣ; na_invΣ; savedPropΣ; GFunctor (authUR (optionUR (frac_agreeR gnameO)));
     GFunctor (authUR (gmapUR nat (agreeR gnameO)))].

  Local Instance iris_subG Σ : subG irisΣ Σ → irisPreGS Σ.
  Proof. solve_inG. Qed.

  Local Instance na_inv_subG Σ : subG irisΣ Σ → na_invG Σ.
  Proof. solve_inG. Qed.
  
  Context {vm_preG: gen_VMPreG Addr VMID Word reg_name PID transaction_type irisΣ}.

  Definition get_reg_gmap_vm (σ:state) (v:VMID) : gmap (reg_name * VMID) Word :=
    (list_to_map (map (λ p, ((p.1,v),p.2)) (map_to_list ((get_reg_files σ !!! v):reg_file)))).


  Definition get_mem_gmap_vm (σ:state) (pgt: page_table) (v:VMID) : gmap Addr Word :=
    (filter (λ (m: Addr * Word),  (match pgt !! (tpa m.1) with
                                   | Some perm => v ∈ perm.2
                                   | None => True
                                   end)) σ.1.2).

  Definition get_mem_gmap_page (σ:state) (p : PID) : gmap Addr Word:=
    filter (λ (m:Addr * Word), tpa m.1 = p) σ.1.2.

  Lemma get_mem_gmap_vm_noaccess_disj (σ:state) (pgt: page_table) (p: PID) (v:VMID):
    (∃ perm, pgt !! p = Some perm ∧ v ∉ perm.2) -> get_mem_gmap_page σ p ##ₘ get_mem_gmap_vm σ pgt v.
  Proof.
    intros.
    Admitted.
    
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

  Lemma get_reg_gmap_vm_lookup_Some σ i r w :
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
    ([∗ map] p↦w ∈ get_reg_gmap σ, p ↪[γ] w)%I ⊢ [∗ list] i ∈ (list_of_vmids), [∗ map] p↦w ∈ get_reg_gmap_vm σ i, p ↪[γ] w.
  Proof.
    iIntros "Hmap".
    rewrite /get_reg_gmap.
    iInduction (list_of_vmids) as [ | i l] "IH".
    done.
    simpl.
    rewrite list_to_map_app.
    rewrite big_sepM_union.
    iDestruct "Hmap" as "[Hsub Hmap]".
    iSplitL "Hsub".
    {
      rewrite /get_reg_gmap_vm.
      admit.
      (* couldn't iFrame, because of using different hypervisiorconstants *)
      (* iFrame "Hsub". *)
    }
    iApply "IH".
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
    (* inversion Heqn;subst;clear Heqn. *)
    destruct H1 as [i'].
    destruct H as [HIn H].
    apply elem_of_list_In in H.
    apply H0 in H.
    rewrite Heqn in H.
    simpl in H.
    subst i'.
    (* get a contradiction using HIn as list_of_vmids is NoDup (seems necessary to perform induction on vmcount) *)
  Admitted.

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
    iMod (gen_owned_alloc σ) as (own_gname) "[Hσown Hown]".
    iMod (gen_access_alloc σ) as (access_gname) "[Hσaccess Haccess]".
    iMod (gen_trans_alloc σ) as (trans_gname) "[Hσtrans _]".
    iMod (gen_hpool_alloc σ) as (hpool_gname) "[Hσhpool Hhpool]".
    iMod (gen_retri_alloc σ) as (retri_gname) "[Hσretri _]".
    iMod (gen_lower_bound_alloc ∅) as (lb_gname) "[HLB_auth _]".
    (* iMod (na_alloc) as (nainv_gname) "Hna". *)
    
    iModIntro.
    iIntros (name_map_name).
    pose ((GenVMG irisΣ vm_preG Hinv _ (* nainv_gname *) _ _ (* _ *) name_map_name mem_gname reg_gname mb_gname rx_state_gname
                  own_gname access_gname trans_gname hpool_gname retri_gname lb_gname)) as VMG.
    iExists (gen_vm_interp (Σ := irisΣ)).
    
    destruct Hinit as (-> & -> & (p1 & p2 & Hpne & Hpgt & Hmem & Hreg) & Htrans & Hinv_trans_hpool & Hinv_trans_pgt & Hinv_trans_pg_num_ub).
    destruct Hreg as (Hlookup_reg0_pc & Hlookup_reg1_pc & Htotal_reg).
    destruct Htrans as (Heq_trans & Hin_hpool).

    iModIntro.

    (* allocate VMProps *)
    set pgt := (get_page_table σ).
    iExists [True%I;
      ((R0 @@ V0 ->r run_I ∗ R1 @@ V0 ->r encode_vmid V1 ∗ p2 -@A> V1) ∗
         VMProp V0 ((R0 @@ V0 ->r yield_I ∗ R1 @@ V0 ->r encode_vmid V1 ∗ p2 -@A> V1) ∗ VMProp V1 False%I (1/2)%Qp) (1/2)%Qp)%I;
      ((R0 @@ V0 ->r encode_hvc_func(Run) ∗ R1 @@ V0 ->r encode_vmid(V2) ∗
        VMProp V0 (
          (R0 @@ V0 ->r encode_hvc_func(Yield) ∗ R1 @@ V0 ->r encode_vmid(V2) ∗
           (pagetable_entries pgt)) ∨ False) (1/2)%Qp ∗ (pagetable_entries pgt)))%I].
    iSimpl.
    iSplit; first done.

    (* frame state_interp *)
    iSplitR "Hmem Hreg Haccess Hown Hrxs Hmb Hhpool".
    iFrame.
    repeat iSplit.
    done.
    rewrite Heq_trans.
    iPureIntro.
    set_solver +.
    admit.
    iPureIntro.
    rewrite /inv_trans_pg_num_ub.
    rewrite Heq_trans.
    apply map_Forall_empty.
    admit.

    iIntros "(VMProp0 & VMProp1 & VMProp2)".
    rewrite /scheduled /machine.scheduler //= /scheduler Hcur //=.
    
    (* use assumptions to extract resources *)

    (* extract regs  *)
    iDestruct (get_reg_gmap_split with "Hreg") as "(Hreg0 & Hreg1 & Hreg2 & _)".
    (* extrac regs of VM0 *)
    pose proof (Htotal_reg V0 R0) as [r0_ Hlookup_reg0_r0].
    pose proof (Htotal_reg V0 R1) as [r1_ Hlookup_reg0_r1].
    iDestruct (big_sepM_subseteq _ (get_reg_gmap_vm σ V0) {[(PC, V0):= (of_pid p1); (R0, V0) := r0_;
                                 (R1,V0):= r1_]} with "Hreg0") as "Hreg0";eauto.
    {
      rewrite /get_reg_gmap.
      apply map_subseteq_spec.
      intros i x H.
      admit.
    }
    iDestruct (big_sepM_insert with "Hreg0") as "(PCz & Hreg0)".
    (* iDestruct "Hreg" as "(PCz & R0z & R1z & PCi & R0i & _)". *)
    { rewrite !lookup_insert_None; split;eauto. }
    iDestruct (big_sepM_insert with "Hreg0") as "(R0z & Hreg0)".
    { rewrite !lookup_insert_None; split;eauto. }
    iDestruct (big_sepM_insert with "Hreg0") as "(R1z & _)".
    { rewrite lookup_empty; eauto. }


    (* extrac regs of VM1 *)
    pose proof (Htotal_reg V1 R0) as [r0__ Hlookup_reg1_r0].
    iDestruct (big_sepM_subseteq _ (get_reg_gmap_vm σ V1) {[(PC, V1):= (of_pid p1); (R0, V1) := r0__]} with "Hreg1") as "Hreg1";eauto.
    {
      rewrite /get_reg_gmap.
      apply map_subseteq_spec.
      intros i x H.
      admit.
    }

    iDestruct (big_sepM_insert with "Hreg1") as "(PC1 & Hreg1)".
    { rewrite !lookup_insert_None; split;eauto. }
    iDestruct (big_sepM_insert with "Hreg1") as "(R01 & _)".
    { rewrite lookup_empty; eauto. }

    (* TODO, regs of VM2 in logrel are in another notation *)

    destruct Hmem as ( ? & ? & Htotal_mem).
    destruct Hpgt as ( Hlookup_pgt_p1 & Hlookup_pgt_p2 & Htotal_pgt).

    iDestruct (big_sepM_subseteq _ (get_mem σ) (get_mem_gmap_page σ p1 ∪ get_mem_gmap_page σ p2 ∪ get_mem_gmap_vm σ pgt V2)
                 with "Hmem") as "Hmem"; eauto.
    admit.

    iDestruct ((big_sepM_union _ _) with "Hmem") as "(Hprog12 & Hmem2)".
    {
      apply  map_disjoint_union_l.
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
