From machine_program_logic.program_logic Require Import machine weakestpre adequacy.
From iris.bi Require Import big_op.
From HypVeri Require Import machine_extra lifting.
From HypVeri.algebra Require Import base mailbox pagetable.
From HypVeri.examples Require Import instr run_yield_1.
Require Import Setoid.

Section Adequacy.
  
  
  Context `{hypparams: !HypervisorParameters}.

  Definition run_vms (ms: list exec_mode):=
    ms = [ExecI;ExecI].

  Definition mk_region (p:PID) (ws: list Word) : gmap Addr Word:=
    (list_to_map (zip (finz.seq (of_pid p) (length ws)) ws)).

  Definition mem_layout (σ : state) (p1 p2 : PID) :=
    (∃ a, is_accessible a = true ∧ (get_vm_page_table σ V0).2 !! p1 = Some a) ∧
    (∃ a, is_accessible a = true ∧ (get_vm_page_table σ V1).2 !! p2 = Some a) ∧
    (mk_region p1 (program1)) ∪ (mk_region p2 program2) ⊆ (get_mem σ).

  Definition reg (σ : state) (p1 p2 : PID):=
    (∃ r0 r1 ,{[PC := (of_pid p1); R0 := r0; R1 := r1]} ⊆ (get_reg_files σ)!!!V0) ∧
    ∃ r0 ,{[PC := (of_pid p2); R0 := r0]} ⊆ (get_reg_files σ) !!! V1 .

  Definition transactions (σ: state):=
    (dom (gset handle) (get_transactions σ).1) ## ((get_transactions σ).2) ∧
    (get_transactions σ).2 ≠ ∅ ∧
    (map_Forall (λ _ v , (length v.1.2 <? word_size)%Z = true) (get_transactions σ).1).

  Definition is_initial_config (σ: state) (ms: list exec_mode) (φs : list (exec_mode -> Prop )):=
                  (get_current_vm σ) = V0 ∧
                  φs = [(λ m ,  m = HaltI ); (λ _, True)] ∧
                  ∃ (p1 p2: PID), p1 ≠ p2 ∧
                                  (run_vms ms) ∧
                                  (mem_layout σ p1 p2) ∧
                                  (reg σ p1 p2) ∧
                                  transactions σ.

  Context {vm_preG: gen_VMPreG Addr VMID Word reg_name PID transaction_type gen_VMΣ}.

  (* exec_mode of all VMs *)
  Lemma run_yield_1_adequacy' (σ : state) (ms : list exec_mode) φs:
    (* we need assumptions to be able to allocate resources *)
    (* with these resources, we apply the specification and get the wptp *)
    (* along with some other stuff, then it should be enough to apply the adequacy theorem *)
    (is_initial_config σ ms φs) ->
    adequate ms σ ((λ φ, λ v _, φ v)<$> φs).
    (* φ : vm 0 is scheduled but halted *)
  Proof.
    intros Hinit.
    eapply (wp_adequacy gen_VMΣ).
    { apply _. }
    intro Hinv.
    iIntros.

    destruct Hinit as ( Hcur & Hinit).
    iMod (na_alloc) as (nainv_gname) "Hna".
    iMod (gen_token_alloc V0) as (token_gname) "[Hσtok Htok]".
    iMod (gen_mem_alloc (get_mem σ)) as (mem_gname) "[Hσmem Hmem]".
    iMod (gen_reg_alloc (get_reg_gmap σ)) as (reg_gname) "[Hσreg Hreg]".
    iMod (gen_tx_alloc (get_tx_agree σ)) as (tx_gname) "[Hσtx _]".
    { apply get_txrx_auth_agree_valid. }
    iMod (gen_rx_agree_alloc (get_rx_agree σ)) as (rx_agree_gname) "[Hσrx_a _]".
    { apply get_txrx_auth_agree_valid. }
    iMod (gen_rx_option_alloc (get_rx_gmap σ)) as (rx_option_gname) "[Hσrx_o _]".
    iMod (gen_pagetable_alloc (get_owned_gmap σ)) as (own_gname) "[Hσown _]".
    iMod (gen_pagetable_alloc (get_access_gmap σ)) as (access_gname) "[Hσaccess Haccess]".
    iMod (gen_pagetable_alloc (get_excl_gmap σ)) as (excl_gname) "[Hσexcl _]".
    iMod (gen_trans_alloc (get_trans_gmap σ)) as (trans_gname) "[Hσtrans _]".
    iMod (gen_hpool_alloc (get_hpool_gset σ)) as (hpool_gname) "[Hσhpool _]".
    iMod (gen_retri_alloc (get_retri_gmap σ)) as (retri_gname) "[Hσretri _]".
    pose vmG := GenVMG gen_VMΣ vm_preG Hinv nainv_preG nainv_gname token_gname mem_gname reg_gname tx_gname
    rx_agree_gname rx_option_gname own_gname access_gname excl_gname trans_gname hpool_gname retri_gname.

    destruct Hinit as (Hφ & p1 & p2 & Hpne & Hms & Hmem & Hreg & Htrans ).
    destruct Hreg as (Hreg1 & Hreg2).
    destruct Hreg1 as (r0_ & r1_ & Hreg1).
    destruct Hreg2 as (r0_' & Hreg2).

    iExists gen_vm_interp.
    rewrite /gen_vm_interp.
    cbn.
    rewrite Hcur.
    iFrame "Hσtok Hσmem Hσreg Hσtx Hσrx_a Hσrx_o Hσown Hσaccess Hσexcl Hσtrans Hσhpool Hσretri".
    destruct Htrans as (Hdisj & Hnempty & Hlen).
    iSplitR.
    iModIntro.
    done.
    (* use assumptions to extract resources *)
    (* for mem: sepM -> sepL2 *)

    iDestruct ((big_sepM_subseteq _ (get_reg_gmap σ) {[(PC, V0):= (of_pid p1); (R0, V0) := r0_;
                                 (R1,V0):= r1_ ; (PC,V1):= (of_pid p2); (R0,V1):= r0_' ]}) with "Hreg") as "Hreg";eauto.
    { rewrite /get_reg_gmap.
      apply map_subseteq_spec.
      intros.
      apply elem_of_list_to_map.
      { admit. }
      apply elem_of_list_In.
      apply in_flat_map.
      exists i.2.
      split.
      apply in_list_of_vmids.
      apply in_map_iff.
      exists (i.1, x).
      split.
      destruct i.
      cbn.
      done.
      apply elem_of_list_In.
      apply elem_of_map_to_list.
      rewrite /get_vm_reg_file.
      destruct i.
      cbn.
      admit.
      (* TODO: it is true, don't know how to prove... *)
    }

    destruct Hmem as (Hacc1 & Hacc2 & Hmem).
    iDestruct ((gen_pagetable_SepM_split2 V0 V1) with "[Haccess]") as "(Haccessz & Haccessi & _)";eauto.
    set (sacc1 := (get_pagetable_gset σ V0 (λ pt : page_table, pt.2) is_accessible)) in *.
    set (sacc2 := (get_pagetable_gset σ V1 (λ pt : page_table, pt.2) is_accessible)) in *.
    assert (fin_to_nat V0 = 0) as Heqz. done.
    assert (V0 ≠ V1) as Hneq. done.
    pose proof (@run_yield_1_spec _ _ gen_VMΣ vmG tokG nroot V0 V1 1 1 p1 p2 sacc1 sacc2 r0_ r1_ r0_' Heqz Hneq Hpne)
      as HSpec.

    iDestruct (HSpec with "[Hmem Htok Hreg Haccessz Haccessi Hna]") as "HWPs";eauto.
    { apply elem_of_list_to_set.
      apply elem_of_list_In.
      apply in_map_iff.
      destruct Hacc1 as [a Hacc1].
      exists (p1, a).
      split;[done|].
      apply elem_of_list_In.
      apply elem_of_map_to_list.
      apply map_filter_lookup_Some.
      destruct Hacc1;split;done.
    }
    { apply elem_of_list_to_set.
      apply elem_of_list_In.
      apply in_map_iff.
      destruct Hacc2 as [a Hacc2].
      exists (p2, a).
      split;[done|].
      apply elem_of_list_In.
      apply elem_of_map_to_list.
      apply map_filter_lookup_Some.
      destruct Hacc2;split;done.
    }
    iFrame.

    rewrite !big_sepM_insert ?big_sepM_empty;eauto.
    rewrite reg_mapsto_eq /reg_mapsto_def.
    iDestruct "Hreg" as "(PCz & R0z & R1z & PCi & R0i & _)".
    2: { rewrite !lookup_insert_None; split;eauto. }
    2: { rewrite !lookup_insert_None; split;eauto. }
    2: { rewrite !lookup_insert_None; split;eauto. }
    2: { rewrite !lookup_insert_None; split;eauto. }
    rewrite token_agree_eq /token_agree_def.
    rewrite access_mapsto_eq /access_mapsto_def.
    iFrame.

    iDestruct ((big_sepM_subseteq _ (get_mem σ) (mk_region p1 (program1 V1) ∪ mk_region p2 program2))
                 with "Hmem") as "Hmem";eauto.
    iDestruct ((big_sepM_union _ _) with "Hmem") as "[Hprog1 Hprog2]".
    {
      rewrite /mk_region.
      apply map_disjoint_list_to_map_zip_r_2.
      rewrite finz_seq_length //.
      apply Forall_forall.
      intros.
      apply  not_elem_of_list_to_map_1.
      rewrite fst_zip.
      apply (addr_in_notin p2 p1 x (length program2));eauto.
      by vm_compute.
      by vm_compute.
      rewrite finz_seq_length //.
    }
    (* TODO: make a lemma *)
    {
    rewrite /program.
    iSplitL "Hprog1".
    {
    iApply (big_sepL2_alt with "[Hprog1]").
    iSplitR.
    rewrite finz_seq_length //.
    rewrite <- (@map_to_list_to_map Addr (gmap Addr) _  _  _  _ _ _ _ _ _ Word _).
    2: { rewrite fst_zip. apply finz_seq_NoDup'. pose proof (last_addr_in_bound p1). solve_finz.
       rewrite finz_seq_length //. }
    rewrite -(big_opM_map_to_list (λ a w,  (a ->a w)%I) _ ).
    rewrite  mem_mapsto_eq /mem_mapsto_def /mk_region.
    iFrame.
    }
    {
    iApply (big_sepL2_alt with "[Hprog2]").
    iSplitR.
    rewrite finz_seq_length //.
    rewrite <- (@map_to_list_to_map Addr (gmap Addr) _  _  _  _ _ _ _ _ _ Word _).
    2: { rewrite fst_zip. apply finz_seq_NoDup'. pose proof (last_addr_in_bound p2). solve_finz.
       rewrite finz_seq_length //. }
    rewrite -(big_opM_map_to_list (λ a w,  (a ->a w)%I) _ ).
    rewrite  mem_mapsto_eq /mem_mapsto_def /mk_region.
    iFrame.
    }
    }

    iMod "HWPs" as "[HWPz HWPi]".
    iModIntro.
    rewrite /run_vms in Hms.
    subst ms.
    destruct φs.
    done.
    inversion Hφ.
    subst P.
    iSplitL "HWPz".
    rewrite Heqz.
    iApply (wp_mono with "HWPz") .
    iIntros (k) "[? ?]".
    iFrame.
    destruct φs.
    done.
    inversion Hφ.
    subst P.
    iSplitL "HWPi".
    assert (fin_to_nat V1= 1) as ->.
    done.
    iApply (wp_mono with "HWPi") .
    iIntros (k) "[? ?]".
    done.
    done.
  Admitted.

End Adequacy.
