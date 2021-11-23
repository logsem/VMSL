From machine_program_logic.program_logic Require Import machine weakestpre adequacy.
From iris.bi Require Import big_op.
From HypVeri Require Import machine_extra lifting.
From HypVeri.algebra Require Import base mailbox pagetable.
From HypVeri.examples Require Import instr run_yield_1.
Require Import Setoid.
Require Import Coq.Program.Equality.

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

  Definition mem_inv (σ : state) (p1 : PID) := (∃ a, is_owned a = true ∧ (get_vm_page_table σ V0).1 !! p1 = Some a).

  Definition transactions (σ: state):=
    (dom (gset handle) (get_transactions σ).1) ## ((get_transactions σ).2) ∧
    (get_transactions σ).2 ≠ ∅ ∧
    (map_Forall (λ _ v , (length v.1.2 <? word_size)%Z = true) (get_transactions σ).1).

  Definition is_initial_config (σ: state) (ms: list exec_mode) (φs : list (exec_mode -> Prop )):=
                  (get_current_vm σ) = V0 ∧
                  φs = [(λ m , m = HaltI); (λ _, False)] ∧
                  ∃ (p1 p2: PID), p1 ≠ p2 ∧
                                  (run_vms ms) ∧
                                  (mem_layout σ p1 p2) ∧
                                  (mem_inv σ p1) ∧
                                  (reg σ p1 p2) ∧
                                  transactions σ.
  
  Definition irisΣ :=
    #[gen_VMΣ; invΣ; na_invΣ; savedPropΣ; GFunctor (authUR (optionUR (frac_agreeR gnameO)));
     GFunctor (authUR (gmapUR nat (agreeR gnameO)))].

  Local Instance iris_subG Σ : subG irisΣ Σ → irisPreGS Σ.
  Proof. solve_inG. Qed.

  Local Instance na_inv_subG Σ : subG irisΣ Σ → na_invG Σ.
  Proof. solve_inG. Qed.
  
  Context {vm_preG: gen_VMPreG Addr VMID Word reg_name PID transaction_type irisΣ}.

  Definition invN : namespace := nroot .@ "inv".
  
  (* exec_mode of all VMs *)
  Lemma run_yield_1_adequacy (σ : state) (ms : list exec_mode) φs:
    (* we need assumptions to be able to allocate resources *)
    (* with these resources, we apply the specification and get the wptp *)
    (* along with some other stuff, then it should be enough to apply the adequacy theorem *)
    (is_initial_config σ ms φs) ->
    adequate ms σ ((λ φ, λ v _, φ v)<$> φs).
    (* φ : vm 0 is scheduled but halted *)
  Proof.
    intros Hinit.
    set (saved_props := (let (_, x, _, _) := iris_subG irisΣ (subG_refl irisΣ) in x)).
    set (prop_name := (let (_, _, x, _) := iris_subG irisΣ (subG_refl irisΣ) in x)).
    set (name_map := (let (_, _, _, x) := iris_subG irisΣ (subG_refl irisΣ) in x)).
    eapply (wp_adequacy irisΣ); auto.
    destruct Hinit as (Hcur & -> & (p1 & p2 & p1p2ne & -> & Hmem & Hreg & Hreginv & Htrans)).
    by simpl.
    intro Hinv.
    iIntros.
    destruct Hinit as ( Hcur & Hinit).
    iMod (gen_mem_alloc (get_mem σ)) as (mem_gname) "[Hσmem Hmem]".
    iMod (gen_reg_alloc (get_reg_gmap σ)) as (reg_gname) "[Hσreg Hreg]".
    iMod (gen_tx_alloc (get_tx_agree σ)) as (tx_gname) "[Hσtx _]".
    { apply get_txrx_auth_agree_valid. }
    iMod (gen_rx_agree_alloc (get_rx_agree σ)) as (rx_agree_gname) "[Hσrx_a _]".
    { apply get_txrx_auth_agree_valid. }
    iMod (gen_rx_option_alloc (get_rx_gmap σ)) as (rx_option_gname) "[Hσrx_o _]".
    iMod (gen_pagetable_alloc (get_owned_gmap σ)) as (own_gname) "[Hσown Hown]".
    iMod (gen_pagetable_alloc (get_access_gmap σ)) as (access_gname) "[Hσaccess Haccess]".
    iMod (gen_pagetable_alloc (get_excl_gmap σ)) as (excl_gname) "[Hσexcl _]".
    iMod (gen_trans_alloc (get_trans_gmap σ)) as (trans_gname) "[Hσtrans _]".
    iMod (gen_hpool_alloc (get_hpool_gset σ)) as (hpool_gname) "[Hσhpool _]".
    iMod (gen_retri_alloc (get_retri_gmap σ)) as (retri_gname) "[Hσretri _]".
    iMod (na_alloc) as (nainv_gname) "Hna".
    
    iModIntro.
    iIntros (name_map_name).
    pose ((GenVMG irisΣ vm_preG Hinv _ nainv_gname _ _ _ name_map_name mem_gname reg_gname tx_gname rx_agree_gname rx_option_gname own_gname access_gname excl_gname trans_gname hpool_gname retri_gname)) as VMG.
    iExists (gen_vm_interp (Σ := irisΣ)).
    
    destruct Hinit as (Hφ & p1 & p2 & Hpne & Hms & Hmem & Hmeminv & Hreg & Htrans ).    
    destruct Hreg as (Hreg1 & Hreg2).
    destruct Hreg1 as (r0_ & r1_ & Hreg1).
    destruct Hreg2 as (r0_' & Hreg2).
    destruct Htrans as (Hdisj & Hnempty & Hlen).

    iDestruct ((gen_pagetable_SepM_split1 V0 (vmG := VMG) (σ := σ) (γ := own_gname) (λ pt, pt.1) is_owned) with "[Hown]") as "(Hownz & _)"; eauto.
    iAssert (∃ s, O@V0 :={1}[s] ∧ ⌜p1 ∈ s⌝)%I with "[Hownz]" as "Hownz".
    {
      rewrite owned_mapsto_eq /owned_mapsto_def //=.
      rewrite /get_pagetable_gset.
      unfold mem_inv in Hmeminv.
      destruct Hmeminv as [o Hmeminv].      
      iExists (list_to_set (map (λ p : PID * ownership, p.1) (map_to_list (filter (λ p : PID * ownership, is_owned p.2 = true) (get_vm_page_table σ V0).1)))).
      iSplit; first done.
      iPureIntro.
      rewrite elem_of_list_to_set.
      rewrite elem_of_list_In.
      rewrite in_map_iff.
      exists (p1, Owned).
      split; first done.
      rewrite <-elem_of_list_In.
      rewrite elem_of_map_to_list.
      apply map_filter_lookup_Some_2.
      destruct Hmeminv as [Hmeminv ->].
      destruct o; try done.
      by simpl.
    }
    iMod (inv_alloc invN ⊤ with "Hownz") as "#Hinv".    
    
    iModIntro.    

    iExists [True%I; ((R0 @@ V0 ->r run_I ∗ R1 @@ V0 ->r encode_vmid V1) ∗ VMProp V0 ((R0 @@ V0 ->r yield_I ∗ R1 @@ V0 ->r encode_vmid V1) ∗ VMProp V1 False%I (1/2)%Qp) (1/2)%Qp)%I].
    iSimpl.
    rewrite Hms.
    iSplit; first done.
    iSplitR "Hmem Hreg Haccess Hna".
    iFrame.
    do 2 (iSplit; first (by iPureIntro)).
    iPureIntro.
    apply Hlen.
    
    iIntros "(VMProp0 & VMProp1 & _)".
    rewrite Hφ.
    iSimpl.
    rewrite /scheduled /machine.scheduler //= /scheduler Hcur //=.
    
    (* use assumptions to extract resources *)
    (* for mem: sepM -> sepL2 *)

    iDestruct ((big_sepM_subseteq _ (get_reg_gmap σ) {[(PC, V0):= (of_pid p1); (R0, V0) := r0_;
                                 (R1,V0):= r1_ ; (PC,V1):= (of_pid p2); (R0,V1):= r0_' ]}) with "Hreg") as "Hreg";eauto.
    { rewrite /get_reg_gmap.
      apply map_subseteq_spec.
      intros i x H.
      rewrite /flat_map.
      simpl.
      apply elem_of_list_to_map_1'.
      intros y P.
      apply elem_of_list_In in P.
      rewrite ->!in_app_iff in P.
      destruct P as [P | [P | P]].
      - apply in_map_iff in P.
        destruct P as [[a b] [PEq P]].
        simpl in PEq.
        destruct i as [i1 i2].
        inversion PEq.
        subst.        
        clear PEq.
        rewrite <-elem_of_list_In in P.
        apply elem_of_map_to_list' in P.
        simpl in P.
        unfold get_vm_reg_file in *.
        apply Some_eq_inj.
        pose proof ((iffLR (map_subseteq_spec _ _)) Hreg1 i1 x) as HTemp1.
        rewrite <-P.        
        rewrite <-HTemp1.
        unfold V0.
        by simpl.
        rewrite <-H.
        destruct i1; simplify_map_eq /=.
        + by rewrite lookup_insert.
        + destruct n.
          unfold R0 in *.
          rewrite (@proof_irrel (0 < 31) (nat_lt_pi 0 31) machine_extra.R0_obligation_1 fin).
          rewrite (@proof_irrel (0 < 31) (nat_lt_pi 0 31) machine_extra.R0_obligation_1 fin) in H.
          unfold V0 in *.
          simplify_map_eq /=.
          rewrite lookup_insert_ne.
          by rewrite lookup_insert.
          discriminate.
          destruct n.
          unfold R1 in *.
          rewrite (@proof_irrel (1 < 31) (nat_lt_pi 1 31) machine_extra.R1_obligation_1 fin).
          rewrite (@proof_irrel (1 < 31) (nat_lt_pi 1 31) machine_extra.R1_obligation_1 fin) in H.
          unfold V0 in *.
          simplify_map_eq /=.
          rewrite lookup_insert_ne.
          rewrite lookup_insert_ne.
          by rewrite lookup_insert.
          discriminate.
          discriminate.
          simplify_map_eq /=.
      - apply in_map_iff in P.
        destruct P as [[a b] [PEq P]].
        simpl in PEq.
        destruct i as [i1 i2].
        inversion PEq.
        subst.        
        clear PEq.
        rewrite <-elem_of_list_In in P.
        apply elem_of_map_to_list' in P.
        simpl in P.
        unfold get_vm_reg_file in *.
        apply Some_eq_inj.
        pose proof ((iffLR (map_subseteq_spec _ _)) Hreg2 i1 x) as HTemp1.
        rewrite <-P.        
        rewrite <-HTemp1.
        unfold V1.
        by simpl.
        rewrite <-H.
        destruct i1; simplify_map_eq /=.
        + by rewrite lookup_insert.
        + destruct n.
          unfold R0 in *.
          rewrite (@proof_irrel (0 < 31) (nat_lt_pi 0 31) machine_extra.R0_obligation_1 fin).
          rewrite (@proof_irrel (0 < 31) (nat_lt_pi 0 31) machine_extra.R0_obligation_1 fin) in H.
          unfold V1 in *.
          simplify_map_eq /=.
          rewrite lookup_insert_ne.
          by rewrite lookup_insert.
          discriminate.
          destruct n.
          unfold R0 in H.
          inversion H.
          discriminate.
      - inversion P.
      - rewrite app_nil_r.
        apply elem_of_list_In.
        rewrite in_app_iff.
        rewrite !in_map_iff.
        destruct i as [ir iv].
        unfold VMID in iv.
        unfold vm_count in iv.
        cbn in iv.
        dependent destruction iv.
        + left.
          exists (ir, x).
          split; auto.
          rewrite <-elem_of_list_In.
          apply elem_of_map_to_list'.
          simpl.
          rewrite /get_vm_reg_file.
          destruct ir; simplify_map_eq /=.
          * unfold V0 in Hreg1.
            simpl in Hreg1.
            apply ((iffLR (map_subseteq_spec _ _)) Hreg1 PC p1).
            by rewrite lookup_insert.
          * destruct n.
            unfold R0 in *.
            simpl in *.
            rewrite (@proof_irrel (0 < 31) (nat_lt_pi 0 31) machine_extra.R0_obligation_1 fin) in H.
            rewrite (@proof_irrel (0 < 31) (nat_lt_pi 0 31) machine_extra.R0_obligation_1 fin) in Hreg1.
            unfold V0 in Hreg1.
            simpl in Hreg1.
            simplify_map_eq /=.
            apply ((iffLR (map_subseteq_spec _ _)) Hreg1 _ x).
            rewrite lookup_insert_ne.
            by rewrite lookup_insert.
            discriminate.
            destruct n.
            unfold R1 in *.
            simpl in *.
            rewrite (@proof_irrel (1 < 31) (nat_lt_pi 1 31) machine_extra.R1_obligation_1 fin) in H.
            rewrite (@proof_irrel (1 < 31) (nat_lt_pi 1 31) machine_extra.R1_obligation_1 fin) in Hreg1.
            unfold V0 in Hreg1.
            simpl in Hreg1.
            simplify_map_eq /=.
            apply ((iffLR (map_subseteq_spec _ _)) Hreg1 _ x).
            rewrite lookup_insert_ne.
            rewrite lookup_insert_ne.
            by rewrite lookup_insert.
            discriminate.
            discriminate.
            simplify_map_eq /=.
        + right.
          exists (ir, x).
          split.
          simpl.
          repeat f_equal.
          dependent destruction iv; auto.
          inversion iv.
          dependent destruction iv; auto.
          2 : { inversion iv. }
          rewrite <-elem_of_list_In.
          apply elem_of_map_to_list'.
          simpl.
          rewrite /get_vm_reg_file.
          destruct ir; simplify_map_eq /=.
          * unfold V1 in Hreg2.
            simpl in Hreg2.
            apply ((iffLR (map_subseteq_spec _ _)) Hreg2 PC p2).
            simplify_map_eq /=.
            by rewrite lookup_insert.
          * inversion H.
            simplify_eq.
            unfold R0 in *.
            simpl in *.
            rewrite (@proof_irrel (0 < 31) (nat_lt_pi 0 31) machine_extra.R0_obligation_1 fin) in H.
            rewrite (@proof_irrel (0 < 31) (nat_lt_pi 0 31) machine_extra.R0_obligation_1 fin) in Hreg2.
            unfold V1 in Hreg2.
            simpl in Hreg2.
            simplify_map_eq /=.
            apply ((iffLR (map_subseteq_spec _ _)) Hreg2 _ x).
            rewrite lookup_insert_ne.
            by rewrite lookup_insert.
            discriminate.
    }
    
    iDestruct ((gen_pagetable_SepM_split2 V0 V1 (vmG := VMG) (σ := σ) (γ := access_gname) (λ pt, pt.2) is_accessible) with "[Haccess]") as "(Haccessz & Haccessi & _)"; eauto.
    set (sacc1 := (get_pagetable_gset σ V0 (λ pt : page_table, pt.2) is_accessible)) in *.
    set (sacc2 := (get_pagetable_gset σ V1 (λ pt : page_table, pt.2) is_accessible)) in *.            
    
    rewrite !big_sepM_insert ?big_sepM_empty;eauto.
    rewrite reg_mapsto_eq /reg_mapsto_def.
    iDestruct "Hreg" as "(PCz & R0z & R1z & PCi & R0i & _)".
    2: { rewrite !lookup_insert_None; split;eauto. }
    2: { rewrite !lookup_insert_None; split;eauto. }
    2: { rewrite !lookup_insert_None; split;eauto. }
    2: { rewrite !lookup_insert_None; split;eauto. }

    iDestruct ((big_sepM_subseteq _ (get_mem σ) (mk_region p1 program1 ∪ mk_region p2 program2))
                 with "Hmem") as "Hmem"; eauto.
    rewrite /mem_layout in Hmem.
    by (destruct Hmem as (_ & _ & ?)).
    
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

    destruct Hmem as (Hacc1 & Hacc2 & Hmem).
    
    pose proof (@run_yield_1_spec _ _ VMG 1 1 p1 p2 sacc1 sacc2)
      as HSpec.
    
    iDestruct (HSpec with "[VMProp0 VMProp1 PCz PCi R0z R0i R1z Haccessz Haccessi Hprog1 Hprog2]") as "HWPs"; eauto.
    {
      rewrite /program1 //=.
      unfold seq_in_page. split. solve_finz. split. unfold Is_true. case_match;[done|solve_finz].
      split.
      pose proof (last_addr_in_bound p1).
      solve_finz.
      unfold Is_true. case_match;[done|solve_finz].
    }
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
    {
      rewrite /program2 //=.
      unfold seq_in_page. split. solve_finz. split. unfold Is_true. case_match;[done|solve_finz].
      split.
      pose proof (last_addr_in_bound p2).
      solve_finz.
      unfold Is_true. case_match;[done|solve_finz].
    }
    {
      apply elem_of_list_to_set.
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
    iSimpl.

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

    iSplitL "Hprog2".
    iApply (big_sepL2_alt with "[Hprog2]").
    iSplitR.
    rewrite finz_seq_length //.
    rewrite <- (@map_to_list_to_map Addr (gmap Addr) _  _  _  _ _ _ _ _ _ Word _).
    2: { rewrite fst_zip. apply finz_seq_NoDup'. pose proof (last_addr_in_bound p2). solve_finz.
       rewrite finz_seq_length //. }
    rewrite -(big_opM_map_to_list (λ a w,  (a ->a w)%I) _ ).
    rewrite  mem_mapsto_eq /mem_mapsto_def /mk_region.
    iFrame.

    set (x := (@rules_base.hyp_irisG vmconfig hypparams irisΣ VMG)).
    set (y := (IrisG (@hyp_machine vmconfig hypparams) irisΣ Hinv (@irisG_saved_prop irisΣ (iris_subG irisΣ (subG_refl irisΣ)))
                (@irisG_prop_name irisΣ (iris_subG irisΣ (subG_refl irisΣ))) (@irisG_name_map irisΣ (iris_subG irisΣ (subG_refl irisΣ))) name_map_name
                (@gen_vm_interp vmconfig irisΣ VMG))).
    cbn in x.
    cbn in y.

    rewrite reg_mapsto_eq /reg_mapsto_def.
    rewrite access_mapsto_eq /access_mapsto_def.
    rewrite /gen_access_name /gen_reg_name.
    cbn.
    iFrame.
    
    iSplitL "R0z".
    by iExists r0_.

    iSplitL "R1z".
    by iExists r1_.

    by iExists r0_'.
    }

    iSimpl.
    iDestruct "HWPs" as "(HWP1 & HWP2)".
    iFrame "HWP2".
    iIntros "_".
    iSpecialize ("HWP1" with "[//]").
    iApply (wp_mono with "HWP1").
    intros k.
    iStartProof.
    iIntros "[? _]".
    iFrame.    
  Qed.

  Definition is_final_config (σ: state) :=
                  ∃ (p1 : PID), (mem_inv σ p1).

  Definition is_initial_config' (σ: state) :=
    (get_current_vm σ) = V0 ∧    
    ∃ (p1 p2: PID), p1 ≠ p2 ∧
                    (mem_layout σ p1 p2) ∧
                    (mem_inv σ p1) ∧
                    (reg σ p1 p2) ∧
                    transactions σ.

  (* TODO: we need an invariant here *)
  Lemma run_yield_1_adequacy' (σ σ' : state) :
    (is_initial_config' σ) ->
    rtc machine.step ([ExecI; ExecI], σ) ([HaltI; ExecI], σ') →
    is_final_config σ'.
  Proof.
    intros Hinit.
    set (saved_props := (let (_, x, _, _) := iris_subG irisΣ (subG_refl irisΣ) in x)).
    set (prop_name := (let (_, _, x, _) := iris_subG irisΣ (subG_refl irisΣ) in x)).
    set (name_map := (let (_, _, _, x) := iris_subG irisΣ (subG_refl irisΣ) in x)).
    eapply (wp_invariance irisΣ); auto.
    destruct Hinit as (Hcur & (p1 & p2 & p1p2ne & Hmem & Hmeminv & Hreg & Htrans)).
    intro Hinv.
    iStartProof.
    iMod (gen_mem_alloc (get_mem σ)) as (mem_gname) "[Hσmem Hmem]".
    iMod (gen_reg_alloc (get_reg_gmap σ)) as (reg_gname) "[Hσreg Hreg]".
    iMod (gen_tx_alloc (get_tx_agree σ)) as (tx_gname) "[Hσtx _]".
    { apply get_txrx_auth_agree_valid. }
    iMod (gen_rx_agree_alloc (get_rx_agree σ)) as (rx_agree_gname) "[Hσrx_a _]".
    { apply get_txrx_auth_agree_valid. }
    iMod (gen_rx_option_alloc (get_rx_gmap σ)) as (rx_option_gname) "[Hσrx_o _]".
    iMod (gen_pagetable_alloc (get_owned_gmap σ)) as (own_gname) "[Hσown Hown]".
    iMod (gen_pagetable_alloc (get_access_gmap σ)) as (access_gname) "[Hσaccess Haccess]".
    iMod (gen_pagetable_alloc (get_excl_gmap σ)) as (excl_gname) "[Hσexcl _]".
    iMod (gen_trans_alloc (get_trans_gmap σ)) as (trans_gname) "[Hσtrans _]".
    iMod (gen_hpool_alloc (get_hpool_gset σ)) as (hpool_gname) "[Hσhpool _]".
    iMod (gen_retri_alloc (get_retri_gmap σ)) as (retri_gname) "[Hσretri _]".
    iMod (na_alloc) as (nainv_gname) "Hna".

    iModIntro.
    iIntros (name_map_name).
    pose ((GenVMG irisΣ vm_preG Hinv _ nainv_gname _ _ _ name_map_name mem_gname reg_gname tx_gname rx_agree_gname rx_option_gname own_gname access_gname excl_gname trans_gname hpool_gname retri_gname)) as VMG.
    iExists (gen_vm_interp (Σ := irisΣ)).

    iDestruct ((gen_pagetable_SepM_split1 V0 (vmG := VMG) (σ := σ) (γ := own_gname) (λ pt, pt.1) is_owned) with "[Hown]") as "(Hownz & _)"; eauto.
    iAssert (∃ s, O@V0 :={1}[s] ∧ ⌜p1 ∈ s⌝)%I with "[Hownz]" as "Hownz".
    {
      rewrite owned_mapsto_eq /owned_mapsto_def //=.
      rewrite /get_pagetable_gset.
      unfold mem_inv in Hmeminv.
      destruct Hmeminv as [o Hmeminv].      
      iExists (list_to_set (map (λ p : PID * ownership, p.1) (map_to_list (filter (λ p : PID * ownership, is_owned p.2 = true) (get_vm_page_table σ V0).1)))).
      iSplit; first done.
      iPureIntro.
      rewrite elem_of_list_to_set.
      rewrite elem_of_list_In.
      rewrite in_map_iff.
      exists (p1, Owned).
      split; first done.
      rewrite <-elem_of_list_In.
      rewrite elem_of_map_to_list.
      apply map_filter_lookup_Some_2.
      destruct Hmeminv as [Hmeminv ->].
      destruct o; try done.
      by simpl.
    }
    iMod (inv_alloc invN ⊤ with "Hownz") as "#Hinv".    
    
    iModIntro.

    iExists [True%I; ((R0 @@ V0 ->r run_I ∗ R1 @@ V0 ->r encode_vmid V1) ∗ VMProp V0 ((R0 @@ V0 ->r yield_I ∗ R1 @@ V0 ->r encode_vmid V1) ∗ VMProp V1 False%I (1/2)%Qp) (1/2)%Qp)%I].
    iSimpl.
    iSplit; first done.

    destruct Hreg as (Hreg1 & Hreg2).
    destruct Hreg1 as (r0_ & r1_ & Hreg1).
    destruct Hreg2 as (r0_' & Hreg2).
    destruct Htrans as (Hdisj & Hnempty & Hlen).

    iSplitR "Hmem Hreg Haccess Hna".
    iFrame.
    assert (vm_count = 2) as ->.
    unfold vm_count.
    unfold vmconfig.
    done.
    iSplit; first done.
    iSplit; first done.
    done.   
    
    iDestruct ((big_sepM_subseteq _ (get_reg_gmap σ) {[(PC, V0):= (of_pid p1); (R0, V0) := r0_;
                                 (R1,V0):= r1_ ; (PC,V1):= (of_pid p2); (R0,V1):= r0_' ]}) with "Hreg") as "Hreg";eauto.
    { rewrite /get_reg_gmap.
      apply map_subseteq_spec.
      intros i x H.
      rewrite /flat_map.
      simpl.
      apply elem_of_list_to_map_1'.
      intros y P.
      apply elem_of_list_In in P.
      rewrite ->!in_app_iff in P.
      destruct P as [P | [P | P]].
      - apply in_map_iff in P.
        destruct P as [[a b] [PEq P]].
        simpl in PEq.
        destruct i as [i1 i2].
        inversion PEq.
        subst.        
        clear PEq.
        rewrite <-elem_of_list_In in P.
        apply elem_of_map_to_list' in P.
        simpl in P.
        unfold get_vm_reg_file in *.
        apply Some_eq_inj.
        pose proof ((iffLR (map_subseteq_spec _ _)) Hreg1 i1 x) as HTemp1.
        rewrite <-P.        
        rewrite <-HTemp1.
        unfold V0.
        by simpl.
        rewrite <-H.
        destruct i1; simplify_map_eq /=.
        + by rewrite lookup_insert.
        + destruct n.
          unfold R0 in *.
          rewrite (@proof_irrel (0 < 31) (nat_lt_pi 0 31) machine_extra.R0_obligation_1 fin).
          rewrite (@proof_irrel (0 < 31) (nat_lt_pi 0 31) machine_extra.R0_obligation_1 fin) in H.
          unfold V0 in *.
          simplify_map_eq /=.
          rewrite lookup_insert_ne.
          by rewrite lookup_insert.
          discriminate.
          destruct n.
          unfold R1 in *.
          rewrite (@proof_irrel (1 < 31) (nat_lt_pi 1 31) machine_extra.R1_obligation_1 fin).
          rewrite (@proof_irrel (1 < 31) (nat_lt_pi 1 31) machine_extra.R1_obligation_1 fin) in H.
          unfold V0 in *.
          simplify_map_eq /=.
          rewrite lookup_insert_ne.
          rewrite lookup_insert_ne.
          by rewrite lookup_insert.
          discriminate.
          discriminate.
          simplify_map_eq /=.
      - apply in_map_iff in P.
        destruct P as [[a b] [PEq P]].
        simpl in PEq.
        destruct i as [i1 i2].
        inversion PEq.
        subst.        
        clear PEq.
        rewrite <-elem_of_list_In in P.
        apply elem_of_map_to_list' in P.
        simpl in P.
        unfold get_vm_reg_file in *.
        apply Some_eq_inj.
        pose proof ((iffLR (map_subseteq_spec _ _)) Hreg2 i1 x) as HTemp1.
        rewrite <-P.        
        rewrite <-HTemp1.
        unfold V1.
        by simpl.
        rewrite <-H.
        destruct i1; simplify_map_eq /=.
        + by rewrite lookup_insert.
        + destruct n.
          unfold R0 in *.
          rewrite (@proof_irrel (0 < 31) (nat_lt_pi 0 31) machine_extra.R0_obligation_1 fin).
          rewrite (@proof_irrel (0 < 31) (nat_lt_pi 0 31) machine_extra.R0_obligation_1 fin) in H.
          unfold V1 in *.
          simplify_map_eq /=.
          rewrite lookup_insert_ne.
          by rewrite lookup_insert.
          discriminate.
          destruct n.
          unfold R0 in H.
          inversion H.
          discriminate.
      - inversion P.
      - rewrite app_nil_r.
        apply elem_of_list_In.
        rewrite in_app_iff.
        rewrite !in_map_iff.
        destruct i as [ir iv].
        unfold VMID in iv.
        unfold vm_count in iv.
        cbn in iv.
        dependent destruction iv.
        + left.
          exists (ir, x).
          split; auto.
          rewrite <-elem_of_list_In.
          apply elem_of_map_to_list'.
          simpl.
          rewrite /get_vm_reg_file.
          destruct ir; simplify_map_eq /=.
          * unfold V0 in Hreg1.
            simpl in Hreg1.
            apply ((iffLR (map_subseteq_spec _ _)) Hreg1 PC p1).
            by rewrite lookup_insert.
          * destruct n.
            unfold R0 in *.
            simpl in *.
            rewrite (@proof_irrel (0 < 31) (nat_lt_pi 0 31) machine_extra.R0_obligation_1 fin) in H.
            rewrite (@proof_irrel (0 < 31) (nat_lt_pi 0 31) machine_extra.R0_obligation_1 fin) in Hreg1.
            unfold V0 in Hreg1.
            simpl in Hreg1.
            simplify_map_eq /=.
            apply ((iffLR (map_subseteq_spec _ _)) Hreg1 _ x).
            rewrite lookup_insert_ne.
            by rewrite lookup_insert.
            discriminate.
            destruct n.
            unfold R1 in *.
            simpl in *.
            rewrite (@proof_irrel (1 < 31) (nat_lt_pi 1 31) machine_extra.R1_obligation_1 fin) in H.
            rewrite (@proof_irrel (1 < 31) (nat_lt_pi 1 31) machine_extra.R1_obligation_1 fin) in Hreg1.
            unfold V0 in Hreg1.
            simpl in Hreg1.
            simplify_map_eq /=.
            apply ((iffLR (map_subseteq_spec _ _)) Hreg1 _ x).
            rewrite lookup_insert_ne.
            rewrite lookup_insert_ne.
            by rewrite lookup_insert.
            discriminate.
            discriminate.
            simplify_map_eq /=.
        + right.
          exists (ir, x).
          split.
          simpl.
          repeat f_equal.
          dependent destruction iv; auto.
          inversion iv.
          dependent destruction iv; auto.
          2 : { inversion iv. }
          rewrite <-elem_of_list_In.
          apply elem_of_map_to_list'.
          simpl.
          rewrite /get_vm_reg_file.
          destruct ir; simplify_map_eq /=.
          * unfold V1 in Hreg2.
            simpl in Hreg2.
            apply ((iffLR (map_subseteq_spec _ _)) Hreg2 PC p2).
            simplify_map_eq /=.
            by rewrite lookup_insert.
          * inversion H.
            simplify_eq.
            unfold R0 in *.
            simpl in *.
            rewrite (@proof_irrel (0 < 31) (nat_lt_pi 0 31) machine_extra.R0_obligation_1 fin) in H.
            rewrite (@proof_irrel (0 < 31) (nat_lt_pi 0 31) machine_extra.R0_obligation_1 fin) in Hreg2.
            unfold V1 in Hreg2.
            simpl in Hreg2.
            simplify_map_eq /=.
            apply ((iffLR (map_subseteq_spec _ _)) Hreg2 _ x).
            rewrite lookup_insert_ne.
            by rewrite lookup_insert.
            discriminate.
    }
    
    iDestruct ((gen_pagetable_SepM_split2 V0 V1 (vmG := VMG) (σ := σ) (γ := access_gname) (λ pt, pt.2) is_accessible) with "[Haccess]") as "(Haccessz & Haccessi & _)"; eauto.
    set (sacc1 := (get_pagetable_gset σ V0 (λ pt : page_table, pt.2) is_accessible)) in *.
    set (sacc2 := (get_pagetable_gset σ V1 (λ pt : page_table, pt.2) is_accessible)) in *.    

    rewrite !big_sepM_insert ?big_sepM_empty;eauto.
    rewrite reg_mapsto_eq /reg_mapsto_def.
    iDestruct "Hreg" as "(PCz & R0z & R1z & PCi & R0i & _)".
    2: { rewrite !lookup_insert_None; split;eauto. }
    2: { rewrite !lookup_insert_None; split;eauto. }
    2: { rewrite !lookup_insert_None; split;eauto. }
    2: { rewrite !lookup_insert_None; split;eauto. }

    iDestruct ((big_sepM_subseteq _ (get_mem σ) (mk_region p1 program1 ∪ mk_region p2 program2))
                 with "Hmem") as "Hmem"; eauto.
    rewrite /mem_layout in Hmem.
    by (destruct Hmem as (_ & _ & ?)).
    
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

    destruct Hmem as (Hacc1 & Hacc2 & Hmem).
    
    pose proof (@run_yield_1_spec _ _ VMG 1 1 p1 p2 sacc1 sacc2)
      as HSpec.

    set (x := (@rules_base.hyp_irisG vmconfig hypparams irisΣ VMG)).
    set (y := (IrisG (@hyp_machine vmconfig hypparams) irisΣ Hinv (@irisG_saved_prop irisΣ (iris_subG irisΣ (subG_refl irisΣ)))
                (@irisG_prop_name irisΣ (iris_subG irisΣ (subG_refl irisΣ))) (@irisG_name_map irisΣ (iris_subG irisΣ (subG_refl irisΣ))) name_map_name
                (@gen_vm_interp vmconfig irisΣ VMG))).
    cbn in x.
    cbn in y.

    iSplitL "PCz R0z R1z PCi R0i Haccessz Haccessi Hprog1 Hprog2".
    
    iIntros "(VMProp0 & VMProp1 & _)".
    rewrite /scheduled /machine.scheduler //= /scheduler Hcur //=.

    iDestruct (HSpec with "[VMProp0 VMProp1 PCz PCi R0z R0i R1z Haccessz Haccessi Hprog1 Hprog2]") as "HWPs"; eauto.
    {
      rewrite /program1 //=.
      unfold seq_in_page. split. solve_finz. split. unfold Is_true. case_match;[done|solve_finz].
      split.
      pose proof (last_addr_in_bound p1).
      solve_finz.
      unfold Is_true. case_match;[done|solve_finz].
    }
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
    {
      rewrite /program2 //=.
      unfold seq_in_page. split. solve_finz. split. unfold Is_true. case_match;[done|solve_finz].
      split.
      pose proof (last_addr_in_bound p2).
      solve_finz.
      unfold Is_true. case_match;[done|solve_finz].
    }
    {
      apply elem_of_list_to_set.
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
    iSimpl.

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

    iSplitL "Hprog2".
    iApply (big_sepL2_alt with "[Hprog2]").
    iSplitR.
    rewrite finz_seq_length //.
    rewrite <- (@map_to_list_to_map Addr (gmap Addr) _  _  _  _ _ _ _ _ _ Word _).
    2: { rewrite fst_zip. apply finz_seq_NoDup'. pose proof (last_addr_in_bound p2). solve_finz.
       rewrite finz_seq_length //. }
    rewrite -(big_opM_map_to_list (λ a w,  (a ->a w)%I) _ ).
    rewrite  mem_mapsto_eq /mem_mapsto_def /mk_region.
    iFrame.
    rewrite reg_mapsto_eq /reg_mapsto_def.
    rewrite access_mapsto_eq /access_mapsto_def.
    rewrite /gen_access_name /gen_reg_name.
    cbn.
    iFrame.
    
    iSplitL "R0z".
    by iExists r0_.

    iSplitL "R1z".
    by iExists r1_.

    by iExists r0_'.
    }

    iSimpl.
    iDestruct "HWPs" as "(HWP1 & HWP2)".
    iSplitL "HWP1".
    iSpecialize ("HWP1" with "[//]").
    iIntros "_".
    iApply (wp_mono with "HWP1").
    intros k.
    iStartProof.
    iIntros "[? _]".
    done.
    iSplit; last done.
    iIntros "Hprop".
    iSpecialize ("HWP2" with "Hprop").
    iApply (wp_mono with "HWP2").
    intros k.
    iStartProof.
    iIntros "_".
    done.

    iIntros "interp".

    unfold gen_vm_interp.
    iExists (⊤ ∖ ↑invN).
    iInv invN as ">Hx" "_".
    iModIntro.
    unfold is_final_config.
    unfold mem_inv.
    iDestruct "Hx" as "(%s & Hown & %Hin)".
    iDestruct "interp" as "(_ & _ & _ & _ & _ & _ & Hσ'own & _)".
    iDestruct (gen_own_valid_pure (σ := σ') with "Hσ'own Hown") as "%Hown".
    iPureIntro.
    exists p1, Owned.
    split; first done.
    rewrite /get_vm_page_table /get_page_tables.
    rewrite /get_owned_gmap /get_pagetable_gmap in Hown.
    apply elem_of_list_to_map_2 in Hown.
    rewrite ->elem_of_list_In in Hown.
    rewrite ->in_map_iff in Hown.
    destruct Hown as (x' & Heq & Hin').
    inversion Heq.
    subst.
    clear Heq.
    rewrite /get_pagetable_gset in Hin.
    rewrite ->elem_of_list_to_set in Hin.
    rewrite ->elem_of_list_In in Hin.
    rewrite ->in_map_iff in Hin.
    destruct Hin as ((x1 & x2) & Heq & Hin).
    simpl in Heq.
    subst.
    rewrite <-elem_of_list_In in Hin.
    rewrite ->elem_of_map_to_list in Hin.
    rewrite ->map_filter_lookup_Some in Hin.
    rewrite /get_vm_page_table in Hin.
    rewrite /get_page_tables in Hin.
    destruct Hin as [-> Hin].
    simpl in Hin.
    destruct x2; done.
  Qed.
  
End Adequacy.
