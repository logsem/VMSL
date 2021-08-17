From machine_program_logic.program_logic Require Import machine weakestpre adequacy.
From HypVeri Require Import reg_addr RAs lifting.
From HypVeri.examples Require Import run_yield_1.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Import invariants na_invariants.
From iris.bi Require Import big_op.

Section Adequacy.
  Context (Σ: gFunctors).
  Context {inv_preG : invGS Σ}.
  Context {nainv_preG : na_invG Σ}.
  Context {vm_preG: gen_VMPreG Addr VMID Word reg_name PID transaction_type Σ}.
  Context {tokG: tokG Σ}.

  (* exec_mode of all VMs *)
  Definition run_vms (ms: list exec_mode) (z i: VMID):=
    ms !! (fin_to_nat i) = Some ExecI ∧
    ms !! (fin_to_nat z) = Some ExecI ∧
    ∀ v , (v ≠ (fin_to_nat z) ∧ v ≠ (fin_to_nat i) -> ms !! v = Some HaltI).

  Definition mk_region (p:PID) (ws: list Word) : gmap Addr Word:=
    (list_to_map (zip (finz.seq (of_pid p) (length ws)) ws)).

  Definition mem_layout (σ :state) (z i: VMID) (p1 p2: PID) :=
      (∃ a, is_accessible a= true ∧ (get_vm_page_table σ z).2 !! p1 = Some a) ∧
      (∃ a, is_accessible a= true ∧ (get_vm_page_table σ i).2 !! p2 = Some a) ∧
      (mk_region p1 (program1 i)) ∪ (mk_region p2 program2) ⊆ (get_mem σ).

  Definition reg (σ: state) (z i: VMID) (p1 p2: PID):=
    (∃ r0 r1 ,{[PC := (of_pid p1); R0 := r0; R1 := r1]} ⊆ (get_reg_files σ)!!!z) ∧
    ∃ r0 ,{[PC := (of_pid p2); R0 := r0]} ⊆ (get_reg_files σ) !!! i .

  Definition transactions (σ: state):=
    (dom (gset handle) (get_transactions σ).1) ## ((get_transactions σ).2) ∧
    (get_transactions σ).2 ≠ ∅.

  Definition is_initial_config (σ: state) (ms: list exec_mode):=
    ∃ (z i:VMID), (fin_to_nat z) = 0 ∧ z ≠ i ∧
                  (get_current_vm σ) = z ∧
    ∃ (p1 p2: PID), p1 ≠ p2 ∧
                  (run_vms ms z i) ∧
                  (mem_layout σ z i p1 p2) ∧
                  (reg σ z i p1 p2) ∧
                  transactions σ.

  (*TODO: prove these two *)
      (* seq_in_page (of_pid p1) (length (program1 i)) p1 -> *)
      (* seq_in_page (of_pid p2) (length program2) p2 *)

  Lemma run_yield_1_adequacy' (σ σ': state)  (ms ms': list exec_mode):
    (* we need assumptions to be able to allocate resources *)
    (* with these resources, we apply the specification and get the wptp *)
    (* along with some other stuff, then it should be enough to apply the adequacy theorem *)
    (is_initial_config σ ms) ->
    rtc machine.step (ms, σ) (ms', σ') →
    (* φ : vm 0 is scheduled but halted *)
    ((* scheduled σ' z ∧ *)  ms' !! 0 = Some HaltI).
  Proof.
    intros Hinit Hstep.
    pose proof (wp_invariance Σ hyp_machine ms σ ms' σ') as WPI;cbn in WPI.
    apply WPI. 2: assumption.
    clear WPI.
    intro Hinv.

    destruct Hinit as ( z & i & Heqz & Hneq & Hcur & Hinit).
    iMod (@na_alloc Σ nainv_preG) as (nainv_gname) "Hna".
    iMod (@gen_token_alloc Σ vm_preG z) as (token_gname) "[Hσtok Htok]".
    iMod (@gen_mem_alloc Σ vm_preG (get_mem σ)) as (mem_gname) "[Hσmem Hmem]".
    iMod (@gen_reg_alloc Σ vm_preG (get_reg_gmap σ)) as (reg_gname) "[Hσreg Hreg]".
    iMod (gen_tx_alloc (get_tx_agree σ)) as (tx_gname) "[Hσtx _]".
    { apply get_txrx_auth_agree_valid. }
    iMod (gen_rx_agree_alloc (get_rx_agree σ)) as (rx_agree_gname) "[Hσrx_a _]".
    { apply get_txrx_auth_agree_valid. }
    iMod (gen_rx_option_alloc (get_rx_gmap σ)) as (rx_option_gname) "[Hσrx_o _]".
    iMod (gen_pagetable_alloc (get_owned_gmap σ)) as (own_gname) "[Hσown _]".
    iMod (@gen_pagetable_alloc Σ vm_preG (get_access_gmap σ)) as (access_gname) "[Hσaccess Haccess]".
    iMod (gen_pagetable_alloc (get_excl_gmap σ)) as (excl_gname) "[Hσexcl _]".
    iMod (gen_trans_alloc (get_trans_gmap σ)) as (trans_gname) "[Hσtrans _]".
    iMod (gen_hpool_alloc (get_hpool_gset σ)) as (hpool_gname) "[Hσhpool _]".
    iMod (gen_retri_alloc (get_retri_gmap σ)) as (retri_gname) "[Hσretri _]".
    pose vmG := GenVMG Σ vm_preG inv_preG nainv_preG nainv_gname token_gname mem_gname reg_gname tx_gname
    rx_agree_gname rx_option_gname own_gname access_gname excl_gname trans_gname hpool_gname retri_gname.

    destruct Hinit as (p1 & p2 & Hpne & Hms & Hmem & Hreg & Htrans ).
    destruct Hreg as (Hreg1 & Hreg2).
    destruct Hreg1 as (r0_ & r1_ & Hreg1).
    destruct Hreg2 as (r0_'  & Hreg2).
    assert (HseqIn1: seq_in_page p1 (length (program1 i)) p1).
    {
      rewrite /seq_in_page.
      split.
      rewrite Z.leb_refl //.
      split.
      cbn.
      pose proof (last_addr_in_bound p1).
      solve_finz.
      cbn.
      destruct (((p1 ^+ 4%nat)%f <=? (p1 ^+ (1000 - 1))%f)%Z) eqn:Heqn.
      done.
      exfalso.
      apply Z.leb_nle in Heqn.
      solve_finz.
    }
    assert (HseqIn2: seq_in_page p2 (length program2) p2).
    {
      rewrite /seq_in_page.
      split.
      rewrite Z.leb_refl //.
      split.
      cbn.
      pose proof (last_addr_in_bound p2).
      solve_finz.
      cbn.
      destruct (((p2 ^+ 2%nat)%f <=? (p2 ^+ (1000 - 1))%f)%Z) eqn:Heqn.
      done.
      exfalso.
      apply Z.leb_nle in Heqn.
      solve_finz.
    }
    pose proof (@run_yield_1_spec Σ vmG tokG nroot z i 1 1 p1 p2 r0_ r1_ r0_' Heqz  Hneq Hpne
               HseqIn1 HseqIn2) as HSpec.
    iExists gen_vm_interp.
    rewrite /gen_vm_interp.
    cbn.
    rewrite Hcur.
    iFrame.
    destruct Htrans as (Hdisj & Hnempty).
    iSplitR.
    iModIntro.
    done.

    (* use assumptions to extract resources *)
    (* for mem: sepM -> sepL2 *)

    iDestruct (HSpec with "[Hmem Htok Hreg Haccess Hna]") as "HWPs".
    iFrame.

    iDestruct ((big_sepM_subseteq _ (get_reg_gmap σ) {[(PC, z):= (of_pid p1); (R0, z) := r0_;
                                 (R1,z):= r1_ ; (PC,i):= (of_pid p2); (R0,i):=r0_' ]}) with "Hreg" ) as "Hreg";eauto.
    { admit. }
    rewrite !big_sepM_insert ?big_sepM_empty;eauto.
    rewrite reg_mapsto_eq /reg_mapsto_def.
    iDestruct "Hreg" as "(PCz & R0z & R1z & PCi & R0i & _)".
    iFrame.
    rewrite token_agree_eq /token_agree_def.
    iFrame.
    destruct Hmem as (Hacc1 & Hacc2 & Hmem).
    iDestruct ((big_sepM_subseteq _ (get_access_gmap σ)
                (<[z := (get_vm_page_table σ z).2]>({[i := (get_vm_page_table σ i).2]} : (gmap VMID _)))) with "Haccess" ) as "Haccess";eauto.
    { admit. }
    (* iDestruct "Haccess" as "[H1 H2]". *)
    assert ({[z := (get_vm_page_table σ z).2 ;
                                         i := (get_vm_page_table σ i).2 ]}
            = <[z := (get_vm_page_table σ z).2]>({[i := (get_vm_page_table σ i).2]} : (gmap VMID _))).
    done.
    rewrite H.
    iDestruct ((big_sepM_insert (λ k x,ghost_map.ghost_map_elem access_gname k (dfrac.DfracOwn 1) x) {[i := (get_vm_page_table σ i).2]} z (get_vm_page_table σ z).2)  with "[Haccess]")
    as "H1".
    {admit. }
    iDestruct "Haccess" as "[H1 H2]".
      in "Haccess". ?big_sepM_empty;eauto.



    
    (* [∗ list] WP -> WP @z ∗ WP @i *)
    rewrite /run_vms in Hms.
    iAssert
      (WP ExecI @ z {{ _, True }} ∗ WP ExecI @ i {{ _, True }} -∗ ([∗ list] id↦e ∈ ms, WP e @ id {{ _, True }}))%I as "Hwpimp".
    { iIntros "[Hz Hi]".
      destruct Hms as (Hi& Hz & Hrest).
      destruct ms.
      done.
      rewrite Heqz /= in Hz.
      cbn.
      inversion Hz;subst e.
      rewrite Heqz.
      iFrame.
      iInduction ms as  [m | m] "IH".
      - done.
      - destruct (decide ((fin_to_nat i) = 1)).
        cbn.
        rewrite e // in Hi.
        simplify_list_eq.
        rewrite e.
        iFrame.
        iClear "IH".
        iInduction ms as  [m | m] "IH".
        + done.
        + cbn.
          assert (m= HaltI).
          assert (2 ≠ fin_to_nat (get_current_vm σ) ∧ 2 ≠ (fin_to_nat i)).
          rewrite Heqz;lia.
          pose proof (Hrest 2 H).
          cbn in H0.
          inversion H0;done.
          rewrite H.
          iSplitL.
          iApply wp_terminated';eauto.
          (* cannot apply induction hypothesis *)
          admit.
        + cbn.
          assert (1 ≠ fin_to_nat z ∧ 1 ≠ (fin_to_nat i)).
          rewrite Heqz;lia.
          pose proof (Hrest 1 H).
          cbn in H0.
          inversion H0.
          iSplitR.
          iApply wp_terminated';eauto.
          admit.
    }
    iSplitL.
    (* iApply "Hwpimp". *)
    (* cannot apply it *)


    (* instantiate spec with resources and obtain a WP *)

    (* apply adequacy theorem *)
  Admitted.

End Adequacy.
