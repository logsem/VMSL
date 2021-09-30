From machine_program_logic.program_logic Require Import weakestpre.
From iris.staging Require Import monotone.
From HypVeri.algebra Require Import base mem.
(* From HypVeri.rules Require Import rules_base. *)
From HypVeri.examples Require Import instr.
From HypVeri.lang Require Import lang_extra.
From HypVeri Require Import proofmode.


Section proof.

  Local Program Instance vmconfig : HypervisorConstants :=
    {vm_count := 2;
     vm_count_pos:= _}.
  Solve Obligations with lia.

  Program Definition V0 : VMID := (@nat_to_fin 0 _ _).
  Solve Obligations with rewrite /vmconfig /=; lia.

  Program Definition V1 : VMID := (@nat_to_fin 1 _ _).
  Solve Obligations with rewrite /vmconfig /=; lia.

  Context `{hypparams: !HypervisorParameters}.

  (* STSs *)

  (* the STS used in the invariant
     VMID is the VMID of the currently running VM
     coPoset is the set of names of na invariants that can be open
     bool indicates if the value in lent page has been changed
   *)
  Definition inv_sts_state: Type := VMID * coPset * bool.

  Inductive inv_sts_base: relation inv_sts_state :=
  | inv_sts_base_0_closed_unchanged_open ι: inv_sts_base (V0, ⊤, false) (V0, ⊤ ∖↑ ι, false)
  | inv_sts_base_0_unclosed_unchanged_switch ι: inv_sts_base (V0, ⊤ ∖↑ ι, false) (V1, ⊤, false)
  | inv_sts_base_1_closed_unchanged_change ι: inv_sts_base (V1, ⊤, false) (V1, ⊤ ∖↑ ι, true)
  | inv_sts_base_1_unclosed_changed_switch ι: inv_sts_base (V1, ⊤ ∖↑ ι, true) (V0, ⊤, true)
  | inv_sts_base_0_closed_changed_open ι: inv_sts_base (V0, ⊤, true) (V0, ⊤ ∖↑ ι, true).

  Definition inv_sts_rel := rtc inv_sts_base.

  (* the STS used in the non-atomic invariant
     bool indicates if the value in lent page has been changed
     option handle indicates whether a transaction has been invoked
   *)
  Definition nainv_sts_state: Type :=  bool * option handle.

  Inductive nainv_sts_base: relation nainv_sts_state :=
  | nainv_sts_base_init_run  h: nainv_sts_base (false, None) (false, Some h)
  | nainv_sts_base_lent_yield  h: nainv_sts_base (false, Some h)
                                                    (true, Some h)
  | nainv_sts_base_relinquished_reclaim h: nainv_sts_base (true, Some h)
                                                          (true, None).

  Definition nainv_sts_rel := rtc nainv_sts_base.

  (* CMRAs *)
  (* regular exclusive tokens *)
  Class tokG Σ := tok_G :> inG Σ (exclR unitO).
  (* monotone RA for the STS of the invariant *)
  Class invStsG Σ := invSts_G :> inG Σ (authUR (mraUR inv_sts_rel)).
  (* monotone RA for the STS of the non-atomic invariant *)
  Class nainvStsG Σ := nainvSts_G :> inG Σ (authUR (mraUR nainv_sts_rel)).

  Context `{!gen_VMG Σ, tokG Σ, invStsG Σ, nainvStsG Σ}.

  Definition inv_state_exact (γ: gname) (s: inv_sts_state):=
    own γ (● principal inv_sts_rel s).

  Definition inv_state_atleast (γ: gname) (s: inv_sts_state):=
    own γ (◯ principal inv_sts_rel s).

  Definition nainv_state_exact (γ: gname) (s: nainv_sts_state):=
    own γ (● principal nainv_sts_rel s).

  Definition nainv_state_atleast (γ: gname) (s: nainv_sts_state):=
    own γ (◯ principal nainv_sts_rel s).

  Lemma inv_state_alloc s: ⊢|==> ∃ γ, inv_state_exact γ s.
  Proof. iApply own_alloc; apply auth_auth_valid; done. Qed.

  Lemma inv_state_exact_atleast γ s s':
    inv_state_exact γ s -∗ inv_state_atleast γ s' -∗ ⌜inv_sts_rel s' s⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[Hincl ?]%auth_both_valid_discrete.
    revert Hincl; rewrite principal_included; done.
  Qed.

  Lemma inv_state_update γ s s' :
    inv_sts_rel s s' → inv_state_exact γ s ==∗ inv_state_exact γ s'.
  Proof.
    intros Hss.
    iApply own_update.
    eapply auth_update_auth.
    apply mra_local_update_grow; done.
  Qed.

  Lemma inv_state_observe γ s :
    inv_state_exact γ s ==∗ inv_state_exact γ s ∗ inv_state_atleast γ s.
  Proof.
    rewrite /inv_state_exact /inv_state_atleast -own_op.
    iApply own_update.
    eapply auth_update_alloc.
    apply mra_local_update_get_frag; done.
  Qed.

  Lemma nainv_state_alloc s: ⊢|==> ∃ γ, nainv_state_exact γ s.
  Proof. iApply own_alloc; apply auth_auth_valid; done. Qed.

  Lemma nainv_state_exact_atleast γ s s':
    nainv_state_exact γ s -∗ nainv_state_atleast γ s' -∗ ⌜nainv_sts_rel s' s⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[Hincl ?]%auth_both_valid_discrete.
    revert Hincl; rewrite principal_included; done.
  Qed.

  Lemma nainv_state_update γ s s' :
    nainv_sts_rel s s' → nainv_state_exact γ s ==∗ nainv_state_exact γ s'.
  Proof.
    intros Hss.
    iApply own_update.
    eapply auth_update_auth.
    apply mra_local_update_grow; done.
  Qed.

  Lemma nainv_state_observe γ s :
    nainv_state_exact γ s ==∗ nainv_state_exact γ s ∗ nainv_state_atleast γ s.
  Proof.
    rewrite /nainv_state_exact /nainv_state_atleast -own_op.
    iApply own_update.
    eapply auth_update_alloc.
    apply mra_local_update_get_frag; done.
  Qed.

  Definition token γ := own γ (Excl ()).

  Lemma token_alloc : ⊢|==> ∃ γ, token γ.
  Proof. iApply own_alloc; done. Qed.

  Lemma token_excl γ : token γ -∗ token γ -∗ False.
  Proof. iIntros "H1 H2"; iDestruct (own_valid_2 with "H1 H2") as %?; done. Qed.

  (* invariants *)
  Definition inv_name := nroot .@ "lending" .@ "inv".
  Definition nainv_name := nroot .@ "lending" .@ "na".

  Lemma namespace_disjoint: inv_name ## nainv_name.
  Proof.
    apply ndot_ne_disjoint.
    done.
  Qed.

  (* gnames of exclusive tokens that we will use:
     - γ_closed: VM1 owns it at the beginning.
                 If VM0 owns this token, we can open the non-atomic invariant.
     - γ_switch: VM1 owns it at the beginning, indicating we just switched to VM1.
                 if VM1 has it, we can open the non-atomic invariant.
     - γ_unchanged: VM0 will lose it after VM1 changes the value of the page.
     - γ_done: VM1 owns it at the beginning and will lose it when it halts.
     - γ_access: VM0 will lose it when switching to VM1.
   *)

  Definition inv_def γ_invm γ_nainvm γ_closed γ_access γ_done γ_unchanged γ_switched ι : iProp Σ:=
    ∃ (i : VMID) P b, <<i>>{ 1%Qp } ∗ nainv_closed P ∗ inv_state_exact γ_invm (i,P,b) ∗
    (if b then True else token γ_unchanged) ∗
    (match (fin_to_nat i,b) with
    | (0, false) => (⌜P = ⊤⌝ → token γ_access ∗ nainv_state_atleast γ_nainvm (b, None)) ∗
                    (⌜P = ⊤ ∖↑ ι⌝ → token γ_closed)
    | (0, true) =>  (⌜P = ⊤⌝ → token γ_done ∗
                    ∃ h, nainv_state_atleast γ_nainvm (b, Some h)) ∗
                    (⌜P = ⊤ ∖↑ ι⌝ → token γ_closed ∗ token γ_access)
    | (1, false) => (⌜P = ⊤⌝ → token γ_done ∗
                    ∃ h, nainv_state_atleast γ_nainvm (b, Some h))
    | (1, true) =>  (⌜P = ⊤ ∖ ↑ι⌝ → token γ_switched)
    | _ => True
    end).

  Definition nainv_def γ_nainvm γ_access γ_done γ_unchanged γ_switched prx1 (page: PID): iProp Σ:=
    ∃ r0 r0' r1 w des b o, nainv_state_exact γ_nainvm (b,o) ∗
    R0 @@ V0 ->r r0 ∗ R0 @@ V1 ->r r0' ∗ R1 @@ V0 ->r r1 ∗ page ->a w ∗ mem_region des prx1 ∗
    (if b then ⌜w = W1⌝ ∗ token γ_unchanged ∗ RX@V1 :=() else ⌜w = W0⌝ ) ∗
    (match o with
     | None => True
     | Some h => h ->re false ∗ h ->t{1}(V0, W0, V1, [page], Lending)
     end) ∗
    (match (b,o) with
    | (false, None) => RX@V1 :=()
    | (false, Some h) => ⌜r0 = of_imm run_I⌝ ∗ ⌜r1 = W1⌝ ∗
                         token γ_access ∗
                         ∃ wl, RX@V1 :=(wl, V0) ∗
                         ⌜des = serialized_transaction_descriptor V0 V1 h I1 [page] W0⌝ ∗
                         ⌜finz.to_z wl =Z.of_nat (length des)⌝
    | (true, Some h) => ⌜r0 = of_imm run_I⌝ ∗ ⌜r0' = of_imm yield_I⌝ ∗ ⌜r1 = W1⌝ ∗
                        token γ_switched ∗ token γ_access
    | (true, None) => ⌜r0 = of_imm run_I⌝ ∗ ⌜r0' = of_imm yield_I⌝ ∗ ⌜r1 = W1⌝ ∗
                      token γ_done

    end).

End proof.
