From machine_program_logic.program_logic Require Import weakestpre.
From iris.staging Require Import monotone.
From HypVeri.algebra Require Import base.
(* From HypVeri.rules Require Import rules_base. *)
From HypVeri.examples Require Import instr.
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
  Definition inv_sts_state: Type := VMID * coPset * bool.

  Inductive inv_sts_base: relation inv_sts_state :=
  | inv_sts_base_0_closed_unchanged_open ι: inv_sts_base (V0, ⊤, false) (V0, ⊤ ∖↑ ι, false)
  | inv_sts_base_0_unclosed_unchanged_switch ι: inv_sts_base (V0, ⊤ ∖↑ ι, false) (V1, ⊤, false)
  | inv_sts_base_1_closed_unchanged_change ι: inv_sts_base (V1, ⊤, false) (V1, ⊤ ∖↑ ι, true)
  | inv_sts_base_1_unclosed_changed_switch ι: inv_sts_base (V1, ⊤ ∖↑ ι, true) (V0, ⊤, true)
  | inv_sts_base_0_closed_changed_open ι: inv_sts_base (V0, ⊤, true) (V0, ⊤ ∖↑ ι, true).

  Definition inv_sts_rel := rtc inv_sts_base.

  Definition nainv_sts_state: Type :=  Word * Word * option handle.

  Inductive nainv_sts_base: relation nainv_sts_state :=
  | nainv_sts_base_init_run w0 w0' h: nainv_sts_base (w0, w0', None) (of_imm run_I, w0', Some h)
  | nainv_sts_base_lent_yield w0' h: nainv_sts_base (of_imm run_I, w0', Some h)
                                                    (of_imm run_I, of_imm yield_I, Some h)
  | nainv_sts_base_relinquished_reclaim h: nainv_sts_base (of_imm run_I, of_imm yield_I, Some h)
                                                          (of_imm run_I, of_imm yield_I, None).

  Definition nainv_sts_rel := rtc nainv_sts_base.



  (* CMRAs *)
  Class tokG Σ := tok_G :> inG Σ (exclR unitO).
  Class invStsG Σ := invSts_G :> inG Σ (authUR (mraUR inv_sts_rel)).
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

  Definition inv_def γ_invm γ_nainvm γ_closed γ_access γ_done γ_unchanged γ_switched ι : iProp Σ:=
    ∃ (i : VMID) P b, <<i>>{ 1%Qp } ∗ nainv_closed P ∗ inv_state_exact γ_invm (i,P,b) ∗
    (match (fin_to_nat i,b) with
    | (0, false) => (⌜P = ⊤⌝ → token γ_access ∗ ∃ w0 w0', nainv_state_atleast γ_nainvm (w0,w0', None))
                      ∗ (⌜P = ⊤ ∖↑ ι⌝ → token γ_closed)
    | (0, true) =>  (⌜P = ⊤⌝ → token γ_done
                          ∗ ∃w0' h, nainv_state_atleast γ_nainvm (of_imm run_I, w0', Some h))
                      ∗ (⌜P = ⊤ ∖↑ ι⌝ → token γ_closed ∗ token γ_access)
    | (1, false) => (⌜P = ⊤⌝ → token γ_done ∗ token γ_unchanged
                    ∗ ∃ h, nainv_state_atleast γ_nainvm (of_imm run_I, of_imm yield_I, Some h))
    | (1, true) =>  (⌜P = ⊤ ∖ ↑ι⌝ → token γ_switched
                     ∗ nainv_state_atleast γ_nainvm (of_imm run_I, of_imm yield_I, None))
    | _ => True
    end).

  Definition nainv_def γ_nainvm γ_access γ_done γ_unchanged γ_switched: iProp Σ:=
    ∃ r0 r0' o, nainv_state_exact γ_nainvm (r0,r0',o) ∗ R0 @@ V0 ->r r0 ∗ R0 @@ V1 ->r r0' ∗
    (match o with
    | None => ⌜r0 = of_imm run_I⌝ → ⌜r0' = of_imm yield_I⌝ → token γ_unchanged ∗ token γ_done
    | Some h => (⌜r0' = of_imm yield_I ⌝ → token γ_switched ∗ token γ_unchanged ) ∗ token γ_access
    end).

End proof.
