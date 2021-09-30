From machine_program_logic.program_logic Require Import weakestpre.
From iris.staging Require Import monotone.
From HypVeri.algebra Require Import base.
(* From HypVeri.rules Require Import rules_base. *)
(* From HypVeri.examples Require Import instr. *)
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
  | inv_sts_base_0_closed_unchanged_open ι: inv_sts_base (V0, ⊤, false) (V0, ⊤ ∖ ι, false)
  | inv_sts_base_0_unclosed_unchanged_switch ι: inv_sts_base (V0, ⊤ ∖ ι, false) (V1, ⊤, false)
  | inv_sts_base_1_closed_unchanged_change ι: inv_sts_base (V1, ⊤, false) (V1, ⊤ ∖ ι, true)
  | inv_sts_base_1_unclosed_changed_switch ι: inv_sts_base (V1, ⊤ ∖ ι, true) (V0, ⊤, true)
  | inv_sts_base_0_closed_changed_open ι: inv_sts_base (V0, ⊤, true) (V0, ⊤ ∖ ι, true).

  Definition inv_sts_rel := rtc inv_sts_base.

  Definition nainv_sts_state: Type :=  Word * Word * option handle.

  Inductive nainv_sts_base: relation nainv_sts_state :=
  | nainv_sts_base_init_run w0 w0' h: nainv_sts_base (w0, w0', None) (of_imm (encode_hvc_func Run), w0', Some h)
  | nainv_sts_base_lent_yield w0' h: nainv_sts_base (of_imm (encode_hvc_func Run), w0', Some h)
                                                    (of_imm (encode_hvc_func Run), of_imm (encode_hvc_func Yield), Some h)
  | nainv_sts_base_relinquished_reclaim h: nainv_sts_base (of_imm (encode_hvc_func Run), of_imm (encode_hvc_func Yield), Some h)
                                                          (of_imm (encode_hvc_func Run), of_imm (encode_hvc_func Yield), None).

  Definition nainv_sts_rel := rtc nainv_sts_base.



  (* CMRAs *)
  Class tokG Σ := tok_G :> inG Σ (exclR unitO).
  Class invStsG Σ := invSts_G :> inG Σ (authUR (mraUR inv_sts_rel)).
  Class nainvStsG Σ := nainvSts_G :> inG Σ (authUR (mraUR nainv_sts_rel)).

  Context `{gen_VMG Σ, tokG Σ, invStsG Σ, nainvStsG Σ}.

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


  (* Definition inv_def γ_invm := *)
  (*   (∃ (i : @VMID vmconfig) P b, <<i>>{ 1%Qp } ∗ nainv_closed P ∗ inv_state_exact γ_invm (i,P,b) )%I. *)

  (*     <<z>>{ 1%Qp } ∗ nainv_closed (⊤ ∖ ↑ι1) ∗ tokI γ1) *)
  (*     ∨ <<z>>{ 1%Qp } ∗ nainv_closed ⊤ ∗ tokI γ3 *)
  (*     ∨ <<i>>{ 1%Qp } ∗ nainv_closed ⊤ ∗ tokI γ1 ∗ tokI γ2 )%I. *)



End proof.
