From iris.bi Require Import derived_laws_later.
From machine_program_logic.program_logic Require Import weakestpre.
From iris.staging Require Import monotone.
From HypVeri.algebra Require Import base mem.
From HypVeri.rules Require Import rules_base mov str mem_send_nz send run yield ldr reclaim halt add sub nop cmp bne retrieve relinquish_nz poll.
From HypVeri.examples Require Import instr.
From HypVeri.lang Require Import lang_extra.
From HypVeri Require Import proofmode.
From HypVeri.examples Require Import instr loop_macro.
Require Import Setoid.

Section proof.

  Local Program Instance vmconfig : HypervisorConstants :=
    {vm_count := 2;
     vm_count_pos:= _}.

  Program Definition V0 : VMID := (@nat_to_fin 0 _ _).

  Program Definition V1 : VMID := (@nat_to_fin 1 _ _).

  Context `{hypparams: !HypervisorParameters}.

  (** programs **)

  (* the program of VM0
    ipage is the PID of the page to lend
    l is the length of the descriptor/message,
    NOTE: we assume the descriptor is already written to the TX page, and R3 -> ptx+2*)
  Definition code0 (ipage : Imm) (l : Imm)  : list Word :=
    encode_instructions
    [
    (* store the page address to R1 *)
    (* tx -> memory descriptor *des* *)
    (* R3 -> address of a handle in *des* *)
    Mov R1 (inl ipage);
    (* store the initial value to R0 *)
    (* tx -> memory descriptor *des* *)
    (* R3 -> address of a handle in *des* *)
    (* R1 -> p *)
    Mov R0 (inl I0);
    (* write v to p *)
    (* tx -> memory descriptor *des* *)
    (* R3 -> address of a handle in *des* *)
    (* R1 -> p *)
    (* R0 -> v *)
    Str R0 R1;
    (* tx is populated with memory descriptor *)
    (* lend initiation *)
    (* tx -> memory descriptor *des* *)
    (* R3 -> address of a handle in *des* *)
    (* R1 -> p *)
    (* R0 -> v  *)
    (* p -> 0 *)
    Mov R0 (inl (encode_hvc_func Lend));
    (* tx -> memory descriptor *des* *)
    (* R3 -> address of a handle in *des* *)
    (* R1 -> p *)
    (* R0 -> Lend  *)
    (* p -> 0 *)
    Mov R1 (inl I6); (* populate the length of the descriptor to R1 *)
    Hvc;
    (* R3 is populated with address of handle in the memory descriptor *)
    (* Lend returns a new handle in R2 *)
    (* write h to memory descriptor *)
    (* tx -> memory descriptor *des* *)
    (* R3 -> address of a handle in *des* *)
    (* R1 -> p *)
    (* R0 -> Succ *)
    (* p -> 0 *)
    (* R2 -> h *)
    (* h ->  transaction entry *)
    Str R2 R3;
    Mov R3 (inr R2);
    (* send tx to VM1 *)
    (* tx -> memory descriptor *des* with h *)
    (* R3 -> address of a handle in *des* *)
    (* R1 -> p *)
    (* R0 -> Succ *)
    (* p -> 0 *)
    (* R2 -> h *)
    (* h ->  transaction entry *)
    Mov R0 (inl (encode_hvc_func Send));
    Mov R1 (inl (encode_vmid V1));
    Mov R2 (inl l);
    Hvc;
    (* run VM1 *)
    (* tx -> memory descriptor *des* with h *)
    (* R3 -> address of a handle in *des* *)
    (* R1 -> 1 *)
    (* R0 -> Succ *)
    (* p -> 0 *)
    (* R2 -> l *)
    (* h ->  transaction entry *)
    Mov R0 (inl run_I);
    Hvc;
    (* store the handle to R1 *)
    (* tx -> memory descriptor *des* with h *)
    (* R3 -> address of a handle in *des* *)
    (* R1 -> 1 *)
    (* R0 -> Run *)
    (* p -> 1 *)
    (* R2 -> l *)
    (* h -> transaction entry *)
    Mov R1 (inr R3);
    (* reclaim *)
    Mov R0 (inl (encode_hvc_func Reclaim));
    Hvc;
    (* load the first word from the page to R1 *)
    (* tx -> memory descriptor *des* with h *)
    (* R3 -> address of a handle in *des* *)
    (* R1 -> h *)
    (* R0 -> Succ *)
    (* p -> 1 *)
    (* R2 -> l *)
    Mov R1 (inl ipage);
    Ldr R0 R1;
    (* stop *)
    (* tx -> memory descriptor *des* with h *)
    (* R3 -> address of a handle in *des* *)
    (* R1 -> p *)
    (* R0 -> v' *)
    (* p -> 1 *)
    (* R2 -> l *)
    Halt
    ].

  (** STSs **)
  (* the STS used in the invariant
     VMID is the VMID of the currently running VM
     coPoset is the set of names of na invariants that can be open
     bool indicates if the value in lent page has been changed
   *)

  Section sts.

  Definition inv_sts_state: Type := VMID * bool * bool * option handle.

  Inductive inv_sts_base : relation inv_sts_state :=
  | inv_sts_base_0_closed_unchanged_open : inv_sts_base (V0, false ,false, None) (V0, true, false, None)
  | inv_sts_base_0_unclosed_unchanged_switch h: inv_sts_base (V0, true, false, None) (V1, false, false, Some h)
  | inv_sts_base_1_closed_unchanged_open h: inv_sts_base (V1, false, false, Some h) (V1, true, true, Some h)
  | inv_sts_base_1_unclosed_unchanged_modify h: inv_sts_base (V1, true, true, Some h) (V0, false, true, Some h)
  | inv_sts_base_0_closed_changed_open h: inv_sts_base (V0, false, true, Some h) (V0, true, true, None)
  | inv_sts_base_0_uclosed_changed_close : inv_sts_base (V0, true, true, None) (V0, false, true, None).

  Definition inv_sts_rel := rtc inv_sts_base.

  Lemma inv_sts_0_changed h a b oh : inv_sts_rel (V0, false, false, h) (V1, a, b, oh) ->
    h = None /\ ∃ h', oh = Some h'.
  Proof.
    intros H.
    rewrite /inv_sts_rel in H.
    apply rtc_inv in H.
    destruct H as [|H].
    - discriminate.
    - destruct H as [x [H1 H2]].
      inversion H1; auto.
      simplify_eq.
      apply rtc_inv in H2.
      destruct H2 as [|H2].
      + discriminate.
      + destruct H2 as [x [H3 H4]].
        inversion H3; auto.
        simplify_eq.
        apply rtc_inv in H4.
        destruct H4 as [|H4].
        * inversion H.
          split; auto.
          by exists h.
        * destruct H4 as [x [H5 H6]].
          inversion H5; auto.
          simplify_eq.
          apply rtc_inv in H6.
          destruct H6 as [|H6].
          -- simplify_eq.
             eauto.
          -- destruct H6 as [x [H7 H8]].
             inversion H7; auto.
             simplify_eq.
             apply rtc_inv in H8.
             destruct H8 as [|H8].
             ++ simplify_eq.
             ++ destruct H8 as [x [H9 H10]].
                inversion H9; auto.
                simplify_eq.
                apply rtc_inv in H10.
                destruct H10 as [|H10].
                ** discriminate.
                ** destruct H10 as [x [H11 H12]].
                   inversion H11; auto.
                   simplify_eq.
                   apply rtc_inv in H12.
                   destruct H12 as [|H12].
                   --- discriminate.
                   --- destruct H12 as [x [H13 H14]].
                       inversion H13; auto.
  Qed.
      
  Lemma inv_sts_0_closed_unchanged_open s : inv_sts_rel (V0, false, false, None) s ->
    (s.1.1.1= V0 ∧ ((s.1.2 = false ∧ s.2 = None) ∨ (s.1.2 = true))) ∨
    (s.1.1.1 = V1 ∧ ((s.1.1.2 = false ∧ s.1.2 = false) ∨ (s.1.1.2 = true ∧ s.1.2 = true))) .
  Proof.
    intro.
    pattern s.
    eapply (rtc_ind_r _ (V0,false,false,None)).
    - left;eauto.
    - intros.
      Unshelve.
      2: { exact inv_sts_base. }
      destruct H2.
      destruct y as [ []];simpl in *;inversion H1;subst;cbn;eauto.
      destruct H2.
      simpl in H2.
      destruct H3;
        destruct y as [ []];simpl in *; inversion H1; subst;cbn; eauto.
    - done.
  Qed.

  Lemma inv_sts_0_unclosed_unchanged_switch s:
    inv_sts_rel (V0, true , false, None) s ->
    (s.1.1.1= V0 ∧ ((s.1.1.2 = true ∧ s.1.2 = false ∧ s.2 = None) ∨ (s.1.1.2 = false ∧ s.1.2 = true) ∨ (s.1.1.2 = true ∧ s.1.2 = true ∧ s.2 = None) ∨ (s.1.1.2 = false ∧ s.1.2 = true ∧ s.2 = None))) ∨
    (s.1.1.1 = V1 ∧ ((s.1.1.2 = false ∧ s.1.2 = false) ∨ (s.1.1.2 = true ∧ s.1.2 = true))).
  Proof.
    intro.
    pattern s.
    eapply (rtc_ind_r _ (V0,true,false,None )).
    - left. split.
      done.
      left; done.
    - intros.
      Unshelve.
      2: { exact inv_sts_base. }
      destruct y as [[[]] []];
        simpl in *.
      destruct H2.
      destruct H2 as [-> H2].
      + destruct H2.
        destruct H2 as [-> [-> ?]]; discriminate.
        destruct H2.
        * destruct H2 as [-> ->].
          inversion H1; subst; cbn; eauto.
          left.
          split; auto.
          right.
          right.
          left.
          auto.
        * destruct H2.
          -- destruct H2 as [-> [-> ?]]; discriminate.
          -- destruct H2 as [-> [-> ?]]; discriminate.
      + destruct H2 as [-> [|]].
        * destruct H2 as [-> ->].
          inversion H1; subst; cbn; eauto.
        * destruct H2.
          -- inversion H1; subst; cbn; eauto.
             left.
             auto.
      + destruct H2.
        * destruct H2 as [-> ?].
          destruct H2.
          -- destruct H2 as [-> [-> _]].
             inversion H1; subst; cbn; eauto.
          -- destruct H2.
             destruct H2 as [-> ->].
             ++ inversion H1; subst; cbn; eauto.
             ++ destruct H2.
                ** destruct H2 as [-> [-> _]].
                   inversion H1; subst; cbn; eauto.
                   left.
                   split; auto.
                ** destruct H2 as [-> [-> _]].
                   inversion H1; subst; cbn; eauto.
        * destruct H2 as [-> H2].
          destruct H2.
          -- destruct H2 as [-> ->].
             inversion H1; subst; cbn; eauto.
          -- destruct H2.
             ++ destruct H2 as [-> ->].
                inversion H1; subst; cbn; eauto.
    - done.
  Qed.

  Lemma inv_sts_0_closed_changed_yield h s:
    inv_sts_rel (V1, false , false, Some h) s ->
    (s.1.1.1 = V0 ∧ s.1.2 = true ∧ ((s.1.1.2 = false ∧ s.2 = Some h) ∨ ( s.2 = None)))
    ∨ (s.1.1.1 = V1 ∧ s.2 = Some h).
  Proof.
    intro.
    pattern s.
    eapply (rtc_ind_r _ (V1,false,false,Some h)).
    - right.
      eauto.
    - intros.
      Unshelve.
      2: { exact inv_sts_base. }
      destruct H2.
      + destruct y as [ [ []]]; simpl in *.
        destruct H2 as [-> [-> H2]].
        destruct H2.
        * destruct H2 as [-> ->].
          inversion H1; subst; cbn; eauto.
        * inversion H1; subst; cbn; eauto.
      + destruct y as [ [ []]]; simpl in *.
        destruct H2 as [-> ->].
        inversion H1; subst; cbn; eauto.
        left.
        split; auto.
    - done.
  Qed.

  Lemma inv_sts_0_unclosed_changed_finish s:
    inv_sts_rel (V0, true, true, None) s ->
    s.1.1.1 = V0 ∧ s.1.2 = true ∧ s.2 = None ∧ (s.1.1.2 = false ∨ s.1.1.2 = true).
  Proof.
    intro.
    pattern s.
    eapply (rtc_ind_r _ (V0,true ,true,None)).
    - eauto.
    - intros.
      Unshelve.
      2: { exact inv_sts_base. }
      destruct H2;
      destruct y as [ [ []]];simpl in *.
      destruct H3 as [-> [-> [-> | ->]]];
      inversion H1;
      cbn;eauto.
    - done.
  Qed.

  Lemma inv_sts_1_unclosed_changed_yield cb ob oh h :
      inv_sts_rel (V1, true, true, Some h) (V1, cb, ob, oh) ->
      (cb = true ∧ ob = true ∧ oh = Some h).
    Proof.
      intros G.
      rewrite /inv_sts_rel in G.
      apply rtc_inv in G.
      destruct G as [G|G].
      - inversion G.
        auto.
      - destruct G as [x [G1 G2]].
        inversion G1; auto.
        simplify_eq.
        apply rtc_inv in G2.
        destruct G2 as [G2'|G2].
        + inversion G2'.
        + destruct G2 as [x [G2 G3]].
          inversion G2; auto.
          simplify_eq.
          apply rtc_inv in G3.
          destruct G3 as [G3'|G3].
          * inversion G3'.
          * destruct G3 as [x [G3 G4]].
            inversion G3; auto.
            simplify_eq.
            apply rtc_inv in G4.
            destruct G4 as [G4'|G4].
            -- discriminate.
            -- destruct G4 as [x [G4 G5]].
               inversion G4; auto.              
    Qed.

End sts.


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

  Lemma nainv_sts_init_run s : nainv_sts_rel (false,None) s ->
    (s.1= false ∨ s.1 = true) ∧(s.2 = None ∨ ∃h, s.2 = Some h).
  Proof.
    intro.
    pattern s.
    eapply (rtc_ind_r _ (false,None)).
    - split;left; done.
    - intros.
      Unshelve.
      2: { exact nainv_sts_base. }
      destruct H2.
      destruct H2, H3;destruct y as [ []];simpl in *;inversion H1;subst;cbn;
      split;eauto.
    - done.
  Qed.

  Lemma nainv_sts_init_yield s h : nainv_sts_rel (false, Some h) s ->
       (s.1= false  ∧ s.2 = Some h) ∨ (s.1 = true ∧ (s.2 = None ∨  s.2 = Some h)).
  Proof.
    intro.
    pattern s.
    eapply (rtc_ind_r _ (false, Some h)).
    - left.
      done.
    - intros.
      Unshelve.
      2: { exact nainv_sts_base. }
      destruct y as [ ];simpl in *.
      destruct H2 as [[? ?] | [? [? | ?]]];subst;
      inversion H1; subst;cbn;
      eauto.
    - done.
  Qed.

  Lemma nainv_sts_changed_yield h s : nainv_sts_rel (true, Some h) s ->
      (s.1 = true ∧ (s.2 = None ∨  s.2 = Some h)).
  Proof.
    intro.
    pattern s.
    eapply (rtc_ind_r _ (true, Some h)).
    - eauto.
    - intros.
      Unshelve.
      2: { exact nainv_sts_base. }
      destruct y as [ ];simpl in *.
      destruct H2 as [? [? | ?]];subst;
      inversion H1; subst;cbn;
      eauto.
    - done.
  Qed.

  (* XXX: do we still need this? *)
  Lemma nainv_sts_elim_false h : nainv_sts_rel (false, Some h) (false, None) -> False.
  Proof.
    intros H.
    rewrite /nainv_sts_rel in H.
    apply rtc_inv in H.
    destruct H as [|H].
    - discriminate.
    - destruct H as [x [H1 H2]].
      inversion H1; auto.
      simplify_eq.
      apply rtc_inv in H2.
      destruct H2 as [|H2].
      + discriminate.
      + destruct H2 as [x [H3 H4]].
        inversion H3; auto.
        simplify_eq.
        apply rtc_inv in H4.
        destruct H4 as [|H4].
        * discriminate.
        * destruct H4 as [x [H5 H6]].
          inversion H5; auto.
  Qed.

  (* invariants *)
  Definition inv_name := nroot .@ "lending" .@ "inv".
  Definition nainv_name := nroot .@ "lending" .@ "na".

  Lemma namespace_disjoint: inv_name ## nainv_name.
  Proof.
    apply ndot_ne_disjoint.
    done.
  Qed.
  (* CMRAs *)
  (* regular exclusive tokens *)
  Class tokG Σ := tok_G :> inG Σ (exclR unitO).
  (* monotone RA for the STS of the invariant *)
  Class invStsG Σ := invSts_G :> inG Σ (authUR (mraUR inv_sts_rel)).
  (* monotone RA for the STS of the non-atomic invariant *)
  Class nainvStsG Σ := nainvSts_G :> inG Σ (authUR (mraUR nainv_sts_rel)).

  Context `{!gen_VMG Σ, tokG Σ, invStsG Σ, nainvStsG Σ}.

  Definition inv_state_exact (γ: gname) (s: inv_sts_state):=
    own γ (● principal (inv_sts_rel) s).

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

  Global Instance inv_state_atleast_timeless γ s : Timeless (inv_state_atleast γ s).
  Proof. apply _. Qed.

  Global Instance inv_state_exact_timeless γ s : Timeless (inv_state_exact γ s).
  Proof. apply _. Qed.

  Global Instance nainv_state_atleast_timeless γ s : Timeless (nainv_state_atleast γ s).
  Proof. apply _. Qed.

  Global Instance nainv_state_exact_timeless γ s : Timeless (nainv_state_exact γ s).
  Proof. apply _. Qed.

  Definition token γ := own γ (Excl ()).

  Lemma token_alloc : ⊢|==> ∃ γ, token γ.
  Proof. iApply own_alloc; done. Qed.

  Lemma token_excl γ : token γ -∗ token γ -∗ False.
  Proof. iIntros "H1 H2"; iDestruct (own_valid_2 with "H1 H2") as %?; done. Qed.

  Global Instance token_timeless γ : Timeless (token γ).
  Proof. apply _. Qed.


  (* gnames of exclusive tokens that we will use:
     - γ_closed: VM1 owns it at the beginning.
                 If VM0 owns this token, we can open the non-atomic invariant.
     - γ_switch: VM1 owns it at the beginning, indicating we just switched to VM1.
                 if VM1 has it, we can open the non-atomic invariant.
     - γ_unchanged: VM0 will lose it after VM1 changes the value of the page.
     - γ_done: VM1 owns it at the beginning and will lose it when it halts.
     - γ_access: VM0 will lose it when switching to VM1.
   *)



  Global Instance if_timeless (b:bool) {PROP} `{!Timeless (PROP:=PROP) P1 }  `{!Timeless P2} : Timeless ((if b then P1 else P2)).
  Proof.
    destruct b.
    apply _.
    apply _.
  Qed.

  Definition inv_def γ_invm γ_nainvm γ_closed γ_access γ_done (γ_unchanged: gname) γ_switched : iProp Σ:=
    ∃ (i : VMID)  P ob cb oh, <<i>>{ 1%Qp } ∗ nainv_closed P ∗ inv_state_exact γ_invm (i,ob,cb,oh) ∗
    (* (if cb then True else token γ_unchanged) ∗ *)
    (match (fin_to_nat i,ob,cb, oh) with
    | (0, false, false, _) => (⌜P = ⊤⌝  ∗ nainv_state_atleast γ_nainvm (cb, oh))
    | (0, true, false, _) => (⌜P = ⊤ ∖↑ nainv_name⌝ ∗ token γ_closed)
    | (0, false, true, Some _) => (⌜P = ⊤⌝ ∗ token γ_done ∗ nainv_state_atleast γ_nainvm (cb, oh))
    | (0, false, true, None) => (⌜P = ⊤⌝ ∗ token γ_access ∗ token γ_switched ∗ nainv_state_atleast γ_nainvm (cb, oh))
    | (0, true, true, _) => (⌜P = ⊤ ∖↑ nainv_name⌝ ∗ token γ_closed ∗ token γ_access)
    | (1, false, false, _) => (⌜P = ⊤⌝ ∗ token γ_done ∗ nainv_state_atleast γ_nainvm (cb, oh))
    | (1, true, true, _) => (⌜P = ⊤ ∖ ↑ nainv_name⌝ ∗ token γ_switched)
    | _ => True
    end).

  Local Instance inv_def_timeless γ_invm γ_nainvm γ_closed γ_access γ_done γ_unchanged γ_switched:
        Timeless (inv_def γ_invm γ_nainvm γ_closed γ_access γ_done γ_unchanged γ_switched ).
  Proof.
    unfold inv_def.
    repeat (apply bi.exist_timeless;intro).
    repeat apply bi.sep_timeless;try apply _.
    destruct (fin_to_nat x).
    apply _.
    destruct n;
    apply _.
  Qed.

  Definition nainv_def γ_nainvm (γ_access: gname) γ_done γ_unchanged γ_switched prx1 (page: PID): iProp Σ:=
    ∃ r0 r0' r1 w des b o, nainv_state_exact γ_nainvm (b,o) ∗
    R0 @@ V0 ->r r0 ∗ R0 @@ V1 ->r r0' ∗ R1 @@ V0 ->r r1 ∗ page ->a w ∗ mem_region des prx1 ∗
    (if b then ⌜w = W1⌝ ∗ token γ_unchanged ∗ RX@V1 :=() else True ) ∗
    (match o with
     | None => True
     | Some h => h ->re false ∗ h ->t{1}(V0, W0, V1, [page], Lending)
     end) ∗
    (match (b,o) with
    | (false, None) => RX@V1 :=() ∗ ⌜length des = length (serialized_transaction_descriptor V0 V1 W0 I1 [page] W0)⌝
    | (false, Some h) => ⌜r0 = of_imm run_I⌝ ∗ ⌜r1 = encode_vmid V1⌝ ∗
                         token γ_unchanged∗
                         (* token γ_access ∗ *)
                         ∃ wl, RX@V1 :=(wl, V0) ∗
                         ⌜des = serialized_transaction_descriptor V0 V1 W0 I1 [page] h⌝ ∗
                         ⌜finz.to_z wl =Z.of_nat (length des)⌝ ∗ ⌜w = W0⌝
    | (true, Some h) => ⌜r0 = of_imm yield_I⌝ ∗ ⌜r0' = of_imm yield_I⌝ ∗ ⌜r1 = encode_vmid V1⌝ ∗
                        token γ_switched (* ∗ token γ_access *)
    | (true, None) => ⌜r0 = W1⌝ ∗ ⌜r0' = of_imm yield_I⌝ ∗ token γ_done
    end).

  Global Instance nainv_closed_timeless E : Timeless (nainv_closed E).
  Proof. apply _. Qed.

  Local Instance nainv_def_timeless γ_nainvm γ_access γ_done γ_unchanged γ_switched prx1 page:
        Timeless (nainv_def γ_nainvm γ_access γ_done γ_unchanged γ_switched prx1 page).
  Proof.
    unfold nainv_def.
    repeat (apply bi.exist_timeless;intro).
    repeat apply bi.sep_timeless;try apply _.
  Qed.

  Lemma machine0_proof {sown qo sacc sexcl sh}
             (ppage pprog ptx prx0 prx1: PID)
             (* the page to lend *)
             (ippage : Imm)
             (Hppageeq : of_pid ppage = ippage)
             (Hnotrx0: ppage ≠ prx0)
             (Hnotrx1: ppage ≠ prx1)
             (Hnotrx0': prx0 ≠ ptx)
             (* the des in TX *)
             (des : list Word)
             (Hdeseq : des = serialized_transaction_descriptor V0 V1 W0 W1 [ppage] W0)
             (* ilen is the length of msg *)
             (ilen : Imm)
             (Hileq : (finz.to_z ilen) = Z.of_nat (length des))
             (* the whole program is in page pprog *)
             (Hseq : seq_in_page pprog (length (code0 ippage ilen)) pprog)
             (* has access to all involved pages *)
             (Hacc : {[ppage; pprog; ptx]} ⊆ sacc)
             (* at least owns ppage *)
             (Hown : ppage ∈ sown)
             (* at least has exclusive access to ppage *)
             (Hexcl : ppage ∈ sexcl)
             (* the handle pool is not empty *)
             (Hsh : sh ≠ ∅)
             (γ_invm γ_nainvm γ_closed γ_access γ_done γ_unchanged γ_switched : gname)
    :
    PC @@ V0 ->r pprog
    ∗ hp{ 1 }[ sh ]
    ∗ O@V0 :={qo}[sown]
    ∗ A@V0 :={1}[sacc]
    ∗ E@V0 :={1}[sexcl]
    ∗ TX@V0 := ptx
    ∗ RX@V0 := prx0
    ∗ RX@V1 := prx1
    ∗ mem_region des ptx
    ∗ (∃ r2, R2 @@ V0 ->r r2)
    ∗ R3 @@ V0 ->r (ptx ^+ 2)%f
    ∗ program (code0 ippage ilen) pprog
    (*invariants and ghost variables *)
    ∗ inv inv_name (inv_def γ_invm γ_nainvm γ_closed γ_access γ_done γ_unchanged γ_switched)
    ∗ nainv nainv_name (nainv_def γ_nainvm γ_access γ_done γ_unchanged γ_switched prx1 ppage)
    ∗ token γ_done
    ∗ token γ_closed
    ∗ token γ_access
    ∗ token γ_unchanged
    ∗ inv_state_atleast γ_invm (V0,false,false, None)
    ⊢ WP ExecI @ V0
      {{ (λ m, ⌜m = HaltI⌝ ∗
          PC @@ V0 ->r (pprog ^+ (length (code0 ippage ilen)))%f
          ∗ hp{ 1 }[ sh ]
          ∗ O@V0 :={qo}[sown]
          ∗ A@V0 :={1}[sacc]
          ∗ E@V0 :={1}[sexcl]
          ∗ TX@V0 := ptx
          ∗ RX@V0:=prx0
          ∗ RX@V1:=prx1
          ∗ (∃ des, mem_region des ptx)
          ∗ R2 @@ V0 ->r ilen
          ∗ (∃ r3, R3 @@ V0 ->r r3)
          ∗ token γ_closed
          ∗ program (code0 ippage ilen) pprog)
      }}.
  Proof.
    iIntros  "(PC & hp & Own & Acc & Excl & TX & RX0 & RX1 & des & [% R2] & R3 & prog & #Hinv & #Hnainv & Done & Closed & Access
                                    & Unchanged & InvAtLeast)".
    iDestruct "prog" as "[prog1 prog]".
    pose proof (seq_in_page_forall2 _ _ _ Hseq) as HaddrIn.
    subst des.
    set (des:= (serialized_transaction_descriptor V0 V1 W0 W1 [ppage] W0)).
    assert (HseqTX: seq_in_page ptx (length des) ptx).
    { simpl. unfold seq_in_page. split. solve_finz. split. unfold Is_true. case_match;[done|solve_finz].
      split.
      pose proof (last_addr_in_bound ptx).
      solve_finz.
      unfold Is_true. case_match;[done|solve_finz]. }
    iApply wp_sswp.
    (* open the invariant *)
    iApply (sswp_fupd_around _ ⊤ (⊤ ∖ ↑ inv_name) ⊤).
    iInv inv_name as ">Inv" "HIClose".
    iDestruct "Inv" as (i P cb ob oh) "(ScheToken & NaInvToken & InvExact  & Hmatch)".
    iDestruct (inv_state_exact_atleast with "InvExact InvAtLeast") as "%Rel".
    iClear "InvAtLeast".
    apply inv_sts_0_closed_unchanged_open in Rel.
    simpl in Rel.
    destruct Rel as [[-> [[-> ->] | ->]] | [-> [[-> ->] | [-> ->]]]]; iSimpl in "Hmatch";
      try destruct cb.
    { iDestruct "Hmatch" as "(_ & Closed')".
      iDestruct (token_excl with "Closed Closed'") as %[]. }
    2: { iDestruct "Hmatch" as "(_ & Closed' & _)".
      iDestruct (token_excl with "Closed Closed'") as %[]. }
    2: { destruct oh.
         iDestruct "Hmatch" as "(_ & Done' & _)".
         iDestruct (token_excl with "Done Done'") as %[].
         iDestruct "Hmatch" as "(_ & Access' & _)".
         iDestruct (token_excl with "Access Access'") as %[]. }
    2: { iDestruct "Hmatch" as "(_ & Done' & _)".
         iDestruct (token_excl with "Done Done'") as %[]. }
    2: { iApply (eliminate_wrong_token with "ScheToken").
         done.
         iModIntro.
         iNext.
         iIntros "[_ False]".
         iExFalso.
         done. }
    iDestruct "Hmatch" as "(-> & NaInvAtLeast)".
    (* open the na-invariant *)
    iMod (na_inv_acc with "Hnainv NaInvToken") as "(>NaInv & NaInvToken & NaInvClose)";auto.
    { pose proof namespace_disjoint. set_solver. }
    iDestruct "NaInv" as "(% & % & % & % & % & % & % & NaInvExact & R0 & R0' & R1 & page & RxDes & Hif' & Htrans & Hmatch)".
    iDestruct ((inv_state_update _ _ (V0, true, false, None)) with "InvExact") as ">InvExact".
    { unfold inv_sts_rel. apply rtc_once. constructor. }
    iDestruct (inv_state_observe with "InvExact") as ">[InvExact InvAtLeast]".
    (*mov*)
    iApply (mov_word with "[prog1 PC Acc R1]"); iFrameAutoSolve.
    { set_solver. }
    iModIntro. iNext.
    iIntros "( PC & prog1 & Acc & R1)".
    (* close the invariant *)
    iDestruct ("HIClose" with "[ScheToken NaInvToken InvExact Closed]") as "HIClose".
    { iExists V0, (⊤∖↑ nainv_name), true, false, None. iNext. iFrame. done. }
    iMod "HIClose" as %_.
    iModIntro.
    iDestruct (nainv_state_exact_atleast with "NaInvExact NaInvAtLeast") as "%Rel".
    iClear "NaInvAtLeast".
    apply nainv_sts_init_run in Rel.
    simpl in Rel.
    destruct Rel as [[-> | ->] [-> | [? ->]]];iSimpl in "Hmatch".
    2:{ iDestruct "Hmatch" as "(_ & _ & Unchanged' & _)".
      iDestruct (token_excl with "Unchanged Unchanged'") as %[]. }
    2:{ iDestruct "Hmatch" as "(_ & _ & Done')".
      iDestruct (token_excl with "Done Done'") as %[]. }
    2:{ iDestruct "Hif'" as "(_ &  Unchanged' & _)".
      iDestruct (token_excl with "Unchanged Unchanged'") as %[]. }
    iClear "Htrans Hif'".
    iAssert (⌜ppage ≠ pprog⌝)%I as %Hppagenot.
    { iDestruct (mem_neq with "prog1 page") as %Hppagenot.
      iPureIntro.
      intro.
      apply Hppagenot.
      rewrite H2 //. }
    (* mov *)
    iApply wp_sswp.
    iDestruct "prog" as "[prog2 prog]".
    iApply (mov_word with "[prog2 PC Acc R0]");iFrameAutoSolve.
    { rewrite HaddrIn. set_solver + Hacc. set_solver +. }
    iNext.
    iIntros "( PC & prog2 & Acc & R0)".
    (* str *)
    iApply wp_sswp.
    iDestruct "prog" as "[prog3 prog]".
    rewrite -Hppageeq.
    iApply ((str _ ppage) with "[PC prog3 R0 page R1 Acc RX0]");iFrameAutoSolve.
    { rewrite to_pid_aligned_eq //. }
    { rewrite to_pid_aligned_eq. rewrite HaddrIn. set_solver + Hacc. set_solver +. }
    iNext.
    iIntros "( PC & prog3 & R1 & page & R0 & Acc & RX0)".
    (* mov *)
    iApply wp_sswp.
    iDestruct "prog" as "[prog4 prog]".
    iApply (mov_word with "[prog4 PC Acc R0]");iFrameAutoSolve.
    { rewrite HaddrIn. set_solver + Hacc. set_solver +. }
    iNext.
    iIntros "( PC & prog4 & Acc & R0)".
    (* mov *)
    iApply wp_sswp.
    iDestruct "prog" as "[prog5 prog]".
    iApply (mov_word with "[prog5 PC Acc R1]");iFrameAutoSolve.
    { rewrite HaddrIn. set_solver + Hacc. set_solver +. }
    iNext.
    iIntros "( PC & prog5 & Acc & R1)".
    (* lend *)
    iApply wp_sswp.
    iDestruct "prog" as "[prog6 prog]".
    iApply ((hvc_lend_nz V1 W1 [ppage] {[ppage]}) with "[PC prog6 Own Acc Excl R0 R1 R2 TX des hp]");
    iFrameAutoSolve.
    { apply decode_encode_hvc_func. }
    { simpl. lia. }
    { done. }
    { apply HseqTX. }
    { simpl. done. }
    { set_solver +. }
    { rewrite HaddrIn. set_solver + Hacc. set_solver +. }
    { set_solver + Hown. }
    { set_solver + Hexcl. }
    { done. }
    iNext.
    iIntros "( PC & prog6 & Own & Acc & Excl & R0 & R1 & TX & (% & (%HinHp & R2 & Tran & Retri & Hp) & Des))".
    (* str *)
    iApply wp_sswp.
    iDestruct "prog" as "[prog7 prog]".
    iDestruct "Des" as "(Des0 & Des1 & Des2 & DesRest)".
    iAssert (⌜ppage ≠ ptx⌝)%I as %Hppagenot'.
    { iDestruct (mem_neq with "Des0 page") as %Hppagenot''.
      iPureIntro.
      intro Heq.
      apply Hppagenot''.
      rewrite Heq //. }
    assert(ptx^+ 2 = ptx ^+ 1 ^+ 1)%f as ->. solve_finz.
    iApply ((str _ (ptx ^+ 1 ^+ 1)%f)with "[PC prog7 R2 Des2 R3 Acc RX0]");iFrameAutoSolve.
    { rewrite (seq_in_page_forall2 _ _ _ HseqTX). done.
      simpl. set_solver +. }
    { rewrite HaddrIn. rewrite (seq_in_page_forall2 _ _ _ HseqTX).
      set_solver + Hacc Hppagenot Hppagenot'.
      simpl. set_solver +.
      simpl. set_solver + Hacc.
    }
    iNext.
    iIntros "( PC & prog7 & R3 & Des2 & R2 & Acc & RX0)".
    (* mov *)
    iApply wp_sswp.
    iDestruct "prog" as "[prog8 prog]".
    iApply (mov_reg with "[prog8 PC Acc R2 R3]");iFrameAutoSolve.
    { rewrite HaddrIn. set_solver + Hacc Hppagenot. set_solver +. }
    iNext.
    iIntros "( PC & prog8 & Acc & R3 & R2)".
    (* mov *)
    iApply wp_sswp.
    iDestruct "prog" as "[prog9 prog]".
    iApply (mov_word with "[prog9 PC Acc R0]");iFrameAutoSolve.
    { rewrite HaddrIn. set_solver + Hacc Hppagenot. set_solver +. }
    iNext.
    iIntros "( PC & prog9 & Acc & R0)".
    (* mov *)
    iApply wp_sswp.
    iDestruct "prog" as "[prog10 prog]".
    iApply (mov_word with "[prog10 PC Acc R1]");iFrameAutoSolve.
    { rewrite HaddrIn. set_solver + Hacc Hppagenot. set_solver +. }
    iNext.
    iIntros "( PC & prog10 & Acc & R1)".
    (* mov *)
    iApply wp_sswp.
    iDestruct "prog" as "[prog11 prog]".
    iApply (mov_word with "[prog11 PC Acc R2]");iFrameAutoSolve.
    { rewrite HaddrIn. set_solver + Hacc Hppagenot. set_solver +. }
    iNext.
    iIntros "( PC & prog11 & Acc & R2)".
    (* send *)
    iApply wp_sswp.
    iDestruct "prog" as "[prog12 prog]".
    iApply (hvc_send_primary with "[prog12 PC Acc R0 R1 R2 TX Des0 Des1 Des2 DesRest RX1 Hmatch RxDes]");iFrameAutoSolve.
    { apply decode_encode_hvc_func. }
    { apply decode_encode_vmid. }
    { rewrite HaddrIn. set_solver + Hacc Hppagenot. set_solver +. }
    { assert (finz.to_z (ilen) = Z.of_nat (length (serialized_transaction_descriptor V0 V1 W0 I1 [ppage] wh)))%Z.
      rewrite Hileq.
      simpl.
      done.
      apply H2. }
    { simpl. lia. }
    { done. }
    { iSplitL "Des0 Des1 Des2 DesRest".
      iFrame.
      iSplitL "RX1".
      iFrame.
      iDestruct "Hmatch" as "[RX %Hldes0]".
      iFrame "RX".
      iNext.
      iExists des0.
      iFrame.
      simpl.
      done. }
    iNext.
    iIntros "(PC & prog12 & Acc & R0 & R1 & R2 & TX & RX1 & RX1s & TxDes & RxDes)".
    (* mov *)
    iApply wp_sswp.
    iDestruct "prog" as "[prog13 prog]".
    iApply (mov_word with "[prog13 PC Acc R0]");iFrameAutoSolve.
    { rewrite HaddrIn. set_solver + Hacc Hppagenot. set_solver +. }
    iNext.
    iIntros "( PC & prog13 & Acc & R0)".
    (* run *)
    iDestruct ((nainv_state_update _ _ (false,Some wh)) with "NaInvExact") as ">NaInvExact".
    { unfold inv_sts_rel. apply rtc_once. constructor. }
    iDestruct (nainv_state_observe with "NaInvExact") as ">[NaInvExact NaInvAtLeast]".
    rewrite wp_sswp.
    (* open the invariant *)
    iApply (sswp_fupd_around V0 ⊤ (⊤ ∖ ↑inv_name) _).
    iInv inv_name as ">Inv" "InvClose".
    iDestruct "Inv" as (i P cb ob oh) "(ScheToken & NaInvToken & InvExact & Hmatch)".
    iDestruct (inv_state_exact_atleast with "InvExact InvAtLeast") as "%Rel".
    iClear "InvAtLeast".
    apply inv_sts_0_unclosed_unchanged_switch in Rel.
    simpl in Rel.
    destruct Rel as [[-> [[-> [-> ->]] | [[-> ->] | [[-> [-> ->]] | [-> [-> ->]]]]]] | [-> [[-> ->] | [-> ->]]]]; iSimpl in "Hmatch";
      try destruct oh.
    2 : {
      iDestruct "Hmatch" as "(_ & Done' & _)".
      iDestruct (token_excl with "Done Done'") as %[].
    }
    2 : {
      iDestruct "Hmatch" as "(_ & Access' & _)".
      iDestruct (token_excl with "Access Access'") as %[].
    }
    2 : {
      iDestruct "Hmatch" as "(_ &  _ & Access')".
      iDestruct (token_excl with "Access Access'") as %[].
    }
    2 : {
      iDestruct "Hmatch" as "(_ & Access' & _)".
      iDestruct (token_excl with "Access Access'") as %[].
    }
    2 : {
      iApply (eliminate_wrong_token with "ScheToken").
      done.
      iModIntro.
      iNext.
      iIntros "[_ False]".
      iExFalso.
      done. }
    2 : {
      iApply (eliminate_wrong_token with "ScheToken").
      done.
      iModIntro.
      iNext.
      iIntros "[_ False]".
      iExFalso.
      done. }
    2 : {
      iApply (eliminate_wrong_token with "ScheToken").
      done.
      iModIntro.
      iNext.
      iIntros "[_ False]".
      iExFalso.
      done. }
    2 : {
      iApply (eliminate_wrong_token with "ScheToken").
      done.
      iModIntro.
      iNext.
      iIntros "[_ False]".
      iExFalso.
      done. }
    iDestruct "Hmatch" as "[-> Closed]".
    iDestruct "prog" as "[prog14 prog]".
    iApply (run with "[ScheToken PC prog14 Acc R0 R1]");iFrameAutoSolve.
    { rewrite HaddrIn. set_solver + Hacc Hppagenot. set_solver +. }
    { done. }
    { apply decode_encode_hvc_func. }
    { apply decode_encode_vmid. }
    { iFrame. }
    iModIntro.
    iNext.
    iIntros "(ScheToken & PC & prog14 & Acc & R0 & R1)".
    iDestruct ("NaInvClose" with "[NaInvToken NaInvExact R0 R0' R1 page RxDes Tran Retri Unchanged RX1s]") as "NaInvToken".
    { iSplitR "NaInvToken".
      iNext.
      rewrite /nainv_def.
      iExists run_I, r0', (encode_vmid V1), I0, (serialized_transaction_descriptor V0 V1 W0 I1 [ppage] wh), false, (Some wh).
      iFrame.
      iSplitR;[done|].
      iSplitR;[done|].
      iExists ilen.
      iFrame.
      iSplitR;[done|].
      iSplitR;[|].
      rewrite Hileq //=.
      done.
      iFrame. }
    iMod "NaInvToken".
    (* close the invariant *)
    iDestruct ((inv_state_update _ _ (V1, false, false, Some wh)) with "InvExact") as ">InvExact".
    { unfold inv_sts_rel. apply rtc_once. constructor. }
    iDestruct (inv_state_observe with "InvExact") as ">[InvExact InvAtLeast]".
    iDestruct ("InvClose" with "[ScheToken NaInvToken InvExact NaInvAtLeast Done]") as "HIClose".
    { iExists V1, ⊤, false , false, (Some wh). iNext. iFrame. done. }
    iMod "HIClose" as %_.
    iModIntro.
    (* open the invariant *)
    iApply wp_sswp.
    iApply (sswp_fupd_around _ ⊤ (⊤ ∖ ↑ inv_name) ⊤).
    iInv inv_name as ">Inv" "HIClose".
    iDestruct "Inv" as (i P cb ob oh) "(ScheToken & NaInvToken & InvExact & Hmatch)".
    iDestruct (inv_state_exact_atleast with "InvExact InvAtLeast") as "%Rel".
    iClear "InvAtLeast".
    apply inv_sts_0_closed_changed_yield in Rel.
    simpl in Rel.
    destruct Rel as [[-> [-> [[-> ->] | ->]]] | [-> ->]]; iSimpl in "Hmatch";
    try destruct cb.
    2: { iDestruct "Hmatch" as "(_ & Closed' & _)".
         iDestruct (token_excl with "Closed Closed'") as %[]. }
    2: { iDestruct "Hmatch" as "(_ & Access' & _)".
         iDestruct (token_excl with "Access Access'") as %[]. }
    2: { iApply (eliminate_wrong_token with "ScheToken").
         done.
         iModIntro.
         iNext.
         iIntros "[_ False]".
         iExFalso.
         done. }
    2: { iApply (eliminate_wrong_token with "ScheToken").
         done.
         iModIntro.
         iNext.
         iIntros "[_ False]".
         iExFalso.
         done. }
    iDestruct "Hmatch" as "(-> & Done & NaInvAtLeast)".
    (* open the na-invariant *)
    iMod (na_inv_acc with "Hnainv NaInvToken") as "(>NaInv & NaInvToken & NaInvClose)";auto.
    { pose proof namespace_disjoint. set_solver. }
    iDestruct "NaInv" as "(% & % & % & % & % & % & % & NaInvExact & R0 & R0' & R1 & page & RxDes & Hif' & Htrans & Hmatch)".
    iDestruct ((inv_state_update _ _ (V0, true, true, None)) with "InvExact") as ">InvExact".
    { unfold inv_sts_rel. apply rtc_once. constructor. }
    iDestruct (inv_state_observe with "InvExact") as ">[InvExact InvAtLeast]".
    iDestruct (nainv_state_exact_atleast with "NaInvExact NaInvAtLeast") as "%Rel".
    iClear "NaInvAtLeast".
    apply nainv_sts_changed_yield in Rel.
    simpl in Rel.
    destruct Rel as [-> [-> | ->]];iSimpl in "Hmatch".
    { iDestruct "Hmatch" as "(_ & _ & Done')".
      iDestruct (token_excl with "Done Done'") as %[]. }
    iDestruct "Hif'" as "(-> & Unchanged & RX' )".
    iDestruct "Hmatch" as "(->& ->& ->& Switched)".
    (* mov *)
    iDestruct "prog" as "[prog15 prog]".
    iApply (mov_reg with "[prog15 PC Acc R1 R3]"); iFrameAutoSolve.
    { rewrite HaddrIn. set_solver + Hacc Hppagenot. set_solver +. }
    iModIntro. iNext.
    iIntros "( PC & prog15 & Acc & R1 & R3)".
    (* close the invariant *)
    iDestruct ("HIClose" with "[ScheToken NaInvToken InvExact Closed Access]") as "HIClose".
    { iExists V0, (⊤∖↑ nainv_name), true, true, None. iNext. iFrame. done. }
    iMod "HIClose" as %_.
    iModIntro.
    (* mov *)
    iApply wp_sswp.
    iDestruct "prog" as "[prog16 prog]".
    iApply (mov_word with "[prog16 PC Acc R0]"); iFrameAutoSolve.
    { rewrite HaddrIn. set_solver + Hacc Hppagenot. set_solver +. }
    iNext.
    iIntros "( PC & prog16 & Acc & R0)".
    (* reclaim *)
    iApply wp_sswp.
    iDestruct "prog" as "[prog17 prog]".
    iDestruct "Htrans" as "[Retri Trans]".
    iApply ((hvc_reclaim_lend _ _ _ [ppage] {[ppage]}) with "[prog17 PC Acc R0 R1 Own Excl Retri Trans Hp]"); iFrameAutoSolve.
    { apply decode_encode_hvc_func. }
    { rewrite HaddrIn. set_solver + Hacc Hppagenot. set_solver +. }
    { set_solver + . }
    { set_solver + Hown. }
    { set_solver +.  }
    { set_solver +. }
    iNext.
    iIntros "( PC & prog17 & R0 & R1 & Own & Excl & Acc & Hp)".
    (* mov *)
    iApply wp_sswp.
    iDestruct "prog" as "[prog18 prog]".
    iApply (mov_word with "[prog18 PC Acc R1]"); iFrameAutoSolve.
    { rewrite HaddrIn. set_solver + Hacc Hppagenot. set_solver +. }
    iNext.
    iIntros "( PC & prog18 & Acc & R1)".
    (* ldr *)
    iApply wp_sswp.
    iDestruct "prog" as "[prog19 prog]".
    iApply (ldr with "[prog19 PC Acc page R0 R1 TX]"); iFrameAutoSolve.
    { intro. apply Hppagenot'. rewrite -Hppageeq in H2.  rewrite <-(to_pid_aligned_eq ppage).  done. }
    { rewrite HaddrIn.  rewrite -Hppageeq. rewrite to_pid_aligned_eq. set_solver + Hacc Hppagenot. set_solver +. }
    { rewrite -Hppageeq. iFrame. }
    iNext.
    iIntros "( PC & prog19 & R1 & page & R0 & Acc & TX)".
    (* halt *) 
    iApply wp_sswp.
    (* open invariant *)
    iApply (sswp_fupd_around _ ⊤ (⊤ ∖ ↑ inv_name) ⊤).
    iInv inv_name as ">Inv" "InvClose".
    iDestruct "Inv" as (i P cb ob oh) "(ScheToken & NaInvToken & InvExact & Hmatch)".
    iDestruct (inv_state_exact_atleast with "InvExact InvAtLeast") as "%Rel".
    iClear "InvAtLeast".
    apply inv_sts_0_unclosed_changed_finish in Rel.
    simpl in Rel.
    destruct Rel as [-> [-> [-> [-> | ->]]]];iSimpl in "Hmatch".
    { iDestruct "Hmatch" as "(_ & _ & Switched' & _)".
      iDestruct (token_excl with "Switched Switched'") as %[]. }
    iDestruct "Hmatch" as "(-> & Closed & Access)".
    iDestruct "prog" as "[prog20 _]".
    iApply (halt with "[prog20 PC Acc]"); iFrameAutoSolve.
    { rewrite HaddrIn.  set_solver + Hacc Hppagenot. set_solver +. }
    iModIntro.
    iNext.
    iIntros "( PC & prog20 & Acc )".
    iDestruct ((nainv_state_update _ _ (true,None)) with "NaInvExact") as ">NaInvExact".
    { unfold inv_sts_rel. apply rtc_once. constructor. }
    iDestruct (nainv_state_observe with "NaInvExact") as ">[NaInvExact NaInvAtLeast]".
    iDestruct ("NaInvClose" with "[NaInvToken NaInvExact R0 R0' R1 page RxDes RX' Done Unchanged]") as "NaInvToken".
    { iSplitR "NaInvToken".
      iNext.
      rewrite /nainv_def.
      iExists W1, yield_I, ippage, W1, des1, true , None.
      rewrite Hppageeq.
      iFrame.
      iSplitR;[done|].
      iSplitR;[done|done].
      unfold nainv_closed.
      iFrame.
    }
    iMod "NaInvToken".
    iDestruct ((inv_state_update _ _ (V0, false , true, None)) with "InvExact") as ">InvExact".
    { unfold inv_sts_rel. apply rtc_once. constructor. }
    iDestruct ("InvClose" with "[ScheToken NaInvToken InvExact NaInvAtLeast Access Switched]") as "InvClose".
    { iExists V0, ⊤, false, true , None. iNext. iFrame. done. }
    iMod "InvClose" as %_.
    iModIntro.
    iApply wp_terminated'.
    { done. }
    iSplitR;[done|].
    iFrame "Own TX R2 Closed RX0 RX1".
    iSplitL "PC".
    { simpl.
      assert (forall (f:Word) (n:Z), (n>0)%Z ->  (((f ^+ n) ^+ 1))%f = (f ^+ (n+1)%Z)%f ) as Hplus.
      solve_finz.
      repeat (rewrite (Hplus pprog);[|lia]).
      iFrame.
    }
    assert (Hunion_diff: forall (X Y : gset handle),  Y ⊆ X -> X ∖ Y ∪ Y = X).
    { intros. rewrite (difference_union_L X Y). rewrite union_comm_L.
      assert (Y ∪ X = X) as ->. set_solver + H2. done. }
    (* TODO: merge them *)
    assert (Hunion_diff': forall (X Y : gset PID),  Y ⊆ X -> X ∖ Y ∪ Y = X).
    { intros. rewrite (difference_union_L X Y). rewrite union_comm_L.
      assert (Y ∪ X = X) as ->. set_solver + H2. done. }
    rewrite Hunion_diff;[|set_solver + HinHp].
    rewrite !Hunion_diff';[|set_solver + Hacc|set_solver + Hexcl].
    iFrame "Hp Acc Excl".
    iSplitL "TxDes".
    iExists (serialized_transaction_descriptor V0 V1 W0 I1 [ppage] wh).
    iFrame.
    iSplitL "R3".
    iExists wh.
    iFrame.
    unfold program.
    iApply big_sepL2_cons;iFrame.
    done.
Qed.

  Definition l_pre step base :=
    [
    Mov R5 (inl step); (* remaining runs *)
    Mov R6 (inl I0);    
    Mov R7 (inl base)    (* program base address *)
    ].

  Definition l_post :=
    [
    (* incr counter *)
    Mov R8 (inl I1);
    Sub R5 R8;
    (* conditional jump *)
    (* might be a good idea to have a separate rule for branches *)
    Cmp R6 (inr R5);
    Bne R7
    ].

  Definition cycle prog := prog ++ encode_instructions (l_post).
  Definition loop prog step base := encode_instructions (l_pre step base) ++ cycle prog.

  Definition unknown_mem_region (b : handle) (n : nat) := ([∗ list] a ∈ finz.seq b n, ∃ w, a ->a w)%I.

  Definition mem_region' (b : handle) (n : nat) (instr : list handle) := ([∗ list] a;w ∈ finz.seq b n;instr, a ->a w)%I.
  
  Definition loopP des prx ptx := fun (w : Word) => ((unknown_mem_region (of_pid ptx) (Z.to_nat (finz.to_z w) - 1))
                                                    ∗ (∃ m, (of_pid ptx ^+ ((Z.to_nat (finz.to_z w)) - 1))%f ->a m)
                                                    ∗ (mem_region (drop (Z.to_nat (finz.to_z w)) des) ((of_pid ptx ^+ (Z.to_nat (finz.to_z w)))%f))
                                                    ∗ (∃ r, R0 @@ V1 ->r r) ∗ (∃ r, R1 @@ V1 ->r r) ∗ (∃ r, R2 @@ V1 ->r r)
                                                    ∗ RX@V1 := prx ∗ TX@V1 := ptx
                                                    ∗ (mem_region (take (Z.to_nat (finz.to_z w) - 1) des) (of_pid prx))
                                                    ∗ (∃ m, (of_pid prx ^+ (Z.to_nat (finz.to_z w) - 1))%f ->a m ∗ ⌜Some m = des !! (Z.to_nat (finz.to_z w) - 1)⌝)
                                                    ∗ (mem_region (drop (Z.to_nat (finz.to_z w)) des) ((of_pid prx) ^+ (Z.to_nat (finz.to_z w)))%f))%I.

  Definition loopprog iptx iprx := (encode_instructions [Mov R0 (inl I1);
                                              Mov R1 (inl iprx);
                                              Add R1 R5;
                                              Sub R1 R0;
                                              Ldr R2 R1;
                                              Mov R1 (inl iptx);
                                              Add R1 R5;
                                              Sub R1 R0;
                                              Str R2 R1]).

  Lemma list_exist_cons {A : Type} (n : nat) (l : list A) : length l = S n -> ∃ x xs, l = x :: xs /\ length xs = n.
  Proof.
    intros P.
    destruct l.
    - discriminate. 
    - exists a, l.
      split; auto.
  Qed.
  (*
  Lemma loop_body {sacc} (des : list Word)
             (ppage pprog ptx prx : PID)
             (ippage iptx iprx : Imm)
             (* ibase is the base addr of the loop body *)
             (ibase : Imm)
             (Hibaseeq : of_imm ibase = (pprog ^+ 3)%f)
             (Htxrxne : ptx ≠ prx)
             (Hptxeq : of_imm iptx = ptx)
             (Hprxeq : of_imm iprx = prx)
             (Hppageeq : of_imm ippage = ppage)
             (* has access to RX, TX, and pprog *)
             (Hacc : {[ptx;prx;pprog]} ⊆ sacc)
             (* cannot have access to ppage *)
             (HaccnIn: ppage ∉ sacc)
             (* ilen is the length of msg *)
             (nlen :nat)
             (ilen : Imm)
             (Hileneq : Z.to_nat (finz.to_z ilen) = nlen)
             (* (Hpprogprogaddreq : of_pid pprog = progaddr) *)
             (* the whole program is in page pprog *)
             (Hseq : seq_in_page pprog (length (code1 ilen ibase iprx iptx ippage)) pprog) :
    length des = 6 ->    
    (∀ v (v' : Word) progaddr,
     ⌜v = Z.to_nat (finz.to_z v')⌝ -∗
     ⌜v <= S 5⌝-∗
     ⌜v ≠ 0⌝-∗                     
     ⌜seq_in_page progaddr (length (loopprog iptx iprx)) pprog⌝ -∗
     {PAR{{ (loopP des prx ptx (v' ^+ 1)%f) ∗ PC @@ V1 ->r progaddr
            ∗ R6 @@ V1 ->r I0
            ∗ R5 @@ V1 ->r (v' ^+ 1)%f
            ∗ R7 @@ V1 ->r progaddr
            ∗ (∃ r, R8 @@ V1 ->r r)
            ∗ (∃ nz, NZ @@ V1 ->r nz)
            ∗ A@V1 :={1}[sacc]
            ∗ (program (loopprog iptx iprx) progaddr)
     }}} ExecI @ V1
     {{{ RET ExecI; (loopP des prx ptx v') ∗ PC @@ V1 ->r (progaddr ^+ (length (loopprog iptx iprx)))%f
         ∗ R6 @@ V1 ->r I0
         ∗ R5 @@ V1 ->r (v' ^+ 1)%f
         ∗ R7 @@ V1 ->r progaddr
         ∗ (∃ r, R8 @@ V1 ->r r)
         ∗ (∃ nz, NZ @@ V1 ->r nz)
         ∗ A@V1 :={1}[sacc]
         ∗ (program (loopprog iptx iprx) progaddr)
     }}}%I).
  Proof.
    intros Hdesl.
    iIntros (v v' progaddr Hveq Hvleq Hvneq Hseq').
    iIntros (Ψ).
    iModIntro.
    iIntros "(HProp' & HPC' & HR6' & HR5' & HR7' & HR8' & HNZ' & HACC & Prog') HΨ".
    rewrite /loopprog.
    iDestruct "Prog'" as "(Hinstr1 & Hinstr2 & Hinstr3 & Hinstr4 & Hinstr5 & Hinstr6 & Hinstr7 & Hinstr8 & Hinstr9)".
    iSimpl in "Hinstr9".
    iDestruct "Hinstr9" as "(Hinstr9 & _)".
    iSimpl.
    iDestruct "HProp'" as "(memr & mmemr & rmemr & [% R0] & [% R1] & [% R2] & HRX' & HTX' & HDES')".
    iDestruct "HDES'" as "(PreTX & CurTX & PostTX)".
    assert (Hplusminusone : ∀ p : PID, ((p ^+ (v' ^+ 1) ^- I1)%f = (p ^+ v')%f)).
    assert (v' <= 6)%Z.
    lia.
    assert (v' > 0)%Z.
    lia.
    intros p.
    destruct p as [z].
    destruct z as [t].
    simpl in *.
    assert (t <=? 1999000)%Z.
    assert (∃ k, (t = 1000 * k)%Z).
    assert ((t `rem` 1000)%Z = 0%Z).
    lia.
    admit.
    destruct H4.
    subst t.
    assert (x <? 2000)%Z.
    admit.
    assert (x <=? 1999)%Z.
    admit.
    assert (1999000 = 1000 * 1999)%Z as ->.
    lia.
    assert ((1000 * x <= 1000 * 1999)%Z).
    admit.
    apply Zle_imp_le_bool in H6.
    rewrite H6.
    auto.
    admit.
    assert (Hvoffset : forall p : PID, addr_in_page (p ^+ v')%f p).
    intros p.
    admit.
    iApply parwp_sswp.
    iApply ((@mov_word _ _ _ _ ⊤ V1 _ _ 1 sacc progaddr I1 R0) with "[HPC' HACC R0 Hinstr1]"); iFrameAutoSolve.
    rewrite (to_pid_aligned_in_page _ pprog).
    set_solver.
    apply (seq_in_page_forall1 progaddr (length (loopprog iptx iprx)) pprog Hseq' progaddr).
    rewrite /loopprog.
    simpl.
    set_solver.
    iNext.
    iIntros "(HPC' & Hinstr1 & HACC & R0)".
    iApply parwp_sswp.
    iApply ((@mov_word _ _ _ _ ⊤ V1 _ _ 1 sacc (progaddr ^+ 1)%f iprx R1) with "[HPC' HACC R1 Hinstr2]"); iFrameAutoSolve.
    rewrite (to_pid_aligned_in_page _ pprog).
    set_solver.
    apply (seq_in_page_forall1 progaddr (length (loopprog iptx iprx)) pprog Hseq' (progaddr ^+ 1)%f).
    rewrite /loopprog.
    simpl.
    set_solver.
    iNext.
    iIntros "(HPC' & Hinstr2 & HACC & R1)".
    iApply parwp_sswp.
    iApply ((@add _ _ _ _ (Add R1 R5) V1 (encode_instruction (Add R1 R5)) _ _ _ pprog ((progaddr ^+ 1) ^+ 1)%f R1 R5 sacc) with "[HPC' Hinstr3 R1 HR5' HACC]"); auto; iFrameAutoSolve.
    apply (seq_in_page_forall1 progaddr (length (loopprog iptx iprx))); auto.
    rewrite /loopprog /=.
    set_solver.
    set_solver.
    iNext.
    iIntros "(HPC' & Hinstr3 & R1 & R5 & HACC)".
    iApply parwp_sswp.
    iApply ((@sub _ _ _ _ V1 (encode_instruction (Sub R1 R0)) _ _ _ (((progaddr ^+ 1) ^+ 1) ^+ 1)%f R1 R0 sacc) with "[HPC' Hinstr4 R1 R0 HACC]"); auto; iFrameAutoSolve.
    assert (to_pid_aligned (((progaddr ^+ 1) ^+ 1) ^+ 1)%f = pprog) as ->.
    apply to_pid_aligned_in_page.
    apply (seq_in_page_forall1 progaddr (length (loopprog iptx iprx))); auto.
    rewrite /loopprog /=.
    set_solver.
    set_solver.
    iNext.
    iIntros "(HPC' & Hinstr4 & R1 & R0 & HACC)".
    iApply parwp_sswp.
    rewrite Hprxeq Hplusminusone.
    assert (Z.to_nat (v' ^+ 1)%f = v + 1) as ->.
    solve_finz.
    iDestruct "CurTX" as "[%m [CurTX %Meq]]".
    iApply ((@ldr _ _ _ _ _ V1 (encode_instruction (Ldr R2 R1)) m _ _ _ ((((progaddr ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f (iprx ^+ v')%f R2 R1 sacc) with "[HPC' Hinstr5 R2 R1 HACC HTX' CurTX]"); auto; iFrameAutoSolve.
    {
      intros C.
      rewrite (to_pid_aligned_in_page _ prx) in C.
      symmetry in C.
      contradiction.
      by rewrite Hprxeq.
    }
    assert (to_pid_aligned ((((progaddr ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f = pprog) as ->.
    apply to_pid_aligned_in_page.
    apply (seq_in_page_forall1 progaddr (length (loopprog iptx iprx))); auto.
    rewrite /loopprog /=.
    set_solver.
    rewrite (to_pid_aligned_in_page _ prx).
    set_solver.
    by rewrite Hprxeq.
    assert ((prx ^+ ((v + 1)%nat - 1))%f = (iprx ^+ v')%f) as ->.
    rewrite Hveq.
    solve_finz.
    rewrite Hprxeq.
    iFrame.
    iNext.
    iIntros "(HPC' & Hinstr5 & R1 & CurTX & R2 & HACC & HTX')".
    iApply parwp_sswp.
    iApply ((@mov_word _ _ _ _ ⊤ V1 _ _ 1 sacc (((((progaddr ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f iptx R1) with "[HPC' HACC R1 Hinstr6]"); iFrameAutoSolve.
    rewrite (to_pid_aligned_in_page _ pprog).
    set_solver.
    apply (seq_in_page_forall1 progaddr (length (loopprog iptx iprx)) pprog Hseq' (((((progaddr ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f).
    rewrite /loopprog.
    simpl.
    set_solver.
    iNext.
    iIntros "(HPC' & Hinstr6 & HACC & R1)".
    iApply parwp_sswp.
    iApply ((@add _ _ _ _ (Add R1 R5) V1 (encode_instruction (Add R1 R5)) _ _ _ pprog ((((((progaddr ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f R1 R5 sacc) with "[HPC' Hinstr7 R1 R5 HACC]"); auto; iFrameAutoSolve.
    apply (seq_in_page_forall1 progaddr (length (loopprog iptx iprx))); auto.
    rewrite /loopprog /=.
    set_solver.
    set_solver.
    iNext.
    iIntros "(HPC' & Hinstr7 & R1 & R5 & HACC)".
    iApply parwp_sswp.
    iApply ((@sub _ _ _ _ V1 (encode_instruction (Sub R1 R0)) _ _ _ (((((((progaddr ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f R1 R0 sacc) with "[HPC' Hinstr8 R1 R0 HACC]"); auto; iFrameAutoSolve.
    assert (to_pid_aligned (((((((progaddr ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f = pprog) as ->.
    apply to_pid_aligned_in_page.
    apply (seq_in_page_forall1 progaddr (length (loopprog iptx iprx))); auto.
    rewrite /loopprog /=.
    set_solver.
    set_solver.
    iNext.
    iIntros "(HPC' & Hinstr8 & R1 & R0 & HACC)".
    iApply parwp_sswp.
    iDestruct "mmemr" as "[%m' mmemr]".
    iApply (@str _ _ _ _ _ V1 (encode_instruction (Str R2 R1)) _ m' _ _ ((((((((progaddr ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f (ptx ^+ v')%f R2 R1 sacc with "[HPC' Hinstr9 mmemr R1 R2 HACC HRX']"); auto; iFrameAutoSolve.
    {
      intros C.
      rewrite (to_pid_aligned_in_page _ ptx) in C.
      symmetry in C.
      contradiction.
      apply Hvoffset.
    }
    {
      assert (to_pid_aligned ((((((((progaddr ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f = pprog) as ->.
      apply to_pid_aligned_in_page.
      apply (seq_in_page_forall1 progaddr (length (loopprog iptx iprx))); auto.
      rewrite /loopprog /=.
      set_solver.
      rewrite (to_pid_aligned_in_page _ ptx).
      set_solver.
      done.
    }
    rewrite Hptxeq.
    assert ((ptx ^+ ((v + 1)%nat - 1))%f = (ptx ^+ v)%f) as ->.
    solve_finz.
    rewrite Hplusminusone.
    assert ((ptx ^+ v)%f = (ptx ^+ v')%f) as ->.
    solve_finz.
    iFrame.
    iNext.
    iIntros "(HPC' & Hinstr9 & R1 & mmemr & R2 & HACC & HRX')".
    iApply parwp_finish.
    iApply "HΨ".
    iFrame.
    simpl.
    iSplitR "HPC'".
    2 : {
      simpl.
      assert (forall (f : Word) (n : Z), (n > 0)%Z ->  (((f ^+ n) ^+ 1))%f = (f ^+ (n+1)%Z)%f ) as Hplus.
      solve_finz.
      iSplit; last done.
      repeat (rewrite (Hplus progaddr); [|lia]).
      iFrame.
    }
    iAssert (∃ r : handle, R0 @@ V1 ->r r)%I with "[R0]" as "R0'".
    {
      by iExists W1.     
    }
    iFrame "R0'".
    iAssert (∃ r : handle, R1 @@ V1 ->r r)%I with "[R1]" as "R1'".
    {
      by iExists (ptx ^+ v')%f.     
    }
    iFrame "R1'".
    iAssert (∃ r : handle, R2 @@ V1 ->r r)%I with "[R2]" as "R2'".
    {
      by iExists m.     
    }
    iFrame "R2'".
    assert (exists x1 x2 x3 x4 x5 x6, des = [x1; x2; x3; x4; x5; x6]) as (x1 & x2 & x3 & x4 & x5 & x6 & ->).
    {
      do 6 (destruct(list_exist_cons _ des Hdesl) as [? [xs [-> Hdesl']]]; clear Hdesl; rename Hdesl' into Hdesl; rename xs into des).
      apply nil_length_inv in Hdesl as ->.
      eauto 7.
    }
    simpl.
    rewrite -Hveq.
    rewrite PeanoNat.Nat.add_sub.
    assert ((ptx ^+ v')%f = (ptx ^+ v)%f) as ->.
    solve_finz.
    rewrite Hprxeq.
    assert ((prx ^+ v')%f = (prx ^+ v)%f) as ->.
    solve_finz.
    assert (forall (f : Word) (n : Z), (n > 0)%Z ->  (((f ^+ n) ^+ 1))%f = (f ^+ (n+1)%Z)%f ) as Hplus.
    solve_finz.
    assert (∀ (n : nat) (m : Z) (L : (m >= 0)%Z), (n%nat + m)%Z = (n + Z.to_nat m)%nat) as Hplus'.
    lia.
    assert (∀ (n : nat) (m : Z) (L : (n >= m)%Z) (L' : (m >= 0)%Z), (n%nat - m)%Z = (n - Z.to_nat m)%nat) as Hplus''.
    lia.
    assert (v = 5) as ->.
    admit.
    rewrite /unknown_mem_region /mem_region.
    simpl.
    inversion Meq as [Heq].
    rewrite -Heq.
    repeat (rewrite -assoc).
    repeat (iDestruct "memr" as "(? & memr)").
    repeat (iDestruct "rmemr" as "(? & rmemr)").
    repeat (iDestruct "PreTX" as "(? & PreTX)").
    repeat (iDestruct "PostTX" as "(? & PostTX)").
    iFrame.
    repeat (rewrite Hplus; last lia).
    repeat (rewrite Hplus'; last lia).
    simpl.
    iFrame.
    rewrite Hplus''; [|lia|lia].    
  Admitted.
   *)

  Fixpoint incrN (p : handle) (n : nat) : handle :=
    match n with
    | 0 => p
    | S n => ((incrN p n) ^+ I1)%f
    end.
  
  Fixpoint decrN (p : handle) (n : nat) : handle :=
    match n with
    | 0 => p
    | S n => ((decrN p n) ^- I1)%f
    end.

  Program Definition W3 : Word := (finz.FinZ 3 _ _).
  Program Definition I3 : Imm := (I W3 _).
  
  Program Definition W4 : Word := (finz.FinZ 4 _ _).
  Program Definition I4 : Imm := (I W4 _).
  
  Program Definition W5 : Word := (finz.FinZ 5 _ _).
  Program Definition I5 : Imm := (I W5 _).
  
  Lemma page_spec0 (p : PID) : ((of_pid p) <= word_size - 1000)%Z.
  Proof.
    destruct p as [w align].
    destruct w as [z lt pos].
    simpl in align.
    assert ((z `rem` 1000 = 0)%Z) as align'.
    lia.
    apply Z.rem_divide in align'; last lia.
    rewrite /Z.divide in align'.
    destruct align' as [k align'].
    assert (k < 2000)%Z.
    lia.
    subst z.
    simpl.
    assert ((2000000 - 1000)%Z = 1999000%Z) as ->.
    lia.
    assert (1999000%Z = (1999 * 1000)%Z) as ->.
    lia.
    apply Z.mul_le_mono_nonneg_r; lia.
  Qed.

  (* program of VM1
    l is the length of the message
   ibase is the base address of the loop body
   iprx and iptx are the PIDs of RX and TX pages of VM1
   ipage is the PID of the page to lend *)
  (* TODO: VM1 knows l via msg_wait/poll *)
  Definition code1 (l : Imm) (ibase : Imm) (iprx iptx : Imm) (ipage: Imm) : list Word :=
    encode_instructions
    [
    Nop;    
    (* loop init *)
    Mov R5 (inl l);
    Mov R6 (inl I0);
    Mov R7 (inl ibase);

    (* copy word from rx + l to tx + l *)
    Mov R0 (inl I1);
    Mov R1 (inl iprx);
    Add R1 R5;
    Sub R1 R0;
    Ldr R2 R1;
    Mov R1 (inl iptx);
    Add R1 R5;
    Sub R1 R0;
    Str R2 R1;

    (* loop end *)
    Mov R8 (inl I1);
    Sub R5 R8;
    Cmp R6 (inr R5);
    Bne R7;

    Mov R0 (inl l);
    Mov R1 (inl iprx);
    Mov R2 (inl I1);
    Add R1 R0;
    Add R1 R2;
    Ldr R3 R1;
    Mov R1 (inl iptx);
    Add R1 R0;
    Str R3 R1;
    
    Mov R0 (inl (encode_hvc_func Poll));
    Hvc;
    (* tx -> descriptor *)
    (* h -> transaction entry *)
    (* h -> not taken *)
    Mov R0 (inl (encode_hvc_func Retrieve));
    Mov R1 (inl l);
    Mov R2 (inl I1);
    Add R1 R2;
    Hvc;
    (* tx -> descriptor *)
    (* h -> transaction entry *)
    (* h -> taken *)
    (* store a new value *)
    Mov R1 (inl ipage);
    Mov R0 (inl I1);
    Str R0 R1;
    (* tx -> descriptor *)
    (* h -> transaction entry *)
    (* h -> taken *)
    (* p -> 1 *)
    (* prepare a new retrieve descriptor [h, 0] *)
    (* copy h from rx + 1 to tx + 0 *)
    Mov R1 (inl iprx);
    Mov R0 (inl I2);
    Add R1 R0;
    Ldr R0 R1;
    Mov R1 (inl iptx);
    Str R0 R1;
    (* relinquish *)
    Mov R0 (inl (encode_hvc_func Relinquish));
    Hvc;
    Mov R0 (inl (encode_hvc_func Poll));
    Hvc;
    (* yield *)
    Mov R0 (inl yield_I);
    Hvc
    ].
    
  Lemma machine1_proof {sacc sown sexcl progaddr h}
             (ppage pprog ptx prx : PID)
             (ippage iptx iprx : Imm)
             (* ibase is the base addr of the loop body *)
             (ibase : Imm)
             (Hibaseeq : of_imm ibase = (pprog ^+ 3)%f)
             (Hptxeq : of_imm iptx = ptx)
             (Hprxeq : of_imm iprx = prx)
             (Hnottxrx: prx ≠ ptx)
             (Hppageeq : of_imm ippage = ppage)
             (Hpprogprogaddreq : of_pid pprog = progaddr)
             (Haccowndisj : sacc ## sown)
             (Haccexcldisj : sacc ## sexcl)
             (Hownexcldisj : sown ## sexcl)
             (* has access to RX, TX, and pprog *)
             (Hacc : {[ptx;prx;pprog]} ⊆ sacc)
             (* cannot have access to ppage *)
             (HaccnIn: ppage ∉ sacc)
             (HownnIn: ppage ∉ sown)
             (HexclnIn: ppage ∉ sexcl)
             (* the whole program is in page pprog *)
             (Hseq : seq_in_page pprog (length (code1 I3 ibase iprx iptx ippage)) pprog)
             (γ_invm γ_nainvm γ_closed γ_access γ_done γ_unchanged γ_switched : gname) :
    PC @@ V1 ->r pprog
    ∗ A@V1 :={1}[sacc]
    ∗ TX@ V1 := ptx
    ∗ RX@V1 := prx
    ∗ (∃ des', mem_region des' ptx ∗ ⌜length des'= 6⌝)
    ∗ (∃ r, NZ @@ V1 ->r r)             
    ∗ (∃ r, R1 @@ V1 ->r r)
    ∗ (∃ r, R2 @@ V1 ->r r)
    ∗ (∃ r, R3 @@ V1 ->r r)
    ∗ (∃ r, R5 @@ V1 ->r r)
    ∗ (∃ r, R6 @@ V1 ->r r)
    ∗ (∃ r, R7 @@ V1 ->r r)
    ∗ (∃ r, R8 @@ V1 ->r r)
    ∗ O@V1:={1}[sown]
    ∗ E@V1:={1}[sexcl]
    ∗ program (code1 I3 ibase iprx iptx ippage) pprog
    (*invariants and ghost variables *)
    ∗ inv inv_name (inv_def γ_invm γ_nainvm γ_closed γ_access γ_done γ_unchanged γ_switched)
    ∗ nainv nainv_name (nainv_def γ_nainvm γ_access γ_done γ_unchanged γ_switched prx ppage)
    ∗ token γ_switched
    ∗ inv_state_atleast γ_invm (V0,false,false, h)
    ⊢ WP ExecI @ V1
    {{ λ m, ⌜m = ExecI⌝ ∗ False%I }}.
  Proof.
    iIntros "(PC & Acc & TX & RX & [% [mrdes %mrdesEq]] & NZ & R1 & R2 & R3 & R5 & R6 & R7 & R8 & Own & Excl & program & #Hinv & #Hainv & HSwitched & InvAtLeast)".
    pose proof (seq_in_page_forall2 _ _ _ Hseq) as HaddrIn.
    iFrame.
    iApply wp_sswp.
    (* open the invriant *)
    iApply (sswp_fupd_around _ ⊤ (⊤ ∖ ↑ inv_name) ⊤).
    iInv inv_name as ">Inv" "HIClose".
    iDestruct "Inv" as (i P cb ob oh) "(ScheToken & NaInvToken & InvExact & Hmatch)".
    iDestruct (inv_state_exact_atleast with "InvExact InvAtLeast") as "%Rel".
    iClear "InvAtLeast".
    destruct (decide (i = V1)).
    2 : {
      iApply (eliminate_wrong_token with "ScheToken").
      done.
      iModIntro.
      iNext.
      iIntros "[_ False]".
      iExFalso.
      done.
    }
    simplify_eq.
    iEval (simpl) in "Hmatch".
    pose proof Rel as Rel'.
    apply inv_sts_0_changed in Rel'.
    destruct Rel' as [-> [h' ->]].
    apply inv_sts_0_closed_unchanged_open in Rel.
    simpl in Rel.
    destruct Rel as [[? ?]|[_ Rel]]; first discriminate.
    destruct Rel as [[-> ->] | [-> ->]]; iSimpl in "Hmatch".
    2: {
      iDestruct "Hmatch" as "[_ SW]".
      iDestruct (token_excl with "HSwitched SW") as %[].
    }
    iDestruct "Hmatch" as "(-> & Done & NaInvAtLeast)".
    iMod (na_inv_acc with "Hainv NaInvToken") as "(>NaInv & NaInvToken & NaInvClose)";auto.
    { pose proof namespace_disjoint. set_solver. }
    iDestruct "NaInv" as "(% & % & % & % & % & % & % & NaInvExact & HR0 & R0' & HR1 & page & RxDes & Htrans & Hmatch)".
    iDestruct ((nainv_state_exact_atleast _ (b, o) (false, Some h')) with "NaInvExact NaInvAtLeast" ) as "%NaInvExact".
    apply nainv_sts_init_yield in NaInvExact.
    simpl in NaInvExact.
    destruct NaInvExact as [[-> ->] | [-> NaInvExact]].
    2 : {
      destruct NaInvExact as [-> | ->].
      iDestruct "Hmatch" as "(_ & _ & _ & DONE)".
      iDestruct (token_excl with "Done DONE") as %[].
      iDestruct "Hmatch" as "(_ & _ & _ & _ & SW)".
      iDestruct (token_excl with "HSwitched SW") as %[].
    }
    iDestruct ((inv_state_update _ _ (V1, true, true, Some h')) with "InvExact") as ">InvExact".
    { unfold inv_sts_rel. apply rtc_once. constructor. }
    iDestruct (inv_state_observe with "InvExact") as ">[InvExact InvAtLeast]".
    iDestruct "Hmatch" as "((Hretri & Htrans') & -> & (-> & HUnchanged & [%wl (RX' & -> & %wleq & ->)]))".
    rewrite /serialized_transaction_descriptor /serialized_memory_descirptor.
    iSimpl in "RxDes".
    iDestruct "RxDes" as "(RxDes1 & RxDes2 & RxDes3 & RxDes4 & RxDes5 & RxDes6 & _)".
    assert (Hseqrx : seq_in_page prx 6 prx).
    {
      simpl. unfold seq_in_page. split. solve_finz. split. unfold Is_true. case_match; [done|solve_finz].
      split.
      pose proof (last_addr_in_bound prx).
      solve_finz.
      unfold Is_true. case_match; [done|solve_finz].
    }
    assert (Hseqtx : seq_in_page ptx 6 ptx).
    {
      simpl. unfold seq_in_page. split. solve_finz. split. unfold Is_true. case_match; [done|solve_finz].
      split.
      pose proof (last_addr_in_bound ptx).
      solve_finz.
      unfold Is_true. case_match; [done|solve_finz].
    }
    assert (exists x1 x2 x3 x4 x5 x6, des' = [x1; x2; x3; x4; x5; x6]) as (x1 & x2 & x3 & x4 & x5 & x6 & ->).
    {
      do 6 (destruct(list_exist_cons _ des' mrdesEq) as [? [xs [-> mrdesEq']]]; clear mrdesEq; rename mrdesEq' into mrdesEq; rename xs into des').
      apply nil_length_inv in mrdesEq as ->.
      eauto 7.
    }
    iDestruct "mrdes" as "(TxDes1 & TxDes2 & TxDes3 & TxDes4 & TxDes5 & TxDes6 & _)".
    iAssert (⌜ppage ≠ prx⌝)%I as %Hppagenot'.
    { iDestruct (mem_neq with "RxDes1 page") as %Hppagenot''.
      iPureIntro.
      intro Heq.
      apply Hppagenot''.
      rewrite Heq //.
    }
    iAssert (⌜ppage ≠ ptx⌝)%I as %Hppagenot''.
    { iDestruct (mem_neq with "TxDes1 page") as %Hppagenot'''.
      iPureIntro.
      intro Heq.
      apply Hppagenot'''.
      rewrite Heq //.
    }
    iDestruct "program" as "(prog1 & prog2 & prog3 & prog4 & prog5 & prog6 & prog7 & prog8 & prog9 & prog10 & prog11 & prog12 & prog13 & prog14 & prog15 & prog16 & prog17 & program)".
    iDestruct "NZ" as "[% NZ]".
    iDestruct "R1" as "[% R1]".
    iDestruct "R2" as "[% R2]".
    iDestruct "R3" as "[% R3]".
    iDestruct "R5" as "[% R5]".    
    iDestruct "R6" as "[% R6]".
    iDestruct "R7" as "[% R7]".
    iDestruct "R8" as "[% R8]".

    (* nop to deal with the invariant when we have a working loop macro rule *)
    
    iApply (nop with "[prog1 PC Acc]"); iFrameAutoSolve.
    {
      rewrite HaddrIn.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro. iNext.
    iIntros "( PC & prog1 & Acc )".
    iDestruct ("HIClose" with "[ScheToken NaInvToken InvExact HSwitched NaInvAtLeast]") as "HIClose".
    { iExists V1, (⊤ ∖ ↑nainv_name), true, true, (Some h'). iNext. iFrame. done. }
    iMod "HIClose" as %_.
    iModIntro.
    
    (* preamble *)
    
    rewrite wp_sswp.
    iApply (mov_word _ I3 R5 with "[prog2 R5 Acc PC]"); iFrameAutoSolve.
    {
      rewrite HaddrIn.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & prog2 & Acc & R5)".
    rewrite wp_sswp.
    iApply (mov_word _ I0 R6 with "[prog3 R6 Acc PC]"); iFrameAutoSolve.
    {
      rewrite HaddrIn.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & prog3 & Acc & R6)".
    
    (* iter 1 *)
    
    rewrite wp_sswp.
    iApply (mov_word _ ibase R7 with "[prog4 R7 Acc PC]"); iFrameAutoSolve.
    {
      rewrite HaddrIn.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & prog4 & Acc & R7)".
    rewrite wp_sswp.
    iApply (mov_word _ I1 R0 with "[prog5 R0' Acc PC]"); iFrameAutoSolve.
    {
      rewrite HaddrIn.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & prog5 & Acc & R0)".
    rewrite wp_sswp.
    iApply (mov_word _ iprx R1 with "[prog6 R1 Acc PC]"); iFrameAutoSolve.
    {
      rewrite HaddrIn.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & prog6 & Acc & R1)".
    rewrite wp_sswp.
    iApply (@add _ _ _ _ _ _ _ _ _ _ pprog _ R1 R5 sacc with "[prog7 R1 R5 Acc PC]"); iFrameAutoSolve; auto.
    {
      rewrite <- (HaddrIn ((((((pprog ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f) at 2.
      apply in_page_to_pid_aligned.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    {
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
    }
    iModIntro.
    iIntros "(PC & prog7 & R1 & R5 & Acc)".
    rewrite wp_sswp.
    iApply (sub _ R1 R0 sacc with "[prog8 R1 R0 Acc PC]"); iFrameAutoSolve; auto.
    {
      rewrite HaddrIn.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & prog8 & R1 & R0 & Acc)".
    rewrite wp_sswp.
    rewrite Hprxeq.
    assert ((prx ^+ I3 ^- I1)%f = ((prx ^+ 1) ^+ 1)%f) as ->.
    {
      pose proof (page_spec0 prx) as prxSpec.
      assert ((2000000 - 1000)%Z = 1999000%Z) as prxSpecEq.
      lia.
      rewrite prxSpecEq in prxSpec; clear prxSpecEq.
      assert ((prx ^+ I3 ^- I1)%f = (prx ^+ I2)%f) as ->.      
      rewrite /I3 /W3 /I2 /W2 /I1 /W1 //=.
      solve_finz.
      assert (forall (f : Word) (n : Z), (n > 0)%Z ->  (((f ^+ n) ^+ 1))%f = (f ^+ (n+1)%Z)%f ) as Hplus.
      solve_finz.
      repeat (rewrite (Hplus prx); [|lia]).
      rewrite /I2 /W2 //=.
    }
    iApply (ldr with "[prog9 PC Acc R2 R1 TX RxDes3]"); iFrameAutoSolve.
    {
      intro C. rewrite (to_pid_aligned_in_page _ prx) in C. done.
      apply (seq_in_page_forall1 prx 6 prx Hseqrx).
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    {
      rewrite HaddrIn.
      rewrite (to_pid_aligned_in_page _ prx).
      apply union_least; rewrite singleton_subseteq_l;
        rewrite ->elem_of_subseteq in Hacc;
        apply Hacc.
      apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      apply elem_of_union_l;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      apply (seq_in_page_forall1 prx 6 prx Hseqrx).
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & prog9 & R1 & RxDes3 & R2 & Acc & TX)".
    rewrite wp_sswp.
    iApply (mov_word _ iptx R1 with "[prog10 R1 Acc PC]"); iFrameAutoSolve.
    {
      rewrite HaddrIn.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & prog10 & Acc & R1)".
    rewrite wp_sswp.
    iApply (@add _ _ _ _ _ _ _ _ _ _ pprog _ R1 R5 sacc with "[prog11 R1 R5 Acc PC]"); iFrameAutoSolve; auto.
    {
      rewrite <- (HaddrIn ((((((((((pprog ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f) at 2.
      apply in_page_to_pid_aligned.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    {
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
    }
    iModIntro.
    iIntros "(PC & prog11 & R1 & R5 & Acc)".
    rewrite wp_sswp.
    iApply (sub _ R1 R0 sacc with "[prog12 R1 R0 Acc PC]"); iFrameAutoSolve; auto.
    {
      rewrite HaddrIn.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & prog12 & R1 & R0 & Acc)".
    rewrite wp_sswp.
    rewrite Hptxeq.
    assert ((ptx ^+ I3 ^- I1)%f = ((ptx ^+ 1) ^+ 1)%f) as ->.
    {
      pose proof (page_spec0 ptx) as prxSpec.
      assert ((2000000 - 1000)%Z = 1999000%Z) as prxSpecEq.
      lia.
      rewrite prxSpecEq in prxSpec; clear prxSpecEq.
      assert ((ptx ^+ I3 ^- I1)%f = (ptx ^+ I2)%f) as ->.      
      rewrite /I3 /W3 /I2 /W2 /I1 /W1 //=.
      solve_finz.
      assert (forall (f : Word) (n : Z), (n > 0)%Z ->  (((f ^+ n) ^+ 1))%f = (f ^+ (n+1)%Z)%f ) as Hplus.
      solve_finz.
      repeat (rewrite (Hplus ptx); [|lia]).
      rewrite /I2 /W2 //=.
    }
    iApply ((str _ ((ptx ^+ 1) ^+ 1)%f) with "[PC prog13 R2 TxDes3 R1 Acc RX]");iFrameAutoSolve.
    {
      intro C. rewrite (to_pid_aligned_in_page _ ptx) in C. done.
      apply (seq_in_page_forall1 ptx 6 ptx Hseqtx).
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    {
      rewrite HaddrIn.
      rewrite (to_pid_aligned_in_page _ ptx).
      apply union_least; rewrite singleton_subseteq_l;
        rewrite ->elem_of_subseteq in Hacc;
        apply Hacc.
      apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      apply elem_of_union_l;
        apply elem_of_union_l;
        apply elem_of_singleton_2;
        reflexivity.
      apply (seq_in_page_forall1 ptx 6 ptx Hseqtx).
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & prog13 & R1 & TxDes3 & R2 & Acc & RX)".
    rewrite wp_sswp.    
    iApply (mov_word _ I1 R8 with "[prog14 R8 Acc PC]"); iFrameAutoSolve.
    {
      rewrite HaddrIn.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & prog14 & Acc & R8)".
    rewrite wp_sswp.
    iApply (sub _ R5 R8 sacc with "[prog15 R5 R8 Acc PC]"); iFrameAutoSolve; auto.
    {
      rewrite HaddrIn.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & prog15 & R5 & R8 & Acc)".
    rewrite wp_sswp.
    iApply (cmp_reg _ R6 R5 with "[PC NZ prog16 R6 R5 Acc]"); iFrameAutoSolve.
    {
      rewrite HaddrIn.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & prog16 & R6 & R5 & Acc & NZ)".
    assert ((I0 <? I3 ^- I1)%f = true) as ->.
    {
      rewrite /I0 /W0 /I3 /W3 /I1 /W1 //=.
    }
    rewrite wp_sswp.
    iApply (bne _ R7 with "[PC prog17 R7 Acc NZ]"); iFrameAutoSolve.
    {
      rewrite HaddrIn.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & prog17 & R7 & Acc & NZ)".
    assert ((W2 =? W1)%f = false) as ->.
    { rewrite /W2 /W1 //=. }
    iEval (rewrite Hibaseeq) in "PC".
    assert ((pprog ^+ 3)%f = (((pprog ^+ 1) ^+ 1) ^+ 1)%f) as ->.
    solve_finz.

    (* iter 2 *)
    
    rewrite wp_sswp.
    iApply (mov_word _ ibase R7 with "[prog4 R7 Acc PC]"); iFrameAutoSolve.
    {
      rewrite HaddrIn.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & prog4 & Acc & R7)".
    rewrite wp_sswp.
    iApply (mov_word _ I1 R0 with "[prog5 R0 Acc PC]"); iFrameAutoSolve.
    {
      rewrite HaddrIn.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & prog5 & Acc & R0)".
    rewrite wp_sswp.
    iApply (mov_word _ iprx R1 with "[prog6 R1 Acc PC]"); iFrameAutoSolve.
    {
      rewrite HaddrIn.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & prog6 & Acc & R1)".
    rewrite wp_sswp.
    iApply (@add _ _ _ _ _ _ _ _ _ _ pprog _ R1 R5 sacc with "[prog7 R1 R5 Acc PC]"); iFrameAutoSolve; auto.
    {
      rewrite <- (HaddrIn ((((((pprog ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f) at 2.
      apply in_page_to_pid_aligned.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    {
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
    }
    iModIntro.
    iIntros "(PC & prog7 & R1 & R5 & Acc)".
    rewrite wp_sswp.
    iApply (sub _ R1 R0 sacc with "[prog8 R1 R0 Acc PC]"); iFrameAutoSolve; auto.
    {
      rewrite HaddrIn.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & prog8 & R1 & R0 & Acc)".
    rewrite wp_sswp.
    rewrite Hprxeq.
    assert ((prx ^+ (I3 ^- I1) ^- I1)%f = (prx ^+ 1)%f) as ->.
    {
      pose proof (page_spec0 prx) as prxSpec.
      assert ((2000000 - 1000)%Z = 1999000%Z) as prxSpecEq.
      lia.
      rewrite prxSpecEq in prxSpec; clear prxSpecEq.
      assert ((prx ^+ (I3 ^- I1) ^- I1)%f = (prx ^+ I1)%f) as ->.      
      rewrite /I3 /W3 /I1 /W1 //=.
      solve_finz.
      assert (forall (f : Word) (n : Z), (n > 0)%Z ->  (((f ^+ n) ^+ 1))%f = (f ^+ (n+1)%Z)%f ) as Hplus.
      solve_finz.
      repeat (rewrite (Hplus prx); [|lia]).
      rewrite /I3 /W3 //=.
    }
    iApply (ldr with "[prog9 PC Acc R2 R1 TX RxDes2]"); iFrameAutoSolve.
    {
      intro C. rewrite (to_pid_aligned_in_page _ prx) in C. done.
      apply (seq_in_page_forall1 prx 6 prx Hseqrx).
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    {
      rewrite HaddrIn.
      rewrite (to_pid_aligned_in_page _ prx).
      apply union_least; rewrite singleton_subseteq_l;
        rewrite ->elem_of_subseteq in Hacc;
        apply Hacc.
      apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      apply elem_of_union_l;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      apply (seq_in_page_forall1 prx 6 prx Hseqrx).
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & prog9 & R1 & RxDes2 & R2 & Acc & TX)".
    rewrite wp_sswp.
    iApply (mov_word _ iptx R1 with "[prog10 R1 Acc PC]"); iFrameAutoSolve.
    {
      rewrite HaddrIn.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & prog10 & Acc & R1)".
    rewrite wp_sswp.
    iApply (@add _ _ _ _ _ _ _ _ _ _ pprog _ R1 R5 sacc with "[prog11 R1 R5 Acc PC]"); iFrameAutoSolve; auto.
    {
      rewrite <- (HaddrIn ((((((((((pprog ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f) at 2.
      apply in_page_to_pid_aligned.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    {
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
    }
    iModIntro.
    iIntros "(PC & prog11 & R1 & R5 & Acc)".
    rewrite wp_sswp.
    iApply (sub _ R1 R0 sacc with "[prog12 R1 R0 Acc PC]"); iFrameAutoSolve; auto.
    {
      rewrite HaddrIn.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & prog12 & R1 & R0 & Acc)".
    rewrite wp_sswp.
    rewrite Hptxeq.
    assert ((ptx ^+ (I3 ^- I1) ^- I1)%f = (ptx ^+ 1)%f) as ->.
    {
      pose proof (page_spec0 ptx) as ptxSpec.
      assert ((2000000 - 1000)%Z = 1999000%Z) as ptxSpecEq.
      lia.
      rewrite ptxSpecEq in ptxSpec; clear ptxSpecEq.
      assert ((ptx ^+ (I3 ^- I1) ^- I1)%f = (ptx ^+ I1)%f) as ->.      
      rewrite /I3 /W3 /I1 /W1 //=.
      solve_finz.
      assert (forall (f : Word) (n : Z), (n > 0)%Z ->  (((f ^+ n) ^+ 1))%f = (f ^+ (n+1)%Z)%f ) as Hplus.
      solve_finz.
      repeat (rewrite (Hplus ptx); [|lia]).
      rewrite /I3 /W3 //=.
    }
    iApply ((str _ (ptx ^+ 1)%f) with "[PC prog13 R2 TxDes2 R1 Acc RX]");iFrameAutoSolve.
    {
      intro C. rewrite (to_pid_aligned_in_page _ ptx) in C. done.
      apply (seq_in_page_forall1 ptx 6 ptx Hseqtx).
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    {
      rewrite HaddrIn.
      rewrite (to_pid_aligned_in_page _ ptx).
      apply union_least; rewrite singleton_subseteq_l;
        rewrite ->elem_of_subseteq in Hacc;
        apply Hacc.
      apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      apply elem_of_union_l;
        apply elem_of_union_l;
        apply elem_of_singleton_2;
        reflexivity.
      apply (seq_in_page_forall1 ptx 6 ptx Hseqtx).
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & prog13 & R1 & TxDes2 & R2 & Acc & RX)".
    rewrite wp_sswp.    
    iApply (mov_word _ I1 R8 with "[prog14 R8 Acc PC]"); iFrameAutoSolve.
    {
      rewrite HaddrIn.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & prog14 & Acc & R8)".
    rewrite wp_sswp.
    iApply (sub _ R5 R8 sacc with "[prog15 R5 R8 Acc PC]"); iFrameAutoSolve; auto.
    {
      rewrite HaddrIn.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & prog15 & R5 & R8 & Acc)".
    rewrite wp_sswp.
    iApply (cmp_reg _ R6 R5 with "[PC NZ prog16 R6 R5 Acc]"); iFrameAutoSolve.
    {
      rewrite HaddrIn.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & prog16 & R6 & R5 & Acc & NZ)".
    assert ((I0 <? (I3 ^- I1) ^- I1)%f = true) as ->.
    {
      rewrite /I0 /W0 /I3 /W3 /I1 /W1 //=.
    }
    rewrite wp_sswp.
    iApply (bne _ R7 with "[PC prog17 R7 Acc NZ]"); iFrameAutoSolve.
    {
      rewrite HaddrIn.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & prog17 & R7 & Acc & NZ)".
    assert ((W2 =? W1)%f = false) as ->.
    { rewrite /W2 /W1 //=. }
    iEval (rewrite Hibaseeq) in "PC".
    assert ((pprog ^+ 3)%f = (((pprog ^+ 1) ^+ 1) ^+ 1)%f) as ->.
    solve_finz.
    
    (* iter 3 *)
    
    rewrite wp_sswp.
    iApply (mov_word _ ibase R7 with "[prog4 R7 Acc PC]"); iFrameAutoSolve.
    {
      rewrite HaddrIn.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & prog4 & Acc & R7)".
    rewrite wp_sswp.
    iApply (mov_word _ I1 R0 with "[prog5 R0 Acc PC]"); iFrameAutoSolve.
    {
      rewrite HaddrIn.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & prog5 & Acc & R0)".
    rewrite wp_sswp.
    iApply (mov_word _ iprx R1 with "[prog6 R1 Acc PC]"); iFrameAutoSolve.
    {
      rewrite HaddrIn.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & prog6 & Acc & R1)".
    rewrite wp_sswp.
    iApply (@add _ _ _ _ _ _ _ _ _ _ pprog _ R1 R5 sacc with "[prog7 R1 R5 Acc PC]"); iFrameAutoSolve; auto.
    {
      rewrite <- (HaddrIn ((((((pprog ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f) at 2.
      apply in_page_to_pid_aligned.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    {
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
    }
    iModIntro.
    iIntros "(PC & prog7 & R1 & R5 & Acc)".
    rewrite wp_sswp.
    iApply (sub _ R1 R0 sacc with "[prog8 R1 R0 Acc PC]"); iFrameAutoSolve; auto.
    {
      rewrite HaddrIn.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & prog8 & R1 & R0 & Acc)".
    rewrite wp_sswp.
    rewrite Hprxeq.
    assert ((prx ^+ ((I3 ^- I1) ^- I1) ^- I1)%f = prx) as ->.
    {
      pose proof (page_spec0 prx) as prxSpec.
      assert ((2000000 - 1000)%Z = 1999000%Z) as prxSpecEq.
      lia.
      rewrite prxSpecEq in prxSpec; clear prxSpecEq.
      assert ((prx ^+ ((I3 ^- I1) ^- I1) ^- I1)%f = prx) as ->.      
      rewrite /I3 /W3 /I1 /W1 //=.
      solve_finz.
      assert (forall (f : Word) (n : Z), (n > 0)%Z ->  (((f ^+ n) ^+ 1))%f = (f ^+ (n+1)%Z)%f ) as Hplus.
      solve_finz.
      reflexivity.
    }
    iApply (ldr with "[prog9 PC Acc R2 R1 TX RxDes1]"); iFrameAutoSolve.
    {
      intro C. rewrite (to_pid_aligned_in_page _ prx) in C. done.
      apply (seq_in_page_forall1 prx 6 prx Hseqrx).
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    {
      rewrite HaddrIn.
      rewrite (to_pid_aligned_in_page _ prx).
      apply union_least; rewrite singleton_subseteq_l;
        rewrite ->elem_of_subseteq in Hacc;
        apply Hacc.
      apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      apply elem_of_union_l;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      apply (seq_in_page_forall1 prx 6 prx Hseqrx).
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & prog9 & R1 & RxDes1 & R2 & Acc & TX)".
    rewrite wp_sswp.
    iApply (mov_word _ iptx R1 with "[prog10 R1 Acc PC]"); iFrameAutoSolve.
    {
      rewrite HaddrIn.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & prog10 & Acc & R1)".
    rewrite wp_sswp.
    iApply (@add _ _ _ _ _ _ _ _ _ _ pprog _ R1 R5 sacc with "[prog11 R1 R5 Acc PC]"); iFrameAutoSolve; auto.
    {
      rewrite <- (HaddrIn ((((((((((pprog ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f) at 2.
      apply in_page_to_pid_aligned.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    {
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
    }
    iModIntro.
    iIntros "(PC & prog11 & R1 & R5 & Acc)".
    rewrite wp_sswp.
    iApply (sub _ R1 R0 sacc with "[prog12 R1 R0 Acc PC]"); iFrameAutoSolve; auto.
    {
      rewrite HaddrIn.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & prog12 & R1 & R0 & Acc)".
    rewrite wp_sswp.
    rewrite Hptxeq.
    assert ((ptx ^+ ((I3 ^- I1) ^- I1) ^- I1)%f = ptx) as ->.
    {
      pose proof (page_spec0 ptx) as ptxSpec.
      assert ((2000000 - 1000)%Z = 1999000%Z) as ptxSpecEq.
      lia.
      rewrite ptxSpecEq in ptxSpec; clear ptxSpecEq.
      assert ((ptx ^+ ((I3 ^- I1) ^- I1) ^- I1)%f = ptx) as ->.      
      rewrite /I3 /W3 /I1 /W1 //=.
      solve_finz.
      assert (forall (f : Word) (n : Z), (n > 0)%Z ->  (((f ^+ n) ^+ 1))%f = (f ^+ (n+1)%Z)%f ) as Hplus.
      solve_finz.
      reflexivity.
    }
    iApply ((str _ ptx) with "[PC prog13 R2 TxDes1 R1 Acc RX]");iFrameAutoSolve.
    {
      intro C. rewrite (to_pid_aligned_in_page _ ptx) in C. done.
      apply (seq_in_page_forall1 ptx 6 ptx Hseqtx).
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    {
      rewrite HaddrIn.
      rewrite (to_pid_aligned_in_page _ ptx).
      apply union_least; rewrite singleton_subseteq_l;
        rewrite ->elem_of_subseteq in Hacc;
        apply Hacc.
      apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      apply elem_of_union_l;
        apply elem_of_union_l;
        apply elem_of_singleton_2;
        reflexivity.
      apply (seq_in_page_forall1 ptx 6 ptx Hseqtx).
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & prog13 & R1 & TxDes1 & R2 & Acc & RX)".
    rewrite wp_sswp.    
    iApply (mov_word _ I1 R8 with "[prog14 R8 Acc PC]"); iFrameAutoSolve.
    {
      rewrite HaddrIn.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & prog14 & Acc & R8)".
    rewrite wp_sswp.
    iApply (sub _ R5 R8 sacc with "[prog15 R5 R8 Acc PC]"); iFrameAutoSolve; auto.
    {
      rewrite HaddrIn.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & prog15 & R5 & R8 & Acc)".
    rewrite wp_sswp.
    iApply (cmp_reg _ R6 R5 with "[PC NZ prog16 R6 R5 Acc]"); iFrameAutoSolve.
    {
      rewrite HaddrIn.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & prog16 & R6 & R5 & Acc & NZ)".
    assert ((I0 <? ((I3 ^- I1) ^- I1) ^- I1)%f = false) as ->.
    {
      rewrite /I0 /W0 /I3 /W3 /I1 /W1 //=.
    }
    assert ((((I3 ^- I1) ^- I1) ^- I1 <? I0)%f = false) as ->.
    {
      rewrite /I0 /W0 /I3 /W3 /I1 /W1 //=.
    }
    rewrite wp_sswp.
    iApply (bne _ R7 with "[PC prog17 R7 Acc NZ]"); iFrameAutoSolve.
    {
      rewrite HaddrIn.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & prog17 & R7 & Acc & NZ)".
    assert ((W1 =? W1)%f = true) as ->.
    { rewrite /W1 //=. }

    iDestruct "program" as "(pr1 & pr2 & pr3 & pr4 & pr5 & pr6 & pr7 & pr8 & pr9 & program)".

    (* copy receiver *)

    rewrite wp_sswp.
    iApply (mov_word _ I3 R0 with "[pr1 R0 Acc PC]"); iFrameAutoSolve.
    {
      rewrite HaddrIn.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & pr1 & Acc & R0)".
    rewrite wp_sswp.
    iApply (mov_word _ iprx R1 with "[pr2 R1 Acc PC]"); iFrameAutoSolve.
    {
      rewrite HaddrIn.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & pr2 & Acc & R1)".
    rewrite wp_sswp.
    iApply (mov_word _ I1 R2 with "[pr3 R2 Acc PC]"); iFrameAutoSolve.
    {
      rewrite HaddrIn.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & pr3 & Acc & R2)".
    rewrite wp_sswp.
    iApply (@add _ _ _ _ _ _ _ _ _ _ pprog _ R1 R0 sacc with "[pr4 R1 R0 Acc PC]"); iFrameAutoSolve; auto.
    {
      rewrite <- (HaddrIn ((((((((((((((((((((pprog ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f) at 2.
      apply in_page_to_pid_aligned.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    {
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
    }
    iModIntro.
    iIntros "(PC & pr4 & R1 & R0 & Acc)".
    rewrite wp_sswp.
    iApply (@add _ _ _ _ _ _ _ _ _ _ pprog _ R1 R2 sacc with "[pr5 R1 R2 Acc PC]"); iFrameAutoSolve; auto.
    {
      rewrite <- (HaddrIn (((((((((((((((((((((pprog ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f) at 2.
      apply in_page_to_pid_aligned.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    {
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
    }
    iModIntro.
    iIntros "(PC & pr5 & R1 & R2 & Acc)".
    assert (((iprx ^+ I3) ^+ I1)%f = ((((prx ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f) as ->.
    {
      rewrite Hprxeq.
      rewrite /I3 /W3 /I1 /W1 //=.
      solve_finz.
    }
    rewrite wp_sswp.
    iApply (ldr with "[pr6 PC Acc R3 R1 TX RxDes5]"); iFrameAutoSolve.
    {
      intro C. rewrite (to_pid_aligned_in_page _ prx) in C. done.
      apply (seq_in_page_forall1 prx 6 prx Hseqrx).
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    {
      rewrite HaddrIn.
      rewrite (to_pid_aligned_in_page _ prx).
      apply union_least; rewrite singleton_subseteq_l;
        rewrite ->elem_of_subseteq in Hacc;
        apply Hacc.
      apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      apply elem_of_union_l;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      apply (seq_in_page_forall1 prx 6 prx Hseqrx).
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & pr6 & R1 & RxDes5 & R3 & Acc & TX)".
    rewrite wp_sswp.
    iApply (mov_word _ iptx R1 with "[pr7 R1 Acc PC]"); iFrameAutoSolve.
    {
      rewrite HaddrIn.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & pr7 & Acc & R1)".
    rewrite wp_sswp.
    iApply (@add _ _ _ _ _ _ _ _ _ _ pprog _ R1 R0 sacc with "[pr8 R1 R0 Acc PC]"); iFrameAutoSolve; auto.
    {
      rewrite <- (HaddrIn ((((((((((((((((((((((((pprog ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1)
               ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1) ^+ 1)%f) at 2.
      apply in_page_to_pid_aligned.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    {
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
    }
    iModIntro.
    iIntros "(PC & pr8 & R1 & R0 & Acc)".
    rewrite wp_sswp.
    assert ((iptx ^+ I3)%f = (((ptx ^+ 1) ^+ 1) ^+ 1)%f) as ->.
    {
      rewrite Hptxeq.
      rewrite /I3 /W3 //=.
      solve_finz.
    }
    iApply ((str _ (((ptx ^+ 1) ^+ 1) ^+ 1)%f) with "[PC pr9 R3 TxDes4 R1 Acc RX]");iFrameAutoSolve.
    {
      intro C. rewrite (to_pid_aligned_in_page _ ptx) in C. done.
      apply (seq_in_page_forall1 ptx 6 ptx Hseqtx).
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    {
      rewrite HaddrIn.
      rewrite (to_pid_aligned_in_page _ ptx).
      apply union_least; rewrite singleton_subseteq_l;
        rewrite ->elem_of_subseteq in Hacc;
        apply Hacc.
      apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      apply elem_of_union_l;
        apply elem_of_union_l;
        apply elem_of_singleton_2;
        reflexivity.
      apply (seq_in_page_forall1 ptx 6 ptx Hseqtx).
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & pr9 & R1 & TxDes4 & R3 & Acc & RX)".
    
    (* retrieve and change *)

    iDestruct "program" as "(p1 & p2 & p3 & p4 & p5 & p6 & p7 & p8 & p9 & p10 & p11 & p12 & p13 & p14 & p15 & p16 & p17 & p18 & p19 & p20 & p21 & p22 & _)".

    rewrite wp_sswp.
    iApply (mov_word _ (encode_hvc_func Poll) R0 with "[p1 R0 Acc PC]"); iFrameAutoSolve.
    {
      rewrite HaddrIn.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & p1 & Acc & R0)".
    rewrite wp_sswp.    
    iApply (poll _ V1 (p := pprog) with "[PC R0 R1 R2 p2 Acc RX']"); iFrameAutoSolve; auto.
    {
      apply decode_encode_hvc_func.
    }
    {
      rewrite <- (HaddrIn (incrN pprog 27)%f) at 2.
      rewrite /incrN.
      apply in_page_to_pid_aligned.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    {
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
    }
    iModIntro.
    iIntros "(PC & R0 & R1 & R2 & p2 & Acc & RX')".    
    rewrite wp_sswp.
    iApply (mov_word _ (encode_hvc_func Retrieve) R0 with "[p3 R0 Acc PC]"); iFrameAutoSolve.
    {
      rewrite HaddrIn.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & p3 & Acc & R0)".
    rewrite wp_sswp.
    iApply (mov_word _ I3 R1 with "[p4 R1 Acc PC]"); iFrameAutoSolve.
    {
      rewrite HaddrIn.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & p4 & Acc & R1)".
    rewrite wp_sswp.
    iApply (mov_word _ I1 R2 with "[p5 R2 Acc PC]"); iFrameAutoSolve.
    {
      rewrite HaddrIn.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & p5 & Acc & R2)".
    rewrite wp_sswp.
    iApply (@add _ _ _ _ _ _ _ _ _ _ pprog _ R1 R2 sacc with "[p6 R1 R2 Acc PC]"); iFrameAutoSolve; auto.
    {
      rewrite <- (HaddrIn (incrN pprog 31)%f) at 2.
      rewrite /incrN.
      apply in_page_to_pid_aligned.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    {
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
    }
    iModIntro.
    iIntros "(PC & p6 & R1 & R2 & Acc)".
    assert ((I3 ^+ I1)%f = I4) as ->.
    {
      rewrite /I3 /W3 /I4 /W4 /I1 /W1 //=.
      solve_finz.
    }
    iAssert (mem_region [of_imm (encode_vmid V0); W0; h'; of_imm (encode_vmid V1)] ptx)%I with "[TxDes1 TxDes2 TxDes3 TxDes4]" as "memdes".
    {
      rewrite /mem_region.
      simpl.
      iFrame.
    }
    iAssert (∃l, mem_region l prx ∗ ⌜ length l = 6 ⌝)%I with "[RxDes1 RxDes2 RxDes3 RxDes4 RxDes5 RxDes6]" as "memdes'".
    {
      iExists [of_imm (encode_vmid V0); W0; h'; W1; of_imm (encode_vmid V1); of_pid ppage].
      rewrite /mem_region.
      simpl.
      iFrame.
      done.
    }
    rewrite wp_sswp.
    iApply (hvc_retrieve_lend (wf' := W0) (destx := [of_imm (encode_vmid V0); W0; h'; of_imm (encode_vmid V1)]) (pi := pprog) (spsd := list_to_set [ppage]) (l := I1) _ _ _ h' W0 [ppage] with "[R0 PC Acc p7 Hretri R1 Htrans' Own Excl TX memdes memdes' RX RX']"); iFrameAutoSolve; auto.
    {
      rewrite <- (HaddrIn (incrN pprog 32)%f) at 2.
      rewrite /incrN.
      apply in_page_to_pid_aligned.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    {
      apply decode_encode_hvc_func.
    }
    {
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
    }
    {
      rewrite list_to_set_singleton.
      rewrite disjoint_singleton_l.
      assumption.
    }
    {
      rewrite list_to_set_singleton.
      rewrite disjoint_singleton_l.
      assumption.
    }
    {
      rewrite list_to_set_singleton.
      rewrite disjoint_singleton_l.
      assumption.
    }
    {
      simpl.
      apply (seq_in_page_append1 ptx 4 6 ptx); [lia|lia|assumption].
    }
    {
      iFrame.
    }
    iModIntro.
    iIntros "(PC & p7 & R0 & R1 & Own & Excl & Acc & TX & memdes & RX & RX' & memdes' & Htrans' & Hretri)".
    rewrite wp_sswp.
    iApply (mov_word _ ippage R1 with "[p8 R1 Acc PC]"); iFrameAutoSolve.
    {
      rewrite HaddrIn.
      apply elem_of_union_l.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & p8 & Acc & R1)".
    rewrite wp_sswp.
    iApply (mov_word _ I1 R0 with "[p9 R0 Acc PC]"); iFrameAutoSolve.
    {
      rewrite HaddrIn.
      apply elem_of_union_l.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & p9 & Acc & R0)".
    rewrite wp_sswp.
    rewrite Hppageeq.
    iApply ((str _ ppage) with "[PC p10 R1 page R0 Acc RX]"); iFrameAutoSolve.
    {
      intro C.
      apply Hppagenot'.
      symmetry.
      rewrite to_pid_aligned_eq in C.
      assumption.
    }
    {
      rewrite HaddrIn.
      apply union_mono.
      apply singleton_subseteq_l.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      rewrite to_pid_aligned_eq.
      rewrite list_to_set_singleton.
      apply singleton_subseteq_l.
      apply elem_of_singleton_2.
      reflexivity.
      simpl.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & p10 & R1 & page & R0 & Acc & RX)".
    rewrite wp_sswp.
    iApply (mov_word _ iprx R1 with "[p11 R1 Acc PC]"); iFrameAutoSolve.
    {
      rewrite HaddrIn.
      apply elem_of_union_l.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & p11 & Acc & R1)".
    rewrite Hprxeq.
    rewrite wp_sswp.
    iApply (mov_word _ I2 R0 with "[p12 R0 Acc PC]"); iFrameAutoSolve.
    {
      rewrite HaddrIn.
      apply elem_of_union_l.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & p12 & Acc & R0)".
    rewrite wp_sswp.
    iApply (@add _ _ _ _ _ _ _ _ _ _ pprog _ R1 R0 (sacc ∪ list_to_set [ppage]) with "[p13 R1 R0 Acc PC]"); iFrameAutoSolve; auto.
    {
      rewrite <- (HaddrIn (incrN pprog 38)%f) at 2.
      rewrite /incrN.
      apply in_page_to_pid_aligned.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    {
      apply elem_of_union_l.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
    }
    iModIntro.
    iIntros "(PC & p13 & R1 & R0 & Acc)".
    iEval (simpl) in "memdes'".
    iDestruct "memdes'" as "(rx1 & rx2 & rx3 & memdes')".
    assert ((prx ^+ I2)%f = ((prx ^+ 1) ^+ 1)%f) as ->.
    {
      rewrite /I2 /W2 //=.
      solve_finz.
    }
    rewrite wp_sswp.
    iApply (ldr with "[p14 PC Acc R0 R1 TX rx3]"); iFrameAutoSolve.
    {
      intro C. rewrite (to_pid_aligned_in_page _ prx) in C. done.
      apply (seq_in_page_forall1 prx 6 prx Hseqrx).
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    {
      rewrite HaddrIn.
      rewrite (to_pid_aligned_in_page _ prx).
      apply union_subseteq_l'.
      apply union_least; rewrite singleton_subseteq_l;
        rewrite ->elem_of_subseteq in Hacc;
        apply Hacc.
      apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      apply elem_of_union_l;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      apply (seq_in_page_forall1 prx 6 prx Hseqrx).
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & p14 & R1 & rx3 & R0 & Acc & TX)".
    rewrite wp_sswp.
    iApply (mov_word _ iptx R1 with "[p15 R1 Acc PC]"); iFrameAutoSolve.
    {
      rewrite HaddrIn.
      apply elem_of_union_l.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & p15 & Acc & R1)".
    rewrite wp_sswp.
    iDestruct "memdes" as "(tx1 & memdes)".
    rewrite Hptxeq.
    iApply ((str _ ptx) with "[PC p16 R1 tx1 R0 Acc RX]"); iFrameAutoSolve.
    {
      intro C.
      apply Hppagenot'.
      symmetry.
      rewrite to_pid_aligned_eq in C.
      contradiction.
    }
    {
      rewrite HaddrIn.
      apply union_subseteq_l'.
      rewrite to_pid_aligned_eq.
      apply union_least; rewrite singleton_subseteq_l.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_l;
        apply elem_of_union_l;
        apply elem_of_singleton_2;
        reflexivity.
      simpl.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & p16 & R1 & tx1 & R0 & Acc & RX)".
    rewrite wp_sswp.
    iApply (mov_word _ (encode_hvc_func Relinquish) R0 with "[p17 R0 Acc PC]"); iFrameAutoSolve.
    {
      rewrite HaddrIn.
      apply elem_of_union_l.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & p17 & Acc & R0)".
    rewrite wp_sswp.
    iDestruct "memdes" as "(tx2 & memdes)".
    iAssert (mem_region [h'; W0] ptx) with "[tx1 tx2]" as "memdes''".
    {
      iFrame.
      done.
    }
    iApply (hvc_relinquish_nz _ _ h' W0 [ppage] (des := [h'; W0]) (pi := pprog) (spsd := list_to_set [ppage]) (tt := Lending) (j := V0) with "[PC p18 R0 Acc Excl TX memdes'' Htrans' Hretri]"); iFrameAutoSolve.
    {
      rewrite <- (HaddrIn (incrN pprog 43)%f) at 2.
      rewrite /incrN.
      apply in_page_to_pid_aligned.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    {
      apply decode_encode_hvc_func.
    }
    {
      apply elem_of_union_l.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
    }
    {
      reflexivity.
    }
    {
      simpl.
      apply (seq_in_page_append1 ptx 2 6 ptx); [lia|lia|assumption].
    }
    {
      reflexivity.
    }
    {
      rewrite list_to_set_singleton.
      apply singleton_subseteq_l.
      apply elem_of_union_r.
      apply elem_of_singleton_2.
      reflexivity.
    }
    {
      left.
      split; auto.
      rewrite list_to_set_singleton.
      apply singleton_subseteq_l.
      apply elem_of_union_r.
      apply elem_of_singleton_2.
      reflexivity.
    }
    {
      iFrame.
    }
    iModIntro.
    iIntros "(PC & p18 & Excl & Acc & R0 & Htrans' & Hretri & TX & memdes'')".
    rewrite wp_sswp.
    iApply (mov_word _ (encode_hvc_func Poll) R0 with "[p19 R0 Acc PC]"); iFrameAutoSolve.
    {
      simpl.
      assert ((sacc ∪ ({[ppage]} ∪ ∅)) ∖ ({[ppage]} ∪ ∅) = sacc) as ->.
      set_solver.
      rewrite HaddrIn.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & p19 & Acc & R0)".
    rewrite wp_sswp.
    iApply (poll _ V1 (p := pprog) with "[PC R0 R1 R2 p20 Acc RX']"); iFrameAutoSolve; auto.
    {
      apply decode_encode_hvc_func.
    }
    {
      rewrite <- (HaddrIn (incrN pprog 45)%f) at 2.
      rewrite /incrN.
      apply in_page_to_pid_aligned.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    {
      simpl.
      assert ((sacc ∪ ({[ppage]} ∪ ∅)) ∖ ({[ppage]} ∪ ∅) = sacc) as ->.
      set_solver.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
    }
    iModIntro.
    iIntros "(PC & R0 & R1 & R2 & p20 & Acc & RX')".    
    rewrite wp_sswp.
    iApply (mov_word _ (encode_hvc_func Yield) R0 with "[p21 R0 Acc PC]"); iFrameAutoSolve.
    {
      simpl.
      assert ((sacc ∪ ({[ppage]} ∪ ∅)) ∖ ({[ppage]} ∪ ∅) = sacc) as ->.
      set_solver.
      rewrite HaddrIn.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    iModIntro.
    iIntros "(PC & p21 & Acc & R0)".
    rewrite wp_sswp.
    iApply (sswp_fupd_around _ ⊤ (⊤ ∖ ↑ inv_name) ⊤).
    iInv inv_name as ">Inv" "HIClose".
    iDestruct "Inv" as (i P cb ob oh) "(ScheToken & NaInvToken & InvExact & Hmatch)".
    iDestruct (inv_state_exact_atleast with "InvExact InvAtLeast") as "%Rel".
    destruct (decide (i = V1)).
    2 : {
      iApply (eliminate_wrong_token with "ScheToken").
      done.
      iModIntro.
      iNext.
      iIntros "[_ False]".
      iExFalso.
      done.
    }
    simplify_eq.
    iEval (simpl) in "Hmatch".
    pose proof Rel as Rel'.    
    apply inv_sts_1_unclosed_changed_yield in Rel'.
    destruct Rel' as [-> [-> ->]].
    iDestruct "Hmatch" as "(-> & Switched)".
    iDestruct ((nainv_state_update _ _ (true, Some h')) with "NaInvExact") as ">NaInvExact".
    { unfold inv_sts_rel. apply rtc_once. constructor. }
    iDestruct (nainv_state_observe with "NaInvExact") as ">[NaInvExact NaInvAtLeast']".
    iApply (yield (z := V0) with "[PC p22 ScheToken Acc R0 HR0 HR1]"); iFrameAutoSolve.
    {
      simpl.
      assert ((sacc ∪ ({[ppage]} ∪ ∅)) ∖ ({[ppage]} ∪ ∅) = sacc) as ->.
      set_solver.
      rewrite HaddrIn.
      rewrite ->elem_of_subseteq in Hacc;
        apply Hacc;
        apply elem_of_union_r;
        apply elem_of_singleton_2;
        reflexivity.
      repeat (first [apply elem_of_list_here | apply elem_of_list_further]).
    }
    {
      solve_finz.
    }
    {
      apply decode_encode_hvc_func.
    }
    {
      iFrame.
    }
    iModIntro.
    iModIntro.
    iIntros "(ScheToken & PC & p22 & Acc & R0 & HR0 & HR1)".
    iDestruct ("NaInvClose" with "[NaInvToken NaInvExact R0 page RX' Switched HUnchanged HR0 HR1 Htrans' Hretri]") as "NaInvToken".
    { iSplitR "NaInvToken".
      iNext.
      rewrite /nainv_def.
      iExists yield_I, yield_I, (encode_vmid V1), W1, [], true, (Some h').
      iFrame.
      iFrame.
      iSplitL "".
      rewrite /mem_region.
      simpl.
      done.
      done.
      unfold nainv_closed.
      iFrame.
    }
    iMod "NaInvToken".    
    iDestruct ((inv_state_update _ _ (V0, false, true, Some h')) with "InvExact") as ">InvExact".
    { unfold inv_sts_rel. apply rtc_once. constructor. }
    iDestruct (inv_state_observe with "InvExact") as ">(InvExact & InvAtLeast')".
    iDestruct ("HIClose" with "[ScheToken NaInvToken InvExact NaInvAtLeast' Done]") as "InvClose".
    { iExists V0, ⊤, false, true , (Some h'). iNext. iFrame. done. }
    iMod "InvClose" as %_.
    iModIntro.
    rewrite wp_sswp.
    iApply (sswp_fupd_around V1 ⊤ (⊤ ∖ ↑inv_name) ⊤).
    iInv inv_name as ">Inv" "HIClose".
    iDestruct "Inv" as (i P cb ob oh) "(ScheToken & NaInvToken & InvExact & Hmatch)".
    destruct (decide (i = V1)).
    2 : {
      iApply (eliminate_wrong_token with "ScheToken").
      done.
      iModIntro.
      iNext.
      iIntros "[_ False]".
      iExFalso.
      done.
    }
    simplify_eq.
    iSimpl in "Hmatch".
    clear Rel.
    iDestruct (inv_state_exact_atleast with "InvExact InvAtLeast'") as "%Rel".
    pose proof Rel as Rel'.
    iExFalso.
    iPureIntro.
    rewrite /inv_sts_rel in Rel'.
    do 3 (apply rtc_inv in Rel';
          destruct Rel' as [? | [x Rel']]; first discriminate;
          destruct Rel' as [Rel1 Rel2];
          inversion Rel1; subst;
          clear Rel1;
          rename Rel2 into Rel').
  Qed.  

  Lemma lending_proof {sown0 qo0 sacc0 sexcl0 sh qo1 sacc1 sown1 sexcl1}
             (ppage pprog0 pprog1 ptx0 ptx1 prx0 prx1: PID)
             (* ppage is the page to lend *)
             (ippage iptx1 iprx1 ibase : Imm)
             (* ibase is the base addr of the loop body *)
             (Hppageeq : of_pid ppage = ippage)
             (* (Hibaseeq : of_imm ibase = (pprog1 ^+ 3)%f) *)
             (Hnotrx0: ppage ≠ prx0)
             (Hnotrx1: ppage ≠ prx1)
             (Hnotrx0': prx0 ≠ ptx0)
             (Hnottxrx: prx1 ≠ ptx1)
             (* the des in TX *)
             (des : list Word)
             (Hdeseq : des = serialized_transaction_descriptor V0 V1 W0 W1 [ppage] W0)
             (* ilen is the length of msg *)
             (ilen : Imm)
             (Hileq : (finz.to_z ilen) = Z.of_nat (length des))
             (* the whole program is in page pprog *)
             (Hseq0 : seq_in_page pprog0 (length (code0 ippage ilen)) pprog0)
             (* has access to all involved pages *)
             (Hacc0 : {[ppage; pprog0; ptx1]} ⊆ sacc0)
             (* at least owns ppage *)
             (Hown0 : ppage ∈ sown0)
             (* at least has exclusive access to ppage *)
             (Hexcl0 : ppage ∈ sexcl0)
             (* the handle pool is not empty *)
             (Hsh : sh ≠ ∅)
             (γ_invm γ_nainvm γ_closed γ_access γ_done γ_unchanged γ_switched : gname)
             (* cannot have access to ppage *)
             (* has access to RX, TX, and pprog *)
             (Hacc1 : {[ptx1;prx1;pprog1]} ⊆ sacc1)
             (HaccNotIn: ppage ∉ sacc1)
             (HownNotIn: ppage ∉ sown1)
             (HexclNotIn: ppage ∉ sexcl1)
             (* the whole program is in page pprog *)
             (Hseq1 : seq_in_page pprog1 (length (code1 I3 ibase iprx1 iptx1 ippage)) pprog1) :
    PC @@ V0 ->r pprog0
    ∗ hp{ 1 }[ sh ]
    ∗ O@V0 :={qo0}[sown0]
    ∗ A@V0 :={1}[sacc0]
    ∗ E@V0 :={1}[sexcl0]
    ∗ TX@V0 := ptx0
    ∗ RX@V0 := prx0
    ∗ RX@V1 := prx1
    ∗ mem_region des ptx0
    ∗ (∃ r2, R2 @@ V0 ->r r2)
    ∗ R3 @@ V0 ->r (ptx0 ^+ 2)%f
    ∗ program (code0 ippage ilen) pprog0
    (*invariants and ghost variables *)
    ∗ inv inv_name (inv_def γ_invm γ_nainvm γ_closed γ_access γ_done γ_unchanged γ_switched)
    ∗ nainv nainv_name (nainv_def γ_nainvm γ_access γ_done γ_unchanged γ_switched prx1 ppage)
    ∗ token γ_done
    ∗ token γ_closed
    ∗ token γ_access
    ∗ token γ_unchanged
    ∗ inv_state_atleast γ_invm (V0,false,false, None)
    ∗ PC @@ V1 ->r pprog1
    ∗ A@V1 :={1}[sacc1]
    ∗ TX@V1 := ptx1
    ∗ RX@V1 := prx1
    ∗ (∃ des', mem_region des' ptx1 ∗ ⌜length des'= 6⌝)
    ∗ (∃ r, NZ @@ V1 ->r r)             
    ∗ (∃ r, R1 @@ V1 ->r r)
    ∗ (∃ r, R2 @@ V1 ->r r)
    ∗ (∃ r, R3 @@ V1 ->r r)
    ∗ (∃ r, R5 @@ V1 ->r r)
    ∗ (∃ r, R6 @@ V1 ->r r)
    ∗ (∃ r, R7 @@ V1 ->r r)
    ∗ (∃ r, R8 @@ V1 ->r r)
    ∗ O@V1:={qo1}[sown1]
    ∗ E@V1:={1}[sexcl1]
    ∗ program (code1 I3 ibase iprx1 iptx1 ippage) pprog1
    (*invariants and ghost variables *)
    ∗ token γ_switched
    ⊢ WP ExecI @ V0
      {{ (λ m, ⌜m = HaltI⌝ ∗
          PC @@ V0 ->r (pprog0 ^+ (length (code0 ippage ilen)))%f
          ∗ hp{ 1 }[ sh ]
          ∗ O@V0 :={qo0}[sown0]
          ∗ A@V0 :={1}[sacc0]
          ∗ E@V0 :={1}[sexcl0]
          ∗ TX@V0:=ptx0
          ∗ RX@V0:=prx0
          ∗ RX@V1:=prx1
          ∗ (∃ des, mem_region des ptx0)
          ∗ R2 @@ V0 ->r ilen
          ∗ (∃ r3, R3 @@ V0 ->r r3)
          ∗ token γ_closed
          ∗ program (code0 ippage ilen) pprog0)
      }}∗ 
      WP ExecI @ V1
      {{ λ m, ⌜m = ExecI⌝ ∗ False%I }}.
Proof.
Admitted.

End proof.
