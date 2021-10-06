From iris.bi Require Import derived_laws_later.
From machine_program_logic.program_logic Require Import weakestpre.
From iris.staging Require Import monotone.
From HypVeri.algebra Require Import base mem.
From HypVeri.rules Require Import rules_base.
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
    Str R1 R0;
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
    Str R3 R2;
    (* send tx to VM1 *)
    (* tx -> memory descriptor *des* with h *)
    (* R3 -> address of a handle in *des* *)
    (* R1 -> p *)
    (* R0 -> Succ *)
    (* p -> 0 *)
    (* R2 -> h *)
    (* h ->  transaction entry *)
    Mov R0 (inl (encode_hvc_func Send));
    Mov R1 (inl I1);
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
    Ldr R1 R3;
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

  (* program of VM1
    l is the length of the message
   ibase is the base address of the loop body
   iprx and iptx are the PIDs of RX and TX pages of VM1
   ipage is the PID of the page to lend *)
  (* TODO: VM1 knows l via msg_wait/poll *)
  Definition code1 (l : Imm) (ibase : Imm) (iprx iptx : Imm) (ipage: Imm) : list Word :=
    encode_instructions
    [
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
    Sub R1 R5;
    Str R1 R2;

    (* loop end *)
    Mov R8 (inl I1);
    Sub R5 R8;
    Cmp R6 (inr R5);
    Bne R7;

    (* tx -> descriptor *)
    (* h -> transaction entry *)
    (* h -> not taken *)
    Mov R0 (inl (encode_hvc_func Retrieve));
    Mov R1 (inl l);
    Hvc;
    (* tx -> descriptor *)
    (* h -> transaction entry *)
    (* h -> taken *)
    (* store a new value *)
    Mov R1 (inl ipage);
    Mov R0 (inl I1);
    Str R1 R0;
    (* tx -> descriptor *)
    (* h -> transaction entry *)
    (* h -> taken *)
    (* p -> 1 *)
    (* prepare a new retrieve descriptor [h, 0] *)
    (* copy h from rx + 1 to tx + 0 *)
    Mov R1 (inl iprx);
    Mov R0 (inl I1);
    Add R1 R0;
    Ldr R0 R1;
    Mov R1 (inl iptx);
    Str R1 R0;
    (* relinquish *)
    Mov R0 (inl (encode_hvc_func Relinquish));
    Hvc;
    (* poll *)
    Mov R0 (inl (encode_hvc_func Poll));
    Hvc;
    (* yield *)
    Mov R0 (inl yield_I);
    Hvc
    ].


  (** STSs **)
  (* the STS used in the invariant
     VMID is the VMID of the currently running VM
     coPoset is the set of names of na invariants that can be open
     bool indicates if the value in lent page has been changed
   *)

  Section sts.
    Context {ι:namespace}.


  Definition inv_sts_state: Type := VMID * coPset * bool.

  Inductive inv_sts_base : relation inv_sts_state :=
  | inv_sts_base_0_closed_unchanged_open : inv_sts_base (V0, ⊤, false) (V0, ⊤ ∖↑ ι, false)
  | inv_sts_base_0_unclosed_unchanged_switch : inv_sts_base (V0, ⊤ ∖↑ ι, false) (V1, ⊤, false)
  | inv_sts_base_1_closed_unchanged_change : inv_sts_base (V1, ⊤, false) (V1, ⊤ ∖↑ ι, true)
  | inv_sts_base_1_unclosed_changed_switch : inv_sts_base (V1, ⊤ ∖↑ ι, true) (V0, ⊤, true)
  | inv_sts_base_0_closed_changed_open : inv_sts_base (V0, ⊤, true) (V0, ⊤ ∖↑ ι, true).


  Definition inv_sts_rel := rtc inv_sts_base.

  Lemma inv_sts_0_closed_unchanged_open s : inv_sts_rel (V0, ⊤, false) s ->
    (s.1.1= V0 ∨ s.1.1 = V1) ∧ (s.1.2 =⊤ ∨ s.1.2 = ⊤∖↑ ι) ∧ (s.2 =  false ∨ s.2 = true).
  Proof.
    intro.
    pattern s.
    eapply (rtc_ind_r _ (V0,⊤,false)).
    - split;[|split];left;done.
    - intros.
      Unshelve.
      2: { exact inv_sts_base. }
      destruct H2.
      destruct H2, H3;destruct y as [ []];simpl in *;inversion H1;subst;cbn;
      split;eauto.
    - done.
  Qed.

  Lemma inv_sts_0_unclosed_unchanged_switch  s :
    inv_sts_rel (V0, ⊤∖↑ι, false) s ->
    (s.2 = true -> (s.1.1= V0 ∨ s.1.1 = V1) ∧ (s.1.2 =⊤ ∨ s.1.2 = ⊤∖↑ ι)) ∧ (s.2 =false -> s.1.1= V0 ∧ s.1.2 = ⊤∖↑ ι ∨ s.1.1 = V1 ∧ s.1.2 =⊤).
  Proof.
    intro.
    pattern s.
    eapply (rtc_ind_r _ (V0,⊤∖↑ι,false)).
    - split.
      intro;done.
      intro.
      left; done.
    - intros.
      Unshelve.
      2: { exact inv_sts_base. }
      destruct H2.
      destruct y as [ []];simpl in *;inversion H1;subst;cbn;
      split;eauto.
      intro;done.
      intro;done.
    - done.
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
  Class invStsG Σ := invSts_G :> inG Σ (authUR (mraUR (@inv_sts_rel nainv_name) )).
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
    inv_state_exact γ s -∗ inv_state_atleast γ s' -∗ ⌜@inv_sts_rel nainv_name s' s⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[Hincl ?]%auth_both_valid_discrete.
    revert Hincl; rewrite principal_included; done.
  Qed.

  Lemma inv_state_update γ s s' :
    @inv_sts_rel nainv_name s s' → inv_state_exact γ s ==∗ inv_state_exact γ s'.
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

  Definition inv_def γ_invm γ_nainvm γ_closed γ_access γ_done γ_unchanged γ_switched : iProp Σ:=
    ∃ (i : VMID) P b, <<i>>{ 1%Qp } ∗ nainv_closed P ∗ inv_state_exact γ_invm (i,P,b) ∗
    (if b then True else token γ_unchanged) ∗
    (match (fin_to_nat i,b) with
    | (0, false) => (⌜P = ⊤⌝ → token γ_access ∗ nainv_state_atleast γ_nainvm (b, None)) ∗
                    (⌜P = ⊤ ∖↑ nainv_name⌝ → token γ_closed)
    | (0, true) =>  (⌜P = ⊤⌝ → token γ_done ∗
                    ∃ h, nainv_state_atleast γ_nainvm (b, Some h)) ∗
                    (⌜P = ⊤ ∖↑ nainv_name⌝ → token γ_closed ∗ token γ_access)
    | (1, false) => (⌜P = ⊤⌝ → token γ_done ∗
                    ∃ h, nainv_state_atleast γ_nainvm (b, Some h))
    | (1, true) =>  (⌜P = ⊤ ∖ ↑ nainv_name⌝ → token γ_switched)
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
    | (true, None) => ⌜r0 = W1⌝ ∗ ⌜r0' = of_imm yield_I⌝ ∗ ⌜r1 = W1⌝ ∗
                      token γ_done
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
             (ppage pprog ptx prx: PID)
             (* the page to lend *)
             (ippage : Imm)
             (Hppageeq : of_pid ppage = ippage)
             (* the des in TX *)
             (des : list Word)
             (Hdeseq : des = serialized_transaction_descriptor V0 V1 W0 I1 [ppage] W0)
             (* ilen is the length of msg *)
             (ilen : Imm)
             (Hileq : Z.to_nat (finz.to_z ilen) = length des)
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
    ∗ RX@V1 := prx
    ∗ mem_region des ptx
    ∗ (∃ r2, R2 @@ V0 ->r r2)
    ∗ R3 @@ V0 ->r (ptx ^+ 2)%f
    ∗ (∃ w, ppage ->a w)
    ∗ program (code0 ippage ilen) pprog
    (*invariants and ghost variables *)
    ∗ inv inv_name (inv_def γ_invm γ_nainvm γ_closed γ_access γ_done γ_unchanged γ_switched)
    ∗ nainv nainv_name (nainv_def γ_nainvm γ_access γ_done γ_unchanged γ_switched prx ppage)
    ∗ token γ_done
    ∗ token γ_closed
    ∗ inv_state_atleast γ_invm (V0,⊤,false)
    ⊢ WP ExecI @ V0
      {{ (λ m, ⌜m = HaltI⌝ ∗
          PC @@ V0 ->r (pprog ^+ (length (code0 ippage ilen)))%f
          ∗ hp{ 1 }[ sh ]
          ∗ O@V0 :={qo}[sown]
          ∗ A@V0 :={1}[sacc]
          ∗ E@V0 :={1}[sexcl]
          ∗ TX@V0 := ptx
          (* ∗ ∃ h, ⌜des' = serialized_transaction_descriptor V0 V1 h I1 [ppage] W0⌝ *)
          ∗ (∃ des, mem_region des ptx)
          ∗ R2 @@ V0 ->r ilen
          ∗ R3 @@ V0 ->r (ptx ^+ 2)%f
          ∗ program (code0 ippage ilen) pprog)
      }}.
  Proof.
    iIntros  "(PC & hp & Own & Acc & Excl & TX & RX & des & [% R2] & R3 & [% page] & prog & #Hinv & #Hnainv & Done & Closed & InvAtLeast)".
    iDestruct "prog" as "[prog1 prog]".
    iApply wp_sswp.
    (* open the invriant *)
    iApply (sswp_fupd_around _ ⊤ (⊤ ∖ ↑ inv_name) ⊤).
    iInv inv_name as ">Inv" "HIClose".
    iDestruct "Inv" as (i P b) "(ScheToken & NaInvToken & InvExact & Hif & Hmatch)".
    iDestruct (inv_state_exact_atleast with "InvExact InvAtLeast") as "%Rel".
    apply inv_sts_0_closed_unchanged_open in Rel.
    simpl in Rel.
    destruct Rel as [[->| ->] [[-> | ->] [-> | ->]]];iSimpl in "Hmatch".
    2: { admit. }
    3: { admit. }

    4: { iApply (eliminate_wrong_token with "ScheToken").
         admit.

         iModIntro.
         iNext.
         iIntros "[_ False]".
         iExFalso.
         done.
}
    5: { iApply (eliminate_wrong_token with "ScheToken").
         admit.

         iModIntro.
         iNext.
         iIntros "[_ False]".
         iExFalso.
         done.
    }
    4: { admit. }

    3: { admit. }
    2: { admit. }
Admitted.

  Lemma machine1_proof {sacc}
             (ppage pprog ptx prx : PID)
             (ippage iptx iprx : Imm)
             (* ibase is the base addr of the loop body *)
             (ibase : Imm)
             (Hibaseeq : of_imm ibase = (pprog ^+ 3)%f)
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
             (* the whole program is in page pprog *)
             (Hseq : seq_in_page pprog (length (code1 ilen ibase iprx iptx ippage)) pprog)
             (γ_invm γ_nainvm γ_closed γ_access γ_done γ_unchanged γ_switched : gname) :
    PC @@ V1 ->r pprog
    ∗ A@V1 :={1}[sacc]
    ∗ TX@ V1 := ptx
    ∗ RX@V1 := prx
    ∗ (∃ des', mem_region des' ptx ∗ ⌜length des'= nlen⌝)
    ∗ (∃ r, R1 @@ V1 ->r r)
    ∗ (∃ r, R2 @@ V1 ->r r)
    ∗ (∃ r, R5 @@ V1 ->r r)
    ∗ (∃ r, R6 @@ V1 ->r r)
    ∗ (∃ r, R7 @@ V1 ->r r)
    ∗ (∃ r, R8 @@ V1 ->r r)
    ∗ program (code1 ilen ibase iprx iptx ippage) pprog
    (*invariants and ghost variables *)
    ∗ inv inv_name (inv_def γ_invm γ_nainvm γ_closed γ_access γ_done γ_unchanged γ_switched)
    ∗ nainv nainv_name (nainv_def γ_nainvm γ_access γ_done γ_unchanged γ_switched prx ppage)
    ∗ token γ_switched
    ∗ inv_state_atleast γ_invm (V0,⊤,false)
    ⊢ WP ExecI @ V1
    {{ λ m, ⌜m = ExecI⌝ ∗
        True
          (* PC @@ V1 ->r (pprog ^+ (length (code1 ilen ibase iprx iptx ippage)))%f *)
          (* ∗ A@V1 :={1}[sacc] *)
          (* ∗ TX@ V1 := ptx *)
          (* ∗ (∃ des', mem_region des' ptx ∗ ⌜length des'= length des⌝) *)
          (* ∗ (∃ r, R1 @@ V1 ->r r) *)
          (* ∗ (∃ r, R2 @@ V1 ->r r) *)
          (* ∗ (∃ r, R5 @@ V1 ->r r) *)
          (* ∗ (∃ r, R6 @@ V1 ->r r) *)
          (* ∗ (∃ r, R7 @@ V1 ->r r) *)
          (* ∗ (∃ r, R8 @@ V1 ->r r) *)
          (* ∗ program (code1 ilen ibase iprx iptx ippage) pprog *)
    }}.
  Proof.
    iIntros "(PC & Acc & TX & RX & [% [mrdes %mrdesEq]] & R1 & R2 & R5 & R6 & R7 & R8 & program & #Hinv & #Hainv & HSwitched & InvAtLeast)".
    iDestruct "program" as "[prog1 program]".
    iApply wp_sswp.
    (* open the invriant *)
    iApply (sswp_fupd_around _ ⊤ (⊤ ∖ ↑ inv_name) ⊤).
    iInv inv_name as ">Inv" "HIClose".
    iDestruct "Inv" as (i P b) "(ScheToken & NaInvToken & InvExact & Hif & Hmatch)".
    iDestruct (inv_state_exact_atleast with "InvExact InvAtLeast") as "%Rel".
    apply inv_sts_0_closed_unchanged_open in Rel.
    simpl in Rel.
    destruct Rel as [[->| ->] [[-> | ->] [-> | ->]]];iSimpl in "Hmatch".
    2: { iApply (eliminate_wrong_token with "ScheToken").
         done.
         iModIntro.
         iNext.
         iIntros "[_ False]".
         iExFalso.
         done.
    }
    3: { iApply (eliminate_wrong_token with "ScheToken").
         done.
         iModIntro.
         iNext.
         iIntros "[_ False]".
         iExFalso.
         done.
    }
    4: { admit. }
    5: { iExFalso.
         iApply (token_excl with "[HSwitched]").
         iExact "HSwitched".
         iApply "Hmatch".
         done.
    }
    4: { 
      admit.
    }
    3: { admit. }
    2: { admit. }
  Admitted


End proof.
