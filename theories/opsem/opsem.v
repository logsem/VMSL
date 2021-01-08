Require Import basic.
From iris.program_logic Require Import language ectx_language ectxi_language.

Section opsem.
Ltac inv H := inversion H; clear H; subst.

  Context `{InstrEncoding} .

  Fixpoint mem_copy_aux (m:Mem) (atx arx: Addr) (ws: nat): Mem:=
    match ws with
    | 0 => m
    | S n => mem_copy_aux (upd_mem m (a_add_nat arx n) (m !m! (a_add_nat atx n))) atx arx n
    end.

   Definition mem_copy (m:Mem) (pt pr: PID) (ws : Z) : Mem :=
    if (Z.ltb ws 0) then
      let ws := (Z.to_nat ws) in
      (mem_copy_aux m (pid_to_a pt) (pid_to_a pr) ws)
    else m.

  Definition exec (i: instr) (ϕ : ExecConf) (v:VMID) : Conf :=
    let m := ϕ.m in
    let Δ := (fst ϕ) in
    let s := (snd (snd ϕ)) in
    match (Δ !s! v), (Δ !s! 0) with
    | Some δ_v, Some δ_p =>
      match i with
      | faili => ((Done FailD), ϕ)
      | halt => ((Done HaltD), ϕ)
      | br r => (tick (upd_gen_reg Δ v PC (δ_v.gr !gr! r)) m s v v ident)
      | bne r => let Δ':= if (Z.eqb (z_of_w (δ_v.sr !sr! NZ)) 1)
                          then (upd_gen_reg Δ v PC (δ_v.gr !gr! r))
                          else (upd_gen_reg Δ v PC (w_add_z (δ_v.gr !gr! PC) 1))
                 in
                 (tick Δ' m s v v ident)
      | mov r1 w => let Δ':= (upd_gen_reg Δ v r1 w) in
                    (tick Δ' m s v v updPC)
      | ldr r1 r2 => match (valid_a δ_v r2 RE) with
                     | Some a => let Δ' :=(upd_gen_reg Δ v r1 (m !m! a)) in
                                 (tick Δ' m s v v updPC)
                     | None => ((Done FailD), ϕ)
                     end
      | str r1 r2 => match (valid_a δ_v r1 WR) with
                     | Some a => let m' :=(upd_mem m a (δ_v.gr !gr! r2)) in
                                 (tick Δ m' s v v updPC)
                     | None => ((Done FailD), ϕ)
                     end
      | add r1 r2 r3 => let Δ':= (upd_gen_reg Δ v r1 (w_add_w (δ_v.gr !gr! r2)(δ_v.gr !gr! r3))) in
                        (tick Δ' m s v v updPC)
      | sub r1 r2 r3 => let Δ':= (upd_gen_reg Δ v r1 (w_sub_w (δ_v.gr !gr! r2)(δ_v.gr !gr! r3))) in
                        (tick Δ' m s v v updPC)
      | cmp r1 r2 => match (w_sub_w (δ_v.gr !gr! r1)(δ_v.gr !gr! r2)) with
                     | (W z _ _) => let Δ' := if (Z.eqb z 0) then (upd_sys_reg Δ v NZ (z_to_w 1))
                                    else if (Z.ltb z 0) then (upd_sys_reg Δ v NZ (z_to_w 2))
                                         else  (upd_sys_reg Δ v NZ (z_to_w 0)) in
                                    (tick Δ' m s v v updPC)
                     end
      | hvc => match (w_to_fi (δ_v.gr !gr! (nat_to_r 0))) with
               | F_MEM_DNT => match (valid_a δ_v (nat_to_r 1) VA) with
                              | Some a => let vr :=(Z.to_nat  (z_of_w (δ_v.gr !gr! (nat_to_r 2)))) in
                                          match (Δ !s! vr) with
                                            | Some _ => if (vr =? v) then ((Done FailD), ϕ)
                                                        else
                                                          let pid:=(a_to_pid a) in
                                                          let s' := s ++ [(pid, vr)] in
                                                          let Δ' := (upd_ps_rm Δ v pid) in
                                                          let Δ' := (upd_gen_reg Δ' v (nat_to_r 0) (rc_to_w SUCCESS)) in
                                                          let Δ' := (upd_gen_reg Δ' v (nat_to_r 2) (nat_to_w (length s))) in
                                                             (tick Δ' m s' v v updPC)
                                            | None => ((Done FailD), ϕ)
                                          end
                              | None => ((Done FailD), ϕ)
                              end
               | F_MEM_RTRVQ => let hd := (Z.to_nat (z_of_w (δ_v.gr !gr! (nat_to_r 1)))) in
                                match (s !! hd ) with
                                | Some (p,v) => if (gset_elem_of_b p (δ_v.ps)) then ((Done FailD), ϕ)
                                                else let Δ' := (upd_ps_add Δ v p) in
                                                     let Δ' := (upd_gen_reg Δ' v (nat_to_r 0) (rc_to_w MEM_RTRVP)) in
                                                     let s' := (delete hd s) in
                                                     (tick Δ' m s' v v updPC)
                                | _ => ((Done FailD), ϕ)
                                end
               | F_RUN => let vn :=(Z.to_nat  (z_of_w (δ_v.gr !gr! (nat_to_r 2)))) in
                          match (Δ !s! vn) with
                          | Some _ => if (vn =? 0) then
                                        match δ_v.π.2 with
                                        | Some (((_, b), ws), vs) =>
                                          if b then
                                            let Δ' := (upd_gen_reg Δ vn (nat_to_r 0) (rc_to_w MSG_SEND)) in
                                            let Δ' := (upd_gen_reg Δ' vn (nat_to_r 1) (comb (nat_to_w vs) (nat_to_w vn))) in
                                            let Δ' := (upd_gen_reg Δ' vn (nat_to_r 3) ws) in
                                            (tick Δ' m s v vn updPC)
                                          else (tick Δ m s v vn updPC)
                                        | None => ((Done FailD), ϕ)
                                        end
                                      else ((Done FailD), ϕ)
                          | None => ((Done FailD), ϕ)
                          end
               | F_YIELD =>let Δ' := (upd_gen_reg Δ 0 (nat_to_r 0) (rc_to_w YIELD)) in
                           let Δ' := (upd_gen_reg Δ' 0 (nat_to_r 1) (nat_to_w v)) in
                           (tick Δ' m s v 0 updPC)
               | F_MSG_WAIT =>match δ_v.π.2 with
                              | Some (((pr, b), ws), vs) =>
                                if b then
                                  let Δ' := (upd_gen_reg Δ v (nat_to_r 0) (rc_to_w MSG_SEND)) in
                                  let Δ' := (upd_gen_reg Δ' v (nat_to_r 1) (comb (nat_to_w vs) (nat_to_w v))) in
                                  let Δ' := (upd_gen_reg Δ' v (nat_to_r 3) ws) in
                                    (tick Δ' m s v v updPC)
                                else
                                  let Δ' := (upd_gen_reg Δ 0 (nat_to_r 0) (rc_to_w MSG_WAIT)) in
                                  let Δ' := (upd_gen_reg Δ' 0 (nat_to_r 1) (nat_to_w v)) in
                                    (tick Δ' m s v 0 updPC)
                              | None => ((Done FailD), ϕ)
                              end
               | F_MSG_SEND =>match δ_v.π.1 with
                              | Some (pt) =>
                                let vr := (Z.to_nat (z_of_w (δ_v.gr !gr! (nat_to_r 1)))) in
                                let ws := (z_of_w (δ_v.gr !gr! (nat_to_r 2))) in
                                if (Z.leb ws (Z.pow 2 PageBitSize)) then
                                  match (Δ !s! vr) with
                                    | Some δ_vr => match δ_vr.π.2 with
                                                   | Some (((pr, true), _), _) =>
                                                     let m' := (mem_copy m pt pr ws) in
                                                     let Δ' := (upd_gen_reg Δ v (nat_to_r 0) (rc_to_w SUCCESS)) in
                                                     if (v =? 0) then (tick Δ' m' s v 0 updPC)
                                                     else
                                                       let Δ' := (upd_gen_reg Δ' 0 (nat_to_r 0) (rc_to_w MSG_SEND)) in
                                                       let Δ' := (upd_gen_reg Δ' 0 (nat_to_r 1) (comb (nat_to_w v) (nat_to_w vr))) in
                                                       (tick Δ' m' s v 0 updPC)
                                                   | Some (((pr, false), _), _) =>
                                                     let Δ' := (upd_gen_reg Δ v (nat_to_r 0) (rc_to_w BUSY)) in
                                                     (tick Δ' m s v v updPC)
                                                   | None => ((Done FailD), ϕ)
                                                   end
                                    | None => ((Done FailD), ϕ)
                                  end
                                else ((Done FailD), ϕ)
                              | None => ((Done FailD), ϕ)
                              end
               | F_MSG_RCV => match δ_v.π.2 with
                              | Some (((pr, b), ws), vs) =>
                                if b then
                                  let Δ' := (upd_rx Δ v (Some (((pr, false), ws), v))) in
                                  (tick Δ' m s v v updPC)
                                else ((Done FailD), ϕ)
                              | _ => ((Done FailD), ϕ)
                              end
               | F_UNKNOWN =>((Done FailD), ϕ)
               end
      | mrs r1 r2 =>  let Δ':= (upd_gen_reg Δ v r1 (δ_v.sr !sr! r2)) in
                    (tick Δ' m s v v updPC)
      | msr r1 r2 =>  let Δ':= (upd_sys_reg Δ v r1 (δ_v.gr !gr! r2)) in
                    (tick Δ' m s v v updPC)
      end
    | _,_ => ((Done FailD), ϕ)
    end.
 (* valid_a = Some a is better *)
(* Inductive isValidPC: list State -> VMID -> Prop :=
| isValidPC_intro:
    forall (Δ: list State) (δ: State) v (a: Addr),
      (Δ !s! v) =Some δ ->
       (valid_a δ PC VA)=(Some a) ->
      (isValidPC Δ v).

Lemma isValidPC_dec:
  forall Δ v , { isValidPC Δ v } + { not (isValidPC Δ v ) }.
Proof.
  intros.
  destruct (Δ !s! v) eqn:Hδ.
  - destruct (valid_a s PC VA) eqn:Ha.
    + left.
      econstructor.
      rewrite Hδ.
      done.
      rewrite Ha.
      done.
    + right; red; intro HH.
      inversion HH;subst. naive_solver.
  - right; red; intro HH.
      inversion HH;subst. naive_solver.
Qed.
  *)

Inductive step: Conf → Conf → Prop :=
  | step_exec_invalid_vmid:
      forall ϕ v,
        (ϕ.1 !s! v) = None->
        step ((ExecInstr v), ϕ) ((Done FailD), ϕ)
  | step_exec_invalid_pc:
      forall ϕ v δ,
        (ϕ.1 !s! v) =Some δ ->
        (valid_a δ PC VA)=None ->
        step ((ExecInstr v), ϕ) ((Done FailD), ϕ)
  | step_exec_instr:
      forall ϕ v δ a i,
        (ϕ.1 !s! v) =Some δ ->
       (valid_a δ PC VA)=(Some a) ->
        decodeInstr ((ϕ.m) !m! a) = i →
        step ((ExecInstr v), ϕ) (exec i ϕ v).

Lemma normal_always_step:
    forall ϕ v, exists cf ϕ', step ((ExecInstr v), ϕ) (cf, ϕ').
  Proof.
    intros.
    destruct (ϕ.1 !s! v) eqn:Hδ.
    - destruct  (valid_a s PC VA) eqn:Ha.
      + destruct (exec (decodeInstr ((ϕ.m) !m! a)) ϕ v) eqn:He.
        exists e, e0. rewrite <-He. eapply step_exec_instr; eauto.
      + exists (Done FailD), ϕ.
        eapply step_exec_invalid_pc.
        done.
        assumption.
    - exists (Done FailD), ϕ.
      eapply step_exec_invalid_vmid.
      assumption.
Qed.

  Lemma step_deterministic:
    forall c1 c2 c2' σ1 σ2 σ2',
      step (c1, σ1) (c2, σ2) ->
      step (c1, σ1) (c2', σ2') ->
      c2 = c2' ∧ σ2 = σ2'.
  Proof.
    intros * H1 H2; split; inv H1; inv H2; auto; try congruence.
  Qed.
(* why need these ?*)
  Lemma step_exec_inv (Δ : list State) (m:Mem)  (s: ShareStates) (δ:State) v a w (i:instr) (c: ExecMode) (σ: ExecConf) :
    (Δ !s! v)= Some δ ->
    valid_a δ PC VA = Some a ->
    m !m! a = w ->
    step ((ExecInstr v) ,(Δ, (m,s)) ) (c, σ) ->
    exec (decodeInstr w) (Δ, (m,s)) v = (c, σ).
  Proof.
    intros. inv H3;subst.
    - simpl in H5.
      rewrite H5 in H0.
      inversion H0.
    - simpl in H7.
      rewrite H0 in H7.
      inv H7.
      rewrite H9 in H1.
      inversion H1.
    - simpl in H7.
      rewrite H0 in H7.
      inv H7.
      rewrite H1 in H8.
      inv H8.
      done.
Qed.

  Lemma step_invalid_vmid_fail_inv (Δ : list State) (m:Mem)  (s: ShareStates)v c (ϕ': ExecConf) :
    (Δ !s! v)= None ->
    step ((ExecInstr v) ,(Δ, (m,s))) (c, ϕ') ->
    c = (Done FailD) ∧ ϕ' = (Δ, (m,s)).
  Proof.
    intros.
   inv H1.
   - done.
   - simpl in H5.
     rewrite H0 in H5.
     inv H5.
   - simpl in H5.
     rewrite H0 in H5.
     inv H5.
  Qed.

  (*TODO: step_invalid_pc_fail_inv, skip it for now*)

    (*val*)
 Inductive val: Type :=
  | HaltedV: val
  | FailedV: val
  | NextIV (v: VMID): val.

  Inductive expr: Type :=
  | Single (m : ExecMode)
  | Repeat (e : expr).

  Definition state : Type := ExecConf.

  Definition of_val (v: val): expr :=
    match v with
    | HaltedV => (Single (Done HaltD))
    | FailedV => (Single (Done FailD))
    | NextIV n => (Single (Done (NextD n)))
    end.

  Definition to_val (e: expr): option val :=
    match e with
    | Single d=>
      match d with
      | Done HaltD => Some HaltedV
      | Done FailD => Some FailedV
      | Done (NextD n) => Some (NextIV n)
      | ExecInstr _ => None
      end
    | Repeat _ => None
    end.

  Lemma of_to_val:
    forall e v, to_val e = Some v →
           of_val v = e.
  Proof.
    intros * HH.
    destruct e;try (destruct m;simpl in HH;inv HH).
    destruct d;simpl in H1;inv H1;simpl;done.
    inv HH.
  Qed.

  Lemma to_of_val:
    forall v, to_val (of_val v) = Some v.
  Proof. destruct v; reflexivity. Qed.

(*Evaluation context*)
  Inductive ectx_item :=
  | RepeatCtx.

  Notation ectx := (list ectx_item).

  Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
    match Ki with
    | RepeatCtx => Repeat e
    end.

  (*reduction rules *)
  (* TODO: remove Single *)
  Inductive prim_step: expr → state → list Empty_set → expr → state → list expr → Prop :=
  | PS_no_fork_single n σ e' σ' :
      step ((ExecInstr n), σ) (e', σ') → prim_step (Single (ExecInstr n)) σ [] (Single e') σ' []
  | PS_no_fork_next n σ : prim_step (Repeat (Single (Done (NextD n)))) σ [] (Repeat (Single (ExecInstr n))) σ []
  | PS_no_fork_halt σ : prim_step (Repeat (Single (Done HaltD))) σ [] (Single (Done HaltD)) σ []
  | PS_no_fork_fail σ : prim_step (Repeat (Single (Done FailD))) σ [] (Single (Done FailD)) σ [].

  Lemma val_stuck:
    forall e σ o e' σ' efs,
      prim_step e σ o e' σ' efs →
      to_val e = None.
  Proof. intros * HH. by inversion HH. Qed.

  Lemma prim_step_exec_inv n σ1 l1 e2 σ2 efs :
    prim_step (Single (ExecInstr n)) σ1 l1 e2 σ2 efs →
    l1 = [] ∧ efs = [] ∧
    exists (c: ExecMode),
      e2 = (Single c)∧
      step ((ExecInstr n ), σ1) (c, σ2).
  Proof. inversion 1; subst; split; eauto. Qed.

  Lemma prim_step_and_step_exec n σ1 e2 σ2 l1 e2' σ2' efs :
    step ((ExecInstr n), σ1) (e2, σ2) →
    prim_step (Single (ExecInstr n)) σ1 l1 e2' σ2' efs →
    l1 = [] ∧ e2' = (Single e2) ∧ σ2' = σ2 ∧ efs = [].
  Proof.
    intros* Hstep Hpstep.
    inversion Hpstep as [? ? ? ? Hstep' | | |]; subst.
    generalize (step_deterministic _ _ _ _ _ _ Hstep Hstep'). intros [-> ->].
    auto.
  Qed.

  Lemma vm_lang_determ e1 σ1 κ κ' e2 e2' σ2 σ2' efs efs' :
    prim_step e1 σ1 κ e2 σ2 efs →
    prim_step e1 σ1 κ' e2' σ2' efs' →
    κ = κ' ∧ e2 = e2' ∧ σ2 = σ2' ∧ efs = efs'.
  Proof.
    intros Hs1 Hs2. inv Hs1; inv Hs2.
    all: repeat match goal with HH : step _ _ |- _ => inv HH end; try congruence.
    all: auto.
    rewrite H5 in H7; inv H7.
    rewrite H8 in H6; inv H6.
    rewrite H3 in H4; inv H4.
    done.
  Qed.

  Lemma fill_item_val Ki e :
    is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
  Proof. intros [v ?]. destruct Ki; simplify_option_eq; eauto. Qed.
  Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
  Proof. destruct Ki; intros ???; simplify_eq; auto with f_equal. Qed.
  Lemma head_ctx_step_val Ki e σ1 κ e2 σ2 ef :
    prim_step (fill_item Ki e) σ1 κ e2 σ2 ef → is_Some (to_val e).
  Proof. destruct Ki; inversion_clear 1; simplify_option_eq; eauto. Qed.
  Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
    to_val e1 = None → to_val e2 = None →
    fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
  Proof.
    destruct Ki1, Ki2; intros; try discriminate; simplify_eq;
    repeat match goal with
           | HH : to_val (of_val _) = None |- _ => by rewrite to_of_val in HH
           end; auto.
  Qed.
  Lemma vm_lang_mixin : EctxiLanguageMixin of_val to_val fill_item prim_step.
    constructor.
    apply to_of_val.
    apply of_to_val.
    apply val_stuck.
    apply fill_item_val.
    apply fill_item_inj.
    apply fill_item_no_val_inj.
    apply head_ctx_step_val.
Qed.

 Definition is_atomic (e : expr) : Prop :=
    match e with
    | Single _ => True
    | _ => False
    end.

 (* ugly proofs... *)
 Lemma tick_updpc_atomic Δ m s n v :
   ∃ v' ϕ', (tick Δ m s n v updPC) = ((Done FailD), ϕ') ∨
         ((tick Δ m s n v updPC) = ((Done (NextD v') ,ϕ'))) ∨
          ((tick Δ m s  n v updPC)= ((Done HaltD) ,ϕ')).
  Proof.
    rewrite /tick; rewrite /updPC;
      repeat case_match.
     exists 0; eauto.
     exists 0; eauto.
     exists v; eauto.
     exists v; eauto.
     exists 0; eauto.
     exists 0; eauto.
  Qed.

  Lemma tick_id_atomic Δ m s n v:
   ∃ v' ϕ', (tick Δ m s n v ident) = ((Done FailD), ϕ') ∨
         ((tick Δ m s n v ident) = ((Done (NextD v') ,ϕ'))) ∨
          ((tick Δ m s n v ident)= ((Done HaltD) ,ϕ')).
  Proof.
    rewrite /tick; rewrite /ident;
      repeat case_match.
     exists 0; eauto.
     exists v; eauto.
     exists 0; eauto.
     exists 0; eauto.
  Qed.

  Lemma instr_atomic i φ n :
    ∃ n' φ', (exec i φ n = ((Done FailD), φ')) ∨ (exec i φ n = ((Done (NextD n')), φ')) ∨
          (exec i φ n = ((Done HaltD), φ')).
  Proof.
    unfold exec.
    repeat case_match;
      try (apply tick_updpc_atomic);
      try (apply tick_id_atomic);
      try (exists 0; eauto).
    Qed.

End opsem.

Canonical Structure vm_ectxi_lang `{InstrEncoding} := EctxiLanguage vm_lang_mixin.
Canonical Structure vm_ectx_lang `{InstrEncoding} := EctxLanguageOfEctxi vm_ectxi_lang.
Canonical Structure vm_lang `{InstrEncoding} := LanguageOfEctx vm_ectx_lang.
