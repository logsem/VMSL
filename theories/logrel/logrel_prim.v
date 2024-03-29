From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang.
From HypVeri.algebra Require Import base base_extra mem mailbox trans.
From HypVeri.logrel Require Export logrel big_sepSS.


(* Section vmprop. *)
(*   Context `{HypervisorConstants}. *)
(*   Context `{!HypervisorParameters}. *)
(*   Context `{vmG: !gen_VMG Σ}. *)
(*   Context (i : VMID). *)
(*   Context (Φ_t : (gmap Addr transaction) -> VMID -> VMID -> iProp Σ). *)
(*   Context (Φ_r : VMID -> option (Word * VMID)-> VMID -> iProp Σ). *)

  (* Definition rx_states_transferred (rxs: gmap VMID (option (Word*VMID))) : iProp Σ := *)
  (*   [∗ map]i ↦ os ∈ rxs, match os with *)
  (*                          | None => True *)
  (*                          | Some s => Φ_r i os V0 *)
  (*                         end. *)

  (* Definition rx_states_owned (rxs: gmap VMID (option (Word*VMID))) : iProp Σ := *)
  (*   [∗ map]i ↦ os ∈ rxs, match os with *)
  (*                          | None => True *)
  (*                          | Some s => if bool_decide (s.2 = V0) then Φ_r i os i else True *)
  (*                         end. *)

  (* Definition return_reg_rx i (rs : option (Word * VMID)) (rxs :gmap VMID (option(Word*VMID))): iProp Σ:= *)
  (*   ((R0 @@ V0 ->r encode_hvc_func(Yield) ∨ *)
  (*     R0 @@ V0 ->r encode_hvc_func(Wait) ∗ ⌜rs = None⌝) *)
  (*    ∗ rx_states_global (delete i rxs) *)
  (*    ∗ R1 @@ V0 ->r encode_vmid(i) ∗ ∃ r2, R2 @@ V0 ->r r2) ∨ *)
  (*   (R0 @@ V0 ->r encode_hvc_func(Send) *)
  (*     ∗ ∃ l j, Φ_r j (Some (l,i)) V0 *)
  (*     ∗ rx_states_global (<[j:=Some(l,i)]>(delete i rxs)) ∗ ⌜rxs !! j = Some None⌝ *)
  (*     ∗ (∃r1, R1 @@ V0 ->r r1 ∗ ⌜decode_vmid r1 = Some j⌝) ∗  R2 @@ V0 ->r l). *)

  (* Definition vmprop_zero_pre (Ψ: (gmap Word transaction) -d> iPropO Σ) : (gmap Word transaction) -d> (gmap VMID (option(Word * VMID))) -d> iPropO Σ := *)
  (*   λ trans rxs, (∃ (trans' :gmap Word transaction) rs', *)
  (*                    let trans_ret := (only i trans') ∪ (except i trans) in *)
  (*                          ⌜dom (only i trans') ## dom (except i trans)⌝ ∗ *)
  (*                          ⌜∀ x, x ≠ i -> trans_rel_secondary x trans trans_ret⌝ ∗ *)
  (*                          transaction_hpool_global_transferred (trans_ret) ∗ *)
  (*                          big_sepSS_singleton set_of_vmids i (Φ_t trans_ret) ∗ *)
  (*                          rx_state_match i rs' ∗ Φ_r i rs' V0 ∗ *)
  (*                          return_reg_rx i rs' rxs ∗ *)
  (*                          VMProp i (Ψ trans_ret) (1/2)%Qp)%I. *)

  (* Definition vmprop_unknown_pre *)
  (*   (Ψ :(gmap Word transaction) -d> iPropO Σ) : (gmap Word transaction) -d> iPropO Σ := *)
  (*  λ trans, (∃ (trans' : gmap Word transaction) (rxs : gmap VMID (option(Word * VMID))), *)
  (*              ⌜trans_rel_secondary i trans trans'⌝ ∗ *)
  (*              (* transaction and pagetable entries *) *)
  (*              transaction_hpool_global_transferred trans' ∗ *)
  (*              big_sepSS_singleton set_of_vmids i (Φ_t trans') ∗ *)
  (*              (∃ r0, R0 @@ V0 ->r r0 ∗ ⌜decode_hvc_func r0 = Some Run⌝) ∗ (∃ r1, R1 @@ V0 ->r r1 ∗ ⌜decode_vmid r1 = Some i⌝)∗ (∃ r2, R2 @@ V0 ->r r2) ∗ *)
  (*              (∀ rs : option (Addr * VMID), ⌜rxs !! i = Some rs⌝ -∗ rx_state_match i rs ∗ Φ_r i rs i) ∗ *)
  (*              (* rx pages for all other VMs *) *)
  (*              (rx_states_global (delete i rxs)) ∗ ⌜is_total_gmap rxs⌝ ∗ *)
  (*              (* if i yielding, we give following resources back to pvm *) *)
  (*              VMProp V0 (vmprop_zero_pre Ψ trans' rxs) (1/2)%Qp)%I. *)

  (* Local Instance vmprop_unknown_pre_contractive : Contractive (vmprop_unknown_pre). *)
  (* Proof. *)
  (*   rewrite /vmprop_unknown_pre => n vmprop_unknown vmprop_unknown' Hvmprop_unknown trans /=. *)
  (*   do 13 f_equiv. *)
  (*   rewrite /VMProp /=. *)
  (*   do 6 f_equiv. *)
  (*   f_contractive. *)
  (*   rewrite /vmprop_zero_pre. *)
  (*   do 10 f_equiv. *)
  (*   rewrite /VMProp. *)
  (*   repeat f_equiv. *)
  (* Qed. *)

  (* Definition vmprop_unknown:= fixpoint (vmprop_unknown_pre). *)

  (* Definition vmprop_zero := vmprop_zero_pre vmprop_unknown. *)

  (* Lemma vmprop_unknown_eq trans: vmprop_unknown trans ⊣⊢ *)
  (*   (∃ (trans' : gmap Word transaction) (rxs : gmap VMID (option(Word * VMID))), *)
  (*              ⌜trans_rel_secondary i trans trans'⌝ ∗ *)
  (*              (* transaction and pagetable entries *) *)
  (*              transaction_hpool_global_transferred trans' ∗ *)
  (*              big_sepSS_singleton set_of_vmids i (Φ_t trans') ∗ *)
  (*              (∃ r0, R0 @@ V0 ->r r0 ∗ ⌜decode_hvc_func r0 = Some Run⌝) ∗ (∃ r1, R1 @@ V0 ->r r1 ∗ ⌜decode_vmid r1 = Some i⌝)∗ (∃ r2, R2 @@ V0 ->r r2) ∗ *)
  (*              (∀ rs : option (Addr * VMID), ⌜rxs !! i = Some rs⌝ -∗ rx_state_match i rs ∗ Φ_r i rs i) ∗ *)
  (*              (* rx pages for all other VMs *) *)
  (*              (rx_states_global (delete i rxs)) ∗ ⌜is_total_gmap rxs⌝ ∗ *)
  (*              (* if i yielding, we give following resources back to pvm *) *)
  (*         VMProp V0 (vmprop_zero trans' rxs) (1/2)%Qp)%I. *)
  (* Proof. *)
  (*   rewrite /vmprop_unknown. *)
  (*   apply (fixpoint_unfold vmprop_unknown_pre). *)
  (* Qed. *)

  (* End vmprop. *)

Section logrel_prim.

  Context `{HypervisorConstants}.
  Context `{!HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.


  Definition interp_access_prim Φ_t Φ_r (p_tx p_rx :PID) (ps_acc: gset PID) (trans: gmap Word transaction)
    (rxs : gmap VMID (option (Word * VMID))) `{!SliceTransWf Φ_t} `{!SliceRxsWf Φ_r}: iPropO Σ:=
    (
      (* making sure we have enough resources for V0 *)
      ⌜∀ i j trans, (i = V0 ∨ j = V0) -> Φ_t trans i j ⊣⊢ slice_transfer_all trans i j⌝ ∗
      ⌜∀ i os, (match os with
                 | None => True
                 | Some (_,j) => j = V0 -> Φ_r i os i ⊣⊢ slice_rx_state i os
                end)⌝ ∗
      ⌜∀ i os, match os with
               | None => True
               | Some (_ ,k) => k = V0
               end -> Φ_r i os i ⊣⊢ Φ_r i os V0⌝ ∗
      ⌜∀ i j os, (match os with
                 | None => True
                 | Some (_,j) => j = V0
                end) -> j ≠ i -> j ≠ V0 -> Φ_r i os j ⊣⊢ True⌝ ∗
      ⌜∀ os, (match os with
              | None => True
              | _ => Φ_r V0 os V0 ⊣⊢ slice_rx_state V0 os
              end)⌝ ∗
      let ps_oea := ps_acc ∖ {[p_rx;p_tx]} ∖ (currently_accessible_in_trans_memory_pages V0 trans) in
      (∃ regs, ⌜is_total_gmap regs⌝ ∗ [∗ map] r ↦ w ∈ regs, r @@ V0 ->r w) ∗
      (tx_page V0 p_tx ∗ ∃ mem_tx, memory_page p_tx mem_tx) ∗
      (rx_page V0 p_rx) ∗
      V0 -@A> ps_acc ∗
      ⌜{[p_tx;p_rx]} ⊆ ps_acc⌝ ∗ ⌜currently_accessible_in_trans_memory_pages V0 trans ⊆ ps_acc ∖ {[p_tx;p_rx]}⌝ ∗
      pagetable_entries_excl_owned V0 ps_oea ∗
      transaction_pagetable_entries_owned V0 trans ∗
      retrieved_transaction_owned V0 trans ∗
      (∃ mem_oea, memory_pages (ps_oea ∪ (retrieved_lending_memory_pages V0 trans)) mem_oea) ∗
      (∃ P0, VMProp V0 P0 1%Qp) ∗
      (* transferred *)
      transaction_hpool_global_transferred trans ∗
      ⌜is_total_gmap rxs⌝ ∗
      rx_states_global rxs ∗
      rx_states_transferred Φ_r rxs ∗
      (big_sepSS set_of_vmids (Φ_t trans)) ∗
      [∗ set] i ∈ set_of_vmids ∖ {[V0]}, VMProp (i:VMID) (vmprop_unknown i Φ_t Φ_r trans) (1/2)%Qp
    )%I.

  Definition interp_execute_prim: iPropO Σ :=
    WP ExecI @ V0 {{(λ _, True )}}%I.

End logrel_prim.
