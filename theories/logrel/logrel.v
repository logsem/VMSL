From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang.
From HypVeri.algebra Require Import base base_extra mem.
Import uPred.

(**  unary logical relation *)
Section logrel.
  Context `{hypconst:HypervisorConstants}.
  Context `{hypparams:!HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.

  Program Definition V0 : VMID := (@nat_to_fin 0 _ _).
  Next Obligation.
  destruct hypconst. simpl. lia.
  Defined.

  (* XXX: a better def using list zip? - no, gmap makes case analysis simpler*)
  Definition unknown_mem_page (p: PID) :=
    (∃ mem, ⌜∀ (a:Addr), a ∈ (addr_of_page p) -> is_Some (mem !! a)⌝ ∗ [∗ map] a ↦ w ∈ mem, (a ->a w))%I.

  (** definition **)

  Context (i : (leibnizO VMID)).

  Program Definition interp_execute: iPropO Σ :=
   (⌜ fin_to_nat i ≠ 0 ⌝ -∗
        (VMProp_holds i (1/2)%Qp -∗ WP ExecI @ i {{(λ _, True )}}))%I.

  Definition pgt_entries_own_excl (ps: gset PID) (vo: VMID) (be:bool) : iProp Σ:=
    [∗ set] p ∈ ps, p -@O> vo ∗ p -@E> be.

  (* [transferred_tran_entries] includes all transaction related entries transferred to/from i from/to primary when scheduling,*)
  Definition transferred_tran_entries (trans: gmap Addr transaction) : iProp Σ:=
    [∗ map] h ↦ tran ∈ trans ,
        (* All of half of transactions are required, as we don't know which one would be used by i.
          Only *half* is needed so that related vms can remember transactions by keeping the other half. *)
        h -{1/2}>t tran.1 ∗
        (* If i is the sender or receiver of a donation, the other half of transaction entry is required.
            Since it is possible for i to retrieve/reclaim the transaction, getting the whole entry removed.*)
        (⌜(tran.1.1.1.1.1 = i ∨ tran.1.1.1.2 = i) ∧ tran.1.2 = Donation⌝ -∗ h -{1/2}>t tran.1) ∗
        (* Retrievals must be provided so that i as the receiver is able to retrieve/relinquish. *)
        (⌜tran.1.1.1.2 = i⌝ -∗ h ->re tran.2) ∗
        (* Donation is again special here due to the same reason. *)
        (⌜tran.1.1.1.1.1 = i ∧ tran.1.2 = Donation⌝ -∗ h ->re tran.2 ∗ ⌜tran.2 = false⌝).

  (* [owned_trans_entries] are entries kept by i as the sender of non-donation transactions. *)
  Definition owned_tran_entries (trans: gmap Addr transaction) : iProp Σ:=
    [∗ map] h ↦ tran ∈ trans , ⌜tran.1.1.1.1.1 = i ∧ tran.1.2 ≠ Donation⌝ -∗ h -{1/2}>t tran.1.

  Definition transferred_pgt_entries (trans: gmap Addr transaction) : iProp Σ:=
    [∗ map] h ↦ tran ∈ trans ,
       ⌜(tran.1.1.1.1.1 = i ∧ tran.2 = true) ∨ (tran.1.1.1.2 = i ∧ tran.1.2 = Donation)⌝ -∗
           pgt_entries_own_excl tran.1.1.2 tran.1.1.1.1.1 tran.2.

  Definition memory_cells (ps : gset PID) : iProp Σ :=
    [∗ set] p ∈ ps, unknown_mem_page p.

  (* TODO: alternative definition, many lemmas in [logrel_extra.v] need to be proved to use it *)
  Definition memory_cell' (ps :gset PID): iProp Σ:=
    ∃ mem, (⌜dom (gset Addr) mem = (set_fold (λ p acc, list_to_set (addr_of_page p) ∪ acc) ∅ ps)⌝ ∗ [∗ map] k ↦ v ∈ mem, k ->a v)%I.


  Definition accessible_trans (trans : gmap Word transaction) :=
   filter (λ kv, (kv.2.1.1.1.1.1 = i ∧ kv.2.1.2 = Sharing) ∨ (kv.2.1.1.1.2 = i ∧ kv.2.2 = true)) trans.

  Definition ps_trans (trans: gmap Word transaction) : gset PID :=
    map_fold (λ (k:Addr) v acc, v.1.1.2 ∪ acc) (∅: gset PID) trans.

  Program Definition interp_access ps_acc p_tx p_rx (trans : gmap Word transaction) : iPropO Σ:=
    (
      let ps_nea := ps_trans (accessible_trans trans) ∪ {[p_rx]} in
      let ps_ea := ps_acc ∖ ps_nea in
      (* registers *)
      (∃ regs, ⌜is_total_gmap regs⌝ ∗ [∗ map] r ↦ w ∈ regs, r @@ i ->r w) ∗
      (* mailbox *)
      (TX@i := p_tx) ∗
      (* access *)
      i -@A> [ps_acc] ∗
      (* own & excl *)
      pgt_entries_own_excl ps_ea i true ∗
      (* transaction *)
      owned_tran_entries trans ∗
      ⌜ ps_nea ⊆ ps_acc ⌝ ∗
      (* mem *)
      memory_cells ps_ea ∗
      (* VMProp *)
      VMProp i ((∃ ps_na (trans' : gmap Word transaction) hpool,
                    let ps_trans' := ps_trans (accessible_trans trans') in
                    ⌜accessible_trans trans = accessible_trans trans'⌝ ∗
                    (* lower bound *)
                    LB@ i := [ps_na] ∗ ⌜ps_na ## ps_acc⌝ ∗
                    (* we need this to ensure all transaction entries are transferred *)
                    ⌜inv_trans_hpool_consistent' trans' hpool⌝ ∗
                    (* transaction entries *)
                    hp [hpool] ∗ transferred_tran_entries trans' ∗
                    (* page table entries *)
                    transferred_pgt_entries trans' ∗
                    (* mem *)
                    memory_cells ps_trans' ∗
                    (* status of RX *)
                    (RX@ i :=() ∨ ∃l s, RX@i :=(l,s)) ∗
                    (* RX *)
                    (RX@i := p_rx ∗ memory_cells {[p_rx]})) ∗
                  R0 @@ V0 ->r encode_hvc_func(Run) ∗ R1 @@ V0 ->r encode_vmid(i) ∗
                  (* if i yielding, we give following resources back to pvm *)
                  VMProp V0 (
                           ∃ ps_na' ps_acc' trans'' hpool',
                             let ps_trans'' := ps_trans (accessible_trans trans'') in
                             (* lower bound *)
                             LB@ i := [ps_na'] ∗ ⌜ps_na' ## ps_acc'⌝ ∗
                                        (* resources *)
                                        hp [hpool'] ∗ transferred_tran_entries trans'' ∗
                                        transferred_pgt_entries trans'' ∗
                                        memory_cells ps_trans'' ∗
                                        (* R0 and R1 of pvm *)
                                        (R0 @@ V0 ->r encode_hvc_func(Yield) ∗ R1 @@ V0 ->r encode_vmid(i))
                                      (* no scheduling, we finish the proof *)
                                      (* NOTE: if i will be scheduled arbitrary number of times, need recursive definition *)
                                      ∨ False) (1/2)%Qp)
               (1/2)%Qp
    )%I.

End logrel.


(* TODO:
   - [] rewrite adequacy
   - [] fix mem_send_nz
 *)
