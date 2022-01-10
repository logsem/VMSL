From iris.proofmode Require Import tactics.
From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri.lang Require Import lang.
From HypVeri Require Import machine_extra.
From HypVeri.algebra Require Import base base_extra mem.
Import uPred.

(**  unary logical relation *)
Section logrel.
  Context `{hypconst:HypervisorConstants}.
  Context `{hypparams:!HypervisorParameters}.
  Context `{vmG: !gen_VMG Σ}.


  (* XXX: a better def using list zip? - no, gmap makes case analysis simpler*)
  Definition unknown_mem_page (p: PID) :=
    (∃ mem, ⌜∀ (a:Addr), a ∈ (addr_of_page p) -> is_Some (mem !! a)⌝ ∗ [∗ map] a ↦ w ∈ mem, (a ->a w))%I.

  (** definition **)

  Context (i : (leibnizO VMID)).

  Program Definition interp_execute: iPropO Σ :=
   (⌜i ≠ V0⌝ -∗
        (VMProp_holds i (1/2)%Qp -∗ WP ExecI @ i {{(λ _, True )}}))%I.

  Definition pgt_entries_own_excl (ps: gset PID) (vo: VMID) (be:bool) : iProp Σ:=
    [∗ set] p ∈ ps, p -@O> vo ∗ p -@E> be.

  (* [transferred_tran_entries] includes all transaction related entries transferred to/from i from/to primary when scheduling,*)
  Definition transferred_tran_entries (trans: gmap Addr transaction) : iProp Σ:=
    [∗ map] h ↦ tran ∈ trans,
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

  Definition set_of_addr (ps:gset PID) := (set_fold (λ p (acc:gset Addr), list_to_set (addr_of_page p) ∪ acc) ∅ ps).
  Definition memory_pages (ps :gset PID): iProp Σ:=
    ∃ mem, (⌜dom (gset Addr) mem = set_of_addr ps⌝ ∗ [∗ map] k ↦ v ∈ mem, k ->a v)%I.

  Definition accessible_trans (trans : gmap Word transaction) :=
   filter (λ kv, (kv.2.1.1.1.1.1 = i ∧ kv.2.1.2 = Sharing) ∨ (kv.2.1.1.1.2 = i ∧ kv.2.2 = true)) trans.

  Definition ps_trans (trans: gmap Word transaction) : gset PID :=
    map_fold (λ (k:Addr) v acc, v.1.1.2 ∪ acc) (∅: gset PID) trans.

  Definition VMProp_unknown p_rx Transferred:=
    VMProp i (∃ (trans : gmap Word transaction) hpool,
                    (* let ps_trans' := ps_trans (accessible_trans trans) in *)
                    (* ⌜accessible_trans trans = accessible_trans trans'⌝ ∗ *)
                    (* lower bound *)
                    (* we need this to ensure all transaction entries are transferred *)
                    ⌜inv_trans_hpool_consistent' trans hpool⌝ ∗
                    (* transaction entries *)
                    hp [hpool] ∗ transferred_tran_entries trans ∗
                    (* page table entries *)
                    transferred_pgt_entries trans ∗
                    (* mem *)
                    (* memory_pages ps_trans' ∗ *)
                    Transferred ∗
                    (* status of RX *)
                    (RX@ i :=() ∨ ∃l s, RX@i :=(l,s)) ∗
                    (* RX *)
                    (RX@i := p_rx ∗ memory_pages {[p_rx]}) ∗
                    R0 @@ V0 ->r encode_hvc_func(Run) ∗ R1 @@ V0 ->r encode_vmid(i) ∗
                  (* if i yielding, we give following resources back to pvm *)
                  VMProp V0 (
                           (∃ ps_na ps_acc' trans'' hpool',
                             (* TODO: we may need more constraints for trans'',
                                      probably relate it to trans' *)
                             let ps_trans'' := ps_trans (accessible_trans trans'') in
                             (* lower bound *)
                             LB@ i := [ps_na] ∗ ⌜ps_na ## ps_acc'⌝ ∗
                                        (* resources *)
                                        i -@{1/2}A> [ps_acc'] ∗
                                        hp [hpool'] ∗ transferred_tran_entries trans'' ∗
                                        transferred_pgt_entries trans'' ∗
                                        memory_pages ps_trans'' ∗
                                        (RX@ i :=() ∨ ∃l s, RX@i :=(l,s)) ∗
                                        (RX@i := p_rx ∗ memory_pages {[p_rx]}) ∗
                                        R0 @@ V0 ->r encode_hvc_func(Yield) ∗ R1 @@ V0 ->r encode_vmid(i))
                                      (* no scheduling, we finish the proof *)
                                      (* NOTE: if i will be scheduled arbitrary number of times, need recursive definition *)
                                      ∨ False) (1/2)%Qp)
               (1/2)%Qp.

  Program Definition interp_access ps_acc p_tx p_rx Owned Transferred : iPropO Σ:=
    (
      (* let ps_nea := ps_trans (accessible_trans trans) ∪ {[p_rx]} in *)
      (* let ps_ea := ps_acc ∖ ps_nea in *)
      (* registers *)
      (∃ regs, ⌜is_total_gmap regs⌝ ∗ [∗ map] r ↦ w ∈ regs, r @@ i ->r w) ∗
      (* mailbox *)
      (TX@i := p_tx) ∗
      (* access *)
      i -@{1/2}A> [ps_acc] ∗
      (* own & excl *)
      (* pgt_entries_own_excl ps_ea i true ∗ *)
      (* (* transaction *) *)
      (* ⌜ ps_nea ⊆ ps_acc ⌝ ∗ *)
      (* (* mem *) *)
      (* memory_pages ps_ea ∗ *)
      Owned ∗
      (* VMProp *)
      VMProp_unknown p_rx Transferred ∗
      (Owned ∗ ▷ Transferred -∗
       (∃ ps_na trans,
           let ps_nea := ps_trans (accessible_trans trans) ∪ {[p_rx]} in
           let ps_ea := ps_acc ∖ ps_nea in
           pgt_entries_own_excl ps_ea i true ∗
           owned_tran_entries trans ∗
           memory_pages ps_acc ∗
           LB@ i := [ps_na] ∗ ⌜ps_na ## ps_acc⌝ ∗
           i -@{1/2}A> [ps_acc]
    )))%I.

End logrel.


(* TODO:
   - [] rewrite adequacy
   - [] fix mem_send_nz
 *)
