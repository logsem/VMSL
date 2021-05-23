From iris.base_logic.lib Require Import gen_heap ghost_map.
From iris.algebra Require Import auth agree dfrac csum excl gmap gmap_view gset.
From stdpp Require Import listset_nodup.
Require Import lang.


Section RA.
  (* Context{A V W R P F:Type} `{Countable A, Countable V, Countable W, Countable R, Countable P}. *)

  Class gen_VMPreG (A V W R P F: Type) (Σ:gFunctors)
        `{Countable A, Countable V, Countable W, Countable R, Countable P} := {
                      gen_num_preG_inG :> inG Σ (agreeR natO);
                      gen_mem_preG_inG :> gen_heapPreG A W Σ;
                      gen_reg_preG_inG :> gen_heapPreG (R * V) W Σ;
                      gen_tx_preG_inG :> inG Σ (authR (gmapUR V (agreeR (leibnizO P))));
                      gen_rx_preG_inG :> inG Σ (prodR (authR (gmapUR V (agreeR (leibnizO P))))
                                                      (optionR (gmap_viewR V (optionO (prodO natO (leibnizO V))))));
                      gen_owned_preG_inG :> inG Σ (authR (gset_disjUR (leibnizO P)));
                      gen_access_preG_inG :> inG Σ (authR (gmapUR P (prodR dfracR (csumR (agreeR unitO) (exclR unitO)))));
                      gen_trans_preG_inG :> gen_heapPreG W (V * W* W*(gmap V (listset_nodup P))*F) Σ;
                      gen_retri_preG_inG :> inG Σ (authR (gmapUR W (gset_disjR (leibnizO V))))
                   }.


 Class gen_VMG Σ := GenVMG{
                      gen_VM_inG :> gen_VMPreG addr vmid word reg_name pid transaction_type  Σ;
                      gen_num_name : gname;
                      gen_mem_name : gname;
                      gen_reg_name : gname;
                      gen_tx_name : gname;
                      gen_rx_name : gname;
                      gen_owned_name : gname;
                      gen_access_name : gname;
                      gen_trans_name : gname;
                      gen_retri_name : gname
                    }.

Global Arguments gen_num_name {Σ} _.
Global Arguments gen_mem_name {Σ} _.
Global Arguments gen_reg_name {Σ} _.
Global Arguments gen_rx_name {Σ} _.
Global Arguments gen_tx_name {Σ} _.
Global Arguments gen_owned_name {Σ} _.
Global Arguments gen_access_name {Σ} _.
Global Arguments gen_trans_name {Σ} _.
Global Arguments gen_retri_name {Σ} _.

Definition ra_TXBuffer :=
  (authR (gmapUR vmid (agreeR (leibnizO pid)))).

Definition ra_RXBuffer :=
  (prodR ra_TXBuffer
         (optionR (gmap_viewR vmid (optionO (prodO natO (leibnizO vmid)))))).
Definition ra_Accessible:=
  (authR (gmapUR pid (prodR dfracR (csumR (agreeR unitO) (exclR unitO))))).


Definition gen_VMΣ : gFunctors :=
  #[
      GFunctor (agreeR natO);
      gen_heapΣ addr word;
      gen_heapΣ (reg_name * vmid) word;
      GFunctor ra_TXBuffer;
      GFunctor ra_RXBuffer;
      GFunctor (authR (gset_disjUR (leibnizO pid)));
      GFunctor ra_Accessible;
      gen_heapΣ word (vmid * word * word * (gmap vmid (listset_nodup pid)) * transaction_type);
      GFunctor (authR (gmapUR word (gset_disjR (leibnizO vmid))))
   ].

Global Instance subG_gen_VMPreG {Σ}:
  subG gen_VMΣ Σ -> gen_VMPreG addr vmid word reg_name pid transaction_type Σ.
Proof.
  (* hack: solve_inG does not currently unfold [subG X _] where X has more than
     4 parameters. We have 6 (A, V, W, R, P, F). *)
  (* set HA := gen_VMΣ. unfold gen_VMΣ in HA. *)
  solve_inG.
Qed.

Section definitions.
  Context `{vmG : !gen_VMG Σ}.
  Implicit Type σ: state.
  Implicit Type δ: vm_state.

  Definition get_reg_gmap δ (i: vmid): gmap (reg_name * vmid) word :=
    list_to_map (map  (λ (p: reg_name * word), ((p.1 , i), p.2))
                      (map_to_list (δ.1.1))).

  Program Fixpoint vector_of_vmids_aux(n:nat) (H:n<vm_count) : vec vmid (S n):=
    match n with
      | S m => (nat_to_fin H) ::: (vector_of_vmids_aux m _)
      | 0  => (nat_to_fin H):::vnil
    end.
  Next Obligation.
    Proof.
      intros.
      lia.
  Defined.

    Program Definition vector_of_vmids :vec vmid vm_count :=
    vector_of_vmids_aux (vm_count-1) _.
    Next Obligation.
     Proof.
        simpl.
        pose proof vm_count_pos.
        pose vm_count.
        lia.
     Qed.
     Next Obligation.
       Proof.
        pose vm_count.
        pose proof vm_count_pos.
        lia.
      Qed.

    (* Definition vec_to_gmap{A:Type}{B : cmra}  (vec: vec A vm_count)  : gmapUR vmid B:= *)
    (* (foldr (λ p acc, <[p.1:=p.2]>acc) ∅ *)
    (*        (vzip_with (λ v s, (v,s)) (vector_of_vmids) vec)). *)

    (* TODO : how to convert a gmap to gmapUR?*)
    (* Definition get_txrx_auth_agree σ (f: mail_box -> pid) : *)
    (* ra_TXBuffer:= *)
    (* (● (vec_to_gmap (vmap (λ δ, (to_agree (f δ.1.2)))  (get_vm_states σ)))). *)


   Definition get_txrx_auth_agree σ (f: mail_box -> pid) :
    ra_TXBuffer:=
    (● (foldr (λ p acc, <[p.1:=p.2]>acc) ∅
              (vzip_with (λ v δ, (v,to_agree (f δ.1.2))) (vector_of_vmids) (get_vm_states σ)))).


  Definition get_rx_state δ :(optionO (prodO natO (leibnizO vmid))):=
    let mb := δ.1.2 in
    match mb.2.2 with
      | Some j => (Some (0, j))
      | None => None
    end.
   (* HACK : don't know why *)
   (* match perm.1 with *)
   (*                | Owned => s ⊎ {[ p ]} *)
   (*                | Unowned => s *)
   (*               end ) *)
   (* doesn't work...*)
  Definition get_owned_gset δ : (authR (gset_disjUR pid)) :=
    (● (map_fold (λ (p:pid) (perm:permission) (s: gset_disjUR pid),
                  match perm.1 with
                  | Owned =>  match s with
                                | GSet s' => GSet (s' ∪ {[p]})
                                | GSetBot => GSet ∅
                              end
                  | Unowned => s
                 end)  (GSet ∅)  δ.2 )).

  Definition get_access_gmap δ : ra_Accessible :=
    (●  (map_fold (λ (p:pid) (perm:permission) (s: (gmap pid (prodR dfracR (csumR (agreeR unitO) (exclR unitO))))),
                  match perm.2 with
                  | NoAccess => s
                  | SharedAccess => <[p:= ((DfracOwn 1), (Cinl (to_agree ())))]>s
                  | ExclusiveAccess => <[p:= ((DfracOwn 1),(Cinr (Excl ())))]>s
                 end)  ∅  δ.2 )).


  Program Fixpoint vec_to_gmap{A:Type}  (vec: vec A vm_count)  : gmap vmid A:=
    (foldr (λ p acc, <[p.1:=p.2]>acc) ∅
           (vzip_with (λ v s, (v,s)) (vector_of_vmids) vec)).
  (* TODO we need getters for transations.. *)
  Definition get_trans_gmap σ : gmap word (vmid * word * word  * (gmap vmid (listset_nodup pid)) * transaction_type):=
   (map_fold (λ (h:word) (trans: transaction) m,
                  <[h:=((((trans.1.1.1.1.1, trans.1.1.1.1.2), trans.1.1.1.2), (vec_to_gmap trans.1.2)), trans.2)]>m
      ) ∅ (get_transactions σ)).
  
  Definition get_receivers_gset σ : authR (gmapUR word (gset_disjR (leibnizO vmid))) :=
    let transactions := get_transactions σ
    in ● (map_fold (λ (h : word) (trn : transaction) m, <[h:=GSet (trn.1.1.2)]>m) ∅ transactions).
  
  Definition gen_vm_interp σ: iProp Σ :=
    let i := (get_current_vm σ) in
    let δ := (get_vm_state σ i) in
      own (gen_num_name vmG) (to_agree vm_count)∗
      ghost_map_auth (gen_mem_name vmG) 1 (get_mem σ) ∗
      ghost_map_auth (gen_reg_name vmG) 1 (get_reg_gmap δ i) ∗
      own (gen_tx_name vmG) (get_txrx_auth_agree σ (λ p, p.1)) ∗
      own (gen_rx_name vmG)
        ((get_txrx_auth_agree σ (λ p, p.2.1.1)),
          (Some (gmap_view_auth 1
            (vec_to_gmap (vmap (get_rx_state) (get_vm_states σ)))))) ∗
      own (gen_owned_name vmG) (get_owned_gset δ) ∗
      own (gen_access_name vmG) (get_access_gmap δ) ∗
      ghost_map_auth (gen_trans_name vmG) 1 (get_trans_gmap σ) ∗
      own (gen_retri_name vmG) (get_receivers_gset σ)
    .
