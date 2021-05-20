(* From iris.base_logic.lib Require Import gen_heap ghost_map. *)
From iris.algebra Require Import auth agree dfrac csum excl gmap gmap_view gset.
(* From stdpp Require Import vector. *)
Require Import lang monad.


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
                      gen_trans_preG_inG :> gen_heapPreG W (V * W* W*(gmap V (gset P))*F) Σ;
                      gen_retri_preG_inG :> inG Σ (authR (gmapUR W (gset_disjR (leibnizO V))))
                   }.


 Class gen_VMG Σ := GenVMG{
                      gen_VM_inG :> gen_VMPreG Addr VMID Word RegName PID HvcFunc  Σ;
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
  (authR (gmapUR VMID (agreeR (leibnizO PID)))).

Definition ra_RXBuffer :=
  (prodR ra_TXBuffer
         (optionR (gmap_viewR VMID (optionO (prodO natO (leibnizO VMID)))))).
Definition ra_Accessible:=
  (authR (gmapUR PID (prodR dfracR (csumR (agreeR unitO) (exclR unitO))))).


Definition gen_VMΣ : gFunctors :=
  #[
      GFunctor (agreeR natO);
      gen_heapΣ Addr Word;
      gen_heapΣ (RegName * VMID) Word;
      GFunctor ra_TXBuffer;
      GFunctor ra_RXBuffer;
      GFunctor (authR (gset_disjUR (leibnizO PID)));
      GFunctor ra_Accessible;
      gen_heapΣ Word (VMID * Word * Word * (gmap VMID (gset PID)) * HvcFunc);
      GFunctor (authR (gmapUR Word (gset_disjR (leibnizO VMID))))
   ].

Global Instance subG_gen_VMPreG {Σ}:
  subG gen_VMΣ Σ -> gen_VMPreG Addr VMID Word RegName PID HvcFunc Σ.
Proof.
  (* hack: solve_inG does not currently unfold [subG X _] where X has more than
     4 parameters. We have 6 (A, V, W, R, P, F). *)
  (* set HA := gen_VMΣ. unfold gen_VMΣ in HA. *)
  solve_inG.
Qed.

Section definitions.
  Context `{vmG : !gen_VMG Σ}.
  Implicit Type σ: State.
  Implicit Type δ: VMState.

  Definition get_reg_gmap δ (i: VMID): gmap (RegName * VMID) Word :=
    list_to_map (map  (λ (p: RegName * Word), ((p.1 , i), p.2))
                      (map_to_list (δ.1.1))).

  Definition get_txrx_auth_agree σ (f: MailBox -> PID) :
    ra_TXBuffer:=
    (● ((λ (δ: VMState), to_agree (f δ.1.2)) <$> (vmStates σ))).

  Definition get_rx_state δ :(optionO (prodO natO (leibnizO VMID))):=
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
  Definition get_owned_gset δ : (authR (gset_disjUR PID)) :=
    (● (map_fold (λ (p:PID) (perm:Perm) (s: gset_disjUR PID),
                  match perm.1 with
                  | Owned =>  match s with
                                | GSet s' => GSet (s' ∪ {[p]})
                                | GSetBot => GSet ∅
                              end
                  | Unowned => s
                 end)  (GSet ∅)  δ.2 )).

  Definition get_access_gmap δ : ra_Accessible :=
    (●  (map_fold (λ (p:PID) (perm:Perm) (s: (gmap PID (prodR dfracR (csumR (agreeR unitO) (exclR unitO))))),
                  match perm.2 with
                  | NoAccess => s
                  | SharedAccess => <[p:= ((DfracOwn 1), (Cinl (to_agree ())))]>s
                  | ExclusiveAccess => <[p:= ((DfracOwn 1),(Cinr (Excl ())))]>s
                 end)  ∅  δ.2 )).

  (* TODO *)

  (* Program Fixpoint vec_to_gmap_aux (i: fin VMCount) {n:fin VMCount} (vec: vec (gset PID) n)  : gmap VMID (gset PID):= *)
  (*   foldr *)
  (*   match vec with *)
  (*   | s ::: ss => <[(@nat_to_fin (i-n) VMCount _):=s]>(vec_to_gmap_aux i ss) *)
  (*   | vnil => ∅ *)
  (*   end. *)
  (* Next Obligation. *)
  (*   intros. *)
  (*   pose proof fin_to_nat_lt i. *)
  (*   pose proof fin_to_nat_lt n. *)
  (*   lia. *)
  (* Qed. *)
  (* Search (_ < _ -> _ < _ -> _ < _). *)
  (* Definition to_fin(i m:nat) (n: fin i ) (H: (m < n)) : fin i := (@nat_to_fin m i (Nat.lt_trans m n i H (fin_to_nat_lt n))). *)

  (* Definition fin_coerce {n m :nat} (i : fin n )( lt: fin_to_nat i < m ): fin m := *)
  (*   Fin.of_nat_lt lt. *)

  (* Program Definition to_fin(i m:nat) (n: fin i ) (H: (m < n)) : fin i := (fin_coerce (nat_to_fin H) _). *)
  (* Next Obligation. *)
  (*   intros. *)


  (* Lemma to_nat_eq(i m:nat) (n: fin i) (H: m < n) : (fin_to_nat (to_fin i m n H)) = m. *)
  (*   Proof. *)
  (*     unfold to_fin. *)
  (*     (* unfold to_nat_obligation_1. *) *)
  (*     (* unfold nat_to_fin. *) *)
  (*     pose proof fin_to_nat_lt n. *)
  (*     generalize dependent i. *)
  (*     generalize dependent m. *)
  (*     induction n. *)
  (*     intros. *)
  (*     inversion H. *)
  (*     simpl.  *)
  (*     intros. *)
  (*     (* induction m. *) *)
  (*     (* intros. *) *)
  (*     (* simpl. *) *)
  (*     (* destruct i. *) *)
  (*     (* lia. *) *)
  (*     (* done. *) *)
  (*     (* intros. *) *)
  (*     (* simpl. *) *)
  (*     (* destruct i. *) *)
  (*     (* inversion H0. *) *)
  (*     (* simpl. *) *)
  (*     (* f_equal. *) *)
  (*    pose proof (Nat.lt_trans m (S n0) (S n) H H0). *)
  (*     pose proof (proof_irrel H1 *)
  (*                              (Nat.lt_trans  m (S n0) (S n) H  H0)). *)
  (*     pose proof (proof_irrel H0 (fin_to_nat_lt (FS n0))). *)
  (*     rewrite <- H3. *)
  (*     rewrite <- H2. *)
  (*     Check nat_to_fin_to_nat. *)
  (*     pose proof (nat_to_fin_to_nat  (fin_to_nat_lt (nat_to_fin H1)) ). *)
  (*     rewrite <- H4. *)


  (*     pose proof (proof_irrel H1 (Nat.lt_trans m (nat_to_fin H1) n () (fin_to_nat_lt n))). *)
  (*     rewrite <- H2. *)
  (*     pose proof (IHm i (@nat_to_fin m i H1)). *)

  (*     Search lt_S_n.  *)
  (*     unfold to_fin_obligation_1. *)
  (*     intros. *)
  (*     inversion H0. *)


  (*     inversion H. *)
  (*     destruct m eqn:Heqn. *)
  (*     simpl. *)
  (*     done. *)
  (*     Search nat lt. *)

  (*     apply lt_S_n in H0. *)
  (*     simpl. *)
  (*     destruct n0. *)
  (*     inversion H. *)
  (*     lia. *)
  (*     subst m. *)
  (*     simplify_eq /=. *)

  (* Next Obligation. *)
  (*   intros. *)

  (*   assert (H' : wildcard' < i). *)
  (* pose proof fin_to_nat_lt n. *)
  (* rewrite <- Heq_anonymous in H. *)
  (* Search nat lt. *)
  (* apply (PeanoNat.Nat.lt_succ_l _ _ H). *)
  (* exact (@nat_to_fin wildcard' i H'). *)
  (* Defined. *)
  (* Next Obligation. *)
  (* intros. *)
  (* simpl. *)
  (* pose proof fin_to_nat_lt n. *)
  (* assert (H': wildcard' < i). *)
  (* lia. *)
  (* induction ss. *)
  (* - unfold vec_to_gmap_aux_obligation_2. *)
  (*   simpl. *)
  (*   destruct (fin_to_nat i) eqn:Hi. *)
  (*   lia. *)
  (*   done. *)
  (* - unfold vec_to_gmap_aux_obligation_2. *)
  (*   simpl. *)
  (*   destruct (fin_to_nat i). *)



  (*   assert (Hw: wildcard' <i). *)
  (*   assert (Hw' : wildcard' < (S wildcard'));lia. *)
  (*   unfold vec_to_gmap_aux_obligation_2. *)
  (*   simplify_eq /=. *)
  (*   destruct ss eqn:Hss. *)

  (*   destruct (fin_to_nat i) eqn:Hi. *)
  (*   inversion H'. *)
  (*   rewrite  Heq_anonymous in H1. *)
  (*   unfold vec_to_gmap_aux_obligation_2. *)
  (*   simpl. *)
  (*   lia. *)
  (*   rewrite <- H0 in H'. *)
  (*   inversion H'. *)
  (*   rewrite H3 in H1. *)
  (*   lia. *)
  (*   subst m0. *)
  (*   clear H3. *)
  (*   rewrite  Heq_anonymous in H1. *)
  (*   rewrite H0 in H'. *)
  (*   unfold vec_to_gmap_aux_obligation_2. *)
  (*   simpl. *)
  (*   pose proof fin_to_nat_lt i. *)
  (*   assert (Hm: (S m)< VMCount). *)
  (*   lia. *)
  (*   destruct (fin_to_nat (@nat_to_fin (S m) VMCount Hm)) eqn:Heqn. *)
  (*   inversion Heqn. *)
  (*   destruct VMCount. *)
  (*   lia. *)
  (*   inversion H4. *)
  (*   simplify_eq /=. *)
  (*   destruct VMCount. *)
  (*   lia. *)
  (*   simplify_eq /=. *)

  (*   rewrite H0 in Hm. *)
  (* lia. *)
  (*   inversion Heqn. *)
  (*   lia. *)
  (*   inversion H'. *)


  (* Definition vec_to_gmap{n: fin VMCount} (vec: vec (gset PID) n) : gmap VMID (gset PID):= *)
  (*  (vec_to_gmap_aux n vec). *)

  Definition get_trans_gmap σ : gmap Word (VMID * Word * Word  * (gmap VMID (gset PID)) * HvcFunc).

  Definition gen_vm_interp σ: iProp Σ :=
    let n := (map_size (vmStates σ)) in
    let i := (currentVM σ) in
    match (vmState σ i) with
    | Some δ =>  own (gen_num_name vmG) (to_agree n) ∗
                 ghost_map_auth (gen_mem_name vmG) 1 (mem σ) ∗
                 ghost_map_auth (gen_reg_name vmG) 1 (get_reg_gmap δ i) ∗
                 own (gen_tx_name vmG) (get_txrx_auth_agree σ (λ p, p.1)) ∗
                 own (gen_rx_name vmG) ((get_txrx_auth_agree σ (λ p, p.2.1)),
                                        (Some (gmap_view_auth 1 ((get_rx_state) <$> (vmStates σ))))) ∗
                 own (gen_owned_name vmG) (get_owned_gset δ) ∗
                 own (gen_access_name vmG) (get_access_gmap δ) ∗
                 ghost_map_auth (gen_trans_name vmG) 1 (get_trans_gmap σ)
    | None => True
    end.
