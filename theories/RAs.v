From iris.base_logic.lib Require Import gen_heap ghost_map invariants na_invariants.
From iris.algebra Require Import auth agree dfrac csum excl gmap gmap_view gset frac_agree.
From iris.proofmode Require Import tactics.
From HypVeri Require Export lang machine.

  Class gen_VMPreG (A V W R P F: Type) (Σ:gFunctors)
        `{Countable A, Countable V, Countable W, Countable R, Countable P} := {
                      (* gen_num_preG_inG :> inG Σ (agreeR natO); *)
                      gen_token_preG_inG :> inG Σ (frac_agreeR (leibnizO V));
                      gen_mem_preG_inG :> gen_heapGpreS A W Σ;
                      gen_reg_preG_inG :> gen_heapGpreS (R * V) W Σ;
                      gen_tx_preG_inG :> inG Σ (authR (gmapUR V (agreeR (leibnizO P))));
                      gen_rx_preG_inG :> inG Σ (prodR (authR (gmapUR V (agreeR (leibnizO P))))
                                                      (optionR (gmap_viewR V (optionO (prodO (leibnizO W) (leibnizO V))))));
                      (* gen_owned_preG_inG :> inG Σ (authR (gset_disjUR (leibnizO P))); *)
                      (* gen_access_preG_inG :> inG Σ (authR (gmapUR P (prodR dfracR (csumR (agreeR unitO) (exclR unitO))))); *)
                      gen_owned_preG_inG :> inG Σ (authR (gmapUR V
                                    (prodR dfracR (agreeR (gset_disjUR (leibnizO P))))));
                      (* gen_access_preG_inG :> inG Σ (authR (gmapUR V *)
                                    (* (prodR dfracR (gmapUR P (csumR (agreeR unitO) (exclR unitO)))))); *)
                      gen_access_preG_inG :> inG Σ (authR (gmapUR V
                                                    (prodR dfracR (agreeR (gset_disjUR (leibnizO P))))));
                      gen_trans_preG_inG :> gen_heapGpreS W (V * W* W*(gmap V (gset P))*F) Σ;
                      gen_hpool_preG_inG :> inG Σ (frac_agreeR (gset_disjR (leibnizO W)));
                      gen_retri_preG_inG :> inG Σ (authR (gmapUR W (gset_disjR (leibnizO V))))
                   }.


  Class gen_VMG Σ := GenVMG{
                      gen_VM_inG :> gen_VMPreG Addr VMID Word reg_name PID transaction_type Σ;
                      gen_invG :> invGS Σ;
                      gen_na_invG :> na_invG Σ;
                      gen_nainv_name : na_inv_pool_name;
                      gen_token_name : gname;
                      (* gen_num_name : gname; *)
                      gen_mem_name : gname;
                      gen_reg_name : gname;
                      gen_tx_name : gname;
                      gen_rx_name : gname;
                      gen_owned_name : gname;
                      gen_access_name : gname;
                      gen_trans_name : gname;
                      gen_hpool_name : gname;
                      gen_retri_name : gname
                    }.

Global Arguments gen_nainv_name {Σ} _.
(* Global Arguments gen_num_name {Σ} _. *)
Global Arguments gen_token_name {Σ} _.
Global Arguments gen_mem_name {Σ} _.
Global Arguments gen_reg_name {Σ} _.
Global Arguments gen_rx_name {Σ} _.
Global Arguments gen_tx_name {Σ} _.
Global Arguments gen_owned_name {Σ} _.
Global Arguments gen_access_name {Σ} _.
Global Arguments gen_trans_name {Σ} _.
Global Arguments gen_hpool_name {Σ} _.
Global Arguments gen_retri_name {Σ} _.

Definition ra_TXBuffer :=
  (authR (gmapUR VMID (agreeR (leibnizO PID)))).

Definition ra_RXBuffer :=
  (prodR ra_TXBuffer
         (optionR (gmap_viewR VMID (optionO (prodO (leibnizO Word) (leibnizO VMID)))))).
Definition ra_Accessible:=
  (* (authR (gmapUR vmid (prodR dfracR (gmapUR pid  (csumR (agreeR unitO) (exclR unitO)))))). *)
  (* (authR (gmapUR pid (prodR dfracR (csumR (agreeR unitO) (exclR unitO))))). *)
  (authR (gmapUR VMID (prodR dfracR (agreeR (gset_disjUR (leibnizO PID)))))).



Definition gen_VMΣ : gFunctors :=
  #[
      invΣ;
      na_invΣ;
      (* GFunctor (agreeR natO); *)
      GFunctor (frac_agreeR (leibnizO VMID));
      gen_heapΣ Addr Word;
      gen_heapΣ (reg_name * VMID) Word;
      GFunctor ra_TXBuffer;
      GFunctor ra_RXBuffer;
      GFunctor (authR (gmapUR VMID (prodR dfracR (agreeR (gset_disjUR (leibnizO PID))))));
      (* GFunctor (authR (gset_disjUR (leibnizO pid))); *)
      GFunctor ra_Accessible;
      gen_heapΣ Word (VMID * Word * Word * (gmap VMID (gset PID)) * transaction_type);
      GFunctor (frac_agreeR (gset_disjR (leibnizO Word)));
      GFunctor (authR (gmapUR Word (gset_disjR (leibnizO VMID))))
   ].

Global Instance subG_gen_VMPreG {Σ}:
  subG gen_VMΣ Σ -> gen_VMPreG Addr VMID Word reg_name PID transaction_type Σ.
Proof.
  (* hack: solve_inG does not currently unfold [subG X _] where X has more than
     4 parameters. We have 6 (A, V, W, R, P, F). *)
  (* set HA := gen_VMΣ. unfold gen_VMΣ in HA. *)
  solve_inG.
Qed.

Section definitions.
  Context `{vmG : !gen_VMG Σ}.
  Implicit Type σ: state.


  Definition list_of_vmids  := vec_to_list (fun_to_vec (λ v: fin vm_count, v)).

  Lemma in_list_of_vmids v: In v  list_of_vmids.
  Proof.
    apply elem_of_list_In.
    apply elem_of_vlookup.
    exists v.
    apply lookup_fun_to_vec.
  Qed.

  Definition get_token  (v:VMID) :=
     (to_frac_agree (1/2) (v: leibnizO VMID)).

  Definition get_reg_gmap σ: gmap (reg_name * VMID) Word :=
     (list_to_map (flat_map (λ v, (map (λ p, ((p.1,v),p.2)) (map_to_list (get_vm_reg_file σ v)))) (list_of_vmids))).


  Definition get_txrx_auth_agree σ (f: mail_box -> PID) :
    ra_TXBuffer:=
    (● (list_to_map (map (λ v, (v,to_agree (f (get_vm_mail_box σ v)))) (list_of_vmids) )
    )).

  Definition get_tx_agree σ := get_txrx_auth_agree σ (λ p, p.1).


  Definition get_rx_agree σ := get_txrx_auth_agree σ (λ p, p.2.1).



  Definition get_rx_gmap σ :=
    (Some (gmap_view_auth 1
            ((list_to_map (map (λ v, let mb := (get_vm_mail_box σ v) in
                                    match mb.2.2 with
                                      | Some (l, j) => (v, (Some ( l, j)))
                                      | None => (v,None)
                                    end) (list_of_vmids))): (gmap VMID (optionO (prodO (leibnizO Word) (leibnizO VMID))) )))).


  (* XXX:  seems like we have to keep resources being indexed by VMIDs...  *)

  (* Definition get_owned_gset δ : (authR (gset_disjUR PID)) := *)
  (*   (● (map_fold (λ (p:PID) (perm:permission) (s: gset_disjUR PID), *)
  (*                 match perm.1 with *)
  (*                 | Owned =>  match s with *)
  (*                               | GSet s' => GSet (s' ∪ {[p]}) *)
  (*                               | GSetBot => GSet ∅ *)
  (*                             end *)
  (*                 | Unowned => s *)
  (*                end)  (GSet ∅) δ.2)). *)


  (* Definition get_access_gmap δ : ra_Accessible := *)
  (*   (●  (map_fold (λ (p:PID) (perm:permission) (s: (gmap PID (prodR dfracR (csumR (agreeR unitO) (exclR unitO))))), *)
  (*                 match perm.2 with *)
  (*                 | NoAccess => s *)
  (*                 | SharedAccess => <[p:= ((DfracOwn 1), (Cinl (to_agree ())))]>s *)
  (*                 | ExclusiveAccess => <[p:= ((DfracOwn 1),(Cinr (Excl ())))]>s *)
  (*                end)  ∅  δ.2 )). *)

  (* XXX: another attempt: *)

  Definition get_owned_gmap σ : (authR (gmapUR VMID (prodR dfracR (agreeR (gset_disjUR PID))))) :=
    (● (list_to_map (map (λ v, (v, ((DfracOwn 1),
        to_agree (GSet ((list_to_set (map (λ (p:(PID*permission)), p.1)
           (map_to_list (filter (λ p, (is_owned p.2) = true) (get_vm_page_table σ v)))))
                         : gset PID))))) (list_of_vmids)))).


  (* Definition get_access_gmap σ : ra_Accessible := *)
  (*   (● (list_to_map (map (λ v, (v, ((DfracOwn 1),(map_fold (λ (p:PID) (perm:permission) (s: (gset_disjUR PID)), *)
  (*                 match (is_accessible perm) with *)
  (*                 | false => s *)
  (*                 | true => match s with *)
  (*                                     | GSet s' => GSet (s' ∪ {[p]}) *)
  (*                                     | GSetBot => GSet ∅ *)
  (*                                   end *)
  (*                end) (GSet ∅) (get_vm_page_table σ v))))) (list_of_VMIDs)))). *)

  Definition get_access_gmap σ : ra_Accessible :=
    (● (list_to_map (map (λ v, (v, ((DfracOwn 1),
        to_agree (GSet ((list_to_set (map (λ (p:(PID*permission)), p.1)
           (map_to_list (filter (λ p, (is_accessible p.2) = true) (get_vm_page_table σ v)))))
                         : gset PID))))) (list_of_vmids)))).

  (* TODO: a new exclusive ra*)


  (* TODO we need getters for transations.. *)
  Definition get_trans_gmap σ : gmap Word (VMID * Word * Word  * (gmap VMID (gset PID)) * transaction_type):=
    list_to_map (map (λ (p:Word * transaction) ,
                      let trans := p.2 in
                         (p.1,((((trans.1.1.1.1.1, trans.1.1.1.1.2), trans.1.1.1.2),  trans.1.2), trans.2))
                     )  (map_to_list (get_transactions σ).1)).
  Definition get_trans_gset σ :=
    (to_frac_agree (1/2) (GSet (get_transactions σ).2)).

  Definition get_receivers_gmap σ : authR (gmapUR Word (gset_disjR (leibnizO VMID))) :=
    ● (list_to_map (map (λ (p:Word * transaction) ,
                      let trans := p.2 in
                  (p.1,(GSet trans.1.1.2))) (map_to_list (get_transactions σ).1))).

  Definition gen_vm_interp σ: iProp Σ :=
      (* XXX: seems like (to_agree vm_count) is not very useful ...*)
      (* own (gen_num_name vmG) (to_agree vm_count)∗ *)
      own (gen_token_name vmG) (get_token (get_current_vm σ)) ∗
      ghost_map_auth (gen_mem_name vmG) 1 (get_mem σ) ∗
      ghost_map_auth (gen_reg_name vmG) 1 (get_reg_gmap σ) ∗
      own (gen_tx_name vmG) (get_tx_agree σ) ∗
      own (gen_rx_name vmG) ((get_rx_agree σ), (get_rx_gmap σ) )∗
      own (gen_owned_name vmG) (get_owned_gmap σ) ∗
      own (gen_access_name vmG) (get_access_gmap σ) ∗
      ghost_map_auth (gen_trans_name vmG) 1 (get_trans_gmap σ) ∗
      own (gen_hpool_name vmG) (get_trans_gset σ) ∗
      own (gen_retri_name vmG) (get_receivers_gmap σ)
    .


  (* Definition num_agree_def (n:nat) : iProp Σ := *)
  (*   own (gen_num_name vmG) (to_agree n). *)
  (* Definition num_agree_aux : seal (@num_agree_def). Proof. by eexists. Qed. *)
  (* Definition num_agree:= num_agree_aux.(unseal). *)
  (* Definition num_agree_eq : @num_agree = @num_agree_def := num_agree_aux.(seal_eq). *)


  Definition token_agree_def (v:VMID) : iProp Σ :=
    own (gen_token_name vmG) (get_token v) .
  Definition token_agree_aux : seal (@token_agree_def). Proof. by eexists. Qed.
  Definition token_agree:= token_agree_aux.(unseal).
  Definition token_agree_eq : @token_agree = @token_agree_def := token_agree_aux.(seal_eq).


  Definition mem_mapsto_def (a:Addr) (dq : dfrac) (w:Word) : iProp Σ :=
    (ghost_map_elem (gen_mem_name vmG) a dq w).
    (* own (gen_mem_name vmG) (gmap_view_frag a dq (w : leibnizO Word)). *)
  Definition mem_mapsto_aux : seal (@mem_mapsto_def). Proof. by eexists. Qed.
  Definition mem_mapsto := mem_mapsto_aux.(unseal).
  Definition mem_mapsto_eq : @mem_mapsto = @mem_mapsto_def := mem_mapsto_aux.(seal_eq).

  Definition reg_mapsto_def (r:reg_name) (i:VMID) (dq : dfrac) (w:Word) : iProp Σ :=
    (ghost_map_elem (gen_reg_name vmG) (r,i) dq w).
    (* own (gen_reg_name vmG) (gmap_view_frag (r,i) dq (w : leibnizO Word)). *)
  Definition reg_mapsto_aux : seal (@reg_mapsto_def). Proof. by eexists. Qed.
  Definition reg_mapsto := reg_mapsto_aux.(unseal).
  Definition reg_mapsto_eq : @reg_mapsto = @reg_mapsto_def := reg_mapsto_aux.(seal_eq).

  Definition tx_mapsto_def (i:VMID) (p:PID) : iProp Σ :=
    own (gen_tx_name vmG) (◯ {[i := (to_agree (p: leibnizO PID))]}).
  Definition tx_mapsto_aux : seal (@tx_mapsto_def). Proof. by eexists. Qed.
  Definition tx_mapsto := tx_mapsto_aux.(unseal).
  Definition tx_mapsto_eq : @tx_mapsto = @tx_mapsto_def := tx_mapsto_aux.(seal_eq).

  Definition rx_mapsto_def1 (i:VMID) (p:PID) (nr : option (Word *  VMID)) : iProp Σ :=
    match nr with
      | Some (n, r) =>
        own (gen_rx_name vmG) ((◯ {[i := (to_agree p)]}),
                               (Some (gmap_view_frag i (DfracOwn 1) (Some ((n:(leibnizO Word)), (r: leibnizO VMID))))))
      | None =>
        own (gen_rx_name vmG) ((◯ {[i := (to_agree p)]}),
                               (Some (gmap_view_frag i (DfracOwn 1) None)))
    end.
  Definition rx_mapsto_aux1 : seal (@rx_mapsto_def1). Proof. by eexists. Qed.
  Definition rx_mapsto1 := rx_mapsto_aux1.(unseal).
  Definition rx_mapsto_eq1 : @rx_mapsto1 = @rx_mapsto_def1 := rx_mapsto_aux1.(seal_eq).

  Definition rx_mapsto_def2 (i:VMID) (p:PID) : iProp Σ :=
    own (gen_rx_name vmG) ((◯ {[i := (to_agree p)]}),None).
  Definition rx_mapsto_aux2 : seal (@rx_mapsto_def2). Proof. by eexists. Qed.
  Definition rx_mapsto2 := rx_mapsto_aux2.(unseal).
  Definition rx_mapsto_eq2 : @rx_mapsto2 = @rx_mapsto_def2 := rx_mapsto_aux2.(seal_eq).

  Definition owned_mapsto_def (i:VMID) dq (s: gset_disj PID) : iProp Σ :=
    own (gen_owned_name vmG) (◯ {[i := (dq, to_agree s)]}).
  (* Definition owned_mapsto_def (s: gset_disj PID) : iProp Σ := *)
    (* own (gen_owned_name vmG) (◯ s). *)
  Definition owned_mapsto_aux : seal (@owned_mapsto_def). Proof. by eexists. Qed.
  Definition owned_mapsto := owned_mapsto_aux.(unseal).
  Definition owned_mapsto_eq : @owned_mapsto = @owned_mapsto_def := owned_mapsto_aux.(seal_eq).

  (* Definition access_mapsto_def (i:VMID) dq (m: gmap PID access) : iProp Σ := *)
  (*   own (gen_access_name vmG) (◯ {[i := (dq, (map_fold (λ p a acc, *)
  (*                                                      match a with *)
  (*                                                        | NoAccess => acc *)
  (*                                                        | SharedAccess => <[p:=(Cinl (to_agree ()))]>acc *)
  (*                                                        | ExclusiveAccess => <[p:=(Cinr (Excl ()))]>acc *)
  (*                                                      end) ∅ m))]}). *)
  (* Definition access_mapsto_def dq (m: gmap PID access) : iProp Σ := *)
  (*   own (gen_access_name vmG) (◯ (map_fold (λ p a acc, *)
  (*                                                      match a with *)
  (*                                                        | NoAccess => acc *)
  (*                                                        | SharedAccess => <[p:=(dq, (Cinl (to_agree ())))]>acc *)
  (*                                                        | ExclusiveAccess => <[p:=(dq, (Cinr (Excl ())))]>acc *)
  (*                                                      end) ∅ m)). *)
  Definition access_mapsto_def (i:VMID) dq (s: gset_disj PID) : iProp Σ :=
    own (gen_access_name vmG) (◯ {[i := (dq, to_agree s)]}).
  Definition access_mapsto_aux : seal (@access_mapsto_def). Proof. by eexists. Qed.
  Definition access_mapsto := access_mapsto_aux.(unseal).
  Definition access_mapsto_eq : @access_mapsto = @access_mapsto_def := access_mapsto_aux.(seal_eq).

  Definition trans_mapsto_def(wh : Word) dq (v: VMID) (wf: Word) (wt: Word) (pgs : gmap VMID (gset PID)) (fid : transaction_type) : iProp Σ :=
    own (gen_trans_name vmG) (gmap_view_frag wh dq
                          (((((v, wf) , wt), pgs), fid): (leibnizO (VMID * Word * Word * (gmap VMID (gset PID)) * transaction_type)))).
  Definition trans_mapsto_aux : seal (@trans_mapsto_def). Proof. by eexists. Qed.
  Definition trans_mapsto := trans_mapsto_aux.(unseal).
  Definition trans_mapsto_eq : @trans_mapsto = @trans_mapsto_def := trans_mapsto_aux.(seal_eq).

  Definition retri_mapsto_def (w:Word) (s: gset_disj VMID) : iProp Σ :=
    own (gen_retri_name vmG) (◯ {[w := s]}).
  Definition retri_mapsto_aux : seal (@retri_mapsto_def). Proof. by eexists. Qed.
  Definition retri_mapsto := retri_mapsto_aux.(unseal).
  Definition retri_mapsto_eq : @retri_mapsto = @retri_mapsto_def := retri_mapsto_aux.(seal_eq).

End definitions.

(* predicate for the number of vms *)
(* Notation "## n" := (num_agree n) *)
(*                         (at level 50, format "## n"): bi_scope. *)

(* predicate for current vm (token) *)

Notation "<< n >>" := (token_agree n)
                        (at level 50, format "<< n >>"): bi_scope.

(* point-to predicates for registers and memory *)
Notation "r @@ i ->r{ q } w" := (reg_mapsto r i (DfracOwn q) w)
  (at level 22, q at level 50, format "r @@ i ->r{ q } w") : bi_scope.
Notation "r @@ i ->r w" :=
  (reg_mapsto r i (DfracOwn 1) w) (at level 21, w at level 50) : bi_scope.

Notation "a ->a{ q } w" := (mem_mapsto a (DfracOwn q) w)
  (at level 20, q at level 50, format "a ->a{ q } w") : bi_scope.
Notation "a ->a w" := (mem_mapsto a (DfracOwn 1) w) (at level 20) : bi_scope.

(* predicates for TX and RX *)
Notation "TX@ i := p" := (tx_mapsto i p)
                              (at level 20, format "TX@ i := p"): bi_scope.
Notation "RX@ i :=( p ! n , r )" := (rx_mapsto1 i p (Some (n, r)))
                                        (at level 20, format "RX@ i :=( p ! n , r )"):bi_scope.
Notation "RX@ i :=( p !)" := (rx_mapsto1 i p None)
                                        (at level 20, format "RX@ i :=( p !)"):bi_scope.
Notation "RX@ i := p " := (rx_mapsto2 i p)
                                        (at level 20, format "RX@ i := p"):bi_scope.

(* predicates for pagetables *)
Notation "O@ i :={ q }[ s ] " := (owned_mapsto i (DfracOwn q) (GSet s))
                                           (at level 20, format "O@ i :={ q }[ s ] "):bi_scope.
Notation "O@ i :={ q } p" := (owned_mapsto  i (DfracOwn q) (GSet {[p]}))
                                           (at level 20, format "O@ i :={ q } p "):bi_scope.

Notation "A@ i :={ q }[ s ] " := (access_mapsto i (DfracOwn q) (GSet s))
                                          (at level 20, format "A@ i :={ q }[ s ] "):bi_scope.
Notation "A@ i :={ q } p " := (access_mapsto  i (DfracOwn q) (GSet {[p]}))
                                           (at level 20, format "A@ i :={ q } p "):bi_scope.


(* predicates for transactions *)
Notation "w ->t{ q }( v , x , y , m , f )" := (trans_mapsto w (DfracOwn q) v x y m f)
                                                   (at level 20, format "w ->t{ q }( v , x , y , m , f )"):bi_scope.
Notation "w ->re[ s ]" := (retri_mapsto w (GSet s))
                              (at level 20, format "w ->re[ s ]"):bi_scope.
Notation "w ->re v" := (retri_mapsto w (GSet {[v]}))
                          (at level 20, format "w ->re v"):bi_scope.

Section hyp_lang_rules.

  Context `{vmG :!gen_VMG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : state.
  Implicit Types a b c : Addr.
  Implicit Types r : reg_name.
  Implicit Types w: Word.


  Lemma token_valid i1 i2 :
   << i1 >> -∗
      << i2 >> -∗
      ⌜ i1 = i2 ⌝.
  Proof.
    rewrite token_agree_eq /token_agree_def.
    iIntros "H1 H2".
    iDestruct (own_valid_2  with "H1 H2") as %Hvalid.
    rewrite /get_token in Hvalid.
    apply frac_agree_op_valid_L in Hvalid.
    destruct Hvalid;done.
   Qed.

    Lemma token_update i1 i2 :
   << i1 >> -∗
      << i1 >> ==∗
      << i2 >> ∗ << i2 >>.
  Proof.
    rewrite token_agree_eq /token_agree_def /get_token.
    rewrite -own_op.
    iApply own_update_2.
    rewrite - frac_agree_op.
    pose proof (to_frac_agree_exclusive (i1: leibnizO VMID)).
    assert (Heq:  ( 1/2 + 1/2 =  1)%Qp ).
    { apply (bool_decide_unpack _). by compute. }
    rewrite Heq.
    apply (cmra_update_exclusive ).
    rewrite -frac_agree_op.
    unfold to_frac_agree.
    rewrite Heq.
    apply pair_valid.
    split;done.
  Qed.

   Lemma gen_token_valid_neq{σ} i j:
   i ≠ j ->
   << i >> -∗
   own (gen_token_name vmG) (get_token (get_current_vm σ)) -∗
   ⌜ ¬ scheduler σ j ⌝.
  Proof.
    iIntros (Hne) "Htok Hstate".
    rewrite token_agree_eq /token_agree_def.
     iDestruct (own_valid_2  with "Htok Hstate") as %Hvalid.
    rewrite /get_token in Hvalid.
    apply frac_agree_op_valid_L in Hvalid.
    destruct Hvalid.
    iPureIntro.
    rewrite /scheduler -H0.
    intro.
    apply fin_to_nat_inj in H1.
    done.
    Qed.

  (* rules for register points-to *)

  Lemma reg_dupl_false r i w1 w2 :
   r @@ i ->r w1 -∗ r @@ i ->r w2 -∗ False.
  Proof using.
    rewrite reg_mapsto_eq /reg_mapsto_def.
    iIntros "Hr1 Hr2".
    iDestruct (ghost_map_elem_valid_2 with "Hr1 Hr2") as %?.
    destruct H.
    apply dfrac_valid_own_r in H.
    inversion H.
  Qed.

  Lemma reg_neq r1 r2 i j w1 w2:
   r1 @@ i ->r w1 -∗ r2 @@ j ->r w2 -∗ ⌜ r1 <> r2 ∨ i <> j⌝.
  Proof using.
    iIntros "Hr1 Hr2".
    destruct (decide (r1 = r2)).
    destruct (decide (i = j)).
    - simplify_eq /=.
      iDestruct (reg_dupl_false with "Hr1 Hr2") as %[].
    - iRight. done.
    - iLeft. done.
  Qed.

Lemma gen_reg_valid1:
  ∀ (σ : state) r i w,
    (get_current_vm σ) = i ->
    ghost_map_auth (gen_reg_name vmG) 1 (get_reg_gmap σ) -∗
    r @@ i ->r w -∗
          ⌜ (get_reg σ r) = Some w ⌝.
Proof.
  iIntros (?????) "Hσ Hr".
  rewrite reg_mapsto_eq /reg_mapsto_def.
  iDestruct (ghost_map_lookup with "Hσ Hr") as "%".
  iPureIntro.
  rewrite /get_reg /get_reg_global.
  unfold get_reg_gmap in H0.
  apply elem_of_list_to_map_2 in H0.
  apply elem_of_list_In in H0.
  apply in_flat_map in H0.
  inversion H0; clear H0.
  destruct H1.
  apply in_map_iff in H1.
  inversion H1;clear H1.
  inversion H2;clear H2.
  inversion H1.
  apply elem_of_list_In in H3.
  apply elem_of_map_to_list' in H3.
  by simplify_eq /=.
Qed.


Lemma gen_reg_valid_global1:
  ∀ (σ : state) r i w,
    ghost_map_auth (gen_reg_name vmG) 1 (get_reg_gmap σ) -∗
    r @@ i ->r w -∗
          ⌜ (get_reg_global σ i r) = Some w ⌝.
Proof.
  iIntros (????) "Hσ Hr".
  rewrite reg_mapsto_eq /reg_mapsto_def.
  iDestruct (ghost_map_lookup with "Hσ Hr") as "%".
  iPureIntro.
  rewrite /get_reg /get_reg_global.
  unfold get_reg_gmap in H.
  apply elem_of_list_to_map_2 in H.
  apply elem_of_list_In in H.
  apply in_flat_map in H.
  inversion H; clear H.
  destruct H0.
  apply in_map_iff in H0.
  inversion H0;clear H0.
  inversion H1;clear H1.
  inversion H0.
  apply elem_of_list_In in H2.
  apply elem_of_map_to_list' in H2.
  by simplify_eq /=.
Qed.


(* TODO : quite ugly... *)
Lemma gen_reg_valid_Sep:
  ∀ (σ : state) i (regs: gmap (reg_name * VMID) Word) ,
    (get_current_vm σ) = i ->
    ghost_map_auth (gen_reg_name vmG) 1 (get_reg_gmap σ) -∗
    ([∗ map] r↦w ∈ regs,  r.1 @@ r.2 ->r w)-∗
          ([∗ map] r↦w ∈ regs, ⌜r.2 = i -> (get_reg σ r.1) = Some w ⌝).
Proof.
  iIntros (????) "Hσ Hregs".
  rewrite reg_mapsto_eq /reg_mapsto_def.
  iDestruct ((ghost_map_lookup_big regs) with "Hσ [Hregs]") as "%Hincl".
  iApply (big_sepM_proper (λ k x, (k.1, k.2)↪[gen_reg_name vmG] x)%I).
  intros.
  simplify_eq.
  f_equiv.
  by destruct k.
  done.
  iApply big_sepM_pure.
  iIntros (????).
  rewrite /get_reg /get_reg_global.
  apply (lookup_weaken  _ (get_reg_gmap σ) _ _) in a1;eauto.
  apply elem_of_list_to_map_2 in a1.
  apply elem_of_list_In in a1.
  apply in_flat_map in a1.
  inversion a1; clear a1.
  destruct H0.
  apply in_map_iff in H1.
  inversion H1;clear H1.
  inversion H2;clear H2.
  inversion H1.
  apply elem_of_list_In in H3.
  apply elem_of_map_to_list' in H3.
  by simplify_eq /=.
Qed.

Lemma gen_reg_valid2:
  ∀ (σ : state) i r1 w1 r2 w2 ,
    (get_current_vm σ) = i ->
    r1 ≠ r2->
    ghost_map_auth (gen_reg_name vmG) 1 (get_reg_gmap σ) -∗
                r1 @@ i ->r w1 -∗
                             r2 @@ i ->r w2 -∗
           ⌜ (get_reg σ r1) = Some w1 ⌝ ∗ ⌜ (get_reg σ r2) =Some w2 ⌝.
Proof.
  iIntros (?????? Hneq Hi) "Hreg Hr1 Hr2".
  iDestruct ((gen_reg_valid_Sep σ i (<[(r1,i):=w1]>{[(r2,i):=w2]}))
               with "Hreg [Hr1 Hr2]") as "%Hreg";eauto.
  rewrite !big_sepM_insert ?big_sepM_empty;eauto.
  iFrame.
  apply lookup_insert_None; split;eauto; intros P; by inversion P.
  iPureIntro.
  split.
  - by apply (Hreg (r1, i) w1 (lookup_insert _ (r1, i) w1)).
  - apply (Hreg (r2, i) w2);eauto.
    rewrite lookup_insert_Some;right;split;
    [intros P; inversion P; contradiction|];
    by rewrite !lookup_insert.
 Qed.


Lemma gen_reg_valid3:
  ∀ (σ : state) i r1 w1 r2 w2 r3 w3 ,
    (get_current_vm σ) = i ->
    r1 ≠ r2->
    r1 ≠ r3->
    r2 ≠ r3->
    ghost_map_auth (gen_reg_name vmG) 1 (get_reg_gmap σ) -∗
    r1 @@ i ->r w1 -∗
    r2 @@ i ->r w2 -∗
    r3 @@ i ->r w3 -∗
                ⌜ (get_reg σ r1) = Some w1 ⌝ ∗ ⌜ (get_reg σ r2) =Some w2 ⌝ ∗ ⌜ (get_reg σ r3) = Some w3⌝.
Proof.
  iIntros (???????? Hi Hneq1 Hneq2 Hneq3) "Hreg Hr1 Hr2 Hr3".
  iDestruct ((gen_reg_valid_Sep σ i ({[(r1,i):=w1;(r2,i):=w2;(r3,i):=w3]}))
               with "Hreg [Hr1 Hr2 Hr3]") as "%Hreg";eauto.
  rewrite !big_sepM_insert ?big_sepM_empty;eauto.
  iFrame.
  apply lookup_insert_None; split;eauto; intros P; by inversion P.
  apply lookup_insert_None; split;eauto.
  apply lookup_insert_None; split;eauto; intros P; by inversion P.
  intros P; by inversion P.
  iPureIntro.
  split;[|split].
  - by apply (Hreg (r1, i) w1 (lookup_insert _ (r1, i) w1)).
  - apply (Hreg (r2, i) w2);eauto.
    rewrite lookup_insert_Some;right;split;
    [intros P; inversion P; contradiction|];
    by rewrite !lookup_insert.
  - apply (Hreg (r3, i) w3);eauto.
    rewrite lookup_insert_Some;right;split;
    [intros P; inversion P; contradiction|].
    rewrite lookup_insert_Some;right;split;
    [intros P; inversion P; contradiction|];
    by rewrite !lookup_insert.
Qed.

Lemma gen_reg_valid4 (σ : state) i r1 w1 r2 w2 r3 w3 r4 w4:
    (get_current_vm σ) = i ->
    r1 ≠ r2->
    r1 ≠ r3->
    r2 ≠ r3->
    r1 ≠ r4->
    r2 ≠ r4->
    r3 ≠ r4->
    ghost_map_auth (gen_reg_name vmG) 1 (get_reg_gmap σ) -∗
    r1 @@ i ->r w1 -∗
    r2 @@ i ->r w2 -∗
    r3 @@ i ->r w3 -∗
    r4 @@ i ->r w4 -∗
    ⌜ (get_reg σ r1) = Some w1 ⌝ ∗ ⌜ (get_reg σ r2) =Some w2 ⌝ ∗ ⌜ (get_reg σ r3) = Some w3⌝ ∗ ⌜(get_reg σ r4) = Some w4⌝.
Proof.
  iIntros (Hi Hneq1 Hneq2 Hneq3 Hneq4 Hneq5 Hneq6) "Hreg Hr1 Hr2 Hr3 Hr4".
  iDestruct ((gen_reg_valid_Sep σ i ({[(r1,i):=w1;(r2,i):=w2;(r3,i):=w3;(r4,i):=w4]}))
               with "Hreg [Hr1 Hr2 Hr3 Hr4]") as "%Hreg";eauto.
  rewrite !big_sepM_insert ?big_sepM_empty;eauto.
  iFrame.
  apply lookup_insert_None; split;eauto; intros P; by inversion P.
  apply lookup_insert_None; split;eauto.
  apply lookup_insert_None; split;eauto; intros P; by inversion P.
  intros P; by inversion P.
  apply lookup_insert_None; split;eauto.
  apply lookup_insert_None; split;eauto.
  apply lookup_insert_None; split;eauto; intros P; by inversion P.
  intros P; by inversion P.
  intros P; by inversion P.
  iPureIntro.
  split;[|split;[|split]].
  - by apply (Hreg (r1, i) w1 (lookup_insert _ (r1, i) w1)).
  - apply (Hreg (r2, i) w2);eauto.
    rewrite lookup_insert_Some;right;split;
    [intros P; inversion P; contradiction|];
    by rewrite !lookup_insert.
  - apply (Hreg (r3, i) w3);eauto.
    rewrite lookup_insert_Some;right;split;
    [intros P; inversion P; contradiction|].
    rewrite lookup_insert_Some;right;split;
    [intros P; inversion P; contradiction|];
    by rewrite !lookup_insert.
  - apply (Hreg (r4, i) w4);eauto.
    rewrite lookup_insert_Some;right;split;
    [intros P; inversion P; contradiction|].
    rewrite lookup_insert_Some;right;split;
    [intros P; inversion P; contradiction|].
    rewrite lookup_insert_Some;right;split;
    [intros P; inversion P; contradiction|];
    by rewrite !lookup_insert.
Qed.



Lemma gen_reg_update1_global:
  ∀ (σ : state) r i w w',
    ghost_map_auth (gen_reg_name vmG) 1 (get_reg_gmap σ) -∗
    r @@ i ->r w ==∗
               ghost_map_auth (gen_reg_name vmG) 1 (<[(r,i):=w']>(get_reg_gmap σ)) ∗
              r @@ i ->r  w'.
 Proof.
  iIntros (?????) "Hσ Hr".
  rewrite reg_mapsto_eq /reg_mapsto_def.
  iDestruct (ghost_map_update w' with "Hσ Hr") as ">[Hσ Hr]".
  iFrame.
  done.
 Qed.


 Lemma reg_proper {m: gmap (reg_name * VMID) Word}:
([∗ map] k ↦ x ∈ m, k↪[gen_reg_name vmG] x) ⊣⊢ ([∗ map]k ↦ x ∈ m,  (k.1, k.2)↪[gen_reg_name vmG] x).
   Proof.
      iApply (big_sepM_proper _ (λ k x, (k.1, k.2)↪[gen_reg_name vmG] x)%I).
      intros.
  simpl.
  f_equiv.
  destruct k;done.
Qed.


 Lemma gen_reg_update_Sep:
  ∀ (σ : state) regs regs',
      dom (gset (reg_name * VMID)) regs = dom (gset (reg_name * VMID )) regs' ->
    ghost_map_auth (gen_reg_name vmG) 1 (get_reg_gmap σ) -∗
    ([∗ map] r↦w ∈ regs,  r.1 @@ r.2 ->r w) ==∗
               ghost_map_auth (gen_reg_name vmG) 1 (regs' ∪ (get_reg_gmap σ)) ∗
             ([∗ map] r↦w ∈ regs',  r.1 @@ r.2 ->r w).
 Proof.
  iIntros (????) "Hσ Hr".
  rewrite reg_mapsto_eq /reg_mapsto_def.
  iDestruct (ghost_map_update_big regs regs' H with "[Hσ] [Hr]") as ">[Hσ Hr]".
  done.
  by iApply reg_proper.
  iModIntro.
  rewrite reg_proper.
  iFrame.
 Qed.

 Lemma gen_reg_update2_global:
  ∀ (σ : state) r1 i1 w1 w1' r2 i2 w2 w2',
    r1 ≠ r2 ∨ i1 ≠ i2 ->
    ghost_map_auth (gen_reg_name vmG) 1 (get_reg_gmap σ) -∗
     r1 @@ i1 ->r w1 -∗
                      r2 @@ i2 ->r w2==∗
               ghost_map_auth (gen_reg_name vmG) 1 (<[(r1,i1) := w1']> (<[(r2,i2) := w2']> (get_reg_gmap σ))) ∗
             r1 @@ i1 ->r w1'  ∗ r2 @@ i2 ->r w2'.
 Proof.
  iIntros (????????? Hneq) "Hreg Hr1 Hr2".
  iDestruct ((gen_reg_update_Sep _ {[(r1,i1):=w1; (r2,i2):=w2]} {[(r1,i1):=w1'; (r2,i2):=w2']}) with "Hreg [Hr1 Hr2]")
    as ">[Hreg Hr12]" ;eauto;[set_solver| | ].
        rewrite !big_sepM_insert ?big_sepM_empty;eauto.
        iFrame.
        destruct Hneq; apply lookup_insert_None; split;eauto; intros P; by inversion P.
        iModIntro.
        rewrite !big_sepM_insert ?big_sepM_empty;eauto.
        iDestruct "Hr12" as "(? & ? & _)".
        rewrite ?insert_union_singleton_l map_union_assoc.
        simplify_map_eq.
        by iFrame.
        destruct Hneq; apply lookup_insert_None; split;eauto; intros P; by inversion P.
Qed.


 (* rules for memory points-to *)
  Lemma mem_dupl_false a w1 w2:
   a ->a w1 -∗ a ->a w2 -∗ False.
  Proof using.
    rewrite mem_mapsto_eq /mem_mapsto_def.
    iIntros "Ha1 Ha2".
    iDestruct (ghost_map_elem_valid_2 with "Ha1 Ha2") as %?.
    destruct H.
    apply dfrac_valid_own_r in H.
    inversion H.
  Qed.

  Lemma mem_neq a1 a2  w1 w2:
   a1 ->a w1 -∗ a2 ->a w2 -∗ ⌜ a1 <> a2⌝.
  Proof using.
    iIntros "Ha1 Ha2".
    destruct (decide (a1 = a2)).
    - simplify_eq /=.
      iDestruct (mem_dupl_false with "Ha1 Ha2") as %[].
    - done.
  Qed.

Lemma gen_mem_valid:
  ∀ (σ : state) a w,
    ghost_map_auth (gen_mem_name vmG) 1 (get_mem σ) -∗
    a ->a w -∗
          ⌜ (get_mem σ) !! a = Some w ⌝.
Proof.
  iIntros (???) "Hσ Ha".
  rewrite mem_mapsto_eq /mem_mapsto_def.
  iDestruct (ghost_map_lookup with "Hσ Ha") as "%".
  done.
 Qed.

Lemma gen_mem_valid_Sep:
  ∀ (σ : state) mem,
    ghost_map_auth (gen_mem_name vmG) 1 (get_mem σ) -∗
    ([∗ map] a↦w ∈ mem,  a ->a w)-∗
         ([∗ map] a↦w ∈ mem, ⌜ (get_mem σ) !! a = Some w ⌝).
Proof.
  iIntros (??) "Hσ Hmem".
  rewrite mem_mapsto_eq /mem_mapsto_def.
  iDestruct ((ghost_map_lookup_big mem) with "Hσ Hmem") as "%Hincl".
  iApply big_sepM_pure.
  iIntros (???).
  iPureIntro.
  apply (lookup_weaken  mem (get_mem σ) _ _ a1 Hincl) .
Qed.

Lemma gen_mem_valid2:
  ∀ (σ : state) a1 w1 a2 w2,
    a1 ≠ a2 ->
    ghost_map_auth (gen_mem_name vmG) 1 (get_mem σ) -∗
    a1 ->a w1 -∗
    a2 ->a w2 -∗
          ⌜ (get_mem σ) !! a1 = Some w1 ⌝ ∗ ⌜ (get_mem σ) !! a2 = Some w2 ⌝.
Proof.
  iIntros (????? Hneq) "Hσ Ha1 Ha2".
  iDestruct (gen_mem_valid_Sep _ {[a1:=w1;a2:=w2]} with "Hσ [Ha1 Ha2]") as "%";eauto.
  rewrite !big_sepM_insert ?big_sepM_empty;eauto.
  iFrame.
  by simplify_map_eq.
  iPureIntro.
  split.
  - by apply (H a1 w1 (lookup_insert _ a1 w1)).
  - apply (H a2 w2);eauto.
    by simplify_map_eq.
 Qed.

(* Program Definition p0 := (@nat_to_fin 0 page_size _). *)
(* Program Definition p1 := (@nat_to_fin 1 page_size _). *)
(* Program Definition p2 := (@nat_to_fin 2 page_size _). *)
(* Program Definition p3 := (@nat_to_fin 3 page_size _). *)
(* Program Definition p4 := (@nat_to_fin 4 page_size _). *)
(* Program Definition p5 := (@nat_to_fin 5 page_size _). *)
(* Program Definition p6 := (@nat_to_fin 6 page_size _). *)
(* Program Definition p7 := (@nat_to_fin 7 page_size _). *)
(* Solve All Obligations with *)
(*     (intros;pose proof (page_size_at_least);assert(H': page_size_lower_bound=15);first done;lia). *)

(* Program Definition new_transaction_descriptor11 p v wf wh wt wc rcvr p' := *)
(*  ((page_offset_to_Addr p p0)->a encode_VMID v ∗ *)
(*  (page_offset_to_Addr p p1)->a wf ∗ *)
(*  (page_offset_to_Addr p p2)->a wh ∗ *)
(*  (page_offset_to_Addr p p3)->a wt ∗ *)
(*  (page_offset_to_Addr p p4)->a wc ∗ *)
(*  (page_offset_to_Addr p p5)->a one_Word ∗ *)
(*  (page_offset_to_Addr p p6)->a encode_VMID rcvr ∗ *)
(*  (page_offset_to_Addr p p7)->a encode_PID p')%I. *)

(* Lemma gen_mem_valid_td11: *)
(*   ∀ (σ : state) ptx i wf wh wt j pd, *)
(*     new_transaction_descriptor11 ptx i wf wh wt one_Word j pd -∗ *)
(*     ghost_map_auth (gen_mem_name vmG) 1 (get_mem σ) -∗ *)
(*     ⌜ (get_mem σ) !! (page_offset_to_Addr ptx p0) = Some (encode_VMID i) ⌝ *)
(*     ∗ ⌜ (get_mem σ) !! (page_offset_to_Addr ptx p1) = Some wf ⌝ *)
(*     ∗ ⌜ (get_mem σ) !! (page_offset_to_Addr ptx p2) = Some wh ⌝ *)
(*     ∗ ⌜ (get_mem σ) !! (page_offset_to_Addr ptx p3) = Some wt ⌝ *)
(*     ∗ ⌜ (get_mem σ) !! (page_offset_to_Addr ptx p4) = Some one_Word ⌝ *)
(*     ∗ ⌜ (get_mem σ) !! (page_offset_to_Addr ptx p5) = Some one_Word ⌝ *)
(*     ∗ ⌜ (get_mem σ) !! (page_offset_to_Addr ptx p6) = Some (encode_VMID j) ⌝ *)
(*     ∗ ⌜ (get_mem σ) !! (page_offset_to_Addr ptx p7) = Some (encode_PID pd) ⌝. *)
(* Proof. *)
(*   iIntros (????????) "Htd Hσ". *)
(*   rewrite /new_transaction_descriptor11 . *)
(*   iDestruct (gen_mem_valid_Sep _ {[(page_offset_to_Addr ptx p0):= encode_VMID i; *)
(*                                    (page_offset_to_Addr ptx p1):= wf; *)
(*                                    (page_offset_to_Addr ptx p2):= wh; *)
(*                                    (page_offset_to_Addr ptx p3):= wt; *)
(*                                    (page_offset_to_Addr ptx p4):= one_Word ; *)
(*                                    (page_offset_to_Addr ptx p5):= one_Word ; *)
(*                                    (page_offset_to_Addr ptx p6):= encode_VMID j; *)
(*                                    (page_offset_to_Addr ptx p7):= encode_PID pd]} with "Hσ [Htd]") as "%";eauto. *)
(*   rewrite !big_sepM_insert ?big_sepM_empty;eauto;first *)
(*   (iDestruct "Htd" as "(?&?&?&?&?&?&?&?)"; *)
(*   iFrame); *)
(*   repeat rewrite lookup_insert_ne;first done;repeat (apply  page_offset_to_Addr_neq;eauto);done. *)
(*   iPureIntro. *)
(*   remember {[(page_offset_to_Addr ptx p0):=encode_VMID i; *)
(*                                    (page_offset_to_Addr ptx p1):=wf; *)
(*                                    (page_offset_to_Addr ptx p2):= wh; *)
(*                                    (page_offset_to_Addr ptx p3):= wt; *)
(*                                    (page_offset_to_Addr ptx p4):= one_Word ; *)
(*                                    (page_offset_to_Addr ptx p5):= one_Word ; *)
(*                                    (page_offset_to_Addr ptx p6):= encode_VMID j; *)
(*                                    (page_offset_to_Addr ptx p7):= encode_PID pd]} as m. *)
(*   repeat (try split); *)
(*   apply (map_Forall_lookup_1 (λ (k : Addr) (x : Word), get_mem σ !! k = Some x) m );eauto; *)
(*   simplify_eq /=; repeat try (simplify_map_eq;try done;try (rewrite lookup_insert_ne; simplify_map_eq;try done)); *)
(*   apply page_offset_to_Addr_neq;eauto;done. *)
(* Qed. *)


Lemma gen_mem_update1:
  ∀ (σ : state) a w w',
    ghost_map_auth (gen_mem_name vmG) 1 (get_mem σ) -∗
    a ->a w ==∗
               ghost_map_auth (gen_mem_name vmG) 1 (<[a:=w']>(get_mem σ)) ∗
              a ->a w'.
 Proof.
  iIntros (????) "Hσ Ha".
  rewrite mem_mapsto_eq /mem_mapsto_def.
  iDestruct (ghost_map_update w' with "Hσ Ha") as ">[Hσ Ha]".
  iFrame.
  done.
 Qed.

 (* rules for TX *)
  Lemma tx_dupl i p :
   TX@ i := p -∗ TX@ i := p ∗ TX@ i := p.
  Proof using.
    rewrite tx_mapsto_eq.
    iIntros "Htx".
    iApply own_op.
    rewrite -auth_frag_op singleton_op.
    rewrite agree_idemp.
    done.
  Qed.

  Lemma gen_tx_valid σ i p:
   TX@ i := p -∗ own (gen_tx_name vmG) (get_tx_agree σ) -∗ ⌜ (get_vm_mail_box σ i).1 = p ⌝.
  Proof.
    iIntros "Htx Hσ".
    rewrite tx_mapsto_eq /tx_mapsto_def.
    destruct σ as [[[[[? σ'] ?] ?] ?] ?].
    rewrite /get_tx_agree /get_txrx_auth_agree /get_vm_mail_box /get_mail_boxes.
    iDestruct (own_valid_2 with "Hσ Htx") as %Hown.
    simpl in *.
    apply auth_both_valid_discrete in Hown.
    destruct Hown as [Hown1 Hown2].
    iPureIntro.
    pose proof (@lookup_included VMID _ _
                                 ((agreeR (leibnizO PID)))
                                 {[i := to_agree p]}
                                 (list_to_map (map (λ v : VMID, (v, to_agree (σ' !!! v).1)) list_of_vmids))) as H.
    rewrite ->H in Hown1.
    pose proof (Hown1 i) as H1.
    apply option_included in H1.
    destruct H1.
    simplify_map_eq.
    destruct H0.
    destruct H0.
    destruct H0.
    apply lookup_singleton_Some in H0.
    destruct H0.
    simplify_map_eq /=.
    destruct H1.
    apply (elem_of_list_to_map_2 _ i x0) in H0.
    apply elem_of_list_In in H0.
    apply (in_map_iff ) in H0.
    destruct H0.
    destruct H0.
    inversion H0.
    simplify_eq /=.
    destruct H1.
    - unfold to_agree in H1.
      destruct (H1 0) as [H1' H1''].
      simpl in H1', H1''.
      pose proof (H1' p).
      assert (p ∈ [p]). apply elem_of_list_here.
      pose proof (H3 H4).
      destruct H5 as [b [b1 b2]].
      inversion b1; subst.
      + unfold dist in b2.
        unfold ofe_dist in b2.
        unfold discrete_dist in b2.
        rewrite b2.
        reflexivity.
      + inversion H7.
    - apply to_agree_included in H1.
      rewrite H1.
      reflexivity.
  Qed.


  (* rules for RX *)
  Lemma rx_split_some i p n (v: VMID):
  RX@ i :=( p ! n , v)  -∗ RX@ i :=( p ! n, v)  ∗ RX@ i := p.
  Proof using.
    iIntros "HR".
    rewrite rx_mapsto_eq1 rx_mapsto_eq2.
    iApply own_op.
    rewrite -pair_op -auth_frag_op.
    rewrite singleton_op agree_idemp.
    rewrite Some_op_opM.
    simplify_eq /=.
    done.
  Qed.

  Lemma rx_split_none i p:
  RX@ i :=(p !) -∗ RX@ i :=(p !) ∗ RX@ i := p.
  Proof using.
    iIntros "HR".
    rewrite rx_mapsto_eq1 rx_mapsto_eq2.
    iApply own_op.
    rewrite -pair_op -auth_frag_op.
    rewrite singleton_op agree_idemp.
    rewrite  Some_op_opM.
    simplify_eq /=.
    done.
  Qed.

  Lemma rx_dupl i p:
   RX@i:=p -∗ RX@i:=p ∗ RX@i:=p.
  Proof using.
    iIntros "HR".
    rewrite rx_mapsto_eq2.
    iApply own_op.
    rewrite -pair_op -auth_frag_op.
    rewrite singleton_op agree_idemp.
    naive_solver.
  Qed.


  Lemma gen_rx_agree_valid σ i p:
   ✓ (get_rx_agree σ ⋅ ◯ {[i := to_agree p]}) -> (get_vm_mail_box σ i).2.1 = p.
  Proof.
    intro.
    rewrite /get_rx_agree /get_txrx_auth_agree in H.
    apply auth_both_valid_discrete in H;destruct H as [H _].
    remember  ((list_to_map (map (λ v : VMID, (v, to_agree (get_vm_mail_box σ v).2.1)) list_of_vmids)): gmap VMID (agreeR (leibnizO PID))) as m.
    rewrite -Heqm in H.
    rewrite -> (lookup_included {[i := to_agree p]} m) in H.
    pose proof (H i).
    clear H.
    simplify_map_eq /=.
    apply option_included_total in H0;destruct H0.
    rewrite -> (lookup_singleton_None i i (to_agree p)) in H;done.
    destruct H as [x [x0 [H H0]]].
    rewrite -> (lookup_singleton_Some i i (to_agree p)) in H.
    inversion H; subst x;clear H H1.
    destruct H0.
    apply elem_of_list_to_map_2 in H.
    apply elem_of_list_In in H.
    apply in_map_iff in H.
    inversion H;clear H.
    destruct H1 as [H1 _];inversion H1;subst;clear H1.
    rewrite -> (to_agree_included (p: (leibnizO PID)) _) in H0.
    by fold_leibniz.
  Qed.


  Lemma gen_rx_pid_valid σ i p:
   RX@ i := p -∗ own (gen_rx_name vmG) ((get_rx_agree σ), (get_rx_gmap σ) )-∗ ⌜ (get_vm_mail_box σ i).2.1 = p ⌝.
  Proof.
    iIntros "Hrx Hσ".
    rewrite rx_mapsto_eq2 /rx_mapsto_def2 .
    iDestruct (own_valid_2  with "Hσ Hrx") as %?.
    iPureIntro.
    rewrite -pair_op in H.
    apply pair_valid in H; destruct H as [H _].
    simpl in H.
    by apply gen_rx_agree_valid.
  Qed.

  Lemma gen_rx_gmap_none_valid σ i:
  ✓ (get_rx_gmap σ ⋅ Some (gmap_view_frag i (DfracOwn 1) None)) -> (get_vm_mail_box σ i).2.2 = None.
  Proof.
    intro.
    rewrite /get_rx_gmap -Some_op in H.
    rewrite -> Some_valid in H.
    apply gmap_view_both_frac_valid_L in H as [_ [_ H]].
    apply elem_of_list_to_map_2 in H.
    apply elem_of_list_In in H.
    apply in_map_iff in H.
    destruct H as [x [H _]].
    destruct ((get_vm_mail_box σ x).2.2) eqn:Heqn.
    destruct p;inversion H.
    inversion H;subst.
    by inversion H.
  Qed.

  Lemma gen_rx_none_valid σ i p:
   RX@ i :=( p !) -∗
   own (gen_rx_name vmG) ((get_rx_agree σ), (get_rx_gmap σ) )-∗
   ⌜ (get_vm_mail_box σ i).2 = (p,None)  ⌝.
  Proof.
    iIntros "Hrx Hσ".
    rewrite rx_mapsto_eq1 /rx_mapsto_def1.
    iDestruct (own_valid_2 with "Hσ Hrx") as %?.
    iPureIntro.
    rewrite -pair_op in H.
    apply pair_valid in H; destruct H as [Hagree Hgmap];simpl in Hagree;simpl in Hgmap.
    apply gen_rx_agree_valid in Hagree.
    apply gen_rx_gmap_none_valid in Hgmap.
    destruct ((get_vm_mail_box σ i).2) eqn:Heqn.
    rewrite -Hagree -Hgmap.
    done.
  Qed.


  Lemma gen_rx_gmap_some_valid σ i l v:
  ✓ (get_rx_gmap σ ⋅ Some (gmap_view_frag i (DfracOwn 1) (Some(l,v)))) -> (get_vm_mail_box σ i).2.2 = Some(l,v).
  Proof.
    intro.
    rewrite /get_rx_gmap -Some_op in H.
    rewrite -> Some_valid in H.
    apply gmap_view_both_frac_valid_L in H as [_ [_ H]].
    apply elem_of_list_to_map_2 in H.
    apply elem_of_list_In in H.
    apply in_map_iff in H.
    destruct H as [x [H _]].
    destruct ((get_vm_mail_box σ x).2.2) eqn:Heqn.
    by destruct p;inversion H;subst.
    by inversion H.
  Qed.


  Lemma gen_rx_valid_some σ i p l v:
   RX@ i :=( p ! l , v) -∗
   own (gen_rx_name vmG) ((get_rx_agree σ), (get_rx_gmap σ) )-∗
   ⌜ (get_vm_mail_box σ i).2 = (p,Some(l,v))⌝.
  Proof.
    iIntros "Hrx Hσ".
    rewrite rx_mapsto_eq1 /rx_mapsto_def1.
    iDestruct (own_valid_2 with "Hσ Hrx") as %?.
    iPureIntro.
    rewrite -pair_op in H.
    apply pair_valid in H; destruct H as [Hagree Hgmap];simpl in Hagree;simpl in Hgmap.
    apply gen_rx_agree_valid in Hagree.
    apply gen_rx_gmap_some_valid in Hgmap.
    destruct ((get_vm_mail_box σ i).2) eqn:Heqn.
    rewrite -Hagree -Hgmap.
    done.
  Qed.
(*
  (* rules for pagetables  *)
  Lemma owned_split_set i q1 q2 (s1 s2 : gset PID):
   s1 ## s2 -> O@i:={(q1+q2)%Qp}[(s1 ∪ s2)] -∗ O@i:={q1}[s1] ∗ O@i:={q2}[s2].
  Proof using.
  iIntros (Hdisj) "HO".
  rewrite owned_mapsto_eq.
  iApply own_op.
  rewrite -auth_frag_op singleton_op.
  rewrite -pair_op.
  rewrite (gset_disj_union _ _ Hdisj).
  naive_solver.
  Qed.

  Lemma owned_split_singleton i q1 q2 (s : gset PID) p:
   p ∉ s -> O@i:={(q1+q2)%Qp}[(s ∪ {[p]})] -∗ O@i:={q1}[s] ∗ O@i:={q2}p.
  Proof using.
    iIntros (Hnotin) "HO".
    assert (Hdisj: s ## {[p]}). { set_solver. }
    iDestruct (owned_split_set i q1 q2 _ _ Hdisj with "HO")  as "HO'".
    done.
  Qed.

 Lemma access_split_set i q1 q2 (s1 s2 : gset PID):
   s1 ## s2 -> A@i:={(q1+q2)%Qp}[(s1 ∪ s2)] -∗ A@i:={q1}[s1] ∗ A@i:={q2}[s2].
  Proof using.
  iIntros (Hdisj) "HO".
  rewrite access_mapsto_eq.
  iApply own_op.
  rewrite -auth_frag_op singleton_op.
  rewrite -pair_op.
  rewrite (gset_disj_union _ _ Hdisj).
  naive_solver.
  Qed.

  Lemma access_split_singleton i q1 q2 (s : gset PID) p:
   p ∉ s -> A@i:={(q1+q2)%Qp}[(s ∪ {[p]})] -∗ A@i:={q1}[s] ∗ A@i:={q2}p.
  Proof using.
    iIntros (Hnotin) "HO".
    assert (Hdisj: s ## {[p]}). { set_solver. }
    iDestruct (access_split_set i q1 q2 _ _ Hdisj with "HO")  as "HO'".
    done.
  Qed.
*)

Lemma gen_access_valid_Set:
  ∀ (σ : state) i q (s:gset PID),
    own (gen_access_name vmG) (get_access_gmap σ)  -∗
    (A@ i :={q}[s] ) -∗
          ([∗ set]  p ∈ s, ⌜(check_access_page σ i p)= true ⌝).
Proof.
    iIntros (????) "Hσ Hacc".
    rewrite access_mapsto_eq /access_mapsto_def.
    iDestruct (own_valid_2 with "Hσ Hacc") as %Hvalid.
    iPureIntro.
    unfold get_access_gmap in Hvalid.
    apply auth_both_valid_discrete in Hvalid.
    destruct Hvalid.
    remember (list_to_map (map
              (λ v : VMID,
                 (v,
                 (DfracOwn 1,
                 to_agree (GSet
                   (list_to_set
                      (map (λ p : PID * permission, p.1)
                         (map_to_list
                            (filter (λ p : PID * permission, is_accessible p.2 = true)
                               (get_vm_page_table σ v))))))))) list_of_vmids)) as m.
    pose proof (lookup_included {[i := (DfracOwn q, to_agree (GSet s))]} m).
    rewrite ->H1 in H.
    clear H1.
    pose proof (H i).
    clear H.
    apply option_included in H1.
    destruct H1.
    simplify_map_eq.
    destruct H.
    destruct H.
    destruct H.
    apply lookup_singleton_Some in H.
    destruct H.
    simplify_map_eq /=.
    destruct H1.
    apply (elem_of_list_to_map_2 _ i x0) in H.
    apply elem_of_list_In in H.
    apply (in_map_iff ) in H.
    destruct H.
    destruct H.
    inversion H.
    simplify_eq /=.
    clear H.
    unfold set_Forall.
    intros p Hin.
    destruct H1.
    - inversion H;clear H.
      simplify_eq /=.
      unfold check_access_page.
      apply to_agree_inj in H3.
      inversion H3; subst; clear H3.
      apply elem_of_list_to_set in Hin.
      apply elem_of_list_In in Hin.
      apply (in_map_iff _ _ p) in Hin.
      destruct Hin.
      destruct H.
      rewrite <- elem_of_list_In in H1.
      apply elem_of_map_to_list' in H1.
      apply map_filter_lookup_Some in H1.
      destruct H1.
      subst p.
      by rewrite H1 /=.
    - apply pair_included in H.
      destruct H;clear H.
      apply to_agree_included in H1.
      inversion H1; subst; clear H1.
      unfold check_access_page.
      assert ( p ∈ (list_to_set
           (map (λ p : PID * permission, p.1)
              (map_to_list (filter (λ p : PID * permission, is_accessible p.2 = true) (get_vm_page_table σ i)))): gset PID)) as Hin'.
      { set_solver.  }
      clear Hin;rename Hin' into Hin.
      apply elem_of_list_to_set in Hin.
      apply elem_of_list_In in Hin.
      apply (in_map_iff _ _ p) in Hin.
      destruct Hin.
      destruct H.
      rewrite <- elem_of_list_In in H1.
      apply elem_of_map_to_list' in H1.
      apply map_filter_lookup_Some in H1.
      destruct H1.
      subst p.
      rewrite H1.
      done.
Qed.

  Lemma gen_access_valid:
  ∀ (σ : state) i q p,
    own (gen_access_name vmG) (get_access_gmap σ)  -∗
    (A@ i :={q}p ) -∗
          ( ⌜(check_access_page σ i p)= true ⌝).
  Proof.
     iIntros (????) "Hσ Hacc".
     iDestruct (gen_access_valid_Set _ _ _ {[p]} with "Hσ Hacc") as %->;eauto.
     set_solver.
  Qed.

  Lemma gen_access_valid2:
  ∀ (σ : state) i q s p1 p2,
    {[p1;p2]} ⊆ s ->
    own (gen_access_name vmG) (get_access_gmap σ)  -∗
    (A@ i :={q}[s] ) -∗
          ( ⌜(check_access_page σ i p1)= true⌝ ∗ ⌜(check_access_page σ i p2)= true ⌝).
  Proof.
     iIntros (?????? Hsubset) "Hσ Hacc".
     iDestruct (gen_access_valid_Set _ _ _ s with "Hσ Hacc") as %Hcheck;eauto.
     iPureIntro.
     split.
     - pose proof (Hcheck p1).
       simpl in H.
       apply H.
       set_solver.
     - pose proof (Hcheck p2).
       simpl in H.
       apply H.
       set_solver.
  Qed.

Lemma gen_access_valid_addr:
  ∀ (σ : state) i q a,
    own (gen_access_name vmG) (get_access_gmap σ)  -∗
    (A@ i :={q} (to_pid_aligned a) ) -∗
          ( ⌜(check_access_addr σ i a)= true ⌝).
Proof.
  iIntros (????) "Haccess Hacc".
  iDestruct (gen_access_valid σ i q (to_pid_aligned a) with "Haccess Hacc") as %Hacc.
  iPureIntro.
  by unfold check_access_page.
Qed.


Lemma gen_access_valid_addr_elem:
  ∀ (σ : state) i q s a,
    to_pid_aligned a ∈ s ->
    own (gen_access_name vmG) (get_access_gmap σ)  -∗
        (A@ i :={q}[s] ) -∗
        ⌜(check_access_addr σ i a)= true ⌝.
Proof.
  iIntros (??????) "Haccess Hacc".
  iDestruct (gen_access_valid_Set σ i q s with "Haccess Hacc") as %Hacc.
  iPureIntro.
  pose proof (Hacc (to_pid_aligned a)) as H'.
  apply H'.
  set_solver.
Qed.        


Lemma gen_access_valid_addr2:
  ∀ (σ : state) i q s a1 a2,
      s= {[(to_pid_aligned a1); (to_pid_aligned a2)]} ->
    own (gen_access_name vmG) (get_access_gmap σ)  -∗
    (A@ i :={q}[s] ) -∗
          ( ⌜(check_access_addr σ i a1)= true ⌝ ∗ ⌜(check_access_addr σ i a2)= true ⌝).
Proof.
  iIntros (???????) "Haccess Hacc".
  iDestruct (gen_access_valid_Set σ i q s with "Haccess Hacc") as %Hacc.
  iPureIntro.
  split.
  pose proof (Hacc (to_pid_aligned a1)).
  apply H0.
  set_solver.
  pose proof (Hacc (to_pid_aligned a2)).
  apply H0.
  set_solver.
Qed.


Lemma gen_no_access_valid:
  ∀ (σ : state) i p s,
    p ∉ s ->
    own (gen_access_name vmG) (get_access_gmap σ)  -∗
        (A@ i :={1}[s]) -∗
        ( ⌜(check_access_page σ i p)= false ⌝).
Proof.
  iIntros (?????) "Hσ Hacc".
  rewrite access_mapsto_eq /access_mapsto_def /get_access_gmap.
  iDestruct (own_valid_2 with "Hσ Hacc") as %Hvalid.
  iPureIntro.
  remember (list_to_map
                (map
                   (λ v : VMID,
                          (v,
                           (DfracOwn 1,
                            to_agree (gset.GSet
                              (list_to_set
                                 (map (λ p0 : PID * permission, p0.1)
                                      (map_to_list
                                         (filter
                                            (λ p0 : PID * permission, is_accessible p0.2 = true)
                                            (get_vm_page_table σ v))))))))) list_of_vmids)) as m.
  apply auth_both_valid_discrete in Hvalid.
  destruct Hvalid.
  pose proof (lookup_included {[i := (DfracOwn 1, to_agree (GSet s))]} m).
  rewrite ->H2 in H0.
  clear H2.
  pose proof (H0 i) as H2.
  apply option_included in H2.
  destruct H2.
  - simplify_map_eq.
  - rewrite /check_access_page.
    destruct H2 as [a [b [H2 [H2' H2'']]]].
    apply lookup_singleton_Some in H2.
    destruct H2; simplify_map_eq.
    destruct H2''.
    + inversion H2; subst; clear H2.
      apply (elem_of_list_to_map_2 _ i b) in H2'.
      apply elem_of_list_In in H2'.
      apply (in_map_iff ) in H2'.
      destruct H2' as [x [H2' H2'']].
      inversion H2'; subst.
      rewrite /get_vm_page_table.
      clear H2'.
      simpl in H4.
      apply to_agree_inj in H4.
      inversion H4; subst; clear H4.
      apply not_elem_of_list_to_set in H.
      rewrite /get_page_tables.
      rewrite /get_vm_page_table /get_page_tables in H.
      clear H2'' H3 H0.
      destruct ((σ.1.1.1.2 !!! i) !! p) eqn:Heq.
      destruct (is_accessible p0) eqn:Heqn'; try done.
      exfalso.
      apply H.
      apply elem_of_list_In.
      apply in_map_iff.
      exists (p, p0).
      split; eauto.
      rewrite <-elem_of_list_In.
      rewrite elem_of_map_to_list.
      apply map_filter_lookup_Some.
      split; auto.
      reflexivity.
    + apply prod_included in H2.
      destruct H2 as [_ H2].
      simpl in H2.
      apply (elem_of_list_to_map_2 _ i b) in H2'.
      apply elem_of_list_In in H2'.
      apply (in_map_iff ) in H2'.
      destruct H2' as [x' [H2' H2'']].
      inversion H2'; subst.
      simpl in H2.
      apply to_agree_included in H2.
      inversion H2; subst; clear H2.
      rewrite /get_vm_page_table /get_page_tables in H.
      destruct ((σ.1.1.1.2 !!! i) !! p) eqn:Heq.
      destruct (is_accessible p0) eqn:Heqn'; try done.
      exfalso.
      apply not_elem_of_list_to_set in H.
      apply H.
      apply elem_of_list_In.
      apply in_map_iff.
      exists (p, p0).
      split; eauto.
      rewrite <-elem_of_list_In.
      rewrite elem_of_map_to_list.
      apply map_filter_lookup_Some.
      split; auto.
      rewrite /get_vm_page_table /get_page_tables.
      rewrite Heq.
      assumption.
      rewrite /get_vm_page_table /get_page_tables.
      rewrite Heq.
      reflexivity.
Qed.

  (* TODO : gen_access_valid_Sep*)

  (* rules for transactions *)
  Lemma trans_split wh q1 q2 i wf wt m f:
   wh ->t{(q1+q2)%Qp}(i,wf,wt,m,f) -∗  wh ->t{q1}(i,wf,wt,m,f) ∗ wh ->t{q2}(i,wf,wt,m,f).
  Proof using.
    iIntros "HT".
    rewrite trans_mapsto_eq.
    iApply own_op.
    rewrite -gmap_view_frag_op.
    rewrite dfrac_op_own.
    done.
  Qed.

  Lemma retri_split_set wh (s1 s2 : gset VMID):
   s1 ## s2 -> wh ->re[(s1 ∪ s2)] -∗ wh ->re[s1] ∗ wh ->re[s2].
  Proof using.
    iIntros (Hdisj) "Hre".
    rewrite retri_mapsto_eq.
    iApply own_op.
    rewrite -auth_frag_op singleton_op.
    rewrite (gset_disj_union _ _ Hdisj).
    naive_solver.
  Qed.

  Lemma  retri_split_singleton wh (s: gset VMID) i:
   i ∉ s -> wh ->re[(s ∪ {[i]})] -∗ wh ->re[s] ∗ wh ->re i.
  Proof using.
    iIntros (Hnotin) "Hr".
    assert (Hdisj: s ## {[i]}).
    { set_solver. }
    iDestruct (retri_split_set wh _ _ Hdisj with "Hr")  as "Hr'".
    done.
  Qed.


End hyp_lang_rules.
