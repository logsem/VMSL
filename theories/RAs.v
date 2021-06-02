From iris.base_logic.lib Require Import gen_heap ghost_map invariants na_invariants.
From iris.algebra Require Import auth agree dfrac csum excl gmap gmap_view gset.
From iris.proofmode Require Import tactics.
From stdpp Require Import listset_nodup.
From HypVeri Require Export lang machine.
(* From machine_program_logic.program_logic Require Import weakestpre. *)


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
                      (* gen_owned_preG_inG :> inG Σ (authR (gmapUR V *)
                      (*               (prodR dfracR (gset_disjUR (leibnizO P))))); *)
                      (* gen_access_preG_inG :> inG Σ (authR (gmapUR V *)
                      (*               (prodR dfracR (gmapUR P (csumR (agreeR unitO) (exclR unitO)))))); *)
                      gen_trans_preG_inG :> gen_heapPreG W (V * W* W*(gmap V (listset_nodup P))*F) Σ;
                      gen_retri_preG_inG :> inG Σ (authR (gmapUR W (gset_disjR (leibnizO V))))
                   }.


  Class gen_VMG Σ := GenVMG{
                      gen_VM_inG :> gen_VMPreG addr vmid word reg_name pid transaction_type Σ;
                      gen_invG :> invG Σ;
                      gen_na_invG :> na_invG Σ;
                      gen_nainv_name : na_inv_pool_name;
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

Global Arguments gen_nainv_name {Σ} _.
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
  (* (authR (gmapUR vmid (prodR dfracR (gmapUR pid  (csumR (agreeR unitO) (exclR unitO)))))). *)
  (authR (gmapUR pid (prodR dfracR (csumR (agreeR unitO) (exclR unitO))))).



Definition gen_VMΣ : gFunctors :=
  #[
      invΣ;
      na_invΣ;
      GFunctor (agreeR natO);
      gen_heapΣ addr word;
      gen_heapΣ (reg_name * vmid) word;
      GFunctor ra_TXBuffer;
      GFunctor ra_RXBuffer;
      (* GFunctor (authR (gmapUR vmid (prodR dfracR (gset_disjUR (leibnizO pid))))); *)
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

  Definition get_reg_gmap σ: gmap (reg_name * vmid) word :=
    (foldr (λ p acc, (map_fold (λ (r:reg_name) (w:word) acc', <[(r,p.1):= w ]>acc') acc p.2)) ∅
              (vzip_with (λ v δ, (v,δ.1.1)) (vector_of_vmids) (get_vm_states σ))).


  Definition get_txrx_auth_agree σ (f: mail_box -> pid) :
    ra_TXBuffer:=
    (● (foldr (λ p acc, <[p.1:=p.2]>acc) ∅
              (vzip_with (λ v δ, (v,to_agree (f δ.1.2))) (vector_of_vmids) (get_vm_states σ)))).


  Definition get_rx_state δ :(optionO (prodO natO (leibnizO HypVeri.lang.vmid))):=
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

  (* XXX : Now our wp is parameterized by vmid, so we don't need it for owned and accessible anymore? *)
  (* Definition get_owned_gmap σ : (authR (gmapUR vmid (prodR dfracR (gset_disjUR pid)))) := *)
  (*   (● (foldr (λ p acc, <[p.1:=((DfracOwn 1),p.2)]>acc) ∅ *)
  (*             (vzip_with (λ v δ, (v, *)
  (*                   (map_fold (λ (p:pid) (perm:permission) (s: gset_disjUR pid), *)
  (*                 match perm.1 with *)
  (*                 | Owned =>  match s with *)
  (*                               | GSet s' => GSet (s' ∪ {[p]}) *)
  (*                               | GSetBot => GSet ∅ *)
  (*                             end *)
  (*                 | Unowned => s *)
  (*                end)  (GSet ∅) δ.2))) (vector_of_vmids) (get_vm_states σ)))). *)

  (* Definition get_access_gmap σ : ra_Accessible := *)
    (* (●  (foldr (λ p acc, <[p.1:=((DfracOwn 1),p.2)]>acc) ∅ *)
    (*      (vzip_with (λ v δ, (v, *)
    (*                 (map_fold (λ (p:pid) (perm:permission) (s: (gmap pid (csumR (agreeR unitO) (exclR unitO)))), *)
    (*               match perm.2 with *)
    (*               | NoAccess => s *)
    (*               | SharedAccess => <[p:= (Cinl (to_agree ()))]>s *)
    (*               | ExclusiveAccess => <[p:= (Cinr (Excl ()))]>s *)
    (*              end)  ∅ δ.2 ))) (vector_of_vmids) (get_vm_states σ) ))). *)

  Definition get_owned_gset δ : (authR (gset_disjUR pid)) :=
    (● (map_fold (λ (p:pid) (perm:permission) (s: gset_disjUR pid),
                  match perm.1 with
                  | Owned =>  match s with
                                | GSet s' => GSet (s' ∪ {[p]})
                                | GSetBot => GSet ∅
                              end
                  | Unowned => s
                 end)  (GSet ∅) δ.2)).


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
  
  Definition get_receivers_gmap σ : authR (gmapUR word (gset_disjR (leibnizO vmid))) :=
    let transactions := get_transactions σ
    in ● (map_fold (λ (h : word) (trn : transaction) m, <[h:=GSet (trn.1.1.2)]>m) ∅ transactions).
  
  Definition gen_vm_interp σ: iProp Σ :=
    let i := (get_current_vm σ) in
    let δ := (get_vm_state σ i) in
      own (gen_num_name vmG) (to_agree vm_count)∗
      ghost_map_auth (gen_mem_name vmG) 1 (get_mem σ) ∗
      ghost_map_auth (gen_reg_name vmG) 1 (get_reg_gmap σ) ∗
      own (gen_tx_name vmG) (get_txrx_auth_agree σ (λ p, p.1)) ∗
      own (gen_rx_name vmG)
        ((get_txrx_auth_agree σ (λ p, p.2.1.1)),
          (Some (gmap_view_auth 1
            (vec_to_gmap (vmap (get_rx_state) (get_vm_states σ)))))) ∗
      own (gen_owned_name vmG) (get_owned_gset δ) ∗
      own (gen_access_name vmG) (get_access_gmap δ) ∗
      ghost_map_auth (gen_trans_name vmG) 1 (get_trans_gmap σ) ∗
      own (gen_retri_name vmG) (get_receivers_gmap σ)
    .


(* The Iris instance.*)
  Definition num_agree_def (n:nat) : iProp Σ :=
    own (gen_num_name vmG) (to_agree n).
  Definition num_agree_aux : seal (@num_agree_def). Proof. by eexists. Qed.
  Definition num_agree:= num_agree_aux.(unseal).
  Definition num_agree_eq : @num_agree = @num_agree_def := num_agree_aux.(seal_eq).

  Definition mem_mapsto_def (a:addr) (dq : dfrac) (w:word) : iProp Σ :=
    own (gen_mem_name vmG) (gmap_view_frag a dq (w : leibnizO word)).
  Definition mem_mapsto_aux : seal (@mem_mapsto_def). Proof. by eexists. Qed.
  Definition mem_mapsto := mem_mapsto_aux.(unseal).
  Definition mem_mapsto_eq : @mem_mapsto = @mem_mapsto_def := mem_mapsto_aux.(seal_eq).

  Definition reg_mapsto_def (r:reg_name) (i:vmid) (dq : dfrac) (w:word) : iProp Σ :=
    own (gen_reg_name vmG) (gmap_view_frag (r,i) dq (w : leibnizO word)).
  Definition reg_mapsto_aux : seal (@reg_mapsto_def). Proof. by eexists. Qed.
  Definition reg_mapsto := reg_mapsto_aux.(unseal).
  Definition reg_mapsto_eq : @reg_mapsto = @reg_mapsto_def := reg_mapsto_aux.(seal_eq).

  Definition tx_mapsto_def (i:vmid) (p:pid) : iProp Σ :=
    own (gen_tx_name vmG) (◯ {[i := (to_agree (p: leibnizO pid))]}).
  Definition tx_mapsto_aux : seal (@tx_mapsto_def). Proof. by eexists. Qed.
  Definition tx_mapsto := tx_mapsto_aux.(unseal).
  Definition tx_mapsto_eq : @tx_mapsto = @tx_mapsto_def := tx_mapsto_aux.(seal_eq).

  Definition rx_mapsto_def1 (i:vmid) (p:pid) (nr : option (nat *  vmid)) : iProp Σ :=
    match nr with
      | Some (n, r) =>
        own (gen_rx_name vmG) ((◯ {[i := (to_agree p)]}),
                               (Some (gmap_view_frag i (DfracOwn 1) (Some ((n:natO), (r: leibnizO vmid))))))
      | None =>
        own (gen_rx_name vmG) ((◯ {[i := (to_agree p)]}),
                               (Some (gmap_view_frag i (DfracOwn 1) None)))
    end.
  Definition rx_mapsto_aux1 : seal (@rx_mapsto_def1). Proof. by eexists. Qed.
  Definition rx_mapsto1 := rx_mapsto_aux1.(unseal).
  Definition rx_mapsto_eq1 : @rx_mapsto1 = @rx_mapsto_def1 := rx_mapsto_aux1.(seal_eq).

  Definition rx_mapsto_def2 (i:vmid) (p:pid) : iProp Σ :=
    own (gen_rx_name vmG) ((◯ {[i := (to_agree p)]}),None).
  Definition rx_mapsto_aux2 : seal (@rx_mapsto_def2). Proof. by eexists. Qed.
  Definition rx_mapsto2 := rx_mapsto_aux2.(unseal).
  Definition rx_mapsto_eq2 : @rx_mapsto2 = @rx_mapsto_def2 := rx_mapsto_aux2.(seal_eq).

  (* Definition owned_mapsto_def (i:vmid) dq (s: gset_disj pid) : iProp Σ := *)
  (*   own (gen_owned_name vmG) (◯ {[i := (dq, s)]}). *)
  Definition owned_mapsto_def (s: gset_disj pid) : iProp Σ :=
    own (gen_owned_name vmG) (◯ s).
  Definition owned_mapsto_aux : seal (@owned_mapsto_def). Proof. by eexists. Qed.
  Definition owned_mapsto := owned_mapsto_aux.(unseal).
  Definition owned_mapsto_eq : @owned_mapsto = @owned_mapsto_def := owned_mapsto_aux.(seal_eq).

  (* Definition access_mapsto_def (i:vmid) dq (m: gmap pid access) : iProp Σ := *)
  (*   own (gen_access_name vmG) (◯ {[i := (dq, (map_fold (λ p a acc, *)
  (*                                                      match a with *)
  (*                                                        | NoAccess => acc *)
  (*                                                        | SharedAccess => <[p:=(Cinl (to_agree ()))]>acc *)
  (*                                                        | ExclusiveAccess => <[p:=(Cinr (Excl ()))]>acc *)
  (*                                                      end) ∅ m))]}). *)
  Definition access_mapsto_def dq (m: gmap pid access) : iProp Σ :=
    own (gen_access_name vmG) (◯ (map_fold (λ p a acc,
                                                       match a with
                                                         | NoAccess => acc
                                                         | SharedAccess => <[p:=(dq, (Cinl (to_agree ())))]>acc
                                                         | ExclusiveAccess => <[p:=(dq, (Cinr (Excl ())))]>acc
                                                       end) ∅ m)).
  Definition access_mapsto_aux : seal (@access_mapsto_def). Proof. by eexists. Qed.
  Definition access_mapsto := access_mapsto_aux.(unseal).
  Definition access_mapsto_eq : @access_mapsto = @access_mapsto_def := access_mapsto_aux.(seal_eq).

  Definition trans_mapsto_def(wh : word) dq (v: vmid) (wf: word) (wt: word) (pgs : gmap vmid (listset_nodup pid)) (fid : transaction_type) : iProp Σ :=
    own (gen_trans_name vmG) (gmap_view_frag wh dq
                          (((((v, wf) , wt), pgs), fid): (leibnizO (vmid * word * word * (gmap vmid (listset_nodup pid)) * transaction_type)))).
  Definition trans_mapsto_aux : seal (@trans_mapsto_def). Proof. by eexists. Qed.
  Definition trans_mapsto := trans_mapsto_aux.(unseal).
  Definition trans_mapsto_eq : @trans_mapsto = @trans_mapsto_def := trans_mapsto_aux.(seal_eq).

  Definition retri_mapsto_def (w:word) (s: gset_disj vmid) : iProp Σ :=
    own (gen_retri_name vmG) (◯ {[w := s]}).
  Definition retri_mapsto_aux : seal (@retri_mapsto_def). Proof. by eexists. Qed.
  Definition retri_mapsto := retri_mapsto_aux.(unseal).
  Definition retri_mapsto_eq : @retri_mapsto = @retri_mapsto_def := retri_mapsto_aux.(seal_eq).

End definitions.

(* predicate for the number of vms *)
Notation "## n" := (num_agree n)
                        (at level 50, format "## n"): bi_scope.

(* point-to predicates for registers and memory *)
Notation "r @@ i ->r{ q } w" := (reg_mapsto r i (DfracOwn q) w)
  (at level 22, q at level 50, format "r @@ i ->r{ q } w") : bi_scope.
Notation "r @@ i ->r w" := (reg_mapsto r i (DfracOwn 1) w) (at level 21, w at level 50) : bi_scope.

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
Notation "O:=[ s ] " := (owned_mapsto (GSet s))
                                           (at level 20, format "O:=[ s ] "):bi_scope.
Notation "O:= p" := (owned_mapsto (GSet {[p]}))
                                           (at level 20, format "O:= p"):bi_scope.

Notation "A:=[ m ]" := (access_mapsto m)
                                      (at level 20, format "A:=[ m ]"):bi_scope.
Notation "A:={ q }( p , a ) " := (access_mapsto (DfracOwn q) {[p:=a]})
                                          (at level 20, format "A:={ q }( p , a )"):bi_scope.
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
  Implicit Types a b c : addr.
  Implicit Types r : reg_name.
  Implicit Types w: word.


  (* rules for register points-to *)

  Lemma reg_dupl_false r i w1 w2 :
   r @@ i ->r w1 -∗ r @@ i ->r w2 -∗ False.
  Proof using.
    rewrite reg_mapsto_eq.
    iIntros "Hr1 Hr2".
    iDestruct (own_valid_2 with "Hr1 Hr2") as %?%gmap_view_frag_op_valid_L.
    destruct H0.
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

 (* rules for memory points-to *)
  Lemma mem_dupl_false a w1 w2:
   a ->a w1 -∗ a ->a w2 -∗ False.
  Proof using.
    rewrite mem_mapsto_eq.
    iIntros "Ha1 Ha2".
    iDestruct (own_valid_2 with "Ha1 Ha2") as %?%gmap_view_frag_op_valid_L.
    destruct H0.
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

  (* rules for RX *)
  Lemma rx_split_some i p n (v: vmid):
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

  (* rules for pagetables  *)
  Lemma owned_split_set (s1 s2 : gset pid):
   s1 ## s2 -> O:=[(s1 ∪ s2)] -∗ O:=[s1] ∗ O:=[s2].
  Proof using.
  iIntros (Hdisj) "HO".
  rewrite owned_mapsto_eq.
  iApply own_op.
  rewrite -auth_frag_op.
  rewrite (gset_disj_union _ _ Hdisj).
  naive_solver.
  Qed.

  Lemma owned_split_singleton (s : gset pid) p:
   p ∉ s -> O:=[(s ∪ {[p]})] -∗ O:=[s] ∗ O:=p.
  Proof using.
    iIntros (Hnotin) "HO".
    assert (Hdisj: s ## {[p]}).
    { set_solver. }
    iDestruct (owned_split_set _ _ Hdisj with "HO")  as "HO'".
    done.
  Qed.


  (* TODO: skip rules for accessible for now. not sure if the construction is good enough. *)

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

  Lemma retri_split_set wh (s1 s2 : gset vmid):
   s1 ## s2 -> wh ->re[(s1 ∪ s2)] -∗ wh ->re[s1] ∗ wh ->re[s2].
  Proof using.
    iIntros (Hdisj) "Hre".
    rewrite retri_mapsto_eq.
    iApply own_op.
    rewrite -auth_frag_op singleton_op.
    rewrite (gset_disj_union _ _ Hdisj).
    naive_solver.
  Qed.

  Lemma  retri_split_singleton wh (s: gset vmid) i:
   i ∉ s -> wh ->re[(s ∪ {[i]})] -∗ wh ->re[s] ∗ wh ->re i.
  Proof using.
    iIntros (Hnotin) "Hr".
    assert (Hdisj: s ## {[i]}).
    { set_solver. }
    iDestruct (retri_split_set wh _ _ Hdisj with "Hr")  as "Hr'".
    done.
  Qed.




End hyp_lang_rules.
