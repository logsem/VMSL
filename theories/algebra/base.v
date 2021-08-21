From iris.base_logic.lib Require Export invariants na_invariants gen_heap ghost_map.
From iris.algebra Require Export auth agree dfrac excl gmap gset frac_agree frac_auth.
From iris.proofmode Require Export tactics.
From HypVeri Require Import monad machine.
From HypVeri Require Export lang.
(* From stdpp Require Import fin_maps. *)

  Class gen_VMPreG (A V W R P F: Type) (Σ:gFunctors)
        `{Countable A, Countable V, Countable W, Countable R, Countable P} := {
    gen_token_preG_inG :> inG Σ (frac_authR (agreeR (leibnizO V)));
    gen_mem_preG_inG :> gen_heapGpreS A W Σ;
    gen_reg_preG_inG :> gen_heapGpreS (R * V) W Σ;
    gen_tx_preG_inG :> inG Σ (authR (gmapUR V (agreeR (leibnizO P))));
    gen_rx_agree_preG_inG :> inG Σ (authR (gmapUR V (agreeR (leibnizO P))));
    gen_rx_option_preG_inG :> gen_heapGpreS V (option (W * V)) Σ;
    gen_owned_preG_inG :> gen_heapGpreS V (gset P) Σ;
    gen_access_preG_inG :> gen_heapGpreS V (gset P) Σ;
    gen_excl_preG_inG :> gen_heapGpreS V (gset P) Σ;
    gen_trans_preG_inG :> gen_heapGpreS W (V * W*  V * (list P)*F) Σ;
    gen_hpool_preG_inG :> inG Σ (frac_authR (gset_disjR (leibnizO W)));
    gen_retri_preG_inG :> gen_heapGpreS W bool Σ
    }.


  Class gen_VMG Σ := GenVMG{
                         gen_VM_inG :> gen_VMPreG Addr VMID Word reg_name PID transaction_type Σ;
                         gen_invG :> invGS Σ;
                         gen_na_invG :> na_invG Σ;
                         gen_nainv_name : na_inv_pool_name;
                         gen_token_name : gname;
                         gen_mem_name : gname;
                         gen_reg_name : gname;
                         gen_tx_name : gname;
                         gen_rx_agree_name : gname;
                         gen_rx_option_name : gname;
                         gen_owned_name : gname;
                         gen_access_name : gname;
                         gen_excl_name : gname;
                         gen_trans_name : gname;
                         gen_hpool_name : gname;
                         gen_retri_name : gname
                       }.
Global Arguments gen_nainv_name {Σ} _.
Global Arguments gen_token_name {Σ} _.
Global Arguments gen_mem_name {Σ} _.
Global Arguments gen_reg_name {Σ} _.
Global Arguments gen_rx_agree_name {Σ} _.
Global Arguments gen_rx_option_name {Σ} _.
Global Arguments gen_tx_name {Σ} _.
Global Arguments gen_owned_name {Σ} _.
Global Arguments gen_access_name {Σ} _.
Global Arguments gen_excl_name {Σ} _.
Global Arguments gen_trans_name {Σ} _.
Global Arguments gen_hpool_name {Σ} _.
Global Arguments gen_retri_name {Σ} _.

Definition ra_rx_tx_agree := (authR (gmapUR VMID (agreeR (leibnizO PID)))).

Definition ra_rx := (gmap VMID (option (Word*VMID))).

Definition ra_page_table:= gmap VMID (gset_disj PID).

Definition gen_VMΣ : gFunctors :=
  #[
    invΣ;
    na_invΣ;
    GFunctor (frac_authR (agreeR (leibnizO VMID)));
    gen_heapΣ Addr Word;
    gen_heapΣ (reg_name * VMID) Word;
    GFunctor ra_rx_tx_agree;
    GFunctor ra_rx_tx_agree;
    gen_heapΣ VMID (option (Word*VMID));
    gen_heapΣ VMID (gset PID);
    gen_heapΣ VMID (gset PID);
    gen_heapΣ VMID (gset PID);
    gen_heapΣ Word (VMID * Word *  VMID * (list PID) * transaction_type);
    GFunctor (frac_authR (gset_disjR (leibnizO Word)));
    gen_heapΣ Word bool
   ].

Global Instance subG_gen_VMPreG {Σ}:
  subG gen_VMΣ Σ -> gen_VMPreG Addr VMID Word reg_name PID transaction_type Σ.
Proof.
  solve_inG.
Qed.


  (* list of all valid vmids *)
  Definition list_of_vmids  := vec_to_list (fun_to_vec (λ v: fin vm_count, v)).

  Lemma length_list_of_vmids : length list_of_vmids = vm_count.
  Proof.
      rewrite /list_of_vmids.
      apply vec_to_list_length.
  Qed.

  Lemma in_list_of_vmids v: In v list_of_vmids.
  Proof.
    apply elem_of_list_In.
    apply elem_of_vlookup.
    exists v.
    apply lookup_fun_to_vec.
  Qed.

  Lemma NoDup_list_of_vmids : NoDup list_of_vmids.
  Proof.
    apply NoDup_alt.
    rewrite /list_of_vmids.
    intros.
    rewrite <-vlookup_lookup' in H.
    rewrite <-vlookup_lookup' in H0.
    destruct H, H0.
    rewrite lookup_fun_to_vec in H.
    rewrite lookup_fun_to_vec in H0.
    rewrite -H in H0.
    rewrite <-(fin_to_nat_to_fin i vm_count x0).
    rewrite <-(fin_to_nat_to_fin j vm_count x1).
    rewrite H0.
    done.
  Qed.



Section definitions.
  Context `{vmG : !gen_VMG Σ}.
  Implicit Type σ: state.

  Definition get_token  (v:VMID) :=
     (frac_auth_auth (to_agree (v: leibnizO VMID))).

  Definition get_reg_gmap σ: gmap (reg_name * VMID) Word :=
     (list_to_map (flat_map (λ v, (map (λ p, ((p.1,v),p.2)) (map_to_list (get_vm_reg_file σ v)))) (list_of_vmids))).

  Definition get_txrx_auth_agree σ (f: mail_box -> PID) :(gmap VMID (agreeR (leibnizO PID))) :=
    (list_to_map (map (λ v, (v,to_agree (f (get_vm_mail_box σ v)))) (list_of_vmids))).

  Definition get_tx_agree σ := get_txrx_auth_agree σ (λ p, p.1).

  Definition get_rx_agree σ := get_txrx_auth_agree σ (λ p, p.2.1).

  Definition get_rx_gmap σ : gmap VMID _ :=
            ((list_to_map (map (λ v, let mb := (get_vm_mail_box σ v) in
                                    match mb.2.2 with
                                      | Some (l, j) => (v, (Some ( l, j)))
                                      | None => (v,None)
                                    end) (list_of_vmids)))).

  Definition get_pagetable_gset {Perm: Type}  σ v  (proj: page_table -> gmap PID Perm)
             (checkb: Perm -> bool):=
    ((list_to_set (map (λ (p:(PID*Perm)), p.1)
           (map_to_list (filter (λ p, (checkb p.2) = true)
                                (proj (get_vm_page_table σ v))))) : gset PID)).

  Definition get_pagetable_gmap{Perm: Type} σ (proj: page_table -> gmap PID Perm)
             (checkb: Perm -> bool) : (gmap VMID (gset PID)) :=
    (list_to_map (map (λ v, (v, (get_pagetable_gset σ v proj checkb))) (list_of_vmids))).

  Definition get_owned_gmap σ := (get_pagetable_gmap σ (λ pt, pt.1) is_owned).

  Definition get_access_gmap σ := (get_pagetable_gmap σ (λ pt, pt.2) is_accessible).

  Definition get_excl_gmap σ := (get_pagetable_gmap σ (λ pt, pt.2) is_exclusive).

  (* TODO we need getters for transations.. *)

  Definition get_transactions_gmap{Info: Type} σ (proj : transaction -> Info):
   gmap handle Info :=
    list_to_map (map (λ (p:Word * transaction) ,
                         (p.1, (proj p.2)))  (map_to_list (get_transactions σ).1)).

  Definition get_trans_gmap σ :=
    get_transactions_gmap σ (λ tran, (tran.1.1.1.1.1, tran.1.1.1.1.2, tran.1.1.2, tran.1.2, tran.2)).

  Definition get_hpool_gset σ := (get_transactions σ).2.

  Definition get_retri_gmap σ := get_transactions_gmap σ (λ tran, tran.1.1.1.2).

  Definition gen_vm_interp σ: iProp Σ :=
      own (gen_token_name vmG) (get_token (get_current_vm σ)) ∗
      ghost_map_auth (gen_mem_name vmG) 1 (get_mem σ) ∗
      ghost_map_auth (gen_reg_name vmG) 1 (get_reg_gmap σ) ∗
      own (gen_tx_name vmG) (● (get_tx_agree σ)) ∗
      own (gen_rx_agree_name vmG) (● (get_rx_agree σ)) ∗
      ghost_map_auth (gen_rx_option_name vmG) 1 (get_rx_gmap σ) ∗
      ghost_map_auth (gen_owned_name vmG) 1 (get_owned_gmap σ) ∗
      ghost_map_auth (gen_access_name vmG) 1 (get_access_gmap σ) ∗
      ghost_map_auth (gen_excl_name vmG) 1 (get_excl_gmap σ) ∗
      ghost_map_auth (gen_trans_name vmG) 1 (get_trans_gmap σ) ∗
      own (gen_hpool_name vmG) (frac_auth_auth (GSet (get_hpool_gset σ))) ∗
      ⌜ (dom (gset handle) (get_transactions σ).1) ## ((get_transactions σ).2) ⌝ ∗
      ⌜ map_Forall (λ _ v, (Z.of_nat (length v.1.2) <? word_size)%Z = true) (get_transactions σ).1 ⌝ ∗
      ghost_map_auth (gen_retri_name vmG) 1 (get_retri_gmap σ).

  Definition token_agree_def (v:VMID) (q:frac) : iProp Σ :=
    own (gen_token_name vmG) (frac_auth_frag q (to_agree (v: leibnizO VMID))) .
  Definition token_agree_aux : seal (@token_agree_def). Proof. by eexists. Qed.
  Definition token_agree:= token_agree_aux.(unseal).
  Definition token_agree_eq : @token_agree = @token_agree_def := token_agree_aux.(seal_eq).


  Definition mem_mapsto_def (a:Addr) (dq : dfrac) (w:Word) : iProp Σ :=
    (ghost_map_elem (gen_mem_name vmG) a dq w).
  Definition mem_mapsto_aux : seal (@mem_mapsto_def). Proof. by eexists. Qed.
  Definition mem_mapsto := mem_mapsto_aux.(unseal).
  Definition mem_mapsto_eq : @mem_mapsto = @mem_mapsto_def := mem_mapsto_aux.(seal_eq).

  Definition reg_mapsto_def (r:reg_name) (i:VMID) (dq : dfrac) (w:Word) : iProp Σ :=
    (ghost_map_elem (gen_reg_name vmG) (r,i) dq w).
  Definition reg_mapsto_aux : seal (@reg_mapsto_def). Proof. by eexists. Qed.
  Definition reg_mapsto := reg_mapsto_aux.(unseal).
  Definition reg_mapsto_eq : @reg_mapsto = @reg_mapsto_def := reg_mapsto_aux.(seal_eq).

  Definition tx_mapsto_def (i:VMID) (p:PID) : iProp Σ :=
    own (gen_tx_name vmG) (◯ {[i := (to_agree (p: leibnizO PID))]}).
  Definition tx_mapsto_aux : seal (@tx_mapsto_def). Proof. by eexists. Qed.
  Definition tx_mapsto := tx_mapsto_aux.(unseal).
  Definition tx_mapsto_eq : @tx_mapsto = @tx_mapsto_def := tx_mapsto_aux.(seal_eq).

  Definition rx_option_mapsto_def (i:VMID) (nr : option (Word *  VMID)) : iProp Σ :=
    ghost_map_elem (gen_rx_option_name vmG) i (DfracOwn 1) nr.
  Definition rx_option_mapsto_aux : seal (@rx_option_mapsto_def). Proof. by eexists. Qed.
  Definition rx_option_mapsto := rx_option_mapsto_aux.(unseal).
  Definition rx_option_mapsto_eq : @rx_option_mapsto = @rx_option_mapsto_def :=
    rx_option_mapsto_aux.(seal_eq).

  Definition rx_agree_mapsto_def (i:VMID) (p:PID) : iProp Σ :=
    own (gen_rx_agree_name vmG) (◯ {[i := (to_agree p)]}).
  Definition rx_agree_mapsto_aux : seal (@rx_agree_mapsto_def). Proof. by eexists. Qed.
  Definition rx_agree_mapsto := rx_agree_mapsto_aux.(unseal).
  Definition rx_agree_mapsto_eq : @rx_agree_mapsto = @rx_agree_mapsto_def :=
    rx_agree_mapsto_aux.(seal_eq).

  Definition owned_mapsto_def (i:VMID) dq (s: gset PID) : iProp Σ :=
    ghost_map_elem (gen_owned_name vmG) i dq s.
  Definition owned_mapsto_aux : seal (@owned_mapsto_def). Proof. by eexists. Qed.
  Definition owned_mapsto := owned_mapsto_aux.(unseal).
  Definition owned_mapsto_eq : @owned_mapsto = @owned_mapsto_def := owned_mapsto_aux.(seal_eq).

  Definition access_mapsto_def (i:VMID) dq (s: gset PID) : iProp Σ :=
    ghost_map_elem (gen_access_name vmG) i dq s.
  Definition access_mapsto_aux : seal (@access_mapsto_def). Proof. by eexists. Qed.
  Definition access_mapsto := access_mapsto_aux.(unseal).
  Definition access_mapsto_eq : @access_mapsto = @access_mapsto_def := access_mapsto_aux.(seal_eq).

  Definition excl_mapsto_def (i:VMID) dq (s: gset PID) : iProp Σ :=
    ghost_map_elem (gen_excl_name vmG) i dq s.
  Definition excl_mapsto_aux : seal (@excl_mapsto_def). Proof. by eexists. Qed.
  Definition excl_mapsto := excl_mapsto_aux.(unseal).
  Definition excl_mapsto_eq : @excl_mapsto = @excl_mapsto_def := excl_mapsto_aux.(seal_eq).

  Definition trans_mapsto_def(wh : Word) dq (v r: VMID) (wf: Word) (pgs : (list PID)) (fid : transaction_type) : iProp Σ :=
    wh ↪[ (gen_trans_name vmG) ]{ dq } (((((v, wf) , r), pgs), fid): (leibnizO (VMID * Word * VMID * (list PID) * transaction_type))).
  Definition trans_mapsto_aux : seal (@trans_mapsto_def). Proof. by eexists. Qed.
  Definition trans_mapsto := trans_mapsto_aux.(unseal).
  Definition trans_mapsto_eq : @trans_mapsto = @trans_mapsto_def := trans_mapsto_aux.(seal_eq).

  Definition retri_mapsto_def (w:Word) (b:bool) : iProp Σ :=
    w ↪[ (gen_retri_name vmG) ] b.
  Definition retri_mapsto_aux : seal (@retri_mapsto_def). Proof. by eexists. Qed.
  Definition retri_mapsto := retri_mapsto_aux.(unseal).
  Definition retri_mapsto_eq : @retri_mapsto = @retri_mapsto_def := retri_mapsto_aux.(seal_eq).

  Definition hpool_mapsto_def q (s: gset handle) : iProp Σ :=
    own (gen_hpool_name vmG) (frac_auth_frag q (GSet s)).
  Definition hpool_mapsto_aux : seal (@hpool_mapsto_def). Proof. by eexists. Qed.
  Definition hpool_mapsto := hpool_mapsto_aux.(unseal).
  Definition hpool_mapsto_eq : @hpool_mapsto = @hpool_mapsto_def := hpool_mapsto_aux.(seal_eq).

  Definition nainv_closed E := na_own (gen_nainv_name vmG) E.

  Definition nainv γ P := na_inv (gen_nainv_name vmG) γ P.

End definitions.

(* predicate for current vm (token) *)

Notation "<< n >>{ q }" := (token_agree n q)
                        (at level 50, format "<< n >>{ q  }"): bi_scope.

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
Notation "RX@ i :=( p ! n , r )" := ((rx_agree_mapsto i p) ∗ (rx_option_mapsto i (Some (n,r))))%I
                                        (at level 20, format "RX@ i :=( p ! n , r )"):bi_scope.
Notation "RX@ i :=( p !)" := ((rx_agree_mapsto i p) ∗ (rx_option_mapsto i None))%I
                                        (at level 20, format "RX@ i :=( p !)"):bi_scope.
Notation "RX@ i := p " := (rx_agree_mapsto i p)
                                        (at level 20, format "RX@ i := p"):bi_scope.

(* predicates for pagetables *)
Notation "O@ i :={ q }[ s ] " := (owned_mapsto i (DfracOwn q) s)
                                           (at level 20, format "O@ i :={ q }[ s ] "):bi_scope.
Notation "O@ i :={ q } p" := (owned_mapsto  i (DfracOwn q) {[p]})
                                           (at level 20, format "O@ i :={ q } p "):bi_scope.

Notation "A@ i :={ q }[ s ] " := (access_mapsto i (DfracOwn q) s)
                                          (at level 20, format "A@ i :={ q }[ s ] "):bi_scope.
Notation "A@ i :={ q } p " := (access_mapsto  i (DfracOwn q) {[p]})
                                           (at level 20, format "A@ i :={ q } p "):bi_scope.

Notation "E@ i :={ q }[ s ] " := (excl_mapsto i (DfracOwn q) s)
                                          (at level 20, format "E@ i :={ q }[ s ] "):bi_scope.
Notation "E@ i :={ q } p " := (excl_mapsto  i (DfracOwn q) {[p]})
                                           (at level 20, format "E@ i :={ q } p "):bi_scope.

(* predicates for transactions *)
Notation "w ->t{ q }( v , x , y , m , f )" := (trans_mapsto w (DfracOwn q) v y x m f)
                                                   (at level 20, format "w ->t{ q }( v , x , y , m , f )"):bi_scope.
Notation "w ->re b" := (retri_mapsto w b) (at level 20, format "w ->re b"):bi_scope.

(* predicates for hpool *)
Notation "hp{ q }[ s ]" := (hpool_mapsto q s) (at level 20, format "hp{ q }[ s ]"):bi_scope.

Section alloc_rules.
  (* these rules cannot be parametrized by gen_vmG, otherwise it is not possible to prove any
   adequacy lemmas for examples. *)
  Context `{! gen_VMPreG Addr VMID Word reg_name PID transaction_type Σ}.
  Lemma gen_token_alloc i :
   ⊢ |==> ∃ γ, own γ (get_token i) ∗ own γ (frac_auth_frag 1%Qp (to_agree (i: leibnizO VMID))).
  Proof.
    iIntros.
    rewrite /get_token.
    iDestruct (own_alloc ((●F (to_agree (i: leibnizO VMID))) ⋅ (◯F (to_agree (i: leibnizO VMID))))) as ">Halloc".
    { apply frac_auth_valid. done. }
    iModIntro.
    iDestruct "Halloc" as (γ) "Halloc".
    iExists γ.
    rewrite own_op //.
  Qed.

  Lemma gen_reg_alloc (regs: gmap (reg_name * VMID) Word) :
   ⊢ |==> ∃ γ, ghost_map_auth γ 1%Qp regs ∗
               [∗ map] p↦w∈ regs, ghost_map_elem γ p (DfracOwn 1%Qp) w.
  Proof.
    iApply ghost_map_alloc.
  Qed.

  Lemma gen_mem_alloc (mem: gmap Addr Word) :
   ⊢ |==> ∃ γ, ghost_map_auth γ 1 mem ∗
               [∗ map] p↦w∈ mem, ghost_map_elem γ p (DfracOwn 1) w.
  Proof.
    iApply (ghost_map_alloc mem).
  Qed.

  Lemma gen_tx_alloc (gm : (gmap VMID (agreeR (leibnizO PID)))) :
   ✓ gm ->
   ⊢ |==> ∃ γ, own γ (● gm) ∗ own γ (◯ gm).
  Proof.
    iIntros.
    iDestruct (own_alloc ((● gm) ⋅ (◯ gm ))) as ">Halloc".
    { apply auth_both_valid_discrete. split;done. }
    iModIntro.
    iDestruct "Halloc" as (γ) "Halloc".
    iExists γ.
    rewrite own_op //.
  Qed.

  Definition gen_rx_agree_alloc := gen_tx_alloc.

  Lemma gen_rx_option_alloc (gmo: gmap VMID (option (Word * VMID))):
   ⊢ |==> ∃ γ, ghost_map_auth γ 1 gmo ∗
                              [∗ map] k ↦ v∈ gmo, ghost_map_elem γ k (DfracOwn 1) v.
  Proof.
    iIntros.
    iApply (ghost_map_alloc gmo).
  Qed.

  Lemma gen_pagetable_alloc (gm : gmap VMID (gset PID) ):
   ⊢ |==> ∃ γ, ghost_map_auth γ 1 gm ∗ [∗ map] k ↦ v ∈ gm, ghost_map_elem γ k (DfracOwn 1) v.
  Proof.
    iApply (ghost_map_alloc gm).
  Qed.

  Lemma gen_trans_alloc (gm: gmap Word _):
   ⊢ |==> ∃ γ, ghost_map_auth γ 1 gm ∗ [∗ map] k ↦ v ∈ gm, ghost_map_elem γ k (DfracOwn 1) v.
  Proof.
    iApply (ghost_map_alloc gm).
  Qed.

  Lemma gen_hpool_alloc (gs: gset Word):
   ⊢ |==> ∃ γ, own γ (frac_auth_auth (GSet gs)) ∗ own γ (frac_auth_frag 1 (GSet gs)).
  Proof.
    iIntros.
    iDestruct (own_alloc ((●F (GSet gs)) ⋅ (◯F (GSet gs)))) as ">Halloc".
    { apply frac_auth_valid. done. }
    iModIntro.
    iDestruct "Halloc" as (γ) "Halloc".
    iExists γ.
    rewrite own_op //.
  Qed.

  Lemma gen_retri_alloc (gm: gmap Word bool):
   ⊢ |==> ∃ γ, ghost_map_auth γ 1 gm ∗ [∗ map] k ↦ v ∈ gm, ghost_map_elem γ k (DfracOwn 1) v.
  Proof.
    iApply (ghost_map_alloc gm).
  Qed.

End alloc_rules.

Section other_rules.
  Context `{vmG : !gen_VMG Σ}.

  Lemma nainv_alloc γ E P :  ▷ P ={E}=∗ na_inv (gen_nainv_name vmG) γ P.
  Proof.
    iIntros "P".
    iMod ((na_inv_alloc (gen_nainv_name vmG) E γ P) with "P") as "H".
    done.
  Qed.

  (* all resources are timeless(▷ P -> P),
    which means we can easily get rid of the later modality when opening invariants. *)
  Global Instance token_timeless i q : Timeless (<<i>>{ q }).
  Proof. rewrite token_agree_eq /token_agree_def. apply _. Qed.

  Global Instance mem_mapsto_timeless a q w : Timeless ((a ->a{q} w)).
  Proof. rewrite mem_mapsto_eq /mem_mapsto_def. apply _. Qed.

  Global Instance reg_mapsto_timeless r i a : Timeless ((r @@ i ->r a)).
  Proof. rewrite reg_mapsto_eq /reg_mapsto_def. apply _. Qed.

  Global Instance access_mapsto_timeless i q s : Timeless (A@i:={q}[s]).
  Proof. rewrite access_mapsto_eq /access_mapsto_def. apply _. Qed.

  Global Instance owned_mapsto_timeless i q s : Timeless (O@i:={q}[s]).
  Proof. rewrite owned_mapsto_eq /owned_mapsto_def. apply _. Qed.

  Global Instance excl_mapsto_timeless i q s : Timeless (E@i:={q}[s]).
  Proof. rewrite excl_mapsto_eq /excl_mapsto_def. apply _. Qed.

  Global Instance tx_mapsto_timeless i p : Timeless (TX@ i := p).
  Proof. rewrite tx_mapsto_eq /tx_mapsto_def. apply _. Qed.

  Global Instance rx_mapsto_timeless1 i p : Timeless (RX@ i :=p).
  Proof. rewrite rx_agree_mapsto_eq /rx_agree_mapsto_def. apply _. Qed.

  Global Instance rx_mapsto_timeless2 i p n (r:VMID) : Timeless (RX@ i :=(p ! n , r )).
  Proof. rewrite rx_option_mapsto_eq /rx_option_mapsto_def. apply _. Qed.

  Global Instance rx_mapsto_timeless3 i p : Timeless (RX@ i :=(p !)).
  Proof. rewrite rx_option_mapsto_eq /rx_option_mapsto_def. apply _. Qed.

  Global Instance trans_mapsto_timeless w q v x y m f : Timeless (w ->t{ q }( v , x , y , m , f )).
  Proof. rewrite trans_mapsto_eq /trans_mapsto_def. apply _. Qed.

  Global Instance hpool_mapsto_timeless q sh : Timeless (hp{ q }[ sh ]).
  Proof. rewrite hpool_mapsto_eq /hpool_mapsto_def. apply _. Qed.

  Global Instance retri_mapsto_timeless w (b:bool) : Timeless (w ->re b).
  Proof. rewrite retri_mapsto_eq /retri_mapsto_def. apply _. Qed.

End other_rules.
