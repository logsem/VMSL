From iris.base_logic.lib Require Import gen_heap ghost_map invariants na_invariants.
From iris.algebra Require Import auth agree dfrac csum excl gmap gmap_view gset frac_agree frac_auth.
From iris.proofmode Require Import tactics.
From HypVeri Require Import monad.
From HypVeri Require Export lang machine.
From stdpp Require Import fin_maps.

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

Section definitions.
  Context `{vmG : !gen_VMG Σ}.
  Implicit Type σ: state.

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

  Definition get_pagetable_gmap{Perm: Type} σ (proj: page_table -> gmap PID Perm)
             (checkb: Perm -> bool) : (gmap VMID (gset PID)) :=
    (list_to_map (map (λ v, (v,
         ((list_to_set (map (λ (p:(PID*Perm)), p.1)
           (map_to_list (filter (λ p, (checkb p.2) = true) (proj (get_vm_page_table σ v))))))
                         : gset PID))) (list_of_vmids))).

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

Section hyp_lang_rules.

  Context `{vmG :!gen_VMG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : state.
  Implicit Types a : Addr.
  Implicit Types r : reg_name.
  Implicit Types w: Word.

  Lemma nainv_alloc γ E P :  ▷ P ={E}=∗ na_inv (gen_nainv_name vmG) γ P.
  Proof.
    iIntros "P".
    iMod ((na_inv_alloc (gen_nainv_name vmG) E γ P) with "P") as "H".
    done.
  Qed.

  Lemma token_frag_valid i1 i2 q1 q2 :
   << i1 >>{ q1 } -∗
   << i2 >>{ q2 } -∗
   ⌜ i1 = i2 ⌝ ∧ ⌜ ((q1 + q2) ≤ 1)%Qp ⌝.
  Proof.
    rewrite token_agree_eq /token_agree_def.
    iIntros "H1 H2".
    iDestruct (own_valid_2  with "H1 H2") as %Hvalid.
    rewrite /get_token in Hvalid.
    rewrite <- frac_auth_frag_op in Hvalid.
    apply frac_auth_frag_valid in Hvalid.
    destruct Hvalid.
    apply to_agree_op_inv_L in H0.
    done.
  Qed.

  Lemma token_frag_split i q1 q2 :
   (q1 + q2 = 1)%Qp ->
   << i >>{ 1%Qp } -∗
   << i >>{ q1 } ∗ << i >>{ q2}.
  Proof.
    intro.
    rewrite token_agree_eq /token_agree_def.
    iIntros "H".
    rewrite -own_op.
    rewrite -frac_auth_frag_op.
    rewrite H.
    by rewrite agree_idemp.
  Qed.

  Lemma token_frag_merge i q1 q2 :
   (q2 + q1 = 1)%Qp ->
   << i >>{ q1 } -∗ << i >>{ q2} -∗
   << i >>{ 1%Qp }.
  Proof.
    intro.
    rewrite token_agree_eq /token_agree_def.
    iIntros "H1 H2".
    iDestruct (own_op with "[H1 H2]") as "H".
    iFrame.
    rewrite -frac_auth_frag_op.
    rewrite H.
    by rewrite agree_idemp.
  Qed.

  Lemma token_auth_valid i1 i2 q :
   << i1 >>{ q } -∗
   (own (gen_token_name vmG) (get_token i2)%I) -∗
   ⌜ i1 = i2 ⌝.
  Proof.
    rewrite token_agree_eq /token_agree_def.
    iIntros "H1 H2".
    iDestruct (own_valid_2  with "H2 H1") as %Hvalid.
    rewrite /get_token in Hvalid.
    apply frac_auth_included_total in Hvalid.
    apply to_agree_included in Hvalid.
    destruct Hvalid.
    done.
  Qed.

  Lemma token_update i1 i2 i3 :
   << i1 >>{ 1%Qp } -∗
   (own (gen_token_name vmG) (get_token i2))  ==∗
   << i3 >>{ 1%Qp } ∗ (own (gen_token_name vmG) (get_token i3)).
  Proof.
    rewrite token_agree_eq /token_agree_def /get_token.
    rewrite -own_op.
    iApply own_update_2.
   apply frac_auth_update_1.
   done.
  Qed.

  Lemma gen_token_valid_neq{σ q} i j:
   i ≠ j ->
   << i >>{ q } -∗
   own (gen_token_name vmG) (get_token (get_current_vm σ)) -∗
   ⌜ ¬ scheduler σ j ⌝.
  Proof.
    iIntros (Hne) "Htok Hstate".
    iDestruct (token_auth_valid with "Htok Hstate") as %->.
    iPureIntro.
    rewrite /scheduler .
    intro.
    apply fin_to_nat_inj in H.
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
    r1 @@ i1 ->r w1' ∗ r2 @@ i2 ->r w2'.
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

 Lemma gen_reg_update3_global {σ w1 w2 w3} r1 i1 w1' r2 i2 w2' r3 i3 w3':
    r1 ≠ r2 ∨ i1 ≠ i2  ->
    r1 ≠ r3 ∨ i1 ≠ i3  ->
    r3 ≠ r2 ∨ i3 ≠ i2  ->
    ghost_map_auth (gen_reg_name vmG) 1 (get_reg_gmap σ) -∗
    r1 @@ i1 ->r w1 -∗
    r2 @@ i2 ->r w2 -∗
    r3 @@ i3 ->r w3==∗
    ghost_map_auth (gen_reg_name vmG) 1 (<[(r1,i1) := w1']> (<[(r2,i2) := w2']> (<[(r3,i3):= w3']>(get_reg_gmap σ)))) ∗
    r1 @@ i1 ->r w1'  ∗ r2 @@ i2 ->r w2' ∗ r3 @@ i3 ->r w3'.
 Proof.
  iIntros (Hneq12 Hneq13 Hneq32) "Hreg Hr1 Hr2 Hr3".
  iDestruct ((gen_reg_update_Sep _ {[(r1,i1):=w1; (r2,i2):=w2 ;(r3,i3):=w3]} {[(r1,i1):=w1'; (r2,i2):=w2'; (r3,i3):=w3']}) with "Hreg [Hr1 Hr2 Hr3]")
    as ">[Hreg Hr123]" ;eauto;[set_solver| | ].
  rewrite !big_sepM_insert ?big_sepM_empty;eauto.
  iFrame.
  destruct Hneq32; apply lookup_insert_None; split;eauto; intros P; by inversion P.
  destruct Hneq12; apply lookup_insert_None; split;eauto.
  destruct Hneq13; apply lookup_insert_None; split;eauto; intros P; by inversion P.
  intros P; by inversion P.
  destruct Hneq13; apply lookup_insert_None; split;eauto; intros P; by inversion P.
  intros P; by inversion P.
  iModIntro.
  rewrite !big_sepM_insert ?big_sepM_empty;eauto.
  iDestruct "Hr123" as "(? & ? & ? & _)".
  rewrite ?insert_union_singleton_l !map_union_assoc.
  simplify_map_eq.
  by iFrame.
  destruct Hneq32; apply lookup_insert_None; split;eauto; intros P; by inversion P.
  destruct Hneq12; apply lookup_insert_None; split;eauto.
  destruct Hneq13; apply lookup_insert_None; split;eauto; intros P; by inversion P.
  intros P; by inversion P.
  destruct Hneq13; apply lookup_insert_None; split;eauto; intros P; by inversion P.
  intros P; by inversion P.
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

Lemma gen_mem_valid_SepM {σ} mem:
    ghost_map_auth (gen_mem_name vmG) 1 (get_mem σ) -∗
    ([∗ map] a↦w ∈ mem,  a ->a w)-∗
         ([∗ map] a↦w ∈ mem, ⌜ (get_mem σ) !! a = Some w ⌝).
Proof.
  iIntros  "Hσ Hmem".
  rewrite mem_mapsto_eq /mem_mapsto_def.
  iDestruct ((ghost_map_lookup_big mem) with "Hσ Hmem") as "%Hincl".
  iApply big_sepM_pure.
  iIntros (???).
  iPureIntro.
  apply (lookup_weaken  mem (get_mem σ) _ _ a1 Hincl) .
Qed.

Lemma gen_mem_valid_SepL {σ} al ml:
    NoDup al ->
    ghost_map_auth (gen_mem_name vmG) 1 (get_mem σ) -∗
    ([∗ list] a;w ∈ al;ml,  a ->a w)-∗
         ( [∗ list] a;w ∈ al;ml, ⌜ (get_mem σ) !! a = Some w ⌝) .
Proof.
  iIntros (Hnodup) "Hσ Hmem".
  iDestruct (big_sepL2_alt with "Hmem") as "[% Hmem]".
  iApply big_sepL2_alt.
  iSplitR;eauto.
  rewrite <- (@map_to_list_to_map Addr (gmap Addr) _  _  _  _ _ _ _ _ _ Word (zip al ml)).
  2: { rewrite fst_zip;try lia;eauto.  }
  rewrite -(big_opM_map_to_list (λ a w,  ⌜ (get_mem σ) !! a = Some w ⌝%I) _ ).
  rewrite -(big_opM_map_to_list (λ a w,  (a ->a w)%I) _ ).
  iApply (gen_mem_valid_SepM with "Hσ Hmem").
Qed.

Lemma gen_mem_valid_SepL_pure {σ} al ml:
    NoDup al ->
    ghost_map_auth (gen_mem_name vmG) 1 (get_mem σ) -∗
    ([∗ list] a;w ∈ al;ml,  a ->a w)-∗
         ⌜ ∀ (k : nat) (y1 y2 : Addr),
             al !! k = Some y1 → ml !! k = Some y2 → get_mem σ !! y1 = Some y2 ⌝ .
Proof.
  iIntros (Hnodup) "Hσ Hmem".
  iDestruct (gen_mem_valid_SepL with "Hσ Hmem") as "H";eauto.
  iDestruct ( big_sepL2_pure_1 with "H") as %Hadesc.
  iPureIntro;done.
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
  iDestruct (gen_mem_valid_SepM {[a1:=w1;a2:=w2]} with "Hσ [Ha1 Ha2]") as "%";eauto.
  rewrite !big_sepM_insert ?big_sepM_empty;eauto.
  iFrame.
  by simplify_map_eq.
  iPureIntro.
  split.
  - by apply (H a1 w1 (lookup_insert _ a1 w1)).
  - apply (H a2 w2);eauto.
    by simplify_map_eq.
 Qed.

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

Definition mem_region (instr: list Word) (b:Addr):=
  ([∗ list] a;w ∈ (finz.seq b (length instr));instr, (a ->a w))%I.

(* This definition implicitly requires the length of instr is equal to page_size  *)
Definition mem_page (instr: list Word) (p: PID):=
  ([∗ list] a;w ∈ (finz.seq (of_pid p) (Z.to_nat page_size));instr, (a ->a w))%I.

(* This alternative donesn't require that the length of ws is page_size *)
(* Definition mem_page (p:PID) (ws: list Word):= *)
(*   ([∗ list] i ↦ a ∈ (addr_of_page p), *)
(*    match (ws !! i) with *)
(*      | Some w => (a ->a w) *)
(*      | None => ∃ w, (a->a w) *)
(*    end)%I. *)

Lemma gen_mem_update_Sep_list{ σ} (ads : list Addr) (ws ws': list Word):
 NoDup ads ->
 length ws = length ws' ->
 ghost_map_auth (gen_mem_name vmG) 1 (get_mem σ) -∗
 ([∗ list] a;w ∈ ads;ws, a ->a w) ==∗
 ghost_map_auth (gen_mem_name vmG) 1 ((list_to_map (zip ads ws'))  ∪ (get_mem σ))
 ∗ [∗ list] a;w' ∈ ads;ws', a ->a w'.
Proof.
  iIntros (Hnodup Hlen) "Hσ Hmm".
  iDestruct (big_sepL2_alt with "Hmm") as "[% Hmm]".
  rewrite <- (@map_to_list_to_map Addr (gmap Addr) _  _  _  _ _ _ _ _ _ Word _).
  2: { rewrite fst_zip //;lia. }
  rewrite -(big_opM_map_to_list (λ a w,  (a ->a w)%I) _ ).
  rewrite  mem_mapsto_eq /mem_mapsto_def.
  iDestruct ((ghost_map_update_big _  (list_to_map (zip ads ws'))) with "Hσ Hmm") as ">[Hσ Hmm]".
    { rewrite  !dom_list_to_map_L. f_equal.  rewrite !fst_zip  //. lia. lia. }
  rewrite (big_opM_map_to_list (λ a w,  (a ↪[gen_mem_name vmG] w)%I) _ ).
  rewrite map_to_list_to_map.
  2 : { rewrite fst_zip //. lia. }
  rewrite  big_sepL2_alt.
  iFrame.
  iModIntro. iPureIntro. lia.
Qed.

Lemma gen_mem_update_page{σ ws} p (ws': list Word):
 length ws' = (Z.to_nat page_size) ->
 ghost_map_auth (gen_mem_name vmG) 1 (get_mem σ) -∗
 mem_page ws p ==∗
 ghost_map_auth (gen_mem_name vmG) 1
 (list_to_map (zip (finz.seq p (Z.to_nat page_size)) ws') ∪ get_mem σ)
 ∗ mem_page ws' p.
Proof.
    iIntros (Hlen) "Hσ Hp".
    rewrite /mem_page.
    iAssert (⌜ length ws = Z.to_nat 1000 ⌝%I) as "%Hlen'".
    {  iDestruct (big_sepL2_alt with "Hp") as "[% Hp]". iPureIntro. rewrite finz_seq_length in H. lia. }
    iApply ((gen_mem_update_Sep_list (finz.seq p (Z.to_nat 1000)) ws ws') with "Hσ").
    apply finz_seq_NoDup'. apply last_addr_in_bound.
    lia.
    iFrame.
Qed.

Lemma list_pid_to_addr_NoDup (ps:list PID):
  NoDup ps ->
  NoDup (list_pid_to_addr ps).
Proof.
  intro Hnd.
  rewrite /list_pid_to_addr.
  induction ps.
  - simpl. by apply NoDup_nil.
  - cbn.  apply  NoDup_app.
    split.
    { apply finz_seq_NoDup'. apply last_addr_in_bound. }
    split.
    { intros. apply NoDup_cons in Hnd. destruct Hnd as [ Hnotin Hnd].
      pose proof (finz_seq_in2 _ _ _ H) as Halt.
      pose proof (finz_seq_in1 _ _ _ H) as Hagt.
      clear IHps.
      induction ps.
      cbn.
      apply not_elem_of_nil.
      cbn.
      apply not_elem_of_app.
      split.
      { intro.
        pose proof (finz_seq_in2 _ _ _ H0) as Ha0lt.
        pose proof (finz_seq_in1 _ _ _ H0) as Ha0gt.
        assert (Hne: a ≠ a0).
        apply not_elem_of_cons in Hnotin.
        destruct Hnotin;eauto.
        destruct (decide ((of_pid a)<= (of_pid a0))%f).
        assert (Hlt: ((of_pid a)< (of_pid a0))%f).
        assert (Hne': ((of_pid a) ≠ (of_pid a0))%f).
        intro.
        apply Hne.
        apply of_pid_eq;eauto.
        solve_finz.
        clear l Hne.
        assert (a ^+ (Z.to_nat page_size - 1) < a0 )%f.
        apply pid_lt_lt;eauto.
        solve_finz.
        assert (a0<a)%f.
        solve_finz.
        assert (a0 ^+ (Z.to_nat page_size - 1) < a )%f.
        apply pid_lt_lt;eauto.
        solve_finz.
      }
      apply IHps.
      { apply not_elem_of_cons in Hnotin;destruct Hnotin;done. }
      { apply NoDup_cons in Hnd;destruct Hnd;done. }
    }
    apply IHps.
    apply NoDup_cons in Hnd;destruct Hnd;done.
Qed.

Lemma flat_list_list_word_length_eq wss wss':
 length wss = length wss'->
 (forall ws, ws ∈ wss -> length ws = (Z.to_nat page_size)) ->
 (forall ws', ws' ∈ wss' -> length ws' = (Z.to_nat page_size)) ->
 length (flat_list_list_word wss) = length (flat_list_list_word wss').
Proof.
 intro.
 rewrite /flat_list_list_word.
 generalize dependent  wss'.
 induction wss;destruct wss';eauto;cbn;intros;try inversion H.
 rewrite !app_length.
 rewrite (IHwss wss');eauto.
 rewrite (H0 a).
 rewrite (H1 l).
 done.
 apply elem_of_cons;left;done.
 apply elem_of_cons;left;done.
 intros. apply H0. apply elem_of_cons;right;done.
 intros. apply H1. apply elem_of_cons;right;done.
Qed.

Lemma list_wss_length_correct ps wss:
 ([∗ list] p;ws ∈ ps;wss, mem_page ws p) -∗ ⌜ (forall ws, ws ∈ wss -> length ws = (Z.to_nat page_size)) ⌝.
Proof.
  revert ps.
  rewrite /mem_page.
  induction wss.
  - iIntros (?) "Hl".
    iPureIntro; intros; inversion H.
  -  iIntros (?) "Hl".
  destruct ps; cbn.
  { iExFalso; done. }
  { iIntros (??).
    iDestruct "Hl" as "[Hl Hls]".
    iDestruct (big_sepL2_length with  "Hl") as "%".
    rewrite finz_seq_length in H.
    apply elem_of_cons in a1.
    destruct a1.
    subst a0.
    done.
    iDestruct ((IHwss ps) with "Hls") as "%".
    iPureIntro.
    by apply H1.
  }
Qed.

Lemma list2_pid_words_in p ps wss:
  p ∈ ps ->
   ([∗ list] p;ws ∈ ps;wss, mem_page ws p) ⊢
  ∃ ws,  mem_page ws p ∗ ( mem_page ws p -∗  ([∗ list] p;ws ∈ ps;wss, mem_page ws p)).
Proof.
  iIntros (Hin) "Hl".
  (* lookup_lt_is_Some_1 *)
  apply elem_of_list_lookup_1 in Hin.
  destruct Hin.
  assert (HisSome: is_Some (ps!!x) ). done.
  pose proof (lookup_lt_is_Some_1 ps x HisSome).
  iDestruct (big_sepL2_length with  "Hl") as "%".
  rewrite H1 in H0.
  apply lookup_lt_is_Some_2 in H0.
  destruct H0.
  iExists x0.
  iApply (big_sepL2_lookup_acc (λ _ p0 ws, mem_page ws p0) ps wss );eauto.
Qed.

Lemma mem_page2_invalid{ws ws'} p :
 mem_page ws p ∗ mem_page ws' p -∗ False.
Proof.
  iIntros "[Hpg Hpg']".
  rewrite /mem_page.
  iDestruct (big_sepL2_alt with "Hpg") as "[% Hpg]".
  iDestruct (big_sepL2_alt with "Hpg'") as "[% Hpg']".
  destruct ws, ws';cbn.
  inversion H.
  inversion H.
  inversion H0.
  rewrite finz_seq_cons;[|lia].
  cbn.
  iDestruct "Hpg" as "[Hp Hpg]".
  iDestruct "Hpg'" as "[Hp' Hpg']".
  rewrite mem_mapsto_eq /mem_mapsto_def.
  iDestruct (ghost_map_elem_valid_2 with "Hp Hp'") as "%".
  destruct H1.
  rewrite dfrac_op_own in H1.
  rewrite -> dfrac_valid_own in H1.
  exfalso.
 apply (bool_decide_unpack _).
  by compute.
Qed.

Lemma list2_pid_words_NoDup ps wss:
 ([∗ list] p;ws ∈ ps;wss, mem_page ws p) -∗ ⌜ NoDup ps ⌝.
Proof.
  revert wss.
  induction ps.
  - iIntros (?) "Hl".
    iPureIntro; intros; constructor.
  -  iIntros (?) "Hl".
  destruct wss; cbn.
  { iExFalso; done. }
  { rewrite NoDup_cons.
    iAssert (⌜ a ∉ ps ⌝%I) as "%Hnotin".
    iIntros (?).
    iDestruct "Hl" as "[Hl Hls]".
    iDestruct ((list2_pid_words_in a ps wss) with "Hls") as "Hl'";eauto.
    iDestruct "Hl'" as (ws') "[Hl' Hacc]".
    iApply mem_page2_invalid.
    iFrame.
    iDestruct "Hl" as "[Hl Hls]".
    iDestruct ((IHps wss) with "Hls") as "%".
    iPureIntro.
    done.
    }
Qed.

Lemma mem_page_list_list (ps: list PID) (wss: list (list Word)):
 ([∗ list] p;ws ∈ ps;wss, mem_page ws p) -∗
 [∗ list] a;w ∈ (list_pid_to_addr ps);(flat_list_list_word wss), a ->a w.
Proof.
  rewrite /mem_page /list_pid_to_addr /flat_list_list_word.
  iRevert (wss).
  iInduction ps as [|p ps'] "IH";cbn.
  iIntros (?) "Hl".
  iDestruct (big_sepL2_alt with "Hl") as "[% Hl]".
  destruct a;try inversion H.
  done.
  iIntros (wss) "Hlist".
  destruct wss;cbn;try done.
  iDestruct ("Hlist") as "[Hl Hlist]".
  iApply (big_sepL2_app with "Hl").
  iApply "IH".
  done.
Qed.

Lemma mem_page_list_list' (ps: list PID) (wss: list (list Word)):
 (forall ws', ws' ∈ wss -> length ws' = (Z.to_nat page_size)) ->
 ([∗ list] a;w ∈ (list_pid_to_addr ps);(flat_list_list_word wss), a ->a w) -∗
  ([∗ list] p;ws ∈ ps;wss, mem_page ws p).
Proof.
  rewrite /mem_page /list_pid_to_addr /flat_list_list_word.
  iRevert (wss).
  iInduction ps as [|p ps'] "IH";cbn.
  iIntros (??) "Hl".
  iDestruct (big_sepL2_alt with "Hl") as "[% Hl]".
  destruct a.
  done.
  simpl in H.
  assert (length l = Z.to_nat 1000) as Hlen.
  { apply x. apply elem_of_cons;left;done. }
  rewrite app_length in H.
  lia.
  iIntros (wss Hlen) "Hlist".
  destruct wss;cbn;try done.
  iDestruct (big_sepL2_app_inv with "Hlist") as "Hlist".
  { left. rewrite finz_seq_length. symmetry;apply Hlen.  apply elem_of_cons;left;done. }
  iDestruct ("Hlist") as "[Hl Hlist]".
  iFrame.
  iApply "IH".
  { iPureIntro. intros.
    apply Hlen.
    apply elem_of_cons;right;done. }
  done.
Qed.

Lemma gen_mem_update_pages{wss} σ (ps: list PID) (wss': list (list Word)):
 (forall ws', ws' ∈ wss' -> length ws' = (Z.to_nat page_size)) ->
 length ps = length wss' ->
 ghost_map_auth (gen_mem_name vmG) 1 (get_mem σ) -∗
 ([∗ list] p;ws ∈ ps;wss, mem_page ws p) ==∗
 ghost_map_auth (gen_mem_name vmG) 1 ((list_to_map (zip (list_pid_to_addr ps) (flat_list_list_word wss'))) ∪ (get_mem σ))
 ∗ [∗ list] p;ws'∈ ps;wss',mem_page ws' p.
Proof.
  iIntros (Hwslen Hwsslen) "Hσ Hpgs".
  iDestruct (list2_pid_words_NoDup with "Hpgs") as "%".
  iDestruct (list_wss_length_correct with "Hpgs") as "%".
  iDestruct (big_sepL2_length with "Hpgs") as "%".
  iDestruct (mem_page_list_list with "Hpgs") as "Hpgs".
  iDestruct ((gen_mem_update_Sep_list _ (flat_list_list_word wss) (flat_list_list_word wss')) with "Hσ Hpgs") as ">[Hσ Hpgs]".
  { apply list_pid_to_addr_NoDup;eauto. }
  {  apply  flat_list_list_word_length_eq;eauto. lia. }
  iFrame.
  iApply mem_page_list_list';eauto.
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

 Lemma get_txrx_auth_agree_valid σ f:
  ✓ (get_txrx_auth_agree σ f).
 Proof.
   rewrite /get_txrx_auth_agree.
   induction list_of_vmids;cbn.
   done.
   apply (insert_valid _ a ((to_agree (f (get_vm_mail_box σ a))): (agreeR (leibnizO PID)))).
   { done. }
   apply IHl.
 Qed.

 Lemma gen_tx_valid σ i p:
  TX@ i := p -∗ own (gen_tx_name vmG) (● (get_tx_agree σ)) -∗ ⌜ (get_vm_mail_box σ i).1 = p ⌝.
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
   pose proof (@lookup_included
                 VMID _ _
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
   apply in_map_iff in H0.
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
   iIntros "[HRa HRo]".
   rewrite rx_agree_mapsto_eq rx_option_mapsto_eq.
   iFrame "HRo".
   iApply own_op.
   rewrite -auth_frag_op.
   rewrite singleton_op agree_idemp.
   simplify_eq /=.
   done.
 Qed.

 Lemma rx_split_none i p:
  RX@ i :=(p !) -∗ RX@ i :=(p !) ∗ RX@ i := p.
 Proof using.
   iIntros "[HRa HRo]".
   rewrite rx_agree_mapsto_eq rx_option_mapsto_eq.
   iFrame "HRo".
   iApply own_op.
   rewrite -auth_frag_op.
   rewrite singleton_op agree_idemp.
   simplify_eq /=.
   done.
 Qed.

 Lemma rx_dupl i p:
   RX@i:=p -∗ RX@i:=p ∗ RX@i:=p.
 Proof using.
   iIntros "HR".
   rewrite rx_agree_mapsto_eq.
   iApply own_op.
   rewrite -auth_frag_op.
   rewrite singleton_op agree_idemp.
   naive_solver.
 Qed.
  
 Lemma gen_rx_agree_valid σ i p:
  ✓ (● get_rx_agree σ ⋅ ◯ {[i := to_agree p]}) -> (get_vm_mail_box σ i).2.1 = p.
 Proof.
   intro.
   rewrite /get_rx_agree /get_txrx_auth_agree in H.
   apply auth_both_valid_discrete in H;destruct H as [H _].
   remember  ((list_to_map (map (λ v : VMID, (v, to_agree (get_vm_mail_box σ v).2.1)) list_of_vmids)): gmap VMID (agreeR (leibnizO PID))) as m.
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
  RX@ i := p -∗ own (gen_rx_agree_name vmG) (● (get_rx_agree σ))-∗ ⌜ (get_vm_mail_box σ i).2.1 = p ⌝.
 Proof.
   iIntros "Hrx Hσ".
   rewrite rx_agree_mapsto_eq /rx_agree_mapsto_def.
   iDestruct (own_valid_2 with "Hσ Hrx") as %?.
   iPureIntro.
   by apply gen_rx_agree_valid.
 Qed.

 Lemma gen_rx_none_valid σ i p:
  RX@ i :=( p !) -∗
  ghost_map_auth (gen_rx_option_name vmG) 1 (get_rx_gmap σ)-∗
  ⌜ (get_vm_mail_box σ i).2.2 = None⌝.
 Proof.
   iIntros "[_ Hrx] Hσ".
   rewrite rx_option_mapsto_eq /rx_option_mapsto_def.
   iDestruct (ghost_map_lookup with "Hσ Hrx") as "%".
   rewrite /get_rx_gmap in H.
   apply elem_of_list_to_map_2 in H.
   apply elem_of_list_In in H.
   apply in_map_iff in H.
   destruct H as [x [H _]].
   destruct ((get_vm_mail_box σ x).2.2) eqn:Heqn.
   destruct p0;inversion H.
   inversion H;subst.
   iPureIntro.
   rewrite -Heqn //.
 Qed.

 Lemma gen_rx_valid_some σ i p l v:
  RX@ i :=( p ! l , v) -∗
  ghost_map_auth (gen_rx_option_name vmG) 1 (get_rx_gmap σ)-∗
  ⌜ (get_vm_mail_box σ  i).2.2 = Some(l,v)⌝.
 Proof.
    iIntros "[_ Hrx] Hσ".
    rewrite rx_option_mapsto_eq /rx_option_mapsto_def.
    iDestruct (ghost_map_lookup with "Hσ Hrx") as "%".
   rewrite /get_rx_gmap in H.
   apply elem_of_list_to_map_2 in H.
   apply elem_of_list_In in H.
   apply in_map_iff in H.
   destruct H as [x [H _]].
   destruct ((get_vm_mail_box σ x).2.2) eqn:Heqn.
   destruct p0;inversion H.
   inversion H;subst.
   iPureIntro.
   rewrite -Heqn //.
   inversion H.
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
*)
 (* (* TODO *) *)
 (* Lemma access_split_set_union i q1 q2 (s1 s2 : gset PID): *)
 (*  s1 ## s2 -> *)
 (*  A@i:={(q1+q2)%Qp}[s1 ∪ s2] -∗ A@i:={q1}[s1] ∗ A@i:={q2}[s2]. *)
 (* Proof using. *)
 (*   iIntros (Hdisj) "HO". *)
 (*   rewrite access_mapsto_eq /access_mapsto_def. *)
 (*   iApply own_op. *)
 (*   rewrite -auth_frag_op singleton_op. *)
 (*   rewrite -pair_op. *)
 (*   rewrite (gset_disj_union _ _ Hdisj). *)
 (*   naive_solver. *)
 (* Qed. *)
 (* Lemma access_split_set_diff i q1 q2 (s1 s2 : gset_disj PID): *)
 (*  A@i:={(q1+q2)%Qp}[s1] -∗ A@i:={q1}[s1] ∗ A@i:={q2}[s1 ∖ s2]. *)
 (* Proof using. *)
 (*   iIntros (Hdisj) "HO". *)
 (*   rewrite access_mapsto_eq. *)
 (*   iApply own_op. *)
 (*   rewrite -auth_frag_op singleton_op. *)
 (*   rewrite -pair_op. *)
 (*   rewrite (gset_disj_union _ _ Hdisj). *)
 (*   naive_solver. *)
 (* Qed. *)

 (* Lemma access_split_singleton i q1 q2 (s : gset PID) p: *)
 (*  p ∉ s -> A@i:={(q1+q2)%Qp}[(s ∪ {[p]})] -∗ A@i:={q1}[s] ∗ A@i:={q2}p. *)
 (* Proof using. *)
 (*   iIntros (Hnotin) "HO". *)
 (*   assert (Hdisj: s ## {[p]}). { set_solver. } *)
 (*   iApply (access_split_set i q1 q2 _ _ Hdisj with "HO"). *)
 (* Qed. *)

 Definition get_pagetable_gset {Perm: Type}  σ v  (proj: page_table -> gmap PID Perm)
   (checkb: Perm -> bool):=
   ((list_to_set (map (λ (p:(PID*Perm)), p.1)
           (map_to_list (filter (λ p, (checkb p.2) = true) (proj (get_vm_page_table σ v)))))
                         : gset PID)).

 Lemma gen_pagetable_split_1{Perm: Type} { σ γ} i (proj: page_table -> gmap PID Perm)
       (checkb: Perm -> bool):
  ([∗ map] k↦v ∈ (get_pagetable_gmap σ proj checkb ), ghost_map_elem γ k (dfrac.DfracOwn 1) v)%I -∗
  ghost_map_elem γ i (dfrac.DfracOwn 1) (get_pagetable_gset σ i proj checkb) ∗
  [∗ map] k↦v ∈ (delete i (get_pagetable_gmap σ proj checkb)), ghost_map_elem γ k (dfrac.DfracOwn 1) v.
 Proof.
   iIntros "Hall".
   iApply ((big_sepM_delete _ (get_pagetable_gmap σ proj checkb) i (get_pagetable_gset σ i proj checkb)) with "Hall").
   rewrite /get_pagetable_gmap.
   apply elem_of_list_to_map_1.
   {  rewrite -list_fmap_compose /compose /=. rewrite list_fmap_id. apply NoDup_list_of_vmids. }
   rewrite elem_of_list_In.
   rewrite in_map_iff.
   exists i.
   split.
   rewrite /get_pagetable_gset //.
   apply in_list_of_vmids.
 Qed.

 Lemma gen_pagetable_split_2{Perm: Type} { σ γ} i j (proj: page_table -> gmap PID Perm)
       (checkb: Perm -> bool):
  i ≠ j ->
  ([∗ map] k↦v ∈ (get_pagetable_gmap σ proj checkb ), ghost_map_elem γ k (dfrac.DfracOwn 1) v)%I -∗
  ghost_map_elem γ i (dfrac.DfracOwn 1) (get_pagetable_gset σ i proj checkb) ∗
  ghost_map_elem γ j (dfrac.DfracOwn 1) (get_pagetable_gset σ j proj checkb) ∗
  [∗ map] k↦v ∈ (delete j (delete i (get_pagetable_gmap σ proj checkb))), ghost_map_elem γ k (dfrac.DfracOwn 1) v.
 Proof.
   iIntros (Hne) "Hall".
   iDestruct ((gen_pagetable_split_1 i) with "Hall") as "[Hi Hrest]".
   iFrame.
   iApply ((big_sepM_delete _ _ j (get_pagetable_gset σ j proj checkb)) with "Hrest").
   rewrite /get_pagetable_gmap.
   rewrite lookup_delete_ne;eauto.
   apply elem_of_list_to_map_1.
   {  rewrite -list_fmap_compose /compose /=. rewrite list_fmap_id. apply NoDup_list_of_vmids. }
   rewrite elem_of_list_In.
   rewrite in_map_iff.
   exists j.
   split.
   rewrite /get_pagetable_gset //.
   apply in_list_of_vmids.
 Qed.


 Lemma gen_pagetable_valid_lookup_Set{Perm: Type} {σ i q γ} proj (checkb: Perm -> bool) (s:gset PID):
  ghost_map_auth γ 1 (get_pagetable_gmap σ proj checkb)  -∗
  ghost_map_elem γ i (DfracOwn q) s -∗
  ⌜(get_pagetable_gmap σ proj checkb) !! i = Some s ⌝.
 Proof.
   iIntros  "Hσ Hpt".
   iApply (ghost_map_lookup with "Hσ Hpt").
 Qed.

 Lemma gen_access_valid_lookup_Set σ i q s:
  ghost_map_auth (gen_access_name vmG) 1 (get_access_gmap σ) -∗
  (A@ i :={q}[s] ) -∗
  ⌜(get_access_gmap σ) !! i = Some s ⌝.
 Proof.
   iIntros  "Hσ Hacc".
   rewrite access_mapsto_eq /access_mapsto_def.
   iApply (gen_pagetable_valid_lookup_Set with "Hσ Hacc").
 Qed.

 Lemma gen_excl_valid_lookup_Set σ i q s:
  ghost_map_auth (gen_excl_name vmG) 1 (get_excl_gmap σ) -∗
  (E@ i :={q}[s] ) -∗
  ⌜(get_excl_gmap σ) !! i = Some s⌝.
 Proof.
   iIntros  "Hσ Hexcl".
   rewrite excl_mapsto_eq /excl_mapsto_def.
   iApply (gen_pagetable_valid_lookup_Set with "Hσ Hexcl").
 Qed.

 Lemma gen_pagetable_valid_Set{Perm: Type} {σ i q γ} proj (checkb: Perm -> bool) (s:gset PID):
  ghost_map_auth γ 1 (get_pagetable_gmap σ proj checkb) -∗
  ghost_map_elem γ i (DfracOwn q) s -∗
  ([∗ set]  p ∈ s, ∃ perm, ⌜(proj (get_vm_page_table σ i)) !! p =Some perm ∧ checkb perm = true ⌝).
 Proof.
   iIntros "Hσ Hpt".
   iDestruct (gen_pagetable_valid_lookup_Set with "Hσ Hpt") as %Hvalid.
   iPureIntro.
   apply (elem_of_list_to_map_2 _ i s) in Hvalid.
   apply elem_of_list_In in Hvalid.
   apply in_map_iff in Hvalid.
   destruct Hvalid.
   destruct H.
   inversion H.
   simplify_eq /=.
   intros p Hin.
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
   exists x.2.
   done.
 Qed.

 Lemma gen_own_valid_Set {σ i q} (s:gset PID):
  ghost_map_auth (gen_owned_name vmG) 1 (get_owned_gmap σ) -∗
  (O@ i :={q}[s] ) -∗
  ([∗ set]  p ∈ s, ∃ perm, ⌜(get_vm_page_table σ i).1 !! p =Some perm ∧ is_owned perm = true ⌝).
 Proof.
   iIntros "Hσ Hown".
   rewrite owned_mapsto_eq /owned_mapsto_def /get_owned_gmap.
   iApply (gen_pagetable_valid_Set with "Hσ Hown").
 Qed.

 Lemma gen_access_valid_Set {σ i q} (s:gset PID):
  ghost_map_auth (gen_access_name vmG) 1 (get_access_gmap σ) -∗
  (A@ i :={q}[s] ) -∗
  ([∗ set]  p ∈ s, ∃ perm, ⌜(get_vm_page_table σ i).2 !! p =Some perm ∧ is_accessible perm = true ⌝).
 Proof.
   iIntros "Hσ Hacc".
   rewrite access_mapsto_eq /access_mapsto_def /get_access_gmap.
   iApply (gen_pagetable_valid_Set with "Hσ Hacc").
 Qed.

 Lemma gen_excl_valid_Set {σ i q} (s:gset PID):
  ghost_map_auth (gen_excl_name vmG) 1 (get_excl_gmap σ) -∗
  (E@ i :={q}[s] ) -∗
  ([∗ set]  p ∈ s, ∃ perm, ⌜(get_vm_page_table σ i).2 !! p =Some perm ∧ is_exclusive perm = true ⌝).
 Proof.
   iIntros "Hσ Hexcl".
   rewrite excl_mapsto_eq /excl_mapsto_def /get_excl_gmap.
   iApply (gen_pagetable_valid_Set with "Hσ Hexcl").
 Qed.

 Lemma gen_access_valid_Set_check σ i q s:
  ghost_map_auth (gen_access_name vmG) 1 (get_access_gmap σ) -∗
  (A@ i :={q}[s] ) -∗
  ([∗ set]  p ∈ s, ⌜(check_access_page' σ i p)= true ⌝).
 Proof.
   iIntros "Hσ Hacc".
   rewrite access_mapsto_eq /access_mapsto_def.
   iDestruct (gen_pagetable_valid_Set with "Hσ Hacc") as %Hvalid.
   iPureIntro.
   intros p Hin.
   unfold check_access_page'.
   pose proof (Hvalid p Hin).
   destruct H.
   destruct H.
   rewrite H /= //.
 Qed.

 Lemma gen_access_valid:
  ∀ (σ : state) i q p,
    ghost_map_auth (gen_access_name vmG) 1 (get_access_gmap σ) -∗
    (A@ i :={q}p ) -∗
    ⌜(check_access_page' σ i p)= true ⌝.
 Proof.
   iIntros (????) "Hσ Hacc".
   iDestruct (gen_access_valid_Set_check _ _ _ {[p]} with "Hσ Hacc") as %->;eauto.
   set_solver.
 Qed.

 Lemma gen_access_valid2:
  ∀ (σ : state) i q s p1 p2,
    {[p1;p2]} ⊆ s ->
    ghost_map_auth (gen_access_name vmG) 1 (get_access_gmap σ) -∗
    (A@ i :={q}[s] ) -∗
    ( ⌜(check_access_page' σ i p1)= true⌝ ∗ ⌜(check_access_page' σ i p2)= true ⌝).
 Proof.
  iIntros (?????? Hsubset) "Hσ Hacc".
  iDestruct (gen_access_valid_Set_check _ _ _ s with "Hσ Hacc") as %Hcheck;eauto.
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

 Lemma gen_access_valid_addr {σ i q} a p:
  addr_in_page a p ->
  ghost_map_auth (gen_access_name vmG) 1 (get_access_gmap σ) -∗
  (A@ i :={q} p ) -∗
  ⌜(check_access_addr σ i a)= true ⌝.
 Proof.
   iIntros (HIn) "Haccess Hacc".
   iDestruct (gen_access_valid σ i q p with "Haccess Hacc") as %Hacc.
   iPureIntro.
   unfold check_access_addr.
   apply to_pid_aligned_in_page in HIn.
   rewrite HIn //=.
 Qed.

 Lemma gen_access_valid_addr_Set {σ i q} a p s:
  addr_in_page a p ->
  p ∈ s ->
  ghost_map_auth (gen_access_name vmG) 1 (get_access_gmap σ) -∗
  (A@ i :={q}[s] ) -∗
  ⌜(check_access_addr σ i a)= true ⌝.
 Proof.
   iIntros (HaIn HpIn) "Haccess Hacc".
   iDestruct (gen_access_valid_Set with "Haccess Hacc") as %Hacc.
   iPureIntro.
   unfold check_access_addr.
   apply to_pid_aligned_in_page in HaIn.
   rewrite HaIn /check_access_page'.
   pose proof (Hacc p HpIn).
   destruct H.
   destruct H.
   rewrite H //.
 Qed.

 Lemma gen_access_valid_addr_elem{ σ i q } a s:
  to_pid_aligned a ∈ s ->
  ghost_map_auth (gen_access_name vmG) 1 (get_access_gmap σ) -∗
  (A@ i :={q}[s] ) -∗
  ⌜(check_access_addr σ i a)= true ⌝.
 Proof.
   iIntros (?) "Haccess Hacc".
   iDestruct (gen_access_valid_Set_check σ i q s with "Haccess Hacc") as %Hacc.
   iPureIntro.
   pose proof (Hacc (to_pid_aligned a)) as H'.
   apply H'.
   set_solver.
 Qed.

 Lemma gen_access_valid_addr2 {σ i q } a1 a2 s:
  s= {[(to_pid_aligned a1); (to_pid_aligned a2)]} ->
  ghost_map_auth (gen_access_name vmG) 1 (get_access_gmap σ) -∗
  (A@ i :={q}[s] ) -∗
  ⌜(check_access_addr σ i a1)= true ⌝ ∗ ⌜(check_access_addr σ i a2)= true ⌝.
 Proof.
   iIntros (?) "Haccess Hacc".
   iDestruct (gen_access_valid_Set_check σ i q s with "Haccess Hacc") as %Hacc.
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
    ghost_map_auth (gen_access_name vmG) 1 (get_access_gmap σ) -∗
    (A@ i :={1}[s]) -∗
    ⌜(check_access_page' σ i p)= false ⌝.
 Proof.
   iIntros (?????) "Hσ Hacc".
   rewrite access_mapsto_eq /access_mapsto_def.
   iDestruct (ghost_map_lookup with "Hσ Hacc") as %Hvalid.
   rewrite /check_access_page'.
   rewrite /get_access_gmap /get_pagetable_gmap in Hvalid.
   apply elem_of_list_to_map_2 in Hvalid.
   apply elem_of_list_In in Hvalid.
   apply in_map_iff in Hvalid.
   destruct Hvalid as [x [Hvalid Hvalid']].
   inversion Hvalid; subst;
   clear Hvalid.
   rewrite /get_vm_page_table.
   apply not_elem_of_list_to_set in H.
   rewrite /get_page_tables.
   rewrite /get_vm_page_table /get_page_tables in H.
   destruct ((σ.1.1.1.2 !!! i).2 !! p) eqn:Heq.
   rewrite Heq /=.
   destruct (is_accessible a) eqn:Heqn'; try done.
   exfalso.
   apply H.
   apply elem_of_list_In.
   apply in_map_iff.
   exists (p, a).
   split; eauto.
   rewrite <-elem_of_list_In.
   rewrite elem_of_map_to_list.
   apply map_filter_lookup_Some.
   split; auto.
   rewrite Heq //.
 Qed.

 Lemma gen_pagetable_update_diff {Perm: Type} {σ i γ s} proj (checkb: Perm -> bool) sps:
  ghost_map_elem γ i (DfracOwn 1) s -∗
  ghost_map_auth γ 1 (get_pagetable_gmap σ proj checkb) ==∗
  ghost_map_auth γ 1 (<[i:= (s∖sps)]>(get_pagetable_gmap σ proj checkb)) ∗
  ghost_map_elem γ i (DfracOwn 1) (s∖sps).
 Proof.
   iIntros "Hpt Hσ".
   iApply (ghost_map_update (s∖sps) with "Hσ Hpt").
 Qed.

 Lemma gen_access_update_diff{σ i sacc} sps:
  A@i:={1}[sacc] -∗
  ghost_map_auth (gen_access_name vmG) 1 (get_access_gmap σ)==∗
  ghost_map_auth (gen_access_name vmG) 1 (<[i:= (sacc∖sps)]>(get_access_gmap σ)) ∗
  A@i:={1}[sacc∖sps].
 Proof.
   iIntros "HA Hacc".
   rewrite access_mapsto_eq /access_mapsto_def.
   iApply (gen_pagetable_update_diff with "HA Hacc");eauto.
 Qed.

 Lemma gen_excl_update_diff{σ i sexcl} sps:
  E@i:={1}[sexcl] -∗
  ghost_map_auth (gen_excl_name vmG) 1 (get_excl_gmap σ)==∗
  ghost_map_auth (gen_excl_name vmG) 1 (<[i:= (sexcl∖sps)]>(get_excl_gmap σ)) ∗
  E@i:={1}[sexcl∖sps].
 Proof.
   iIntros "HE Hexcl".
   rewrite excl_mapsto_eq /excl_mapsto_def.
   iApply (gen_pagetable_update_diff with "HE Hexcl");eauto.
 Qed.

(* rules for transactions *)
 Lemma trans_split wh q1 q2 i (r:VMID) wf m f:
  wh ->t{(q1+q2)%Qp}(i,wf,r,m,f) -∗  wh ->t{q1}(i,wf,r,m,f) ∗ wh ->t{q2}(i,wf,r,m,f).
 Proof using.
   iIntros "HT".
   rewrite trans_mapsto_eq /trans_mapsto_def.
   rewrite ?ghost_map_elem_eq /ghost_map_elem_def.
   rewrite -own_op gmap_view_frag_add //.
 Qed.

 Lemma gen_trans_valid {σ q i wf} {r:VMID} {m f} wh :
  wh ->t{q}(i,wf,r,m,f) -∗
  (ghost_map_auth (gen_trans_name vmG) 1 (get_trans_gmap σ))-∗
  ⌜∃ (b:bool), (get_transactions σ).1 !! wh = Some (i,wf,b,r,m,f) ⌝.
 Proof.
 Admitted.

 Lemma gen_trans_update_insert {σ} h i wf rc m f:
  (get_trans_gmap σ) !! h = None ->
  (ghost_map_auth (gen_trans_name vmG) 1 (get_trans_gmap σ))==∗
  (ghost_map_auth (gen_trans_name vmG) 1 (<[h:= (i,wf,rc,m,f)]>(get_trans_gmap σ)))∗
  h ->t{1}(i,wf,rc,m,f).
 Proof.
   iIntros (HNone) "Htrans".
   rewrite trans_mapsto_eq /trans_mapsto_def.
   iApply (ghost_map_insert with "Htrans");eauto.
 Qed.

 Lemma gen_hpool_valid_subset {σ q} s :
  hp{ q }[ s ] -∗
  (own (gen_hpool_name vmG) (frac_auth_auth (GSet (get_hpool_gset σ))))-∗
  ⌜ s ⊆ (get_hpool_gset σ) ⌝.
 Proof.
   rewrite hpool_mapsto_eq /hpool_mapsto_def.
   iIntros "H1 H2".
   iDestruct (own_valid_2  with "H2 H1") as %Hvalid.
   rewrite /get_hpool_gset in Hvalid.
   apply frac_auth_included in Hvalid.
   iPureIntro.
   apply option_included_total in Hvalid.
   destruct Hvalid as [|Hvalid];[done|].
   destruct Hvalid as [? [? [Heq1 [Heq2 Hincl]]]].
   inversion Heq1;subst x.
   inversion Heq2;subst x0.
   apply gset_disj_included in Hincl.
   assumption.
 Qed.

 Lemma gen_hpool_valid_eq {σ} s :
  hp{ 1 }[ s ] -∗
  (own (gen_hpool_name vmG) (frac_auth_auth (GSet (get_hpool_gset σ))))-∗
  ⌜ s = (get_hpool_gset σ) ⌝.
 Proof.
   rewrite hpool_mapsto_eq /hpool_mapsto_def.
   iIntros "H1 H2".
   iDestruct (own_valid_2  with "H2 H1") as %Hvalid.
   rewrite /get_hpool_gset in Hvalid.
   apply frac_auth_agree_L in Hvalid.
   iPureIntro.
   inversion Hvalid.
   done.
 Qed.

 Lemma gen_hpool_valid {σ q} s :
  hp{ q }[ s ] -∗
  (own (gen_hpool_name vmG) (frac_auth_auth (GSet (get_hpool_gset σ))))-∗
  ⌜ (elements s) ⊆ get_fresh_handles (get_transactions σ) ⌝.
 Proof.
   iIntros "H1 H2".
   iDestruct (gen_hpool_valid_subset  with "H1 H2") as %Hvalid.
   rewrite /get_hpool_gset in Hvalid.
   rewrite /get_fresh_handles.
   iPureIntro.
   set_solver.
 Qed.

 Lemma gen_hpool_valid1 {σ} s :
  hp{ 1 }[ s ] -∗
  (own (gen_hpool_name vmG) (frac_auth_auth (GSet (get_hpool_gset σ))))-∗
  ⌜ (elements s) = get_fresh_handles (get_transactions σ) ⌝.
 Proof.
   iIntros "H1 H2".
   iDestruct (gen_hpool_valid_eq  with "H1 H2") as %Hvalid.
   rewrite /get_hpool_gset in Hvalid.
   rewrite /get_fresh_handles.
   iPureIntro.
   set_solver.
 Qed.

 Lemma gen_hpool_update_diff {σ s q} (h: handle):
  h ∈ s ->
  hp{ q }[ s ] -∗
  (own (gen_hpool_name vmG) (frac_auth_auth (GSet (get_hpool_gset σ)))) ==∗
  (own (gen_hpool_name vmG) (frac_auth_auth (GSet ( (get_hpool_gset σ)∖ {[h]}))))∗
  hp{ q }[ s ∖ {[h]} ].
 Proof.
   iIntros (HIn) "Hhp HHp".
   iDestruct (gen_hpool_valid_subset with "Hhp HHp")as %Hvalid.
   rewrite hpool_mapsto_eq /hpool_mapsto_def.
   rewrite -own_op.
   iApply ((own_update _ (●F (GSet (get_hpool_gset σ)) ⋅ ◯F{q } (GSet s)) _ ) with "[HHp Hhp]").
   2: { rewrite own_op. iFrame. }
   apply frac_auth_update.
   set (X := (get_hpool_gset σ ∖ {[h]})).
   set (Y := (s ∖ {[h]})).
   assert (HX: GSet (get_hpool_gset σ) = GSet {[h]} ⋅ GSet X ).
   { rewrite gset_disj_union;[|set_solver].  f_equal. rewrite singleton_union_difference_L.
     rewrite difference_diag_L difference_empty_L. set_solver. }
   assert (HY: GSet s = GSet {[h]} ⋅ GSet Y ).
   { rewrite gset_disj_union;[|set_solver].  f_equal. rewrite singleton_union_difference_L.
     rewrite difference_diag_L difference_empty_L. set_solver. }
   rewrite HX HY.
   apply gset_disj_dealloc_op_local_update.
 Qed.

 Lemma gen_hpool_update_union {σ s q} (h: handle):
  h ∉ (get_hpool_gset σ) ->
  hp{ q }[ s ] ∗
  (own (gen_hpool_name vmG) (frac_auth_auth (GSet (get_hpool_gset σ)))) ==∗
  (own (gen_hpool_name vmG) (frac_auth_auth (GSet ( (get_hpool_gset σ) ∪ {[h]}))))∗
  hp{ q }[ s ∪ {[h]} ].
 Proof.
   iIntros (HIn) "[Hhp HHp]".
   iDestruct (gen_hpool_valid_subset with "Hhp HHp")as %Hvalid.
   rewrite hpool_mapsto_eq /hpool_mapsto_def.
   rewrite -own_op.
   iApply ((own_update _ (●F (GSet (get_hpool_gset σ)) ⋅ ◯F{q} (GSet s)) _ ) with "[HHp Hhp]").
   2: { rewrite own_op. iFrame. }
   apply frac_auth_update.
   set (X := (get_hpool_gset σ ∖ {[h]})).
   set (Y := (s ∖ {[h]})).
   rewrite union_comm_L.
   assert (HY: GSet (s ∪ {[h]}) = GSet ({[h]} ∪ s) ).
   { rewrite union_comm_L //. }
   rewrite HY.
   apply gset_disj_alloc_local_update;by set_solver.
 Qed.

 Lemma gen_retri_update_insert {σ} (h: handle):
  (get_retri_gmap σ) !! h = None ->
  ghost_map_auth (gen_retri_name vmG) 1 (get_retri_gmap σ) ==∗
  ghost_map_auth (gen_retri_name vmG) 1 (<[h:=false]>(get_retri_gmap σ))∗
  h ->re false.
 Proof.
   iIntros (HNone) "H".
   rewrite retri_mapsto_eq /retri_mapsto_def.
   iDestruct (ghost_map_insert with "H") as "H";eauto.
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

End hyp_lang_rules.
