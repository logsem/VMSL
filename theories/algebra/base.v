From iris.base_logic.lib Require Export invariants na_invariants gen_heap ghost_map saved_prop.
From iris.algebra Require Export auth agree frac excl gmap gset frac_agree frac_auth gset_bij.
From iris.proofmode Require Export tactics.
From HypVeri Require Import monad machine machine_extra.
From HypVeri Require Export lang.

Inductive MailBox :=
  RX
| TX.

Local Instance mb_eqdec :EqDecision MailBox.
Proof.
  intros x y.
  destruct x, y.
  left;done.
  right;done.
  right;done.
  left;done.
Qed.

Local Instance mb_countable : Countable MailBox.
Proof.
  refine {| encode r :=  match r with
                         | RX => encode (Some ())
                         | TX => encode (None)
                         end;
           decode n := match decode n with
                       | Some (Some ()) => Some RX
                       | Some (None) => Some TX
                       | _ => None
                       end ;
           decode_encode := _ |}.
  intro.
  destruct x;auto.
  rewrite ->(decode_encode None).
  done.
Qed.


Class gen_VMPreG  (A V W R P F: Type) (Σ:gFunctors)
        `{Countable A, Countable V, Countable W, Countable R, Countable P, Countable (V * MailBox)} := {
  gen_mem_preG_inG :> gen_heapGpreS A W Σ;
  gen_reg_preG_inG :> gen_heapGpreS (R * V) W Σ;
  gen_rx_preG_inG :> gen_heapGpreS V (option (W * V)) Σ;
  gen_mb_preG_inG :> gen_heapGpreS (V * MailBox) P Σ;
  gen_own_preG_inG :> gen_heapGpreS P (option V) Σ;
  gen_access_preG_inG :> inG Σ (authR (gmapUR V (prodR fracR (gset_disjR (leibnizO P)))));
  gen_excl_preG_inG :> gen_heapGpreS P boolO Σ;
  gen_trans_preG_inG :> gen_heapGpreS W (V * W * V * (gset P) * F) Σ;
  gen_hpool_preG_inG :> inG Σ (frac_authR (gsetR (leibnizO W)));
  gen_retri_preG_inG :> gen_heapGpreS W bool Σ;
  gen_lower_bound_preG_inG :> inG Σ (authR (gmapUR V (exclR (gsetR (leibnizO P)))))
  }.

Section gen_vmG.
  Context `{hypconst : !HypervisorConstants}.

  Class gen_VMG Σ := GenVMG{
                            gen_VM_inG :> gen_VMPreG Addr VMID Word reg_name PID transaction_type Σ;
                            gen_invG :> invGS Σ;
                            gen_saved_propG :> savedPropG Σ;
                            gen_prop_nameG :> inG Σ (authUR (optionUR (frac_agreeR gnameO)));
                            gen_name_mapG :> inG Σ (authUR (gmapUR nat (agreeR gnameO)));
                            gen_name_map_name: gname;
                            gen_mem_name : gname;
                            gen_reg_name : gname;
                            gen_mb_name : gname;
                            gen_rx_state_name : gname;
                            gen_own_name : gname;
                            gen_access_name : gname;
                            gen_excl_name : gname;
                            gen_trans_name : gname;
                            gen_hpool_name : gname;
                            gen_retri_name : gname;
                            gen_lower_bound_name: gname
                       }.

  Global Arguments gen_mem_name {Σ} {_}.
  Global Arguments gen_reg_name {Σ} {_}.
  Global Arguments gen_rx_state_name {Σ} {_}.
  Global Arguments gen_mb_name {Σ} {_}.
  Global Arguments gen_own_name {Σ} {_}.
  Global Arguments gen_access_name {Σ} {_}.
  Global Arguments gen_excl_name {Σ} {_}.
  Global Arguments gen_trans_name {Σ} {_}.
  Global Arguments gen_hpool_name {Σ} {_}.
  Global Arguments gen_retri_name {Σ} {_}.
  Global Arguments gen_name_map_name {Σ} {_}.
  Global Arguments gen_lower_bound_name {Σ} {_}.


  Definition gen_VMΣ : gFunctors :=
    #[
           invΣ;
           na_invΣ;
           gen_heapΣ Addr Word;
           gen_heapΣ (reg_name * VMID) Word;
           gen_heapΣ VMID (option (Word*VMID));
           gen_heapΣ PID (option VMID);
           gen_heapΣ (VMID* MailBox) PID;
           GFunctor (authUR (gmapUR VMID (prodR fracR (gset_disjR (leibnizO PID)))));
           gen_heapΣ PID boolO;
           gen_heapΣ Word (VMID * Word *  VMID * (gset PID) * transaction_type);
           GFunctor (frac_authR (gsetR (leibnizO Word)));
           gen_heapΣ Word bool;
           GFunctor (authR (gmapUR VMID (exclR (gsetR (leibnizO PID)))))
      ].


  Global Instance subG_gen_VMPreG {Σ}:
   subG gen_VMΣ Σ -> gen_VMPreG Addr VMID Word reg_name PID transaction_type Σ.
  Proof.
    solve_inG.
  Qed.

End gen_vmG.

Section definitions.
  Context `{hypconst : !HypervisorConstants}.

  Implicit Type σ: state.

  Definition get_reg_gmap σ: gmap (reg_name * VMID) Word :=
     (list_to_map (flat_map (λ v, (map (λ p, ((p.1,v),p.2)) (map_to_list (get_reg_file σ @ v)))) (list_of_vmids))).

  Definition get_rx_gmap σ : gmap VMID (option (Word*VMID)) :=
            ((list_to_map (map (λ v, let mb := (get_mail_box σ @ v) in
                                    match mb.2.2 with
                                      | Some (l, j) => (v, (Some ( l, j)))
                                      | None => (v,None)
                                    end) (list_of_vmids)))).

  Definition get_mb_gmap σ : gmap (VMID * MailBox) PID :=
    list_to_map (flat_map (λ v, let mb := (get_mail_box σ @ v) in
                            [((v,TX), mb.1);((v,RX), mb.2.1)]
                          ) (list_of_vmids)).

  Definition get_own_gmap σ : gmap PID (option VMID):=
    let pt := (get_page_table σ) in
    ((λ (p: (option VMID * _ * _)), p.1.1) <$> pt).

  Definition get_access_gmap σ : gmap VMID (frac * (gset_disj PID)):=
    let pt := (get_page_table σ) in
    list_to_map (map (λ i, (i,(1%Qp, GSet (dom (gset PID) (map_filter
                                          (λ (kv: PID * permission), i ∈ kv.2.2) _ pt))))) (list_of_vmids)).

  Definition get_excl_gmap σ : gmap PID bool:=
    let pt := (get_page_table σ) in
    ((λ (p: (_ * bool * _)), p.1.2) <$> pt).

  Definition get_transactions_gmap{Info: Type} σ (proj : transaction -> Info):
   gmap Word Info :=
    list_to_map (map (λ (p:Word * transaction) ,
                         (p.1, (proj p.2)))  (map_to_list (get_transactions σ).1)).

  Definition get_trans_gmap σ :=
    get_transactions_gmap σ (λ tran, tran.1).

  Definition get_hpool_gset σ := (get_transactions σ).2.

  Definition get_retri_gmap σ := get_transactions_gmap σ (λ tran, tran.2).

  Definition inv_trans_hpool_disj (trans: gmap Word transaction) (hpool: gset _) := (dom (gset Word) trans) ## hpool.

  Definition inv_trans_pg_num_ub (trans: gmap Word transaction) :=
    map_Forall (λ _ v, (Z.of_nat (size v.1.1.2) <? word_size)%Z = true) trans.

  Definition inv_trans_pgs_disj (trans: gmap Word transaction) :=
    map_Forall (λ h tran,  map_Forall( λ h' tran', h' ≠ h -> tran.1.1.2 ## tran'.1.1.2 ) trans) trans.

  Definition inv_trans_sndr_rcvr_neq (trans: gmap Word transaction) :=
    map_Forall (λ h tran, tran.1.1.1.1.1 ≠ tran.1.1.1.2) trans.

  Definition inv_trans_wellformed' (trans : gmap Word transaction) :=
    inv_trans_pgs_disj trans ∧ inv_trans_pg_num_ub trans ∧ inv_trans_sndr_rcvr_neq trans.

  Definition inv_trans_wellformed σ := inv_trans_wellformed' (get_transactions σ).1.

  Definition inv_finite_handles (trans: gmap Word transaction) (hpool: gset _) :=
    list_to_set (finz.seq W0 100) = dom (gset Word) trans ∪ hpool.

  Definition inv_trans_hpool_consistent' (trans: gmap Word transaction) (hpool: gset _) :=
    (inv_trans_hpool_disj trans hpool) ∧ (inv_finite_handles trans hpool).

  Definition inv_trans_hpool_consistent σ := inv_trans_hpool_consistent' (get_transactions σ).1 (get_transactions σ).2.

  Definition inv_trans_pgt_consistent' (trans: gmap Word transaction) (pgt: gmap PID permission) :=
    map_Forall
           (λ (k:Word) v,
               let sender := v.1.1.1.1.1 in
               let receiver := v.1.1.1.2 in
               ∀ p, p ∈ v.1.1.2 ->
               match v.1.2(* type *), v.2(*retrieved*) with
                 | Sharing, false =>  pgt !! p = Some (Some sender, false, {[sender]})
                 | Sharing, true =>  pgt !! p = Some (Some sender, false, {[sender;receiver]})
                 | Donation, false | Lending, false => pgt !! p = Some (Some sender, true, ∅)
                 | Lending, true=>  pgt !! p = Some (Some sender, true , {[receiver]})
                 | Donation, true => False
            end
    ) trans.

  Definition inv_trans_pgt_consistent σ := inv_trans_pgt_consistent' (get_transactions σ).1 (get_page_table σ).

  Definition inv_pgt_mb_consistent' (pgt : gmap PID permission) (mb : vec mail_box vm_count) :=
    ∀ (i:VMID), match mb !!! i with
                |(tx, (rx, _)) => pgt !! tx = Some (None, true, {[i]}) ∧ pgt !! rx = Some (None, true, {[i]})
                end.

  Definition inv_mb_wellformed σ :=
    map_Forall (λ k p, map_Forall (λ k' p', k ≠ k' -> p ≠ p' ) (get_mb_gmap σ) ) (get_mb_gmap σ).

  Definition inv_pgt_mb_consistent σ := inv_pgt_mb_consistent' (get_page_table σ) (get_mail_boxes σ).

  Context `{vmG: !gen_VMG Σ}.

  Definition gen_vm_interp n σ: iProp Σ :=
      ⌜n = vm_count⌝
      ∗ ghost_map_auth gen_mem_name 1 (get_mem σ)
      ∗ ghost_map_auth gen_reg_name 1 (get_reg_gmap σ)
      ∗ ghost_map_auth gen_mb_name 1 (get_mb_gmap σ)
      ∗ ghost_map_auth gen_rx_state_name 1 (get_rx_gmap σ)
      ∗ ghost_map_auth gen_own_name 1 (get_own_gmap σ)
      ∗ own gen_access_name (● (get_access_gmap σ))
      ∗ ghost_map_auth gen_excl_name 1 (get_excl_gmap σ)
      ∗ ghost_map_auth gen_trans_name 1 (get_trans_gmap σ)
      ∗ own gen_hpool_name (frac_auth_auth (get_hpool_gset σ))
      ∗ ghost_map_auth gen_retri_name 1 (get_retri_gmap σ)
      ∗ ⌜inv_trans_hpool_consistent σ⌝
      ∗ ⌜inv_trans_wellformed σ⌝
      ∗ ⌜inv_trans_pgt_consistent σ⌝
      ∗ ⌜inv_pgt_mb_consistent σ⌝
      ∗ ⌜inv_mb_wellformed σ⌝
  .

  Definition mem_mapsto_def (a:Addr) (q : frac) (w:Word) : iProp Σ :=
    (ghost_map_elem gen_mem_name a (DfracOwn q) w).
  Definition mem_mapsto_aux : seal (@mem_mapsto_def). Proof. by eexists. Qed.
  Definition mem_mapsto := mem_mapsto_aux.(unseal).
  Definition mem_mapsto_eq : @mem_mapsto = @mem_mapsto_def := mem_mapsto_aux.(seal_eq).

  Definition reg_mapsto_def (r:reg_name) (i:VMID) (q : frac) (w:Word) : iProp Σ :=
    (ghost_map_elem gen_reg_name (r,i) (DfracOwn q) w).
  Definition reg_mapsto_aux : seal (@reg_mapsto_def). Proof. by eexists. Qed.
  Definition reg_mapsto := reg_mapsto_aux.(unseal).
  Definition reg_mapsto_eq : @reg_mapsto = @reg_mapsto_def := reg_mapsto_aux.(seal_eq).

  Definition mb_mapsto_def (i:VMID) (mb: MailBox) q (p: PID) : iProp Σ :=
    ghost_map_elem gen_mb_name (i,mb) (DfracOwn q) p.
  Definition mb_mapsto_aux : seal (@mb_mapsto_def). Proof. by eexists. Qed.
  Definition mb_mapsto := mb_mapsto_aux.(unseal).
  Definition mb_mapsto_eq : @mb_mapsto = @mb_mapsto_def := mb_mapsto_aux.(seal_eq).

  Definition rx_state_mapsto_def (i:VMID) (nr : option (Word * VMID)) : iProp Σ :=
    ghost_map_elem gen_rx_state_name i (DfracOwn 1) nr.
  Definition rx_state_mapsto_aux : seal (@rx_state_mapsto_def). Proof. by eexists. Qed.
  Definition rx_state_mapsto := rx_state_mapsto_aux.(unseal).
  Definition rx_state_mapsto_eq : @rx_state_mapsto = @rx_state_mapsto_def :=
    rx_state_mapsto_aux.(seal_eq).

  Definition own_mapsto_def (p: PID) (i:option VMID) : iProp Σ :=
    ghost_map_elem gen_own_name p (DfracOwn 1) i.
  Definition own_mapsto_aux : seal (@own_mapsto_def). Proof. by eexists. Qed.
  Definition own_mapsto := own_mapsto_aux.(unseal).
  Definition own_mapsto_eq : @own_mapsto = @own_mapsto_def := own_mapsto_aux.(seal_eq).

  Definition access_mapsto_def (v: VMID) (dq:frac) (s: gset PID) : iProp Σ :=
    own gen_access_name (◯ {[v:=(dq,(GSet s))]}).
  Definition access_mapsto_aux : seal (@access_mapsto_def). Proof. by eexists. Qed.
  Definition access_mapsto := access_mapsto_aux.(unseal).
  Definition access_mapsto_eq : @access_mapsto = @access_mapsto_def := access_mapsto_aux.(seal_eq).

  Definition excl_mapsto_def  (p: PID) (b:bool) : iProp Σ :=
    ghost_map_elem gen_excl_name p (DfracOwn 1) b.
  Definition excl_mapsto_aux : seal (@excl_mapsto_def). Proof. by eexists. Qed.
  Definition excl_mapsto := excl_mapsto_aux.(unseal).
  Definition excl_mapsto_eq : @excl_mapsto = @excl_mapsto_def := excl_mapsto_aux.(seal_eq).

  Definition trans_mapsto_def(wh : Word) dq ( meta :VMID * Word * VMID  * gset PID  * transaction_type) : iProp Σ :=
    wh ↪[ gen_trans_name ]{ dq } (meta: (leibnizO (VMID * Word * VMID * (gset PID) * transaction_type))).
  Definition trans_mapsto_aux : seal (@trans_mapsto_def). Proof. by eexists. Qed.
  Definition trans_mapsto := trans_mapsto_aux.(unseal).
  Definition trans_mapsto_eq : @trans_mapsto = @trans_mapsto_def := trans_mapsto_aux.(seal_eq).

  Definition retri_mapsto_def (w:Word) (b:bool) : iProp Σ :=
    w ↪[ gen_retri_name ] b.
  Definition retri_mapsto_aux : seal (@retri_mapsto_def). Proof. by eexists. Qed.
  Definition retri_mapsto := retri_mapsto_aux.(unseal).
  Definition retri_mapsto_eq : @retri_mapsto = @retri_mapsto_def := retri_mapsto_aux.(seal_eq).

  Definition hpool_mapsto_def q (s: gset Word) : iProp Σ :=
    own gen_hpool_name (frac_auth_frag q s).
  Definition hpool_mapsto_aux : seal (@hpool_mapsto_def). Proof. by eexists. Qed.
  Definition hpool_mapsto := hpool_mapsto_aux.(unseal).
  Definition hpool_mapsto_eq : @hpool_mapsto = @hpool_mapsto_def := hpool_mapsto_aux.(seal_eq).

  Definition lower_bound_frag_mapsto_def (i:VMID) (s: gset PID) : iProp Σ :=
    own (gen_lower_bound_name) (◯ {[i:= Excl s]}).
  Definition lower_bound_frag_mapsto_aux : seal (@lower_bound_frag_mapsto_def). Proof. by eexists. Qed.
  Definition lower_bound_frag_mapsto := lower_bound_frag_mapsto_aux.(unseal).
  Definition lower_bound_frag_mapsto_eq : @lower_bound_frag_mapsto = @lower_bound_frag_mapsto_def := lower_bound_frag_mapsto_aux.(seal_eq).

  Definition lower_bound_auth_mapsto_def (gm : gmap VMID (gset PID)) : iProp Σ :=
    own (gen_lower_bound_name) (● (((λ (v: (gset PID)), Excl v) <$> gm): gmap VMID (exclR (gsetR PID)))).
  Definition lower_bound_auth_mapsto_aux : seal (@lower_bound_auth_mapsto_def). Proof. by eexists. Qed.
  Definition lower_bound_auth_mapsto := lower_bound_auth_mapsto_aux.(unseal).
  Definition lower_bound_auth_mapsto_eq : @lower_bound_auth_mapsto = @lower_bound_auth_mapsto_def := lower_bound_auth_mapsto_aux.(seal_eq).

End definitions.

(* point-to predicates for registers and memory *)
Notation "r @@ i ->r{ q } w" := (reg_mapsto r i q w)
  (at level 22, q at level 50, format "r @@ i ->r{ q } w") : bi_scope.
Notation "r @@ i ->r w" :=
  (reg_mapsto r i 1 w) (at level 21, w at level 50) : bi_scope.

Notation "a ->a{ q } w" := (mem_mapsto a q w)
  (at level 20, q at level 50, format "a ->a{ q } w") : bi_scope.
Notation "a ->a w" := (mem_mapsto a 1 w) (at level 20) : bi_scope.

(* predicates for TX and RX *)
Notation "TX@ i := p" := (mb_mapsto i TX 1%Qp p)
                              (at level 20, format "TX@ i := p"): bi_scope.
Notation "RX@ i :=( n , r )" := ((rx_state_mapsto i (Some (n,r))))%I
                                        (at level 20, format "RX@ i :=( n , r )"):bi_scope.
Notation "RX@ i :=()" := ((rx_state_mapsto i None))%I
                                        (at level 20, format "RX@ i :=()"):bi_scope.
Notation "RX@ i := p " := (mb_mapsto i RX 1%Qp p)
                                        (at level 20, format "RX@ i := p"):bi_scope.

(* predicates for pagetables *)
Notation "p -@O> v" := (own_mapsto p (Some v))
                              (at level 20, format "p  -@O>  v"):bi_scope.

Notation "p -@O> -" := (own_mapsto p None)
                              (at level 20, format "p  -@O>  -"):bi_scope.

Notation "v -@{ q }A> p " := (access_mapsto v q {[p]})
                              (at level 20, format "v  -@{ q }A>  p"):bi_scope.

Notation "v -@{ q }A> [ s ] " := (access_mapsto v q s)
                              (at level 20, format "v  -@{ q }A>  [ s ]"):bi_scope.

Notation "v -@A> [ s ]" := (access_mapsto v 1%Qp s)
                              (at level 20, format "v  -@A>  [ s ]"):bi_scope.

Notation "p -@E> b" := (excl_mapsto p b)
                              (at level 20, format "p  -@E>  b"):bi_scope.

(* predicates for transactions *)
Notation "w ->t t" := (trans_mapsto w (DfracOwn 1) t)
                                                   (at level 20, format "w  ->t  t"):bi_scope.
Notation "w ->re b" := (retri_mapsto w b) (at level 20, format "w  ->re  b"):bi_scope.

(* predicates for hpool *)
Notation "'hp' [ s ]" := (hpool_mapsto 1 s) (at level 20, format "hp  [ s ]"):bi_scope.

Notation "'LB_auth' m" := (lower_bound_auth_mapsto m) (at level 20, format "'LB_auth' m"):bi_scope.

Notation "LB@ i := [ s ]" := (lower_bound_frag_mapsto i s) (at level 20, format "LB@  i  :=  [ s ]"):bi_scope.

Section alloc_rules.
  (* these rules cannot be parametrized by gen_vmG, otherwise it is not possible to prove any
   adequacy lemmas for examples. *)

  Context `{HyperConst : !HypervisorConstants}.
  Context `{HyperParams : !HypervisorParameters}.
  Context `{!gen_VMPreG Addr VMID Word reg_name PID transaction_type Σ}.

  Lemma gen_lower_bound_alloc (gm: gmap VMID (gset PID)):
   ⊢ |==> ∃ γ, own γ (● (((λ (v: (gset PID)), Excl v) <$> gm): gmap VMID (exclR (gsetR PID)))) ∗ [∗ map] k ↦ v ∈ gm, own γ (◯ {[k:= Excl v]}) .
  Proof.
    iIntros.
    set gm' := ((λ (v: (gset PID)), Excl v) <$> gm).
    iMod (own_alloc ((● gm') ⋅ (◯ gm'))) as (γ) "Halloc".
    { apply auth_both_valid;split;first done. intro.
      rewrite lookup_fmap /=.
      destruct (gm !! i) eqn:Hlookup;  last done.
      apply Some_valid.
      done.
    }
    rewrite own_op.
    iDestruct "Halloc" as "[Hauth Hfrag]".
    iExists γ.
    iSplitR "Hfrag"; first done.
    rewrite -big_opM_own_1 -big_opM_auth_frag.
    rewrite -big_opM_fmap.
    rewrite big_opM_singletons //.
  Qed.

  Context (σ : state).

  Lemma gen_reg_alloc:
   ⊢ |==> ∃ γ, ghost_map_auth γ 1%Qp (get_reg_gmap σ) ∗
               [∗ map] p↦w∈ (get_reg_gmap σ), ghost_map_elem γ p (DfracOwn 1%Qp) w.
  Proof.
    iApply (ghost_map_alloc (get_reg_gmap σ)).
  Qed.

  Lemma gen_mem_alloc:
   ⊢ |==> ∃ γ, ghost_map_auth γ 1 (get_mem σ) ∗
               [∗ map] p↦w∈((get_mem σ) : gmap Addr Word), ghost_map_elem γ p (DfracOwn 1) w.
  Proof.
    iApply (ghost_map_alloc (get_mem σ)).
  Qed.

  Lemma gen_mb_alloc:
   ⊢ |==> ∃ γ, ghost_map_auth γ 1 (get_mb_gmap σ) ∗
                [∗ map] p↦w∈ (get_mb_gmap σ), ghost_map_elem γ p (DfracOwn 1) w.
  Proof.
    iApply (ghost_map_alloc (get_mb_gmap σ)).
  Qed.

  Lemma gen_rx_state_alloc:
   ⊢ |==> ∃ γ, ghost_map_auth γ 1 (get_rx_gmap σ)∗
                              [∗ map] k ↦ v∈ (get_rx_gmap σ), ghost_map_elem γ k (DfracOwn 1) v.
  Proof.
    iApply (ghost_map_alloc (get_rx_gmap σ)).
  Qed.

  Lemma gen_own_alloc:
    ⊢ |==> ∃ γ, ghost_map_auth γ 1 (get_own_gmap σ) ∗ [∗ map] k ↦ v ∈ (get_own_gmap σ), ghost_map_elem γ k (DfracOwn 1) v.
  Proof.
    iApply (ghost_map_alloc (get_own_gmap σ)).
  Qed.

  Lemma gen_access_alloc:
   ⊢ |==> ∃ γ, own γ (● (get_access_gmap σ)) ∗ [∗ map] k ↦ v ∈ (get_access_gmap σ), own γ (◯ {[k:= v]}).
  Proof.
    iIntros.
    set gm := (get_access_gmap σ).
    iMod (own_alloc ((● gm) ⋅ (◯ gm))) as (γ) "Halloc".
    { apply auth_both_valid;split;first done. intro.
      destruct (gm !! i) eqn:Hlookup.
      rewrite Hlookup.
      rewrite /gm /get_access_gmap in Hlookup.
      apply elem_of_list_to_map_2 in Hlookup.
      rewrite elem_of_list_In in Hlookup.
      rewrite in_map_iff in Hlookup.
      destruct Hlookup as [? [Hin _]].
      inversion_clear Hin.
      apply Some_valid.
      apply pair_valid;split;done.
      rewrite Hlookup.
      done.
    }
    rewrite own_op.
    iDestruct "Halloc" as "[Hauth Hfrag]".
    iExists γ.
    iSplitR "Hfrag"; first done.
    rewrite -big_opM_own_1 -big_opM_auth_frag.
    rewrite /get_access_gmap.
    rewrite big_opM_singletons //.
  Qed.

  Lemma gen_excl_alloc:
    ⊢ |==> ∃ γ, ghost_map_auth γ 1 (get_excl_gmap σ) ∗ [∗ map] k ↦ v ∈ (get_excl_gmap σ), ghost_map_elem γ k (DfracOwn 1) v.
  Proof.
    iApply (ghost_map_alloc (get_excl_gmap σ)).
  Qed.

  Lemma gen_trans_alloc:
   ⊢ |==> ∃ γ, ghost_map_auth γ 1 (get_trans_gmap σ)∗ [∗ map] k ↦ v ∈ (get_trans_gmap σ), ghost_map_elem γ k (DfracOwn 1) v.
  Proof.
    iApply (ghost_map_alloc (get_trans_gmap σ)).
  Qed.

  Lemma gen_hpool_alloc:
   ⊢ |==> ∃ γ, own γ (frac_auth_auth (get_hpool_gset σ)) ∗ own γ (frac_auth_frag 1 (get_hpool_gset σ)).
  Proof.
    iIntros.
    set gs := (get_hpool_gset σ).
    iDestruct (own_alloc ((●F gs) ⋅ (◯F gs))) as ">Halloc".
    { apply frac_auth_valid. done. }
    iModIntro.
    iDestruct "Halloc" as (γ) "Halloc".
    iExists γ.
    rewrite own_op //.
  Qed.

  Lemma gen_retri_alloc:
   ⊢ |==> ∃ γ, ghost_map_auth γ 1 (get_retri_gmap σ)∗ [∗ map] k ↦ v ∈ (get_retri_gmap σ), ghost_map_elem γ k (DfracOwn 1) v.
  Proof.
    iApply (ghost_map_alloc (get_retri_gmap σ)).
  Qed.

End alloc_rules.

Section timeless.
  Context `{vmG : gen_VMG Σ}.
  (* all resources are timeless(▷ P -> P),
    which means we can easily get rid of the later modalities of resources when opening invariants. *)

  Global Instance mem_mapsto_timeless a q w : Timeless ((a ->a{q} w)).
  Proof. rewrite mem_mapsto_eq /mem_mapsto_def. apply _. Qed.

  Global Instance reg_mapsto_timeless r i a : Timeless ((r @@ i ->r a)).
  Proof. rewrite reg_mapsto_eq /reg_mapsto_def. apply _. Qed.
  
  Global Instance access_mapsto_timeless p q v : Timeless (p -@{ q }A> [ v ]).
  Proof. rewrite access_mapsto_eq /access_mapsto_def. apply _. Qed.

  Global Instance own_mapsto_timeless p v : Timeless (p -@O> v).
  Proof. rewrite own_mapsto_eq /own_mapsto_def. apply _. Qed.

  Global Instance own_mapsto_timeless' p : Timeless (p -@O> -).
  Proof. rewrite own_mapsto_eq /own_mapsto_def. apply _. Qed.

  Global Instance excl_mapsto_timeless p b : Timeless (p -@E> b).
  Proof. rewrite excl_mapsto_eq /excl_mapsto_def. apply _. Qed.

  Global Instance tx_mapsto_timeless i p : Timeless (TX@ i := p).
  Proof. rewrite mb_mapsto_eq /mb_mapsto_def. apply _. Qed.

  Global Instance rx_mapsto_timeless i p : Timeless (RX@ i := p).
  Proof. rewrite mb_mapsto_eq /mb_mapsto_def. apply _. Qed.

  Global Instance rx_mapsto_timeless1 i n (r:VMID) : Timeless (RX@ i :=( n , r )).
  Proof. rewrite rx_state_mapsto_eq /rx_state_mapsto_def. apply _. Qed.

  Global Instance rx_mapsto_timeless2 i : Timeless (RX@ i :=()).
  Proof. rewrite rx_state_mapsto_eq /rx_state_mapsto_def. apply _. Qed.

  Global Instance trans_mapsto_timeless w me : Timeless (w ->t me).
  Proof. rewrite trans_mapsto_eq /trans_mapsto_def. apply _. Qed.

  Global Instance hpool_mapsto_timeless sh : Timeless (hp [sh]).
  Proof. rewrite hpool_mapsto_eq /hpool_mapsto_def. apply _. Qed.

  Global Instance retri_mapsto_timeless w (b:bool) : Timeless (w ->re b).
  Proof. rewrite retri_mapsto_eq /retri_mapsto_def. apply _. Qed.

  Global Instance lower_bound_frag_mapsto_timeless (i:VMID) (s:gset PID) : Timeless (LB@ i := [s]).
  Proof. rewrite lower_bound_frag_mapsto_eq /lower_bound_frag_mapsto_def. apply _. Qed.

  Global Instance lower_bound_auth_mapsto_timeless (gm :gmap VMID (gset PID)) : Timeless (LB_auth gm).
  Proof. rewrite lower_bound_auth_mapsto_eq /lower_bound_auth_mapsto_def. apply _. Qed.

End timeless.
