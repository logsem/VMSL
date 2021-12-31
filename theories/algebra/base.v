From iris.base_logic.lib Require Export invariants na_invariants gen_heap ghost_map saved_prop.
From iris.algebra Require Export auth agree frac excl gmap gset frac_agree frac_auth.
From iris.proofmode Require Export tactics.
From HypVeri Require Import monad machine machine_extra.
From HypVeri Require Export lang.

Inductive MailBox :=
  RX
| TX.

Class gen_VMPreG  (A V W R P F: Type) (Σ:gFunctors)
        `{Countable A, Countable V, Countable W, Countable R, Countable P} := {
  gen_mem_preG_inG :> gen_heapGpreS A W Σ;
  gen_reg_preG_inG :> gen_heapGpreS (R * V) W Σ;
  gen_rx_preG_inG :> gen_heapGpreS V (option (W * V)) Σ;
  gen_owned_preG_inG :> gen_heapGpreS P V Σ;
  gen_mb_preG_inG :> gen_heapGpreS P (V * MailBox) Σ;
  gen_access_preG_inG :> inG Σ (authR (gmapUR P (prodR fracR (gset_disjR (leibnizO V)))));
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
                            (* gen_na_invG :> na_invG Σ; *)
                            (* gen_nainv_name : na_inv_pool_name; *)
                            gen_saved_propG :> savedPropG Σ;
                            gen_prop_nameG :> inG Σ (authUR (optionUR (frac_agreeR gnameO)));
                            gen_name_mapG :> inG Σ (authUR (gmapUR nat (agreeR gnameO)));
                            gen_name_map_name: gname;
                            gen_mem_name : gname;
                            gen_reg_name : gname;
                            gen_mb_name : gname;
                            gen_rx_state_name : gname;
                            gen_owned_name : gname;
                            gen_access_name : gname;
                            gen_trans_name : gname;
                            gen_hpool_name : gname;
                            gen_retri_name : gname;
                            gen_lower_bound_name: gname
                       }.

  (* Global Arguments gen_nainv_name {Σ} _. *)
  Global Arguments gen_mem_name {Σ} _.
  Global Arguments gen_reg_name {Σ} _.
  Global Arguments gen_rx_state_name {Σ} _.
  Global Arguments gen_mb_name {Σ} _.
  Global Arguments gen_owned_name {Σ} _.
  Global Arguments gen_access_name {Σ} _.
  Global Arguments gen_trans_name {Σ} _.
  Global Arguments gen_hpool_name {Σ} _.
  Global Arguments gen_retri_name {Σ} _.
  Global Arguments gen_name_map_name {Σ} {_}.
  Global Arguments gen_lower_bound_name {Σ} {_}.


  Definition gen_VMΣ : gFunctors :=
    #[
           invΣ;
           na_invΣ;
           gen_heapΣ Addr Word;
           gen_heapΣ (reg_name * VMID) Word;
           gen_heapΣ VMID (option (Word*VMID));
           gen_heapΣ PID VMID;
           gen_heapΣ PID (VMID * MailBox);
           GFunctor (authUR (gmapUR PID (prodR fracR (gset_disjR (leibnizO VMID)))));
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

  Definition get_mb_gmap σ : gmap PID (VMID * MailBox) :=
    (* let pt := (get_page_table σ) in *)
    list_to_map (flat_map (λ v, let mb := (get_mail_box σ @ v) in
                            [(mb.1, (v,TX));(mb.2.1, (v,RX))]
                          ) (list_of_vmids)).

  Definition get_owned_gmap σ : gmap PID VMID:=
    let pt := (get_page_table σ) in
    ((λ (p: (VMID * _)), p.1) <$> pt).

  Definition get_access_gmap σ : gmap PID (frac * (gset_disj VMID)):=
    let pt := (get_page_table σ) in
    ((λ (v: ( _ * gset VMID)), (1%Qp,(GSet v.2))) <$> pt).

  Definition get_transactions_gmap{Info: Type} σ (proj : transaction -> Info):
   gmap Word Info :=
    list_to_map (map (λ (p:Word * transaction) ,
                         (p.1, (proj p.2)))  (map_to_list (get_transactions σ).1)).

  Definition get_trans_gmap σ :=
    get_transactions_gmap σ (λ tran, tran.1).

  Definition get_hpool_gset σ := (get_transactions σ).2.

  Definition get_retri_gmap σ := get_transactions_gmap σ (λ tran, tran.2).

  Definition inv_trans_hpool_disj' (trans: gmap Word transaction) (hpool: gset _) := (dom (gset Word) trans) ## hpool.

  Definition inv_trans_hpool_disj σ := inv_trans_hpool_disj' (get_transactions σ).1 (get_transactions σ).2.

  Definition inv_trans_pg_num_ub σ :=
    map_Forall (λ _ v, (Z.of_nat (size v.1.1.2) <? word_size)%Z = true) (get_transactions σ).1.

  Definition inv_finite_handles' (trans: gmap Word transaction) (hpool: gset _) :=
    list_to_set (finz.seq W0 100) = dom (gset Word) trans ∪ hpool.

  Definition inv_finite_handles σ := inv_finite_handles' (get_transactions σ).1 (get_transactions σ).2.

  Definition inv_trans_hpool_consistent' (trans: gmap Word transaction) (hpool: gset _) :=
    (inv_trans_hpool_disj' trans hpool) ∧ (inv_finite_handles' trans hpool).

  Definition inv_trans_hpool_consistent σ := inv_trans_hpool_consistent' (get_transactions σ).1 (get_transactions σ).2.

  Definition inv_trans_pgt_consistent' (trans: gmap Word transaction) (pgt: gmap PID (VMID * (gset VMID))) :=
    map_Forall
           (λ (k:Word) v,
               let sender := v.1.1.1.1.1 in
               let receiver := v.1.1.1.2 in
               ∀ p, p ∈ v.1.1.2 ->
               match v.1.2(* type *), v.2(*retrieved*) with
                 | Sharing, false =>  pgt !! p = Some (sender, {[sender]})
                 | Sharing, true =>  pgt !! p = Some (sender, {[sender;receiver]})
                 | Donation, false | Lending, false => pgt !! p = Some (sender, ∅)
                 | Lending, true=>  pgt !! p = Some (sender, {[receiver]})
                 | Donation, true => False
            end
    ) trans.

  Definition inv_trans_pgt_consistent σ := inv_trans_pgt_consistent' (get_transactions σ).1 (get_page_table σ).

  Context `{vmG: !gen_VMG Σ}.

  Definition gen_vm_interp n σ: iProp Σ :=
      ⌜n = vm_count⌝
      ∗ ghost_map_auth (gen_mem_name vmG) 1 (get_mem σ)
      ∗ ghost_map_auth (gen_reg_name vmG) 1 (get_reg_gmap σ)
      ∗ ghost_map_auth (gen_mb_name vmG) 1 (get_mb_gmap σ)
      ∗ ghost_map_auth (gen_rx_state_name vmG) 1 (get_rx_gmap σ)
      ∗ ghost_map_auth (gen_owned_name vmG) 1 (get_owned_gmap σ)
      ∗ own (gen_access_name vmG) (● (get_access_gmap σ))
      ∗ ghost_map_auth (gen_trans_name vmG) 1 (get_trans_gmap σ)
      ∗ own (gen_hpool_name vmG) (frac_auth_auth (get_hpool_gset σ))
      ∗ ghost_map_auth (gen_retri_name vmG) 1 (get_retri_gmap σ)
      ∗ ⌜inv_trans_hpool_consistent σ⌝
      ∗ ⌜inv_trans_pg_num_ub σ⌝
      ∗ ⌜inv_trans_pgt_consistent σ⌝
  .

  Definition mem_mapsto_def (a:Addr) (q : frac) (w:Word) : iProp Σ :=
    (ghost_map_elem (gen_mem_name vmG) a (DfracOwn q) w).
  Definition mem_mapsto_aux : seal (@mem_mapsto_def). Proof. by eexists. Qed.
  Definition mem_mapsto := mem_mapsto_aux.(unseal).
  Definition mem_mapsto_eq : @mem_mapsto = @mem_mapsto_def := mem_mapsto_aux.(seal_eq).

  Definition reg_mapsto_def (r:reg_name) (i:VMID) (q : frac) (w:Word) : iProp Σ :=
    (ghost_map_elem (gen_reg_name vmG) (r,i) (DfracOwn q) w).
  Definition reg_mapsto_aux : seal (@reg_mapsto_def). Proof. by eexists. Qed.
  Definition reg_mapsto := reg_mapsto_aux.(unseal).
  Definition reg_mapsto_eq : @reg_mapsto = @reg_mapsto_def := reg_mapsto_aux.(seal_eq).

  Definition mb_mapsto_def (i:VMID) (p: PID) (mb: MailBox) : iProp Σ :=
    ghost_map_elem (gen_mb_name vmG) p (DfracOwn 1) (i, mb).
  Definition mb_mapsto_aux : seal (@mb_mapsto_def). Proof. by eexists. Qed.
  Definition mb_mapsto := mb_mapsto_aux.(unseal).
  Definition mb_mapsto_eq : @mb_mapsto = @mb_mapsto_def := mb_mapsto_aux.(seal_eq).

  Definition rx_state_mapsto_def (i:VMID) (nr : option (Word *  VMID)) : iProp Σ :=
    ghost_map_elem (gen_rx_state_name vmG) i (DfracOwn 1) nr.
  Definition rx_state_mapsto_aux : seal (@rx_state_mapsto_def). Proof. by eexists. Qed.
  Definition rx_state_mapsto := rx_state_mapsto_aux.(unseal).
  Definition rx_state_mapsto_eq : @rx_state_mapsto = @rx_state_mapsto_def :=
    rx_state_mapsto_aux.(seal_eq).

  Definition owned_mapsto_def (i:VMID) (p: PID) : iProp Σ :=
    ghost_map_elem (gen_owned_name vmG) p (DfracOwn 1) i.
  Definition owned_mapsto_aux : seal (@owned_mapsto_def). Proof. by eexists. Qed.
  Definition owned_mapsto := owned_mapsto_aux.(unseal).
  Definition owned_mapsto_eq : @owned_mapsto = @owned_mapsto_def := owned_mapsto_aux.(seal_eq).

  Definition access_mapsto_def (p: PID) (dq:frac) (s: gset VMID) : iProp Σ :=
    own (gen_access_name vmG) (◯ {[p:=(dq,(GSet s))]}).
  Definition access_mapsto_aux : seal (@access_mapsto_def). Proof. by eexists. Qed.
  Definition access_mapsto := access_mapsto_aux.(unseal).
  Definition access_mapsto_eq : @access_mapsto = @access_mapsto_def := access_mapsto_aux.(seal_eq).

  Definition trans_mapsto_def(wh : Word) dq ( meta :VMID * Word * VMID  * gset PID  * transaction_type) : iProp Σ :=
    wh ↪[ (gen_trans_name vmG) ]{ dq } (meta: (leibnizO (VMID * Word * VMID * (gset PID) * transaction_type))).
  Definition trans_mapsto_aux : seal (@trans_mapsto_def). Proof. by eexists. Qed.
  Definition trans_mapsto := trans_mapsto_aux.(unseal).
  Definition trans_mapsto_eq : @trans_mapsto = @trans_mapsto_def := trans_mapsto_aux.(seal_eq).

  Definition retri_mapsto_def (w:Word) (b:bool) : iProp Σ :=
    w ↪[ (gen_retri_name vmG) ] b.
  Definition retri_mapsto_aux : seal (@retri_mapsto_def). Proof. by eexists. Qed.
  Definition retri_mapsto := retri_mapsto_aux.(unseal).
  Definition retri_mapsto_eq : @retri_mapsto = @retri_mapsto_def := retri_mapsto_aux.(seal_eq).

  Definition hpool_mapsto_def q (s: gset Word) : iProp Σ :=
    own (gen_hpool_name vmG) (frac_auth_frag q s).
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

  (* Definition nainv_closed E := na_own (gen_nainv_name vmG) E. *)

  (* Definition nainv γ P := na_inv (gen_nainv_name vmG) γ P. *)

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
Notation "TX@ i := p" := (mb_mapsto i p TX)
                              (at level 20, format "TX@ i := p"): bi_scope.
Notation "RX@ i :=( n , r )" := ((rx_state_mapsto i (Some (n,r))))%I
                                        (at level 20, format "RX@ i :=( n , r )"):bi_scope.
Notation "RX@ i :=()" := ((rx_state_mapsto i None))%I
                                        (at level 20, format "RX@ i :=()"):bi_scope.
Notation "RX@ i := p " := (mb_mapsto i p RX)
                                        (at level 20, format "RX@ i := p"):bi_scope.

(* predicates for pagetables *)
Notation "p -@O> v" := (owned_mapsto v p)
                              (at level 20, format "p  -@O>  v"):bi_scope.

Notation "p -@{ q }A> v " := (access_mapsto p q {[v]})
                              (at level 20, format "p  -@{ q }A>  v"):bi_scope.

Notation "p -@{ q }A> [ s ] " := (access_mapsto p q s)
                              (at level 20, format "p  -@{ q }A>  [ s ]"):bi_scope.

Notation "p -@A> [ s ]" := (access_mapsto p 1%Qp s)
                              (at level 20, format "p  -@A>  [ s ]"):bi_scope.

Notation "p -@A> v" := (access_mapsto p 1%Qp {[v]})
                              (at level 20, format "p  -@A>  v"):bi_scope.

Notation "p -@A> -" := (access_mapsto p 1%Qp ∅)
                              (at level 20, format "p  -@A>  -"):bi_scope.

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
   ⊢ |==> ∃ γ, ghost_map_auth γ 1 (get_mb_gmap σ)∗
                              [∗ map] k ↦ v∈ (get_mb_gmap σ), ghost_map_elem γ k (DfracOwn 1) v.
  Proof.
    iApply (ghost_map_alloc (get_mb_gmap σ)).
  Qed.

  Lemma gen_rx_state_alloc:
   ⊢ |==> ∃ γ, ghost_map_auth γ 1 (get_rx_gmap σ)∗
                              [∗ map] k ↦ v∈ (get_rx_gmap σ), ghost_map_elem γ k (DfracOwn 1) v.
  Proof.
    iApply (ghost_map_alloc (get_rx_gmap σ)).
  Qed.

  Lemma gen_owned_alloc:
    ⊢ |==> ∃ γ, ghost_map_auth γ 1 (get_owned_gmap σ) ∗ [∗ map] k ↦ v ∈ (get_owned_gmap σ), ghost_map_elem γ k (DfracOwn 1) v.
  Proof.
    iApply (ghost_map_alloc (get_owned_gmap σ)).
  Qed.

  Lemma gen_access_alloc:
   ⊢ |==> ∃ γ, own γ (● (get_access_gmap σ)) ∗ [∗ map] k ↦ v ∈ (get_access_gmap σ), own γ (◯ {[k:= v]}).
  Proof.
    iIntros.
    set gm := (get_access_gmap σ).
    rewrite /get_access_gmap.
    iMod (own_alloc ((● gm) ⋅ (◯ gm))) as (γ) "Halloc".
    { apply auth_both_valid;split;first done. intro.
      rewrite lookup_fmap /=.
      destruct (σ.1.1.1.2 !! i) eqn:Hlookup;rewrite Hlookup;last done.
      apply Some_valid.
      apply pair_valid;split;done.
    }
    rewrite own_op.
    iDestruct "Halloc" as "[Hauth Hfrag]".
    iExists γ.
    iSplitR "Hfrag"; first done.
    rewrite -big_opM_own_1 -big_opM_auth_frag.
    rewrite /get_access_gmap.
    rewrite big_opM_singletons //.
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

  (* Lemma nainv_alloc γ E P :  ▷ P ={E}=∗ na_inv (gen_nainv_name vmG) γ P. *)
  (* Proof. *)
  (*   iIntros "P". *)
  (*   iMod ((na_inv_alloc (gen_nainv_name vmG) E γ P) with "P") as "H". *)
  (*   done. *)
  (* Qed. *)

  (* all resources are timeless(▷ P -> P),
    which means we can easily get rid of the later modalities of resources when opening invariants. *)

  Global Instance mem_mapsto_timeless a q w : Timeless ((a ->a{q} w)).
  Proof. rewrite mem_mapsto_eq /mem_mapsto_def. apply _. Qed.

  Global Instance reg_mapsto_timeless r i a : Timeless ((r @@ i ->r a)).
  Proof. rewrite reg_mapsto_eq /reg_mapsto_def. apply _. Qed.
  
  Global Instance access_mapsto_timeless p q v : Timeless (p -@{ q }A> [ v ]).
  Proof. rewrite access_mapsto_eq /access_mapsto_def. apply _. Qed.

  Global Instance owned_mapsto_timeless p v : Timeless (p -@O> v).
  Proof. rewrite owned_mapsto_eq /owned_mapsto_def. apply _. Qed.

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
