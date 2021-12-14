From iris.base_logic.lib Require Export invariants na_invariants gen_heap ghost_map saved_prop.
From iris.algebra Require Export auth agree frac excl gmap gset frac_agree frac_auth.
From iris.proofmode Require Export tactics.
From HypVeri Require Import monad machine machine_extra.
From HypVeri Require Export lang.

Inductive OwnAndMB :=
| Owned 
| Rx
| Tx.

Class gen_VMPreG  (A V W R P F: Type) (Σ:gFunctors)
        `{Countable A, Countable V, Countable W, Countable R, Countable P} := {
  gen_mem_preG_inG :> gen_heapGpreS A W Σ;
  gen_reg_preG_inG :> gen_heapGpreS (R * V) W Σ;
  gen_rx_preG_inG :> gen_heapGpreS V (option (W * V)) Σ;
  gen_owned_and_mb_preG_inG :> gen_heapGpreS P (V * OwnAndMB) Σ;
  gen_access_preG_inG :> inG Σ (authUR (gmapUR P (prodR fracR (gset_disjR (leibnizO V)))));
  gen_trans_preG_inG :> gen_heapGpreS W (V * W * V * (list P) * F) Σ;
  gen_hpool_preG_inG :> inG Σ (frac_authR (gset_disjR (leibnizO W)));
  gen_retri_preG_inG :> gen_heapGpreS W bool Σ
  }.

Section gen_vmG.
  Context `{hypconst : !HypervisorConstants}.

  Class gen_VMG Σ := GenVMG{
                            gen_VM_inG :> gen_VMPreG Addr VMID Word reg_name PID transaction_type Σ;
                            gen_invG :> invGS Σ;
                            gen_na_invG :> na_invG Σ;
                            gen_nainv_name : na_inv_pool_name;
                            gen_saved_propG :> savedPropG Σ;
                            gen_prop_nameG :> inG Σ (authUR (optionUR (frac_agreeR gnameO)));
                            gen_name_mapG :> inG Σ (authUR (gmapUR nat (agreeR gnameO)));
                            gen_name_map_name: gname;
                            gen_mem_name : gname;
                            gen_reg_name : gname;
                            gen_rx_state_name : gname;
                            gen_owned_mb_name : gname;
                            gen_access_name : gname;
                            gen_trans_name : gname;
                            gen_hpool_name : gname;
                            gen_retri_name : gname
                       }.

  Global Arguments gen_nainv_name {Σ} _.
  (* Global Arguments gen_token_name {Σ} _. *)
  Global Arguments gen_mem_name {Σ} _.
  Global Arguments gen_reg_name {Σ} _.
  Global Arguments gen_rx_state_name {Σ} _.
  Global Arguments gen_owned_mb_name {Σ} _.
  Global Arguments gen_access_name {Σ} _.
  Global Arguments gen_trans_name {Σ} _.
  Global Arguments gen_hpool_name {Σ} _.
  Global Arguments gen_retri_name {Σ} _.
  Global Arguments gen_name_map_name {Σ} {_}.


  Definition gen_VMΣ : gFunctors :=
    #[
           invΣ;
           na_invΣ;
           gen_heapΣ Addr Word;
           gen_heapΣ (reg_name * VMID) Word;
           gen_heapΣ VMID (option (Word*VMID));
           gen_heapΣ PID (VMID* OwnAndMB);
           GFunctor (authUR (gmapUR PID (prodR fracR (gset_disjR (leibnizO VMID)))));
           gen_heapΣ Word (VMID * Word *  VMID * (list PID) * transaction_type);
           GFunctor (frac_authR (gset_disjR (leibnizO Word)));
           gen_heapΣ Word bool
      ].


  Global Instance subG_gen_VMPreG {Σ}:
   subG gen_VMΣ Σ -> gen_VMPreG Addr VMID Word reg_name PID transaction_type Σ.
  Proof.
    solve_inG.
  Qed.

End gen_vmG.


Section definitions.
  Context `{vmG : gen_VMG Σ}.

  Implicit Type σ: state.
 
  Notation gmap_rx := (gmap VMID (option (Word*VMID))).
  Notation gmap_own_mb:= (gmap PID (VMID * OwnAndMB)).
  Notation gmap_acc:= (gmap PID (frac * (gset_disj VMID))).

  Definition get_reg_gmap σ: gmap (reg_name * VMID) Word :=
     (list_to_map (flat_map (λ v, (map (λ p, ((p.1,v),p.2)) (map_to_list (get_reg_file σ @ v)))) (list_of_vmids))).

  Definition get_rx_gmap σ : gmap VMID _ :=
            ((list_to_map (map (λ v, let mb := (get_mail_box σ @ v) in
                                    match mb.2.2 with
                                      | Some (l, j) => (v, (Some ( l, j)))
                                      | None => (v,None)
                                    end) (list_of_vmids)))).

  Definition get_owned_gmap σ : gmap_own_mb  :=
    let pt := (get_page_table σ) in 
    let own :=(map_to_list ((λ (p: (VMID * _)), (p.1, Owned)) <$> pt)) in
    list_to_map own.

  Definition get_mb_gmap σ : gmap_own_mb:=
    (* let pt := (get_page_table σ) in *)
    list_to_map (flat_map (λ v, let mb := (get_mail_box σ @ v) in
                        (* match (bool_decide (pt !! (mb.1) = Some (∅,{[v]})), bool_decide (pt !! (mb.2.1) = Some (∅,{[v]}))) with *)
                        (* | (true,  true) => *)
                            [(mb.1, (v,Tx));(mb.2.1, (v,Rx))]
                        (* | _ => [] *)
                        (* end *)
                          ) (list_of_vmids)).

  Definition get_access_gmap σ : gmap_acc :=
    let pt := (get_page_table σ) in
    ((λ (v: ( _ * gset VMID)), (1%Qp,(GSet v.2))) <$> pt).

  (* TODO we need getters for transations.. *)

  Definition get_transactions_gmap{Info: Type} σ (proj : transaction -> Info):
   gmap Word Info :=
    list_to_map (map (λ (p:Word * transaction) ,
                         (p.1, (proj p.2)))  (map_to_list (get_transactions σ).1)).

  Definition get_trans_gmap σ :=
    get_transactions_gmap σ (λ tran, (tran.1.1.1.1.1, tran.1.1.1.1.2, tran.1.1.2, tran.1.2, tran.2)).

  Definition get_hpool_gset σ := (get_transactions σ).2.

  Definition get_retri_gmap σ := get_transactions_gmap σ (λ tran, tran.1.1.1.2).

  Definition gen_vm_interp n σ: iProp Σ :=
      ⌜n = vm_count ⌝ ∗
      ghost_map_auth (gen_mem_name vmG) 1 (get_mem σ) ∗
      ghost_map_auth (gen_reg_name vmG) 1 (get_reg_gmap σ) ∗
      ghost_map_auth (gen_rx_state_name vmG) 1 (get_rx_gmap σ) ∗
      ghost_map_auth (gen_owned_mb_name vmG) 1 (get_owned_gmap σ) ∗
      ghost_map_auth (gen_owned_mb_name vmG) 1 (get_mb_gmap σ) ∗
      own (gen_access_name vmG) (● (get_access_gmap σ)) ∗
      ghost_map_auth (gen_trans_name vmG) 1 (get_trans_gmap σ) ∗
      own (gen_hpool_name vmG) (frac_auth_auth (GSet (get_hpool_gset σ))) ∗
      ⌜ (dom (gset Word) (get_transactions σ).1) ## ((get_transactions σ).2) ⌝ ∗
      ⌜ map_Forall (λ _ v, (Z.of_nat (length v.1.2) <? word_size)%Z = true) (get_transactions σ).1 ⌝ ∗
      ghost_map_auth (gen_retri_name vmG) 1 (get_retri_gmap σ).

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

  Definition rx_state_mapsto_def (i:VMID) (nr : option (Word *  VMID)) : iProp Σ :=
    ghost_map_elem (gen_rx_state_name vmG) i (DfracOwn 1) nr.
  Definition rx_state_mapsto_aux : seal (@rx_state_mapsto_def). Proof. by eexists. Qed.
  Definition rx_state_mapsto := rx_state_mapsto_aux.(unseal).
  Definition rx_state_mapsto_eq : @rx_state_mapsto = @rx_state_mapsto_def :=
    rx_state_mapsto_aux.(seal_eq).

  Definition owned_mb_mapsto_def (i:VMID) (p: PID) (om:OwnAndMB) : iProp Σ :=
    ghost_map_elem (gen_owned_mb_name vmG) p (DfracOwn 1) (i,om).
  Definition owned_mb_mapsto_aux : seal (@owned_mb_mapsto_def). Proof. by eexists. Qed.
  Definition owned_mb_mapsto := owned_mb_mapsto_aux.(unseal).
  Definition owned_mb_mapsto_eq : @owned_mb_mapsto = @owned_mb_mapsto_def := owned_mb_mapsto_aux.(seal_eq).

  Definition access_mapsto_def (p: PID) (dq:frac) (s: gset VMID) : iProp Σ :=
    own (gen_access_name vmG) (◯ {[p:=(dq,(GSet s))]}).
  Definition access_mapsto_aux : seal (@access_mapsto_def). Proof. by eexists. Qed.
  Definition access_mapsto := access_mapsto_aux.(unseal).
  Definition access_mapsto_eq : @access_mapsto = @access_mapsto_def := access_mapsto_aux.(seal_eq).

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

  Definition hpool_mapsto_def q (s: gset Word) : iProp Σ :=
    own (gen_hpool_name vmG) (frac_auth_frag q (GSet s)).
  Definition hpool_mapsto_aux : seal (@hpool_mapsto_def). Proof. by eexists. Qed.
  Definition hpool_mapsto := hpool_mapsto_aux.(unseal).
  Definition hpool_mapsto_eq : @hpool_mapsto = @hpool_mapsto_def := hpool_mapsto_aux.(seal_eq).

  Definition nainv_closed E := na_own (gen_nainv_name vmG) E.

  Definition nainv γ P := na_inv (gen_nainv_name vmG) γ P.

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
Notation "TX@ i := p" := (owned_mb_mapsto i p Tx)
                              (at level 20, format "TX@ i := p"): bi_scope.
Notation "RX@ i :=( n , r )" := ((rx_state_mapsto i (Some (n,r))))%I
                                        (at level 20, format "RX@ i :=( n , r )"):bi_scope.
Notation "RX@ i :=()" := ((rx_state_mapsto i None))%I
                                        (at level 20, format "RX@ i :=()"):bi_scope.
Notation "RX@ i := p " := (owned_mb_mapsto i p Rx)
                                        (at level 20, format "RX@ i := p"):bi_scope.

(* predicates for pagetables *)
Notation "p -@O> v" := (owned_mb_mapsto v p Owned )
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
Notation "w ->t{ q }( v , x , y , m , f )" := (trans_mapsto w (DfracOwn q) v y x m f)
                                                   (at level 20, format "w  ->t{ q }( v , x , y , m , f )"):bi_scope.
Notation "w ->re b" := (retri_mapsto w b) (at level 20, format "w  ->re  b"):bi_scope.

(* predicates for hpool *)
Notation "hp{ q }[ s ]" := (hpool_mapsto q s) (at level 20, format "hp{ q }[ s ]"):bi_scope.

Section alloc_rules.
  (* these rules cannot be parametrized by gen_vmG, otherwise it is not possible to prove any
   adequacy lemmas for examples. *)

  Context `{HyperConst : !HypervisorConstants}.
  Context `{HyperParams : !HypervisorParameters}.
  Context `{!gen_VMPreG Addr VMID Word reg_name PID transaction_type Σ}.

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

  Lemma gen_rx_state_alloc (gmo: gmap VMID (option (Word * VMID))):
   ⊢ |==> ∃ γ, ghost_map_auth γ 1 gmo ∗
                              [∗ map] k ↦ v∈ gmo, ghost_map_elem γ k (DfracOwn 1) v.
  Proof.
    iIntros.
    iApply (ghost_map_alloc gmo).
  Qed.

  Lemma gen_owned_mb_alloc (gm : gmap PID (VMID* OwnAndMB)) :
    ⊢ |==> ∃ γ, ghost_map_auth γ 1 gm ∗ [∗ map] k ↦ v ∈ gm, ghost_map_elem γ k (DfracOwn 1) v.
  Proof.
    iApply (ghost_map_alloc gm).
  Qed.

  Lemma gen_access_alloc (gm : gmap PID (gset VMID)):
   ⊢ |==> ∃ γ, own γ (● (((λ (s: gset VMID), (1%Qp, (GSet s))) <$> gm) :(gmap PID (frac * (gset_disj VMID))) )) ∗ [∗ map] k ↦ v ∈ gm, own γ (◯ {[k:= (1%Qp, (GSet v))]}).
  Proof.
    iIntros.
    iMod (own_alloc ((● (((λ s, (1%Qp, (GSet s))) <$> gm) :(gmap PID (frac * (gset_disj VMID))) )) ⋅ (◯ (((λ s, (1%Qp, (GSet s))) <$> gm) :(gmap PID (frac * (gset_disj VMID))) )))) as (γ) "Halloc".
    { apply auth_both_valid;split;first done. intro. 
    rewrite lookup_fmap.
    destruct (gm !! i); simpl;last done.
    apply Some_valid.
    apply pair_valid;split;done.
    }
    rewrite own_op.
    iDestruct "Halloc" as "[Hauth Hfrag]".
    iExists γ.
    iSplitR "Hfrag"; first done.
    rewrite -big_opM_own_1 -big_opM_auth_frag. 
    rewrite -(big_opM_fmap (λ s : gset VMID, (1%Qp, GSet s)) (λ k v, {[k := v]})).
    rewrite big_opM_singletons //.
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
  Context `{HyperConst : !HypervisorConstants}.
  Context `{HyperParams : !HypervisorParameters}.
  Context `{vmG : !gen_VMG Σ}.

  Lemma nainv_alloc γ E P :  ▷ P ={E}=∗ na_inv (gen_nainv_name vmG) γ P.
  Proof.
    iIntros "P".
    iMod ((na_inv_alloc (gen_nainv_name vmG) E γ P) with "P") as "H".
    done.
  Qed.

  (* all resources are timeless(▷ P -> P),
    which means we can easily get rid of the later modalities of resources when opening invariants. *)

  Global Instance mem_mapsto_timeless a q w : Timeless ((a ->a{q} w)).
  Proof. rewrite mem_mapsto_eq /mem_mapsto_def. apply _. Qed.

  Global Instance reg_mapsto_timeless r i a : Timeless ((r @@ i ->r a)).
  Proof. rewrite reg_mapsto_eq /reg_mapsto_def. apply _. Qed.
  
  Global Instance access_mapsto_timeless p q v : Timeless (p -@{ q }A> [ v ]).
  Proof. rewrite access_mapsto_eq /access_mapsto_def. apply _. Qed.

  Global Instance owned_mapsto_timeless p v : Timeless (p -@O> v).
  Proof. rewrite owned_mb_mapsto_eq /owned_mb_mapsto_def. apply _. Qed.

  Global Instance tx_mapsto_timeless i p : Timeless (TX@ i := p).
  Proof. rewrite owned_mb_mapsto_eq /owned_mb_mapsto_def. apply _. Qed.

  Global Instance rx_mapsto_timeless i p : Timeless (RX@ i := p).
  Proof. rewrite owned_mb_mapsto_eq /owned_mb_mapsto_def. apply _. Qed.

  Global Instance rx_mapsto_timeless1 i n (r:VMID) : Timeless (RX@ i :=( n , r )).
  Proof. rewrite rx_state_mapsto_eq /rx_state_mapsto_def. apply _. Qed.

  Global Instance rx_mapsto_timeless2 i : Timeless (RX@ i :=()).
  Proof. rewrite rx_state_mapsto_eq /rx_state_mapsto_def. apply _. Qed.

  Global Instance trans_mapsto_timeless w q v x y m f : Timeless (w ->t{ q }( v , x , y , m , f )).
  Proof. rewrite trans_mapsto_eq /trans_mapsto_def. apply _. Qed.

  Global Instance hpool_mapsto_timeless q sh : Timeless (hp{ q }[ sh ]).
  Proof. rewrite hpool_mapsto_eq /hpool_mapsto_def. apply _. Qed.

  Global Instance retri_mapsto_timeless w (b:bool) : Timeless (w ->re b).
  Proof. rewrite retri_mapsto_eq /retri_mapsto_def. apply _. Qed.

End other_rules.
