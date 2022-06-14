From iris.base_logic.lib Require Export invariants na_invariants gen_heap ghost_map saved_prop.
From iris.algebra Require Export auth agree frac excl gmap gset.
From iris.algebra.lib Require Export dfrac_agree frac_auth.
From iris.proofmode Require Export tactics.
From HypVeri Require Import monad machine machine_extra.
From HypVeri Require Export lang.

Inductive MailBox :=
  RX
| TX.

Global Instance mb_eqdec :EqDecision MailBox.
Proof.
  intros x y.
  destruct x, y.
  left;done.
  right;done.
  right;done.
  left;done.
Qed.

Global Instance mb_countable : Countable MailBox.
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
  gen_mem_preG_inG :> ghost_mapG Σ A W;
  gen_reg_preG_inG :> ghost_mapG Σ (R * V) W;
  gen_rx_preG_inG :> ghost_mapG Σ V (option (W * V));
  gen_mb_preG_inG :> ghost_mapG Σ (V * MailBox) P;
  gen_own_preG_inG :> ghost_mapG Σ P (option V);
  gen_access_preG_inG :> inG Σ (authR (gmapUR V (dfrac_agreeR (gsetO P))));
  gen_excl_preG_inG :> ghost_mapG Σ P boolO;
  gen_trans_preG_inG :> ghost_mapG Σ W (option (V * V * (gset P) * F));
  gen_hpool_preG_inG :> inG Σ (frac_authR (agreeR (gsetR W)));
  gen_retri_preG_inG :> ghost_mapG Σ W (option bool)
  }.

Section gen_vmG.
  Context `{hypconst : !HypervisorConstants}.

  Class gen_VMG Σ := GenVMG{
                            gen_VM_inG :> gen_VMPreG Addr VMID Word reg_name PID transaction_type Σ;
                            gen_invG :> invGS Σ;
                            gen_saved_propG :> savedPropG Σ;
                            gen_prop_nameG :> inG Σ (authUR (optionUR (dfrac_agreeR gnameO)));
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
                            gen_retri_name : gname
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

  Definition gen_VMΣ : gFunctors :=
    #[
           invΣ;
           na_invΣ;
           ghost_mapΣ Addr Word;
           ghost_mapΣ (reg_name * VMID) Word;
           ghost_mapΣ VMID (option (Word*VMID));
           ghost_mapΣ PID (option VMID);
           ghost_mapΣ (VMID* MailBox) PID;
           GFunctor (authUR (gmapUR VMID (dfrac_agreeR (gsetO PID))));
           ghost_mapΣ PID boolO;
           ghost_mapΣ Word (option (VMID * VMID * (gset PID) * transaction_type));
           GFunctor (frac_authR (agreeR (gsetR Word)));
           ghost_mapΣ Word (option bool)
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
     (list_to_map (flat_map (λ (v:VMID), (map (λ p, ((p.1,v),p.2)) (map_to_list (get_reg_file σ @ v)))) (list_of_vmids))).

  Definition get_rx_gmap σ : gmap VMID (option (Word*VMID)) :=
            ((list_to_map (map (λ (v:VMID), let mb := (get_mail_box σ @ v) in
                                    match mb.2.2 with
                                      | Some (l, j) => (v, (Some (l, j)))
                                      | None => (v,None)
                                    end) (list_of_vmids)))).

  Definition get_mb_gmap σ : gmap (VMID * MailBox) PID :=
    list_to_map (flat_map (λ (v:VMID), let mb := (get_mail_box σ @ v) in
                            [((v,TX), mb.1);((v,RX), mb.2.1)]
                          ) (list_of_vmids)).

  Definition get_own_gmap σ : gmap PID (option VMID):=
    let pt := (get_page_table σ) in
    ((λ (p: (option VMID * _ * _)), p.1.1) <$> pt).

  Definition get_access_gmap σ : gmap VMID (dfrac_agreeR (gsetO PID)):=
    let pt := (get_page_table σ) in
    list_to_map (map (λ i, (i,(to_frac_agree 1 (dom (filter
                                          (λ (kv: PID * gset VMID), i ∈ kv.2) ((λ (p: ( _ * gset VMID)), p.2) <$> pt)))))) (list_of_vmids)).

  Definition get_excl_gmap σ : gmap PID bool:=
    let pt := (get_page_table σ) in
    ((λ (p: (_ * bool * gset _)), p.1.2 && bool_decide (size p.2 <= 1)) <$> pt).

  Definition get_transactions_gmap{Info: Type} σ (proj : transaction -> Info):
   gmap Word (option Info) :=
    (λ (tran: option transaction) ,
                           match tran with
                           | Some tran => Some (proj tran)
                           | None => None
                           end
                           ) <$> ((get_transactions σ):gmap Word (option transaction)).

  Definition get_trans_gmap σ := get_transactions_gmap σ (λ tran, tran.1).

  Definition get_hpool_gset σ := (get_fresh_handles (get_transactions σ)).

  Definition get_retri_gmap σ := get_transactions_gmap σ (λ tran, tran.2).

  Definition inv_trans_pg_num_ub (trans: gmap Word (option transaction)) :=
    map_Forall (λ _ v,
                 match v with
                 |Some tran =>
                 (Z.of_nat ((size tran.1.1.2) + 4) <=? page_size)%Z = true
                 |None => True
               end) trans.

  Definition inv_trans_sndr_rcvr_neq (trans: gmap Word (option transaction)) :=
    map_Forall (λ h otran, match otran with
                           |Some tran => tran.1.1.1.1 ≠ tran.1.1.1.2
                           |None => True
                           end) trans.

  Definition inv_finite_handles (trans: gmap Word (option transaction)) :=
   valid_handles = dom trans.

  Definition valid_transaction (tran: VMID * VMID  * gset PID  * transaction_type):= tran.1.1.1 ≠ tran.1.1.2.

  Definition inv_trans_wellformed' (trans : gmap Word (option transaction)) :=
    inv_trans_pg_num_ub trans ∧ inv_trans_sndr_rcvr_neq trans ∧ inv_finite_handles trans.

  Definition inv_trans_wellformed σ := inv_trans_wellformed' (get_transactions σ).

  Definition pages_in_trans' (trans: gmap Word (option transaction)) : gset PID :=
    map_fold (λ (k:Addr) v acc, match v with
                                  Some v => v.1.1.2 ∪ acc
                                | None => acc
             end) (∅: gset PID) trans.

  Definition inv_trans_ps_disj' (trans : gmap Word (option transaction))  := map_Forall (λ h tran, match tran with
                                                             Some tran => tran.1.1.2 ## pages_in_trans' (delete h trans)
                                                           | None => True
                                                end) trans.

  Definition inv_trans_ps_disj σ:= inv_trans_ps_disj' (get_transactions σ).

  Definition inv_trans_pgt_consistent' (trans: gmap Word (option transaction)) (pgt: gmap PID permission) :=
    map_Forall
           (λ (k:Word) otran,
             match otran with
             | Some tran =>
                 let sender := tran.1.1.1.1 in
                 let receiver := tran.1.1.1.2 in
                 ∀ p, p ∈ tran.1.1.2 ->
                      match tran.1.2(* type *), tran.2(*retrieved*) with
                      | Sharing, false =>  pgt !! p = Some (Some sender, false, {[sender]})
                      | Sharing, true =>  pgt !! p = Some (Some sender, false, {[sender;receiver]})
                      | Donation, false | Lending, false => pgt !! p = Some (Some sender, true, ∅)
                      | Lending, true=>  pgt !! p = Some (Some sender, true , {[receiver]})
                      | Donation, true => False
                      end
           |None => True
            end
    ) trans.

  Definition inv_trans_pgt_consistent σ := inv_trans_pgt_consistent' (get_transactions σ) (get_page_table σ).


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
      ∗ own gen_hpool_name (frac_auth_auth (to_agree (get_hpool_gset σ)))
      ∗ ghost_map_auth gen_retri_name 1 (get_retri_gmap σ)
      ∗ ⌜inv_trans_wellformed σ⌝
      ∗ ⌜inv_trans_ps_disj σ⌝
      ∗ ⌜inv_trans_pgt_consistent σ⌝
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

  Definition mb_mapsto_def (i:VMID) (mb: MailBox) (p: PID) : iProp Σ :=
    ghost_map_elem gen_mb_name (i,mb) (DfracDiscarded) p.
  Definition mb_mapsto_aux : seal (@mb_mapsto_def). Proof. by eexists. Qed.
  Definition mb_mapsto := mb_mapsto_aux.(unseal).
  Definition mb_mapsto_eq : @mb_mapsto = @mb_mapsto_def := mb_mapsto_aux.(seal_eq).

  Definition rx_state_mapsto_def (i:VMID) (q: frac) (nr : option (Word * VMID)) : iProp Σ :=
    ghost_map_elem gen_rx_state_name i (DfracOwn q) nr.
  Definition rx_state_mapsto_aux : seal (@rx_state_mapsto_def). Proof. by eexists. Qed.
  Definition rx_state_mapsto := rx_state_mapsto_aux.(unseal).
  Definition rx_state_mapsto_eq : @rx_state_mapsto = @rx_state_mapsto_def :=
    rx_state_mapsto_aux.(seal_eq).

  Definition own_mapsto_def (p: PID) q (i:option VMID) : iProp Σ :=
    ghost_map_elem gen_own_name p (DfracOwn q) i.
  Definition own_mapsto_aux : seal (@own_mapsto_def). Proof. by eexists. Qed.
  Definition own_mapsto := own_mapsto_aux.(unseal).
  Definition own_mapsto_eq : @own_mapsto = @own_mapsto_def := own_mapsto_aux.(seal_eq).

  Definition access_mapsto_def (v: VMID) (dq:frac) (s: gset PID) : iProp Σ :=
    own gen_access_name (◯ {[v:=(to_frac_agree dq s)]}).
  Definition access_mapsto_aux : seal (@access_mapsto_def). Proof. by eexists. Qed.
  Definition access_mapsto := access_mapsto_aux.(unseal).
  Definition access_mapsto_eq : @access_mapsto = @access_mapsto_def := access_mapsto_aux.(seal_eq).

  Definition excl_mapsto_def  (p: PID) q (b:bool) : iProp Σ :=
    ghost_map_elem gen_excl_name p (DfracOwn q) b.
  Definition excl_mapsto_aux : seal (@excl_mapsto_def). Proof. by eexists. Qed.
  Definition excl_mapsto := excl_mapsto_aux.(unseal).
  Definition excl_mapsto_eq : @excl_mapsto = @excl_mapsto_def := excl_mapsto_aux.(seal_eq).

  Definition trans_mapsto_def(wh : Word) dq (meta :option (VMID * VMID  * gset PID  * transaction_type)) : iProp Σ :=
    wh ↪[ gen_trans_name ]{ dq } meta.
  Definition trans_mapsto_aux : seal (@trans_mapsto_def). Proof. by eexists. Qed.
  Definition trans_mapsto := trans_mapsto_aux.(unseal).
  Definition trans_mapsto_eq : @trans_mapsto = @trans_mapsto_def := trans_mapsto_aux.(seal_eq).

  Definition hpool_mapsto_def q (s: gset Word) : iProp Σ :=
     own gen_hpool_name (frac_auth_frag q (to_agree s)).
  Definition hpool_mapsto_aux : seal (@hpool_mapsto_def). Proof. by eexists. Qed.
  Definition hpool_mapsto := hpool_mapsto_aux.(unseal).
  Definition hpool_mapsto_eq : @hpool_mapsto = @hpool_mapsto_def := hpool_mapsto_aux.(seal_eq).

  Definition retri_mapsto_def (w:Word) dq (b: option bool) : iProp Σ :=
    w ↪[ gen_retri_name ]{dq} b.
  Definition retri_mapsto_aux : seal (@retri_mapsto_def). Proof. by eexists. Qed.
  Definition retri_mapsto := retri_mapsto_aux.(unseal).
  Definition retri_mapsto_eq : @retri_mapsto = @retri_mapsto_def := retri_mapsto_aux.(seal_eq).

End definitions.

(* point-to predicates for registers and memory *)
Notation "r @@ i -{ q }>r w" := (reg_mapsto r i q w)
  (at level 22, q at level 50, format "r @@ i -{ q }>r w") : bi_scope.
Notation "r @@ i ->r w" :=
  (reg_mapsto r i 1 w) (at level 21, w at level 50) : bi_scope.

Notation "a ->a w" := (mem_mapsto a 1 w) (at level 20) : bi_scope.

(* predicates for TX and RX *)
Notation "TX@ i := p" := (mb_mapsto i TX p)
                              (at level 20, format "TX@ i := p"): bi_scope.

Notation "RX_state{ q }@ i := o" := ((rx_state_mapsto i q o) ∗ ⌜((λ (oo: option (Word*VMID)), match oo with
                                      | None => True
                                      | Some s => s.2 ≠ i
                                      end) o)⌝)%I
                                        (at level 20, format "RX_state{ q }@ i :=  o"):bi_scope.
Notation "RX_state@ i := o" := (RX_state{1}@i := o)%I
                                        (at level 20, format "RX_state@ i :=  o"):bi_scope.
Notation "RX@ i := p " := (mb_mapsto i RX p)
                                        (at level 20, format "RX@ i := p"):bi_scope.

(* predicates for pagetables *)
Notation "p -@{ q }O> v" := (own_mapsto p q (Some v)) (at level 20, format "p  -@{ q }O>  v"):bi_scope.
Notation "p -@O> v" := (p -@{ 1 }O> v)%I (at level 20, format "p  -@O>  v"):bi_scope.
Notation "p -@O> -" := (own_mapsto p 1 None) (at level 20, format "p  -@O>  -"):bi_scope.

Notation "v -@{ q }A> s" := (access_mapsto v q s) (at level 20, format "v  -@{ q }A>  s"):bi_scope.
Notation "v -@A> s" := (v -@{ 1 }A> s)%I (at level 20, format "v  -@A>  s"):bi_scope.

Notation "p -@{ q }E> b" := (excl_mapsto p q b) (at level 20, format "p  -@{ q }E>  b"):bi_scope.
Notation "p -@E> b" := (p -@{ 1 }E> b)%I (at level 20, format "p  -@E>  b"):bi_scope.

(* predicates for transactions *)
Notation "w -{ q }>t t" := ((trans_mapsto w (DfracOwn q) (Some t)) ∗ ⌜w ∈ valid_handles ∧ valid_transaction t⌝)%I (at level 20, format "w  -{ q }>t  t"):bi_scope.
Notation "w -{ q }>t -" := ((trans_mapsto w (DfracOwn q) None) ∗ ⌜w ∈ valid_handles ⌝)%I (at level 20, format "w  -{ q }>t  -"):bi_scope.
Notation "w ->t t" := (w -{ 1 }>t t)%I (at level 20, format "w  ->t  t"):bi_scope.
Notation "w ->t -" := (w -{ 1 }>t -)%I (at level 20, format "w  ->t  -"):bi_scope.

Notation "w -{ q }>re b" := ((retri_mapsto w (DfracOwn q) (Some b)) ∗ ⌜w ∈ valid_handles⌝)%I (at level 20, format "w  -{ q }>re  b"):bi_scope.
Notation "w -{ q }>re -" := ((retri_mapsto w (DfracOwn q) None) ∗ ⌜w ∈ valid_handles⌝)%I (at level 20, format "w  -{ q }>re  -"):bi_scope.
Notation "w ->re b" := (w -{ 1 }>re b)%I (at level 20, format "w  ->re  b"):bi_scope.
Notation "w ->re -" := (w -{ 1 }>re -)%I (at level 20, format "w  ->re  -"):bi_scope.

(* predicates for hpool *)

Notation "'hp' { q }[ s ]" := (hpool_mapsto q s)  (at level 20, format "hp  { q }[ s ]"):bi_scope.
Notation "'hp' [ s ]" := ( hp {1}[s] )%I (at level 20, format "hp  [ s ]"):bi_scope.

Section alloc_rules.
  (* these rules cannot be parametrized by gen_vmG, otherwise it is not possible to prove any
   adequacy lemmas for examples. *)

  Context `{HyperConst : !HypervisorConstants}.
  Context `{HyperParams : !HypervisorParameters}.
  Context `{!gen_VMPreG Addr VMID Word reg_name PID transaction_type Σ}.
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
      rewrite /gm /get_access_gmap in Hlookup.
      apply elem_of_list_to_map_2 in Hlookup.
      rewrite elem_of_list_In in Hlookup.
      rewrite in_map_iff in Hlookup.
      destruct Hlookup as [? [Hin _]].
      inversion_clear Hin.
      apply Some_valid.
      apply pair_valid;split;done.
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
    ⊢ |==> ∃ γ, own γ (frac_auth_auth (to_agree (get_hpool_gset σ))) ∗ own γ (frac_auth_frag 1 (to_agree (get_hpool_gset σ))).
  Proof.
    iIntros.
    set gs := (get_hpool_gset σ).
    iDestruct (own_alloc ((●F (to_agree gs)) ⋅ (◯F (to_agree gs)))) as ">Halloc".
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
    which means we can easily eliminate the later modalities before these resrouces. *)

  Global Instance mem_mapsto_timeless a w : Timeless ((a ->a w)).
  Proof. rewrite mem_mapsto_eq /mem_mapsto_def. apply _. Qed.

  Global Instance reg_mapsto_timeless r i a : Timeless ((r @@ i ->r a)).
  Proof. rewrite reg_mapsto_eq /reg_mapsto_def. apply _. Qed.
  
  Global Instance access_mapsto_timeless p q v : Timeless (p -@{q}A> v).
  Proof. rewrite access_mapsto_eq /access_mapsto_def. apply _. Qed.

  Global Instance own_mapsto_timeless_Some p q v : Timeless (p -@{q}O> v).
  Proof. rewrite own_mapsto_eq /own_mapsto_def. apply _. Qed.

  Global Instance own_mapsto_timeless_None p : Timeless (p -@O> -).
  Proof. rewrite own_mapsto_eq /own_mapsto_def. apply _. Qed.

  Global Instance excl_mapsto_timeless p q b : Timeless (p -@{q}E> b).
  Proof. rewrite excl_mapsto_eq /excl_mapsto_def. apply _. Qed.

  Global Instance tx_mapsto_timeless i p : Timeless (TX@ i := p).
  Proof. rewrite mb_mapsto_eq /mb_mapsto_def. apply _. Qed.

  Global Instance tx_mapsto_persistent i p : Persistent (TX@ i := p).
  Proof. rewrite mb_mapsto_eq /mb_mapsto_def. apply _. Qed.

  Global Instance rx_mapsto_timeless i p : Timeless (RX@ i := p).
  Proof. rewrite mb_mapsto_eq /mb_mapsto_def. apply _. Qed.

  Global Instance rx_mapsto_persistent i p : Persistent (RX@ i := p).
  Proof. rewrite mb_mapsto_eq /mb_mapsto_def. apply _. Qed.

  Global Instance rx_state_mapsto_timeless i q o : Timeless (RX_state{q}@ i := o).
  Proof. rewrite rx_state_mapsto_eq /rx_state_mapsto_def. apply _. Qed.

  Global Instance trans_mapsto_timeless_Some w q me : Timeless (w -{q}>t me).
  Proof. rewrite trans_mapsto_eq /trans_mapsto_def. apply _. Qed.

  Global Instance trans_mapsto_timeless_None w q : Timeless (w -{q}>t -).
  Proof. rewrite trans_mapsto_eq /trans_mapsto_def. apply _. Qed.

  Global Instance hpool_mapsto_timeless q sh : Timeless (hp {q}[sh]).
  Proof. rewrite hpool_mapsto_eq /hpool_mapsto_def. apply _. Qed.

  Global Instance retri_mapsto_timeless_Some w q (b:bool) : Timeless (w -{q}>re b).
  Proof. rewrite retri_mapsto_eq /retri_mapsto_def. apply _. Qed.

  Global Instance retri_mapsto_timeless_None w q : Timeless (w -{q}>re -).
  Proof. rewrite retri_mapsto_eq /retri_mapsto_def. apply _. Qed.
End timeless.

From machine_program_logic.program_logic Require Import weakestpre.
From HypVeri Require Export lifting.

Global Instance hyp_irisG `{HypervisorParameters} `{!gen_VMG Σ} :
  irisG hyp_machine Σ:=
  {
  iris_invG := gen_invG;
  irisG_saved_prop := gen_saved_propG;
  irisG_prop_name := gen_prop_nameG;
  irisG_name_map := gen_name_mapG;
  irisG_name_map_name := gen_name_map_name;
  state_interp :=gen_vm_interp
  }.
