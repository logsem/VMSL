From Coq.Logic Require Import FunctionalExtensionality.
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
                      gen_mem_preG_inG :> gen_heapGpreS A W Σ;
                      gen_reg_preG_inG :> gen_heapGpreS (R * V) W Σ;
                      gen_tx_preG_inG :> inG Σ (authR (gmapUR V (agreeR (leibnizO P))));
                      gen_rx_preG_inG :> inG Σ (prodR (authR (gmapUR V (agreeR (leibnizO P))))
                                                      (optionR (gmap_viewR V (optionO (prodO natO (leibnizO V))))));
                      (* gen_owned_preG_inG :> inG Σ (authR (gset_disjUR (leibnizO P))); *)
                      (* gen_access_preG_inG :> inG Σ (authR (gmapUR P (prodR dfracR (csumR (agreeR unitO) (exclR unitO))))); *)
                      gen_owned_preG_inG :> inG Σ (authR (gmapUR V
                                    (prodR dfracR (gset_disjUR (leibnizO P)))));
                      (* gen_access_preG_inG :> inG Σ (authR (gmapUR V *)
                                    (* (prodR dfracR (gmapUR P (csumR (agreeR unitO) (exclR unitO)))))); *)
                      gen_access_preG_inG :> inG Σ (authR (gmapUR V
                                                    (prodR dfracR (gset_disjUR (leibnizO P)))));
                      gen_trans_preG_inG :> gen_heapGpreS W (V * W* W*(gmap V (listset_nodup P))*F) Σ;
                      gen_retri_preG_inG :> inG Σ (authR (gmapUR W (gset_disjR (leibnizO V))))
                   }.


  Class gen_VMG Σ := GenVMG{
                      gen_VM_inG :> gen_VMPreG addr vmid word reg_name pid transaction_type Σ;
                      gen_invG :> invGS Σ;
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
  (* (authR (gmapUR pid (prodR dfracR (csumR (agreeR unitO) (exclR unitO))))). *)
  (authR (gmapUR vmid (prodR dfracR (gset_disjUR (leibnizO pid))))).



Definition gen_VMΣ : gFunctors :=
  #[
      invΣ;
      na_invΣ;
      GFunctor (agreeR natO);
      gen_heapΣ addr word;
      gen_heapΣ (reg_name * vmid) word;
      GFunctor ra_TXBuffer;
      GFunctor ra_RXBuffer;
      GFunctor (authR (gmapUR vmid (prodR dfracR (gset_disjUR (leibnizO pid)))));
      (* GFunctor (authR (gset_disjUR (leibnizO pid))); *)
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

  Program Fixpoint list_of_vmids_aux(n:nat) (H:n<vm_count) : list vmid:=
    match n with
      | S m => (nat_to_fin H) :: (list_of_vmids_aux m _)
      | 0  => (nat_to_fin H)::nil
    end.
  Next Obligation.
    Proof.
      intros.
      lia.
    Defined.

  Program Definition list_of_vmids :list vmid:=
    list_of_vmids_aux (vm_count-1) _.
  Next Obligation.
    Proof.
      simpl.
      pose proof vm_count_pos.
      pose vm_count.
      lia.
    Defined.

    (* hard to prove lemmas for it, because of the use of foldr of vectors. *)
    (*  Definition get_reg_gmap σ: gmap (reg_name * vmid) word := *)
    (*     (foldr (λ p acc, (map_fold (λ (r:reg_name) (w:word) acc', <[(r,p.1):= w ]>acc') acc p.2)) ∅ *)
    (*               (vzip_with (λ v δ, (v,δ.1.1)) (vector_of_vmids) (get_vm_states σ))). *)


  Definition get_reg_gmap σ: gmap (reg_name * vmid) word :=
     (list_to_map (flat_map (λ v, (map (λ p, ((p.1,v),p.2)) (map_to_list (get_vm_reg_file σ v)))) (list_of_vmids))).

(* TODO: very ugly proof... to be shorten *)
  Lemma update_reg_global_update_reg σ i r w : is_Some((get_reg_gmap σ) !! (r,i)) -> get_reg_gmap (update_reg_global σ i r w) =
                                             <[(r,i) := w]>(get_reg_gmap σ).
  Proof.
    intros.
    rewrite /get_reg_gmap /update_reg_global.
    apply map_eq.
    intro j.
    destruct( decide (j=(r,i)) ).
    - subst j.
      rewrite lookup_insert.
      apply elem_of_list_to_map_1'.
      + intro.
        rewrite elem_of_list_In in_flat_map .
        intro H1.
        destruct H1.
        destruct H0.
        apply in_map_iff in H1.
        destruct H1.
        destruct H1.
        apply elem_of_list_In in H2.
        apply elem_of_map_to_list' in H2.
        inversion H1;subst;clear H1.
        rewrite /get_vm_reg_file /get_vm_state /get_vm_states in H2.
        destruct (get_vm_states σ !!! i) in H2.
        destruct p.
        simpl in H2.
        rewrite -> (vlookup_insert i _  σ.1.1.1) in H2.
        inversion H2;subst.
        rewrite lookup_insert in H2.
        by inversion H2.
      + rewrite elem_of_list_In in_flat_map .
        exists i.
        split.
        * rewrite /get_reg_gmap /is_Some in H.
          destruct H.
          apply  elem_of_list_to_map_2 in H.
          apply elem_of_list_In in H.
          apply in_flat_map in H.
          destruct H.
          destruct H.
          apply in_map_iff in H0.
          destruct H0.
          destruct H0.
          by inversion H0;subst.
        *  apply in_map_iff.
           exists (r,w).
           split;[done|].
           apply elem_of_list_In.
           apply elem_of_map_to_list'.
           rewrite /get_vm_reg_file /get_vm_state /get_vm_states.
           destruct (get_vm_states σ !!! i).
           destruct p.
           simpl.
           rewrite -> (vlookup_insert i _  σ.1.1.1).
           by rewrite lookup_insert.
    - destruct ((get_reg_gmap σ) !! j) eqn:Heqn.
      + rewrite lookup_insert_ne;[|done].
        unfold get_reg_gmap in Heqn.
        rewrite -> Heqn.
        apply  elem_of_list_to_map_1'.
        intros.
        apply elem_of_list_In in H0.
        apply in_flat_map in H0.
        destruct H0.
        destruct H0.
        apply in_map_iff in H1.
        destruct H1.
        destruct H1.
        apply elem_of_list_In in H2.
        apply elem_of_map_to_list' in H2.
        inversion H1;subst;clear H1.
        rewrite /get_vm_reg_file /get_vm_state /get_vm_states in H2.
        simpl in H2.
        destruct (decide (x=i)).
        subst x.
        destruct (decide (x0.1 =r));[ subst r; contradiction|].
        apply elem_of_list_to_map_2 in Heqn.
        apply elem_of_list_In in Heqn.
        apply in_flat_map in Heqn.
        destruct Heqn.
        destruct H1.
        apply in_map_iff in H3.
        destruct H3.
        destruct H3.
        inversion H3;subst;clear H3.
        apply elem_of_list_In in H4.
        apply elem_of_map_to_list' in H4.
        rewrite /get_vm_reg_file /get_vm_state /get_vm_states in H4.
        destruct (σ.1.1.1 !!! i).
        destruct p.
        simpl in H2.
        rewrite -> (vlookup_insert i _  σ.1.1.1) in H2.
        rewrite lookup_insert_ne in H2.
        simpl in H4.
        rewrite H6 in H4.
        rewrite H2 in H4.
        by inversion H4.
        done.
        rewrite /get_vm_reg_file /get_vm_state /get_vm_states in Heqn.
        destruct (σ.1.1.1 !!! i).
        destruct p.
        simpl in H2.
        rewrite vlookup_insert_ne in H2;[|done].
        apply elem_of_list_to_map_2 in Heqn.
        apply elem_of_list_In in Heqn.
        apply in_flat_map in Heqn.
        destruct Heqn.
        destruct H1.
        apply in_map_iff in H3.
        destruct H3.
        destruct H3.
        inversion H3;subst;clear H3.
        apply elem_of_list_In in H4.
        apply elem_of_map_to_list' in H4.
        rewrite H6 in H4.
        rewrite H2 in H4.
        by inversion H4.
        rewrite elem_of_list_In in_flat_map .
        destruct j.
        exists v.
        split.
        * apply elem_of_list_to_map_2 in Heqn.
          apply elem_of_list_In in Heqn.
          apply in_flat_map in Heqn.
          destruct Heqn.
          destruct H0.
          apply in_map_iff in H1.
          destruct H1.
          destruct H1.
          by inversion H1;subst;clear H1.
        * apply in_map_iff.
          exists (r0,w0).
          split;[done|].
          apply elem_of_list_In.
          apply elem_of_map_to_list'.
          rewrite  /get_vm_state /get_vm_reg_file.
          destruct (decide (v=i));subst.
          destruct (decide (r=r0));subst;[contradiction|].
          apply elem_of_list_to_map_2 in Heqn.
          apply elem_of_list_In in Heqn.
          apply in_flat_map in Heqn.
          destruct Heqn.
          destruct H0.
          apply in_map_iff in H1.
          destruct H1.
          destruct H1.
          inversion H1;subst;clear H1.
          apply elem_of_list_In in H2.
          apply elem_of_map_to_list' in H2.
          rewrite  /get_vm_reg_file /get_vm_state in H2.
          destruct (get_vm_states σ !!! i).
          destruct p.
          unfold get_vm_state.
          unfold get_vm_states.
          simpl.
          rewrite -> (vlookup_insert i _ σ.1.1.1).
          simpl.
          by rewrite lookup_insert_ne.
          simpl.
          apply elem_of_list_to_map_2 in Heqn.
          apply elem_of_list_In in Heqn.
          apply in_flat_map in Heqn.
          destruct Heqn.
          destruct H0.
          apply in_map_iff in H1.
          destruct H1.
          destruct H1.
          inversion H1;subst;clear H1.
          apply elem_of_list_In in H2.
          apply elem_of_map_to_list' in H2.
          rewrite  /get_vm_reg_file /get_vm_state /get_vm_states in H2.
          destruct (σ.1.1.1 !!! i).
          destruct p.
          rewrite /get_vm_state /get_vm_states.
          simpl.
          by rewrite vlookup_insert_ne.
      + rewrite lookup_insert_ne;[|done].
        unfold get_reg_gmap in Heqn.
        rewrite Heqn.
        rewrite /get_vm_reg_file /get_vm_state /get_vm_states.
        rewrite /get_vm_reg_file /get_vm_state /get_vm_states in Heqn.
        destruct j.
        apply not_elem_of_list_to_map_2 in Heqn.
        apply not_elem_of_list_to_map_1.
        intro.
        apply elem_of_list_In in H0.
        apply in_map_iff in H0.
        destruct H0.
        destruct H0.
        apply in_flat_map in H1.
        destruct H1;destruct H1.
        apply in_map_iff in H2.
        destruct H2;destruct H2.
        apply elem_of_list_In in H3.
        apply elem_of_map_to_list' in H3.
        simplify_eq /=.
        destruct (decide (v=i)).
        apply Heqn.
        apply elem_of_list_In.
        apply in_map_iff.
        exists (x1.1,v,x1.2).
        split;[done|].
        apply in_flat_map.
        exists v.
        split;[done|].
        apply in_map_iff.
        exists (x1.1, x1.2).
        split;[done|].
        apply elem_of_list_In.
        apply elem_of_map_to_list'.
        simplify_eq /=.
        rewrite  -H3.
        destruct (σ.1.1.1 !!! i).
        destruct p.
        simpl.
        rewrite (vlookup_insert i _ σ.1.1.1).
        simpl.
        destruct (decide (r = x1.1));[subst;contradiction|].
        by rewrite lookup_insert_ne.
        apply Heqn.
        apply elem_of_list_In.
        apply in_map_iff.
        exists (x1.1,v,x1.2).
        split;[done|].
        apply in_flat_map.
        exists v.
        split;[done|].
        apply in_map_iff.
        exists (x1.1, x1.2).
        split;[done|].
        apply elem_of_list_In.
        apply elem_of_map_to_list'.
        simplify_eq /=.
        rewrite  -H3.
        destruct (σ.1.1.1 !!! i).
        destruct p.
        simpl.
        by rewrite vlookup_insert_ne.
  Qed.

(* TODO: how to specify this lemma? *)
(* Lemma update_PC_offset_update_reg σ  *)

  Definition get_txrx_auth_agree σ (f: mail_box -> pid) :
    ra_TXBuffer:=
    (● (list_to_map (map (λ v, (v,to_agree (f (get_vm_mail_box σ v)))) (list_of_vmids) )
    )).

  Definition get_tx_agree σ := get_txrx_auth_agree σ (λ p, p.1).

  Lemma update_reg_global_preserve_tx σ i r w : get_tx_agree (update_reg_global σ i r w) =
                                               (get_tx_agree σ).
  Proof.
    rewrite /get_tx_agree /get_txrx_auth_agree.
    f_equal.
    f_equal.
    f_equal.
    apply functional_extensionality.
    intros.
    rewrite /update_reg_global /get_vm_mail_box.
    destruct (decide (i=x)).
    - subst x.
      destruct (get_vm_state σ i).
      destruct p.
      rewrite /get_vm_state /get_vm_states.
      simpl.
      by rewrite -> (vlookup_insert i _  σ.1.1.1).
    - destruct (get_vm_state σ i).
      destruct p.
      rewrite /get_vm_state /get_vm_states.
      simpl.
      by rewrite vlookup_insert_ne;[done|].
    Qed.

  Lemma update_offset_PC_preserve_tx σ d o : get_tx_agree (update_offset_PC σ d o) = get_tx_agree σ.
  Proof.
    unfold update_offset_PC.
    destruct (get_vm_reg_file σ (get_current_vm σ) !! PC).
    destruct d; rewrite /update_reg update_reg_global_preserve_tx;done.
    done.
  Qed.

  Definition get_rx_agree σ := get_txrx_auth_agree σ (λ p, p.2.1.1).

Lemma update_reg_global_preserve_rx1 σ i r w : get_rx_agree (update_reg_global σ i r w) =
                                               (get_rx_agree σ).
  Proof.
    rewrite /get_rx_agree /get_txrx_auth_agree.
    f_equal.
    f_equal.
    f_equal.
    apply functional_extensionality.
    intros.
    rewrite /update_reg_global /get_vm_mail_box.
    destruct (decide (i=x)).
    - subst x.
      destruct (get_vm_state σ i).
      destruct p.
      rewrite /get_vm_state /get_vm_states.
      simpl.
      by rewrite -> (vlookup_insert i _  σ.1.1.1).
    - destruct (get_vm_state σ i).
      destruct p.
      rewrite /get_vm_state /get_vm_states.
      simpl.
      by rewrite vlookup_insert_ne;[done|].
    Qed.

  Lemma update_offset_PC_preserve_rx1 σ d o : get_rx_agree (update_offset_PC σ d o) = get_rx_agree σ.
  Proof.
    unfold update_offset_PC.
    destruct (get_vm_reg_file σ (get_current_vm σ) !! PC).
    destruct d; rewrite /update_reg update_reg_global_preserve_rx1;done.
    done.
  Qed.


  Definition get_rx_gmap σ :=
    (Some (gmap_view_auth 1
            ((list_to_map (map (λ v, let mb := (get_vm_mail_box σ v) in
                                    match mb.2.2 with
                                      | Some j => (v, (Some (0, j)))
                                      | None => (v,None)
                                    end) (list_of_vmids))): (gmap vmid (optionO (prodO natO (leibnizO vmid))) )))).

  Lemma update_reg_global_preserve_rx2 σ i r w : get_rx_gmap (update_reg_global σ i r w) =
                                               (get_rx_gmap σ).
  Proof.
    rewrite /get_rx_gmap /get_txrx_auth_agree.
    f_equal.
    f_equal.
    f_equal.
    f_equal.
    apply functional_extensionality.
    intros.
    rewrite /update_reg_global /get_vm_mail_box.
    destruct (decide (i=x)).
    - subst x.
      destruct (get_vm_state σ i).
      destruct p.
      rewrite /get_vm_state /get_vm_states.
      simpl.
      by rewrite -> (vlookup_insert i _  σ.1.1.1).
    - destruct (get_vm_state σ i).
      destruct p.
      rewrite /get_vm_state /get_vm_states.
      simpl.
      by rewrite vlookup_insert_ne;[done|].
    Qed.

  Lemma update_offset_PC_preserve_rx2 σ d o : get_rx_gmap (update_offset_PC σ d o) = get_rx_gmap σ.
  Proof.
    unfold update_offset_PC.
    destruct (get_vm_reg_file σ (get_current_vm σ) !! PC).
    destruct d; rewrite /update_reg update_reg_global_preserve_rx2;done.
    done.
  Qed.


  (* TODO: the proofs above are identical *)

  Lemma update_reg_global_preserve_rx σ i r w : (get_rx_agree (update_reg_global σ i r w), get_rx_gmap (update_reg_global σ i r w)) =
                                               (get_rx_agree σ, get_rx_gmap σ).
  Proof.
    by rewrite update_reg_global_preserve_rx1 update_reg_global_preserve_rx2.
  Qed.

Lemma update_offset_PC_preserve_rx  σ d o : (get_rx_agree (update_offset_PC σ d o), get_rx_gmap (update_offset_PC σ d o) ) =
                                               (get_rx_agree σ, get_rx_gmap σ).
  Proof.
    by rewrite update_offset_PC_preserve_rx1 update_offset_PC_preserve_rx2 .
  Qed.

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


  (* XXX:  seems like we have to keep resources being indexed by vmids...  *)

  (* Definition get_owned_gset δ : (authR (gset_disjUR pid)) := *)
  (*   (● (map_fold (λ (p:pid) (perm:permission) (s: gset_disjUR pid), *)
  (*                 match perm.1 with *)
  (*                 | Owned =>  match s with *)
  (*                               | GSet s' => GSet (s' ∪ {[p]}) *)
  (*                               | GSetBot => GSet ∅ *)
  (*                             end *)
  (*                 | Unowned => s *)
  (*                end)  (GSet ∅) δ.2)). *)


  (* Definition get_access_gmap δ : ra_Accessible := *)
  (*   (●  (map_fold (λ (p:pid) (perm:permission) (s: (gmap pid (prodR dfracR (csumR (agreeR unitO) (exclR unitO))))), *)
  (*                 match perm.2 with *)
  (*                 | NoAccess => s *)
  (*                 | SharedAccess => <[p:= ((DfracOwn 1), (Cinl (to_agree ())))]>s *)
  (*                 | ExclusiveAccess => <[p:= ((DfracOwn 1),(Cinr (Excl ())))]>s *)
  (*                end)  ∅  δ.2 )). *)

  (* XXX: another attempt: *)

  Definition get_owned_gmap σ : (authR (gmapUR vmid (prodR dfracR (gset_disjUR pid)))) :=
    (● (list_to_map (map (λ v, (v, ((DfracOwn 1),
        (GSet ((list_to_set (map (λ (p:(pid*permission)), p.1)
           (map_to_list (filter (λ p, (is_owned p.2) = true) (get_vm_page_table σ v)))))
                         : gset pid))))) (list_of_vmids)))).

  Lemma update_reg_global_preserve_owned σ i r w : get_owned_gmap (update_reg_global σ i r w) =
                                               (get_owned_gmap σ).
  Proof.
    rewrite /get_owned_gmap.
    f_equal.
    f_equal.
    f_equal.
    apply functional_extensionality.
    intros.
    rewrite /update_reg_global /get_vm_page_table.
    destruct (decide (i=x)).
    - subst x.
      destruct (get_vm_state σ i).
      destruct p.
      rewrite /get_vm_state /get_vm_states.
      simpl.
      by rewrite -> (vlookup_insert i _  σ.1.1.1).
    - destruct (get_vm_state σ i).
      destruct p.
      rewrite /get_vm_state /get_vm_states.
      simpl.
      by rewrite vlookup_insert_ne;[done|].
    Qed.

  Lemma update_offset_PC_preserve_owned σ d o : get_owned_gmap (update_offset_PC σ d o) = get_owned_gmap σ.
  Proof.
    unfold update_offset_PC.
    destruct (get_vm_reg_file σ (get_current_vm σ) !! PC).
    destruct d; rewrite /update_reg update_reg_global_preserve_owned;done.
    done.
  Qed.



  (* Definition get_access_gmap σ : ra_Accessible := *)
  (*   (●  (foldr (λ p acc, <[p.1:=((DfracOwn 1),p.2)]>acc) ∅ *)
  (*        (vzip_with (λ v δ, (v, *)
  (*                   (map_fold (λ (p:pid) (perm:permission) (s: (gset_disjUR pid)), *)
  (*                 match perm.2 with *)
  (*                 | NoAccess => s *)
  (*                 | SharedAccess | ExclusiveAccess => match s with *)
  (*                                     | GSet s' => GSet (s' ∪ {[p]}) *)
  (*                                     | GSetBot => GSet ∅ *)
  (*                                   end *)
  (*                end) (GSet ∅) δ.2 ))) (vector_of_vmids) (get_vm_states σ) ))). *)

  (* Definition get_access_gmap σ : ra_Accessible := *)
  (*   (● (list_to_map (map (λ v, (v, ((DfracOwn 1),(map_fold (λ (p:pid) (perm:permission) (s: (gset_disjUR pid)), *)
  (*                 match (is_accessible perm) with *)
  (*                 | false => s *)
  (*                 | true => match s with *)
  (*                                     | GSet s' => GSet (s' ∪ {[p]}) *)
  (*                                     | GSetBot => GSet ∅ *)
  (*                                   end *)
  (*                end) (GSet ∅) (get_vm_page_table σ v))))) (list_of_vmids)))). *)

  Definition get_access_gmap σ : ra_Accessible :=
    (● (list_to_map (map (λ v, (v, ((DfracOwn 1),
        (GSet ((list_to_set (map (λ (p:(pid*permission)), p.1)
           (map_to_list (filter (λ p, (is_accessible p.2) = true) (get_vm_page_table σ v)))))
                         : gset pid))))) (list_of_vmids)))).

 Lemma update_reg_global_preserve_access σ i r w : get_access_gmap (update_reg_global σ i r w) =
                                               (get_access_gmap σ).
  Proof.
    rewrite /get_access_gmap.
    f_equal.
    f_equal.
    f_equal.
    apply functional_extensionality.
    intros.
    rewrite /update_reg_global /get_vm_page_table.
    destruct (decide (i=x)).
    - subst x.
      destruct (get_vm_state σ i).
      destruct p.
      rewrite /get_vm_state /get_vm_states.
      simpl.
      by rewrite -> (vlookup_insert i _  σ.1.1.1).
    - destruct (get_vm_state σ i).
      destruct p.
      rewrite /get_vm_state /get_vm_states.
      simpl.
      by rewrite vlookup_insert_ne;[done|].
    Qed.

  Lemma update_offset_PC_preserve_access σ d o : get_access_gmap (update_offset_PC σ d o) = get_access_gmap σ.
  Proof.
    unfold update_offset_PC.
    destruct (get_vm_reg_file σ (get_current_vm σ) !! PC).
    destruct d; rewrite /update_reg update_reg_global_preserve_access;done.
    done.
  Qed.

  (* TODO: a new exclusive ra*)


  Fixpoint vec_to_gmap{A:Type}  (vec: vec A vm_count)  : gmap vmid A:=
    (foldr (λ p acc, <[p.1:=p.2]>acc) ∅
           (vzip_with (λ v s, (v,s)) (vector_of_vmids) vec)).
  (* TODO we need getters for transations.. *)
  Definition get_trans_gmap σ : gmap word (vmid * word * word  * (gmap vmid (listset_nodup pid)) * transaction_type):=
    list_to_map (map (λ (p:word * transaction) ,
                      let trans := p.2 in
                  (p.1,((((trans.1.1.1.1.1, trans.1.1.1.1.2), trans.1.1.1.2), (vec_to_gmap trans.1.2)), trans.2))
      )  (map_to_list (get_transactions σ))).


 Lemma update_reg_global_preserve_trans σ i r w : get_trans_gmap (update_reg_global σ i r w) =
                                               (get_trans_gmap σ).
  Proof.
    rewrite /get_trans_gmap.
    f_equal.
    f_equal.
    f_equal.
    rewrite /update_reg_global /get_transactions.
    destruct (get_vm_state σ i).
    destruct p.
    by rewrite /get_vm_states.
  Qed.

  Lemma update_offset_PC_preserve_trans σ d o : get_trans_gmap (update_offset_PC σ d o) = get_trans_gmap σ.
  Proof.
    unfold update_offset_PC.
    destruct (get_vm_reg_file σ (get_current_vm σ) !! PC).
    destruct d; rewrite /update_reg update_reg_global_preserve_trans;done.
    done.
  Qed.


  Definition get_receivers_gmap σ : authR (gmapUR word (gset_disjR (leibnizO vmid))) :=
    ● (list_to_map (map (λ (p:word * transaction) ,
                      let trans := p.2 in
                  (p.1,(GSet trans.1.1.2))) (map_to_list (get_transactions σ)))).

  Lemma update_reg_global_preserve_receivers σ i r w : get_receivers_gmap (update_reg_global σ i r w) =
                                               (get_receivers_gmap σ).
  Proof.
    rewrite /get_receivers_gmap.
    f_equal.
    f_equal.
    f_equal.
    f_equal.
    rewrite /update_reg_global /get_transactions.
    destruct (get_vm_state σ i).
    destruct p.
    by rewrite /get_vm_states.
  Qed.

  Lemma update_offset_PC_preserve_receivers σ d o : get_receivers_gmap (update_offset_PC σ d o) = get_receivers_gmap σ.
  Proof.
    unfold update_offset_PC.
    destruct (get_vm_reg_file σ (get_current_vm σ) !! PC).
    destruct d; rewrite /update_reg update_reg_global_preserve_receivers;done.
    done.
  Qed.


  Definition gen_vm_interp σ: iProp Σ :=
    let i := (get_current_vm σ) in
    let δ := (get_vm_state σ i) in
      own (gen_num_name vmG) (to_agree vm_count)∗
      ghost_map_auth (gen_mem_name vmG) 1 (get_mem σ) ∗
      ghost_map_auth (gen_reg_name vmG) 1 (get_reg_gmap σ) ∗
      own (gen_tx_name vmG) (get_tx_agree σ) ∗
      own (gen_rx_name vmG) ((get_rx_agree σ), (get_rx_gmap σ) )∗
      own (gen_owned_name vmG) (get_owned_gmap σ) ∗
      own (gen_access_name vmG) (get_access_gmap σ) ∗
      ghost_map_auth (gen_trans_name vmG) 1 (get_trans_gmap σ) ∗
      own (gen_retri_name vmG) (get_receivers_gmap σ)
    .


  Definition num_agree_def (n:nat) : iProp Σ :=
    own (gen_num_name vmG) (to_agree n).
  Definition num_agree_aux : seal (@num_agree_def). Proof. by eexists. Qed.
  Definition num_agree:= num_agree_aux.(unseal).
  Definition num_agree_eq : @num_agree = @num_agree_def := num_agree_aux.(seal_eq).

  Definition mem_mapsto_def (a:addr) (dq : dfrac) (w:word) : iProp Σ :=
    (ghost_map_elem (gen_mem_name vmG) a dq w).
    (* own (gen_mem_name vmG) (gmap_view_frag a dq (w : leibnizO word)). *)
  Definition mem_mapsto_aux : seal (@mem_mapsto_def). Proof. by eexists. Qed.
  Definition mem_mapsto := mem_mapsto_aux.(unseal).
  Definition mem_mapsto_eq : @mem_mapsto = @mem_mapsto_def := mem_mapsto_aux.(seal_eq).

  Definition reg_mapsto_def (r:reg_name) (i:vmid) (dq : dfrac) (w:word) : iProp Σ :=
    (ghost_map_elem (gen_reg_name vmG) (r,i) dq w).
    (* own (gen_reg_name vmG) (gmap_view_frag (r,i) dq (w : leibnizO word)). *)
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

  Definition owned_mapsto_def (i:vmid) dq (s: gset_disj pid) : iProp Σ :=
    own (gen_owned_name vmG) (◯ {[i := (dq, s)]}).
  (* Definition owned_mapsto_def (s: gset_disj pid) : iProp Σ := *)
    (* own (gen_owned_name vmG) (◯ s). *)
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
  (* Definition access_mapsto_def dq (m: gmap pid access) : iProp Σ := *)
  (*   own (gen_access_name vmG) (◯ (map_fold (λ p a acc, *)
  (*                                                      match a with *)
  (*                                                        | NoAccess => acc *)
  (*                                                        | SharedAccess => <[p:=(dq, (Cinl (to_agree ())))]>acc *)
  (*                                                        | ExclusiveAccess => <[p:=(dq, (Cinr (Excl ())))]>acc *)
  (*                                                      end) ∅ m)). *)
  Definition access_mapsto_def (i:vmid) dq (s: gset_disj pid) : iProp Σ :=
    own (gen_access_name vmG) (◯ {[i := (dq,  s)]}).
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
  Implicit Types a b c : addr.
  Implicit Types r : reg_name.
  Implicit Types w: word.


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

Lemma gen_reg_valid:
  ∀ (σ : state) r i w,
    i = (get_current_vm σ) ->
    ghost_map_auth (gen_reg_name vmG) 1 (get_reg_gmap σ) -∗
    r @@ i ->r w -∗
          ⌜ (get_reg σ r) = Some w ⌝.
Proof.
  iIntros (?????) "Hσ Hr".
  rewrite reg_mapsto_eq /reg_mapsto_def.
  iDestruct (ghost_map_lookup with "Hσ Hr") as "%".
  simplify_eq /=.
  iPureIntro.
  unfold get_reg.
  unfold get_reg_gmap in H0.
  simplify_eq /=.
  unfold get_reg_global.
  Check elem_of_list_to_map_2.
  apply elem_of_list_to_map_2 in H0.
  apply elem_of_list_In in H0.
  apply in_flat_map in H0.
  inversion H0; clear H0.
  destruct H.
  apply in_map_iff in H0.
  inversion H0;clear H0.
  inversion H1;clear H1.
  inversion H0.
  apply elem_of_list_In in H2.
  apply elem_of_map_to_list' in H2.
  subst x.
  done.
Qed.


(* TODO : quite ugly... *)
Lemma gen_reg_valid_Sep:
  ∀ (σ : state) i (regs: gmap (reg_name * vmid) word) ,
    i = (get_current_vm σ) ->
    ghost_map_auth (gen_reg_name vmG) 1 (get_reg_gmap σ) -∗
    ([∗ map] r↦w ∈ regs,  r.1 @@ r.2 ->r w)-∗
          ([∗ map] r↦w ∈ regs, ⌜r.2 = i -> (get_reg σ r.1) = Some w ⌝).
Proof.
  iIntros (????) "Hσ Hregs".
  rewrite reg_mapsto_eq /reg_mapsto_def.
  iDestruct ((ghost_map_lookup_big  regs) with "[Hσ] [Hregs]") as "%Hincl".
  iApply "Hσ".
  iApply (big_sepM_proper (λ k x, (k.1, k.2)↪[gen_reg_name vmG] x)%I).
  intros.
  simplify_eq.
  f_equiv.
  destruct k.
  done.
  done.
  iApply big_sepM_pure.
  iIntros (????).
  unfold get_reg.
  unfold get_reg_global.
  apply (lookup_weaken  _ (get_reg_gmap σ) _ _) in a1.
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
  simplify_eq /=.
  done.
  done.
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

(* TODO: bigSep version *)


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
    rewrite tx_mapsto_eq /mem_mapsto_def.
    Admitted.


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
  Lemma owned_split_set i q1 q2 (s1 s2 : gset pid):
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

  Lemma owned_split_singleton i q1 q2 (s : gset pid) p:
   p ∉ s -> O@i:={(q1+q2)%Qp}[(s ∪ {[p]})] -∗ O@i:={q1}[s] ∗ O@i:={q2}p.
  Proof using.
    iIntros (Hnotin) "HO".
    assert (Hdisj: s ## {[p]}). { set_solver. }
    iDestruct (owned_split_set i q1 q2 _ _ Hdisj with "HO")  as "HO'".
    done.
  Qed.

 Lemma access_split_set i q1 q2 (s1 s2 : gset pid):
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

  Lemma access_split_singleton i q1 q2 (s : gset pid) p:
   p ∉ s -> A@i:={(q1+q2)%Qp}[(s ∪ {[p]})] -∗ A@i:={q1}[s] ∗ A@i:={q2}p.
  Proof using.
    iIntros (Hnotin) "HO".
    assert (Hdisj: s ## {[p]}). { set_solver. }
    iDestruct (access_split_set i q1 q2 _ _ Hdisj with "HO")  as "HO'".
    done.
  Qed.

Lemma gen_access_valid:
  ∀ (σ : state) i q p,
    own (gen_access_name vmG) (get_access_gmap σ)  -∗
    (A@ i :={q}p ) -∗
          ( ⌜(check_access_page σ i p)= true ⌝).
  Proof.
    iIntros (????) "Hσ Hacc".
    rewrite access_mapsto_eq /access_mapsto_def.
    iDestruct (own_valid_2 with "Hσ Hacc") as %Hvalid.
    iPureIntro.
    unfold get_access_gmap in Hvalid.
    apply auth_both_valid_discrete in Hvalid.
    destruct Hvalid.
    remember (list_to_map (map
              (λ v : vmid,
                 (v,
                 (DfracOwn 1,
                 GSet
                   (list_to_set
                      (map (λ p : pid * permission, p.1)
                         (map_to_list
                            (filter (λ p : pid * permission, is_accessible p.2 = true)
                               (get_vm_page_table σ v)))))))) list_of_vmids)) as m.
    pose proof (lookup_included {[i := (DfracOwn q, GSet {[p]})]} m).
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
   destruct H1.
    - inversion H;clear H.
      simplify_eq /=.
      unfold check_access_page.
     destruct (get_vm_page_table σ i !! p) eqn:Heqn.
    + assert ( p ∈ ({[p]}: gset pid)) as Hin.
      { set_solver.  }
      rewrite H3 in Hin.
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
      rewrite H1 in Heqn.
      inversion Heqn.
      assumption.
    + assert ( p ∈ ({[p]}: gset pid)) as Hin.
      { set_solver.  }
      rewrite H3 in Hin.
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
      rewrite H1 in Heqn.
      inversion Heqn.
    - apply pair_included in H.
      destruct H;clear H.
      apply gset_disj_included in H1.
      unfold check_access_page.
     destruct (get_vm_page_table σ i !! p) eqn:Heqn.
    + assert ( p ∈ (list_to_set
           (map (λ p : pid * permission, p.1)
              (map_to_list (filter (λ p : pid * permission, is_accessible p.2 = true) (get_vm_page_table σ i)))): gset pid)) as Hin.
      { set_solver.  }
      apply elem_of_list_to_set in Hin.
      apply elem_of_list_In in Hin.
      apply (in_map_iff _ _ p) in Hin.
      destruct Hin.
      destruct H.
      rewrite <- elem_of_list_In in H3.
      apply elem_of_map_to_list' in H3.
      apply map_filter_lookup_Some in H3.
      destruct H3.
      subst p.
      rewrite H3 in Heqn.
      inversion Heqn.
      assumption.
    + assert ( p ∈ (list_to_set
           (map (λ p : pid * permission, p.1)
              (map_to_list (filter (λ p : pid * permission, is_accessible p.2 = true) (get_vm_page_table σ i)))): gset pid)) as Hin.
      { set_solver.  }
      apply elem_of_list_to_set in Hin.
      apply elem_of_list_In in Hin.
      apply (in_map_iff _ _ p) in Hin.
      destruct Hin.
      destruct H.
      rewrite <- elem_of_list_In in H3.
      apply elem_of_map_to_list' in H3.
      apply map_filter_lookup_Some in H3.
      destruct H3.
      subst p.
      rewrite H3 in Heqn.
      inversion Heqn.
Qed.



  (* TODO : gen_access_valid_Sep, gen_access_valid_set*)

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
