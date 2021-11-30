From HypVeri Require Import machine machine_extra tactics.
From HypVeri.algebra Require Import base.

Section pagetable_extra.

Context `{HyperConst : HypervisorConstants}.

Lemma update_ownership_batch_preserve_current_vm σ (ps: list PID):
 get_current_vm (update_ownership_batch σ ps) = get_current_vm σ.
Proof. f_equal. Qed.

Lemma update_ownership_batch_preserve_regs σ (ps: list PID):
 get_reg_gmap (update_ownership_batch σ ps) = get_reg_gmap σ.
Proof. f_equal. Qed.

Lemma update_ownership_batch_preserve_mem σ (ps: list PID):
 get_mem (update_ownership_batch σ ps) = get_mem σ.
Proof. f_equal. Qed.

Lemma update_ownership_batch_preserve_rx σ (ps: list PID):
 get_rx_gmap (update_ownership_batch σ ps) = get_rx_gmap σ.
Proof. f_equal. Qed.

Lemma update_ownership_batch_preserve_trans σ (ps: list PID):
 get_trans_gmap (update_ownership_batch σ ps) = get_trans_gmap σ.
Proof.  f_equal. Qed.

Lemma update_ownership_batch_preserve_trans' σ (ps: list PID):
 get_transactions (update_ownership_batch σ ps) = get_transactions σ.
Proof. f_equal. Qed.

Lemma update_ownership_batch_preserve_hpool σ (ps: list PID):
 get_hpool_gset (update_ownership_batch σ ps) = get_hpool_gset σ.
Proof. f_equal. Qed.

Lemma update_ownership_batch_preserve_retri σ (ps: list PID):
 get_retri_gmap (update_ownership_batch σ ps) = get_retri_gmap σ.
Proof. f_equal. Qed.

Lemma update_ownership_batch_preserve_access σ ps:
((get_access_gmap (update_ownership_batch σ ps)):gmap _ _) = ((get_access_gmap σ): gmap _ _).
Proof.
  rewrite /get_access_gmap /update_ownership_batch /update_ownership_global_batch /get_page_table /=.
  generalize dependent σ.
  induction ps.
  done.
  simpl.
  intro.
  rewrite /update_ownership' /=.
  destruct (list.foldr
      (λ (p : PID) (acc : page_table),
         match acc !! p with
         | Some (_, s) => <[p:= (get_current_vm σ, s)]> acc
         | None => acc
         end) σ.1.1.1.2 ps !! a) eqn:Hlookup.
  { destruct p.
    rewrite fmap_insert.
    rewrite IHps /=.
    assert (∃ v', σ.1.1.1.2 !! a = Some (v', g)).
    { clear IHps.
      generalize dependent v.
      induction ps;intros v Hlookup; simpl in Hlookup.
      exists v;done.
      destruct (list.foldr
                (λ (p : PID) (acc : page_table),
                   match acc !! p with
                   | Some (_, s) => <[p:= (get_current_vm σ, s)]> acc
                   | None => acc
                   end) σ.1.1.1.2 ps !! a0) eqn: Hlookup'.
      { destruct p.
        destruct (decide (a0=a)).
        subst a0.
        apply (IHps v0).
        rewrite lookup_insert in Hlookup.
        inversion Hlookup.
        subst g0.
        done.
        rewrite lookup_insert_ne in Hlookup;[|done].
        apply (IHps v Hlookup).
      }
      { apply (IHps v Hlookup).
      }
    }
    destruct H.
    apply map_eq.
    intro.
    destruct (decide (i=a)).
    rewrite e.
    rewrite lookup_insert.
    rewrite lookup_fmap H.
    done.
    rewrite lookup_insert_ne;[done|eauto].
  }
  rewrite IHps //.
Qed.

Lemma update_access_batch_preserve_current_vm σ (ps: list PID) :
 get_current_vm (update_access_batch σ ps) = get_current_vm σ.
Proof. f_equal. Qed.

Lemma update_access_batch_preserve_regs σ (ps: list PID):
 get_reg_gmap (update_access_batch σ ps) = get_reg_gmap σ.
Proof. f_equal. Qed.

Lemma update_access_batch_preserve_mem σ (ps: list PID):
 get_mem (update_access_batch σ ps) = get_mem σ.
Proof. f_equal. Qed.

Lemma update_access_batch_preserve_rx σ (ps: list PID):
 get_rx_gmap (update_access_batch σ ps) = get_rx_gmap σ.
Proof. f_equal. Qed.

Lemma update_access_batch_preserve_trans σ (ps: list PID) :
 get_trans_gmap (update_access_batch σ ps) = get_trans_gmap σ.
Proof. f_equal. Qed.

Lemma update_access_batch_preserve_trans' σ (ps: list PID):
 get_transactions (update_access_batch σ ps) = get_transactions σ.
Proof. f_equal. Qed.

Lemma update_access_batch_preserve_hpool σ (ps: list PID):
 get_hpool_gset (update_access_batch σ ps) = get_hpool_gset σ.
Proof. f_equal. Qed.

Lemma update_access_batch_preserve_retri σ (ps: list PID):
 get_retri_gmap (update_access_batch σ ps) = get_retri_gmap σ.
Proof. f_equal. Qed.

Lemma update_access_batch_preserve_ownerships σ ps:
 (get_owned_gmap (update_access_batch σ ps)) = (get_owned_gmap σ).
Proof.
  rewrite /get_owned_gmap /update_access_batch /update_access_global_batch /get_page_table /=.
  do 2 f_equal.
  generalize dependent σ.
  induction ps.
  done.
  simpl.
  intro.
  rewrite /update_access' /=.
  destruct (list.foldr
      (λ (p : PID) (acc : page_table),
         match acc !! p with
         | Some (o, s) => <[p:= (o, {[get_current_vm σ]} ∪ s)]> acc
         | None => acc
         end) σ.1.1.1.2 ps !! a) eqn:Hlookup.
  { destruct p.
    rewrite fmap_insert.
    rewrite IHps /=.
    assert (∃ g', σ.1.1.1.2 !! a = Some (v, g')).
    { clear IHps.
      generalize dependent g.
      induction ps;intros g Hlookup; simpl in Hlookup.
      exists g;done.
      destruct (list.foldr
                (λ (p : PID) (acc : page_table),
                   match acc !! p with
                   | Some (o, s) => <[p:= (o, {[get_current_vm σ]} ∪ s)]> acc
                   | None => acc
                   end) σ.1.1.1.2 ps !! a0) eqn: Hlookup'.
      { destruct p.
        destruct (decide (a0=a)).
        subst a0.
        apply (IHps g0).
        rewrite lookup_insert in Hlookup.
        inversion Hlookup.
        subst v0.
        done.
        rewrite lookup_insert_ne in Hlookup;[|done].
        apply (IHps g Hlookup).
      }
      { apply (IHps g Hlookup).
      }
    }
    destruct H.
    apply map_eq.
    intro.
    destruct (decide (i=a)).
    rewrite e.
    rewrite lookup_insert.
    rewrite lookup_fmap H.
    done.
    rewrite lookup_insert_ne;[done|eauto].
  }
  rewrite IHps //.
Qed.

Lemma update_access_batch_preserve_mb σ ps:
 (get_mb_gmap (update_access_batch σ ps)) = (get_mb_gmap σ).
Proof.
  rewrite /get_mb_gmap /update_access_batch /update_access_global_batch /=.
  f_equal.
 Qed.

Lemma update_ownership_batch_preserve_mb σ ps:
 (get_mb_gmap (update_ownership_batch σ ps)) = (get_mb_gmap σ).
Proof.
  rewrite /get_mb_gmap /=.
  f_equal.
Qed.

(* TODO: *)

(* Lemma get_pagetable_gmap_checkb {σ} p v s: *)
(*  (get_pagetable_gmap σ) !! p = Some (v, s)-> *)
(*  (p ∈ s <-> *)
(*   ∃ perm, (proj (get_vm_page_table σ i)) !! p =Some perm ∧ checkb perm = true). *)
(* Proof. *)
(*   intros. *)
(*   rewrite /get_access_gmap in H. *)
(*   apply (elem_of_list_to_map_2 _ i s) in H. *)
(*   inv_map_in. clear H0. *)
(*   inversion H. *)
(*   subst. *)
(*   clear H. *)
(*   split. *)
(*   - intro H. apply elem_of_list_to_set in H. *)
(*     inv_map_in. *)
(*     apply elem_of_list_In in H0. *)
(*     apply elem_of_map_to_list' in H0. *)
(*     apply map_filter_lookup_Some in H0. *)
(*     destruct H0. *)
(*     exists x.2. *)
(*     split;eauto. *)
(*       by subst p. *)
(*   - intros H. *)
(*     destruct H. *)
(*     apply elem_of_list_to_set. *)
(*     apply elem_of_list_In. *)
(*     apply in_map_iff. *)
(*     exists (p,x). *)
(*     split;eauto. *)
(*     apply elem_of_list_In. *)
(*     apply elem_of_map_to_list'. *)
(*     apply map_filter_lookup_Some. *)
(*     done. *)
(* Qed. *)

(*--- prove having mappings in gmap implies owership/access to pages in opsem ---*)

Lemma get_owned_gmap_is_owned {σ} p i:
 (get_owned_gmap σ) !! p = Some (i,Owned) ->
 ∃ acc, (get_page_table σ) !! p =Some (i,acc).
Proof.
  intros.
  rewrite /get_owned_gmap in H.
  apply (elem_of_list_to_map_2 _ p (i,Owned) ) in H.
  (* inv_map_in. clear H0. *)
    apply elem_of_map_to_list' in H.
  simpl in H.
  rewrite lookup_fmap in H.
  destruct (get_page_table σ !! p) eqn:Heqn.
  exists p0.2.
  rewrite Heqn /= in H.
  inversion H.
  destruct p0;done.
  rewrite Heqn in H.
  done.
Qed.

Lemma get_access_gmap_is_accessible {σ} p sacc:
 (get_access_gmap σ) !! p = Some (1%Qp, GSet sacc) ->
  ∃ v, (get_page_table σ) !! p = Some (v,sacc).
Proof.
  intros.
  rewrite /get_access_gmap in H.
  (* apply (elem_of_list_to_map_2 _ p (1%Qp,GSet sacc) ) in H. *)
  (* inv_map_in. clear H0. *)
    (* apply elem_of_map_to_list' in H. *)
  (* simpl in H. *)
  rewrite lookup_fmap in H.
  destruct (get_page_table σ !! p) eqn:Heqn.
  exists p0.1.
  rewrite Heqn /= in H.
  inversion H.
  destruct p0;done.
  rewrite Heqn in H.
  done.
Qed.

(* Lemma get_access_gmap_is_exclusive {σ} p i : *)
(*  (get_access_gmap σ) !! p = Some  (1%Qp, GSet {[i]}) -> *)
(*   ∃ v , (get_page_table σ) !! p =Some(v, {[i]}) . *)

(* XXX what should the following lemma look like? *)
(* Lemma update_access_batch_update_access_gmap {σ i s p} {sps:gset PID} *)
(*       (ps: list PID): *)
(*  sps = (list_to_set ps) -> *)
(*  i = (get_current_vm σ) -> *)
(*  (∀ p, p ∈ ps -> ∃ q sacc, (get_access_gmap σ) !! p = Some (q, sacc) -> *)
(*                           (get_access_gmap (update_access_batch σ ps)) !! p = Some (q,sacc ∪ {[i]})). *)
(* Proof. *)
(*   intros Hsps Hi Hcheckb Hlookup. *)
(*   rewrite /get_pagetable_gmap. *)
(*   apply (@map_eq VMID (gmap VMID) _ _ _ _ _ _ _ _ gmap_finmap);eauto. *)
(*   intro. *)
(*   rewrite -Hi. *)
(*   destruct(decide (i0 = i)). *)
(*   - subst i0. rewrite lookup_insert. *)
(*     assert(Hgoal : list_to_set *)
(*                      (map (λ p : PID * access, p.1) *)
(*                           (map_to_list (filter (λ p : PID * access, checkb p.2 = true) *)
(*                                                (get_vm_page_table (update_access_batch σ ps p) i).2))) = s ∖ sps). *)
(*     { apply set_eq. *)
(*       intro. *)
(*       rewrite elem_of_list_to_set. *)
(*       split. *)
(*       * intros. *)
(*         inv_map_in. *)
(*         apply elem_of_list_In in H0. *)
(*         apply (elem_of_map_to_list' _ x0) in H0. *)
(*         apply map_filter_lookup_Some in H0. *)
(*         destruct H0 as [Hlookup' Hcheckbtrue]. *)
(*         simplify_eq /=. *)
(*         rewrite /get_vm_page_table /get_page_tables /update_access_batch *)
(*                 /update_access_global_batch //= in Hlookup'. *)
(*         rewrite vlookup_insert in Hlookup'. *)
(*         apply elem_of_difference. *)
(*         induction ps; simpl in *. *)
(*         -- split;[|set_solver]. *)
(*            apply ((get_pagetable_gmap_checkb (λ pt,pt.2) checkb) x0.1 Hlookup). *)
(*            exists (x0.2). *)
(*            split;eauto. *)
(*         -- assert (Hneq: a ≠ x0.1). *)
(*            { destruct (decide (a=x0.1));eauto. *)
(*              subst a. *)
(*              rewrite lookup_insert in Hlookup'. *)
(*              inversion Hlookup'. *)
(*              rewrite -H0  Hcheckb // in Hcheckbtrue. *)
(*            } *)
(*            rewrite not_elem_of_union. *)
(*            assert (Himp : x0.1 ∈ s ∧ x0.1 ∉ ((list_to_set ps):gset PID) *)
(*                           ->(x0.1 ∈ s ∧ (x0.1 ∉ ({[a]}:gset PID)) ∧ x0.1 ∉ ((list_to_set ps):gset PID))). *)
(*            { intros. destruct H; split;eauto. split. set_solver. done. } *)
(*            apply Himp. *)
(*            apply IHps;eauto. *)
(*            rewrite lookup_insert_ne in Hlookup';done. *)
(*       * intros Hin. *)
(*         apply elem_of_difference in Hin. *)
(*         destruct Hin as [Hin Hnotin]. *)
(*         apply ((get_pagetable_gmap_checkb (λ pt,pt.2) checkb) x Hlookup) in Hin;eauto. *)
(*         destruct Hin. *)
(*         destruct H. *)
(*         inv_map_in. *)
(*         exists (x,x0). *)
(*         split;eauto. *)
(*         apply elem_of_list_In . *)
(*         apply  elem_of_map_to_list. *)
(*         apply map_filter_lookup_Some. *)
(*         rewrite /get_vm_page_table /get_page_tables /update_access_batch *)
(*                 /update_access_global_batch /=. *)
(*         rewrite -Hi vlookup_insert. *)
(*         split;eauto. *)
(*         generalize dependent sps. *)
(*         induction ps;simpl. *)
(*         done. *)
(*         intros. *)
(*         assert (Hneq: a ≠ x). *)
(*         { set_solver. } *)
(*         rewrite lookup_insert_ne;eauto. *)
(*         apply (IHps (list_to_set ps));eauto. *)
(*         set_solver. *)
(*     } *)
(*     apply (@elem_of_list_to_map_1' VMID (gmap VMID) _ _ _ _ _ _ _ _ gmap_finmap). *)
(*     + intros. *)
(*       inv_map_in. *)
(*       inversion H. *)
(*       do 3 f_equal. *)
(*       clear H3 H0 H. *)
(*       subst x. *)
(*       symmetry. *)
(*       apply Hgoal. *)
(*     + inv_map_in. *)
(*       exists i. *)
(*       split;[|apply in_list_of_vmids]. *)
(*       do 4 f_equal. *)
(*       apply Hgoal. *)
(*   - rewrite (lookup_insert_ne _ i i0 _);eauto. *)
(*     set (l:= (map (λ v,  (v, get_pagetable_gset (update_access_batch σ ps p) v (λ pt : page_table, pt.2) checkb)) list_of_vmids)) in *. *)
(*     destruct (list_to_map l !! i0) eqn:Heqn. *)
(*     + apply (elem_of_list_to_map_2 l i0 g) in Heqn. *)
(*       apply elem_of_list_In in Heqn. *)
(*       apply in_map_iff in Heqn. *)
(*       inversion Heqn;clear Heqn. *)
(*       destruct H as [H HIn];inversion H;subst;clear H. *)
(*       symmetry. *)
(*       eapply elem_of_list_to_map_1'. *)
(*       * intros. *)
(*         inv_map_in. *)
(*         inversion H. *)
(*         rewrite /get_pagetable_gset. *)
(*         do 4 f_equal. *)
(*         rewrite /get_vm_page_table update_access_batch_preserve_other_page_tables //. *)
(*       * inv_map_in. *)
(*         exists i0. *)
(*         split;eauto. *)
(*         rewrite /get_pagetable_gset. *)
(*         do 6 f_equal. *)
(*         rewrite /get_vm_page_table update_access_batch_preserve_other_page_tables //. *)
(*     + apply (@not_elem_of_list_to_map_2 VMID (gmap VMID) _ _ _ _ _ _ _ _ gmap_finmap) in Heqn. *)
(*       symmetry. *)
(*       apply not_elem_of_list_to_map_1. *)
(*       intro P. *)
(*       apply Heqn. *)
(*       apply elem_of_list_In. *)
(*       apply in_map_iff. *)
(*       apply elem_of_list_In in P. *)
(*       apply in_map_iff in P. *)
(*       destruct P. *)
(*       exists x. *)
(*       destruct H. *)
(*       split;eauto. *)
(*       apply in_map_iff. *)
(*       apply in_map_iff in H0. *)
(*       destruct H0. *)
(*       exists x0. *)
(*       destruct H0. *)
(*       split;eauto. *)
(*       rewrite -H0 /get_pagetable_gset. *)
(*       do 6 f_equal. *)
(*       rewrite /get_vm_page_table update_access_batch_preserve_other_page_tables //. *)
(*       destruct x. *)
(*       inversion H0. *)
(*         by subst. *)
(* Qed. *)

(* Lemma update_access_batch_update_access_diff{σ i sacc} {sps:gset PID} (ps: list PID): *)
(*  sps = (list_to_set ps)-> *)
(*  i = (get_current_vm σ) -> *)
(*  (get_access_gmap σ) !! i = Some sacc -> *)
(*  get_access_gmap (update_access_batch σ ps NoAccess) = *)
(*  <[(get_current_vm σ):= (sacc∖ sps)]>(get_access_gmap σ). *)
(* Proof. *)
(*   intros. *)
(*   apply (@update_access_batch_update_pagetable_diff _ i);eauto. *)
(* Qed. *)

(* Lemma update_access_batch_update_excl_diff{σ i sexcl p} {sps:gset PID} (ps: list PID): *)
(*  sps = (list_to_set ps)-> *)
(*  i = (get_current_vm σ) -> *)
(*  is_exclusive p = false ->                                               *)
(*  (get_excl_gmap σ) !! i = Some sexcl -> *)
(*  get_excl_gmap (update_access_batch σ ps p) = *)
(*  <[(get_current_vm σ):= (sexcl ∖ sps)]>(get_excl_gmap σ). *)
(* Proof. *)
(*   intros. *)
(*   apply (@update_access_batch_update_pagetable_diff _ i);eauto. *)
(* Qed. *)

(* Lemma update_ownership_batch_update_pagetable_union {σ i sown} {sps:gset PID} (ps: list PID): *)
(*  sps = (list_to_set ps)-> *)
(*  i = (get_current_vm σ)-> *)
(*  (get_owned_gmap σ) !! i = Some sown -> *)
(*  get_owned_gmap (update_ownership_batch σ ps Owned) = *)
(*  <[i:= sown ∪ sps]>(get_owned_gmap σ). *)
(* Proof. *)
(*   intros. *)
(*   rewrite /get_owned_gmap /get_pagetable_gmap. *)
(*   apply (@map_eq VMID (gmap VMID) _ _ _ _ _ _ _ _ gmap_finmap);eauto. *)
(*   intro. *)
(*   destruct(decide (i0 = i)). *)
(*   - subst i0. rewrite lookup_insert. *)
(*     assert(Hgoal: get_pagetable_gset (update_ownership_batch σ ps Owned) i (λ pt : page_table, pt.1) is_owned *)
(*                   = sown ∪ sps). *)
(*     { *)
(*       apply set_eq. *)
(*       intro. *)
(*       rewrite elem_of_list_to_set. *)
(*       split. *)
(*       * intros. *)
(*         inv_map_in. *)
(*         apply elem_of_list_In in H3. *)
(*         apply (elem_of_map_to_list' _ x0) in H3. *)
(*         apply map_filter_lookup_Some in H3. *)
(*         destruct H3. *)
(*         simplify_eq /=. *)
(*         rewrite /get_vm_page_table /get_page_tables /update_ownership_batch *)
(*                 /update_ownership_global_batch //= in H3. *)
(*         rewrite vlookup_insert in H3. *)
(*         apply elem_of_union. *)
(*         induction ps; simpl in *. *)
(*         -- left. *)
(*            apply (get_owned_gmap_is_owned x0.1 H1). *)
(*            exists (x0.2). *)
(*            split;eauto. *)
(*         -- destruct (decide (a=x0.1)). *)
(*            right;set_solver. *)
(*            assert (Himp :(x0.1 ∈ sown ∨ x0.1 ∈ ((list_to_set ps):gset PID)) *)
(*                          ->(x0.1 ∈ sown ∨ x0.1 ∈ {[a]} ∪ ((list_to_set ps):gset PID))). *)
(*            { intros. destruct H. left;done. right; set_solver. } *)
(*            apply Himp. *)
(*            apply IHps;eauto. *)
(*            rewrite lookup_insert_ne in H3;done. *)
(*       * intros. *)
(*         apply elem_of_union in H2. *)
(*         destruct H2. *)
(*         apply (get_owned_gmap_is_owned x H1) in H2;eauto. *)
(*         destruct H2. *)
(*         destruct H2. *)
(*         inv_map_in. *)
(*         exists (x,x0). *)
(*         split;eauto. *)
(*         apply elem_of_list_In . *)
(*         apply elem_of_map_to_list. *)
(*         apply map_filter_lookup_Some. *)
(*         rewrite /get_vm_page_table /get_page_tables /update_ownership_batch *)
(*                 /update_ownership_global_batch /=. *)
(*         rewrite -H0 vlookup_insert. *)
(*         destruct H1;split;eauto. *)
(*         generalize dependent sps. *)
(*         induction ps;simpl in *. *)
(*         done. *)
(*         intros. *)
(*         destruct (decide (x=a)). *)
(*         subst a. *)
(*         rewrite lookup_insert. *)
(*         rewrite /is_owned in H3. *)
(*         destruct x0;eauto. *)
(*         done. *)
(*         rewrite lookup_insert_ne;eauto. *)
(*         inv_map_in. *)
(*         exists (x,Owned). *)
(*         split;eauto. *)
(*         apply elem_of_list_In . *)
(*         apply elem_of_map_to_list. *)
(*         apply map_filter_lookup_Some. *)
(*         rewrite /get_vm_page_table /get_page_tables /update_ownership_batch *)
(*                 /update_ownership_global_batch /=. *)
(*         split;eauto. *)
(*         rewrite -H0 vlookup_insert //=. *)
(*         generalize dependent sps. *)
(*         induction ps;simpl in *. *)
(*         intros. *)
(*         set_solver. *)
(*         intros. *)
(*         destruct (decide (x=a)). *)
(*         subst a. *)
(*         rewrite lookup_insert //. *)
(*         rewrite lookup_insert_ne;eauto. *)
(*         apply (IHps (list_to_set ps));eauto. *)
(*         set_solver. *)
(*     } *)
(*     apply (@elem_of_list_to_map_1' VMID (gmap VMID) _ _ _ _ _ _ _ _ gmap_finmap). *)
(*     + intros. *)
(*       inv_map_in. *)
(*       inversion H2. *)
(*       do 3 f_equal. *)
(*       clear H6 H3 H2. *)
(*       subst x. *)
(*       symmetry. *)
(*       apply Hgoal. *)
(*     + inv_map_in. *)
(*       exists i. *)
(*       split;[|apply in_list_of_vmids]. *)
(*       do 4 f_equal. *)
(*       apply Hgoal. *)
(*   - rewrite (lookup_insert_ne _ i i0 _);eauto. *)
(*     set (l:= (map *)
(*                 (λ v, *)
(*                  (v, get_pagetable_gset (update_ownership_batch σ ps Owned) v (λ pt : page_table, pt.1) is_owned)) *)
(*                 list_of_vmids)) in *. *)
(*     destruct (list_to_map l !! i0) eqn:Heqn. *)
(*     + apply (elem_of_list_to_map_2 l i0 g) in Heqn. *)
(*       apply elem_of_list_In in Heqn. *)
(*       apply in_map_iff in Heqn. *)
(*       inversion Heqn;clear Heqn. *)
(*       destruct H2 as [H3 HIn];inversion H3;subst;clear H3. *)
(*       symmetry. *)
(*       apply elem_of_list_to_map_1'. *)
(*       *  intros. *)
(*          inv_map_in. *)
(*          inversion H. *)
(*          rewrite /get_pagetable_gset. *)
(*          do 5 f_equal. *)
(*          rewrite /get_vm_page_table update_ownership_batch_preserve_other_page_tables //. *)
(*       * inv_map_in. *)
(*         exists i0. *)
(*         split;eauto. *)
(*         rewrite /get_pagetable_gset. *)
(*         do 6 f_equal. *)
(*         rewrite /get_vm_page_table update_ownership_batch_preserve_other_page_tables //. *)
(*     + apply (@not_elem_of_list_to_map_2 VMID (gmap VMID) _ _ _ _ _ _ _ _ gmap_finmap) in Heqn. *)
(*       symmetry. *)
(*       apply not_elem_of_list_to_map_1. *)
(*       intro P. *)
(*       apply Heqn. *)
(*       apply elem_of_list_In. *)
(*       apply in_map_iff. *)
(*       apply elem_of_list_In in P. *)
(*       apply in_map_iff in P. *)
(*       destruct P. *)
(*       exists x. *)
(*       destruct H2. *)
(*       split;eauto. *)
(*       apply in_map_iff. *)
(*       apply in_map_iff in H3. *)
(*       destruct H3. *)
(*       exists x0. *)
(*       destruct H3. *)
(*       split;eauto. *)
(*       rewrite -H3 /get_pagetable_gset. *)
(*       do 6 f_equal. *)
(*       rewrite /get_vm_page_table update_ownership_batch_preserve_other_page_tables //. *)
(*       destruct x. *)
(*       simpl in H2;inversion H3. *)
(*         by subst. *)
(* Qed. *)

(* Lemma update_exclusive_batch_update_pagetable_union {σ i sexcl} {sps:gset PID} (ps: list PID): *)
(*  sps = (list_to_set ps) -> *)
(*  i = (get_current_vm σ) -> *)
(*  (get_excl_gmap σ) !! i = Some (sexcl) -> *)
(*  get_excl_gmap (update_access_batch σ ps ExclusiveAccess) = *)
(*  <[i:= (sexcl ∪ sps)]>(get_excl_gmap σ). *)
(* Proof. *)
(*   intros. *)
(*   rewrite /get_excl_gmap /get_pagetable_gmap. *)
(*   apply (@map_eq VMID (gmap VMID) _ _ _ _ _ _ _ _ gmap_finmap); eauto. *)
(*   intro. *)
(*   destruct(decide (i0 = i)). *)
(*   - subst i0. rewrite lookup_insert. *)
(*     assert(Hgoal: get_pagetable_gset (update_access_batch σ ps ExclusiveAccess) i (λ pt : page_table, pt.2) is_exclusive *)
(*                   = sexcl ∪ sps). *)
(*     { *)
(*       apply set_eq. *)
(*       intro. *)
(*       rewrite  elem_of_list_to_set. *)
(*       split. *)
(*       * intros. *)
(*         inv_map_in. *)
(*         apply elem_of_list_In in H3. *)
(*         apply (elem_of_map_to_list' _ x0) in H3. *)
(*         apply map_filter_lookup_Some in H3. *)
(*         destruct H3. *)
(*         simplify_eq /=. *)
(*         rewrite /get_vm_page_table /get_page_tables /update_access_batch *)
(*                 /update_access_global_batch //= in H3. *)
(*         rewrite vlookup_insert in H3. *)
(*         apply elem_of_union. *)
(*         induction ps; simpl in *. *)
(*         -- left. *)
(*            apply (get_excl_gmap_is_exclusive_true x0.1 H1). *)
(*            exists (x0.2). *)
(*            split;eauto. *)
(*         -- destruct (decide (a=x0.1)). *)
(*            right;set_solver. *)
(*            assert (Himp :(x0.1 ∈ sexcl ∨ x0.1 ∈ ((list_to_set ps):gset PID)) *)
(*                          ->(x0.1 ∈ sexcl ∨ x0.1 ∈ {[a]} ∪ ((list_to_set ps):gset PID))). *)
(*            { intros. destruct H. left;done. right; set_solver. } *)
(*            apply Himp. *)
(*            apply IHps;eauto. *)
(*            rewrite lookup_insert_ne in H3;done. *)
(*       * intros. *)
(*         apply elem_of_union in H2. *)
(*         destruct H2. *)
(*         apply (get_excl_gmap_is_exclusive_true x H1) in H2;eauto. *)
(*         destruct H2. *)
(*         destruct H2. *)
(*         inv_map_in. *)
(*         exists (x,x0). *)
(*         split;eauto. *)
(*         apply elem_of_list_In . *)
(*         apply elem_of_map_to_list. *)
(*         apply map_filter_lookup_Some. *)
(*         rewrite /get_vm_page_table /get_page_tables /update_access_batch *)
(*                 /update_access_global_batch /=. *)
(*         rewrite -H0 vlookup_insert. *)
(*         destruct H1;split;eauto. *)
(*         generalize dependent sps. *)
(*         induction ps;simpl in *. *)
(*         done. *)
(*         intros. *)
(*         destruct (decide (x=a)). *)
(*         subst a. *)
(*         rewrite lookup_insert. *)
(*         rewrite /is_exclusive in H3. *)
(*         destruct x0;try done. *)
(*         rewrite lookup_insert_ne;eauto. *)
(*         inv_map_in. *)
(*         exists (x, ExclusiveAccess). *)
(*         split;eauto. *)
(*         apply elem_of_list_In . *)
(*         apply elem_of_map_to_list. *)
(*         apply map_filter_lookup_Some. *)
(*         rewrite /get_vm_page_table /get_page_tables /update_access_batch *)
(*                 /update_access_global_batch /=. *)
(*         split;eauto. *)
(*         rewrite -H0 vlookup_insert //=. *)
(*         generalize dependent sps. *)
(*         induction ps;simpl in *. *)
(*         intros. *)
(*         set_solver. *)
(*         intros. *)
(*         destruct (decide (x=a)). *)
(*         subst a. *)
(*         rewrite lookup_insert //. *)
(*         rewrite lookup_insert_ne;eauto. *)
(*         apply (IHps (list_to_set ps));eauto. *)
(*         set_solver. *)
(*     } *)
(*     apply (@elem_of_list_to_map_1' VMID (gmap VMID) _ _ _ _ _ _ _ _ gmap_finmap). *)
(*     + intros. *)
(*       inv_map_in. *)
(*       inversion H2. *)
(*       do 3 f_equal. *)
(*       clear H6 H3 H2. *)
(*       subst x. *)
(*       symmetry. *)
(*       apply Hgoal. *)
(*     + inv_map_in. *)
(*       exists i. *)
(*       split;[|apply in_list_of_vmids]. *)
(*       do 4 f_equal. *)
(*       apply Hgoal. *)
(*   - rewrite (lookup_insert_ne _ i i0 _);eauto. *)
(*     set (l:= (map (λ v, (v, *)
(*                          get_pagetable_gset (update_access_batch σ ps ExclusiveAccess) v (λ pt : page_table, pt.2) is_exclusive)) *)
(*                   list_of_vmids)) in *. *)
(*     destruct (list_to_map l !! i0) eqn:Heqn. *)
(*     + apply (elem_of_list_to_map_2 l i0 g) in Heqn. *)
(*       apply elem_of_list_In in Heqn. *)
(*       apply in_map_iff in Heqn. *)
(*       inversion Heqn;clear Heqn. *)
(*       destruct H2 as [H3 HIn];inversion H3;subst;clear H3. *)
(*       symmetry. *)
(*       apply elem_of_list_to_map_1'. *)
(*       *  intros. *)
(*          inv_map_in. *)
(*          inversion H. *)
(*          rewrite /get_pagetable_gset. *)
(*          do 5 f_equal. *)
(*          rewrite /get_vm_page_table update_access_batch_preserve_other_page_tables //. *)
(*       * inv_map_in. *)
(*         exists i0. *)
(*         split;eauto. *)
(*         rewrite /get_pagetable_gset. *)
(*         do 6 f_equal. *)
(*         rewrite /get_vm_page_table update_access_batch_preserve_other_page_tables //. *)
(*     + apply (@not_elem_of_list_to_map_2 VMID (gmap VMID) _ _ _ _ _ _ _ _ gmap_finmap) in Heqn. *)
(*       symmetry. *)
(*       apply not_elem_of_list_to_map_1. *)
(*       intro P. *)
(*       apply Heqn. *)
(*       apply elem_of_list_In. *)
(*       apply in_map_iff. *)
(*       apply elem_of_list_In in P. *)
(*       apply in_map_iff in P. *)
(*       destruct P. *)
(*       exists x. *)
(*       destruct H2. *)
(*       split;eauto. *)
(*       apply in_map_iff. *)
(*       apply in_map_iff in H3. *)
(*       destruct H3. *)
(*       exists x0. *)
(*       destruct H3. *)
(*       split;eauto. *)
(*       rewrite -H3 /get_pagetable_gset. *)
(*       do 6 f_equal. *)
(*       rewrite /get_vm_page_table update_access_batch_preserve_other_page_tables //. *)
(*       destruct x. *)
(*       simpl in H2;inversion H3. *)
(*         by subst. *)
(* Qed. *)

(* Lemma update_access_batch_update_pagetable_union {σ i sacc a'} {sps:gset PID} (ps: list PID): *)
(*  sps = (list_to_set ps) -> *)
(*  i = (get_current_vm σ) -> *)
(*  (get_access_gmap σ) !! i = Some (sacc) -> *)
(*  sps ## sacc -> *)
(*  is_accessible a' = true -> *)
(*  get_access_gmap (update_access_batch σ ps a') = *)
(*  <[i:= (sacc ∪ sps)]>(get_access_gmap σ). *)
(* Proof. *)
(*   intros H H0 H1 P Q. *)
(*   rewrite /get_access_gmap /get_pagetable_gmap. *)
(*   apply (@map_eq VMID (gmap VMID) _ _ _ _ _ _ _ _ gmap_finmap); eauto. *)
(*   intro. *)
(*   destruct(decide (i0 = i)). *)
(*   - subst i0. rewrite lookup_insert. *)
(*     assert(Hgoal: get_pagetable_gset (update_access_batch σ ps a') i (λ pt : page_table, pt.2) is_accessible *)
(*                   = sacc ∪ sps). *)
(*     { *)
(*       apply set_eq. *)
(*       intro. *)
(*       rewrite elem_of_list_to_set. *)
(*       split. *)
(*       * intros. *)
(*         inv_map_in. *)
(*         apply elem_of_list_In in H3. *)
(*         apply (elem_of_map_to_list' _ x0) in H3. *)
(*         apply map_filter_lookup_Some in H3. *)
(*         destruct H3. *)
(*         simplify_eq /=. *)
(*         rewrite /get_vm_page_table /get_page_tables /update_access_batch *)
(*                 /update_access_global_batch //= in H3. *)
(*         rewrite vlookup_insert in H3. *)
(*         apply elem_of_union. *)
(*         induction ps; simpl in *. *)
(*         -- left. *)
(*            apply (get_access_gmap_is_accessible x0.1 H1). *)
(*            exists (x0.2). *)
(*            split;eauto. *)
(*         -- destruct (decide (a=x0.1)). *)
(*            right;set_solver. *)
(*            assert (Himp :(x0.1 ∈ sacc ∨ x0.1 ∈ ((list_to_set ps):gset PID)) *)
(*                          ->(x0.1 ∈ sacc ∨ x0.1 ∈ {[a]} ∪ ((list_to_set ps):gset PID))). *)
(*            { intros. destruct H. left;done. right; set_solver. } *)
(*            apply Himp. *)
(*            apply IHps;eauto. *)
(*            rewrite ->disjoint_union_l in P. *)
(*            destruct P; done. *)
(*            rewrite lookup_insert_ne in H3;done. *)
(*       * intros. *)
(*         apply elem_of_union in H2. *)
(*         destruct H2. *)
(*         pose proof H2 as H2'. *)
(*         apply (get_access_gmap_is_accessible x H1) in H2;eauto. *)
(*         destruct H2. *)
(*         destruct H2. *)
(*         inv_map_in. *)
(*         exists (x,x0). *)
(*         split;eauto. *)
(*         apply elem_of_list_In . *)
(*         apply elem_of_map_to_list. *)
(*         apply map_filter_lookup_Some. *)
(*         rewrite /get_vm_page_table /get_page_tables /update_access_batch *)
(*                 /update_access_global_batch /=. *)
(*         rewrite -H0 vlookup_insert. *)
(*         destruct H1;split;eauto. *)
(*         simpl. *)
(*         generalize dependent sps. *)
(*         induction ps;simpl in *. *)
(*         done. *)
(*         intros. *)
(*         destruct (decide (x=a)). *)
(*         subst a. *)
(*         rewrite lookup_insert. *)
(*         rewrite /is_accessible in H3. *)
(*         destruct x0;try done. *)
(*         rewrite ->elem_of_disjoint in P. *)
(*         exfalso. *)
(*         apply P with x; set_solver. *)
(*         rewrite ->elem_of_disjoint in P. *)
(*         exfalso. *)
(*         apply P with x; set_solver. *)
(*         rewrite lookup_insert_ne; eauto. *)
(*         apply IHps with (list_to_set ps); auto. *)
(*         apply disjoint_union_l with {[a]}. *)
(*         rewrite H in P; auto. *)
(*         inv_map_in. *)
(*         exists (x, a'). *)
(*         split;eauto. *)
(*         apply elem_of_list_In . *)
(*         apply elem_of_map_to_list. *)
(*         apply map_filter_lookup_Some. *)
(*         rewrite /get_vm_page_table /get_page_tables /update_access_batch *)
(*                 /update_access_global_batch /=. *)
(*         split;eauto. *)
(*         rewrite -H0 vlookup_insert //=. *)
(*         generalize dependent sps. *)
(*         induction ps;simpl in *. *)
(*         intros. *)
(*         set_solver. *)
(*         intros. *)
(*         destruct (decide (x=a)). *)
(*         subst a. *)
(*         rewrite lookup_insert //. *)
(*         rewrite lookup_insert_ne;eauto. *)
(*         apply (IHps (list_to_set ps));eauto. *)
(*         set_solver. *)
(*         set_solver. *)
(*     } *)
(*     apply (@elem_of_list_to_map_1' VMID (gmap VMID) _ _ _ _ _ _ _ _ gmap_finmap). *)
(*     + intros. *)
(*       inv_map_in. *)
(*       inversion H2. *)
(*       do 3 f_equal. *)
(*       clear H6 H3 H2. *)
(*       subst x. *)
(*       symmetry. *)
(*       apply Hgoal. *)
(*     + inv_map_in. *)
(*       exists i. *)
(*       split;[|apply in_list_of_vmids]. *)
(*       do 4 f_equal. *)
(*       apply Hgoal. *)
(*   - rewrite (lookup_insert_ne _ i i0 _);eauto. *)
(*     set (l:= (map (λ v, *)
(*                    (v, get_pagetable_gset (update_access_batch σ ps a') v (λ pt : page_table, pt.2) is_accessible)) *)
(*                   list_of_vmids)) in *. *)
(*     destruct (list_to_map l !! i0) eqn:Heqn. *)
(*     + apply (elem_of_list_to_map_2 l i0 g) in Heqn. *)
(*       apply elem_of_list_In in Heqn. *)
(*       apply in_map_iff in Heqn. *)
(*       inversion Heqn;clear Heqn. *)
(*       destruct H2 as [H3 HIn];inversion H3;subst;clear H3. *)
(*       symmetry. *)
(*       apply elem_of_list_to_map_1'. *)
(*       *  intros. *)
(*          inv_map_in. *)
(*          inversion H. *)
(*          rewrite /get_pagetable_gset. *)
(*          do 5 f_equal. *)
(*          rewrite /get_vm_page_table update_access_batch_preserve_other_page_tables //. *)
(*       * inv_map_in. *)
(*         exists i0. *)
(*         split;eauto. *)
(*         rewrite /get_pagetable_gset. *)
(*         do 6 f_equal. *)
(*         rewrite /get_vm_page_table update_access_batch_preserve_other_page_tables //. *)
(*     + apply (@not_elem_of_list_to_map_2 VMID (gmap VMID) _ _ _ _ _ _ _ _ gmap_finmap) in Heqn. *)
(*       symmetry. *)
(*       apply not_elem_of_list_to_map_1. *)
(*       intro R. *)
(*       apply Heqn. *)
(*       apply elem_of_list_In. *)
(*       apply in_map_iff. *)
(*       apply elem_of_list_In in R. *)
(*       apply in_map_iff in R. *)
(*       destruct R. *)
(*       exists x. *)
(*       destruct H2. *)
(*       split;eauto. *)
(*       apply in_map_iff. *)
(*       apply in_map_iff in H3. *)
(*       destruct H3. *)
(*       exists x0. *)
(*       destruct H3. *)
(*       split;eauto. *)
(*       rewrite -H3 /get_pagetable_gset. *)
(*       do 6 f_equal. *)
(*       rewrite /get_vm_page_table update_access_batch_preserve_other_page_tables //. *)
(*       destruct x. *)
(*       simpl in H2;inversion H3. *)
(*         by subst. *)
(* Qed. *)

(* Lemma update_access_batch_update_pagetable_idempotent {σ i sacc a'} {sps:gset PID} (ps: list PID): *)
(*  sps = (list_to_set ps) -> *)
(*  i = (get_current_vm σ) -> *)
(*  (get_access_gmap σ) !! i = Some (sacc) -> *)
(*  sps ⊆ sacc -> *)
(*  is_accessible a' = true -> *)
(*  get_access_gmap (update_access_batch σ ps a') = *)
(*  (get_access_gmap σ). *)
(* Proof. *)
(*   intros H H0 H1 P Q. *)
(*   rewrite /get_access_gmap /get_pagetable_gmap. *)
(*   apply (@map_eq VMID (gmap VMID) _ _ _ _ _ _ _ _ gmap_finmap); eauto. *)
(*   rewrite /get_access_gmap /get_pagetable_gmap in H1. *)
(*   intro. *)
(*   destruct(decide (i0 = i)). *)
(*   - subst i0. *)
(*     rewrite H1.   *)
(*     assert(Hgoal: get_pagetable_gset (update_access_batch σ ps a') i (λ pt : page_table, pt.2) is_accessible *)
(*                   = sacc). *)
(*     { *)
(*       apply set_eq. *)
(*       intro. *)
(*       rewrite elem_of_list_to_set. *)
(*       split. *)
(*       * intros. *)
(*         inv_map_in. *)
(*         apply elem_of_list_In in H3. *)
(*         apply (elem_of_map_to_list' _ x0) in H3. *)
(*         apply map_filter_lookup_Some in H3. *)
(*         destruct H3. *)
(*         simplify_eq /=. *)
(*         rewrite /get_vm_page_table /get_page_tables /update_access_batch *)
(*                 /update_access_global_batch //= in H3. *)
(*         rewrite vlookup_insert in H3. *)
(*         induction ps; simpl in *. *)
(*         -- apply (get_access_gmap_is_accessible x0.1 H1). *)
(*            exists (x0.2). *)
(*            split;eauto. *)
(*         -- destruct (decide (a=x0.1)). *)
(*            set_solver. *)
(*            apply IHps;eauto. *)
(*            set_solver. *)
(*            rewrite lookup_insert_ne in H3;done. *)
(*       * intros. *)
(*         apply (get_access_gmap_is_accessible x H1) in H2;eauto. *)
(*         destruct H2. *)
(*         destruct H2. *)
(*         destruct (decide (x0=a')). *)
(*         -- subst x0. *)
(*            inv_map_in. *)
(*            exists (x,a'). *)
(*            split;eauto. *)
(*            apply elem_of_list_In . *)
(*            apply elem_of_map_to_list. *)
(*            apply map_filter_lookup_Some. *)
(*            rewrite /get_vm_page_table /get_page_tables /update_access_batch *)
(*                    /update_access_global_batch /=. *)
(*            rewrite -H0 vlookup_insert. *)
(*            destruct H1;split;eauto. *)
(*            simpl. *)
(*            generalize dependent sps. *)
(*            induction ps;simpl in *. *)
(*            done. *)
(*            intros. *)
(*            destruct (decide (x=a)). *)
(*            subst a. *)
(*            rewrite lookup_insert. *)
(*            reflexivity. *)
(*            rewrite lookup_insert_ne; eauto. *)
(*            apply IHps with (list_to_set ps); auto. *)
(*            rewrite H in P. *)
(*            rewrite ->union_subseteq in P. *)
(*            destruct P; auto. *)
(*         -- inv_map_in. *)
(*            destruct (decide (x ∈ ps)). *)
(*            ++ exists (x, a'). *)
(*               split; auto. *)
(*               apply elem_of_list_In. *)
(*               apply elem_of_map_to_list'. *)
(*               apply map_filter_lookup_Some. *)
(*               split; auto. *)
(*               simpl. *)
(*               rewrite /update_access_batch /update_access_global_batch /get_vm_page_table /get_page_tables. *)
(*               simpl. *)
(*               rewrite H0. *)
(*               rewrite <-H0. *)
(*               rewrite /get_vm_page_table /get_page_tables in H2. *)
(*               rewrite vlookup_insert. *)
(*               simpl. *)
(*               generalize dependent sps. *)
(*               induction ps;simpl in *. *)
(*               set_solver. *)
(*               intros. *)
(*               destruct (decide (a = x)). *)
(*               - subst a. *)
(*                 apply lookup_insert. *)
(*               - rewrite lookup_insert_ne; auto. *)
(*                 apply IHps with (list_to_set ps); auto. *)
(*                 set_solver. *)
(*                 rewrite H in P. *)
(*                 rewrite ->union_subseteq in P. *)
(*                 destruct P; auto. *)
(*            ++ exists (x, x0). *)
(*               split; auto. *)
(*               apply elem_of_list_In. *)
(*               apply elem_of_map_to_list'. *)
(*               apply map_filter_lookup_Some. *)
(*               split; auto. *)
(*               simpl. *)
(*               rewrite /update_access_batch /update_access_global_batch /get_vm_page_table /get_page_tables. *)
(*               simpl. *)
(*               rewrite H0. *)
(*               rewrite <-H0. *)
(*               rewrite /get_vm_page_table /get_page_tables in H2. *)
(*               rewrite vlookup_insert. *)
(*               simpl. *)
(*               generalize dependent sps. *)
(*               induction ps;simpl in *. *)
(*               set_solver. *)
(*               intros. *)
(*               destruct (decide (a = x)). *)
(*               - subst a. *)
(*                 set_solver. *)
(*               - rewrite lookup_insert_ne; auto. *)
(*                 apply IHps with (list_to_set ps); auto. *)
(*                 set_solver. *)
(*                 rewrite H in P. *)
(*                 rewrite ->union_subseteq in P. *)
(*                 destruct P; auto. *)
(*     } *)
(*     apply (@elem_of_list_to_map_1' VMID (gmap VMID) _ _ _ _ _ _ _ _ gmap_finmap). *)
(*     + intros. *)
(*       inv_map_in. *)
(*       inversion H2. *)
(*       subst x. *)
(*       symmetry. *)
(*       apply Hgoal. *)
(*     + inv_map_in. *)
(*       exists i. *)
(*       split;[|apply in_list_of_vmids]. *)
(*       do 4 f_equal. *)
(*       apply Hgoal. *)
(*   - set (l:= (map (λ v, *)
(*                    (v, get_pagetable_gset (update_access_batch σ ps a') v (λ pt : page_table, pt.2) is_accessible)) *)
(*                   list_of_vmids)) in *. *)
(*     destruct (list_to_map l !! i0) eqn:Heqn. *)
(*     + apply (elem_of_list_to_map_2 l i0 g) in Heqn. *)
(*       apply elem_of_list_In in Heqn. *)
(*       apply in_map_iff in Heqn. *)
(*       inversion Heqn;clear Heqn. *)
(*       destruct H2 as [H3 HIn];inversion H3;subst;clear H3. *)
(*       symmetry. *)
(*       apply elem_of_list_to_map_1'. *)
(*       *  intros. *)
(*          inv_map_in. *)
(*          inversion H. *)
(*          rewrite /get_pagetable_gset. *)
(*          do 5 f_equal. *)
(*          rewrite /get_vm_page_table update_access_batch_preserve_other_page_tables //. *)
(*       * inv_map_in. *)
(*         exists i0. *)
(*         split;eauto. *)
(*         rewrite /get_pagetable_gset. *)
(*         do 6 f_equal. *)
(*         rewrite /get_vm_page_table update_access_batch_preserve_other_page_tables //. *)
(*     + apply (@not_elem_of_list_to_map_2 VMID (gmap VMID) _ _ _ _ _ _ _ _ gmap_finmap) in Heqn. *)
(*       symmetry. *)
(*       apply not_elem_of_list_to_map_1. *)
(*       intro R. *)
(*       apply Heqn. *)
(*       apply elem_of_list_In. *)
(*       apply in_map_iff. *)
(*       apply elem_of_list_In in R. *)
(*       apply in_map_iff in R. *)
(*       destruct R. *)
(*       exists x. *)
(*       destruct H2. *)
(*       split;eauto. *)
(*       apply in_map_iff. *)
(*       apply in_map_iff in H3. *)
(*       destruct H3. *)
(*       exists x0. *)
(*       destruct H3. *)
(*       split;eauto. *)
(*       rewrite -H3 /get_pagetable_gset. *)
(*       do 6 f_equal. *)
(*       rewrite /get_vm_page_table update_access_batch_preserve_other_page_tables //. *)
(*       destruct x. *)
(*       simpl in H2;inversion H3. *)
(*         by subst. *)
(* Qed. *)


End pagetable_extra.

Ltac rewrite_ownership_all :=
  match goal with
  | |- _ =>
    try rewrite -> update_ownership_batch_preserve_current_vm;
    try rewrite -> update_ownership_batch_preserve_regs;
    try rewrite -> update_ownership_batch_preserve_mem;
    try rewrite -> update_ownership_batch_preserve_mb;
    try rewrite -> update_ownership_batch_preserve_rx;
    try rewrite -> update_ownership_batch_preserve_trans;
    try rewrite -> update_ownership_batch_preserve_trans';
    try rewrite -> update_ownership_batch_preserve_hpool;
    try rewrite -> update_ownership_batch_preserve_retri
  end.

Ltac rewrite_access_all :=
  match goal with
  | |- _ =>
    try rewrite -> update_access_batch_preserve_current_vm;
    try rewrite -> update_access_batch_preserve_regs;
    try rewrite -> update_access_batch_preserve_mem;
    try rewrite -> update_access_batch_preserve_mb;
    try rewrite -> update_access_batch_preserve_rx;
    try rewrite -> update_access_batch_preserve_trans;
    try rewrite -> update_access_batch_preserve_trans';
    try rewrite -> update_access_batch_preserve_hpool;
    try rewrite -> update_access_batch_preserve_retri
  end.
