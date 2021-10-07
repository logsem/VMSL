From iris.base_logic.lib Require Import gen_heap ghost_map.
From HypVeri.algebra Require Import base.

Section pagetable_rules.

  Context `{vmG :gen_VMG Σ}.

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


  Lemma gen_pagetable_SepM_split1 {Perm: Type} {σ γ} i (proj: page_table -> gmap PID Perm)
        (checkb: Perm -> bool):
   ([∗ map] k↦v ∈ (get_pagetable_gmap σ proj checkb ), ghost_map_elem γ k (dfrac.DfracOwn 1) v)%I -∗
   ghost_map_elem γ i (dfrac.DfracOwn 1) (get_pagetable_gset σ i proj checkb) ∗
   [∗ map] k↦v ∈ (delete i (get_pagetable_gmap σ proj checkb)), ghost_map_elem γ k (dfrac.DfracOwn 1) v.
  Proof.
    iIntros "Hall".
    iApply ((big_sepM_delete _ (get_pagetable_gmap σ proj checkb) i
                             (get_pagetable_gset σ i proj checkb)) with "Hall").
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

  Lemma gen_pagetable_SepM_split2 {Perm: Type} {σ γ} i j (proj: page_table -> gmap PID Perm)
        (checkb: Perm -> bool):
   i ≠ j ->
   ([∗ map] k↦v ∈ (get_pagetable_gmap σ proj checkb ), ghost_map_elem γ k (dfrac.DfracOwn 1) v)%I -∗
   ghost_map_elem γ i (dfrac.DfracOwn 1) (get_pagetable_gset σ i proj checkb) ∗
   ghost_map_elem γ j (dfrac.DfracOwn 1) (get_pagetable_gset σ j proj checkb) ∗
   [∗ map] k↦v ∈ (delete j (delete i (get_pagetable_gmap σ proj checkb))),
                  ghost_map_elem γ k (dfrac.DfracOwn 1) v.
  Proof.
    iIntros (Hne) "Hall".
    iDestruct ((gen_pagetable_SepM_split1 i) with "Hall") as "[Hi Hrest]".
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

  Lemma gen_pagetable_valid_pure{Perm: Type} {σ i q γ} proj (checkb: Perm -> bool) (s:gset PID):
   ghost_map_auth γ 1 (get_pagetable_gmap σ proj checkb)  -∗
   ghost_map_elem γ i (DfracOwn q) s -∗
   ⌜(get_pagetable_gmap σ proj checkb) !! i = Some s ⌝.
  Proof.
    iIntros  "Hσ Hpt".
    iApply (ghost_map_lookup with "Hσ Hpt").
  Qed.

  Lemma gen_access_valid_pure {σ i q} s:
   ghost_map_auth (gen_access_name vmG) 1 (get_access_gmap σ) -∗
   (A@ i :={q}[s] ) -∗
   ⌜(get_access_gmap σ) !! i = Some s⌝.
  Proof.
    iIntros  "Hσ Hacc".
    rewrite access_mapsto_eq /access_mapsto_def.
    iApply (gen_pagetable_valid_pure with "Hσ Hacc").
  Qed.

  Lemma gen_excl_valid_pure {σ i q} s:
   ghost_map_auth (gen_excl_name vmG) 1 (get_excl_gmap σ) -∗
   (E@ i :={q}[s] ) -∗
   ⌜(get_excl_gmap σ) !! i = Some s⌝.
  Proof.
    iIntros "Hσ Hexcl".
    rewrite excl_mapsto_eq /excl_mapsto_def.
    iApply (gen_pagetable_valid_pure with "Hσ Hexcl").
  Qed.

  Lemma gen_own_valid_pure {σ i q} s:
   ghost_map_auth (gen_owned_name vmG) 1 (get_owned_gmap σ) -∗
   (O@ i :={q}[s] ) -∗
   ⌜(get_owned_gmap σ) !! i = Some s⌝.
  Proof.
    iIntros  "Hσ Hown".
    rewrite owned_mapsto_eq /owned_mapsto_def.
    iApply (gen_pagetable_valid_pure with "Hσ Hown").
  Qed.

  Lemma gen_pagetable_valid_SepS_pure {Perm: Type} {σ i q γ} proj (checkb: Perm -> bool) (s:gset PID):
   ghost_map_auth γ 1 (get_pagetable_gmap σ proj checkb) -∗
   ghost_map_elem γ i (DfracOwn q) s -∗
   ([∗ set]  p ∈ s, ∃ perm, ⌜(proj (get_vm_page_table σ i)) !! p =Some perm ∧ checkb perm = true⌝).
  Proof.
    iIntros "Hσ Hpt".
    iDestruct (gen_pagetable_valid_pure with "Hσ Hpt") as %Hvalid.
    iPureIntro.
    apply (elem_of_list_to_map_2 _ i s) in Hvalid.
    apply elem_of_list_In in Hvalid.
    apply in_map_iff in Hvalid.
    destruct Hvalid as [? [Heqp _]].
    inversion Heqp;subst;clear Heqp.
    intros p Hin.
    apply elem_of_list_to_set in Hin.
    apply elem_of_list_In in Hin.
    apply (in_map_iff _ _ p) in Hin.
    destruct Hin as [? [<- Hin]].
    rewrite <- elem_of_list_In in Hin.
    apply elem_of_map_to_list' in Hin.
    apply map_filter_lookup_Some in Hin.
    destruct Hin.
    exists x.2.
    done.
  Qed.

  Lemma gen_own_valid_SepS_pure {σ i q} (s:gset PID):
   ghost_map_auth (gen_owned_name vmG) 1 (get_owned_gmap σ) -∗
   (O@ i :={q}[s]) -∗
   ([∗ set] p ∈ s, ∃ perm, ⌜(get_vm_page_table σ i).1 !! p =Some perm ∧ is_owned perm = true⌝).
  Proof.
    iIntros "Hσ Hown".
    rewrite owned_mapsto_eq /owned_mapsto_def /get_owned_gmap.
    iApply (gen_pagetable_valid_SepS_pure with "Hσ Hown").
  Qed.

  Lemma gen_access_valid_SepS_pure {σ i q} (s:gset PID):
   ghost_map_auth (gen_access_name vmG) 1 (get_access_gmap σ) -∗
   (A@ i :={q}[s]) -∗
   ([∗ set] p ∈ s, ∃ perm, ⌜(get_vm_page_table σ i).2 !! p =Some perm ∧ is_accessible perm = true⌝).
  Proof.
    iIntros "Hσ Hacc".
    rewrite access_mapsto_eq /access_mapsto_def /get_access_gmap.
    iApply (gen_pagetable_valid_SepS_pure with "Hσ Hacc").
  Qed.

  Lemma gen_excl_valid_SepS_pure {σ i q} (s:gset PID):
   ghost_map_auth (gen_excl_name vmG) 1 (get_excl_gmap σ) -∗
   (E@ i :={q}[s]) -∗
   ([∗ set] p ∈ s, ∃ perm, ⌜(get_vm_page_table σ i).2 !! p =Some perm ∧ is_exclusive perm = true⌝).
  Proof.
    iIntros "Hσ Hexcl".
    rewrite excl_mapsto_eq /excl_mapsto_def /get_excl_gmap.
    iApply (gen_pagetable_valid_SepS_pure with "Hσ Hexcl").
  Qed.

  Lemma gen_access_valid_SepS_check {σ i q} s:
   ghost_map_auth (gen_access_name vmG) 1 (get_access_gmap σ) -∗
   (A@ i :={q}[s]) -∗
   ([∗ set] p ∈ s, ⌜(check_access_page' σ i p)= true⌝).
  Proof.
    iIntros "Hσ Hacc".
    rewrite access_mapsto_eq /access_mapsto_def.
    iDestruct (gen_pagetable_valid_SepS_pure with "Hσ Hacc") as %Hvalid.
    iPureIntro.
    intros p Hin.
    unfold check_access_page'.
    pose proof (Hvalid p Hin) as [? [Hlk Hisa]].
    rewrite Hlk /= //.
  Qed.

  Lemma gen_access_valid {σ i q} p:
   ghost_map_auth (gen_access_name vmG) 1 (get_access_gmap σ) -∗
   (A@ i :={q}p) -∗
   ⌜(check_access_page' σ i p)= true⌝.
  Proof.
    iIntros "Hσ Hacc".
    iDestruct (gen_access_valid_SepS_check {[p]} with "Hσ Hacc") as %->;eauto.
    set_solver.
  Qed.

  Lemma gen_access_valid2 {σ i q} s p1 p2:
   {[p1;p2]} ⊆ s ->
   ghost_map_auth (gen_access_name vmG) 1 (get_access_gmap σ) -∗
   (A@ i :={q}[s] ) -∗
   ⌜(check_access_page' σ i p1)= true⌝ ∗ ⌜(check_access_page' σ i p2) = true⌝.
  Proof.
    iIntros (Hsubset) "Hσ Hacc".
    iDestruct (gen_access_valid_SepS_check s with "Hσ Hacc") as %Hcheck;eauto.
    iPureIntro.
    split.
    - apply (Hcheck p1).
      set_solver.
    - apply (Hcheck p2).
      set_solver.
  Qed.

  Lemma gen_access_valid_addr {σ i q} a p:
   addr_in_page a p ->
   ghost_map_auth (gen_access_name vmG) 1 (get_access_gmap σ) -∗
   (A@ i :={q} p ) -∗
   ⌜(check_access_addr σ i a)= true⌝.
  Proof.
    iIntros (HIn) "Haccess Hacc".
    iDestruct (gen_access_valid p with "Haccess Hacc") as %Hacc.
    iPureIntro.
    unfold check_access_addr.
    apply to_pid_aligned_in_page in HIn.
    rewrite HIn //=.
  Qed.

  Lemma gen_access_valid_addr_Set {σ i q} a s:
   (to_pid_aligned a) ∈ s ->
   ghost_map_auth (gen_access_name vmG) 1 (get_access_gmap σ) -∗
   (A@ i :={q}[s] ) -∗
   ⌜(check_access_addr σ i a)= true⌝.
  Proof.
    iIntros (HaIn) "Haccess Hacc".
    iDestruct (gen_access_valid_SepS_pure with "Haccess Hacc") as %Hacc.
    iPureIntro.
    unfold check_access_addr.
    (* apply to_pid_aligned_in_page in HaIn. *)
    rewrite /check_access_page'.
    pose proof (Hacc (to_pid_aligned a) HaIn) as [? [-> Hisa]].
    done.
  Qed.

  Lemma gen_access_valid_addr_elem {σ i q} a s:
   to_pid_aligned a ∈ s ->
   ghost_map_auth (gen_access_name vmG) 1 (get_access_gmap σ) -∗
   (A@ i :={q}[s] ) -∗
   ⌜(check_access_addr σ i a)= true⌝.
  Proof.
    iIntros (Hin) "Haccess Hacc".
    iDestruct (gen_access_valid_SepS_check s with "Haccess Hacc") as %Hacc.
    iPureIntro.
    apply (Hacc (to_pid_aligned a));auto.
  Qed.

  Lemma gen_access_valid_addr2 {σ i q } a1 a2 s:
   s = {[(to_pid_aligned a1); (to_pid_aligned a2)]} ->
   ghost_map_auth (gen_access_name vmG) 1 (get_access_gmap σ) -∗
   (A@ i :={q}[s]) -∗
   ⌜(check_access_addr σ i a1) = true⌝ ∗ ⌜(check_access_addr σ i a2) = true⌝.
  Proof.
    iIntros (Heqs) "Haccess Hacc".
    iDestruct (gen_access_valid_SepS_check s with "Haccess Hacc") as %Hacc.
    iPureIntro.
    split.
    apply (Hacc (to_pid_aligned a1)).
    set_solver.
    apply (Hacc (to_pid_aligned a2)).
    set_solver.
  Qed.

  Lemma gen_access_valid_not {σ i} p s:
   p ∉ s ->
   ghost_map_auth (gen_access_name vmG) 1 (get_access_gmap σ) -∗
   (A@ i :={1}[s]) -∗
   ⌜(check_access_page' σ i p)= false⌝.
  Proof.
    iIntros (Hnin) "Hσ Hacc".
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
    apply not_elem_of_list_to_set in Hnin.
    rewrite /get_page_tables.
    rewrite /get_vm_page_table /get_page_tables in Hnin.
    destruct ((σ.1.1.1.2 !!! i).2 !! p) eqn:Heq.
    rewrite Heq /=.
    destruct (is_accessible a) eqn:Heqn'; try done.
    exfalso.
    apply Hnin.
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

  Lemma gen_pagetable_update_union {Perm: Type} {σ i γ s ps} proj (checkb: Perm -> bool) sps:
   sps = (list_to_set ps) ->
   ghost_map_elem γ i (DfracOwn 1)  s -∗
   ghost_map_auth γ 1 (get_pagetable_gmap σ proj checkb) ==∗
   ghost_map_auth γ 1 (<[i:= s ∪ sps]>(get_pagetable_gmap σ proj checkb)) ∗
   ghost_map_elem γ i (DfracOwn 1)  (s ∪ sps).
  Proof.
    iIntros (Hsps) "Hpt Hσ".
    iApply ((ghost_map_update (s ∪ sps)) with "Hσ Hpt").
  Qed.

  Lemma gen_access_update_union{σ i sacc psd} sps:
   sps = (list_to_set psd) ->
   A@i:={1}[sacc] -∗
   ghost_map_auth (gen_access_name vmG) 1 (get_access_gmap σ)==∗
   ghost_map_auth (gen_access_name vmG) 1 (<[i:= (sacc ∪ sps)]>(get_access_gmap σ)) ∗
   A@i:={1}[sacc ∪ sps].
  Proof.
    iIntros (Hsps) "HA Hacc".
    rewrite access_mapsto_eq /access_mapsto_def.
    iApply (gen_pagetable_update_union with "HA Hacc");eauto.
  Qed.

  Lemma gen_own_update_union{σ i sown psd} sps:
   sps = (list_to_set psd) ->
   O@i:={1}[sown] -∗
   ghost_map_auth (gen_owned_name vmG) 1 (get_owned_gmap σ)==∗
   ghost_map_auth (gen_owned_name vmG) 1 (<[i:= (sown ∪ sps)]>(get_owned_gmap σ)) ∗
   O@i:={1}[sown ∪ sps].
  Proof.
    iIntros (Hsps) "HO Hown".
    rewrite owned_mapsto_eq /owned_mapsto_def.
    iApply (gen_pagetable_update_union with "HO Hown");eauto.
  Qed.

  Lemma gen_excl_update_union{σ i sexcl psd} sps:
   sps = (list_to_set psd) ->
   E@i:={1}[sexcl] -∗
   ghost_map_auth (gen_excl_name vmG) 1 (get_excl_gmap σ)==∗
   ghost_map_auth (gen_excl_name vmG) 1 (<[i:= (sexcl ∪ sps)]>(get_excl_gmap σ)) ∗
   E@i:={1}[sexcl ∪ sps].
  Proof.
    iIntros (Hsps) "HE Hexcl".
    rewrite excl_mapsto_eq /excl_mapsto_def.
    iApply (gen_pagetable_update_union with "HE Hexcl");eauto.
  Qed.

End pagetable_rules.
