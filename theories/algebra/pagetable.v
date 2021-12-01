From iris.base_logic.lib Require Import gen_heap ghost_map.
From HypVeri.algebra Require Import base.

Section pagetable_rules.

  Context `{vmG :gen_VMG Σ}.

  (** properties of the pagetable RA **)

  (* owned *)
  Lemma owned_ne p1 p2 (v1 v2 : VMID):
   O@p1:=v1 ∗ O@p2:=v2 -∗ ⌜p1 ≠ p2⌝ .
  Proof using.
    iIntros "[HO1 HO2]".
    rewrite owned_mb_mapsto_eq /owned_mb_mapsto_def.
    destruct (decide (p1 = p2)).
    { subst p2.
      iDestruct (ghost_map_elem_valid_2 with "HO1 HO2") as "[%Hvalid _]".
      apply dfrac_valid_own_l in Hvalid.
      inversion Hvalid.
    }
    done.
  Qed.

  Lemma owned_agree {σ q γ} p s:
   ghost_map_auth γ 1 (get_owned_gmap σ)  -∗
   ghost_map_elem γ p (DfracOwn q) s -∗
   ⌜(get_owned_gmap σ) !! p = Some s ⌝.
  Proof.
    iIntros  "Hσ Hpt".
    iApply (ghost_map_lookup with "Hσ Hpt").
  Qed.

  (* access *)

  Lemma access_split_set_union {p} q1 q2 (s1 s2 : gset VMID):
   s1 ## s2 ->
   A@p:={(q1+q2)%Qp} [s1 ∪ s2] -∗ A@p:={q1} [s1] ∗ A@p:={q2} [s2].
  Proof using.
    iIntros (Hdisj) "HO".
    rewrite access_mapsto_eq /access_mapsto_def.
    iApply own_op.
    rewrite -auth_frag_op singleton_op.
    rewrite -pair_op.
    rewrite (gset_disj_union _ _ Hdisj).
    naive_solver.
  Qed.

  Lemma access_split_set_diff {p} q1 q2 (s1 s2 : gset VMID):
   s2 ⊆ s1 -> A@p:={(q1+q2)%Qp} [s1] -∗ A@p:={q1} [s2] ∗ A@p:={q2} [s1 ∖ s2].
  Proof using.
    iIntros (Hsub) "HO".
    rewrite access_mapsto_eq.
    iApply own_op.
    rewrite -auth_frag_op singleton_op.
    rewrite -pair_op.
    rewrite (gset_disj_union _ _);
    last set_solver+ .
    rewrite -(union_difference_L _ _ Hsub).
    naive_solver.
  Qed.

  (** relations between get_access_gmap and the opsem **)
  Lemma opsem_access_lookup {σ} {s:gset VMID} (p:PID):
  (get_access_gmap σ) !! p = Some (1%Qp, (GSet s)) ->
  ∃ j, (get_page_table σ) !! p = Some(j, s).
  Proof.
    rewrite /get_access_gmap.
    rewrite lookup_fmap_Some.
    intros [? [Helem Hlookup]].
    inversion Helem.
    subst.
    exists x.1.
    destruct x;done.
  Qed.

  (** agreement (RA -> opsem) **)

  (* single pt *)

  Lemma access_agree {σ γ} (p:PID) q s:
   own γ (● (get_access_gmap σ)) -∗
   own γ (◯ {[p := (q, (GSet s))]}) -∗
   ⌜∃ s', (get_access_gmap σ) !! p = Some (1%Qp, (GSet s')) ∧ s ⊆ s' ⌝.
  Proof.
    iIntros  "Hσ Hpt".
    iDestruct (own_valid_2 with "Hσ Hpt") as "%Hvalid".
    setoid_rewrite auth_both_valid_discrete in Hvalid.
    destruct Hvalid as [Hvalid1 Hvalid2].
    apply singleton_included_l in Hvalid1.
    destruct Hvalid1 as [y [Hvalid1 Hvalid1']].
    apply option_included in Hvalid1'.
    destruct Hvalid1' as [? | Hvalid1']; first done.
    destruct Hvalid1' as [Hvalid1' Hvalid1''].
    destruct Hvalid1'' as [b [? [? Hvalid1'']]].
    simplify_eq.
    iPureIntro.
    destruct b as [b1 b2].
    destruct b2 as [b' |].
    - exists b'.
      split.
      + rewrite Hvalid1.
        assert (b1 = 1%Qp) as ->.
        {
          unfold get_access_gmap in Hvalid1.
          apply lookup_fmap_Some in Hvalid1.
          destruct Hvalid1 as [Hvalid1 [Hvalid1' Hvalid1''']].
          simplify_eq.
          reflexivity.
        }
        reflexivity.
      + destruct Hvalid1'' as [Hvalid1'' | Hvalid1''].
        * simplify_eq.
          done.
        * apply pair_included in Hvalid1'' as [_ Hvalid1''].
          apply gset_disj_included in Hvalid1''.
          done.
    - destruct Hvalid1'' as [Hvalid1'' | Hvalid1''].
      + simplify_eq.
      + apply (lookup_valid_Some (get_access_gmap σ) p (b1, GSetBot)) in Hvalid2; rewrite Hvalid1; last done.
        apply pair_valid in Hvalid2 as [_ Hvalid2].
        simpl in Hvalid2.
        done.
  Qed.

  Lemma access_agree_1 {σ γ} (p:PID) s :
   own γ (● (get_access_gmap σ)) -∗
   own γ (◯ {[p := (1%Qp, (GSet s))]}) -∗
   ⌜(get_access_gmap σ) !! p = Some (1%Qp, (GSet s)) ⌝.
  Proof.
    iIntros  "Hσ Hpt".
    iDestruct (own_valid_2 with "Hσ Hpt") as "%Hvalid".
    setoid_rewrite auth_both_valid_discrete in Hvalid.
    destruct Hvalid as [Hvalid1 Hvalid2].
    apply singleton_included_l in Hvalid1.
    destruct Hvalid1 as [y [Hvalid1 Hvalid1']].
    apply option_included in Hvalid1'.
    destruct Hvalid1' as [? | Hvalid1']; first done.
    destruct Hvalid1' as [Hvalid1' Hvalid1''].
    destruct Hvalid1'' as [b [? [? Hvalid1'']]].
    simplify_eq.
    iPureIntro.
    destruct b as [b1 b2].
    assert (b1 = 1%Qp) as ->.
    {
      unfold get_access_gmap in Hvalid1.
      apply lookup_fmap_Some in Hvalid1.
      destruct Hvalid1 as [Hvalid1 [Hvalid1' Hvalid1''']].
      simplify_eq.
      reflexivity.
    }        
    destruct b2 as [b' |].
    - destruct Hvalid1'' as [Hvalid1'' | Hvalid1''].
      + simplify_eq.
        done.
      + unfold included in Hvalid1''.
        destruct Hvalid1'' as [z Hvalid1''].
        exfalso.
        apply exclusive0_l with (1%Qp, GSet s) z.
        apply pair_exclusive_l.
        apply frac_full_exclusive.
        setoid_rewrite <-Hvalid1''.
        apply (lookup_valid_Some (get_access_gmap σ) p (1%Qp, GSet b')) in Hvalid2; first done.
        by rewrite Hvalid1.
    - apply (lookup_valid_Some (get_access_gmap σ) p (1%Qp, GSetBot)) in Hvalid2.
      setoid_rewrite pair_valid in Hvalid2.
      destruct Hvalid2 as [_ Hvalid2].
      by cbv in Hvalid2.
      by rewrite Hvalid1.
  Qed.

  Lemma access_agree_check_noaccess {σ i} p s:
   i ∉ s ->
   own (gen_access_name vmG) (●(get_access_gmap σ)) -∗
   (A@ p :={1} [s]) -∗
   ⌜(check_access_page σ i p)= false⌝.
  Proof.
    iIntros (Hnin) "Hσ Hacc".
    rewrite access_mapsto_eq /access_mapsto_def.
    iDestruct (access_agree_1 with "Hσ Hacc") as %Hvalid.
    rewrite /check_access_page.
    apply opsem_access_lookup in Hvalid as [? Hvalid].
    rewrite Hvalid.
    destruct (decide (i ∈ s)) as [Hde|?]; last done.
    contradiction.
  Qed.


  (** bigSL/M **)
  (* TODO *)

 (* Lemma gen_pagetable_SepM_split1 {Perm: Type} {σ γ} i (proj: page_table -> gmap PID Perm) *)
 (*        (checkb: Perm -> bool): *)
 (*   ([∗ map] k↦v ∈ (get_pagetable_gmap σ proj checkb ), ghost_map_elem γ k (dfrac.DfracOwn 1) v)%I -∗ *)
 (*   ghost_map_elem γ i (dfrac.DfracOwn 1) (get_pagetable_gset σ i proj checkb) ∗ *)
 (*   [∗ map] k↦v ∈ (delete i (get_pagetable_gmap σ proj checkb)), ghost_map_elem γ k (dfrac.DfracOwn 1) v. *)
 (*  Proof. *)
 (*    iIntros "Hall". *)
 (*    iApply ((big_sepM_delete _ (get_pagetable_gmap σ proj checkb) i *)
 (*                             (get_pagetable_gset σ i proj checkb)) with "Hall"). *)
 (*    rewrite /get_pagetable_gmap. *)
 (*    apply elem_of_list_to_map_1. *)
 (*    {  rewrite -list_fmap_compose /compose /=. rewrite list_fmap_id. apply NoDup_list_of_vmids. } *)
 (*    rewrite elem_of_list_In. *)
 (*    rewrite in_map_iff. *)
 (*    exists i. *)
 (*    split. *)
 (*    rewrite /get_pagetable_gset //. *)
 (*    apply in_list_of_vmids. *)
 (*  Qed. *)

 (*  Lemma gen_pagetable_SepM_split2 {Perm: Type} {σ γ} i j (proj: page_table -> gmap PID Perm) *)
 (*        (checkb: Perm -> bool): *)
 (*   i ≠ j -> *)
 (*   ([∗ map] k↦v ∈ (get_pagetable_gmap σ proj checkb ), ghost_map_elem γ k (dfrac.DfracOwn 1) v)%I -∗ *)
 (*   ghost_map_elem γ i (dfrac.DfracOwn 1) (get_pagetable_gset σ i proj checkb) ∗ *)
 (*   ghost_map_elem γ j (dfrac.DfracOwn 1) (get_pagetable_gset σ j proj checkb) ∗ *)
 (*   [∗ map] k↦v ∈ (delete j (delete i (get_pagetable_gmap σ proj checkb))), *)
 (*                  ghost_map_elem γ k (dfrac.DfracOwn 1) v. *)
 (*  Proof. *)
 (*    iIntros (Hne) "Hall". *)
 (*    iDestruct ((gen_pagetable_SepM_split1 i) with "Hall") as "[Hi Hrest]". *)
 (*    iFrame. *)
 (*    iApply ((big_sepM_delete _ _ j (get_pagetable_gset σ j proj checkb)) with "Hrest"). *)
 (*    rewrite /get_pagetable_gmap. *)
 (*    rewrite lookup_delete_ne;eauto. *)
 (*    apply elem_of_list_to_map_1. *)
 (*    {  rewrite -list_fmap_compose /compose /=. rewrite list_fmap_id. apply NoDup_list_of_vmids. } *)
 (*    rewrite elem_of_list_In. *)
 (*    rewrite in_map_iff. *)
 (*    exists j. *)
 (*    split. *)
 (*    rewrite /get_pagetable_gset //. *)
 (*    apply in_list_of_vmids. *)
 (*  Qed. *)

  (* Lemma gen_pagetable_valid_SepS_pure {Perm: Type} {σ i q γ} proj (checkb: Perm -> bool) (s:gset PID): *)
  (*  ghost_map_auth γ 1 (get_pagetable_gmap σ proj checkb) -∗ *)
  (*  ghost_map_elem γ i (DfracOwn q) s -∗ *)
  (*  ([∗ set]  p ∈ s, ∃ perm, ⌜(proj (get_vm_page_table σ i)) !! p =Some perm ∧ checkb perm = true⌝). *)
  (* Proof. *)
  (*   iIntros "Hσ Hpt". *)
  (*   iDestruct (gen_pagetable_valid_pure with "Hσ Hpt") as %Hvalid. *)
  (*   iPureIntro. *)
  (*   apply (elem_of_list_to_map_2 _ i s) in Hvalid. *)
  (*   apply elem_of_list_In in Hvalid. *)
  (*   apply in_map_iff in Hvalid. *)
  (*   destruct Hvalid as [? [Heqp _]]. *)
  (*   inversion Heqp;subst;clear Heqp. *)
  (*   intros p Hin. *)
  (*   apply elem_of_list_to_set in Hin. *)
  (*   apply elem_of_list_In in Hin. *)
  (*   apply (in_map_iff _ _ p) in Hin. *)
  (*   destruct Hin as [? [<- Hin]]. *)
  (*   rewrite <- elem_of_list_In in Hin. *)
  (*   apply elem_of_map_to_list' in Hin. *)
  (*   apply map_filter_lookup_Some in Hin. *)
  (*   destruct Hin. *)
  (*   exists x.2. *)
  (*   done. *)
  (* Qed. *)

  (* Lemma gen_own_valid_SepS_pure {σ i q} (s:gset PID): *)
  (*  ghost_map_auth (gen_owned_name vmG) 1 (get_owned_gmap σ) -∗ *)
  (*  (O@ i :={q}[s]) -∗ *)
  (*  ([∗ set] p ∈ s, ∃ perm, ⌜(get_vm_page_table σ i).1 !! p =Some perm ∧ is_owned perm = true⌝). *)
  (* Proof. *)
  (*   iIntros "Hσ Hown". *)
  (*   rewrite owned_mapsto_eq /owned_mapsto_def /get_owned_gmap. *)
  (*   iApply (gen_pagetable_valid_SepS_pure with "Hσ Hown"). *)
  (* Qed. *)

  (* Lemma gen_access_valid_SepS_pure {σ i q} (s:gset PID): *)
  (*  ghost_map_auth (gen_access_name vmG) 1 (get_access_gmap σ) -∗ *)
  (*  (A@ i :={q}[s]) -∗ *)
  (*  ([∗ set] p ∈ s, ∃ perm, ⌜(get_vm_page_table σ i).2 !! p =Some perm ∧ is_accessible perm = true⌝). *)
  (* Proof. *)
  (*   iIntros "Hσ Hacc". *)
  (*   rewrite access_mapsto_eq /access_mapsto_def /get_access_gmap. *)
  (*   iApply (gen_pagetable_valid_SepS_pure with "Hσ Hacc"). *)
  (* Qed. *)

  (* Lemma gen_excl_valid_SepS_pure {σ i q} (s:gset PID): *)
  (*  ghost_map_auth (gen_excl_name vmG) 1 (get_excl_gmap σ) -∗ *)
  (*  (E@ i :={q}[s]) -∗ *)
  (*  ([∗ set] p ∈ s, ∃ perm, ⌜(get_vm_page_table σ i).2 !! p =Some perm ∧ is_exclusive perm = true⌝). *)
  (* Proof. *)
  (*   iIntros "Hσ Hexcl". *)
  (*   rewrite excl_mapsto_eq /excl_mapsto_def /get_excl_gmap. *)
  (*   iApply (gen_pagetable_valid_SepS_pure with "Hσ Hexcl"). *)
  (* Qed. *)

  (* Lemma gen_access_valid_SepS_check {σ i q} s: *)
  (*  ghost_map_auth (gen_access_name vmG) 1 (get_access_gmap σ) -∗ *)
  (*  (A@ i :={q}[s]) -∗ *)
  (*  ([∗ set] p ∈ s, ⌜(check_access_page' σ i p)= true⌝). *)
  (* Proof. *)
  (*   iIntros "Hσ Hacc". *)
  (*   rewrite access_mapsto_eq /access_mapsto_def. *)
  (*   iDestruct (gen_pagetable_valid_SepS_pure with "Hσ Hacc") as %Hvalid. *)
  (*   iPureIntro. *)
  (*   intros p Hin. *)
  (*   unfold check_access_page'. *)
  (*   pose proof (Hvalid p Hin) as [? [Hlk Hisa]]. *)
  (*   rewrite Hlk /= //. *)
  (* Qed. *)

  (* Lemma gen_access_valid {σ i q} p: *)
  (*  ghost_map_auth (gen_access_name vmG) 1 (get_access_gmap σ) -∗ *)
  (*  (A@ i :={q}p) -∗ *)
  (*  ⌜(check_access_page' σ i p)= true⌝. *)
  (* Proof. *)
  (*   iIntros "Hσ Hacc". *)
  (*   iDestruct (gen_access_valid_SepS_check {[p]} with "Hσ Hacc") as %->;eauto. *)
  (*   set_solver. *)
  (* Qed. *)

  (* Lemma gen_access_valid2 {σ i q} s p1 p2: *)
  (*  {[p1;p2]} ⊆ s -> *)
  (*  ghost_map_auth (gen_access_name vmG) 1 (get_access_gmap σ) -∗ *)
  (*  (A@ i :={q}[s] ) -∗ *)
  (*  ⌜(check_access_page' σ i p1)= true⌝ ∗ ⌜(check_access_page' σ i p2) = true⌝. *)
  (* Proof. *)
  (*   iIntros (Hsubset) "Hσ Hacc". *)
  (*   iDestruct (gen_access_valid_SepS_check s with "Hσ Hacc") as %Hcheck;eauto. *)
  (*   iPureIntro. *)
  (*   split. *)
  (*   - apply (Hcheck p1). *)
  (*     set_solver. *)
  (*   - apply (Hcheck p2). *)
  (*     set_solver. *)
  (* Qed. *)

  (* Lemma gen_access_valid_addr {σ i q} a p: *)
  (*  addr_in_page a p -> *)
  (*  ghost_map_auth (gen_access_name vmG) 1 (get_access_gmap σ) -∗ *)
  (*  (A@ i :={q} p ) -∗ *)
  (*  ⌜(check_access_addr σ i a)= true⌝. *)
  (* Proof. *)
  (*   iIntros (HIn) "Haccess Hacc". *)
  (*   iDestruct (gen_access_valid p with "Haccess Hacc") as %Hacc. *)
  (*   iPureIntro. *)
  (*   unfold check_access_addr. *)
  (*   apply to_pid_aligned_in_page in HIn. *)
  (*   rewrite HIn //=. *)
  (* Qed. *)

  (* Lemma gen_access_valid_addr_Set {σ i q} a s: *)
  (*  (to_pid_aligned a) ∈ s -> *)
  (*  ghost_map_auth (gen_access_name vmG) 1 (get_access_gmap σ) -∗ *)
  (*  (A@ i :={q}[s] ) -∗ *)
  (*  ⌜(check_access_addr σ i a)= true⌝. *)
  (* Proof. *)
  (*   iIntros (HaIn) "Haccess Hacc". *)
  (*   iDestruct (gen_access_valid_SepS_pure with "Haccess Hacc") as %Hacc. *)
  (*   iPureIntro. *)
  (*   unfold check_access_addr. *)
  (*   (* apply to_pid_aligned_in_page in HaIn. *) *)
  (*   rewrite /check_access_page'. *)
  (*   pose proof (Hacc (to_pid_aligned a) HaIn) as [? [-> Hisa]]. *)
  (*   done. *)
  (* Qed. *)

  (* Lemma gen_access_valid_addr_elem {σ i q} a s: *)
  (*  to_pid_aligned a ∈ s -> *)
  (*  ghost_map_auth (gen_access_name vmG) 1 (get_access_gmap σ) -∗ *)
  (*  (A@ i :={q}[s] ) -∗ *)
  (*  ⌜(check_access_addr σ i a)= true⌝. *)
  (* Proof. *)
  (*   iIntros (Hin) "Haccess Hacc". *)
  (*   iDestruct (gen_access_valid_SepS_check s with "Haccess Hacc") as %Hacc. *)
  (*   iPureIntro. *)
  (*   apply (Hacc (to_pid_aligned a));auto. *)
  (* Qed. *)

  (* Lemma gen_access_valid_addr2 {σ i q } a1 a2 s: *)
  (*  s = {[(to_pid_aligned a1); (to_pid_aligned a2)]} -> *)
  (*  ghost_map_auth (gen_access_name vmG) 1 (get_access_gmap σ) -∗ *)
  (*  (A@ i :={q}[s]) -∗ *)
  (*  ⌜(check_access_addr σ i a1) = true⌝ ∗ ⌜(check_access_addr σ i a2) = true⌝. *)
  (* Proof. *)
  (*   iIntros (Heqs) "Haccess Hacc". *)
  (*   iDestruct (gen_access_valid_SepS_check s with "Haccess Hacc") as %Hacc. *)
  (*   iPureIntro. *)
  (*   split. *)
  (*   apply (Hacc (to_pid_aligned a1)). *)
  (*   set_solver. *)
  (*   apply (Hacc (to_pid_aligned a2)). *)
  (*   set_solver. *)
  (* Qed. *)


  (* Lemma gen_pagetable_update_diff {Perm: Type} {σ i γ s} proj (checkb: Perm -> bool) sps: *)
  (*  ghost_map_elem γ i (DfracOwn 1) s -∗ *)
  (*  ghost_map_auth γ 1 (get_pagetable_gmap σ proj checkb) ==∗ *)
  (*  ghost_map_auth γ 1 (<[i:= (s∖sps)]>(get_pagetable_gmap σ proj checkb)) ∗ *)
  (*  ghost_map_elem γ i (DfracOwn 1) (s∖sps). *)
  (* Proof. *)
  (*   iIntros "Hpt Hσ". *)
  (*   iApply (ghost_map_update (s∖sps) with "Hσ Hpt"). *)
  (* Qed. *)

  (* Lemma gen_access_update_diff{σ i sacc} sps: *)
  (*  A@i:={1}[sacc] -∗ *)
  (*  ghost_map_auth (gen_access_name vmG) 1 (get_access_gmap σ)==∗ *)
  (*  ghost_map_auth (gen_access_name vmG) 1 (<[i:= (sacc∖sps)]>(get_access_gmap σ)) ∗ *)
  (*  A@i:={1}[sacc∖sps]. *)
  (* Proof. *)
  (*   iIntros "HA Hacc". *)
  (*   rewrite access_mapsto_eq /access_mapsto_def. *)
  (*   iApply (gen_pagetable_update_diff with "HA Hacc");eauto. *)
  (* Qed. *)

  (* Lemma gen_pagetable_update_union {Perm: Type} {σ i γ s ps} proj (checkb: Perm -> bool) sps: *)
  (*  sps = (list_to_set ps) -> *)
  (*  ghost_map_elem γ i (DfracOwn 1)  s -∗ *)
  (*  ghost_map_auth γ 1 (get_pagetable_gmap σ proj checkb) ==∗ *)
  (*  ghost_map_auth γ 1 (<[i:= s ∪ sps]>(get_pagetable_gmap σ proj checkb)) ∗ *)
  (*  ghost_map_elem γ i (DfracOwn 1)  (s ∪ sps). *)
  (* Proof. *)
  (*   iIntros (Hsps) "Hpt Hσ". *)
  (*   iApply ((ghost_map_update (s ∪ sps)) with "Hσ Hpt"). *)
  (* Qed. *)

  (* Lemma gen_access_update_union{σ i sacc psd} sps: *)
  (*  sps = (list_to_set psd) -> *)
  (*  A@i:={1}[sacc] -∗ *)
  (*  ghost_map_auth (gen_access_name vmG) 1 (get_access_gmap σ)==∗ *)
  (*  ghost_map_auth (gen_access_name vmG) 1 (<[i:= (sacc ∪ sps)]>(get_access_gmap σ)) ∗ *)
  (*  A@i:={1}[sacc ∪ sps]. *)
  (* Proof. *)
  (*   iIntros (Hsps) "HA Hacc". *)
  (*   rewrite access_mapsto_eq /access_mapsto_def. *)
  (*   iApply (gen_pagetable_update_union with "HA Hacc");eauto. *)
  (* Qed. *)

  (* Lemma gen_own_update_union{σ i sown psd} sps: *)
  (*  sps = (list_to_set psd) -> *)
  (*  O@i:={1}[sown] -∗ *)
  (*  ghost_map_auth (gen_owned_name vmG) 1 (get_owned_gmap σ)==∗ *)
  (*  ghost_map_auth (gen_owned_name vmG) 1 (<[i:= (sown ∪ sps)]>(get_owned_gmap σ)) ∗ *)
  (*  O@i:={1}[sown ∪ sps]. *)
  (* Proof. *)
  (*   iIntros (Hsps) "HO Hown". *)
  (*   rewrite owned_mapsto_eq /owned_mapsto_def. *)
  (*   iApply (gen_pagetable_update_union with "HO Hown");eauto. *)
  (* Qed. *)

End pagetable_rules.
