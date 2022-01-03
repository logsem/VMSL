From iris.base_logic.lib Require Import gen_heap ghost_map.
From HypVeri.algebra Require Import base base_extra.

Section pagetable_rules.

  Context `{vmG :gen_VMG Σ}.

  (** properties of the pagetable RA **)

  (* own *)
  Lemma own_ne p1 p2 (v1 v2 : VMID):
   p1 -@O> v1 ∗ p2 -@O>v2 -∗ ⌜p1 ≠ p2⌝ .
  Proof using.
    iIntros "[HO1 HO2]".
    rewrite own_mapsto_eq /own_mapsto_def.
    destruct (decide (p1 = p2)).
    { subst p2.
      iDestruct (ghost_map_elem_valid_2 with "HO1 HO2") as "[%Hvalid _]".
      apply dfrac_valid_own_l in Hvalid.
      inversion Hvalid.
    }
    done.
  Qed.

  Lemma own_agree {σ q γ} p s:
   ghost_map_auth γ 1 (get_own_gmap σ)  -∗
   ghost_map_elem γ p (DfracOwn q) s -∗
   ⌜(get_own_gmap σ) !! p = Some s ⌝.
  Proof.
    iIntros  "Hσ Hpt".
    iApply (ghost_map_lookup with "Hσ Hpt").
  Qed.

  (* access *)

  (* Lemma access_split_set_union {p} q1 q2 (s1 s2 : gset VMID): *)
  (*  s1 ## s2 -> *)
  (*  p -@{(q1+q2)%Qp}A> [s1 ∪ s2] -∗ p -@{q1}A> [s1] ∗ p -@{q2}A> [s2]. *)
  (* Proof using. *)
  (*   iIntros (Hdisj) "HO". *)
  (*   rewrite access_mapsto_eq /access_mapsto_def. *)
  (*   iApply own_op. *)
  (*   rewrite -auth_frag_op singleton_op. *)
  (*   rewrite -pair_op. *)
  (*   rewrite (gset_disj_union _ _ Hdisj). *)
  (*   naive_solver. *)
  (* Qed. *)

  (* Lemma access_split_set_diff {p} q1 q2 (s1 s2 : gset VMID): *)
  (*  s2 ⊆ s1 -> p -@{(q1+q2)%Qp}A> [s1] -∗ p -@{q1}A> [s2] ∗ p -@{q2}A> [s1 ∖ s2]. *)
  (* Proof using. *)
  (*   iIntros (Hsub) "HO". *)
  (*   rewrite access_mapsto_eq. *)
  (*   iApply own_op. *)
  (*   rewrite -auth_frag_op singleton_op. *)
  (*   rewrite -pair_op. *)
  (*   rewrite (gset_disj_union _ _); *)
  (*   last set_solver+ . *)
  (*   rewrite -(union_difference_L _ _ Hsub). *)
  (*   naive_solver. *)
  (* Qed. *)

  (* Lemma access_split {q} p s s1 s2 : *)
  (*   s = s1 ∪ s2 -> *)
  (*   s1 ## s2 -> *)
  (*   p -@{ q }A> [ s ] -∗ *)
  (*   p -@{ q/2 }A> [ s1 ] ∗ *)
  (*   p -@{ q/2 }A> [ s2 ]. *)
  (* Proof. *)
  (*   iIntros (Heq Hdisj) "H". *)
  (*   rewrite Heq. *)
  (*   rewrite access_mapsto_eq /access_mapsto_def. *)
  (*   rewrite <-gset_disj_union; auto. *)
  (*   rewrite <-(Qp_div_2 q). *)
  (*   rewrite pair_op. *)
  (*   setoid_rewrite <- singleton_op. *)
  (*   rewrite auth_frag_op. *)
  (*   rewrite own_op. *)
  (*   iDestruct "H" as "[? ?]". *)
  (*   rewrite (Qp_div_2 q). *)
  (*   by iFrame. *)
  (* Qed. *)

  (** relations between get_access_gmap and the opsem **)
  (* Lemma opsem_access_lookup {σ} {s:gset VMID} (p:PID): *)
  (* (get_access_gmap σ) !! p = Some (1%Qp, (GSet s)) -> *)
  (* ∃ j, (get_page_table σ) !! p = Some(j, s). *)
  (* Proof. *)
  (*   rewrite /get_access_gmap. *)
  (*   rewrite lookup_fmap_Some. *)
  (*   intros [? [Helem Hlookup]]. *)
  (*   inversion Helem. *)
  (*   subst. *)
  (*   exists x.1. *)
  (*   destruct x;done. *)
  (* Qed. *)

  Lemma opsem_ownership_lookup {σ} {i:option VMID} (p:PID):
  (get_own_gmap σ) !! p = Some i ->
  ∃ b s, (get_page_table σ) !! p = Some(i, b, s).
  Proof.
    rewrite /get_own_gmap.
    rewrite lookup_fmap_Some.
    intros [? [Helem Hlookup]].
    inversion Helem.
    subst.
    exists x.1.2, x.2.
    destruct x; destruct p0;done.
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

  Lemma access_agree_1 {γ} gm (p:PID) s :
   own γ (● gm) -∗
   own γ (◯ {[p := (1%Qp, (GSet s))]}) -∗
   ⌜gm !! p = Some (1%Qp, (GSet s)) ⌝.
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
    destruct Hvalid1''.
    rewrite Hvalid1.
    apply leibniz_equiv in H.
    rewrite H //.
    exfalso.
    apply (exclusive_included (1%Qp, GSet s) _ H ).
    apply (lookup_valid_Some gm p (b1, b2) Hvalid2).
    rewrite Hvalid1.
    done.
  Qed.

  Lemma access_agree_1_lookup {σ} p s:
   own (gen_access_name vmG) (●(get_access_gmap σ)) -∗
   (p -@A> [s]) -∗
   ⌜∃ v, (get_page_table σ) !! p= Some (v,s)⌝.
  Proof.
    iIntros "Hauth Hfrag".
    rewrite access_mapsto_eq /access_mapsto_def.
    iDestruct (access_agree_1 with "Hauth Hfrag") as %Hvalid.
    iPureIntro.
    apply opsem_access_lookup in Hvalid as [? Hvalid].
    exists x.
    done.
  Qed.

  Lemma access_agree_1_check_false {σ i} p s:
   i ∉ s ->
   own (gen_access_name vmG) (●(get_access_gmap σ)) -∗
   (p -@A> [s]) -∗
   ⌜(check_access_page σ i p)= false⌝.
  Proof.
    iIntros (Hnin) "Hauth Hfrag".
    iDestruct (access_agree_1_lookup with "Hauth Hfrag") as %[v Hlookup].
    rewrite /check_access_page.
    rewrite Hlookup.
    destruct (decide (i ∈ s)) as [Hde|?]; last done.
    contradiction.
  Qed.

  Lemma access_agree_check_true_forall {q} σ p s :
    own (gen_access_name vmG) (●(get_access_gmap σ)) -∗
    p -@{ q }A> [ s ] -∗
    ⌜∀ i, i ∈ s -> check_access_page σ i p = true⌝.
  Proof.
    iIntros "Hσ Hacc".
    rewrite access_mapsto_eq /access_mapsto_def.
    iDestruct (access_agree with "Hσ Hacc") as %Hvalid.
    destruct Hvalid as [s' [Hvalid1 Hvalid2]].
    iPureIntro.
    intros i Hin.
    rewrite /check_access_page.
    apply opsem_access_lookup in Hvalid1 as [? Hvalid1].
    rewrite Hvalid1.
    assert (Hvalid3 : i ∈ s').
    {
      apply elem_of_weaken with s; auto.
    }
    rewrite decide_True; auto.
  Qed.

  Lemma access_agree_check_true {σ q} p i s:
   i ∈ s ->
   own (gen_access_name vmG) (●(get_access_gmap σ)) -∗
   (p -@{q}A> [s]) -∗
   ⌜(check_access_page σ i p)= true⌝.
  Proof.
    iIntros (Hin) "Hσ Hacc".
    iDestruct (access_agree_check_true_forall with "Hσ Hacc") as "%Hforall".
    iPureIntro.
    by apply Hforall.
  Qed.

  Lemma access_agree_1_excl_check_true {σ} p i:
   own (gen_access_name vmG) (●(get_access_gmap σ)) -∗
   (p -@A> i) -∗
   ⌜(check_excl_access_page σ i p)= true⌝.
  Proof.
    iIntros "Hσ Hacc".
    rewrite access_mapsto_eq /access_mapsto_def.
    iDestruct (access_agree_1 with "Hσ Hacc") as %Hvalid.
    iPureIntro.
    rewrite /check_excl_access_page.
    apply opsem_access_lookup in Hvalid as [? Hvalid].
    rewrite Hvalid.
    case_match.
    case_match;first done.
    exfalso.
    apply n.
    apply size_singleton.
    set_solver + n.
  Qed.

  Lemma ownership_agree {σ γ} (p:PID) i:
   ghost_map_auth γ 1 (get_own_gmap σ) -∗
   ghost_map_elem γ p (DfracOwn 1%Qp) i -∗
   ⌜(get_own_gmap σ) !! p = Some i⌝.
  Proof.
    iIntros  "Hσ Hpt".
    iApply (ghost_map_lookup with "Hσ Hpt").
  Qed.

  Lemma ownership_agree_Some_lookup {σ} p i:
   ghost_map_auth (gen_own_name vmG) 1 (get_own_gmap σ) -∗
   (p -@O> i) -∗
   ⌜∃ s, (get_page_table σ) !! p= Some (Some i,s)⌝.
  Proof.
    iIntros  "Hσ Hown".
    rewrite own_mapsto_eq /own_mapsto_def.
    iDestruct (ownership_agree with "Hσ Hown") as %Hvalid.
    iPureIntro.
    apply opsem_ownership_lookup in Hvalid as [? Hvalid].
    exists x.
    done.
  Qed.

  Lemma ownership_agree_Some_check_true {σ} p i:
   ghost_map_auth (gen_own_name vmG) 1 (get_own_gmap σ) -∗
   (p -@O> i) -∗
   ⌜(check_ownership_page σ i p)= true⌝.
  Proof.
    iIntros  "Hσ Hown".
    iDestruct (ownership_agree_Some_lookup with "Hσ Hown") as %[s Hlookup].
    iPureIntro.
    rewrite /check_ownership_page.
    rewrite Hlookup.
    rewrite decide_True;eauto.
  Qed.

  (* bigS *)

  Lemma access_agree_1_lookup_bigS {σ} (s:gset PID) (sacc: gset VMID):
   own (gen_access_name vmG) (●(get_access_gmap σ)) -∗
   ([∗ set] p ∈ s, p -@A> [sacc]) -∗
   ⌜set_Forall (λ p, ∃ v,  get_page_table σ !! p = Some (v,sacc) ) s⌝.
  Proof.
    iIntros "Hauth Hfrags".
    iIntros (p Hin_p).
    iDestruct (big_sepS_elem_of _ _ p Hin_p with "Hfrags") as "Hfrags".
    iApply (access_agree_1_lookup with "Hauth Hfrags").
  Qed.

  Lemma access_agree_check_true_bigS {σ i} (s:gset PID):
   own (gen_access_name vmG) (●(get_access_gmap σ)) -∗
   ([∗ set] p ∈ s, ∃ q, p -@{q}A> i) -∗
   ⌜set_Forall (λ p, check_access_page σ i p = true) s⌝.
  Proof.
    iIntros "Hacc Hpgt".
    iIntros (p Hin_p).
    iDestruct (big_sepS_elem_of _ _ p Hin_p with "Hpgt") as (q) "Hpgt".
    iApply (access_agree_check_true with "Hacc Hpgt").
    by apply elem_of_singleton.
  Qed.

  Lemma access_agree_1_excl_check_true_bigS {σ i} (s:gset PID):
   own (gen_access_name vmG) (●(get_access_gmap σ)) -∗
   ([∗ set] p ∈ s, p -@A> i) -∗
   ⌜set_Forall (λ p, check_excl_access_page σ i p = true) s⌝.
  Proof.
    iIntros "Hacc Hpgt".
    iIntros (p Hin_p).
    iDestruct (big_sepS_elem_of _ _ p Hin_p with "Hpgt") as "Hpgt".
    iApply (access_agree_1_excl_check_true with "Hacc Hpgt").
  Qed.

  Lemma ownership_agree_Some_lookup_bigS {σ i} (s:gset PID):
   ghost_map_auth (gen_own_name vmG) 1 (get_own_gmap σ) -∗
   ([∗ set] p ∈ s, p -@O> i) -∗
   ⌜set_Forall (λ p, ∃ s,  get_page_table σ !! p = Some (Some i,s) ) s⌝.
  Proof.
    iIntros "Hown Hpgt".
    iIntros (p Hin_p).
    iDestruct (big_sepS_elem_of _ _ p Hin_p with "Hpgt") as "Hpgt".
    iApply (ownership_agree_Some_lookup with "Hown Hpgt").
  Qed.

  Lemma ownership_agree_Some_check_true_bigS {σ i} (s:gset PID):
   ghost_map_auth (gen_own_name vmG) 1 (get_own_gmap σ) -∗
   ([∗ set] p ∈ s, p -@O> i) -∗
   ⌜set_Forall (λ p, check_ownership_page σ i p = true) s⌝.
  Proof.
    iIntros "Hown Hpgt".
    iIntros (p Hin_p).
    iDestruct (big_sepS_elem_of _ _ p Hin_p with "Hpgt") as "Hpgt".
    iApply (ownership_agree_Some_check_true with "Hown Hpgt").
  Qed.

  Lemma access_update{gm x s} s':
    own (gen_access_name vmG) (● gm) -∗ x -@A> [s] ==∗ own (gen_access_name vmG) (● <[x := (1%Qp,GSet s')]>gm) ∗ x -@A> [s'].
  Proof.
    iIntros "Hauth Hfrag".
    rewrite access_mapsto_eq /access_mapsto_def.
    iDestruct (access_agree_1 with "Hauth Hfrag") as %Hlookup.
    rewrite -own_op.
    iApply ((own_update _ (● gm ⋅ ◯ {[x := (1%Qp, GSet s)]}) _ ) with "[Hauth Hfrag]").
    2: { rewrite own_op. iFrame. }
    apply auth_update.
    apply (singleton_local_update gm x (1%Qp,GSet s)).
    done.
    apply exclusive_local_update.
    done.
  Qed.

  Lemma access_update_revoke {gm i s} sps:
    i ∈ s ->
    own (gen_access_name vmG) (● gm) -∗
    ([∗ set] p ∈ sps, p -@A> [s])%I==∗
    own (gen_access_name vmG) (●(revoke_acc_gmap gm i sps)) ∗
    ([∗ set] p ∈ sps, p -@A> [s∖ {[i]}])%I.
  Proof.
    iIntros (Hin_s ) "Hauth Hfrag".
    rewrite /revoke_acc_gmap /update_acc_gmap /=.
    iInduction sps as [|] "IH" using set_ind_L forall (gm).
    rewrite set_fold_empty.
    rewrite !big_sepS_empty.
    by iFrame.
    rewrite set_fold_disj_union_strong.
    rewrite set_fold_singleton.
    iDestruct (big_sepS_union with "Hfrag") as "[Hsingle Hfrag]".
    set_solver + H.
    rewrite big_sepS_singleton.
    iDestruct (access_agree_1 with "Hauth [Hsingle]") as %Hlookup.
    { rewrite access_mapsto_eq /access_mapsto_def. iFrame. }
    rewrite Hlookup.
    {
      iDestruct (access_update (s ∖ {[i]}) with "Hauth Hsingle") as ">[Hauth Hsingle]".
      rewrite big_sepS_union;last set_solver + H.
      rewrite big_sepS_singleton.
      iFrame "Hsingle".
      iApply ("IH" with "Hauth Hfrag").
     }
    {
      intros.
      destruct (b' !! x2) as [p2|] eqn: Hlookup2, (b' !! x1) as [p1|] eqn:Hlookup1;
        try destruct p1 as [q1 []]; try destruct p2 as [q2 []]; rewrite ?lookup_insert_ne ?Hlookup1 ?Hlookup2 //;last eauto.
      apply insert_commute.
      done.
    }
    set_solver + H.
  Qed.

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
  (*  ghost_map_auth (gen_own_name vmG) 1 (get_own_gmap σ)==∗ *)
  (*  ghost_map_auth (gen_own_name vmG) 1 (<[i:= (sown ∪ sps)]>(get_own_gmap σ)) ∗ *)
  (*  O@i:={1}[sown ∪ sps]. *)
  (* Proof. *)
  (*   iIntros (Hsps) "HO Hown". *)
  (*   rewrite own_mapsto_eq /own_mapsto_def. *)
  (*   iApply (gen_pagetable_update_union with "HO Hown");eauto. *)
  (* Qed. *)

End pagetable_rules.
