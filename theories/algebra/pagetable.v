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

  (* excl *)
  Lemma excl_ne p1 p2 (b1 b2 : bool):
   p1 -@E> b1 ∗ p2 -@E>b2 -∗ ⌜p1 ≠ p2⌝ .
  Proof using.
    iIntros "[HO1 HO2]".
    rewrite excl_mapsto_eq /excl_mapsto_def.
    destruct (decide (p1 = p2)).
    { subst p2.
      iDestruct (ghost_map_elem_valid_2 with "HO1 HO2") as "[%Hvalid _]".
      apply dfrac_valid_own_l in Hvalid.
      inversion Hvalid.
    }
    done.
  Qed.

  Lemma excl_agree {σ q γ} p s:
   ghost_map_auth γ 1 (get_excl_gmap σ)  -∗
   ghost_map_elem γ p (DfracOwn q) s -∗
   ⌜(get_excl_gmap σ) !! p = Some s ⌝.
  Proof.
    iIntros  "Hσ Hpt".
    iApply (ghost_map_lookup with "Hσ Hpt").
  Qed.

  (* access *)
  (* Lemma access_split_set_union {v} q1 q2 (s1 s2 : gset PID): *)
  (*  s1 ## s2 -> *)
  (*  v -@{(q1+q2)%Qp}A> [s1 ∪ s2] -∗ v -@{q1}A> [s1] ∗ v -@{q2}A> [s2]. *)
  (* Proof using. *)
  (*   iIntros (Hdisj) "HO". *)
  (*   rewrite access_mapsto_eq /access_mapsto_def. *)
  (*   iApply own_op. *)
  (*   rewrite -auth_frag_op singleton_op. *)
  (*   rewrite -pair_op. *)
  (*   rewrite (gset_disj_union _ _ Hdisj). *)
  (*   naive_solver. *)
  (* Qed. *)

  (* Lemma access_split_set_diff {v} q1 q2 (s1 s2 : gset PID): *)
  (*  s2 ⊆ s1 -> v -@{(q1+q2)%Qp}A> [s1] -∗ v -@{q1}A> [s2] ∗ v -@{q2}A> [s1 ∖ s2]. *)
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

  Lemma access_split {q} v (s : gset PID) :
    v -@{ q }A> [ s ] ⊣⊢
    v -@{ q/2 }A> [ s ] ∗ v -@{ q/2 }A> [ s ].
  Proof.
    rewrite access_mapsto_eq /access_mapsto_def.
    rewrite -own_op.
    rewrite -auth_frag_op.
    setoid_rewrite singleton_op.
    rewrite -frac_agree_op.
    iEval(rewrite (Qp_div_2 q)).
    iSplit;eauto.
  Qed.

  (** relations between get_access_gmap and the opsem **)
  Lemma access_pgt_lookup {σ} {s:gset PID} (v:VMID):
  (get_access_gmap σ) !! v = Some (to_frac_agree 1 s) ->
  set_Forall (λ p, ∃ i b s, (get_page_table σ) !! p = Some(i,b,s) ∧ v ∈ s) s.
  Proof.
    intro Hlookup.
    rewrite /get_access_gmap in Hlookup.
    apply (elem_of_list_to_map_2 _ v) in Hlookup.
    apply elem_of_list_In in Hlookup.
    apply in_map_iff in Hlookup.
    destruct Hlookup as [? [Heqp _]].
    inversion Heqp;subst;clear Heqp.
    intros p Hin.
    rewrite elem_of_dom in Hin.
    destruct Hin as [sa Hlookup].
    pose proof Hlookup as Hlookup'.
    apply (map_filter_lookup_Some_1_1 _ _ p sa) in Hlookup.
    apply (map_filter_lookup_Some_1_2 _ _ p sa) in Hlookup'.
    apply lookup_fmap_Some in Hlookup.
    destruct Hlookup as [[[]] [<- Hlookup]].
    exists o,b,g.
    split;eauto.
  Qed.

  Lemma own_pgt_lookup {σ} {i:option VMID} (p:PID):
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

  Lemma excl_pgt_lookup {σ} {b:bool} (p:PID):
  (get_excl_gmap σ) !! p = Some b ->
  ∃ o s, (get_page_table σ) !! p = Some(o, b, s).
  Proof.
    rewrite /get_excl_gmap.
    rewrite lookup_fmap_Some.
    intros [? [Helem Hlookup]].
    subst.
    exists x.1.1, x.2.
    destruct x; destruct p0;done.
  Qed.

  (** agreement (RA -> opsem) **)

  (* single pt *)

  Lemma access_agree {σ γ} (v:VMID) q s:
   own γ (● (get_access_gmap σ)) -∗
   own γ (◯ {[v := to_frac_agree q s]}) -∗
   ⌜(get_access_gmap σ) !! v = Some (to_frac_agree 1 s)⌝.
  Proof.
    iIntros  "Hσ Hpt".
    iDestruct (own_valid_2 with "Hσ Hpt") as "%Hvalid".
    setoid_rewrite auth_both_valid_discrete in Hvalid.
    destruct Hvalid as [Hvalid1 Hvalid2].
    apply singleton_included_l in Hvalid1.
    destruct Hvalid1 as [y [Hvalid1 Hvalid1']].
    apply option_included in Hvalid1'.
    destruct Hvalid1' as [? | Hvalid1']; first done.
    destruct Hvalid1' as [? [? Hvalid1']].
    destruct Hvalid1' as [? [? Hvalid1']].
    simplify_eq.
    iPureIntro.
    assert (get_access_gmap σ !! v = Some(to_frac_agree 1
                (dom (gset PID)
                   (map_filter (λ kv : PID * gset VMID, v ∈ kv.2) (λ x1 : PID * gset VMID, decide_rel elem_of v x1.2)
                      ((λ p : option VMID * bool * gset VMID, p.2) <$> σ.1.1.1.2))))) as Hlookup.
    { rewrite /get_access_gmap.
      apply (elem_of_list_to_map_1 _ v).
      {
        rewrite -list_fmap_compose.
        simpl.
        rewrite NoDup_fmap.
        apply NoDup_list_of_vmids.
      }
      apply elem_of_list_In.
      apply in_map_iff.
      exists v.
      split;auto.
      apply in_list_of_vmids.
    }
    rewrite Hlookup in Hvalid1.
    inversion Hvalid1.
    subst.
    destruct Hvalid1' as [Hvalid1' | Hvalid1'].
    * rewrite -Hvalid1' in H1.
      inversion H1.
      simpl in *.
      rewrite Hlookup.
      f_equal.
      f_equal.
      apply to_agree_inj in H0.
      fold_leibniz.
      done.
    * rewrite -H1 in Hvalid1'.
      apply dfrac_agree_included_L in Hvalid1'.
      destruct Hvalid1'.
      rewrite Hlookup.
      subst s.
      done.
  Qed.

  Lemma access_agree_lookup {σ} v s:
   own gen_access_name (●(get_access_gmap σ)) -∗
   (v -@A> [s]) -∗
   ⌜set_Forall (λ p, ∃ o b s, (get_page_table σ) !! p= Some (o,b,s) ∧ v ∈ s ) s⌝.
  Proof.
    iIntros "Hauth Hfrag".
    rewrite access_mapsto_eq /access_mapsto_def.
    iDestruct (access_agree with "Hauth Hfrag") as %Hvalid.
    iPureIntro.
    apply access_pgt_lookup in Hvalid as Hvalid.
    done.
  Qed.

  Lemma access_agree_check_false {σ v} p s:
   p ∉ s ->
   own gen_access_name (●(get_access_gmap σ)) -∗
   (v -@A> [s]) -∗
   ⌜(check_access_page σ v p)= false⌝.
  Proof.
    iIntros (Hnin) "Hauth Hfrag".
     rewrite access_mapsto_eq /access_mapsto_def.
    iDestruct (access_agree with "Hauth Hfrag") as %Hlookup.
    iPureIntro.
    rewrite /get_access_gmap in Hlookup.
    apply (elem_of_list_to_map_2 _ v) in Hlookup.
    apply elem_of_list_In in Hlookup.
    apply in_map_iff in Hlookup.
    destruct Hlookup as [? [Heqp _]].
    inversion Heqp;subst;clear Heqp.
    rewrite not_elem_of_dom in Hnin.
    apply (map_filter_lookup_None_1 _ _ p) in Hnin.
    rewrite /check_access_page.
    destruct (σ.1.1.1.2 !! p) eqn:Heq;auto.
    destruct Hnin.
    rewrite lookup_fmap Heq //in H.
    specialize (H p0.2).
    case_match.
    case_match;auto.
    exfalso.
    apply H.
    rewrite lookup_fmap Heq //.
    done.
  Qed.

  Lemma access_agree_check_true_forall {q} σ v s :
    own gen_access_name (●(get_access_gmap σ)) -∗
    v -@{ q }A> [ s ] -∗
    ⌜∀ p, p ∈ s -> check_access_page σ v p = true⌝.
  Proof.
    iIntros "Hσ Hacc".
    rewrite access_mapsto_eq /access_mapsto_def.
    iDestruct (access_agree with "Hσ Hacc") as %Hvalid.
    apply access_pgt_lookup in Hvalid as Hvalid.
    iPureIntro.
    intros p Hin.
    eapply Hvalid in Hin.
    rewrite /check_access_page.
    destruct Hin as (? & ? & ? & [-> Hin']).
    case_match;auto.
  Qed.

  Lemma access_agree_check_true {σ q} p i s:
   p ∈ s ->
   own gen_access_name (●(get_access_gmap σ)) -∗
   (i -@{q}A> [s]) -∗
   ⌜(check_access_page σ i p)= true⌝.
  Proof.
    iIntros (Hin) "Hσ Hacc".
    iDestruct (access_agree_check_true_forall with "Hσ Hacc") as "%Hforall".
    iPureIntro.
    by apply Hforall.
  Qed.

  Lemma own_agree_Some_lookup {σ} p i:
   ghost_map_auth gen_own_name 1 (get_own_gmap σ) -∗
   (p -@O> i) -∗
   ⌜∃ b s, (get_page_table σ) !! p= Some (Some i,b,s)⌝.
  Proof.
    iIntros  "Hσ Hown".
    rewrite own_mapsto_eq /own_mapsto_def.
    iDestruct (own_agree with "Hσ Hown") as %Hvalid.
    iPureIntro.
    apply own_pgt_lookup in Hvalid as [? Hvalid].
    exists x.
    done.
  Qed.

  Lemma own_agree_Some_check_true {σ} p i:
   ghost_map_auth gen_own_name 1 (get_own_gmap σ) -∗
   (p -@O> i) -∗
   ⌜(check_ownership_page σ i p)= true⌝.
  Proof.
    iIntros  "Hσ Hown".
    iDestruct (own_agree_Some_lookup with "Hσ Hown") as %[b [s Hlookup]].
    iPureIntro.
    rewrite /check_ownership_page.
    rewrite Hlookup.
    rewrite decide_True;eauto.
  Qed.

  Lemma excl_agree_Some_lookup {σ} p b:
   ghost_map_auth gen_excl_name 1 (get_excl_gmap σ) -∗
   (p -@E> b) -∗
   ⌜∃ o s, (get_page_table σ) !! p= Some (o,b,s)⌝.
  Proof.
    iIntros  "Hσ Hexcl".
    rewrite excl_mapsto_eq /excl_mapsto_def.
    iDestruct (excl_agree with "Hσ Hexcl") as %Hvalid.
    iPureIntro.
    apply excl_pgt_lookup in Hvalid as (? & ? & Hvalid).
    exists x, x0.
    done.
  Qed.

  Lemma excl_agree_Some_check_true {σ} p b:
   ghost_map_auth gen_excl_name 1 (get_excl_gmap σ) -∗
   (p -@E> b) -∗
   ⌜(check_excl_page σ p)= b⌝.
  Proof.
    iIntros  "Hσ Hexcl".
    iDestruct (excl_agree_Some_lookup with "Hσ Hexcl") as %[o [s Hlookup]].
    iPureIntro.
    rewrite /check_excl_page.
    rewrite Hlookup //.
  Qed.

  (* bigS *)

  (* Lemma access_agree_1_lookup_bigS {σ} (s:gset PID) (sacc: gset VMID): *)
  (*  own (gen_access_name vmG) (●(get_access_gmap σ)) -∗ *)
  (*  ([∗ set] p ∈ s, p -@A> [sacc]) -∗ *)
  (*  ⌜set_Forall (λ p, ∃ v,  get_page_table σ !! p = Some (v,sacc) ) s⌝. *)
  (* Proof. *)
  (*   iIntros "Hauth Hfrags". *)
  (*   iIntros (p Hin_p). *)
  (*   iDestruct (big_sepS_elem_of _ _ p Hin_p with "Hfrags") as "Hfrags". *)
  (*   iApply (access_agree_1_lookup with "Hauth Hfrags"). *)
  (* Qed. *)

  (* Lemma access_agree_check_true_bigS {σ i} (s:gset PID): *)
  (*  own (gen_access_name vmG) (●(get_access_gmap σ)) -∗ *)
  (*  ([∗ set] p ∈ s, ∃ q, p -@{q}A> i) -∗ *)
  (*  ⌜set_Forall (λ p, check_access_page σ i p = true) s⌝. *)
  (* Proof. *)
  (*   iIntros "Hacc Hpgt". *)
  (*   iIntros (p Hin_p). *)
  (*   iDestruct (big_sepS_elem_of _ _ p Hin_p with "Hpgt") as (q) "Hpgt". *)
  (*   iApply (access_agree_check_true with "Hacc Hpgt"). *)
  (*   by apply elem_of_singleton. *)
  (* Qed. *)

  (* Lemma access_agree_1_excl_check_true_bigS {σ i} (s:gset PID): *)
  (*  own (gen_access_name vmG) (●(get_access_gmap σ)) -∗ *)
  (*  ([∗ set] p ∈ s, p -@A> i) -∗ *)
  (*  ⌜set_Forall (λ p, check_excl_access_page σ i p = true) s⌝. *)
  (* Proof. *)
  (*   iIntros "Hacc Hpgt". *)
  (*   iIntros (p Hin_p). *)
  (*   iDestruct (big_sepS_elem_of _ _ p Hin_p with "Hpgt") as "Hpgt". *)
  (*   iApply (access_agree_1_excl_check_true with "Hacc Hpgt"). *)
  (* Qed. *)

  (* own *)
  Lemma owne_agree_Some_lookup_bigS {σ i} (s:gset PID):
   ghost_map_auth gen_own_name 1 (get_own_gmap σ) -∗
   ([∗ set] p ∈ s, p -@O> i) -∗
   ⌜set_Forall (λ p, ∃ b s,  get_page_table σ !! p = Some (Some i,b,s) ) s⌝.
  Proof.
    iIntros "Hown Hpgt".
    iIntros (p Hin_p).
    iDestruct (big_sepS_elem_of _ _ p Hin_p with "Hpgt") as "Hpgt".
    iApply (own_agree_Some_lookup with "Hown Hpgt").
  Qed.

  Lemma own_agree_Some_check_true_bigS {σ i} (s:gset PID):
   ghost_map_auth gen_own_name 1 (get_own_gmap σ) -∗
   ([∗ set] p ∈ s, p -@O> i) -∗
   ⌜set_Forall (λ p, check_ownership_page σ i p = true) s⌝.
  Proof.
    iIntros "Hown Hpgt".
    iIntros (p Hin_p).
    iDestruct (big_sepS_elem_of _ _ p Hin_p with "Hpgt") as "Hpgt".
    iApply (own_agree_Some_check_true with "Hown Hpgt").
  Qed.

  (* excl *)
  Lemma excle_agree_Some_lookup_bigS {σ b} (s:gset PID):
   ghost_map_auth gen_excl_name 1 (get_excl_gmap σ) -∗
   ([∗ set] p ∈ s, p -@E> b) -∗
   ⌜set_Forall (λ p, ∃ o s,  get_page_table σ !! p = Some (o,b,s)) s⌝.
  Proof.
    iIntros "Hexcl Hpgt".
    iIntros (p Hin_p).
    iDestruct (big_sepS_elem_of _ _ p Hin_p with "Hpgt") as "Hpgt".
    iApply (excl_agree_Some_lookup with "Hexcl Hpgt").
  Qed.

  Lemma excl_agree_Some_check_true_bigS {σ b} (s:gset PID):
   ghost_map_auth gen_excl_name 1 (get_excl_gmap σ) -∗
   ([∗ set] p ∈ s, p -@E> b) -∗
   ⌜set_Forall (λ p, check_excl_page σ p = b) s⌝.
  Proof.
    iIntros "Hexcl Hpgt".
    iIntros (p Hin_p).
    iDestruct (big_sepS_elem_of _ _ p Hin_p with "Hpgt") as "Hpgt".
    iApply (excl_agree_Some_check_true with "Hexcl Hpgt").
  Qed.

  (* Lemma access_update{gm x s} s': *)
  (*   own (gen_access_name vmG) (● gm) -∗ x -@A> [s] ==∗ own (gen_access_name vmG) (● <[x := (1%Qp,GSet s')]>gm) ∗ x -@A> [s']. *)
  (* Proof. *)
  (*   iIntros "Hauth Hfrag". *)
  (*   rewrite access_mapsto_eq /access_mapsto_def. *)
  (*   iDestruct (access_agree_1 with "Hauth Hfrag") as %Hlookup. *)
  (*   rewrite -own_op. *)
  (*   iApply ((own_update _ (● gm ⋅ ◯ {[x := (1%Qp, GSet s)]}) _ ) with "[Hauth Hfrag]"). *)
  (*   2: { rewrite own_op. iFrame. } *)
  (*   apply auth_update. *)
  (*   apply (singleton_local_update gm x (1%Qp,GSet s)). *)
  (*   done. *)
  (*   apply exclusive_local_update. *)
  (*   done. *)
  (* Qed. *)

  (* Lemma access_update_revoke {gm i s} sps: *)
  (*   i ∈ s -> *)
  (*   own (gen_access_name vmG) (● gm) -∗ *)
  (*   ([∗ set] p ∈ sps, p -@A> [s])%I==∗ *)
  (*   own (gen_access_name vmG) (●(revoke_acc_gmap gm i sps)) ∗ *)
  (*   ([∗ set] p ∈ sps, p -@A> [s∖ {[i]}])%I. *)
  (* Proof. *)
  (*   iIntros (Hin_s ) "Hauth Hfrag". *)
  (*   rewrite /revoke_acc_gmap /update_acc_gmap /=. *)
  (*   iInduction sps as [|] "IH" using set_ind_L forall (gm). *)
  (*   rewrite set_fold_empty. *)
  (*   rewrite !big_sepS_empty. *)
  (*   by iFrame. *)
  (*   rewrite set_fold_disj_union_strong. *)
  (*   rewrite set_fold_singleton. *)
  (*   iDestruct (big_sepS_union with "Hfrag") as "[Hsingle Hfrag]". *)
  (*   set_solver + H. *)
  (*   rewrite big_sepS_singleton. *)
  (*   iDestruct (access_agree_1 with "Hauth [Hsingle]") as %Hlookup. *)
  (*   { rewrite access_mapsto_eq /access_mapsto_def. iFrame. } *)
  (*   rewrite Hlookup. *)
  (*   { *)
  (*     iDestruct (access_update (s ∖ {[i]}) with "Hauth Hsingle") as ">[Hauth Hsingle]". *)
  (*     rewrite big_sepS_union;last set_solver + H. *)
  (*     rewrite big_sepS_singleton. *)
  (*     iFrame "Hsingle". *)
  (*     iApply ("IH" with "Hauth Hfrag"). *)
  (*    } *)
  (*   { *)
  (*     intros. *)
  (*     destruct (b' !! x2) as [p2|] eqn: Hlookup2, (b' !! x1) as [p1|] eqn:Hlookup1; *)
  (*       try destruct p1 as [q1 []]; try destruct p2 as [q2 []]; rewrite ?lookup_insert_ne ?Hlookup1 ?Hlookup2 //;last eauto. *)
  (*     apply insert_commute. *)
  (*     done. *)
  (*   } *)
  (*   set_solver + H. *)
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
  (*  ghost_map_auth gen_own_name 1 (get_own_gmap σ)==∗ *)
  (*  ghost_map_auth gen_own_name 1 (<[i:= (sown ∪ sps)]>(get_own_gmap σ)) ∗ *)
  (*  O@i:={1}[sown ∪ sps]. *)
  (* Proof. *)
  (*   iIntros (Hsps) "HO Hown". *)
  (*   rewrite own_mapsto_eq /own_mapsto_def. *)
  (*   iApply (gen_pagetable_update_union with "HO Hown");eauto. *)
  (* Qed. *)

End pagetable_rules.
