From HypVeri.algebra Require Import base.
From HypVeri Require Import lang_extra.

Section mem_rules.

  Context `{vmG : gen_VMG Σ}.
  Implicit Type σ : state.
  Implicit Types w: Word.
  Implicit Types a: Addr.


  (* rules for memory points-to *)

  Lemma mem_dupl_false a w1 w2:
    a ->a w1 -∗ a ->a w2 -∗ False.
  Proof using.
    rewrite mem_mapsto_eq /mem_mapsto_def.
    iIntros "Ha1 Ha2".
    iDestruct (ghost_map_elem_valid_2 with "Ha1 Ha2") as %Hvalid.
    destruct Hvalid as [Hvalid _].
    apply dfrac_valid_own_r in Hvalid.
    inversion Hvalid.
  Qed.

  Lemma mem_neq a1 a2 w1 w2:
    a1 ->a w1 -∗ a2 ->a w2 -∗ ⌜ a1 <> a2⌝.
  Proof using.
    iIntros "Ha1 Ha2".
    destruct (decide (a1 = a2)).
    - rewrite e //.
      iDestruct (mem_dupl_false with "Ha1 Ha2") as %[].
    - done.
  Qed.

  Lemma gen_mem_valid {σ} a w:
    ghost_map_auth gen_mem_name 1 (get_mem σ) -∗
    a ->a w -∗
    ⌜(get_mem σ) !! a = Some w⌝.
  Proof.
    iIntros "Hσ Ha".
    rewrite mem_mapsto_eq /mem_mapsto_def.
    iApply (ghost_map_lookup with "Hσ Ha").
  Qed.

  Lemma gen_mem_valid_SepM {σ} mem:
    ghost_map_auth gen_mem_name 1 (get_mem σ) -∗
    ([∗ map] a↦w ∈ mem, a ->a w)-∗
    ([∗ map] a↦w ∈ mem, ⌜(get_mem σ) !! a = Some w⌝).
  Proof.
    iIntros "Hσ Hmem".
    rewrite mem_mapsto_eq /mem_mapsto_def.
    iDestruct ((ghost_map_lookup_big mem) with "Hσ Hmem") as "%Hincl".
    iApply big_sepM_pure.
    iPureIntro.
    intros a w H.
    apply (lookup_weaken mem (get_mem σ) _ _ H Hincl) .
  Qed.

  Lemma gen_mem_valid_SepL {σ} al ml:
    NoDup al ->
    ghost_map_auth gen_mem_name 1 (get_mem σ) -∗
    ([∗ list] a;w ∈ al;ml, a ->a w)-∗
    ([∗ list] a;w ∈ al;ml, ⌜(get_mem σ) !! a = Some w⌝).
  Proof.
    iIntros (Hnodup) "Hσ Hmem".
    iDestruct (big_sepL2_alt with "Hmem") as "[%Heqlen Hmem]".
    iApply big_sepL2_alt.
    iSplitR;eauto.
    rewrite <- (@map_to_list_to_map Addr (gmap Addr) _  _  _  _ _ _ _ _ _ Word (zip al ml)).
    2: { rewrite fst_zip;[eauto|lia].  }
    rewrite -(big_opM_map_to_list (λ a w, ⌜(get_mem σ) !! a = Some w ⌝%I)).
    rewrite -(big_opM_map_to_list (λ a w, (a ->a w)%I)).
    iApply (gen_mem_valid_SepM with "Hσ Hmem").
  Qed.

  Lemma gen_mem_valid_SepL_pure {σ} al ml:
    NoDup al ->
    ghost_map_auth gen_mem_name 1 (get_mem σ) -∗
    ([∗ list] a;w ∈ al;ml,  a ->a w) -∗
    ⌜∀ (k : nat) (y1 y2 : Addr),
      al !! k = Some y1 → ml !! k = Some y2 → get_mem σ !! y1 = Some y2⌝.
  Proof.
    iIntros (Hnodup) "Hσ Hmem".
    iDestruct (gen_mem_valid_SepL with "Hσ Hmem") as "H";eauto.
    iApply (big_sepL2_pure_1 with "H").
  Qed.

  Lemma gen_mem_valid2 {σ} a1 w1 a2 w2:
    ghost_map_auth gen_mem_name 1 (get_mem σ) -∗
    a1 ->a w1 -∗
    a2 ->a w2 -∗
    ⌜(get_mem σ) !! a1 = Some w1⌝ ∗ ⌜(get_mem σ) !! a2 = Some w2⌝.
  Proof.
    iIntros "Hσ Ha1 Ha2".
    iDestruct (mem_neq with "Ha1 Ha2") as "%Hne".
    iDestruct (gen_mem_valid_SepM {[a1:=w1;a2:=w2]} with "Hσ [Ha1 Ha2]") as "%Hforall";eauto.
    { rewrite !big_sepM_insert ?big_sepM_empty;eauto.
      iFrame.
      by simplify_map_eq.
    }
    iPureIntro. split.
    by apply (Hforall a1 w1 (lookup_insert _ a1 w1)).
    apply (Hforall a2 w2); by simplify_map_eq.
  Qed.

  Lemma gen_mem_update1 {σ} a w w':
    ghost_map_auth gen_mem_name 1 (get_mem σ) -∗
    a ->a w ==∗
    ghost_map_auth gen_mem_name 1 (<[a:=w']>(get_mem σ)) ∗
    a ->a w'.
  Proof.
    iIntros "Hσ Ha".
    rewrite mem_mapsto_eq /mem_mapsto_def.
    iDestruct (ghost_map_update w' with "Hσ Ha") as ">[Hσ Ha]".
    by iFrame.
  Qed.

  Lemma gen_mem_update_SepM {σ} (mem mem': mem):
    dom (gset _) mem = dom (gset _) mem' ->
    ghost_map_auth gen_mem_name 1 (get_mem σ) -∗
    ([∗ map] a↦w ∈ mem, a ->a w) ==∗
    ghost_map_auth gen_mem_name 1 (mem' ∪ (get_mem σ)) ∗
    [∗ map] a↦w ∈ mem', a ->a w.
  Proof.
    Admitted.
    (* iIntros (Hnodup Hlen) "Hσ Hmm". *)
    (* iDestruct (big_sepL2_alt with "Hmm") as "[% Hmm]". *)
    (* rewrite <- (@map_to_list_to_map Addr (gmap Addr) _  _  _  _ _ _ _ _ _ Word _). *)
    (* 2: { rewrite fst_zip //;lia. } *)
    (* rewrite -(big_opM_map_to_list (λ a w,  (a ->a w)%I) _ ). *)
    (* rewrite  mem_mapsto_eq /mem_mapsto_def. *)
    (* iDestruct ((ghost_map_update_big _  (list_to_map (zip ads wl'))) with "Hσ Hmm") as ">[Hσ Hmm]". *)
    (* { rewrite  !dom_list_to_map_L. f_equal.  rewrite !fst_zip  //. lia. lia. } *)
    (* rewrite (big_opM_map_to_list (λ a w,  (a ↪[gen_mem_name] w)%I) _ ). *)
    (* rewrite map_to_list_to_map. *)
    (* 2 : { rewrite fst_zip //. lia. } *)
    (* rewrite big_sepL2_alt. *)
    (* iFrame "Hσ Hmm". rewrite -Hlen H //. *)
  (* Qed. *)



  (* Definition mem_region (instr: list Word) (b:Addr):= *)
  (*   ([∗ list] a;w ∈ (finz.seq b (length instr));instr, (a ->a w))%I. *)

  (* This definition implicitly requires the length of instr is equal to/less than page_size  *)
  (* Definition mem_page (instr: list Word) (p: PID):= *)
  (*   ([∗ list] a;w ∈ (finz.seq (of_pid p) (Z.to_nat page_size));instr, (a ->a w))%I. *)

  Definition memory_page (p : PID) (mem: mem): iProp Σ:=
    ⌜dom (gset Addr) mem = list_to_set (addr_of_page p)⌝ ∗ [∗ map] k ↦ v ∈ mem, k ->a v.

  Definition set_of_addr (ps:gset PID) := (set_fold (λ p (acc:gset Addr), list_to_set (addr_of_page p) ∪ acc) ∅ ps).

  Definition memory_pages (ps :gset PID) (mem:mem): iProp Σ:=
    ⌜dom (gset Addr) mem = set_of_addr ps⌝ ∗ [∗ map] k ↦ v ∈ mem, k ->a v.


  (* lemmas about [memory_pages] *)
  Notation fold_union_addr_of_page b ps :=
    (set_fold (λ (p : PID) (acc : gset Addr), list_to_set (addr_of_page p) ∪ acc) b ps).

  Lemma fold_union_addr_of_page_strong_assoc_comm (X : gset PID):
    ∀ (x1 x2 : PID) (b' : gset Addr),
    x1 ∈ X
    → x2 ∈ X
    → x1 ≠ x2
    → list_to_set (addr_of_page x1) ∪ (list_to_set (addr_of_page x2) ∪ b') =
        list_to_set (addr_of_page x2) ∪ (list_to_set (addr_of_page x1) ∪ b').
  Proof.
    intros ? ? b Hin1 Hin2 Hneq.
    rewrite assoc_L.
    rewrite assoc_L.
    f_equal.
    rewrite comm_L //.
  Qed.

  Lemma fold_union_addr_of_page_comm (s1 : gset PID) (s2 s3: gset Addr) :
    fold_union_addr_of_page (s3 ∪ s2) s1 = s3 ∪ fold_union_addr_of_page s2 s1.
  Proof.
    revert s1 s2 s3.
    induction s1 using set_ind_L.
    {
      intros.
      rewrite !set_fold_empty.
      done.
    }
    {
      intros.
      rewrite (set_fold_disj_union_strong _ _  (s3 ∪ s2) {[x]} X).
      {
        rewrite set_fold_singleton.
        assert ((list_to_set (addr_of_page x) ∪ (s3 ∪ s2)) = (s3 ∪ (list_to_set (addr_of_page x) ∪  s2))) as ->.
        {
          rewrite (union_assoc_L _ s3 s2).
          rewrite (union_comm_L _ s3).
          rewrite union_assoc_L //.
        }
        rewrite IHs1.
        rewrite (set_fold_disj_union_strong _ _ s2 {[x]} X).
        rewrite set_fold_singleton //.
        apply fold_union_addr_of_page_strong_assoc_comm.
        set_solver + H.
      }
      apply fold_union_addr_of_page_strong_assoc_comm.
      set_solver + H.
    }
  Qed.

  Lemma fold_union_addr_of_page_disj_aux (p: PID) (s1 : gset PID) (s2: gset Addr) : p ∉ s1 ->
    (list_to_set (addr_of_page p)) ## s2 ->
    (list_to_set (addr_of_page p)) ## (fold_union_addr_of_page s2 s1).
  Proof.
    revert s1 s2.
    induction s1 using set_ind_L.
    {
      intros.
      rewrite set_fold_empty.
      done.
    }
    {
      intros.
      rewrite (set_fold_disj_union_strong _ _ s2 {[x]} X).
      {
        rewrite set_fold_singleton.
        rewrite fold_union_addr_of_page_comm.
        apply disjoint_union_r.
        split.
        { apply addr_of_page_disj. set_solver + H0. }
        apply IHs1.
        set_solver + H0.
        done.
      }
      apply fold_union_addr_of_page_strong_assoc_comm.
      set_solver + H.
    }
  Qed.

  Lemma set_of_addr_disj (s1 s2 : gset PID) :
    s1 ## s2 ->
    (set_of_addr s1) ## (set_of_addr s2).
  Proof.
    revert s1 s2.
    rewrite /set_of_addr.
    induction s1 using set_ind_L.
    {
      intros.
      rewrite set_fold_empty.
      done.
    }
    {
      intros ? Hdisj.
      rewrite (set_fold_disj_union_strong _ _ _ {[x]} X).
      {
        rewrite set_fold_singleton.
        rewrite fold_union_addr_of_page_comm.
        apply disjoint_union_l.
        split.
        { apply fold_union_addr_of_page_disj_aux.
          set_solver + Hdisj.
          apply disjoint_empty_r.
        }
        { apply IHs1.
          set_solver + Hdisj. }
      }
      apply fold_union_addr_of_page_strong_assoc_comm.
      set_solver + H.
    }
  Qed.

  Lemma set_of_addr_union (s1 s2 : gset PID):
    s1 ## s2 ->
    set_of_addr (s1 ∪ s2) =
      (set_of_addr s1) ∪ (set_of_addr s2).
  Proof.
    intro Hdisj.
    rewrite /set_of_addr.
    rewrite (set_fold_disj_union_strong _ _ _ s1 s2).
    {
      rewrite -fold_union_addr_of_page_comm.
      rewrite union_empty_r_L //.
    }
    apply fold_union_addr_of_page_strong_assoc_comm.
    exact Hdisj.
  Qed.

  Lemma elem_of_set_of_addr a p ps:
    a ∈ addr_of_page p ->
    p ∈ ps ->
    a ∈ set_of_addr ps.
  Proof.
    revert ps.
    induction ps using set_ind_L.
    {
      intros.
      inversion H0.
    }
    intros Hin_a Hin_p.
    destruct (decide (p = x)).
    {
      subst x.
      rewrite set_of_addr_union.
      {
        apply elem_of_union_l.
        rewrite /set_of_addr.
        rewrite set_fold_singleton union_empty_r.
        rewrite elem_of_list_to_set //.
      }
      rewrite disjoint_singleton_l //.
    }
    {
      rewrite set_of_addr_union.
      {
       apply elem_of_union_r.
       apply IHps.
       done.
       apply elem_of_union in Hin_p.
       destruct Hin_p.
       rewrite elem_of_singleton // in H0.
       done.
      }
      rewrite disjoint_singleton_l //.
    }
    Qed.

  Lemma elem_of_set_of_addr_tpa a ps:
    (tpa a) ∈ ps -> a ∈ set_of_addr ps.
  Proof.
    apply elem_of_set_of_addr.
    apply elem_of_addr_of_page_tpa.
  Qed.

  Lemma elem_of_memory_pages_lookup (m: gmap Addr Word) a ps:
    (tpa a) ∈ ps ->
    dom (gset Addr) m = set_of_addr ps ->
    is_Some (m !! a).
  Proof.
    intros Hin Heq_dom.
    apply elem_of_set_of_addr_tpa in Hin.
    rewrite -Heq_dom in Hin.
    by apply elem_of_dom.
  Qed.

  Lemma set_of_addr_empty : set_of_addr ∅ = ∅.
  Proof.
    rewrite /set_of_addr set_fold_empty //.
  Qed.

  Lemma set_of_addr_singleton p : set_of_addr {[p]} = (list_to_set (addr_of_page p)).
  Proof.
    rewrite /set_of_addr.
    unfold fold_union_addr_of_page.
    cbn.
    rewrite elements_singleton.
    cbn.
    rewrite union_empty_r_L //.
  Qed.

  Lemma memory_pages_split_union {mem} (ps1 ps2 :gset PID):
    ps1 ## ps2 ->
    memory_pages (ps1 ∪ ps2) mem ⊣⊢ ∃ mem1 mem2, memory_pages ps1 mem1 ∗ memory_pages ps2 mem2 ∗ ⌜mem1 ∪ mem2 = mem⌝.
  Proof.
    intro Hdisj.
    iSplit.
    {
      iIntros "[%Hdom mem]".
      rewrite set_of_addr_union in Hdom;last done.
      pose proof (dom_union_inv_L mem _ _ (set_of_addr_disj _ _ Hdisj) Hdom) as Hsplit.
      destruct Hsplit as (m1 & m2 & Heq & Hdisj_m & Hdom1 & Hdom2).
      rewrite Heq.
      rewrite big_sepM_union;last done.
      iDestruct "mem" as "[mem1 mem2]".
      iExists m1, m2.
      iFrame.
      done.
    }
    {
      iIntros "(%m1 & %m2 & [%Hdom1 mem1] & [%Hdom2 mem2] & %Heq)".
      rewrite -Heq.
      iSplitL "".
      iPureIntro.
      rewrite dom_union_L.
      rewrite Hdom1 Hdom2.
      rewrite /set_of_addr set_fold_disj_union_strong.
      {
        rewrite -fold_union_addr_of_page_comm.
        rewrite union_empty_r_L //.
      }
      apply fold_union_addr_of_page_strong_assoc_comm.
      exact Hdisj.
      rewrite big_sepM_union.
      iFrame.
      apply map_disjoint_dom.
      rewrite Hdom1 Hdom2.
      apply set_of_addr_disj.
      done.
    }
  Qed.

  Lemma memory_pages_split_diff {mem} s s':
    s' ⊆ s ->
    memory_pages s mem ⊣⊢ ∃ mem1 mem2, memory_pages (s ∖ s') mem1 ∗ memory_pages s' mem2 ∗ ⌜mem1 ∪ mem2 = mem⌝.
  Proof.
    intro Hsub.
    rewrite -memory_pages_split_union;last set_solver +.
    assert (s ∖ s' ∪ s' = s) as ->.
    {
      rewrite difference_union_L.
      set_solver + Hsub.
    }
    done.
  Qed.

  Lemma memory_pages_singleton {mem} p:
    memory_pages {[p]} mem ⊣⊢ memory_page p mem.
  Proof.
    rewrite /memory_pages /memory_page.
    rewrite set_of_addr_singleton.
    done.
  Qed.

  Lemma memory_pages_split_singleton {mem} p s:
    p ∈ s ->
    memory_pages s mem ⊣⊢ ∃ mem1 mem2, memory_pages (s ∖ {[p]}) mem1  ∗ memory_page p mem2 ∗ ⌜mem1 ∪ mem2 = mem⌝.
  Proof.
    intro Hin.
    iSplit.
    {
      iIntros  "mem".
      iDestruct (memory_pages_split_diff s {[p]} with "mem") as "(%m1 & %m2 & mem1 & mem2)".
      set_solver + Hin.
      iExists m1, m2.
      rewrite memory_pages_singleton.
      iFrame.
    }
    {
      iIntros "(%m1 & %m2 & mem1 & mem2 & %Heq)".
      rewrite -Heq -memory_pages_singleton.
      iApply (memory_pages_split_diff).
      2:{  iExists m1, m2. iFrame "mem1 mem2". done. }
      set_solver + Hin.
    }
  Qed.

  Lemma big_sepM_not_disj`{Countable K} {V :Type} (m1 m2: gmap K V) (Φ: K -> V -> iProp Σ) :
    ¬ (m1 ##ₘ m2) ->
    (∀ k v1 v2, Φ k v1 ∗ Φ k v2 -∗ False) ⊢
    ([∗ map] k↦v ∈ m1, Φ k v) ∗ ([∗ map] k↦v ∈ m2, Φ k v) -∗ False.
  Proof.
    iIntros (Hnot_disj) "Hexcl [m1 m2]".
    assert (∃ k, is_Some(m1 !! k) ∧ is_Some(m2 !! k)) as Hexists.
    {
      rewrite map_disjoint_dom elem_of_disjoint in Hnot_disj.
      apply  not_set_Forall_Exists in Hnot_disj;last eapply _.
      destruct Hnot_disj as [k [Hin H']].
      exists k.
      split.
      rewrite elem_of_dom // in Hin.
      simpl in H'.
      apply dec_stable in H'.
      rewrite elem_of_dom // in H'.
    }
    destruct Hexists as [k [Hin1 Hin2]].
    destruct Hin1 as [v1 Hlookup1].
    destruct Hin2 as [v2 Hlookup2].
    iDestruct (big_sepM_lookup with "m1") as "m1";first exact Hlookup1.
    iDestruct (big_sepM_lookup with "m2") as "m2";first exact Hlookup2.
    iApply ("Hexcl" $! k).
    iFrame.
  Qed.

  Lemma memory_pages_disj_singleton {mem mem'} p  : memory_page p mem ∗ memory_page p mem'⊢ False.
  Proof.
    iIntros " [[%Hdom1 mem1] [%Hdom2 mem2]]".
    iApply (big_sepM_not_disj with "[] [$mem1 $mem2]").
    rewrite map_disjoint_dom.
    rewrite Hdom1 Hdom2.
    rewrite disjoint_intersection_L.
    pose proof (addr_of_page_not_empty_set p) as Hne.
    rewrite intersection_idemp_L.
    done.
    iIntros (k v1 v2) "[Hp1 Hp2]".
    rewrite mem_mapsto_eq /mem_mapsto_def.
    iDestruct (ghost_map_elem_valid_2 with "Hp1 Hp2") as "%Hvalid".
    destruct Hvalid as [Hvalid _].
    rewrite dfrac_op_own in Hvalid.
    rewrite -> dfrac_valid_own in Hvalid.
    exfalso.
    eauto using Qp_not_add_le_r.
  Qed.

  Lemma memory_pages_disj {mem mem'} s1 s2 : memory_pages s1 mem ∗ memory_pages s2 mem' ⊢ ⌜s1 ## s2⌝.
  Proof.
    iIntros "[mem1 mem2]".
    rewrite elem_of_disjoint.
    iIntros (p Hin1 Hin2).
    iPoseProof (memory_pages_split_singleton p _ Hin1) as "[Hsplit _]".
    iDestruct ("Hsplit" with "[mem1]") as "(% & % & mem1' & mem1_p & _)".
    iFrame.
    iPoseProof (memory_pages_split_singleton p _ Hin2) as "[Hsplit' _]".
    iDestruct ("Hsplit'" with "[mem2]") as "(% & % & mem2' & mem2_p & _)".
    iFrame.
    iApply (memory_pages_disj_singleton with "[$mem1_p $mem2_p]").
  Qed.

  Lemma memory_pages_empty : ⊢ memory_pages ∅ ∅.
  Proof.
    iIntros.
    rewrite /memory_pages.
    iSplit.
    rewrite dom_empty_L set_of_addr_empty //.
    rewrite big_sepM_empty //.
  Qed.

  Lemma gen_mem_update_pages{σ mem_ps} ps (mem_ps': mem):
    dom (gset _) mem_ps = dom (gset _) mem_ps' ->
    ghost_map_auth gen_mem_name 1 (get_mem σ) -∗
    memory_pages ps mem_ps ==∗
    ghost_map_auth gen_mem_name 1 (mem_ps' ∪ (get_mem σ)) ∗
    memory_pages ps mem_ps'.
  Proof.
    iIntros (Hdom) "auth [%Hdom_mem frag]".
    rewrite /memory_page.
    iDestruct ((gen_mem_update_SepM mem_ps mem_ps') with "auth frag") as ">[auth frag]";first auto.
    iModIntro.
    iFrame "auth frag".
    rewrite -Hdom //.
  Qed.

  Lemma gen_mem_update_page{σ mem_p} p (mem_p': mem):
    dom (gset _) mem_p = dom (gset _) mem_p' ->
    ghost_map_auth gen_mem_name 1 (get_mem σ) -∗
    memory_page p mem_p ==∗
    ghost_map_auth gen_mem_name 1 (mem_p' ∪ (get_mem σ)) ∗
    memory_page p mem_p'.
  Proof.
    rewrite -!memory_pages_singleton.
    iIntros (Hdom) "H".
    iApply (gen_mem_update_pages {[p]} mem_p');eauto.
  Qed.


  (* Lemma mem_pages_SepL2_length_pure ps wss: *)
  (*   ([∗ list] p;ws ∈ ps;wss, mem_page ws p) ⊢ ⌜ (forall ws, ws ∈ wss -> length ws = (Z.to_nat page_size)) ⌝. *)
  (* Proof. *)
  (*   revert ps. *)
  (*   rewrite /mem_page. *)
  (*   induction wss. *)
  (*   - iIntros (?) "Hl". *)
  (*     iPureIntro; intros; inversion H. *)
  (*   -  iIntros (?) "Hl". *)
  (*      destruct ps; cbn. *)
  (*      { iExFalso; done. } *)
  (*      { iIntros (??). *)
  (*        iDestruct "Hl" as "[Hl Hls]". *)
  (*        iDestruct (big_sepL2_length with  "Hl") as "%". *)
  (*        rewrite finz_seq_length in H. *)
  (*        apply elem_of_cons in a1 as [Heqa | Hin]. *)
  (*        subst a0. *)
  (*        done. *)
  (*        iDestruct ((IHwss ps) with "Hls") as "%Hforall". *)
  (*        iPureIntro. *)
  (*        by apply Hforall. } *)
  (* Qed. *)

  Lemma memory_pages_acc p ps mem:
    p ∈ ps ->
    memory_pages ps mem ⊢
    ∃ mem_p,  memory_page p mem_p ∗ (memory_page p mem_p -∗  memory_pages ps mem).
  Proof.
    iIntros (Hin) "mem".
    iPoseProof (memory_pages_split_singleton p ps Hin) as "[Hsplit Hsplit2]".
    iDestruct ("Hsplit" with "[mem]") as (m1 m2) "[Hrest [Hsingle %Heq]]".
    { iFrame. }
    iExists m2.
    iFrame.
    iIntros "Hsingle".
    iApply ("Hsplit2" with "[Hrest Hsingle]").
    iExists m1, m2.
    iFrame.
    done.
  Qed.

  (* Lemma mem_pages_to_mem_region_SepL2 (ps: list PID) (wss: list (list Word)): *)
  (*   ([∗ list] p;ws ∈ ps;wss, mem_page ws p) -∗ *)
  (*   [∗ list] a;w ∈ (list_pid_to_addr ps);(flat_list_list_word wss), a ->a w. *)
  (* Proof. *)
  (*   rewrite /mem_page /list_pid_to_addr /flat_list_list_word. *)
  (*   iRevert (wss). *)
  (*   iInduction ps as [|p ps'] "IH";cbn. *)
  (*   iIntros (?) "Hl". *)
  (*   iDestruct (big_sepL2_alt with "Hl") as "[%Heqlen Hl]". *)
  (*   destruct a;try inversion Heqlen. *)
  (*   done. *)
  (*   iIntros (wss) "Hlist". *)
  (*   destruct wss;cbn;try done. *)
  (*   iDestruct ("Hlist") as "[Hl Hlist]". *)
  (*   iApply (big_sepL2_app with "Hl"). *)
  (*   by iApply "IH". *)
  (* Qed. *)

  (* Lemma mem_region_to_mem_pages_SepL2 (ps: list PID) (wss: list (list Word)): *)
  (*   (forall ws', ws' ∈ wss -> length ws' = (Z.to_nat page_size)) -> *)
  (*   ([∗ list] a;w ∈ (list_pid_to_addr ps);(flat_list_list_word wss), a ->a w) -∗ *)
  (*   ([∗ list] p;ws ∈ ps;wss, mem_page ws p). *)
  (* Proof. *)
  (*   rewrite /mem_page /list_pid_to_addr /flat_list_list_word. *)
  (*   iRevert (wss). *)
  (*   iInduction ps as [|p ps'] "IH";cbn. *)
  (*   iIntros (??) "Hl". *)
  (*   iDestruct (big_sepL2_alt with "Hl") as "[%Heqlen Hl]". *)
  (*   destruct a. *)
  (*   done. *)
  (*   assert (length l = Z.to_nat 1000) as Heqlen'. *)
  (*   { apply x. apply elem_of_cons;left;done. } *)
  (*   rewrite app_length Heqlen' in Heqlen. *)
  (*   inversion Heqlen. *)
  (*   iIntros (wss Hlen) "Hlist". *)
  (*   destruct wss;cbn;try done. *)
  (*   iDestruct (big_sepL2_app_inv with "Hlist") as "Hlist". *)
  (*   { left. rewrite finz_seq_length. symmetry;apply Hlen.  apply elem_of_cons;left;done. } *)
  (*   iDestruct ("Hlist") as "[Hl Hlist]". *)
  (*   iFrame "Hl". *)
  (*   iApply "IH". *)
  (*   { iPureIntro. intros. *)
  (*     apply Hlen. *)
  (*     apply elem_of_cons;right;done. } *)
  (*   done. *)
  (* Qed. *)


End mem_rules.
