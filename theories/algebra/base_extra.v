From HypVeri.algebra Require Import base.
From HypVeri Require Import stdpp_extra.

Section predicates.

  Context `{hypconst : !HypervisorConstants}.
  Context `{Countable K} {V: Type}.

  Definition is_total_gmap (m : gmap K V) := ∀ (k : K), is_Some (m !! k).

  Lemma is_total_gmap_insert (m : gmap K V) k v:
    is_total_gmap m -> is_total_gmap (<[k := v]>m).
  Proof.
    intros Ht. intros k'.
    destruct (decide (k'=k)).
    subst k'. rewrite lookup_insert //.
    rewrite lookup_insert_ne //.
  Qed.

End predicates.

Section preservation.
  Context `{hypconst : !HypervisorConstants}.

  Implicit Type σ: state.

  Lemma preserve_get_reg_gmap σ' σ :
    get_reg_files σ = get_reg_files σ' -> get_reg_gmap σ = get_reg_gmap σ'.
  Proof.
    intro Heq_proj.
    rewrite /get_reg_gmap Heq_proj //.
  Qed.

  Lemma preserve_get_mb_gmap σ' σ :
    get_mail_boxes σ = get_mail_boxes σ' -> get_mb_gmap σ = get_mb_gmap σ'.
  Proof.
    intro Heq_proj.
    rewrite /get_mb_gmap Heq_proj //.
  Qed.

  Lemma preserve_get_rx_gmap σ' σ :
    get_mail_boxes σ = get_mail_boxes σ' -> get_rx_gmap σ = get_rx_gmap σ'.
  Proof.
    intro Heq_proj.
    rewrite /get_rx_gmap Heq_proj //.
  Qed.

  Lemma preserve_get_own_gmap σ' σ :
    get_page_table σ = get_page_table σ' -> get_own_gmap σ = get_own_gmap σ'.
  Proof.
    intro Heq_proj.
    rewrite /get_own_gmap Heq_proj //.
  Qed.

  Lemma preserve_get_access_gmap σ' σ :
    get_page_table σ = get_page_table σ' -> get_access_gmap σ = get_access_gmap σ'.
  Proof.
    intro Heq_proj.
    rewrite /get_access_gmap Heq_proj //.
  Qed.

  Lemma preserve_get_excl_gmap σ' σ :
    get_page_table σ = get_page_table σ' -> get_excl_gmap σ = get_excl_gmap σ'.
  Proof.
    intro Heq_proj.
    rewrite /get_excl_gmap Heq_proj //.
  Qed.

  Lemma preserve_get_trans_gmap σ' σ :
    (get_transactions σ) = (get_transactions σ') -> get_trans_gmap σ = get_trans_gmap σ'.
  Proof.
    intro Heq_proj.
    rewrite /get_trans_gmap /get_transactions_gmap Heq_proj //.
  Qed.

  Lemma preserve_get_hpool_gset σ' σ :
    (get_transactions σ) = (get_transactions σ') -> get_hpool_gset σ = get_hpool_gset σ'.
  Proof.
    intro Heq_proj.
    rewrite /get_hpool_gset /get_transactions_gmap Heq_proj //.
  Qed.

  Lemma preserve_get_retri_gmap σ' σ :
    (get_transactions σ) = (get_transactions σ') -> get_retri_gmap σ = get_retri_gmap σ'.
  Proof.
    intro Heq_proj.
    rewrite /get_retri_gmap /get_transactions_gmap Heq_proj //.
  Qed.

  Lemma preserve_inv_trans_wellformed σ' σ :
    (get_transactions σ) = (get_transactions σ') -> inv_trans_wellformed σ = inv_trans_wellformed σ'.
  Proof.
    intro Heq_proj.
    rewrite /inv_trans_wellformed Heq_proj //.
  Qed.

  Lemma preserve_inv_trans_pgt_consistent σ' σ :
    (get_transactions σ) = (get_transactions σ') ->
    (get_page_table σ) = (get_page_table σ') ->
    inv_trans_pgt_consistent σ = inv_trans_pgt_consistent σ'.
  Proof.
    intros Heq_proj_trans Heq_proj_pgt.
    rewrite /inv_trans_pgt_consistent Heq_proj_trans Heq_proj_pgt //.
  Qed.

  Lemma preserve_inv_trans_ps_disj σ' σ :
    (get_transactions σ) = (get_transactions σ') -> inv_trans_ps_disj σ = inv_trans_ps_disj σ'.
  Proof.
    intro Heq_proj.
    rewrite /inv_trans_ps_disj Heq_proj //.
  Qed.

End preservation.

Section helpers.

  Context `{hypconst : !HypervisorConstants}.

  Definition  update_pgt_gmap {A : Type } upd (gm:gmap PID A) (sps: gset PID):=
    (set_fold (λ p acc, upd acc p) gm sps).

  Definition flip_excl_gmap :=
    update_pgt_gmap (λ (gm: gmap _ bool) (p:PID), match (gm !! p) with
                                | Some (b) => <[p:= negb b]>gm
                                | _ => gm
                                end).

  Definition upd_own_gmap (v:VMID) :=
    update_pgt_gmap (λ (gm: gmap _ (option VMID)) (p:PID), match (gm !! p) with
                                | Some (_) => <[p:= Some v]>gm
                                | _ => gm
                                end).

  (* lemmas about pages_in_trans *)
  Lemma elem_of_pages_in_trans' p trans:
    p ∈ pages_in_trans' trans <-> ∃ h tran, trans !! h = Some (Some tran) ∧ p ∈ tran.1.1.2.
  Proof.
    rewrite /pages_in_trans'.
    induction trans using map_ind.
    {
      rewrite map_fold_empty //.
      split;intros;first done.
      destruct H as [? [? [? ?]]].
      done.
    }
    {
      rewrite map_fold_insert_L.
      2:{
        intros w1 w2 trans1 trans2 y.
        intros Hneq Hlookup1 Hlookup2.
        destruct trans1, trans2;
        set_solver +.
      }
      2: done.
      destruct x as [x|].
      + rewrite elem_of_union.
        split;intro Hin.
        destruct Hin as [Hin|Hin].
        exists i, x.
        split;auto.
        rewrite lookup_insert_Some;left;done.
        apply IHtrans in Hin as [h [x' [Hlookup Hin']]].
        exists h, x'.
        split;auto.
        rewrite lookup_insert_Some;right.
        split;auto.
        intro.
        subst i.
        rewrite H // in Hlookup.
        destruct (decide (p ∈ x.1.1.2)).
        left;done.
        right.
        apply IHtrans.
        destruct Hin as [h [x' [Hlookup Hin']]].
        destruct (decide (i = h)).
        subst i.
        rewrite lookup_insert_Some in Hlookup.
        destruct Hlookup as [? | [? ?]].
        destruct H0;subst.
        inversion H1;subst.
        contradiction.
        contradiction.
        exists h, x'.
        split;last done.
        rewrite lookup_insert_ne in Hlookup.
        done.
        done.
      + rewrite IHtrans.
        split.
        intros [h [tran [Hlookup Hin]]].
        exists h, tran.
        split;auto.
        destruct (decide (i= h)).
        subst i. rewrite H in Hlookup; done.
        rewrite lookup_insert_ne //.
        intros [h [tran [Hlookup Hin]]].
        destruct (decide (i= h)).
        subst i. rewrite lookup_insert_Some in Hlookup.
        destruct Hlookup as [[_ ?]|[? _]];done.
        exists h, tran.
        split;auto.
        rewrite lookup_insert_ne in Hlookup;auto.
    }
  Qed.

  Lemma subseteq_pages_in_trans' h tran trans:
    trans !! h = Some (Some tran) ->
    tran.1.1.2 ⊆ pages_in_trans' trans.
  Proof.
    intros Hlk.
    rewrite /pages_in_trans'.
    induction trans using map_ind.
    {
      rewrite map_fold_empty //.
    }
    {
      rewrite map_fold_insert_L.
      2:{
        intros w1 w2 trans1 trans2 y.
        intros Hneq Hlookup1 Hlookup2.
        destruct trans1, trans2;
        set_solver +.
      }
      2: done.
      destruct (decide (i = h)).
      {
        subst i.
        rewrite lookup_insert in Hlk.
        inversion Hlk.
        subst x.
        set_solver +.
      }
      {
        feed specialize IHtrans.
        rewrite lookup_insert_ne in Hlk;auto.
        destruct x;
        set_solver + IHtrans.
      }
    }
  Qed.

  Lemma pages_in_trans_subseteq' m m':
    m' ⊆ m -> pages_in_trans' m' ⊆ pages_in_trans' m.
  Proof.
    intros Hsub.
    rewrite /pages_in_trans'.
    induction m' using map_ind.
    {
      rewrite map_fold_empty //.
    }
    {
      rewrite map_fold_insert_L.
      2:{
        intros w1 w2 trans1 trans2 y.
        intros Hneq Hlookup1 Hlookup2.
        destruct trans1, trans2;
        set_solver +.
      }
      2: done.
      pose proof Hsub.
      rewrite map_subseteq_spec in Hsub.
      specialize (Hsub i x).
      feed specialize Hsub.
      rewrite lookup_insert //.
      destruct x as [x|].
      + apply union_least.
        {
          rewrite elem_of_subseteq.
          intros.
          rewrite elem_of_pages_in_trans'.
          exists i, x.
          split;done.
        }
        apply IHm'.
        rewrite map_subseteq_spec.
        intros.
        rewrite map_subseteq_spec in H0.
        apply H0.
        rewrite lookup_insert_Some.
        right.
        split;last done.
        intro.
        subst.
        rewrite H1 in H.
        done.
      + apply IHm'.
        apply map_subseteq_spec.
        intros.
        rewrite map_subseteq_spec in H0.
        apply (H0 i0 x).
        destruct (decide (i = i0)).
        subst i0.
        rewrite H // in H1.
        rewrite lookup_insert_ne //.
    }
  Qed.

  Lemma pages_in_trans_insert_None'{h tran trans}:
    trans !! h = None ->
    pages_in_trans' (<[h := Some tran]> trans) = tran.1.1.2 ∪ pages_in_trans' trans.
  Proof.
    intros Hlk.
    rewrite /pages_in_trans'.
    rewrite map_fold_insert_L.
    2:{
      intros w1 w2 trans1 trans2 y.
      intros Hneq Hlookup1 Hlookup2.
      destruct trans1, trans2;
      set_solver +.
    }
    2: done.
    done.
  Qed.

  Lemma pages_in_trans_update' {h tran trans}:
    trans !! h = Some None ->
    pages_in_trans' (<[h:=Some tran]> trans) = tran.1.1.2 ∪ pages_in_trans' trans.
  Proof.
    intros Hlk.
    rewrite /pages_in_trans'.
    induction trans using map_ind.
    {
      rewrite map_fold_empty //.
    }
    {
      destruct (decide (i = h)).
      subst i.
      rewrite insert_insert.
      rewrite lookup_insert_Some in Hlk.
      destruct Hlk as [[_ ->]|[? _]].
      2: done.
      rewrite map_fold_insert_L;auto.
      2:{
        intros w1 w2 trans1 trans2 y.
        intros Hneq Hlookup1 Hlookup2.
        destruct trans1, trans2;
        set_solver +.
      }
      rewrite map_fold_insert_L;auto.
      {
        intros w1 w2 trans1 trans2 y.
        intros Hneq Hlookup1 Hlookup2.
        destruct trans1, trans2;
        set_solver +.
      }
      rewrite map_insert_swap //.
      (* specialize (IHtrans Hlk). *)
      rewrite (map_fold_insert_L _ _ _ _ (<[h:=Some tran]> m));auto.
      2:{
        intros w1 w2 trans1 trans2 y.
        intros Hneq Hlookup1 Hlookup2.
        destruct trans1, trans2;
        set_solver +.
      }
      rewrite IHtrans //.
      rewrite (map_fold_insert_L _ _ i _ );auto.
      2:{
        intros w1 w2 trans1 trans2 y.
        intros Hneq Hlookup1 Hlookup2.
        destruct trans1, trans2;
        set_solver +.
      }
      destruct x.
      set_solver +.
      set_solver +.
      rewrite lookup_insert_ne // in Hlk.
      rewrite lookup_insert_ne //.
    }
    Qed.

  Lemma trans_ps_disj_subseteq' m m':
    inv_trans_ps_disj' m -> m' ⊆ m -> inv_trans_ps_disj' m'.
  Proof.
    intros Hdisj Hsub.
    intros k v Hlookup.
    rewrite map_subseteq_spec in Hsub.
    assert (delete k m' ⊆ delete k m).
    rewrite map_subseteq_spec.
    intros.
    destruct (decide (i = k)).
    {
      subst.
      rewrite lookup_delete_Some in H.
      destruct H;contradiction.
    }
    {
      rewrite lookup_delete_ne in H;auto.
      rewrite lookup_delete_ne;auto.
    }
    pose proof (pages_in_trans_subseteq' _ _ H).
    specialize (Hdisj k v).
    simpl in Hdisj.
    feed specialize Hdisj.
    apply Hsub;eauto.
    destruct v;auto.
    set_solver + Hdisj H0.
  Qed.

  Lemma pages_in_trans_lookup' {trans  h tran}:
    trans !! h = Some (Some tran)->
    tran.1.1.2 ⊆ pages_in_trans' trans.
  Proof.
    intros.
    induction trans using map_ind.
    done.
    rewrite /pages_in_trans'.
    rewrite map_fold_insert_L //.
    2:{
      intros w1 w2 trans1 trans2 y.
      intros Hneq Hlookup1 Hlookup2.
      destruct trans1, trans2;
        set_solver +.
    }
    destruct (decide (i = h)).
    subst.
    rewrite lookup_insert_Some in H.
    destruct H as [[_ ->]| [[] _]].
    set_solver +.
    done.
    rewrite lookup_insert_ne // in H.
    apply IHtrans in H.
    destruct x;set_solver + H.
  Qed.

  Lemma pages_in_trans_insert_Some_strong'{h tran tran' trans}:
    trans !! h = Some (Some tran) ->
    inv_trans_ps_disj' trans ->
    pages_in_trans' (<[h := Some tran']> trans) = pages_in_trans' trans ∖ tran.1.1.2 ∪ tran'.1.1.2.
  Proof.
    intros Hlk Hdisj.
    rewrite /pages_in_trans'.
    induction trans using map_ind.
    {
      rewrite map_fold_empty //.
    }
    {
      destruct (decide (i = h)).
      subst i.
      rewrite insert_insert.
      rewrite lookup_insert_Some in Hlk.
      destruct Hlk as [[_ ->]|[? _]].
      2: done.
      rewrite map_fold_insert_L;auto.
      2:{
        intros w1 w2 trans1 trans2 y.
        intros Hneq Hlookup1 Hlookup2.
        destruct trans1, trans2;
        set_solver +.
      }
      rewrite map_fold_insert_L;auto.
      2:{
        intros w1 w2 trans1 trans2 y.
        intros Hneq Hlookup1 Hlookup2.
        destruct trans1, trans2;
        set_solver +.
      }
      rewrite /inv_trans_ps_disj' in Hdisj.
      rewrite map_Forall_insert //in Hdisj.
      destruct Hdisj as [Hd Hdisj].
      rewrite delete_insert // in Hd.
      set_solver + Hd.
      rewrite lookup_insert_Some in Hlk.
      destruct Hlk as [[? _]|[_ Hlk]].
      contradiction.
      rewrite map_insert_swap //.
      rewrite /inv_trans_ps_disj' in Hdisj.
      rewrite map_Forall_insert //in Hdisj.
      destruct Hdisj as [Hd Hdisj].
      rewrite (map_fold_insert_L _ _ _ _ (<[h:=tran']> m));auto.
      2:{
        intros w1 w2 trans1 trans2 y.
        intros Hneq Hlookup1 Hlookup2.
        destruct trans1, trans2;
        set_solver +.
      }
      rewrite (map_fold_insert_L _ _ i _ );auto.
      2:{
        intros w1 w2 trans1 trans2 y.
        intros Hneq Hlookup1 Hlookup2.
        destruct trans1, trans2;
        set_solver +.
      }
      2: rewrite lookup_insert_ne //.
      assert (inv_trans_ps_disj' m) as Hdisj'.
      {
        clear Hlk n IHtrans Hd tran tran'.
        intros ???.
        specialize (Hdisj i0 x0 H0). simpl in Hdisj.
        destruct x0;auto.
        destruct (decide (i = i0)).
        {
          subst.
          rewrite delete_insert_delete // in Hdisj.
        }
        {
          rewrite delete_insert_ne // in Hdisj.
          rewrite /pages_in_trans' in Hdisj.
          rewrite map_fold_insert_L in Hdisj.
          2:{
            intros w1 w2 trans1 trans2 y.
            intros Hneq Hlookup1 Hlookup2.
            destruct trans1, trans2;
              set_solver +.
          }
          destruct x; set_solver + Hdisj.
          rewrite lookup_delete_ne //.
        }
      }
      destruct x.
      rewrite (difference_union_distr_l_L t.1.1.2).
      assert (t.1.1.2 ∖ tran.1.1.2 = t.1.1.2) as ->.
      {
        rewrite delete_insert // in Hd.
        pose proof(pages_in_trans_lookup' Hlk).
        set_solver + H0 Hd.
      }
      rewrite -union_assoc_L.
      f_equal.
      apply IHtrans;auto.
      apply IHtrans;auto.
    }
  Qed.

  Lemma pages_in_trans_insert_Some'{h tran tran' trans}:
    trans !! h = Some (Some tran) ->
    tran.1 = tran'.1 ->
    pages_in_trans' (<[h := Some tran']> trans) = pages_in_trans' trans.
  Proof.
    intros Hlk.
    rewrite /pages_in_trans'.
    induction trans using map_ind.
    {
      rewrite map_fold_empty //.
    }
    {
      intro Heq.
      destruct (decide (i = h)).
      subst i.
      rewrite insert_insert.
      rewrite lookup_insert_Some in Hlk.
      destruct Hlk as [[_ ->]|[? _]].
      2: done.
      rewrite map_fold_insert_L;auto.
      2:{
        intros w1 w2 trans1 trans2 y.
        intros Hneq Hlookup1 Hlookup2.
        destruct trans1, trans2;
        set_solver +.
      }
      rewrite map_fold_insert_L;auto.
      2:{
        intros w1 w2 trans1 trans2 y.
        intros Hneq Hlookup1 Hlookup2.
        destruct trans1, trans2;
        set_solver +.
      }
      rewrite Heq //.
      rewrite lookup_insert_Some in Hlk.
      destruct Hlk as [[? _]|[_ Hlk]].
      contradiction.
      rewrite map_insert_swap //.
      specialize (IHtrans Hlk Heq).
      rewrite (map_fold_insert_L _ _ _ _ (<[h:=tran']> m));auto.
      2:{
        intros w1 w2 trans1 trans2 y.
        intros Hneq Hlookup1 Hlookup2.
        destruct trans1, trans2;
        set_solver +.
      }
      rewrite (map_fold_insert_L _ _ i _ );auto.
      2:{
        intros w1 w2 trans1 trans2 y.
        intros Hneq Hlookup1 Hlookup2.
        destruct trans1, trans2;
        set_solver +.
      }
      2: rewrite lookup_insert_ne //.
      rewrite IHtrans //.
    }
Qed.

 Lemma pages_in_trans_None' {h trans}:
   trans !! h = None ->
  pages_in_trans' (<[h:=None]> trans) = pages_in_trans' trans.
   Proof.
     intro Hlk.
     rewrite /pages_in_trans'.
    induction trans using map_ind.
    {
      rewrite map_fold_insert_L.
      rewrite map_fold_empty //.
      {
        intros w1 w2 trans1 trans2 y.
        intros Hneq Hlookup1 Hlookup2.
        destruct trans1, trans2;
        set_solver +.
      }
      rewrite lookup_empty //.
    }
    {
      destruct (decide (i = h)).
      subst i.
      rewrite map_fold_insert_L;auto.
      {
        intros w1 w2 trans1 trans2 y.
        intros Hneq Hlookup1 Hlookup2.
        destruct trans1, trans2;
        set_solver +.
      }
      rewrite lookup_insert_ne // in Hlk.
      rewrite map_fold_insert_L;auto.
      {
        intros w1 w2 trans1 trans2 y.
        intros Hneq Hlookup1 Hlookup2.
        destruct trans1, trans2;
        set_solver +.
      }
      rewrite lookup_insert_ne //.
      }
   Qed.


  Lemma pages_in_trans_delete_None' {h trans}:
    trans !! h = Some (None) ->
    inv_trans_ps_disj' trans ->
    pages_in_trans' (delete h trans) = pages_in_trans' trans.
  Proof.
    intros Hlk.
    rewrite /pages_in_trans'.
    induction trans using map_ind.
    {
      rewrite map_fold_empty //.
    }
    {
      intro Hdisj.
      destruct (decide (i = h)).
      subst i.
      rewrite lookup_insert_Some in Hlk.
      destruct Hlk as [[_ ->]|[? _]].
      2: done.
      rewrite map_fold_insert_L;auto.
      2:{
        intros w1 w2 trans1 trans2 y.
        intros Hneq Hlookup1 Hlookup2.
        destruct trans1, trans2;
          set_solver +.
      }
      rewrite delete_insert //.
      {
        rewrite delete_insert_ne;auto.
        rewrite map_fold_insert_L.
        2:{
          intros w1 w2 trans1 trans2 y.
          intros Hneq Hlookup1 Hlookup2.
          destruct trans1, trans2;
            set_solver +.
        }
        2: {
          rewrite lookup_delete_ne;auto.
        }
        rewrite lookup_insert_ne // in Hlk.
        rewrite /inv_trans_ps_disj' in Hdisj.
        rewrite map_Forall_insert // in Hdisj.
        destruct Hdisj as [Hdisj Hforall].
        destruct x.
        {
          rewrite IHtrans;auto.
          rewrite map_fold_insert_L //.
          {
            intros w1 w2 trans1 trans2 y.
            intros Hneq Hlookup1 Hlookup2.
            destruct trans1, trans2;
              set_solver +.
          }
          rewrite /inv_trans_ps_disj'.
          intros h' tran' Hlk'.
          specialize (Hforall h' tran' Hlk').
          simpl in Hforall.
          destruct tran';last done.
          destruct (decide (h' = i)).
          {
            subst h'.
            rewrite Hlk' // in H.
          }
          rewrite delete_insert_ne // in Hforall.
          rewrite pages_in_trans_insert_None' in Hforall.
          set_solver + Hforall.
          rewrite lookup_delete_ne //.
        }
        rewrite map_fold_insert_L .
        {
          apply IHtrans.
          done.
          rewrite /inv_trans_ps_disj'.
          intros h' tran' Hlk'.
          specialize (Hforall h' tran' Hlk').
          simpl in Hforall.
          destruct tran';last done.
          destruct (decide (h' = i)).
          {
            subst h'.
            rewrite Hlk' // in H.
          }
          rewrite delete_insert_ne // in Hforall.
          rewrite pages_in_trans_None' // in Hforall.
          rewrite lookup_delete_ne //.
        }
        {
          intros w1 w2 trans1 trans2 y.
          intros Hneq Hlookup1 Hlookup2.
          destruct trans1, trans2;
            set_solver +.
        }
        done.
      }
    }
  Qed.

  Lemma pages_in_trans_delete' {h tran trans}:
    trans !! h = Some (Some tran) ->
    inv_trans_ps_disj' trans ->
    pages_in_trans' (delete h trans) = pages_in_trans' trans ∖ tran.1.1.2.
  Proof.
    intros Hlk Hdisj.
    specialize (Hdisj _ _ Hlk).
    rewrite /pages_in_trans'.
    induction trans using map_ind.
    {
      rewrite map_fold_empty //.
    }
    {
      rewrite map_fold_insert_L.
      2:{
        intros w1 w2 trans1 trans2 y.
        intros Hneq Hlookup1 Hlookup2.
        destruct trans1, trans2;
        set_solver +.
      }
      2: done.
      destruct (decide (i = h)).
      subst i.
      rewrite delete_insert. 2: done.
      {
        simpl in Hdisj.
        rewrite lookup_insert in Hlk.
        inversion Hlk.
        subst x.
        clear Hlk.
        rewrite delete_insert in Hdisj;auto.
        rewrite /pages_in_trans' in Hdisj.
        set_solver + Hdisj.
      }
      {
        rewrite delete_insert_ne;auto.
        rewrite map_fold_insert_L.
        2:{
          intros w1 w2 trans1 trans2 y.
          intros Hneq Hlookup1 Hlookup2.
          destruct trans1, trans2;
          set_solver +.
        }
        2: {
          rewrite lookup_delete_ne;auto.
        }
        rewrite lookup_insert_ne in Hlk.
        rewrite delete_insert_ne in Hdisj;auto.
        rewrite /pages_in_trans' in Hdisj.
        rewrite map_fold_insert_L in Hdisj.
        2:{
          intros w1 w2 trans1 trans2 y.
          intros Hneq Hlookup1 Hlookup2.
          destruct trans1, trans2;
          set_solver +.
        }
        2: {
          rewrite lookup_delete_ne;auto.
        }
        rewrite /pages_in_trans'.
        destruct x.
        rewrite IHtrans;auto.
        2: set_solver + Hdisj.
        set_solver + Hdisj.
        2: done.
        rewrite IHtrans;auto.
      }
    }
  Qed.

  Lemma trans_ps_disj_insert' h tran trans :
    inv_trans_ps_disj' trans ->
    trans !! h = None ->
    tran.1.1.2 ## pages_in_trans' trans ->
    inv_trans_ps_disj' (<[h:=Some tran]> trans).
  Proof.
    intros Hdisj Hlk Hdisj'.
    intros k v Hlk'.
    destruct (decide (k = h)).
    {
      subst.
      rewrite delete_insert;auto.
      rewrite lookup_insert in Hlk'.
      inversion Hlk'.
      subst v.
      done.
    }
    {
      rewrite delete_insert_ne;auto.
      destruct v as [v|];auto.
      rewrite lookup_insert_ne in Hlk';auto.
      rewrite (pages_in_trans_insert_None').
      rewrite (pages_in_trans_delete' Hlk' );auto.
      pose proof (subseteq_pages_in_trans' _ _ _ Hlk').
      set_solver + Hdisj' H.
      rewrite lookup_delete_ne;auto.
    }
  Qed.

  Lemma trans_ps_disj_update_None' h tran trans :
    inv_trans_ps_disj' trans ->
    trans !! h = Some None ->
    tran.1.1.2 ## pages_in_trans' trans ->
    inv_trans_ps_disj' (<[h:=Some tran]> trans).
  Proof.
    intros Hdisj Hlk Hdisj'.
    intros k v Hlk'.
    destruct (decide (k = h)).
    {
      subst.
      rewrite delete_insert_delete;auto.
      rewrite lookup_insert in Hlk'.
      inversion Hlk'.
      subst v.
      rewrite pages_in_trans_delete_None' //.
    }
    {
      rewrite delete_insert_ne;auto.
      rewrite lookup_insert_ne in Hlk';auto.
      destruct v as [v|];auto.
      rewrite pages_in_trans_update'.
      2: { rewrite lookup_delete_ne //. }
      pose proof (subseteq_pages_in_trans' k _ trans Hlk').
      erewrite pages_in_trans_delete';eauto.
      set_solver + H Hdisj'.
    }
Qed.

  Lemma trans_ps_disj_update'{trans h tran tran'}:
    inv_trans_ps_disj' trans ->
    trans !! h = Some (Some tran)->
    tran.1 = tran'.1 ->
    inv_trans_ps_disj' (<[h:= Some tran']> trans).
  Proof.
    intros Hdisj Hlk Heq.
    intros k v Hlk'.
    destruct (decide (k = h)).
    {
      subst.
      rewrite delete_insert_delete;auto.
      rewrite lookup_insert in Hlk'.
      inversion Hlk'.
      subst v.
      rewrite -Heq.
      specialize (Hdisj h (Some tran) Hlk).
      simpl in Hdisj.
      done.
    }
    {
      rewrite delete_insert_ne;auto.
      rewrite (pages_in_trans_insert_Some' (tran:=tran));auto.
      rewrite lookup_insert_ne in Hlk';auto.
      destruct v as [v|];auto.
      specialize (Hdisj k (Some v) Hlk').
      simpl in Hdisj.
      done.
      rewrite lookup_delete_ne //.
    }
  Qed.

  Lemma trans_ps_disj_delete'{trans h}:
    inv_trans_ps_disj' trans ->
    inv_trans_ps_disj' (<[h:= None]> trans).
  Proof.
    intros Hdisj.
    intros k v Hlk'.
    destruct (decide (k = h)).
    {
      subst.
      rewrite delete_insert_delete;auto.
      rewrite lookup_insert in Hlk'.
      inversion Hlk'.
      subst v.
      done.
    }
    {
      rewrite delete_insert_ne;auto.
      rewrite lookup_insert_ne in Hlk';auto.
      destruct v as [v|];auto.
      specialize (Hdisj k (Some v) Hlk').
      simpl in Hdisj.
      rewrite -insert_delete_insert.
      rewrite /pages_in_trans'.
      rewrite map_fold_insert_L.
      assert (delete h (delete k trans) ⊆ delete k trans).
      { apply map_subseteq_delete. }
      apply pages_in_trans_subseteq' in H.
      set_solver + H Hdisj.
      {
        intros.
        destruct z1,z2;set_solver.
      }
      rewrite lookup_delete_None.
      eauto.
    }
  Qed.

End helpers.

From iris.algebra.lib Require Import gmap_view.

Section ghost_map_extra.

  Context `{ghost_mapG Σ K V}.

  Lemma ghost_map_elem_split (k :K) γ q (v:V) :
    k ↪[γ]{#q} v ⊣⊢ k ↪[γ]{#q / 2} v ∗ k ↪[γ]{#q / 2} v.
  Proof.
    iSplit.
    iIntros "elem".
    rewrite ghost_map_elem_eq /ghost_map_elem_def.
    rewrite -own_op.
    rewrite -gmap_view_frag_op.
    rewrite dfrac_op_own.
    rewrite (Qp_div_2 q).
    done.
    iIntros "[elem1 elem2]".
    iDestruct (ghost_map_elem_combine with "elem1 elem2") as "[elem _]".
    rewrite dfrac_op_own.
    rewrite (Qp_div_2 q).
    done.
  Qed.

End ghost_map_extra.
