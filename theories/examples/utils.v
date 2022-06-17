From HypVeri Require Import machine_extra lifting.
From HypVeri.algebra Require Import base mailbox pagetable mem.
From HypVeri.lang Require Import reg_extra.

Section Utils.
  Context `{hypconsrs : !HypervisorConstants}.
  Context `{hypparams: !HypervisorParameters}. 
  
  Definition reg_layout (σ : state) (m : gmap reg_name Word) (i : VMID) :=
    map_Forall (λ (k : reg_name) (v : Word), (get_reg_files σ) !!! i !! k = Some v) m.  

  Lemma reg_layout_extend (σ : state) (m : gmap reg_name Word) (i : VMID)
        (H : reg_layout σ m i) (r : reg_name) (w : Word)
        (G : (σ.1.1.1.1.1 !!! i) !! r = Some w)
    : reg_layout σ (<[r:=w]> m) i.
  Proof.
    induction m using map_ind.
    - rewrite insert_empty.
      rewrite /reg_layout map_Forall_singleton.
      assumption.
    - apply map_Forall_insert_2; first assumption.
      apply map_Forall_insert_2.
      + by apply map_Forall_insert_1_1 in H.
      + by apply map_Forall_insert_1_2 in H.
  Qed.

  Definition mailbox_layout (σ: state) (m : gmap (VMID * MailBox) PID) :=
    map_Forall (λ (k : (VMID * MailBox)) (v : PID), match k.2 with
                                                    | TX => (get_mail_box σ @ k.1).1 = v
                                                    | RX => (get_mail_box σ @ k.1).2.1 = v
                                                    end) m.

  Definition rx_layout (σ : state) (m : gmap VMID (option (Word * VMID))) :=
    map_Forall (λ (k : VMID) (v : (option (Word * VMID))),
                (get_mail_box σ @ k).2.2 = v) m.  
  
  Definition excl_layout (σ : state) (m : gmap PID bool) :=
    map_Forall (λ (k : PID) (v : bool),
                (((λ (p: (_ * bool * gset VMID)), p.1.2 && bool_decide (size p.2 <= 1)) <$> (get_page_table σ !! k)) = Some v)) m.

  Definition own_layout (σ : state) (m : gmap PID (option VMID)) :=
    map_Forall (λ (k : PID) (v : option VMID),
                (((λ (p: (option VMID * _ * _)), p.1.1) <$> (get_page_table σ !! k)) = Some v)) m.

  Definition access_layout (σ : state) (m : gmap VMID (dfrac_agreeR (gsetO PID))) :=
    map_Forall (λ (k : VMID) (v : (dfrac_agreeR (gsetO PID))),
                to_frac_agree 1
                              (dom (gset PID)
                                   (map_filter (λ kv : PID * gset VMID, k ∈ kv.2)
                                               (λ x : PID * gset VMID, decide_rel elem_of k x.2)
                                               ((λ p : option VMID * bool * gset VMID, p.2) <$> σ.1.1.1.2))) = v
      ) m.

  Definition mem_page_program (p : PID) (wl: list Word) (Hle: length wl < (Z.to_nat page_size)) : gmap Addr Word :=
    list_to_map (zip (finz.seq p (length wl)) wl).

    Lemma pid_non_strict_upper_bound (p : PID) : (p ≤ 1999900)%Z.
  Proof.
    destruct p as [z align].
    simpl.
    destruct z as [z lt nn].
    simpl.
    assert ((z <=? 1999900)%Z = true).
    {
      clear -lt nn align.
      rewrite (Z.eqb_eq (z `rem` 1000) 0) in align.
      apply Z.rem_divide in align;[| lia].
      destruct align.
      subst z.
      apply Z.ltb_lt in lt.
      apply Z.leb_le in nn.
      lia.
    }
    lia.
  Qed.  

  Definition get_reg_gmap_vm (σ:state) (v:VMID) : gmap (reg_name * VMID) Word :=
    (list_to_map (map (λ p, ((p.1,v),p.2)) (map_to_list ((get_reg_files σ !!! v))))).

  Lemma get_reg_gmap_vm_lookup_eq σ i i' r:
    is_Some ((get_reg_gmap_vm σ i) !! (r,i')) -> i = i'.
  Proof.
    intros [? Hlookup].
    rewrite /get_reg_gmap_vm in Hlookup.
    apply elem_of_list_to_map_2 in Hlookup.
    apply elem_of_list_In in Hlookup.
    apply in_map_iff in Hlookup.
    destruct Hlookup as [p].
    destruct H as [Heqn].
    inversion Heqn ;subst;clear Heqn.
    done.
  Qed.

  Lemma get_reg_gmap_vm_lookup_Some σ (i:VMID) r w :
    (get_reg_gmap_vm σ i) !! (r,i) = Some w <-> get_reg_file σ @ i !! r = Some w.
  Proof.
    split.
    - unfold get_reg_gmap_vm.
      intro HSome.
      apply elem_of_list_to_map_2 in HSome.
      apply elem_of_list_In in HSome.
      apply in_map_iff in HSome.
      destruct HSome as [p].
      destruct H as [Heqn].
      inversion Heqn ;subst;clear Heqn.
      apply elem_of_list_In in H.
      by apply elem_of_map_to_list' in H.
    - intro HSome.
      apply  elem_of_list_to_map_1'.
      + intros.
        apply elem_of_list_In in H.
        apply in_map_iff in H.
        destruct H as [p].
        destruct H as [Heqn H].
        apply elem_of_list_In in H.
        apply elem_of_map_to_list' in H.
        inversion Heqn;subst;clear Heqn.
        rewrite H in HSome.
        by inversion HSome.
      + apply elem_of_list_In.
        apply in_map_iff.
        exists (r,w).
        split;[done|].
        apply elem_of_list_In.
        apply elem_of_map_to_list'.
        done.
  Qed.

  Lemma reg_layout_get_reg_gmap (σ : state) (m : gmap reg_name Word) (i : VMID)
        (H : reg_layout σ m i) (G : ∀ i rn, is_Some (((get_reg_files σ) !!! i) !! rn))
    : (kmap (λ k, (pair k i)) m) ⊆ get_reg_gmap_vm σ i.
  Proof.
    induction m as [| i' a' m' J IH] using map_ind.
    - rewrite kmap_empty.
      apply map_empty_subseteq.
    - rewrite kmap_insert.
      apply insert_subseteq_l.
      + rewrite get_reg_gmap_vm_lookup_Some.
        destruct (G i i') as [w P].        
        rewrite P.
        rewrite /reg_layout map_Forall_lookup in H.
        specialize (H i' a' (lookup_insert _ _ _)).
        rewrite <-H, <-P.
        reflexivity.
      + apply IH.
        apply map_Forall_insert_1_2 in H.
        * apply H.
        * assumption.
  Qed.
  
  Lemma flat_map_NoDup {A B : Type} (l : list A) (f : A -> list B)
    : NoDup l -> (∀ x y, x ∈ l -> y ∈ l -> x ≠ y -> (∀ x', x' ∈ f x -> x' ∉ f y)) -> (∀ x, NoDup (f x)) -> NoDup (flat_map f l).
  Proof.
    intros Hnd Hinj Hf.
    induction l as [| x xs IH].
    - apply NoDup_nil_2.
    - apply NoDup_app.
      split.
      + apply Hf.
      + split.
        * intros x' x'in contra.
          assert ((fix flat_map (l : list A) : list B :=
                     match l with
                     | [] => []
                     | x :: t => f x ++ flat_map t
                     end) = flat_map f) as Hrew.
          { reflexivity. }
          rewrite Hrew in contra.
          clear Hrew.
          rewrite elem_of_list_In in contra.
          rewrite in_flat_map in contra.
          destruct contra as [x'' [contra1 contra2]].
          specialize (Hinj x'' x).
          feed specialize Hinj.
          -- rewrite elem_of_list_In.
             by apply in_cons.
          -- rewrite elem_of_list_In.
             by apply in_eq.
          -- apply NoDup_cons_1_1 in Hnd.
             intros contra3.
             rewrite <-contra3 in Hnd.
             apply Hnd.
             by rewrite elem_of_list_In.
          -- specialize (Hinj x').
             feed specialize Hinj.
             ++ by rewrite elem_of_list_In.
             ++ done.
             ++ contradiction.
        * apply IH.
          -- by apply NoDup_cons_1_2 in Hnd.
          -- intros x' y' x'in y'in x'y'neq x'' x''in contra.
             specialize (Hinj x' y').
             feed specialize Hinj;
               [by apply elem_of_list_further | by apply elem_of_list_further | assumption |].
             by apply (Hinj x'' x''in).
  Qed.
  
  Lemma mailbox_layout_get_mb_gmap (σ : state) (m : gmap (VMID * MailBox) PID)
        (H : mailbox_layout σ m)
    : m ⊆ get_mb_gmap σ.
  Proof.
    induction m as [| i' a' m' J IH] using map_ind.
    - apply map_empty_subseteq.
    - apply insert_subseteq_l.
      + apply map_Forall_insert_1_1 in H.
        unfold get_mb_gmap.
        destruct i' as [i1 i2].
        destruct i2.
        * simpl in H.
          rewrite <-H.
          clear.
          apply elem_of_list_to_map_1.
          -- apply NoDup_fmap_fst.
             ++ intros x y1 y2 H1 H2.
                rewrite elem_of_list_In in_flat_map in H1.
                rewrite elem_of_list_In in_flat_map in H2.
                destruct H1 as [x1 [H11 H12]].
                destruct H2 as [x2 [H21 H22]].
                destruct x as [x1' x2'].
                destruct x2'.
                ** apply in_inv in H12.
                   destruct H12 as [Htemp | [H12 | ?]];
                     first (inversion Htemp);
                     last contradiction.
                   apply in_inv in H22.
                   destruct H22 as [Htemp | [H22 | ?]];
                     first (inversion Htemp);
                     last contradiction.
                   inversion H12; subst.
                   inversion H22; subst.
                   reflexivity.
                ** apply in_inv in H12.
                   destruct H12 as [H12 | [Htemp | ?]]; [| inversion Htemp | contradiction].
                   destruct H22 as [H22 | [Htemp | ?]]; [| inversion Htemp | contradiction].
                   inversion H12; subst.
                   inversion H22; subst.
                   reflexivity.
             ++ apply flat_map_NoDup;
                  first apply NoDup_list_of_vmids.
                ** intros x y xin yin xyneq x' x'in contra.
                   rewrite elem_of_cons elem_of_list_singleton in x'in.
                   rewrite elem_of_cons elem_of_list_singleton in contra.
                   destruct x'in, contra; simplify_eq.
                ** intros x.
                   apply NoDup_cons_2; last apply NoDup_singleton.
                   intros contra.
                   rewrite elem_of_list_singleton in contra.
                   inversion contra.
          -- rewrite elem_of_list_In.
             rewrite in_flat_map.
             exists i1.
             split; first apply in_list_of_vmids.
             apply in_cons.
             apply in_eq.
        * simpl in H.
          rewrite <-H.
          clear.
          apply elem_of_list_to_map_1.
          -- apply NoDup_fmap_fst.
             ++ intros x y1 y2 H1 H2.
                rewrite elem_of_list_In in_flat_map in H1.
                rewrite elem_of_list_In in_flat_map in H2.
                destruct H1 as [x1 [H11 H12]].
                destruct H2 as [x2 [H21 H22]].
                destruct x as [x1' x2'].
                destruct x2'.
                ** apply in_inv in H12.
                   destruct H12 as [Htemp | [H12 | ?]];
                     first (inversion Htemp);
                     last contradiction.
                   apply in_inv in H22.
                   destruct H22 as [Htemp | [H22 | ?]];
                     first (inversion Htemp);
                     last contradiction.
                   inversion H12; subst.
                   inversion H22; subst.
                   reflexivity.
                ** apply in_inv in H12.
                   destruct H12 as [H12 | [Htemp | ?]]; [| inversion Htemp | contradiction].
                   destruct H22 as [H22 | [Htemp | ?]]; [| inversion Htemp | contradiction].
                   inversion H12; subst.
                   inversion H22; subst.
                   reflexivity.
             ++ apply flat_map_NoDup;
                  first apply NoDup_list_of_vmids.
                ** intros x y xin yin xyneq x' x'in contra.
                   rewrite elem_of_cons elem_of_list_singleton in x'in.
                   rewrite elem_of_cons elem_of_list_singleton in contra.
                   destruct x'in, contra; simplify_eq.
                ** intros x.
                   apply NoDup_cons_2; last apply NoDup_singleton.
                   intros contra.
                   rewrite elem_of_list_singleton in contra.
                   inversion contra.
          -- rewrite elem_of_list_In.
             rewrite in_flat_map.
             exists i1.
             split; first apply in_list_of_vmids.
             apply in_eq.
      + apply IH.
        apply map_Forall_insert_1_2 in H.
        * apply H.
        * assumption.
  Qed.

  Lemma rx_layout_get_rx_gmap (σ : state) (m : gmap VMID (option (Word * VMID)))
        (H : rx_layout σ m)
    : m ⊆ get_rx_gmap σ.
  Proof.
    induction m as [| i' a' m' J IH] using map_ind.
    - apply map_empty_subseteq.
    - apply insert_subseteq_l.
      + apply map_Forall_insert_1_1 in H.
        unfold get_rx_gmap.
        apply elem_of_list_to_map_1.
        * apply NoDup_fmap_fst.
          -- intros x y1 y2 H1 H2.
             rewrite elem_of_list_In in_map_iff in H1.
             rewrite elem_of_list_In in_map_iff in H2.
             destruct H1 as [x1 [H11 H12]].
             destruct H2 as [x2 [H21 H22]].
             repeat case_match; by simplify_eq.
          -- apply NoDup_fmap_2; last apply NoDup_list_of_vmids.
             intros x y H'.
             destruct (σ.1.1.1.1.2 !!! x).2.2, (σ.1.1.1.1.2 !!! y).2.2;
               repeat case_match;
               by simplify_eq.
        * rewrite elem_of_list_In in_map_iff.
          exists i'.
          rewrite H.
          split; last apply in_list_of_vmids.
          destruct a' as [[a1 a2] |]; done.
      + apply IH.
        apply map_Forall_insert_1_2 in H.
        * apply H.
        * assumption.
  Qed.
  
  Lemma excl_layout_get_excl_gmap (σ : state) (m : gmap PID bool)
        (H : excl_layout σ m)
    : m ⊆ get_excl_gmap σ.
  Proof.
    induction m as [| i' a' m' J IH] using map_ind.
    - apply map_empty_subseteq.
    - apply insert_subseteq_l.
      + apply map_Forall_insert_1_1 in H.
        unfold get_excl_gmap.
        rewrite (lookup_fmap _ σ.1.1.1.2 i') //.
      + apply IH.
        apply map_Forall_insert_1_2 in H.
        * apply H.
        * assumption.
  Qed.

  Lemma own_layout_get_own_gmap (σ : state) (m : gmap PID (option VMID))
        (H : own_layout σ m)
    : m ⊆ get_own_gmap σ.
  Proof.
    induction m as [| i' a' m' J IH] using map_ind.
    - apply map_empty_subseteq.
    - apply insert_subseteq_l.
      + apply map_Forall_insert_1_1 in H.
        unfold get_own_gmap.
        rewrite (lookup_fmap _ σ.1.1.1.2 i') //.
      + apply IH.
        apply map_Forall_insert_1_2 in H.
        * apply H.
        * assumption.
  Qed.

  Lemma access_layout_get_access_gmap (σ : state) (m : gmap VMID (dfrac_agreeR (gsetO PID)))
        (H : access_layout σ m)
    : m ⊆ get_access_gmap σ.
  Proof.
    induction m as [| i' a' m' J IH] using map_ind.
    - apply map_empty_subseteq.
    - apply insert_subseteq_l.
      + apply map_Forall_insert_1_1 in H.
        unfold get_access_gmap.
        apply elem_of_list_to_map_1.
        * apply NoDup_fmap_fst.
          -- intros x y1 y2 H1 H2.
             rewrite elem_of_list_In in_map_iff in H1.
             rewrite elem_of_list_In in_map_iff in H2.
             destruct H1 as [x1 [H11 H12]].
             destruct H2 as [x2 [H21 H22]].
             repeat case_match; by simplify_eq.
          -- apply NoDup_fmap_2; last apply NoDup_list_of_vmids.
             intros x y H'.
             destruct (σ.1.1.1.1.2 !!! x).2.2, (σ.1.1.1.1.2 !!! y).2.2;
               repeat case_match;
               by simplify_eq.
        * rewrite elem_of_list_In in_map_iff.
          exists i'.
          split; last apply in_list_of_vmids.
          f_equal.
          rewrite <-H.
          done.
      + apply IH.
        apply map_Forall_insert_1_2 in H.
        * apply H.
        * assumption.
  Qed.  
  
  Definition NoDup' {A} (l : list A) := ∀ i j, i < length l -> j < length l -> i ≠ j -> (l !! i ≠ l !! j).

  Lemma lt_unique: forall m n (lt_mn1 lt_mn2 : m < n), lt_mn1 = lt_mn2.
  Proof.
    intros m n lt1 lt2.
    apply proof_irrel.
  Qed.

  Lemma lookup_list_now : ∀{A} (l : list A) (x : A) i, i = 0 -> (x :: l) !! i = Some x.
  Proof.
    intros.
    simplify_eq.
    done.
  Qed.
  
  Lemma lookup_list_later : ∀{A} (l : list A) i, drop 1 l !! i = l !! S i.
  Proof.
    intros.
    induction l.
    - simpl.
      done.
    - simpl.
      rewrite drop_0.
      reflexivity.
  Qed.
  
  Lemma minus_one_cong : ∀ x y, x = y + 1 -> x - 1 = y.
  Proof.
    intros ? ? ->.
    lia.
  Qed.
  
  Lemma NoDup_rev {A} (l : list A) (H : NoDup' l) : NoDup' (reverse l).
  Proof.
    induction l.
    - assumption.
    - simpl.
      intros x y xlt ylt xyne contra.
      rewrite reverse_length in xlt.
      rewrite reverse_length in ylt.
      rewrite !reverse_lookup in contra; simpl in *; [| assumption | assumption].
      assert (length l - x ≠ length l - y).
      lia.
      apply (H (length l - x) (length l - y)); simpl; [lia | lia | assumption | assumption].
  Qed.  
  
End Utils.

Ltac solve_NoDup_pre :=
  match goal with
  | G : NoDup' ?l |- _ => rewrite ?disjoint_singleton_r;
                        rewrite ?disjoint_singleton_l;
                        intros contra;
                        clear -contra G;
                        rewrite ?elem_of_union in contra;
                        rewrite !elem_of_singleton in contra
  end.

Ltac solve_NoDup_pre' :=    
  match goal with
  | G : NoDup' ?l, contra : _ |- False =>      
      repeat (destruct contra as [contra | eq]); simplify_eq
  end.

Ltac solve_NoDup_pre'' i j :=    
  match goal with
  | G : NoDup' ?l |- False =>
      (eapply (G i j); simpl; [lia | lia | lia | reflexivity]; fail)
      + solve_NoDup_pre'' i (S j)
  end.

Ltac solve_NoDup i :=
  try solve_NoDup_pre;
  try solve_NoDup_pre';
  solve_NoDup_pre'' i 0.

Ltac program_in_seq :=
  match goal with
  | |- seq_in_page (of_pid ?prog_p) _ ?prog_p =>
      simpl;
      unfold seq_in_page; split; first solve_finz; split; first (unfold Is_true; case_match ; [done | solve_finz]);
      split;
      first (pose proof (last_addr_in_bound prog_p);
             solve_finz);
      unfold Is_true; case_match;[done | solve_finz]
  end.
