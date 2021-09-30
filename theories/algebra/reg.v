From HypVeri.algebra Require Import base.

Section reg_rules.

  Context `{vmG :gen_VMG Σ}.

  Implicit Type σ : state.
  Implicit Type i : VMID.
  Implicit Type w : Word.

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


  Lemma gen_reg_valid_global1 {σ} r i w:
    ghost_map_auth (gen_reg_name vmG) 1 (get_reg_gmap σ) -∗
    r @@ i ->r w -∗
    ⌜(get_reg_global σ i r) = Some w⌝.
  Proof.
    iIntros "Hσ Hr".
    rewrite reg_mapsto_eq /reg_mapsto_def.
    iDestruct (ghost_map_lookup with "Hσ Hr") as "%Hlk".
    iPureIntro.
    rewrite /get_reg /get_reg_global.
    rewrite /get_reg_gmap in Hlk.
    apply elem_of_list_to_map_2 in Hlk.
    apply elem_of_list_In in Hlk.
    apply in_flat_map in Hlk.
    inversion Hlk as [? Hin]; clear Hlk.
    destruct Hin as [Hinv Hin].
    apply in_map_iff in Hin.
    destruct Hin as [? [Heqp Hin]].
    inversion Heqp;clear Heqp;subst.
    apply elem_of_list_In in Hin.
    apply elem_of_map_to_list' in Hin.
    done.
   Qed.

  Lemma gen_reg_valid1 {σ} r i w:
    (get_current_vm σ) = i ->
    ghost_map_auth (gen_reg_name vmG) 1 (get_reg_gmap σ) -∗
    r @@ i ->r w -∗
    ⌜(get_reg σ r) = Some w⌝.
  Proof.
    iIntros (Hcur) "Hσ Hr".
    rewrite /get_reg -Hcur.
    iApply (gen_reg_valid_global1 with "Hσ Hr").
  Qed.

  Lemma gen_reg_valid_Sep {σ} i (regs: gmap (reg_name * VMID) Word):
   (get_current_vm σ) = i ->
   ghost_map_auth (gen_reg_name vmG) 1 (get_reg_gmap σ) -∗
   ([∗ map] r↦w ∈ regs, r.1 @@ r.2 ->r w)-∗
   ([∗ map] r↦w ∈ regs, ⌜r.2 = i -> (get_reg σ r.1) = Some w⌝).
  Proof.
    iIntros (Hcur) "Hσ Hregs".
    rewrite reg_mapsto_eq /reg_mapsto_def.
    iDestruct ((ghost_map_lookup_big regs) with "Hσ [Hregs]") as "%Hincl".
    iApply (big_sepM_proper (λ k x, (k.1, k.2)↪[gen_reg_name vmG] x)%I);auto.
    intros k x Hlk.
    cbn.
    f_equiv.
    by destruct k.
    iApply big_sepM_pure.
    iIntros (?? Hlk Heqi).
    rewrite /get_reg /get_reg_global.
    apply (lookup_weaken _ (get_reg_gmap σ)) in Hlk;eauto.
    apply elem_of_list_to_map_2 in Hlk.
    apply elem_of_list_In in Hlk.
    apply in_flat_map in Hlk.
    destruct Hlk as [? [_ Hinp]].
    apply in_map_iff in Hinp.
    destruct Hinp as [? [Heqp Hinx]].
    inversion Heqp;subst.
    apply elem_of_list_In in Hinx.
    apply elem_of_map_to_list' in Hinx.
    by simplify_eq /=.
  Qed.

  Lemma gen_reg_valid2 {σ} i r1 w1 r2 w2:
    (get_current_vm σ) = i ->
    ghost_map_auth (gen_reg_name vmG) 1 (get_reg_gmap σ) -∗
    r1 @@ i ->r w1 -∗
    r2 @@ i ->r w2 -∗
    ⌜(get_reg σ r1) = Some w1⌝ ∗ ⌜(get_reg σ r2) = Some w2⌝.
  Proof.
    iIntros (Hcur) "Hreg Hr1 Hr2".
    iDestruct (reg_neq with "Hr1 Hr2") as %[Hneq|];[|contradiction].
    iDestruct ((gen_reg_valid_Sep i (<[(r1,i):=w1]>{[(r2,i):=w2]}))
                 with "Hreg [Hr1 Hr2]") as "%Hreg";eauto.
    rewrite !big_sepM_insert ?big_sepM_empty;eauto.
    iFrame.
    apply lookup_insert_None; split;eauto; intros P; by inversion P.
    iPureIntro.
    split.
    - by apply (Hreg (r1, i) w1 (lookup_insert _ (r1, i) w1)).
    - apply (Hreg (r2, i) w2);eauto.
      rewrite lookup_insert_Some;right;split;
      [intros P; inversion P; contradiction|];
      rewrite !lookup_insert //.
  Qed.

  Lemma gen_reg_valid3 {σ} i r1 w1 r2 w2 r3 w3:
   (get_current_vm σ) = i ->
   ghost_map_auth (gen_reg_name vmG) 1 (get_reg_gmap σ) -∗
   r1 @@ i ->r w1 -∗
   r2 @@ i ->r w2 -∗
   r3 @@ i ->r w3 -∗
   ⌜(get_reg σ r1) = Some w1⌝ ∗ ⌜(get_reg σ r2) =Some w2⌝ ∗ ⌜(get_reg σ r3) = Some w3⌝.
  Proof.
    iIntros (Hcur ) "Hreg Hr1 Hr2 Hr3".
    iDestruct (reg_neq with "Hr1 Hr2") as %[Hneq1|];[|contradiction].
    iDestruct (reg_neq with "Hr2 Hr3") as %[Hneq2|];[|contradiction].
    iDestruct (reg_neq with "Hr1 Hr3") as %[Hneq3|];[|contradiction].
    iDestruct ((gen_reg_valid_Sep i ({[(r1,i):=w1;(r2,i):=w2;(r3,i):=w3]}))
                 with "Hreg [Hr1 Hr2 Hr3]") as "%Hreg";eauto.
    rewrite !big_sepM_insert ?big_sepM_empty;eauto.
    iFrame.
    apply lookup_insert_None; split;eauto; intros P; by inversion P.
    apply lookup_insert_None; split;eauto.
    apply lookup_insert_None; split;eauto; intros P; by inversion P.
    intros P; by inversion P.
    iPureIntro.
    split;[|split].
    - by apply (Hreg (r1, i) w1 (lookup_insert _ (r1, i) w1)).
    - apply (Hreg (r2, i) w2);eauto.
      rewrite lookup_insert_Some;right;split;
      [intros P; inversion P; contradiction|];
        by rewrite !lookup_insert.
    - apply (Hreg (r3, i) w3);eauto.
      rewrite !lookup_insert_Some.
      repeat (right;split;
      [intros P; inversion P; contradiction|]).
      left;done.
  Qed.

  Lemma gen_reg_valid4 {σ} i r1 w1 r2 w2 r3 w3 r4 w4:
   (get_current_vm σ) = i ->
   ghost_map_auth (gen_reg_name vmG) 1 (get_reg_gmap σ) -∗
   r1 @@ i ->r w1 -∗
   r2 @@ i ->r w2 -∗
   r3 @@ i ->r w3 -∗
   r4 @@ i ->r w4 -∗
   ⌜(get_reg σ r1) = Some w1⌝ ∗ ⌜(get_reg σ r2) =Some w2⌝ ∗
   ⌜(get_reg σ r3) = Some w3⌝ ∗ ⌜(get_reg σ r4) = Some w4⌝.
  Proof.
    iIntros (Hi) "Hreg Hr1 Hr2 Hr3 Hr4".
    iDestruct (reg_neq with "Hr1 Hr2") as %[Hneq1|];[|contradiction].
    iDestruct (reg_neq with "Hr2 Hr3") as %[Hneq2|];[|contradiction].
    iDestruct (reg_neq with "Hr1 Hr3") as %[Hneq3|];[|contradiction].
    iDestruct (reg_neq with "Hr1 Hr4") as %[Hneq4|];[|contradiction].
    iDestruct (reg_neq with "Hr2 Hr4") as %[Hneq5|];[|contradiction].
    iDestruct (reg_neq with "Hr3 Hr4") as %[Hneq6|];[|contradiction].
    iDestruct ((gen_reg_valid_Sep i ({[(r1,i):=w1;(r2,i):=w2;(r3,i):=w3;(r4,i):=w4]}))
                 with "Hreg [Hr1 Hr2 Hr3 Hr4]") as "%Hreg";eauto.
    rewrite !big_sepM_insert ?big_sepM_empty;first iFrame;
    rewrite ?lookup_insert_None;repeat split;eauto;
    intros P; by inversion P.
    iPureIntro.
    split;[|split;[|split]].
    - by apply (Hreg (r1, i) w1 (lookup_insert _ (r1, i) w1)).
    - apply (Hreg (r2, i) w2);eauto.
      rewrite lookup_insert_Some;right;split;
      [intros P; inversion P; contradiction|];
        by rewrite !lookup_insert.
    - apply (Hreg (r3, i) w3);eauto.
      rewrite !lookup_insert_Some.
      repeat (right;split;
      [intros P; inversion P; contradiction|]).
      left;done.
    - apply (Hreg (r4, i) w4);eauto.
      rewrite !lookup_insert_Some.
      repeat (right;split;
      [intros P; inversion P; contradiction|]).
      left;done.
  Qed.

  Lemma gen_reg_update1_global {σ} r i w w':
    ghost_map_auth (gen_reg_name vmG) 1 (get_reg_gmap σ) -∗
    r @@ i ->r w ==∗
    ghost_map_auth (gen_reg_name vmG) 1 (<[(r,i):=w']>(get_reg_gmap σ)) ∗
    r @@ i ->r w'.
  Proof.
    iIntros "Hσ Hr".
    rewrite reg_mapsto_eq /reg_mapsto_def.
    iDestruct (ghost_map_update w' with "Hσ Hr") as ">[Hσ Hr]".
      by iFrame.
  Qed.

  Lemma reg_proper {m: gmap (reg_name * VMID) Word}:
   ([∗ map] k ↦ x ∈ m, k↪[gen_reg_name vmG] x) ⊣⊢ ([∗ map]k ↦ x ∈ m,  (k.1, k.2)↪[gen_reg_name vmG] x).
  Proof.
    iApply (big_sepM_proper _ (λ k x, (k.1, k.2)↪[gen_reg_name vmG] x)%I).
    intros.
    cbn.
    f_equiv.
    destruct k;done.
  Qed.

  Lemma gen_reg_update_Sep {σ} regs regs':
   dom (gset (reg_name * VMID)) regs = dom (gset (reg_name * VMID )) regs' ->
   ghost_map_auth (gen_reg_name vmG) 1 (get_reg_gmap σ) -∗
   ([∗ map] r↦w ∈ regs,  r.1 @@ r.2 ->r w) ==∗
   ghost_map_auth (gen_reg_name vmG) 1 (regs' ∪ (get_reg_gmap σ)) ∗
   ([∗ map] r↦w ∈ regs',  r.1 @@ r.2 ->r w).
  Proof.
    iIntros (Hdom) "Hσ Hr".
    rewrite reg_mapsto_eq /reg_mapsto_def.
    iDestruct (ghost_map_update_big regs regs' Hdom with "[Hσ] [Hr]") as ">[Hσ Hr]";eauto.
    by iApply reg_proper.
    rewrite reg_proper.
    by iFrame.
  Qed.

  Lemma gen_reg_update2_global {σ} r1 i1 w1 w1' r2 i2 w2 w2':
   ghost_map_auth (gen_reg_name vmG) 1 (get_reg_gmap σ) -∗
   r1 @@ i1 ->r w1 -∗
   r2 @@ i2 ->r w2==∗
   ghost_map_auth (gen_reg_name vmG) 1 (<[(r1,i1) := w1']> (<[(r2,i2) := w2']> (get_reg_gmap σ))) ∗
   r1 @@ i1 ->r w1' ∗ r2 @@ i2 ->r w2'.
  Proof.
    iIntros "Hreg Hr1 Hr2".
    iDestruct (reg_neq with "Hr1 Hr2") as %Hneq.
    iDestruct ((gen_reg_update_Sep {[(r1,i1):=w1; (r2,i2):=w2]}
                                   {[(r1,i1):=w1'; (r2,i2):=w2']}) with "Hreg [Hr1 Hr2]")
      as ">[Hreg Hr12]" ;eauto;[set_solver| | ].
    rewrite !big_sepM_insert ?big_sepM_empty;eauto.
    iFrame.
    destruct Hneq; apply lookup_insert_None; split;eauto; intros P; by inversion P.
    iModIntro.
    rewrite !big_sepM_insert ?big_sepM_empty;eauto.
    iDestruct "Hr12" as "(? & ? & _)".
    rewrite ?insert_union_singleton_l map_union_assoc.
    simplify_map_eq.
    by iFrame.
    destruct Hneq; apply lookup_insert_None; split;eauto; intros P; by inversion P.
  Qed.

  Lemma gen_reg_update3_global {σ w1 w2 w3} r1 i1 w1' r2 i2 w2' r3 i3 w3':
   ghost_map_auth (gen_reg_name vmG) 1 (get_reg_gmap σ) -∗
   r1 @@ i1 ->r w1 -∗
   r2 @@ i2 ->r w2 -∗
   r3 @@ i3 ->r w3==∗
   ghost_map_auth (gen_reg_name vmG) 1 (<[(r1,i1) := w1']> (<[(r2,i2) := w2']>
                                                            (<[(r3,i3):= w3']>(get_reg_gmap σ)))) ∗
   r1 @@ i1 ->r w1'  ∗ r2 @@ i2 ->r w2' ∗ r3 @@ i3 ->r w3'.
  Proof.
    iIntros "Hreg Hr1 Hr2 Hr3".
    iDestruct (reg_neq with "Hr1 Hr2") as %Hneq12.
    iDestruct (reg_neq with "Hr3 Hr2") as %Hneq32.
    iDestruct (reg_neq with "Hr1 Hr3") as %Hneq13.
    assert (Hlk: ∀ w3 ,  ({[(r3, i3) := w3]}: gmap _ _) !! (r2, i2) = None).
    intro. destruct Hneq32; rewrite !lookup_insert_None; split;eauto; intros P; by inversion P.
    assert (Hlk': ∀ w2 w3, ({[(r2, i2) := w2; (r3, i3) := w3]} : gmap _ _ ) !! (r1, i1) = None).
    intros. destruct Hneq12; rewrite !lookup_insert_None; repeat split;eauto;
    destruct Hneq13; intros P; by inversion P.
    iDestruct ((gen_reg_update_Sep  {[(r1,i1):=w1; (r2,i2):=w2 ;(r3,i3):=w3]}
                                   {[(r1,i1):=w1'; (r2,i2):=w2'; (r3,i3):=w3']}) with "Hreg [Hr1 Hr2 Hr3]")
      as ">[Hreg Hr123]" ;eauto;[set_solver| | ].
    rewrite !big_sepM_insert ?big_sepM_empty;eauto.
    iFrame.
    rewrite !big_sepM_insert ?big_sepM_empty;eauto.
    iDestruct "Hr123" as "(? & ? & ? & _)".
    rewrite ?insert_union_singleton_l !map_union_assoc.
    simplify_map_eq.
    by iFrame.
  Qed.

  Lemma gen_reg_update4_global {σ w1 w2 w3 w4} r1 i1 w1' r2 i2 w2' r3 i3 w3' r4 i4 w4':
   ghost_map_auth (gen_reg_name vmG) 1 (get_reg_gmap σ) -∗
   r1 @@ i1 ->r w1 -∗
   r2 @@ i2 ->r w2 -∗
   r3 @@ i3 ->r w3 -∗
   r4 @@ i4 ->r w4==∗
   ghost_map_auth (gen_reg_name vmG) 1 (<[(r1,i1) := w1']> (<[(r2,i2) := w2']>
                                                            (<[(r3,i3):= w3']> (<[(r4,i4):= w4']> (get_reg_gmap σ))))) ∗
   r1 @@ i1 ->r w1'  ∗ r2 @@ i2 ->r w2' ∗ r3 @@ i3 ->r w3' ∗ r4 @@ i4 ->r w4'.
  Proof.
    iIntros "Hreg Hr1 Hr2 Hr3 Hr4".
    iDestruct (reg_neq with "Hr1 Hr2") as %Hneq12.
    iDestruct (reg_neq with "Hr3 Hr2") as %Hneq32.
    iDestruct (reg_neq with "Hr1 Hr3") as %Hneq13.
    iDestruct (reg_neq with "Hr3 Hr4") as %Hneq34.
    iDestruct (reg_neq with "Hr2 Hr4") as %Hneq24.
    iDestruct (reg_neq with "Hr1 Hr4") as %Hneq14.
    assert (Hlk1 : ∀ w4, ({[(r4, i4) := w4]}: gmap _ _) !! (r3, i3) = None).
    intro. destruct Hneq34; rewrite !lookup_insert_None; split;eauto; intros P; by inversion P.
    assert (Hlk2 : ∀ w3 w4, ({[(r3, i3) := w3; (r4, i4) := w4]}: gmap _ _) !! (r2, i2) = None).
    intros. destruct Hneq32, Hneq24; rewrite !lookup_insert_None; split;eauto; set_solver.
    assert (Hlk3 : ∀ w2 w3 w4, ({[(r2, i2) := w2; (r3, i3) := w3; (r4, i4) := w4]}: gmap _ _) !! (r1, i1) = None).
    intros. destruct Hneq12, Hneq13, Hneq14; rewrite !lookup_insert_None; split;eauto; set_solver.
    assert (Hlk: ∀ w3 ,  ({[(r3, i3) := w3]}: gmap _ _) !! (r2, i2) = None).
    intro. destruct Hneq32; rewrite !lookup_insert_None; split;eauto; intros P; by inversion P.
    assert (Hlk': ∀ w2 w3, ({[(r2, i2) := w2; (r3, i3) := w3]} : gmap _ _ ) !! (r1, i1) = None).
    intros. destruct Hneq12; rewrite !lookup_insert_None; repeat split;eauto;
    destruct Hneq13; intros P; by inversion P.
    iDestruct ((gen_reg_update_Sep  {[(r1,i1):=w1; (r2,i2):=w2 ;(r3,i3):=w3;(r4,i4):=w4]}
                                   {[(r1,i1):=w1'; (r2,i2):=w2'; (r3,i3):=w3'; (r4, i4):=w4']}) with "Hreg [Hr1 Hr2 Hr3 Hr4]")
      as ">[Hreg Hr123]" ;eauto;[set_solver| | ].
    rewrite !big_sepM_insert ?big_sepM_empty;eauto.
    iFrame.
    rewrite !big_sepM_insert ?big_sepM_empty;eauto.
    iDestruct "Hr123" as "(? & ? & ? & ? & _)".
    rewrite ?insert_union_singleton_l !map_union_assoc.
    simplify_map_eq.
    by iFrame.
  Qed.

End reg_rules.
