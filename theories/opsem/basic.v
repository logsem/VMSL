From Coq Require Import Eqdep_dec.
From Coq.micromega Require Import ZifyClasses.
From stdpp Require Import base gmap fin_maps list.



(*Register*)

Definition RegNum: nat := 31.

Inductive GenRegName: Type :=
| PC
| R (n: nat) (fin: n <=? RegNum = true).

Inductive SysRegName: Type :=
| NZ
| CNTVAL
| CNTCTL.

(*To use RegName in gmap, have to show countable*)
Global Instance genreg_eq_dec : EqDecision GenRegName.
Proof.
  unfold EqDecision.
  intros.
  unfold Decision.
  destruct x,y.
  - by left.
  - by right.
  - by right.
  - destruct (nat_eq_dec n n0).
      subst n0.
      * left.
        assert (forall (n m: nat) (P1 P2: n <=? m =true), P1 = P2).
        { intros. apply eq_proofs_unicity. intros. destruct x,y;auto. }
        rewrite (H _ _ fin fin0).
        done.
      * right.
        congruence.
Defined.

Program Definition n_to_genregname (n : nat) : option GenRegName :=
  if (nat_le_dec n RegNum) then Some (R n _) else None.
Next Obligation.
Proof.
  intros.
  apply Nat.leb_le.
  done.
Defined.

Global Instance genreg_countable : Countable GenRegName.
Proof.
  refine {| encode r := encode match r with
                               | PC => inl ()
                               | R n fin => inr n
                               end;
            decode n := match (decode n) with
                        | Some (inl ()) => Some PC
                        | Some (inr n) => n_to_genregname n
                        | None => None
                        end;
            decode_encode := _ |}.
  intro r.
  destruct r;auto.
  rewrite decode_encode.
  unfold n_to_genregname.
  destruct (nat_le_dec n RegNum).
  - do 2 f_equal.
    apply eq_proofs_unicity.
    decide equality.
  - exfalso.
    apply (Nat.leb_le n RegNum) in fin.
    contradiction.
 Defined.

Global Instance sysreg_eq_dec : EqDecision SysRegName.
Proof.
  unfold EqDecision.
  intros.
  unfold Decision.
  destruct x,y;try (left;done);right;done.
Defined.

Global Instance sysreg_countable : Countable SysRegName.
Proof.
  refine {| encode r := encode match r with
                               | NZ => inr 0
                               | CNTVAL => inr 1
                               | CNTCTL =>inr 2
                               end;
            decode n := match (decode n) with
                        | Some (inl ()) => None
                        | Some (inr 0) => Some NZ
                        | Some (inr 1) => Some CNTVAL
                        | Some (inr 2) => Some CNTCTL
                        | Some (inr _) => None
                        | None => None
                        end;
            decode_encode := _ |}.
  intro r.
  destruct r;auto;
  rewrite decode_encode;done.
Defined.

Definition WordNum : Z :=Z.pow 2 64.

Inductive Word: Type :=
| W (z : Z) (fin: Z.leb z WordNum = true) (pos: Z.leb 0 z = true).

Definition z_of_w (w: Word): Z :=
  match w with
  | W z _ _ => z
  end.

Definition GenReg := gmap GenRegName Word.
Definition SysReg := gmap SysRegName Word.

Definition GenRegLocate (reg : GenReg) (r : GenRegName) : Word.
Proof.
  destruct (reg !! r).
  - exact w.
  - exact (W WordNum eq_refl eq_refl).
Defined.
Definition SysRegLocate (reg : SysReg) (r : SysRegName) : Word.
Proof.
  destruct (reg !! r).
  - exact w.
  - exact (W WordNum eq_refl eq_refl).
Defined.

(*Instruction*)

Inductive instr: Type :=
| br (r: GenRegName)
| bne (r: GenRegName)
| mov (dst: GenRegName) (src: Word)
| ldr (dst src: GenRegName)
| str (dst src: GenRegName)
| add (dst r1 r2: GenRegName)
| sub (dst r1 r2: GenRegName)
| cmp (r1 r2: GenRegName)
| hvc
| mrs (dst: GenRegName) (src: SysRegName)
| msr (dst: SysRegName) (src: GenRegName)
| faili
| halt.


(* Encoding *)

Class InstrEncoding := {
  decodeInstr : Word → instr;
  encodeInstr : instr → Word;

  decode_encode_instr_inv :
    forall (i: instr), decodeInstr (encodeInstr i) = i;
}.


(*Memory *)

Definition MemNum : Z := Z.pow 2 48.

Inductive Addr: Type :=
| A (z : Z) (fin: Z.leb z MemNum = true) (pos: Z.leb 0 z = true).

Definition z_of_a (a: Addr): Z :=
  match a with
  | A z _ _ => z
  end.

Coercion z_of_a: Addr >-> Z.

Lemma z_of_eq a1 a2 :
  z_of_a a1 = z_of_a a2 ->
  a1 = a2.
Proof.
  destruct a1, a2; cbn. intros ->.
  repeat f_equal; apply eq_proofs_unicity; decide equality.
Qed.

Lemma eq_z_of a1 a2 :
  a1 = a2 ->
  z_of_a a1 = z_of_a a2.
Proof. destruct a1; destruct a2. congruence. Qed.

Global Instance addr_eq_dec: EqDecision Addr.
Proof.
intros x y. destruct x,y. destruct (Z_eq_dec z z0).
- left. subst z0. eapply z_of_eq; eauto.
- right. inversion 1. simplify_eq.
Defined.

Definition z_to_addr (z : Z) :  Addr.
Proof.
  destruct (Z_le_dec z MemNum),(Z_le_dec 0 z).
  - apply (Z.leb_le z MemNum) in l.
    apply (Z.leb_le 0 z) in l0.
    exact (A z l l0).
  - exact (A MemNum eq_refl eq_refl).
  - exact (A 0 eq_refl eq_refl).
  - apply (Znot_le_gt _ _) in n.
    exfalso.
    apply n0.
    assert (0< z)%Z.
    { apply (Z.lt_trans _ MemNum _). done. apply Z.gt_lt in n. assumption. }
    lia.
Defined.

Global Instance addr_countable : Countable Addr.
Proof.
  refine {| encode r := encode (z_of_a r) ;
            decode n := match (decode n) with
                        | Some z => Some (z_to_addr z)
                        | None => None
                        end ;
            decode_encode := _ |}.
  intro r. destruct r; auto.
  rewrite decode_encode.
  unfold z_to_addr. simpl.
  destruct (Z_le_dec z MemNum),(Z_le_dec 0 z).
  - repeat f_equal; apply eq_proofs_unicity; decide equality.
  - exfalso. by apply (Z.leb_le 0 z) in pos.
  - exfalso. by apply (Z.leb_le z MemNum) in fin.
  - exfalso. by apply (Z.leb_le z MemNum) in fin.
Defined.

Definition Mem := gmap Addr Word.


Definition MemLocate (mem : Mem) (a : Addr): Word.
Proof.
  destruct (mem !! a).
  - exact w.
  - exact (W WordNum eq_refl eq_refl).
Defined.

(*PID*)

Definition PageBitSize : Z := 12.

Definition PIDNum :Z := Z.shiftr MemNum PageBitSize.

Inductive PID :Type :=
  | P (z:Z) (fin: Z.leb z PIDNum = true) (pos: Z.leb 0 z = true).

(*helper lemmas for pid_of*)
Lemma iter_div2_zero:forall (s:positive), (0=(Pos.iter Z.div2 0 s))%Z.
Proof.
  intro.
  induction s as [s|s|];simpl.
  do 2 rewrite <-IHs;done.
do 2  rewrite <-IHs;done.
  done.
Qed.

Lemma iter_div2_noneg:forall (m s:positive), (0≤(Pos.iter Z.div2 (Z.pos m) s))%Z.
Proof.
  intros.
  generalize dependent m.
  induction s as [s|s|];simpl.
  - intro.
    rewrite Z.div2_nonneg.
    destruct (Pos.iter Z.div2 (Z.pos m) s)%Z eqn:Heqn.
    rewrite <-(iter_div2_zero s);done.
    apply (IHs p).
    assert (0 ≤Z.neg p)%Z.
    { rewrite <-Heqn. apply (IHs m).}
    contradiction.
  - intro.
    destruct (Pos.iter Z.div2 (Z.pos m) s)%Z eqn:Heqn.
    rewrite <-(iter_div2_zero s);done.
    apply (IHs p).
    assert (0 ≤Z.neg p)%Z.
    { rewrite <-Heqn. apply (IHs m).}
    contradiction.
  - intro.
    destruct m;simpl;done.
Qed.

Lemma Zpos_le: forall (m n:positive), (m ≤ n)%positive <-> ((Z.pos m)≤(Z.pos n))%Z.
Proof.
  intros.
  split.
  - intro.
    done.
  - intro.
    done.
Qed.

Lemma iter_div2_mono:forall (m n s:positive), (0 ≤ Z.pos s)%Z -> (m≤n)%positive
        → (Pos.iter Z.div2 (Z.pos m) s ≤ Pos.iter Z.div2 (Z.pos n) s)%Z.
Proof.
  intros.
  generalize dependent m.
  generalize dependent n.
  induction s as [s | s|];simpl.
  - intros.
    do 2 rewrite Zdiv2_div.
    apply Z_div_le.
    done.
    destruct (Pos.iter Z.div2 (Z.pos m) s)%Z eqn:Heqm.
    + rewrite <-(iter_div2_zero s).
      destruct (Pos.iter Z.div2 (Z.pos n) s)%Z eqn:Heqn.
      * rewrite <-(iter_div2_zero s);done.
      * apply iter_div2_noneg.
      * assert (0 ≤Z.neg p)%Z.
        { rewrite <-Heqn. apply iter_div2_noneg.}
        contradiction.
    + destruct (Pos.iter Z.div2 (Z.pos n) s)%Z eqn:Heqn.
      * rewrite <-(iter_div2_zero s).
        destruct (Pos.iter Z.div2 (Z.pos p) s)%Z eqn:Heqp.
        done.
        exfalso.
        assert (Z.pos p ≤ 0)%Z.
        { rewrite <-Heqn, <-Heqm. apply (IHs). done. done. }
        contradiction.
        done.
      * apply IHs.
        done.
        rewrite Zpos_le.
        rewrite <-Heqm,<-Heqn.
        apply IHs.
        done.
        done.
      * exfalso.
        assert (Z.pos p ≤ Z.neg p0)%Z.
        { rewrite <-Heqn, <-Heqm. apply (IHs). done. done. }
        contradiction.
    + assert (0 ≤Z.neg p)%Z.
        { rewrite <-Heqm. apply iter_div2_noneg.}
        contradiction.
  - intros.
    destruct (Pos.iter Z.div2 (Z.pos m) s)%Z eqn:Heqm.
    + rewrite <-(iter_div2_zero s).
      destruct (Pos.iter Z.div2 (Z.pos n) s)%Z eqn:Heqn.
      * rewrite <-(iter_div2_zero s);done.
      * apply iter_div2_noneg.
      * assert (0 ≤Z.neg p)%Z.
        { rewrite <-Heqn. apply iter_div2_noneg.}
        contradiction.
    + destruct (Pos.iter Z.div2 (Z.pos n) s)%Z eqn:Heqn.
      * rewrite <-(iter_div2_zero s).
        destruct (Pos.iter Z.div2 (Z.pos p) s)%Z eqn:Heqp.
        done.
        exfalso.
        assert (Z.pos p ≤ 0)%Z.
        { rewrite <-Heqn, <-Heqm. apply (IHs). done. done. }
        contradiction.
        done.
      * apply IHs.
        done.
        rewrite Zpos_le.
        rewrite <-Heqm,<-Heqn.
        apply IHs.
        done.
        done.
      * exfalso.
        assert (Z.pos p ≤ Z.neg p0)%Z.
        { rewrite <-Heqn, <-Heqm. apply (IHs). done. done. }
        contradiction.
    + assert (0 ≤Z.neg p)%Z.
        { rewrite <-Heqm. apply iter_div2_noneg.}
        contradiction.
  - intros.
    destruct m,n;try done.
    + simpl.
      rewrite <-Zpos_le.
      lia.
    + simpl.
      rewrite <-Zpos_le.
      lia.
Qed.

Lemma shiftr_le: forall (m n s: Z), (0≤m)%Z -> (0≤n)%Z -> (0≤s)%Z-> (m≤n)%Z -> ((m≫s) ≤ (n ≫s))%Z.
Proof.
  intros.
  destruct m ,n; try (rewrite (Z.shiftr_0_l _));auto;try contradiction.
  - rewrite (Z.shiftr_nonneg _ _). done.
  - destruct s.
    + rewrite (Z.shiftr_0_r _).
      rewrite (Z.shiftr_0_r _).
      done.
    + unfold Z.shiftr.
      unfold Z.shiftl.
      simpl.
      apply iter_div2_mono.
      done.
      rewrite Zpos_le.
      done.
    + unfold Z.shiftr.
      unfold Z.shiftl.
      simpl.
      done.
Defined.

Definition a_to_pid (a : Addr) : PID.
Proof.
  destruct a.
  assert(z ≫ PageBitSize ≤ PIDNum)%Z.
  { unfold PIDNum.
    apply (Z.leb_le z MemNum) in fin.
    apply (Z.leb_le 0 z) in pos.
    apply shiftr_le;done.
  }
  apply (Z.leb_le (z≫ PageBitSize) PIDNum) in H.
    apply (Z.leb_le 0 z) in pos.
    assert (0≤ (z ≫ PageBitSize))%Z.
    { apply Z.shiftr_nonneg.  done. }
   apply (Z.leb_le 0 (z≫ PageBitSize)) in H0.
    exact (P (z≫ PageBitSize)%Z H H0).
Defined.


(*VMID*)

Definition VMID :Type := nat.


(*MailBox*)

Definition MB :Type := (option PID) * option(PID * bool * Word * VMID).


(*TODO: State*)

Definition z_of_p (p: PID): Z :=
  match p with
  | P z _ _ => z
  end.

Coercion z_of_p: PID >-> Z.

Lemma z_of_p_eq a1 a2 :
  z_of_p a1 = z_of_p a2 ->
  a1 = a2.
Proof.
  destruct a1, a2; cbn. intros ->.
  repeat f_equal; apply eq_proofs_unicity; decide equality.
Qed.

Lemma eq_z_of_p a1 a2 :
  a1 = a2 ->
  z_of_p a1 = z_of_p a2.
Proof. destruct a1; destruct a2. congruence. Qed.


Global Instance pid_eq_dec: EqDecision PID.
Proof.
intros x y. destruct x,y. destruct (Z_eq_dec z z0).
- left. subst z0. eapply z_of_p_eq; eauto.
- right. inversion 1. simplify_eq.
Defined.

Definition z_to_pid (z : Z) : PID.
Proof.
  destruct (Z_le_dec z PIDNum),(Z_le_dec 0 z).
  - apply (Z.leb_le z PIDNum) in l.
    apply (Z.leb_le 0 z) in l0.
    exact (P z l l0).
  - exact (P PIDNum eq_refl eq_refl).
  - exact (P 0 eq_refl eq_refl).
  - apply (Znot_le_gt _ _) in n.
    exfalso.
    apply n0.
    assert (0< z)%Z.
    { apply (Z.lt_trans _ PIDNum _). done. apply Z.gt_lt in n. assumption. }
    lia.
Defined.


Global Instance pid_countable : Countable PID.
Proof.
  refine {| encode r := encode (z_of_p r) ;
            decode n := match (decode n) with
                        | Some z => Some (z_to_pid z)
                        | None => None
                        end ;
            decode_encode := _ |}.
  intro r. destruct r; auto.
  rewrite decode_encode.
  unfold z_to_pid. simpl.
  destruct (Z_le_dec z PIDNum),(Z_le_dec 0 z).
  - repeat f_equal; apply eq_proofs_unicity; decide equality.
  - exfalso. by apply (Z.leb_le 0 z) in pos.
  - exfalso. by apply (Z.leb_le z PIDNum) in fin.
  - exfalso. by apply (Z.leb_le z PIDNum) in fin.
Defined.

Definition State: Type := (gset PID) *( GenReg * (SysReg * MB)).


(*ShareState*)

Definition ShareStates: Type := list (PID * VMID).


(*ExecConf*)

Definition ExecConf: Type := list State * (Mem * ShareStates).


(*ExecMode*)

Inductive DoneState: Type:=
| Next (v: VMID)
| Halt
| Fail.

Inductive ExecMode: Type :=
| ExecInstr (v: VMID)
| Repeat (u : ExecMode)
| Done (d : DoneState).


(*Conf*)

Definition Conf : Type := ExecMode * ExecConf.

Implicit Type ϕ : ExecConf.
Implicit Type Δ : list (State).
Implicit Type δ : State.
Implicit Type m : Mem.
Implicit Type s : ShareStates.
Implicit Type v n : VMID.

Definition mem_of  ϕ  : Mem := fst (snd ϕ) .

Fixpoint ith_of {A} (l: list A) (i:nat): option A :=
  match i with
  | 0 => match l with
         | cons a _ => Some a
         |  nil => None
         end
  | S n => match l with
           |  nil => None
           |  cons a l' => ith_of l' n
           end
  end.


Definition state_of Δ (v:VMID) : option State := ith_of Δ v.

Definition sysreg_of δ: SysReg := fst (snd (snd δ)).

Definition genreg_of δ: GenReg := fst (snd δ).

Definition pids_of δ : gset PID := fst δ.

Definition mb_of δ : MB := snd (snd (snd δ)).

Notation "ϕ .m" := (mem_of ϕ) (at level 20).
Notation "δ .gr" := (genreg_of δ) (at level 20).
Notation "δ .sr" := (sysreg_of δ) (at level 20).
Notation "δ .ps" := (pids_of δ) (at level 20).
Notation "δ .π" := (mb_of δ) (at level 20).
Notation "Δ !s! i " := (state_of Δ i) (at level 20).
Notation "g !gr! r " := (GenRegLocate g r)(at level 20).
Notation "s !sr! r " := (SysRegLocate s r)(at level 20).


Inductive MemPermission :Type :=
| VA
| RE
| WR.


(* helper functions *)
Definition w_to_a (w:Word): Addr.
Proof.
  destruct w.
  destruct (Z_le_dec z MemNum).
  - apply (Z.leb_le z MemNum) in l.
    exact (A z l pos).
  - exact (A MemNum eq_refl eq_refl).
Defined.

Definition valid_a δ (r: GenRegName) (p : MemPermission) : option Addr.
Proof.
  destruct p eqn:Hp.
  - exact ((gset_to_gmap (w_to_a (δ.gr !gr! r)) (pids_of δ)) !! (a_to_pid (w_to_a (δ.gr !gr! r)))).
  - destruct (δ.π.2).
    + destruct p0.1.1.
      destruct (decide ((a_to_pid (w_to_a (δ.gr !gr! r)))=p1)).
      exact (Some (w_to_a (δ.gr !gr! r))).
      exact ((gset_to_gmap (w_to_a (δ.gr !gr! r)) (pids_of δ)) !! (a_to_pid (w_to_a (δ.gr !gr! r)))).
    + exact ((gset_to_gmap (w_to_a (δ.gr !gr! r)) (pids_of δ)) !! (a_to_pid (w_to_a (δ.gr !gr! r)))).
  - destruct (δ.π.1).
    + destruct (decide ((a_to_pid (w_to_a (δ.gr !gr! r)))=p0)).
      exact (Some (w_to_a (δ.gr !gr! r))).
      exact ((gset_to_gmap (w_to_a (δ.gr !gr! r)) (pids_of δ)) !! (a_to_pid (w_to_a (δ.gr !gr! r)))).
    + exact ((gset_to_gmap (w_to_a (δ.gr !gr! r)) (pids_of δ)) !! (a_to_pid (w_to_a (δ.gr !gr! r)))).
Defined.

Definition w_add_z (w: Word) (i:Z) : Word.
Proof.
  destruct w.
  assert ((0 ≤ (Z.modulo (z+i) WordNum) )%Z
          ∧ ((Z.modulo (z+i) WordNum)< WordNum)%Z).
  { apply (Z_mod_lt (z+i) WordNum). done. }
  destruct H.
  apply (Z.leb_le 0 (Z.modulo (z+i) WordNum)) in H.
  apply Z.lt_le_incl in H0.
  apply (Z.leb_le (Z.modulo (z+i) WordNum) WordNum) in H0.
  exact (W (Z.modulo (z+i) WordNum) H0 H).
Defined.

Definition w_add_w (w1: Word) (w2: Word) : Word:=
  match w2 with
  | W z _ _ => (w_add_z w1 z)
  end.

Definition w_sub_z (w: Word) (i:Z) : Word.
Proof.
  destruct w.
  assert ((0 ≤ (Z.modulo (z-i) WordNum) )%Z
          ∧ ((Z.modulo (z-i) WordNum)< WordNum)%Z).
  { apply (Z_mod_lt (z-i) WordNum). done. }
  destruct H.
  apply (Z.leb_le 0 (Z.modulo (z-i) WordNum)) in H.
  apply Z.lt_le_incl in H0.
  apply (Z.leb_le (Z.modulo (z-i) WordNum) WordNum) in H0.
  exact (W (Z.modulo (z-i) WordNum) H0 H).
Defined.

Definition w_sub_w (w1: Word) (w2: Word) : Word:=
  match w2 with
  | W z _ _ => (w_sub_z w1 z)
  end.


Definition upd_gen_reg Δ v (r: GenRegName) (w: Word): list State :=
  match (Δ !s! v) with
    | Some δ => <[v:=(δ.ps, (<[r:=w]>(δ.gr), (δ.sr, δ.π )))]>Δ
    | None => Δ
  end.

Definition upd_sys_reg Δ v (r: SysRegName) (w: Word): list State :=
  match (Δ !s! v) with
    | Some δ => <[v:=(δ.ps, ( δ.gr ,(<[r:=w]>(δ.sr), δ.π )))]>Δ
    | None => Δ
  end.



Definition updPC Δ m s v: ExecConf :=
  match (Δ !s! v) with
  |Some δ => ((upd_gen_reg Δ v PC (w_add_z ((δ.gr) !gr! PC) 1)) ,(m,s))
  |None => (Δ, (m,s))
  end.

Definition ident Δ m s v: ExecConf :=
  (Δ, (m,s)).

Inductive ReturnCode: Type:=
|INTERRUPT
|SUCCESS
|BUSY
|MSG_WAIT
|MSG_SEND
|MEM_RTRVP
|YIELD.

Definition rc_to_w (rc : ReturnCode):Word.
Proof.
  destruct rc eqn:Hrc.
  - exact (W 0 eq_refl eq_refl).
  - exact (W 1 eq_refl eq_refl).
  - exact (W 2 eq_refl eq_refl).
  - exact (W 3 eq_refl eq_refl).
  - exact (W 4 eq_refl eq_refl).
  - exact (W 5 eq_refl eq_refl).
  - exact (W 6 eq_refl eq_refl).
Defined.

Definition z_to_w (z:Z):Word.
Proof.
  destruct (Z_le_dec 0%Z z), (Z_le_dec z WordNum).
  - apply (Z.leb_le 0 z) in l.
    apply (Z.leb_le z WordNum) in l0.
    exact (W z l0 l).
  - exact (W WordNum eq_refl eq_refl).
  - exact (W 0 eq_refl eq_refl).
  - apply (Znot_le_gt _ _) in n0.
    exfalso.
    apply n.
    assert (0< z)%Z.
    { apply (Z.lt_trans _ WordNum _). done. apply Z.gt_lt in n0. assumption. }
    lia.
Defined.


Definition nat_to_w (n:nat):Word:=
(z_to_w (Z.of_nat n)).

Definition nat_to_r (n:nat):GenRegName.
Proof.
  destruct (decide(n≤ RegNum)).
  - apply (Nat.leb_le n RegNum) in l.
    exact (R n l).
  - exact (R RegNum eq_refl).
Defined.

Definition tick Δ m s v n (f: list State -> Mem -> ShareStates -> VMID -> ExecConf): Conf :=
  match (Δ !s! 0) with
  | Some δ_p =>match (Δ !s! v) with
                 | Some δ_v =>if (andb (Z.leb (z_of_w (δ_p.sr !sr! CNTVAL)) 1) (Z.eqb (z_of_w (δ_p.sr !sr! CNTCTL)) 1)) then
                                let Δ' := upd_sys_reg Δ 0 CNTVAL (w_sub_z (δ_p.sr !sr! CNTVAL) 1) in
                                let Δ' := upd_sys_reg Δ' 0 CNTCTL (z_to_w 0) in
                                let Δ' := upd_gen_reg Δ' 0 (nat_to_r 0) (rc_to_w INTERRUPT) in
                                let Δ' := upd_gen_reg Δ' 0 (nat_to_r 1) (nat_to_w v) in
                                ((Done (Next 0)),(f Δ' m s v))
                              else
                                let Δ' := upd_sys_reg Δ 0 CNTVAL (w_sub_z (δ_p.sr !sr! CNTVAL) 1) in
                                ((Done (Next n)),(f Δ' m s v))
                 |None => (Done Fail, (Δ,(m, s)))
               end
  |None => (Done Fail, (Δ, (m, s )))
  end.


Definition comb (w1 w2 : Word) : Word:=
  match w1 with
  | (W z _ _) => w_add_z w2 (Z.shiftl z 32)
  end.


(*TODO decode*)
