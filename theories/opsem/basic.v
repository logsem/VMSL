From Coq Require Import Eqdep_dec.
From Coq.micromega Require Import ZifyClasses.
From stdpp Require Import gmap fin_maps list.



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

Definition z_of (a: Addr): Z :=
  match a with
  | A z _ _ => z
  end.

Coercion z_of: Addr >-> Z.

Lemma z_of_eq a1 a2 :
  z_of a1 = z_of a2 ->
  a1 = a2.
Proof.
  destruct a1, a2; cbn. intros ->.
  repeat f_equal; apply eq_proofs_unicity; decide equality.
Qed.

Lemma eq_z_of a1 a2 :
  a1 = a2 ->
  z_of a1 = z_of a2.
Proof. destruct a1; destruct a2. congruence. Qed.

Global Instance addr_eq_dec: EqDecision Addr.
Proof.
intros x y. destruct x,y. destruct (Z_eq_dec z z0).
- left. subst z0. eapply z_of_eq; eauto.
- right. inversion 1. simplify_eq.
Defined.

Definition z_to_addr (z : Z) : option Addr.
Proof.
  destruct (Z_le_dec z MemNum),(Z_le_dec 0 z).
  - apply (Z.leb_le z MemNum) in l.
    apply (Z.leb_le 0 z) in l0.
    exact (Some (A z l l0)).
  - exact None.
  - exact None.
  - exact None.
Defined.

Global Instance addr_countable : Countable Addr.
Proof.
  refine {| encode r := encode (z_of r) ;
            decode n := match (decode n) with
                        | Some z => z_to_addr z
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

Definition pid_of (a : Addr) : PID.
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


(*TODO: MailBox*)



(*TODO: State*)



(*TODO: ShareState*)



(*TODO: ExecConf*)
