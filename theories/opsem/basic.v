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

Definition Word: Type := nat.

Definition GenReg := gmap GenRegName Word.
Definition SysReg := gmap SysRegName Word.


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
  decodeInstr : Z → instr;
  encodeInstr : instr → Z;

  decode_encode_instr_inv :
    forall (i: instr), decodeInstr (encodeInstr i) = i;
}.


(*TODO: Memory *)
