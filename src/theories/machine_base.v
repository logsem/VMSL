From stdpp Require Import countable fin vector.
From Coq Require Import ssreflect Bool Eqdep_dec.
From ExtLib Require Import Structures.Monads.

Open Scope general_if_scope.

Definition RegCountLowerBound := 30.
Definition WordSizeLowerBound := 15.
(* Definition AddressSpaceSizeLowerBound := 1023. *)
Definition PageSizeLowerBound := 15.

(* TODO: ZArith seems to be much more convenient *)
Class MachineParameters := {
  WordSize : nat;
  WordSizeAtLeast : WordSizeLowerBound < WordSize;
  RegCount : nat;
  RegCountAtLeast : RegCountLowerBound < RegCount;
  (*
  AddressSpaceSize : nat;
  AddressSpaceSizeAtLeast : AddressSpaceSizeLowerBound < AddressSpaceSize;
   *)
  (*
  DecodeAddress : fin WordSize -> option (fin AddressSpaceSize);
  EncodeAddress : fin AddressSpaceSize -> fin WordSize;
  DecodeEncodeAddress : forall (addr : fin AddressSpaceSize), DecodeAddress (EncodeAddress addr) = Some addr;
   *)
  PageSize : nat; (* in words *)
  PageSizeAtLeast : PageSizeLowerBound < PageSize;
  PageCount : nat;
  DecodePID : fin WordSize -> option (fin PageCount);
  EncodePID : fin PageCount -> fin WordSize;
  DecodeEncodePID : forall (pid : fin PageCount), DecodePID (EncodePID pid) = Some pid;
  PageSizeSanity : PageSize * PageCount = WordSize;
  MMTranslation : fin WordSize -> fin PageCount;
  MMTranslationInv : fin PageCount -> vec (fin WordSize) PageSize;
  }.

Context `(MachineParams : MachineParameters).

Definition Word : Type :=
  fin WordSize.

Instance eqDecisionWord : EqDecision Word.
Proof.
  solve_decision.
Qed.

Instance countableWord : Countable Word.
Proof.
  refine {| encode := _;
            decode := _;
            decode_encode := _ |}.
  apply fin_countable.
Qed.

Inductive RegName : Type :=
| PC
| NZ
| R (n : nat) (fin : n < RegCount).

Instance eqDecisionRegName : EqDecision RegName.
Proof.
  intros x y. destruct x as [| | n fin], y as [| | n' fin']; try (by left); try (by right).
  destruct (nat_eq_dec n n').
  - subst n'; left; f_equal; apply proof_irrel.
  - right; congruence.
Qed.

Program Definition n_to_regname (n : nat) : option RegName :=
  if (nat_lt_dec n RegCount) then Some (R n _) else None.
Next Obligation.
  auto.
Defined.

Instance countableRegName : Countable RegName.
Proof.
  refine {| encode r := encode match r with
                               | PC => inl false
                               | NZ => inl true
                               | R n fin => inr n
                               end;
            decode n := match (decode n) with
                        | Some (inl false) => Some PC
                        | Some (inl true) => Some NZ
                        | Some (inr n) => n_to_regname n
                        | None => None
                        end;
            decode_encode := _ |}.
  intro r. destruct r; auto.
  rewrite decode_encode.
  unfold n_to_regname.
  destruct (nat_lt_dec n RegCount).
  - do 2 f_equal; apply proof_irrel.
  - exfalso; auto.
Qed.

Inductive Ownership : Type :=
| Owned
| NotOwned.

Instance eqDecisionOwnership : EqDecision Ownership.
Proof.
  solve_decision.
Qed.

Inductive Access : Type :=
| NoAccess
| SharedAccess
| ExclusiveAccess.

Instance eqDecisionAccess : EqDecision Access.
Proof.
  solve_decision.
Qed.

Definition Perm : Type :=
  (Ownership * Access).

Definition isAccessible (p : Perm) : bool :=
  match p with
  | (_, SharedAccess) => true
  | (_, ExclusiveAccess) => true
  | _ => false
  end.

Definition isOwned (p : Perm) : bool :=
  match p with
  | (Owned, _) => true
  | _ => false
  end.

Instance eqDecisionPerm : EqDecision Perm.
Proof.
  solve_decision.
Qed.

Inductive TransactionType : Type :=
| Donation
| Sharing
| Lending.

Instance eqDecisionTransactionType : EqDecision TransactionType.
Proof.
  solve_decision.
Qed.

Inductive Instruction : Type :=
| Mov (dst : RegName) (src : Word + RegName)
| Ldr (dst : RegName) (src : RegName)
| Str (src : RegName) (dst : RegName)
| Cmp (arg1 : RegName) (arg2 : Word + RegName)
| Jnz (arg : RegName)
| Jmp (arg : RegName)
| Halt
| Fail
| Hvc.

Class InstructionSerialization := {
  DecodeInstr : Word * Word -> option Instruction;
  EncodeInstr : Instruction -> Word * Word;
  DecodeEncodeInstr : forall (i : Instruction), DecodeInstr (EncodeInstr i) = Some i;
                                 }.

Context `(InstrSer : InstructionSerialization).

Instance eqDecisionInstruction : EqDecision Instruction.
Proof.
  solve_decision.
Qed.

Instance countableInstruction : Countable Instruction.
Proof.
  refine {| encode := fun i => encode (EncodeInstr i);
            decode := fun p => match decode p with
                               | None => None
                               | Some p' => DecodeInstr p'
                               end;
            decode_encode := _ |}.
  intros x.
  rewrite decode_encode.
  apply DecodeEncodeInstr.
Qed.

Definition Addr : Type := Word.

Instance eqDecisionAddr : EqDecision Addr.
Proof.
  solve_decision.
Qed.

Instance countableAddr : Countable Addr.
Proof.
  refine {| encode := _;
            decode := _;
            decode_encode := _ |}.
  apply fin_countable.
Qed.

Inductive HvcFunc : Type :=
  Run
| Yield
| Share
| Lend 
| Donate
| Retrieve
| Relinquish
| Reclaim
| Send 
| Wait.

Inductive HvcError : Type :=
  InvParam
| Denied
| Busy
| Ready.

Class HypervisorParameters := {
  VMCount : nat;
  VMCountPos : 0 < VMCount;
  DecodeVMID : Word -> option (fin VMCount);
  EncodeVMID : (fin VMCount)  -> Word;
  DecodeEncodeVMID : forall (vmid : fin VMCount),
      DecodeVMID (EncodeVMID vmid) = Some vmid;
  DecodeHvcFunc : Word -> option HvcFunc;
  EncodeHvcFunc : HvcFunc -> Word;
  DecodeEncodeHvcFunc : forall (hvc : HvcFunc),
      DecodeHvcFunc (EncodeHvcFunc hvc) = Some hvc;
  DecodeHvcError : Word -> option HvcError;
  EncodeHvcError : HvcError -> Word;
  DecodeEncodeHvcError : forall (hvc : HvcError),
      DecodeHvcError (EncodeHvcError hvc) = Some hvc;
  DecodeTransactionType : Word -> option TransactionType;
  EncodeTransactionType : TransactionType -> Word;
  DecodeEncodeTransactionType : forall (ty : TransactionType),
      DecodeTransactionType (EncodeTransactionType ty) = Some ty
                             }.
