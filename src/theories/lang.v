From Coq Require Import ssreflect Bool Eqdep_dec.
From ExtLib Require Import Structures.Monads.
From stdpp Require Import gmap fin_maps list binders strings countable fin mapset fin_map_dom listset_nodup.
From iris.prelude Require Import options.
From iris.algebra Require Import ofe.
From iris.program_logic Require Import language ectx_language ectxi_language.

Instance MonadOption : Monad option.
Proof.
  refine {| ret t x := Some x;
            bind t u mt f := match mt with | None => None | Some t => f t end;
         |}.
Qed.

Module MonadBaseNotation.
  
  Delimit Scope monad_scope with monad.
  
  Notation "c >>= f" := (@bind _ _ _ _ c f) (at level 58, left associativity) : monad_scope.
  Notation "f =<< c" := (@bind _ _ _ _ c f) (at level 62, right associativity) : monad_scope.
  Notation "f >=> g" := (@mcompose _ _ _ _ _ f g) (at level 62, right associativity) : monad_scope.
  
  Notation "e1 ;;; e2" := (@bind _ _ _ _ e1%monad (fun _ => e2%monad))%monad
                                                                     (at level 62, right associativity) : monad_scope.
  
End MonadBaseNotation.

Module MonadNotation.
  
  Export MonadBaseNotation.
  
  Notation "x <- c1 ;;; c2" := (@bind _ _ _ _ c1 (fun x => c2))
                                (at level 62, c1 at next level, right associativity) : monad_scope.
  
  Notation "' pat <- c1 ;;; c2" :=
    (@bind _ _ _ _ c1 (fun x => match x with pat => c2 end))
      (at level 62, pat pattern, c1 at next level, right associativity) : monad_scope.
  
End MonadNotation.

Module MonadLetNotation.
  
  Export MonadBaseNotation.
  
  Notation "'let*' p ':=' c1 'in' c2" := (@bind _ _ _ _ c1 (fun p => c2))
                                           (at level 62, p as pattern, c1 at next level, right associativity) : monad_scope.
  
End MonadLetNotation.

Fixpoint listFromSome {A : Type} (l : list (option A)) : list A :=
  match l with
  | nil => nil
  | cons x xs =>
    match x with
    | None => listFromSome xs
    | Some x' => cons x' (listFromSome xs)
    end
  end.

Definition WordUpperBound := 65536.

Definition Word : Type :=
  fin WordUpperBound.

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

Class ArchitectureParameters := {
  RegCount : nat;
                               }.

Context `(ArchParams : ArchitectureParameters).

Inductive RegName : Type :=
| PC
| NZ
| R (n : nat) (fin : n <=? RegCount = true).

Instance eqDecisionRegName : EqDecision RegName.
Proof.
  intros x y. destruct x as [| | n fin], y as [| | n' fin']; try (by left); try (by right).
  destruct (nat_eq_dec n n').
  - subst n'. left.
    assert (forall (b: bool) (n m: nat) (P1 P2: n <=? m = b), P1 = P2).
    { intros. apply eq_proofs_unicity.
      intros; destruct x; destruct y; auto. }
    rewrite (H _ _ _ fin fin'); reflexivity.
  - right. congruence.
Qed.

Program Definition n_to_regname (n : nat) : option RegName :=
  if (nat_le_dec n RegCount) then Some (R n _) else None.
Next Obligation.
  intros. eapply Nat.leb_le; eauto.
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
  destruct (nat_le_dec n RegCount).
  - do 2 f_equal. apply eq_proofs_unicity. decide equality.
  - exfalso. by apply (Nat.leb_le n RegCount) in fin.
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
| Run (arg : RegName)
| Yield
| Share (addr : RegName) (receivers : list RegName)
| Lend (addr : RegName) (receivers : list RegName)
| Donate (addr : RegName) (receiver : RegName)
| Retrieve (handle : RegName)
| Relinquish (handle : RegName)
| Reclaim (handle : RegName)
| Send (receiver : RegName)
| Receive (dst1 : RegName) (dst2 : RegName)
| Wait.

Instance eqDecisionInstruction : EqDecision Instruction.
Proof.
  solve_decision.
Qed.

Class MachineParameters := {
  AddressSize : nat;
  DecodeInstr : Word -> option Instruction;
  EncodeInstr : Instruction -> Word;
  DecodeEncodeInstr : forall (i : Instruction), DecodeInstr (EncodeInstr i) = Some i;
                          }.

Context `(MachineParams : MachineParameters).

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

Definition Addr : Type :=
  fin AddressSize.

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

Definition Mem : Type :=
  gmap Addr Word.

Definition RegFile : Type :=
  gmap RegName Word.

Class HypervisorParameters := {
  VMCount : nat;
  VMCountStrictlyPositive : 0 < VMCount;
  VMUpperBound : VMCount < WordUpperBound;
                             }.

Context `(HypervisorParams : HypervisorParameters).

Definition VMID : Type :=
  fin VMCount.

Definition PageTable : Type :=
  gmap Addr Perm.

Definition TXBuffer : Type :=
  Addr.

Definition RXBuffer : Type :=
  (Addr * option(VMID)).

Definition MailBox : Type :=
  (TXBuffer * RXBuffer).

Definition CurrentVM := VMID.

Definition VMState : Type :=
  gmap VMID (RegFile * MailBox * PageTable).

Definition Transaction : Type :=
  Addr * TransactionType * listset_nodup VMID * listset_nodup VMID.

Definition Handle := Word.

Definition Transactions : Type :=
  gmap Handle Transaction.

Definition State : Type :=
  VMState * (CurrentVM * (Mem * Transactions)).

Definition vmStates (st : State) : VMState :=
  fst st.

Definition currentVM (st : State) : CurrentVM :=
  fst (snd st).

Definition mem (st : State) : Mem :=
  fst (snd (snd st)).

Definition transactions (st : State) : Transactions :=
  snd (snd (snd st)).

Definition vmState (st : State) (v : VMID) : option (RegFile * MailBox * PageTable) :=
  (vmStates st) !! v.

Definition vmRegFile (st : State) (v : VMID) : option RegFile :=
  match vmState st v with
  | None => None
  | Some a => Some (fst (fst a))
  end.

Definition vmMailBox (st : State) (v : VMID) : option MailBox :=
  match vmState st v with
  | None => None
  | Some a => Some (snd (fst a))
  end.

Definition vmPageTable (st : State) (v : VMID) : option PageTable :=
  match vmState st v with
  | None => None
  | Some a => Some (snd a)
  end.

Definition checkAccess (st : State) (v : VMID) (addr : Addr) : bool :=
  match (vmPageTable st v) with
  | None => false
  | Some pt =>
    match pt !! addr with
    | Some p => isAccessible p
    | _ => false
    end
  end.

Definition checkOwnership (st : State) (v : VMID) (addr : Addr) : bool :=
  match (vmPageTable st v) with
  | None => false
  | Some pt =>
    match pt !! addr with
    | Some p => isOwned p
    | _ => false
    end
  end.

Inductive ExecMode : Type :=
| ExecI
| NextI
| HaltI
| FailI.

Inductive ControlMode : Type :=
| YieldM : VMID -> ControlMode
| NormalM.

Definition Conf : Type := ExecMode * State.

Definition updateReg (st : State) (v : VMID) (r : RegName) (w : Word) : option State :=
  match r with
  | PC => None
  | NZ => None
  | R n fin =>
    match vmState st v with
    | None => None
    | Some (rf, mb, pt) =>
      Some (<[(currentVM st):=(<[r:=w]>rf, mb, pt)]>(vmStates st),
            (currentVM st,
             (mem st, transactions st)))
    end
  end.

Definition updateSysReg (st : State) (v : VMID) (r : RegName) (w : Word) : option State :=
  match r with
  | R n fin => None
  | _ => match vmState st v with
         | None => None
         | Some (rf, mb, pt) =>
           Some (<[(currentVM st):=(<[r:=w]>rf, mb, pt)]>(vmStates st),
                 (currentVM st,
                  (mem st, transactions st)))
         end
  end.

Definition getReg (st : State) (v : VMID) (r : RegName) : option Word :=
  match vmRegFile st v with
  | None => None
  | Some rf => rf !! r 
  end.

Definition updatePageTable (st : State) (v : VMID) (addr : Addr) (p : Perm) : option State :=
  match vmState st v with
  | None => None
  | Some (rf, mb, pt) =>
    Some (<[(currentVM st):=(rf, mb, <[addr:=p]>pt)]>(vmStates st),
          (currentVM st,
           (mem st, transactions st)))
  end.

Definition getPageTable (st : State) (v : VMID) (addr : Addr) : option Perm :=
  match vmPageTable st v with
  | None => None
  | Some pt => pt !! addr
  end.
                
Definition updateMem (st : State) (a : Addr) (w : Word) : State :=
  ((vmStates st), (currentVM st, ((<[a:=w]>(mem st), transactions st)))).

Definition updateMemWithPerm (st : State) (a : Addr) (w : Word) : option State :=
  if checkAccess st (currentVM st) a
  then ret (updateMem st a w)
  else None.

Definition getMem (st : State) (a : Addr) : option Word :=
  (mem st) !! a.

Definition getMemWithPerm (st : State) (a : Addr) : option Word :=
  if checkAccess st (currentVM st) a
  then getMem st a
  else None.

Definition writeTX (st : State) (v : VMID) (msg : Word) : option State :=
  match vmState st v with
  | None => None
  | Some (rf, (txAddr, _), pt) => updateMemWithPerm st txAddr msg
  end.

Definition isRXReady (st : State) (v : VMID) : bool :=
  match vmState st v with
  | Some (rf, (_, (_, Some _)), pt) => true
  | _ => false
  end.

Definition getRXSender (st : State) (v : VMID) : option VMID :=
  match vmState st v with
  | Some (rf, (_, (_, Some v')), pt) => Some v'
  | _ => None
  end.

Definition getRXMsg (st : State) (v : VMID) : option Word :=
  match vmState st v with
  | Some (rf, (_, (addr, Some _)), pt) => getMem st addr
  | _ => None
  end.

Definition emptyRX (st : State) (v : VMID) : option State :=
  match vmState st v with
  | Some (rf, (txAddr, (rxAddr, Some v)), pt) =>
    Some (<[(currentVM st):=(rf, (txAddr, (rxAddr, None)), pt)]>(vmStates st),
          (currentVM st,
           (mem st, transactions st)))
  | _ => None
  end.

Definition transferMsg (st : State) (v : VMID) (r : VMID) : option State :=
  match vmState st v with
  | Some (_, (txAddr, _), _) =>
    match vmState st r with
    | Some (rf, (txAddr', (rxAddr, _)), pt) =>
      match getMem st txAddr with
        | Some val =>
          let st' := updateMem st rxAddr val
          in Some (<[(currentVM st):=(rf, (txAddr', (rxAddr, Some v)), pt)]>(vmStates st),
                   (currentVM st,
                    (mem st, transactions st)))
        | _ => None
      end
    | _ => None
    end
  | _ => None
  end.

Definition tryIncrWord (n : Word) : option Word :=
  match (nat_lt_dec (n + 1) WordUpperBound) with
  | left l => Some (@nat_to_fin (n + 1) _ l)
  | _ => None
  end.

Lemma finMax {n : nat} (x y : fin n) : fin n.
Proof.
  destruct (Fin.to_nat x).
  destruct (Fin.to_nat y).
  destruct (x <? y).
  - apply y.
  - apply x.
Qed.

Definition freshHandleHelper (val : Handle) (acc : option Handle) : option Handle :=
  match (tryIncrWord val) with
  | None => None
  | Some val' => match acc with
                 | None => Some val'
                 | Some acc' => Some (finMax val' acc')
                 end
  end.

Definition freshHandle (m : gmap Handle Transaction) : option Handle := 
  set_fold freshHandleHelper None (@dom (gmap Handle Transaction) (gset Handle) gset_dom m).

Definition insertTransaction (st : State) (h : Handle) (t : Transaction) : State :=
  ((vmStates st), (currentVM st, ((mem st, <[h:=t]>(transactions st))))).

Definition newTransaction (st : State) (v : VMID)
           (addr : Addr) (tt : TransactionType)
           (receivers : listset_nodup VMID)  : option State :=
  if checkOwnership st v addr
  then
    match freshHandle (transactions st) with
    | None => None
    | Some h' =>
      ret (insertTransaction st h' (addr, tt, receivers, listset_nodup_empty))
    end
  else None.

Definition getTransaction (st : State) (h : Handle) : option Transaction :=
  (transactions st) !! h.

Definition removeTransaction (s : State) (handle : Handle) : State :=
  (vmStates s, (currentVM s, (mem s, delete handle (transactions s)))).

Definition updateOffsetPC (st : State) (dir : bool) (offset : nat) : option State :=
  bind
    (vmRegFile st (currentVM st))
    (fun rf =>
       bind (rf !! PC)
            (fun v =>
               let v' := fin_to_nat v in
               if dir
               then
                 match (nat_lt_dec (v' + offset) WordUpperBound) with
                 | left l => updateReg st (currentVM st) PC (@nat_to_fin (v' + offset) _ l)
                 | _ => None
                 end
               else
                 match (nat_lt_dec (v' - offset) WordUpperBound) with
                 | left l => updateReg st (currentVM st) PC (@nat_to_fin (v' - offset) _ l)
                 | _ => None
                 end
    )).

Definition updateIncrPC (st : State) : option State :=
  updateOffsetPC st true 1.

Definition updateCurrentVMID (st : State) (v : VMID) : State :=
  (vmStates st, (v, (mem st, transactions st))).

Definition isPrimary (st : State) : bool :=
  (currentVM st) =? 0.

Definition isSecondary (st : State) : bool :=
  negb (isPrimary st).

Definition wordToVMID (w : Word) : option VMID :=
  let w' := fin_to_nat w in
  match (nat_lt_dec w' VMCount) with
  | left l => Some (nat_to_fin l)
  | _ => None
  end.

Lemma vmidToWord (v : VMID) : Word.
Proof.
  destruct (Fin.to_nat v) as [x l].
  apply (@Fin.of_nat_lt x WordUpperBound
                        (Nat.lt_trans x VMCount WordUpperBound l VMUpperBound)).
 Defined.

Definition wordToAddr (w : Word) : option Addr :=
  let w' := fin_to_nat w in
  match (nat_lt_dec w' AddressSize) with
  | left l => Some (nat_to_fin l)
  | _ => None
  end.

Export MonadNotation.
Open Scope monad_scope.

Definition isValidPC (st : State) : option bool :=
  w <- getReg st (currentVM st) PC ;;;
  addr <- wordToAddr w ;;;
  p <- getPageTable st (currentVM st) addr ;;;
  ret (isAccessible p).

Definition simpleOptionStateUnpack (oldSt : State) (newSt : option State) : Conf :=
  match newSt with
  | None => (FailI, oldSt)
  | Some s => (NextI, s)
  end.

Definition MovHelperWord (s : State) (dst : RegName) (src : Word) : Conf * ControlMode :=
  let comp :=
        s' <- updateReg s (currentVM s) dst src ;;;
        updateIncrPC s'
    in
    (simpleOptionStateUnpack s comp, NormalM).

Definition MovHelperReg (s : State) (dst : RegName) (src : RegName) : Conf * ControlMode :=
  let comp :=
      src' <- getReg s (currentVM s) src ;;;
      s'' <- updateReg s (currentVM s) dst src' ;;;
      updateIncrPC s''
    in
  (simpleOptionStateUnpack s comp, NormalM).

Definition LdrHelper (s : State) (dst : RegName) (src : RegName) : Conf * ControlMode :=
  let comp :=
      src' <- getReg s (currentVM s) src ;;;
      addr <- wordToAddr src' ;;;
      v <- getMemWithPerm s addr ;;;
      m <- updateReg s (currentVM s) dst v ;;;
      updateIncrPC m
  in
  (simpleOptionStateUnpack s comp, NormalM).

Definition StrHelper (s : State) (src : RegName) (dst : RegName) : Conf * ControlMode :=
  let comp :=
      src' <- getReg s (currentVM s) src ;;;
      dst' <- getReg s (currentVM s) dst ;;;                                  
      addr <- wordToAddr dst' ;;;
      m <- updateMemWithPerm s addr src' ;;;
      updateIncrPC m
  in
  (simpleOptionStateUnpack s comp, NormalM).

Program Definition CmpHelperWord (s : State) (arg1 : RegName) (arg2 : Word) : Conf * ControlMode :=
  let comp :=
      arg1' <- getReg s (currentVM s) arg1 ;;;
      m <- match (nat_lt_dec (fin_to_nat arg1') (fin_to_nat arg2)) with
           | left _ => updateSysReg s (currentVM s) NZ (@nat_to_fin 1 WordUpperBound _)
           | right _ => updateSysReg s (currentVM s) NZ (@nat_to_fin 0 WordUpperBound _)
           end ;;;
      updateIncrPC m       
  in
  (simpleOptionStateUnpack s comp, NormalM).
Next Obligation.
  pose proof (Nat.ltb_spec0 1 WordUpperBound) as H;
    remember (1 <? WordUpperBound);
    subst; inversion H; auto.
Qed.
Next Obligation.
  pose proof (Nat.ltb_spec0 0 WordUpperBound) as H;
    remember (0 <? WordUpperBound);
    subst; inversion H; auto.
Qed.

Program Definition CmpHelperReg (s : State) (arg1 : RegName) (arg2 : RegName) : Conf * ControlMode :=
  let comp :=
      arg1' <- getReg s (currentVM s) arg1 ;;;
      arg2' <- getReg s (currentVM s) arg2 ;;;
      m <- match (nat_lt_dec (fin_to_nat arg1') (fin_to_nat arg2')) with
           | left _ => updateSysReg s (currentVM s) NZ (@nat_to_fin 1 WordUpperBound _)
           | right _ => updateSysReg s (currentVM s) NZ (@nat_to_fin 0 WordUpperBound _)
           end ;;;
      updateIncrPC m
  in
  (simpleOptionStateUnpack s comp, NormalM).
Next Obligation.
  pose proof (Nat.ltb_spec0 1 WordUpperBound) as H;
    remember (1 <? WordUpperBound);
    subst; inversion H; auto.
Qed.
Next Obligation.
  pose proof (Nat.ltb_spec0 0 WordUpperBound) as H;
    remember (0 <? WordUpperBound);
    subst; inversion H; auto.
Qed.

Definition JnzHelper (s : State) (arg : RegName) : Conf * ControlMode :=
  let comp :=
      arg' <- getReg s (currentVM s) arg ;;;
      nz <- getReg s (currentVM s) NZ ;;;
      match (fin_to_nat nz) with
      | 0 => updateSysReg s (currentVM s) PC arg'
      | _ => updateIncrPC s
      end
  in
  (simpleOptionStateUnpack s comp, NormalM).

Definition JmpHelper (s : State) (arg : RegName) : Conf * ControlMode :=
  let comp :=
      arg' <- getReg s (currentVM s) arg ;;;
      updateSysReg s (currentVM s) PC arg'
  in
  (simpleOptionStateUnpack s comp, NormalM).

Definition RunHelper (s : State) (arg : RegName) : Conf * ControlMode :=
  let comp :=
      arg' <- getReg s (currentVM s) arg ;;;
      id <- wordToVMID arg' ;;;
      m <- updateIncrPC s ;;;
      ret (m, id)
  in
  match comp with
  | None => (FailI, s, NormalM)
  | Some (st, id) =>
    match fin_to_nat (currentVM st) with
    | 0 => (NextI, st, YieldM id)
    | _ => (FailI, s, NormalM)
    end
  end.

Definition FailHelper (s : State) : Conf * ControlMode :=
  (FailI, s, NormalM).

Definition HaltHelper (s : State) : Conf * ControlMode :=
  (HaltI, s, NormalM).

Definition YieldHelper (s : State) : Conf * ControlMode :=
  let comp := updateIncrPC s
  in
  match comp with
  | None => (FailI, s, NormalM)
  | Some st =>
    match fin_to_nat (currentVM st) with
    | 0 => (FailI, s, NormalM)
    | _ => (NextI, st, YieldM (@nat_to_fin 0 _ VMCountStrictlyPositive))
    end
  end.

Definition parseVMIDs (s : State) (l : list RegName) : list VMID :=
  listFromSome (map (fun x => bind (getReg s (currentVM s) x) wordToVMID) l).

Definition ShareHelper (s : State) (r : RegName) (receivers : list RegName) : Conf * ControlMode :=
  let receivers := parseVMIDs s receivers
  in
  let comp :=
      r' <- getReg s (currentVM s) r ;;;
      addr <- wordToAddr r' ;;;
      pgEntry <- getPageTable s (currentVM s) addr ;;;
      m <- match pgEntry with
           | (Owned, ExclusiveAccess) =>
             match decide (NoDup receivers) with
               | left pr => 
                 newTransaction s (currentVM s) addr Sharing (ListsetNoDup receivers pr)
               | _ => None
             end
           | _ => None
           end ;;;
      m' <- updatePageTable s (currentVM s) addr (Owned, SharedAccess) ;;;
      updateIncrPC m'
  in 
  (simpleOptionStateUnpack s comp, NormalM).

Definition LendHelper (s : State) (r : RegName) (receivers : list RegName) : Conf * ControlMode :=
  let receivers := parseVMIDs s receivers
  in
  let comp :=
      r' <- getReg s (currentVM s) r ;;;
      addr <- wordToAddr r' ;;;
      pgEntry <- getPageTable s (currentVM s) addr ;;;
      m <- match pgEntry with
           | (Owned, ExclusiveAccess) =>
             match decide (NoDup receivers) with
               | left pr => 
                 newTransaction s (currentVM s) addr Lending (ListsetNoDup receivers pr)
               | _ => None
             end
           | _ => None
           end ;;;
      m' <- updatePageTable s (currentVM s) addr (Owned, NoAccess) ;;;
      updateIncrPC m'
  in 
  (simpleOptionStateUnpack s comp, NormalM).

Definition DonateHelper (s : State) (r : RegName) (receiver : RegName) : Conf * ControlMode :=
  let comp :=
      receiver <- getReg s (currentVM s) receiver ;;;
      receiver <- wordToVMID receiver ;;;
      r' <- getReg s (currentVM s) r ;;;
      addr <- wordToAddr r' ;;;
      pgEntry <- getPageTable s (currentVM s) addr ;;;
      m <- match pgEntry with
           | (Owned, ExclusiveAccess) =>
             newTransaction s (currentVM s) addr Donation (listset_nodup_singleton receiver)
           | _ => None
           end ;;;
      m' <- updatePageTable m (currentVM m) addr (NotOwned, NoAccess) ;;;
      updateIncrPC m'
  in 
  (simpleOptionStateUnpack s comp, NormalM).

(* TODO *)
Definition commitTransaction (s : State) (addr : Addr)
           (type : TransactionType)
           (receivers : listset_nodup VMID)
           (received : listset_nodup VMID) : option State :=
  match type with
  | Sharing => None
  | Lending => None
  | Donation => None
  end.

(* TODO *)
Definition revertTransaction (s : State) (addr : Addr)
           (type : TransactionType)
           (receivers : listset_nodup VMID)
           (received : listset_nodup VMID) : option State :=
  match type with
  | Sharing => None
  | Lending => None 
  | Donation => None
  end.

Definition RetrieveHelper (s : State) (r : RegName) : Conf * ControlMode :=
  let comp :=
      handle <- getReg s (currentVM s) r ;;;
      trn <- getTransaction s handle ;;;
      m <- match trn with
           | (addr, type, receivers, received) => commitTransaction s addr type receivers received
           end ;;;
      updateIncrPC m
  in
  (simpleOptionStateUnpack s comp, NormalM).

Definition RelinquishHelper (s : State) (r : RegName) : Conf * ControlMode :=
  let comp :=
      handle <- getReg s (currentVM s) r ;;;
      trn <- getTransaction s handle ;;;
      m <- match trn with
           | (addr, type, receivers, received) => revertTransaction s addr type receivers received
           end ;;;
      updateIncrPC m
  in
  (simpleOptionStateUnpack s comp, NormalM).
  
Definition ReclaimHelper (s : State) (r : RegName) : Conf * ControlMode :=
  let comp :=
      handle <- getReg s (currentVM s) r ;;;
      trn <- getTransaction s handle ;;;
      m <- match trn with
           | (addr, _, receivers, ListsetNoDup [] _) =>
             m' <- ret (removeTransaction s handle) ;;;
             updatePageTable m' (currentVM m') addr (Owned, ExclusiveAccess)
           | _ => None
           end ;;;
      updateIncrPC m
  in
  (simpleOptionStateUnpack s comp, NormalM).

Definition SendHelper (s : State)
           (receiver : RegName) : Conf * ControlMode :=
  let comp :=
      receiver' <- getReg s (currentVM s) receiver ;;;
      receiver'' <- wordToVMID receiver' ;;;
      mb <- vmMailBox s (currentVM s) ;;;
      mem <- getMem s (fst mb) ;;;
      m <- transferMsg s (currentVM s) receiver'' ;;;
      updateIncrPC m
  in
  (simpleOptionStateUnpack s comp, NormalM).

Definition ReceiveHelper (s : State) (dst1 : RegName) (dst2 : RegName) : Conf * ControlMode :=
  let comp :=
      w <- getRXMsg s (currentVM s) ;;;
      v <- getRXSender s (currentVM s) ;;;
      m <- emptyRX s (currentVM s) ;;;
      m' <- updateReg m (currentVM m) dst2 (vmidToWord v) ;;;
      m'' <- updateReg m' (currentVM m') dst1 w ;;;
      m''' <- emptyRX m'' (currentVM m'') ;;;
      updateIncrPC m'''
  in
  (simpleOptionStateUnpack s comp, NormalM).

Definition WaitHelper (s : State) : Conf * ControlMode :=
  match updateIncrPC s with
  | None => (FailI, s, NormalM)
  | Some s' =>
    if isRXReady s (currentVM s)
    then (NextI, s', NormalM)
    else (NextI, s', YieldM (@nat_to_fin 0 _ VMCountStrictlyPositive))
  end.

Definition exec (i : Instruction) (s : State) : Conf * ControlMode :=
  match i with
  | Mov dst (inl srcWord) => MovHelperWord s dst srcWord
  | Mov dst (inr srcReg) => MovHelperReg s dst srcReg
  | Ldr dst src => LdrHelper s dst src
  | Str src dst => StrHelper s src dst
  | Cmp arg1 (inl arg2) => CmpHelperWord s arg1 arg2
  | Cmp arg1 (inr arg2) => CmpHelperReg s arg1 arg2
  | Jnz arg => JnzHelper s arg
  | Jmp arg => JmpHelper s arg
  | Fail => FailHelper s
  | Halt => HaltHelper s
  | Run arg => RunHelper s arg
  | Yield => YieldHelper s
  | Share addr receivers => ShareHelper s addr receivers
  | Lend addr receivers => LendHelper s addr receivers
  | Donate addr receiver => DonateHelper s addr receiver
  | Retrieve handle => RetrieveHelper s handle
  | Relinquish handle => RelinquishHelper s handle
  | Reclaim handle => ReclaimHelper s handle
  | Send receiver => SendHelper s receiver
  | Receive dst1 dst2 => ReceiveHelper s dst1 dst2
  | Wait => WaitHelper s
  end.

Inductive val : Type :=
| NextV
| HaltV
| FailV.

Inductive expr: Type :=
| Instr (c : ExecMode)
| Seq (e : expr).

Definition of_val (v : val) : expr :=
  match v with
  | NextV => Instr NextI
  | HaltV => Instr HaltI
  | FailV => Instr FailI
  end.

Fixpoint to_val (e : expr) : option val :=
  match e with
  | Instr c =>
    match c with
    | ExecI => None
    | HaltI => Some HaltV
    | FailI => Some FailV
    | NextI => Some NextV
    end
  | Seq _ => None
  end.

Lemma of_to_val:
  forall e v, to_val e = Some v ->
              of_val v = e.
Proof.
  intros * HH. destruct e; try destruct c; simpl in HH; inversion HH; auto.
Qed.

Lemma to_of_val:
    forall v, to_val (of_val v) = Some v.
Proof. destruct v; reflexivity. Qed.

Inductive ectx_item :=
| SeqCtx.
Notation ectx := (list ectx_item).

Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
  match Ki with
  | SeqCtx => Seq e
  end.

Lemma fill_item_val Ki e :
    is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
Proof.
  intros [v ?]. destruct Ki; simplify_option_eq; eauto.
Qed.

Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof.
  destruct Ki; intros ???; simplify_eq; auto with f_equal.
Qed.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Proof.
  destruct Ki1, Ki2; intros; try discriminate; simplify_eq;
    repeat match goal with
           | HH : to_val (of_val _) = None |- _ => by rewrite to_of_val in HH
           end; auto.
Qed.
