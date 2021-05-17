From Coq Require Import ssreflect Bool Eqdep_dec Program.Equality.
From stdpp Require Import gmap fin_maps list binders strings countable fin mapset fin_map_dom listset_nodup.
From iris.prelude Require Import options.
From iris.algebra Require Import ofe.
From iris.program_logic Require Import language ectx_language ectxi_language.
From ExtLib Require Import Structures.Monads.
Require Import monad_aux.
Require Import machine_base.

Export monad_notation.
Open Scope monad_scope.

Context `(HypervisorParams : HypervisorParameters).

(* State *)

Definition Mem : Type :=
  gmap Addr Word.

Definition RegFile : Type :=
  gmap RegName Word.

Definition VMID : Type :=
  fin VMCount.

Definition PID : Type :=
  fin PageCount.

Definition PageTable : Type :=
  gmap PID Perm.

Definition TXBuffer : Type :=
  PID.

Definition RXBuffer : Type :=
  (PID * option(VMID)).

Definition MailBox : Type :=
  (TXBuffer * RXBuffer).

Definition CurrentVM := VMID.

Definition VMState : Type :=
  gmap VMID (RegFile * MailBox * PageTable).

Definition Flag : Type :=
  bool.

Definition Transaction : Type :=
  VMID (* sender *) * Word (*flag *) * Word (* tag *) * gmap VMID (gmap PID Flag) * TransactionType.

Definition Handle := Word.

Definition Transactions : Type :=
  gmap Handle Transaction.

Definition State : Type :=
  VMState * CurrentVM * Mem * Transactions.

(* Getters *)

Definition vmStates (st : State) : VMState :=
  fst (fst (fst st)).

Definition currentVM (st : State) : CurrentVM :=
  snd (fst (fst st)).

Definition mem (st : State) : Mem :=
  snd (fst st).

Definition transactions (st : State) : Transactions :=
  snd st.

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

(* Conf *)

Inductive ExecMode : Type :=
| ExecI
| NextI
| HaltI
| FailI.

Inductive ControlMode : Type :=
| YieldM : VMID -> ControlMode
| NormalM.

Definition Conf : Type := ExecMode * State.

(* Aux funcs *)

Definition checkPermPage (st : State) (v : VMID) (pid : PID) (p : Perm) : bool :=
  match (vmPageTable st v) with
  | None => false
  | Some pt =>
    match pt !! pid with
    | Some p' =>
      match (decide (p = p')) with
      | left _ => true
      | right _ => false
      end
    | _ => false
    end
  end.

Definition checkPermAddr (st : State) (v : VMID) (addr : Addr) (p : Perm) : bool :=
  checkPermPage st v (MMTranslation addr) p.

Definition checkAccessPage (st : State) (v : VMID) (pid : PID) : bool :=
  match (vmPageTable st v) with
  | None => false
  | Some pt =>
    match pt !! pid with
    | Some p => isAccessible p
    | _ => false
    end
  end.

Definition checkAccessAddr (st : State) (v : VMID) (addr : Addr) : bool :=
  checkAccessPage st v (MMTranslation addr).

Definition checkOwnershipPage (st : State) (v : VMID) (pid : PID) : bool :=
  match (vmPageTable st v) with
  | None => false
  | Some pt =>
    match pt !! pid with
    | Some p => isOwned p
    | _ => false
    end
  end.

Definition checkOwnershipAddr (st : State) (v : VMID) (addr : Addr) : bool :=
  checkOwnershipPage st v (MMTranslation addr).

Definition updateGeneralRegGlobal (st : State) (v : VMID) (r : RegName) (w : Word) : option State :=
  match r with
  | PC => None
  | NZ => None
  | R n fin =>
    match vmState st v with
    | None => None
    | Some (rf, mb, pt) =>
      Some (<[v:=(<[r:=w]>rf, mb, pt)]>(vmStates st),
            currentVM st,
            mem st, transactions st)
    end
  end.

Definition updateGeneralReg (st : State) (r : RegName) (w : Word) : option State :=
  updateGeneralRegGlobal st (currentVM st) r w.

Definition updateSysRegGlobal (st : State) (v : VMID) (r : RegName) (w : Word) : option State :=
  match r with
  | R n fin => None
  | _ => match vmState st v with
         | None => None
         | Some (rf, mb, pt) =>
           Some (<[v:=(<[r:=w]>rf, mb, pt)]>(vmStates st),
                 currentVM st,
                 mem st, transactions st)
         end
  end.

Definition updateSysReg (st : State) (r : RegName) (w : Word) : option State :=
  updateSysRegGlobal st (currentVM st) r w.

Definition getRegGlobal (st : State) (v : VMID) (r : RegName) : option Word :=
  match vmRegFile st v with
  | None => None
  | Some rf => rf !! r 
  end.

Definition getReg (st : State) (r : RegName) : option Word :=
  getRegGlobal st (currentVM st) r.

Definition updatePageTableGlobal (st : State) (v : VMID) (pid : PID) (p : Perm) : option State :=
  match vmState st v with
  | None => None
  | Some (rf, mb, pt) =>
    Some (<[v:=(rf, mb, <[pid:=p]>pt)]>(vmStates st),
          currentVM st,
          mem st, transactions st)
  end.

Definition updatePageTable (st : State) (pid : PID) (p : Perm) : option State :=
  updatePageTableGlobal st (currentVM st) pid p.

Definition getPageTableGlobal (st : State) (v : VMID) (pid : PID) : option Perm :=
  match vmPageTable st v with
  | None => None
  | Some pt => pt !! pid
  end.

Definition getPageTable (st : State) (pid : PID) : option Perm :=
  getPageTableGlobal st (currentVM st) pid.
                
Definition updateMemUnsafe (st : State) (a : Addr) (w : Word) : State :=
  (vmStates st, currentVM st, <[a:=w]>(mem st), transactions st).

Definition updateMem (st : State) (a : Addr) (w : Word) : option State :=
  if checkAccessAddr st (currentVM st) a
  then ret (updateMemUnsafe st a w)
  else None.

Definition getMemUnsafe (st : State) (a : Addr) : option Word :=
  (mem st) !! a.

Definition getMem (st : State) (a : Addr) : option Word :=
  if checkAccessAddr st (currentVM st) a
  then getMemUnsafe st a
  else None.
(* 
Definition writeTXUnsafe (st : State) (v : VMID) (msg : vec Word PageCount) : option State :=
  match vmState st v with
  | None => None
  | Some (rf, (txPid, _), pt) => ret (updateMemUnsafe st txAddr msg)
  end.

Definition writeTX (st : State) (v : VMID) (msg : Word) : option State :=
    match vmState st v with
  | None => None
  | Some (rf, (txAddr, _), pt) => updateMem st txAddr msg
  end.
 *)
Lemma atLeastOneAddrInPage (pid : PID) : vec Word (S (PageSize - 1)).
Proof.
  pose proof PageSizeSanity as H.
  pose proof WordSizeAtLeast as H'.
  pose proof (MMTranslationInv pid) as H''.
  destruct PageSize.
  - simpl in H. 
    unfold WordSizeLowerBound in H'.
    rewrite <- H in H'.
    exfalso.
    apply (Nat.nlt_0_r 15 H').
  - simpl in *.
    rewrite <- minus_n_O.
    exact H''.
Qed.

Definition getTXBaseAddrGlobal (st : State) (v : VMID) : option Word :=
  match vmState st v with
  | Some (rf, (pid, _), pt) =>
    Some (@Vector.hd Word (PageSize - 1) (atLeastOneAddrInPage pid))
  | _ => None
  end.

Definition isRXReadyGlobal (st : State) (v : VMID) : bool :=
  match vmState st v with
  | Some (rf, (_, (_, Some _)), pt) => true
  | _ => false
  end.

Definition isRXReady (st : State) : bool :=
  isRXReadyGlobal st (currentVM st).

Definition getRXSenderGlobal (st : State) (v : VMID) : option VMID :=
  match vmState st v with
  | Some (rf, (_, (_, Some v')), pt) => Some v'
  | _ => None
  end.

Definition getRXSender (st : State) : option VMID :=
  getRXSenderGlobal st (currentVM st).

Program Definition getRXBaseAddrGlobal (st : State) (v : VMID) : option Word :=
  match vmState st v with
  | Some (rf, (_, (pid, Some _)), pt) => Some (@Vector.hd Word (PageSize - 1) (atLeastOneAddrInPage pid))
  | _ => None
  end.

(*
Definition getRXMsg (st : State) : option Word :=
  match vmState st (currentVM st) with
  | Some (rf, (_, (addr, Some _)), pt) => getMem st addr
  | _ => None
  end.
 *)

Definition emptyRXGlobal (st : State) (v : VMID) : option State :=
  match vmState st v with
  | Some (rf, (txAddr, (rxAddr, Some _)), pt) =>
    Some (<[v:=(rf, (txAddr, (rxAddr, None)), pt)]>(vmStates st),
          currentVM st,
          mem st, transactions st)
  | _ => None
  end.
Definition emptyRX (st : State) : option State :=
  emptyRXGlobal st (currentVM st).

Definition copyFromAddrToAddrUnsafe (st : State) (src dst : Addr) : option State :=
  w <- getMemUnsafe st src ;;;
  Some (updateMemUnsafe st dst w).

Definition copyPageUnsafe (st : State) (src dst : PID) : option State :=
  let src' := MMTranslationInv src
  in
  let dst' := MMTranslationInv dst
  in
  let H := vzip_with (fun x y => (x, y)) src' dst'
  in
  monad_general.foldrMVec (fun x s => match x with | (a, b) => copyFromAddrToAddrUnsafe s a b end) H st.

Definition transferMsgUnsafe (st : State) (v : VMID) (r : VMID) : option State :=
  match vmState st v with
  | Some (_, (txPid, _), _) =>
    match vmState st r with
    | Some (rf, (_, (rxPid, _)), pt) =>
      copyPageUnsafe st txPid rxPid
    | _ => None
    end
  | _ => None
  end.

Definition tryIncrWord (n : Word) (p : nat) : option Word :=
  match (nat_lt_dec (n + p) WordSize) with
  | left l => Some (@nat_to_fin (n + p) _ l)
  | _ => None
  end.

Lemma finMax {n : nat} (x y : fin n) : fin n.
Proof.
  destruct (Fin.to_nat x);
    destruct (Fin.to_nat y);
    destruct (x <? y); auto.
Defined.

Definition freshHandleHelper (val : Handle) (acc : option Handle) : option Handle :=
  match (tryIncrWord val 1) with
  | None => None
  | Some val' => match acc with
                 | None => Some val'
                 | Some acc' => Some (finMax val' acc')
                 end
  end.

Definition freshHandle (m : gmap Handle Transaction) : option Handle := 
  set_fold freshHandleHelper None (@dom (gmap Handle Transaction) (gset Handle) gset_dom m).

Definition MemoryRegionDescriptor : Type :=
  Word (* length *) * VMID (* receiver *) * list PID (* pids *).  

(*
Instance proofIrrelNoDup {A : Type} {l : list A} `{EqDecision A} : ProofIrrel (NoDup l).
Proof.
  assert (forall x (p : NoDup x) y (q : NoDup y),
    x = y -> eq_dep (list A) NoDup x p y q) as aux.
  {
    fix FIX 4. intros x p y q eq.
    destruct p.
    - subst; dependent destruction q; reflexivity.
    - subst; dependent destruction q.
      Check In.
      pose proof (FIX l0 p l0 q eq_refl).
      admit.
  }
  intros p q;
    apply (Eqdep_dec.eq_dep_eq_dec (fun x y => decide (x = y)));
    apply aux; reflexivity.
  Admitted.
  
Instance eqDecisionListsetNoDup {A : Type} `{EqDecision A} : EqDecision (listset_nodup A).
Proof.
  intros [x prfx] [y prfy].
  destruct (decide (x = y)).
  - subst; left.
    pose proof (proof_irrel prfx prfy).
    rewrite H.
    reflexivity.
  - right.
    intros contra.
    inversion contra.
    contradiction.
Qed.

Instance eqDecisionMemoryRegionDescriptor : EqDecision MemoryRegionDescriptor.
Proof.
  intros [[w v] [ls prf]] [[w' v'] [ls' prf']]; try (by left); try (by right).
  destruct (decide (w = w'));
    destruct (decide (v = v'));
    destruct (decide (ls = ls'));
    try (right; congruence); subst.
  rewrite (proof_irrel prf prf').
  left.
  reflexivity.
Qed.
*)

Definition TransactionDescriptor : Type :=
  VMID (* Sender *) * option Handle (* Handle *) * Word (* Tag *)
  * Word (* Flag *)
  * gmap VMID (listset_nodup PID) (* Receivers *).

Definition memoryRegionsToGmap (md : listset_nodup MemoryRegionDescriptor) : gmap VMID (listset_nodup PID) :=
  set_fold (fun v acc => match decide (NoDup (snd v)) with
                         | left l => map_insert (snd (fst v)) (ListsetNoDup v.2 l) acc
                         | right r => acc
                         end) empty md.

Definition addrOffset (base : Addr) (offset : nat) : option Addr :=
  tryIncrWord base offset.

Definition getMemWithOffset (st : State) (base : Addr) (offset : nat) : option Word :=
  addr <- addrOffset base offset ;;;
  getMem st addr.

Definition parseMemoryRegionDescriptor (st : State) (base : Addr) : option MemoryRegionDescriptor :=
  match getMemWithOffset st base 0 with
  | None => None
  | Some l =>
    match getMemWithOffset st base 1 with
    | None => None
    | Some r =>
      match DecodeVMID r with
      | None => None
      | Some r' =>
        let ls := foldl (fun acc v => cons (bind (getMemWithOffset st base (2 + v)) DecodePID) acc) nil (seq 0 (fin_to_nat l))
        in
        match (monad_general.sequenceMList ls) with
        | None => None
        | Some ls' => ret (l, r', ls')
        end
      end
    end
  end.

Definition parseMemoryRegionDescriptors (st : State) (base : Addr) (count : nat) : option (listset_nodup MemoryRegionDescriptor) :=
  let ls := (foldl (fun acc v =>
                     cons (bind (addrOffset base v) (parseMemoryRegionDescriptor st)) acc) (@nil (option MemoryRegionDescriptor)) (seq 0 count))
  in
  match monad_general.sequenceMList ls with
  | None => None
  | Some ls' =>
    match NoDup_dec ls' with
    | left prf => ret (ListsetNoDup ls' prf)
    | right prf => None
    end
  end.

(* TODO: Prop version, reflection *)
Definition parseTransactionDescriptor (st : State) (wl : Word) (base : Addr) (ty : TransactionType) : option TransactionDescriptor :=
  (* Main fields *)
  vs <- getMemWithOffset st base 0 ;;;
  vs' <- DecodeVMID vs ;;;
  wf <- getMemWithOffset st base 1 ;;;
  wh <- getMemWithOffset st base 2 ;;;
  wt <- getMemWithOffset st base 3 ;;;
  wc <- getMemWithOffset st base 4 ;;;
  memDescrBase <- addrOffset base 5 ;;;
  memDescrs <- parseMemoryRegionDescriptors st memDescrBase (fin_to_nat wc) ;;;
  (* Validate length *)                                          
  _ <- addrOffset base (fin_to_nat wl) ;;;
  _ <- @monad_option.boolCheckOption True (negb (fin_to_nat wc =? 0)) ;;;
  _ <- @monad_option.boolCheckOption True (fin_to_nat wl =? 5 + 3 * (fin_to_nat wc) + (set_fold (fun v acc => length (snd v) + acc) 0 memDescrs)) ;;;
  _ <- @monad_option.boolCheckOption True (match ty with
                                     | Donation => (fin_to_nat wc) =? 1
                                     | _ => true
                                     end) ;;;
  ret (vs', (if (fin_to_nat wh) =? 0 then None else Some wh), wt, wf, memoryRegionsToGmap memDescrs).
                                                           
Definition insertTransaction (st : State) (h : Handle) (t : Transaction) : State :=
  (vmStates st, currentVM st, mem st, <[h:=t]>(transactions st)).

Definition newTransaction (st : State) (vid : VMID)
           (tt : TransactionType)
           (flag tag : Word)
           (m : gmap VMID (gmap PID Flag))  : option State :=
  if map_fold (fun _ v acc => andb acc (set_fold (fun v' acc' => andb acc' (checkOwnershipPage st vid v')) true (@dom (gmap PID Flag) (gset PID) gset_dom v))) true m
  then
    match freshHandle (transactions st) with
    | None => None
    | Some h' =>
      ret (insertTransaction st h' (vid, flag, tag, m, tt))
    end
  else None.

Definition getTransaction (st : State) (h : Handle) : option Transaction :=
  (transactions st) !! h.

Definition removeTransaction (s : State) (handle : Handle) : State :=
  (vmStates s, currentVM s, mem s, delete handle (transactions s)).

Definition newTransactionFromDescriptor (st : State) (ty : TransactionType) (td : TransactionDescriptor) : option State :=
  match td with
  | (s, None, t, f, rs) => newTransaction st s ty f t (fmap (fun x => set_to_map (fun el => (el, false)) x) rs)
  | _ => None
  end.

Definition newTransactionFromDescriptorInTXUnsafe (st : State) (v : VMID) (wl : Word) (ty : TransactionType) : option State :=
  if (PageSize <? fin_to_nat wl)
  then None
  else
    txBAddr <- getTXBaseAddrGlobal st v ;;;
    td <- parseTransactionDescriptor st wl txBAddr ty ;;;
    newTransactionFromDescriptor st ty td.

Definition updateOffsetPC (st : State) (dir : bool) (offset : nat) : option State :=
  bind
    (vmRegFile st (currentVM st))
    (fun rf =>
       bind (rf !! PC)
            (fun v =>
               let v' := fin_to_nat v in
               if dir
               then
                 match (nat_lt_dec (v' + offset) WordSize) with
                 | left l => updateSysReg st PC (@nat_to_fin (v' + offset) _ l)
                 | _ => None
                 end
               else
                 match (nat_lt_dec (v' - offset) WordSize) with
                 | left l => updateSysReg st PC (@nat_to_fin (v' - offset) _ l)
                 | _ => None
                 end
    )).

Definition updateIncrPC (st : State) : option State :=
  updateOffsetPC st true 2.

Definition updateCurrentVMID (st : State) (v : VMID) : State :=
  (vmStates st, v, mem st, transactions st).

Definition isPrimary (st : State) : bool :=
  (currentVM st) =? 0.

Definition isSecondary (st : State) : bool :=
  negb (isPrimary st).

Definition isValidPC (st : State) : option bool :=
  w <- getReg st PC ;;;
  w' <- addrOffset w 1 ;;;
  Some (andb (checkAccessAddr st (currentVM st) w) (checkAccessAddr st (currentVM st) w')).

Definition simpleOptionStateUnpack (oldSt : State) (newSt : option State) : Conf :=
  match newSt with
  | None => (FailI, oldSt)
  | Some s => (NextI, s)
  end.

Definition MovHelperWord (s : State) (dst : RegName) (src : Word) : Conf * ControlMode :=
  let comp :=
        s' <- updateGeneralReg s dst src ;;;
        updateIncrPC s'
    in
    (simpleOptionStateUnpack s comp, NormalM).

Definition MovHelperReg (s : State) (dst : RegName) (src : RegName) : Conf * ControlMode :=
  let comp :=
      src' <- getReg s src ;;;
      s'' <- updateGeneralReg s dst src' ;;;
      updateIncrPC s''
    in
  (simpleOptionStateUnpack s comp, NormalM).

Definition LdrHelper (s : State) (dst : RegName) (src : RegName) : Conf * ControlMode :=
  let comp :=
      src' <- getReg s src ;;;
      v <- getMem s src' ;;;
      m <- updateGeneralReg s dst v ;;;
      updateIncrPC m
  in
  (simpleOptionStateUnpack s comp, NormalM).

Definition StrHelper (s : State) (src : RegName) (dst : RegName) : Conf * ControlMode :=
  let comp :=
      src' <- getReg s src ;;;
      dst' <- getReg s dst ;;;
      m <- updateMem s dst' src' ;;;
      updateIncrPC m
  in
  (simpleOptionStateUnpack s comp, NormalM).

Program Definition CmpHelperWord (s : State) (arg1 : RegName) (arg2 : Word) : Conf * ControlMode :=
  let comp :=
      arg1' <- getReg s arg1 ;;;
      m <- match (nat_lt_dec (fin_to_nat arg1') (fin_to_nat arg2)) with
           | left _ => updateSysReg s NZ (@nat_to_fin 1 WordSize _)
           | right _ => updateSysReg s NZ (@nat_to_fin 0 WordSize _)
           end ;;;
      updateIncrPC m       
  in
  (simpleOptionStateUnpack s comp, NormalM).
Next Obligation.
  pose proof WordSizeAtLeast as G.
  unfold WordSizeLowerBound in G.
  lia.
Qed.
Next Obligation.
  pose proof WordSizeAtLeast as G.
  unfold WordSizeLowerBound in G.
  lia.
Qed.

Program Definition CmpHelperReg (s : State) (arg1 : RegName) (arg2 : RegName) : Conf * ControlMode :=
  let comp :=
      arg1' <- getReg s arg1 ;;;
      arg2' <- getReg s arg2 ;;;
      m <- match (nat_lt_dec (fin_to_nat arg1') (fin_to_nat arg2')) with
           | left _ => updateSysReg s NZ (@nat_to_fin 1 WordSize _)
           | right _ => updateSysReg s NZ (@nat_to_fin 0 WordSize _)
           end ;;;
      updateIncrPC m
  in
  (simpleOptionStateUnpack s comp, NormalM).
Next Obligation.
  pose proof WordSizeAtLeast as G.
  unfold WordSizeLowerBound in G.
  lia.
Qed.
Next Obligation.
  pose proof WordSizeAtLeast as G.
  unfold WordSizeLowerBound in G.
  lia.
Qed.

Definition JnzHelper (s : State) (arg : RegName) : Conf * ControlMode :=
  let comp :=
      arg' <- getReg s arg ;;;
      nz <- getReg s NZ ;;;
      match (fin_to_nat nz) with
      | 0 => updateSysReg s PC arg'
      | _ => updateIncrPC s
      end
  in
  (simpleOptionStateUnpack s comp, NormalM).

Definition JmpHelper (s : State) (arg : RegName) : Conf * ControlMode :=
  let comp :=
      arg' <- getReg s arg ;;;
      updateSysReg s PC arg'
  in
  (simpleOptionStateUnpack s comp, NormalM).

Definition FailHelper (s : State) : Conf * ControlMode :=
  (FailI, s, NormalM).

Definition HaltHelper (s : State) : Conf * ControlMode :=
  (HaltI, s, NormalM).

Program Definition RunHelper (s : State) : Conf * ControlMode :=
  match getReg s  (R 1 _) with
  | None => (FailI, s, NormalM)
  | Some id =>
    match updateIncrPC s with
    | None => (FailI, s, NormalM)
    | Some s' =>
      match DecodeVMID id with
      | None => (FailI, s, NormalM)
      | Some id' => (NextI, s', YieldM id')
      end
    end
  end.
Next Obligation.
  pose proof RegCountAtLeast as G.
  unfold RegCountLowerBound in G.
  lia.
Qed.

Definition YieldHelper (s : State) : Conf * ControlMode :=
  match updateIncrPC s with
  | None => (FailI, s, NormalM)
  | Some s' => (NextI, s', YieldM (@nat_to_fin 0 VMCount VMCountPos))
  end.

Definition verifyPermTransaction (s : State) (p : Perm) (td : TransactionDescriptor) : bool :=
  match td with
  | (_, _, _, _, m) => map_fold
                         (fun _ v acc => andb acc (set_fold (fun v' acc' => andb acc' (checkPermPage s (currentVM s) v' p)) true v))
                         true
                         m
  end.

Program Definition ShareHelper (s : State) : Conf * ControlMode :=
    let comp :=
        r <- getReg s (R 1 _) ;;;
        m <- (if (PageSize <? fin_to_nat r)
              then None
              else
                txBAddr <- getTXBaseAddrGlobal s (currentVM s) ;;;
                td <- parseTransactionDescriptor s r txBAddr Sharing ;;;
                if (verifyPermTransaction s (Owned, ExclusiveAccess) td)
                then bind (newTransactionFromDescriptor s Sharing td) (fun x => Some (x, td))
                else None) ;;;
        match m with
        | (m', td) => _
        end
    in 
    (simpleOptionStateUnpack s comp, NormalM).
Next Obligation.
  pose proof RegCountAtLeast as G.
  unfold RegCountLowerBound in G.
  lia.
Defined.
Next Obligation.
  intros.
  destruct td.
  pose proof (map_fold (fun _ v acc => union v acc) empty g) as G.
  destruct G as [ls prf].
  exact (monad_general.foldrMList (fun v' acc' => updatePageTable acc' v' (Owned, SharedAccess)) ls m').
Defined.

Program Definition LendHelper (s : State) : Conf * ControlMode :=
  let comp :=
      r <- getReg s (R 1 _) ;;;
      m <- (if (PageSize <? fin_to_nat r)
            then None
            else
              txBAddr <- getTXBaseAddrGlobal s (currentVM s) ;;;
              td <- parseTransactionDescriptor s r txBAddr Lending ;;;
              if (verifyPermTransaction s (Owned, ExclusiveAccess) td)
              then bind (newTransactionFromDescriptor s Lending td) (fun x => Some (x, td))
              else None) ;;;
      match m with
      | (m', td) => _
      end
  in 
  (simpleOptionStateUnpack s comp, NormalM).
Next Obligation.
  pose proof RegCountAtLeast as G.
  unfold RegCountLowerBound in G.
  lia.
Defined.
Next Obligation.
  intros.
  destruct td.
  pose proof (map_fold (fun _ v acc => union v acc) empty g) as G.
  destruct G as [ls prf].
  exact (monad_general.foldrMList (fun v' acc' => updatePageTable acc' v' (Owned, NoAccess)) ls m').
Defined.

Program Definition DonateHelper (s : State) : Conf * ControlMode :=
  let comp :=
      r <- getReg s (R 1 _) ;;;
      m <- (if (PageSize <? fin_to_nat r)
            then None
            else
              txBAddr <- getTXBaseAddrGlobal s (currentVM s) ;;;
              td <- parseTransactionDescriptor s r txBAddr Donation ;;;
              if (verifyPermTransaction s (Owned, ExclusiveAccess) td)
              then bind (newTransactionFromDescriptor s Donation td) (fun x => Some (x, td))
              else None) ;;;
      match m with
      | (m', td) => _
      end
  in 
  (simpleOptionStateUnpack s comp, NormalM).
Next Obligation.
  pose proof RegCountAtLeast as G.
  unfold RegCountLowerBound in G.
  lia.
Defined.
Next Obligation.
  intros.
  destruct td.
  pose proof (map_fold (fun _ v acc => union v acc) empty g) as G.
  destruct G as [ls prf].
  exact (monad_general.foldrMList (fun v' acc' => updatePageTable acc' v' (NotOwned, NoAccess)) ls m').
Defined.

Definition toggleTransactionEntry (s : State) (h : Handle) (v : VMID) (p : PID) : State :=
  (vmStates s, currentVM s, mem s,
   alter (fun x => match x with
                   | (vs, w1, w2, gm, ty) => (vs, w1, w2, alter (fun y => alter (fun z => negb z) p y) v gm, ty)
                   end) h (transactions s)).

Program Definition toggleTransactionEntries (s : State) (h : Handle) (v : VMID) : State.
Proof.
  intros.
  destruct ((transactions s) !! h) as [[[? t] ?] |].
  - destruct (t !! v) as [g |].
    + exact (map_fold (fun k _ acc => toggleTransactionEntry acc h v k) s g).
    + exact s.
  - exact s.
Defined.

Definition getPIDs (s : State) (handle : Handle) : list PID :=
  match (transactions s) !! handle with
  | None => nil
  | Some (_, _, _, m, _) =>
    match m !! (currentVM s) with
    | None => nil
    | Some m' => map (fun x => match x with | (y, _) => y end) (map_to_list m')
    end
  end.

Definition retrieveTransaction (s : State)
           (handle : Handle)
           (type : TransactionType)
           (receiversMap : gmap VMID (gmap PID Flag)) : option State :=
  match type with
  | Sharing =>
    let m := toggleTransactionEntries s handle (currentVM s)
    in (monad_general.foldrMList (fun v' acc' => updatePageTable acc' v' (NotOwned, SharedAccess)) (getPIDs s handle) m)
  | Lending =>
    let m := toggleTransactionEntries s handle (currentVM s)
    in if decide (1 < size receiversMap)
       then (monad_general.foldrMList (fun v' acc' => updatePageTable acc' v' (NotOwned, SharedAccess)) (getPIDs s handle) m)
       else (monad_general.foldrMList (fun v' acc' => updatePageTable acc' v' (NotOwned, ExclusiveAccess)) (getPIDs s handle) m)
  | Donation =>
    let m := toggleTransactionEntries s handle (currentVM s)
    in (monad_general.foldrMList (fun v' acc' => updatePageTable acc' v' (Owned, ExclusiveAccess)) (getPIDs s handle) m)
  end.

Definition relinquishTransaction (s : State)
           (handle : Handle) : option State :=
  let m := toggleTransactionEntries s handle (currentVM s)
  in (monad_general.foldrMList (fun v' acc' => updatePageTable acc' v' (NotOwned, NoAccess)) (getPIDs s handle) m).

Definition receivers (t : Transaction) : gmap VMID (gmap PID Flag) :=
  match t with
  | (_, _, _, m, _) => m
  end.

Definition type (t : Transaction) : TransactionType :=
  match t with
  | (_, _, _, _, ty) => ty
  end.

Program Definition RetrieveHelper (s : State) : Conf * ControlMode :=
  let comp :=
      handle <- getReg s (R 1 _) ;;;
      trn <- getTransaction s handle ;;;
      m <- retrieveTransaction s handle (type trn) (receivers trn) ;;;
      updateIncrPC m
  in
  (simpleOptionStateUnpack s comp, NormalM).
Next Obligation.
  pose proof RegCountAtLeast as G.
  unfold RegCountLowerBound in G.
  lia.
Defined.

Program Definition RelinquishHelper (s : State) : Conf * ControlMode :=
  let comp :=
      handle <- getReg s (R 1 _) ;;;
      m <- relinquishTransaction s handle ;;;
      updateIncrPC m
  in
  (simpleOptionStateUnpack s comp, NormalM).
Next Obligation.
  pose proof RegCountAtLeast as G.
  unfold RegCountLowerBound in G.
  lia.
Defined.

Definition allNotReceived (s : State) (handle : Handle) (v : VMID) : bool :=
  match (transactions s) !! handle with
  | None => true
  | Some (_, _, _, m, _) =>
    match m !! v with
    | None => true
    | Some m' => map_fold (fun _ v acc => andb v acc) true m'
    end
  end.

Program Definition ReclaimHelper (s : State) : Conf * ControlMode :=
  let comp :=
      handle <- getReg s (R 1 _) ;;;
      m <- (if allNotReceived s handle (currentVM s)
            then
              (monad_general.foldrMList
                 (fun v' acc' => updatePageTable acc' v' (Owned, ExclusiveAccess))
                 (getPIDs s handle) (removeTransaction s handle))
            else None) ;;;
      updateIncrPC m
  in
  (simpleOptionStateUnpack s comp, NormalM).
Next Obligation.
  pose proof RegCountAtLeast as G.
  unfold RegCountLowerBound in G.
  lia.
Defined.

Program Definition SendHelper (s : State) : Conf * ControlMode :=
  let comp :=
      receiver <- getReg s (R 1 _) ;;;
      receiver' <- DecodeVMID receiver ;;;
      m <- transferMsgUnsafe s (currentVM s) receiver' ;;;
      updateIncrPC m
  in
  (simpleOptionStateUnpack s comp, NormalM).
Next Obligation.
  pose proof RegCountAtLeast as G.
  unfold RegCountLowerBound in G.
  lia.
Defined.

Definition WaitHelper (s : State) : Conf * ControlMode :=
  match updateIncrPC s with
  | None => (FailI, s, NormalM)
  | Some s' =>
    if isRXReady s
    then (NextI, s', NormalM)
    else (NextI, s', YieldM (@nat_to_fin 0 _ VMCountPos))
  end.

Program Definition HvcHelper (s : State) : Conf * ControlMode :=
  match getReg s (R 0 _) with
  | None => FailHelper s
  | Some r0 =>
    match DecodeHvcFunc r0 with
    | None => FailHelper s
    | Some func =>
      match func with
      | Run => RunHelper s
      | Yield => YieldHelper s
      | Share => ShareHelper s
      | Lend => LendHelper s
      | Donate => DonateHelper s
      | Retrieve => RetrieveHelper s
      | Relinquish => RelinquishHelper s
      | Reclaim => ReclaimHelper s
      | Send => SendHelper s
      | Wait => WaitHelper s
      end
    end
  end.
Next Obligation.
  pose proof RegCountAtLeast as G.
  unfold RegCountLowerBound in G.
  lia.
Qed.

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
  | Hvc => HvcHelper s
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
  intros * HH; destruct e; try destruct c; simpl in HH; inversion HH; auto.
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

Inductive step : Conf -> Conf * ControlMode -> Prop :=
| step_exec_fail:
    forall st,
      not (isValidPC st = Some true) ->
      step (ExecI, st) (FailI, st, NormalM)
| step_exec_instr:
    forall st a w1 w2 i c,
      isValidPC st = Some true ->
      getReg st PC = Some a ->
      getMem st a = Some w1 ->
      getMemWithOffset st a 1 = Some w2 ->
      DecodeInstr (w1, w2) = Some i ->
      exec i st = c ->
      step (ExecI, st) c.

Inductive prim_step : expr -> State -> list Empty_set -> expr -> State -> list Empty_set -> ControlMode -> Prop :=
| PS_instr_normal st e' st' :
    step (ExecI, st) (e', st', NormalM) -> prim_step (Instr ExecI) st [] (Instr e') st' [] NormalM
| PS_instr_yield st e' st' i :
    step (ExecI, st) (e', st', YieldM i) -> prim_step (Instr ExecI) st [] (Instr e') (updateCurrentVMID st' i) [] NormalM
| PS_seq st : prim_step (Seq (Instr NextI)) st [] (Seq (Instr ExecI)) st [] NormalM
| PS_halt st : prim_step (Seq (Instr HaltI)) st [] (Instr HaltI) st [] NormalM
| PS__fail st : prim_step (Seq (Instr FailI)) st [] (Instr FailI) st [] NormalM.

(*
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
*)
