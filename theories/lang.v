From stdpp Require Import gmap fin_maps list countable fin mapset fin_map_dom listset_nodup vector.
From HypVeri Require Export machine monad reg_addr.

Import MonadNotation.
Import Option.
Import Sum.
Open Scope monad_scope.

Context `{HyperConst : !HypervisorConstants}.
Context `{HyperParams : !HypervisorParameters}.
(* State *)

Definition mem : Type :=
  gmap Addr Word.

Definition reg_file : Type :=
  gmap reg_name Word.

Definition page_table : Type :=
  gmap PID permission.

Definition tx_buffer : Type :=
  PID.

Definition rx_buffer : Type :=
  (PID * option(Word * VMID)).

Definition mail_box : Type :=
  (tx_buffer * rx_buffer).

Definition transaction : Type :=
  VMID (* sender *)
  * Word (*flag *)
  * Word (* tag *)
  * gset VMID
  * gmap VMID (gset PID)
  * transaction_type.

Definition handle := Word.


Definition hpool := gset handle.

Definition transactions : Type :=
  gmap handle transaction  * hpool.


Definition state : Type :=
  vec reg_file vm_count * vec mail_box vm_count * vec page_table vm_count * VMID * mem * transactions.

(* Getters *)

Definition get_current_vm (st : state) : VMID :=
  snd (fst (fst st)).

Definition get_mem (st : state) : mem :=
  snd (fst st).

Definition get_transactions (st : state) : transactions :=
  snd st.

Definition get_reg_files (st : state) : vec reg_file vm_count :=
  fst (fst (fst (fst (fst st)))).

Definition get_vm_reg_file (st : state) (v : VMID) : reg_file :=
  (get_reg_files st) !!! v.

Definition get_mail_boxes (st : state) : vec mail_box vm_count :=
  snd (fst (fst (fst (fst st)))).

Definition get_vm_mail_box (st : state) (v : VMID) : mail_box :=
  (get_mail_boxes st) !!! v.

Definition get_page_tables (st : state) : vec page_table vm_count :=
  snd (fst (fst (fst st))).

Definition get_vm_page_table (st : state) (v : VMID) : page_table :=
  (get_page_tables st) !!! v.

(* Conf *)

Inductive exec_mode : Type :=
| ExecI
| HaltI
| FailI
| FailPageFaultI.

(* Aux funcs *)

Definition check_perm_page (st : state) (v : VMID) (p : PID) (pm : permission) : bool :=
  match (get_vm_page_table st v) !! p with
  | Some p' =>
    match (decide (pm = p')) with
    | left _ => true
    | right _ => false
    end
  | _ => false
  end.

Definition check_perm_addr (st : state) (v : VMID) (a : Addr) (p : permission) : bool :=
  check_perm_page st v (to_pid_aligned a) p.

Definition check_access_page (st : state) (v : VMID) (p : PID) : bool :=
  match (get_vm_page_table st v) !! p with
  | Some p' => is_accessible p'
  | _ => false
  end.

Definition check_access_addr (st : state) (v : VMID) (a : Addr) : bool :=
  check_access_page st v (to_pid_aligned a).

Definition check_ownership_page (st : state) (v : VMID) (p : PID) : bool :=
  match (get_vm_page_table st v) !! p with
  | Some p' => is_owned p'
  | _ => false
  end.

Definition check_ownership_addr (st : state) (v : VMID) (a : Addr) : bool :=
  check_ownership_page st v (to_pid_aligned a).

Definition update_reg_global (st : state) (v : VMID) (r : reg_name) (w : Word) : state :=
  (vinsert v (<[r:=w]>(get_vm_reg_file st v)) (get_reg_files st), (get_mail_boxes st), (get_page_tables st),
   get_current_vm st,
   get_mem st, get_transactions st).

Definition update_reg (st : state) (r : reg_name) (w : Word) : state :=
  update_reg_global st (get_current_vm st) r w.

Definition get_reg_global (st : state) (v : VMID) (r : reg_name) : option Word :=
  (get_vm_reg_file st v) !! r.

Definition get_reg (st : state) (r : reg_name) : option Word :=
  get_reg_global st (get_current_vm st) r.

Definition update_page_table_global (st : state) (v : VMID) (p : PID) (pm : permission) : state :=
  (get_reg_files st, get_mail_boxes st, vinsert v (<[p:=pm]>(get_vm_page_table st v)) (get_page_tables st),
   get_current_vm st,
   get_mem st, get_transactions st).

Definition update_page_table (st : state) (p : PID) (pm : permission) : state :=
  update_page_table_global st (get_current_vm st) p pm.

Definition get_page_table_global (st : state) (v : VMID) (p : PID) : option permission :=
  (get_vm_page_table st v) !! p.

Definition get_page_table (st : state) (p : PID) : option permission :=
  get_page_table_global st (get_current_vm st) p.
                
Definition update_memory_unsafe (st : state) (a : Addr) (w : Word) : state :=
  (get_reg_files st, get_mail_boxes st, get_page_tables st, get_current_vm st, <[a:=w]>(get_mem st), get_transactions st).

Definition get_memory_unsafe (st : state) (a : Addr) : option Word :=
  (get_mem st) !! a.

Program Definition update_offset_PC (st : state) (offset : Z) :  state :=
  match ((get_vm_reg_file st (get_current_vm st)) !! PC) with
   | Some v => (update_reg st PC (v ^+ offset)%f)
   | None => st
   end.

Definition update_incr_PC (st : state) : state :=
  update_offset_PC st 1.

Definition is_valid_PC (st : state) : option bool :=
  w <- get_reg st PC ;;;
  Some (check_access_addr st (get_current_vm st) w).

Definition option_state_unpack (oldSt : state) (newSt : option state) : exec_mode * state :=
  match newSt with
  | None => (FailI, oldSt)
  | Some s => (ExecI, s)
  end.

Definition mov_word (s : state) (dst : reg_name) (src : Word) : exec_mode * state :=
  let comp :=
      match dst with
      | PC => None
      | NZ => None
      | _ => Some (update_incr_PC (update_reg s dst src))
      end
    in
    (option_state_unpack s comp).

Definition mov_reg (s : state) (dst : reg_name) (src : reg_name) : exec_mode * state :=
  let comp :=
      match (dst, src) with
      | (R _ _, R _ _) =>
        src' <- get_reg s src ;;;
                Some (update_incr_PC (update_reg s dst src'))
      | _ => None
      end
    in
  (option_state_unpack s comp).

Definition update_memory (st : state) (a : Addr) (w : Word) : exec_mode * state :=
  if check_access_addr st (get_current_vm st) a
  then (ExecI, update_memory_unsafe st a w)
  else (FailPageFaultI, st).

Definition get_memory (st : state) (a : Addr) : option Word :=
  if check_access_addr st (get_current_vm st) a
  then get_memory_unsafe st a
  else None.

Definition get_memory_with_offset (st : state) (base : Addr) (offset : Z) : option Word :=
  a <- (base + offset)%f ;;;
  (get_memory st a).

Definition ldr (s : state) (dst : reg_name) (src : reg_name) : exec_mode * state :=
  match (dst, src) with
  | (R _ _, R _ _) =>
    match get_reg s src with
    | Some src' =>
      match (get_mail_boxes s) !!! (get_current_vm s) with
      | (tx, _) =>
        match decide (to_pid_aligned src' = tx) with
        | right _ =>
          match get_memory s src' with
          | Some v => (ExecI, update_incr_PC (update_reg s dst v))
          | _ => (FailPageFaultI, s)
          end
        | left _ => (FailPageFaultI, s)
        end
      end
    | _ => (FailI, s)
    end
  | _ => (FailI, s)
  end.

Definition str (s : state) (src : reg_name) (dst : reg_name) : exec_mode * state :=
  let comp :=
      src' <- get_reg s src ;;;
      dst' <- get_reg s dst ;;;
      Some (src', dst')
  in
  match comp with
  | Some (src', dst') =>
    match (get_mail_boxes s) !!! (get_current_vm s) with
    | (_, (rx, _)) =>
      match decide (to_pid_aligned dst' = rx) with
      | right _ =>
        match update_memory s dst' src' with
        | (ExecI, s') => (ExecI, update_incr_PC s')
        | _ => (FailPageFaultI, s)
        end
      | left _ => (FailPageFaultI, s)
      end
    end
  | _ => (FailI, s)
  end.


Definition cmp_word (s : state) (arg1 : reg_name) (arg2 : Word) : exec_mode * state :=
  let comp :=
      arg1' <- get_reg s arg1 ;;;
      m <- (if (arg1' <? arg2)%f then
           Some (update_reg s NZ W2)
           else if  (arg2 <? arg1')%f then
              Some (update_reg s NZ W0)
             else Some (update_reg s NZ W1)) ;;;
      Some(update_incr_PC m)
  in
  (option_state_unpack s comp).

Definition cmp_reg (s : state) (arg1 : reg_name) (arg2 : reg_name) : exec_mode * state :=
  let comp :=
      arg1' <- get_reg s arg1 ;;;
      arg2' <- get_reg s arg2 ;;;
      m <- (if (arg1' <? arg2')%f then
           Some (update_reg s NZ W2)
           else if  (arg2' <? arg1')%f then
              Some (update_reg s NZ W0)
             else Some (update_reg s NZ W1)) ;;;
      Some(update_incr_PC m)
  in
  (option_state_unpack s comp).

Definition bne (s : state) (arg : reg_name) : exec_mode * state :=
  let comp :=
      arg' <- get_reg s arg ;;;
      nz <- get_reg s NZ ;;;
      if (nz =? W1)%f then  Some(update_incr_PC s)
      else Some (update_reg s PC arg')
  in
  (option_state_unpack s comp).

Definition br (s : state) (arg : reg_name) : exec_mode * state :=
  let comp := (fun x => update_reg s PC x) <$> (get_reg s arg)
  in
  (option_state_unpack s comp).

Definition fail (s : state) : exec_mode * state :=
  (FailI, s).

Definition halt (s : state) : exec_mode * state :=
  (HaltI, (update_incr_PC s)).

(* Hvc calls *)
Definition hvc_result : Type -> Type :=
  sum (sum () hvc_error).

Definition lift_option {B : Type} (o : option B) : hvc_result B :=
  match o with
  | None => inl (inl ())
  | Some b => inr b
  end.

Definition lift_option_with_err {B : Type}
           (o : option B) (e : hvc_error) : hvc_result B :=
  match o with
  | None => inl (inr e)
  | Some b => inr b
  end.

Definition undef {B : Type} : hvc_result B := inl (inl ()).

Definition throw {B : Type} (e : hvc_error) : hvc_result B := inl (inr e).

Definition unpack_hvc_result_normal (o : state) (q : hvc_result state) : exec_mode * state :=
  match q with
  | inl err =>
    match err with
    | inl () => (FailI, o)
    | inr err' =>
      (ExecI, (update_incr_PC (update_reg
                        (update_reg o R0 (encode_hvc_ret_code Error))
                            R2 (encode_hvc_error err'))))
    end
  | inr o' => (ExecI, update_incr_PC o')
  end.

Definition update_current_vmid (st : state) (v : VMID) : state :=
  (get_reg_files st, get_mail_boxes st, get_page_tables st, v, get_mem st, get_transactions st).

Definition unpack_hvc_result_yield (o : state) (q : hvc_result (state * VMID)) : exec_mode * state :=
  match q with
  | inl err =>
    match err with
    | inl () => (FailI, o)
    | inr err' =>
       (ExecI, update_incr_PC (update_reg
                                 (update_reg o R0
                                    (encode_hvc_ret_code Error))
                                 R2 (encode_hvc_error err')))
    end
  | inr (o', id) => (ExecI, (update_current_vmid  (update_incr_PC o') id))
  end.

Definition get_tx_pid_global (st : state) (v : VMID) : PID:=
  match get_vm_mail_box st v with
    | (pid, _) => pid
  end.

Definition is_rx_ready_global (st : state) (v : VMID) : bool :=
  match get_vm_mail_box st v with
  | (_, (_, Some _)) => true
  | _ => false
  end.

Definition is_rx_ready (st : state) : bool :=
  is_rx_ready_global st (get_current_vm st).

Definition get_rx_sender_global (st : state) (v : VMID) : option VMID:=
  match get_vm_mail_box st v with
  | (_, (_, Some (_, v'))) => Some v'
  | _ => None
  end.

Definition get_rx_sender (st : state) : option VMID:=
  get_rx_sender_global st (get_current_vm st).

Definition empty_rx_global (st : state) (v : VMID) : option state :=
  match get_vm_mail_box st v with
  | (txAddr, (rxAddr, Some(len, _))) =>
    Some (get_reg_files st,
          vinsert v (txAddr, (rxAddr,  None)) (get_mail_boxes st),
          get_page_tables st,
          get_current_vm st,
          get_mem st, get_transactions st)
  | _ => None
  end.

Definition empty_rx (st : state) : option state :=
  empty_rx_global st (get_current_vm st).

Definition copy_from_addr_to_addr_unsafe (st : state) (src dst : Addr) : option state :=
  w <- get_memory_unsafe st src ;;;
  Some (update_memory_unsafe st dst w).

Definition copy_page_unsafe (st : state) (src dst : PID) : option state :=
  foldr (fun x s =>
           match x with
           | (a, b) =>
             (@bind option _ _ _ state state s (fun y => copy_from_addr_to_addr_unsafe y a b))
           end)
        (Some st)
        (zip (finz.seq (of_pid src)  (Z.to_nat page_size))
                   (finz.seq (of_pid dst)  (Z.to_nat page_size))).

(* Definition fin_coerce {n m : nat} (i : fin n) (lt : fin_to_nat i < m) : fin m := *)
(*   Fin.of_nat_lt lt.   *)

Program Definition transfer_msg_unsafe (st : state) (l : Word) (v : VMID) (r : VMID) : hvc_result state :=
  if (l <? page_size)%Z then
    match get_vm_mail_box st v with
    | (txPid, _) =>
      match get_vm_mail_box st r with
      | (tx, (rxPid, _)) =>
        st' <- lift_option (copy_page_unsafe st txPid rxPid) ;;;
        unit (get_reg_files st,
              vinsert r (tx, (rxPid, Some(l, v))) (get_mail_boxes st),
              get_page_tables st,
              get_current_vm st,
              get_mem st', get_transactions st)
      end
    end
  else throw InvParam.

Definition transfer_msg (st : state) (l : Word) (r : VMID) : hvc_result state :=
  transfer_msg_unsafe st l (get_current_vm st) r.

Definition get_fresh_handles (trans: transactions): list handle:=
  (elements trans.2).

(* TODO: pick the least *free* handle *)

Definition fresh_handle (trans : transactions) : hvc_result handle :=
    let hds := (get_fresh_handles trans) in
    match hds with
    | [] => throw NoMem
    | hd :: hds' => unit hd
  end.

Definition memory_region_descriptor : Type :=
  VMID(* receiver *) * list PID (* pids *).

Definition transaction_descriptor : Type :=
  VMID (* Sender *) * option handle (* Handle *) * Word (* Tag *)
  * Word(* Flag *)
  * Word(* Counter *)
  * gmap VMID (gset PID) (* Receivers *).

Definition memory_regions_to_vec (md : list memory_region_descriptor) : gmap VMID (gset PID):=
  foldr (fun v acc => match decide (NoDup v.2) with
                         | left l =>  <[v.1:=(list_to_set v.2)]> acc
                         | right r => acc (* XXX throw InvalidParam ? *)
                         end) ∅ md.

Definition parse_memory_region_descriptor (st : state) (b:Addr) (o:Z) : option memory_region_descriptor :=
  l <- get_memory_with_offset st b o ;;;
  r <- get_memory_with_offset st b (o + 1) ;;;
  r' <- decode_vmid r ;;;
  ls' <- sequence_a (foldl (fun acc (v:Z) =>
                              (bind (get_memory_with_offset st b (o + 2 + v)) to_pid) :: acc) nil (seqZ 0 (finz.to_z l))) ;;;
  unit (r', ls').



Definition parse_memory_region_descriptors (st : state) (b : Addr) (o:Z) (count : Z) : option (list memory_region_descriptor) :=
  ls' <- sequence_a (foldl (fun acc v =>  ((parse_memory_region_descriptor st) b (o+v)) :: acc)
                          (@nil (option memory_region_descriptor)) (seqZ 0 count)) ;;;
  unit (ls').

(* TODO: Prop version, reflection *)

Definition parse_transaction_descriptor (st : state) (wl : Word) (b: Addr) : option transaction_descriptor :=
  (* Main fields *)
  vs <- get_memory_with_offset st b 0 ;;;
  wf <- get_memory_with_offset st b 1 ;;;
  wh <- get_memory_with_offset st b 2 ;;;
  wt <- get_memory_with_offset st b 3 ;;;
  wc <- get_memory_with_offset st b 4 ;;;
  memDescrs <- parse_memory_region_descriptors st b 5 (finz.to_z wc);;;
  (* Validate length *)
  vs' <- decode_vmid W0 ;;;
  unit (vs', (if (finz.to_z wh =? 0)%Z then None else Some wh), wt , wf, wc, memory_regions_to_vec memDescrs).

(*TODO: more things to be checked ...*)
Definition validate_transaction_descriptor (st : state) (wl : Word) (ty : transaction_type)
           (t : transaction_descriptor) : hvc_result () :=
  match t with
  | (vs', h, wt, wf, wc, gm) =>
    _ <- lift_option_with_err (
             (* at least one receiver*)
        _ <- @bool_check_option True (negb (finz.to_z wc =? 0)%Z) ;;;
             (* wc is consistent with gm*)
        _ <- @bool_check_option True (finz.to_z wc =? Z.of_nat (size gm))%Z ;;;
             (* for now hafnium doesn't support multi-way memory sharing, so wc must equal 1 *)
        _ <- @bool_check_option True (match ty with
                                     | Donation => (finz.to_z wc =? 1)%Z
                                     | Sharing => (finz.to_z wc =? 1)%Z
                                     | Lending => (finz.to_z wc =? 1)%Z
                                 end) ;;;
             (* sender is the caller *)
        _ <- @bool_check_option True ((get_current_vm st) =? vs');;;
             (* none of the receivers is the caller  *)
        _ <- @bool_check_option True (map_fold (λ (k: VMID) v acc, (andb (vs' =? k) acc)) true gm);;;
             (* clear is not allowed for mem sharing *)
        _ <- @bool_check_option True (match ty with
                                     | Sharing => (negb (finz.to_z wf =? 1)%Z)
                                     | _ => true
                                 end);;;
             (* no other flags are supported *)
        _ <- @bool_check_option True (finz.to_z wf <=? 1)%Z;;;
             (* h equals 0*)
        h
           ) InvParam ;;;
    unit tt
  end.


Definition insert_transaction (st : state) (h : handle) (t : transaction) : state :=
  (get_reg_files st, get_mail_boxes st, get_page_tables st, get_current_vm st, get_mem st,
   (<[h:=t]>(get_transactions st).1 , (get_transactions st).2 ∖ {[h]})).

Definition new_transaction (st : state) (vid : VMID)
           (tt : transaction_type) (flag tag : Word) (m : gmap VMID (gset PID))  : hvc_result (state * handle) :=
  if decide (map_Forall (fun _ v =>
                   (set_fold (fun v' acc' =>
                                andb acc' (check_ownership_page st vid v'))
                             true
                             v))
           m)
  then
    h <- fresh_handle (get_transactions st) ;;;
    unit (insert_transaction st h (vid, flag, tag, ∅, m, tt), h)
  else throw Denied.

Definition get_transaction (st : state) (h : handle) : option transaction :=
  ((get_transactions st).1) !! h.

Definition remove_transaction (s : state) (h : handle) : state :=
  (get_reg_files s, get_mail_boxes s, get_page_tables s, get_current_vm s, get_mem s,
    (delete h (get_transactions s).1, union (get_transactions s).2 {[h]})).

Definition new_transaction_from_descriptor (st : state) (ty : transaction_type)
           (td : transaction_descriptor) : hvc_result (state * handle) :=
  match td with
  | (s, None, t, f, wc, rs) => new_transaction st s ty f t rs
  | _ => throw InvParam
  end.

Definition is_primary (st : state) : bool :=
  (get_current_vm st) =? 0.

Definition is_secondary (st : state) : bool :=
  negb (is_primary st).

Definition run (s : state) : exec_mode * state :=
  let comp :=
      r <- lift_option (get_reg s R1) ;;;
      id <- lift_option_with_err (decode_vmid r) InvParam ;;;
      if is_primary s
      then
        unit (s, id)
      else
        throw InvParam
  in
  unpack_hvc_result_yield s comp.

Program Definition yield (s : state) : exec_mode * state :=
  let comp :=
      let s' := (update_reg_global s (@nat_to_fin 0 vm_count vm_count_pos) R0 (encode_hvc_func Yield))
      in
      if is_primary s'
      then
        unit (s', (@nat_to_fin 0 vm_count vm_count_pos))
      else
        unit ((update_reg_global s' (@nat_to_fin 0 vm_count vm_count_pos) R1 (encode_vmid (get_current_vm s'))), (@nat_to_fin 0 vm_count vm_count_pos))
  in
  unpack_hvc_result_yield s comp.


(* all pages have the same required permission*)
Definition check_transition_transaction (s : state) (td : transaction_descriptor) : bool :=
  let p := (Owned, ExclusiveAccess) in
  match td with
  | (_, _, _, _, m) => map_fold
                         (fun _ v acc  => andb acc (set_fold (fun v' acc' => andb acc'
                           (check_perm_page s (get_current_vm s) v' p)) true v))
                       true m
  end.

Definition mem_send (s : state) (ty: transaction_type) : exec_mode * state :=
  let comp :=
      r <- lift_option (get_reg s R1) ;;;
      m <- (if (page_size <? r)%Z
            then throw InvParam
            else
              td <- lift_option (parse_transaction_descriptor s r (of_pid (get_tx_pid_global s (get_current_vm s)))) ;;;
              _ <- validate_transaction_descriptor s r ty td ;;;
              if (check_transition_transaction s td)
              then bind (new_transaction_from_descriptor s ty td)
                        (fun x => unit (x, td))
              else throw Denied) ;;;
        match m with
        | (st,hd, td) =>
          match td with
          | (_, gm) => unit(update_reg (update_reg
                      (set_fold (fun v' (acc': state) => update_page_table acc' v' (Owned, NoAccess))
                         st (foldr (fun v (acc: gset PID) => union v.2 acc) (∅: gset PID) (map_to_list gm)))
                      R0 (encode_hvc_ret_code Succ))
                      R2 hd)
          end
        end
  in
  unpack_hvc_result_normal s comp.

Definition toggle_transaction_retrieve (s : state) (h : handle) (trn: transaction) : hvc_result state :=
  let v := (get_current_vm s) in
  match trn with
   (vs, w1, w2, sr, vr, ty) =>
      match (vr !! v) with
      | None => throw Denied
      | _ => if decide (v ∈ sr)
             then throw Denied
             else unit (get_reg_files s, get_mail_boxes s, get_page_tables s, get_current_vm s, get_mem s,
                        (<[h:=(vs, w1, w2, union sr (singleton v), vr, ty)]>(get_transactions s).1, (get_transactions s).2 ))
      end
  end.

Definition toggle_transaction_relinquish (s : state) (h : handle) (v : VMID) : hvc_result state :=
  match get_transaction s h with
  | Some (vs, w1, w2, sr, vr, ty) =>
    match (vr !! v) with
      | None => throw Denied
      | _ => if decide (v ∈ sr)
             then unit (get_reg_files s, get_mail_boxes s, get_page_tables s, get_current_vm s, get_mem s,
                        (<[h:=(vs, w1, w2, difference sr (singleton v), vr, ty)]>(get_transactions s).1, (get_transactions s).2 ))
             else throw Denied
    end
  | _ => throw InvParam
  end.

Definition relinquish_transaction (s : state)
           (h : handle)
           (receiversMap : gmap VMID (gset PID)) : hvc_result state :=
  s' <- toggle_transaction_relinquish s h (get_current_vm s) ;;;
   l <- lift_option (receiversMap !! (get_current_vm s));;;
  unit (set_fold (fun v' acc' => update_page_table acc' v' (NotOwned, NoAccess)) s' l).

Definition get_receivers (t : transaction) : gmap VMID (gset PID) :=
  match t with
  | (_, _, _, m, _) => m
  end.

Definition get_type (t : transaction) : transaction_type :=
  match t with
  | (_, _, _, _, ty) => ty
  end.
Definition retrieve (s : state) : exec_mode * state :=
  let comp :=
 (* TODO: get the descriptor from tx and validate it *)
      handle <- lift_option (get_reg s R1) ;;;
      trn <- lift_option_with_err (get_transaction s handle) InvParam ;;;
      (let gm := get_receivers trn in
       let ty := get_type trn in
       (* add receiver(caller) into the list of the transaction *)
          s' <- toggle_transaction_retrieve s handle trn ;;;
       (* for all pages of the trancation ... (change the page table of the caller according to the type)*)
          l <- lift_option (gm !! (get_current_vm s));;;
  match ty with
  | Sharing =>
    unit (set_fold (fun v' acc' =>
                   update_page_table acc' v' (NotOwned, SharedAccess))
                s' l)
  | Lending =>
    (* it is fine because we only allow at most one receiver *)
      unit (set_fold (fun v' acc' =>
                        update_page_table acc' v' (NotOwned, ExclusiveAccess))
                     s' l)
  | Donation =>
    unit (set_fold (fun v' acc' =>
                   update_page_table acc' v' (Owned, ExclusiveAccess))
                s' l)
  end)
  (* TODO: put a descriptor into rx *)
  in
  unpack_hvc_result_normal s comp.

Definition relinquish (s : state) : exec_mode * state :=
  let comp :=
      handle <- lift_option (get_reg s R1) ;;;
      trn <- lift_option_with_err (get_transaction s handle) InvParam ;;;
      relinquish_transaction s handle (get_receivers trn)
  in
  unpack_hvc_result_normal s comp.

Definition no_borrowers (s : state) (h : handle) (v : VMID) : bool :=
  match (get_transaction s h) with
  | None => true
  | Some (vs, w1, w2, sr, vr, ty) =>
    if decide (sr = empty)
    then false
    else true
  end.

Definition reclaim (s : state) : exec_mode * state :=
  let comp :=
      handle <- lift_option (get_reg s R1) ;;;
      trn <- lift_option_with_err (get_transaction s handle) InvParam ;;;
      l <- lift_option ((get_receivers trn) !! (get_current_vm s));;;
      if no_borrowers s handle (get_current_vm s)
      then
        unit (set_fold
                (fun v' acc' =>
                   update_page_table acc' v' (Owned, ExclusiveAccess))
                (remove_transaction s handle) l)
      else throw Denied
  in
  unpack_hvc_result_normal s comp.

Definition send (s : state) : exec_mode * state :=
  let comp :=
      receiver <- lift_option (get_reg s R1) ;;;
      receiver' <- lift_option_with_err (decode_vmid receiver) InvParam ;;;
      l <- lift_option (get_reg s R2) ;;;
      transfer_msg s l receiver'
  in
  unpack_hvc_result_normal s comp.

Definition wait (s : state) : exec_mode * state :=
  let comp :=
      if is_rx_ready s
      then unit (s, get_current_vm s)
      else unit (s, (@nat_to_fin 0 _ vm_count_pos))
  in
  unpack_hvc_result_yield s comp.

Definition hvc (s : state) : exec_mode * state :=
  match get_reg s R0 with
  | None => fail s
  | Some r0 =>
    match decode_hvc_func r0 with
    | None => fail s
    | Some func =>
      match func with
      | Run => run s
      | Yield => yield s
      | Share => mem_send s Sharing
      | Lend => mem_send s Lending
      | Donate => mem_send s Donation
      | Retrieve => retrieve s
      | Relinquish => relinquish s
      | Reclaim => reclaim s
      | Send => send s
      | Wait => wait s
      end
    end
  end.

Definition exec (i : instruction) (s : state) : exec_mode * state :=
  match i with
  | Mov dst (inl srcWord) => mov_word s dst srcWord
  | Mov dst (inr srcReg) => mov_reg s dst srcReg
  | Ldr dst src => ldr s dst src
  | Str src dst => str s src dst
  | Cmp arg1 (inl arg2) => cmp_word s arg1 arg2
  | Cmp arg1 (inr arg2) => cmp_reg s arg1 arg2
  | Bne arg => bne s arg
  | Br arg => br s arg
  | Fail => fail s
  | Halt => halt s
  | Hvc => hvc s
  end.

Arguments exec !_ _.

Inductive step : exec_mode -> state -> exec_mode -> state -> Prop :=
| step_exec_fail:
    forall st,
      not (is_valid_PC st = Some true) ->
      step ExecI st FailI st
| step_exec_normal:
    forall st a w i c,
      is_valid_PC st = Some true ->
      get_reg st PC = Some a ->
      get_memory st a = Some w ->
      decode_instruction w = Some i ->
      exec i st = c ->
      step ExecI st c.1 c.2.

Definition terminated (e : exec_mode) :=
  match e with
  | ExecI => false
  | _ => true
  end.

Lemma terminated_stuck m σ m' σ' :
  step m σ m' σ' → terminated m = false.
Proof.
  intros st; destruct st; reflexivity.
Qed.

Definition scheduler : state → nat → Prop :=
λ σ i,  (fin_to_nat (get_current_vm σ)) = i.
