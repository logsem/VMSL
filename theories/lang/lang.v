(* the operational semantics *)
From stdpp Require Import gmap fin_maps list countable fin mapset fin_map_dom vector.
From HypVeri Require Export monad machine  machine_extra.

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
  gmap PID ownership * gmap PID access.

Definition tx_buffer : Type :=
  PID.

Definition rx_buffer : Type :=
  (PID * option(Word * VMID)).

Definition mail_box : Type :=
  (tx_buffer * rx_buffer).

Definition transaction : Type :=
  VMID (* sender *)
  * Word (*flag *)
  * bool (* if retrieved *)
  * VMID (* receiver *)
  * list PID (* PIDs *)
  * transaction_type.

Notation handle := Word.

Definition hpool := gset handle.

Definition transactions : Type :=
  gmap handle transaction  * hpool.

Definition state : Type :=
  vec reg_file vm_count
  * vec mail_box vm_count
  * vec page_table vm_count
  * VMID
  * mem
  * transactions.

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
Definition check_ownership_page (st : state) (v : VMID) (p : PID) (pm : ownership ) : bool :=
  match (get_vm_page_table st v).1 !! p  with
  | Some p' =>
    match (decide (pm = p')) with
    | left _ => true
    | right _ => false
    end

  | _ => false
  end.

Definition check_access_page (st : state) (v : VMID) (p : PID) (pm : access) : bool :=
  match (get_vm_page_table st v).2 !! p  with
  | Some p' =>
    match (decide (pm = p')) with
    | left _ => true
    | right _ => false
    end
  | _ => false
  end.

Definition check_perm_page (st : state) (v : VMID) (p:PID) (pm : ownership* access) : bool :=
  andb (check_ownership_page st v p pm.1)
  (check_access_page st v p pm.2).


Definition check_perm_addr (st : state) (v : VMID) (a : Addr) (p : ownership* access) : bool :=
  check_perm_page st v (to_pid_aligned a) p.

Definition check_ownership_page' (st : state) (v : VMID) (p : PID)  : bool :=
  match (get_vm_page_table st v).1 !! p  with
  | Some p' => is_owned p'
  | _ => false
  end.


Definition check_access_page' (st : state) (v : VMID) (p : PID) : bool :=
  match (get_vm_page_table st v).2 !! p with
  | Some p' => is_accessible p'
  | _ => false
  end.

Definition check_access_addr (st : state) (v : VMID) (a : Addr) : bool :=
  check_access_page' st v (to_pid_aligned a).

Definition check_ownership_addr (st : state) (v : VMID) (a : Addr) : bool :=
  check_ownership_page' st v (to_pid_aligned a).

Definition update_reg_global (st : state) (v : VMID) (r : reg_name) (w : Word) : state :=
  (vinsert v (<[r:=w]>(get_vm_reg_file st v)) (get_reg_files st),
   (get_mail_boxes st), (get_page_tables st),
   get_current_vm st,
   get_mem st, get_transactions st).

Definition update_reg (st : state) (r : reg_name) (w : Word) : state :=
  update_reg_global st (get_current_vm st) r w.

Definition get_reg_global (st : state) (v : VMID) (r : reg_name) : option Word :=
  (get_vm_reg_file st v) !! r.

Definition get_reg (st : state) (r : reg_name) : option Word :=
  get_reg_global st (get_current_vm st) r.

Definition update_ownership_global (st : state) (v : VMID) (p : PID) (pm : ownership) : state :=
  (get_reg_files st, get_mail_boxes st,
   vinsert v (<[p:=pm]>(get_vm_page_table st v).1, (get_vm_page_table st v).2) (get_page_tables st),
   get_current_vm st,
   get_mem st, get_transactions st).

Definition update_ownership (st : state) (p : PID) (pm : ownership) : state :=
  update_ownership_global st (get_current_vm st) p pm.

Definition update_access_global (st : state) (v : VMID) (p : PID) (pm : access) : state :=
  (get_reg_files st, get_mail_boxes st,
   vinsert v ((get_vm_page_table st v).1, <[p:=pm]>(get_vm_page_table st v).2) (get_page_tables st),
   get_current_vm st,
   get_mem st, get_transactions st).

Definition update_access(st : state) (p : PID) (pm : access) : state :=
  update_access_global st (get_current_vm st) p pm.

Definition update_ownership_global_batch st (v:VMID) (ps : list PID) (pm: ownership): state :=
   (get_reg_files st, get_mail_boxes st,
   vinsert v ((foldr (λ p acc, <[p:=pm]>acc)(get_vm_page_table st v).1 ps),
              (get_vm_page_table st v).2) (get_page_tables st),
   get_current_vm st,
   get_mem st, get_transactions st).

Definition update_access_global_batch st (v:VMID) (ps : list PID) (pm: access): state :=
   (get_reg_files st, get_mail_boxes st,
   vinsert v ((get_vm_page_table st v).1,
              (foldr (λ p acc, <[p:=pm]>acc)(get_vm_page_table st v).2 ps)) (get_page_tables st),
   get_current_vm st,
   get_mem st, get_transactions st).

Definition update_memory_global_batch (st : state) (l : list (Addr * Word)) : state :=
  (get_reg_files st, get_mail_boxes st, get_page_tables st, get_current_vm st, (list_to_map l) ∪ (get_mem st), get_transactions st).

Definition update_ownership_batch st (ps : list PID) (pm: ownership): state :=
  update_ownership_global_batch st (get_current_vm st) ps pm.

Definition update_access_batch st (ps : list PID) (pm: access): state :=
  update_access_global_batch st (get_current_vm st) ps pm.

Definition update_memory_unsafe (st : state) (a : Addr) (w : Word) : state :=
  (get_reg_files st, get_mail_boxes st, get_page_tables st, get_current_vm st,
   <[a:=w]>(get_mem st), get_transactions st).

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
  (get_mem st) !! a.

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
   (get_vm_mail_box st v).1.

Definition get_rx_pid_global (st : state) (v : VMID) : PID :=
  (get_vm_mail_box st v).2.1.
                       
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

Definition write_mem_segment_unsafe (st : state) (dst : Addr) (segment : list Word) : state :=
  update_memory_global_batch st (zip (finz.seq dst (Z.to_nat page_size)) segment).

Definition read_mem_segment_unsafe (st : state) (src : Addr) (l : Word) : list Word :=
  foldr (fun x s => match get_memory_unsafe st x with | Some x' => x' :: s | None => s end) [] (finz.seq src (Z.to_nat (finz.to_z l))).

Definition copy_from_addr_to_addr_unsafe (st : state) (src dst : Addr) (l : Word) : state :=
  write_mem_segment_unsafe st dst (read_mem_segment_unsafe st src l).

Definition copy_page_segment_unsafe (st : state) (src dst : PID) (l : Word) : state :=
  copy_from_addr_to_addr_unsafe st (of_pid src) (of_pid dst) l.

Definition fill_rx_unsafe (st : state) (l : Word) (v r : VMID) (tx rx : PID) : state :=
  (get_reg_files st, vinsert r (tx, (rx, Some(l, v))) (get_mail_boxes st), get_page_tables st, get_current_vm st, get_mem st, get_transactions st).

Definition fill_rx (st : state) (l : Word) (v r : VMID) : hvc_result state :=
  match get_vm_mail_box st r with
  | (tx, (rx, None)) =>
    unit (fill_rx_unsafe st l v r tx rx)
  | _ => throw Busy
  end.

Definition transfer_msg_unsafe (st : state) (l : Word) (v : VMID) (r : VMID) : hvc_result state :=
  if (page_size <? l)%Z
  then throw InvParam
  else
    let st' := copy_page_segment_unsafe st (get_tx_pid_global st v) (get_rx_pid_global st r) l
    in fill_rx st' l v r.

Definition transfer_msg (st : state) (l : Word) (r : VMID) : hvc_result state :=
  transfer_msg_unsafe st l (get_current_vm st) r.

Definition get_fresh_handles (trans: transactions): list handle:=
  (elements trans.2).

Definition fresh_handle (trans : transactions) : hvc_result handle :=
    let hds := (get_fresh_handles trans) in
    match hds with
    | [] => throw NoMem
    | hd :: hds' => unit hd
  end.

Definition memory_region_descriptor : Type :=
  VMID(* receiver *) * list PID (* pids *).

Definition transaction_descriptor : Type :=
  VMID (* Sender *)
  * option handle (* Handle *)
  * Word(* Flag *)
  * VMID (* Receiver *)
  * list PID.

Definition transaction_to_transaction_descriptor (t : transaction) (h : handle) : transaction_descriptor :=
  match t with
  | (vs, f, _, vr, ls, _) => (vs, Some h, f, vr, ls)
  end.

Definition transaction_to_list_words (t : transaction) (h : handle) : option (list Word) :=
  match transaction_to_transaction_descriptor t h with
  | (vs, Some h, f, vr, ls) =>
    match finz.of_z (Z.of_nat (length ls)) with
    | Some l =>
      Some ([of_imm (encode_vmid vs); f; h; l; of_imm (encode_vmid vr)] ++ map of_pid ls)
    | None => None
    end
  | (vs, None, f, vr, ls) =>
    match finz.of_z (Z.of_nat (length ls)) with
    | Some l =>
      Some ([of_imm (encode_vmid vs); f; W0; l; of_imm (encode_vmid vr)] ++ map of_pid ls)
    | None => None
    end
  end.

Definition transaction_write_rx (st : state) (t : transaction) (h : handle) : option state :=
  match transaction_to_list_words t h with
  | Some ls => Some (write_mem_segment_unsafe st (get_rx_pid_global st (get_current_vm st)) ls)
  | None => None
  end.

Definition parse_list_of_pids st (b : Addr) l : option (list PID) :=
   @sequence_a list _ _ _ PID option _ _ (map (λ v, (w <- ((get_mem st) !! v) ;;; (to_pid w) ))
                      (finz.seq b l)).

Definition parse_memory_region_descriptor (st : state) (b:Addr) : option memory_region_descriptor :=
  l <- get_memory_with_offset st b 0 ;;;
  r <- get_memory_with_offset st b 1 ;;;
  r' <- decode_vmid r ;;;
  ls' <- parse_list_of_pids st (b^+2)%f (Z.to_nat (finz.to_z l));;;
  unit (r', ls').

Definition parse_transaction_descriptor_retrieve (st : state) (b : Addr) : option transaction_descriptor :=
  vs <- get_memory_with_offset st b 0 ;;;
  wf <- get_memory_with_offset st b 1 ;;;
  wh <- get_memory_with_offset st b 2 ;;;
  vs' <- decode_vmid vs ;;;
  unit (vs', Some wh, wf, (get_current_vm st), []).

(* TODO: Prop version, reflection *)

Definition parse_transaction_descriptor (st : state) (b: Addr) : option transaction_descriptor :=
  (* Main fields *)
  vs <- get_memory_with_offset st b 0 ;;;
  wf <- get_memory_with_offset st b 1 ;;;
  wh <- get_memory_with_offset st b 2 ;;;
  md <- parse_memory_region_descriptor st (b^+3)%f;;;
  vs' <- decode_vmid vs ;;;
  unit (vs', (if (finz.to_z wh =? 0)%Z then None else Some wh), wf, md.1, md.2).

(*TODO: validate length*)

Definition validate_transaction_descriptor (st : state) (wl : Word) (ty : transaction_type)
           (t : transaction_descriptor) : hvc_result () :=
  match t with
  | (s, h, wf, r ,ps) =>
    _ <- lift_option_with_err (
             (* sender is the caller *)
        _ <- @bool_check_option True ((get_current_vm st) =? s);;;
             (* none of the receivers is the caller  *)
        _ <- @bool_check_option True  (negb (s =? r));;;
             (* no other flags are supported *)
        _ <- @bool_check_option True (wf <=? W1)%f;;;
             (* clearing is not allowed for mem sharing *)
        _ <- @bool_check_option True (match ty with
                                     | Sharing => (negb (wf =? W1)%f)
                                     | _ => true
                                 end);;;
             (* h equals 0*)
        @bool_check_option True (match h with
                                      | None => true
                                      | Some _ => false
                                     end)
           ) InvParam ;;;
    unit tt
  end.

Definition insert_transaction (st : state) (h : handle) (t : transaction) (shp: gset handle):=
  (get_reg_files st, get_mail_boxes st, get_page_tables st, get_current_vm st, get_mem st,
   (<[h:=t]>(get_transactions st).1 ,shp)).

Definition alloc_transaction (st : state) (h : handle) (t : transaction) : state :=
  (insert_transaction st h t ((get_transactions st).2 ∖ {[h]})).

Definition update_transaction (st : state) (h : handle) (t : transaction) : state :=
  (insert_transaction st h t (get_transactions st).2).

Definition new_transaction (st : state) (v r : VMID)
           (tt : transaction_type) (flag : Word) (ps:(list PID))  : hvc_result (state * handle) :=
  h <- fresh_handle (get_transactions st) ;;;
  unit (alloc_transaction st h (v, flag, false, r, ps, tt), h).

Definition get_transaction (st : state) (h : handle) : option transaction :=
  ((get_transactions st).1) !! h.

Definition remove_transaction (s : state) (h : handle) : state :=
  (get_reg_files s, get_mail_boxes s, get_page_tables s, get_current_vm s, get_mem s,
    (delete h (get_transactions s).1, union (get_transactions s).2 {[h]})).

Definition new_transaction_from_descriptor (st : state) (ty : transaction_type)
           (td : transaction_descriptor) : hvc_result (state * handle) :=
  match td with
  | (s, None, f, r, ps) => new_transaction st s r ty f ps
  | _ => throw InvParam
  end.

(* all pages have the same required permission *)
Definition check_transition_transaction (s : state) (td : transaction_descriptor) : bool :=
  let p := (Owned, ExclusiveAccess) in
  match td with
  | (_, _, _, _, m) => forallb (fun v' =>
                           (check_perm_page s (get_current_vm s) v' p))  m
  end.

Definition list_pid_to_addr (ps: list PID):=
  (foldr (++) [] (map (λ p,  (finz.seq (of_pid p) (Z.to_nat page_size))) ps)).

Definition flat_list_list_word (wss: list (list Word)):=
  (foldr (++) [] wss).

Definition zero_pages (st: state) (ps: list PID):=
   (get_reg_files st, get_mail_boxes st,
  get_page_tables st, get_current_vm st,
  (list_to_map (zip (list_pid_to_addr ps) (flat_list_list_word (pages_of_W0 (length ps))))) ∪ (get_mem st),
   get_transactions st).

Definition mem_send (s : state) (ty: transaction_type) : exec_mode * state :=
  let comp :=
      len <- lift_option (get_reg s R1) ;;;
      m <- (if (page_size <? len)%Z
            then throw InvParam
            else
              td <- lift_option (parse_transaction_descriptor s
                                              (of_pid (get_tx_pid_global s (get_current_vm s)))) ;;;
              _ <- validate_transaction_descriptor s len ty td ;;;
              if (check_transition_transaction s td)
              then bind (new_transaction_from_descriptor s ty td)
                        (fun x => unit (x, td))
              else throw Denied) ;;;
        match m with
        | (st,hd, (_, _ ,wf,_,ps)) =>
           let st':= (if (wf =? W1)%f
                      then (zero_pages st ps)
                      else st)
           in
          unit(update_reg (update_reg
                      (update_access_batch st' ps NoAccess)
                      R0 (encode_hvc_ret_code Succ))
                      R2 hd)
        end
  in
  unpack_hvc_result_normal s comp.

(*TODO: zero the pages*)
Definition toggle_transaction_retrieve (s : state) (h : handle) (trn: transaction)
  : hvc_result state :=
  let v := (get_current_vm s) in
  match trn with
   (vs, w1, b,r, ps, ty) =>
      match (v =? r) with
      | false => throw Denied
      | _ => if b
             then throw Denied
             else unit (update_transaction s h (vs, w1, true, r, ps, ty))
      end
  end.

Definition toggle_transaction_relinquish (s : state) (h : handle) (v : VMID) : hvc_result state :=
  match get_transaction s h with
  | Some (vs, w1, b,r, ps, ty) =>
    match (v =? r) with
      | false => throw Denied
      | _ => if b
             then unit (update_transaction s h (vs, w1, false ,r, ps, ty))
             else throw Denied
    end
  | _ => throw InvParam
  end.

Definition relinquish_transaction (s : state)
           (h : handle) (f : Word) (t : transaction) : hvc_result state :=
  let ps := t.1.2 in
  s' <- toggle_transaction_relinquish s h (get_current_vm s) ;;;
  if (f =? W1)%Z then
    unit (update_access_batch (update_reg (zero_pages s' ps) R0 (encode_hvc_ret_code Succ)) ps NoAccess)
  else
  unit (update_access_batch (update_reg s' R0 (encode_hvc_ret_code Succ)) ps NoAccess).

Definition get_memory_descriptor (t : transaction) : VMID * (list PID) :=
  match t with
  | (_, _, _, r, m, _) =>(r, m)
  end.

Definition get_transaction_type (t : transaction) : transaction_type :=
  match t with
  | (_, _, _, _,  _, ty) => ty
  end.

Definition retrieve (s : state) : exec_mode * state :=
  let comp :=
      len <- lift_option (get_reg s R1) ;;;
      m <- (if (page_size <? len)%Z
            then throw InvParam
            else
              lift_option (parse_transaction_descriptor_retrieve s
                             (of_pid (get_tx_pid_global s (get_current_vm s))))) ;;;
      match m with
      | (vs, Some handle, _, _, _) =>
        trn <- lift_option_with_err (get_transaction s handle) InvParam ;;;
        (let (r, ps) := get_memory_descriptor trn in
         let ty := get_transaction_type trn in
         (* add receiver(caller) into the list of the transaction *)
         s' <- transfer_msg s len (get_current_vm s) ;;;
         (* for all pages of the trancation ... (change the page table of the caller according to the type)*)
         match ty with
         | Sharing =>
           s'' <- toggle_transaction_retrieve s' handle trn ;;;
           unit (update_access_batch (update_reg s'' R0 (encode_hvc_ret_code Succ)) ps SharedAccess)
         | Lending =>
           s'' <- toggle_transaction_retrieve s' handle trn ;;;
           (* it is fine because we only allow at most one receiver *)
           unit (update_access_batch (update_reg s'' R0 (encode_hvc_ret_code Succ)) ps ExclusiveAccess)
         | Donation =>
           unit (update_access_batch (update_ownership_batch (update_reg (remove_transaction s' handle) R0 (encode_hvc_ret_code Succ)) ps Owned) ps ExclusiveAccess)
         end)
      | _ => throw InvParam
      end
  in
  unpack_hvc_result_normal s comp.

Definition relinquish (s : state) : exec_mode * state :=
  let b := (of_pid (get_tx_pid_global s (get_current_vm s))) in
  let comp :=
      h <- lift_option (get_memory_with_offset s b 0) ;;;
      f <- lift_option (get_memory_with_offset s b 1) ;;;
      trn <- lift_option_with_err (get_transaction s h) InvParam ;;;
      if (f >? W1)%Z then throw InvParam else
       relinquish_transaction s h f trn
  in
  unpack_hvc_result_normal s comp.

Definition no_borrowers (s : state) (h : handle) (v : VMID) : bool :=
  match (get_transaction s h) with
  | None => false
  | Some (vs, w1, b, r, ps, ty) => negb b
  end.

Definition reclaim (s : state) : exec_mode * state :=
  let comp :=
      handle <- lift_option (get_reg s R1) ;;;
      trn <- lift_option_with_err (get_transaction s handle) InvParam ;;;
      l <- unit ((get_memory_descriptor trn).2 );;;
      if no_borrowers s handle (get_current_vm s)
      then
        unit (update_reg  (update_access_batch
                             (update_ownership_batch
                                (remove_transaction s handle) l Owned) l ExclusiveAccess) R0 (encode_hvc_ret_code Succ))
      else throw Denied
  in
  unpack_hvc_result_normal s comp.

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
      let s' := (update_reg_global s (@nat_to_fin 0 vm_count vm_count_pos) R0
                                   (encode_hvc_func Yield))
      in
      if is_primary s'
      then
        unit (s', (@nat_to_fin 0 vm_count vm_count_pos))
      else
        unit ((update_reg_global s'
                      (@nat_to_fin 0 vm_count vm_count_pos) R1
                      (encode_vmid (get_current_vm s'))),
              (@nat_to_fin 0 vm_count vm_count_pos))
  in
  unpack_hvc_result_yield s comp.

Definition send (s : state) : exec_mode * state :=
  let comp :=
      let prim := @nat_to_fin 0 vm_count vm_count_pos in
      receiver <- lift_option (get_reg s R1) ;;;
      receiver' <- lift_option_with_err (decode_vmid receiver) InvParam ;;;
      l <- lift_option (get_reg s R2) ;;;
      st <- transfer_msg s l receiver' ;;;
      if is_primary st
      then
        unit (st, prim)
      else    
        unit (update_reg_global (update_reg_global (update_reg_global st prim R0 (encode_hvc_func Send))
                                                   prim R1 receiver) prim R2 l, prim)
  in
  unpack_hvc_result_yield s comp.

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
