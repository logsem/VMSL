(* the operational semantics *)
From stdpp Require Import gmap fin_maps list countable fin mapset fin_map_dom vector.
From HypVeri Require Export monad machine machine_extra.

Import MonadNotation.
Import Option.
Import Sum.
Open Scope monad_scope.

(* Getters *)
Notation "'get_current_vm' st" := (snd (fst (fst st))) (at level 70, only parsing).
Notation "'get_mem' st" := (snd (fst st)) (at level 18, only parsing).
Notation "'get_transactions' st" := (snd st) (at level 70, only parsing).
Notation "'get_reg_files' st" := (fst (fst (fst (fst (fst st))))) (at level 18, only parsing).
Notation "'get_mail_boxes' st" := (snd (fst (fst (fst (fst st))))) (at level 18, only parsing).
Notation "'get_page_table' st" := (snd (fst (fst (fst st)))) (at level 18, only parsing).
Notation "'get_reg_file' st @ v" := (get_reg_files st !!! v) (at level 18, st as ident, only parsing).
Notation "'get_mail_box' st @ v" := (get_mail_boxes st !!! v) (at level 18, only parsing).

Section lang.
Context `{HyperConst : !HypervisorConstants}.
Context `{HyperParams : !HypervisorParameters}.

(* State *)
Definition mem : Type :=
  gmap Addr Word.

Definition reg_file : Type :=
  gmap reg_name Word.

(* TODO: this is a very confusing name *)
Definition permission : Type :=
  (** owner *) option VMID * (** exclusive *) bool * (** can_access *) gset VMID.

Definition page_table : Type :=
  gmap PID permission.

Definition tx_buffer : Type :=
  PID.

Definition rx_buffer : Type :=
  (PID * option (Word * VMID)).

Definition mail_box : Type :=
  (tx_buffer * rx_buffer).

Definition meta_info : Type :=
   VMID (* sender *)
  * VMID (* receiver *)
  * gset PID (* PIDs *)
  * transaction_type.

Definition transaction : Type :=
  meta_info * bool (* if retrieved *).

Definition transactions : Type :=
  gmap Word (option transaction).

Definition state : Type :=
  vec reg_file vm_count
  * vec mail_box vm_count
  * page_table
  * VMID
  * mem
  * transactions.

Notation "'get_tx_pid' st @ v" := (((get_mail_box st @ v):mail_box).1) (at level 199).
Notation "'get_rx_pid' st @ v" := (((get_mail_box st @ v):mail_box).2.1) (at level 199).

(* Conf *)
Inductive exec_mode : Type :=
| ExecI
| HaltI
| FailI
| FailPageFaultI.

(* Aux funcs *)
Definition check_ownership_page (st : state) (v : VMID) (p : PID) : bool :=
  match (get_page_table st !! p)  with
  | Some (Some p', _ , _) =>
    match (decide (v = p')) with
    | left _ => true
    | right _ => false
    end

  | _ => false
  end.

Definition check_access_page (st : state) (v : VMID) (p : PID) : bool :=
  match (get_page_table st !! p)  with
  | Some (_, s) =>
    match (decide (v ∈ s)) with
    | left _ => true
    | right _ => false
    end
  | _ => false
  end.

Definition check_read_access_page (st : state) (v : VMID) (p : PID) : bool :=
  check_access_page st v p && (bool_decide ((get_mail_box st @ v).1 ≠ p)).

Definition check_write_access_page (st : state) (v :VMID) (p : PID) : bool :=
  check_access_page st v p && (bool_decide ((get_mail_box st @ v).2.1 ≠ p)).

Definition check_excl_page (st: state) (p: PID) : bool :=
  match (get_page_table st !! p)  with
  | Some (_, b, _) => b
  | _ => false
  end.

Definition check_excl_access_page (st : state) (v : VMID) (p : PID) : bool :=
  check_access_page st v p && check_excl_page st p.

Definition check_access_addr (st : state) (v : VMID) (a : Addr) : bool :=
  check_access_page st v (to_pid_aligned a).

Definition check_read_access_addr (st : state) (v : VMID) (a : Addr) : bool :=
  check_read_access_page st v (to_pid_aligned a).

Definition check_write_access_addr (st : state) (v : VMID) (a : Addr) : bool :=
  check_write_access_page st v (to_pid_aligned a).

Definition check_ownership_addr (st : state) (v : VMID) (a : Addr) : bool :=
  check_ownership_page st v (to_pid_aligned a).

Definition update_reg_global (st : state) (v : VMID) (r : reg_name) (w : Word) : state :=
  (vinsert v (<[r:=w]>(get_reg_file st @ v)) (get_reg_files st),
   (get_mail_boxes st), (get_page_table st),
   get_current_vm st,
   get_mem st, get_transactions st).

Definition update_reg (st : state) (r : reg_name) (w : Word) : state :=
  update_reg_global st (get_current_vm st) r w.

Definition get_reg_global (st : state) (v : VMID) (r : reg_name) : option Word :=
  (get_reg_file st @ v) !! r.

Definition get_reg (st : state) (r : reg_name) : option Word :=
  get_reg_global st (get_current_vm st) r.

Definition update_ownership (perm: permission) (v: VMID) : permission :=
  match perm with
  | (Some o, b, s) => (Some v, b, s)
  | _ => perm
  end.

Definition grant_access (perm: permission) (v: VMID) : permission :=
  match perm with
  | (o, s) => (o, {[v]} ∪ s)
  end.

Definition revoke_access (perm: permission) (v: VMID) : permission :=
  match perm with
  | (o, s) => (o, s ∖ {[v]})
  end.

Definition flip_excl (perm: permission) (v: VMID) : permission :=
  match perm with
  | (o, b, s) => (o, negb b, s)
  end.

Definition update_page_table_global (upd: permission -> VMID -> permission) (st:state) (v:VMID) (ps: gset PID) : state :=
  (get_reg_files st, get_mail_boxes st,
   (set_fold (λ p acc, match (acc !! p) with
                       | Some perm => <[p:= (upd perm v)]>acc
                       | None => acc
                       end) (get_page_table st) ps),
   get_current_vm st,
   get_mem st, get_transactions st).

Definition update_memory_global_batch (st : state) (m : mem) : state :=
  (get_reg_files st, get_mail_boxes st, get_page_table st, get_current_vm st, m ∪ (get_mem st), get_transactions st).

Definition update_memory (st : state) (a : Addr) (w : Word) : state :=
  (get_reg_files st, get_mail_boxes st, get_page_table st, get_current_vm st,
   <[a:=w]>(get_mem st), get_transactions st).

Program Definition update_offset_PC (st : state) (offset : Z) :  state :=
  match ((get_reg_file st @ (get_current_vm st)) !! PC) with
   | Some v => (update_reg st PC (v ^+ offset)%f)
   | None => st
   end.

Definition update_incr_PC (st : state) : state :=
  update_offset_PC st 1.

Definition option_state_unpack (oldSt : state) (newSt : option state) : exec_mode * state :=
  match newSt with
  | None => (FailI, oldSt)
  | Some s => (ExecI, s)
  end.

Definition nop (s : state) : exec_mode * state :=
  let s' := update_incr_PC s in
  (ExecI, s').

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

Definition write_memory (st : state) (a : Addr) (w : Word) : exec_mode * state :=
  if check_write_access_addr st (get_current_vm st) a
  then (ExecI, update_memory st a w)
  else (FailPageFaultI, st).

Definition read_memory (st : state) (a : Addr) : option Word :=
  if check_read_access_addr st (get_current_vm st) a
  then (get_mem st !! a)
  else None.

Definition get_memory (st : state) (a : Addr) : option Word :=
  (get_mem st !! a).

Definition get_memory_with_offset (st : state) (base : Addr) (offset : Z) : option Word :=
  a <- (base + offset)%f ;;;
  (get_mem st) !! a.

Definition ldr (s : state) (dst : reg_name) (src : reg_name) : exec_mode * state :=
  match (dst, src) with
  | (R _ _, R _ _) =>
    match get_reg s src with
    | Some src' =>
          match read_memory s src' with
          | Some v => (ExecI, update_incr_PC (update_reg s dst v))
          | _ => (FailPageFaultI, s)
          end
    | _ => (FailI, s)
    end
  | _ => (FailI, s)
  end.

Definition str (s : state) (src : reg_name) (dst : reg_name) : exec_mode * state :=
  let comp :=
     match (dst, src) with
     | (R _ _, R _ _) =>
         src' <- get_reg s src ;;;
         dst' <- get_reg s dst ;;;
         Some (src', dst')
     | _ => None
     end
  in
  match comp with
  | Some (src', dst') =>
        match write_memory s dst' src' with
        | (ExecI, s') => (ExecI, update_incr_PC s')
        | _ => (FailPageFaultI, s)
        end
  | _ => (FailI, s)
  end.

Definition cmp_word (s : state) (arg1 : reg_name) (arg2 : Word) : exec_mode * state :=
  let comp :=
    match arg1 with
     | R _ _ =>
      arg1' <- get_reg s arg1 ;;;
      m <- (if (arg1' <? arg2)%f then
           Some (update_reg s NZ W2)
           else if  (arg2 <? arg1')%f then
              Some (update_reg s NZ W0)
             else Some (update_reg s NZ W1)) ;;;
      Some(update_incr_PC m)
    | _ => None
    end
  in
  (option_state_unpack s comp).

Definition cmp_reg (s : state) (arg1 : reg_name) (arg2 : reg_name) : exec_mode * state :=
  let comp :=
     match (arg1, arg2) with
     | (R _ _, R _ _) =>
      arg1' <- get_reg s arg1 ;;;
      arg2' <- get_reg s arg2 ;;;
      m <- (if (arg1' <? arg2')%f then
           Some (update_reg s NZ W2)
           else if  (arg2' <? arg1')%f then
              Some (update_reg s NZ W0)
             else Some (update_reg s NZ W1)) ;;;
      Some(update_incr_PC m)
     | _ => None
     end
  in
  (option_state_unpack s comp).

Definition add (s : state) (arg1 : reg_name) (arg2 : reg_name) : exec_mode * state :=
  let comp :=
     match (arg1, arg2) with
     | (R _ _, R _ _) =>
      arg1' <- get_reg s arg1 ;;;
      arg2' <- get_reg s arg2 ;;;
      Some(update_incr_PC (update_reg s arg1 ((arg1': Word) ^+ (finz.to_z (arg2':Word)))%f))
     | _ => None
     end
  in
  (option_state_unpack s comp).

Definition sub (s : state) (arg1 : reg_name) (arg2 : reg_name) : exec_mode * state :=
  let comp :=
  match (arg1, arg2) with
     | (R _ _, R _ _) =>
     arg1' <- get_reg s arg1 ;;;
      arg2' <- get_reg s arg2 ;;;
      Some(update_incr_PC (update_reg s arg1 ((arg1': Word) ^- (finz.to_z (arg2':Word)))%f))
     | _ => None
     end
  in
  (option_state_unpack s comp).

Definition mult (s : state) (arg1 : reg_name) (arg2 : Imm) : exec_mode * state :=
  let comp :=
    match arg1 with
      | R _ _ =>
      arg1' <- get_reg s arg1 ;;;
      Some(update_incr_PC (update_reg s arg1 ((arg1': Word) ^* (finz.to_z (arg2:Word)))%f))
      | _ => None
    end
  in
  (option_state_unpack s comp).

Definition bne (s : state) (arg : reg_name) : exec_mode * state :=
  let comp :=
    match arg with
    | R _ _ => arg' <- get_reg s arg ;;;
      nz <- get_reg s NZ ;;;
      if (nz =? W1)%f then  Some(update_incr_PC s)
      else Some (update_reg s PC arg')
    | _ => None
    end
  in
  (option_state_unpack s comp).

Definition br (s : state) (arg : reg_name) : exec_mode * state :=
  let comp := match arg with
              | R _ _ => (fun x => update_reg s PC x) <$> (get_reg s arg)
              | _ => None
              end
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
  (get_reg_files st, get_mail_boxes st, get_page_table st, v, get_mem st, get_transactions st).

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


Definition is_rx_ready_global (st : state) (v : VMID) : bool :=
  match get_mail_box st @ v with
  | (_, (_, Some _)) => true
  | _ => false
  end.

Definition is_rx_ready (st : state) : bool :=
  is_rx_ready_global st (get_current_vm st).

Definition get_rx_sender_global (st : state) (v : VMID) : option VMID:=
  match get_mail_box st @ v with
  | (_, (_, Some (_, v'))) => Some v'
  | _ => None
  end.

Definition get_rx_length_global (st : state) (v : VMID) : option Word :=
  match get_mail_box st @ v with
  | (_, (_, Some (v', _))) => Some v'
  | _ => None
  end.

Definition get_rx_sender (st : state) : option VMID:=
  get_rx_sender_global st (get_current_vm st).

Definition get_rx_length (st : state) : option Word :=
  get_rx_length_global st (get_current_vm st).

Definition empty_rx(st : state) : state :=
  match get_mail_box st @ (get_current_vm st) with
  | (txAddr, (rxAddr, _)) =>
    (get_reg_files st,
     vinsert (get_current_vm st) (txAddr, (rxAddr,  None)) (get_mail_boxes st),
     get_page_table st,
     get_current_vm st,
     get_mem st, get_transactions st)
  end.

Definition write_mem_segment (st: state) (dst : Addr) (ws : list Word) : state :=
  let m := list_to_map (zip (finz.seq dst (length ws)) ws) in
  update_memory_global_batch st m.

Definition read_mem_segment (m:mem) (src : Addr) (l : nat) : option (list Word) :=
  @sequence_a list _ _ _ Word option _ _ ((λ a, (m !! a)) <$> (finz.seq src l)).

Definition copy_page_segment (st:state) (src dst : PID) (l : nat) : state :=
    match (read_mem_segment (get_mem st) (of_pid src) l) with
      Some wl => write_mem_segment st (of_pid dst) wl
      |None => st
    end.

Definition fill_rx_unsafe (st : state) (l : Word) (v r : VMID) (tx rx : PID) : state :=
  (get_reg_files st, vinsert r (tx, (rx, Some(l, v))) (get_mail_boxes st), get_page_table st, get_current_vm st, get_mem st, get_transactions st).

Definition fill_rx (st : state) (l : Word) (v r : VMID) : hvc_result state :=
  match get_mail_box st @ r with
  | (tx, (rx, None)) =>
    unit (fill_rx_unsafe st l v r tx rx)
  | _ => throw Busy
  end.

Definition write_retrieve_msg (st:state) (dst: Addr) (wh:Word) (trn: transaction): hvc_result state:=
 match trn with
  | (vs, vr, ls, t, _) =>
    match finz.of_z (Z.of_nat ((size ls) + 4)) with
    | Some l =>
      let des := ([of_imm (encode_vmid vs); wh; encode_transaction_type t ;(l ^- 4)%f]
                    ++ map of_pid (elements ls)) in
      fill_rx (write_mem_segment st dst des) l vs vr
    | None => throw InvParam
    end
 end.

Definition transfer_msg (st : state) (v : VMID) (r : VMID) (l : Word) : hvc_result state :=
  if bool_decide (page_size < l)%Z
  then throw InvParam
  else
    let st' := copy_page_segment st (get_tx_pid st @ v) (get_rx_pid st @ r) (Z.to_nat l)
    in fill_rx st' l v r.

Definition get_fresh_handles (trans: transactions): gset Word:=
  (dom (gset _) (filter (λ kv, kv.2 = None) trans)) ∩ valid_handles.

Definition fresh_handle (trans : transactions) : hvc_result Word:=
    let hds := elements (get_fresh_handles trans) in
    match hds with
    | [] => throw NoMem
    | hd :: hds' => unit hd
  end.

Definition memory_region_descriptor : Type :=
  VMID(* receiver *) * list PID (* pids *).

Definition transaction_descriptor : Type :=
  VMID (* Sender *)
  * option Word(* Handle *)
  * VMID (* Receiver *)
  * gset PID.

Definition transaction_to_transaction_descriptor (t : transaction) (h : Word) : transaction_descriptor :=
  match t with
  | (vs, vr, ls, _, _) => (vs, Some h, vr, ls)
  end.

Definition transaction_to_list_words (t : transaction) (h : Word) : option (list Word) :=
  match transaction_to_transaction_descriptor t h with
  | (vs, Some h, vr, ls) =>
    match finz.of_z (Z.of_nat (size ls)) with
    | Some l =>
      Some ([of_imm (encode_vmid vs); h; l; of_imm (encode_vmid vr)] ++ map of_pid (elements ls))
    | None => None
    end
  | (vs, None, vr, ls) =>
    match finz.of_z (Z.of_nat (size ls)) with
    | Some l =>
      Some ([of_imm (encode_vmid vs); W0; l; of_imm (encode_vmid vr)] ++ map of_pid (elements ls))
    | None => None
    end
  end.

Definition transaction_write_rx (st : state) (t : transaction) (h : Word) : option state :=
  match transaction_to_list_words t h with
  | Some ls => Some (write_mem_segment st (get_rx_pid st @ (get_current_vm st)) ls)
  | None => None
  end.

Definition parse_list_of_pids (ws: list Word) (wl: Word): option (list PID) :=
  _ <- @bool_check_option True ((Z.to_nat (finz.to_z wl)) =? length ws);;;
   @sequence_a list _ _ _ PID option _ _ (map to_pid ws).

Definition parse_list_of_Word (mem : mem) (b : Addr) l : option (list Word) :=
   @sequence_a list _ _ _ Word option _ _ (map (λ v, (mem !! v))
                      (finz.seq b l)).

(* TODO: Prop version, reflection *)

Definition parse_transaction_descriptor (mem : mem) (b: Addr) (len: nat) : option transaction_descriptor :=
  (* Main fields *)
  raw_descriptor <- parse_list_of_Word mem b len;;;
  vs_raw <- raw_descriptor !! 0 ;;;
  vs <- decode_vmid vs_raw ;;;
  wh <- raw_descriptor !! 1 ;;;
  wl <- raw_descriptor !! 2 ;;;
  vr_raw <- raw_descriptor !! 3 ;;;
  vr <- decode_vmid vr_raw ;;;
  ps <- parse_list_of_pids (drop 4 raw_descriptor) wl ;;;
  unit (vs, (if bool_decide (finz.to_z wh = 0)%Z then None else Some wh), vr, list_to_set ps).

Definition validate_transaction_descriptor (i:VMID) (t : transaction_descriptor) : bool  :=
  match t with
  | (s, h, r, ps) => bool_decide (i = s ∧ s ≠ r ∧ ¬ is_Some(h))
             (* sender is the caller *)
             (* none of the receivers is the caller  *)
             (* h equals 0*)
  end.

Definition insert_transaction (st : state) (h : Word) (t : transaction):=
  (get_reg_files st, get_mail_boxes st, get_page_table st, get_current_vm st, get_mem st,
   <[h:= Some t]>(get_transactions st)).

Definition alloc_transaction := insert_transaction.
Definition update_transaction := insert_transaction.

Definition new_transaction (st : state) (v r : VMID)
           (tt : transaction_type) (ps:(gset PID))  : hvc_result (state * Word) :=
  h <- fresh_handle (get_transactions st) ;;;
  unit (alloc_transaction st h (v, r, ps, tt, false), h).

Definition get_transaction (st : state) (h : Word) : option transaction:=
  if bool_decide (h ∈ valid_handles) then
  match (get_transactions st) !! h with
    |Some o => o
    |None => None
  end else None.

Definition remove_transaction (s : state) (h : Word) : state :=
  (get_reg_files s, get_mail_boxes s, get_page_table s, get_current_vm s, get_mem s,
    <[h := None]>(get_transactions s)).

Definition new_transaction_from_descriptor (st : state) (ty : transaction_type)
           (td : transaction_descriptor) : hvc_result (state * Word) :=
  match td with
  | (s, None, r, ps) => new_transaction st s r ty ps
  | _ => throw InvParam
  end.

(* all pages have the same required permission *)
Definition check_transition_transaction (s : state) (td : transaction_descriptor) : bool :=
  match td with
  | (_, _, _, m) => bool_decide (set_Forall (fun v' =>
                                 (check_excl_access_page s (get_current_vm s) v')
                                 && check_ownership_page s (get_current_vm s) v' = true) m)
  end.

Definition list_pid_to_addr (ps: list PID):=
  (foldr (++) [] (map (λ p,  (finz.seq (of_pid p) (Z.to_nat page_size))) ps)).

Definition flat_list_list_word (wss: list (list Word)):=
  (foldr (++) [] wss).

Definition mem_send (s : state) (ty: transaction_type) : exec_mode * state :=
  let comp :=
      len <- lift_option (get_reg s R1) ;;;
      m <- (if bool_decide (page_size < len)%Z
            then throw InvParam
            else
              td <- lift_option_with_err (parse_transaction_descriptor (get_mem s)
                                               (get_tx_pid s @ (get_current_vm s)) (Z.to_nat (finz.to_z len))) InvParam ;;;
              _ <- (if (validate_transaction_descriptor (get_current_vm s) td) then unit () else throw InvParam) ;;;
              if (check_transition_transaction s td)
              then bind (new_transaction_from_descriptor s ty td)
                        (fun x => unit (x, td))
              else throw Denied) ;;;
        match m with
        | (st,hd, (_, _, _, ps)) =>
           match ty with
           | Sharing =>
             unit(update_reg (update_reg
                                (update_page_table_global flip_excl st (get_current_vm st) ps)
                                R0 (encode_hvc_ret_code Succ))
                             R2 hd)
           | _ => 
             unit(update_reg (update_reg
                                (update_page_table_global revoke_access st (get_current_vm st) ps)
                                R0 (encode_hvc_ret_code Succ))
                             R2 hd)
           end
        end
  in
  unpack_hvc_result_normal s comp.


Definition get_memory_descriptor (t : transaction) : VMID * (gset PID) :=
  match t with
  | (_, r, m, _, _) =>(r, m)
  end.

Definition get_transaction_type (t : transaction) : transaction_type :=
  match t with
  | (_, _, _, ty, _) => ty
  end.

Definition retrieve (s : state) : exec_mode * state :=
  let comp :=
      handle <- lift_option (get_reg s R1) ;;;
      trn <- lift_option_with_err (get_transaction s handle) InvParam ;;;
      match trn with
         | (vs, vr, ps, ty, b) =>
           let v := (get_current_vm s) in
           match bool_decide (v = vr), b with
           | true, false =>
             s' <- (write_retrieve_msg s (get_rx_pid s @ v) handle trn) ;;;
             match ty with
             | Sharing | Lending =>
                 unit  (update_reg
                          (update_page_table_global grant_access (update_transaction s' handle (vs, vr, ps, ty, true)) v ps)
                          R0 (encode_hvc_ret_code Succ))
             | Donation =>
                 unit  (update_reg
                          (update_page_table_global update_ownership
                          (update_page_table_global grant_access (remove_transaction s' handle) v ps) v ps)
                          R0 (encode_hvc_ret_code Succ))
             end
           | _ , _ => throw Denied
           end
      end
  in
  unpack_hvc_result_normal s comp.

Definition relinquish (s : state) : exec_mode * state :=
  let comp :=
    h <- lift_option (get_reg s R1) ;;;
    trn <- lift_option_with_err (get_transaction s h) InvParam ;;;
    let ps := trn.1.1.2 in
    let v := (get_current_vm s) in
      s' <- (match trn with
             | (vs, r, ps, ty, b) =>
                 if b && bool_decide (v = r)
                 then unit (update_transaction s h (vs, r, ps, ty, false))
                 else throw Denied
             end) ;;;
      unit (update_reg (update_page_table_global revoke_access s' v ps) R0 (encode_hvc_ret_code Succ))
  in
  unpack_hvc_result_normal s comp.

Definition reclaim (s : state) : exec_mode * state :=
  let comp :=
      handle <- lift_option (get_reg s R1) ;;;
      trn <- lift_option_with_err (get_transaction s handle) InvParam ;;;
      ps <- unit ((get_memory_descriptor trn).2);;;
      v <- unit (get_current_vm s) ;;;
      if bool_decide (trn.1.1.1.1 = v) && (negb trn.2)
      then
        match trn.1.2 with
        | Sharing =>
            unit (update_reg
                    (remove_transaction (update_page_table_global flip_excl s v ps) handle)
                    R0 (encode_hvc_ret_code Succ))
        | Lending | Donation =>
            unit (update_reg
                    (remove_transaction (update_page_table_global grant_access s v ps) handle)
                    R0 (encode_hvc_ret_code Succ))
        end
      else throw Denied
  in
  unpack_hvc_result_normal s comp.

Definition is_primary (st : state) : bool :=
  bool_decide ((get_current_vm st) = V0).

Definition is_secondary (st : state) : bool :=
  negb (is_primary st).

Definition run (s : state) : exec_mode * state :=
  let comp :=
    if is_primary s
      then
      r <- lift_option (get_reg s R1) ;;;
      id <- lift_option_with_err (decode_vmid r) InvParam ;;;
        unit (s, id)
      else
        throw Denied
  in
  unpack_hvc_result_yield s comp.

Program Definition yield (s : state) : exec_mode * state :=
  let comp :=
      let s' := (update_reg_global s V0 R0
                                   (encode_hvc_func Yield))
      in
      if is_primary s
      then
        unit (s', V0)
      else
        unit ((update_reg_global s' V0 R1
                      (encode_vmid (get_current_vm s'))), V0)
  in
  unpack_hvc_result_yield s comp.

Definition send (s : state) : exec_mode * state :=
  let comp :=
      receiver <- lift_option (get_reg s R1) ;;;
      receiver' <- lift_option_with_err (decode_vmid receiver) InvParam ;;;
      _ <- (if bool_decide (receiver' = (get_current_vm s)) then throw InvParam else unit ()) ;;;
      l <- lift_option (get_reg s R2) ;;;
      st <- transfer_msg s (get_current_vm s) receiver' l ;;;
      if is_primary st
      then
        unit (st, V0)
      else    
        unit (update_reg_global (update_reg_global (update_reg_global st V0 R0 (encode_hvc_func Send))
                                                   V0 R1 receiver) V0 R2 l, V0)
  in
  unpack_hvc_result_yield s comp.

Definition wait (s : state) : exec_mode * state :=
  let comp :=
      if is_rx_ready s
      then
        l <- lift_option (get_rx_length s) ;;;
        n <- lift_option (get_rx_sender s) ;;;
        unit ((update_reg (update_reg (update_reg (empty_rx s) R0 (encode_hvc_func Send)) R1 l) R2 (encode_vmid n)), (get_current_vm s))
      else unit ((update_reg_global (update_reg_global s V0 R0 (encode_hvc_func Wait)) V0 R1
                      (encode_vmid (get_current_vm s))), V0)
  in
  unpack_hvc_result_yield s comp.

Definition poll (s : state) : exec_mode * state :=
  let comp :=
      if is_rx_ready s
      then
        l <- lift_option (get_rx_length s) ;;;
        n <- lift_option (get_rx_sender s) ;;;
        unit (update_reg (update_reg (update_reg (empty_rx s) R0 (encode_hvc_func Send)) R1 l) R2 (encode_vmid n))
      else throw Denied
  in
  unpack_hvc_result_normal s comp.

Definition hvc (s : state) : exec_mode * state :=
  let comp :=
    r0 <- lift_option (get_reg s R0) ;;;
  func <- lift_option_with_err (decode_hvc_func r0) InvParam ;;;
  unit (match func with
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
      | Poll => poll s
      end) in
    match comp with
    | inl err =>
        match err with
        | inl () => (FailI, s)
        | inr err' =>
            (ExecI, (update_incr_PC (update_reg
                                       (update_reg s R0 (encode_hvc_ret_code Error))
                                       R2 (encode_hvc_error err'))))
        end
    | inr o' => o'
  end.

Definition exec (i : instruction) (s : state) : exec_mode * state :=
  match i with
  | Nop => nop s
  | Mov dst (inl srcWord) => mov_word s dst srcWord
  | Mov dst (inr srcReg) => mov_reg s dst srcReg
  | Ldr dst src => ldr s dst src
  | Str src dst => str s src dst
  | Add op1 op2 => add s op1 op2
  | Sub op1 op2 => sub s op1 op2
  | Mult op1 op2 => mult s op1 op2
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
| step_exec_fail_invalid_pc:
    forall st a,
      get_reg st PC = Some a ->
      read_memory st a = None ->
      step ExecI st FailI st
| step_exec_fail_invalid_instr:
    forall st a w,
      get_reg st PC = Some a ->
      read_memory st a = Some w ->
      decode_instruction w = None ->
      step ExecI st FailI st
| step_exec_normal:
    forall st a w i c,
      get_reg st PC = Some a ->
      read_memory st a = Some w ->
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

Definition scheduler : state → nat → bool:=
λ σ i,  bool_decide ((fin_to_nat (get_current_vm σ)) = i).

End lang.
