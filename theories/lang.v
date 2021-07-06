From stdpp Require Import gmap fin_maps list countable fin mapset fin_map_dom listset_nodup vector.
From HypVeri Require Export machine monad.

Import MonadNotation.
Import Option.
Import Sum.
Open Scope monad_scope.

Section lang.
Context `{MachineParams : !MachineParameters}.
Context `(HypervisorParams : !HypervisorParameters).
Context `{InstrSerial :!InstructionSerialization}.
(* State *)

Definition mem : Type :=
  gmap addr word.

Definition reg_file : Type :=
  gmap reg_name word.

Definition vmid : Type :=
  fin vm_count.

Definition pid : Type :=
  fin page_count.

Definition page_table : Type :=
  gmap pid permission.

Definition tx_buffer : Type :=
  pid.

Definition rx_buffer : Type :=
  (pid * fin page_size * option vmid).

Definition mail_box : Type :=
  (tx_buffer * rx_buffer).

Definition current_vm := vmid.

Definition transaction : Type :=
  vmid (* sender *)
  * word (*flag *)
  * word (* tag *)
  * gset vmid
  * vec (listset_nodup pid) vm_count
  * transaction_type.

Definition handle := word.

Definition transactions : Type :=
  gmap handle transaction.

Definition state : Type :=
  vec reg_file vm_count * vec mail_box vm_count * vec page_table vm_count * current_vm * mem * transactions.

(* Getters *)

Definition get_current_vm (st : state) : current_vm :=
  snd (fst (fst st)).

Definition get_mem (st : state) : mem :=
  snd (fst st).

Definition get_transactions (st : state) : transactions :=
  snd st.

Definition get_reg_files (st : state) : vec reg_file vm_count :=
  fst (fst (fst (fst (fst st)))).

Definition get_vm_reg_file (st : state) (v : vmid) : reg_file :=
  (get_reg_files st) !!! v.

Definition get_mail_boxes (st : state) : vec mail_box vm_count :=
  snd (fst (fst (fst (fst st)))).

Definition get_vm_mail_box (st : state) (v : vmid) : mail_box :=
  (get_mail_boxes st) !!! v.

Definition get_page_tables (st : state) : vec page_table vm_count :=
  snd (fst (fst (fst st))).

Definition get_vm_page_table (st : state) (v : vmid) : page_table :=
  (get_page_tables st) !!! v.

(* Conf *)

Inductive exec_mode : Type :=
| ExecI
| HaltI
| FailI.

(* Aux funcs *)

Definition check_perm_page (st : state) (v : vmid) (p : pid) (pm : permission) : bool :=
  match (get_vm_page_table st v) !! p with
  | Some p' =>
    match (decide (pm = p')) with
    | left _ => true
    | right _ => false
    end
  | _ => false
  end.

Definition check_perm_addr (st : state) (v : vmid) (a : addr) (p : permission) : bool :=
  check_perm_page st v (mm_translation a) p.

Definition check_access_page (st : state) (v : vmid) (p : pid) : bool :=
  match (get_vm_page_table st v) !! p with
  | Some p' => is_accessible p'
  | _ => false
  end.

Definition check_access_addr (st : state) (v : vmid) (a : addr) : bool :=
  check_access_page st v (mm_translation a).

Definition check_ownership_page (st : state) (v : vmid) (p : pid) : bool :=
  match (get_vm_page_table st v) !! p with
  | Some p' => is_owned p'
  | _ => false
  end.

Definition check_ownership_addr (st : state) (v : vmid) (a : addr) : bool :=
  check_ownership_page st v (mm_translation a).

Definition update_reg_global (st : state) (v : vmid) (r : reg_name) (w : word) : state :=
  (vinsert v (<[r:=w]>(get_vm_reg_file st v)) (get_reg_files st), (get_mail_boxes st), (get_page_tables st),
   get_current_vm st,
   get_mem st, get_transactions st).

Definition update_reg (st : state) (r : reg_name) (w : word) : state :=
  update_reg_global st (get_current_vm st) r w.

Definition get_reg_global (st : state) (v : vmid) (r : reg_name) : option word :=
  (get_vm_reg_file st v) !! r.

Definition get_reg (st : state) (r : reg_name) : option word :=
  get_reg_global st (get_current_vm st) r.

Definition update_page_table_global (st : state) (v : vmid) (p : pid) (pm : permission) : state :=
  (get_reg_files st, get_mail_boxes st, vinsert v (<[p:=pm]>(get_vm_page_table st v)) (get_page_tables st),
   get_current_vm st,
   get_mem st, get_transactions st).

Definition update_page_table (st : state) (p : pid) (pm : permission) : state :=
  update_page_table_global st (get_current_vm st) p pm.

Definition get_page_table_global (st : state) (v : vmid) (p : pid) : option permission :=
  (get_vm_page_table st v) !! p.

Definition get_page_table (st : state) (p : pid) : option permission :=
  get_page_table_global st (get_current_vm st) p.
                
Definition update_memory_unsafe (st : state) (a : addr) (w : word) : state :=
  (get_reg_files st, get_mail_boxes st, get_page_tables st, get_current_vm st, <[a:=w]>(get_mem st), get_transactions st).

Definition update_memory (st : state) (a : addr) (w : word) : option state :=
  if check_access_addr st (get_current_vm st) a
  then unit (update_memory_unsafe st a w)
  else None.

Definition get_memory_unsafe (st : state) (a : addr) : option word :=
  (get_mem st) !! a.

Definition get_memory (st : state) (a : addr) : option word :=
  if check_access_addr st (get_current_vm st) a
  then get_memory_unsafe st a
  else None.

Definition try_incr_word (n : word) (p : nat) : option word :=
  match (nat_lt_dec (n + p) word_size) with
  | left l => Some (@nat_to_fin (n + p) _ l)
  | _ => None
  end.

Lemma fin_max {n : nat} (x y : fin n) : fin n.
Proof.
  destruct (Fin.to_nat x);
    destruct (Fin.to_nat y);
    destruct (x <? y); auto.
Defined.

Definition addr_offset (base : addr) (offset : nat) : option addr :=
  try_incr_word base offset.

Definition get_memory_with_offset (st : state) (base : addr) (offset : nat) : option word :=
  addr <- addr_offset base offset ;;;
  get_memory st addr.

Program Definition word_add (w:word) (n:nat):word:=
  (@nat_to_fin (((fin_to_nat w)+n) mod word_size) _ _).
Next Obligation.
Proof.
  intros.
  apply mod_bound_pos.
  lia.
  pose proof word_size_at_least.
  lia.
  Defined.

Infix "+w" := word_add (at level 70, no associativity).

Program Definition update_offset_PC (st : state) (dir : bool) (offset : nat) :  state :=
  match ((get_vm_reg_file st (get_current_vm st)) !! PC) with
   | Some v =>
          if dir
          then
          (update_reg st PC (v +w offset))
          else
          (update_reg st PC (@nat_to_fin ((v - offset) mod word_size) _ _)) (* TODO: v'-offset = 0 if offset> v'*)
   | None => st
   end.

Next Obligation.
Proof.
  intros.
  apply mod_bound_pos.
  lia.
  pose proof word_size_at_least.
  lia.
  Defined.

Definition update_incr_PC (st : state) : state :=
  update_offset_PC st true 1.

Definition is_valid_PC (st : state) : option bool :=
  w <- get_reg st PC ;;;
  (* w' <- addr_offset w 1 ;;; *)
  (* Some (andb (check_access_addr st (get_current_vm st) w) (check_access_addr st (get_current_vm st) w')). *)
  Some (check_access_addr st (get_current_vm st) w).

Definition option_state_unpack (oldSt : state) (newSt : option state) : exec_mode * state :=
  match newSt with
  | None => (FailI, oldSt)
  | Some s => (ExecI, s)
  end.



Definition mov_word (s : state) (dst : reg_name) (src : word) : exec_mode * state :=
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

Definition ldr (s : state) (dst : reg_name) (src : reg_name) : exec_mode * state :=
  let comp :=
      match (dst, src) with
      | (R _ _, R _ _) =>
        src' <- get_reg s src ;;;
        v <- get_memory s src' ;;;
        Some(update_incr_PC (update_reg s dst v))
      | _ => None
      end
  in
  (option_state_unpack s comp).

Definition str (s : state) (src : reg_name) (dst : reg_name) : exec_mode * state :=
  let comp :=
      match (src, dst) with
        | (R _ _, R _ _) =>
          src' <- get_reg s src ;;;
          dst' <- get_reg s dst ;;;
          m <- update_memory s dst' src' ;;;
          Some(update_incr_PC m)
        | _ => None
      end
  in
  (option_state_unpack s comp).

Ltac solveWordSize :=
  pose proof word_size_at_least as G;
  unfold word_size_lower_bound in G;
  lia.

Ltac solveRegCount :=
  pose proof reg_count_at_least as G;
  unfold reg_count_lower_bound in G;
  lia.

Program Definition cmp_word (s : state) (arg1 : reg_name) (arg2 : word) : exec_mode * state :=
  let comp :=
      arg1' <- get_reg s arg1 ;;;
      m <- match (nat_lt_dec (fin_to_nat arg1') (fin_to_nat arg2)) with
           | left _ => Some (update_reg s NZ (@nat_to_fin 1 word_size _))
           | right _ => Some (update_reg s NZ (@nat_to_fin 0 word_size _))
           end ;;;
      Some(update_incr_PC m)
  in
  (option_state_unpack s comp).
Solve Obligations with solveWordSize.

Program Definition cmp_reg (s : state) (arg1 : reg_name) (arg2 : reg_name) : exec_mode * state :=
  let comp :=
      arg1' <- get_reg s arg1 ;;;
      arg2' <- get_reg s arg2 ;;;
      m <- match (nat_lt_dec (fin_to_nat arg1') (fin_to_nat arg2')) with
           | left _ => Some (update_reg s NZ (@nat_to_fin 1 word_size _))
           | right _ => Some (update_reg s NZ (@nat_to_fin 0 word_size _))
           end ;;;
      Some(update_incr_PC m)
  in
  (option_state_unpack s comp).
Solve Obligations with solveWordSize.

Definition jnz (s : state) (arg : reg_name) : exec_mode * state :=
  let comp :=
      arg' <- get_reg s arg ;;;
      nz <- get_reg s NZ ;;;
      match (fin_to_nat nz) with
      | 0 => Some (update_reg s PC arg')
      | _ => Some(update_incr_PC s)
      end
  in
  (option_state_unpack s comp).

Definition jmp (s : state) (arg : reg_name) : exec_mode * state :=
  let comp := (fun x => update_reg s PC x) <$> (get_reg s arg)
  in
  (option_state_unpack s comp).

Definition fail (s : state) : exec_mode * state :=
  (FailI, s).

Definition halt (s : state) : exec_mode * state :=
  (HaltI, s).

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

Program Definition unpack_hvc_result_normal (o : state) (q : hvc_result state) : exec_mode * state :=
  match q with
  | inl err =>
    match err with
    | inl () => (FailI, o)
    | inr err' =>
      (ExecI, (update_incr_PC (update_reg
                        (update_reg o
                                    (R 0 _)
                                    (encode_hvc_ret_code Error))
                        (R 2 _)
                        (encode_hvc_error err'))))
    end
  | inr o' => (ExecI, update_incr_PC o')
  end.
Solve Obligations with solveRegCount.

Definition update_current_vmid (st : state) (v : vmid) : state :=
  (get_reg_files st, get_mail_boxes st, get_page_tables st, v, get_mem st, get_transactions st).

Program Definition unpack_hvc_result_yield (o : state) (q : hvc_result (state * vmid)) : exec_mode * state :=
  match q with
  | inl err =>
    match err with
    | inl () => (FailI, o)
    | inr err' =>
       (ExecI, update_incr_PC (update_reg
                              (update_reg o
                                          (R 0 _)
                                          (encode_hvc_ret_code Error))
                              (R 2 _)
                              (encode_hvc_error err')))
    end
  | inr (o', id) => (ExecI, (update_current_vmid  (update_incr_PC o') id))
  end.
Solve Obligations with solveRegCount.

(* ! depends on a constant ! *)
Lemma at_least_one_addr_in_page (p : pid) : vec word (S (page_size - 1)).
Proof.
  pose proof page_size_sanity as H.
  pose proof word_size_at_least as H'.
  pose proof (mm_translation_inv p) as H''.
  destruct page_size.
  - simpl in H. 
    unfold word_size_lower_bound in H'.
    rewrite <- H in H'.
    exfalso.
    apply (Nat.nlt_0_r 15 H').
  - simpl in *.
    rewrite <- minus_n_O.
    exact H''.
Qed.

Definition get_tx_base_addr_global (st : state) (v : vmid) : word :=
  match get_vm_mail_box st v with
    | (pid, _) => (@Vector.hd word (page_size - 1) (at_least_one_addr_in_page pid))
  end.

Definition is_rx_ready_global (st : state) (v : vmid) : bool :=
  match get_vm_mail_box st v with
  | (_, (_, _, Some _)) => true
  | _ => false
  end.

Definition is_rx_ready (st : state) : bool :=
  is_rx_ready_global st (get_current_vm st).

Definition get_rx_sender_global (st : state) (v : vmid) : option vmid :=
  match get_vm_mail_box st v with
  | (_, (_, Some v')) => Some v'
  | _ => None
  end.

Definition get_rx_sender (st : state) : option vmid :=
  get_rx_sender_global st (get_current_vm st).

Definition get_rx_base_addr_global (st : state) (v : vmid) : option word :=
  match get_vm_mail_box st v with
  | (_, (pid, _, Some _)) => Some (@Vector.hd word (page_size - 1) (at_least_one_addr_in_page pid))
  | _ => None
  end.

Definition get_rx_base_addr (st : state) : option word :=
  get_rx_base_addr_global st (get_current_vm st).

Definition empty_rx_global (st : state) (v : vmid) : option state :=
  match get_vm_mail_box st v with
  | (txAddr, (rxAddr, len, Some _)) =>
    Some (get_reg_files st,
          vinsert v (txAddr, (rxAddr, len, None)) (get_mail_boxes st),
          get_page_tables st,
          get_current_vm st,
          get_mem st, get_transactions st)
  | _ => None
  end.

Definition empty_rx (st : state) : option state :=
  empty_rx_global st (get_current_vm st).

Definition copy_from_addr_to_addr_unsafe (st : state) (src dst : addr) : option state :=
  w <- get_memory_unsafe st src ;;;
  Some (update_memory_unsafe st dst w).

Definition copy_page_unsafe (st : state) (src dst : pid) : option state :=
  foldr (fun x s =>
           match x with
           | (a, b) =>
             (@bind option _ _ _ state state s (fun y => copy_from_addr_to_addr_unsafe y a b))
           end)
        (Some st)
        (vzip_with (fun x y => (x, y)) (mm_translation_inv src) (mm_translation_inv dst)).

Definition fin_coerce {n m : nat} (i : fin n) (lt : fin_to_nat i < m) : fin m :=
  Fin.of_nat_lt lt.  

Program Definition transfer_msg_unsafe (st : state) (l : word) (v : vmid) (r : vmid) : hvc_result state :=
  match decide (l < page_size) with
  | left p =>
    match get_vm_mail_box st v with
    | (txPid, _) =>
      match get_vm_mail_box st r with
      | (tx, ((rxPid, _), _)) =>
        st' <- lift_option (copy_page_unsafe st txPid rxPid) ;;;
        unit (get_reg_files st,
              vinsert r (tx, (rxPid, _, Some v)) (get_mail_boxes st),
              get_page_tables st,
              get_current_vm st,
              get_mem st, get_transactions st)
      end
    end
  | right _ => throw InvParam
  end.
Next Obligation.
  intros; exact (@fin_coerce word_size page_size l p).
Defined.  

Definition transfer_msg (st : state) (l : word) (r : vmid) : hvc_result state :=
  transfer_msg_unsafe st l (get_current_vm st) r.

Definition fresh_handle_helper (val : handle) (acc : hvc_result handle) : hvc_result handle :=
  match (try_incr_word val 1) with
  | None => throw NoMem
  | Some val' =>
    match acc with
    | inl (inl ()) => unit val
    | inl _ => acc
    | inr acc' => unit (fin_max val' acc')
    end
  end.

(* TODO: pick the least *free* handle *)
Definition fresh_handle (m : gmap handle transaction) : hvc_result handle := 
  set_fold fresh_handle_helper (inl (inl ())) (@dom (gmap handle transaction) (gset handle) gset_dom m).

Definition memory_region_descriptor : Type :=
  vmid (* receiver *) * list pid (* pids *).

Definition transaction_descriptor : Type :=
  vmid (* Sender *) * option handle (* Handle *) * word (* Tag *)
  * word (* Flag *)
  * word (* Counter *)
  * vec (listset_nodup pid) vm_count (* Receivers *).

Definition memory_regions_to_vec (md : listset_nodup memory_region_descriptor) : vec (listset_nodup pid) vm_count :=
  set_fold (fun v acc => match decide (NoDup v.2) with
                         | left l => vinsert v.1 (ListsetNoDup v.2 l) acc
                         | right r => acc
                         end) (vreplicate vm_count empty) md.

Definition parse_memory_region_descriptor (st : state) (base : addr) : option memory_region_descriptor :=
  l <- get_memory_with_offset st base 0 ;;;
  r <- get_memory_with_offset st base 1 ;;;
  r' <- decode_vmid r ;;;
  ls' <- sequence_a (foldl (fun acc v => cons (bind (get_memory_with_offset st base (2 + v)) decode_pid) acc) nil (seq 0 (fin_to_nat l))) ;;;
  unit (r', ls').

Definition parse_memory_region_descriptors (st : state) (base : addr) (count : nat) : option (listset_nodup memory_region_descriptor) :=
  ls' <- sequence_a (foldl (fun acc v =>
                     cons (bind (addr_offset base v) (parse_memory_region_descriptor st)) acc) (@nil (option memory_region_descriptor)) (seq 0 count)) ;;;
 (match NoDup_dec ls' with
    | left prf => unit (ListsetNoDup ls' prf)
    | right prf => None
  end).

(* TODO: Prop version, reflection *)
Definition parse_transaction_descriptor (st : state) (wl : word) (base : addr) (ty : transaction_type) : option transaction_descriptor :=
  (* Main fields *)
  vs <- get_memory_with_offset st base 0 ;;;
  wf <- get_memory_with_offset st base 1 ;;;
  wh <- get_memory_with_offset st base 2 ;;;
  wt <- get_memory_with_offset st base 3 ;;;
  wc <- get_memory_with_offset st base 4 ;;;
  memDescrBase <- addr_offset base 5 ;;;
  memDescrs <- parse_memory_region_descriptors st memDescrBase (fin_to_nat wc) ;;;
  (* Validate length *)
  vs' <- decode_vmid vs ;;;                                             
  unit (vs', (if (fin_to_nat wh) =? 0 then None else Some wh), wt, wf, wc, memory_regions_to_vec memDescrs).

Definition validate_transaction_descriptor (wl : word) (ty : transaction_type)
           (t : transaction_descriptor) : hvc_result () :=
  match t with
  | (vs', h, wt, wf, wc, gm) =>
    _ <- lift_option_with_err (
        _ <- @bool_check_option True (negb (fin_to_nat wc =? 0)) ;;;
        _ <- @bool_check_option True (fin_to_nat wc =? length gm) ;;;
        @bool_check_option True (match ty with
                                     | Donation => (fin_to_nat wc) =? 1
                                     | _ => true
                                 end)) InvParam ;;;
    unit tt
  end.

Definition insert_transaction (st : state) (h : handle) (t : transaction) : state :=
  (get_reg_files st, get_mail_boxes st, get_page_tables st, get_current_vm st, get_mem st, <[h:=t]>(get_transactions st)).

Program Definition new_transaction (st : state) (vid : vmid)
           (tt : transaction_type)
           (flag tag : word)
           (m : vec (listset_nodup pid) vm_count)  : hvc_result state :=
  if foldr (fun v acc =>
              andb acc
                   (set_fold (fun v' acc' =>
                                andb acc' (check_ownership_page st vid v'))
                             true
                             v))
           true
           m
  then
    h <- fresh_handle (get_transactions st) ;;;
    unit (insert_transaction st h (vid, flag, tag, empty, m, tt))
  else throw Denied.

Definition get_transaction (st : state) (h : handle) : option transaction :=
  (get_transactions st) !! h.

Definition remove_transaction (s : state) (h : handle) : state :=
  (get_reg_files s, get_mail_boxes s, get_page_tables s, get_current_vm s, get_mem s, delete h (get_transactions s)).

Definition new_transaction_from_descriptor (st : state) (ty : transaction_type) (td : transaction_descriptor) : hvc_result state :=
  match td with
  | (s, None, t, f, wc, rs) => new_transaction st s ty f t rs
  | _ => throw InvParam
  end.

Definition new_transaction_from_descriptor_in_tx_unsafe (st : state) (v : vmid) (wl : word) (ty : transaction_type) : hvc_result state :=
  if (page_size <? fin_to_nat wl)
  then throw InvParam
  else
    td <- lift_option (parse_transaction_descriptor st wl (get_tx_base_addr_global st v) ty) ;;;
    new_transaction_from_descriptor st ty td.


Definition is_primary (st : state) : bool :=
  (get_current_vm st) =? 0.

Definition is_secondary (st : state) : bool :=
  negb (is_primary st).

Program Definition run (s : state) : exec_mode * state :=
  let comp :=
      r <- lift_option (get_reg s (R 1 _)) ;;;
      id <- lift_option_with_err (decode_vmid r) InvParam ;;;
      if is_primary s
      then
        unit (s, id)
      else
        throw InvParam
  in
  unpack_hvc_result_yield s comp.
Solve Obligations with solveRegCount.
  
Program Definition yield (s : state) : exec_mode * state :=
  let comp :=
      let s' := (update_reg s (R 0 _) (encode_hvc_ret_code Succ))
      in
      if is_primary s'
      then
        unit (s', (@nat_to_fin 0 vm_count vm_count_pos))
      else
        unit ((update_reg s' (R 1 _) (encode_vmid (get_current_vm s'))), (@nat_to_fin 0 vm_count vm_count_pos))
  in
  unpack_hvc_result_yield s comp.
Solve Obligations with solveRegCount.

Definition verify_perm_transaction (s : state) (p : permission) (td : transaction_descriptor) : bool :=
  match td with
  | (_, _, _, _, m) => foldr
                         (fun v acc => andb acc (set_fold (fun v' acc' => andb acc' (check_perm_page s (get_current_vm s) v' p)) true v))
                         true
                         m
  end.

Program Definition share (s : state) : exec_mode * state :=
    let comp :=
        r <- lift_option (get_reg s (R 1 _)) ;;;
        m <- (if (page_size <? fin_to_nat r)
              then throw InvParam
              else
                td <- lift_option (parse_transaction_descriptor s r (get_tx_base_addr_global s (get_current_vm s)) Sharing) ;;;
                _ <- validate_transaction_descriptor r Sharing td ;;;
                if (verify_perm_transaction s (Owned, ExclusiveAccess) td)
                then (bind (new_transaction_from_descriptor s Sharing td) (fun x => unit (x, td)))
                else throw Denied) ;;;
        match m with
        | (m', td) =>
          match td with
          | (_, gm) =>
            match (foldr (fun v acc => union v acc) empty gm) with
            | ListsetNoDup ls prf =>
              unit (update_reg
                      (foldr (fun v' acc' => update_page_table acc' v' (Owned, SharedAccess)) m' ls)
                      (R 0 _)
                      (encode_hvc_ret_code Succ))
            end
          end
        end
    in 
    unpack_hvc_result_normal s comp.
Solve Obligations with solveRegCount.

Program Definition lend (s : state) : exec_mode * state :=
  let comp :=
      r <- lift_option (get_reg s (R 1 _)) ;;;
      m <- (if (page_size <? fin_to_nat r)
            then throw InvParam
            else
              td <- lift_option (parse_transaction_descriptor s r (get_tx_base_addr_global s (get_current_vm s)) Lending) ;;;
              _ <- validate_transaction_descriptor r Sharing td ;;;
              if (verify_perm_transaction s (Owned, ExclusiveAccess) td)
              then bind (new_transaction_from_descriptor s Lending td)
                        (fun x => unit (x, td))
              else throw Denied) ;;;
      match m with
      | (m', td) =>
        match td with
        | (_, gm) =>
          match foldr (fun v acc => union v acc) empty gm with
          | ListsetNoDup ls prf =>
            unit (update_reg
                    (foldr (fun v' acc' => update_page_table acc' v' (Owned, NoAccess)) m' ls)
                    (R 0 _)
                    (encode_hvc_ret_code Succ))
          end
        end
      end
  in 
  unpack_hvc_result_normal s comp.
Solve Obligations with solveRegCount.

Program Definition donate (s : state) : exec_mode * state :=
  let comp :=
      r <- lift_option (get_reg s (R 1 _)) ;;;
      m <- (if (page_size <? fin_to_nat r)
            then throw InvParam
            else
              td <- lift_option (parse_transaction_descriptor s r (get_tx_base_addr_global s (get_current_vm s)) Donation) ;;;
              _ <- validate_transaction_descriptor r Donation td ;;;
              if (verify_perm_transaction s (Owned, ExclusiveAccess) td)
              then bind (new_transaction_from_descriptor s Donation td)
                        (fun x => unit (x, td))
              else throw Denied) ;;;
      match m with
      | (m', td) =>
        match td with
        | (_, gm) =>
          match foldr (fun v acc => union v acc) empty gm with
          | ListsetNoDup ls prf =>
            unit (update_reg
                    (foldr (fun v' acc' => update_page_table acc' v' (NotOwned, NoAccess)) m' ls)
                    (R 0 _)
                    (encode_hvc_ret_code Succ))
          end
        end
      end
  in 
  unpack_hvc_result_normal s comp.
Solve Obligations with solveRegCount.

Definition toggle_transaction_retrieve (s : state) (h : handle) (v : vmid) : hvc_result state :=
  match get_transaction s h with
  | Some (vs, w1, w2, sr, vr, ty) =>
    match (vr !!! v) with
    | ListsetNoDup ls prf =>
      match ls with
      | nil => throw Denied
      | _ => if decide (v ∈ sr)
             then throw Denied
             else unit (get_reg_files s, get_mail_boxes s, get_page_tables s, get_current_vm s, get_mem s,
                       insert h (vs, w1, w2, union sr (singleton v), vr, ty) (get_transactions s))
      end
    end
  | _ => throw InvParam
  end.

Definition toggle_transaction_relinquish (s : state) (h : handle) (v : vmid) : hvc_result state :=
  match get_transaction s h with
  | Some (vs, w1, w2, sr, vr, ty) =>
    match (vr !!! v) with
    | ListsetNoDup ls prf =>
      match ls with
      | nil => throw Denied
      | _ => if decide (v ∈ sr)
             then unit (get_reg_files s, get_mail_boxes s, get_page_tables s, get_current_vm s, get_mem s,
                        insert h (vs, w1, w2, difference sr (singleton v), vr, ty) (get_transactions s))
             else throw Denied
      end
    end
  | _ => throw InvParam
  end.

Definition retrieve_transaction (s : state)
           (h : handle)
           (type : transaction_type)
           (receiversMap : vec (listset_nodup pid) vm_count) : hvc_result state :=
  m <- toggle_transaction_retrieve s h (get_current_vm s) ;;;
  match type with
  | Sharing =>
    unit (foldr (fun v' acc' =>
                   update_page_table acc' v' (NotOwned, SharedAccess))
                m
         (receiversMap !!! (get_current_vm s)))
  | Lending =>
    if decide (1 < foldr (fun v acc => acc + size v) 0 receiversMap)
    then unit (foldr (fun v' acc' =>
                        update_page_table acc' v' (NotOwned, SharedAccess))
                     m
                     (receiversMap !!! (get_current_vm s)))
    else unit (foldr (fun v' acc' =>
                        update_page_table acc' v' (NotOwned, ExclusiveAccess))
                     m
                     (receiversMap !!! (get_current_vm s)))
  | Donation =>
    unit (foldr (fun v' acc' =>
                   update_page_table acc' v' (Owned, ExclusiveAccess))
                m
                (receiversMap !!! (get_current_vm s)))
  end.

Definition relinquish_transaction (s : state)
           (h : handle)
           (receiversMap : vec (listset_nodup pid) vm_count) : hvc_result state :=
  s' <- toggle_transaction_relinquish s h (get_current_vm s) ;;;
  unit (foldr (fun v' acc' => update_page_table acc' v' (NotOwned, NoAccess)) s' (receiversMap !!! (get_current_vm s))).

Definition get_receivers (t : transaction) : vec (listset_nodup pid) vm_count :=
  match t with
  | (_, _, _, m, _) => m
  end.

Definition get_type (t : transaction) : transaction_type :=
  match t with
  | (_, _, _, _, ty) => ty
  end.

Program Definition retrieve (s : state) : exec_mode * state :=
  let comp :=
      handle <- lift_option (get_reg s (R 1 _)) ;;;
      trn <- lift_option_with_err (get_transaction s handle) InvParam ;;;
      retrieve_transaction s handle (get_type trn) (get_receivers trn)
  in
  unpack_hvc_result_normal s comp.
Solve Obligations with solveRegCount.

Program Definition relinquish (s : state) : exec_mode * state :=
  let comp :=
      handle <- lift_option (get_reg s (R 1 _)) ;;;
      trn <- lift_option_with_err (get_transaction s handle) InvParam ;;;
      relinquish_transaction s handle (get_receivers trn)
  in
  unpack_hvc_result_normal s comp.
Solve Obligations with solveRegCount.

Definition no_borrowers (s : state) (h : handle) (v : vmid) : bool :=
  match (get_transaction s h) with
  | None => true
  | Some (vs, w1, w2, sr, vr, ty) =>
    if decide (sr = empty)
    then false
    else true
  end.

Program Definition reclaim (s : state) : exec_mode * state :=
  let comp :=
      handle <- lift_option (get_reg s (R 1 _)) ;;;
      trn <- lift_option_with_err (get_transaction s handle) InvParam ;;;
      if no_borrowers s handle (get_current_vm s)
      then
        unit (foldr
                (fun v' acc' =>
                   update_page_table acc' v' (Owned, ExclusiveAccess))
                (remove_transaction s handle)
                ((get_receivers trn) !!! (get_current_vm s)))
      else throw Denied
  in
  unpack_hvc_result_normal s comp.
Solve Obligations with solveRegCount.

Program Definition send (s : state) : exec_mode * state :=
  let comp :=
      receiver <- lift_option (get_reg s (R 1 _)) ;;;
      receiver' <- lift_option_with_err (decode_vmid receiver) InvParam ;;;
      l <- lift_option (get_reg s (R 2 _)) ;;;                
      transfer_msg s l receiver'
  in
  unpack_hvc_result_normal s comp.
Solve Obligations with solveRegCount.

Definition wait (s : state) : exec_mode * state :=
  let comp :=
      if is_rx_ready s
      then unit (s, get_current_vm s)
      else unit (s, (@nat_to_fin 0 _ vm_count_pos))
  in
  unpack_hvc_result_yield s comp.

Program Definition hvc (s : state) : exec_mode * state :=
  match get_reg s (R 0 _) with
  | None => fail s
  | Some r0 =>
    match decode_hvc_func r0 with
    | None => fail s
    | Some func =>
      match func with
      | Run => run s
      | Yield => yield s
      | Share => share s
      | Lend => lend s
      | Donate => donate s
      | Retrieve => retrieve s
      | Relinquish => relinquish s
      | Reclaim => reclaim s
      | Send => send s
      | Wait => wait s
      end
    end
  end.
Solve Obligations with solveRegCount.

Definition exec (i : instruction) (s : state) : exec_mode * state :=
  match i with
  | Mov dst (inl srcWord) => mov_word s dst srcWord
  | Mov dst (inr srcReg) => mov_reg s dst srcReg
  | Ldr dst src => ldr s dst src
  | Str src dst => str s src dst
  | Cmp arg1 (inl arg2) => cmp_word s arg1 arg2
  | Cmp arg1 (inr arg2) => cmp_reg s arg1 arg2
  | Jnz arg => jnz s arg
  | Jmp arg => jmp s arg
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
      (* get_memory_with_offset st a 1 = Some w2 -> *)
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

End lang.
