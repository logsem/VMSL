From Coq Require Import ssreflect Bool Eqdep_dec Program.Equality.
From stdpp Require Import gmap fin_maps list binders strings countable fin mapset fin_map_dom listset_nodup.
From iris.prelude Require Import options.
From iris.algebra Require Import ofe.
From iris.program_logic Require Import language ectx_language ectxi_language.
From hypvis Require Import machine monad.

Import MonadNotation.
Import Option.
Open Scope monad_scope.

Context `(HypervisorParams : HypervisorParameters).

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
  (pid * option vmid).

Definition mail_box : Type :=
  (tx_buffer * rx_buffer).

Definition current_vm := vmid.

Definition vm_states : Type :=
  gmap vmid (reg_file * mail_box * page_table).

Definition transaction : Type :=
  vmid (* sender *)
  * word (*flag *)
  * word (* tag *)
  * gmap vmid (gmap pid bool)
  * transaction_type.

Definition handle := word.

Definition transactions : Type :=
  gmap handle transaction.

Definition state : Type :=
  vm_states * current_vm * mem * transactions.

(* Getters *)

Definition get_vm_states (st : state) : vm_states :=
  fst (fst (fst st)).

Definition get_current_vm (st : state) : current_vm :=
  snd (fst (fst st)).

Definition get_mem (st : state) : mem :=
  snd (fst st).

Definition get_transactions (st : state) : transactions :=
  snd st.

Definition get_vm_state (st : state) (v : vmid) : option (reg_file * mail_box * page_table) :=
  (get_vm_states st) !! v.

Definition get_vm_reg_file (st : state) (v : vmid) : option reg_file :=
  match get_vm_state st v with
  | None => None
  | Some a => Some (fst (fst a))
  end.

Definition get_vm_mail_box (st : state) (v : vmid) : option mail_box :=
  match get_vm_state st v with
  | None => None
  | Some a => Some (snd (fst a))
  end.

Definition get_vm_page_table (st : state) (v : vmid) : option page_table :=
  match get_vm_state st v with
  | None => None
  | Some a => Some (snd a)
  end.

(* Conf *)

Inductive exec_mode : Type :=
| ExecI
| NextI
| HaltI
| FailI.

Inductive control_mode : Type :=
| YieldM : vmid -> control_mode
| NormalM.

Definition conf : Type := exec_mode * state.

(* Aux funcs *)

Definition check_perm_page (st : state) (v : vmid) (p : pid) (pm : permission) : bool :=
  match (get_vm_page_table st v) with
  | None => false
  | Some pt =>
    match pt !! p with
    | Some p' =>
      match (decide (pm = p')) with
      | left _ => true
      | right _ => false
      end
    | _ => false
    end
  end.

Definition check_perm_addr (st : state) (v : vmid) (a : addr) (p : permission) : bool :=
  check_perm_page st v (mm_translation a) p.

Definition check_access_page (st : state) (v : vmid) (p : pid) : bool :=
  match get_vm_page_table st v with
  | None => false
  | Some pt =>
    match pt !! p with
    | Some p' => is_accessible p'
    | _ => false
    end
  end.

Definition check_access_addr (st : state) (v : vmid) (a : addr) : bool :=
  check_access_page st v (mm_translation a).

Definition check_ownership_page (st : state) (v : vmid) (p : pid) : bool :=
  match get_vm_page_table st v with
  | None => false
  | Some pt =>
    match pt !! p with
    | Some p' => is_owned p'
    | _ => false
    end
  end.

Definition check_ownership_addr (st : state) (v : vmid) (a : addr) : bool :=
  check_ownership_page st v (mm_translation a).

Definition update_general_reg_global (st : state) (v : vmid) (r : reg_name) (w : word) : option state :=
  match r with
  | PC => None
  | NZ => None
  | R n fin =>
    match get_vm_state st v with
    | None => None
    | Some (rf, mb, pt) =>
      Some (<[v:=(<[r:=w]>rf, mb, pt)]>(get_vm_states st),
            get_current_vm st,
            get_mem st, get_transactions st)
    end
  end.

Definition update_general_reg (st : state) (r : reg_name) (w : word) : option state :=
  update_general_reg_global st (get_current_vm st) r w.

Definition update_sys_reg_global (st : state) (v : vmid) (r : reg_name) (w : word) : option state :=
  match r with
  | R n fin => None
  | _ => match get_vm_state st v with
         | None => None
         | Some (rf, mb, pt) =>
           Some (<[v:=(<[r:=w]>rf, mb, pt)]>(get_vm_states st),
                 get_current_vm st,
                 get_mem st, get_transactions st)
         end
  end.

Definition update_sys_reg (st : state) (r : reg_name) (w : word) : option state :=
  update_sys_reg_global st (get_current_vm st) r w.

Definition get_reg_global (st : state) (v : vmid) (r : reg_name) : option word :=
  match get_vm_reg_file st v with
  | None => None
  | Some rf => rf !! r 
  end.

Definition get_reg (st : state) (r : reg_name) : option word :=
  get_reg_global st (get_current_vm st) r.

Definition update_page_table_global (st : state) (v : vmid) (p : pid) (pm : permission) : option state :=
  match get_vm_state st v with
  | None => None
  | Some (rf, mb, pt) =>
    Some (<[v:=(rf, mb, <[p:=pm]>pt)]>(get_vm_states st),
          get_current_vm st,
          get_mem st, get_transactions st)
  end.

Definition update_page_table (st : state) (p : pid) (pm : permission) : option state :=
  update_page_table_global st (get_current_vm st) p pm.

Definition get_page_table_global (st : state) (v : vmid) (p : pid) : option permission :=
  match get_vm_page_table st v with
  | None => None
  | Some pt => pt !! p
  end.

Definition get_page_table (st : state) (p : pid) : option permission :=
  get_page_table_global st (get_current_vm st) p.
                
Definition update_memory_unsafe (st : state) (a : addr) (w : word) : state :=
  (get_vm_states st, get_current_vm st, <[a:=w]>(get_mem st), get_transactions st).

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

Definition get_tx_base_addr_global (st : state) (v : vmid) : option word :=
  match get_vm_state st v with
  | Some (rf, (pid, _), pt) =>
    Some (@Vector.hd word (page_size - 1) (at_least_one_addr_in_page pid))
  | _ => None
  end.

Definition is_rx_ready_global (st : state) (v : vmid) : bool :=
  match get_vm_state st v with
  | Some (rf, (_, (_, Some _)), pt) => true
  | _ => false
  end.

Definition is_rx_ready (st : state) : bool :=
  is_rx_ready_global st (get_current_vm st).

Definition get_rx_sender_global (st : state) (v : vmid) : option vmid :=
  match get_vm_state st v with
  | Some (rf, (_, (_, Some v')), pt) => Some v'
  | _ => None
  end.

Definition get_rx_sender (st : state) : option vmid :=
  get_rx_sender_global st (get_current_vm st).

Definition get_rx_base_addr_global (st : state) (v : vmid) : option word :=
  match get_vm_state st v with
  | Some (rf, (_, (pid, Some _)), pt) => Some (@Vector.hd word (page_size - 1) (at_least_one_addr_in_page pid))
  | _ => None
  end.

Definition get_rx_base_addr (st : state) : option word :=
  get_rx_base_addr_global st (get_current_vm st).

Definition empty_rx_global (st : state) (v : vmid) : option state :=
  match get_vm_state st v with
  | Some (rf, (txAddr, (rxAddr, Some _)), pt) =>
    Some (<[v:=(rf, (txAddr, (rxAddr, None)), pt)]>(get_vm_states st),
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
             (@bind option _ state state s (fun y => copy_from_addr_to_addr_unsafe y a b))
           end)
        (Some st)
        (vzip_with (fun x y => (x, y)) (mm_translation_inv src) (mm_translation_inv dst)).

Definition transfer_msg_unsafe (st : state) (v : vmid) (r : vmid) : option state :=
  match get_vm_state st v with
  | Some (_, (txPid, _), _) =>
    match get_vm_state st r with
    | Some (rf, (_, (rxPid, _)), pt) =>
      copy_page_unsafe st txPid rxPid
    | _ => None
    end
  | _ => None
  end.

Definition transfer_msg (st : state) (r : vmid) : option state :=
  transfer_msg_unsafe st (get_current_vm st) r.

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

Definition fresh_handle_helper (val : handle) (acc : option handle) : option handle :=
  match (try_incr_word val 1) with
  | None => None
  | Some val' => match acc with
                 | None => Some val'
                 | Some acc' => Some (fin_max val' acc')
                 end
  end.

(* TODO: pick the least *free* handle *)
Definition fresh_handle (m : gmap handle transaction) : option handle := 
  set_fold fresh_handle_helper None (@dom (gmap handle transaction) (gset handle) gset_dom m).

Definition memory_region_descriptor : Type :=
  word (* length *) * vmid (* receiver *) * list pid (* pids *).  

(* It would make a lot of things simplier... *)
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

Definition transaction_descriptor : Type :=
  vmid (* Sender *) * option handle (* Handle *) * word (* Tag *)
  * word (* Flag *)
  * gmap vmid (listset_nodup pid) (* Receivers *).

Definition memory_regions_to_gmap (md : listset_nodup memory_region_descriptor) : gmap vmid (listset_nodup pid) :=
  set_fold (fun v acc => match decide (NoDup (snd v)) with
                         | left l => map_insert (snd (fst v)) (ListsetNoDup v.2 l) acc
                         | right r => acc
                         end) empty md.

Definition addr_offset (base : addr) (offset : nat) : option addr :=
  try_incr_word base offset.

Definition get_memory_with_offset (st : state) (base : addr) (offset : nat) : option word :=
  addr <- addr_offset base offset ;;;
  get_memory st addr.

Definition parse_memory_region_descriptor (st : state) (base : addr) : option memory_region_descriptor :=
  l <- get_memory_with_offset st base 0 ;;;
  r <- get_memory_with_offset st base 1 ;;;
  r' <- decode_vmid r ;;;
  ls' <- sequence_a (foldl (fun acc v => cons (bind (get_memory_with_offset st base (2 + v)) decode_pid) acc) nil (seq 0 (fin_to_nat l))) ;;;
  unit (l, r', ls').

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
  vs' <- decode_vmid vs ;;;
  wf <- get_memory_with_offset st base 1 ;;;
  wh <- get_memory_with_offset st base 2 ;;;
  wt <- get_memory_with_offset st base 3 ;;;
  wc <- get_memory_with_offset st base 4 ;;;
  memDescrBase <- addr_offset base 5 ;;;
  memDescrs <- parse_memory_region_descriptors st memDescrBase (fin_to_nat wc) ;;;
  (* Validate length *)                                          
  _ <- addr_offset base (fin_to_nat wl) ;;;
  _ <- @bool_check_option True (negb (fin_to_nat wc =? 0)) ;;;
  _ <- @bool_check_option True (fin_to_nat wl =? 5 + 3 * (fin_to_nat wc) + (set_fold (fun v acc => length (snd v) + acc) 0 memDescrs)) ;;;
  _ <- @bool_check_option True (match ty with
                                     | Donation => (fin_to_nat wc) =? 1
                                     | _ => true
                                     end) ;;;
  unit (vs', (if (fin_to_nat wh) =? 0 then None else Some wh), wt, wf, memory_regions_to_gmap memDescrs).
                                                           
Definition insert_transaction (st : state) (h : handle) (t : transaction) : state :=
  (get_vm_states st, get_current_vm st, get_mem st, <[h:=t]>(get_transactions st)).

Definition new_transaction (st : state) (vid : vmid)
           (tt : transaction_type)
           (flag tag : word)
           (m : gmap vmid (gmap pid bool))  : option state :=
  if map_fold (fun _ v acc => andb acc (set_fold (fun v' acc' => andb acc' (check_ownership_page st vid v')) true (@dom (gmap pid bool) (gset pid) gset_dom v))) true m
  then
    match fresh_handle (get_transactions st) with
    | None => None
    | Some h' =>
      unit (insert_transaction st h' (vid, flag, tag, m, tt))
    end
  else None.

Definition get_transaction (st : state) (h : handle) : option transaction :=
  (get_transactions st) !! h.

Definition remove_transaction (s : state) (h : handle) : state :=
  (get_vm_states s, get_current_vm s, get_mem s, delete h (get_transactions s)).

Definition new_transaction_from_descriptor (st : state) (ty : transaction_type) (td : transaction_descriptor) : option state :=
  match td with
  | (s, None, t, f, rs) => new_transaction st s ty f t (base.fmap (fun x => set_to_map (fun el => (el, false)) x) rs)
  | _ => None
  end.

Definition new_transaction_from_descriptor_in_tx_unsafe (st : state) (v : vmid) (wl : word) (ty : transaction_type) : option state :=
  if (page_size <? fin_to_nat wl)
  then None
  else
    txBAddr <- get_tx_base_addr_global st v ;;;
    td <- parse_transaction_descriptor st wl txBAddr ty ;;;
    new_transaction_from_descriptor st ty td.

Definition update_offset_PC (st : state) (dir : bool) (offset : nat) : option state :=
  bind
    (get_vm_reg_file st (get_current_vm st))
    (fun rf =>
       bind (rf !! PC)
            (fun v =>
               let v' := fin_to_nat v in
               if dir
               then
                 match (nat_lt_dec (v' + offset) word_size) with
                 | left l => update_sys_reg st PC (@nat_to_fin (v' + offset) _ l)
                 | _ => None
                 end
               else
                 match (nat_lt_dec (v' - offset) word_size) with
                 | left l => update_sys_reg st PC (@nat_to_fin (v' - offset) _ l)
                 | _ => None
                 end
    )).

Definition update_incr_PC (st : state) : option state :=
  update_offset_PC st true 2.

Definition update_current_vmid (st : state) (v : vmid) : state :=
  (get_vm_states st, v, get_mem st, get_transactions st).

Definition is_primary (st : state) : bool :=
  (get_current_vm st) =? 0.

Definition is_secondary (st : state) : bool :=
  negb (is_primary st).

Definition is_valid_PC (st : state) : option bool :=
  w <- get_reg st PC ;;;
  w' <- addr_offset w 1 ;;;
  Some (andb (check_access_addr st (get_current_vm st) w) (check_access_addr st (get_current_vm st) w')).

Definition option_state_unpack (oldSt : state) (newSt : option state) : conf :=
  match newSt with
  | None => (FailI, oldSt)
  | Some s => (NextI, s)
  end.

Definition mov_word (s : state) (dst : reg_name) (src : word) : conf * control_mode :=
  let comp :=
        s' <- update_general_reg s dst src ;;;
        update_incr_PC s'
    in
    (option_state_unpack s comp, NormalM).

Definition mov_reg (s : state) (dst : reg_name) (src : reg_name) : conf * control_mode :=
  let comp :=
      src' <- get_reg s src ;;;
      s'' <- update_general_reg s dst src' ;;;
      update_incr_PC s''
    in
  (option_state_unpack s comp, NormalM).

Definition ldr (s : state) (dst : reg_name) (src : reg_name) : conf * control_mode :=
  let comp :=
      src' <- get_reg s src ;;;
      v <- get_memory s src' ;;;
      m <- update_general_reg s dst v ;;;
      update_incr_PC m
  in
  (option_state_unpack s comp, NormalM).

Definition str (s : state) (src : reg_name) (dst : reg_name) : conf * control_mode :=
  let comp :=
      src' <- get_reg s src ;;;
      dst' <- get_reg s dst ;;;
      m <- update_memory s dst' src' ;;;
      update_incr_PC m
  in
  (option_state_unpack s comp, NormalM).

Program Definition cmp_word (s : state) (arg1 : reg_name) (arg2 : word) : conf * control_mode :=
  let comp :=
      arg1' <- get_reg s arg1 ;;;
      m <- match (nat_lt_dec (fin_to_nat arg1') (fin_to_nat arg2)) with
           | left _ => update_sys_reg s NZ (@nat_to_fin 1 word_size _)
           | right _ => update_sys_reg s NZ (@nat_to_fin 0 word_size _)
           end ;;;
      update_incr_PC m       
  in
  (option_state_unpack s comp, NormalM).
Next Obligation.
  pose proof word_size_at_least as G.
  unfold word_size_lower_bound in G.
  lia.
Qed.
Next Obligation.
  pose proof word_size_at_least as G.
  unfold word_size_lower_bound in G.
  lia.
Qed.

Program Definition cmp_reg (s : state) (arg1 : reg_name) (arg2 : reg_name) : conf * control_mode :=
  let comp :=
      arg1' <- get_reg s arg1 ;;;
      arg2' <- get_reg s arg2 ;;;
      m <- match (nat_lt_dec (fin_to_nat arg1') (fin_to_nat arg2')) with
           | left _ => update_sys_reg s NZ (@nat_to_fin 1 word_size _)
           | right _ => update_sys_reg s NZ (@nat_to_fin 0 word_size _)
           end ;;;
      update_incr_PC m
  in
  (option_state_unpack s comp, NormalM).
Next Obligation.
  pose proof word_size_at_least as G.
  unfold word_size_lower_bound in G.
  lia.
Qed.
Next Obligation.
  pose proof word_size_at_least as G.
  unfold word_size_lower_bound in G.
  lia.
Qed.

Definition jnz (s : state) (arg : reg_name) : conf * control_mode :=
  let comp :=
      arg' <- get_reg s arg ;;;
      nz <- get_reg s NZ ;;;
      match (fin_to_nat nz) with
      | 0 => update_sys_reg s PC arg'
      | _ => update_incr_PC s
      end
  in
  (option_state_unpack s comp, NormalM).

Definition jmp (s : state) (arg : reg_name) : conf * control_mode :=
  let comp :=
      arg' <- get_reg s arg ;;;
      update_sys_reg s PC arg'
  in
  (option_state_unpack s comp, NormalM).

Definition fail (s : state) : conf * control_mode :=
  (FailI, s, NormalM).

Definition halt (s : state) : conf * control_mode :=
  (HaltI, s, NormalM).

Program Definition run (s : state) : conf * control_mode :=
  match get_reg s  (R 1 _) with
  | None => (FailI, s, NormalM)
  | Some id =>
    match update_incr_PC s with
    | None => (FailI, s, NormalM)
    | Some s' =>
      match decode_vmid id with
      | None => (FailI, s, NormalM)
      | Some id' => (NextI, s', YieldM id')
      end
    end
  end.
Next Obligation.
  pose proof reg_count_at_least as G.
  unfold reg_count_lower_bound in G.
  lia.
Qed.

Program Definition sum_state_unpack (oldSt : state) (newSt : sum hvc_error state) : conf :=
  match newSt with
  | inl err =>
    match (update_general_reg oldSt (R 0 _) (encode_hvc_error err)) with
    | None => (FailI, oldSt)
    | Some s => (NextI, s)
    end
  | inr s => (NextI, s)
  end.
Next Obligation.
  pose proof reg_count_at_least as G.
  unfold reg_count_lower_bound in G.
  lia.
Qed.

Definition yield (s : state) : conf * control_mode :=
  match update_incr_PC s with
  | None => (FailI, s, NormalM)
  | Some s' => (NextI, s', YieldM (@nat_to_fin 0 vm_count vm_count_pos))
  end.

Definition verify_perm_transaction (s : state) (p : permission) (td : transaction_descriptor) : bool :=
  match td with
  | (_, _, _, _, m) => map_fold
                         (fun _ v acc => andb acc (set_fold (fun v' acc' => andb acc' (check_perm_page s (get_current_vm s) v' p)) true v))
                         true
                         m
  end.

Program Definition share (s : state) : conf * control_mode :=
    let comp :=
        r <- get_reg s (R 1 _) ;;;
        m <- (if (page_size <? fin_to_nat r)
              then None
              else
                txBAddr <- get_tx_base_addr_global s (get_current_vm s) ;;;
                td <- parse_transaction_descriptor s r txBAddr Sharing ;;;
                if (verify_perm_transaction s (Owned, ExclusiveAccess) td)
                then bind (new_transaction_from_descriptor s Sharing td) (fun x => Some (x, td))
                else None) ;;;
        match m with
        | (m', td) =>
          match td with
          | (_, gm) =>
            match (map_fold (fun _ v acc => union v acc) empty gm) with
            | ListsetNoDup ls prf =>
              foldr (fun v' acc' => bind acc' (fun x => update_page_table x v' (Owned, SharedAccess))) (Some m') ls
            end
          end
        end
    in 
    (option_state_unpack s comp, NormalM).
Next Obligation.
  pose proof reg_count_at_least as G.
  unfold reg_count_lower_bound in G.
  lia.
Defined.

Program Definition lend (s : state) : conf * control_mode :=
  let comp :=
      r <- get_reg s (R 1 _) ;;;
      m <- (if (page_size <? fin_to_nat r)
            then None
            else
              txBAddr <- get_tx_base_addr_global s (get_current_vm s) ;;;
              td <- parse_transaction_descriptor s r txBAddr Lending ;;;
              if (verify_perm_transaction s (Owned, ExclusiveAccess) td)
              then bind (new_transaction_from_descriptor s Lending td) (fun x => Some (x, td))
              else None) ;;;
      match m with
      | (m', td) =>
        match td with
        | (_, gm) =>
          match map_fold (fun _ v acc => union v acc) empty gm with
          | ListsetNoDup ls prf =>
            foldr (fun v' acc' => bind acc' (fun x => update_page_table x v' (Owned, NoAccess))) (Some m') ls
          end
        end
      end
  in 
  (option_state_unpack s comp, NormalM).
Next Obligation.
  pose proof reg_count_at_least as G.
  unfold reg_count_lower_bound in G.
  lia.
Defined.

Program Definition donate (s : state) : conf * control_mode :=
  let comp :=
      r <- get_reg s (R 1 _) ;;;
      m <- (if (page_size <? fin_to_nat r)
            then None
            else
              txBAddr <- get_tx_base_addr_global s (get_current_vm s) ;;;
              td <- parse_transaction_descriptor s r txBAddr Donation ;;;
              if (verify_perm_transaction s (Owned, ExclusiveAccess) td)
              then bind (new_transaction_from_descriptor s Donation td) (fun x => Some (x, td))
              else None) ;;;
      match m with
      | (m', td) =>
        match td with
        | (_, gm) =>
          match map_fold (fun _ v acc => union v acc) empty gm with
          | ListsetNoDup ls prf =>
            foldr (fun v' acc' => bind acc' (fun x => update_page_table x v' (NotOwned, NoAccess))) (Some m') ls
          end
        end
      end
  in 
  (option_state_unpack s comp, NormalM).
Next Obligation.
  pose proof reg_count_at_least as G.
  unfold reg_count_lower_bound in G.
  lia.
Defined.

Definition toggle_transaction_entry (s : state) (h : handle) (v : vmid) (p : pid) : state :=
  (get_vm_states s, get_current_vm s, get_mem s,
   alter (fun x => match x with
                   | (vs, w1, w2, gm, ty) => (vs, w1, w2, alter (fun y => alter (fun z => negb z) p y) v gm, ty)
                   end) h (get_transactions s)).

Definition toggle_transaction_entries (s : state) (h : handle) (v : vmid) : state.
Proof.
  intros.
  destruct ((get_transactions s) !! h) as [[[? t] ?] |].
  - destruct (t !! v) as [g |].
    + exact (map_fold (fun k _ acc => toggle_transaction_entry acc h v k) s g).
    + exact s.
  - exact s.
Defined.

Definition get_pids (s : state) (h : handle) : list pid :=
  match (get_transactions s) !! h with
  | None => nil
  | Some (_, _, _, m, _) =>
    match m !! (get_current_vm s) with
    | None => nil
    | Some m' => map (fun x => match x with | (y, _) => y end) (map_to_list m')
    end
  end.

Definition retrieve_transaction (s : state)
           (h : handle)
           (type : transaction_type)
           (receiversMap : gmap vmid (gmap pid bool)) : option state :=
  let m := toggle_transaction_entries s h (get_current_vm s)
  in
  match type with
  | Sharing =>
    foldr (fun v' acc' =>
             bind acc'
                  (fun x => update_page_table x v' (NotOwned, SharedAccess)))
          (Some m)
          (get_pids s h)
  | Lending =>
    if decide (1 < size receiversMap)
    then foldr (fun v' acc' =>
                  bind acc' (fun x => update_page_table x v' (NotOwned, SharedAccess)))
               (Some m)
               (get_pids s h)
    else foldr (fun v' acc' =>
                  bind acc' (fun x => update_page_table x v' (NotOwned, ExclusiveAccess)))
               (Some m)
               (get_pids s h)
  | Donation =>
    foldr (fun v' acc' =>
             bind acc' (fun x => update_page_table x v' (Owned, ExclusiveAccess)))
          (Some m)
          (get_pids s h)
  end.

Definition relinquish_transaction (s : state)
           (h : handle) : option state :=
  let m := toggle_transaction_entries s h (get_current_vm s)
  in foldr (fun v' acc' => bind acc' (fun x => update_page_table x v' (NotOwned, NoAccess))) (Some m) (get_pids s h).

Definition get_receivers (t : transaction) : gmap vmid (gmap pid bool) :=
  match t with
  | (_, _, _, m, _) => m
  end.

Definition get_type (t : transaction) : transaction_type :=
  match t with
  | (_, _, _, _, ty) => ty
  end.

Program Definition retrieve (s : state) : conf * control_mode :=
  let comp :=
      handle <- get_reg s (R 1 _) ;;;
      trn <- get_transaction s handle ;;;
      m <- retrieve_transaction s handle (get_type trn) (get_receivers trn) ;;;
      update_incr_PC m
  in
  (option_state_unpack s comp, NormalM).
Next Obligation.
  pose proof reg_count_at_least as G.
  unfold reg_count_lower_bound in G.
  lia.
Defined.

Program Definition relinquish (s : state) : conf * control_mode :=
  let comp :=
      handle <- get_reg s (R 1 _) ;;;
      m <- relinquish_transaction s handle ;;;
      update_incr_PC m
  in
  (option_state_unpack s comp, NormalM).
Next Obligation.
  pose proof reg_count_at_least as G.
  unfold reg_count_lower_bound in G.
  lia.
Defined.

Definition all_not_received (s : state) (h : handle) (v : vmid) : bool :=
  match (get_transactions s) !! h with
  | None => true
  | Some (_, _, _, m, _) =>
    match m !! v with
    | None => true
    | Some m' => map_fold (fun _ v acc => andb v acc) true m'
    end
  end.

Program Definition reclaim (s : state) : conf * control_mode :=
  let comp :=
      handle <- get_reg s (R 1 _) ;;;
      m <- (if all_not_received s handle (get_current_vm s)
            then
              foldr
                (fun v' acc' => bind acc' (fun x => update_page_table x v' (Owned, ExclusiveAccess)))
                                     (Some (remove_transaction s handle))
                                     (get_pids s handle)
            else None) ;;;
      update_incr_PC m
  in
  (option_state_unpack s comp, NormalM).
Next Obligation.
  pose proof reg_count_at_least as G.
  unfold reg_count_lower_bound in G.
  lia.
Defined.

Program Definition send (s : state) : conf * control_mode :=
  let comp :=
      receiver <- get_reg s (R 1 _) ;;;
      receiver' <- decode_vmid receiver ;;;
      m <- transfer_msg_unsafe s (get_current_vm s) receiver' ;;;
      update_incr_PC m
  in
  (option_state_unpack s comp, NormalM).
Next Obligation.
  pose proof reg_count_at_least as G.
  unfold reg_count_lower_bound in G.
  lia.
Defined.

Definition wait (s : state) : conf * control_mode :=
  match update_incr_PC s with
  | None => (FailI, s, NormalM)
  | Some s' =>
    if is_rx_ready s
    then (NextI, s', NormalM)
    else (NextI, s', YieldM (@nat_to_fin 0 _ vm_count_pos))
  end.

Program Definition hvc (s : state) : conf * control_mode :=
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
Next Obligation.
  pose proof reg_count_at_least as G.
  unfold reg_count_lower_bound in G.
  lia.
Qed.

Definition exec (i : instruction) (s : state) : conf * control_mode :=
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

Inductive val : Type :=
| NextV
| HaltV
| FailV.

Inductive expr: Type :=
| Instr (c : exec_mode)
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

Inductive step : conf -> conf * control_mode -> Prop :=
| step_exec_fail:
    forall st,
      not (is_valid_PC st = Some true) ->
      step (ExecI, st) (FailI, st, NormalM)
| step_exec_instr:
    forall st a w1 w2 i c,
      is_valid_PC st = Some true ->
      get_reg st PC = Some a ->
      get_memory st a = Some w1 ->
      get_memory_with_offset st a 1 = Some w2 ->
      decode_instruction (w1, w2) = Some i ->
      exec i st = c ->
      step (ExecI, st) c.

Inductive prim_step : expr -> state -> list Empty_set -> expr -> state -> list Empty_set -> control_mode -> Prop :=
| PS_instr_normal st e' st' :
    step (ExecI, st) (e', st', NormalM) -> prim_step (Instr ExecI) st [] (Instr e') st' [] NormalM
| PS_instr_yield st e' st' i :
    step (ExecI, st) (e', st', YieldM i) -> prim_step (Instr ExecI) st [] (Instr e') (update_current_vmid st' i) [] NormalM
| PS_seq st : prim_step (Seq (Instr NextI)) st [] (Seq (Instr ExecI)) st [] NormalM
| PS_halt st : prim_step (Seq (Instr HaltI)) st [] (Instr HaltI) st [] NormalM
| PS__fail st : prim_step (Seq (Instr FailI)) st [] (Instr FailI) st [] NormalM.
