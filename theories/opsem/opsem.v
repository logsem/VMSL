Require Import basic.

Section opsem.
  Context `{MachineParameters}.

  Definition gset_elemofb {A} `{Countable A} (p:A) (ps: gset A):bool:=
  match (decide (p ∈@{gset A} ps)) with
  | left _ => true
  | right _ => false
   end.


(*TODO*)
  Fixpoint mem_copy_aux (m:Mem) (pt pr: PID) (ws: nat): Mem:=
    match ws with
    | 0 => m
    | S n => mem_copy_aux m pt pr n
    end.

   Definition mem_copy (m:Mem) (pt pr: PID) (ws : Z) : Mem :=
    if (Z.lt ws 0) then
      let ws := (Z.to_nat ws) in
      (mem_copy_aux m pt pr ws)
    else m.

  Definition exec (i: instr) (ϕ : ExecConf) (v:VMID) : Conf :=
    let m := ϕ.m in
    let Δ := (fst ϕ) in
    let s := (snd (snd ϕ)) in
    match (Δ !s! v), (Δ !s! 0) with
    | Some δ_v, Some δ_p =>
      match i with
      | faili => ((Done Fail), ϕ)
      | halt => ((Done Halt), ϕ)
      | br r => (tick (upd_gen_reg Δ v PC (δ_v.gr !gr! r)) m s v v ident)
      | bne r => let Δ':= if (Z.eqb (z_of_w (δ_v.sr !sr! NZ)) 1)
                          then (upd_gen_reg Δ v PC (δ_v.gr !gr! r))
                          else (upd_gen_reg Δ v PC (w_add_z (δ_v.gr !gr! PC) 1))
                 in
                 (tick Δ' m s v v ident)
      | mov r1 w => let Δ':= (upd_gen_reg Δ v r1 w) in
                    (tick Δ' m s v v updPC)
      | ldr r1 r2 => match (valid_a δ_v r2 RE) with
                     | Some a => let Δ' :=(upd_gen_reg Δ v r1 (m !m! a)) in
                                 (tick Δ' m s v v updPC)
                     | None => ((Done Fail), ϕ)
                     end
      | str r1 r2 => match (valid_a δ_v r1 WR) with
                     | Some a => let m' :=(upd_mem m a (δ_v.gr !gr! r2)) in
                                 (tick Δ m' s v v updPC)
                     | None => ((Done Fail), ϕ)
                     end
      | add r1 r2 r3 => let Δ':= (upd_gen_reg Δ v r1 (w_add_w (δ_v.gr !gr! r2)(δ_v.gr !gr! r3))) in
                        (tick Δ' m s v v updPC)
      | sub r1 r2 r3 => let Δ':= (upd_gen_reg Δ v r1 (w_sub_w (δ_v.gr !gr! r2)(δ_v.gr !gr! r3))) in
                        (tick Δ' m s v v updPC)
      | cmp r1 r2 => match (w_sub_w (δ_v.gr !gr! r1)(δ_v.gr !gr! r2)) with
                     | (W z _ _) => let Δ' := if (Z.eqb z 0) then (upd_sys_reg Δ v NZ (z_to_w 1))
                                    else if (Z.ltb z 0) then (upd_sys_reg Δ v NZ (z_to_w 2))
                                         else  (upd_sys_reg Δ v NZ (z_to_w 0)) in
                                    (tick Δ' m s v v updPC)
                     end
      | hvc => match (w_to_fi (δ_v.gr !gr! (nat_to_r 0))) with
               | F_MEM_DNT => match (valid_a δ_v (nat_to_r 1) VA) with
                              | Some a => let vr :=(Z.to_nat  (z_of_w (δ_v.gr !gr! (nat_to_r 2)))) in
                                          match (Δ !s! vr) with
                                            | Some _ => if (vr =? v) then ((Done Fail), ϕ)
                                                        else
                                                          let pid:=(a_to_pid a) in
                                                          let s' := s ++ [(pid, vr)] in
                                                          let Δ' := (upd_ps_rm Δ v pid) in
                                                          let Δ' := (upd_gen_reg Δ' v (nat_to_r 0) (rc_to_w SUCCESS)) in
                                                          let Δ' := (upd_gen_reg Δ' v (nat_to_r 2) (nat_to_w (length s))) in
                                                             (tick Δ' m s' v v updPC)
                                            | None => ((Done Fail), ϕ)
                                          end
                              | None => ((Done Fail), ϕ)
                              end
               | F_MEM_RTRVQ => let hd := (Z.to_nat (z_of_w (δ_v.gr !gr! (nat_to_r 1)))) in
                                match (s !! hd ) with
                                | Some (p,v) => if (gset_elemofb p (δ_v.ps)) then ((Done Fail), ϕ)
                                                else let Δ' := (upd_ps_add Δ v p) in
                                                     let Δ' := (upd_gen_reg Δ' v (nat_to_r 0) (rc_to_w MEM_RTRVP)) in
                                                     let s' := (delete hd s) in
                                                     (tick Δ' m s' v v updPC)
                                | _ => ((Done Fail), ϕ)
                                end
               | F_RUN => let vn :=(Z.to_nat  (z_of_w (δ_v.gr !gr! (nat_to_r 2)))) in
                          match (Δ !s! vn) with
                          | Some _ => if (vn =? 0) then
                                        match δ_v.π.2 with
                                        | Some (((_, b), ws), vs) =>
                                          if b then
                                            let Δ' := (upd_gen_reg Δ vn (nat_to_r 0) (rc_to_w MSG_SEND)) in
                                            let Δ' := (upd_gen_reg Δ' vn (nat_to_r 1) (comb (nat_to_w vs) (nat_to_w vn))) in
                                            let Δ' := (upd_gen_reg Δ' vn (nat_to_r 3) ws) in
                                            (tick Δ' m s v vn updPC)
                                          else (tick Δ m s v vn updPC)
                                        | None => ((Done Fail), ϕ)
                                        end
                                      else ((Done Fail), ϕ)
                          | None => ((Done Fail), ϕ)
                          end
               | F_YIELD =>let Δ' := (upd_gen_reg Δ 0 (nat_to_r 0) (rc_to_w YIELD)) in
                           let Δ' := (upd_gen_reg Δ' 0 (nat_to_r 1) (nat_to_w v)) in
                           (tick Δ' m s v 0 updPC)
               | F_MSG_WAIT =>match δ_v.π.2 with
                              | Some (((pr, b), ws), vs) =>
                                if b then
                                  let Δ' := (upd_gen_reg Δ v (nat_to_r 0) (rc_to_w MSG_SEND)) in
                                  let Δ' := (upd_gen_reg Δ' v (nat_to_r 1) (comb (nat_to_w vs) (nat_to_w v))) in
                                  let Δ' := (upd_gen_reg Δ' v (nat_to_r 3) ws) in
                                    (tick Δ' m s v v updPC)
                                else
                                  let Δ' := (upd_gen_reg Δ 0 (nat_to_r 0) (rc_to_w MSG_WAIT)) in
                                  let Δ' := (upd_gen_reg Δ' 0 (nat_to_r 1) (nat_to_w v)) in
                                    (tick Δ' m s v 0 updPC)
                              | None => ((Done Fail), ϕ)
                              end
               | F_MSG_SEND =>let Δ' := Δ in (*TODO: memcpy*)
                              let n:= 1 in
                             (tick Δ m s v n updPC)
               | F_MSG_RCV => match δ_v.π.2 with
                              | Some (((pr, b), ws), vs) =>
                                if b then
                                  let Δ' := (upd_rx Δ v (Some (((pr, false), ws), v))) in
                                  (tick Δ' m s v v updPC)
                                else ((Done Fail), ϕ)
                              | _ => ((Done Fail), ϕ)
                              end
               | F_UNKNOWN =>((Done Fail), ϕ)
               end
      | mrs r1 r2 =>  let Δ':= (upd_gen_reg Δ v r1 (δ_v.sr !sr! r2)) in
                    (tick Δ' m s v v updPC)
      | msr r1 r2 =>  let Δ':= (upd_sys_reg Δ v r1 (δ_v.gr !gr! r2)) in
                    (tick Δ' m s v v updPC)
      end
    | _,_ => ((Done Fail), ϕ)
    end.




End opsem.
