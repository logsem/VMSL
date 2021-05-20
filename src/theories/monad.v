From stdpp Require Import vector.

Class Functor (F : Type -> Type) := {
  fmap {A B : Type} (f : A -> B) (fa : F A) : F B;
  (*
  fmap_id {A : Type} : forall x, fmap (@id A) x = id x;
  fmap_compose {A B C : Type} : forall (g : B -> C) (h : A -> B) x, fmap (compose g h) x = compose (fmap g) (fmap h) x;
   *)
                                   }.

Delimit Scope functor_scope with functor.

(* Notation "f <$> a" := (@fmap _ _ _ _ f a) (at level 61, left associativity) : functor_scope. *)

Class Applicative (F : Type -> Type) `{Functor F} := {
  unit {A : Type} (a : A) : F A;
  ap {A B : Type} (f : F (A -> B)) (a : F A) : F B;
  (*
  ap_unit_id {A : Type} : forall (v : F A),
      ap (unit id) v = v;
  unit_composition {A B C : Type} : forall (u : F (B -> C)) (v : F (A -> B)) (w : F A),
      ap (ap (ap (unit compose) u) v) w = ap u (ap v w);
  unit_homomorphism {A B : Type} : forall (f : A -> B) (x : A),
      ap (unit f) (unit x) = unit (f x);
  unit_interchange {A B : Type} : forall (u : F (A -> B)) (y : A),
      ap u (unit y) = ap (unit (fun f => f y)) u;
   *)
                                                    }.

Delimit Scope applicative_scope with applicative.

Notation "f <*> a" := (@ap _ _ _ _ _ f a) (at level 62, left associativity) : applicative_scope.

Class Monad (M : Type -> Type) `{Applicative M} := {
  bind {A B : Type} : M A -> (A -> M B) -> M B;
  (*
  unit_l_id_bind {A B : Type} : forall (f : A -> M B) (a : A),
      bind (unit a) f = f a;
  unit_r_id_bind {A B : Type} : forall (ma : M A),
      bind ma unit = ma;
  bind_assoc {A B C : Type} : forall (f : A -> M B) (g : B -> M C) (ma : M A),
      bind ma (fun x => bind (f x) g) = bind (bind ma f) g;
   *)
                                                  }.

Definition join {M : Type -> Type} {A : Type} `{Monad M} (mma : M (M A)) : M A :=
  bind mma id.

Class Monoid (M : Type) := {
  op : M -> M -> M;
  neutral : M;
  unit_id_l : forall (a : M), op neutral a = a;
  unit_id_r : forall (a : M), op a neutral = a;
  op_assoc {a b c : M} : op a (op b c) = op (op a b) c;
                          }.

Class Foldable (T : Type -> Type) := {
  foldr {A B : Type} : (A -> B -> B) -> B -> T A -> B;
  fold_map {A : Type} {M : Type} `{Monoid M} : (A -> M) -> T A -> M;
                                   }.

Class Traversable (T : Type -> Type) `{Foldable T} `{Functor T} := {
  traverse {A B : Type} {F : Type -> Type} `{Applicative F} : (A -> F B) -> T A -> F (T B);
  sequence_a {A : Type} {F : Type -> Type} `{Applicative F} : T (F A) -> F (T A); 
  }.

Module Option.
  
  Instance functor_option : Functor option.
  Proof.
    refine {| monad.fmap := fun {A B : Type} (f : A -> B) (x : option A) => match x with | None => None | Some x' => Some (f x') end; |}.
    (*
    - intros A [x |]; reflexivity.
    - intros A B C g h [x |]; reflexivity.
     *)
  Defined.

  Instance applicative_option : Applicative option.
  Proof.
    refine {| unit := fun {A : Type} (x : A) => Some x;
              ap := fun {A B : Type} (f : option (A -> B)) (a : option A) =>
                      match f with
                      | None => None
                      | Some f' =>
                        match a with
                        | None => None
                        | Some a' => Some (f' a')
                        end
                      end; |}.
    (*
    - intros A [v |]; reflexivity.
    - intros A B C [u |] [v |] [w |]; reflexivity.
    - reflexivity.
    - intros A B [u |] y; reflexivity.
     *)
  Defined.
  
  Instance monad_option : Monad option.
  Proof.
    refine {| bind t u mt f := match mt with | None => None | Some t => f t end;
           |}.
    (*
    - reflexivity.
    - intros ? ? [ma |]; reflexivity.
    - intros A B C f g [ma |]; reflexivity.
     *)
  Defined.

  Fixpoint list_from_some {A : Type} (l : list (option A)) : list A :=
    match l with
    | nil => nil
    | cons x xs =>
      match x with
      | None => list_from_some xs
      | Some x' => cons x' (list_from_some xs)
      end
    end.
  
  Definition bool_check_option {A : Type} (b : bool) : option bool :=
    match b with
    | false => None
    | true => Some true
    end.
  
End Option.

Module Sum.
  
  Instance functor_sum {E : Type} : Functor (sum E).
  Proof.
    refine {| fmap := fun {A B : Type} (f : A -> B) (x : E + A) => match x with
                                     | inl l => inl l
                                     | inr r => inr (f r)
                                 end
           |}.
    (*
    - intros A [e | a]; reflexivity.
    - intros A B C g h [e | a]; reflexivity.
     *)
  Defined.

  Instance applicative_sum {E : Type} : Applicative (sum E).
  Proof.
    refine {| unit := fun {A : Type} (x : A) => inr x;
              ap := fun {A B : Type} (f : E + (A -> B)) (x : E + A) =>
                      match f with
                      | inl l => inl l
                      | inr r =>
                        match x with
                        | inl l' => inl l'
                        | inr r' => inr (r r')
                        end
                      end
           |}.
    (*
    - intros A [e | a]; reflexivity.
    - intros A B C [e1 | u] [e2 | v] [e3 | w]; reflexivity.
    - reflexivity.
    - intros ? ? [e | f] y; reflexivity.
     *)
  Defined.
  
  Instance monad_sum {E : Type} : Monad (sum E).
  Proof.
    refine {| bind t u mt f := match mt with | inl l => inl l | inr r => f r end;
           |}.
    (*
    - reflexivity.
    - intros ? ? [? | ?]; reflexivity.
    - intros ? ? ? f g [? | a]; [| destruct (f a)]; reflexivity.
     *)
  Defined.
  
End Sum.

Module List.

  Local Fixpoint list_bind {A B : Type} (l : list A) (f : A -> list B) : list B :=
    match l with
    | nil => nil
    | cons x xs => app (f x) (list_bind xs f)
    end.

  Instance functor_list : Functor list.
  Proof.
    refine {| fmap := map |}.
    (*
    - exact map_id.
    - symmetry.
      apply map_map.
     *)
  Defined.

  Local Fixpoint foldr_list {A B : Type} (f : A -> B -> B) (b : B) (l : list A) : B :=
    match l with
    | nil => b
    | cons x xs => f x (foldr_list f b xs)
    end.
  
  Local Fixpoint fold_map_list {A M : Type} `{Monoid M} (f : A -> M) (l : list A) : M :=
    match l with
    | nil => neutral
    | cons x xs => op (f x) (fold_map_list f xs)
    end.
  
  Instance foldable_list : Foldable list.
  Proof.
    refine {| foldr := @foldr_list;
              fold_map := @fold_map_list ;|}.
  Defined.
  
  Local Fixpoint sequence_a_list {A : Type} {F : Type -> Type} `{Applicative F} (l : list (F A)) : F (list A) :=
    foldr (fun val acc => ap (fmap cons val) acc) (unit nil) l.

  Local Definition traverse_list {A B : Type} {F : Type -> Type} `{Applicative F} (f : A -> F B) : list A -> F (list B) :=
    compose sequence_a_list (fmap f).    
  
  Instance traversable_list : Traversable list.
  Proof.
    refine {| traverse := @traverse_list;
              sequence_a := @sequence_a_list;
           |}.
  Defined.

  Local Fixpoint ap_list {A B : Type} (f : list (A -> B)) (x : list A) : list B := 
    match (f, x) with
    | (nil, _) => nil
    | (_,  nil) => nil
    | (cons f' fs, ls) => app (fmap f' ls) (ap_list fs ls)
    end.

  (* TODO *)
  (*
  Instance applicative_list : Applicative list.
  Proof.
    refine {| pure := fun _ x => [x];
              ap := @ap_list;
           |}.
    - intros A [| x xs]; [reflexivity |].
      simpl.
      f_equal.
      rewrite map_id.
      exact (app_nil_r _).
    - admit.
    - intros ? ? f x; reflexivity.
    - intros ? ? f.
      induction f as [| f fs IHf].
      + reflexivity.
      + intros y.
        simpl.
        rewrite app_nil_r.
        f_equal.
        rewrite (IHf y).
        destruct fs.
        * reflexivity.
        * simpl.
          f_equal.
          rewrite app_nil_r.
          reflexivity.
  Admitted.

  (* TODO *)
  Instance monad_list : Monad list.
  Proof.
    refine {| unit t x := [x];
              bind t u := list_bind
           |}.
    - intros ? ? f a; rewrite <- app_nil_r.
      reflexivity.
    - intros ? ? l; induction l as [| x xs IHl].
      + reflexivity.
      + simpl.
        f_equal.
        assumption.
    - intros ? ? ? f g ma.
      induction ma as [| x xs IHl].
      + reflexivity.
      + simpl.
        rewrite IHl.
        admit.
  Admitted.
   *)

End List.

Module ListNoDup.
  From stdpp Require Import listset_nodup.    

  Local Definition foldr_listset_nodup {A B : Type} (f : A -> B -> B) (b : B) (l : listset_nodup A) : B :=
    match l with
    | ListsetNoDup l' _ => foldr f b l'
    end.
  
  Local Definition fold_map_listset_nodup {A M : Type} `{Monoid M} (f : A -> M) (l : listset_nodup A) : M :=
    match l with
    | ListsetNoDup l' _ => fold_map f l'
    end.

  Instance foldable_listset_nodup : Foldable listset_nodup.
  Proof.
    refine {| fold_map := @fold_map_listset_nodup |}.
    apply @foldr_listset_nodup.
  Defined.

  (* Seems terribly wrong *)
  Lemma sequence_m_no_dup {A : Type} {M : Type -> Type} `{Monad M} (l : listset_nodup (M A)) : M (listset_nodup A).
  Proof.
    destruct l as [car prf].
    induction car as [| x xs HQ].
    - apply unit; apply empty.
    - eapply bind.
      + exact x.
      + intros a.
        eapply bind.
        * apply HQ.
          rewrite NoDup_ListNoDup in prf.
          rewrite List.NoDup_cons_iff in prf.
          destruct prf as [prf1 prf2].
          rewrite <- NoDup_ListNoDup in prf2.
          exact prf2.
        * intros l'.
          apply unit.
          exact l'.
    Defined.
  
End ListNoDup.

Module Vector.

  Local Fixpoint foldr_vec {A B : Type} {n : nat} (f : A -> B -> B) (b : B) (l : vec A n) : B :=
    match l with
    | vnil => b
    | vcons x xs => f x (foldr_vec f b xs)
    end.
  
  Local Fixpoint fold_map_vec {A M : Type} {n : nat} `{Monoid M} (f : A -> M) (l : vec A n) : M :=
    match l with
    | vnil => neutral
    | vcons x xs => op (f x) (fold_map_vec f xs)
    end.
  
  Instance foldable_vec {n : nat} : Foldable (fun x => vec x n).
  Proof.
    refine {| foldr := fun A B f acc v => @foldr_vec A B _ f acc v;
              fold_map := fun A M _ f v => @fold_map_vec A M _ _ f v ;|}.
  Defined.
  
  Local Fixpoint sequence_a_vec {A : Type} {F : Type -> Type} {n : nat} `{Applicative F} (l : vec (F A) n) : F (vec A n) :=
    match l with
    | vnil => unit vnil
    | @Vector.cons _ x n xs => ap (fmap (fun y => @vcons A y n) x) (sequence_a_vec xs)
    end.

  Local Definition traverse_vec {A B : Type} {F : Type -> Type} {n : nat} `{Applicative F} (f : A -> F B) : vec A n -> F (vec B n) :=
    compose sequence_a_vec (vmap f).    

  Instance functor_vec {n : nat} : Functor (fun x => vec x n).
  Proof.
    refine {| fmap := fun _ _ f v => vmap f v; |}.
    (*
    - intros.
      rewrite Vector.map_id.
      reflexivity.
    - intros A B C g h [| x xs].
      + reflexivity.
      + simpl.
        f_equal.
        rewrite Vector.map_map.
        reflexivity.
     *)
  Defined.
  
  Instance traversable_vec {n : nat} : Traversable (fun x => vec x n).
  Proof.
    refine {| traverse := fun _ _ _ _ _ => traverse_vec;
              sequence_a := fun _ _ _ _ => sequence_a_vec;
           |}.
  Defined.
  
End Vector.

Module General.
  
  Definition map_m {A B : Type} {T : Type -> Type} {M : Type -> Type} `{Monad M} `{Traversable T}
             (f : A -> M B) (l : T A) : M (T B) := traverse f l.
  
End General.

Module MonadNotationBase.
  
  Delimit Scope monad_scope with monad.
  
  Notation "c >>= f" := (@bind _ _ _ _ _ _ c f) (at level 58, left associativity) : monad_scope.
  Notation "e1 ;;; e2" := (@bind _ _ _ _ _ _ e1%monad (fun _ => e2%monad))%monad
                                                                        (at level 63, right associativity) : monad_scope.
  
End MonadNotationBase.

Module MonadNotation.
  
  Export MonadNotationBase.
  
  Notation "x <- c1 ;;; c2" := (@bind _ _ _ _ _ _ c1 (fun x => c2))
                                 (at level 63, c1 at next level, right associativity) : monad_scope.
  
  Notation "' pat <- c1 ;;; c2" :=
    (@bind _ _ _ _ _ _ c1 (fun x => match x with pat => c2 end))
      (at level 63, pat pattern, c1 at next level, right associativity) : monad_scope.
  
End MonadNotation.
