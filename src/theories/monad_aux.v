From ExtLib Require Import Structures.Monads.
From stdpp Require Import vector.

Module monad_option.
  
  Instance MonadOption : Monad option.
  Proof.
    refine {| ret t x := Some x;
              bind t u mt f := match mt with | None => None | Some t => f t end;
           |}.
  Defined.

  Fixpoint listFromSome {A : Type} (l : list (option A)) : list A :=
  match l with
  | nil => nil
  | cons x xs =>
    match x with
    | None => listFromSome xs
    | Some x' => cons x' (listFromSome xs)
    end
  end.

  Definition boolCheckOption {A : Type} (b : bool) : option bool :=
    match b with
    | false => None
    | true => Some true
    end.

End monad_option.

Module monad_sum.
  Instance MonadEither {E : Type} : Monad (sum E).
  Proof.
    refine {| ret t x := inr x;
              bind t u mt f := match mt with | inl l => inl l | inr r => f r end;
           |}.
  Defined.
  
  Definition unpackOptionWithLeft {A B : Type} (v : option B) (err : A) : sum A B :=
    match v with
    | None => inl err
    | Some v' => inr v'
    end.
End monad_sum.

Fixpoint listBind {A B : Type} (l : list A) (f : A -> list B) : list B :=
  match l with
  | nil => nil
  | cons x xs => app (f x) (listBind xs f)
  end.

Fixpoint listFmap {A B : Type} (f : A -> B) (l : list A) : list B :=
  match l with
  | nil => nil
  | cons x xs => cons (f x) (listFmap f xs)
  end.
                     
Instance MonadList : Monad list.
Proof.
  refine {| ret t x := cons x nil;
            bind t u := listBind
         |}.
Defined.

Module monad_list.
  
End monad_list.

Module monad_general.
  From stdpp Require Import listset_nodup.

  Lemma sequenceMNoDup {A : Type} {M : Type -> Type} `{Monad M} (l : listset_nodup (M A)) : M (listset_nodup A).
  Proof.
    destruct l as [car prf].
    induction car as [| x xs HQ].
    - apply ret; apply empty.
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
          apply ret.
          exact l'.
    Defined.
  
  Fixpoint sequenceMList {A : Type} {M : Type -> Type} `{Monad M} (l : list (M A)) : M (list A) :=
    match l with
    | nil => ret nil
    | cons x xs => bind x (fun x' => bind (sequenceMList xs) (fun xs' => ret (cons x' xs')))
    end.
  
  Definition mapM {A B : Type} {M : Type -> Type} `{Monad M} (f : A -> M B) (l : list A) : M (list B) :=
    sequenceMList (listFmap f l).

  (* Generalize over traverseable *)
  Fixpoint foldrMVec {A B : Type} {n : nat} {M : Type -> Type} `{Monad M}
           (m : A -> B -> M B) (v : vec A n) (i : B) : M B :=
    match v with
    | vnil => ret i
    | vcons x xs => bind (m x i) (foldrMVec m xs)
    end.

  Fixpoint foldrMList {A B : Type} {M : Type -> Type} `{Monad M}
           (m : A -> B -> M B) (v : list A) (i : B) : M B :=
    match v with
    | nil => ret i
    | cons x xs => bind (m x i) (foldrMList m xs)
    end.

  Fixpoint sequenceMVec {A : Type} {n : nat} {M : Type -> Type} `{Monad M} (v : vec (M A) n) : M (vec A n) :=
    match v with
    | vnil => ret vnil
    | vcons x xs => bind x (fun x' => bind (sequenceMVec xs) (fun k => ret (vcons x' k)))
    end.
  
End monad_general.

Module monad_base_notation.
  
  Delimit Scope monad_scope with monad.
  
  Notation "c >>= f" := (@bind _ _ _ _ c f) (at level 58, left associativity) : monad_scope.
  Notation "f =<< c" := (@bind _ _ _ _ c f) (at level 62, right associativity) : monad_scope.
  Notation "f >=> g" := (@mcompose _ _ _ _ _ f g) (at level 62, right associativity) : monad_scope.
  
  Notation "e1 ;;; e2" := (@bind _ _ _ _ e1%monad (fun _ => e2%monad))%monad
                                                                     (at level 62, right associativity) : monad_scope.
  
End monad_base_notation.

Module monad_notation.
  
  Export monad_base_notation.
  
  Notation "x <- c1 ;;; c2" := (@bind _ _ _ _ c1 (fun x => c2))
                                (at level 62, c1 at next level, right associativity) : monad_scope.
  
  Notation "' pat <- c1 ;;; c2" :=
    (@bind _ _ _ _ c1 (fun x => match x with pat => c2 end))
      (at level 62, pat pattern, c1 at next level, right associativity) : monad_scope.
  
End monad_notation.

Module monad_let_notation.
  
  Export monad_base_notation.
  
  Notation "'let*' p ':=' c1 'in' c2" := (@bind _ _ _ _ c1 (fun p => c2))
                                           (at level 62, p as pattern, c1 at next level, right associativity) : monad_scope.
  
End monad_let_notation.
