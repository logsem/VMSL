From ExtLib Require Import Structures.Monads.

Module monad_option.
  
  Instance MonadOption : Monad option.
  Proof.
    refine {| ret t x := Some x;
              bind t u mt f := match mt with | None => None | Some t => f t end;
           |}.
  Qed.

End monad_option.

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
