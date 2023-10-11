(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Data.Either.
Require GHC.Base.

(* No type declarations to convert. *)

(* Converted value declarations: *)

(* Skipping definition `MonadUtils.liftIO1' *)

(* Skipping definition `MonadUtils.liftIO2' *)

(* Skipping definition `MonadUtils.liftIO3' *)

(* Skipping definition `MonadUtils.liftIO4' *)

Axiom zipWith3M : forall {m : Type -> Type},
                  forall {a : Type},
                  forall {b : Type},
                  forall {c : Type},
                  forall {d : Type},
                  forall `{GHC.Base.Monad m},
                  (a -> b -> c -> m d) -> list a -> list b -> list c -> m (list d).

Axiom zipWith3M_ : forall {m : Type -> Type},
                   forall {a : Type},
                   forall {b : Type},
                   forall {c : Type},
                   forall {d : Type},
                   forall `{GHC.Base.Monad m},
                   (a -> b -> c -> m d) -> list a -> list b -> list c -> m unit.

Axiom zipWith4M : forall {m : Type -> Type},
                  forall {a : Type},
                  forall {b : Type},
                  forall {c : Type},
                  forall {d : Type},
                  forall {e : Type},
                  forall `{GHC.Base.Monad m},
                  (a -> b -> c -> d -> m e) -> list a -> list b -> list c -> list d -> m (list e).

Axiom zipWithAndUnzipM : forall {m : Type -> Type},
                         forall {a : Type},
                         forall {b : Type},
                         forall {c : Type},
                         forall {d : Type},
                         forall `{GHC.Base.Monad m},
                         (a -> b -> m (c * d)%type) -> list a -> list b -> m (list c * list d)%type.

Axiom mapAndUnzip3M : forall {m : Type -> Type},
                      forall {a : Type},
                      forall {b : Type},
                      forall {c : Type},
                      forall {d : Type},
                      forall `{GHC.Base.Monad m},
                      (a -> m (b * c * d)%type) -> list a -> m (list b * list c * list d)%type.

Axiom mapAndUnzip4M : forall {m : Type -> Type},
                      forall {a : Type},
                      forall {b : Type},
                      forall {c : Type},
                      forall {d : Type},
                      forall {e : Type},
                      forall `{GHC.Base.Monad m},
                      (a -> m (b * c * d * e)%type) ->
                      list a -> m (list b * list c * list d * list e)%type.

Axiom mapAndUnzip5M : forall {m : Type -> Type},
                      forall {a : Type},
                      forall {b : Type},
                      forall {c : Type},
                      forall {d : Type},
                      forall {e : Type},
                      forall {f : Type},
                      forall `{GHC.Base.Monad m},
                      (a -> m (b * c * d * e * f)%type) ->
                      list a -> m (list b * list c * list d * list e * list f)%type.

Axiom mapAccumLM : forall {m : Type -> Type},
                   forall {acc : Type},
                   forall {x : Type},
                   forall {y : Type},
                   forall `{GHC.Base.Monad m},
                   (acc -> x -> m (acc * y)%type) -> acc -> list x -> m (acc * list y)%type.

Axiom mapSndM : forall {m : Type -> Type},
                forall {b : Type},
                forall {c : Type},
                forall {a : Type},
                forall `{GHC.Base.Monad m},
                (b -> m c) -> list (a * b)%type -> m (list (a * c)%type).

Axiom concatMapM : forall {m : Type -> Type},
                   forall {a : Type},
                   forall {b : Type},
                   forall `{GHC.Base.Monad m}, (a -> m (list b)) -> list a -> m (list b).

Axiom mapMaybeM : forall {m : Type -> Type},
                  forall {a : Type},
                  forall {b : Type},
                  forall `{GHC.Base.Monad m}, (a -> m (option b)) -> list a -> m (list b).

Axiom fmapMaybeM : forall {m : Type -> Type},
                   forall {a : Type},
                   forall {b : Type},
                   forall `{GHC.Base.Monad m}, (a -> m b) -> option a -> m (option b).

Axiom fmapEitherM : forall {m : Type -> Type},
                    forall {a : Type},
                    forall {b : Type},
                    forall {c : Type},
                    forall {d : Type},
                    forall `{GHC.Base.Monad m},
                    (a -> m b) ->
                    (c -> m d) -> Data.Either.Either a c -> m (Data.Either.Either b d).

Axiom anyM : forall {m : Type -> Type},
             forall {a : Type},
             forall `{GHC.Base.Monad m}, (a -> m bool) -> list a -> m bool.

Axiom allM : forall {m : Type -> Type},
             forall {a : Type},
             forall `{GHC.Base.Monad m}, (a -> m bool) -> list a -> m bool.

Axiom orM : forall {m : Type -> Type},
            forall `{GHC.Base.Monad m}, m bool -> m bool -> m bool.

Axiom foldlM : forall {m : Type -> Type},
               forall {a : Type},
               forall {b : Type},
               forall `{GHC.Base.Monad m}, (a -> b -> m a) -> a -> list b -> m a.

Axiom foldlM_ : forall {m : Type -> Type},
                forall {a : Type},
                forall {b : Type},
                forall `{GHC.Base.Monad m}, (a -> b -> m a) -> a -> list b -> m unit.

Axiom foldrM : forall {m : Type -> Type},
               forall {b : Type},
               forall {a : Type},
               forall `{GHC.Base.Monad m}, (b -> a -> m a) -> a -> list b -> m a.

Axiom maybeMapM : forall {m : Type -> Type},
                  forall {a : Type},
                  forall {b : Type},
                  forall `{GHC.Base.Monad m}, (a -> m b) -> option a -> m (option b).

Axiom whenM : forall {m : Type -> Type},
              forall `{GHC.Base.Monad m}, m bool -> m unit -> m unit.

(* Skipping definition `MonadUtils.unlessM' *)

(* External variables:
     Type bool list op_zt__ option unit Data.Either.Either GHC.Base.Monad
*)
