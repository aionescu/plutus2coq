(* Default settings (from HsToCoq.Coq.Preamble) *)

Generalizable All Variables.

Unset Implicit Arguments.
Set Maximal Implicit Insertion.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Coq.Program.Tactics.
Require Coq.Program.Wf.

(* Converted imports: *)

Require Control.Monad.Fail.
Require Control.Monad.Signatures.
Require Control.Monad.Trans.Class.
Require Data.Functor.Identity.
Require Data.Tuple.
Require GHC.Base.
Import GHC.Base.Notations.

(* Converted type declarations: *)

Inductive RWST r w s m a : Type :=
  | Mk_RWST (runRWST : r -> s -> m (a * s * w)%type) : RWST r w s m a.

Definition RWS r w s :=
  (RWST r w s Data.Functor.Identity.Identity)%type.

Arguments Mk_RWST {_} {_} {_} {_} {_} _.

Definition runRWST {r} {w} {s} {m} {a} (arg_0__ : RWST r w s m a) :=
  let 'Mk_RWST runRWST := arg_0__ in
  runRWST.

(* Midamble *)

Local Definition Monad__RWST_tmp {inst_w} {inst_m} {inst_r} {inst_s}
  `{GHC.Base.Monoid inst_w} `{GHC.Base.Monad inst_m}
   : forall {a} {b},
     (RWST inst_r inst_w inst_s inst_m) a ->
     (a -> (RWST inst_r inst_w inst_s inst_m) b) ->
     (RWST inst_r inst_w inst_s inst_m) b :=
  fun {a} {b} =>
    fun m k =>
      Mk_RWST (fun r s =>
                 let cont_0__ arg_1__ :=
                   let 'pair (pair a s') w := arg_1__ in
                   let cont_2__ arg_3__ :=
                     let 'pair (pair b s'') w' := arg_3__ in
                     GHC.Base.return_ (pair (pair b s'') (GHC.Base.mappend w w')) in
                   runRWST (k a) r s' GHC.Base.>>= cont_2__ in
                 runRWST m r s GHC.Base.>>= cont_0__).

(* Converted value declarations: *)

Local Definition Functor__RWST_fmap {inst_m : Type -> Type} {inst_r : Type}
  {inst_w : Type} {inst_s : Type} `{(GHC.Base.Functor inst_m)}
   : forall {a : Type},
     forall {b : Type},
     (a -> b) ->
     RWST inst_r inst_w inst_s inst_m a -> RWST inst_r inst_w inst_s inst_m b :=
  fun {a : Type} {b : Type} =>
    fun f m =>
      Mk_RWST (fun r s =>
                 GHC.Base.fmap (fun '(pair (pair a s') w) => pair (pair (f a) s') w) (runRWST m r
                                                                                              s)).

Local Definition Functor__RWST_op_zlzd__ {inst_m : Type -> Type} {inst_r : Type}
  {inst_w : Type} {inst_s : Type} `{(GHC.Base.Functor inst_m)}
   : forall {a : Type},
     forall {b : Type},
     a -> RWST inst_r inst_w inst_s inst_m b -> RWST inst_r inst_w inst_s inst_m a :=
  fun {a : Type} {b : Type} => Functor__RWST_fmap GHC.Base.∘ GHC.Base.const.

Program Instance Functor__RWST {m : Type -> Type} {r : Type} {w : Type} {s
   : Type} `{(GHC.Base.Functor m)}
   : GHC.Base.Functor (RWST r w s m) :=
  fun _ k__ =>
    k__ {| GHC.Base.fmap__ := fun {a : Type} {b : Type} => Functor__RWST_fmap ;
           GHC.Base.op_zlzd____ := fun {a : Type} {b : Type} => Functor__RWST_op_zlzd__ |}.

Local Definition Applicative__RWST_op_zlztzg__ {inst_w : Type} {inst_m
   : Type -> Type} {inst_r : Type} {inst_s : Type} `{GHC.Base.Monoid inst_w}
  `{GHC.Base.Functor inst_m} `{GHC.Base.Monad inst_m}
   : forall {a : Type},
     forall {b : Type},
     RWST inst_r inst_w inst_s inst_m (a -> b) ->
     RWST inst_r inst_w inst_s inst_m a -> RWST inst_r inst_w inst_s inst_m b :=
  fun {a : Type} {b : Type} =>
    fun arg_0__ arg_1__ =>
      match arg_0__, arg_1__ with
      | Mk_RWST mf, Mk_RWST mx =>
          Mk_RWST (fun r s =>
                     let cont_2__ arg_3__ :=
                       let 'pair (pair f s') w := arg_3__ in
                       let cont_4__ arg_5__ :=
                         let 'pair (pair x s'') w' := arg_5__ in
                         GHC.Base.return_ (pair (pair (f x) s'') (GHC.Base.mappend w w')) in
                       mx r s' GHC.Base.>>= cont_4__ in
                     mf r s GHC.Base.>>= cont_2__)
      end.

Local Definition Applicative__RWST_liftA2 {inst_w : Type} {inst_m
   : Type -> Type} {inst_r : Type} {inst_s : Type} `{GHC.Base.Monoid inst_w}
  `{GHC.Base.Functor inst_m} `{GHC.Base.Monad inst_m}
   : forall {a : Type},
     forall {b : Type},
     forall {c : Type},
     (a -> b -> c) ->
     RWST inst_r inst_w inst_s inst_m a ->
     RWST inst_r inst_w inst_s inst_m b -> RWST inst_r inst_w inst_s inst_m c :=
  fun {a : Type} {b : Type} {c : Type} =>
    fun f x => Applicative__RWST_op_zlztzg__ (GHC.Base.fmap f x).

Local Definition Applicative__RWST_op_ztzg__ {inst_w : Type} {inst_m
   : Type -> Type} {inst_r : Type} {inst_s : Type} `{GHC.Base.Monoid inst_w}
  `{GHC.Base.Functor inst_m} `{GHC.Base.Monad inst_m}
   : forall {a : Type},
     forall {b : Type},
     RWST inst_r inst_w inst_s inst_m a ->
     RWST inst_r inst_w inst_s inst_m b -> RWST inst_r inst_w inst_s inst_m b :=
  fun {a : Type} {b : Type} =>
    fun a1 a2 => Applicative__RWST_op_zlztzg__ (GHC.Base.id GHC.Base.<$ a1) a2.

Local Definition Applicative__RWST_pure {inst_w : Type} {inst_m : Type -> Type}
  {inst_r : Type} {inst_s : Type} `{GHC.Base.Monoid inst_w} `{GHC.Base.Functor
  inst_m} `{GHC.Base.Monad inst_m}
   : forall {a : Type}, a -> RWST inst_r inst_w inst_s inst_m a :=
  fun {a : Type} =>
    fun a =>
      Mk_RWST (fun arg_0__ arg_1__ =>
                 match arg_0__, arg_1__ with
                 | _, s => GHC.Base.return_ (pair (pair a s) GHC.Base.mempty)
                 end).

Program Instance Applicative__RWST {w : Type} {m : Type -> Type} {r : Type} {s
   : Type} `{GHC.Base.Monoid w} `{GHC.Base.Functor m} `{GHC.Base.Monad m}
   : GHC.Base.Applicative (RWST r w s m) :=
  fun _ k__ =>
    k__ {| GHC.Base.liftA2__ := fun {a : Type} {b : Type} {c : Type} =>
             Applicative__RWST_liftA2 ;
           GHC.Base.op_zlztzg____ := fun {a : Type} {b : Type} =>
             Applicative__RWST_op_zlztzg__ ;
           GHC.Base.op_ztzg____ := fun {a : Type} {b : Type} =>
             Applicative__RWST_op_ztzg__ ;
           GHC.Base.pure__ := fun {a : Type} => Applicative__RWST_pure |}.

(* Skipping all instances of class `GHC.Base.Alternative', including
   `Control.Monad.Trans.RWS.Lazy.Alternative__RWST' *)

Definition Monad__RWST_op_zgzgze__ {inst_w} {inst_m} {inst_r} {inst_s} `{_
   : GHC.Base.Monoid inst_w} `{_ : GHC.Base.Monad inst_m}
   : forall {a} {b},
     RWST inst_r inst_w inst_s inst_m a ->
     (a -> RWST inst_r inst_w inst_s inst_m b) ->
     RWST inst_r inst_w inst_s inst_m b :=
  fun {a} {b} => Monad__RWST_tmp.

Local Definition Monad__RWST_op_zgzg__ {inst_w : Type} {inst_m : Type -> Type}
  {inst_r : Type} {inst_s : Type} `{GHC.Base.Monoid inst_w} `{GHC.Base.Monad
  inst_m}
   : forall {a : Type},
     forall {b : Type},
     RWST inst_r inst_w inst_s inst_m a ->
     RWST inst_r inst_w inst_s inst_m b -> RWST inst_r inst_w inst_s inst_m b :=
  fun {a : Type} {b : Type} =>
    fun m k => Monad__RWST_op_zgzgze__ m (fun arg_0__ => k).

Local Definition Monad__RWST_return_ {inst_w : Type} {inst_m : Type -> Type}
  {inst_r : Type} {inst_s : Type} `{GHC.Base.Monoid inst_w} `{GHC.Base.Monad
  inst_m}
   : forall {a : Type}, a -> RWST inst_r inst_w inst_s inst_m a :=
  fun {a : Type} => GHC.Base.pure.

Program Instance Monad__RWST {w : Type} {m : Type -> Type} {r : Type} {s : Type}
  `{GHC.Base.Monoid w} `{GHC.Base.Monad m}
   : GHC.Base.Monad (RWST r w s m) :=
  fun _ k__ =>
    k__ {| GHC.Base.op_zgzg____ := fun {a : Type} {b : Type} =>
             Monad__RWST_op_zgzg__ ;
           GHC.Base.op_zgzgze____ := fun {a : Type} {b : Type} => Monad__RWST_op_zgzgze__ ;
           GHC.Base.return___ := fun {a : Type} => Monad__RWST_return_ |}.

Local Definition MonadTrans__RWST_lift {inst_w : Type} {inst_r : Type} {inst_s
   : Type} `{(GHC.Base.Monoid inst_w)}
   : forall {m : Type -> Type},
     forall {a : Type},
     forall `{GHC.Base.Monad m}, m a -> RWST inst_r inst_w inst_s m a :=
  fun {m : Type -> Type} {a : Type} `{GHC.Base.Monad m} =>
    fun m =>
      Mk_RWST (fun arg_0__ arg_1__ =>
                 match arg_0__, arg_1__ with
                 | _, s =>
                     m GHC.Base.>>= (fun a => GHC.Base.return_ (pair (pair a s) GHC.Base.mempty))
                 end).

Program Instance MonadTrans__RWST {w : Type} {r : Type} {s : Type}
  `{(GHC.Base.Monoid w)}
   : Control.Monad.Trans.Class.MonadTrans (RWST r w s) :=
  fun _ k__ =>
    k__ {| Control.Monad.Trans.Class.lift__ := fun {m : Type -> Type}
           {a : Type}
           `{GHC.Base.Monad m} =>
             MonadTrans__RWST_lift |}.

Local Definition MonadFail__RWST_fail {inst_w : Type} {inst_m : Type -> Type}
  {inst_r : Type} {inst_s : Type} `{GHC.Base.Monoid inst_w}
  `{Control.Monad.Fail.MonadFail inst_m}
   : forall {a : Type}, GHC.Base.String -> RWST inst_r inst_w inst_s inst_m a :=
  fun {a : Type} =>
    fun msg => Mk_RWST (fun arg_0__ arg_1__ => Control.Monad.Fail.fail msg).

Program Instance MonadFail__RWST {w : Type} {m : Type -> Type} {r : Type} {s
   : Type} `{GHC.Base.Monoid w} `{Control.Monad.Fail.MonadFail m}
   : Control.Monad.Fail.MonadFail (RWST r w s m) :=
  fun _ k__ =>
    k__ {| Control.Monad.Fail.fail__ := fun {a : Type} => MonadFail__RWST_fail |}.

(* Skipping all instances of class `GHC.Base.MonadPlus', including
   `Control.Monad.Trans.RWS.Lazy.MonadPlus__RWST' *)

(* Skipping all instances of class `Control.Monad.Fix.MonadFix', including
   `Control.Monad.Trans.RWS.Lazy.MonadFix__RWST' *)

(* Skipping all instances of class `Control.Monad.IO.Class.MonadIO', including
   `Control.Monad.Trans.RWS.Lazy.MonadIO__RWST' *)

Definition rws {r : Type} {s : Type} {a : Type} {w : Type}
   : (r -> s -> (a * s * w)%type) -> RWS r w s a :=
  fun f => Mk_RWST (fun r s => Data.Functor.Identity.Mk_Identity (f r s)).

Definition runRWS {r : Type} {w : Type} {s : Type} {a : Type}
   : RWS r w s a -> r -> s -> (a * s * w)%type :=
  fun m r s => Data.Functor.Identity.runIdentity (runRWST m r s).

Definition evalRWS {r : Type} {w : Type} {s : Type} {a : Type}
   : RWS r w s a -> r -> s -> (a * w)%type :=
  fun m r s => let 'pair (pair a _) w := runRWS m r s in pair a w.

Definition execRWS {r : Type} {w : Type} {s : Type} {a : Type}
   : RWS r w s a -> r -> s -> (s * w)%type :=
  fun m r s => let 'pair (pair _ s') w := runRWS m r s in pair s' w.

Definition mapRWST {m : Type -> Type} {a : Type} {s : Type} {w : Type} {n
   : Type -> Type} {b : Type} {w' : Type} {r : Type}
   : (m (a * s * w)%type -> n (b * s * w')%type) ->
     RWST r w s m a -> RWST r w' s n b :=
  fun f m => Mk_RWST (fun r s => f (runRWST m r s)).

Definition mapRWS {a : Type} {s : Type} {w : Type} {b : Type} {w' : Type} {r
   : Type}
   : ((a * s * w)%type -> (b * s * w')%type) -> RWS r w s a -> RWS r w' s b :=
  fun f =>
    mapRWST (Data.Functor.Identity.Mk_Identity GHC.Base.∘
             (f GHC.Base.∘ Data.Functor.Identity.runIdentity)).

Definition withRWST {r' : Type} {s : Type} {r : Type} {w : Type} {m
   : Type -> Type} {a : Type}
   : (r' -> s -> (r * s)%type) -> RWST r w s m a -> RWST r' w s m a :=
  fun f m => Mk_RWST (fun r s => Data.Tuple.uncurry (runRWST m) (f r s)).

Definition withRWS {r' : Type} {s : Type} {r : Type} {w : Type} {a : Type}
   : (r' -> s -> (r * s)%type) -> RWS r w s a -> RWS r' w s a :=
  withRWST.

Definition evalRWST {m : Type -> Type} {r : Type} {w : Type} {s : Type} {a
   : Type} `{GHC.Base.Monad m}
   : RWST r w s m a -> r -> s -> m (a * w)%type :=
  fun m r s =>
    let cont_0__ arg_1__ :=
      let 'pair (pair a _) w := arg_1__ in
      GHC.Base.return_ (pair a w) in
    runRWST m r s GHC.Base.>>= cont_0__.

Definition execRWST {m : Type -> Type} {r : Type} {w : Type} {s : Type} {a
   : Type} `{GHC.Base.Monad m}
   : RWST r w s m a -> r -> s -> m (s * w)%type :=
  fun m r s =>
    let cont_0__ arg_1__ :=
      let 'pair (pair _ s') w := arg_1__ in
      GHC.Base.return_ (pair s' w) in
    runRWST m r s GHC.Base.>>= cont_0__.

Definition asks {w : Type} {m : Type -> Type} {r : Type} {a : Type} {s : Type}
  `{GHC.Base.Monoid w} `{GHC.Base.Monad m}
   : (r -> a) -> RWST r w s m a :=
  fun f =>
    Mk_RWST (fun r s => GHC.Base.return_ (pair (pair (f r) s) GHC.Base.mempty)).

Definition reader {w : Type} {m : Type -> Type} {r : Type} {a : Type} {s : Type}
  `{GHC.Base.Monoid w} `{GHC.Base.Monad m}
   : (r -> a) -> RWST r w s m a :=
  asks.

Definition ask {w : Type} {m : Type -> Type} {r : Type} {s : Type}
  `{GHC.Base.Monoid w} `{GHC.Base.Monad m}
   : RWST r w s m r :=
  Mk_RWST (fun r s => GHC.Base.return_ (pair (pair r s) GHC.Base.mempty)).

Definition local {r : Type} {w : Type} {s : Type} {m : Type -> Type} {a : Type}
   : (r -> r) -> RWST r w s m a -> RWST r w s m a :=
  fun f m => Mk_RWST (fun r s => runRWST m (f r) s).

Definition writer {m : Type -> Type} {a : Type} {w : Type} {r : Type} {s : Type}
  `{GHC.Base.Monad m}
   : (a * w)%type -> RWST r w s m a :=
  fun '(pair a w) =>
    Mk_RWST (fun arg_1__ arg_2__ =>
               match arg_1__, arg_2__ with
               | _, s => GHC.Base.return_ (pair (pair a s) w)
               end).

Definition tell {m : Type -> Type} {w : Type} {r : Type} {s : Type}
  `{GHC.Base.Monad m}
   : w -> RWST r w s m unit :=
  fun w =>
    Mk_RWST (fun arg_0__ arg_1__ =>
               match arg_0__, arg_1__ with
               | _, s => GHC.Base.return_ (pair (pair tt s) w)
               end).

Definition listen {m : Type -> Type} {r : Type} {w : Type} {s : Type} {a : Type}
  `{GHC.Base.Monad m}
   : RWST r w s m a -> RWST r w s m (a * w)%type :=
  fun m =>
    Mk_RWST (fun r s =>
               let cont_0__ arg_1__ :=
                 let 'pair (pair a s') w := arg_1__ in
                 GHC.Base.return_ (pair (pair (pair a w) s') w) in
               runRWST m r s GHC.Base.>>= cont_0__).

Definition listens {m : Type -> Type} {w : Type} {b : Type} {r : Type} {s
   : Type} {a : Type} `{GHC.Base.Monad m}
   : (w -> b) -> RWST r w s m a -> RWST r w s m (a * b)%type :=
  fun f m =>
    Mk_RWST (fun r s =>
               let cont_0__ arg_1__ :=
                 let 'pair (pair a s') w := arg_1__ in
                 GHC.Base.return_ (pair (pair (pair a (f w)) s') w) in
               runRWST m r s GHC.Base.>>= cont_0__).

Definition pass {m : Type -> Type} {r : Type} {w : Type} {s : Type} {a : Type}
  `{GHC.Base.Monad m}
   : RWST r w s m (a * (w -> w))%type -> RWST r w s m a :=
  fun m =>
    Mk_RWST (fun r s =>
               let cont_0__ arg_1__ :=
                 let 'pair (pair (pair a f) s') w := arg_1__ in
                 GHC.Base.return_ (pair (pair a s') (f w)) in
               runRWST m r s GHC.Base.>>= cont_0__).

Definition censor {m : Type -> Type} {w : Type} {r : Type} {s : Type} {a : Type}
  `{GHC.Base.Monad m}
   : (w -> w) -> RWST r w s m a -> RWST r w s m a :=
  fun f m =>
    Mk_RWST (fun r s =>
               let cont_0__ arg_1__ :=
                 let 'pair (pair a s') w := arg_1__ in
                 GHC.Base.return_ (pair (pair a s') (f w)) in
               runRWST m r s GHC.Base.>>= cont_0__).

Definition state {w : Type} {m : Type -> Type} {s : Type} {a : Type} {r : Type}
  `{GHC.Base.Monoid w} `{GHC.Base.Monad m}
   : (s -> (a * s)%type) -> RWST r w s m a :=
  fun f =>
    Mk_RWST (fun arg_0__ arg_1__ =>
               match arg_0__, arg_1__ with
               | _, s =>
                   let 'pair a s' := f s in
                   GHC.Base.return_ (pair (pair a s') GHC.Base.mempty)
               end).

Definition get {w : Type} {m : Type -> Type} {r : Type} {s : Type}
  `{GHC.Base.Monoid w} `{GHC.Base.Monad m}
   : RWST r w s m s :=
  Mk_RWST (fun arg_0__ arg_1__ =>
             match arg_0__, arg_1__ with
             | _, s => GHC.Base.return_ (pair (pair s s) GHC.Base.mempty)
             end).

Definition put {w : Type} {m : Type -> Type} {s : Type} {r : Type}
  `{GHC.Base.Monoid w} `{GHC.Base.Monad m}
   : s -> RWST r w s m unit :=
  fun s =>
    Mk_RWST (fun arg_0__ arg_1__ =>
               GHC.Base.return_ (pair (pair tt s) GHC.Base.mempty)).

Definition modify {w : Type} {m : Type -> Type} {s : Type} {r : Type}
  `{GHC.Base.Monoid w} `{GHC.Base.Monad m}
   : (s -> s) -> RWST r w s m unit :=
  fun f =>
    Mk_RWST (fun arg_0__ arg_1__ =>
               match arg_0__, arg_1__ with
               | _, s => GHC.Base.return_ (pair (pair tt (f s)) GHC.Base.mempty)
               end).

Definition gets {w : Type} {m : Type -> Type} {s : Type} {a : Type} {r : Type}
  `{GHC.Base.Monoid w} `{GHC.Base.Monad m}
   : (s -> a) -> RWST r w s m a :=
  fun f =>
    Mk_RWST (fun arg_0__ arg_1__ =>
               match arg_0__, arg_1__ with
               | _, s => GHC.Base.return_ (pair (pair (f s) s) GHC.Base.mempty)
               end).

Definition liftCallCC {w : Type} {m : Type -> Type} {a : Type} {s : Type} {b
   : Type} {r : Type} `{GHC.Base.Monoid w}
   : Control.Monad.Signatures.CallCC m (a * s * w)%type (b * s * w)%type ->
     Control.Monad.Signatures.CallCC (RWST r w s m) a b :=
  fun callCC f =>
    Mk_RWST (fun r s =>
               callCC (fun c =>
                         runRWST (f (fun a =>
                                       Mk_RWST (fun arg_0__ arg_1__ => c (pair (pair a s) GHC.Base.mempty)))) r s)).

Definition liftCallCC' {w : Type} {m : Type -> Type} {a : Type} {s : Type} {b
   : Type} {r : Type} `{GHC.Base.Monoid w}
   : Control.Monad.Signatures.CallCC m (a * s * w)%type (b * s * w)%type ->
     Control.Monad.Signatures.CallCC (RWST r w s m) a b :=
  fun callCC f =>
    Mk_RWST (fun r s =>
               callCC (fun c =>
                         runRWST (f (fun a =>
                                       Mk_RWST (fun arg_0__ arg_1__ =>
                                                  match arg_0__, arg_1__ with
                                                  | _, s' => c (pair (pair a s') GHC.Base.mempty)
                                                  end))) r s)).

(* Skipping definition `Control.Monad.Trans.RWS.Lazy.liftCatch' *)

(* External variables:
     Monad__RWST_tmp Type op_zt__ pair tt unit Control.Monad.Fail.MonadFail
     Control.Monad.Fail.fail Control.Monad.Fail.fail__
     Control.Monad.Signatures.CallCC Control.Monad.Trans.Class.MonadTrans
     Control.Monad.Trans.Class.lift__ Data.Functor.Identity.Identity
     Data.Functor.Identity.Mk_Identity Data.Functor.Identity.runIdentity
     Data.Tuple.uncurry GHC.Base.Applicative GHC.Base.Functor GHC.Base.Monad
     GHC.Base.Monoid GHC.Base.String GHC.Base.const GHC.Base.fmap GHC.Base.fmap__
     GHC.Base.id GHC.Base.liftA2__ GHC.Base.mappend GHC.Base.mempty
     GHC.Base.op_z2218U__ GHC.Base.op_zgzg____ GHC.Base.op_zgzgze__
     GHC.Base.op_zgzgze____ GHC.Base.op_zlzd__ GHC.Base.op_zlzd____
     GHC.Base.op_zlztzg____ GHC.Base.op_ztzg____ GHC.Base.pure GHC.Base.pure__
     GHC.Base.return_ GHC.Base.return___
*)
