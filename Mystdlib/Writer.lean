import Mystdlib.State
import Mathlib.Control.Monad.Writer
import Mystdlib.Optics.Tambara

universe u v
variable {m : Type u -> Type v} [Monad m]
variable {ω : Type u} [Append ω] [EmptyCollection ω]

instance [MonadWriter ω m] : MonadWriter ω (OptionT m) where
  tell := fun w => tell (M := m) w
  listen := fun xm => OptionT.mk do
    let (a, w) <- listen xm.run
    return a.map (Prod.mk · w)
  pass := fun xm => OptionT.mk <| pass do
      let x? <- xm.run
      return match x? with | .some (x, f) => (.some x, f) | _ => (.none, id)

instance [MonadWriter ω m] : MonadWriter ω (ExceptT ε m) where
  tell := fun w => tell (M := m) w
  listen := fun xm => ExceptT.mk do
    let (e, w) <- listen xm.run
    return e.map (Prod.mk · w)
  pass := fun xm => ExceptT.mk <| pass do
    let xe <- xm.run
    return match xe with | .ok (x, f) => (.ok x, f) | .error x => (.error x, id)

instance [MonadExceptOf ε m] : MonadExceptOf ε (WriterT ω m) where
  throw := throw 
  tryCatch := tryCatch

instance [MonadStateOfLens ω m] [Append ω] : MonadWriter ω m where
  tell := fun w => do let σ <- getOfLens; setOfLens (σ ++ w)
  listen := fun x => do let σ <- getOfLens; return (<- x, σ)
  pass := fun x => do let r <- x; let σ <- getOfLens; setOfLens (r.snd σ); return r.fst





