import Mathlib.Control.Monad.Writer

universe u
variable (m : Type -> Type u) [Monad m]
variable (ω : Type) [Append ω] [EmptyCollection ω]

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


