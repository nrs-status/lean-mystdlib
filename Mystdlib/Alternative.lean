import Mystdlib.Functor

instance : Alternative List where
  failure := .nil
  orElse := fun l f => if l.isEmpty then f () else l

instance : Alternative Array where
  failure := #[]
  orElse := fun ar f => if ar.isEmpty then f () else ar

instance [Monad m] [Alternative m] : Alternative (ExceptT ε m) where
  failure := ExceptT.mk failure
  orElse := fun xm ym => ExceptT.mk <| Alternative.orElse xm.run ym

