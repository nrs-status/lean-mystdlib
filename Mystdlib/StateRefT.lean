import Lean

open Lean

variable [Monad m]

instance [AddErrorMessageContext m] : AddErrorMessageContext (StateRefT' ω σ m) where
  add := fun stx msg _ => AddErrorMessageContext.add stx msg

variable {σ m}


instance [MonadRecDepth m] : MonadRecDepth (StateRefT' ω σ m) where
  withRecDepth := fun n xm f => MonadRecDepth.withRecDepth n (xm f)
  getRecDepth := fun _ => MonadRecDepth.getRecDepth
  getMaxRecDepth := fun _ => MonadRecDepth.getMaxRecDepth

