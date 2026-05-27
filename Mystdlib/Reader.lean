import Lean

open Lean

instance [Monad m] [MonadRef m] : MonadRef (ReaderT ξ m) where
  getRef := fun _ => getRef
  withRef := fun stx xm f => withRef stx (xm f)

instance [Monad m] [MonadQuotation m] : MonadQuotation (ReaderT ξ m) where
  getCurrMacroScope := fun _ => getCurrMacroScope
  getContext := fun _ => MonadQuotation.getContext
  withFreshMacroScope := fun xm f => withFreshMacroScope (xm f)

instance [Lean.AddErrorMessageContext m] : Lean.AddErrorMessageContext (ReaderT ξ m) where
  add := fun stx msg _ => Lean.AddErrorMessageContext.add stx msg

instance [MonadRecDepth m] : MonadRecDepth (ReaderT ξ m) where
  withRecDepth := fun n xm f => MonadRecDepth.withRecDepth n (xm f)
  getRecDepth := fun _ => MonadRecDepth.getRecDepth
  getMaxRecDepth := fun _ => MonadRecDepth.getMaxRecDepth
