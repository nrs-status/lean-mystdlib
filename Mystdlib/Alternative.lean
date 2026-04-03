
instance : Applicative List where
  pure := ([·])
  seq := fun lf l => lf.foldl (fun acc a => (l ()).foldl (fun acc b => acc.push (a b)) acc) #[] |>.toList

instance : Alternative List where
  failure := .nil
  orElse := fun l f => if l.isEmpty then f () else l

instance : Applicative Array where
  pure := (#[·])
  seq := fun arf ar => 
    arf.foldl (fun acc a => (ar ()).foldl (fun acc b => acc.push (a b)) acc) #[]

instance : Alternative Array where
  failure := #[]
  orElse := fun ar f => if ar.isEmpty then f () else ar

instance [Monad m] [Alternative m] : Alternative (ExceptT ε m) where
  failure := ExceptT.mk failure
  orElse := fun xm ym => ExceptT.mk <| Alternative.orElse xm.run ym

