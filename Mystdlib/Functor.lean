import Mathlib.Control.Functor

instance
  [Functor G]
  [Functor F]
  : Functor (G ∘ F) := (inferInstance : Functor (Functor.Comp G F))

instance [instf : Applicative F] [instg : Applicative G] : Applicative (G ∘ F) :=
  (inferInstance : Applicative (Functor.Comp G F))

instance : Functor (Prod α) where
  map := fun f x => (x.fst, f x.snd)

instance : Applicative List where
  pure := ([·])
  seq := fun lf l => lf.foldl (fun acc a => (l ()).foldl (fun acc b => acc.push (a b)) acc) #[] |>.toList

instance : Applicative Array where
  pure := (#[·])
  seq := fun arf ar => 
    arf.foldl (fun acc a => (ar ()).foldl (fun acc b => acc.push (a b)) acc) #[]

instance : Functor (Vector · n) where
  map := fun f ⟨l, h⟩ => ⟨Array.map f l, by grind⟩
