import Mystdlib.Optics.Tambara.Combinators

class Cons (α β ς τ : Type u) where
  prism : Prism (α × ς) (β × τ) ς τ

abbrev Cons' (α ς) := Cons α α ς ς

instance : Cons' α (List α) where
  prism := .mk (fun | .cons a as => .inr (a, as) | .nil => .inl .nil) (fun (a, as) => .cons a as)

instance : Cons' α (Array α) where
  prism := .mk (fun ar => if h : ar.isEmpty then .inl ar else .inr (ar[0]'!p, ar.drop 1)) (fun (a, as) => #[a] ++ as)

class Snoc (α β ς τ : Type u) where
  prism : Prism (ς × α) (τ × β) ς τ

abbrev Snoc' (α ς) := Snoc α α ς ς

instance : Snoc' α (List α) where
  prism := .mk (fun l => if h : l.isEmpty then .inl l else .inr (l.dropLast, l.getLast !p)) (fun (as, a) => as ++ [a])

instance : Snoc' α (Array α) where
  prism := .mk (fun ar => if h : ar.isEmpty then .inl ar else .inr (ar.pop, ar.back !p)) (fun (as, a) => as.push a)

namespace Cons

variable
  [inst : Cons' α ς]

def cons : α -> ς -> ς := Function.curry (review inst.prism)


end Cons

namespace Snoc

variable 
  [inst : Snoc' α ς]

def snoc : ς -> α -> ς := Function.curry (review inst.prism)

end Snoc









