import Mystdlib.General

-- compare mniip's implementation @Bazaar

@[reducible]
def FunList.unfold_type (n : Nat) (α β : Type) : Type := 
  match n with
  | .zero => β
  | .succ nn => α -> recur nn α β

@[reducible]
def FunList.unfold_type_const {n : Nat} (b : β) : FunList.unfold_type n α β :=
  let rec aux : (n : Nat) -> FunList.unfold_type n α β
  | .zero => b
  | .succ _ => fun _ => aux _
  aux n

def FunList.unfold_type_fmap (f : β -> γ) : FunList.unfold_type n α β -> FunList.unfold_type n α γ :=
  match n with
  | .zero => f
  | .succ nn => fun g a => recur f (g a)

instance : Functor (FunList.unfold_type n α) where
  map := FunList.unfold_type_fmap

instance {n : Nat} : Functor (FunList.unfold_type n.succ α) where
  map := FunList.unfold_type_fmap

def FunList (ς α β : Type) : Type :=
  Σn, { l : List ς // l.length = n } × FunList.unfold_type n α β

instance : Functor (FunList ς α ·) where
  map := fun f ⟨n, (l, t)⟩ => ⟨n, (l, fmap f t)⟩

def FunList.unfold_type_join_aux : unfold_type (nn.succ + m) α β = unfold_type (nn + m).succ α β := by grind

def FunList.unfold_type_join : FunList.unfold_type n α (FunList.unfold_type m α β) -> FunList.unfold_type (n + m) α β := fun fl => match n with
| .zero => Eq.mpr (by simp) fl
| .succ nn => Eq.mpr FunList.unfold_type_join_aux (fun a => recur (fl a))

def FunList.seq_aux {nn : Nat} {α α_1 β : Type} : FunList.unfold_type nn.succ α (α_1 -> β) -> α_1 -> FunList.unfold_type nn.succ α β :=
  fun ufa => fun xa1 => FunList.unfold_type_fmap (fun f => f xa1) ufa 

def FunList.seq {α_1 β : Type} (x : FunList ς α (α_1 → β)) (y : (Unit → FunList ς α α_1)) : FunList ς α β :=
  let ⟨n, p⟩ := x
  match n with
  | .zero => fmap p.2 (y .unit)
  | .succ nn => 
    let := y .unit
    have new_unfold_type := FunList.unfold_type_join (FunList.unfold_type_fmap (FunList.seq_aux p.2) this.2.2)
    ⟨_, (⟨p.1 ++ this.2.1.1, by grind⟩, new_unfold_type)⟩

instance : Applicative (FunList ς α ·) where
  pure := fun a => ⟨0, (⟨.nil, !p⟩, a)⟩
  seq := FunList.seq

def FunList.unfold_aux {nn : Nat} : unfold_type nn.succ α β -> { l : List α // l.length = nn.succ } → β := 
  fun f => fun ⟨.cons x xs, p⟩ =>
    match nn with
    | .zero => f x
    | .succ nnn => recur (f x) ⟨xs, by grind⟩

def FunList.unfold : FunList ς α β -> (n : Nat) × ({ l : List ς // l.length = n} × ({ l : List α // l.length = n } -> β))
| ⟨n, (l, f)⟩ => Sigma.mk n <| Prod.mk l <|
  match n with
  | .zero => fun _ => f
  | .succ _ => FunList.unfold_aux f

def FunList.listfn_curry_aux {n : Nat}  (f : { l : List α // l.length = n.succ } -> β) (a : α) : {l : List α // l.length = n } -> β :=
  fun l => f ⟨.cons a l.1, by grind⟩

def FunList.listfn_curry (f : { l : List α // l.length = n } -> β) : FunList.unfold_type n α β := match n with
| .zero => f ∅<:
| .succ nn => fun a => FunList.listfn_curry (FunList.listfn_curry_aux f a)

def FunList.out (fl : FunList α β τ) : τ ⊕ (α × FunList α β (β -> τ)) :=
  let ⟨n, (l, f)⟩ := FunList.unfold fl
  match n with
  | .zero => .inl (f ∅<:)
  | .succ nn => .inr (l.1.head !p, ⟨nn, (l.1.tail<:, FunList.listfn_curry (fun l' b => f ⟨.cons b l'.1, !p⟩))⟩)

def FunList.in : τ ⊕ (α × FunList α β (β -> τ)) -> FunList α β τ
| .inl t => ⟨0, (∅<:, t)⟩
| .inr (a, ⟨n, (l, u)⟩) => ⟨n.succ, ((.cons a l)<:, fun b => FunList.unfold_type_fmap (· b) u)⟩


def FunList.fuse : FunList β β τ -> τ 
| ⟨n, (l, fl)⟩ => match n with
  | .zero => fl
  | .succ nn => fuse ⟨nn, (l.val.tail<:, fl <| l.val.head !p)⟩
termination_by x => x.fst

def FunList.unfold_type_expand_one : unfold_type nn.succ γ τ -> unfold_type nn γ (γ -> τ) :=
  fun f => match nn with
  | .zero => f
  | .succ nnn => fun y => recur (f y)


def FunList.in' : α × FunList α β (β -> τ) -> FunList α β τ
| (a, ⟨n, (l, utf)⟩) => match n with
  | .zero => ⟨1, (⟨[a], !p⟩, utf)⟩
  | .succ nn => 
    have : (a :: l.val).length = nn.succ.succ := by grind
    have thisa := FunList.unfold_type_expand_one utf
    have thisb (b) := FunList.unfold_type_fmap (fun f => f b) utf
    ⟨_, ((.cons a l.1)<:, by rw [this]; exact fun b => thisb b)⟩

def FunList.traverse [Applicative F] : (α -> F β) -> FunList α γ τ -> F (FunList β γ τ) :=
  fun f fl => match fl with
  | ⟨n, (l, fl)⟩ => match h : n with
    | .zero => pure ⟨_, (∅<:, fl)⟩
    | .succ nn =>
      match l with
      | ⟨.cons a as, p⟩ =>
        let r := FunList.traverse f ⟨nn, (⟨as, !p⟩, FunList.unfold_type_expand_one fl)⟩
        FunList.in' <$> (Prod.mk <$> f a <*> r)
termination_by _ x => x.fst

def FunList.single (a : α) : FunList α β β :=
  ⟨1, ([a]<:, id)⟩
