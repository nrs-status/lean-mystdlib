import Mystdlib.General

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

def FunList (ς α β : Type) : Type :=
  Σn, { l : List ς // l.length = n } × FunList.unfold_type n α β

instance : Functor (FunList ς α ·) where
  map := fun f ⟨n, (l, t)⟩ => ⟨n, (l, FunList.unfold_type_fmap f t)⟩

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
