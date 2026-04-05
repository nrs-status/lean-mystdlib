
opaque FixRef (f : Type -> Type) : NonemptyType.{0}

structure Fix (f : Type -> Type) where
  val : (FixRef f).type

instance : Nonempty (Fix f) :=
  (FixRef f).2.rec fun x => ⟨.mk x⟩

instance [Nonempty α] : Nonempty (Thunk α) := 
  (inferInstance : Nonempty α).rec fun x => ⟨.mk fun _ => x⟩

unsafe def Fix.in_impl (f : Type -> Type) : f (Thunk (Fix f)) -> Fix f := unsafeCast

@[implemented_by Fix.in_impl]
opaque Fix.in {f : Type -> Type} : f (Thunk (Fix f)) -> Fix f

unsafe def Fix.out_impl (f : Type -> Type) : Fix f -> [Inhabited (f (Thunk (Fix f)))] -> f (Thunk (Fix f)) :=
  fun x _ => unsafeCast x

instance : Inhabited (Fix f → [Inhabited (f (Thunk (Fix f)))] → f (Thunk (Fix f))) :=
  ⟨(fun _ ⟨y⟩ => y)⟩

@[implemented_by Fix.out_impl]
opaque Fix.out {f : Type -> Type}  : Fix f -> [Inhabited (f (Thunk (Fix f)))] -> f (Thunk (Fix f))

@[reducible]
def ListF (α β : Type) := Unit ⊕ (α × β)

@[reducible]
def List' (α : Type) := Fix (ListF α)

instance : Inhabited (ListF α (Thunk (Fix (ListF α)))) :=
  ⟨.inl .unit⟩

def List'.head : List' α -> Option α :=
  fun l => match Fix.out l with
  | .inl _ => .none
  | .inr (head, _) => head

def List'.tail : List' α -> List' α :=
  fun l => match Fix.out l with
  | .inl _ => Fix.in <| .inl .unit
  | .inr (_, tail) => tail.get

partial def List'.toList : List' α -> List α :=
  fun l => match Fix.out l with
  | .inl _ => .nil
  | .inr (head, tail) => .cons head <| List'.toList tail.get

