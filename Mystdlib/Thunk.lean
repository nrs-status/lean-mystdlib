

instance [inst : Nonempty α] : Nonempty (Thunk α) :=
  inst.rec fun a => ⟨.mk fun _ => a⟩
