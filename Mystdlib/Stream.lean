import Mystdlib.Thunk

namespace Stream

structure StreamImpl (α : Type) where
  head : α
  tail : Thunk (StreamImpl α)

opaque StreamRef (α : Type) : NonemptyType.{0}

structure Stream (α : Type) where
  private mk' :: 
  val : (StreamRef α).type
  nonempty : Nonempty α

instance [Nonempty α] : Nonempty (Stream α) := 
  (StreamRef α).2.rec (⟨·, inferInstance⟩)

unsafe def Stream.mk_impl [Nonempty α] (a : α) (b : Thunk (Stream α)) : Stream α :=
  unsafeCast (StreamImpl.mk a (unsafeCast b))

unsafe def Stream.head_impl [Nonempty α] (s : Stream α) : α :=
  (unsafeCast (β := StreamImpl α) s).head

unsafe def Stream.tail_impl [Nonempty α] (s : Stream α) : Thunk (Stream α) :=
  unsafeCast (unsafeCast (β := StreamImpl α) s).tail

variable {α β γ : Type} [Nonempty α] [Nonempty β] [Nonempty γ]

@[implemented_by Stream.mk_impl]
opaque Stream.mk  (a : α) (b : Thunk (Stream α)) : Stream α 

@[implemented_by Stream.head_impl]
opaque Stream.head (s : Stream α) : α

@[implemented_by Stream.tail_impl]
opaque Stream.tail (s : Stream α) : Thunk (Stream α)
  

partial def always (a : α) : Stream α :=
  Stream.mk a (.mk fun _ => always a)

partial def repeat' (f : α -> α) (a : α) : Stream α :=
  .mk a (.mk fun _ => repeat' f (f a))

partial def zeroes := always 0

partial def nats := repeat' Nat.succ 0

partial def alt := repeat' Bool.not .true

partial def maps (f : α -> β) (sa : Stream α) : Stream β :=
  .mk (f sa.head) (.mk fun _ => maps f sa.tail.get)

partial def coiter (f : β -> α) (g : β -> β) (b : β) : Stream α :=
  .mk (f b) (.mk fun _ => coiter f g (g b))

def maps' (f : α -> β) : Stream α -> Stream β :=
  coiter (f ·.head) (·.tail.get)


partial def zipsWith (f : α -> β -> γ) (sa : Stream α) (sb : Stream β) : Stream γ :=
  .mk (f sa.head sb.head) (.mk fun _ => zipsWith f sa.tail.get sb.tail.get)
  
partial def zipsWith' (f : α -> β -> γ) (sa : Stream α) (sb : Stream β) : Stream γ :=
  coiter (fun x => f x.1.head x.2.head) (fun x => (x.1.tail.get, x.2.tail.get)) (Prod.mk sa sb)

partial def countDown (n : Nat) : Stream Nat :=
  .mk n (match n with | .zero => .mk fun _ => zeroes | .succ nn => countDown nn)

partial def countDown' : Nat -> Stream Nat :=
  coiter id (fun | .zero => .zero | .succ n => n)

partial def corec (f : β -> α) (g : β -> (Stream α) ⊕ β) (b : β) : Stream α :=
  .mk (f b) (match g b with | .inl s => s | .inr b' => .mk fun _ => corec f g b')

partial def countDown'' : Nat -> Stream Nat :=
  corec id (fun | .zero => .inl zeroes | .succ n => .inr n)

partial def append (l : List α) (s : Stream α) : Stream α :=
  match l with
  | .cons x xs => .mk x (append xs s)
  | .nil => s.tail.get

partial def append' (l : List α) (s : Stream α) : Stream α :=
  corec (fun | .nil => s.head | .cons x xs => x) (fun | .nil => .inl s.tail.get | .cons x xs => .inr xs) l



