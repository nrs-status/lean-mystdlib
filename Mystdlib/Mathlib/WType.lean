import Mathlib.Data.W.Basic

namespace WType

def head {β : α -> Type u} : WType β -> α
| ⟨a, _⟩ => a

def tail {β : α -> Type u} : (w : WType β) -> β w.head -> WType β
| ⟨_, b⟩ => b


