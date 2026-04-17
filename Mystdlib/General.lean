import Lean

instance [Inhabited x] : Inhabited (x ⊕ y) where
  default := .inl default

instance [Inhabited y] : Inhabited (x ⊕ y) where
  default := .inr default


def Prod.assoc : α × β × γ -> (α × β) × γ :=
  fun (a, b, c) => ((a, b), c)

def Prod.assoc_inv : (α × β) × γ -> α × β × γ :=
  fun ((a, b), c) => (a, b, c)

def Sum.assoc : α ⊕ β ⊕ γ -> (α ⊕ β) ⊕ γ :=
  Sum.elim (.inl ∘ .inl) (Sum.elim (.inl ∘ .inr) .inr)

def Sum.assoc_inv : (α ⊕ β) ⊕ γ -> α ⊕ β ⊕ γ :=
  Sum.elim (Sum.elim .inl (.inr ∘ .inl)) (.inr ∘ .inr)

abbrev fmap [Functor F] (f : α -> β) (xfα : F α) : F β := Functor.map f xfα

instance [Functor F] [Functor G] : Functor (G ∘ F) where
  map := fun f => ((Functor.map (Functor.map f)) ·)

instance [instf : Applicative F] [instg : Applicative G] : Applicative (G ∘ F) where
    pure := fun a => let aux := instg.pure a; let r := fmap instf.pure aux; r
    seq := fun f g =>   instg.seq (fmap (fun f' g' => instf.seq f' (fun _ => g')) f) g


def Monad.join [Monad m] : m (m α) -> m α :=
  fun xm => do (<- xm)

instance : Monad List where
  pure := ([ · ])
  bind := fun l f => List.flatten (fmap f l)


def mapA_attaching {m : Type u → Type v} [Applicative m] {α : Type w} {β : Type u} (f : α → m β) : { l : List α // l.length = n } -> m { l : List β // l.length = n } :=
  fun ⟨l, p⟩ => match l with
  | []    => pure ⟨∅, by simp at p; simpa⟩
  | .cons a as => 
    fmap (fun b x => ⟨.cons b x.1, by grind⟩) (f a) <*> mapA_attaching f ⟨as, rfl⟩
  --List.cons <$> f a <*> mapA_attaching f as



--

syntax (name := recur_pdescr) "recur" : term

open Lean Elab Term in
@[term_elab recur_pdescr]
def recur_stx_elab : TermElab := fun _ et => do
  let .some decl_nm <- getDeclName? | throwError "could not get decl name"
  let e <- elabTerm (mkIdent decl_nm) et
  return e

--

syntax (name := holeModReduction_pdescr) "_r" : term

open Lean Elab Term in
@[term_elab holeModReduction_pdescr]
def holeModReductionElab : TermElab := fun _ expectedType? => do
  let .some expectedType := expectedType? | throwError "no expected type"
  let reducedExpectedType <- Lean.Meta.reduce expectedType true false true
  let w_pp <- Lean.PrettyPrinter.ppExpr reducedExpectedType
  logInfo w_pp
  let hole <- elabTerm (<- `(_)) expectedType
  .pure hole


--

syntax (name := elab_w_pdescr) "elab_w " term : term

open Lean Elab Term Meta in
@[term_elab elab_w_pdescr]
def elab_w_elab : TermElab := fun stx et? => 
  match stx with
  | `(elab_w $x) => do
    let `(fun $_ => $_) := x | throwUnsupportedSyntax
    let val : Expr := Lean.mkForall `stx .default 
      (<- mkAppM ``Option #[mkConst ``Expr])
      (<- mkAppM ``TermElabM #[mkConst ``Expr])
    let tac <- unsafe evalTerm (Option Expr -> TermElabM Expr) val x
    tac et?
  | _ => throwUnsupportedSyntax

--

macro "#run_elab " x:doSeq : command => `(#eval show Lean.Elab.TermElabM Unit from do $x)


--

syntax:max (name := mod_subtype_pdescr) term "<:" : term
macro_rules
| `($(x)<:) => `(⟨$x, (by repeat first | rfl | native_decide | simp | simp_all | grind)⟩)

syntax:max (name := bang_p_pdescr) "!p" : term
macro_rules
| `(!p) => `(by repeat first | rfl | native_decide | simp | simp_all | grind)

--

elab "#grab" c:command : command => Lean.logInfo (toString c)

elab "#grab_expand" c:command : command => do
  let x <- Lean.Elab.liftMacroM (Lean.expandMacros c)
  Lean.logInfo x

--

syntax (name := mod_match_pdescr) term " %fun| " term " => " term : term
macro_rules 
| `($x %fun| $y => $z) => `(fun | $y => $z | v => $x v)


