
structure Cont where
  ops : Type
  ar : ops -> Type

inductive W (ops : Type) (ar : ops -> Type)
| sup : (op : ops) -> (ar op -> W ops ar) -> W ops ar

def Cont.W (cont : Cont) : Type := _root_.W cont.ops cont.ar

structure ICont (I : Type) where
  ops : I -> Type
  ar : (i : I) -> ops i -> I -> Type

inductive IW (I : Type) 
  (ops : I -> Type)
  (ar : (i : I) -> ops i -> I -> Type) : I -> Type
| sup : {i : I} -> (op : ops i) -> ({i' : I} -> ar i op i' -> IW I ops ar i') -> IW I ops ar i

def ICont.IW (icont : ICont I) : I -> Type := 
  _root_.IW I icont.ops icont.ar

@[reducible]
def ICont.concat (ica icb : ICont I) : ICont I where
  ops := fun i => ica.ops i ⊕ icb.ops i
  ar := fun i x i' => match x with
  | .inl v => ica.ar i v i'
  | .inr v => icb.ar i v i'

structure Embedding (I IJ : Type) where
  to : I -> IJ
  from_ : IJ -> Option I
  subtype_p : ∀i, .some i = from_ (to i)

@[reducible]
def ICont.concat_embedding (p : Embedding I IJ) (ica : ICont I) (icb : ICont IJ) : ICont IJ where
  ops := fun ij => match p.from_ ij with
  | .none => icb.ops ij
  | .some x => ica.ops x ⊕ icb.ops ij
  ar := fun ij x ij' => match h : p.from_ ij with
  | .none => by rw [h] at x; simp at x; exact icb.ar ij x ij'
  | .some xx => match h' : p.from_ ij' with
   | .none => by rw [h] at x; simp at x; exact match x with
    | .inl x' => Empty
    | .inr x' => icb.ar _ x' ij'
   | .some xxx => by rw [h] at x; simp at x; exact match x with
    | .inl x' => ica.ar _ x' xxx
    | .inr x' => icb.ar _ x' ij'


@[reducible]
def Ext (σ : Cont) : Type -> Type :=
  fun α => (op : σ.ops) × ((σ.ar op) -> α)

@[reducible]
def Ext.W {σ} (x : Ext σ σ.W) : σ.W := 
  .sup x.1 x.2 

@[reducible]
def Alg (σ : Cont) (α : Type) : Type := Ext σ α -> α

def cata (alg : Alg σ α) : σ.W -> α :=
  fun ⟨op, f⟩ => alg ⟨op, fun x => cata alg (f x)⟩

@[reducible]
def lAlg (σ : Cont) (γ η : Type) := Ext σ (γ × η) -> γ

@[reducible]
def rAlg (σ : Cont) (γ η : Type) := Ext σ (γ × η) -> η

def mutu (lalg : lAlg σ γ η) (ralg : rAlg σ γ η) : (σ.W -> γ) × (σ.W -> η) := 
  let alg x : γ × η := (lalg x, ralg x)
  ((cata alg · |>.fst), (cata alg · |>.snd))

def zygo (alga : lAlg σ γ η) (algb : Alg σ η) : σ.W -> γ := fun mu =>
  (mutu alga (algb ∘ (fun ext => ⟨ext.1, Prod.snd ∘ ext.2⟩)) |>.fst) mu

@[reducible]
def IExt (ζ : ICont I) (P : I -> Type) : I -> Type :=
  fun i => (op : ζ.ops i) × ({i' : I} -> ζ.ar i op i' -> P i')

@[reducible]
def IExt.W {ζ : ICont I} (x : (i : I) -> IExt ζ ζ.IW i) : (i : I) -> ζ.IW i := 
  fun i => IW.sup (x i).1 (x i).2

@[reducible]
def IExt.W' {ζ : ICont I} : {i : I} -> (x : IExt ζ ζ.IW i) -> ζ.IW i := 
  fun x => IW.sup x.1 x.2

@[reducible]
def IAlg (ζ : ICont I) (P : I -> Type) : Type :=
  {i : I} -> IExt ζ P i -> P i

def icata {P : I -> Type} (ialg : IAlg ζ P) : {i : I} -> ζ.IW i -> P i :=
  fun ⟨iop, if_⟩ => ialg ⟨iop, fun x => icata ialg (if_ x)⟩


