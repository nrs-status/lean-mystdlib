
structure Lens α β where
  get : α -> β
  set : α -> β -> α

def Lens.compose (lb : Lens β γ) (la : Lens α β) : Lens α γ where
  get := lb.get ∘ la.get
  set := fun prev x => la.set prev (lb.set (la.get prev) x)

def Splitter α β := Lens (Option α) (Option β)

def liftGet {α : Type} (zerolike : α -> Bool) (getf : α -> Option β) : Option α -> Option β
| .none => .none
| .some a => if zerolike a then .none else getf a

def splitToSet 
  (residue : α -> α) 
  (unsplit : α -> β -> α) 
  (pure : β -> α) 
  : Option α -> Option β -> Option α
  | .none, .none => .none
  | .none, .some b => .some <| pure b
  | .some a, .none => .some <| residue a
  | .some a, some b => .some <| unsplit (residue a) b

def arraySplitter : Splitter (Array α) α where
  get := liftGet Array.isEmpty Array.back?
  set := splitToSet Array.pop (·.push ·) (#[·])

structure TreeZipper α β where
  target : Option β
  ctxs : Array α
  lefts : Array (Array β)
  rights : Array (Array β)

open Lean in
inductive StxZipperHead 
| node : SourceInfo -> SyntaxNodeKind -> StxZipperHead
| atom : SourceInfo -> String -> StxZipperHead
| ident : Substring.Raw -> Name -> List Lean.Syntax.Preresolved -> StxZipperHead

def StxZipper := TreeZipper StxZipperHead Lean.Syntax

def recordLensToSplitter [BEq β] (nilrecord : α) (lens : Lens α β) : Splitter α β where
  get := liftGet (fun x => (· == lens.get nilrecord) <| lens.get x) (.some <| lens.get ·)
  set := splitToSet (lens.set · <| lens.get nilrecord) lens.set (lens.set nilrecord ·) 

def nilZipper : TreeZipper α β := .mk .none #[] #[] #[]

def leftsLens : Lens (TreeZipper α β) (Array (Array β)) := 
  Lens.mk TreeZipper.lefts ({ · with lefts := ·})

def leftsSplitter [BEq β] : Splitter (TreeZipper α β) (Array (Array β)) := 
  recordLensToSplitter nilZipper leftsLens
  
def leftSplitter [BEq β] : Splitter (TreeZipper α β) (Array β) := 
  arraySplitter.compose (leftsSplitter (α := α) (β := β))

def immediateLeftSplitter [BEq β] : Splitter (TreeZipper α β) β := 
  arraySplitter.compose leftSplitter

def rightsLens : Lens (TreeZipper α β) (Array (Array β)) where
  get := TreeZipper.rights
  set := ({ · with rights := · })

def rightsSplitter [BEq β] : Splitter (TreeZipper α β) (Array (Array β)) :=
  recordLensToSplitter nilZipper rightsLens

def rightSplitter [BEq β] : Splitter (TreeZipper α β) (Array β) :=
  arraySplitter.compose rightsSplitter

def immediateRightSplitter [BEq β] : Splitter (TreeZipper α β) β :=
  arraySplitter.compose rightSplitter

def targetLens [BEq β] : Lens (TreeZipper α β) (Option β) where
  get := TreeZipper.target
  set := ({ · with target := ·})

def targetSplitter [BEq β] : Splitter (TreeZipper α β) (Option β) :=
  recordLensToSplitter nilZipper targetLens

def ctxsLens [BEq β] : Lens (TreeZipper α β) (Array α) where
  get := TreeZipper.ctxs
  set := ({ · with ctxs := · })

def ctxsSplitter [BEq α] [BEq β] : Splitter (TreeZipper α β) (Array α) :=
  recordLensToSplitter nilZipper ctxsLens

def ctxSplitter [BEq α] [BEq β] : Splitter (TreeZipper α β) α :=
  arraySplitter.compose ctxsSplitter

def move (prevPos nextPos : Splitter (TreeZipper α β) γ) (xm : Option (TreeZipper α β)) : TreeZipper α β :=
  let valToMove := prevPos.get xm
  let woPrevPosVal := nextPos.set xm .none
  let appending := nextPos.set woPrevPosVal valToMove
  match appending with
  | .none => nilZipper
  | .some x => x

