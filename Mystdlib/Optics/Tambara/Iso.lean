import Mystdlib.Optics.Tambara.Combinators

namespace Tamb

def Iso.under
  (x : Iso α β ς τ)
  := (x.view ∘ · ∘ x.review)

def Iso.re
  (x : Iso α β ς τ)
  : Iso τ ς β α 
  := .mk x.review x.view


