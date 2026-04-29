import Mystdlib.Optics.Tambara.Combinators
import Mystdlib.Optics.Tambara.Each


-- notation; most are taken from Control.Lens.Operators

infixr:90 "<∘>" => Tamb.ProfOptic.compose

infixr:40 "%~" => Tamb.ProfOptic.over

infixr:40 ".~" => Tamb.ProfOptic.set

infixl:80 "^?" => flip Tamb.ProfOptic.preview

infixr:80 "#" => Tamb.ProfOptic.review

infixr:80 "^.." => flip Tamb.ProfOptic.toListOf

def notation_view
  (s : ς)
  (x : Tamb.ProfOptic l α β ς τ)
  [Tamb.Tambs l (fun x _ => x -> α)]
  : α
  := x.view s

infixl:80 "^." => notation_view


