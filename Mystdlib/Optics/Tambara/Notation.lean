import Mystdlib.Optics.Tambara.Combinators
import Mystdlib.Optics.Tambara.Each


-- notation; most are taken from Control.Lens.Operators

infixr:90 "<∘>" => Tamb.ProfOptic.compose

infixr:40 "%~" => over

infixr:40 ".~" => set

infixl:80 "^?" => flip preview

infixr:80 "#" => review

infixr:80 "^.." => flip Tamb.ProfOptic.toListOf

infixl:80 "^." => view
