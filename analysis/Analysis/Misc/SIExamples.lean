import Mathlib.Tactic
import Analysis.Misc.SI

instance instSI : UnitsSystem := SI

namespace SI
open UnitsSystem

variable (m:Mass) (v c:Speed) (F:Force) (p:Momentum) (E:Energy) (s:Length) (t:Time) (a:Acceleration)

#check F = m * a
#check E = m * c**2
-- #check E = m * c**3  -- fails to typecheck


end SI
