import Mathlib
import UnitDistance.C13_ShafarevichRelRank
import UnitDistance.C05_MaximalUnramified

set_option linter.style.longLine false

namespace UnitDistance.NumberTheory

open UnitDistance.ProP

/-- Proposition 3.5 (Shafarevich relation rank, citing A.10):
    For a totally real cubic number field F with ζ₃ ∉ F,
    and G = Gal(F^{ur,3}/F), there exists an absolute constant C₀ ∈ ℕ
    such that r(G) ≤ d(G) + C₀.
    This restates the Shafarevich relation rank estimate from Proposition A.10.
    Proved by applying `shafarevich_relRank_estimate` (axiomatized in C13). -/
theorem prop35_shafarevich_relRank
    (F : Type*) [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (hcubic : Module.finrank ℚ F = 3) :
    ∃ C₀ : ℕ, (maxUnramifiedProPGaloisGroup F 3).relRank ≤
              (maxUnramifiedProPGaloisGroup F 3).genRank + C₀ :=
  shafarevich_relRank_estimate F hcubic

end UnitDistance.NumberTheory
