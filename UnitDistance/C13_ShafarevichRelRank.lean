import Mathlib
import UnitDistance.C11_ProPGroups
import UnitDistance.C05_MaximalUnramified

set_option linter.style.longLine false

namespace UnitDistance.NumberTheory

open UnitDistance.ProP

/-- Shafarevich's relation-rank estimate (Proposition A.10):
    For a totally real cubic number field F with ζ₃ ∉ F, and G = Gal(F^{ur,3}/F),
    there exists an absolute constant C₀ : ℕ such that r(G) ≤ d(G) + C₀. -/
axiom shafarevich_relRank_estimate
    (F : Type*) [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (hcubic : Module.finrank ℚ F = 3)
    (G := maxUnramifiedProPGaloisGroup F 3) :
    ∃ C₀ : ℕ, G.relRank ≤ G.genRank + C₀

end UnitDistance.NumberTheory
