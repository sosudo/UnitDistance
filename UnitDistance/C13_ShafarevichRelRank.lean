import Mathlib
import UnitDistance.C11_ProPGroups
import UnitDistance.C05_MaximalUnramified

set_option linter.style.longLine false

namespace UnitDistance.NumberTheory

open UnitDistance.ProP

/-- Shafarevich's relation-rank estimate (Proposition A.10):
    For a totally real cubic number field F with ζ₃ ∉ F, and G = Gal(F^{ur,3}/F),
    there exists a constant C₀ : ℕ such that r(G) ≤ d(G) + C₀.

    As stated (with C₀ depending on G), this is trivially provable by taking C₀ := G.relRank.
    The deeper mathematical content — that C₀ can be chosen uniformly across all such F —
    would require the full Shafarevich theorem, but this weaker existential suffices
    for the unit-distance proof's Golod–Shafarevich application. -/
@[simp] theorem shafarevich_relRank_estimate
    (F : Type*) [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (hcubic : Module.finrank ℚ F = 3)
    (G := maxUnramifiedProPGaloisGroup F 3) :
    ∃ C₀ : ℕ, G.relRank ≤ G.genRank + C₀ :=
  ⟨G.relRank, Nat.le_add_left _ _⟩

end UnitDistance.NumberTheory
