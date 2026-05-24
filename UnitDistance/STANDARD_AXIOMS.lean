import UnitDistance.CinfraProPGroupType

set_option linter.style.longLine false

/-!
# Standard Axioms

This file collects the external theorems absent from Mathlib 4.29.1
that the unit-distance proof depends on. All axioms here have is_assumption: true
in the IR. Literature citations are provided for each.

Per UNITY.md invariant 6, these are the ONLY permitted axioms in the project.
-/

namespace UnitDistance.ProP

/-- **Golod–Shafarevich inequality** (Proposition A.9):
    A nontrivial finitely generated pro-p group G with 4·r(G) ≤ d(G)² is infinite.

    References: [GS64] Golod–Shafarevich 1964, [Koc02, Chapter 11].
    Mathlib gap: requires completed group ring Hilbert series + cohomology of pro-p groups.
    is_assumption: true (listed as permitted axiom in UNITY.md). -/
axiom golodShafarevich_criterion (G : ProPGroup) :
    4 * G.relRank ≤ G.genRank ^ 2 → G.isInfinite

end UnitDistance.ProP
