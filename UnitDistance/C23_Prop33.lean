import UnitDistance.C11_ProPGroups

set_option linter.style.longLine false

namespace UnitDistance.ProP

/-- Proposition 3.3 (Frattini–Burnside, citing Proposition A.8):
    For a finitely generated pro-p group G, if g₁,...,gₖ ∈ Φ(G) generate
    a closed normal subgroup N, then d(G/N) = d(G) and r(G/N) ≤ r(G)+k. -/
theorem prop33_frattiniQuotientRanks (G N : ProPGroup) (k : ℕ) :
    ProPGroup.genRank (G.quotient N) = ProPGroup.genRank G ∧
    ProPGroup.relRank (G.quotient N) ≤ ProPGroup.relRank G + k := by
  sorry

end UnitDistance.ProP
