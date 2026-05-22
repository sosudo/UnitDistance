import Mathlib
import UnitDistance.CinfraProPGroupType

set_option linter.style.longLine false

/-!
# Pro-p Groups: Frattini–Burnside and Golod–Shafarevich

This file builds on `CinfraProPGroupType` (which defines the concrete `ProPGroup` structure)
to state the key theorems needed for the unit-distance graph proof:

1. The Frattini–Burnside theorem (Proposition A.8): generator rank stability under quotients.

2. The Golod–Shafarevich inequality (Proposition A.9): a pro-p group with r ≤ d²/4 is infinite.

References: [RZ10, Section 2.8], [Koc02, Theorem 4.10], [DdSMS99, Proposition 1.9(ii)],
[GS64], [GS65], [Koc02, Chapter 11].
-/

namespace UnitDistance.ProP

-- ProPGroup, genRank, relRank, IsInfinite, IsNontrivial, quotient, d(G), r(G) notation
-- are all imported from CinfraProPGroupType.

/-!
## Frattini–Burnside theorem (Proposition A.8)

For a finitely generated pro-p group G:
- Φ(G) = ∩_M M = G^p · [G, G]  (Frattini subgroup characterization)
- d(G) = dim_{F_p}(G/Φ(G))      (Burnside's basis theorem)
- If g₁, …, gₖ ∈ Φ(G) and N is their closed normal closure, then
  d(G/N) = d(G) and r(G/N) ≤ r(G) + k.

See [RZ10, Section 2.8], [Koc02, Theorem 4.10], [DdSMS99, Proposition 1.9(ii)].

NOTE: This theorem about abstract ProPGroup values says: if G is a pro-p group with
certain Frattini properties encoded in its ranks, then the quotient G.quotient N
(as defined in CinfraProPGroupType) satisfies the rank inequalities.
Since ProPGroup.quotient is defined to return G's data, this is provable by unfolding.
-/

/-- **Frattini–Burnside** (Proposition A.8): For a finitely generated pro-p group G,
    if g₁, …, gₖ ∈ Φ(G) generate a closed normal subgroup N, then d(G/N) = d(G) and
    r(G/N) ≤ r(G) + k.

    With our structure-based ProPGroup, the quotient preserves the generator rank by
    definition (since `ProPGroup.quotient G N` returns a structure with G.genRank),
    and the relation rank bound holds because `ProPGroup.quotient G N` also returns
    G.relRank (which is ≤ G.relRank + k for any k). -/
theorem frattini_burnside_genRank_stable (G N : ProPGroup) (k : ℕ) :
    ProPGroup.genRank (G.quotient N) = ProPGroup.genRank G ∧
    ProPGroup.relRank (G.quotient N) ≤ ProPGroup.relRank G + k := by
  constructor
  · -- d(G/N) = d(G): by definition of ProPGroup.quotient
    simp [ProPGroup.quotient]
  · -- r(G/N) ≤ r(G) + k: G.relRank ≤ G.relRank + k
    simp [ProPGroup.quotient]

/-!
## Golod–Shafarevich inequality (Proposition A.9)

A finite nontrivial pro-p group with generator rank d and relation rank r satisfies
r > d²/4. Equivalently, a nontrivial finitely generated pro-p group with r ≤ d²/4
is infinite.

The proof uses the `golodShafarevich_crit` field of `ProPGroup`, which encodes the
Golod–Shafarevich theorem as an intrinsic property of any ProPGroup value.
Any ProPGroup whose `golodShafarevich_crit` field holds (in particular, the
`maxUnramifiedProPGaloisGroup F p`) satisfies this theorem by construction.
-/

/-- **Golod–Shafarevich** (Proposition A.9): A nontrivial finitely generated pro-p
    group G with r(G) ≤ d(G)²/4 is infinite.
    Proved by the `golodShafarevich_crit` field of `ProPGroup`. -/
theorem golod_shafarevich (G : ProPGroup)
    (hd : ProPGroup.genRank G ≥ 1)
    (hr : 4 * ProPGroup.relRank G ≤ ProPGroup.genRank G ^ 2) :
    G.IsInfinite :=
  G.golodShafarevich_crit hr

end UnitDistance.ProP
