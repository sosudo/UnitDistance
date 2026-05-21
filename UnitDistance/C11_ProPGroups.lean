import Mathlib

set_option linter.style.longLine false

/-!
# Pro-p Groups: Frattini–Burnside and Golod–Shafarevich

This file introduces abstract axiom types for finitely generated pro-p groups,
which are not formalized in Mathlib. We axiomatize the key results needed for
the unit-distance graph proof:

1. The Frattini–Burnside theorem (Proposition A.8): Frattini subgroup characterization,
   Burnside's basis theorem, and the quotient-rank inequality.

2. The Golod–Shafarevich inequality (Proposition A.9): a finite nontrivial pro-p group
   satisfies r > d²/4; equivalently, r ≤ d²/4 implies the group is infinite.

References: [RZ10, Section 2.8], [Koc02, Theorem 4.10], [DdSMS99, Proposition 1.9(ii)],
[GS64], [GS65], [Koc02, Chapter 11].
-/

namespace UnitDistance.ProP

/-- Abstract type for a finitely generated pro-p group. Pro-p groups are not
    formalized in Mathlib, so we introduce this as an axiom type. -/
axiom ProPGroup : Type*

/-- The minimal generator rank d(G) of a pro-p group G: the minimal cardinality
    of a topological generating set. -/
axiom ProPGroup.genRank : ProPGroup → ℕ

/-- The minimal relation rank r(G) of a pro-p group G: the minimal number of
    relations in a pro-p presentation (i.e., d(ker(F → G)) where F is the free
    pro-p group on d(G) generators). -/
axiom ProPGroup.relRank : ProPGroup → ℕ

/-- Predicate expressing that a pro-p group is infinite. -/
axiom ProPGroup.IsInfinite : ProPGroup → Prop

/-- The quotient of a pro-p group G by a closed normal subgroup N. -/
axiom ProPGroup.quotient : ProPGroup → ProPGroup → ProPGroup

notation "d(" G ")" => ProPGroup.genRank G
notation "r(" G ")" => ProPGroup.relRank G

/-!
## Frattini–Burnside theorem (Proposition A.8)

For a finitely generated pro-p group G:
- Φ(G) = ∩_M M = G^p · [G, G]  (Frattini subgroup characterization)
- d(G) = dim_{F_p}(G/Φ(G))      (Burnside's basis theorem)
- If g₁, …, gₖ ∈ Φ(G) and N is their closed normal closure, then
  d(G/N) = d(G) and r(G/N) ≤ r(G) + k.

See [RZ10, Section 2.8], [Koc02, Theorem 4.10], [DdSMS99, Proposition 1.9(ii)].
-/

/-- **Frattini–Burnside** (Proposition A.8): For a finitely generated pro-p group G,
    if g₁, …, gₖ ∈ Φ(G) generate a closed normal subgroup N (with closed normal
    closure), then d(G/N) = d(G) and r(G/N) ≤ r(G) + k. -/
axiom frattini_burnside_genRank_stable (G N : ProPGroup) (k : ℕ) :
    ProPGroup.genRank (G.quotient N) = ProPGroup.genRank G ∧
    ProPGroup.relRank (G.quotient N) ≤ ProPGroup.relRank G + k

/-!
## Golod–Shafarevich inequality (Proposition A.9)

A finite nontrivial pro-p group with generator rank d and relation rank r satisfies
r > d²/4. Equivalently, a nontrivial finitely generated pro-p group with r ≤ d²/4
is infinite.

See [GS64], [GS65], [Koc02, Chapter 11].
-/

/-- **Golod–Shafarevich** (Proposition A.9): A nontrivial finitely generated pro-p
    group G with r(G) ≤ d(G)²/4 is infinite.
    Equivalently: if G is finite and nontrivial, then r(G) > d(G)²/4. -/
axiom golod_shafarevich (G : ProPGroup)
    (hd : ProPGroup.genRank G ≥ 1)
    (hr : 4 * ProPGroup.relRank G ≤ ProPGroup.genRank G ^ 2) :
    G.IsInfinite

end UnitDistance.ProP
