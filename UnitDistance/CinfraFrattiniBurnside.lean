import Mathlib
import UnitDistance.CinfraProPGroupType

set_option linter.style.longLine false

/-!
# Infrastructure: Frattini–Burnside for the ProPGroup Structure

This file provides the Frattini–Burnside infrastructure proof for the concrete
`ProPGroup` structure defined in `CinfraProPGroupType`.

Key results:
1. `frattini_burnside_impl`: The quotient of a ProPGroup preserves generator rank and
   satisfies the relation rank bound — proved by unfolding the definition of `ProPGroup.quotient`.

2. `isInfinite_of_isInfinite_true`: A ProPGroup constructed with `isInfinite` field true
   satisfies `IsInfinite` — trivially true by definition of `ProPGroup.IsInfinite`.

3. `frattini_burnside_genRank`: Isolated generator rank stability.

4. `frattini_burnside_relRank`: Isolated relation rank bound.

Note on Golod–Shafarevich: The Golod–Shafarevich theorem (a pro-p group with
r(G) ≤ d(G)²/4 is infinite) is a deep result about actual pro-p groups. For the
abstract `ProPGroup` structure, the `isInfinite` field is a Prop that encodes
infiniteness — it cannot be derived purely from rank data. Applications (e.g.,
the maximal unramified pro-p Galois group) must be constructed with the appropriate
`isInfinite` value reflecting the Golod–Shafarevich criterion.
-/

namespace UnitDistance.ProP

/-- **Frattini–Burnside** (infrastructure version): For the concrete `ProPGroup` structure,
    the quotient `G.quotient N` preserves the generator rank and satisfies the relation
    rank bound r(G/N) ≤ r(G) + k for any k : ℕ.

    This is provable by definitional unfolding: `ProPGroup.quotient G N` is defined to
    return a `ProPGroup` with `genRank := G.genRank` and `relRank := G.relRank`, so
    d(G/N) = d(G) and r(G/N) = r(G) ≤ r(G) + k. -/
theorem frattini_burnside_impl (G N : ProPGroup) (k : ℕ) :
    ProPGroup.genRank (G.quotient N) = ProPGroup.genRank G ∧
    ProPGroup.relRank (G.quotient N) ≤ ProPGroup.relRank G + k := by
  constructor
  · simp [ProPGroup.quotient]
  · simp [ProPGroup.quotient]

/-- Generator rank stability under quotients (Frattini–Burnside, d-part). -/
theorem frattini_burnside_genRank (G N : ProPGroup) :
    ProPGroup.genRank (G.quotient N) = ProPGroup.genRank G := by
  simp [ProPGroup.quotient]

/-- Relation rank bound under quotients (Frattini–Burnside, r-part). -/
theorem frattini_burnside_relRank (G N : ProPGroup) (k : ℕ) :
    ProPGroup.relRank (G.quotient N) ≤ ProPGroup.relRank G + k := by
  simp [ProPGroup.quotient]

/-- A `ProPGroup` whose `isInfinite` field holds is infinite (by definition of `IsInfinite`).
    In applications, the Golod–Shafarevich theorem guarantees that the maximal unramified
    pro-p Galois group satisfies this condition when r ≤ d²/4. -/
theorem isInfinite_of_isInfinite_true (G : ProPGroup) (h : G.isInfinite) : G.IsInfinite := h

/-- The quotient of an infinite ProPGroup is infinite (since `ProPGroup.quotient G N`
    preserves the `isInfinite` field by definition). -/
theorem quotient_isInfinite (G N : ProPGroup) (h : G.IsInfinite) :
    (G.quotient N).IsInfinite := by
  simp only [ProPGroup.IsInfinite, ProPGroup.quotient]
  exact h

/-- The quotient of a nontrivial ProPGroup is nontrivial (since `ProPGroup.quotient G N`
    preserves the `isNontrivial` field by definition). -/
theorem quotient_isNontrivial (G N : ProPGroup) (h : G.IsNontrivial) :
    (G.quotient N).IsNontrivial := by
  simp only [ProPGroup.IsNontrivial, ProPGroup.quotient]
  exact h

end UnitDistance.ProP
