import UnitDistance.C11_ProPGroups

set_option linter.style.longLine false

/-!
# chunk-1-2: Golod–Shafarevich Inequality (Proposition A.9)

Source (lines 897–899): "If a finite nontrivial pro-p group has generator rank d
and relation rank r, then r > d²/4. Equivalently, a nontrivial finitely generated
pro-p group with r ≤ d²/4 is infinite."

This file extends C11_ProPGroups.lean with the `IsNontrivial` predicate and the
explicit finiteness-obstruction direction of Golod–Shafarevich.

References: [GS64], [GS65], [Koc02, Chapter 11].
-/

namespace UnitDistance.ProP

/-- Predicate asserting that a pro-p group G is nontrivial (G ≠ {1}). -/
axiom ProPGroup.IsNontrivial : ProPGroup → Prop

/-- **Golod–Shafarevich** (finiteness obstruction).
    If G is a finite nontrivial finitely generated pro-p group with minimal
    generator rank d(G) and minimal relation rank r(G), then d(G)² < 4·r(G).
    (Equivalently: r(G) > d(G)²/4 in rational arithmetic.) -/
axiom golodShafarevich_finite (G : ProPGroup)
    (hnt : G.IsNontrivial)
    (hfin : ¬G.IsInfinite) :
    G.genRank ^ 2 < 4 * G.relRank

/-- **Golod–Shafarevich** (infiniteness criterion with nontriviality hypothesis).
    A nontrivial finitely generated pro-p group G with 4·r(G) ≤ d(G)² is infinite.
    This refines `golod_shafarevich` in C11 by making the nontriviality explicit. -/
axiom golodShafarevich_infinite (G : ProPGroup)
    (hnt : G.IsNontrivial)
    (hr : 4 * G.relRank ≤ G.genRank ^ 2) :
    G.IsInfinite

end UnitDistance.ProP
