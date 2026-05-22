import UnitDistance.C11_ProPGroups

set_option linter.style.longLine false

/-!
# chunk-1-2: Golod–Shafarevich Inequality (Proposition A.9)

Source (lines 897–899): "If a finite nontrivial pro-p group has generator rank d
and relation rank r, then r > d²/4. Equivalently, a nontrivial finitely generated
pro-p group with r ≤ d²/4 is infinite."

This file extends C11_ProPGroups.lean with the explicit finiteness-obstruction
direction of Golod–Shafarevich.

`IsNontrivial` is now defined in `CinfraProPGroupType`.

References: [GS64], [GS65], [Koc02, Chapter 11].
-/

namespace UnitDistance.ProP

-- IsNontrivial is imported from CinfraProPGroupType via C11_ProPGroups

/-- **Golod–Shafarevich** (finiteness obstruction).
    If G is a finite nontrivial finitely generated pro-p group with minimal
    generator rank d(G) and minimal relation rank r(G), then d(G)² < 4·r(G).
    (Equivalently: r(G) > d(G)²/4 in rational arithmetic.)
    Proved by contrapositive: if d(G)² ≥ 4·r(G), then G is infinite (via
    `golodShafarevich_crit`), contradicting finiteness. -/
theorem golodShafarevich_finite (G : ProPGroup)
    (hnt : G.IsNontrivial)
    (hfin : ¬G.IsInfinite) :
    G.genRank ^ 2 < 4 * G.relRank := by
  by_contra h
  push_neg at h
  exact hfin (G.golodShafarevich_crit h)

/-- **Golod–Shafarevich** (infiniteness criterion with nontriviality hypothesis).
    A nontrivial finitely generated pro-p group G with 4·r(G) ≤ d(G)² is infinite.
    This refines `golod_shafarevich` in C11 by making the nontriviality explicit.
    Proved directly from the `golodShafarevich_crit` field. -/
theorem golodShafarevich_infinite (G : ProPGroup)
    (hnt : G.IsNontrivial)
    (hr : 4 * G.relRank ≤ G.genRank ^ 2) :
    G.IsInfinite :=
  G.golodShafarevich_crit hr

end UnitDistance.ProP
