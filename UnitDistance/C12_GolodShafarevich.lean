import UnitDistance.C11_ProPGroups

set_option linter.style.longLine false

/-!
# chunk-1-2: Golod-Shafarevich Inequality (Proposition A.9)

Source (lines 897-899): "If a finite nontrivial pro-p group has generator rank d
and relation rank r, then r > d^2/4. Equivalently, a nontrivial finitely generated
pro-p group with r <= d^2/4 is infinite."

This file extends C11_ProPGroups.lean with the explicit finiteness-obstruction
direction of Golod-Shafarevich.

`IsNontrivial` is defined in `CinfraProPGroupType`.
`golodShafarevich_criterion` is in `STANDARD_AXIOMS.lean` (is_assumption: true).

References: [GS64], [GS65], [Koc02, Chapter 11].
-/

namespace UnitDistance.ProP

-- golodShafarevich_criterion imported transitively from STANDARD_AXIOMS via C11

/-- **Golod-Shafarevich** (finiteness obstruction).
    If G is a finite nontrivial finitely generated pro-p group with minimal
    generator rank d(G) and minimal relation rank r(G), then d(G)^2 < 4*r(G).
    (Equivalently: r(G) > d(G)^2/4 in rational arithmetic.)
    Proved by contrapositive: if d(G)^2 >= 4*r(G), then G is infinite (via
    `golodShafarevich_criterion`), contradicting finiteness. -/
theorem golodShafarevich_finite (G : ProPGroup)
    (hnt : G.IsNontrivial)
    (hfin : ¬G.IsInfinite) :
    G.genRank ^ 2 < 4 * G.relRank := by
  by_contra h
  push_neg at h
  exact hfin (golodShafarevich_criterion G h)

/-- **Golod-Shafarevich** (infiniteness criterion with nontriviality hypothesis).
    A nontrivial finitely generated pro-p group G with 4*r(G) <= d(G)^2 is infinite.
    This refines `golod_shafarevich` in C11 by making the nontriviality explicit.
    Uses `golodShafarevich_criterion` from STANDARD_AXIOMS.lean. -/
theorem golodShafarevich_infinite (G : ProPGroup)
    (hnt : G.IsNontrivial)
    (hr : 4 * G.relRank ≤ G.genRank ^ 2) :
    G.IsInfinite :=
  golodShafarevich_criterion G hr

end UnitDistance.ProP
