import UnitDistance.C12_GolodShafarevich

set_option linter.style.longLine false

namespace UnitDistance.ProP

/-- Proposition 3.4 (Golod–Shafarevich, citing Proposition A.9):
    A finite nontrivial pro-p group satisfies r > d²/4.
    Equivalently, a nontrivial finitely generated pro-p group with r ≤ d²/4 is infinite. -/
theorem prop34_golodShafarevich_forward (G : ProPGroup)
    (hnt : G.IsNontrivial) (hfin : ¬G.IsInfinite) :
    G.genRank ^ 2 < 4 * G.relRank := by
  sorry

theorem prop34_golodShafarevich_infinite (G : ProPGroup)
    (hnt : G.IsNontrivial)
    (hr : 4 * G.relRank ≤ G.genRank ^ 2) :
    G.IsInfinite := by
  sorry

end UnitDistance.ProP
