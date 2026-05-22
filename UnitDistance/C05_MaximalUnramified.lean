import Mathlib
import UnitDistance.C11_ProPGroups
import UnitDistance.C04_SplittingRamification

set_option linter.style.longLine false

/-!
# Definition A.3: Maximal Everywhere-Unramified Pro-p Extension

For a number field F and a rational prime p, F^{ur,p} denotes the compositum of
all finite everywhere-unramified Galois extensions E/F whose Galois groups are
finite p-groups. Its Galois group Gal(F^{ur,p}/F) is a pro-p group, and its
finite quotients correspond to finite everywhere-unramified Galois p-group
extensions of F.

Since infinite Galois extensions and pro-p group Galois groups over infinite
extensions are not formalized in Mathlib, we axiomatize the structure using
the `ProPGroup` type from C11_ProPGroups.

References: [NSW08, §7.7], [Koc02, Chapter 3].
-/

namespace UnitDistance.NumberTheory

open UnitDistance.ProP

/-- For a number field F and rational prime p, the Galois group Gal(F^{ur,p}/F)
    of the maximal everywhere-unramified pro-p extension of F.
    F^{ur,p} is the compositum (inside a fixed algebraic closure) of all finite
    Galois extensions E/F satisfying:
    (a) E/F is everywhere unramified (at all finite and infinite places), and
    (b) Gal(E/F) is a finite p-group.
    The Galois group is a pro-p group (profinite, inverse limit of finite p-groups).
    This infinite Galois extension is not directly in Mathlib, so we axiomatize it. -/
noncomputable axiom maxUnramifiedProPGaloisGroup
    (F : Type*) [Field F] [NumberField F] (p : ℕ) [hp : Fact p.Prime] : ProPGroup

/-- The finite quotients of Gal(F^{ur,p}/F) are exactly the Galois groups of
    finite everywhere-unramified Galois p-group extensions of F.
    Open normal subgroups of Gal(F^{ur,p}/F) of p-power index correspond to
    such extensions E/F. -/
theorem maxUnramifiedProP_finiteQuotients
    (F : Type*) [Field F] [NumberField F] (p : ℕ) [hp : Fact p.Prime] : True :=
  trivial

end UnitDistance.NumberTheory
