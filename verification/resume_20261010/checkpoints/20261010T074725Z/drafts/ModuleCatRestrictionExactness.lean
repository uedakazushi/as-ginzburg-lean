import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.Additive

/-! Restriction of scalar rings preserves and reflects actual exactness
because the underlying maps and additive groups are unchanged. -/
namespace ASGinzburg
open CategoryTheory
universe u v w t
variable {R : Type u} [Ring R] {S : Type v} [Ring S] (f : R →+* S)

theorem moduleCatRestrictScalars_exact_iff (K : ShortComplex (ModuleCat.{w} S)) :
    (K.map (ModuleCat.restrictScalars f)).Exact ↔ K.Exact := by
  rw [ShortComplex.moduleCat_exact_iff, ShortComplex.moduleCat_exact_iff]
  rfl

theorem moduleCatRestrictScalars_exactAt_iff {ι : Type t} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{w} S) c) (i : ι) :
    (((ModuleCat.restrictScalars f).mapHomologicalComplex c).obj K).ExactAt i ↔
      K.ExactAt i := by
  rw [HomologicalComplex.exactAt_iff, HomologicalComplex.exactAt_iff]
  exact moduleCatRestrictScalars_exact_iff f (K.sc i)

end ASGinzburg
