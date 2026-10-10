import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! Homology at the actual last nonzero cochain term is its actual
incoming differential's concrete range quotient. The ring and carrier
universes are independent; no lower-degree exactness is required. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
universe u v
variable {R : Type u} [Ring R]

noncomputable def moduleCatShortComplexHomologyIsoRangeQuotient
    (S : ShortComplex (ModuleCat.{v} R)) (hg : S.g = 0) :
    S.homology ≅ ModuleCat.of R (S.X₂ ⧸ LinearMap.range S.f.hom) :=
  (ShortComplex.LeftHomologyData.ofHasCokernel S hg).homologyIso ≪≫
    ModuleCat.cokernelIsoRangeQuotient S.f

noncomputable def moduleCatCochainTopCokernelIso
    (K : CochainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
    (hNext : IsZero (K.X (n + 2))) :
    K.homology (n + 1) ≅
      ModuleCat.of R (K.X (n + 1) ⧸ LinearMap.range (K.d n (n + 1)).hom) := by
  let S := K.sc' n (n + 1) (n + 2)
  have hg : S.g = 0 := hNext.eq_of_tgt _ _
  exact K.homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp) ≪≫
    moduleCatShortComplexHomologyIsoRangeQuotient S hg

noncomputable def moduleCatCochainHomologyThreeIsoTopCokernel
    (K : CochainComplex (ModuleCat.{v} R) ℕ) (hFour : IsZero (K.X 4)) :
    K.homology 3 ≅ ModuleCat.of R (K.X 3 ⧸ LinearMap.range (K.d 2 3).hom) :=
  moduleCatCochainTopCokernelIso K 2 hFour

end ASGinzburg
