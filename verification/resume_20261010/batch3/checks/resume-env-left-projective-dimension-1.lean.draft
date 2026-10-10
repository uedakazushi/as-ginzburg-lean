import work.ASGinzburgDraft.AlgebraEnvelopingOppositeRegularComparison
import work.ASGinzburgDraft.ModuleCatRingEquivProjectiveDimension
import ASGinzburg.EnvelopingModuleProjectiveDimension

/-! The actual multiplication bimodule controls ordinary left modules as
well. This uses the genuine opposite enveloping algebra equivalence and
the actual double-opposite equivalence of module categories. -/
namespace ASGinzburg
open CategoryTheory
universe u v
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]

theorem regularEnvelopingOpposite_hasProjectiveDimensionLE_three
    (hR : HasProjectiveDimensionLE (regularEnvelopingModuleCat k R) 3) :
    HasProjectiveDimensionLE (regularEnvelopingModuleCat k Rᵐᵒᵖ) 3 := by
  haveI := moduleCatRingEquiv_hasProjectiveDimensionLE_three
    (algebraEnvelopingOppositeAlgEquiv k R).toRingEquiv
    (regularEnvelopingModuleCat k R) hR
  exact hasProjectiveDimensionLT_of_iso
    (regularEnvelopingOppositeRestrictionIso k R).symm 4

theorem leftModule_hasProjectiveDimensionLE_three_of_enveloping_dimension
    (M : ModuleCat.{v} R)
    (hR : HasProjectiveDimensionLE (regularEnvelopingModuleCat k R) 3) :
    HasProjectiveDimensionLE M 3 := by
  let e := RingEquiv.opOp R
  let M₂ := (ModuleCat.restrictScalars e.symm.toRingHom).obj M
  have hM₂ : HasProjectiveDimensionLE M₂ 3 :=
    rightModule_hasProjectiveDimensionLE_three_of_enveloping_dimension k Rᵐᵒᵖ M₂
      (regularEnvelopingOpposite_hasProjectiveDimensionLE_three k R hR)
  haveI := moduleCatRingEquiv_hasProjectiveDimensionLE_three e M₂ hM₂
  exact hasProjectiveDimensionLT_of_iso
    ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).counitIso.app M) 4

end ASGinzburg
