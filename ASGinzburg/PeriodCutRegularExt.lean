import ASGinzburg.PeriodCutRegularBiproduct
import ASGinzburg.PeriodCutGradedExtFunctor
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! Actual Ext into a shifted regular ring is the finite product of
actual Ext into its vertex representables, using the proved biproduct. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

noncomputable def cutRegularExtLinearEquiv (M : E.CutGradedRightModule Q) (n : ℕ) (t : ℤ) :
    Abelian.Ext.{v} M ((E.cutRegularGradedRightModule Q).shifted t) n ≃ₗ[k]
      (∀ i : Q.Vertex,Abelian.Ext.{v} M (E.cornerGradedRepresentable Q (i,t)) n) := by
  let F := cutGradedExtCovariant M n
  let B := F.mapBicone (E.cutRegularRepresentableBicone Q t)
  have hB : B.IsBilimit := isBilimitOfPreserves F (E.cutRegularRepresentableBiconeIsBilimit Q t)
  exact ((biproduct.uniqueUpToIso _ hB) ≪≫ ModuleCat.biproductIsoPi _).toLinearEquiv

end ASGinzburg.ZAlgebra.PeriodIso
