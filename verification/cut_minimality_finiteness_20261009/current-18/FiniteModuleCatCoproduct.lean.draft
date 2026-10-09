import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.RingTheory.Finiteness.Basic

/-! A finite categorical coproduct of genuinely finite modules is finite. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
universe u v
variable {R : Type u} [Ring R]

theorem finiteModuleCatCoproduct {I : Type} [Fintype I] (f : I → ModuleCat.{v} R)
    [∀ i,Module.Finite R (f i)] : Module.Finite R (∐ f : ModuleCat.{v} R) := by
  let e : (∐ f : ModuleCat.{v} R) ≅ ModuleCat.of R (∀ i,f i) :=
    (biproduct.isoCoproduct f).symm ≪≫ ModuleCat.biproductIsoPi f
  exact Module.Finite.of_surjective e.symm.toLinearEquiv.toLinearMap
    e.symm.toLinearEquiv.surjective

end ASGinzburg
