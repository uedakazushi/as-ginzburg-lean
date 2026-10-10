import work.ASGinzburgDraft.RegularEnvelopingInducedScalars
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Algebra.Category.ModuleCat.Algebra

/-! Canonical field grading on the genuine ordinary multiplication
bimodule object. The identity comparison uses the proved equality of
its induced field module with the original algebra field module. -/
namespace ASGinzburg
open CategoryTheory
open scoped ModuleCat.Algebra DirectSum
universe u v
set_option maxHeartbeats 800000
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]

noncomputable def regularEnvelopingNativeFieldEquiv :
    (regularEnvelopingModuleCat k R) ≃ₗ[k] R :=
  @AddEquiv.toLinearEquiv _ _ _ _ _ _
    (Module.compHom (regularEnvelopingModuleCat k R)
      (algebraMap k (AlgebraEnvelopingRing k R))) _
    (AddEquiv.refl R) (fun c x => congrArg
      (fun m : Module k R => @SMul.smul k R m.toSMul c x)
      (regularEnvelopingModuleCat_inducedScalarModule_eq k R))

theorem regularEnvelopingNativeFieldEquiv_apply (x : regularEnvelopingModuleCat k R) :
    regularEnvelopingNativeFieldEquiv k R x = x := rfl

noncomputable def regularEnvelopingNativeGrade (G : ℤ → Submodule k R) (q : ℤ) :
    Submodule k (regularEnvelopingModuleCat k R) :=
  (G q).comap (regularEnvelopingNativeFieldEquiv k R).toLinearMap

theorem regularEnvelopingNativeGrade_mem (G : ℤ → Submodule k R) (q : ℤ)
    (x : regularEnvelopingModuleCat k R) :
    x ∈ regularEnvelopingNativeGrade k R G q ↔ x ∈ G q := Iff.rfl

theorem regularEnvelopingNativeGrade_isInternal (G : ℤ → Submodule k R)
    (hG : DirectSum.IsInternal G) :
    DirectSum.IsInternal (regularEnvelopingNativeGrade k R G) := by
  change DirectSum.IsInternal G
  exact hG

theorem regularEnvelopingNativeGrade_eq_bot (G : ℤ → Submodule k R) (q : ℤ)
    (hq : G q = ⊥) : regularEnvelopingNativeGrade k R G q = ⊥ := by
  ext x
  change x ∈ G q ↔ x = 0
  rw [hq]
  rfl

end ASGinzburg
