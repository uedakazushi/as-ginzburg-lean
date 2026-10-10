import ASGinzburg.GradedOrdinaryModuleData
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! Restriction along a genuinely graded algebra homomorphism preserves
the actual internal decomposition of an ordinary graded module. -/
namespace ASGinzburg.GradedOrdinaryModuleData
open CategoryTheory
open scoped ModuleCat.Algebra
universe u v
variable {k : Type u} [Field k] {R S : Type v}
  [Ring R] [Ring S] [Algebra k R] [Algebra k S]
variable {G : ℤ → Submodule k R} {H : ℤ → Submodule k S}
variable (f : S →ₐ[k] R) (M : GradedOrdinaryModuleData k R G)

def restrictionGrade (q : ℤ) :
    Submodule k ((ModuleCat.restrictScalars f.toRingHom).obj M.ringModule) where
  carrier := {x | x ∈ M.grade q}
  zero_mem' := (M.grade q).zero_mem
  add_mem' := (M.grade q).add_mem
  smul_mem' c x hx := by
    change (f (algebraMap k S c) • x) ∈ M.grade q
    rw [f.commutes]
    exact (M.grade q).smul_mem c hx

@[simp] theorem restrictionGrade_mem_iff (q : ℤ)
    (x : (ModuleCat.restrictScalars f.toRingHom).obj M.ringModule) :
    x ∈ M.restrictionGrade f q ↔ x ∈ M.grade q := Iff.rfl

noncomputable def restrictionData
    (hf : ∀ p : ℤ, ∀ s ∈ H p, f s ∈ G p) :
    GradedOrdinaryModuleData k S H where
  ringModule := (ModuleCat.restrictScalars f.toRingHom).obj M.ringModule
  grade := M.restrictionGrade f
  isInternal := by
    change DirectSum.IsInternal M.grade
    exact M.isInternal
  smul_mem p q s hs x hx := M.smul_mem p q (f s) (hf p s hs) x hx

theorem restrictionData_boundedBelow
    (hf : ∀ p : ℤ, ∀ s ∈ H p, f s ∈ G p)
    (b : ℤ) (hb : M.BoundedBelow b) :
    (M.restrictionData f hf).BoundedBelow b := by
  intro q hq
  ext x
  change x ∈ M.grade q ↔ x = 0
  rw [hb q hq]
  rfl

theorem restrictionData_preservesGrade
    (hf : ∀ p : ℤ, ∀ s ∈ H p, f s ∈ G p)
    (N : GradedOrdinaryModuleData k R G)
    (g : M.ringModule ⟶ N.ringModule) (hg : M.PreservesGrade N g) :
    (M.restrictionData f hf).PreservesGrade (N.restrictionData f hf)
      ((ModuleCat.restrictScalars f.toRingHom).map g) := hg

end ASGinzburg.GradedOrdinaryModuleData
