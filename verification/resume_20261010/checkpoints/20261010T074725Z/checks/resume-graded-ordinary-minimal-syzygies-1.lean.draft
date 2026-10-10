import work.ASGinzburgDraft.GradedOrdinaryProjectiveCover
import work.ASGinzburgDraft.GradedOrdinaryKernelData
import ASGinzburg.FourTermProjectiveResolution
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! Iteration of constructed ordinary graded covers through their actual
concrete kernels. A cover-selection family is supplied by a cover theorem;
this construction makes no assertion that all rings possess such covers. -/
namespace ASGinzburg.GradedOrdinaryBoundedModule
open CategoryTheory CategoryTheory.Limits
open scoped DirectSum ModuleCat.Algebra
universe u v
variable {k : Type u} [Field k] {R : Type v} [Ring R] [Algebra k R]
variable {A : ℤ → Submodule k R} {b : ℤ} {J : Ideal R}
variable (C : ∀ M : GradedOrdinaryBoundedModule k R A b,
  GradedOrdinaryProjectiveCover M.val b J)

noncomputable def nextSyzygy (M : GradedOrdinaryBoundedModule k R A b) :
    GradedOrdinaryBoundedModule k R A b :=
  ⟨(C M).source.kernelData M.val (C M).π (C M).preservesGrade,
    (C M).source.kernelData_boundedBelow M.val (C M).π
      (C M).preservesGrade b (C M).boundedBelow⟩

noncomputable def syzygy (M : GradedOrdinaryBoundedModule k R A b) :
    ℕ → GradedOrdinaryBoundedModule k R A b
  | 0 => M
  | n + 1 => nextSyzygy C (syzygy M n)

variable (M : GradedOrdinaryBoundedModule k R A b)

noncomputable def termData (n : ℕ) : GradedOrdinaryModuleData k R A :=
  (C (syzygy C M n)).source

noncomputable def term (n : ℕ) : ModuleCat.{v} R := (termData C M n).ringModule

noncomputable def cover (n : ℕ) : term C M n ⟶ (syzygy C M n).val.ringModule :=
  (C (syzygy C M n)).π

instance term_projective (n : ℕ) : Projective (term C M n) :=
  (C (syzygy C M n)).projective

instance cover_epi (n : ℕ) : Epi (cover C M n) := (C (syzygy C M n)).epi

theorem term_boundedBelow (n : ℕ) : (termData C M n).BoundedBelow b :=
  (C (syzygy C M n)).boundedBelow

noncomputable def inclusion (n : ℕ) :
    (syzygy C M (n + 1)).val.ringModule ⟶ term C M n :=
  (termData C M n).kernelInclusion (syzygy C M n).val (cover C M n)

instance inclusion_mono (n : ℕ) : Mono (inclusion C M n) :=
  (termData C M n).kernelInclusion_mono (syzygy C M n).val (cover C M n)

theorem inclusion_cover (n : ℕ) : inclusion C M n ≫ cover C M n = 0 :=
  (termData C M n).kernelInclusion_comp (syzygy C M n).val (cover C M n)

noncomputable def differential (n : ℕ) : term C M (n + 1) ⟶ term C M n :=
  cover C M (n + 1) ≫ inclusion C M n

theorem differential_cover (n : ℕ) : differential C M n ≫ cover C M n = 0 := by
  dsimp only [differential]
  rw [Category.assoc, inclusion_cover, comp_zero]

theorem differential_sq (n : ℕ) :
    differential C M (n + 1) ≫ differential C M n = 0 := by
  change differential C M (n + 1) ≫ (cover C M (n + 1) ≫ inclusion C M n) = 0
  rw [← Category.assoc, differential_cover, zero_comp]

theorem differential_preservesGrade (n : ℕ) :
    (termData C M (n + 1)).PreservesGrade (termData C M n) (differential C M n) := by
  intro q x hx
  exact (C (syzygy C M (n + 1))).preservesGrade q x hx

theorem differential_minimal (n : ℕ) (x : term C M (n + 1)) :
    differential C M n x ∈ ordinaryIdealActionSpan k R (term C M n) J := by
  apply (C (syzygy C M n)).kernel_minimal
  exact (cover C M (n + 1) x).property

theorem inclusion_cover_exact (n : ℕ) :
    (ShortComplex.mk (inclusion C M n) (cover C M n) (inclusion_cover C M n)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  exact ⟨⟨x, hx⟩, rfl⟩

theorem differential_cover_exact (n : ℕ) :
    (ShortComplex.mk (differential C M n) (cover C M n) (differential_cover C M n)).Exact := by
  apply (ASGinzburg.exact_epi_comp_iff (cover C M (n + 1))
    (inclusion C M n) (cover C M n) (inclusion_cover C M n)).mpr
  exact inclusion_cover_exact C M n

theorem differential_exact (n : ℕ) :
    (ShortComplex.mk (differential C M (n + 1)) (differential C M n)
      (differential_sq C M n)).Exact :=
  (ASGinzburg.exact_comp_mono_iff (differential C M (n + 1)) (cover C M (n + 1))
    (inclusion C M n) (differential_cover C M (n + 1))).mp
      (differential_cover_exact C M (n + 1))

end ASGinzburg.GradedOrdinaryBoundedModule
