import ASGinzburg.LeftSubmodules
import Mathlib.Algebra.Category.ModuleCat.Simple

/-! The concrete left quotient A e_i / A_{>0} e_i. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

/-- Positive-degree part of A e_i, with the covariant left action. -/
def leftRepresentableRadical (i : ℤ) : LeftSubmodule (A.leftRepresentable i) where
  component X := if i < X.index then ⊤ else ⊥
  map_mem := by
    intro X Y f x hx
    by_cases hy : i < Y.index
    · simp [hy]
    · by_cases hx' : i < X.index
      · have hf : f = 0 := A.positive (lt_of_le_of_lt (le_of_not_gt hy) hx') f
        change A.comp f x ∈ (if i < Y.index then ⊤ else ⊥)
        rw [hf]
        simp
      · have hx0 : x = 0 := by simpa [hx'] using hx
        rw [hx0]
        simp

/-- Actual positive-degree left products, with source height lower than the component. -/
def positiveLeftActionSpan (M : A.LeftModule) (j : ℤ) :
    Submodule k ((A.leftModuleEvaluation j).obj M) :=
  Submodule.span k { y | ∃ l : ℤ, l < j ∧ ∃ x : (A.leftModuleEvaluation l).obj M,
    ∃ a : A.Hom l j, M.obj.map (show (⟨l⟩ : A.Obj) ⟶ ⟨j⟩ from a) x = y }

theorem leftRepresentableRadical_eq_positiveLeftActionSpan (i j : ℤ) :
    (A.leftRepresentableRadical i).component ⟨j⟩ =
      A.positiveLeftActionSpan (A.leftRepresentable i) j := by
  by_cases hj : i < j
  · apply le_antisymm
    · intro x hx
      apply Submodule.subset_span
      refine ⟨i, hj, A.id i, x, ?_⟩
      change A.comp x (A.id i) = x
      exact A.id_comp x
    · simp [leftRepresentableRadical, hj]
  · have hz : A.positiveLeftActionSpan (A.leftRepresentable i) j ≤ ⊥ := by
      apply Submodule.span_le.mpr
      rintro y ⟨l, hl, x, a, rfl⟩
      have hx : x = 0 := A.positive (lt_of_lt_of_le hl (le_of_not_gt hj)) x
      change A.comp a x ∈ (⊥ : Submodule k (A.Hom i j))
      rw [hx]
      simp
    simpa [leftRepresentableRadical, hj] using (le_antisymm hz bot_le).symm

noncomputable def simpleLeftModule (i : ℤ) : A.LeftModule :=
  (A.leftRepresentableRadical i).quotient
noncomputable def simpleLeftModuleπ (i : ℤ) : A.leftRepresentable i ⟶ A.simpleLeftModule i :=
  (A.leftRepresentableRadical i).quotientπ
noncomputable instance simpleLeftModuleπEpi (i : ℤ) : Epi (A.simpleLeftModuleπ i) :=
  (A.leftRepresentableRadical i).quotientπEpi

theorem leftRepresentableRadical_diagonal_zero (i : ℤ) :
    (A.leftModuleEvaluation i).map (A.leftRepresentableRadical i).inclusion = 0 := by
  apply ModuleCat.hom_ext
  ext x
  change x.val = 0
  have h := x.property
  simpa [leftRepresentableRadical] using h

noncomputable def simpleLeftModuleDiagonalIso (i : ℤ) :
    (A.leftModuleEvaluation i).obj (A.simpleLeftModule i) ≅
      (A.leftModuleEvaluation i).obj (A.leftRepresentable i) := by
  let e := A.leftModuleCokernelObjIso (A.leftRepresentableRadical i).inclusion i
  have e' : (A.leftModuleEvaluation i).obj (A.simpleLeftModule i) ≅
      cokernel (0 : (A.leftModuleEvaluation i).obj (A.leftRepresentableRadical i).object ⟶
        (A.leftModuleEvaluation i).obj (A.leftRepresentable i)) := by
    simpa only [A.leftRepresentableRadical_diagonal_zero] using e
  exact e' ≪≫ cokernelZeroIsoTarget

theorem simpleLeftModule_off_diagonal (i j : ℤ) (hji : j ≠ i) :
    IsZero ((A.leftModuleEvaluation j).obj (A.simpleLeftModule i)) := by
  rcases lt_or_gt_of_ne hji with h | h
  · apply IsZero.of_epi ((A.leftModuleEvaluation j).map (A.simpleLeftModuleπ i))
    apply ModuleCat.isZero_iff_subsingleton.mpr
    refine ⟨fun x y => ?_⟩
    change A.Hom i j at x y
    rw [A.positive h x, A.positive h y]
  · have he : Epi ((A.leftModuleEvaluation j).map (A.leftRepresentableRadical i).inclusion) := by
      apply (ModuleCat.epi_iff_surjective _).mpr
      intro x
      refine ⟨⟨x, ?_⟩, rfl⟩
      simp [leftRepresentableRadical, h]
    exact (isZero_cokernel_of_epi _).of_iso
      (A.leftModuleCokernelObjIso (A.leftRepresentableRadical i).inclusion j)

theorem simpleLeftModule_diagonal_finrank (i : ℤ) :
    Module.finrank k ((A.leftModuleEvaluation i).obj (A.simpleLeftModule i)) = 1 := by
  rw [(A.simpleLeftModuleDiagonalIso i).toLinearEquiv.finrank_eq]
  change Module.finrank k (A.Hom i i) = 1
  rw [← (A.scalarEndEquiv i).finrank_eq]
  exact Module.finrank_self k

instance simpleLeftModuleDiagonalSimple (i : ℤ) :
    Simple ((A.leftModuleEvaluation i).obj (A.simpleLeftModule i)) :=
  simple_of_finrank_eq_one (A.simpleLeftModule_diagonal_finrank i)

theorem simpleLeftModule_hom_eq_zero_iff (i : ℤ) {M : A.LeftModule}
    (f : M ⟶ A.simpleLeftModule i) :
    f = 0 ↔ (A.leftModuleEvaluation i).map f = 0 := by
  constructor
  · intro h
    rw [h, Functor.map_zero]
  · intro h
    apply NatTrans.ext
    funext X
    by_cases hi : X.index = i
    · have hX : X = (⟨i⟩ : A.Obj) := by cases X; congr
      subst X
      exact h
    · exact (A.simpleLeftModule_off_diagonal i X.index hi).eq_zero_of_tgt (f.app X)

instance simpleLeftModuleSimple (i : ℤ) : Simple (A.simpleLeftModule i) where
  mono_isIso_iff_nonzero := by
    intro M f hf
    constructor
    · intro hi hz
      letI := hi
      have hzi : (A.leftModuleEvaluation i).map f = 0 := by rw [hz, Functor.map_zero]
      exact Simple.not_isZero _ (IsZero.of_epi_eq_zero _ hzi)
    · intro hn
      have hni : (A.leftModuleEvaluation i).map f ≠ 0 := by
        intro h
        exact hn ((A.simpleLeftModule_hom_eq_zero_iff i f).mpr h)
      haveI : IsIso ((A.leftModuleEvaluation i).map f) := isIso_of_mono_of_nonzero hni
      haveI : Epi f := (A.leftModule_epi_iff f).mpr fun j => by
        by_cases hj : j = i
        · subst j
          infer_instance
        · exact epi_of_target_iso_zero _ (A.simpleLeftModule_off_diagonal i j hj).isoZero
      exact isIso_of_mono_of_epi f

theorem simpleLeftModule_shortExact (i : ℤ) :
    (A.leftRepresentableRadical i).quotientShortComplex.ShortExact :=
  (A.leftRepresentableRadical i).quotientShortExact

end ASGinzburg.ZAlgebra
