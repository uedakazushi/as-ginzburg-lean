import ASGinzburg.GradedOrdinaryKernelData
import ASGinzburg.HomogeneousOrdinaryQuotientAction

/-! The actual cokernel of a grade-preserving ordinary ring map inherits
the genuine internal grading and lower bound of its target. -/
namespace ASGinzburg.GradedOrdinaryModuleData
open CategoryTheory CategoryTheory.Limits
open scoped DirectSum ModuleCat.Algebra
universe u v
variable {k : Type u} [Field k] {R : Type v} [Ring R] [Algebra k R]
variable {A : ℤ → Submodule k R}
variable (P M : GradedOrdinaryModuleData k R A)

def cokernelModule (f : P.ringModule ⟶ M.ringModule) : ModuleCat.{v} R :=
  ModuleCat.of R (M.ringModule ⧸ LinearMap.range f.hom)

def cokernelGrade (f : P.ringModule ⟶ M.ringModule) (q : ℤ) :
    Submodule k (P.cokernelModule M f) :=
  homogeneousOrdinaryQuotientGrade k R M.ringModule M.grade (LinearMap.range f.hom) q

noncomputable def cokernelGradeDecomposition (f : P.ringModule ⟶ M.ringModule)
    (hf : P.PreservesGrade M f) : DirectSum.Decomposition (P.cokernelGrade M f) := by
  letI := P.decomposition
  letI := M.decomposition
  apply homogeneousOrdinaryQuotientDecomposition k R M.ringModule M.grade
    (LinearMap.range f.hom)
  intro q x hx
  obtain ⟨y,rfl⟩ := hx
  refine ⟨homogeneousComponent k P.ringModule P.grade q y,?_⟩
  exact homogeneousLinearMap_component k P.ringModule M.ringModule P.grade M.grade
    (f.hom.restrictScalars k) hf q y

noncomputable def cokernelData (f : P.ringModule ⟶ M.ringModule)
    (hf : P.PreservesGrade M f) : GradedOrdinaryModuleData k R A where
  ringModule := P.cokernelModule M f
  grade := P.cokernelGrade M f
  isInternal := by
    letI := P.cokernelGradeDecomposition M f hf
    exact DirectSum.Decomposition.isInternal (P.cokernelGrade M f)
  smul_mem := by
    intro p q r hr x hx
    exact homogeneousOrdinaryQuotientGrade_smul_mem k R M.ringModule A M.grade
      (LinearMap.range f.hom) M.smul_mem p q r hr x hx

theorem cokernelData_boundedBelow (f : P.ringModule ⟶ M.ringModule)
    (hf : P.PreservesGrade M f) (b : ℤ) (hb : M.BoundedBelow b) :
    (P.cokernelData M f hf).BoundedBelow b :=
  fun q hq => homogeneousOrdinaryQuotientGrade_eq_bot_of_lower_bound k R M.ringModule
    M.grade (LinearMap.range f.hom) b hb q hq

def cokernelProjection (f : P.ringModule ⟶ M.ringModule) :
    M.ringModule ⟶ P.cokernelModule M f :=
  ModuleCat.ofHom (LinearMap.range f.hom).mkQ

theorem cokernelProjection_preservesGrade (f : P.ringModule ⟶ M.ringModule)
    (hf : P.PreservesGrade M f) :
    M.PreservesGrade (P.cokernelData M f hf) (P.cokernelProjection M f) :=
  fun q x hx => homogeneousOrdinaryQuotientGrade_mkQ_mem k R M.ringModule
    M.grade (LinearMap.range f.hom) q x hx

instance cokernelProjection_epi (f : P.ringModule ⟶ M.ringModule) :
    Epi (P.cokernelProjection M f) :=
  (ModuleCat.epi_iff_surjective _).mpr (LinearMap.range f.hom).mkQ_surjective

theorem comp_cokernelProjection (f : P.ringModule ⟶ M.ringModule) :
    f ≫ P.cokernelProjection M f = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨x,rfl⟩

noncomputable def cokernelIsoCokernelModule (f : P.ringModule ⟶ M.ringModule) :
    cokernel f ≅ P.cokernelModule M f := ModuleCat.cokernelIsoRangeQuotient f

end ASGinzburg.GradedOrdinaryModuleData
