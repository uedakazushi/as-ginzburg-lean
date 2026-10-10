import work.ASGinzburgDraft.HomogeneousBinaryProductDecomposition
import ASGinzburg.GradedOrdinaryModuleData
import ASGinzburg.FiniteProjectiveDuality
import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-! Actual binary products of ordinary graded modules, including the
canonical maps, lower bounds, and genuine projectivity. -/
namespace ASGinzburg.GradedOrdinaryModuleData
open CategoryTheory CategoryTheory.Limits
open scoped DirectSum ModuleCat.Algebra
universe u v
variable {k : Type u} [Field k] {R : Type v} [Ring R] [Algebra k R]
variable {A : ℤ → Submodule k R}
variable (M N : GradedOrdinaryModuleData k R A)

noncomputable def binaryProductData : GradedOrdinaryModuleData k R A where
  ringModule := ModuleCat.of R (M.ringModule × N.ringModule)
  grade q := (M.grade q).prod (N.grade q)
  isInternal := by
    letI := M.decomposition
    letI := N.decomposition
    letI := homogeneousBinaryProductDecomposition M.grade N.grade
    exact DirectSum.Decomposition.isInternal _
  smul_mem := by
    intro p q r hr x hx
    exact ⟨M.smul_mem p q r hr x.1 hx.1,N.smul_mem p q r hr x.2 hx.2⟩

theorem binaryProductData_boundedBelow (b : ℤ)
    (hM : M.BoundedBelow b) (hN : N.BoundedBelow b) :
    (M.binaryProductData N).BoundedBelow b := by
  intro q hq
  change (M.grade q).prod (N.grade q) = ⊥
  rw [hM q hq,hN q hq,Submodule.prod_bot]

def binaryProductFst : (M.binaryProductData N).ringModule ⟶ M.ringModule :=
  ModuleCat.ofHom (LinearMap.fst R M.ringModule N.ringModule)

def binaryProductSnd : (M.binaryProductData N).ringModule ⟶ N.ringModule :=
  ModuleCat.ofHom (LinearMap.snd R M.ringModule N.ringModule)

def binaryProductInl : M.ringModule ⟶ (M.binaryProductData N).ringModule :=
  ModuleCat.ofHom (LinearMap.inl R M.ringModule N.ringModule)

def binaryProductInr : N.ringModule ⟶ (M.binaryProductData N).ringModule :=
  ModuleCat.ofHom (LinearMap.inr R M.ringModule N.ringModule)

theorem binaryProductFst_preservesGrade :
    (M.binaryProductData N).PreservesGrade M (M.binaryProductFst N) :=
  fun _ _ hx => hx.1

theorem binaryProductSnd_preservesGrade :
    (M.binaryProductData N).PreservesGrade N (M.binaryProductSnd N) :=
  fun _ _ hx => hx.2

theorem binaryProductInl_preservesGrade :
    M.PreservesGrade (M.binaryProductData N) (M.binaryProductInl N) :=
  fun q _ hx => ⟨hx,(N.grade q).zero_mem⟩

theorem binaryProductInr_preservesGrade :
    N.PreservesGrade (M.binaryProductData N) (M.binaryProductInr N) :=
  fun q _ hx => ⟨(M.grade q).zero_mem,hx⟩

theorem binaryProductData_projective [Projective M.ringModule] [Projective N.ringModule] :
    Projective (M.binaryProductData N).ringModule := by
  exact ASGinzburg.projective_of_retract
    (Retract.ofIso (ModuleCat.biprodIsoProd M.ringModule N.ringModule).symm)

end ASGinzburg.GradedOrdinaryModuleData
