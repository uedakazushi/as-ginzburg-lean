import work.ASGinzburgDraft.GradedOrdinaryBinaryProduct
import work.ASGinzburgDraft.GradedOrdinaryProjectiveLift
import ASGinzburg.GradedOrdinaryCokernelData
import ASGinzburg.GradedOrdinaryProjectiveCover

/-! The actual top-cokernel projective cover of a graded four-term
complex admits a homogeneous lift. Adding this cover in degree two
produces the genuine cone used for semisimple exactness detection. -/
namespace ASGinzburg.GradedOrdinaryModuleData
open CategoryTheory CategoryTheory.Limits
open scoped DirectSum ModuleCat.Algebra
universe u v
variable {k : Type u} [Field k] {R : Type v} [Ring R] [Algebra k R]
variable {A : ℤ → Submodule k R}
variable (P₀ P₁ P₂ P₃ V : GradedOrdinaryModuleData k R A)

def topCoverConeIncoming (f₁ : P₁.ringModule ⟶ P₂.ringModule) :
    P₁.ringModule ⟶ (P₂.binaryProductData V).ringModule :=
  f₁ ≫ P₂.binaryProductInl V

def topCoverConeOutgoing (f₂ : P₂.ringModule ⟶ P₃.ringModule)
    (l : V.ringModule ⟶ P₃.ringModule) :
    (P₂.binaryProductData V).ringModule ⟶ P₃.ringModule :=
  ModuleCat.ofHom (f₂.hom.coprod l.hom)

theorem topCoverConeIncoming_preservesGrade (f₁ : P₁.ringModule ⟶ P₂.ringModule)
    (hf₁ : P₁.PreservesGrade P₂ f₁) :
    P₁.PreservesGrade (P₂.binaryProductData V) (P₁.topCoverConeIncoming P₂ V f₁) :=
  P₁.preservesGrade_comp P₂ (P₂.binaryProductData V) f₁ (P₂.binaryProductInl V)
    hf₁ (P₂.binaryProductInl_preservesGrade V)

theorem topCoverConeOutgoing_preservesGrade (f₂ : P₂.ringModule ⟶ P₃.ringModule)
    (l : V.ringModule ⟶ P₃.ringModule)
    (hf₂ : P₂.PreservesGrade P₃ f₂) (hl : V.PreservesGrade P₃ l) :
    (P₂.binaryProductData V).PreservesGrade P₃ (P₂.topCoverConeOutgoing P₃ V f₂ l) := by
  intro q x hx
  exact (P₃.grade q).add_mem (hf₂ q x.1 hx.1) (hl q x.2 hx.2)

theorem comp_topCoverConeIncoming (f₀ : P₀.ringModule ⟶ P₁.ringModule)
    (f₁ : P₁.ringModule ⟶ P₂.ringModule) (h : f₀ ≫ f₁ = 0) :
    f₀ ≫ P₁.topCoverConeIncoming P₂ V f₁ = 0 := by
  rw [topCoverConeIncoming,← Category.assoc,h,zero_comp]

theorem topCoverConeIncoming_comp_outgoing (f₁ : P₁.ringModule ⟶ P₂.ringModule)
    (f₂ : P₂.ringModule ⟶ P₃.ringModule) (l : V.ringModule ⟶ P₃.ringModule)
    (h : f₁ ≫ f₂ = 0) :
    P₁.topCoverConeIncoming P₂ V f₁ ≫ P₂.topCoverConeOutgoing P₃ V f₂ l = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change f₂ (f₁ x) + l 0 = 0
  rw [map_zero,add_zero]
  exact congrArg (fun f : P₁.ringModule ⟶ P₃.ringModule => f x) h

theorem exists_topCover_homogeneous_lift [DirectSum.Decomposition A]
    (f₂ : P₂.ringModule ⟶ P₃.ringModule) (hf₂ : P₂.PreservesGrade P₃ f₂)
    (b : ℤ) (J : Ideal R)
    (C : GradedOrdinaryProjectiveCover (P₂.cokernelData P₃ f₂ hf₂) b J) :
    ∃ l : C.source.ringModule ⟶ P₃.ringModule,
      C.source.PreservesGrade P₃ l ∧ l ≫ P₂.cokernelProjection P₃ f₂ = C.π := by
  letI := C.projective
  exact C.source.exists_gradePreserving_projective_lift P₃
    (P₂.cokernelData P₃ f₂ hf₂) C.π (P₂.cokernelProjection P₃ f₂)
    C.preservesGrade (P₂.cokernelProjection_preservesGrade P₃ f₂ hf₂)

end ASGinzburg.GradedOrdinaryModuleData
