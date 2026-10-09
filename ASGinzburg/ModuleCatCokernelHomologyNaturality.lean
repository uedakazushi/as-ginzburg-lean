import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Kernels

/-! Naturality of the actual cokernel presentation of short-complex
homology when its outgoing differential is zero. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
universe u
variable {k : Type u} [Field k]

noncomputable def moduleCatCokernelHomologyIso (S : ShortComplex (ModuleCat.{u} k))
    (hg : S.g=0) : S.homology ≅ ModuleCat.of k (S.X₂ ⧸ LinearMap.range S.f.hom) :=
  (ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork S hg
    (ModuleCat.cokernelCocone S.f) (ModuleCat.cokernelIsColimit S.f)).homologyIso

theorem moduleCatShortComplex_map_range {S T : ShortComplex (ModuleCat.{u} k)}
    (f : S ⟶ T) :
    LinearMap.range S.f.hom ≤ (LinearMap.range T.f.hom).comap f.τ₂.hom := by
  rintro x ⟨y,rfl⟩
  refine ⟨f.τ₁ y,?_⟩
  exact congrArg (fun g => g y) f.comm₁₂

noncomputable def moduleCatShortComplexQuotientMap {S T : ShortComplex (ModuleCat.{u} k)}
    (f : S ⟶ T) :
    ModuleCat.of k (S.X₂ ⧸ LinearMap.range S.f.hom) ⟶
      ModuleCat.of k (T.X₂ ⧸ LinearMap.range T.f.hom) :=
  ModuleCat.ofHom ((LinearMap.range S.f.hom).mapQ (LinearMap.range T.f.hom)
    f.τ₂.hom (moduleCatShortComplex_map_range f))

theorem moduleCatCokernelHomologyIso_naturality {S T : ShortComplex (ModuleCat.{u} k)}
    (f : S ⟶ T) (hS : S.g=0) (hT : T.g=0) :
    ShortComplex.homologyMap f ≫ (moduleCatCokernelHomologyIso T hT).hom=
      (moduleCatCokernelHomologyIso S hS).hom ≫ moduleCatShortComplexQuotientMap f := by
  exact (ShortComplex.LeftHomologyMapData.ofIsColimitCokernelCofork f
    hS (ModuleCat.cokernelCocone S.f) (ModuleCat.cokernelIsColimit S.f)
    hT (ModuleCat.cokernelCocone T.f) (ModuleCat.cokernelIsColimit T.f)
    (moduleCatShortComplexQuotientMap f) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rfl)).homologyMap_comm

end ASGinzburg
