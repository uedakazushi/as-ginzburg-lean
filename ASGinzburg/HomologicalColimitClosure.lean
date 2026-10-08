import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! Colimit preservation is closed under kernels for exact colimits, and cokernels. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
universe uC vC uJ vJ uK vK uD vD
section Exchange
variable {C : Type uC} [Category.{vC} C]
variable {J : Type uJ} [Category.{vJ} J]
variable {K : Type uK} [Category.{vK} K]
variable [HasColimitsOfShape J C] [HasLimitsOfShape K C]

/-- The interchange is induced by exactness of colimits, not assumed for the limit functor. -/
noncomputable def colimitLimitExchangeIso
    [PreservesLimitsOfShape K (colim : (J ⥤ C) ⥤ C)] (G : J ⥤ K ⥤ C) :
    colimit (G ⋙ lim) ≅ limit (colimit G) :=
  HasColimit.isoOfNatIso (limitFlipIsoCompLim G).symm ≪≫
    (isLimitOfPreserves colim (limit.isLimit G.flip)).conePointUniqueUpToIso
      (limit.isLimit _) ≪≫
        HasLimit.isoOfNatIso (colimitFlipIsoCompColim G.flip).symm

@[reassoc] theorem ι_colimitLimitExchangeIso_π
    [PreservesLimitsOfShape K (colim : (J ⥤ C) ⥤ C)] (G : J ⥤ K ⥤ C) (j : J) (a : K) :
    colimit.ι (G ⋙ lim) j ≫ (colimitLimitExchangeIso G).hom ≫ limit.π (colimit G) a =
      limit.π (G.obj j) a ≫ (colimit.ι G j).app a := by
  dsimp [colimitLimitExchangeIso]
  simp only [HasColimit.isoOfNatIso_ι_hom_assoc, Functor.mapCone_π_app, Iso.symm_hom,
    Limits.limit.conePointUniqueUpToIso_hom_comp_assoc, Limits.limit.cone_π,
    Limits.colimit.ι_map_assoc, Limits.colimitFlipIsoCompColim_inv_app, Category.assoc,
    Limits.HasLimit.isoOfNatIso_hom_π]
  simp
  rfl

noncomputable def limitPreservesColimitsOfExactShape
    [PreservesLimitsOfShape K (colim : (J ⥤ C) ⥤ C)] :
    PreservesColimitsOfShape J (lim : (K ⥤ C) ⥤ C) where
  preservesColimit {G} := by
    have h : colimit.post G lim = (colimitLimitExchangeIso G).hom := by
      apply colimit.hom_ext
      intro j
      apply limit.hom_ext
      intro a
      simp [ι_colimitLimitExchangeIso_π]
    letI : IsIso (colimit.post G lim) := by rw [h]; infer_instance
    exact preservesColimit_of_isIso_post lim G

end Exchange

section KernelsCokernels
variable {C : Type uC} [Category.{vC} C]
variable {J : Type uJ} [Category.{vJ} J]
variable {D : Type uD} [Category.{vD} D] [Abelian D]
variable [HasColimitsOfShape J D]
variable {F G : C ⥤ D} (f : F ⟶ G)
variable [PreservesColimitsOfShape J F] [PreservesColimitsOfShape J G]

def parallelPairDiagramPreservesColimits :
    PreservesColimitsOfShape J (parallelPair f 0).flip := by
  apply preservesColimitsOfShape_of_evaluation
  intro a
  cases a
  · change PreservesColimitsOfShape J F
    infer_instance
  · change PreservesColimitsOfShape J G
    infer_instance

noncomputable def kernelFunctorPreservesExactColimits [HasExactColimitsOfShape J D] :
    PreservesColimitsOfShape J (kernel f) := by
  letI := parallelPairDiagramPreservesColimits (J := J) f
  letI : PreservesColimitsOfShape J (lim : (WalkingParallelPair ⥤ D) ⥤ D) :=
    limitPreservesColimitsOfExactShape
  exact preservesColimitsOfShape_of_natIso (limitIsoFlipCompLim (parallelPair f 0)).symm

noncomputable def cokernelFunctorPreservesColimits :
    PreservesColimitsOfShape J (cokernel f) := by
  letI : PreservesColimitsOfSize.{vJ,uJ} (colim : (WalkingParallelPair ⥤ D) ⥤ D) :=
    colimConstAdj.leftAdjoint_preservesColimits
  letI := parallelPairDiagramPreservesColimits (J := J) f
  exact preservesColimitsOfShape_of_natIso (colimitIsoFlipCompColim (parallelPair f 0)).symm

end KernelsCokernels

universe u v
variable {k : Type u} [Field k]

/-- Arbitrary small coproducts of modules are exact, including when k and modules have
different universe levels. -/
noncomputable def moduleCatExactCoproducts (I : Type) :
    HasExactColimitsOfShape (Discrete I) (ModuleCat.{v} k) :=
  HasExactColimitsOfShape.domain_of_functor (Discrete I)
    (forget₂ (ModuleCat.{v} k) AddCommGrpCat.{v})

end ASGinzburg
