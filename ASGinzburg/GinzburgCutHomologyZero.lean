import ASGinzburg.GinzburgCutDegreeZero
import ASGinzburg.PathJacobianGrading

/-! Actual fixed cut H-zero equals the genuine homogeneous Jacobian
quotient. This comparison is independent of regularity. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory CategoryTheory.Limits
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgCutGradedDifferential_zero (φ : Q.Potential k) (u v : Q.Vertex) (c : ℤ) :
    Q.ginzburgCutGradedDifferential k φ u v 0 c=0 := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  exact Q.ginzburgDifferential_degreeZero k φ f.property.1

noncomputable def ginzburgCutNegativeOneDifferential (φ : Q.Potential k)
    (u v : Q.Vertex) (c : ℤ) :
    Q.ginzburgCutCohomologicalComponent k u v (-1) c →ₗ[k]
      Q.ginzburgCutCohomologicalComponent k u v 0 c :=
  Q.ginzburgCutGradedDifferential k φ u v (-1) c

noncomputable def ginzburgCutZeroShortComplex (φ : Q.Potential k) (u v : Q.Vertex) (c : ℤ) :
    ShortComplex (ModuleCat.{u} k) :=
  ShortComplex.moduleCatMk (Q.ginzburgCutNegativeOneDifferential k φ u v c)
    (Q.ginzburgCutGradedDifferential k φ u v 0 c)
    (by
      have h := Q.ginzburgCutGradedDifferential_square k φ u v (-1) c
      simpa only [show (-1:ℤ)+1=0 by omega,ginzburgCutNegativeOneDifferential] using h)

theorem ginzburgCutZeroShortComplex_g (φ : Q.Potential k) (u v : Q.Vertex) (c : ℤ) :
    (Q.ginzburgCutZeroShortComplex k φ u v c).g=0 := by
  apply ModuleCat.hom_ext
  exact Q.ginzburgCutGradedDifferential_zero k φ u v c

noncomputable def ginzburgCutZeroShortComplexIso (φ : Q.Potential k)
    (u v : Q.Vertex) (c : ℤ) :
    (Q.ginzburgCutCochainComplex k φ u v c).sc' (-1) 0 1 ≅
      Q.ginzburgCutZeroShortComplex k φ u v c :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simpa only [Category.id_comp,Category.comp_id] using
      (Q.ginzburgCutCochainComplex_d k φ u v c (-1)).symm)
    (by simpa only [Category.id_comp,Category.comp_id] using
      (Q.ginzburgCutCochainComplex_d k φ u v c 0).symm)

noncomputable def ginzburgCutHomologyZeroQuotientIso (φ : Q.Potential k)
    (u v : Q.Vertex) (c : ℤ) :
    Q.ginzburgCutHomology k φ u v c 0 ≅
      ModuleCat.of k (Q.ginzburgCutCohomologicalComponent k u v 0 c ⧸
        LinearMap.range (Q.ginzburgCutNegativeOneDifferential k φ u v c)) :=
  ShortComplex.homologyMapIso ((Q.ginzburgCutCochainComplex k φ u v c).isoSc'
    (i:=(-1)) (j:=0) (k:=1) (by simp) (by simp)) ≪≫
  ShortComplex.homologyMapIso (Q.ginzburgCutZeroShortComplexIso k φ u v c) ≪≫
  (ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork
    (Q.ginzburgCutZeroShortComplex k φ u v c) (Q.ginzburgCutZeroShortComplex_g k φ u v c)
      (ModuleCat.cokernelCocone (Q.ginzburgCutZeroShortComplex k φ u v c).f)
      (ModuleCat.cokernelIsColimit (Q.ginzburgCutZeroShortComplex k φ u v c).f)).homologyIso

theorem ginzburgCutGradedBoundary_map (φ : Q.Potential k) (u v : Q.Vertex) (c : ℤ) :
    (LinearMap.range (Q.ginzburgCutNegativeOneDifferential k φ u v c)).map
      (Q.originalGinzburgCutDegreeZeroEquiv k u v c).symm.toLinearMap=
        Q.pathJacobianCutIdeal k φ u v c := by
  rw [←LinearMap.range_comp]
  have heq : (Q.originalGinzburgCutDegreeZeroEquiv k u v c).symm.toLinearMap.comp
      (Q.ginzburgCutNegativeOneDifferential k φ u v c)=
        Q.ginzburgCutBoundaryLift k φ u v c := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    apply Q.originalGinzburgLinearMap_injective k u v
    change Q.originalGinzburgLinearMap k u v
      ((Q.originalGinzburgCutDegreeZeroEquiv k u v c).symm
        (Q.ginzburgCutNegativeOneDifferential k φ u v c x)).val=
      Q.originalGinzburgLinearMap k u v
        (Q.ginzburgBoundaryLift k φ u v ⟨x.val,x.property.1⟩)
    rw [Q.originalGinzburgCutDegreeZeroEquiv_symm_coe,
      Q.originalGinzburgLinearMap_boundaryLift]
    rfl
  rw [heq,Q.ginzburgCutBoundaryLift_range]

noncomputable def ginzburgCutZeroQuotientJacobianEquiv (φ : Q.Potential k)
    (u v : Q.Vertex) (c : ℤ) :
    (Q.ginzburgCutCohomologicalComponent k u v 0 c ⧸
      LinearMap.range (Q.ginzburgCutNegativeOneDifferential k φ u v c)) ≃ₗ[k]
        (Q.pathCutComponent k u v c ⧸ Q.pathJacobianCutIdeal k φ u v c) :=
  Submodule.Quotient.equiv _ _ (Q.originalGinzburgCutDegreeZeroEquiv k u v c).symm
    (Q.ginzburgCutGradedBoundary_map k φ u v c)

noncomputable def ginzburgCutHomologyZeroJacobianIso (φ : Q.Potential k)
    (u v : Q.Vertex) (c : ℤ) :
    Q.ginzburgCutHomology k φ u v c 0 ≅
      ModuleCat.of k (Q.pathCutComponent k u v c ⧸ Q.pathJacobianCutIdeal k φ u v c) :=
  Q.ginzburgCutHomologyZeroQuotientIso k φ u v c ≪≫
    (Q.ginzburgCutZeroQuotientJacobianEquiv k φ u v c).toModuleIso

end ASGinzburg.CutQuiver
