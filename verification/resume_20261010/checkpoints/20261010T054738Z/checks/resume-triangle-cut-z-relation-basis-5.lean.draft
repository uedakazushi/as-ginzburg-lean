import work.ASGinzburgDraft.TriangleQuadraticPaths
import work.ASGinzburgDraft.TriangleJacobianQuadraticRelations
import work.ASGinzburgDraft.QuadraticHilbertGrowth
import ASGinzburg.JacobianUnrollingQuotient
import ASGinzburg.GinzburgRegularImpliesASRegular

/-! Original Ginzburg regularity forces the three original cut-arrow
derivatives to be a basis of the actual quadratic relation space. -/
namespace ASGinzburg
universe u
variable (k : Type u) [Field k]

noncomputable def triangleJacobianQuadraticQuotientEquiv (φ : triangle333.Potential k) :
    (triangle333.pathCutComponent k 0 2 0 ⧸
      triangle333.pathJacobianCutIdeal k φ 0 2 0) ≃ₗ[k]
        (triangle333.unrolledJacobianZAlgebra k φ).Hom 0 2 :=
  triangle333.homogeneousJacobianUnrolledEquiv k φ (0,0) (2,0)

theorem triangleGinzburgRegular_hom02_finrank (φ : triangle333.Potential k)
    (hG : triangle333.GinzburgRegular k φ) :
    Module.finrank k ((triangle333.unrolledJacobianZAlgebra k φ).Hom 0 2) = 6 := by
  let A := triangle333.unrolledJacobianZAlgebra k φ
  have hAS : A.QuadraticASRegular :=
    (ZAlgebra.quadraticASRegular_iff_triangleASRegular A).mpr (hG.asRegular triangle333 k φ)
  simpa using hAS.component_finrank A 0 2

theorem triangleGinzburgRegular_quadraticQuotient_finrank (φ : triangle333.Potential k)
    (hG : triangle333.GinzburgRegular k φ) :
    Module.finrank k (triangle333.pathCutComponent k 0 2 0 ⧸
      triangle333.pathJacobianCutIdeal k φ 0 2 0) = 6 := by
  rw [(triangleJacobianQuadraticQuotientEquiv k φ).finrank_eq]
  exact triangleGinzburgRegular_hom02_finrank k φ hG

theorem triangleGinzburgRegular_quadraticIdeal_finrank (φ : triangle333.Potential k)
    (hG : triangle333.GinzburgRegular k φ) :
    Module.finrank k (triangle333.pathJacobianCutIdeal k φ 0 2 0) = 3 := by
  have hs := Submodule.finrank_quotient_add_finrank
    (triangle333.pathJacobianCutIdeal k φ 0 2 0)
  rw [triangleGinzburgRegular_quadraticQuotient_finrank k φ hG,
    triangleXYCutComponent_finrank k] at hs
  omega

noncomputable def triangleCutZRelation (φ : triangle333.Potential k) (z : Fin 3) :
    triangle333.pathJacobianCutIdeal k φ 0 2 0 :=
  ⟨triangleCutZDerivative k φ z,triangleCutZDerivative_mem_ideal k φ z⟩

theorem triangleCutZRelation_span_eq_top (φ : triangle333.Potential k) :
    Submodule.span k (Set.range (triangleCutZRelation k φ)) = ⊤ := by
  apply top_unique
  intro x _
  let J := triangle333.pathJacobianCutIdeal k φ 0 2 0
  apply (Submodule.apply_mem_span_image_iff_mem_span
    (f := J.subtype) J.injective_subtype).mp
  have himage : J.subtype '' Set.range (triangleCutZRelation k φ) =
      Set.range (triangleCutZDerivative k φ) := by
    ext y
    constructor
    · rintro ⟨x,⟨z,rfl⟩,rfl⟩
      exact ⟨z,rfl⟩
    · rintro ⟨z,rfl⟩
      exact ⟨triangleCutZRelation k φ z,⟨z,rfl⟩,rfl⟩
  rw [himage,←triangleJacobianCutIdeal_eq_span_cutZ k φ]
  exact x.property

noncomputable def triangleCutZRelationBasis (φ : triangle333.Potential k)
    (hG : triangle333.GinzburgRegular k φ) :
    Module.Basis (Fin 3) k (triangle333.pathJacobianCutIdeal k φ 0 2 0) :=
  basisOfTopLeSpanOfCardEqFinrank (triangleCutZRelation k φ)
    (triangleCutZRelation_span_eq_top k φ).ge (by
      rw [triangleGinzburgRegular_quadraticIdeal_finrank k φ hG]
      rfl)

@[simp] theorem triangleCutZRelationBasis_apply (φ : triangle333.Potential k)
    (hG : triangle333.GinzburgRegular k φ) (z : Fin 3) :
    triangleCutZRelationBasis k φ hG z = triangleCutZRelation k φ z := by
  exact congrFun (coe_basisOfTopLeSpanOfCardEqFinrank _ _ _) z

theorem triangleCutZDerivative_linearIndependent (φ : triangle333.Potential k)
    (hG : triangle333.GinzburgRegular k φ) :
    LinearIndependent k (triangleCutZDerivative k φ) := by
  have hb : ⇑(triangleCutZRelationBasis k φ hG) = triangleCutZRelation k φ := by
    funext z
    exact triangleCutZRelationBasis_apply k φ hG z
  have h := (triangleCutZRelationBasis k φ hG).linearIndependent
  rw [hb] at h
  have he : (triangle333.pathJacobianCutIdeal k φ 0 2 0).subtype ∘
      triangleCutZRelation k φ = triangleCutZDerivative k φ := rfl
  rw [←he]
  exact h.map' _ (Submodule.ker_subtype _)

end ASGinzburg
