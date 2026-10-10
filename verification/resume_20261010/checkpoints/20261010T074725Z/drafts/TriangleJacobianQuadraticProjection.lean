import work.ASGinzburgDraft.TriangleCutZRelationBasis
import work.ASGinzburgDraft.TriangleJacobianArrowQuotients
import work.ASGinzburgDraft.TriangleCutZDerivativeCoordinates

/-! The actual quadratic evaluation map has the genuine cut-Z relation
space as its kernel, and evaluates canonical XY paths as arrow products. -/
namespace ASGinzburg
universe u
variable (k : Type u) [Field k]

noncomputable def triangleJacobianQuadraticProjection (φ : triangle333.Potential k) :
    triangle333.pathCutComponent k 0 2 0 →ₗ[k]
      (triangle333.unrolledJacobianZAlgebra k φ).Hom 0 2 :=
  (triangleJacobianQuadraticQuotientEquiv k φ).toLinearMap.comp
    (triangle333.pathJacobianCutIdeal k φ 0 2 0).mkQ

theorem triangleJacobianQuadraticProjection_surjective (φ : triangle333.Potential k) :
    Function.Surjective (triangleJacobianQuadraticProjection k φ) :=
  (triangleJacobianQuadraticQuotientEquiv k φ).surjective.comp
    (triangle333.pathJacobianCutIdeal k φ 0 2 0).mkQ_surjective

theorem triangleJacobianQuadraticProjection_kernel (φ : triangle333.Potential k) :
    LinearMap.ker (triangleJacobianQuadraticProjection k φ) =
      triangle333.pathJacobianCutIdeal k φ 0 2 0 := by
  rw [triangleJacobianQuadraticProjection,LinearEquiv.ker_comp,Submodule.ker_mkQ]

theorem triangleJacobianQuadraticProjection_kernel_eq_span (φ : triangle333.Potential k) :
    LinearMap.ker (triangleJacobianQuadraticProjection k φ) =
      Submodule.span k (Set.range (triangleCutZDerivative k φ)) := by
  rw [triangleJacobianQuadraticProjection_kernel,triangleJacobianCutIdeal_eq_span_cutZ]

@[simp] theorem triangleJacobianQuadraticProjection_cutZ (φ : triangle333.Potential k)
    (z : Fin 3) :
    triangleJacobianQuadraticProjection k φ (triangleCutZDerivative k φ z) = 0 := by
  have h : triangleCutZDerivative k φ z ∈
      LinearMap.ker (triangleJacobianQuadraticProjection k φ) := by
    rw [triangleJacobianQuadraticProjection_kernel]
    exact triangleCutZDerivative_mem_ideal k φ z
  exact h

noncomputable def triangleXYCutVector (xy : Fin 3 × Fin 3) :
    triangle333.pathCutComponent k 0 2 0 :=
  ⟨Finsupp.single (triangleXYPath xy) 1,Finsupp.single_mem_supported _ _ (by simp)⟩

theorem triangleJacobianQuadraticProjection_XY (φ : triangle333.Potential k)
    (xy : Fin 3 × Fin 3) :
    triangleJacobianQuadraticProjection k φ (triangleXYCutVector k xy) =
      (triangle333.unrolledJacobianZAlgebra k φ).comp
        (triangleJacobianYArrow k φ xy.2) (triangleJacobianXArrow k φ xy.1) := by
  let f : triangle333.pathCutComponent k 0 1 0 :=
    ⟨Finsupp.single (triangleXPath xy.1) 1,Finsupp.single_mem_supported _ _ (by simp)⟩
  let g : triangle333.pathCutComponent k 1 2 0 :=
    ⟨Finsupp.single (triangleYPath xy.2) 1,Finsupp.single_mem_supported _ _ (by simp)⟩
  have h := triangle333.homogeneousJacobianUnrolledEquiv_comp k φ
    (u := (0,0)) (v := (1,0)) (w := (2,0))
    (Submodule.Quotient.mk f) (Submodule.Quotient.mk g)
  rw [triangle333.cutJacobianQuotientComp_mk k φ] at h
  have hp : triangle333.pathCutCompBetweenLinear k
      (u := (0,0)) (v := (1,0)) (w := (2,0)) g f = triangleXYCutVector k xy := by
    apply Subtype.ext
    change triangle333.pathComp k (Finsupp.single (triangleYPath xy.2) 1)
      (Finsupp.single (triangleXPath xy.1) 1) = Finsupp.single (triangleXYPath xy) 1
    rw [triangle333.pathComp_single k,one_mul]
    rfl
  rw [hp] at h
  exact h

noncomputable def triangleJacobianXYEvaluation (φ : triangle333.Potential k) :
    (Fin 3 × Fin 3 → k) →ₗ[k] (triangle333.unrolledJacobianZAlgebra k φ).Hom 0 2 :=
  (triangleJacobianQuadraticProjection k φ).comp (triangleXYCutComponentEquiv k).symm.toLinearMap

@[simp] theorem triangleJacobianXYEvaluation_single (φ : triangle333.Potential k)
    (xy : Fin 3 × Fin 3) :
    triangleJacobianXYEvaluation k φ (Pi.single xy 1) =
      (triangle333.unrolledJacobianZAlgebra k φ).comp
        (triangleJacobianYArrow k φ xy.2) (triangleJacobianXArrow k φ xy.1) := by
  rw [triangleJacobianXYEvaluation,LinearMap.comp_apply]
  change triangleJacobianQuadraticProjection k φ
    ((triangleXYCutComponentEquiv k).symm (Pi.single xy 1)) = _
  have hs : (triangleXYCutComponentEquiv k).symm (Pi.single xy 1) =
      triangleXYCutVector k xy := by
    apply Subtype.ext
    exact triangleXYCutComponentEquiv_symm_single k xy 1
  rw [hs]
  exact triangleJacobianQuadraticProjection_XY k φ xy

theorem triangleJacobianXYEvaluation_kernel_eq_tensorSlices (φ : triangle333.Potential k) :
    LinearMap.ker (triangleJacobianXYEvaluation k φ) =
      Submodule.span k (Set.range
        (tensorToCutRelations333 k ((triangleTensorPotentialEquiv k).symm φ))) := by
  rw [triangleJacobianXYEvaluation,LinearMap.ker_comp,
    triangleJacobianQuadraticProjection_kernel_eq_span,
    Submodule.comap_equiv_eq_map_symm,Submodule.map_span]
  have hs : ∀ z : Fin 3, triangleXYCutComponentEquiv k (triangleCutZDerivative k φ z) =
      tensorToCutRelations333 k ((triangleTensorPotentialEquiv k).symm φ) z := by
    intro z
    have h := triangleTensorPotential_cutZDerivative_coordinates k
      ((triangleTensorPotentialEquiv k).symm φ) z
    rwa [LinearEquiv.apply_symm_apply] at h
  congr 1
  ext r
  constructor
  · rintro ⟨d,⟨z,rfl⟩,rfl⟩
    exact ⟨z,(hs z).symm⟩
  · rintro ⟨z,rfl⟩
    exact ⟨triangleCutZDerivative k φ z,⟨z,rfl⟩,hs z⟩

theorem triangleJacobianXYEvaluation_surjective (φ : triangle333.Potential k) :
    Function.Surjective (triangleJacobianXYEvaluation k φ) :=
  (triangleJacobianQuadraticProjection_surjective k φ).comp
    (triangleXYCutComponentEquiv k).symm.surjective

end ASGinzburg
