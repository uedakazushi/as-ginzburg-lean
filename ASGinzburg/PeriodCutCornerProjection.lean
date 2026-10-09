import ASGinzburg.PeriodCutCorners

/-! The two vertex idempotents project each homogeneous block onto its
actual matrix component. The homogeneous corner is precisely the range
of the injective component embedding. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
universe u v w
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k} {p : ℤ}
variable (E : A.PeriodIso p) {ι : Type w} [Fintype ι] (vertex : ι → ℤ)

theorem cutVertexIdempotent_mul_component_ne (m : ℕ) (i j t : ι)
    (f : E.CutGradedHom m (vertex i) (vertex j)) (h : j≠t) :
    E.cutVertexIdempotent vertex t * E.cutHomogeneousComponentLinear vertex m i j f=0 := by
  rw [cutVertexIdempotent,cutHomogeneousComponentLinear_apply,E.cutHomogeneousInclusion_mul]
  change E.cutHomogeneousInclusion vertex (0+m)
    (E.cutBlockTransport vertex (m+0) (0+m) (Nat.add_comm m 0)
      (E.cutMatrixComp vertex m 0 (E.cutMatrixComponent vertex 0 t t (E.cutGradedId (vertex t)))
        (E.cutMatrixComponent vertex m i j f)))=0
  rw [E.cutMatrixComp_component_ne vertex m 0 i j t t f _ h,map_zero,map_zero]

theorem cutComponent_mul_vertexIdempotent_ne (m : ℕ) (i j t : ι)
    (f : E.CutGradedHom m (vertex i) (vertex j)) (h : i≠t) :
    E.cutHomogeneousComponentLinear vertex m i j f * E.cutVertexIdempotent vertex t=0 := by
  rw [cutVertexIdempotent,cutHomogeneousComponentLinear_apply,E.cutHomogeneousInclusion_mul]
  change E.cutHomogeneousInclusion vertex (m+0)
    (E.cutBlockTransport vertex (0+m) (m+0) (Nat.add_comm 0 m)
      (E.cutMatrixComp vertex 0 m (E.cutMatrixComponent vertex m i j f)
        (E.cutMatrixComponent vertex 0 t t (E.cutGradedId (vertex t)))))=0
  rw [E.cutMatrixComp_component_ne vertex 0 m t t i j _ f (Ne.symm h),map_zero,map_zero]

theorem sum_cutHomogeneousComponentLinear (m : ℕ) (x : E.CutGradedBlock vertex m) :
    (∑ i : ι,∑ j : ι,E.cutHomogeneousComponentLinear vertex m i j (x i j))=
      E.cutHomogeneousLinearInclusion vertex m x := by
  simp only [cutHomogeneousComponentLinear_apply,← map_sum]
  exact congrArg (E.cutHomogeneousInclusion vertex m) (E.sum_cutMatrixComponent vertex m x)

theorem cutHomogeneous_corner_projection (m : ℕ) (i j : ι) (x : E.CutGradedBlock vertex m) :
    E.cutVertexIdempotent vertex j * E.cutHomogeneousLinearInclusion vertex m x *
      E.cutVertexIdempotent vertex i=E.cutHomogeneousComponentLinear vertex m i j (x i j) := by
  rw [← E.sum_cutHomogeneousComponentLinear vertex m x]
  simp only [Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · rw [E.cutVertexIdempotent_mul_component,E.cutComponent_mul_vertexIdempotent]
    · intro b hb h
      rw [E.cutVertexIdempotent_mul_component_ne vertex m i b j _ h,zero_mul]
    · simp
  · intro a ha h
    apply Finset.sum_eq_zero
    intro b hb
    rw [mul_assoc,E.cutComponent_mul_vertexIdempotent_ne vertex m a b i _ h,mul_zero]
  · simp

theorem mem_cutHomogeneousComponentRange_iff (m : ℕ) (i j : ι) (r : E.CutGradedRing vertex) :
    r ∈ LinearMap.range (E.cutHomogeneousComponentLinear vertex m i j) ↔
      (∃ x : E.CutGradedBlock vertex m, r=E.cutHomogeneousLinearInclusion vertex m x) ∧
        E.cutVertexIdempotent vertex j * r * E.cutVertexIdempotent vertex i=r := by
  constructor
  · rintro ⟨f,rfl⟩
    refine ⟨⟨E.cutMatrixComponent vertex m i j f,rfl⟩,?_⟩
    rw [E.cutVertexIdempotent_mul_component,E.cutComponent_mul_vertexIdempotent]
  · rintro ⟨⟨x,rfl⟩,h⟩
    exact ⟨x i j,(E.cutHomogeneous_corner_projection vertex m i j x).symm.trans h⟩

noncomputable def cutHomogeneousCornerEquiv (m : ℕ) (i j : ι) :
    E.CutGradedHom m (vertex i) (vertex j) ≃ₗ[k]
      LinearMap.range (E.cutHomogeneousComponentLinear vertex m i j) :=
  LinearEquiv.ofInjective (E.cutHomogeneousComponentLinear vertex m i j)
    (E.cutHomogeneousComponentLinear_injective vertex m i j)

end ASGinzburg.ZAlgebra.PeriodIso
