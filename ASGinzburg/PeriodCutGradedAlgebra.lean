import ASGinzburg.PeriodCutGradedRing

/-! The actual cut-graded direct sum is a k-algebra, with the
componentwise scalar action and homogeneous multiplication. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
universe u v w
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k} {p : ℤ}
variable (E : A.PeriodIso p) {ι : Type w} [Fintype ι] (vertex : ι → ℤ)

theorem cutGradedMonoid_smul_mul (c : k) (x y : GradedMonoid (E.CutGradedBlock vertex)) :
    (c • x)*y=c • (x*y) := by
  rcases x with ⟨m,x⟩
  rcases y with ⟨n,y⟩
  change (Sigma.mk (m+n) (E.cutBlockMul vertex m n (c • x) y) :
    Σ q, E.CutGradedBlock vertex q)=Sigma.mk (m+n) (c • E.cutBlockMul vertex m n x y)
  apply congrArg (Sigma.mk (m+n))
  rw [map_smul,LinearMap.smul_apply]

theorem cutGradedMonoid_mul_smul (c : k) (x y : GradedMonoid (E.CutGradedBlock vertex)) :
    x*(c • y)=c • (x*y) := by
  rcases x with ⟨m,x⟩
  rcases y with ⟨n,y⟩
  change (Sigma.mk (m+n) (E.cutBlockMul vertex m n x (c • y)) :
    Σ q, E.CutGradedBlock vertex q)=Sigma.mk (m+n) (c • E.cutBlockMul vertex m n x y)
  apply congrArg (Sigma.mk (m+n))
  exact map_smul (E.cutBlockMul vertex m n x) c y

noncomputable instance cutBlockGAlgebra : DirectSum.GAlgebra k (E.CutGradedBlock vertex) where
  toFun :=
    { toFun := fun c => c • E.cutMatrixId vertex
      map_zero' := by simp
      map_add' := by intro c d; exact add_smul c d _ }
  map_one := by simp; rfl
  map_mul := by
    intro c d
    change (c*d) • (1 : GradedMonoid (E.CutGradedBlock vertex))=
      (c • (1 : GradedMonoid (E.CutGradedBlock vertex)))*
        (d • (1 : GradedMonoid (E.CutGradedBlock vertex)))
    rw [E.cutGradedMonoid_smul_mul,E.cutGradedMonoid_mul_smul,one_mul,smul_smul]
  commutes := by
    intro c x
    change (c • (1 : GradedMonoid (E.CutGradedBlock vertex)))*x=
      x*(c • (1 : GradedMonoid (E.CutGradedBlock vertex)))
    rw [E.cutGradedMonoid_smul_mul,E.cutGradedMonoid_mul_smul,one_mul,mul_one]
  smul_def := by
    intro c x
    change c • x=(c • (1 : GradedMonoid (E.CutGradedBlock vertex)))*x
    rw [E.cutGradedMonoid_smul_mul,one_mul]

noncomputable def cutHomogeneousLinearInclusion (m : ℕ) :
    E.CutGradedBlock vertex m →ₗ[k] E.CutGradedRing vertex :=
  DirectSum.lof k ℕ (E.CutGradedBlock vertex) m

theorem cutAlgebraMap_apply (c : k) :
    algebraMap k (E.CutGradedRing vertex) c=
      E.cutHomogeneousInclusion vertex 0 (c • E.cutMatrixId vertex) := rfl

theorem cutHomogeneousLinearInclusion_smul (m : ℕ) (c : k)
    (x : E.CutGradedBlock vertex m) :
    E.cutHomogeneousLinearInclusion vertex m (c • x)=
      c • E.cutHomogeneousLinearInclusion vertex m x := map_smul _ c x

end ASGinzburg.ZAlgebra.PeriodIso
