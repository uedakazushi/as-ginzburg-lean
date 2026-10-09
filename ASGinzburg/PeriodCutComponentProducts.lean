import ASGinzburg.PeriodCutCornerProjection

/-! The ring products of actual homogeneous component embeddings are
exactly the shifted component composition used for the cover. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
universe u v w
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k} {p : ℤ}
variable (E : A.PeriodIso p) {ι : Type w} [Fintype ι] (vertex : ι → ℤ)

theorem cutHomogeneousComponentLinear_mul (m n : ℕ) (i j l : ι)
    (f : E.CutGradedHom m (vertex i) (vertex j))
    (g : E.CutGradedHom n (vertex j) (vertex l)) :
    E.cutHomogeneousComponentLinear vertex n j l g *
      E.cutHomogeneousComponentLinear vertex m i j f=
        E.cutHomogeneousComponentLinear vertex (m+n) i l (E.cutGradedComp m n g f) := by
  rw [cutHomogeneousComponentLinear_apply,cutHomogeneousComponentLinear_apply,
    cutHomogeneousComponentLinear_apply,E.cutHomogeneousInclusion_mul]
  apply DirectSum.of_eq_of_gradedMonoid_eq
  dsimp only [GradedMonoid.mk]
  rw [E.cutBlockMul_sigma]
  change (Sigma.mk (m+n)
    (E.cutMatrixComp vertex m n (E.cutMatrixComponent vertex n j l g)
      (E.cutMatrixComponent vertex m i j f)) : GradedMonoid (E.CutGradedBlock vertex))=
        Sigma.mk (m+n) (E.cutMatrixComponent vertex (m+n) i l (E.cutGradedComp m n g f))
  rw [E.cutMatrixComp_component_same]

omit [Fintype ι] in
theorem cutHomogeneousComponentLinear_gradeTransport (m n : ℕ) (h : m=n) (i j : ι)
    (f : E.CutGradedHom m (vertex i) (vertex j)) :
    E.cutHomogeneousComponentLinear vertex m i j f=
      E.cutHomogeneousComponentLinear vertex n i j
        (A.homTransport (vertex i) (vertex j+(m:ℤ)*p)
          (vertex i) (vertex j+(n:ℤ)*p) rfl (by rw [h]) f) := by
  subst n
  rfl

end ASGinzburg.ZAlgebra.PeriodIso
