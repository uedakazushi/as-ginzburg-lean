import ASGinzburg.PeriodCutGradedMonoid

/-! The nonnegative cut blocks give an actual unital ring on their
finite-support direct sum, using mathlib's graded ring construction. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open DirectSum
universe u v w
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k} {p : ℤ}
variable (E : A.PeriodIso p) {ι : Type w} [Fintype ι] (vertex : ι → ℤ)

noncomputable instance cutBlockGRing : DirectSum.GRing (E.CutGradedBlock vertex) where
  toGMonoid := inferInstance
  mul_zero := by
    intro m n x
    exact map_zero (E.cutBlockMul vertex m n x)
  zero_mul := by
    intro m n y
    change E.cutBlockMul vertex m n 0 y=0
    rw [map_zero,LinearMap.zero_apply]
  mul_add := by
    intro m n x y z
    exact map_add (E.cutBlockMul vertex m n x) y z
  add_mul := by
    intro m n x y z
    change E.cutBlockMul vertex m n (x+y) z=
      E.cutBlockMul vertex m n x z+E.cutBlockMul vertex m n y z
    rw [map_add,LinearMap.add_apply]
  natCast := fun n => n • E.cutMatrixId vertex
  natCast_zero := by simp
  natCast_succ := by intro n; rw [add_nsmul,one_nsmul]; rfl
  intCast := fun n => n • E.cutMatrixId vertex
  intCast_ofNat := by intro n; simp only [natCast_zsmul]
  intCast_negSucc_ofNat := by intro n; simp only [negSucc_zsmul]

abbrev CutGradedRing := ⨁ m : ℕ, E.CutGradedBlock vertex m

noncomputable def cutHomogeneousInclusion (m : ℕ) :
    E.CutGradedBlock vertex m →+ E.CutGradedRing vertex :=
  DirectSum.of (E.CutGradedBlock vertex) m

theorem cutHomogeneousInclusion_mul (m n : ℕ)
    (x : E.CutGradedBlock vertex m) (y : E.CutGradedBlock vertex n) :
    E.cutHomogeneousInclusion vertex m x * E.cutHomogeneousInclusion vertex n y =
      E.cutHomogeneousInclusion vertex (m+n) (E.cutBlockMul vertex m n x y) :=
  DirectSum.of_mul_of x y

theorem cutHomogeneousInclusion_one :
    E.cutHomogeneousInclusion vertex 0 (E.cutMatrixId vertex)=
      (1 : E.CutGradedRing vertex) := rfl

end ASGinzburg.ZAlgebra.PeriodIso
