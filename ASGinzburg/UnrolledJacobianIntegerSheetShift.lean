import ASGinzburg.UnrolledJacobianErasureEquality
import ASGinzburg.PeriodIdealQuotient

/-! Every integer sheet shift preserves the actual full Jacobian
ideal and induces a multiplicative period of its genuine quotient. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem unrolledIntegerSheetShiftLinearEquiv_mem_Jacobian
    (φ : Q.Potential k) (r i j : ℤ) (f : (Q.unrolledPathZAlgebra k).Hom i j) :
    Q.unrolledIntegerSheetShiftLinearEquiv k r i j f ∈
        (Q.unrolledJacobianIdeal k φ).hom (i+Q.vertices*r) (j+Q.vertices*r) ↔
      f ∈ (Q.unrolledJacobianIdeal k φ).hom i j := by
  rw [Q.unrolledJacobianIdeal_eq_erasureIdeal k φ,
    Q.unrolledJacobianIdeal_eq_erasureIdeal k φ]
  change Q.unrolledPathEraseLinearMap k _ _
      (Finsupp.mapDomain (UnrolledPath.endpointEquiv Q
        (Q.shift_heightEquiv_symm r i) (Q.shift_heightEquiv_symm r j))
        (Q.unrolledSheetShiftLinearEquiv k r (Q.heightEquiv.symm i) (Q.heightEquiv.symm j) f)) ∈
      (Q.pathJacobianIdeal k φ).hom _ _ ↔
    Q.unrolledPathEraseLinearMap k _ _ f ∈ (Q.pathJacobianIdeal k φ).hom _ _
  exact (Q.unrolledEndpointEquiv_mem_erasureIdeal k (Q.pathJacobianIdeal k φ)
    (Q.shift_heightEquiv_symm r i) (Q.shift_heightEquiv_symm r j)
    (Q.unrolledSheetShiftLinearEquiv k r (Q.heightEquiv.symm i) (Q.heightEquiv.symm j) f)).trans
      (Q.unrolledSheetShiftLinearEquiv_mem_erasureIdeal k (Q.pathJacobianIdeal k φ) r f)

theorem unrolledIntegerSheetShiftLinearEquiv_Jacobian
    (φ : Q.Potential k) (r i j : ℤ) :
    ((Q.unrolledJacobianIdeal k φ).hom i j).map
        (Q.unrolledIntegerSheetShiftLinearEquiv k r i j).toLinearMap =
      (Q.unrolledJacobianIdeal k φ).hom (i+Q.vertices*r) (j+Q.vertices*r) := by
  ext f
  constructor
  · rintro ⟨g,hg,rfl⟩
    exact (Q.unrolledIntegerSheetShiftLinearEquiv_mem_Jacobian k φ r i j g).mpr hg
  · intro hf
    obtain ⟨g,rfl⟩ := (Q.unrolledIntegerSheetShiftLinearEquiv k r i j).surjective f
    exact ⟨g,(Q.unrolledIntegerSheetShiftLinearEquiv_mem_Jacobian k φ r i j g).mp hf,rfl⟩

noncomputable def unrolledJacobianSheetPeriodIso (φ : Q.Potential k) (r : ℤ) :
    (Q.unrolledJacobianZAlgebra k φ).PeriodIso (Q.vertices*r) :=
  (Q.unrolledPathSheetPeriodIso k r).idealQuotientPeriod (Q.unrolledJacobianIdeal k φ)
    (Q.unrolledJacobianIdeal_diagonal_eq_bot k φ)
    (Q.unrolledIntegerSheetShiftLinearEquiv_Jacobian k φ r)

theorem unrolledJacobianSheetPeriodIso_apply_mk (φ : Q.Potential k)
    (r i j : ℤ) (f : (Q.unrolledPathZAlgebra k).Hom i j) :
    (Q.unrolledJacobianSheetPeriodIso k φ r).map i j (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (Q.unrolledIntegerSheetShiftLinearEquiv k r i j f) := rfl

end ASGinzburg.CutQuiver
