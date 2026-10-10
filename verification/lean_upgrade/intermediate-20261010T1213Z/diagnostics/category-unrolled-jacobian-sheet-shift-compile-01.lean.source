import ASGinzburg.UnrolledSheetShiftErasure
import ASGinzburg.BetweenSheetJacobianIdeals

/-! Actual unrolled Jacobian relations are invariant under every
integer sheet shift, by the homogeneous Jacobian ideal comparison. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem unrolledJacobianLiftIdeal_mem_iff_erase (φ : Q.Potential k)
    {x y : Q.LiftVertex} (f : Q.UnrolledPathComponent k x y) :
    f ∈ Q.unrolledJacobianLiftIdeal k φ x y ↔
      Q.unrolledPathEraseLinearMap k x y f ∈ (Q.pathJacobianIdeal k φ).hom x.1 y.1 := by
  constructor
  · exact Q.unrolledJacobianLiftIdeal_erase k φ
  · intro hf
    rw [← Q.betweenSheetJacobianIdeal_map k φ x y]
    refine ⟨(Q.betweenSheetLinearEquiv k x y).symm f, ?_,
      (Q.betweenSheetLinearEquiv k x y).apply_symm_apply f⟩
    change ((Q.betweenSheetLinearEquiv k x y).symm f).val ∈
      (Q.pathJacobianIdeal k φ).hom x.1 y.1
    rwa [Q.betweenSheetLinearEquiv_symm_coe]

theorem unrolledSheetShiftLinearEquiv_mem_Jacobian (φ : Q.Potential k)
    (r : ℤ) {x y : Q.LiftVertex} (f : Q.UnrolledPathComponent k x y) :
    Q.unrolledSheetShiftLinearEquiv k r x y f ∈
        Q.unrolledJacobianLiftIdeal k φ (Q.shift r x) (Q.shift r y) ↔
      f ∈ Q.unrolledJacobianLiftIdeal k φ x y := by
  rw [Q.unrolledJacobianLiftIdeal_mem_iff_erase k φ,
    Q.unrolledSheetShiftLinearEquiv_erase k,
    Q.unrolledJacobianLiftIdeal_mem_iff_erase k φ]
  rfl

theorem unrolledSheetShiftLinearEquiv_Jacobian (φ : Q.Potential k)
    (r : ℤ) (x y : Q.LiftVertex) :
    (Q.unrolledJacobianLiftIdeal k φ x y).map
        (Q.unrolledSheetShiftLinearEquiv k r x y).toLinearMap =
      Q.unrolledJacobianLiftIdeal k φ (Q.shift r x) (Q.shift r y) := by
  apply Submodule.ext
  intro f
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (Q.unrolledSheetShiftLinearEquiv_mem_Jacobian k φ r g).mpr hg
  · intro hf
    obtain ⟨g, rfl⟩ := (Q.unrolledSheetShiftLinearEquiv k r x y).surjective f
    exact ⟨g, (Q.unrolledSheetShiftLinearEquiv_mem_Jacobian k φ r g).mp hf, rfl⟩

end ASGinzburg.CutQuiver
