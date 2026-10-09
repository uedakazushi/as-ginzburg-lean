import ASGinzburg.UnrolledPathIntegerSheetShift

/-! The genuine full Jacobian ideal equals the erasure pullback
in every integer component, using the proved homogeneous comparison. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem unrolledJacobianIdeal_eq_erasureIdeal (φ : Q.Potential k) (i j : ℤ) :
    (Q.unrolledJacobianIdeal k φ).hom i j =
      (Q.unrolledErasureIdeal k (Q.pathJacobianIdeal k φ)).hom i j := by
  let P : ℤ → ℤ → Prop := fun a b =>
    (Q.unrolledJacobianIdeal k φ).hom a b =
      (Q.unrolledErasureIdeal k (Q.pathJacobianIdeal k φ)).hom a b
  let x := Q.heightEquiv.symm i
  let y := Q.heightEquiv.symm j
  have h : P (Q.height x) (Q.height y) := by
    apply Submodule.comap_injective_of_surjective (Q.unrolledComponentHeightEquiv k x y).surjective
    ext f
    change f ∈ Q.unrolledJacobianLiftIdeal k φ x y ↔
      Q.unrolledComponentHeightEquiv k x y f ∈
        (Q.unrolledErasureIdeal k (Q.pathJacobianIdeal k φ)).hom (Q.height x) (Q.height y)
    exact (Q.unrolledJacobianLiftIdeal_mem_iff_erase k φ f).trans
      (Q.unrolledComponentHeightEquiv_mem_erasureIdeal k (Q.pathJacobianIdeal k φ) x y f).symm
  change P (Q.height (Q.heightEquiv.symm i)) (Q.height (Q.heightEquiv.symm j)) at h
  rw [Q.height_heightEquiv_symm,Q.height_heightEquiv_symm] at h
  exact h

end ASGinzburg.CutQuiver
