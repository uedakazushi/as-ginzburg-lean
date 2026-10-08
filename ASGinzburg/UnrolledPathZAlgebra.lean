import ASGinzburg.UnrolledPathAlgebra
import ASGinzburg.UnrolledPathFiniteness

/-! The actual free unrolled path components form a locally finite directed
Z-algebra with the original cut quiver's height indexing. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

@[simp] theorem height_heightEquiv_symm (i : ℤ) :
    Q.height (Q.heightEquiv.symm i) = i :=
  (Q.heightEquiv_apply _).symm.trans (Q.heightEquiv.apply_symm_apply i)

noncomputable def unrolledPathZAlgebra : ZAlgebra.{u,u} k where
  Hom i j := Q.UnrolledPathComponent k (Q.heightEquiv.symm i) (Q.heightEquiv.symm j)
  id i := Q.unrolledPathId k (Q.heightEquiv.symm i)
  comp := Q.unrolledPathComp k
  comp_id := Q.unrolledPathComp_id k
  id_comp := Q.id_unrolledPathComp k
  comp_assoc := Q.unrolledPathComp_assoc k
  positive := by
    intro i j h f
    haveI : IsEmpty (Q.UnrolledPath (Q.heightEquiv.symm i) (Q.heightEquiv.symm j)) :=
      ⟨fun p => by have hp := p.height_le; simp only [Q.height_heightEquiv_symm] at hp; omega⟩
    exact Subsingleton.elim _ _
  connected := by
    intro i f
    refine ⟨f (.nil (Q.heightEquiv.symm i)),?_⟩
    ext p
    rw [p.diagonal_eq_nil]
    simp [unrolledPathId,Finsupp.smul_single,smul_eq_mul]
  id_nonzero := by
    intro i
    simp [unrolledPathId]
  finite := by
    intro i j
    letI := Fintype.ofFinite (Q.UnrolledPath (Q.heightEquiv.symm i) (Q.heightEquiv.symm j))
    infer_instance

end ASGinzburg.CutQuiver
