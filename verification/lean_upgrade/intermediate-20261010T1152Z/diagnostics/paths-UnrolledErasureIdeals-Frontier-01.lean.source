import ASGinzburg.UnrolledPathErasure
import ASGinzburg.UnrolledPathZAlgebra
import ASGinzburg.PathLinearIdeals
import ASGinzburg.ZAlgebraHomomorphisms

/-! Pullback of genuine two-sided path ideals under forgetting sheets
is a genuine linear ideal of the unrolled Z-algebra. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def unrolledErasureIdeal (I : Q.PathLinearIdeal k) :
    (Q.unrolledPathZAlgebra k).LinearIdeal where
  hom i j := (I.hom (Q.heightEquiv.symm i).1 (Q.heightEquiv.symm j).1).comap
    (Q.unrolledPathEraseLinearMap k (Q.heightEquiv.symm i) (Q.heightEquiv.symm j))
  comp_left := by
    intro i j l f hf g
    change Q.unrolledPathEraseLinearMap k _ _ (Q.unrolledPathComp k g f) ∈
      I.hom (Q.heightEquiv.symm i).1 (Q.heightEquiv.symm l).1
    rw [Q.unrolledPathEraseLinearMap_comp]
    exact I.comp_left hf _
  comp_right := by
    intro i j l g hg f
    change Q.unrolledPathEraseLinearMap k _ _ (Q.unrolledPathComp k g f) ∈
      I.hom (Q.heightEquiv.symm i).1 (Q.heightEquiv.symm l).1
    rw [Q.unrolledPathEraseLinearMap_comp]
    exact I.comp_right hg _

end ASGinzburg.CutQuiver
