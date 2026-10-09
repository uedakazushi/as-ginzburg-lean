import ASGinzburg.ZeroCutPathAlgebra
import ASGinzburg.PathCutUnrollingComparison

/-! Actual non-cut path components unroll to sheet zero with their
original units and composition preserved. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def zeroCutNativeUnrollingEquiv (i j : Q.Vertex) :
    Q.pathCutComponent k i j 0 ≃ₗ[k] Q.UnrolledPathComponent k (i,0) (j,0) :=
  Q.pathCutUnrollingEquiv k i j 0 0

theorem zeroCutNativeUnrollingEquiv_erase (i j : Q.Vertex)
    (f : Q.pathCutComponent k i j 0) :
    Q.unrolledPathEraseLinearMap k (i,0) (j,0) (Q.zeroCutNativeUnrollingEquiv k i j f)=f.val :=
  Q.pathCutUnrollingEquiv_erase k i j 0 0 f

theorem zeroCutNativeUnrollingEquiv_id (i : Q.Vertex) :
    Q.zeroCutNativeUnrollingEquiv k i i (Q.zeroCutPathId k i)=Q.unrolledPathId k (i,0) := by
  apply Q.unrolledPathEraseLinearMap_injective k (i,0) (i,0)
  rw [Q.zeroCutNativeUnrollingEquiv_erase]
  simpa [zeroCutPathId,pathId,unrolledPathId,UnrolledPath.erase] using
    (Q.unrolledPathEraseLinearMap_single k (.nil (i,0)) 1).symm

theorem zeroCutNativeUnrollingEquiv_comp {i j l : Q.Vertex}
    (f : Q.pathCutComponent k i j 0) (g : Q.pathCutComponent k j l 0) :
    Q.zeroCutNativeUnrollingEquiv k i l (Q.zeroCutPathComp k g f)=
      Q.unrolledPathComp k (Q.zeroCutNativeUnrollingEquiv k j l g)
        (Q.zeroCutNativeUnrollingEquiv k i j f) := by
  apply Q.unrolledPathEraseLinearMap_injective k (i,0) (l,0)
  rw [Q.zeroCutNativeUnrollingEquiv_erase,Q.unrolledPathEraseLinearMap_comp,
    Q.zeroCutNativeUnrollingEquiv_erase,Q.zeroCutNativeUnrollingEquiv_erase]
  rfl

end ASGinzburg.CutQuiver
