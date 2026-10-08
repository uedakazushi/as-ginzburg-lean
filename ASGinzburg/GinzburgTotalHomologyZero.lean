import ASGinzburg.GinzburgHomologyZero
import ASGinzburg.GinzburgRegularity

/-! Actual H-zero of the full finite quiver complex is the finite direct
sum of the genuine Jacobian quotient components. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory CategoryTheory.Limits
open scoped DirectSum
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def ginzburgTotalHomologyZeroJacobianIso (φ : Q.Potential k) :
    Q.ginzburgTotalHomology k φ 0 ≅
      ModuleCat.of k (⨁ uv : Q.Vertex×Q.Vertex,
        Q.PathComponent k uv.1 uv.2 ⧸ (Q.pathJacobianIdeal k φ).hom uv.1 uv.2) :=
  Q.ginzburgTotalHomologyComponentIso k φ 0 ≪≫
    Sigma.mapIso (fun uv : Q.Vertex×Q.Vertex => Q.ginzburgHomologyZeroJacobianIso k φ uv.1 uv.2) ≪≫
      ModuleCat.coprodIsoDirectSum _

end ASGinzburg.CutQuiver
