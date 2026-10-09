import ASGinzburg.PeriodCornerCoverRecovery
import ASGinzburg.ASCutGradedDescent

/-! The AS conditions themselves provide R and its actual corner cover,
and the latter recovers A without an added periodicity hypothesis. -/
namespace ASGinzburg.ZAlgebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

noncomputable def ASRegular.cutCornerCover (hAS : A.ASRegular Q) : ZAlgebra.{u,v} k :=
  (hAS.periodIso A Q).cornerCoverZAlgebra Q

noncomputable def ASRegular.cutCornerCoverRecovery (hAS : A.ASRegular Q) :
    Isomorphism (hAS.cutCornerCover A Q) A :=
  (hAS.periodIso A Q).cornerCoverRecovery Q

noncomputable def ASRegular.cutVertexIdempotent (hAS : A.ASRegular Q) (i : Q.Vertex) :
    hAS.CutGradedAlgebra A Q :=
  (hAS.periodIso A Q).cutVertexIdempotent (fun t : Q.Vertex => (t.val:ℤ)) i

theorem ASRegular.sum_cutVertexIdempotent (hAS : A.ASRegular Q) :
    (∑ i : Q.Vertex,hAS.cutVertexIdempotent A Q i)=1 :=
  (hAS.periodIso A Q).sum_cutVertexIdempotent (fun t : Q.Vertex => (t.val:ℤ))

end ASGinzburg.ZAlgebra
