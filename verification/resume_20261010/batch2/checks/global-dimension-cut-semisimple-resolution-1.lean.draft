import work.ASGinzburgDraft.ASCutSemisimpleRightDimension
import work.ASGinzburgDraft.FiniteBiproductProjectiveResolution

/-! The genuine graded-radical quotient has a genuine four-term
ordinary projective resolution with finitely generated terms. It is
the finite direct sum of the original AS vertex resolutions. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

noncomputable def ASRegular.cutSemisimpleRightProjectiveResolution (hAS : A.ASRegular Q) :
    ProjectiveResolution (hAS.cutSemisimpleRightObject A Q) :=
  projectiveResolutionAlongIso
    (finiteBiproductProjectiveResolution (fun i : Q.Vertex => hAS.cutOrdinarySimple A Q (i,0))
      (fun i => hAS.cutOrdinarySimpleProjectiveResolution A Q (i,0)))
    (hAS.cutSemisimpleRightVertexIso A Q).symm

theorem ASRegular.cutSemisimpleRightProjectiveResolution_finite (hAS : A.ASRegular Q)
    (n : ℕ) : Module.Finite (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ
      ((hAS.cutSemisimpleRightProjectiveResolution A Q).complex.X n) :=
  finiteBiproductProjectiveResolution_finite
    (fun i : Q.Vertex => hAS.cutOrdinarySimple A Q (i,0))
    (fun i => hAS.cutOrdinarySimpleProjectiveResolution A Q (i,0)) n
    (fun i => hAS.cutOrdinarySimpleProjectiveResolution_finite A Q (i,0) n)

theorem ASRegular.cutSemisimpleRightProjectiveResolution_isZero_ge_four
    (hAS : A.ASRegular Q) (n : ℕ) :
    IsZero ((hAS.cutSemisimpleRightProjectiveResolution A Q).complex.X (n+4)) :=
  finiteBiproductProjectiveResolution_isZero
    (fun i : Q.Vertex => hAS.cutOrdinarySimple A Q (i,0))
    (fun i => hAS.cutOrdinarySimpleProjectiveResolution A Q (i,0)) (n+4)
    (fun i => hAS.cutOrdinarySimpleProjectiveResolution_isZero_ge_four A Q (i,0) n)

end ASGinzburg.ZAlgebra
