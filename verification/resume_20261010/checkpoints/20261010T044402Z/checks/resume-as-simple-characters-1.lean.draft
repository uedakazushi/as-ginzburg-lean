import work.ASGinzburgDraft.PeriodCutSimpleRightEquiv
import work.ASGinzburgDraft.ASCutOrdinaryResolutions

/-! From the original AS condition, each ordinary vertex simple has
its actual scalar augmentation character, for arbitrary universes. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

noncomputable def ASRegular.cutOrdinarySimpleFieldEquiv (hAS : A.ASRegular Q)
    (x : Q.LiftVertex) : (hAS.cutGradedSimple A Q x).space ≃ₗ[k] k :=
  (hAS.periodIso A Q).cornerSimpleTotalFieldEquiv Q x

theorem ASRegular.cutOrdinarySimpleFieldEquiv_smul (hAS : A.ASRegular Q)
    (x : Q.LiftVertex) (r : (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ)
    (a : hAS.cutOrdinarySimple A Q x) :
    hAS.cutOrdinarySimpleFieldEquiv A Q x (r • a)=
      (hAS.periodIso A Q).cutVertexCharacter Q x.1 r.unop*
        hAS.cutOrdinarySimpleFieldEquiv A Q x a :=
  (hAS.periodIso A Q).cornerSimpleTotalFieldEquiv_right_action Q x r.unop a

noncomputable def ASRegular.cutOrdinarySimpleVertexLinearEquiv (hAS : A.ASRegular Q)
    (x : Q.LiftVertex) :
    letI := (hAS.periodIso A Q).cutVertexRightModule Q x.1
    (hAS.cutOrdinarySimple A Q x) ≃ₗ[(hAS.CutGradedAlgebra A Q)ᵐᵒᵖ] k :=
  (hAS.periodIso A Q).cornerSimpleVertexRightLinearEquiv Q x

noncomputable def ASRegular.cutOrdinarySimpleSheetIso (hAS : A.ASRegular Q)
    (i : Q.Vertex) (s t : ℤ) :
    hAS.cutOrdinarySimple A Q (i,s) ≅ hAS.cutOrdinarySimple A Q (i,t) :=
  (hAS.periodIso A Q).cornerSimpleSheetRightIso Q i s t

end ASGinzburg.ZAlgebra
