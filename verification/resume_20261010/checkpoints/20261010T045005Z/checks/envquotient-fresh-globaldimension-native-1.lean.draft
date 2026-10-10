import work.ASGinzburgDraft.OrdinaryGlobalDimension
import work.ASGinzburgDraft.ASCutOrdinaryGlobalBounds
import work.ASGinzburgDraft.ASCutOrdinaryLeftSharpDimension

/-! The original AS condition gives global dimension three on both
sides of the actual ordinary cut algebra. The bounds range over all
ordinary modules, and actual semisimple modules attain them. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

theorem ASRegular.cutOrdinaryRight_globalDimension_eq_three
    (hAS : A.ASRegular Q) :
    ordinaryGlobalDimension.{v,v} (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ = 3 :=
  ordinaryGlobalDimension_eq_of_bound_and_attained
    (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ 3
    (hAS.cutOrdinaryRight_projectiveDimension_le_three A Q)
    (hAS.cutOrdinaryRight_projectiveDimension_three_attained A Q)

theorem ASRegular.cutOrdinaryLeft_globalDimension_eq_three
    (hAS : A.ASRegular Q) :
    ordinaryGlobalDimension.{v,v} (hAS.CutGradedAlgebra A Q) = 3 :=
  ordinaryGlobalDimension_eq_of_bound_and_attained
    (hAS.CutGradedAlgebra A Q) 3
    (hAS.cutOrdinaryLeft_projectiveDimension_le_three A Q)
    (hAS.cutOrdinaryLeft_projectiveDimension_three_attained A Q)

end ASGinzburg.ZAlgebra
