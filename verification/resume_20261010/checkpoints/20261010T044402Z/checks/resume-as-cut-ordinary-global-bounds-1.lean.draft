import work.ASGinzburgDraft.ASCutEnvelopingFiniteResolution
import ASGinzburg.EnvelopingModuleProjectiveDimension
import work.ASGinzburgDraft.EnvelopingLeftModuleProjectiveDimension

/-! The original AS condition bounds the projective dimension of every
ordinary right and left module over the actual cut algebra by three.
The actual semisimple right quotient attains this bound. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

theorem ASRegular.cutOrdinaryRight_hasProjectiveDimensionLE_three
    (hAS : A.ASRegular Q) (M : ModuleCat.{v} (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ) :
    HasProjectiveDimensionLE M 3 :=
  rightModule_hasProjectiveDimensionLE_three_of_enveloping_dimension k
    (hAS.CutGradedAlgebra A Q) M
    (hAS.cutRegularEnveloping_hasProjectiveDimensionLE_three A Q)

theorem ASRegular.cutOrdinaryLeft_hasProjectiveDimensionLE_three
    (hAS : A.ASRegular Q) (M : ModuleCat.{v} (hAS.CutGradedAlgebra A Q)) :
    HasProjectiveDimensionLE M 3 :=
  leftModule_hasProjectiveDimensionLE_three_of_enveloping_dimension k
    (hAS.CutGradedAlgebra A Q) M
    (hAS.cutRegularEnveloping_hasProjectiveDimensionLE_three A Q)

theorem ASRegular.cutOrdinaryRight_projectiveDimension_le_three
    (hAS : A.ASRegular Q) (M : ModuleCat.{v} (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ) :
    projectiveDimension M≤3 :=
  (projectiveDimension_le_iff M 3).mpr
    (hAS.cutOrdinaryRight_hasProjectiveDimensionLE_three A Q M)

theorem ASRegular.cutOrdinaryLeft_projectiveDimension_le_three
    (hAS : A.ASRegular Q) (M : ModuleCat.{v} (hAS.CutGradedAlgebra A Q)) :
    projectiveDimension M≤3 :=
  (projectiveDimension_le_iff M 3).mpr
    (hAS.cutOrdinaryLeft_hasProjectiveDimensionLE_three A Q M)

theorem ASRegular.cutOrdinaryRight_projectiveDimension_three_attained
    (hAS : A.ASRegular Q) :
    ∃ M : ModuleCat.{v} (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ, projectiveDimension M=3 :=
  ⟨hAS.cutSemisimpleRightObject A Q,
    hAS.cutSemisimpleRight_projectiveDimension_eq_three_unconditional A Q⟩

end ASGinzburg.ZAlgebra
