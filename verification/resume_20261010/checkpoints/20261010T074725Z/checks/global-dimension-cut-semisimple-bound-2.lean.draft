import ASGinzburg.ScalarQuotientProjectiveDimension
import work.ASGinzburgDraft.ASCutOrdinarySimpleCharacters
import work.ASGinzburgDraft.ASCutOrdinarySimpleDimension
import ASGinzburg.ASCutGradedRadicalQuotient

/-! The actual graded-radical quotient is an ordinary right-R module
of projective dimension at most three. Its decomposition into genuine
ordinary vertex simples comes from their actual augmentation action. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

noncomputable def ASRegular.cutSemisimpleRightObject (hAS : A.ASRegular Q) :
    ModuleCat.{v} (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ :=
  idealQuotientRightObject (hAS.cutGradedRadical A Q)

noncomputable def ASRegular.cutSemisimpleRightVertexIso (hAS : A.ASRegular Q) :
    hAS.cutSemisimpleRightObject A Q ≅
      ⨁ (fun i : Q.Vertex => hAS.cutOrdinarySimple A Q (i,0)) := by
  let E := hAS.periodIso A Q
  have hJ : hAS.cutGradedRadical A Q=RingHom.ker (E.cutAugmentation Q).toRingHom :=
    E.cutGradedJacobson_eq_augmentationKernel Q
  letI : ∀ i : Q.Vertex, Module k (hAS.cutOrdinarySimple A Q (i,0)) := fun i =>
    inferInstanceAs (Module k (hAS.cutGradedSimple A Q (i,0)).space)
  exact (idealQuotientRightLinearEquivOfEq _ _ hJ).toModuleIso ≪≫
    scalarQuotientVertexBiproductIso (E.cutAugmentation Q) (E.cutAugmentation_surjective Q)
      (fun i => hAS.cutOrdinarySimple A Q (i,0))
      (fun i => hAS.cutOrdinarySimpleFieldEquiv A Q (i,0))
      (fun i r a => hAS.cutOrdinarySimpleFieldEquiv_smul A Q (i,0) r a)

instance ASRegular.cutSemisimpleRight_hasProjectiveDimensionLE_three
    (hAS : A.ASRegular Q) :
    HasProjectiveDimensionLE (hAS.cutSemisimpleRightObject A Q) 3 := by
  letI := finiteBiproduct_hasProjectiveDimensionLT
    (fun i : Q.Vertex => hAS.cutOrdinarySimple A Q (i,0)) 4
  exact hasProjectiveDimensionLT_of_iso (hAS.cutSemisimpleRightVertexIso A Q).symm 4

theorem ASRegular.cutSemisimpleRight_ext_ge_four_eq_zero (hAS : A.ASRegular Q)
    (N : ModuleCat.{v} (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ) (n : ℕ)
    (e : Abelian.Ext.{v} (hAS.cutSemisimpleRightObject A Q) N (n+4)) : e=0 :=
  e.eq_zero_of_hasProjectiveDimensionLT 4 (by omega)

end ASGinzburg.ZAlgebra
