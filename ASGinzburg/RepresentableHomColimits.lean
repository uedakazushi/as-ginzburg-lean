import ASGinzburg.RightModuleExtLeftAction
import ASGinzburg.RightModuleHomology

/-!
# Representable Hom commutes with colimits

Linear Yoneda identifies the actual Hom functor with vertex evaluation.
This is the first necessary exchange result for Ext into the sum of P_i;
higher Ext and finite coproduct domains require further proofs.
-/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v w w'
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

noncomputable def representableHomEvaluationIso (i : ℤ) :
    (linearCoyoneda k A.RightModule).obj (op (A.representable i)) ≅
      A.rightModuleEvaluation i :=
  NatIso.ofComponents (fun M => (A.representableYonedaEquiv i M).toModuleIso) (by
    intro M N f
    apply ModuleCat.hom_ext
    ext g
    exact A.representableYonedaEquiv_comp i g f)

noncomputable instance rightModuleEvaluationPreservesColimitsOfShape (i : ℤ)
    (J : Type w) [Category.{w'} J] [HasColimitsOfShape J (ModuleCat.{v} k)] :
    PreservesColimitsOfShape J (A.rightModuleEvaluation i) := by
  dsimp [rightModuleEvaluation]
  infer_instance

noncomputable instance representableHomPreservesColimitsOfShape (i : ℤ)
    (J : Type w) [Category.{w'} J] [HasColimitsOfShape J (ModuleCat.{v} k)] :
    PreservesColimitsOfShape J
      ((linearCoyoneda k A.RightModule).obj (op (A.representable i))) :=
  preservesColimitsOfShape_of_natIso (A.representableHomEvaluationIso i).symm

/-- A canonical exchange isomorphism for Hom(P_i,-), including arbitrary
coproduct shapes permitted by the target universe. -/
noncomputable def representableHomColimitIso (i : ℤ)
    {J : Type w} [Category.{w'} J] [HasColimitsOfShape J (ModuleCat.{v} k)]
    (F : J ⥤ A.RightModule) :
    ModuleCat.of k (A.representable i ⟶ colimit F) ≅
      colimit (F ⋙ (linearCoyoneda k A.RightModule).obj (op (A.representable i))) :=
  preservesColimitIso ((linearCoyoneda k A.RightModule).obj (op (A.representable i))) F

/-- Degree-zero derived Ext agrees with Hom naturally in the whole second argument. -/
noncomputable def rightModuleExtZeroFunctorIso (M : A.RightModule) :
    A.rightModuleExtCovariant M 0 ≅ (linearCoyoneda k A.RightModule).obj (op M) :=
  NatIso.ofComponents (fun N => (A.rightModuleExtZeroLinearEquiv M N).toModuleIso) (by
    intro X Y f
    apply ModuleCat.hom_ext
    ext x
    apply (A.rightModuleExtZeroLinearEquiv M Y).symm.injective
    change (A.rightModuleExtZeroLinearEquiv M Y).symm
      ((A.rightModuleExtZeroLinearEquiv M Y)
        (x.comp (Abelian.Ext.mk₀ f) (by rfl))) =
      (A.rightModuleExtZeroLinearEquiv M Y).symm
        (A.rightModuleExtZeroLinearEquiv M X x ≫ f)
    rw [LinearEquiv.symm_apply_apply]
    change x.comp (Abelian.Ext.mk₀ f) (by rfl) =
      Abelian.Ext.mk₀ (A.rightModuleExtZeroLinearEquiv M X x ≫ f)
    rw [← Abelian.Ext.mk₀_comp_mk₀]
    congr 1
    exact (Abelian.Ext.mk₀_addEquiv₀_apply x).symm)

noncomputable instance representableExtZeroPreservesColimitsOfShape (i : ℤ)
    (J : Type w) [Category.{w'} J] [HasColimitsOfShape J (ModuleCat.{v} k)] :
    PreservesColimitsOfShape J (A.rightModuleExtCovariant (A.representable i) 0) :=
  preservesColimitsOfShape_of_natIso (A.rightModuleExtZeroFunctorIso (A.representable i)).symm

/-- Actual degree-zero Ext of P_i commutes with arbitrary allowed colimits. -/
noncomputable def representableExtZeroColimitIso (i : ℤ)
    {J : Type w} [Category.{w'} J] [HasColimitsOfShape J (ModuleCat.{v} k)]
    (F : J ⥤ A.RightModule) :
    ModuleCat.of k (Abelian.Ext.{v} (A.representable i) (colimit F) 0) ≅
      colimit (F ⋙ A.rightModuleExtCovariant (A.representable i) 0) :=
  preservesColimitIso (A.rightModuleExtCovariant (A.representable i) 0) F

end ASGinzburg.ZAlgebra
