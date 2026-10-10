import work.ASGinzburgDraft.PeriodCutForgetExactness

/-! The actual grading-forgetful functor on every graded R-module is
faithful and exact, by the proved equivalence with cover modules. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices : ℤ))

noncomputable def recoveredRingForgetNatIso :
    (E.cornerGradedModuleEquivalence Q).inverse ⋙ E.cornerModuleRingFunctor Q ≅
      E.cutGradedForgetFunctor Q :=
  (Functor.associator (E.cornerGradedModuleEquivalence Q).inverse
    (E.cornerGradedModuleFunctor Q) (E.cutGradedForgetFunctor Q)).symm ≪≫
    isoWhiskerRight (E.cornerGradedModuleEquivalence Q).counitIso
      (E.cutGradedForgetFunctor Q) ≪≫
    Functor.leftUnitor (E.cutGradedForgetFunctor Q)

noncomputable instance cutGradedForgetFunctorPreservesFiniteLimits :
    PreservesFiniteLimits (E.cutGradedForgetFunctor Q) :=
  preservesFiniteLimits_of_natIso (E.recoveredRingForgetNatIso Q)

noncomputable instance cutGradedForgetFunctorPreservesFiniteColimits :
    PreservesFiniteColimits (E.cutGradedForgetFunctor Q) :=
  preservesFiniteColimits_of_natIso (E.recoveredRingForgetNatIso Q)

theorem cutGradedForgetFunctor_exact_iff (S : ShortComplex (E.CutGradedRightModule Q)) :
    (S.map (E.cutGradedForgetFunctor Q)).Exact ↔ S.Exact :=
  ShortComplex.exact_map_iff_of_faithful _ _

theorem cutGradedForgetFunctor_map_shortExact (S : ShortComplex (E.CutGradedRightModule Q))
    (hS : S.ShortExact) : (S.map (E.cutGradedForgetFunctor Q)).ShortExact :=
  hS.map_of_exact _

end ASGinzburg.ZAlgebra.PeriodIso
