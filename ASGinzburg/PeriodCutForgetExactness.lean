import ASGinzburg.PeriodCutForgetScalarComparison
import Mathlib.CategoryTheory.Abelian.Exact

/-! Forgetting the integer grading preserves genuine exact sequences of
ordinary right R-modules, hence preserves homology. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices : ℤ))

theorem cornerModuleRingFunctor_map_exact
    (S : ShortComplex (E.cornerCoverZAlgebra Q).RightModule) (hS : S.Exact) :
    (S.map (E.cornerModuleRingFunctor Q)).Exact := by
  let R := (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))ᵐᵒᵖ
  let G := ModuleCat.restrictScalars (algebraMap k R)
  apply G.reflects_exact_of_faithful
  change (S.map (E.cornerModuleRingFunctor Q ⋙ G)).Exact
  exact ShortComplex.exact_of_iso
    (S.mapNatIso (E.cornerRingScalarNatIso Q)).symm
    (hS.map (E.cornerTotalSpaceFunctor Q))

noncomputable instance cornerModuleRingFunctorPreservesHomology :
    (E.cornerModuleRingFunctor Q).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ (E.cornerModuleRingFunctor_map_exact Q)

noncomputable instance cornerModuleRingFunctorPreservesFiniteLimits :
    PreservesFiniteLimits (E.cornerModuleRingFunctor Q) :=
  Functor.preservesFiniteLimits_of_preservesHomology _

noncomputable instance cornerModuleRingFunctorPreservesFiniteColimits :
    PreservesFiniteColimits (E.cornerModuleRingFunctor Q) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

theorem cornerModuleRingFunctor_map_shortExact
    (S : ShortComplex (E.cornerCoverZAlgebra Q).RightModule) (hS : S.ShortExact) :
    (S.map (E.cornerModuleRingFunctor Q)).ShortExact :=
  hS.map_of_exact _

theorem cornerModuleRingFunctor_exact_iff
    (S : ShortComplex (E.cornerCoverZAlgebra Q).RightModule) :
    (S.map (E.cornerModuleRingFunctor Q)).Exact ↔ S.Exact :=
  ShortComplex.exact_map_iff_of_faithful _ _

end ASGinzburg.ZAlgebra.PeriodIso
