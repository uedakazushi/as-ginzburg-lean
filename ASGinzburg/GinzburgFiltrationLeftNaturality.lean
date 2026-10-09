import ASGinzburg.GinzburgAssociatedLeftAction
import ASGinzburg.GinzburgGeneratorFiltrationHomologySequence
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-! Left multiplication gives actual morphisms of the filtration short
exact sequences, hence naturality of the genuine connecting maps. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def ginzburgFiltrationLeftShortComplexMap (φ : Q.Potential k)
    {x y v : Q.LiftVertex} (r : ℤ)
    (f : Q.ginzburgCutCohomologicalComponent k x.1 y.1 0 (y.2-x.2)) :
    Q.ginzburgGeneratorFilteredShortComplex k φ y.1 v.1 r (v.2-y.2) ⟶
      Q.ginzburgGeneratorFilteredShortComplex k φ x.1 v.1 r (v.2-x.2) :=
  ShortComplex.homMk (Q.ginzburgFilteredLeftCochainMap k φ (r+1) f)
    (Q.ginzburgFilteredLeftCochainMap k φ r f)
    (Q.ginzburgAssociatedLeftCochainMap k φ r f)
    (Q.ginzburgFilteredLeftCochainMap_inclusion k φ r f)
    (Q.ginzburgFilteredLeftCochainMap_quotient k φ r f)

noncomputable def ginzburgFilteredLeftHomology (φ : Q.Potential k)
    {x y v : Q.LiftVertex} (r q : ℤ)
    (f : Q.ginzburgCutCohomologicalComponent k x.1 y.1 0 (y.2-x.2)) :
    Q.ginzburgGeneratorFilteredHomology k φ y.1 v.1 r (v.2-y.2) q ⟶
      Q.ginzburgGeneratorFilteredHomology k φ x.1 v.1 r (v.2-x.2) q :=
  HomologicalComplex.homologyMap (Q.ginzburgFilteredLeftCochainMap k φ r f) q

noncomputable def ginzburgAssociatedLeftHomology (φ : Q.Potential k)
    {x y v : Q.LiftVertex} (r q : ℤ)
    (f : Q.ginzburgCutCohomologicalComponent k x.1 y.1 0 (y.2-x.2)) :
    Q.ginzburgAssociatedGradedHomology k φ y.1 v.1 r (v.2-y.2) q ⟶
      Q.ginzburgAssociatedGradedHomology k φ x.1 v.1 r (v.2-x.2) q :=
  HomologicalComplex.homologyMap (Q.ginzburgAssociatedLeftCochainMap k φ r f) q

theorem ginzburgFiltrationConnecting_left_naturality (φ : Q.Potential k)
    {x y v : Q.LiftVertex} (r q : ℤ)
    (f : Q.ginzburgCutCohomologicalComponent k x.1 y.1 0 (y.2-x.2)) :
    Q.ginzburgGeneratorFiltrationConnecting k φ y.1 v.1 r (v.2-y.2) q ≫
        Q.ginzburgFilteredLeftHomology k φ (r+1) (q+1) f=
      Q.ginzburgAssociatedLeftHomology k φ r q f ≫
        Q.ginzburgGeneratorFiltrationConnecting k φ x.1 v.1 r (v.2-x.2) q :=
  HomologicalComplex.HomologySequence.δ_naturality
    (Q.ginzburgFiltrationLeftShortComplexMap k φ r f)
    (Q.ginzburgGeneratorFilteredShortComplex_shortExact k φ y.1 v.1 r (v.2-y.2))
    (Q.ginzburgGeneratorFilteredShortComplex_shortExact k φ x.1 v.1 r (v.2-x.2))
    q (q+1) (by simp)

theorem ginzburgFilteredInclusionHomology_left_naturality (φ : Q.Potential k)
    {x y v : Q.LiftVertex} (r q : ℤ)
    (f : Q.ginzburgCutCohomologicalComponent k x.1 y.1 0 (y.2-x.2)) :
    Q.ginzburgFilteredLeftHomology k φ (r+1) q f ≫
        Q.ginzburgGeneratorFilteredInclusionHomology k φ x.1 v.1 r (v.2-x.2) q=
      Q.ginzburgGeneratorFilteredInclusionHomology k φ y.1 v.1 r (v.2-y.2) q ≫
        Q.ginzburgFilteredLeftHomology k φ r q f := by
  have he := congrArg
    ((HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.up ℤ) q).map)
    (Q.ginzburgFilteredLeftCochainMap_inclusion k φ (v:=v) r f)
  simpa only [Functor.map_comp] using he

theorem ginzburgFilteredQuotientHomology_left_naturality (φ : Q.Potential k)
    {x y v : Q.LiftVertex} (r q : ℤ)
    (f : Q.ginzburgCutCohomologicalComponent k x.1 y.1 0 (y.2-x.2)) :
    Q.ginzburgFilteredLeftHomology k φ r q f ≫
        Q.ginzburgGeneratorFilteredQuotientHomology k φ x.1 v.1 r (v.2-x.2) q=
      Q.ginzburgGeneratorFilteredQuotientHomology k φ y.1 v.1 r (v.2-y.2) q ≫
        Q.ginzburgAssociatedLeftHomology k φ r q f := by
  have he := congrArg
    ((HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.up ℤ) q).map)
    (Q.ginzburgFilteredLeftCochainMap_quotient k φ (v:=v) r f)
  simpa only [Functor.map_comp] using he

end ASGinzburg.CutQuiver
