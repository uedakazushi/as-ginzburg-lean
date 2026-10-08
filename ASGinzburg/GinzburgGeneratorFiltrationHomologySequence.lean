import ASGinzburg.GinzburgGeneratorFiltrationShortExact

/-! The connecting maps and long exact homology sequence come from
the actual short exact sequence of generator-filtered complexes. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory CategoryTheory.Limits
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def ginzburgGeneratorFilteredHomology (φ : Q.Potential k)
    (u v : Q.Vertex) (r c q : ℤ) : ModuleCat.{u} k :=
  (Q.ginzburgGeneratorFilteredComplex k φ u v r c).homology q

noncomputable def ginzburgGeneratorFilteredInclusionHomology (φ : Q.Potential k)
    (u v : Q.Vertex) (r c q : ℤ) :
    Q.ginzburgGeneratorFilteredHomology k φ u v (r+1) c q ⟶
      Q.ginzburgGeneratorFilteredHomology k φ u v r c q :=
  HomologicalComplex.homologyMap (Q.ginzburgGeneratorFilteredInclusion k φ u v r c) q

noncomputable def ginzburgGeneratorFilteredQuotientHomology (φ : Q.Potential k)
    (u v : Q.Vertex) (r c q : ℤ) :
    Q.ginzburgGeneratorFilteredHomology k φ u v r c q ⟶
      Q.ginzburgAssociatedGradedHomology k φ u v r c q :=
  HomologicalComplex.homologyMap (Q.ginzburgFilteredToAssociatedGraded k φ u v r c) q

noncomputable def ginzburgGeneratorFiltrationConnecting (φ : Q.Potential k)
    (u v : Q.Vertex) (r c q : ℤ) :
    Q.ginzburgAssociatedGradedHomology k φ u v r c q ⟶
      Q.ginzburgGeneratorFilteredHomology k φ u v (r+1) c (q+1) :=
  (Q.ginzburgGeneratorFilteredShortComplex_shortExact k φ u v r c).δ q (q+1) (by simp)

theorem ginzburgGeneratorFiltrationConnecting_comp (φ : Q.Potential k)
    (u v : Q.Vertex) (r c q : ℤ) :
    Q.ginzburgGeneratorFiltrationConnecting k φ u v r c q ≫
      Q.ginzburgGeneratorFilteredInclusionHomology k φ u v r c (q+1)=0 :=
  (Q.ginzburgGeneratorFilteredShortComplex_shortExact k φ u v r c).δ_comp q (q+1) (by simp)

theorem ginzburgGeneratorFilteredQuotientHomology_comp_connecting (φ : Q.Potential k)
    (u v : Q.Vertex) (r c q : ℤ) :
    Q.ginzburgGeneratorFilteredQuotientHomology k φ u v r c q ≫
      Q.ginzburgGeneratorFiltrationConnecting k φ u v r c q=0 :=
  (Q.ginzburgGeneratorFilteredShortComplex_shortExact k φ u v r c).comp_δ q (q+1) (by simp)

theorem ginzburgGeneratorFiltrationHomology_exact₁ (φ : Q.Potential k)
    (u v : Q.Vertex) (r c q : ℤ) :
    (ShortComplex.mk (Q.ginzburgGeneratorFiltrationConnecting k φ u v r c q)
      (Q.ginzburgGeneratorFilteredInclusionHomology k φ u v r c (q+1))
      (Q.ginzburgGeneratorFiltrationConnecting_comp k φ u v r c q)).Exact :=
  (Q.ginzburgGeneratorFilteredShortComplex_shortExact k φ u v r c).homology_exact₁
    q (q+1) (by simp)

theorem ginzburgGeneratorFiltrationHomology_exact₂ (φ : Q.Potential k)
    (u v : Q.Vertex) (r c q : ℤ) :
    ((Q.ginzburgGeneratorFilteredShortComplex k φ u v r c).map
      (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.up ℤ) q)).Exact :=
  (Q.ginzburgGeneratorFilteredShortComplex_shortExact k φ u v r c).homology_exact₂ q

theorem ginzburgGeneratorFiltrationHomology_exact₃ (φ : Q.Potential k)
    (u v : Q.Vertex) (r c q : ℤ) :
    (ShortComplex.mk (Q.ginzburgGeneratorFilteredQuotientHomology k φ u v r c q)
      (Q.ginzburgGeneratorFiltrationConnecting k φ u v r c q)
      (Q.ginzburgGeneratorFilteredQuotientHomology_comp_connecting k φ u v r c q)).Exact :=
  (Q.ginzburgGeneratorFilteredShortComplex_shortExact k φ u v r c).homology_exact₃
    q (q+1) (by simp)

end ASGinzburg.CutQuiver
