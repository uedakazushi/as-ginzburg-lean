import ASGinzburg.GinzburgGeneratorLayerInverse

/-! The actual generator-layer comparison is an isomorphism of
mathlib complexes and transfers the genuine shifted-prefix homology. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory CategoryTheory.Limits
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

instance ginzburgGeneratorPrefixToAssociatedGraded_f_isIso (φ : Q.Potential k)
    (u v : Q.Vertex) (r c q : ℤ) :
    IsIso ((Q.ginzburgGeneratorPrefixToAssociatedGraded k φ u v r c).f q) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact Q.ginzburgGeneratorPrefixToGradedRow_bijective k u v r q c

instance ginzburgGeneratorPrefixToAssociatedGraded_isIso (φ : Q.Potential k)
    (u v : Q.Vertex) (r c : ℤ) :
    IsIso (Q.ginzburgGeneratorPrefixToAssociatedGraded k φ u v r c) :=
  HomologicalComplex.Hom.isIso_of_components _

noncomputable def ginzburgGeneratorPrefixGradedIso (φ : Q.Potential k)
    (u v : Q.Vertex) (r c : ℤ) :
    Q.ginzburgGeneratorPrefixComplex k φ u v r c ≅
      Q.ginzburgAssociatedGradedComplex k φ u v r c :=
  asIso (Q.ginzburgGeneratorPrefixToAssociatedGraded k φ u v r c)

noncomputable def ginzburgAssociatedGradedHomology (φ : Q.Potential k)
    (u v : Q.Vertex) (r c q : ℤ) : ModuleCat.{u} k :=
  (Q.ginzburgAssociatedGradedComplex k φ u v r c).homology q

noncomputable def ginzburgAssociatedGradedPrefixHomologyIso (φ : Q.Potential k)
    (u v : Q.Vertex) (r c q : ℤ) :
    Q.ginzburgAssociatedGradedHomology k φ u v r c q ≅
      Q.ginzburgGeneratorPrefixHomology k φ u v r c q :=
  (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.up ℤ) q).mapIso
    (Q.ginzburgGeneratorPrefixGradedIso k φ u v r c).symm

theorem GinzburgRegular.associatedGradedHomology_succ_isZero {φ : Q.Potential k}
    (h : Q.GinzburgRegular k φ) (u v : Q.Vertex) (r c q : ℤ) (hq : q+1<r) :
    IsZero (Q.ginzburgAssociatedGradedHomology k φ u v r c (q+1)) :=
  (h.generatorPrefixHomology_succ_isZero Q k u v r c q hq).of_iso
    (Q.ginzburgAssociatedGradedPrefixHomologyIso k φ u v r c (q+1))

theorem GinzburgRegular.associatedGradedHomology_isZero {φ : Q.Potential k}
    (h : Q.GinzburgRegular k φ) (u v : Q.Vertex) (r c q : ℤ) (hq : q<r) :
    IsZero (Q.ginzburgAssociatedGradedHomology k φ u v r c q) := by
  obtain ⟨t,rfl⟩ : ∃ t : ℤ, q=t+1 := ⟨q-1,by omega⟩
  exact h.associatedGradedHomology_succ_isZero Q k u v r c t hq

end ASGinzburg.CutQuiver
