import ASGinzburg.GinzburgGeneratorFiltrationHomologySequence
import ASGinzburg.GinzburgAugmentationRegularity

/-! The lowest genuine filtered subcomplex is the actual augmentation
complex, so its negative homology vanishes under Ginzburg regularity. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory CategoryTheory.Limits
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgGeneratorFiltrationAtDegree_le_augmentation (u v : Q.Vertex) (r q c : ℤ) :
    Q.ginzburgGeneratorFiltrationAtDegree k u v r q c ≤
      Q.ginzburgAugmentationAtDegree k u v q c := by
  apply Finsupp.supported_mono
  intro p hp
  exact ⟨Q.ginzburgGeneratorFiltrationPaths_nonempty hp.1,hp.2⟩

noncomputable def ginzburgGeneratorFilteredAugmentationInclusion (φ : Q.Potential k)
    (u v : Q.Vertex) (r c : ℤ) :
    Q.ginzburgGeneratorFilteredComplex k φ u v r c ⟶
      Q.ginzburgAugmentationCochainComplex k φ u v c :=
  CochainComplex.ofHom _ _ _ _ _ _
    (fun q => ModuleCat.ofHom
      (Submodule.inclusion (Q.ginzburgGeneratorFiltrationAtDegree_le_augmentation k u v r q c)))
    (fun _q => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      apply Subtype.ext
      rfl)

instance ginzburgGeneratorFilteredAugmentationInclusion_negTwo_f_isIso (φ : Q.Potential k)
    (u v : Q.Vertex) (c q : ℤ) :
    IsIso ((Q.ginzburgGeneratorFilteredAugmentationInclusion k φ u v (-2) c).f q) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  refine ⟨Submodule.inclusion_injective
    (Q.ginzburgGeneratorFiltrationAtDegree_le_augmentation k u v (-2) q c),?_⟩
  intro f
  refine ⟨⟨f.val,?_⟩,Subtype.ext rfl⟩
  rw [Q.ginzburgGeneratorFiltrationAtDegree_negTwo]
  exact f.property

instance ginzburgGeneratorFilteredAugmentationInclusion_negTwo_isIso (φ : Q.Potential k)
    (u v : Q.Vertex) (c : ℤ) :
    IsIso (Q.ginzburgGeneratorFilteredAugmentationInclusion k φ u v (-2) c) :=
  HomologicalComplex.Hom.isIso_of_components _

noncomputable def ginzburgGeneratorFilteredNegTwoIso (φ : Q.Potential k)
    (u v : Q.Vertex) (c : ℤ) :
    Q.ginzburgGeneratorFilteredComplex k φ u v (-2) c ≅
      Q.ginzburgAugmentationCochainComplex k φ u v c :=
  asIso (Q.ginzburgGeneratorFilteredAugmentationInclusion k φ u v (-2) c)

noncomputable def ginzburgGeneratorFilteredNegTwoHomologyIso (φ : Q.Potential k)
    (u v : Q.Vertex) (c q : ℤ) :
    Q.ginzburgGeneratorFilteredHomology k φ u v (-2) c q ≅
      Q.ginzburgAugmentationHomology k φ u v c q :=
  (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.up ℤ) q).mapIso
    (Q.ginzburgGeneratorFilteredNegTwoIso k φ u v c)

theorem GinzburgRegular.generatorFilteredNegTwoHomology_isZero {φ : Q.Potential k}
    (h : Q.GinzburgRegular k φ) (u v : Q.Vertex) (c q : ℤ) (hq : q<0) :
    IsZero (Q.ginzburgGeneratorFilteredHomology k φ u v (-2) c q) :=
  (h.augmentationHomology_isZero Q k u v c q hq).of_iso
    (Q.ginzburgGeneratorFilteredNegTwoHomologyIso k φ u v c q)

end ASGinzburg.CutQuiver
