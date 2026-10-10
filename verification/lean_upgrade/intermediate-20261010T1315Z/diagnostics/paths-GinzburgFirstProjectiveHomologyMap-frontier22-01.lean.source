import ASGinzburg.GinzburgGeneratorFiltrationRadical
import ASGinzburg.GinzburgAugmentationHeightHomology

/-! The first native projective map is induced by the genuine
inclusion of the original filtration into the augmentation and cut complexes. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def ginzburgOriginalMiddleInclusion (φ : Q.Potential k)
    (u v : Q.Vertex) (c : ℤ) :
    Q.ginzburgGeneratorFilteredComplex k φ u v 0 c ⟶
      Q.ginzburgGeneratorFilteredComplex k φ u v (-1) c := by
  simpa only [show (-1:ℤ)+1=0 by norm_num] using
    Q.ginzburgGeneratorFilteredInclusion k φ u v (-1) c

noncomputable def ginzburgMiddleBottomInclusion (φ : Q.Potential k)
    (u v : Q.Vertex) (c : ℤ) :
    Q.ginzburgGeneratorFilteredComplex k φ u v (-1) c ⟶
      Q.ginzburgGeneratorFilteredComplex k φ u v (-2) c := by
  simpa only [show (-2:ℤ)+1=-1 by norm_num] using
    Q.ginzburgGeneratorFilteredInclusion k φ u v (-2) c

theorem ginzburgGeneratorFilteredAugmentationInclusion_comp (φ : Q.Potential k)
    (u v : Q.Vertex) (c : ℤ) :
    Q.ginzburgOriginalMiddleInclusion k φ u v c ≫
      Q.ginzburgMiddleBottomInclusion k φ u v c ≫
        Q.ginzburgGeneratorFilteredAugmentationInclusion k φ u v (-2) c=
      Q.ginzburgGeneratorFilteredAugmentationInclusion k φ u v 0 c := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  rfl

theorem ginzburgGeneratorFiltrationRadicalMap_eq_homologyMap (φ : Q.Potential k)
    (u v : Q.Vertex) (c : ℤ) :
    Q.ginzburgGeneratorFiltrationRadicalMap k φ u v c=
      HomologicalComplex.homologyMap
        (Q.ginzburgGeneratorFilteredAugmentationInclusion k φ u v 0 c) 0 := by
  change HomologicalComplex.homologyMap
    (Q.ginzburgOriginalMiddleInclusion k φ u v c) 0 ≫
    HomologicalComplex.homologyMap
      (Q.ginzburgMiddleBottomInclusion k φ u v c) 0 ≫
    HomologicalComplex.homologyMap
      (Q.ginzburgGeneratorFilteredAugmentationInclusion k φ u v (-2) c) 0=_
  rw [←HomologicalComplex.homologyMap_comp_assoc,←HomologicalComplex.homologyMap_comp]
  rw [Category.assoc,Q.ginzburgGeneratorFilteredAugmentationInclusion_comp]

theorem ginzburgGeneratorFiltrationRadicalMap_cut (φ : Q.Potential k)
    (x v : Q.LiftVertex) (hx : Q.height x<Q.height v) :
    Q.ginzburgGeneratorFiltrationRadicalMap k φ x.1 v.1 (v.2-x.2) ≫
      (Q.ginzburgAugmentationHeightHomologyIso k φ x v hx 0).hom=
      HomologicalComplex.homologyMap
        (Q.ginzburgGeneratorFilteredAugmentationInclusion k φ x.1 v.1 0 (v.2-x.2) ≫
          Q.ginzburgAugmentationCochainInclusion k φ x.1 v.1 (v.2-x.2)) 0 := by
  rw [Q.ginzburgGeneratorFiltrationRadicalMap_eq_homologyMap]
  change HomologicalComplex.homologyMap _ 0 ≫
    HomologicalComplex.homologyMap _ 0=_
  exact (HomologicalComplex.homologyMap_comp _ _ 0).symm

end ASGinzburg.CutQuiver
