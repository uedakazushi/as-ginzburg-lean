import ASGinzburg.GinzburgAugmentationHeight

/-! The actual augmentation inclusion is an isomorphism at positive
height difference; at other heights the entire augmentation complex is zero. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory CategoryTheory.Limits
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgAugmentationCochainInclusion_f_isIso_of_height_lt (φ : Q.Potential k)
    (x y : Q.LiftVertex) (hxy : Q.height x<Q.height y) (q : ℤ) :
    IsIso ((Q.ginzburgAugmentationCochainInclusion k φ x.1 y.1 (y.2-x.2)).f q) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  refine ⟨?_,?_⟩
  · intro f g h
    exact Subtype.ext (congrArg (fun z :
      Q.ginzburgCutCohomologicalComponent k x.1 y.1 q (y.2-x.2) => z.val) h)
  · intro f
    refine ⟨⟨f.val,?_⟩,Subtype.ext rfl⟩
    rw [Q.ginzburgAugmentationAtDegree_eq_cut_of_height_lt k x y q hxy]
    exact f.property

theorem ginzburgAugmentationCochainInclusion_isIso_of_height_lt (φ : Q.Potential k)
    (x y : Q.LiftVertex) (hxy : Q.height x<Q.height y) :
    IsIso (Q.ginzburgAugmentationCochainInclusion k φ x.1 y.1 (y.2-x.2)) := by
  letI (q : ℤ) : IsIso ((Q.ginzburgAugmentationCochainInclusion k φ x.1 y.1 (y.2-x.2)).f q) :=
    Q.ginzburgAugmentationCochainInclusion_f_isIso_of_height_lt k φ x y hxy q
  exact HomologicalComplex.Hom.isIso_of_components _

noncomputable def ginzburgAugmentationHeightComplexIso (φ : Q.Potential k)
    (x y : Q.LiftVertex) (hxy : Q.height x<Q.height y) :
    Q.ginzburgAugmentationCochainComplex k φ x.1 y.1 (y.2-x.2) ≅
      Q.ginzburgCutCochainComplex k φ x.1 y.1 (y.2-x.2) := by
  letI := Q.ginzburgAugmentationCochainInclusion_isIso_of_height_lt k φ x y hxy
  exact asIso (Q.ginzburgAugmentationCochainInclusion k φ x.1 y.1 (y.2-x.2))

noncomputable def ginzburgAugmentationHeightHomologyIso (φ : Q.Potential k)
    (x y : Q.LiftVertex) (hxy : Q.height x<Q.height y) (q : ℤ) :
    Q.ginzburgAugmentationHomology k φ x.1 y.1 (y.2-x.2) q ≅
      Q.ginzburgCutHomology k φ x.1 y.1 (y.2-x.2) q :=
  (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.up ℤ) q).mapIso
    (Q.ginzburgAugmentationHeightComplexIso k φ x y hxy)

theorem ginzburgAugmentationTerm_isZero_of_not_height_lt (x y : Q.LiftVertex)
    (q : ℤ) (hxy : ¬Q.height x<Q.height y) :
    IsZero (ModuleCat.of k (Q.ginzburgAugmentationAtDegree k x.1 y.1 q (y.2-x.2))) := by
  rw [Q.ginzburgAugmentationAtDegree_eq_bot_of_not_height_lt k x y q hxy]
  exact ModuleCat.isZero_of_subsingleton _

theorem ginzburgAugmentationHomology_isZero_of_not_height_lt (φ : Q.Potential k)
    (x y : Q.LiftVertex) (q : ℤ) (hxy : ¬Q.height x<Q.height y) :
    IsZero (Q.ginzburgAugmentationHomology k φ x.1 y.1 (y.2-x.2) q) :=
  ((Q.ginzburgAugmentationCochainComplex k φ x.1 y.1 (y.2-x.2)).sc q).isZero_homology_of_isZero_X₂
    (Q.ginzburgAugmentationTerm_isZero_of_not_height_lt k x y q hxy)

end ASGinzburg.CutQuiver
