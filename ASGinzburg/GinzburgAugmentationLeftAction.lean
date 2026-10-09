import ASGinzburg.GinzburgCutLeftAction
import ASGinzburg.GinzburgFilteredLeftAction
import ASGinzburg.GinzburgGeneratorFilteredAugmentation

/-! Degree-zero paths act on the genuine augmentation ideal complex.
The inclusion into the cut complex and every filtration inclusion are
natural actual cochain maps. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgAugmentationAtDegree_leftComp {x y v : Q.LiftVertex} (q : ℤ)
    (f : Q.ginzburgCutCohomologicalComponent k x.1 y.1 0 (y.2-x.2))
    (g : Q.ginzburgAugmentationAtDegree k y.1 v.1 q (v.2-y.2)) :
    Q.ginzburgPathComp k g.val f.val ∈
      Q.ginzburgAugmentationAtDegree k x.1 v.1 q (v.2-x.2) := by
  have hg : g.val ∈ Q.ginzburgGeneratorFiltrationAtDegree k y.1 v.1 (-2) q (v.2-y.2) := by
    rw [Q.ginzburgGeneratorFiltrationAtDegree_negTwo]
    exact g.property
  have he := Q.ginzburgGeneratorFiltrationAtDegree_leftComp k (-2) q f ⟨g.val,hg⟩
  rwa [Q.ginzburgGeneratorFiltrationAtDegree_negTwo] at he

noncomputable def ginzburgAugmentationLeftTerm {x y v : Q.LiftVertex} (q : ℤ)
    (f : Q.ginzburgCutCohomologicalComponent k x.1 y.1 0 (y.2-x.2)) :
    Q.ginzburgAugmentationAtDegree k y.1 v.1 q (v.2-y.2) →ₗ[k]
      Q.ginzburgAugmentationAtDegree k x.1 v.1 q (v.2-x.2) :=
  (((Q.ginzburgPathComp k).flip f.val).comp
    (Q.ginzburgAugmentationAtDegree k y.1 v.1 q (v.2-y.2)).subtype).codRestrict _
      (fun g => Q.ginzburgAugmentationAtDegree_leftComp k q f g)

theorem ginzburgAugmentationLeftTerm_differential (φ : Q.Potential k)
    {x y v : Q.LiftVertex} (q : ℤ)
    (f : Q.ginzburgCutCohomologicalComponent k x.1 y.1 0 (y.2-x.2)) :
    (Q.ginzburgAugmentationGradedDifferential k φ x.1 v.1 q (v.2-x.2)).comp
        (Q.ginzburgAugmentationLeftTerm k q f)=
      (Q.ginzburgAugmentationLeftTerm k (q+1) f).comp
        (Q.ginzburgAugmentationGradedDifferential k φ y.1 v.1 q (v.2-y.2)) := by
  apply LinearMap.ext
  intro g
  apply Subtype.ext
  change Q.ginzburgDifferential k φ x.1 v.1 (Q.ginzburgPathComp k g.val f.val)=
    Q.ginzburgPathComp k (Q.ginzburgDifferential k φ y.1 v.1 g.val) f.val
  rw [Q.ginzburgDifferential_comp,Q.ginzburgDifferential_degreeZero k φ f.property.1]
  simp

noncomputable def ginzburgAugmentationLeftCochainMap (φ : Q.Potential k)
    {x y v : Q.LiftVertex}
    (f : Q.ginzburgCutCohomologicalComponent k x.1 y.1 0 (y.2-x.2)) :
    Q.ginzburgAugmentationCochainComplex k φ y.1 v.1 (v.2-y.2) ⟶
      Q.ginzburgAugmentationCochainComplex k φ x.1 v.1 (v.2-x.2) :=
  CochainComplex.ofHom _ _ _ _ _ _
    (fun q => ModuleCat.ofHom (Q.ginzburgAugmentationLeftTerm k q f))
    (fun q => by
      apply ModuleCat.hom_ext
      exact Q.ginzburgAugmentationLeftTerm_differential k φ q f)

theorem ginzburgAugmentationLeftCochainMap_inclusion (φ : Q.Potential k)
    {x y v : Q.LiftVertex}
    (f : Q.ginzburgCutCohomologicalComponent k x.1 y.1 0 (y.2-x.2)) :
    Q.ginzburgAugmentationLeftCochainMap k φ f ≫
        Q.ginzburgAugmentationCochainInclusion k φ x.1 v.1 (v.2-x.2)=
      Q.ginzburgAugmentationCochainInclusion k φ y.1 v.1 (v.2-y.2) ≫
        Q.ginzburgCutLeftCochainMap k φ f := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro g
  apply Subtype.ext
  rfl

theorem ginzburgFilteredAugmentationInclusion_left_naturality (φ : Q.Potential k)
    {x y v : Q.LiftVertex} (r : ℤ)
    (f : Q.ginzburgCutCohomologicalComponent k x.1 y.1 0 (y.2-x.2)) :
    Q.ginzburgFilteredLeftCochainMap k φ r f ≫
        Q.ginzburgGeneratorFilteredAugmentationInclusion k φ x.1 v.1 r (v.2-x.2)=
      Q.ginzburgGeneratorFilteredAugmentationInclusion k φ y.1 v.1 r (v.2-y.2) ≫
        Q.ginzburgAugmentationLeftCochainMap k φ f := by
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro g
  apply Subtype.ext
  rfl

noncomputable def ginzburgAugmentationLeftHomology (φ : Q.Potential k)
    {x y v : Q.LiftVertex} (q : ℤ)
    (f : Q.ginzburgCutCohomologicalComponent k x.1 y.1 0 (y.2-x.2)) :
    Q.ginzburgAugmentationHomology k φ y.1 v.1 (v.2-y.2) q ⟶
      Q.ginzburgAugmentationHomology k φ x.1 v.1 (v.2-x.2) q :=
  HomologicalComplex.homologyMap (Q.ginzburgAugmentationLeftCochainMap k φ f) q

end ASGinzburg.CutQuiver
