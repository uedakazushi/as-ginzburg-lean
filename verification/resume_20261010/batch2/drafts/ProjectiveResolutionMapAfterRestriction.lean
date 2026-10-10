import work.ASGinzburgDraft.ProjectiveResolutionMapOfProjectiveTarget

/-! An exact projective-preserving restriction followed by any
additive functor maps a resolution augmentation to a quasi-isomorphism
when the restricted target is projective. -/
namespace ASGinzburg
open CategoryTheory
universe u v u' v' u'' v''
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]
variable {E : Type u''} [Category.{v''} E] [Abelian E]

theorem projectiveResolution_map_augmentation_after_restriction
    (L : C ⥤ D) [L.Additive] [L.PreservesProjectiveObjects] [L.PreservesHomology]
    (G : D ⥤ E) [G.Additive] {X : C} [Projective (L.obj X)]
    (Q : ProjectiveResolution X) :
    QuasiIso (((L ⋙ G).mapHomologicalComplex (ComplexShape.down ℕ)).map Q.π) := by
  let q := L.mapProjectiveResolution Q
  have h := projectiveResolution_map_augmentation_quasiIso G q
  change QuasiIso ((G.mapHomologicalComplex (ComplexShape.down ℕ)).map
    ((L.mapHomologicalComplex (ComplexShape.down ℕ)).map Q.π ≫
      (HomologicalComplex.singleMapHomologicalComplex L (ComplexShape.down ℕ) 0).hom.app X)) at h
  rw [Functor.map_comp] at h
  letI := h
  change QuasiIso ((G.mapHomologicalComplex (ComplexShape.down ℕ)).map
    ((L.mapHomologicalComplex (ComplexShape.down ℕ)).map Q.π))
  exact quasiIso_of_comp_right _
    ((G.mapHomologicalComplex (ComplexShape.down ℕ)).map
      ((HomologicalComplex.singleMapHomologicalComplex L (ComplexShape.down ℕ) 0).hom.app X))

end ASGinzburg
