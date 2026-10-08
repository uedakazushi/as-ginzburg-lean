import ASGinzburg.FiniteCoproductHomColimits
import ASGinzburg.FiniteProjectiveBidual

namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
universe u₁ u₂ u₃ v₁ v₂ v₃
variable {C : Type u₁} [Category.{v₁} C]
  {D : Type u₂} [Category.{v₂} D] {J : Type u₃} [Category.{v₃} J]

theorem isIso_natTrans_app_retract_general {F G : C ⥤ D}
    (η : F ⟶ G) {X Y : C} (r : Retract X Y) [IsIso (η.app Y)] :
    IsIso (η.app X) := by
  refine ⟨⟨G.map r.i ≫ inv (η.app Y) ≫ F.map r.r,?_,?_⟩⟩
  · rw [← Category.assoc,← η.naturality r.i,Category.assoc,
      IsIso.hom_inv_id_assoc,← F.map_comp,r.retract,F.map_id]
  · rw [Category.assoc,Category.assoc,η.naturality r.r,
      ← Category.assoc (inv (η.app Y)),IsIso.inv_hom_id,Category.id_comp,
      ← G.map_comp,r.retract,G.map_id]

noncomputable def colimitPostNatTrans (K : J ⥤ C) [HasColimit K]
    [HasColimitsOfShape J D] :
    (Functor.whiskeringLeft J C D).obj K ⋙ colim ⟶ (evaluation C D).obj (colimit K) where
  app F := colimit.post K F
  naturality {F G} α := by
    apply colimit.hom_ext
    intro j
    dsimp
    simp only [ι_colimMap_assoc,colimit.ι_post,colimit.ι_post_assoc,
      Functor.whiskerLeft_app]
    exact (α.naturality (colimit.ι K j)).symm

noncomputable def preservesColimit_of_functor_retract (K : J ⥤ C) [HasColimit K]
    [HasColimitsOfShape J D] {F G : C ⥤ D} (r : Retract F G) [PreservesColimit K G] :
    PreservesColimit K F := by
  letI : IsIso ((colimitPostNatTrans K).app G) :=
    inferInstanceAs (IsIso (colimit.post K G))
  letI : IsIso (colimit.post K F) :=
    isIso_natTrans_app_retract_general (colimitPostNatTrans K) r
  exact preservesColimit_of_isIso_post F K

noncomputable def preservesColimitsOfShape_of_functor_retract
    [HasColimitsOfShape J C] [HasColimitsOfShape J D]
    {F G : C ⥤ D} (r : Retract F G) [PreservesColimitsOfShape J G] :
    PreservesColimitsOfShape J F where
  preservesColimit := preservesColimit_of_functor_retract _ r
end ASGinzburg

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v w w'
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

noncomputable def rightFiniteProjectiveHomPreservesColimits {P : A.RightModule}
    (hP : A.rightFiniteProjectiveProperty P) (J : Type w) [Category.{w'} J]
    [HasColimitsOfShape J A.RightModule] [HasColimitsOfShape J (ModuleCat.{v} k)] :
    PreservesColimitsOfShape J ((linearCoyoneda k A.RightModule).obj (op P)) := by
  obtain ⟨n,i,⟨r⟩⟩ := hP
  exact ASGinzburg.preservesColimitsOfShape_of_functor_retract
    (r.op.map (linearCoyoneda k A.RightModule))
end ASGinzburg.ZAlgebra
