import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Homology.QuasiIso

/-! The canonical augmentation to actual homology at a degree with zero
outgoing differential, and its genuine quasi-isomorphism criterion. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
universe u v w
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type w} [DecidableEq ι] {c : ComplexShape ι}
variable (K : HomologicalComplex C c) [∀ i, K.HasHomology i] (j : ι) (hg : (K.sc j).g=0)

noncomputable def homologyAugmentationProjection : K.X j ⟶ K.homology j :=
  ((K.sc j).cyclesIsoX₂ hg).inv ≫ K.homologyπ j

omit [DecidableEq ι] in
theorem d_homologyAugmentationProjection (i : ι) :
    K.d i j ≫ homologyAugmentationProjection K j hg=0 := by
  rw [←K.toCycles_i i j]
  change (K.toCycles i j ≫ (K.sc j).iCycles) ≫
    ((K.sc j).cyclesIsoX₂ hg).inv ≫ (K.sc j).homologyπ=0
  rw [←Category.assoc,Category.assoc (K.toCycles i j),
    (K.sc j).cyclesIsoX₂_hom_inv_id]
  change (K.toCycles i j ≫ (𝟙 (K.cycles j))) ≫ K.homologyπ j=0
  rw [Category.comp_id]
  exact K.toCycles_comp_homologyπ i j

noncomputable def homologyAugmentation : K ⟶
    (HomologicalComplex.single C c j).obj (K.homology j) :=
  HomologicalComplex.mkHomToSingle (homologyAugmentationProjection K j hg)
    (fun i _hi => d_homologyAugmentationProjection K j hg i)

theorem homologyAugmentation_map_self :
    HomologicalComplex.homologyMap (homologyAugmentation K j hg) j ≫
      (HomologicalComplex.singleObjHomologySelfIso c j (K.homology j)).hom=𝟙 _ := by
  rw [←cancel_epi (K.homologyπ j)]
  rw [HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom,
    HomologicalComplex.singleObjCyclesSelfIso_hom,
    ←Category.assoc,HomologicalComplex.cyclesMap_i,Category.assoc,
    homologyAugmentation,HomologicalComplex.mkHomToSingle_f]
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]
  change (K.sc j).iCycles ≫ ((K.sc j).cyclesIsoX₂ hg).inv ≫ (K.sc j).homologyπ=
    (K.sc j).homologyπ
  rw [←Category.assoc,(K.sc j).cyclesIsoX₂_hom_inv_id,Category.id_comp]

instance homologyAugmentation_quasiIsoAt_self :
    QuasiIsoAt (homologyAugmentation K j hg) j := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have h : HomologicalComplex.homologyMap (homologyAugmentation K j hg) j=
      (HomologicalComplex.singleObjHomologySelfIso c j (K.homology j)).inv := by
    rw [←cancel_mono (HomologicalComplex.singleObjHomologySelfIso c j (K.homology j)).hom,
      homologyAugmentation_map_self,Iso.inv_hom_id]
  rw [h]
  infer_instance

theorem homologyAugmentation_quasiIso_iff :
    QuasiIso (homologyAugmentation K j hg) ↔
      ∀ i, i≠j → IsZero (K.homology i) := by
  rw [quasiIso_iff]
  constructor
  · intro h i hi
    have hzero := HomologicalComplex.isZero_single_obj_homology c j (K.homology j) i hi
    haveI := (quasiIsoAt_iff_isIso_homologyMap _ i).mp (h i)
    exact hzero.of_iso (asIso (HomologicalComplex.homologyMap (homologyAugmentation K j hg) i))
  · intro h i
    by_cases hi : i=j
    · subst i; infer_instance
    · rw [quasiIsoAt_iff_isIso_homologyMap]
      have hzero := HomologicalComplex.isZero_single_obj_homology c j (K.homology j) i hi
      exact ⟨⟨0,(h i hi).eq_of_src _ _,hzero.eq_of_src _ _⟩⟩

end ASGinzburg
