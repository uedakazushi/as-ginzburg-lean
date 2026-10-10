import Mathlib.CategoryTheory.Equivalence
import ASGinzburg.UnitizationComponentSums
import ASGinzburg.UnitizationComponentFunctors
/-! The total-space and component-range functors are inverse equivalences.
The counit is the actual sum of inclusions, is linear over the unitization,
and is bijective by the proved locally unital direct-sum decomposition. -/

namespace ASGinzburg.ZAlgebra
open CategoryTheory Opposite
open scoped ModuleCat.Algebra DirectSum
attribute [local instance 2000] ModuleCat.isModule
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)
theorem leftUnitizationComponentSum_action (M : ModuleCat.{v} A.totalUnitization)
    {i j : ℤ} (a : A.Hom i j) :
    (A.leftUnitizationComponentSum M).comp
      (A.leftModuleTotalAction (A.unitizationLeftComponentModule M) a) =
      (A.leftUnitizationComponentAction M a).comp (A.leftUnitizationComponentSum M) := by
  apply DFinsupp.lhom_ext
  intro l x
  change A.leftUnitizationComponentSpace M l at x
  change A.leftUnitizationComponentSum M
    (A.leftModuleTotalAction (A.unitizationLeftComponentModule M) a (DirectSum.lof k ℤ _ l x)) =
      A.leftUnitizationComponentAction M a
        (A.leftUnitizationComponentSum M (DirectSum.lof k ℤ _ l x))
  by_cases hli : l = i
  · subst l
    rw [A.leftModuleTotalAction_lof, A.leftUnitizationComponentSum_lof,
      A.leftUnitizationComponentSum_lof]
    rfl
  · rw [A.leftModuleTotalAction_lof_off _ a l hli, map_zero,
      A.leftUnitizationComponentSum_lof]
    have h := LinearMap.congr_fun
      (A.leftUnitizationComponentAction_comp_off M (A.id l) a hli) x.val
    change A.leftUnitizationComponentAction M a (A.leftUnitizationProjection M l x.val) = 0 at h
    rw [A.leftUnitizationProjection_range_fixed] at h
    exact h.symm

theorem rightUnitizationComponentSum_action (M : ModuleCat.{v} A.totalUnitizationᵐᵒᵖ)
    {i j : ℤ} (a : A.Hom i j) :
    (A.rightUnitizationComponentSum M).comp
      (A.rightModuleTotalAction (A.unitizationRightComponentModule M) a) =
      (A.rightUnitizationComponentAction M a).comp (A.rightUnitizationComponentSum M) := by
  apply DFinsupp.lhom_ext
  intro l x
  change A.rightUnitizationComponentSpace M l at x
  change A.rightUnitizationComponentSum M
    (A.rightModuleTotalAction (A.unitizationRightComponentModule M) a (DirectSum.lof k ℤ _ l x)) =
      A.rightUnitizationComponentAction M a
        (A.rightUnitizationComponentSum M (DirectSum.lof k ℤ _ l x))
  by_cases hlj : l = j
  · subst l
    rw [A.rightModuleTotalAction_lof, A.rightUnitizationComponentSum_lof,
      A.rightUnitizationComponentSum_lof]
    rfl
  · rw [A.rightModuleTotalAction_lof_off _ a l hlj, map_zero,
      A.rightUnitizationComponentSum_lof]
    have h := LinearMap.congr_fun
      (A.rightUnitizationComponentAction_comp_off M a (A.id l) (Ne.symm hlj)) x.val
    change A.rightUnitizationComponentAction M a (A.rightUnitizationProjection M l x.val) = 0 at h
    rw [A.rightUnitizationProjection_range_fixed] at h
    exact h.symm
theorem leftUnitizationComponentSum_representation (M : ModuleCat.{v} A.totalUnitization)
    (a : A.totalAlgebra)
    (x : A.leftModuleTotalSpace (A.unitizationLeftComponentModule M)) :
    A.leftUnitizationComponentSum M (A.leftTotalRepresentation (A.unitizationLeftComponentModule M) a x) =
      (a : A.totalUnitization) • A.leftUnitizationComponentSum M x := by
  obtain ⟨a,rfl⟩ := A.totalAlgebraEquiv.surjective a
  induction a using DFinsupp.induction with
  | h0 =>
    change A.leftUnitizationComponentSum M
      (A.leftTotalRepresentation (A.unitizationLeftComponentModule M) (A.totalAlgebraEquiv 0) x) =
      Unitization.inrHom k A.totalAlgebra (A.totalAlgebraEquiv 0) • A.leftUnitizationComponentSum M x
    rw [map_zero, map_zero, LinearMap.zero_apply, map_zero, map_zero, zero_smul]
  | ha p b a _ _ ih =>
    rw [A.totalAlgebraEquiv.map_add,
      (A.leftTotalRepresentation (A.unitizationLeftComponentModule M)).map_add,
      LinearMap.add_apply, map_add]
    change _ = Unitization.inrHom k A.totalAlgebra
      (A.totalAlgebraEquiv (DFinsupp.single p b) + A.totalAlgebraEquiv a) • _
    rw [map_add, add_smul, ih]
    congr 1
    change A.leftUnitizationComponentSum M
      (A.leftTotalRepresentation (A.unitizationLeftComponentModule M) (A.totalAlgebraComponent b) x) = _
    rw [A.leftTotalRepresentation_component]
    exact LinearMap.congr_fun (A.leftUnitizationComponentSum_action M b) x

theorem rightUnitizationComponentSum_representation (M : ModuleCat.{v} A.totalUnitizationᵐᵒᵖ)
    (a : A.totalAlgebra)
    (x : A.rightModuleTotalSpace (A.unitizationRightComponentModule M)) :
    A.rightUnitizationComponentSum M
      ((A.rightTotalRepresentation (A.unitizationRightComponentModule M) a).unop x) =
      MulOpposite.op (a : A.totalUnitization) • A.rightUnitizationComponentSum M x := by
  obtain ⟨a,rfl⟩ := A.totalAlgebraEquiv.surjective a
  induction a using DFinsupp.induction with
  | h0 =>
    change A.rightUnitizationComponentSum M
      ((A.rightTotalRepresentation (A.unitizationRightComponentModule M) (A.totalAlgebraEquiv 0)).unop x) =
      MulOpposite.op (Unitization.inrHom k A.totalAlgebra (A.totalAlgebraEquiv 0)) •
        A.rightUnitizationComponentSum M x
    rw [map_zero, map_zero, MulOpposite.unop_zero, LinearMap.zero_apply, map_zero,
      map_zero, MulOpposite.op_zero, zero_smul]
  | ha p b a _ _ ih =>
    rw [A.totalAlgebraEquiv.map_add,
      (A.rightTotalRepresentation (A.unitizationRightComponentModule M)).map_add,
      MulOpposite.unop_add, LinearMap.add_apply, map_add]
    change _ = MulOpposite.op (Unitization.inrHom k A.totalAlgebra
      (A.totalAlgebraEquiv (DFinsupp.single p b) + A.totalAlgebraEquiv a)) • _
    rw [map_add, MulOpposite.op_add, add_smul, ih]
    congr 1
    change A.rightUnitizationComponentSum M
      ((A.rightTotalRepresentation (A.unitizationRightComponentModule M)
        (A.totalAlgebraComponent b)).unop x) = _
    rw [A.rightTotalRepresentation_component]
    exact LinearMap.congr_fun (A.rightUnitizationComponentSum_action M b) x

theorem leftUnitization_smul_decomposition (M : ModuleCat.{v} A.totalUnitization)
    (r : A.totalUnitization) (x : M) :
    r • x = r.fst • x + (r.snd : A.totalUnitization) • x := by
  conv_lhs => rw [← Unitization.inl_fst_add_inr_snd_eq r]
  rw [add_smul]
  rfl

theorem rightUnitization_smul_decomposition (M : ModuleCat.{v} A.totalUnitizationᵐᵒᵖ)
    (r : A.totalUnitizationᵐᵒᵖ) (x : M) :
    r • x = r.unop.fst • x + MulOpposite.op (r.unop.snd : A.totalUnitization) • x := by
  conv_lhs => rw [← MulOpposite.op_unop r, ← Unitization.inl_fst_add_inr_snd_eq r.unop]
  rw [MulOpposite.op_add, add_smul]
  rfl

noncomputable def leftUnitizationComponentSumModuleMap (M : ModuleCat.{v} A.totalUnitization) :
    A.leftTotalModule (A.unitizationLeftComponentModule M) ⟶ M := by
  letI := A.leftTotalUnitizationModule (A.unitizationLeftComponentModule M)
  exact ModuleCat.ofHom
    { toFun := A.leftUnitizationComponentSum M
      map_add' := (A.leftUnitizationComponentSum M).map_add
      map_smul' := by
        intro r x
        change A.leftUnitizationComponentSum M
          (r.fst • x + A.leftTotalRepresentation (A.unitizationLeftComponentModule M) r.snd x) =
            r • A.leftUnitizationComponentSum M x
        rw [map_add, map_smul, A.leftUnitizationComponentSum_representation]
        exact (A.leftUnitization_smul_decomposition M r (A.leftUnitizationComponentSum M x)).symm }

noncomputable def rightUnitizationComponentSumModuleMap (M : ModuleCat.{v} A.totalUnitizationᵐᵒᵖ) :
    A.rightTotalModule (A.unitizationRightComponentModule M) ⟶ M := by
  letI := A.rightTotalUnitizationModule (A.unitizationRightComponentModule M)
  exact ModuleCat.ofHom
    { toFun := A.rightUnitizationComponentSum M
      map_add' := (A.rightUnitizationComponentSum M).map_add
      map_smul' := by
        intro r x
        change A.rightUnitizationComponentSum M
          (r.unop.fst • x +
            (A.rightTotalRepresentation (A.unitizationRightComponentModule M) r.unop.snd).unop x) =
              r • A.rightUnitizationComponentSum M x
        rw [map_add, map_smul, A.rightUnitizationComponentSum_representation]
        exact (A.rightUnitization_smul_decomposition M r (A.rightUnitizationComponentSum M x)).symm }

noncomputable def leftLocallyUnitalComponentSumIso (M : A.LeftLocallyUnitalModule) :
    A.leftTotalLocallyUnitalModule (A.unitizationLeftComponentModule M.obj) ≅ M := by
  let e := LinearEquiv.ofBijective (A.leftUnitizationComponentSumModuleMap M.obj).hom
    ⟨A.leftUnitizationComponentSum_injective M.obj, A.leftUnitizationComponentSum_surjective M⟩
  exact A.leftLocallyUnitalProperty.isoMk e.toModuleIso

noncomputable def rightLocallyUnitalComponentSumIso (M : A.RightLocallyUnitalModule) :
    A.rightTotalLocallyUnitalModule (A.unitizationRightComponentModule M.obj) ≅ M := by
  let e := LinearEquiv.ofBijective (A.rightUnitizationComponentSumModuleMap M.obj).hom
    ⟨A.rightUnitizationComponentSum_injective M.obj, A.rightUnitizationComponentSum_surjective M⟩
  exact A.rightLocallyUnitalProperty.isoMk e.toModuleIso

theorem leftUnitizationComponentSumModuleMap_natural
    {M N : ModuleCat.{v} A.totalUnitization} (f : M ⟶ N) :
    A.leftTotalModuleMap (A.unitizationLeftComponentModuleMap f) ≫
      A.leftUnitizationComponentSumModuleMap N =
      A.leftUnitizationComponentSumModuleMap M ≫ f := by
  have h : (A.leftUnitizationComponentSum N).comp
      (A.leftTotalLinearMap (A.unitizationLeftComponentModuleMap f)) =
      (f.hom.restrictScalars k).comp (A.leftUnitizationComponentSum M) := by
    apply DFinsupp.lhom_ext
    intro i x
    change A.leftUnitizationComponentSpace M i at x
    change A.leftUnitizationComponentSum N
      (A.leftTotalLinearMap (A.unitizationLeftComponentModuleMap f)
        (DirectSum.lof k ℤ _ i x)) =
      f.hom (A.leftUnitizationComponentSum M (DirectSum.lof k ℤ _ i x))
    rw [A.leftTotalLinearMap_lof, A.leftUnitizationComponentSum_lof,
      A.leftUnitizationComponentSum_lof]
    rfl
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun h x

theorem rightUnitizationComponentSumModuleMap_natural
    {M N : ModuleCat.{v} A.totalUnitizationᵐᵒᵖ} (f : M ⟶ N) :
    A.rightTotalModuleMap (A.unitizationRightComponentModuleMap f) ≫
      A.rightUnitizationComponentSumModuleMap N =
      A.rightUnitizationComponentSumModuleMap M ≫ f := by
  have h : (A.rightUnitizationComponentSum N).comp
      (A.rightTotalLinearMap (A.unitizationRightComponentModuleMap f)) =
      (f.hom.restrictScalars k).comp (A.rightUnitizationComponentSum M) := by
    apply DFinsupp.lhom_ext
    intro i x
    change A.rightUnitizationComponentSpace M i at x
    change A.rightUnitizationComponentSum N
      (A.rightTotalLinearMap (A.unitizationRightComponentModuleMap f)
        (DirectSum.lof k ℤ _ i x)) =
      f.hom (A.rightUnitizationComponentSum M (DirectSum.lof k ℤ _ i x))
    rw [A.rightTotalLinearMap_lof, A.rightUnitizationComponentSum_lof,
      A.rightUnitizationComponentSum_lof]
    rfl
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun h x

noncomputable def leftLocallyUnitalCounitIso :
    A.leftLocallyUnitalComponentFunctor ⋙ A.leftTotalLocallyUnitalFunctor ≅
      𝟭 A.LeftLocallyUnitalModule :=
  NatIso.ofComponents (A.leftLocallyUnitalComponentSumIso)
    (fun f => ObjectProperty.hom_ext _ (A.leftUnitizationComponentSumModuleMap_natural f.hom))

noncomputable def rightLocallyUnitalCounitIso :
    A.rightLocallyUnitalComponentFunctor ⋙ A.rightTotalLocallyUnitalFunctor ≅
      𝟭 A.RightLocallyUnitalModule :=
  NatIso.ofComponents (A.rightLocallyUnitalComponentSumIso)
    (fun f => ObjectProperty.hom_ext _ (A.rightUnitizationComponentSumModuleMap_natural f.hom))

noncomputable def leftLocallyUnitalUnitIso :
    𝟭 A.LeftModule ≅ A.leftTotalLocallyUnitalFunctor ⋙ A.leftLocallyUnitalComponentFunctor :=
  Functor.fullyFaithfulCancelRight A.leftTotalLocallyUnitalFunctor
    (Functor.leftUnitor A.leftTotalLocallyUnitalFunctor ≪≫
      (Functor.associator A.leftTotalLocallyUnitalFunctor A.leftLocallyUnitalComponentFunctor
        A.leftTotalLocallyUnitalFunctor ≪≫
          Functor.isoWhiskerLeft A.leftTotalLocallyUnitalFunctor A.leftLocallyUnitalCounitIso ≪≫
            Functor.rightUnitor A.leftTotalLocallyUnitalFunctor).symm)

noncomputable def rightLocallyUnitalUnitIso :
    𝟭 A.RightModule ≅ A.rightTotalLocallyUnitalFunctor ⋙ A.rightLocallyUnitalComponentFunctor :=
  Functor.fullyFaithfulCancelRight A.rightTotalLocallyUnitalFunctor
    (Functor.leftUnitor A.rightTotalLocallyUnitalFunctor ≪≫
      (Functor.associator A.rightTotalLocallyUnitalFunctor A.rightLocallyUnitalComponentFunctor
        A.rightTotalLocallyUnitalFunctor ≪≫
          Functor.isoWhiskerLeft A.rightTotalLocallyUnitalFunctor A.rightLocallyUnitalCounitIso ≪≫
            Functor.rightUnitor A.rightTotalLocallyUnitalFunctor).symm)

noncomputable def leftLocallyUnitalEquivalence : A.LeftModule ≌ A.LeftLocallyUnitalModule :=
  CategoryTheory.Equivalence.mk A.leftTotalLocallyUnitalFunctor A.leftLocallyUnitalComponentFunctor
    A.leftLocallyUnitalUnitIso A.leftLocallyUnitalCounitIso

noncomputable def rightLocallyUnitalEquivalence : A.RightModule ≌ A.RightLocallyUnitalModule :=
  CategoryTheory.Equivalence.mk A.rightTotalLocallyUnitalFunctor A.rightLocallyUnitalComponentFunctor
    A.rightLocallyUnitalUnitIso A.rightLocallyUnitalCounitIso

instance leftTotalLocallyUnitalFunctorIsEquivalence : A.leftTotalLocallyUnitalFunctor.IsEquivalence :=
  A.leftLocallyUnitalEquivalence.isEquivalence_functor

instance rightTotalLocallyUnitalFunctorIsEquivalence : A.rightTotalLocallyUnitalFunctor.IsEquivalence :=
  A.rightLocallyUnitalEquivalence.isEquivalence_functor

end ASGinzburg.ZAlgebra
