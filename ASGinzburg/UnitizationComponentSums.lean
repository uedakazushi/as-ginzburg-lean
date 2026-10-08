import ASGinzburg.UnitizationComponentModules

/-! Component recovery on morphisms and finite direct-sum reconstruction.
The bijectivity of the sum map uses the concrete locally unital condition.
Compatibility with the full unitization action is proved separately. -/

namespace ASGinzburg.ZAlgebra
open CategoryTheory Opposite
open scoped ModuleCat.Algebra DirectSum
attribute [local instance 2000] ModuleCat.isModule
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

noncomputable def leftUnitizationComponentSum (M : ModuleCat.{v} A.totalUnitization) :
    A.leftModuleTotalSpace (A.unitizationLeftComponentModule M) →ₗ[k] M :=
  DFinsupp.lsum k (fun i => (A.leftUnitizationComponentSpace M i).subtype)

noncomputable def rightUnitizationComponentSum (M : ModuleCat.{v} A.totalUnitizationᵐᵒᵖ) :
    A.rightModuleTotalSpace (A.unitizationRightComponentModule M) →ₗ[k] M :=
  DFinsupp.lsum k (fun i => (A.rightUnitizationComponentSpace M i).subtype)

@[simp] theorem leftUnitizationComponentSum_lof (M : ModuleCat.{v} A.totalUnitization) (i : ℤ)
    (x : A.leftUnitizationComponentSpace M i) :
    A.leftUnitizationComponentSum M (DirectSum.lof k ℤ _ i x) = x.val :=
  DFinsupp.lsum_single k (fun l => (A.leftUnitizationComponentSpace M l).subtype) i x

@[simp] theorem rightUnitizationComponentSum_lof (M : ModuleCat.{v} A.totalUnitizationᵐᵒᵖ) (i : ℤ)
    (x : A.rightUnitizationComponentSpace M i) :
    A.rightUnitizationComponentSum M (DirectSum.lof k ℤ _ i x) = x.val :=
  DFinsupp.lsum_single k (fun l => (A.rightUnitizationComponentSpace M l).subtype) i x

theorem leftUnitizationProjection_range_off (M : ModuleCat.{v} A.totalUnitization) (i j : ℤ)
    (hji : j ≠ i) (x : A.leftUnitizationComponentSpace M j) :
    A.leftUnitizationProjection M i x = 0 := by
  obtain ⟨y,hy⟩ := x.property
  rw [← hy]
  exact LinearMap.congr_fun (A.leftUnitizationProjection_orthogonal M j i hji) y

theorem rightUnitizationProjection_range_off (M : ModuleCat.{v} A.totalUnitizationᵐᵒᵖ) (i j : ℤ)
    (hji : j ≠ i) (x : A.rightUnitizationComponentSpace M j) :
    A.rightUnitizationProjection M i x = 0 := by
  obtain ⟨y,hy⟩ := x.property
  rw [← hy]
  exact LinearMap.congr_fun (A.rightUnitizationProjection_orthogonal M j i hji) y

theorem leftUnitizationProjection_componentSum (M : ModuleCat.{v} A.totalUnitization) (i : ℤ)
    (x : A.leftModuleTotalSpace (A.unitizationLeftComponentModule M)) :
    A.leftUnitizationProjection M i (A.leftUnitizationComponentSum M x) = (x i).val := by
  have h : (A.leftUnitizationProjection M i).comp (A.leftUnitizationComponentSum M) =
      (A.leftUnitizationComponentSpace M i).subtype.comp (DirectSum.component k ℤ _ i) := by
    apply DFinsupp.lhom_ext
    intro j y
    change A.leftUnitizationComponentSpace M j at y
    change A.leftUnitizationProjection M i
      (A.leftUnitizationComponentSum M (DirectSum.lof k ℤ _ j y)) =
        (DirectSum.component k ℤ (fun l => A.leftUnitizationComponentSpace M l) i
          (DirectSum.lof k ℤ (fun l => A.leftUnitizationComponentSpace M l) j y)).val
    rw [A.leftUnitizationComponentSum_lof, DirectSum.component.of]
    by_cases hji : j = i
    · subst j
      simp only [dite_true]
      exact A.leftUnitizationProjection_range_fixed M i y
    · simp only [dif_neg hji]
      exact A.leftUnitizationProjection_range_off M i j hji y
  exact LinearMap.congr_fun h x

theorem rightUnitizationProjection_componentSum (M : ModuleCat.{v} A.totalUnitizationᵐᵒᵖ) (i : ℤ)
    (x : A.rightModuleTotalSpace (A.unitizationRightComponentModule M)) :
    A.rightUnitizationProjection M i (A.rightUnitizationComponentSum M x) = (x i).val := by
  have h : (A.rightUnitizationProjection M i).comp (A.rightUnitizationComponentSum M) =
      (A.rightUnitizationComponentSpace M i).subtype.comp (DirectSum.component k ℤ _ i) := by
    apply DFinsupp.lhom_ext
    intro j y
    change A.rightUnitizationComponentSpace M j at y
    change A.rightUnitizationProjection M i
      (A.rightUnitizationComponentSum M (DirectSum.lof k ℤ _ j y)) =
        (DirectSum.component k ℤ (fun l => A.rightUnitizationComponentSpace M l) i
          (DirectSum.lof k ℤ (fun l => A.rightUnitizationComponentSpace M l) j y)).val
    rw [A.rightUnitizationComponentSum_lof, DirectSum.component.of]
    by_cases hji : j = i
    · subst j
      simp only [dite_true]
      exact A.rightUnitizationProjection_range_fixed M i y
    · simp only [dif_neg hji]
      exact A.rightUnitizationProjection_range_off M i j hji y
  exact LinearMap.congr_fun h x

theorem leftUnitizationComponentSum_injective (M : ModuleCat.{v} A.totalUnitization) :
    Function.Injective (A.leftUnitizationComponentSum M) := by
  intro x y h
  apply DFinsupp.ext
  intro i
  apply Subtype.ext
  have hi := congrArg (A.leftUnitizationProjection M i) h
  rwa [A.leftUnitizationProjection_componentSum, A.leftUnitizationProjection_componentSum] at hi

theorem rightUnitizationComponentSum_injective (M : ModuleCat.{v} A.totalUnitizationᵐᵒᵖ) :
    Function.Injective (A.rightUnitizationComponentSum M) := by
  intro x y h
  apply DFinsupp.ext
  intro i
  apply Subtype.ext
  have hi := congrArg (A.rightUnitizationProjection M i) h
  rwa [A.rightUnitizationProjection_componentSum, A.rightUnitizationProjection_componentSum] at hi

theorem leftUnitizationLocalUnit_smul (M : ModuleCat.{v} A.totalUnitization)
    (s : Finset ℤ) (x : M) :
    (A.totalAlgebraLocalUnit s : A.totalUnitization) • x =
      ∑ i ∈ s, A.leftUnitizationProjection M i x := by
  change Unitization.inrHom k A.totalAlgebra (∑ i ∈ s, A.totalAlgebraComponent (A.id i)) • x = _
  rw [map_sum, Finset.sum_smul]
  rfl

theorem rightUnitizationLocalUnit_smul (M : ModuleCat.{v} A.totalUnitizationᵐᵒᵖ)
    (s : Finset ℤ) (x : M) :
    MulOpposite.op (A.totalAlgebraLocalUnit s : A.totalUnitization) • x =
      ∑ i ∈ s, A.rightUnitizationProjection M i x := by
  change MulOpposite.op
    (Unitization.inrHom k A.totalAlgebra (∑ i ∈ s, A.totalAlgebraComponent (A.id i))) • x = _
  rw [map_sum, Finset.op_sum, Finset.sum_smul]
  rfl

theorem leftUnitizationComponentSum_surjective (M : A.LeftLocallyUnitalModule) :
    Function.Surjective (A.leftUnitizationComponentSum M.obj) := by
  intro x
  obtain ⟨s,hs⟩ := M.property x
  refine ⟨∑ i ∈ s, DirectSum.lof k ℤ (fun j => A.leftUnitizationComponentSpace M.obj j) i
    ⟨A.leftUnitizationProjection M.obj i x, ⟨x,rfl⟩⟩, ?_⟩
  rw [map_sum]
  refine Eq.trans ?_ ((A.leftUnitizationLocalUnit_smul M.obj s x).symm.trans hs)
  apply Finset.sum_congr rfl
  intro i _
  exact A.leftUnitizationComponentSum_lof M.obj i
    ⟨A.leftUnitizationProjection M.obj i x, ⟨x,rfl⟩⟩

theorem rightUnitizationComponentSum_surjective (M : A.RightLocallyUnitalModule) :
    Function.Surjective (A.rightUnitizationComponentSum M.obj) := by
  intro x
  obtain ⟨s,hs⟩ := M.property x
  refine ⟨∑ i ∈ s, DirectSum.lof k ℤ (fun j => A.rightUnitizationComponentSpace M.obj j) i
    ⟨A.rightUnitizationProjection M.obj i x, ⟨x,rfl⟩⟩, ?_⟩
  rw [map_sum]
  refine Eq.trans ?_ ((A.rightUnitizationLocalUnit_smul M.obj s x).symm.trans hs)
  apply Finset.sum_congr rfl
  intro i _
  exact A.rightUnitizationComponentSum_lof M.obj i
    ⟨A.rightUnitizationProjection M.obj i x, ⟨x,rfl⟩⟩

noncomputable def leftUnitizationComponentSumEquiv (M : A.LeftLocallyUnitalModule) :
    A.leftModuleTotalSpace (A.unitizationLeftComponentModule M.obj) ≃ₗ[k] M.obj :=
  LinearEquiv.ofBijective (A.leftUnitizationComponentSum M.obj)
    ⟨A.leftUnitizationComponentSum_injective M.obj, A.leftUnitizationComponentSum_surjective M⟩

noncomputable def rightUnitizationComponentSumEquiv (M : A.RightLocallyUnitalModule) :
    A.rightModuleTotalSpace (A.unitizationRightComponentModule M.obj) ≃ₗ[k] M.obj :=
  LinearEquiv.ofBijective (A.rightUnitizationComponentSum M.obj)
    ⟨A.rightUnitizationComponentSum_injective M.obj, A.rightUnitizationComponentSum_surjective M⟩

end ASGinzburg.ZAlgebra
