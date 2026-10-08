import ASGinzburg.TotalModuleLocalUnits

/-!
The finite-support space of all Z-algebra components embeds faithfully into the
endomorphisms of the regular right module. Matrix entries recover every component.
This fixes the original multiplication orientation: `A.Hom i j = e_j A e_i`.
The multiplication and locally unital module comparison are constructed separately.
-/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

/-- The actual finite-support vector space of all components e_j A e_i. -/
abbrev totalAlgebraSpace : Type v :=
  ⨁ p : ℤ × ℤ, A.Hom p.1 p.2

noncomputable def regularComponentActionLinear (i j : ℤ) :
    A.Hom i j →ₗ[k] End A.rightRegularCoproduct where
  toFun := A.rightRegularCoproductAction
  map_add' := A.rightRegularCoproductAction_add
  map_smul' r a := A.rightRegularCoproductAction_smul a r

/-- Finite sums of genuine left multiplication maps on the regular right module. -/
noncomputable def totalAlgebraRepresentation :
    A.totalAlgebraSpace →ₗ[k] End A.rightRegularCoproduct :=
  DFinsupp.lsum k (fun p : ℤ × ℤ => A.regularComponentActionLinear p.1 p.2)

@[simp] theorem totalAlgebraRepresentation_single (i j : ℤ) (a : A.Hom i j) :
    A.totalAlgebraRepresentation (DFinsupp.single (i,j) a) =
      A.rightRegularCoproductAction a :=
  DFinsupp.lsum_single k _ _ _

noncomputable def regularMatrixEntry (i j : ℤ) :
    End A.rightRegularCoproduct →ₗ[k] (A.representable i ⟶ A.representable j) where
  toFun f := Sigma.ι (fun l : ℤ => A.representable l) i ≫
    f ≫ A.rightRegularCoproductProjection j
  map_add' f g := by
    change _ ≫ (f + g) ≫ _ = _
    rw [Preadditive.add_comp, Preadditive.comp_add]
  map_smul' r f := by
    change _ ≫ (r • f) ≫ _ = _
    rw [Linear.smul_comp, Linear.comp_smul]
    rfl

@[simp] theorem regularMatrixEntry_action (i j : ℤ) (a : A.Hom i j) :
    A.regularMatrixEntry i j (A.rightRegularCoproductAction a) =
      A.representableFunctor.map (show (⟨i⟩ : A.Obj) ⟶ ⟨j⟩ from a) := by
  change _ ≫ A.rightRegularCoproductAction a ≫ _ = _
  rw [A.rightRegularCoproduct_inclusion_action_assoc,
    A.rightRegularCoproduct_inclusion_projection]
  exact Category.comp_id _

theorem regularMatrixEntry_action_off {i j p q : ℤ} (a : A.Hom p q)
    (h : p ≠ i ∨ q ≠ j) :
    A.regularMatrixEntry i j (A.rightRegularCoproductAction a) = 0 := by
  rcases h with hpi | hqj
  · change _ ≫ A.rightRegularCoproductAction a ≫ _ = _
    rw [A.rightRegularCoproduct_inclusion_action_off_assoc a i (Ne.symm hpi), zero_comp]
  · by_cases hpi : p = i
    · subst p
      change _ ≫ A.rightRegularCoproductAction a ≫ _ = _
      rw [A.rightRegularCoproduct_inclusion_action_assoc,
        A.rightRegularCoproduct_inclusion_projection_off j q hqj, comp_zero]
    · change _ ≫ A.rightRegularCoproductAction a ≫ _ = _
      rw [A.rightRegularCoproduct_inclusion_action_off_assoc a i (Ne.symm hpi), zero_comp]

/-- Recover a concrete component from a matrix entry by linear Yoneda. -/
noncomputable def totalAlgebraEntry (i j : ℤ) :
    End A.rightRegularCoproduct →ₗ[k] A.Hom i j :=
  (A.representableHomEquiv i j).symm.toLinearMap.comp (A.regularMatrixEntry i j)

theorem totalAlgebraEntry_representation (i j : ℤ) (x : A.totalAlgebraSpace) :
    A.totalAlgebraEntry i j (A.totalAlgebraRepresentation x) = x (i,j) := by
  have h : (A.totalAlgebraEntry i j).comp A.totalAlgebraRepresentation =
      DFinsupp.lapply (i,j) := by
    apply DFinsupp.lhom_ext'
    rintro ⟨p,q⟩
    apply LinearMap.ext
    intro a
    change A.totalAlgebraEntry i j (A.totalAlgebraRepresentation (DFinsupp.single (p,q) a)) =
      (DFinsupp.single (p,q) a : A.totalAlgebraSpace) (i,j)
    rw [A.totalAlgebraRepresentation_single]
    by_cases hp : p = i
    · subst p
      by_cases hq : q = j
      · subst q
        simp only [totalAlgebraEntry, LinearMap.comp_apply, regularMatrixEntry_action]
        change (A.representableHomEquiv i j).symm
          ((linearYoneda k A.Obj).map a) = _
        change (A.representableHomEquiv i j).symm (A.representableHomEquiv i j a) = _
        rw [LinearEquiv.symm_apply_apply]
        symm
        exact DFinsupp.single_eq_same
      · simp only [totalAlgebraEntry, LinearMap.comp_apply]
        rw [A.regularMatrixEntry_action_off a (Or.inr hq), map_zero]
        symm
        apply DFinsupp.single_eq_of_ne
        intro h
        exact hq (congrArg Prod.snd h).symm
    · simp only [totalAlgebraEntry, LinearMap.comp_apply]
      rw [A.regularMatrixEntry_action_off a (Or.inl hp), map_zero]
      symm
      apply DFinsupp.single_eq_of_ne
      intro h
      exact hp (congrArg Prod.fst h).symm
  exact DFunLike.congr_fun h x

/-- No component information is lost by the regular representation. -/
theorem totalAlgebraRepresentation_injective :
    Function.Injective A.totalAlgebraRepresentation := by
  intro x y h
  apply DFinsupp.ext
  rintro ⟨i,j⟩
  have he := congrArg (A.totalAlgebraEntry i j) h
  simpa only [totalAlgebraEntry_representation] using he

end ASGinzburg.ZAlgebra
