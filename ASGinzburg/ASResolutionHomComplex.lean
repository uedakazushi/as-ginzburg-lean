import ASGinzburg.ASResolutionComplex

/-!
# The actual k-linear Hom complex of the finite AS resolution

These are morphism spaces of the existing right modules. In particular no
Ext comparison is postulated: identifying its homology with the derived
category's `Abelian.Ext` is a further proof obligation.
-/

namespace ASGinzburg.ZAlgebra.ASResolution
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k} {Q : CutQuiver}
variable {v : Q.LiftVertex} (R : A.ASResolution Q v)

noncomputable def homDifferential (N : A.RightModule) (n : ℕ) :
    ModuleCat.of k (R.complexTerm n ⟶ N) ⟶
      ModuleCat.of k (R.complexTerm (n + 1) ⟶ N) :=
  ModuleCat.ofHom {
    toFun := fun f => R.complexDifferential n ≫ f
    map_add' := by intro f g; simp only [Preadditive.comp_add]
    map_smul' := by intro r f; simp only [Linear.comp_smul, RingHom.id_apply] }

theorem homDifferential_sq (N : A.RightModule) (n : ℕ) :
    R.homDifferential N n ≫ R.homDifferential N (n + 1) = 0 := by
  apply ModuleCat.hom_ext
  ext f
  change R.complexDifferential (n + 1) ≫ (R.complexDifferential n ≫ f) = 0
  rw [← Category.assoc, R.complexDifferential_sq, zero_comp]

noncomputable def homComplex (N : A.RightModule) : CochainComplex (ModuleCat k) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of k (R.complexTerm n ⟶ N))
    (R.homDifferential N) (R.homDifferential_sq N)

theorem complexDifferential_minimal (n : ℕ) : A.IsMinimalMorphism (R.complexDifferential n) := by
  rcases n with _ | _ | _ | n
  · exact R.minimal₁
  · exact R.minimal₂
  · exact R.minimal₃
  · exact A.isMinimalMorphism_zero _ _

/-- Every cochain differential into a simple module vanishes by actual minimality. -/
theorem homDifferential_simple_zero (i : ℤ) (n : ℕ) :
    R.homDifferential (A.simpleRightModule i) n = 0 := by
  apply ModuleCat.hom_ext
  ext f
  exact A.minimalMorphism_comp_simple_eq_zero _ (R.complexDifferential_minimal n) i f

theorem homComplex_simple_d_zero (i : ℤ) (n : ℕ) :
    (R.homComplex (A.simpleRightModule i)).d n (n + 1) = 0 :=
  (CochainComplex.of_d _ _ _ n).trans (R.homDifferential_simple_zero i n)

theorem homComplex_simple_d_all_zero (i : ℤ) (n m : ℕ) :
    (R.homComplex (A.simpleRightModule i)).d n m = 0 := by
  by_cases h : n + 1 = m
  · subst m
    exact R.homComplex_simple_d_zero i n
  · exact CochainComplex.of_d_ne _ _ _ h

/-- Homology of Hom(-,s_i) is its actual degree-n morphism space. This does
not yet identify this homology with derived-category Ext. -/
noncomputable def homComplex_simple_homologyIso (i : ℤ) (n : ℕ) :
    (R.homComplex (A.simpleRightModule i)).homology n ≅
      ModuleCat.of k (R.complexTerm n ⟶ A.simpleRightModule i) :=
  (ShortComplex.HomologyData.ofZeros ((R.homComplex (A.simpleRightModule i)).sc n)
    (R.homComplex_simple_d_all_zero i _ _)
    (R.homComplex_simple_d_all_zero i _ _)).left.homologyIso

end ASGinzburg.ZAlgebra.ASResolution
