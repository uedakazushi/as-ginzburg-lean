import ASGinzburg.RightModuleRadical

/-!
# Minimal differentials as actual radical containment

Minimality is the componentwise image containment from the source paper.
It is equivalent to factorization through the concrete target radical.
No projective resolution or AS property is inferred from this predicate alone.
-/

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

/-- The image of an actual module morphism lies in the positive-degree radical of its target. -/
def IsMinimalMorphism {M N : A.RightModule} (f : M ⟶ N) : Prop :=
  ∀ (i : ℤ) (x : (A.rightModuleEvaluation i).obj M),
    (A.rightModuleEvaluation i).map f x ∈ A.positiveActionSpan N i

theorem isMinimalMorphism_iff_range_le {M N : A.RightModule} (f : M ⟶ N) :
    A.IsMinimalMorphism f ↔ ∀ i : ℤ,
      LinearMap.range ((A.rightModuleEvaluation i).map f).hom ≤ A.positiveActionSpan N i := by
  constructor
  · intro h i y hy
    obtain ⟨x, rfl⟩ := hy
    exact h i x
  · intro h i x
    exact h i ⟨x, rfl⟩

/-- A minimal morphism factors through the actual target radical with its right action. -/
def minimalMorphismLift {M N : A.RightModule} (f : M ⟶ N) (hf : A.IsMinimalMorphism f) :
    M ⟶ (A.rightModuleRadical N).object where
  app X := ModuleCat.ofHom {
    toFun x := ⟨f.app X x, hf X.unop.index x⟩
    map_add' x y := Subtype.ext (map_add (f.app X).hom x y)
    map_smul' r x := Subtype.ext (map_smul (f.app X).hom r x) }
  naturality := by
    intro X Y a
    apply ModuleCat.hom_ext
    ext x
    apply Subtype.ext
    exact congrArg (fun g => g x) (f.naturality a)

@[simp] theorem minimalMorphismLift_inclusion {M N : A.RightModule} (f : M ⟶ N)
    (hf : A.IsMinimalMorphism f) :
    A.minimalMorphismLift f hf ≫ (A.rightModuleRadical N).inclusion = f := by
  apply NatTrans.ext
  funext X
  rfl

theorem isMinimalMorphism_of_factor {M N : A.RightModule} (f : M ⟶ N)
    (g : M ⟶ (A.rightModuleRadical N).object)
    (h : g ≫ (A.rightModuleRadical N).inclusion = f) : A.IsMinimalMorphism f := by
  intro i x
  rw [← h]
  exact (g.app (op ⟨i⟩) x).property

theorem isMinimalMorphism_iff_factors {M N : A.RightModule} (f : M ⟶ N) :
    A.IsMinimalMorphism f ↔ ∃ g : M ⟶ (A.rightModuleRadical N).object,
      g ≫ (A.rightModuleRadical N).inclusion = f :=
  ⟨fun h => ⟨A.minimalMorphismLift f h, A.minimalMorphismLift_inclusion f h⟩,
    fun ⟨g, h⟩ => A.isMinimalMorphism_of_factor f g h⟩

theorem isMinimalMorphism_zero (M N : A.RightModule) : A.IsMinimalMorphism (0 : M ⟶ N) := by
  intro i x
  change 0 ∈ A.positiveActionSpan N i
  exact (A.positiveActionSpan N i).zero_mem

/-- Precomposing a minimal morphism preserves the actual radical containment. -/
theorem isMinimalMorphism_comp_left {L M N : A.RightModule} (f : L ⟶ M) (g : M ⟶ N)
    (hg : A.IsMinimalMorphism g) : A.IsMinimalMorphism (f ≫ g) := by
  intro i x
  exact hg i ((A.rightModuleEvaluation i).map f x)

/-- Postcomposing preserves minimality because every module morphism preserves positive products. -/
theorem isMinimalMorphism_comp_right {L M N : A.RightModule} (f : L ⟶ M) (g : M ⟶ N)
    (hf : A.IsMinimalMorphism f) : A.IsMinimalMorphism (f ≫ g) := by
  intro i x
  exact A.positiveActionSpan_map_mem g i (hf i x)

end ASGinzburg.ZAlgebra
