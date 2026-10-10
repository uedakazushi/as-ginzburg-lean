import ASGinzburg.OrdinaryModuleRingDualFinite
import ASGinzburg.OrdinaryPerfectComplex
import ASGinzburg.ComplexDegreeReverse
import Mathlib.Algebra.Homology.Opposite

/-! Termwise noncommutative ring duality, followed by reversal of degrees,
gives an actual contravariant functor on cochain complexes. It preserves
genuine bounded finite projective complexes. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits Opposite
universe v
variable (R : Type v) [Ring R]

noncomputable def ordinaryRingDualCochainFunctor :
    (CochainComplex (ModuleCat.{v} R) ℤ)ᵒᵖ ⥤ CochainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ :=
  HomologicalComplex.opFunctor (ModuleCat R) (ComplexShape.up ℤ) ⋙
    (ordinaryRingDualFunctor R).mapHomologicalComplex (ComplexShape.down ℤ) ⋙
      reverseChainFunctor (ModuleCat Rᵐᵒᵖ)

noncomputable def ordinaryRingDualCochainComplex (K : CochainComplex (ModuleCat.{v} R) ℤ) :
    CochainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ :=
  (ordinaryRingDualCochainFunctor R).obj (op K)

@[simp] theorem ordinaryRingDualCochainComplex_d
    (K : CochainComplex (ModuleCat.{v} R) ℤ) (i j : ℤ) :
    (ordinaryRingDualCochainComplex R K).d i j =
      ModuleCat.ofHom (ordinaryRingDualMap R (K.d (-j) (-i))) := rfl

theorem ordinaryRingDualCochainComplex_perfect
    {K : CochainComplex (ModuleCat.{v} R) ℤ}
    (hK : ordinaryFiniteProjectiveCochainProperty R K) :
    ordinaryFiniteProjectiveCochainProperty Rᵐᵒᵖ (ordinaryRingDualCochainComplex R K) := by
  refine ⟨fun i => ordinaryFiniteProjectiveProperty_ringDual R (hK.1 (-i)), ?_⟩
  obtain ⟨a, b, hab⟩ := hK.2
  refine ⟨-b, -a, ?_⟩
  intro i hi
  change IsZero ((ordinaryRingDualFunctor R).obj (op (K.X (-i))))
  exact (ordinaryRingDualFunctor R).map_isZero (hab (-i) (by omega)).op

end ASGinzburg
