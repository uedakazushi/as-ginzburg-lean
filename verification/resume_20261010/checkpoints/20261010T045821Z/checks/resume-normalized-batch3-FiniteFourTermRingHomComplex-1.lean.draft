import ASGinzburg.FiniteFourTermProjectiveResolution
import work.ASGinzburgDraft.OrdinaryModuleRingDualDerived
import work.ASGinzburgDraft.OrdinaryModuleRingDualFinite
import work.ASGinzburgDraft.OrdinaryModuleRingDualTopFinite
import ASGinzburg.OrdinaryPerfectDerivedObject
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-! A genuine finite four-term projective resolution computes the actual
right-derived ring Hom by a bounded finite-projective cochain complex of
opposite-ring modules, in degrees zero through three. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits Opposite
universe v w
variable {R : Type v} [Ring R] {X : ModuleCat.{v} R}

namespace FiniteFourTermProjectiveResolution
variable (F : FiniteFourTermProjectiveResolution X)

noncomputable def ringHomNatCochainComplex : CochainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℕ :=
  ((ordinaryRingDualFunctor R).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    F.toProjectiveResolution.complex.op

noncomputable def ringHomCochainComplex : CochainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ :=
  F.ringHomNatCochainComplex.extend ComplexShape.embeddingUpNat

theorem ringHomNatCochainComplex_term_finiteProjective (n : ℕ) :
    ordinaryFiniteProjectiveProperty Rᵐᵒᵖ (F.ringHomNatCochainComplex.X n) := by
  haveI : Projective (F.toProjectiveResolution.complex.X n) :=
    F.toProjectiveResolution.projective n
  haveI : Module.Finite R (F.toProjectiveResolution.complex.X n) :=
    F.toProjectiveResolution_term_finite n
  exact ordinaryFiniteProjectiveProperty_ringDual R
    (ordinaryModule_finiteFreeRetract R (F.toProjectiveResolution.complex.X n))

theorem ringHomNatCochainComplex_isZero_ge_four (n : ℕ) :
    IsZero (F.ringHomNatCochainComplex.X (n + 4)) :=
  (ordinaryRingDualFunctor R).map_isZero
    (F.toProjectiveResolution_isZero_ge_four n).op

theorem ringHomCochainComplex_term_finiteProjective (i : ℤ) :
    ordinaryFiniteProjectiveProperty Rᵐᵒᵖ (F.ringHomCochainComplex.X i) := by
  by_cases h : ∃ n : ℕ, ComplexShape.embeddingUpNat.f n = i
  · obtain ⟨n, hn⟩ := h
    exact ordinaryFiniteProjectiveProperty_of_iso Rᵐᵒᵖ
      (F.ringHomNatCochainComplex.extendXIso ComplexShape.embeddingUpNat hn)
      (F.ringHomNatCochainComplex_term_finiteProjective n)
  · exact ordinaryFiniteProjectiveProperty_of_isZero Rᵐᵒᵖ
      (F.ringHomNatCochainComplex.isZero_extend_X ComplexShape.embeddingUpNat i
        (fun n hn => h ⟨n, hn⟩))

theorem ringHomCochainComplex_isZero_outside (i : ℤ) (hi : i < 0 ∨ 3 < i) :
    IsZero (F.ringHomCochainComplex.X i) := by
  by_cases h : ∃ n : ℕ, ComplexShape.embeddingUpNat.f n = i
  · obtain ⟨n, hn⟩ := h
    have hn4 : 4 ≤ n := by
      dsimp [ComplexShape.embeddingUpNat] at hn
      omega
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn4
    rw [Nat.add_comm 4 m] at hn
    exact (F.ringHomNatCochainComplex_isZero_ge_four m).of_iso
      (F.ringHomNatCochainComplex.extendXIso ComplexShape.embeddingUpNat hn)
  · exact F.ringHomNatCochainComplex.isZero_extend_X ComplexShape.embeddingUpNat i
      (fun n hn => h ⟨n, hn⟩)

theorem ringHomCochainComplex_perfect :
    ordinaryFiniteProjectiveCochainProperty Rᵐᵒᵖ F.ringHomCochainComplex :=
  ⟨F.ringHomCochainComplex_term_finiteProjective,
    0, 3, F.ringHomCochainComplex_isZero_outside⟩

noncomputable def ringDualExtCochainHomologyIso (n : ℕ) :
    (ordinaryRingDualExtFunctor R n).obj (op X) ≅
      F.ringHomCochainComplex.homology (n : ℤ) :=
  ordinaryRingDualResolutionHomologyIso R F.toProjectiveResolution n ≪≫
    (F.ringHomNatCochainComplex.extendHomologyIso ComplexShape.embeddingUpNat
      (show ComplexShape.embeddingUpNat.f n = (n : ℤ) from rfl)).symm

include F in
theorem ringDualExt_isZero_ge_four (n : ℕ) :
    IsZero ((ordinaryRingDualExtFunctor R (n + 4)).obj (op X)) :=
  ordinaryRingDualExt_isZero_ge_four R F.toProjectiveResolution
    F.toProjectiveResolution_isZero_ge_four n

include F in
theorem ringDualExt_three_finite :
    Module.Finite Rᵐᵒᵖ ((ordinaryRingDualExtFunctor R 3).obj (op X)) := by
  haveI : Module.Finite R (F.toProjectiveResolution.complex.X 3) :=
    F.toProjectiveResolution_term_finite 3
  exact ordinaryRingDualExt_three_finite_of_resolution R F.toProjectiveResolution
    (F.toProjectiveResolution_isZero_ge_four 0)

theorem ringHomPerfectDerived [HasDerivedCategory.{w} (ModuleCat.{v} Rᵐᵒᵖ)] :
    ordinaryPerfectDerivedProperty Rᵐᵒᵖ
      (DerivedCategory.Q.obj F.ringHomCochainComplex) :=
  ordinaryPerfectDerivedProperty_of_cochain Rᵐᵒᵖ F.ringHomCochainComplex
    F.ringHomCochainComplex_perfect

end FiniteFourTermProjectiveResolution
end ASGinzburg
