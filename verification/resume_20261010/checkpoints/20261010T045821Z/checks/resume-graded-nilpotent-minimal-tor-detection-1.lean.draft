import work.ASGinzburgDraft.BalancedTensorRightMinimalTop
import work.ASGinzburgDraft.GradedNilpotentNakayamaLinearGrading
import work.ASGinzburgDraft.FourTermTruncationOfResolution

/-! Genuine second-factor Tor detects an actual minimal resolution term
by bounded-below graded Nakayama. In degree four this gives projective
dimension at most three and a concrete four-term projective resolution.
The acting ring is arbitrary; no native cut cover model is assumed. -/
namespace ASGinzburg
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra DirectSum
universe u v w z t
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (J : Ideal R) [J.IsTwoSided]
variable (N : ModuleCat.{max v z} R) (P : ProjectiveResolution N)
variable (hP : ∀ i j, ∀ y : P.complex.X i,
  P.complex.d i j y ∈ ordinaryIdealActionSpan k R (P.complex.X j) J)
variable (R₀ : Type w) [Ring R₀] [Algebra k R₀]

include hP in
theorem gradedMinimalResolution_term_isZero_of_tor
    (n : ℕ) [Module R₀ (P.complex.X n)] [IsScalarTower k R₀ (P.complex.X n)]
    (G : ℤ → Submodule k (P.complex.X n)) [DirectSum.Decomposition G]
    (h₀ : ∀ (q : ℤ) (r : R₀) (x : P.complex.X n), x ∈ G q → r • x ∈ G q)
    {ι : Type t} (d : ι → ℕ) (f : ι → (P.complex.X n) →ₗ[k] (P.complex.X n))
    (I₀ : Ideal R₀) (N₀ : ℕ) (hN₀ : I₀^N₀=⊥) (hd : ∀ i : ι, 0 < d i)
    (hf : ∀ (i : ι) (q : ℤ) (x : P.complex.X n),
      x ∈ G q → f i x ∈ G (q+(d i:ℤ)))
    (b : ℤ) (hb : ∀ q : ℤ, q < b → G q=⊥)
    (hAction : gradedNilpotentActionSpan k R₀ (P.complex.X n) f I₀=
      ordinaryIdealActionSpan k R (P.complex.X n) J)
    (hTor : IsZero ((balancedTensorTorFunctor.{u,v,v,z} k R (R ⧸ J)ᵐᵒᵖ n).obj N)) :
    IsZero (P.complex.X n) := by
  have hTop : gradedNilpotentActionSpan k R₀ (P.complex.X n) f I₀=⊤ := by
    rw [hAction]
    exact ordinaryIdealActionSpan_eq_top_of_minimal_tor_zero k R J N P hP n hTor
  letI : Subsingleton (P.complex.X n) :=
    gradedModule_subsingleton_of_linear_grading_nilpotent_action_span_top k R₀
      (P.complex.X n) G h₀ d f I₀ N₀ hN₀ hd hf b hb hTop
  exact ModuleCat.isZero_iff_subsingleton.mpr inferInstance

variable [Module R₀ (P.complex.X 4)] [IsScalarTower k R₀ (P.complex.X 4)]
variable (G : ℤ → Submodule k (P.complex.X 4)) [DirectSum.Decomposition G]
variable (h₀ : ∀ (q : ℤ) (r : R₀) (x : P.complex.X 4), x ∈ G q → r • x ∈ G q)
variable {ι : Type t} (d : ι → ℕ) (f : ι → (P.complex.X 4) →ₗ[k] (P.complex.X 4))
variable (I₀ : Ideal R₀) (N₀ : ℕ) (hN₀ : I₀^N₀=⊥) (hd : ∀ i : ι, 0 < d i)
variable (hf : ∀ (i : ι) (q : ℤ) (x : P.complex.X 4),
  x ∈ G q → f i x ∈ G (q+(d i:ℤ)))
variable (b : ℤ) (hb : ∀ q : ℤ, q < b → G q=⊥)
variable (hAction : gradedNilpotentActionSpan k R₀ (P.complex.X 4) f I₀=
  ordinaryIdealActionSpan k R (P.complex.X 4) J)
variable (hTor : IsZero ((balancedTensorTorFunctor.{u,v,v,z} k R (R ⧸ J)ᵐᵒᵖ 4).obj N))

noncomputable def fourTermProjectiveResolution_of_graded_minimal_tor_four :
    FourTermProjectiveResolution N :=
  fourTermTruncationOfResolution P
    (gradedMinimalResolution_term_isZero_of_tor k R J N P hP R₀ 4 G h₀ d f I₀
      N₀ hN₀ hd hf b hb hAction hTor)

include hP h₀ hN₀ hd hf hb hAction hTor in
theorem hasProjectiveDimensionLE_three_of_graded_minimal_tor_four :
    HasProjectiveDimensionLE N 3 :=
  fourTermProjectiveResolution_hasProjectiveDimensionLE P
    (gradedMinimalResolution_term_isZero_of_tor k R J N P hP R₀ 4 G h₀ d f I₀
      N₀ hN₀ hd hf b hb hAction hTor)

end ASGinzburg
