import ASGinzburg.GinzburgASProjectiveExactness
import ASGinzburg.RightModuleExt

/-! The genuine four AS projective terms and Ginzburg connecting
differentials form an actual chain complex of existing right modules.
Genuine Ginzburg regularity proves its positive-degree exactness. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def ginzburgASProjectiveComplexTerm (φ : Q.Potential k)
    (v : Q.LiftVertex) : ℕ → (Q.unrolledJacobianZAlgebra k φ).RightModule
  | 0 => (Q.unrolledJacobianZAlgebra k φ).representable (Q.height v)
  | 1 => (Q.unrolledJacobianZAlgebra k φ).asResolutionTerm₁ Q v
  | 2 => (Q.unrolledJacobianZAlgebra k φ).asResolutionTerm₂ Q v
  | 3 => (Q.unrolledJacobianZAlgebra k φ).representable (Q.height (Q.tau.symm v))
  | _+4 => 0

noncomputable def ginzburgASProjectiveComplexDifferential (φ : Q.Potential k)
    (v : Q.LiftVertex) :
    ∀ n : ℕ, Q.ginzburgASProjectiveComplexTerm k φ v (n+1) ⟶
      Q.ginzburgASProjectiveComplexTerm k φ v n
  | 0 => Q.ginzburgASProjectiveD₁ k φ v
  | 1 => Q.ginzburgASProjectiveD₂ k φ v
  | 2 => Q.ginzburgASProjectiveD₃ k φ v
  | _+3 => 0

theorem ginzburgASProjectiveComplexDifferential_square (φ : Q.Potential k)
    (v : Q.LiftVertex) (n : ℕ) :
    Q.ginzburgASProjectiveComplexDifferential k φ v (n+1) ≫
      Q.ginzburgASProjectiveComplexDifferential k φ v n=0 := by
  rcases n with _|_|_|n
  · exact Q.ginzburgASProjectiveD₂_comp_D₁ k φ v
  · exact Q.ginzburgASProjectiveD₃_comp_D₂ k φ v
  · simp [ginzburgASProjectiveComplexDifferential]
  · simp [ginzburgASProjectiveComplexDifferential]

noncomputable def ginzburgASProjectiveComplex (φ : Q.Potential k)
    (v : Q.LiftVertex) : ChainComplex (Q.unrolledJacobianZAlgebra k φ).RightModule ℕ :=
  ChainComplex.of (Q.ginzburgASProjectiveComplexTerm k φ v)
    (Q.ginzburgASProjectiveComplexDifferential k φ v)
    (Q.ginzburgASProjectiveComplexDifferential_square k φ v)

theorem ginzburgASProjectiveComplex_d (φ : Q.Potential k) (v : Q.LiftVertex) (n : ℕ) :
    (Q.ginzburgASProjectiveComplex k φ v).d (n+1) n=
      Q.ginzburgASProjectiveComplexDifferential k φ v n :=
  ChainComplex.of_d _ _ _ n

noncomputable instance ginzburgASProjectiveComplexTerm_projective (φ : Q.Potential k)
    (v : Q.LiftVertex) (n : ℕ) :
    Projective (Q.ginzburgASProjectiveComplexTerm k φ v n) := by
  rcases n with _|_|_|_|n <;> dsimp [ginzburgASProjectiveComplexTerm] <;> infer_instance

theorem GinzburgRegular.asProjectiveComplex_exactAt_succ {φ : Q.Potential k}
    (h : Q.GinzburgRegular k φ) (v : Q.LiftVertex) (n : ℕ) :
    (Q.ginzburgASProjectiveComplex k φ v).ExactAt (n+1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n+2) (n+1) n (by simp) (by simp)]
  rcases n with _|_|_|n
  · simpa [ginzburgASProjectiveComplex,ginzburgASProjectiveComplexTerm,
      ginzburgASProjectiveComplexDifferential,HomologicalComplex.sc'] using
      Q.ginzburgASProjectiveDualOriginalShortComplex_exact k φ v
  · simpa [ginzburgASProjectiveComplex,ginzburgASProjectiveComplexTerm,
      ginzburgASProjectiveComplexDifferential,HomologicalComplex.sc'] using
      h.asProjectiveConnectingShortComplex_exact Q k v
  · apply (ShortComplex.exact_iff_mono _ ?_).mpr
    · simpa [ginzburgASProjectiveComplex,ginzburgASProjectiveComplexDifferential,
        HomologicalComplex.sc',HomologicalComplex.shortComplexFunctor'] using
        h.asProjectiveD₃_mono Q k v
    · change (Q.ginzburgASProjectiveComplex k φ v).d 4 3=0
      simpa only [ginzburgASProjectiveComplex,Nat.reduceAdd,
        ginzburgASProjectiveComplexDifferential] using
        ChainComplex.of_d (Q.ginzburgASProjectiveComplexTerm k φ v)
          (Q.ginzburgASProjectiveComplexDifferential k φ v)
          (Q.ginzburgASProjectiveComplexDifferential_square k φ v) 3
  · apply ShortComplex.exact_of_isZero_X₂
    simpa [ginzburgASProjectiveComplex,ginzburgASProjectiveComplexTerm,
      HomologicalComplex.sc',HomologicalComplex.shortComplexFunctor'] using
      isZero_zero (Q.unrolledJacobianZAlgebra k φ).RightModule

theorem ginzburgASProjectiveComplex_isZero_ge_four (φ : Q.Potential k)
    (v : Q.LiftVertex) (n : ℕ) :
    IsZero ((Q.ginzburgASProjectiveComplex k φ v).X (n+4)) := by
  change IsZero (Q.ginzburgASProjectiveComplexTerm k φ v (n+4))
  exact isZero_zero (Q.unrolledJacobianZAlgebra k φ).RightModule

end ASGinzburg.CutQuiver
