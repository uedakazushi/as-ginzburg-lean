import ASGinzburg.GinzburgGeneratorFiltrationCokernel

/-! An actual three-term homology complex and its augmentation. The
terms have not yet been identified with projective algebra modules. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgGeneratorLoopDualOriginal_comp (φ : Q.Potential k)
    (u v : Q.Vertex) (c : ℤ) :
    Q.ginzburgGeneratorLoopToDualHomology k φ u v c ≫
      Q.ginzburgGeneratorDualToOriginalHomology k φ u v c=0 := by
  simpa only [ginzburgGeneratorDualToOriginalHomology,show (-1:ℤ)+1=0 by norm_num] using
    Q.ginzburgGeneratorLoopToDualHomology_comp k φ u v c

noncomputable def ginzburgGeneratorHomologyTerm (φ : Q.Potential k)
    (u v : Q.Vertex) (c : ℤ) : ℕ → ModuleCat.{u} k
  | 0 => Q.ginzburgGeneratorFilteredHomology k φ u v 0 c 0
  | 1 => Q.ginzburgAssociatedGradedHomology k φ u v (-1) c (-1)
  | 2 => Q.ginzburgAssociatedGradedHomology k φ u v (-2) c (-2)
  | _+3 => 0

noncomputable def ginzburgGeneratorHomologyDifferential (φ : Q.Potential k)
    (u v : Q.Vertex) (c : ℤ) :
    ∀ n : ℕ, Q.ginzburgGeneratorHomologyTerm k φ u v c (n+1) ⟶
      Q.ginzburgGeneratorHomologyTerm k φ u v c n
  | 0 => Q.ginzburgGeneratorDualToOriginalHomology k φ u v c
  | 1 => Q.ginzburgGeneratorLoopToDualHomology k φ u v c
  | _+2 => 0

theorem ginzburgGeneratorHomologyDifferential_square (φ : Q.Potential k)
    (u v : Q.Vertex) (c : ℤ) (n : ℕ) :
    Q.ginzburgGeneratorHomologyDifferential k φ u v c (n+1) ≫
      Q.ginzburgGeneratorHomologyDifferential k φ u v c n=0 := by
  rcases n with _|_|n
  · exact Q.ginzburgGeneratorLoopDualOriginal_comp k φ u v c
  · simp [ginzburgGeneratorHomologyDifferential]
  · simp [ginzburgGeneratorHomologyDifferential]

noncomputable def ginzburgGeneratorHomologyChainComplex (φ : Q.Potential k)
    (u v : Q.Vertex) (c : ℤ) : ChainComplex (ModuleCat.{u} k) ℕ :=
  ChainComplex.of (Q.ginzburgGeneratorHomologyTerm k φ u v c)
    (Q.ginzburgGeneratorHomologyDifferential k φ u v c)
    (Q.ginzburgGeneratorHomologyDifferential_square k φ u v c)

theorem GinzburgRegular.generatorHomologyChainComplex_exactAt_succ {φ : Q.Potential k}
    (h : Q.GinzburgRegular k φ) (u v : Q.Vertex) (c : ℤ) (n : ℕ) :
    (Q.ginzburgGeneratorHomologyChainComplex k φ u v c).ExactAt (n+1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n+2) (n+1) n (by simp) (by simp)]
  rcases n with _|_|n
  · simpa [ginzburgGeneratorHomologyChainComplex,ginzburgGeneratorHomologyTerm,
      ginzburgGeneratorHomologyDifferential,HomologicalComplex.sc',
      ginzburgGeneratorDualToOriginalHomology,show (-1:ℤ)+1=0 by norm_num,
      ginzburgGeneratorLoopDualShortComplex] using h.loopDualShortComplex_exact Q k u v c
  · apply (ShortComplex.exact_iff_mono _ ?_).mpr
    · simpa [ginzburgGeneratorHomologyChainComplex,ginzburgGeneratorHomologyDifferential,
        HomologicalComplex.sc',HomologicalComplex.shortComplexFunctor'] using
        h.loopToDualHomology_mono Q k u v c
    · change (Q.ginzburgGeneratorHomologyChainComplex k φ u v c).d 3 2=0
      simpa only [ginzburgGeneratorHomologyChainComplex,ginzburgGeneratorHomologyDifferential] using
        ChainComplex.of_d (Q.ginzburgGeneratorHomologyTerm k φ u v c)
          (Q.ginzburgGeneratorHomologyDifferential k φ u v c)
          (Q.ginzburgGeneratorHomologyDifferential_square k φ u v c) 2
  · apply ShortComplex.exact_of_isZero_X₂
    simpa [ginzburgGeneratorHomologyChainComplex,ginzburgGeneratorHomologyTerm,
      HomologicalComplex.sc',HomologicalComplex.shortComplexFunctor'] using isZero_zero (ModuleCat k)

noncomputable def ginzburgGeneratorHomologyAugmentation (φ : Q.Potential k)
    (u v : Q.Vertex) (c : ℤ) :
    Q.ginzburgGeneratorHomologyChainComplex k φ u v c ⟶
      (ChainComplex.single₀ (ModuleCat.{u} k)).obj (Q.ginzburgAugmentationHomology k φ u v c 0) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨Q.ginzburgGeneratorFiltrationRadicalMap k φ u v c,by
      simpa [ginzburgGeneratorHomologyChainComplex,ginzburgGeneratorHomologyDifferential] using
        Q.ginzburgGeneratorDualToOriginalHomology_comp k φ u v c⟩

theorem GinzburgRegular.generatorHomologyAugmentation_quasiIso {φ : Q.Potential k}
    (h : Q.GinzburgRegular k φ) (u v : Q.Vertex) (c : ℤ) :
    QuasiIso (Q.ginzburgGeneratorHomologyAugmentation k φ u v c) := ⟨fun n => by
  cases n
  · rw [ChainComplex.quasiIsoAt₀_iff,ShortComplex.quasiIso_iff_of_zeros']
    · dsimp
      refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2
        ⟨Q.ginzburgGeneratorDualOriginalShortComplex_exact k φ u v c,
          Q.ginzburgGeneratorFiltrationRadicalMap_epi k φ u v c⟩
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by dsimp; exact (ChainComplex.of_d (Q.ginzburgGeneratorHomologyTerm k φ u v c)
          (Q.ginzburgGeneratorHomologyDifferential k φ u v c)
          (Q.ginzburgGeneratorHomologyDifferential_square k φ u v c) 0).symm)
        (by simp [ginzburgGeneratorHomologyAugmentation,ginzburgGeneratorDualOriginalShortComplex])
    all_goals rfl
  · rw [quasiIsoAt_iff_exactAt']
    · exact h.generatorHomologyChainComplex_exactAt_succ Q k u v c _
    · apply ChainComplex.exactAt_succ_single_obj⟩

end ASGinzburg.CutQuiver
