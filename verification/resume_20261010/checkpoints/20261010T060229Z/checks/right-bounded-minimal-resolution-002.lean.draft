import work.ASGinzburgDraft.RightBoundedMinimalSyzygies

/-! Every actual directed right module with a height upper bound has a
genuine projective resolution with that same bound on all its terms and
with every differential radical minimal. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}

namespace HeightBoundedRightModule
variable {b : ℤ} (M : A.HeightBoundedRightModule b)

noncomputable def complex : ChainComplex A.RightModule ℕ :=
  ChainComplex.of M.term M.differential M.differential_sq

theorem complex_exactAt_succ (n : ℕ) : M.complex.ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  change (ShortComplex.mk (M.complex.d (n + 2) (n + 1)) (M.complex.d (n + 1) n) _).Exact
  simpa only [show M.complex.d (n + 2) (n + 1) = M.differential (n + 1)
      from ChainComplex.of_d _ _ _ (n + 1),
    show M.complex.d (n + 1) n = M.differential n from ChainComplex.of_d _ _ _ n]
    using M.differential_exact n

noncomputable def augmentation : M.complex ⟶ (ChainComplex.single₀ A.RightModule).obj M.val :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨M.cover 0, by
    rw [show M.complex.d 1 0 = M.differential 0 from ChainComplex.of_d _ _ _ 0]
    exact M.differential_cover 0⟩

noncomputable instance augmentation_quasiIso : QuasiIso M.augmentation := ⟨fun n => by
  cases n
  · rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
    · dsimp
      refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2
        ⟨M.differential_cover_exact 0, inferInstance⟩
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by
          simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
          exact (ChainComplex.of_d M.term M.differential M.differential_sq 0).symm)
        (by simp [augmentation])
    all_goals rfl
  · rw [quasiIsoAt_iff_exactAt']
    · exact M.complex_exactAt_succ _
    · exact ChainComplex.exactAt_succ_single_obj _ _⟩

noncomputable def resolution : ProjectiveResolution M.val where
  complex := M.complex
  projective n := by change Projective (M.term n); infer_instance
  π := M.augmentation
  quasiIso := M.augmentation_quasiIso

theorem complex_d_minimal (n : ℕ) : A.IsMinimalMorphism (M.complex.d (n + 1) n) := by
  rw [show M.complex.d (n + 1) n = M.differential n from ChainComplex.of_d _ _ _ n]
  exact M.differential_minimal n

end HeightBoundedRightModule

variable (A)

noncomputable def rightBoundedMinimalResolution (M : A.RightModule) (b : ℤ)
    (hb : ∀ i : ℤ, b < i → IsZero ((A.rightModuleEvaluation i).obj M)) :
    ProjectiveResolution M :=
  HeightBoundedRightModule.resolution (A := A) (b := b) ⟨M, hb⟩

theorem rightBoundedMinimalResolution_term_isZero_above
    (M : A.RightModule) (b : ℤ)
    (hb : ∀ i : ℤ, b < i → IsZero ((A.rightModuleEvaluation i).obj M))
    (n : ℕ) (i : ℤ) (hi : b < i) :
    IsZero ((A.rightModuleEvaluation i).obj ((A.rightBoundedMinimalResolution M b hb).complex.X n)) :=
  HeightBoundedRightModule.term_isZero_above (A := A) (b := b) ⟨M, hb⟩ n i hi

theorem rightBoundedMinimalResolution_d_minimal
    (M : A.RightModule) (b : ℤ)
    (hb : ∀ i : ℤ, b < i → IsZero ((A.rightModuleEvaluation i).obj M)) (n : ℕ) :
    A.IsMinimalMorphism ((A.rightBoundedMinimalResolution M b hb).complex.d (n + 1) n) :=
  HeightBoundedRightModule.complex_d_minimal (A := A) (b := b) ⟨M, hb⟩ n

theorem exists_heightBounded_minimal_projectiveResolution
    (M : A.RightModule) (b : ℤ)
    (hb : ∀ i : ℤ, b < i → IsZero ((A.rightModuleEvaluation i).obj M)) :
    ∃ P : ProjectiveResolution M,
      (∀ n : ℕ, ∀ i : ℤ, b < i → IsZero ((A.rightModuleEvaluation i).obj (P.complex.X n))) ∧
      (∀ n : ℕ, A.IsMinimalMorphism (P.complex.d (n + 1) n)) :=
  ⟨A.rightBoundedMinimalResolution M b hb,
    A.rightBoundedMinimalResolution_term_isZero_above M b hb,
    A.rightBoundedMinimalResolution_d_minimal M b hb⟩

end ASGinzburg.ZAlgebra
