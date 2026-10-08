import ASGinzburg.LeftResolutionDuality
import ASGinzburg.RightResolutionDuality

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)
  {M : A.LeftModule} (P : ProjectiveResolution M) (h₄ : IsZero (P.complex.X 4))
  (hP : ∀ n, n<4 → A.leftFiniteProjectiveProperty (P.complex.X n))
  (hExt : ∀ i n, n<3 → ∀ e : Abelian.Ext.{v} M (A.leftRepresentable i) n, e=0)

noncomputable def leftResolutionBidualTermIso (n : ℕ) (hn : n<4) :
    A.rightModuleADual (A.leftModuleADual (P.complex.X n)) ≅ P.complex.X n := by
  letI := A.leftFiniteProjectiveProperty_bidual (hP n hn)
  exact (asIso (A.leftModuleBidualEvaluation (P.complex.X n))).symm

noncomputable def leftResolutionBidualTopProjection :
    A.rightModuleADual ((A.leftResolutionDualFourTerm P h₄ hP hExt).term 3) ⟶ M :=
  (A.leftResolutionBidualTermIso P hP 0 (by decide)).hom ≫ P.π.f 0

noncomputable instance leftResolutionBidualTopProjectionEpi :
    Epi (A.leftResolutionBidualTopProjection P h₄ hP hExt) := by
  letI := A.leftFiniteProjectiveProperty_bidual (hP 0 (by decide))
  dsimp [leftResolutionBidualTopProjection]
  infer_instance

theorem leftResolutionBidualTopDifferential_comm :
    A.rightModuleADualMap ((A.leftResolutionDualFourTerm P h₄ hP hExt).complex.d 3 2) ≫
      (A.leftResolutionBidualTermIso P hP 0 (by decide)).hom =
    (A.leftResolutionBidualTermIso P hP 1 (by decide)).hom ≫ P.complex.d 1 0 := by
  letI := A.leftFiniteProjectiveProperty_bidual (hP 0 (by decide))
  letI := A.leftFiniteProjectiveProperty_bidual (hP 1 (by decide))
  rw [show (A.leftResolutionDualFourTerm P h₄ hP hExt).complex.d 3 2 =
    A.leftModuleADualMap (P.complex.d 1 0) from ChainComplex.of_d _ _ _ 2]
  change A.rightModuleADualMap (A.leftModuleADualMap (P.complex.d 1 0)) ≫
    inv (A.leftModuleBidualEvaluation (P.complex.X 0)) =
    inv (A.leftModuleBidualEvaluation (P.complex.X 1)) ≫ P.complex.d 1 0
  have H := A.leftModuleBidualEvaluation_natural (P.complex.d 1 0)
  apply Eq.symm
  rw [IsIso.inv_comp_eq,← Category.assoc,← H]
  simp only [Category.assoc,IsIso.hom_inv_id,Category.comp_id]

theorem leftResolutionBidualTopProjection_differential :
    A.rightModuleADualMap ((A.leftResolutionDualFourTerm P h₄ hP hExt).complex.d 3 2) ≫
      A.leftResolutionBidualTopProjection P h₄ hP hExt = 0 := by
  dsimp only [leftResolutionBidualTopProjection]
  rw [← Category.assoc,A.leftResolutionBidualTopDifferential_comm,
    Category.assoc,P.complex_d_comp_π_f_zero,comp_zero]

theorem leftResolutionBidualTopProjection_exact :
    (ShortComplex.mk
      (A.rightModuleADualMap ((A.leftResolutionDualFourTerm P h₄ hP hExt).complex.d 3 2))
      (A.leftResolutionBidualTopProjection P h₄ hP hExt)
      (A.leftResolutionBidualTopProjection_differential P h₄ hP hExt)).Exact := by
  letI := A.leftFiniteProjectiveProperty_bidual (hP 0 (by decide))
  letI := A.leftFiniteProjectiveProperty_bidual (hP 1 (by decide))
  let T := ShortComplex.mk (P.complex.d 1 0) (P.π.f 0) P.complex_d_comp_π_f_zero
  let e : ShortComplex.mk
      (A.rightModuleADualMap ((A.leftResolutionDualFourTerm P h₄ hP hExt).complex.d 3 2))
      (A.leftResolutionBidualTopProjection P h₄ hP hExt)
      (A.leftResolutionBidualTopProjection_differential P h₄ hP hExt) ≅ T :=
    ShortComplex.isoMk (A.leftResolutionBidualTermIso P hP 1 (by decide))
      (A.leftResolutionBidualTermIso P hP 0 (by decide)) (Iso.refl _)
      (by exact (A.leftResolutionBidualTopDifferential_comm P h₄ hP hExt).symm)
      (by simp [T,leftResolutionBidualTopProjection])
  exact (ShortComplex.exact_iff_of_iso e).mpr P.exact₀

/-- Actual degree-three Ext twice recovers M by the canonical finite-projective evaluation. -/
noncomputable def leftResolutionExtBidualIso :
    A.rightModuleExtLeft (A.leftModuleExtRight M 3) 3 ≅ M :=
  IsColimit.coconePointUniqueUpToIso
    (A.rightResolutionExtTopProjection_exact
      (A.leftResolutionDualFourTerm P h₄ hP hExt).toProjectiveResolution
      ((A.leftResolutionDualFourTerm P h₄ hP hExt).complex_isZero_ge_four 0)).gIsCokernel
    (A.leftResolutionBidualTopProjection_exact P h₄ hP hExt).gIsCokernel
end ASGinzburg.ZAlgebra
