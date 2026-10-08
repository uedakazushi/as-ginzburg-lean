import ASGinzburg.ProjectiveResolutionHomExactness
import ASGinzburg.ASLeftExtReciprocity
import ASGinzburg.FourTermProjectiveResolution
import ASGinzburg.FiniteProjectiveClosure

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)
  {M : A.LeftModule} (P : ProjectiveResolution M)

noncomputable def leftResolutionDualComplex : CochainComplex A.RightModule ℕ :=
  (A.leftModuleADualFunctor.mapHomologicalComplex (ComplexShape.up ℕ)).obj P.complex.op

noncomputable def leftResolutionDualComplexEvaluationIso (i : ℤ) :
    ((A.rightModuleEvaluation i).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (A.leftResolutionDualComplex P) ≅ P.homComplex (k := k) (A.leftRepresentable i) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro n m hnm
    obtain rfl : m = n+1 := hnm.symm
    simp only [Iso.refl_hom,Category.id_comp,Category.comp_id]
    rw [show (P.homComplex (k := k) (A.leftRepresentable i)).d n (n+1) =
      P.homDifferential (k := k) (A.leftRepresentable i) n from CochainComplex.of_d _ _ _ n]
    rfl)

theorem leftResolutionDualComplex_exactAt_low (h₄ : IsZero (P.complex.X 4))
    (hExt : ∀ i n, n<3 → ∀ e : Abelian.Ext.{v} M (A.leftRepresentable i) n, e=0)
    (n : ℕ) (hn : n<3) : (A.leftResolutionDualComplex P).ExactAt n := by
  rw [HomologicalComplex.exactAt_iff]
  apply (A.rightModule_exact_iff _).mpr
  intro i
  have he := P.homComplex_exactAt_low_of_ext_zero (k := k) h₄ (A.leftRepresentable i) (hExt i) n hn
  exact (ShortComplex.exact_iff_of_iso
    ((HomologicalComplex.shortComplexFunctor _ _ n).mapIso
      (A.leftResolutionDualComplexEvaluationIso P i))).mpr he
end ASGinzburg.ZAlgebra

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)
  {M : A.LeftModule} (P : ProjectiveResolution M) (h₄ : IsZero (P.complex.X 4))
  (hP : ∀ n, n<4 → A.leftFiniteProjectiveProperty (P.complex.X n))
  (hExt : ∀ i n, n<3 → ∀ e : Abelian.Ext.{v} M (A.leftRepresentable i) n, e=0)

include h₄ hExt in
theorem leftResolutionDual_first_mono : Mono (A.leftModuleADualMap (P.complex.d 1 0)) := by
  have he := A.leftResolutionDualComplex_exactAt_low P h₄ hExt 0 (by decide)
  rw [HomologicalComplex.exactAt_iff' _ 0 0 1 (by simp) (by simp)] at he
  exact (ShortComplex.exact_iff_mono _
    ((A.leftResolutionDualComplex P).shape 0 0 (by simp))).mp he

noncomputable def leftResolutionDualFourTerm :
    ASGinzburg.FourTermProjectiveResolution (A.leftModuleExtRight M 3) where
  P₀ := A.leftModuleADual (P.complex.X 3)
  P₁ := A.leftModuleADual (P.complex.X 2)
  P₂ := A.leftModuleADual (P.complex.X 1)
  P₃ := A.leftModuleADual (P.complex.X 0)
  projective₀ := A.rightFiniteProjectiveProperty_projective
    (A.leftFiniteProjectiveProperty_dual (hP 3 (by decide)))
  projective₁ := A.rightFiniteProjectiveProperty_projective
    (A.leftFiniteProjectiveProperty_dual (hP 2 (by decide)))
  projective₂ := A.rightFiniteProjectiveProperty_projective
    (A.leftFiniteProjectiveProperty_dual (hP 1 (by decide)))
  projective₃ := A.rightFiniteProjectiveProperty_projective
    (A.leftFiniteProjectiveProperty_dual (hP 0 (by decide)))
  π := A.leftResolutionExtTopProjection P h₄
  d₁ := A.leftModuleADualMap (P.complex.d 3 2)
  d₂ := A.leftModuleADualMap (P.complex.d 2 1)
  d₃ := A.leftModuleADualMap (P.complex.d 1 0)
  epi_π := inferInstance
  mono_d₃ := A.leftResolutionDual_first_mono P h₄ hExt
  d₁_π := A.leftResolutionExtTopProjection_dual_d₃ P h₄
  d₂_d₁ := by
    change A.leftModuleADualFunctor.map (P.complex.d 2 1).op ≫
      A.leftModuleADualFunctor.map (P.complex.d 3 2).op = 0
    rw [← A.leftModuleADualFunctor.map_comp,← op_comp,P.complex.d_comp_d]
    exact A.leftModuleADualFunctor.map_zero _ _
  d₃_d₂ := by
    change A.leftModuleADualFunctor.map (P.complex.d 1 0).op ≫
      A.leftModuleADualFunctor.map (P.complex.d 2 1).op = 0
    rw [← A.leftModuleADualFunctor.map_comp,← op_comp,P.complex.d_comp_d]
    exact A.leftModuleADualFunctor.map_zero _ _
  exact₀ := A.leftResolutionExtTopProjection_exact P h₄
  exact₁ := by
    have he := A.leftResolutionDualComplex_exactAt_low P h₄ hExt 2 (by decide)
    rw [HomologicalComplex.exactAt_iff' _ 1 2 3 (by simp) (by simp)] at he
    exact he
  exact₂ := by
    have he := A.leftResolutionDualComplex_exactAt_low P h₄ hExt 1 (by decide)
    rw [HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp)] at he
    exact he

theorem leftResolutionDualFourTerm_finite (n : ℕ) :
    A.rightFiniteProjectiveProperty ((A.leftResolutionDualFourTerm P h₄ hP hExt).term n) := by
  rcases n with _ | _ | _ | _ | n
  · exact A.leftFiniteProjectiveProperty_dual (hP 3 (by decide))
  · exact A.leftFiniteProjectiveProperty_dual (hP 2 (by decide))
  · exact A.leftFiniteProjectiveProperty_dual (hP 1 (by decide))
  · exact A.leftFiniteProjectiveProperty_dual (hP 0 (by decide))
  · exact A.rightFiniteProjectiveProperty_of_isZero (isZero_zero _)
end ASGinzburg.ZAlgebra
