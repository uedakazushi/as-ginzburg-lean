import ASGinzburg.ModuleCochainHomologyClasses
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! Every value of the actual connecting homomorphism has a cycle
representative whose inclusion is the differential of an actual lift. -/
namespace ASGinzburg
open CategoryTheory
universe u
variable {k : Type u} [Field k]

theorem moduleCochainConnecting_exists
    {S : ShortComplex (CochainComplex (ModuleCat.{u} k) ℤ)}
    (hS : S.ShortExact) (i : ℤ) (y : S.X₃.homology i) :
    ∃ x₂ : S.X₂.X i, ∃ x₁ : S.X₁.X (i+1),
      ∃ hx₁ : S.f.f (i+1) x₁=S.X₂.d i (i+1) x₂,
      hS.δ i (i+1) (by simp) y=
        moduleCochainHomologyClass S.X₁ (i+1) x₁
          (hS.d_eq_zero_of_f_eq_d_apply i (i+1) x₂ x₁ hx₁ (i+1+1)) := by
  obtain ⟨x₃,hx₃,hy⟩ := moduleCochainHomologyClass_exists S.X₃ i y
  have hs := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS
  haveI : Epi (S.g.f i) := (hs i).epi_g
  obtain ⟨x₂,hx₂⟩ := (ModuleCat.epi_iff_surjective (S.g.f i)).mp inferInstance x₃
  have hz : S.g.f (i+1) (S.X₂.d i (i+1) x₂)=0 := by
    have hc := congrArg (fun f => f x₂) (S.g.comm i (i+1))
    simpa only [ModuleCat.comp_apply,hx₂,hx₃] using hc.symm
  obtain ⟨x₁,hx₁⟩ := (ShortComplex.moduleCat_exact_iff _).mp (hs (i+1)).exact _ hz
  refine ⟨x₂,x₁,hx₁,?_⟩
  rw [←hy]
  exact moduleCochainConnecting_class hS i x₃ hx₃ x₂ hx₂ x₁ hx₁

end ASGinzburg
