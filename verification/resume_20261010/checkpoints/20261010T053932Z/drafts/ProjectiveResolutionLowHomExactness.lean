import ASGinzburg.ProjectiveResolutionHomExactness

/-! Actual Ext vanishing in degree two implies exactness of the actual
Hom complex without a terminal-zero hypothesis on its resolution. -/
namespace CategoryTheory.ProjectiveResolution
open CategoryTheory.Limits
universe u v t
variable {k : Type t} [Field k] {C : Type u} [Category.{v} C]
  [Abelian C] [Linear k C] [HasExt.{v} C]
variable {X : C} (P : ProjectiveResolution X) (N : C)

theorem hom_two_exact_of_actual_ext_two_zero
    (hExt : ∀ e : Abelian.Ext.{v} X N 2, e = 0)
    (f : P.complex.X 2 ⟶ N) (hf : P.complex.d 3 2 ≫ f = 0) :
    ∃ g : P.complex.X 1 ⟶ N, P.complex.d 2 1 ≫ g = f := by
  obtain ⟨y, hy⟩ := CokernelCofork.IsColimit.desc' P.exact_d₃_secondCover.gIsCokernel f hf
  change P.secondCover ≫ y = f at hy
  have hKernel : ∀ e : Abelian.Ext.{v} (kernel (P.π.f 0)) N 1, e = 0 := by
    intro e
    obtain ⟨z, hz⟩ := Abelian.Ext.contravariant_sequence_exact₁ P.shortExact₀ N e
      (show 1 + 1 = 2 from rfl) (hExt _)
    haveI : Projective (P.complex.X 0) := P.projective 0
    rw [Abelian.Ext.eq_zero_of_projective z, Abelian.Ext.comp_zero] at hz
    exact hz.symm
  obtain ⟨g, hg⟩ := ASGinzburg.hom_extension_of_ext_one_zero P.shortExact₁ N hKernel y
  refine ⟨g, ?_⟩
  rw [← P.secondCover_ι, Category.assoc, hg, hy]

theorem homComplex_exactAt_low_of_actual_ext_zero
    (n : ℕ) (hn : n < 3) (hExt : ∀ e : Abelian.Ext.{v} X N n, e = 0) :
    (P.homComplex (k := k) N).ExactAt n := by
  rcases n with _ | _ | _ | n
  · exact P.homComplex_exactAt_zero_of_ext_zero N hExt
  · exact P.homComplex_exactAt_one_of_ext_zero N hExt
  · exact (P.homComplex_exactAt_succ_iff (k := k) N 1).mpr
      (P.hom_two_exact_of_actual_ext_two_zero N hExt)
  · omega

end CategoryTheory.ProjectiveResolution
