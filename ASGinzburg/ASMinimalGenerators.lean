import ASGinzburg.ASGenerators

/-! Exactness and minimality identify the kernel and positive-product image
of the first AS differential, as required in Proposition 1.2. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k} {Q : CutQuiver}
namespace ASResolution
variable {w : Q.LiftVertex} (R : A.ASResolution Q w)

theorem d₁_component_ker_le_radical (i : ℤ) :
    LinearMap.ker ((A.rightModuleEvaluation i).map R.d₁).hom ≤
      A.positiveActionSpan (A.asResolutionTerm₁ Q w) i := by
  intro x hx
  have hex := (ShortComplex.moduleCat_exact_iff _).mp
    (R.exact₁.map (A.rightModuleEvaluation i))
  obtain ⟨y,rfl⟩ := hex x hx
  exact R.minimal₂ i y

theorem d₁_component_eq_zero_of_ge (i : ℤ) (hi : Q.height w ≤ i)
    (x : (A.rightModuleEvaluation i).obj (A.asResolutionTerm₁ Q w)) :
    ((A.rightModuleEvaluation i).map R.d₁).hom x = 0 := by
  have h := R.minimal₁ i x
  rw [← A.representableRadical_eq_positiveActionSpan] at h
  simpa [representableRadical,not_lt.mpr hi] using h

theorem d₁_component_action (i l : ℤ) (a : A.Hom i l)
    (x : (A.rightModuleEvaluation l).obj (A.asResolutionTerm₁ Q w)) :
    ((A.rightModuleEvaluation i).map R.d₁).hom
      ((A.asResolutionTerm₁ Q w).obj.map (show (⟨i⟩ : A.Obj) ⟶ ⟨l⟩ from a).op x) =
      A.comp (((A.rightModuleEvaluation l).map R.d₁).hom x) a := by
  exact (congrArg (fun f => f.hom x) (R.d₁.naturality
    (show (⟨i⟩ : A.Obj) ⟶ ⟨l⟩ from a).op))

theorem d₁_radical_image (i : ℤ) :
    Submodule.map ((A.rightModuleEvaluation i).map R.d₁).hom
      (A.positiveActionSpan (A.asResolutionTerm₁ Q w) i) =
      Submodule.span k (A.products i (Q.height w)) := by
  apply le_antisymm
  · rintro y ⟨x,hx,rfl⟩
    induction hx using Submodule.span_induction with
    | mem z hz =>
      rcases hz with ⟨l,hil,x,a,rfl⟩
      rw [R.d₁_component_action]
      by_cases hl : l < Q.height w
      · exact Submodule.subset_span ⟨l,hil,hl,a,
          ((A.rightModuleEvaluation l).map R.d₁).hom x,rfl⟩
      · rw [R.d₁_component_eq_zero_of_ge l (le_of_not_gt hl)]
        simp
    | zero => simp
    | add x y hx hy ihx ihy => simpa only [map_add] using
        (Submodule.span k (A.products i (Q.height w))).add_mem ihx ihy
    | smul c x hx ih => simpa only [map_smul] using
        (Submodule.span k (A.products i (Q.height w))).smul_mem c ih
  · apply Submodule.span_le.mpr
    rintro y ⟨l,hil,hlj,a,b,rfl⟩
    obtain ⟨x,hx⟩ := R.d₁_component_surjective l hlj b
    refine ⟨(A.asResolutionTerm₁ Q w).obj.map
      (show (⟨i⟩ : A.Obj) ⟶ ⟨l⟩ from a).op x,?_,?_⟩
    · exact Submodule.subset_span ⟨l,hil,x,a,rfl⟩
    · rw [R.d₁_component_action,hx]

end ASResolution
end ASGinzburg.ZAlgebra
