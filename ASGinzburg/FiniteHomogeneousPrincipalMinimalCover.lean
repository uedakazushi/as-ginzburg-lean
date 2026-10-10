import ASGinzburg.FiniteHomogeneousPrincipalTopPresentation
import ASGinzburg.GradedNilpotentActionSpanHomogeneity
import ASGinzburg.GradedNilpotentCoverSurjectivity
import ASGinzburg.GradedLinearMapRange

/-! Graded Nakayama makes the constructed finite principal presentation
an actual minimal projective cover. Finiteness is derived from the actual
radical top and not assumed for the module or the projective source. -/
namespace ASGinzburg
open CategoryTheory
open scoped DirectSum ModuleCat.Algebra
universe u v w z
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (A : ℤ → Submodule k R) [DirectSum.Decomposition A]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable (ε : R →ₐ[k] (ι → k)) (e : ι → R)
variable (M : ModuleCat.{v} R) (G : ℤ → Submodule k M) [DirectSum.Decomposition G]
variable [Module.Finite k (M ⧸ ordinaryIdealActionSpan k R M (RingHom.ker ε.toRingHom))]
variable (R₀ : Type w) [Ring R₀] [Algebra k R₀] [SMul R₀ R]
variable [Module R₀ M] [IsScalarTower k R₀ M] [IsScalarTower R₀ R M]
variable (h₀ : ∀ q (r : R₀) (x : M), x ∈ G q → r • x ∈ G q)
variable {τ : Type z} (d : τ → ℕ) (a : τ → R) (f : τ → M →ₗ[k] M)
variable (I₀ : Ideal R₀)

include h₀ in
theorem exists_finite_homogeneous_principal_minimal_cover
    (hMul : ∀ p q : ℤ, ∀ r ∈ A p, ∀ s ∈ A q, r*s ∈ A (p+q))
    (hA : ∀ q : ℤ, q<0 → A q=⊥)
    (he : ∀ i, e i*e i=e i) (horth : ∀ i j, i≠j → e i*e j=0)
    (hsum : ∑ i, e i=1) (he0 : ∀ i, e i ∈ A 0) (hε : ∀ i, ε (e i)=Pi.single i 1)
    (hAct : ∀ p q : ℤ, ∀ r ∈ A p, ∀ x ∈ G q, r • x ∈ G (p+q))
    (ha : ∀ t (x : M), f t x=a t • x)
    (N₀ : ℕ) (hN₀ : I₀^N₀=⊥) (hd : ∀ t, 0<d t)
    (hf : ∀ t q (x : M), x ∈ G q → f t x ∈ G (q+(d t:ℤ)))
    (hSpan : ordinaryIdealActionSpan k R M (RingHom.ker ε.toRingHom) =
      gradedNilpotentActionSpan k R₀ M f I₀)
    (b : ℤ) (hb : ∀ q, q<b → G q=⊥) :
    ∃ (P : ModuleCat.{v} R) (H : ℤ → Submodule k P) (π : P ⟶ M),
      Module.Finite R P ∧ Projective P ∧ DirectSum.IsInternal H ∧
        (∀ q, q<b → H q=⊥) ∧
        (∀ p q : ℤ, ∀ r ∈ A p, ∀ x ∈ H q, r • x ∈ H (p+q)) ∧
        (∀ q x, x ∈ H q → π x ∈ G q) ∧ Epi π ∧
        (∀ p : P, π p=0 → p ∈ ordinaryIdealActionSpan k R P (RingHom.ker ε.toRingHom)) := by
  classical
  have hJ : ∀ q x, x ∈ ordinaryIdealActionSpan k R M (RingHom.ker ε.toRingHom) →
      (DirectSum.decompose G x q : M) ∈ ordinaryIdealActionSpan k R M (RingHom.ker ε.toRingHom) := by
    intro q x hx
    rw [hSpan] at hx ⊢
    exact gradedNilpotentActionSpan_linear_homogeneous k R₀ M d f I₀ G h₀ hf q hx
  obtain ⟨γ,c,t,x,_hγ,hFinite,hP,hH,hbP,hActP,hπ,hker,hTop⟩ :=
    exists_finite_homogeneous_principal_top_presentation k R A ε e M G
      hMul hA he horth hsum he0 hε hAct hJ b hb
  let ec : γ → R := fun i => e (c i)
  let P := principalIdempotentCoproductModule R ec
  let H := principalHomogeneousCoverOrdinaryGrade k R A ec t
  let π : P ⟶ M := ModuleCat.ofHom (principalIdempotentBasisCoverMap R ec M x)
  letI : DirectSum.Decomposition H := hH.chooseDecomposition
  have hRange : ∀ q (y : M), y ∈ LinearMap.range π.hom →
      (DirectSum.decompose G y q : M) ∈ LinearMap.range π.hom := by
    intro q y hy
    exact homogeneousLinearMap_range_component_mem k P M H G (π.hom.restrictScalars k)
      hπ q y hy
  have hTopRad : ∀ y : M ⧸ gradedNilpotentActionSpan k R₀ M f I₀,
      ∃ p : P, (gradedNilpotentActionSpan k R₀ M f I₀).mkQ (π p)=y := by
    rw [← hSpan]
    exact hTop
  have hSurj := linearMap_surjective_of_homogeneous_radical_top k R₀ M G h₀ d f I₀ R P
    π.hom hRange a ha N₀ hN₀ hd hf b hb hTopRad
  have hEpi : Epi π := (ModuleCat.epi_iff_surjective π).mpr hSurj
  exact ⟨P,H,π,hFinite,hP,hH,hbP,hActP,hπ,hEpi,hker⟩

end ASGinzburg
