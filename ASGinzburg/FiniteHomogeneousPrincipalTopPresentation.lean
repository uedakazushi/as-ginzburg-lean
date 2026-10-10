import ASGinzburg.FiniteHomogeneousIdempotentQuotientBasisLifts
import ASGinzburg.HomogeneousPrincipalTopPresentation

/-! Finite-dimensional actual radical tops give finite-index homogeneous
principal-projective presentations with genuine finite ordinary sources. -/
namespace ASGinzburg
open CategoryTheory
open scoped DirectSum ModuleCat.Algebra
universe u v
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (A : ℤ → Submodule k R) [DirectSum.Decomposition A]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable (ε : R →ₐ[k] (ι → k)) (e : ι → R)
variable (M : ModuleCat.{v} R) (G : ℤ → Submodule k M) [DirectSum.Decomposition G]
variable [Module.Finite k (M ⧸ ordinaryIdealActionSpan k R M (RingHom.ker ε.toRingHom))]

theorem exists_finite_homogeneous_principal_top_presentation
    (hMul : ∀ p q : ℤ, ∀ r ∈ A p, ∀ s ∈ A q, r*s ∈ A (p+q))
    (hA : ∀ q : ℤ, q<0 → A q=⊥)
    (he : ∀ i, e i*e i=e i) (horth : ∀ i j, i≠j → e i*e j=0)
    (hsum : ∑ i, e i=1) (he0 : ∀ i, e i ∈ A 0) (hε : ∀ i, ε (e i)=Pi.single i 1)
    (hAct : ∀ p q : ℤ, ∀ r ∈ A p, ∀ x ∈ G q, r • x ∈ G (p+q))
    (hJ : ∀ q x, x ∈ ordinaryIdealActionSpan k R M (RingHom.ker ε.toRingHom) →
      (DirectSum.decompose G x q : M) ∈ ordinaryIdealActionSpan k R M (RingHom.ker ε.toRingHom))
    (b : ℤ) (hb : ∀ q, q<b → G q=⊥) :
    ∃ (γ : Type v) (c : γ → ι) (t : γ → ℤ) (x : γ → M),
      Finite γ ∧
      letI : DecidableEq γ := Classical.decEq γ
      let f := principalIdempotentBasisCoverMap R (fun a => e (c a)) M x
      let P := principalIdempotentCoproductModule R (fun a => e (c a))
      let H := principalHomogeneousCoverOrdinaryGrade k R A (fun a => e (c a)) t
      Module.Finite R P ∧ Projective P ∧ DirectSum.IsInternal H ∧
        (∀ q, q<b → H q=⊥) ∧
        (∀ p q : ℤ, ∀ r ∈ A p, ∀ y ∈ H q, r • y ∈ H (p+q)) ∧
        (∀ q p, p ∈ H q → f p ∈ G q) ∧
        (∀ p : P, f p=0 → p ∈ ordinaryIdealActionSpan k R P (RingHom.ker ε.toRingHom)) ∧
        (∀ y : M ⧸ ordinaryIdealActionSpan k R M (RingHom.ker ε.toRingHom),
          ∃ p : P, (ordinaryIdealActionSpan k R M (RingHom.ker ε.toRingHom)).mkQ (f p)=y) := by
  classical
  let J := RingHom.ker ε.toRingHom
  let S := ordinaryIdealActionSubmodule k R M J
  let E := ordinaryIdealActionTopRestrictScalarsEquiv k R M J
  letI : Module.Finite k (M ⧸ S) := Module.Finite.equiv E
  have heG : ∀ i q, ∀ x : M, x ∈ G q → e i • x ∈ G q := by
    intro i q x hx
    simpa only [zero_add] using hAct 0 q (e i) (he0 i) x hx
  obtain ⟨γ,c,t,B₀,x,hγ,hx,ht⟩ :=
    exists_finite_homogeneous_idempotent_quotient_basis_lifts k R M G S e he horth hsum hJ heG b hb
  letI : Finite γ := hγ
  let B := B₀.map E.symm
  have hB : ∀ a, (ordinaryIdealActionSpan k R M J).mkQ (x a)=B a := by
    intro a
    rw [Module.Basis.map_apply]
    apply E.injective
    rw [E.apply_symm_apply, ordinaryIdealActionTopRestrictScalarsEquiv_mkQ]
    exact (hx a).2.2
  let ec : γ → R := fun a => e (c a)
  let P := principalIdempotentCoproductModule R ec
  let H := principalHomogeneousCoverOrdinaryGrade k R A ec t
  letI : DirectSum.Decomposition H :=
    principalHomogeneousCoverOrdinaryGradeDecomposition k R A ec t hMul (fun a => he0 (c a))
  refine ⟨γ,c,t,x,hγ,inferInstance,
    principalIdempotentCoproductModule_projective R ec (fun a => he (c a)),
    DirectSum.Decomposition.isInternal H,?_,?_,?_,?_,?_⟩
  · intro q hq
    exact principalHomogeneousCoverOrdinaryGrade_eq_bot_of_lower_bound k R A ec t hA b ht q hq
  · intro p q r hr y hy
    exact principalHomogeneousCoverOrdinaryGrade_smul_mem k R A ec t hMul p q r hr y hy
  · intro q p hp
    exact principalHomogeneousCoverOrdinaryMap_mem_grade k R A ec t M G hAct x
      (fun a => (hx a).1) q p hp
  · intro p hp
    have hmin := principalIdempotentBasisCover_kernel_minimal k R ε ec c M x
      (fun a => he (c a)) (fun a => hε (c a)) (fun a => (hx a).2.1) B hB p hp
    exact ordinaryIdealActionSpan_map_mem k R J
      (LinearMap.id : (⨁ a, principalIdempotentModule R (ec a)) →ₗ[R] P) hmin
  · intro y
    exact principalIdempotentBasisCover_top_surjective k R ε ec c M x
      (fun a => he (c a)) (fun a => hε (c a)) (fun a => (hx a).2.1) B hB y

end ASGinzburg
