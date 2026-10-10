import work.ASGinzburgDraft.GradedOrdinaryRingDualComponentNaturality
import ASGinzburg.GradedOrdinaryRingDualInternalGrading

/-! Homogeneous exactness gives genuine ordinary ring-dual exactness.
Finite generation gives the actual finite component support needed to
sum homogeneous boundary preimages; no completion or product is used. -/
namespace ASGinzburg.GradedOrdinaryModuleData
open CategoryTheory
open scoped ModuleCat.Algebra
universe u v
variable {k : Type u} [Field k] {R : Type v} [Ring R] [Algebra k R]
variable {G : ℤ → Submodule k R} [DirectSum.Decomposition G]
variable (M N : GradedOrdinaryModuleData k R G)
variable (hG : ∀ p q : ℤ, ∀ a ∈ G p, ∀ b ∈ G q, a * b ∈ G (p + q))

theorem ringDualComponent_isCycle (a : N.ringModule ⟶ M.ringModule)
    (ha : N.PreservesGrade M a) (f : ordinaryRingDual R M.ringModule)
    (hf : ordinaryRingDualMap R a f = 0) (q : ℤ) :
    ordinaryRingDualMap R a (M.ringDualComponent hG f q) = 0 := by
  rw [N.ringDualComponent_precomp M hG a ha f q, hf]
  exact (N.ringDualComponentMap hG q).map_zero

include hG in
theorem ringDualCycle_eq_zero_of_homogeneous_cycles_eq_zero
    (a : N.ringModule ⟶ M.ringModule) (ha : N.PreservesGrade M a)
    (hExact : ∀ q : ℤ, ∀ g ∈ M.ringDualGrade q,
      ordinaryRingDualMap R a g = 0 → g = 0)
    (f : ordinaryRingDual R M.ringModule) (hf : ordinaryRingDualMap R a f = 0) : f = 0 := by
  apply M.ringDual_eq_zero_of_components_eq_zero hG
  intro q
  exact hExact q _ (M.ringDualComponent_mem hG f q)
    (M.ringDualComponent_isCycle N hG a ha f hf q)

variable (L : GradedOrdinaryModuleData k R G)

include hG in
theorem ringDualCycle_exists_boundary_of_homogeneous_exactness
    [Module.Finite R M.ringModule]
    (a : M.ringModule ⟶ L.ringModule) (b : N.ringModule ⟶ M.ringModule)
    (hb : N.PreservesGrade M b)
    (hExact : ∀ q : ℤ, ∀ g ∈ M.ringDualGrade q,
      ordinaryRingDualMap R b g = 0 →
      ∃ h : ordinaryRingDual R L.ringModule, ordinaryRingDualMap R a h = g)
    (f : ordinaryRingDual R M.ringModule) (hf : ordinaryRingDualMap R b f = 0) :
    ∃ g : ordinaryRingDual R L.ringModule, ordinaryRingDualMap R a g = f := by
  classical
  obtain ⟨s, hs⟩ := M.ringDualComponent_finiteSupport hG f
  have hPreimage (q : ℤ) : ∃ g : ordinaryRingDual R L.ringModule,
      ordinaryRingDualMap R a g = M.ringDualComponent hG f q :=
    hExact q _ (M.ringDualComponent_mem hG f q)
      (M.ringDualComponent_isCycle N hG b hb f hf q)
  choose g hg using hPreimage
  refine ⟨∑ q ∈ s, g q, ?_⟩
  rw [map_sum]
  simp only [hg]
  exact M.ringDual_sum_components hG f s hs

end ASGinzburg.GradedOrdinaryModuleData
