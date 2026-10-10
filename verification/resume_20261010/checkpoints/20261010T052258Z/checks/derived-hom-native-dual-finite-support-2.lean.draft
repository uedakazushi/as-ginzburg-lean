import work.ASGinzburgDraft.GradedOrdinaryRingDualComponentMaps
import work.ASGinzburgDraft.GradedOrdinaryFiniteHomogeneousGenerators

/-! Actual ring-linear maps from a finitely generated graded module have
uniform finite homogeneous support. A finite homogeneous generating
family supplies the finite set of possible degree differences. -/
namespace ASGinzburg.GradedOrdinaryModuleData
open scoped DirectSum ModuleCat.Algebra
universe u v
variable {k : Type u} [Field k] {R : Type v} [Ring R] [Algebra k R]
variable {G : ℤ → Submodule k R} [DirectSum.Decomposition G]
variable (M : GradedOrdinaryModuleData k R G)
variable (hG : ∀ p q : ℤ, ∀ a ∈ G p, ∀ b ∈ G q, a * b ∈ G (p + q))

theorem ringDualComponent_finiteSupport [Module.Finite R M.ringModule]
    (f : ordinaryRingDual R M.ringModule) :
    ∃ s : Finset ℤ, ∀ q : ℤ, q ∉ s → M.ringDualComponent hG f q = 0 := by
  classical
  obtain ⟨I, hI, d, x, hhom, hx⟩ := M.exists_finite_homogeneous_generating_family
  letI := hI
  let s := Finset.univ.biUnion fun i : I =>
    (DirectSum.decompose G (f (x i))).support.image (fun p : ℤ => p - d i)
  refine ⟨s, ?_⟩
  intro q hq
  apply LinearMap.ext_on_range hx
  intro i
  rw [M.ringDualComponent_apply_homogeneous hG f q (d i) (x i) (hhom i)]
  have hp : d i + q ∉ (DirectSum.decompose G (f (x i))).support := by
    intro hp
    apply hq
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
      Finset.mem_image.mpr ⟨d i + q, hp, by omega⟩⟩
  change (DirectSum.decompose G (f (x i)) (d i + q) : R) = 0
  have hz : DirectSum.decompose G (f (x i)) (d i + q) = 0 :=
    DFinsupp.notMem_support_iff.mp hp
  exact congrArg (fun y : G (d i + q) => (y : R)) hz

end ASGinzburg.GradedOrdinaryModuleData
