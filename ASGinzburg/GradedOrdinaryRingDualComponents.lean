import ASGinzburg.GradedOrdinaryRingDualHomogeneousSpaces
import ASGinzburg.HomogeneousLinearMapShiftedComponent
import Mathlib.Algebra.Algebra.Bilinear

/-! Homogeneous components of an actual ring-linear map are themselves
ring-linear. They use the native source decomposition and target
projections, and recover homogeneous maps with their original degree. -/
namespace ASGinzburg.GradedOrdinaryModuleData
open CategoryTheory
open scoped DirectSum ModuleCat.Algebra
universe u v
variable {k : Type u} [Field k] {R : Type v} [Ring R] [Algebra k R]
variable {G : ℤ → Submodule k R} [DirectSum.Decomposition G]
variable (M : GradedOrdinaryModuleData k R G)

noncomputable def ringDualComponentLinear
    (f : ordinaryRingDual R M.ringModule) (q : ℤ) : M.ringModule →ₗ[k] R := by
  letI := M.decomposition
  exact (DirectSum.toModule k ℤ R (fun p =>
    (homogeneousComponent k R G (p + q)).comp
      ((f.restrictScalars k).comp (M.grade p).subtype))).comp
    (DirectSum.decomposeLinearEquiv M.grade).toLinearMap

theorem ringDualComponentLinear_apply_homogeneous
    (f : ordinaryRingDual R M.ringModule) (q p : ℤ)
    (x : M.ringModule) (hx : x ∈ M.grade p) :
    M.ringDualComponentLinear f q x = homogeneousComponent k R G (p + q) (f x) := by
  letI := M.decomposition
  change DirectSum.toModule k ℤ R (fun p =>
    (homogeneousComponent k R G (p + q)).comp
      ((f.restrictScalars k).comp (M.grade p).subtype))
      (DirectSum.decompose M.grade x) = _
  rw [DirectSum.decompose_of_mem M.grade hx]
  exact DirectSum.toModule_lof k (M := fun p => M.grade p)
    (φ := fun p => (homogeneousComponent k R G (p + q)).comp
      ((f.restrictScalars k).comp (M.grade p).subtype)) p ⟨x, hx⟩

theorem ringDualComponentLinear_map_smul
    (hG : ∀ p q : ℤ, ∀ a ∈ G p, ∀ b ∈ G q, a * b ∈ G (p + q))
    (f : ordinaryRingDual R M.ringModule) (q : ℤ) (r : R) (x : M.ringModule) :
    M.ringDualComponentLinear f q (r • x) = r * M.ringDualComponentLinear f q x := by
  letI := M.decomposition
  induction r using DirectSum.Decomposition.inductionOn G with
  | zero => rw [zero_smul, map_zero, zero_mul]
  | @homogeneous p r =>
    induction x using DirectSum.Decomposition.inductionOn M.grade with
    | zero => rw [smul_zero, map_zero, mul_zero]
    | @homogeneous s x =>
      rw [M.ringDualComponentLinear_apply_homogeneous f q (p + s) _
        (M.smul_mem p s r r.property x x.property),
        M.ringDualComponentLinear_apply_homogeneous f q s x x.property,
        f.map_smul]
      have h := homogeneousLinearMap_shifted_component k R R G G
        (LinearMap.mulLeft k (r : R)) p
        (fun t y hy => by
          simpa only [LinearMap.mulLeft_apply, add_comm] using hG p t r r.property y hy)
        (s + q) (f x)
      simpa only [LinearMap.mulLeft_apply, smul_eq_mul, add_assoc, add_comm, add_left_comm]
        using h.symm
    | add x y hx hy => rw [smul_add, map_add, map_add, mul_add, hx, hy]
  | add r s hr hs => rw [add_smul, map_add, add_mul, hr, hs]

noncomputable def ringDualComponent
    (hG : ∀ p q : ℤ, ∀ a ∈ G p, ∀ b ∈ G q, a * b ∈ G (p + q))
    (f : ordinaryRingDual R M.ringModule) (q : ℤ) : ordinaryRingDual R M.ringModule where
  toFun := M.ringDualComponentLinear f q
  map_add' := (M.ringDualComponentLinear f q).map_add
  map_smul' r x := M.ringDualComponentLinear_map_smul hG f q r x

theorem ringDualComponent_apply_homogeneous
    (hG : ∀ p q : ℤ, ∀ a ∈ G p, ∀ b ∈ G q, a * b ∈ G (p + q))
    (f : ordinaryRingDual R M.ringModule) (q p : ℤ)
    (x : M.ringModule) (hx : x ∈ M.grade p) :
    M.ringDualComponent hG f q x = homogeneousComponent k R G (p + q) (f x) :=
  M.ringDualComponentLinear_apply_homogeneous f q p x hx

theorem ringDualComponent_mem
    (hG : ∀ p q : ℤ, ∀ a ∈ G p, ∀ b ∈ G q, a * b ∈ G (p + q))
    (f : ordinaryRingDual R M.ringModule) (q : ℤ) :
    M.ringDualComponent hG f q ∈ M.ringDualGrade q := by
  intro p x hx
  rw [M.ringDualComponent_apply_homogeneous hG f q p x hx]
  exact (DirectSum.decompose G (f x) (p + q)).property

theorem ringDualComponent_of_mem_same
    (hG : ∀ p q : ℤ, ∀ a ∈ G p, ∀ b ∈ G q, a * b ∈ G (p + q))
    (f : ordinaryRingDual R M.ringModule) (q : ℤ) (hf : f ∈ M.ringDualGrade q) :
    M.ringDualComponent hG f q = f := by
  letI := M.decomposition
  apply LinearMap.ext
  intro x
  induction x using DirectSum.Decomposition.inductionOn M.grade with
  | zero => rw [map_zero, map_zero]
  | @homogeneous p x =>
    rw [M.ringDualComponent_apply_homogeneous hG f q p x x.property]
    exact DirectSum.decompose_of_mem_same G (hf p x x.property)
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem ringDualComponent_of_mem_ne
    (hG : ∀ p q : ℤ, ∀ a ∈ G p, ∀ b ∈ G q, a * b ∈ G (p + q))
    (f : ordinaryRingDual R M.ringModule) (p q : ℤ)
    (hf : f ∈ M.ringDualGrade p) (hpq : p ≠ q) :
    M.ringDualComponent hG f q = 0 := by
  letI := M.decomposition
  apply LinearMap.ext
  intro x
  induction x using DirectSum.Decomposition.inductionOn M.grade with
  | zero => rw [map_zero]; rfl
  | @homogeneous s x =>
    rw [M.ringDualComponent_apply_homogeneous hG f q s x x.property]
    exact DirectSum.decompose_of_mem_ne G (hf s x x.property)
      (show s + p ≠ s + q from fun h => hpq (add_left_cancel h))
  | add x y hx hy => rw [map_add, hx, hy]; simp

end ASGinzburg.GradedOrdinaryModuleData
