import ASGinzburg.PeriodCutEnvelopingDegreeDecomposition
import ASGinzburg.PeriodCutEnvelopingAugmentationComparison

/-! The degree-zero block of the actual unsigned enveloping algebra is
the ordinary enveloping algebra of the native degree-zero cut ring. Its
linear inclusion agrees with the genuine algebra map induced by the
degree-zero inclusion. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open scoped TensorProduct DirectSum
universe u v w
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k} {p : ℤ}
variable (E : A.PeriodIso p) {ι : Type w} [Fintype ι] (vertex : ι → ℤ)

def cutEnvelopingDegreePairZero : CutEnvelopingDegreePairs 0 := ⟨(0,0), rfl⟩

theorem cutEnvelopingDegreePairZero_unique (d : CutEnvelopingDegreePairs 0) :
    d = cutEnvelopingDegreePairZero := by
  apply Subtype.ext
  obtain ⟨hi,hj⟩ := Nat.add_eq_zero_iff.mp d.property
  exact Prod.ext hi hj

noncomputable def cutEnvelopingZeroTensorDegreeEquiv :
    E.CutEnvelopingBlock vertex (0,0) ≃ₗ[k] E.CutEnvelopingDegreeBlock vertex 0 :=
  { DirectSum.lof k (CutEnvelopingDegreePairs 0)
      (fun d => E.CutEnvelopingBlock vertex d.val) cutEnvelopingDegreePairZero with
    invFun := fun x => x cutEnvelopingDegreePairZero
    left_inv := fun x => DirectSum.of_eq_same _ x
    right_inv := fun x => by
      apply DFinsupp.ext
      intro d
      rw [cutEnvelopingDegreePairZero_unique d]
      exact DirectSum.of_eq_same _ _ }

omit [Fintype ι] in
theorem cutEnvelopingZeroTensorDegreeEquiv_apply
    (x : E.CutEnvelopingBlock vertex (0,0)) :
    E.cutEnvelopingZeroTensorDegreeEquiv vertex x =
      DirectSum.lof k (CutEnvelopingDegreePairs 0)
        (fun d => E.CutEnvelopingBlock vertex d.val) cutEnvelopingDegreePairZero x := rfl

theorem cutEnvelopingDegreeEquiv_zeroHomogeneousInclusion
    (x : E.CutEnvelopingBlock vertex (0,0)) :
    E.cutEnvelopingDegreeEquiv vertex
        (E.cutEnvelopingHomogeneousInclusion vertex (0,0) x) =
      DirectSum.lof k ℕ (E.CutEnvelopingDegreeBlock vertex) 0
        (E.cutEnvelopingZeroTensorDegreeEquiv vertex x) := by
  apply DFinsupp.ext
  intro n
  apply DFinsupp.ext
  intro d
  rw [cutEnvelopingDegreeEquiv_apply, cutEnvelopingBigradingEquiv_inclusion]
  by_cases hn : n = 0
  · subst n
    rw [cutEnvelopingDegreePairZero_unique d]
    simp only [DirectSum.lof_eq_of, DirectSum.of_eq_same,
      cutEnvelopingZeroTensorDegreeEquiv_apply, cutEnvelopingDegreePairZero]
  · have hd : d.val ≠ (0,0) := by
      intro h
      have hsum := d.property
      rw [h] at hsum
      exact hn hsum.symm
    simp only [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ hn,
      DirectSum.of_eq_of_ne _ _ _ hd, DFinsupp.zero_apply]

theorem cutEnvelopingDegreeInclusion_zeroTensorDegreeEquiv
    (x : E.CutEnvelopingBlock vertex (0,0)) :
    E.cutEnvelopingDegreeInclusion vertex 0
        (E.cutEnvelopingZeroTensorDegreeEquiv vertex x) =
      E.cutEnvelopingHomogeneousInclusion vertex (0,0) x := by
  apply (E.cutEnvelopingDegreeEquiv vertex).injective
  rw [cutEnvelopingDegreeEquiv_inclusion,
    cutEnvelopingDegreeEquiv_zeroHomogeneousInclusion]

theorem cutEnvelopingDegreeZeroInclusion_injective :
    Function.Injective (E.cutEnvelopingDegreeInclusion vertex 0) := by
  intro x y h
  have h' := congrArg (E.cutEnvelopingDegreeEquiv vertex) h
  rw [cutEnvelopingDegreeEquiv_inclusion, cutEnvelopingDegreeEquiv_inclusion] at h'
  exact DirectSum.of_injective _ h'

variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices : ℤ))

noncomputable def cutEnvelopingDegreeZeroEquiv :
    AlgebraEnvelopingRing k
        (E.CutGradedBlock (fun i : Q.Vertex => (i.val : ℤ)) 0) ≃ₗ[k]
      E.CutEnvelopingDegreeBlock (fun i : Q.Vertex => (i.val : ℤ)) 0 :=
  (TensorProduct.congr
    (LinearEquiv.refl k (E.CutGradedBlock (fun i : Q.Vertex => (i.val : ℤ)) 0))
    (MulOpposite.opLinearEquiv k).symm).trans
      (E.cutEnvelopingZeroTensorDegreeEquiv (fun i : Q.Vertex => (i.val : ℤ)))

theorem cutEnvelopingDegreeZeroEquiv_tmul
    (a b : E.CutGradedBlock (fun i : Q.Vertex => (i.val : ℤ)) 0) :
    E.cutEnvelopingDegreeZeroEquiv Q (a ⊗ₜ[k] MulOpposite.op b) =
      E.cutEnvelopingZeroTensorDegreeEquiv (fun i : Q.Vertex => (i.val : ℤ))
        (a ⊗ₜ[k] b) := rfl

set_option synthInstance.maxHeartbeats 200000 in
theorem cutEnvelopingDegreeInclusion_degreeZeroEquiv
    (x : AlgebraEnvelopingRing k
      (E.CutGradedBlock (fun i : Q.Vertex => (i.val : ℤ)) 0)) :
    E.cutEnvelopingDegreeInclusion (fun i : Q.Vertex => (i.val : ℤ)) 0
        (E.cutEnvelopingDegreeZeroEquiv Q x) = E.cutEnvelopingZeroInclusion Q x := by
  let f := (E.cutEnvelopingDegreeInclusion (fun i : Q.Vertex => (i.val : ℤ)) 0).comp
    (E.cutEnvelopingDegreeZeroEquiv Q).toLinearMap
  let g := (E.cutEnvelopingZeroInclusion Q).toLinearMap
  change f x = g x
  induction x using TensorProduct.induction_on with
  | zero => exact f.map_zero.trans g.map_zero.symm
  | tmul a b =>
      obtain ⟨b,rfl⟩ := MulOpposite.op_surjective b
      change E.cutEnvelopingDegreeInclusion (fun i : Q.Vertex => (i.val : ℤ)) 0
          (E.cutEnvelopingDegreeZeroEquiv Q (a ⊗ₜ[k] MulOpposite.op b)) =
        E.cutEnvelopingZeroInclusion Q (a ⊗ₜ[k] MulOpposite.op b)
      rw [cutEnvelopingDegreeZeroEquiv_tmul,
        cutEnvelopingDegreeInclusion_zeroTensorDegreeEquiv,
        cutEnvelopingHomogeneousInclusion_tmul, cutEnvelopingZeroInclusion_tmul]
  | add x y hx hy =>
      exact (f.map_add x y).trans
        ((congrArg₂ (· + ·) hx hy).trans (g.map_add x y).symm)

set_option synthInstance.maxHeartbeats 200000 in
theorem cutEnvelopingDegreeZeroLinearMap_eq :
    (E.cutEnvelopingDegreeInclusion (fun i : Q.Vertex => (i.val : ℤ)) 0).comp
        (E.cutEnvelopingDegreeZeroEquiv Q).toLinearMap =
      (E.cutEnvelopingZeroInclusion Q).toLinearMap := by
  apply LinearMap.ext
  intro x
  exact E.cutEnvelopingDegreeInclusion_degreeZeroEquiv Q x

theorem cutEnvelopingZeroInclusion_injective :
    Function.Injective (E.cutEnvelopingZeroInclusion Q) := by
  intro x y h
  apply (E.cutEnvelopingDegreeZeroEquiv Q).injective
  apply E.cutEnvelopingDegreeZeroInclusion_injective (fun i : Q.Vertex => (i.val : ℤ))
  rw [cutEnvelopingDegreeInclusion_degreeZeroEquiv,
    cutEnvelopingDegreeInclusion_degreeZeroEquiv]
  exact h

noncomputable def cutEnvelopingDegreeZeroSubalgebra :
    Subalgebra k (AlgebraEnvelopingRing k
      (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))) :=
  (E.cutEnvelopingZeroInclusion Q).range

set_option synthInstance.maxHeartbeats 200000 in
theorem cutEnvelopingDegreeZeroRange_eq_subalgebra :
    LinearMap.range
        (E.cutEnvelopingDegreeInclusion (fun i : Q.Vertex => (i.val : ℤ)) 0) =
      (E.cutEnvelopingDegreeZeroSubalgebra Q).toSubmodule := by
  ext x
  change (∃ a, E.cutEnvelopingDegreeInclusion (fun i : Q.Vertex => (i.val : ℤ)) 0 a = x) ↔
    ∃ a, E.cutEnvelopingZeroInclusion Q a = x
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨(E.cutEnvelopingDegreeZeroEquiv Q).symm a, ?_⟩
    rw [← E.cutEnvelopingDegreeInclusion_degreeZeroEquiv Q,
      LinearEquiv.apply_symm_apply]
    exact ha
  · rintro ⟨a,ha⟩
    exact ⟨E.cutEnvelopingDegreeZeroEquiv Q a,
      (E.cutEnvelopingDegreeInclusion_degreeZeroEquiv Q a).trans ha⟩

theorem cutEnvelopingDegreeZeroRange_one :
    (1 : AlgebraEnvelopingRing k
      (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))) ∈
      LinearMap.range
        (E.cutEnvelopingDegreeInclusion (fun i : Q.Vertex => (i.val : ℤ)) 0) := by
  rw [E.cutEnvelopingDegreeZeroRange_eq_subalgebra Q]
  exact (E.cutEnvelopingDegreeZeroSubalgebra Q).one_mem

set_option synthInstance.maxHeartbeats 200000 in
theorem cutEnvelopingDegreeZeroRange_mul
    {x y : AlgebraEnvelopingRing k
      (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))}
    (hx : x ∈ LinearMap.range
      (E.cutEnvelopingDegreeInclusion (fun i : Q.Vertex => (i.val : ℤ)) 0))
    (hy : y ∈ LinearMap.range
      (E.cutEnvelopingDegreeInclusion (fun i : Q.Vertex => (i.val : ℤ)) 0)) :
    x*y ∈ LinearMap.range
      (E.cutEnvelopingDegreeInclusion (fun i : Q.Vertex => (i.val : ℤ)) 0) := by
  rw [E.cutEnvelopingDegreeZeroRange_eq_subalgebra Q] at hx hy ⊢
  exact (E.cutEnvelopingDegreeZeroSubalgebra Q).mul_mem hx hy

noncomputable def cutEnvelopingDegreeZeroSubalgebraEquiv :
    AlgebraEnvelopingRing k
        (E.CutGradedBlock (fun i : Q.Vertex => (i.val : ℤ)) 0) ≃ₐ[k]
      E.cutEnvelopingDegreeZeroSubalgebra Q :=
  AlgEquiv.ofInjective (E.cutEnvelopingZeroInclusion Q)
    (E.cutEnvelopingZeroInclusion_injective Q)

theorem cutEnvelopingDegreeZeroSubalgebraEquiv_apply
    (x : AlgebraEnvelopingRing k
      (E.CutGradedBlock (fun i : Q.Vertex => (i.val : ℤ)) 0)) :
    (E.cutEnvelopingDegreeZeroSubalgebraEquiv Q x : AlgebraEnvelopingRing k
      (E.CutGradedRing (fun i : Q.Vertex => (i.val : ℤ)))) =
      E.cutEnvelopingZeroInclusion Q x := rfl

end ASGinzburg.ZAlgebra.PeriodIso
