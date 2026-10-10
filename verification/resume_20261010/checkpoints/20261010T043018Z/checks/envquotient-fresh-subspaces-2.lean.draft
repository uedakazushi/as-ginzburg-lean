import work.ASGinzburgDraft.PeriodCutEnvelopingDegreeDecomposition
import work.ASGinzburgDraft.LinearDirectSumHomogeneousDecomposition

/-! The actual ordinary enveloping algebra has actual total-degree
homogeneous subspaces, forming an internal direct sum. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open scoped TensorProduct DirectSum
universe u v w
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k} {p : ℤ}
variable (E : A.PeriodIso p) {ι : Type w} [Fintype ι] (vertex : ι → ℤ)

noncomputable def cutEnvelopingHomogeneousSubspace (n : ℕ) :
    Submodule k (AlgebraEnvelopingRing k (E.CutGradedRing vertex)) :=
  LinearMap.range (E.cutEnvelopingDegreeInclusion vertex n)

theorem cutEnvelopingDegreeInclusion_injective (n : ℕ) :
    Function.Injective (E.cutEnvelopingDegreeInclusion vertex n) :=
  linearDirectSumHomogeneousInclusion_injective k _
    (E.CutEnvelopingDegreeBlock vertex) (E.cutEnvelopingDegreeEquiv vertex) n

theorem cutEnvelopingHomogeneousSubspaces_isInternal :
    DirectSum.IsInternal (E.cutEnvelopingHomogeneousSubspace vertex) :=
  linearDirectSumHomogeneousSubspaces_isInternal k _
    (E.CutEnvelopingDegreeBlock vertex) (E.cutEnvelopingDegreeEquiv vertex)

noncomputable instance cutEnvelopingHomogeneousDecomposition :
    DirectSum.Decomposition (E.cutEnvelopingHomogeneousSubspace vertex) :=
  (E.cutEnvelopingHomogeneousSubspaces_isInternal vertex).chooseDecomposition

theorem cutEnvelopingDegreeInclusion_mem_homogeneousSubspace (n : ℕ)
    (x : E.CutEnvelopingDegreeBlock vertex n) :
    E.cutEnvelopingDegreeInclusion vertex n x ∈ E.cutEnvelopingHomogeneousSubspace vertex n :=
  LinearMap.mem_range_self _ x

noncomputable def cutEnvelopingHomogeneousProjection (n : ℕ) :
    AlgebraEnvelopingRing k (E.CutGradedRing vertex) →ₗ[k]
      AlgebraEnvelopingRing k (E.CutGradedRing vertex) :=
  (E.cutEnvelopingDegreeInclusion vertex n).comp
    ((DirectSum.component k ℕ (E.CutEnvelopingDegreeBlock vertex) n).comp
      (E.cutEnvelopingDegreeEquiv vertex).toLinearMap)

theorem cutEnvelopingHomogeneousProjection_mem (n : ℕ)
    (x : AlgebraEnvelopingRing k (E.CutGradedRing vertex)) :
    E.cutEnvelopingHomogeneousProjection vertex n x ∈
      E.cutEnvelopingHomogeneousSubspace vertex n :=
  E.cutEnvelopingDegreeInclusion_mem_homogeneousSubspace vertex n _

theorem cutEnvelopingHomogeneousProjection_of_inclusion_same (n : ℕ)
    (x : E.CutEnvelopingDegreeBlock vertex n) :
    E.cutEnvelopingHomogeneousProjection vertex n
      (E.cutEnvelopingDegreeInclusion vertex n x) = E.cutEnvelopingDegreeInclusion vertex n x := by
  change E.cutEnvelopingDegreeInclusion vertex n
    (E.cutEnvelopingDegreeEquiv vertex (E.cutEnvelopingDegreeInclusion vertex n x) n) = _
  rw [E.cutEnvelopingDegreeEquiv_inclusion vertex]
  simp only [DirectSum.lof_eq_of, DirectSum.of_eq_same]

theorem cutEnvelopingHomogeneousProjection_of_inclusion_ne (n m : ℕ) (hnm : n ≠ m)
    (x : E.CutEnvelopingDegreeBlock vertex m) :
    E.cutEnvelopingHomogeneousProjection vertex n
      (E.cutEnvelopingDegreeInclusion vertex m x) = 0 := by
  change E.cutEnvelopingDegreeInclusion vertex n
    (E.cutEnvelopingDegreeEquiv vertex (E.cutEnvelopingDegreeInclusion vertex m x) n) = _
  rw [E.cutEnvelopingDegreeEquiv_inclusion vertex]
  rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ hnm]
  exact (E.cutEnvelopingDegreeInclusion vertex n).map_zero

end ASGinzburg.ZAlgebra.PeriodIso
