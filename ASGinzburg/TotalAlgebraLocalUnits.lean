import ASGinzburg.TotalAlgebra

/-!
Finite sums of the actual component identities are idempotent local units.
Every finite family in the total algebra has a common unit on both sides.
All units are constructed from the finite support of the original components.
-/
namespace ASGinzburg.ZAlgebra
open CategoryTheory
open scoped DirectSum
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

theorem totalAlgebraComponent_id_mul {i j : ℤ} (a : A.Hom i j) :
    A.totalAlgebraComponent (A.id j) * A.totalAlgebraComponent a =
      A.totalAlgebraComponent a := by
  rw [A.totalAlgebraComponent_mul, A.comp_id]

theorem totalAlgebraComponent_mul_id {i j : ℤ} (a : A.Hom i j) :
    A.totalAlgebraComponent a * A.totalAlgebraComponent (A.id i) =
      A.totalAlgebraComponent a := by
  rw [A.totalAlgebraComponent_mul, A.id_comp]

/-- A finite sum of the original orthogonal component identities. -/
noncomputable def totalAlgebraLocalUnit (s : Finset ℤ) : A.totalAlgebra :=
  ∑ i ∈ s, A.totalAlgebraComponent (A.id i)

theorem totalAlgebraLocalUnit_mul_component (s : Finset ℤ) {i j : ℤ} (a : A.Hom i j)
    (hj : j ∈ s) :
    A.totalAlgebraLocalUnit s * A.totalAlgebraComponent a = A.totalAlgebraComponent a := by
  classical
  rw [totalAlgebraLocalUnit, Finset.sum_mul, Finset.sum_eq_single j]
  · exact A.totalAlgebraComponent_id_mul a
  · intro l _ hlj
    exact A.totalAlgebraComponent_mul_off a (A.id l) (Ne.symm hlj)
  · exact fun h => (h hj).elim

theorem totalAlgebraComponent_mul_localUnit (s : Finset ℤ) {i j : ℤ} (a : A.Hom i j)
    (hi : i ∈ s) :
    A.totalAlgebraComponent a * A.totalAlgebraLocalUnit s = A.totalAlgebraComponent a := by
  classical
  rw [totalAlgebraLocalUnit, Finset.mul_sum, Finset.sum_eq_single i]
  · exact A.totalAlgebraComponent_mul_id a
  · intro l _ hli
    exact A.totalAlgebraComponent_mul_off (A.id l) a hli
  · exact fun h => (h hi).elim

theorem totalAlgebraLocalUnit_idempotent (s : Finset ℤ) :
    A.totalAlgebraLocalUnit s * A.totalAlgebraLocalUnit s = A.totalAlgebraLocalUnit s := by
  change A.totalAlgebraLocalUnit s * (∑ i ∈ s, A.totalAlgebraComponent (A.id i)) = _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact A.totalAlgebraLocalUnit_mul_component s (A.id i) hi

theorem totalAlgebra_eq_sum_components (x : A.totalAlgebra) :
    x = ∑ p ∈ (by classical exact (A.totalAlgebraEquiv.symm x).support),
      A.totalAlgebraComponent (A.totalAlgebraEquiv.symm x p) := by
  classical
  have hx := congrArg A.totalAlgebraEquiv
    (DFinsupp.sum_single (f := A.totalAlgebraEquiv.symm x))
  simpa only [DFinsupp.sum, map_sum, LinearEquiv.apply_symm_apply, totalAlgebraComponent] using hx.symm

/-- Both endpoints of every nonzero component form a finite set. -/
noncomputable def totalAlgebraSupport (x : A.totalAlgebra) : Finset ℤ := by
  classical
  exact (A.totalAlgebraEquiv.symm x).support.biUnion (fun p => {p.1,p.2})

theorem totalAlgebraLocalUnit_mul_eq_self (s : Finset ℤ) (x : A.totalAlgebra)
    (h : A.totalAlgebraSupport x ⊆ s) : A.totalAlgebraLocalUnit s * x = x := by
  classical
  rw [A.totalAlgebra_eq_sum_components x, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  apply A.totalAlgebraLocalUnit_mul_component
  apply h
  change p.2 ∈ (A.totalAlgebraEquiv.symm x).support.biUnion (fun q => {q.1,q.2})
  exact Finset.mem_biUnion.mpr ⟨p,hp,Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩

theorem totalAlgebraLocalUnit_right_eq_self (s : Finset ℤ) (x : A.totalAlgebra)
    (h : A.totalAlgebraSupport x ⊆ s) : x * A.totalAlgebraLocalUnit s = x := by
  classical
  rw [A.totalAlgebra_eq_sum_components x, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  apply A.totalAlgebraComponent_mul_localUnit
  apply h
  change p.1 ∈ (A.totalAlgebraEquiv.symm x).support.biUnion (fun q => {q.1,q.2})
  exact Finset.mem_biUnion.mpr ⟨p,hp,Finset.mem_insert_self _ _⟩

theorem totalAlgebra_common_local_unit {I : Type*} (t : Finset I) (x : I → A.totalAlgebra) :
    ∃ s : Finset ℤ, (A.totalAlgebraLocalUnit s * A.totalAlgebraLocalUnit s =
      A.totalAlgebraLocalUnit s) ∧ ∀ i ∈ t,
      A.totalAlgebraLocalUnit s * x i = x i ∧ x i * A.totalAlgebraLocalUnit s = x i := by
  classical
  refine ⟨t.biUnion (fun i => A.totalAlgebraSupport (x i)),
    A.totalAlgebraLocalUnit_idempotent _, ?_⟩
  intro i hi
  have h : A.totalAlgebraSupport (x i) ⊆ t.biUnion (fun i => A.totalAlgebraSupport (x i)) := by
    intro j hj
    exact Finset.mem_biUnion.mpr ⟨i,hi,hj⟩
  exact ⟨A.totalAlgebraLocalUnit_mul_eq_self _ _ h,
    A.totalAlgebraLocalUnit_right_eq_self _ _ h⟩

end ASGinzburg.ZAlgebra
