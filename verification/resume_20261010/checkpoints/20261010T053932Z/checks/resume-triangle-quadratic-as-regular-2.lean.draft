import work.ASGinzburgDraft.TriangleQuadraticResolution
import ASGinzburg.ASResolutionExtFinite
import ASGinzburg.TrianglePeriodicity

/-! The literal quadratic AS conditions (5.1) and (5.2) are equivalent to
ASRegular for the concrete triangle. Every actual Ext is finite by the
resolution condition before finrank is compared with rank. Periodicity is
then a theorem, not part of this quadratic definition. -/

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

/-- The dimension sum in (5.2), with the representable second argument fixed. -/
noncomputable def quadraticExtTotalDimension (i : ℤ) : Cardinal.{v} :=
  Cardinal.sum fun p : ℕ => Cardinal.sum fun j : ℤ =>
    (Module.finrank k (Abelian.Ext.{v} (A.simpleRightModule j) (A.representable i) p) : Cardinal.{v})

/-- Three-dimensional quadratic AS regularity, defined by the actual
minimal resolution (5.1) and the actual Ext dimension condition (5.2). -/
def QuadraticASRegular : Prop :=
  (∀ i : ℤ, Nonempty (A.QuadraticASResolution i)) ∧
  (∀ i : ℤ, A.quadraticExtTotalDimension i = 1)

theorem QuadraticASResolution.extFinite_representable {A : ZAlgebra.{u,v} k} {i : ℤ}
    (R : A.QuadraticASResolution i) (j : ℤ) (p : ℕ) :
    Module.Finite k (Abelian.Ext.{v} (A.simpleRightModule i) (A.representable j) p) := by
  let w := triangle333.heightEquiv.symm i
  have hw : triangle333.height w = i := by
    dsimp only [w]
    rw [← triangle333.heightEquiv_apply, Equiv.apply_symm_apply]
  have R' : A.QuadraticASResolution (triangle333.height w) := by
    simpa only [hw] using R
  have hf := (R'.toTriangleASResolution w).extFinite_representable j p
  exact Eq.mp (congrArg (fun t => Module.Finite k
    (Abelian.Ext.{v} (A.simpleRightModule t) (A.representable j) p)) hw) hf

theorem quadraticASResolutions_nonempty_iff :
    (∀ i : ℤ, Nonempty (A.QuadraticASResolution i)) ↔
      (∀ w : triangle333.LiftVertex, Nonempty (A.ASResolution triangle333 w)) := by
  constructor
  · intro h w
    exact (A.quadraticASResolution_nonempty_iff w).mp (h _)
  · intro h i
    let w := triangle333.heightEquiv.symm i
    have hw : triangle333.height w = i := by
      dsimp only [w]
      rw [← triangle333.heightEquiv_apply, Equiv.apply_symm_apply]
    have hr := (A.quadraticASResolution_nonempty_iff w).mpr (h w)
    simpa only [hw] using hr

/-- Reindexing the literal dimension sum by all lifted vertices, using
finiteness derived from the actual quadratic resolutions. -/
theorem quadraticExtTotalDimension_eq_asExtTotalRank
    (hres : ∀ i : ℤ, Nonempty (A.QuadraticASResolution i)) (w : triangle333.LiftVertex) :
    A.quadraticExtTotalDimension (triangle333.height w) = A.asExtTotalRank triangle333 w := by
  classical
  unfold quadraticExtTotalDimension asExtTotalRank
  congr 1
  funext p
  unfold Cardinal.sum
  apply Cardinal.mk_sigma_congr triangle333.heightEquiv.symm
  intro j
  simp only [Cardinal.mk_out]
  have hj : triangle333.height (triangle333.heightEquiv.symm j) = j := by
    rw [← triangle333.heightEquiv_apply, Equiv.apply_symm_apply]
  rw [hj]
  letI := (Classical.choice (hres j)).extFinite_representable (triangle333.height w) p
  exact Module.finrank_eq_rank k _

theorem quadraticASRegular_iff_triangleASRegular :
    A.QuadraticASRegular ↔ A.ASRegular triangle333 := by
  constructor
  · rintro ⟨hres, hdim⟩
    refine ⟨A.quadraticASResolutions_nonempty_iff.mp hres, fun w => ?_⟩
    rw [← A.quadraticExtTotalDimension_eq_asExtTotalRank hres w]
    exact hdim _
  · intro hAS
    have hres := A.quadraticASResolutions_nonempty_iff.mpr hAS.1
    refine ⟨hres, fun i => ?_⟩
    obtain ⟨w, hw⟩ := triangle333.height_bijective.surjective i
    rw [← hw, A.quadraticExtTotalDimension_eq_asExtTotalRank hres w]
    exact hAS.2 w

/-- Source Proposition 5.1 from the literal quadratic AS conditions. -/
noncomputable def QuadraticASRegular.trianglePeriodIso (hAS : A.QuadraticASRegular) :
    A.PeriodIso 3 :=
  (A.quadraticASRegular_iff_triangleASRegular.mp hAS).trianglePeriodIso A

theorem QuadraticASRegular.triangle_isPeriodic (hAS : A.QuadraticASRegular) :
    A.IsPeriodic 3 := ⟨hAS.trianglePeriodIso A⟩

end ASGinzburg.ZAlgebra
