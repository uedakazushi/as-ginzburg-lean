import ASGinzburg.ASDualityDimension
import ASGinzburg.ASResolutionExtFinite

/-!
# Both numerical directions of Proposition 1.3 in the existing model

Finite-dimensionality is derived from the finite AS sequences before
converting finrank to cardinal rank. No periodicity or Ext comparison is
added to the original AS definition.
-/
namespace ASGinzburg

/-- A single rank-one summand and zero elsewhere give a cardinal sum of one. -/
theorem cardinal_sum_eq_one_of_single {ι : Type*} (r : ι → Cardinal) (i₀ : ι)
    (hi₀ : r i₀ = 1) (hother : ∀ i, i ≠ i₀ → r i = 0) : Cardinal.sum r = 1 := by
  classical
  have hfst : ∀ x : Σ i, (r i).out, x.1 = i₀ := by
    intro x
    by_contra hn
    have hz : Cardinal.mk (r x.1).out = 0 := by rw [Cardinal.mk_out, hother x.1 hn]
    exact (Cardinal.mk_ne_zero_iff.mpr ⟨x.2⟩) hz
  letI : Subsingleton (r i₀).out := Cardinal.le_one_iff_subsingleton.mp (by
    rw [Cardinal.mk_out, hi₀])
  letI : Subsingleton (Σ i, (r i).out) := ⟨fun x y => by
    obtain ⟨i,x⟩ := x
    obtain ⟨j,y⟩ := y
    have hi : i = i₀ := hfst ⟨i,x⟩
    have hj : j = i₀ := hfst ⟨j,y⟩
    subst i
    subst j
    congr 1
    exact Subsingleton.elim _ _⟩
  have hne : Nonempty (r i₀).out := Cardinal.mk_ne_zero_iff.mp (by
    rw [Cardinal.mk_out, hi₀]; exact one_ne_zero)
  letI : Nonempty (Σ i, (r i).out) := ⟨⟨i₀, Classical.choice hne⟩⟩
  exact Cardinal.mk_eq_one _

end ASGinzburg

namespace ASGinzburg.ZAlgebra
open CategoryTheory
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

/-- The original total-rank condition follows from (1.11), using finiteness
proved from condition (i), rather than assuming finite Ext. -/
theorem asExtTotalRank_eq_one_of_finrank
    (hres : ∀ w : Q.LiftVertex, Nonempty (A.ASResolution Q w))
    (w : Q.LiftVertex)
    (hdim : ∀ u : Q.LiftVertex, ∀ p : ℕ,
      Module.finrank k (Abelian.Ext.{v} (A.simpleRightModule (Q.height u))
        (A.representable (Q.height w)) p) = if (p,u) = (3,Q.tau w) then 1 else 0) :
    A.asExtTotalRank Q w = 1 := by
  classical
  let r : ℕ → Q.LiftVertex → Cardinal := fun p u =>
    Module.rank k (Abelian.Ext.{v} (A.simpleRightModule (Q.height u))
      (A.representable (Q.height w)) p)
  have hr : ∀ p u, r p u = if (p,u) = (3,Q.tau w) then 1 else 0 := by
    intro p u
    letI := (Classical.choice (hres u)).extFinite_representable (Q.height w) p
    dsimp only [r]
    rw [← Module.finrank_eq_rank, hdim u p]
    split_ifs <;> rfl
  apply ASGinzburg.cardinal_sum_eq_one_of_single (fun p => Cardinal.sum (r p)) 3
  · apply ASGinzburg.cardinal_sum_eq_one_of_single (r 3) (Q.tau w)
    · simp only [hr, ite_true]
    · intro u hu
      rw [hr, if_neg (by simpa using hu)]
  · intro p hp
    have hz : r p = fun _ => 0 := by
      funext u
      rw [hr, if_neg (by intro he; exact hp (Prod.mk.inj he).1)]
    rw [hz]
    simp

/-- The numerical equivalence, under the original finite minimal resolution condition. -/
theorem asRegular_iff_ext_finrank
    (hres : ∀ w : Q.LiftVertex, Nonempty (A.ASResolution Q w)) :
    A.ASRegular Q ↔ ∀ w u : Q.LiftVertex, ∀ p : ℕ,
      Module.finrank k (Abelian.Ext.{v} (A.simpleRightModule (Q.height u))
        (A.representable (Q.height w)) p) = if (p,u) = (3,Q.tau w) then 1 else 0 := by
  constructor
  · intro h w u p
    exact h.ext_finrank A Q w u p
  · intro h
    exact ⟨hres, fun w => A.asExtTotalRank_eq_one_of_finrank Q hres w (h w)⟩

end ASGinzburg.ZAlgebra
