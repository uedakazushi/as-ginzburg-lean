import ASGinzburg.ASResolutionComplex
import ASGinzburg.RightModuleExtLinear
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# The concrete AS conditions on the existing right-module category

This models Definition 1.1, (1.6) and (1.7), without adding periodicity or
an Ext table as hypotheses. A separate equivalence with the paper's locally
unital Gr(A) remains to be constructed. The existence of these conditions
for any particular algebra is not asserted here.
-/

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

/-- Sum over all degrees and all lifted vertices, with the SECOND Ext argument fixed. -/
noncomputable def asExtTotalRank (v : Q.LiftVertex) : Cardinal :=
  Cardinal.sum fun p : ℕ => Cardinal.sum fun u : Q.LiftVertex =>
    Module.rank k (Abelian.Ext.{v} (A.simpleRightModule (Q.height u))
      (A.representable (Q.height v)) p)

/-- Definition 1.1 in the existing concrete presheaf model. Existence of the
finite minimal sequence is a property; chosen differentials are not extra data. -/
def ASRegular : Prop :=
  (∀ v : Q.LiftVertex, Nonempty (A.ASResolution Q v)) ∧
  (∀ v : Q.LiftVertex, A.asExtTotalRank Q v = 1)

/-- Choice of the sequence whose existence is required in Definition 1.1(i). -/
noncomputable def ASRegular.resolution (h : A.ASRegular Q) (v : Q.LiftVertex) :
    A.ASResolution Q v := Classical.choice (h.1 v)

noncomputable def ASRegular.projectiveResolution (h : A.ASRegular Q) (v : Q.LiftVertex) :
    ProjectiveResolution (A.simpleRightModule (Q.height v)) :=
  (h.resolution A Q v).toProjectiveResolution

theorem ASRegular.projectiveResolution_isZero_ge_four (h : A.ASRegular Q)
    (v : Q.LiftVertex) (n : ℕ) :
    IsZero ((h.projectiveResolution A Q v).complex.X (n + 4)) :=
  (h.resolution A Q v).complex_isZero_ge_four n

theorem asExtRank_le_total (v u : Q.LiftVertex) (p : ℕ) :
    Module.rank k (Abelian.Ext.{v} (A.simpleRightModule (Q.height u))
      (A.representable (Q.height v)) p) ≤ A.asExtTotalRank Q v :=
  (Cardinal.le_sum (fun t : Q.LiftVertex =>
    Module.rank k (Abelian.Ext.{v} (A.simpleRightModule (Q.height t))
      (A.representable (Q.height v)) p)) u).trans
    (Cardinal.le_sum (fun n : ℕ => Cardinal.sum fun t : Q.LiftVertex =>
      Module.rank k (Abelian.Ext.{v} (A.simpleRightModule (Q.height t))
        (A.representable (Q.height v)) n)) p)

theorem ASRegular.extRank_le_one (h : A.ASRegular Q) (v u : Q.LiftVertex) (p : ℕ) :
    Module.rank k (Abelian.Ext.{v} (A.simpleRightModule (Q.height u))
      (A.representable (Q.height v)) p) ≤ 1 :=
  (A.asExtRank_le_total Q v u p).trans_eq (h.2 v)

/-- The total rank condition forces each actual Ext vector space to be finite dimensional. -/
theorem ASRegular.extFinite (h : A.ASRegular Q) (v u : Q.LiftVertex) (p : ℕ) :
    Module.Finite k (Abelian.Ext.{v} (A.simpleRightModule (Q.height u))
      (A.representable (Q.height v)) p) :=
  Module.rank_lt_aleph0_iff.mp
    ((h.extRank_le_one A Q v u p).trans_lt (Cardinal.nat_lt_aleph0 1))

theorem ASRegular.extFinrank_le_one (h : A.ASRegular Q) (v u : Q.LiftVertex) (p : ℕ) :
    Module.finrank k (Abelian.Ext.{v} (A.simpleRightModule (Q.height u))
      (A.representable (Q.height v)) p) ≤ 1 := by
  letI := h.extFinite A Q v u p
  have hr := h.extRank_le_one A Q v u p
  rw [← Module.finrank_eq_rank] at hr
  exact_mod_cast hr

theorem asExtRank_zero_iff (v u : Q.LiftVertex) (p : ℕ) :
    Module.rank k (Abelian.Ext.{v} (A.simpleRightModule (Q.height u))
      (A.representable (Q.height v)) p) = 0 ↔
    ∀ e : Abelian.Ext.{v} (A.simpleRightModule (Q.height u))
      (A.representable (Q.height v)) p, e = 0 := by
  constructor
  · intro h
    letI := Module.subsingleton_of_rank_zero h
    intro e
    exact Subsingleton.elim _ _
  · intro h
    letI : Subsingleton (Abelian.Ext.{v} (A.simpleRightModule (Q.height u))
      (A.representable (Q.height v)) p) := ⟨fun x y => by rw [h x, h y]⟩
    exact rank_subsingleton' k _

end ASGinzburg.ZAlgebra
