import work.ASGinzburgDraft.IdempotentPrincipalGrading
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! The actual principal projective, with the canonical scalar action of
ModuleCat, has the same genuine homogeneous components as its underlying
principal submodule. Integer shifts retain the actual grading. -/
namespace ASGinzburg
open scoped DirectSum ModuleCat.Algebra
universe u v
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (G : ℤ → Submodule k R) [DirectSum.Decomposition G]

def principalIdempotentOrdinaryGrade (e : R) (q : ℤ) :
    Submodule k (principalIdempotentModule R e) where
  carrier := {x | x.val ∈ G q}
  zero_mem' := (G q).zero_mem
  add_mem' := (G q).add_mem
  smul_mem' c x hx := by
    change (algebraMap k R c)*x.val ∈ G q
    simpa only [Algebra.smul_def] using (G q).smul_mem c hx

noncomputable def principalIdempotentOrdinaryGradeDecomposition (e : R)
    (he : ∀ q : ℤ, ∀ r : R, r ∈ G q → r*e ∈ G q) :
    DirectSum.Decomposition (principalIdempotentOrdinaryGrade k R G e) := by
  letI := principalIdempotentGradeDecomposition k R G e he
  exact {
    decompose' := DirectSum.decompose (principalIdempotentGrade k R G e)
    left_inv := (DirectSum.decompose (principalIdempotentGrade k R G e)).left_inv
    right_inv := (DirectSum.decompose (principalIdempotentGrade k R G e)).right_inv
  }

noncomputable def principalIdempotentShiftedGradeDecomposition (e : R)
    (he : ∀ q : ℤ, ∀ r : R, r ∈ G q → r*e ∈ G q) (t : ℤ) :
    DirectSum.Decomposition (fun q => principalIdempotentOrdinaryGrade k R G e (q-t)) := by
  letI := principalIdempotentOrdinaryGradeDecomposition k R G e he
  have h := DirectSum.Decomposition.isInternal (principalIdempotentOrdinaryGrade k R G e)
  apply DirectSum.IsInternal.chooseDecomposition (fun q => principalIdempotentOrdinaryGrade k R G e (q-t))
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact h.submodule_iSupIndep.comp (Equiv.subRight t).injective
  · exact (Equiv.subRight t).iSup_comp.trans h.submodule_iSup_eq_top

omit [DirectSum.Decomposition G] in
theorem principalIdempotentOrdinaryGrade_eq_bot_of_lower_bound
    (e : R) (b : ℤ) (hb : ∀ q : ℤ, q < b → G q = ⊥)
    (q : ℤ) (hq : q < b) : principalIdempotentOrdinaryGrade k R G e q = ⊥ := by
  ext x
  change x.val ∈ G q ↔ x=0
  rw [hb q hq]
  change x.val=0 ↔ x=0
  exact ⟨fun h => Subtype.ext h, fun h => congrArg (fun y => y.val) h⟩

omit [DirectSum.Decomposition G] in
theorem principalIdempotentOrdinaryGenerator_mem_grade_zero
    (e : R) (he : e ∈ G 0) :
    principalIdempotentGenerator R e ∈ principalIdempotentOrdinaryGrade k R G e 0 := he

end ASGinzburg
