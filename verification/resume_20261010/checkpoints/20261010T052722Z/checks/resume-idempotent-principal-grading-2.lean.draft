import work.ASGinzburgDraft.IdempotentPrincipalProjective
import work.ASGinzburgDraft.GradedLinearMapRange

/-! A degree-zero principal idempotent projective inherits a genuine
internal grading from the regular module. Reindexing gives the actual
integer shifts used in homogeneous projective covers. -/
namespace ASGinzburg
open scoped DirectSum
universe u v
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]
variable (G : ℤ → Submodule k R) [DirectSum.Decomposition G]

noncomputable def integerGradingShiftDecomposition (t : ℤ) :
    DirectSum.Decomposition (fun q => G (q-t)) := by
  have h := DirectSum.Decomposition.isInternal G
  apply DirectSum.IsInternal.chooseDecomposition (fun q => G (q-t))
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact h.submodule_iSupIndep.comp (Equiv.subRight t).injective
  · exact (Equiv.subRight t).iSup_comp.trans h.submodule_iSup_eq_top

def principalIdempotentGrade (e : R) (q : ℤ) :
    Submodule k ((LinearMap.range (principalIdempotentOperator R e)).restrictScalars k) :=
  homogeneousSubmoduleGrade k R G
    ((LinearMap.range (principalIdempotentOperator R e)).restrictScalars k) q

noncomputable def principalIdempotentGradeDecomposition (e : R)
    (he : ∀ q : ℤ, ∀ r : R, r ∈ G q → r*e ∈ G q) :
    DirectSum.Decomposition (principalIdempotentGrade k R G e) :=
  homogeneousSubmoduleDecomposition k R G
    ((LinearMap.range (principalIdempotentOperator R e)).restrictScalars k)
    (fun q x hx => homogeneousLinearMap_range_component_mem k R R G G
      ((principalIdempotentOperator R e).restrictScalars k) he q x hx)

omit [DirectSum.Decomposition G] in
theorem principalIdempotentGrade_eq_bot_of_lower_bound
    (e : R) (b : ℤ) (hb : ∀ q : ℤ, q < b → G q = ⊥)
    (q : ℤ) (hq : q < b) : principalIdempotentGrade k R G e q = ⊥ :=
  homogeneousSubmoduleGrade_eq_bot_of_lower_bound k R
    ((LinearMap.range (principalIdempotentOperator R e)).restrictScalars k) G b hb q hq

omit [DirectSum.Decomposition G] in
theorem principalIdempotentGenerator_mem_grade_zero
    (e : R) (he : e ∈ G 0) :
    (principalIdempotentGenerator R e) ∈ principalIdempotentGrade k R G e 0 := he

end ASGinzburg
