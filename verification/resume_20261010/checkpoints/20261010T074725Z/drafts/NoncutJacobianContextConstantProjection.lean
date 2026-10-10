import work.ASGinzburgDraft.NoncutJacobianContextCoefficients
import work.ASGinzburgDraft.CutContextLeadingArrow
import ASGinzburg.FoundationSurvivingArrows

/-! Extract the actual constant relation coefficient of a finite noncut
context expansion. Both context paths must have length zero. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

def noncutJacobianContextConstantArrow (i j : Q.Vertex)
    (c : Q.NoncutJacobianContextIndex i j)
    (hl : c.2.1.val.length = 0) (hr : c.2.2.val.length = 0) :
    Q.FoundationRelationArrow i j :=
  ⟨c.1.val, c.2.2.val.endpoints_eq_of_length_zero Q hr,
    (c.2.1.val.endpoints_eq_of_length_zero Q hl).symm, c.1.property⟩

noncomputable def noncutJacobianContextConstantProjection (i j : Q.Vertex) :
    (Q.NoncutJacobianContextIndex i j →₀ k) →ₗ[k] (Q.FoundationRelationArrow i j →₀ k) :=
  Finsupp.linearCombination k (fun c =>
    if h : c.2.1.val.length = 0 ∧ c.2.2.val.length = 0 then
      Finsupp.single (Q.noncutJacobianContextConstantArrow i j c h.1 h.2) 1 else 0)

theorem noncutJacobianContextConstantProjection_single (i j : Q.Vertex)
    (c : Q.NoncutJacobianContextIndex i j) (a : k) :
    Q.noncutJacobianContextConstantProjection k i j (Finsupp.single c a) =
      if h : c.2.1.val.length = 0 ∧ c.2.2.val.length = 0 then
        Finsupp.single (Q.noncutJacobianContextConstantArrow i j c h.1 h.2) a else 0 := by
  classical
  by_cases h : c.2.1.val.length = 0 ∧ c.2.2.val.length = 0
  · simp [noncutJacobianContextConstantProjection, h]
  · simp [noncutJacobianContextConstantProjection, h]

end ASGinzburg.CutQuiver
