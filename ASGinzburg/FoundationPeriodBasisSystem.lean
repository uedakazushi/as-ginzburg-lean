import ASGinzburg.PeriodGeneratorIndex

/-! A basis system for all unrolled indecomposables obtained solely
from the finite set of basis choices at the zero sheet and the AS period.
Coherence of chosen representative lifts is a further proof obligation. -/
namespace ASGinzburg.ZAlgebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

noncomputable def ASRegular.foundationPeriodBasisSystem (hAS : A.ASRegular Q) :
    A.IncomingBasisSystem Q where
  basis w i hi := by
    let w₀ : Q.LiftVertex := (w.1,0)
    let i₀ : ℤ := i-Q.vertices*w.2
    have hi₀ : i₀<Q.height w₀ := by
      dsimp [i₀,w₀,CutQuiver.height] at *
      omega
    have h := hAS.periodShiftGeneratorBasis A Q w.2 w₀ i₀ hi₀
    have hw : Q.shift w.2 w₀=w := by
      simp [w₀,CutQuiver.shift]
    have he : i₀+Q.vertices*w.2=i := sub_add_cancel _ _
    rw [hw,he] at h
    exact h

end ASGinzburg.ZAlgebra
