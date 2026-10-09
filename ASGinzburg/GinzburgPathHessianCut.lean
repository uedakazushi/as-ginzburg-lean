import ASGinzburg.PathCyclicHessianDegrees
import ASGinzburg.GinzburgGeneratorGradings

/-! The actual path Hessian lies in precisely the cut component
needed for the native dual-arrow to original-arrow connecting matrix. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem pathCyclicHessian_ginzburg_cut (a b : Q.Arrow) (φ : Q.Potential k) :
    Q.pathCyclicHessian k a b φ ∈ Finsupp.supported k k
      {p : Q.Path (Q.target a) (Q.source b) |
        (p.cutDegree:ℤ)=(GinzburgArrow.dual a).cutDegree Q-
          (GinzburgArrow.original b).cutDegree Q} := by
  apply Finsupp.supported_mono _ (Q.pathCyclicHessian_supported_degrees k a b φ)
  rintro p ⟨_,hp⟩
  change (p.cutDegree:ℤ)=(1-(Q.cutDegree a:ℤ))-(Q.cutDegree b:ℤ)
  have hi : (p.cutDegree:ℤ)+(Q.cutDegree b:ℤ)+(Q.cutDegree a:ℤ)=1 := by
    exact_mod_cast hp
  omega

end ASGinzburg.CutQuiver
