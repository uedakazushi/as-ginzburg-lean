import ASGinzburg.GinzburgFixedHomologyNaturality
import ASGinzburg.FiniteCoproductComponentNaturality
import ASGinzburg.GinzburgGeneratorIndices

/-! Genuine finite coproducts of the existing representables at the
actual generator-prefix endpoints, with projectivity and natural component
identifications. No AS-resolution existence hypothesis is used. -/
namespace ASGinzburg.CutQuiver
variable (Q : CutQuiver)
noncomputable instance ginzburgIncomingDegreeFintype (v : Q.Vertex) (r : ℤ) :
    Fintype (Q.GinzburgIncomingDegree v r) := Fintype.ofFinite _
end ASGinzburg.CutQuiver

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

noncomputable def ginzburgGeneratorCoefficientModule (w : Q.LiftVertex) (r : ℤ) :
    A.RightModule :=
  ∐ fun a : Q.GinzburgIncomingDegree w.1 r =>
    A.representable (Q.height (Q.ginzburgPrefixGeneratorEndpoint w a.val))

noncomputable instance ginzburgGeneratorCoefficientModuleProjective (w : Q.LiftVertex) (r : ℤ) :
    Projective (A.ginzburgGeneratorCoefficientModule Q w r) := by
  unfold ginzburgGeneratorCoefficientModule
  exact A.rightModule_coproduct_projective _

noncomputable def ginzburgGeneratorCoefficientComponentEquiv (w : Q.LiftVertex) (r : ℤ)
    (i : ℤ) :
    (A.rightModuleEvaluation i).obj (A.ginzburgGeneratorCoefficientModule Q w r) ≃ₗ[k]
      (Π a : Q.GinzburgIncomingDegree w.1 r,
        A.Hom i (Q.height (Q.ginzburgPrefixGeneratorEndpoint w a.val))) := by
  classical
  exact A.rightFiniteCoproductPiEquiv
    (fun a : Q.GinzburgIncomingDegree w.1 r =>
      A.representable (Q.height (Q.ginzburgPrefixGeneratorEndpoint w a.val))) i

theorem ginzburgGeneratorCoefficientComponentEquiv_action (w : Q.LiftVertex) (r : ℤ)
    (i j : ℤ) (f : A.Hom i j)
    (x : (A.rightModuleEvaluation j).obj (A.ginzburgGeneratorCoefficientModule Q w r))
    (a : Q.GinzburgIncomingDegree w.1 r) :
    A.ginzburgGeneratorCoefficientComponentEquiv Q w r i
        ((A.ginzburgGeneratorCoefficientModule Q w r).obj.map
          (show (⟨i⟩ : A.Obj) ⟶ ⟨j⟩ from f).op x) a=
      A.comp (A.ginzburgGeneratorCoefficientComponentEquiv Q w r j x a) f := by
  classical
  exact A.rightFiniteCoproductPiEquiv_action
    (fun a : Q.GinzburgIncomingDegree w.1 r =>
      A.representable (Q.height (Q.ginzburgPrefixGeneratorEndpoint w a.val))) i j f x a

end ASGinzburg.ZAlgebra
