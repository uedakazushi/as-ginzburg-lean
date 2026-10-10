import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.Algebra.Algebra.Opposite
import Mathlib.RingTheory.SimpleModule.InjectiveProjective

/-! The finite vertex scalar algebra is genuinely separable: its base
change to every field is semisimple, and its actual enveloping algebra
is semisimple as well. These are proved using actual tensor algebra isomorphisms. -/
namespace ASGinzburg
open scoped TensorProduct
universe u v w
variable (k : Type u) [Field k] (I : Type v) [Fintype I] [DecidableEq I]

noncomputable def scalarProductEnvelopingEquiv :
    ((I→k) ⊗[k] (I→k)ᵐᵒᵖ) ≃ₐ[k] (I→I→k) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : (I→k) ≃ₐ[k] (I→k))
    (AlgEquiv.toOpposite k (I→k)).symm).trans
      (Algebra.TensorProduct.piScalarRight k k (I→k) I)

instance scalarProductEnveloping_isSemisimple :
    IsSemisimpleRing ((I→k) ⊗[k] (I→k)ᵐᵒᵖ) :=
  (scalarProductEnvelopingEquiv k I).symm.toRingEquiv.isSemisimpleRing

noncomputable def scalarProductBaseChangeEquiv (K : Type w) [Field K] [Algebra k K] :
    (K ⊗[k] (I→k)) ≃ₐ[K] (I→K) :=
  Algebra.TensorProduct.piScalarRight k K K I

theorem scalarProductBaseChange_isSemisimple (K : Type w) [Field K] [Algebra k K] :
    IsSemisimpleRing (K ⊗[k] (I→k)) :=
  (scalarProductBaseChangeEquiv k I K).symm.toRingEquiv.isSemisimpleRing

noncomputable def scalarProductEnvelopingMultiplication :
    ((I→k) ⊗[k] (I→k)ᵐᵒᵖ) →ₐ[k] (I→k) :=
  Algebra.TensorProduct.lift (AlgHom.id k (I→k))
    (AlgEquiv.toOpposite k (I→k)).symm.toAlgHom (fun _ _ => Commute.all _ _)

noncomputable def scalarProductEnvelopingModule :
    Module ((I→k) ⊗[k] (I→k)ᵐᵒᵖ) (I→k) :=
  Module.compHom (I→k) (scalarProductEnvelopingMultiplication k I).toRingHom

theorem scalarProductEnvelopingModule_projective :
    letI := scalarProductEnvelopingModule k I
    Module.Projective ((I→k) ⊗[k] (I→k)ᵐᵒᵖ) (I→k) := by
  letI := scalarProductEnvelopingModule k I
  exact Module.projective_of_isSemisimpleRing _ _

end ASGinzburg
