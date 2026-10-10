import ASGinzburg.FiniteFourTermPerfectComplex
import ASGinzburg.AlgebraEnvelopingRegularModule

/-! Homological smoothness as in source §2.1: the actual multiplication
bimodule is quasi-isomorphic to a bounded complex of finitely generated
projective modules over the actual enveloping algebra. -/
namespace ASGinzburg
universe u v
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]

def AlgebraHomologicallySmooth : Prop :=
  ordinaryPerfectModuleProperty (AlgebraEnvelopingRing k R) (regularEnvelopingModuleCat k R)

theorem algebraHomologicallySmooth_of_finiteFourTermResolution
    (F : FiniteFourTermProjectiveResolution (regularEnvelopingModuleCat k R)) :
    AlgebraHomologicallySmooth k R :=
  F.ordinaryPerfectModule

end ASGinzburg
