import ASGinzburg.AlgebraEnvelopingRegularFinite

/-! The genuine bundled multiplication bimodule is finitely generated
over the enveloping algebra, with no finite-dimensional field assumption. -/
namespace ASGinzburg
universe u v
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]

instance regularEnvelopingModuleCat_finite :
    Module.Finite (AlgebraEnvelopingRing k R) (regularEnvelopingModuleCat k R) :=
  regularEnvelopingModule_finite_of_cyclic k R

end ASGinzburg
