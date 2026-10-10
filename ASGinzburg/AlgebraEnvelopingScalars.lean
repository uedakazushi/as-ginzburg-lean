import ASGinzburg.AlgebraEnvelopingRegularModule
import Mathlib.RingTheory.Finiteness.Basic

namespace ASGinzburg
universe u v
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]

noncomputable def regularEnvelopingScalarTower :
    letI := regularEnvelopingModule k R
    IsScalarTower k (AlgebraEnvelopingRing k R) R := by
  letI := regularEnvelopingModule k R
  constructor
  intro c a x
  change regularEnvelopingRepresentation k R (c • a) x=
    c • regularEnvelopingRepresentation k R a x
  rw [map_smul,LinearMap.smul_apply]

noncomputable def regularEnvelopingScalarComm :
    letI := regularEnvelopingModule k R
    SMulCommClass k (AlgebraEnvelopingRing k R) R := by
  letI := regularEnvelopingModule k R
  constructor
  intro c a x
  exact ((regularEnvelopingRepresentation k R a).map_smul c x).symm

theorem regularEnvelopingModule_finite [Module.Finite k R] :
    letI := regularEnvelopingModule k R
    Module.Finite (AlgebraEnvelopingRing k R) R := by
  letI := regularEnvelopingModule k R
  letI := regularEnvelopingScalarTower k R
  exact Module.Finite.of_restrictScalars_finite k (AlgebraEnvelopingRing k R) R

end ASGinzburg
