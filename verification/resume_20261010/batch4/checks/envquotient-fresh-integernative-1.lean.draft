import work.ASGinzburgDraft.PeriodCutEnvelopingHomogeneousSubspaces
import work.ASGinzburgDraft.NatHomogeneousSubspacesIntegerExtension

/-! The actual unsigned enveloping ring has its internal integer grading,
with every negative component zero. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
open scoped TensorProduct DirectSum
universe u v w
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k} {p : ℤ}
variable (E : A.PeriodIso p) {ι : Type w} [Fintype ι] (vertex : ι → ℤ)

noncomputable def cutEnvelopingIntegerHomogeneousSubspace (q : ℤ) :
    Submodule k (AlgebraEnvelopingRing k (E.CutGradedRing vertex)) := by
  letI : AddCommGroup (AlgebraEnvelopingRing k (E.CutGradedRing vertex)) :=
    Module.addCommMonoidToAddCommGroup k
  exact natHomogeneousSubspaceIntegerExtension k _
    (E.cutEnvelopingHomogeneousSubspace vertex) q

@[simp] theorem cutEnvelopingIntegerHomogeneousSubspace_natCast (n : ℕ) :
    E.cutEnvelopingIntegerHomogeneousSubspace vertex (n : ℤ) =
      E.cutEnvelopingHomogeneousSubspace vertex n := by
  letI : AddCommGroup (AlgebraEnvelopingRing k (E.CutGradedRing vertex)) :=
    Module.addCommMonoidToAddCommGroup k
  exact natHomogeneousSubspaceIntegerExtension_natCast k _ _ n

theorem cutEnvelopingIntegerHomogeneousSubspace_neg (q : ℤ) (hq : q < 0) :
    E.cutEnvelopingIntegerHomogeneousSubspace vertex q = ⊥ := by
  letI : AddCommGroup (AlgebraEnvelopingRing k (E.CutGradedRing vertex)) :=
    Module.addCommMonoidToAddCommGroup k
  exact natHomogeneousSubspaceIntegerExtension_neg k _ _ q hq

theorem cutEnvelopingIntegerHomogeneousSubspaces_isInternal :
    DirectSum.IsInternal (E.cutEnvelopingIntegerHomogeneousSubspace vertex) := by
  letI : AddCommGroup (AlgebraEnvelopingRing k (E.CutGradedRing vertex)) :=
    Module.addCommMonoidToAddCommGroup k
  exact natHomogeneousSubspaceIntegerExtension_isInternal k _ _
    (E.cutEnvelopingHomogeneousSubspaces_isInternal vertex)

noncomputable instance cutEnvelopingIntegerHomogeneousDecomposition :
    DirectSum.Decomposition (E.cutEnvelopingIntegerHomogeneousSubspace vertex) :=
  (E.cutEnvelopingIntegerHomogeneousSubspaces_isInternal vertex).chooseDecomposition

end ASGinzburg.ZAlgebra.PeriodIso
