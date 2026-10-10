import work.ASGinzburgDraft.AlgebraCyclicQuotient
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.GroupTheory.GroupAction.Defs

/-! Actual algebra automorphisms act on the actual commutator quotient.
The induced linear automorphisms preserve composition and the identity. -/
namespace ASGinzburg
universe u v
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]

noncomputable def algebraCyclicAutomorphismHom :
    (R ≃ₐ[k] R) →* (AlgebraCyclicQuotient k R ≃ₗ[k] AlgebraCyclicQuotient k R) where
  toFun := algebraCyclicEquiv k
  map_one' := by
    apply LinearEquiv.ext
    intro x
    obtain ⟨r,rfl⟩ := (algebraCommutatorSubspace k R).mkQ_surjective x
    rfl
  map_mul' E F := by
    apply LinearEquiv.ext
    intro x
    obtain ⟨r,rfl⟩ := (algebraCommutatorSubspace k R).mkQ_surjective x
    rfl

noncomputable instance algebraCyclicAutomorphismMulAction :
    MulAction (R ≃ₐ[k] R) (AlgebraCyclicQuotient k R) where
  smul E x := algebraCyclicEquiv k E x
  one_smul x := congrArg
    (fun E : AlgebraCyclicQuotient k R ≃ₗ[k] AlgebraCyclicQuotient k R => E x)
    (algebraCyclicAutomorphismHom k R).map_one
  mul_smul E F x := congrArg
    (fun E : AlgebraCyclicQuotient k R ≃ₗ[k] AlgebraCyclicQuotient k R => E x)
    ((algebraCyclicAutomorphismHom k R).map_mul E F)

@[simp] theorem algebraCyclicAutomorphism_smul_mk (E : R ≃ₐ[k] R) (x : R) :
    E • (Submodule.Quotient.mk x : AlgebraCyclicQuotient k R) =
      Submodule.Quotient.mk (E x) := rfl

end ASGinzburg
