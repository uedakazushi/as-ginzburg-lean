import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.Algebra.Equiv

/-! The actual cyclic quotient of an algebra is the vector-space quotient
by the span of commutators. Algebra maps act on it, and genuine algebra
isomorphisms induce genuine linear isomorphisms. -/
namespace ASGinzburg
universe u v w z
variable (k : Type u) [Field k] (R : Type v) [Ring R] [Algebra k R]

noncomputable def algebraCommutatorSubspace : Submodule k R :=
  Submodule.span k {x | ∃ a b : R, a*b-b*a=x}

noncomputable abbrev AlgebraCyclicQuotient := R ⧸ algebraCommutatorSubspace k R

variable {R} {S : Type w} [Ring S] [Algebra k S]

theorem algebraCommutatorSubspace_map_mem (F : R →ₐ[k] S)
    (x : R) (hx : x ∈ algebraCommutatorSubspace k R) :
    F x ∈ algebraCommutatorSubspace k S := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a,b,rfl⟩ := hy
    simp only [map_sub,map_mul]
    exact Submodule.subset_span ⟨F a,F b,rfl⟩
  | zero => simpa only [map_zero] using (algebraCommutatorSubspace k S).zero_mem
  | add x y hx hy ihx ihy =>
    simpa only [map_add] using (algebraCommutatorSubspace k S).add_mem ihx ihy
  | smul c x hx ih =>
    simpa only [map_smul] using (algebraCommutatorSubspace k S).smul_mem c ih

noncomputable def algebraCyclicMap (F : R →ₐ[k] S) :
    AlgebraCyclicQuotient k R →ₗ[k] AlgebraCyclicQuotient k S :=
  (algebraCommutatorSubspace k R).mapQ (algebraCommutatorSubspace k S)
    F.toLinearMap (fun x hx => algebraCommutatorSubspace_map_mem k F x hx)

theorem algebraCyclicMap_mk (F : R →ₐ[k] S) (x : R) :
    algebraCyclicMap k F (Submodule.Quotient.mk x) = Submodule.Quotient.mk (F x) := rfl

noncomputable def algebraCyclicEquiv (E : R ≃ₐ[k] S) :
    AlgebraCyclicQuotient k R ≃ₗ[k] AlgebraCyclicQuotient k S where
  toFun := algebraCyclicMap k E.toAlgHom
  invFun := algebraCyclicMap k E.symm.toAlgHom
  map_add' := (algebraCyclicMap k E.toAlgHom).map_add
  map_smul' := (algebraCyclicMap k E.toAlgHom).map_smul
  left_inv := by
    intro x
    obtain ⟨r,rfl⟩ := (algebraCommutatorSubspace k R).mkQ_surjective x
    change Submodule.Quotient.mk (E.symm (E r)) = Submodule.Quotient.mk r
    rw [E.symm_apply_apply]
  right_inv := by
    intro x
    obtain ⟨s,rfl⟩ := (algebraCommutatorSubspace k S).mkQ_surjective x
    change Submodule.Quotient.mk (E (E.symm s)) = Submodule.Quotient.mk s
    rw [E.apply_symm_apply]

theorem algebraCyclicEquiv_mk (E : R ≃ₐ[k] S) (x : R) :
    algebraCyclicEquiv k E (Submodule.Quotient.mk x) = Submodule.Quotient.mk (E x) := rfl

end ASGinzburg
