import work.ASGinzburgDraft.PotentialPathAutomorphismClasses
import ASGinzburg.ZAlgebraIsomorphisms

/-! The base isomorphism-class assertion of source Theorem 3.2, expressed
using actual potentials, actual path-algebra automorphism orbits, actual
Ginzburg regularity, original AS regularity and actual vertex-fixing
algebra isomorphisms. These are proposition definitions, not an assertion
or a proof of the correspondence. A theorem establishing them will need
the source's characteristic-zero field hypothesis. -/
namespace ASGinzburg
universe u v
variable (k : Type u) [Field k] (Q : CutQuiver)

/-- The original potential-to-algebra map descends through the actual
vertex- and cut-preserving path-algebra automorphism relation. -/
noncomputable def ASGinzburgClassDescentStatement : Prop :=
  ∀ φ ψ : GinzburgRegularPotential k Q,
    φ.pathAutomorphismClass k Q = ψ.pathAutomorphismClass k Q →
      φ.asIsomorphismClass k Q = ψ.asIsomorphismClass k Q

/-- The original potential-to-algebra map is injective on those classes. -/
noncomputable def ASGinzburgClassInjectionStatement : Prop :=
  ∀ φ ψ : GinzburgRegularPotential k Q,
    φ.asIsomorphismClass k Q = ψ.asIsomorphismClass k Q →
      φ.pathAutomorphismClass k Q = ψ.pathAutomorphismClass k Q

/-- Every algebra satisfying the original AS definition is recovered
from an actual Ginzburg-regular potential. No periodicity data is added. -/
noncomputable def ASGinzburgRegularPotentialRecoveryStatement : Prop :=
  ∀ A : ZAlgebra.{u,v} k, A.ASRegular Q →
    ∃ φ : GinzburgRegularPotential k Q,
      Nonempty (ZAlgebra.Isomorphism A (Q.unrolledJacobianZAlgebra k φ.val))

/-- The exact base correspondence claim, separating its three outstanding
proof obligations without assuming any of them to hold. -/
noncomputable def ASGinzburgCorrespondenceStatement : Prop :=
  ASGinzburgClassDescentStatement k Q ∧ ASGinzburgClassInjectionStatement k Q ∧
    ASGinzburgRegularPotentialRecoveryStatement.{u,v} k Q

theorem asGinzburgCorrespondenceStatement_iff :
    ASGinzburgCorrespondenceStatement.{u,v} k Q ↔
      (∀ φ ψ : GinzburgRegularPotential k Q,
        φ.pathAutomorphismClass k Q = ψ.pathAutomorphismClass k Q ↔
          φ.asIsomorphismClass k Q = ψ.asIsomorphismClass k Q) ∧
      ASGinzburgRegularPotentialRecoveryStatement.{u,v} k Q := by
  constructor
  · rintro ⟨hD,hI,hR⟩
    exact ⟨fun φ ψ => ⟨hD φ ψ,hI φ ψ⟩,hR⟩
  · rintro ⟨h,hR⟩
    exact ⟨fun φ ψ => (h φ ψ).mp,fun φ ψ => (h φ ψ).mpr,hR⟩

end ASGinzburg
