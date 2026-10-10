import ASGinzburg.CyclicPathAutomorphismOrbits
import ASGinzburg.PotentialCyclicClass
import ASGinzburg.GinzburgRegularASClassMap
import Mathlib.Data.Setoid.Basic

/-! The actual potential embedding pulls the genuine path-algebra
automorphism orbit relation back to the original potential space and
its Ginzburg-regular subtype. These are the source equivalence classes;
descent of the potential-to-AS-algebra map is a separate obligation. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def potentialPathAutomorphismSetoid : Setoid (Q.Potential k) :=
  Setoid.comap (Q.potentialCyclicClass k) (Q.vertexCutPathCyclicOrbitSetoid k)

noncomputable abbrev PotentialPathAutomorphismClass :=
  Quotient (Q.potentialPathAutomorphismSetoid k)

noncomputable def potentialPathAutomorphismClass (φ : Q.Potential k) :
    Q.PotentialPathAutomorphismClass k :=
  Quotient.mk (Q.potentialPathAutomorphismSetoid k) φ

theorem potentialPathAutomorphism_related_iff (φ ψ : Q.Potential k) :
    (Q.potentialPathAutomorphismSetoid k).r φ ψ ↔
      ∃ E : Q.VertexCutPathAutomorphism k,
        algebraCyclicEquiv k E.val (Q.potentialCyclicClass k φ) = Q.potentialCyclicClass k ψ := by
  change Q.potentialCyclicClass k φ ∈
    MulAction.orbit (Q.VertexCutPathAutomorphism k) (Q.potentialCyclicClass k ψ) ↔ _
  rw [MulAction.mem_orbit_symm,MulAction.mem_orbit_iff]
  rfl

theorem potentialPathAutomorphismClass_eq_iff (φ ψ : Q.Potential k) :
    Q.potentialPathAutomorphismClass k φ = Q.potentialPathAutomorphismClass k ψ ↔
      ∃ E : Q.VertexCutPathAutomorphism k,
        algebraCyclicEquiv k E.val (Q.potentialCyclicClass k φ) = Q.potentialCyclicClass k ψ := by
  change Quotient.mk (Q.potentialPathAutomorphismSetoid k) φ =
    Quotient.mk (Q.potentialPathAutomorphismSetoid k) ψ ↔ _
  exact Quotient.eq.trans (Q.potentialPathAutomorphism_related_iff k φ ψ)

noncomputable def potentialClassCyclicOrbitMap :
    Q.PotentialPathAutomorphismClass k → Q.VertexCutPathCyclicOrbitClass k :=
  Quotient.lift (fun φ => Q.pathCyclicOrbitClass k (Q.potentialCyclicClass k φ))
    (fun _ _ h => Quotient.sound h)

theorem potentialClassCyclicOrbitMap_injective :
    Function.Injective (Q.potentialClassCyclicOrbitMap k) := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro φ ψ h
  change Q.pathCyclicOrbitClass k (Q.potentialCyclicClass k φ) =
    Q.pathCyclicOrbitClass k (Q.potentialCyclicClass k ψ) at h
  have hrel : (Q.vertexCutPathCyclicOrbitSetoid k).r
      (Q.potentialCyclicClass k φ) (Q.potentialCyclicClass k ψ) := Quotient.exact h
  exact Quotient.sound hrel

end ASGinzburg.CutQuiver

namespace ASGinzburg
universe u
variable (k : Type u) [Field k] (Q : CutQuiver)

noncomputable def ginzburgRegularPotentialPathAutomorphismSetoid :
    Setoid (GinzburgRegularPotential k Q) :=
  Setoid.comap Subtype.val (Q.potentialPathAutomorphismSetoid k)

noncomputable abbrev GinzburgRegularPotentialPathAutomorphismClass :=
  Quotient (ginzburgRegularPotentialPathAutomorphismSetoid k Q)

noncomputable def GinzburgRegularPotential.pathAutomorphismClass
    (φ : GinzburgRegularPotential k Q) : GinzburgRegularPotentialPathAutomorphismClass k Q :=
  Quotient.mk (ginzburgRegularPotentialPathAutomorphismSetoid k Q) φ

theorem ginzburgRegularPotentialPathAutomorphism_related_iff
    (φ ψ : GinzburgRegularPotential k Q) :
    (ginzburgRegularPotentialPathAutomorphismSetoid k Q).r φ ψ ↔
      ∃ E : Q.VertexCutPathAutomorphism k,
        algebraCyclicEquiv k E.val (Q.potentialCyclicClass k φ.val) =
          Q.potentialCyclicClass k ψ.val :=
  Q.potentialPathAutomorphism_related_iff k φ.val ψ.val

theorem GinzburgRegularPotential.pathAutomorphismClass_eq_iff
    (φ ψ : GinzburgRegularPotential k Q) :
    φ.pathAutomorphismClass k Q = ψ.pathAutomorphismClass k Q ↔
      ∃ E : Q.VertexCutPathAutomorphism k,
        algebraCyclicEquiv k E.val (Q.potentialCyclicClass k φ.val) =
          Q.potentialCyclicClass k ψ.val := by
  change Quotient.mk (ginzburgRegularPotentialPathAutomorphismSetoid k Q) φ =
    Quotient.mk (ginzburgRegularPotentialPathAutomorphismSetoid k Q) ψ ↔ _
  exact Quotient.eq.trans (ginzburgRegularPotentialPathAutomorphism_related_iff k Q φ ψ)

noncomputable def ginzburgRegularPotentialClassCyclicOrbitMap :
    GinzburgRegularPotentialPathAutomorphismClass k Q → Q.VertexCutPathCyclicOrbitClass k :=
  Quotient.lift (fun φ => Q.pathCyclicOrbitClass k (Q.potentialCyclicClass k φ.val))
    (fun _ _ h => Quotient.sound h)

theorem ginzburgRegularPotentialClassCyclicOrbitMap_injective :
    Function.Injective (ginzburgRegularPotentialClassCyclicOrbitMap k Q) := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro φ ψ h
  change Q.pathCyclicOrbitClass k (Q.potentialCyclicClass k φ.val) =
    Q.pathCyclicOrbitClass k (Q.potentialCyclicClass k ψ.val) at h
  have hrel : (Q.vertexCutPathCyclicOrbitSetoid k).r
      (Q.potentialCyclicClass k φ.val) (Q.potentialCyclicClass k ψ.val) := Quotient.exact h
  exact Quotient.sound hrel

end ASGinzburg
