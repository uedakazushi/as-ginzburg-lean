import work.ASGinzburgDraft.AlgebraCyclicAutomorphismAction
import work.ASGinzburgDraft.VertexCutPathAutomorphisms

/-! Actual vertex- and cut-preserving path algebra automorphisms act
on the actual commutator quotient. The equivalence relation is the
standard orbit Setoid of this genuine group action. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable abbrev PathCyclicQuotient := AlgebraCyclicQuotient k (Q.PathRing k)

noncomputable def vertexCutPathCyclicOrbitSetoid : Setoid (Q.PathCyclicQuotient k) :=
  MulAction.orbitRel (Q.VertexCutPathAutomorphism k) (Q.PathCyclicQuotient k)

noncomputable abbrev VertexCutPathCyclicOrbitClass :=
  Quotient (Q.vertexCutPathCyclicOrbitSetoid k)

noncomputable def pathCyclicOrbitClass (x : Q.PathCyclicQuotient k) :
    Q.VertexCutPathCyclicOrbitClass k :=
  Quotient.mk (Q.vertexCutPathCyclicOrbitSetoid k) x

theorem vertexCutPathCyclicOrbit_refl (x : Q.PathCyclicQuotient k) :
    (Q.vertexCutPathCyclicOrbitSetoid k).r x x :=
  (Q.vertexCutPathCyclicOrbitSetoid k).refl x

theorem vertexCutPathCyclicOrbit_symm {x y : Q.PathCyclicQuotient k}
    (h : (Q.vertexCutPathCyclicOrbitSetoid k).r x y) :
    (Q.vertexCutPathCyclicOrbitSetoid k).r y x :=
  (Q.vertexCutPathCyclicOrbitSetoid k).symm h

theorem vertexCutPathCyclicOrbit_trans {x y z : Q.PathCyclicQuotient k}
    (hxy : (Q.vertexCutPathCyclicOrbitSetoid k).r x y)
    (hyz : (Q.vertexCutPathCyclicOrbitSetoid k).r y z) :
    (Q.vertexCutPathCyclicOrbitSetoid k).r x z :=
  (Q.vertexCutPathCyclicOrbitSetoid k).trans hxy hyz

theorem pathCyclicOrbitClass_eq_iff (x y : Q.PathCyclicQuotient k) :
    Q.pathCyclicOrbitClass k x = Q.pathCyclicOrbitClass k y ↔
      ∃ E : Q.VertexCutPathAutomorphism k, algebraCyclicEquiv k E.val x = y := by
  change Quotient.mk (Q.vertexCutPathCyclicOrbitSetoid k) x =
    Quotient.mk (Q.vertexCutPathCyclicOrbitSetoid k) y ↔ _
  rw [Quotient.eq]
  change x ∈ MulAction.orbit (Q.VertexCutPathAutomorphism k) y ↔ _
  rw [MulAction.mem_orbit_symm,MulAction.mem_orbit_iff]
  rfl

end ASGinzburg.CutQuiver
