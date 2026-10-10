import ASGinzburg.PathCyclicTrace
import ASGinzburg.FiniteComponentIdempotents

/-! Actual closed path classes in the cyclic quotient, with genuine
cyclic rotation by exchanging the two factors of a closed composition. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def closedPathCyclicClass (i : Q.Vertex) :
    Q.PathComponent k i i →ₗ[k] AlgebraCyclicQuotient k (Q.PathRing k) :=
  (algebraCommutatorSubspace k (Q.PathRing k)).mkQ.comp
    ((Q.pathComponentAlgebra k).totalComponentLinear i i)

theorem pathCyclicTrace_totalComponent_closed (i : Q.Vertex) (f : Q.PathComponent k i i) :
    Q.pathCyclicTrace k ((Q.pathComponentAlgebra k).totalComponent i i f) =
      Q.closedPathTrace k i f := by
  classical
  change (∑ j : Q.Vertex, Q.closedPathTrace k j
      ((Q.pathComponentAlgebra k).totalComponent i i f j j)) = _
  rw [Finset.sum_eq_single i]
  · rw [LinearComponentAlgebra.totalComponent_apply_same]
  · intro j hj hji
    rw [(Q.pathComponentAlgebra k).totalComponent_apply_source_ne i i j j f hji,map_zero]
  · simp

theorem pathCyclicQuotientTrace_closedPathClass (i : Q.Vertex) (f : Q.PathComponent k i i) :
    Q.pathCyclicQuotientTrace k (Q.closedPathCyclicClass k i f) = Q.closedPathTrace k i f := by
  change Q.pathCyclicTrace k ((Q.pathComponentAlgebra k).totalComponent i i f) = _
  exact Q.pathCyclicTrace_totalComponent_closed k i f

theorem closedPathCyclicClass_comp (i j : Q.Vertex)
    (f : Q.PathComponent k i j) (g : Q.PathComponent k j i) :
    Q.closedPathCyclicClass k i (Q.pathComp k g f) =
      Q.closedPathCyclicClass k j (Q.pathComp k f g) := by
  change Submodule.Quotient.mk ((Q.pathComponentAlgebra k).totalComponent i i
      (Q.pathComp k g f)) = Submodule.Quotient.mk
      ((Q.pathComponentAlgebra k).totalComponent j j (Q.pathComp k f g))
  apply (Submodule.Quotient.eq (algebraCommutatorSubspace k (Q.PathRing k))).mpr
  change (Q.pathComponentAlgebra k).totalComponent i i
      ((Q.pathComponentAlgebra k).comp g f) -
    (Q.pathComponentAlgebra k).totalComponent j j
      ((Q.pathComponentAlgebra k).comp f g) ∈ algebraCommutatorSubspace k (Q.PathRing k)
  rw [← (Q.pathComponentAlgebra k).totalComponent_mul_same i j i f g,
    ← (Q.pathComponentAlgebra k).totalComponent_mul_same j i j g f]
  exact Submodule.subset_span ⟨_,_,rfl⟩

theorem closedPathCyclicClass_rotate_split (i j : Q.Vertex)
    (p : Q.Path i j) (q : Q.Path j i) :
    Q.closedPathCyclicClass k i (Finsupp.single (p.comp q) 1) =
      Q.closedPathCyclicClass k j (Finsupp.single (q.comp p) 1) := by
  simpa only [Q.pathComp_single,mul_one] using
    Q.closedPathCyclicClass_comp k i j (Finsupp.single p 1) (Finsupp.single q 1)

end ASGinzburg.CutQuiver
