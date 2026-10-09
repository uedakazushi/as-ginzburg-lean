import ASGinzburg.GinzburgSingleGeneratorRepresentatives
import ASGinzburg.GinzburgDualArrowHessianMatrix
import ASGinzburg.GinzburgLoopArrowDualPrefixes

/-! At every integer sheet, the genuine unit-basis representatives
differentiate into the original cyclic derivative and loop commutator. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgUnitDualDifferential_val (φ : Q.Potential k) (a : Q.Arrow) (s : ℤ) :
    (Q.ginzburgDualLayerDifferential k φ (Q.target a) (Q.source a)
      (s-(s-(GinzburgArrow.dual a).cutDegree Q))
      (Q.ginzburgGeneratorUnitRepresentative k (Q.source a,s) (-1)
        ⟨.dual a,rfl,rfl⟩)).val=
      Q.originalGinzburgLinearMap k (Q.target a) (Q.source a)
        (Q.pathCyclicDerivative k a φ) := by
  change Q.ginzburgDifferential k φ (Q.target a) (Q.source a)
    (Q.ginzburgGeneratorUnitRepresentative k (Q.source a,s) (-1)
      ⟨.dual a,rfl,rfl⟩).val=_
  rw [Q.ginzburgGeneratorUnitRepresentative_val]
  change Q.ginzburgDifferential k φ (Q.target a) (Q.source a)
    (Finsupp.single (Q.ginzburgArrowPath (.dual a)) 1)=_
  exact Q.ginzburgDifferential_generator k φ (.dual a)

theorem ginzburgUnitLoopDifferential_val (φ : Q.Potential k) (v : Q.Vertex) (s : ℤ) :
    (Q.ginzburgLoopLayerDifferential k φ v v (s-(s-1))
      (Q.ginzburgGeneratorUnitRepresentative k (v,s) (-2)
        ⟨.loop v,rfl,rfl⟩)).val=Q.ginzburgLoopDifferential k v := by
  change Q.ginzburgDifferential k φ v v
    (Q.ginzburgGeneratorUnitRepresentative k (v,s) (-2)
      ⟨.loop v,rfl,rfl⟩).val=_
  rw [Q.ginzburgGeneratorUnitRepresentative_val]
  change Q.ginzburgDifferential k φ v v
    (Finsupp.single (Q.ginzburgArrowPath (.loop v)) 1)=_
  exact Q.ginzburgDifferential_generator k φ (.loop v)

end ASGinzburg.CutQuiver
