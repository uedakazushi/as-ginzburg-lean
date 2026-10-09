import ASGinzburg.PathCyclicHessianCoefficients
import ASGinzburg.GinzburgDegreeZeroDifferential

/-! The intrinsic generator differential reads the actual path Hessian
matrix when its original last-arrow coefficient is extracted. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem originalGinzburgLinearMap_apply_original {u v : Q.Vertex}
    (f : Q.PathComponent k u v) (p : Q.Path u v) :
    Q.originalGinzburgLinearMap k u v f (p.originalGinzburg Q)=f p :=
  Finsupp.mapDomain_apply (Path.originalGinzburg_injective Q u v) f p

theorem ginzburgDualGeneratorDifferential_snoc_coeff
    (a b : Q.Arrow) (φ : Q.Potential k)
    (p : Q.Path (Q.target a) (Q.source b)) (hb : Q.target b=Q.source a) :
    Q.ginzburgGeneratorDifferential k φ (.dual a)
        (((Path.snoc p b rfl).transport rfl hb).originalGinzburg Q)=
      Q.pathCyclicHessian k a b φ p := by
  change Q.originalGinzburgLinearMap k (Q.target a) (Q.source a)
      (Q.pathCyclicDerivative k a φ) (((Path.snoc p b rfl).transport rfl hb).originalGinzburg Q)=_
  rw [Q.originalGinzburgLinearMap_apply_original,Q.pathCyclicDerivative_snoc_coeff]

theorem ginzburgDifferential_dualArrow_snoc_coeff
    (a b : Q.Arrow) (φ : Q.Potential k)
    (p : Q.Path (Q.target a) (Q.source b)) (hb : Q.target b=Q.source a) :
    Q.ginzburgDifferential k φ (Q.target a) (Q.source a)
        (Finsupp.single (Q.ginzburgArrowPath (.dual a)) 1)
        (((Path.snoc p b rfl).transport rfl hb).originalGinzburg Q)=
      Q.pathCyclicHessian k a b φ p := by
  exact (congrArg (fun f : Q.GinzburgPathComponent k (Q.target a) (Q.source a) =>
    f (((Path.snoc p b rfl).transport rfl hb).originalGinzburg Q))
    (Q.ginzburgDifferential_generator k φ (.dual a))).trans
      (Q.ginzburgDualGeneratorDifferential_snoc_coeff k a b φ p hb)

end ASGinzburg.CutQuiver
