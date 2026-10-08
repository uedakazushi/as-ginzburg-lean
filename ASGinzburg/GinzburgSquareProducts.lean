import ASGinzburg.GinzburgDifferentialSign

/-! The square is an unsigned derivation; this reduces square-zero to
the actual generator calculation, without assuming regularity. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgSign_mul_self (q : ℤ) : ginzburgSign k q*ginzburgSign k q=1 := by
  change (-1:k)^q*(-1:k)^q=1
  rw [←mul_zpow]
  simp

theorem ginzburgSignMap_involutive {u v : Q.Vertex} (f : Q.GinzburgPathComponent k u v) :
    Q.ginzburgSignMap k u v (Q.ginzburgSignMap k u v f)=f := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add,hf,hg]
  | single p c =>
    simp only [ginzburgSignMap_single,map_smul,smul_smul,ginzburgSign_mul_self,one_smul]

theorem ginzburgDifferential_square_comp (φ : Q.Potential k) {u v w : Q.Vertex}
    (f : Q.GinzburgPathComponent k u v) (g : Q.GinzburgPathComponent k v w) :
    Q.ginzburgDifferential k φ u w (Q.ginzburgDifferential k φ u w (Q.ginzburgPathComp k g f))=
      Q.ginzburgPathComp k (Q.ginzburgDifferential k φ v w (Q.ginzburgDifferential k φ v w g)) f+
      Q.ginzburgPathComp k g (Q.ginzburgDifferential k φ u v (Q.ginzburgDifferential k φ u v f)) := by
  rw [Q.ginzburgDifferential_comp k φ f g,map_add,
    Q.ginzburgDifferential_comp,Q.ginzburgDifferential_comp,
    Q.ginzburgDifferential_sign,Q.ginzburgSignMap_involutive]
  simp only [map_neg,LinearMap.neg_apply]
  abel

end ASGinzburg.CutQuiver
