import ASGinzburg.GinzburgLoopSquare

/-! Square-zero of the actual signed Ginzburg differential on every
composable path and every finite linear combination, without extra assumptions. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgDifferential_square_single (φ : Q.Potential k) {u v : Q.Vertex}
    (p : Q.GinzburgPath u v) :
    Q.ginzburgDifferential k φ u v (Q.ginzburgDifferential k φ u v (Finsupp.single p 1))=0 := by
  induction p with
  | nil => simp
  | snoc p a h ih =>
    subst h
    have hs : Finsupp.single (GinzburgPath.snoc p a rfl) (1:k)=
        Q.ginzburgPathComp k (Finsupp.single (Q.ginzburgArrowPath a) 1) (Finsupp.single p 1) := by
      simp [ginzburgArrowPath,GinzburgPath.comp]
    rw [hs,Q.ginzburgDifferential_square_comp,Q.ginzburgDifferential_generator,
      Q.ginzburgGeneratorDifferential_square,ih]
    simp

theorem ginzburgDifferential_square (φ : Q.Potential k) {u v : Q.Vertex}
    (f : Q.GinzburgPathComponent k u v) :
    Q.ginzburgDifferential k φ u v (Q.ginzburgDifferential k φ u v f)=0 := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add,hf,hg,add_zero]
  | single p c =>
    have hp := Q.ginzburgDifferential_square_single k φ p
    simp only [ginzburgDifferential_single,one_smul] at hp
    simp only [ginzburgDifferential_single,map_smul,hp,smul_zero]

theorem ginzburgDifferential_comp_self (φ : Q.Potential k) (u v : Q.Vertex) :
    (Q.ginzburgDifferential k φ u v).comp (Q.ginzburgDifferential k φ u v)=0 := by
  apply LinearMap.ext
  intro f
  exact Q.ginzburgDifferential_square k φ f

end ASGinzburg.CutQuiver
