import ASGinzburg.OppositePathEquiv

/-! Reversal is anti-multiplicative on the genuine linear path algebra. -/
namespace ASGinzburg.CutQuiver
universe u
variable {Q : CutQuiver}

theorem Path.opposite_comp {u v w : Q.Vertex} (p : Q.Path u v) (q : Q.Path v w) :
    (p.comp q).opposite = q.opposite.comp p.opposite := by
  apply Path.toList_injective (Q := Q.opposite) w.rev u.rev
  simp [Path.opposite_toList, Path.toList_comp, List.reverse_append]

variable (Q) (k : Type u) [Field k]

noncomputable def oppositePathComponentEquiv (u v : Q.Vertex) :
    Q.PathComponent k u v ≃ₗ[k] Q.opposite.PathComponent k v.rev u.rev :=
  Finsupp.domLCongr (oppositePathEquiv u v)

@[simp] theorem oppositePathComponentEquiv_single {u v : Q.Vertex}
    (p : Q.Path u v) (a : k) :
    Q.oppositePathComponentEquiv k u v (Finsupp.single p a) =
      Finsupp.single p.opposite a := by
  simp only [oppositePathComponentEquiv, Finsupp.domLCongr_single, oppositePathEquiv]
  rfl

theorem oppositePathComponentEquiv_comp {u v w : Q.Vertex}
    (f : Q.PathComponent k u v) (g : Q.PathComponent k v w) :
    Q.oppositePathComponentEquiv k u w (Q.pathComp k g f) =
      Q.opposite.pathComp k (Q.oppositePathComponentEquiv k u v f)
        (Q.oppositePathComponentEquiv k v w g) := by
  classical
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add g h ihg ihh => simp [map_add, ihg, ihh]
  | single q b =>
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f h ihf ihh => simp [map_add, LinearMap.add_apply, ihf, ihh]
    | single p a => simp [Path.opposite_comp, mul_comm]

@[simp] theorem oppositePathComponentEquiv_id (v : Q.Vertex) :
    Q.oppositePathComponentEquiv k v v (Q.pathId k v) =
      Q.opposite.pathId k v.rev := by
  simp [pathId]

end ASGinzburg.CutQuiver
