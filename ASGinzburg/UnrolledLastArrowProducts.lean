import ASGinzburg.UnrolledLastArrowReconstruction

/-! Multiplication respects genuine last-arrow extension. These are
equalities of actual free-path elements used in the ideal-product proof. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem unrolledPathComp_mapDomain_snoc {u v w : Q.LiftVertex}
    (a : Q.incomingArrows w)
    (g : Q.UnrolledPathComponent k v (Q.incomingSource w a))
    (f : Q.UnrolledPathComponent k u v) :
    Q.unrolledPathComp k (g.mapDomain (UnrolledPath.snoc a)) f=
      (Q.unrolledPathComp k g f).mapDomain (UnrolledPath.snoc a) := by
  classical
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add g h hg hh => simp [Finsupp.mapDomain_add,map_add,LinearMap.add_apply,hg,hh]
  | single q c =>
      induction f using Finsupp.induction_linear with
      | zero => simp
      | add f h hf hh => simp only [map_add,Finsupp.mapDomain_add,hf,hh]
      | single p d => simp [Finsupp.mapDomain_single,UnrolledPath.comp]

theorem unrolledPathComp_lastArrow {u w : Q.LiftVertex}
    (a : Q.incomingArrows w) (f : Q.UnrolledPathComponent k u (Q.incomingSource w a)) :
    Q.unrolledPathComp k
      (Finsupp.single (UnrolledPath.snoc a (.nil (Q.incomingSource w a))) 1) f=
        f.mapDomain (UnrolledPath.snoc a) := by
  rw [←Finsupp.mapDomain_single,Q.unrolledPathComp_mapDomain_snoc]
  change (Q.unrolledPathComp k (Q.unrolledPathId k _) f).mapDomain _=_
  rw [Q.unrolledPathComp_id]

end ASGinzburg.CutQuiver
