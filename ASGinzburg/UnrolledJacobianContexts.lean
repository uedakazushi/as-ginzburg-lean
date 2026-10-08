import ASGinzburg.UnrolledJacobianLiftIdeal
import ASGinzburg.BetweenSheetLinearEquiv
import ASGinzburg.PathJacobianHomogeneousContexts

/-! An actual homogeneous relation context lifts to the genuine
unrolled Jacobian ideal at every compatible pair of endpoint sheets. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem unrolledJacobianContext_mem_liftIdeal (φ : Q.Potential k)
    (u v : Q.LiftVertex) (a : Q.Arrow)
    (l : Q.Path u.1 (Q.target a)) (r : Q.Path (Q.source a) v.1)
    (hdeg : (Q.pathJacobianContextDegree a l r:ℤ)=v.2-u.2) :
    Q.betweenSheetLinearEquiv k u v
      ⟨Q.pathComp k (Finsupp.single r 1)
        (Q.pathComp k (Q.pathCyclicDerivative k a φ) (Finsupp.single l 1)),by
          rw [←hdeg]
          exact Q.pathJacobianContext_mem_cut k φ a l r⟩ ∈
      Q.unrolledJacobianLiftIdeal k φ u v := by
  let t : Q.LiftVertex := (Q.target a,u.2+(l.cutDegree:ℤ))
  let s : Q.LiftVertex := (Q.source a,t.2+((1-Q.cutDegree a:ℕ):ℤ))
  let pl : Q.UnrolledPath u t := Path.unrollBetween u.1 (Q.target a) u.2 t.2
    ⟨l,by dsimp [t]; omega⟩
  let pr : Q.UnrolledPath s v := Path.unrollBetween (Q.source a) v.1 s.2 v.2
    ⟨r,by
      simp only [pathJacobianContextDegree,Nat.cast_add] at hdeg
      dsimp [s,t]
      omega⟩
  let rel : Q.UnrolledPathComponent k t s := Q.unrolledJacobianRelation k a φ t.2
  let f : Q.UnrolledPathComponent k u v := Q.unrolledPathComp k (Finsupp.single pr 1)
    (Q.unrolledPathComp k rel (Finsupp.single pl 1))
  have hrel : rel ∈ Q.unrolledJacobianLiftIdeal k φ t s :=
    Q.unrolledJacobianRelation_mem_liftIdeal k φ a t.2
  have hf : f ∈ Q.unrolledJacobianLiftIdeal k φ u v :=
    Q.unrolledJacobianLiftIdeal_comp_left k φ
      (Q.unrolledJacobianLiftIdeal_comp_right k φ hrel (Finsupp.single pl 1))
        (Finsupp.single pr 1)
  have heq : Q.betweenSheetLinearEquiv k u v
      ⟨Q.pathComp k (Finsupp.single r 1)
        (Q.pathComp k (Q.pathCyclicDerivative k a φ) (Finsupp.single l 1)),by
          rw [←hdeg]
          exact Q.pathJacobianContext_mem_cut k φ a l r⟩=f := by
    apply Q.unrolledPathEraseLinearMap_injective k
    rw [Q.betweenSheetLinearEquiv_erase]
    change _=Q.unrolledPathEraseLinearMap k u v
      (Q.unrolledPathComp k (Finsupp.single pr 1)
        (Q.unrolledPathComp k rel (Finsupp.single pl 1)))
    rw [Q.unrolledPathEraseLinearMap_comp,Q.unrolledPathEraseLinearMap_comp,
      Q.unrolledPathEraseLinearMap_single,Q.unrolledPathEraseLinearMap_single]
    change _=Q.pathComp k (Finsupp.single pr.erase 1)
      (Q.pathComp k (Q.unrolledPathEraseLinearMap k t s
        (Q.unrolledJacobianRelation k a φ t.2)) (Finsupp.single pl.erase 1))
    rw [Q.unrolledJacobianRelation_erase]
    have hl : pl.erase=l := Path.unrollBetween_erase _ _ _ _ _
    have hr : pr.erase=r := Path.unrollBetween_erase _ _ _ _ _
    rw [hl,hr]
  rw [heq]
  exact hf

end ASGinzburg.CutQuiver
