import ASGinzburg.ArbitraryArrowKernelHeights
import ASGinzburg.BetweenSheetJacobianIdeals

/-! In cut degree zero, every genuine Jacobian context uses a cut
derivative. Thus annihilating the cut derivatives suffices on same-sheet
components, without assuming anything about the other derivatives. -/
namespace ASGinzburg.ZAlgebra
open CutQuiver
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)
variable (G : A.IncomingElementFamily Q) (φ : Q.Potential k)
variable (hcut : ∀ a : Q.Arrow, Q.cut a=true → ∀ m : ℤ,
  A.arrowPathLinearEvaluation Q G (Q.target a,m)
    (Q.source a,m+((1-Q.cutDegree a:ℕ):ℤ)) (Q.unrolledJacobianRelation k a φ m)=0)
include hcut

theorem arrowPathLinearEvaluation_zeroCutJacobianContext
    (x y : Q.LiftVertex) (hs : x.2=y.2) (a : Q.Arrow)
    (l : Q.Path x.1 (Q.target a)) (r : Q.Path (Q.source a) y.1)
    (hdeg : (Q.pathJacobianContextDegree a l r:ℤ)=y.2-x.2) :
    A.arrowPathLinearEvaluation Q G x y (Q.betweenSheetLinearEquiv k x y
      ⟨Q.pathComp k (Finsupp.single r 1)
        (Q.pathComp k (Q.pathCyclicDerivative k a φ) (Finsupp.single l 1)),by
          rw [←hdeg]; exact Q.pathJacobianContext_mem_cut k φ a l r⟩) = 0 := by
  have ha : Q.cut a=true := by
    by_cases ha : Q.cut a=true
    · exact ha
    · have hf : Q.cut a=false := Bool.eq_false_of_not_eq_true ha
      have hd := hdeg
      simp only [pathJacobianContextDegree, Q.cutDegree_false hf, Nat.sub_zero,
        Nat.cast_add, Nat.cast_one] at hd
      omega
  let t : Q.LiftVertex := (Q.target a,x.2+(l.cutDegree:ℤ))
  let s : Q.LiftVertex := (Q.source a,t.2+((1-Q.cutDegree a:ℕ):ℤ))
  let pl : Q.UnrolledPath x t := Path.unrollBetween x.1 (Q.target a) x.2 t.2
    ⟨l,by dsimp [t]; omega⟩
  let pr : Q.UnrolledPath s y := Path.unrollBetween (Q.source a) y.1 s.2 y.2
    ⟨r,by
      simp only [pathJacobianContextDegree,Nat.cast_add] at hdeg
      dsimp [s,t]; omega⟩
  let rel : Q.UnrolledPathComponent k t s := Q.unrolledJacobianRelation k a φ t.2
  let f : Q.UnrolledPathComponent k x y := Q.unrolledPathComp k (Finsupp.single pr 1)
    (Q.unrolledPathComp k rel (Finsupp.single pl 1))
  have hrel : A.arrowPathLinearEvaluation Q G t s rel=0 := hcut a ha t.2
  have heq : Q.betweenSheetLinearEquiv k x y
      ⟨Q.pathComp k (Finsupp.single r 1)
        (Q.pathComp k (Q.pathCyclicDerivative k a φ) (Finsupp.single l 1)),by
          rw [←hdeg]; exact Q.pathJacobianContext_mem_cut k φ a l r⟩=f := by
    apply Q.unrolledPathEraseLinearMap_injective k
    rw [Q.betweenSheetLinearEquiv_erase]
    change _=Q.unrolledPathEraseLinearMap k x y
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
  dsimp only [f]
  rw [A.arrowPathLinearEvaluation_comp,A.arrowPathLinearEvaluation_comp,hrel,map_zero]
  simp

theorem arrowPathLinearEvaluation_zeroCutJacobianProjection
    (x y : Q.LiftVertex) (hs : x.2=y.2) {f : Q.PathComponent k x.1 y.1}
    (hf : f ∈ (Q.pathJacobianIdeal k φ).hom x.1 y.1) :
    A.arrowPathLinearEvaluation Q G x y (Q.betweenSheetProjectionMap k x y f)=0 := by
  rw [Q.pathJacobianIdeal_eq_contextSpan] at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a,l,r,rfl⟩ := hf
    by_cases hd : (Q.pathJacobianContextDegree a l r:ℤ)=y.2-x.2
    · rw [Q.betweenSheetProjectionMap_on_cut k x y
        (by rw [←hd]; exact Q.pathJacobianContext_mem_cut k φ a l r)]
      exact A.arrowPathLinearEvaluation_zeroCutJacobianContext Q G φ hcut x y hs a l r hd
    · rw [Q.betweenSheetProjectionMap_on_other_cut k x y
        (Q.pathJacobianContext_mem_cut k φ a l r) hd,map_zero]
  | zero => simp
  | add f g hf hg ihf ihg => simp only [map_add,ihf,ihg,add_zero]
  | smul c f hf ih => simp only [map_smul,ih,smul_zero]

theorem arrowPathLinearEvaluation_zeroCutJacobianLift
    (x y : Q.LiftVertex) (hs : x.2=y.2) {f : Q.UnrolledPathComponent k x y}
    (hf : f ∈ Q.unrolledJacobianLiftIdeal k φ x y) :
    A.arrowPathLinearEvaluation Q G x y f=0 := by
  let g := (Q.betweenSheetLinearEquiv k x y).symm f
  have hg : g.val ∈ (Q.pathJacobianIdeal k φ).hom x.1 y.1 := by
    dsimp only [g]
    rw [Q.betweenSheetLinearEquiv_symm_coe]
    exact Q.unrolledJacobianLiftIdeal_erase k φ hf
  have h := A.arrowPathLinearEvaluation_zeroCutJacobianProjection Q G φ hcut x y hs hg
  rw [Q.betweenSheetProjectionMap_on_cut k x y g.property,
    LinearEquiv.apply_symm_apply] at h
  exact h

end ASGinzburg.ZAlgebra
