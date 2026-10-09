import ASGinzburg.GinzburgHessianEntryReflection
import ASGinzburg.GinzburgOppositeConcreteIndices

/-! The unchanged complete native Hessian matrix transposes under the
actual generator-family equivalences and reflected Jacobian components. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgHomTransport_heq (φ : Q.Potential k)
    (i j i' j' : ℤ) (hi : i=i') (hj : j=j')
    (f : (Q.unrolledJacobianZAlgebra k φ).Hom i j) :
    HEq ((Q.unrolledJacobianZAlgebra k φ).homTransport i j i' j' hi hj f) f := by
  subst i'
  subst j'
  rfl

theorem ginzburgGeneratorHessianEntry_heq_of_eq (φ : Q.Potential k)
    {v v' : Q.LiftVertex} (hv : v=v')
    (a : Q.GinzburgIncomingDegree v.1 (-1))
    (a' : Q.GinzburgIncomingDegree v'.1 (-1)) (ha : a.val=a'.val)
    (b : Q.GinzburgIncomingDegree v.1 0)
    (b' : Q.GinzburgIncomingDegree v'.1 0) (hb : b.val=b'.val) :
    HEq (Q.ginzburgGeneratorHessianEntry k φ v a b)
      (Q.ginzburgGeneratorHessianEntry k φ v' a' b') := by
  subst v'
  have haa : a=a' := Subtype.ext ha
  have hbb : b=b' := Subtype.ext hb
  subst a'
  subst b'
  rfl

theorem ginzburgDualOppositeBase_eq (v : Q.LiftVertex) :
    Q.ginzburgDualOppositeBase v=(v.1.rev,1-v.2) := by
  apply Prod.ext
  · rfl
  · change -(v.2-1)=1-v.2
    omega

theorem ginzburgGeneratorHessianEntry_opposite (φ : Q.Potential k)
    (v : Q.LiftVertex) (a : Q.GinzburgIncomingDegree v.1 (-1))
    (b : Q.GinzburgIncomingDegree v.1 0) :
    (Q.opposite.unrolledJacobianZAlgebra k (Q.oppositePotentialEquiv k φ)).homTransport
      _ _ _ _
      (congrArg Q.opposite.height (Q.ginzburgOriginalOppositeDualEndpoint v b).symm)
      (congrArg Q.opposite.height (Q.ginzburgDualOppositeOriginalEndpoint v a).symm)
      (Q.oppositeUnrolledJacobianHomEquiv k φ
        (Q.ginzburgPrefixGeneratorEndpoint v a.val)
        (Q.ginzburgPrefixGeneratorEndpoint v b.val)
        (Q.ginzburgGeneratorHessianEntry k φ v a b))=
      Q.opposite.ginzburgGeneratorHessianEntry k (Q.oppositePotentialEquiv k φ)
        (Q.ginzburgDualOppositeBase v)
        (Q.ginzburgOriginalOppositeDualEquiv v b)
        (Q.ginzburgDualOppositeOriginalEquiv v a) := by
  rcases v with ⟨v,s⟩
  obtain ⟨a,ha,hda⟩ := a
  cases a with
  | original a => norm_num [GinzburgArrow.cohomologicalDegree] at hda
  | loop w => norm_num [GinzburgArrow.cohomologicalDegree] at hda
  | dual a =>
    change Q.source a=v at ha
    subst v
    obtain ⟨b,hb,hdb⟩ := b
    cases b with
    | dual b => norm_num [GinzburgArrow.cohomologicalDegree] at hdb
    | loop w => norm_num [GinzburgArrow.cohomologicalDegree] at hdb
    | original b =>
      change Q.target b=Q.source a at hb
      have hbo := Q.ginzburgOriginalOppositeDualEquiv_concrete (Q.source a,s) b hb
      have hao := Q.ginzburgDualOppositeOriginalEquiv_concrete (Q.source a,s) a rfl
      have h := Q.ginzburgGeneratorHessianEntry_opposite_raw k φ a b s hb
      have hs : Q.opposite.source b=(Q.source a).rev := by
        change (Q.target b).rev=(Q.source a).rev
        rw [hb]
      have hv : (Q.opposite.source b,1-s)=Q.ginzburgDualOppositeBase (Q.source a,s) := by
        rw [Q.ginzburgDualOppositeBase_eq]
        exact Prod.ext hs rfl
      have hr := Q.opposite.ginzburgGeneratorHessianEntry_heq_of_eq k
        (Q.oppositePotentialEquiv k φ) hv
        (⟨.dual b,rfl,rfl⟩ : Q.opposite.GinzburgIncomingDegree (Q.opposite.source b) (-1))
        (Q.ginzburgOriginalOppositeDualEquiv (Q.source a,s) ⟨.original b,hb,rfl⟩)
        (congrArg Subtype.val hbo).symm
        (⟨.original a,Q.ginzburgHessianOppositeArrowIncidence a b hb,rfl⟩ :
          Q.opposite.GinzburgIncomingDegree (Q.opposite.source b) 0)
        (Q.ginzburgDualOppositeOriginalEquiv (Q.source a,s) ⟨.dual a,rfl,rfl⟩)
        (congrArg Subtype.val hao).symm
      apply eq_of_heq
      exact (Q.opposite.ginzburgHomTransport_heq k (Q.oppositePotentialEquiv k φ)
        _ _ _ _ _ _ _).trans
        ((Q.opposite.ginzburgHomTransport_heq k (Q.oppositePotentialEquiv k φ)
          _ _ _ _ _ _ _).symm.trans ((heq_of_eq h).trans hr))

end ASGinzburg.CutQuiver
