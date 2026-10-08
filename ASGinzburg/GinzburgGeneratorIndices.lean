import ASGinzburg.GinzburgGrading
import ASGinzburg.ASResolution

/-! The three actual last-generator families are exactly the incoming
arrows, outgoing arrows at the previous sheet, and one vertex loop. -/
namespace ASGinzburg.CutQuiver
variable (Q : CutQuiver)

abbrev GinzburgIncomingDegree (v : Q.Vertex) (r : ℤ) :=
  {a : Q.GinzburgArrow // a.target Q=v ∧ a.cohomologicalDegree Q=r}

noncomputable def ginzburgOriginalGeneratorEquiv (v : Q.LiftVertex) :
    Q.incomingArrows v ≃ Q.GinzburgIncomingDegree v.1 0 :=
  Equiv.ofBijective (fun a => ⟨.original a.val,a.property,rfl⟩) (by
    constructor
    · intro a b h
      apply Subtype.ext
      exact GinzburgArrow.original.inj (congrArg Subtype.val h)
    · rintro ⟨a,ht,hd⟩
      cases a with
      | original a => exact ⟨⟨a,ht⟩,rfl⟩
      | dual a => norm_num [GinzburgArrow.cohomologicalDegree] at hd
      | loop w => norm_num [GinzburgArrow.cohomologicalDegree] at hd)

noncomputable def ginzburgDualGeneratorEquiv (v : Q.LiftVertex) :
    Q.outgoingArrows (Q.tau.symm v) ≃ Q.GinzburgIncomingDegree v.1 (-1) :=
  Equiv.ofBijective (fun a => ⟨.dual a.val,a.property,rfl⟩) (by
    constructor
    · intro a b h
      apply Subtype.ext
      exact GinzburgArrow.dual.inj (congrArg Subtype.val h)
    · rintro ⟨a,ht,hd⟩
      cases a with
      | original a => norm_num [GinzburgArrow.cohomologicalDegree] at hd
      | dual a => exact ⟨⟨a,ht⟩,rfl⟩
      | loop w => norm_num [GinzburgArrow.cohomologicalDegree] at hd)

noncomputable def ginzburgLoopGeneratorEquiv (v : Q.LiftVertex) :
    PUnit.{1} ≃ Q.GinzburgIncomingDegree v.1 (-2) :=
  Equiv.ofBijective (fun _ => ⟨.loop v.1,rfl,rfl⟩) (by
    constructor
    · intro a b _h
      exact Subsingleton.elim a b
    · rintro ⟨a,ht,hd⟩
      cases a with
      | original a => norm_num [GinzburgArrow.cohomologicalDegree] at hd
      | dual a => norm_num [GinzburgArrow.cohomologicalDegree] at hd
      | loop w =>
        change w=v.1 at ht
        subst w
        exact ⟨PUnit.unit,rfl⟩)

@[simp] theorem ginzburgOriginalGeneratorEquiv_apply_val (v : Q.LiftVertex)
    (a : Q.incomingArrows v) :
    (Q.ginzburgOriginalGeneratorEquiv v a).val=.original a.val := rfl

@[simp] theorem ginzburgDualGeneratorEquiv_apply_val (v : Q.LiftVertex)
    (a : Q.outgoingArrows (Q.tau.symm v)) :
    (Q.ginzburgDualGeneratorEquiv v a).val=.dual a.val := rfl

@[simp] theorem ginzburgLoopGeneratorEquiv_apply_val (v : Q.LiftVertex) (a : PUnit.{1}) :
    (Q.ginzburgLoopGeneratorEquiv v a).val=.loop v.1 := rfl

theorem ginzburgOriginalGeneratorPrefixLift (x v : Q.LiftVertex) (a : Q.incomingArrows v) :
    ((Q.ginzburgOriginalGeneratorEquiv v a).val.source Q,
      x.2+(v.2-x.2-(Q.ginzburgOriginalGeneratorEquiv v a).val.cutDegree Q))=
        Q.incomingSource v a := by
  apply Prod.ext
  · rfl
  · change x.2+(v.2-x.2-Q.cutDegree a.val)=v.2-Q.cutDegree a.val
    omega

theorem ginzburgDualGeneratorPrefixLift (x v : Q.LiftVertex)
    (a : Q.outgoingArrows (Q.tau.symm v)) :
    ((Q.ginzburgDualGeneratorEquiv v a).val.source Q,
      x.2+(v.2-x.2-(Q.ginzburgDualGeneratorEquiv v a).val.cutDegree Q))=
        Q.outgoingTarget (Q.tau.symm v) a := by
  apply Prod.ext
  · rfl
  · change x.2+(v.2-x.2-(1-Q.cutDegree a.val))=(v.2-1)+Q.cutDegree a.val
    omega

theorem ginzburgLoopGeneratorPrefixLift (x v : Q.LiftVertex) (a : PUnit.{1}) :
    ((Q.ginzburgLoopGeneratorEquiv v a).val.source Q,
      x.2+(v.2-x.2-(Q.ginzburgLoopGeneratorEquiv v a).val.cutDegree Q))=Q.tau.symm v := by
  apply Prod.ext
  · rfl
  · change x.2+(v.2-x.2-1)=v.2-1
    omega

end ASGinzburg.CutQuiver
