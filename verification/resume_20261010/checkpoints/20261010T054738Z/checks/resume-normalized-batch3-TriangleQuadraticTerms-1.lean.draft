import ASGinzburg.Triangle333
import ASGinzburg.ASResolution

/-! The concrete terms of the triangle AS sequence are the three copies
in (5.1). The index and height identifications do not assume periodicity. -/

namespace ASGinzburg

/-- The three incoming arrows at any lifted triangle vertex. -/
def triangleIncomingArrowEquiv (v : triangle333.LiftVertex) :
    triangle333.incomingArrows v ≃ Fin 3 where
  toFun a := ⟨a.val.val % 3, Nat.mod_lt _ (by decide)⟩
  invFun i := ⟨⟨3 * ((v.1.val + 2) % 3) + i.val, by
    change 3 * ((v.1.val + 2) % 3) + i.val < 9
    have hi := i.isLt
    have hv := Nat.mod_lt (v.1.val + 2) (by decide : 0 < 3)
    omega⟩, by
    apply Fin.ext
    change ((3 * ((v.1.val + 2) % 3) + i.val) / 3 + 1) % 3 = v.1.val
    have hi := i.isLt
    have hv : v.1.val < 3 := v.1.isLt
    omega⟩
  left_inv a := by
    apply Subtype.ext
    apply Fin.ext
    have ha : a.val.val < 9 := a.val.isLt
    have hv : v.1.val < 3 := v.1.isLt
    have h := congrArg Fin.val a.property
    change (a.val.val / 3 + 1) % 3 = v.1.val at h
    change 3 * ((v.1.val + 2) % 3) + a.val.val % 3 = a.val.val
    omega
  right_inv i := by
    apply Fin.ext
    change (3 * ((v.1.val + 2) % 3) + i.val) % 3 = i.val
    have hi := i.isLt
    omega

/-- The three outgoing arrows at any lifted triangle vertex. -/
def triangleOutgoingArrowEquiv (v : triangle333.LiftVertex) :
    triangle333.outgoingArrows v ≃ Fin 3 where
  toFun a := ⟨a.val.val % 3, Nat.mod_lt _ (by decide)⟩
  invFun i := ⟨⟨3 * v.1.val + i.val, by
    change 3 * v.1.val + i.val < 9
    have hi := i.isLt
    have hv : v.1.val < 3 := v.1.isLt
    omega⟩, by
    apply Fin.ext
    change (3 * v.1.val + i.val) / 3 = v.1.val
    have hi := i.isLt
    omega⟩
  left_inv a := by
    apply Subtype.ext
    apply Fin.ext
    have ha : a.val.val < 9 := a.val.isLt
    have h := congrArg Fin.val a.property
    change a.val.val / 3 = v.1.val at h
    change 3 * v.1.val + a.val.val % 3 = a.val.val
    omega
  right_inv i := by
    apply Fin.ext
    change (3 * v.1.val + i.val) % 3 = i.val
    have hi := i.isLt
    omega

theorem triangleIncomingSource_height (v : triangle333.LiftVertex)
    (a : triangle333.incomingArrows v) :
    triangle333.height (triangle333.incomingSource v a) = triangle333.height v - 1 := by
  have h := triangle333.lifted_height_difference a.val (v.2 - triangle333.cutDegree a.val)
  rw [triangle333.incoming_liftedTarget, triangle_arrow_winding] at h
  change triangle333.height v - triangle333.height (triangle333.incomingSource v a) = 1 at h
  omega

theorem triangleOutgoingTarget_height (v : triangle333.LiftVertex)
    (a : triangle333.outgoingArrows v) :
    triangle333.height (triangle333.outgoingTarget v a) = triangle333.height v + 1 := by
  have h := triangle333.lifted_height_difference a.val v.2
  rw [triangle333.outgoing_liftedSource, triangle_arrow_winding] at h
  change triangle333.height (triangle333.outgoingTarget v a) - triangle333.height v = 1 at h
  omega

theorem triangleTauInverse_height (v : triangle333.LiftVertex) :
    triangle333.height (triangle333.tau.symm v) = triangle333.height v - 3 := by
  have h := triangle333.height_tau (triangle333.tau.symm v)
  simp only [Equiv.apply_symm_apply] at h
  change triangle333.height v = triangle333.height (triangle333.tau.symm v) + 3 at h
  omega

end ASGinzburg

namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k)

/-- Actual threefold coproduct of one representable. -/
noncomputable def quadraticTriple (i : ℤ) : A.RightModule :=
  ∐ fun _ : Fin 3 => A.representable i

noncomputable def triangleASFirstTermIso (v : triangle333.LiftVertex) :
    A.asResolutionTerm₁ triangle333 v ≅ A.quadraticTriple (triangle333.height v - 1) := by
  let g := fun a : triangle333.incomingArrows v =>
    A.representable (triangle333.height (triangle333.incomingSource v a))
  refine (Sigma.reindex (triangleIncomingArrowEquiv v).symm g).symm ≪≫ ?_
  exact Sigma.mapIso (fun i => eqToIso (congrArg A.representable
    (triangleIncomingSource_height v ((triangleIncomingArrowEquiv v).symm i))))

noncomputable def triangleASSecondTermIso (v : triangle333.LiftVertex) :
    A.asResolutionTerm₂ triangle333 v ≅ A.quadraticTriple (triangle333.height v - 2) := by
  let g := fun a : triangle333.outgoingArrows (triangle333.tau.symm v) =>
    A.representable (triangle333.height (triangle333.outgoingTarget (triangle333.tau.symm v) a))
  refine (Sigma.reindex (triangleOutgoingArrowEquiv (triangle333.tau.symm v)).symm g).symm ≪≫ ?_
  apply Sigma.mapIso
  intro i
  apply eqToIso
  dsimp only [g, Function.comp_def]
  congr 1
  rw [triangleOutgoingTarget_height, triangleTauInverse_height]
  omega

noncomputable def triangleASTopTermIso (v : triangle333.LiftVertex) :
    A.representable (triangle333.height (triangle333.tau.symm v)) ≅
      A.representable (triangle333.height v - 3) :=
  eqToIso (congrArg A.representable (triangleTauInverse_height v))

end ASGinzburg.ZAlgebra
