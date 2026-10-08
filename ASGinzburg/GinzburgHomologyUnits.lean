import ASGinzburg.GinzburgJacobianProducts

/-! Actual zero-path units and associativity on mathlib H-zero. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def ginzburgZeroId (u : Q.Vertex) :
    Q.ginzburgCohomologicalComponent k u u 0 :=
  Q.originalGinzburgDegreeZeroEquiv k u u (Q.pathId k u)

theorem ginzburgZeroId_val (u : Q.Vertex) :
    (Q.ginzburgZeroId k u).val=Q.ginzburgPathId k u :=
  Q.originalGinzburgLinearMap_id k u

theorem ginzburgZeroComp_id {u v : Q.Vertex}
    (f : Q.ginzburgCohomologicalComponent k u v 0) :
    Q.ginzburgZeroComp k (Q.ginzburgZeroId k v) f=f := by
  apply Subtype.ext
  change Q.ginzburgPathComp k (Q.ginzburgZeroId k v).val f.val=f.val
  rw [Q.ginzburgZeroId_val,Q.ginzburgPathComp_id]

theorem id_ginzburgZeroComp {u v : Q.Vertex}
    (f : Q.ginzburgCohomologicalComponent k u v 0) :
    Q.ginzburgZeroComp k f (Q.ginzburgZeroId k u)=f := by
  apply Subtype.ext
  change Q.ginzburgPathComp k f.val (Q.ginzburgZeroId k u).val=f.val
  rw [Q.ginzburgZeroId_val,Q.id_ginzburgPathComp]

theorem ginzburgZeroComp_assoc {u v w x : Q.Vertex}
    (f : Q.ginzburgCohomologicalComponent k u v 0)
    (g : Q.ginzburgCohomologicalComponent k v w 0)
    (h : Q.ginzburgCohomologicalComponent k w x 0) :
    Q.ginzburgZeroComp k h (Q.ginzburgZeroComp k g f)=
      Q.ginzburgZeroComp k (Q.ginzburgZeroComp k h g) f := by
  apply Subtype.ext
  exact Q.ginzburgPathComp_assoc k f.val g.val h.val

noncomputable def ginzburgHomologyZeroId (φ : Q.Potential k) (u : Q.Vertex) :
    Q.ginzburgHomology k φ u u 0 :=
  Q.ginzburgZeroHomologyClass k φ u u (Q.ginzburgZeroId k u)

theorem ginzburgHomologyZeroComp_id (φ : Q.Potential k) {u v : Q.Vertex}
    (f : Q.ginzburgHomology k φ u v 0) :
    Q.ginzburgHomologyZeroComp k φ (Q.ginzburgHomologyZeroId k φ v) f=f := by
  obtain ⟨f,rfl⟩ := Q.ginzburgZeroHomologyClass_surjective k φ u v f
  rw [ginzburgHomologyZeroId,Q.ginzburgHomologyZeroComp_class,Q.ginzburgZeroComp_id]

theorem id_ginzburgHomologyZeroComp (φ : Q.Potential k) {u v : Q.Vertex}
    (f : Q.ginzburgHomology k φ u v 0) :
    Q.ginzburgHomologyZeroComp k φ f (Q.ginzburgHomologyZeroId k φ u)=f := by
  obtain ⟨f,rfl⟩ := Q.ginzburgZeroHomologyClass_surjective k φ u v f
  rw [ginzburgHomologyZeroId,Q.ginzburgHomologyZeroComp_class,Q.id_ginzburgZeroComp]

theorem ginzburgHomologyZeroComp_assoc (φ : Q.Potential k) {u v w x : Q.Vertex}
    (f : Q.ginzburgHomology k φ u v 0)
    (g : Q.ginzburgHomology k φ v w 0)
    (h : Q.ginzburgHomology k φ w x 0) :
    Q.ginzburgHomologyZeroComp k φ h (Q.ginzburgHomologyZeroComp k φ g f)=
      Q.ginzburgHomologyZeroComp k φ (Q.ginzburgHomologyZeroComp k φ h g) f := by
  obtain ⟨f,rfl⟩ := Q.ginzburgZeroHomologyClass_surjective k φ u v f
  obtain ⟨g,rfl⟩ := Q.ginzburgZeroHomologyClass_surjective k φ v w g
  obtain ⟨h,rfl⟩ := Q.ginzburgZeroHomologyClass_surjective k φ w x h
  rw [Q.ginzburgHomologyZeroComp_class,Q.ginzburgHomologyZeroComp_class,
    Q.ginzburgHomologyZeroComp_class,Q.ginzburgHomologyZeroComp_class,
    Q.ginzburgZeroComp_assoc]

theorem ginzburgHomologyZeroJacobianIso_id (φ : Q.Potential k) (u : Q.Vertex) :
    (Q.ginzburgHomologyZeroJacobianIso k φ u u).hom (Q.ginzburgHomologyZeroId k φ u)=
      Submodule.Quotient.mk (Q.pathId k u) := by
  let e := Q.ginzburgHomologyZeroJacobianIso k φ u u
  let x := e.inv (Submodule.Quotient.mk (Q.pathId k u))
  have hx : e.hom x=Submodule.Quotient.mk (Q.pathId k u) := by
    dsimp [x]
    simp
  have h := Q.ginzburgHomologyZeroJacobianIso_comp k φ x (Q.ginzburgHomologyZeroId k φ u)
  rw [Q.ginzburgHomologyZeroComp_id] at h
  change e.hom x=(Q.pathJacobianIdeal k φ).quotientComp (e.hom _) (e.hom x) at h
  rw [hx,(Q.pathJacobianIdeal k φ).id_quotientComp] at h
  exact h.symm

end ASGinzburg.CutQuiver
