import ASGinzburg.GinzburgCutJacobianProducts

/-! Actual zero-path units and associativity on fixed-cut mathlib H-zero. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def ginzburgCutZeroId (u : Q.LiftVertex) :
    Q.ginzburgCutCohomologicalComponent k u.1 u.1 0 (u.2-u.2) :=
  Q.originalGinzburgCutDegreeZeroEquiv k u.1 u.1 (u.2-u.2)
    ⟨Q.pathId k u.1,by
      change Finsupp.single (Path.nil u.1) 1 ∈ Finsupp.supported k k _
      apply Finsupp.single_mem_supported
      simp [Path.cutDegree]⟩

theorem ginzburgCutZeroId_val (u : Q.LiftVertex) :
    (Q.ginzburgCutZeroId k u).val=Q.ginzburgPathId k u.1 :=
  Q.originalGinzburgLinearMap_id k u.1

theorem ginzburgCutZeroComp_id {u v : Q.LiftVertex}
    (f : Q.ginzburgCutCohomologicalComponent k u.1 v.1 0 (v.2-u.2)) :
    Q.ginzburgCutZeroComp k (Q.ginzburgCutZeroId k v) f=f := by
  apply Subtype.ext
  change Q.ginzburgPathComp k (Q.ginzburgCutZeroId k v).val f.val=f.val
  rw [Q.ginzburgCutZeroId_val,Q.ginzburgPathComp_id]

theorem id_ginzburgCutZeroComp {u v : Q.LiftVertex}
    (f : Q.ginzburgCutCohomologicalComponent k u.1 v.1 0 (v.2-u.2)) :
    Q.ginzburgCutZeroComp k f (Q.ginzburgCutZeroId k u)=f := by
  apply Subtype.ext
  change Q.ginzburgPathComp k f.val (Q.ginzburgCutZeroId k u).val=f.val
  rw [Q.ginzburgCutZeroId_val,Q.id_ginzburgPathComp]

theorem ginzburgCutZeroComp_assoc {u v w x : Q.LiftVertex}
    (f : Q.ginzburgCutCohomologicalComponent k u.1 v.1 0 (v.2-u.2))
    (g : Q.ginzburgCutCohomologicalComponent k v.1 w.1 0 (w.2-v.2))
    (h : Q.ginzburgCutCohomologicalComponent k w.1 x.1 0 (x.2-w.2)) :
    Q.ginzburgCutZeroComp k h (Q.ginzburgCutZeroComp k g f)=
      Q.ginzburgCutZeroComp k (Q.ginzburgCutZeroComp k h g) f := by
  apply Subtype.ext
  exact Q.ginzburgPathComp_assoc k f.val g.val h.val

noncomputable def ginzburgCutHomologyZeroId (φ : Q.Potential k) (u : Q.LiftVertex) :
    Q.ginzburgCutHomology k φ u.1 u.1 (u.2-u.2) 0 :=
  Q.ginzburgCutZeroHomologyClass k φ u u (Q.ginzburgCutZeroId k u)

theorem ginzburgCutHomologyZeroComp_id (φ : Q.Potential k) {u v : Q.LiftVertex}
    (f : Q.ginzburgCutHomology k φ u.1 v.1 (v.2-u.2) 0) :
    Q.ginzburgCutHomologyZeroComp k φ (Q.ginzburgCutHomologyZeroId k φ v) f=f := by
  obtain ⟨f,rfl⟩ := Q.ginzburgCutZeroHomologyClass_surjective k φ u v f
  rw [ginzburgCutHomologyZeroId,Q.ginzburgCutHomologyZeroComp_class,Q.ginzburgCutZeroComp_id]

theorem id_ginzburgCutHomologyZeroComp (φ : Q.Potential k) {u v : Q.LiftVertex}
    (f : Q.ginzburgCutHomology k φ u.1 v.1 (v.2-u.2) 0) :
    Q.ginzburgCutHomologyZeroComp k φ f (Q.ginzburgCutHomologyZeroId k φ u)=f := by
  obtain ⟨f,rfl⟩ := Q.ginzburgCutZeroHomologyClass_surjective k φ u v f
  rw [ginzburgCutHomologyZeroId,Q.ginzburgCutHomologyZeroComp_class,Q.id_ginzburgCutZeroComp]

theorem ginzburgCutHomologyZeroComp_assoc (φ : Q.Potential k) {u v w x : Q.LiftVertex}
    (f : Q.ginzburgCutHomology k φ u.1 v.1 (v.2-u.2) 0)
    (g : Q.ginzburgCutHomology k φ v.1 w.1 (w.2-v.2) 0)
    (h : Q.ginzburgCutHomology k φ w.1 x.1 (x.2-w.2) 0) :
    Q.ginzburgCutHomologyZeroComp k φ h (Q.ginzburgCutHomologyZeroComp k φ g f)=
      Q.ginzburgCutHomologyZeroComp k φ (Q.ginzburgCutHomologyZeroComp k φ h g) f := by
  obtain ⟨f,rfl⟩ := Q.ginzburgCutZeroHomologyClass_surjective k φ u v f
  obtain ⟨g,rfl⟩ := Q.ginzburgCutZeroHomologyClass_surjective k φ v w g
  obtain ⟨h,rfl⟩ := Q.ginzburgCutZeroHomologyClass_surjective k φ w x h
  rw [Q.ginzburgCutHomologyZeroComp_class,Q.ginzburgCutHomologyZeroComp_class,
    Q.ginzburgCutHomologyZeroComp_class,Q.ginzburgCutHomologyZeroComp_class,
    Q.ginzburgCutZeroComp_assoc]

theorem ginzburgCutHomologyZeroUnrolledIso_id (φ : Q.Potential k) (u : Q.LiftVertex) :
    (Q.ginzburgCutHomologyZeroUnrolledIso k φ u u).hom (Q.ginzburgCutHomologyZeroId k φ u)=
      (Q.unrolledJacobianZAlgebra k φ).id (Q.height u) := by
  let e := Q.ginzburgCutHomologyZeroUnrolledIso k φ u u
  let x := e.inv ((Q.unrolledJacobianZAlgebra k φ).id (Q.height u))
  have hx : e.hom x=(Q.unrolledJacobianZAlgebra k φ).id (Q.height u) := by
    dsimp [x]
    simp
  have h := Q.ginzburgCutHomologyZeroUnrolledIso_comp k φ x (Q.ginzburgCutHomologyZeroId k φ u)
  rw [Q.ginzburgCutHomologyZeroComp_id] at h
  change e.hom x=(Q.unrolledJacobianZAlgebra k φ).comp (e.hom _) (e.hom x) at h
  rw [hx,(Q.unrolledJacobianZAlgebra k φ).id_comp] at h
  exact h.symm

end ASGinzburg.CutQuiver
