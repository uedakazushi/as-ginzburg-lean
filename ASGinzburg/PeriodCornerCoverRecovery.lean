import ASGinzburg.PeriodCornerCover

/-! Recovery of the original algebra from the homogeneous corners of R,
with composition supplied by multiplication in the constructed ring. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

theorem cornerCoverComponentEquiv_symm_comp {x y z : Q.LiftVertex}
    (f : E.CornerCoverHom Q x y) (g : E.CornerCoverHom Q y z) :
    (E.cornerCoverComponentEquiv Q x z).symm (E.cornerCoverComp Q g f)=
      E.zeroOriginCoverComp Q ((E.cornerCoverComponentEquiv Q y z).symm g)
        ((E.cornerCoverComponentEquiv Q x y).symm f) := by
  apply (E.cornerCoverComponentEquiv Q x z).injective
  rw [LinearEquiv.apply_symm_apply,E.cornerCoverComponentEquiv_comp,
    LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]

theorem cornerCoverComponentEquiv_symm_id (x : Q.LiftVertex) :
    (E.cornerCoverComponentEquiv Q x x).symm (E.cornerCoverId Q x)=E.zeroOriginCoverId Q x := by
  apply (E.cornerCoverComponentEquiv Q x x).injective
  rw [LinearEquiv.apply_symm_apply,E.cornerCoverComponentEquiv_id]

noncomputable def cornerCoverIntegerEquiv (i j : ℤ) :
    E.CornerCoverHom Q (Q.heightEquiv.symm i) (Q.heightEquiv.symm j) ≃ₗ[k] A.Hom i j :=
  (E.cornerCoverComponentEquiv Q _ _).symm.trans (E.zeroOriginCoverIntegerEquiv Q i j)

theorem cornerCoverIntegerEquiv_comp {i j l : ℤ}
    (f : E.CornerCoverHom Q (Q.heightEquiv.symm i) (Q.heightEquiv.symm j))
    (g : E.CornerCoverHom Q (Q.heightEquiv.symm j) (Q.heightEquiv.symm l)) :
    E.cornerCoverIntegerEquiv Q i l (E.cornerCoverComp Q g f)=
      A.comp (E.cornerCoverIntegerEquiv Q j l g) (E.cornerCoverIntegerEquiv Q i j f) := by
  dsimp only [cornerCoverIntegerEquiv,LinearEquiv.trans_apply]
  rw [E.cornerCoverComponentEquiv_symm_comp,E.zeroOriginCoverIntegerEquiv_comp]

theorem cornerCoverIntegerEquiv_id (i : ℤ) :
    E.cornerCoverIntegerEquiv Q i i (E.cornerCoverId Q (Q.heightEquiv.symm i))=A.id i := by
  dsimp only [cornerCoverIntegerEquiv,LinearEquiv.trans_apply]
  rw [E.cornerCoverComponentEquiv_symm_id,E.zeroOriginCoverIntegerEquiv_id]

noncomputable def cornerCoverZAlgebra : ZAlgebra.{u,v} k where
  Hom i j := E.CornerCoverHom Q (Q.heightEquiv.symm i) (Q.heightEquiv.symm j)
  id i := E.cornerCoverId Q (Q.heightEquiv.symm i)
  comp := E.cornerCoverComp Q
  comp_id := by
    intro i j f
    apply (E.cornerCoverIntegerEquiv Q i j).injective
    rw [E.cornerCoverIntegerEquiv_comp,E.cornerCoverIntegerEquiv_id,A.comp_id]
  id_comp := by
    intro i j f
    apply (E.cornerCoverIntegerEquiv Q i j).injective
    rw [E.cornerCoverIntegerEquiv_comp,E.cornerCoverIntegerEquiv_id,A.id_comp]
  comp_assoc := by
    intro i j l m f g h
    apply (E.cornerCoverIntegerEquiv Q i m).injective
    simp only [E.cornerCoverIntegerEquiv_comp,A.comp_assoc]
  positive := by
    intro i j hij f
    apply (E.cornerCoverIntegerEquiv Q i j).injective
    rw [map_zero]
    exact A.positive hij _
  connected := by
    intro i f
    obtain ⟨c,hc⟩ := A.connected i (E.cornerCoverIntegerEquiv Q i i f)
    refine ⟨c,?_⟩
    apply (E.cornerCoverIntegerEquiv Q i i).injective
    rw [map_smul,E.cornerCoverIntegerEquiv_id]
    exact hc
  id_nonzero := by
    intro i h
    have hz := congrArg (E.cornerCoverIntegerEquiv Q i i) h
    rw [E.cornerCoverIntegerEquiv_id,map_zero] at hz
    exact A.id_nonzero i hz
  finite := by
    intro i j
    exact Module.Finite.of_surjective (E.cornerCoverIntegerEquiv Q i j).symm.toLinearMap
      (E.cornerCoverIntegerEquiv Q i j).symm.surjective

noncomputable def cornerCoverRecovery : Isomorphism (E.cornerCoverZAlgebra Q) A where
  map := E.cornerCoverIntegerEquiv Q
  map_id := E.cornerCoverIntegerEquiv_id Q
  map_comp := E.cornerCoverIntegerEquiv_comp Q

end ASGinzburg.ZAlgebra.PeriodIso
