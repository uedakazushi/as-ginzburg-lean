import ASGinzburg.PeriodZeroOriginCover
import ASGinzburg.ZAlgebraIsomorphisms

/-! The actual integer-indexed zero-origin cut component algebra
recovers the original Z-algebra. This is a descent/cover comparison;
identification with a derived preprojective algebra is a separate task. -/
namespace ASGinzburg.ZAlgebra.PeriodIso
universe u v
variable {k : Type u} [Field k] {A : ZAlgebra.{u,v} k}
variable (Q : CutQuiver) (E : A.PeriodIso (Q.vertices:ℤ))

noncomputable def zeroOriginCoverIntegerEquiv (i j : ℤ) :
    E.ZeroOriginCoverHom Q (Q.heightEquiv.symm i) (Q.heightEquiv.symm j) ≃ₗ[k] A.Hom i j :=
  (E.zeroOriginCoverComponentEquiv Q _ _).trans
    (A.homTransport _ _ i j (Q.height_heightEquiv_symm i) (Q.height_heightEquiv_symm j))

theorem zeroOriginCoverIntegerEquiv_comp {i j l : ℤ}
    (f : E.ZeroOriginCoverHom Q (Q.heightEquiv.symm i) (Q.heightEquiv.symm j))
    (g : E.ZeroOriginCoverHom Q (Q.heightEquiv.symm j) (Q.heightEquiv.symm l)) :
    E.zeroOriginCoverIntegerEquiv Q i l (E.zeroOriginCoverComp Q g f)=
      A.comp (E.zeroOriginCoverIntegerEquiv Q j l g)
        (E.zeroOriginCoverIntegerEquiv Q i j f) := by
  dsimp only [zeroOriginCoverIntegerEquiv,LinearEquiv.trans_apply]
  rw [E.zeroOriginCoverComponentEquiv_comp,A.homTransport_comp]

theorem zeroOriginCoverIntegerEquiv_id (i : ℤ) :
    E.zeroOriginCoverIntegerEquiv Q i i (E.zeroOriginCoverId Q (Q.heightEquiv.symm i))=A.id i := by
  dsimp only [zeroOriginCoverIntegerEquiv,LinearEquiv.trans_apply]
  rw [E.zeroOriginCoverComponentEquiv_id,A.homTransport_id]

noncomputable def zeroOriginCoverZAlgebra : ZAlgebra.{u,v} k where
  Hom i j := E.ZeroOriginCoverHom Q (Q.heightEquiv.symm i) (Q.heightEquiv.symm j)
  id i := E.zeroOriginCoverId Q (Q.heightEquiv.symm i)
  comp := E.zeroOriginCoverComp Q
  comp_id := by
    intro i j f
    apply (E.zeroOriginCoverIntegerEquiv Q i j).injective
    rw [E.zeroOriginCoverIntegerEquiv_comp,E.zeroOriginCoverIntegerEquiv_id,A.comp_id]
  id_comp := by
    intro i j f
    apply (E.zeroOriginCoverIntegerEquiv Q i j).injective
    rw [E.zeroOriginCoverIntegerEquiv_comp,E.zeroOriginCoverIntegerEquiv_id,A.id_comp]
  comp_assoc := by
    intro i j l m f g h
    apply (E.zeroOriginCoverIntegerEquiv Q i m).injective
    simp only [E.zeroOriginCoverIntegerEquiv_comp,A.comp_assoc]
  positive := by
    intro i j hij f
    apply (E.zeroOriginCoverIntegerEquiv Q i j).injective
    rw [map_zero]
    exact A.positive hij _
  connected := by
    intro i f
    obtain ⟨c,hc⟩ := A.connected i (E.zeroOriginCoverIntegerEquiv Q i i f)
    refine ⟨c,?_⟩
    apply (E.zeroOriginCoverIntegerEquiv Q i i).injective
    rw [map_smul,E.zeroOriginCoverIntegerEquiv_id]
    exact hc
  id_nonzero := by
    intro i h
    have hz := congrArg (E.zeroOriginCoverIntegerEquiv Q i i) h
    rw [E.zeroOriginCoverIntegerEquiv_id,map_zero] at hz
    exact A.id_nonzero i hz
  finite := by
    intro i j
    exact Module.Finite.of_surjective (E.zeroOriginCoverIntegerEquiv Q i j).symm.toLinearMap
      (E.zeroOriginCoverIntegerEquiv Q i j).symm.surjective

noncomputable def zeroOriginCoverRecovery : Isomorphism (E.zeroOriginCoverZAlgebra Q) A where
  map := E.zeroOriginCoverIntegerEquiv Q
  map_id := E.zeroOriginCoverIntegerEquiv_id Q
  map_comp := E.zeroOriginCoverIntegerEquiv_comp Q

end ASGinzburg.ZAlgebra.PeriodIso
