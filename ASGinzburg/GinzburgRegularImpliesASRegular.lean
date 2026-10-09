import ASGinzburg.GinzburgLowExtVanishing
import ASGinzburg.GinzburgOffDiagonalExtVanishing
import ASGinzburg.GinzburgMinimalResolutionExt
import ASGinzburg.GinzburgSimpleProjectiveDimension
import ASGinzburg.ASDualityEquivalence

/-! Genuine Ginzburg regularity implies both original AS conditions,
including the total cardinal Ext rank, without new duality hypotheses.
This is one direction for the given potential, not the paper's correspondence. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory CategoryTheory.Limits
universe u
variable (Q : CutQuiver) (k : Type u) [Field k] (φ : Q.Potential k)

theorem GinzburgRegular.simpleExt_other_eq_zero_representable
    (h : Q.GinzburgRegular k φ) (v w : Q.LiftVertex) (p : ℕ)
    (hne : (p,w)≠(3,Q.tau v))
    (e : Abelian.Ext.{u}
      ((Q.unrolledJacobianZAlgebra k φ).simpleRightModule (Q.height w))
      ((Q.unrolledJacobianZAlgebra k φ).representable (Q.height v)) p) : e=0 := by
  by_cases hp : p<3
  · exact h.simpleExt_low_eq_zero_representable Q k φ w v p hp e
  by_cases h₃ : p=3
  · subst p
    have hv : v≠Q.tau.symm w := by
      intro hv
      have hw : w=Q.tau v := by rw [hv,Equiv.apply_symm_apply]
      exact hne (congrArg (fun w => (3,w)) hw)
    exact h.simpleExt_three_off_diagonal_eq_zero Q k φ w v hv e
  · have h₄ : 4≤p := by omega
    obtain ⟨n,hn⟩ := Nat.exists_eq_add_of_le h₄
    rw [Nat.add_comm 4 n] at hn
    subst p
    exact h.simple_ext_ge_four_eq_zero Q k w
      ((Q.unrolledJacobianZAlgebra k φ).representable (Q.height v)) n e

theorem GinzburgRegular.simpleExt_finrank_representable
    (h : Q.GinzburgRegular k φ) (v w : Q.LiftVertex) (p : ℕ) :
    Module.finrank k (Abelian.Ext.{u}
      ((Q.unrolledJacobianZAlgebra k φ).simpleRightModule (Q.height w))
      ((Q.unrolledJacobianZAlgebra k φ).representable (Q.height v)) p)=
      if (p,w)=(3,Q.tau v) then 1 else 0 := by
  classical
  split_ifs with he
  · obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
    exact h.distinguishedExtThree_finrank Q k v
  · letI : Subsingleton (Abelian.Ext.{u}
      ((Q.unrolledJacobianZAlgebra k φ).simpleRightModule (Q.height w))
      ((Q.unrolledJacobianZAlgebra k φ).representable (Q.height v)) p) :=
      ⟨fun x y => by rw [h.simpleExt_other_eq_zero_representable Q k φ v w p he x,
        h.simpleExt_other_eq_zero_representable Q k φ v w p he y]⟩
    exact Module.finrank_zero_of_subsingleton

theorem GinzburgRegular.asRegular (h : Q.GinzburgRegular k φ) :
    (Q.unrolledJacobianZAlgebra k φ).ASRegular Q :=
  ((Q.unrolledJacobianZAlgebra k φ).asRegular_iff_ext_finrank Q
    (h.exists_ASResolution Q k)).mpr (h.simpleExt_finrank_representable Q k φ)

theorem GinzburgRegular.asExtTotalRank_eq_one
    (h : Q.GinzburgRegular k φ) (v : Q.LiftVertex) :
    (Q.unrolledJacobianZAlgebra k φ).asExtTotalRank Q v=1 :=
  (h.asRegular Q k φ).2 v

end ASGinzburg.CutQuiver
