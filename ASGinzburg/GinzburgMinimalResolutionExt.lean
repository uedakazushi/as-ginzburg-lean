import ASGinzburg.GinzburgMinimalASResolution
import ASGinzburg.ASDualityExt
import ASGinzburg.ASResolutionExtFinite

/-! Actual finite Ext and the distinguished degree-three copy of k
follow from the proved minimal resolution. The other low-degree and
off-diagonal Ext groups remain separate AS-duality obligations. -/
namespace ASGinzburg.CutQuiver
open CategoryTheory
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

noncomputable def GinzburgRegular.distinguishedExtThreeEquiv {φ : Q.Potential k}
    (h : Q.GinzburgRegular k φ) (v : Q.LiftVertex) :
    Abelian.Ext.{u} ((Q.unrolledJacobianZAlgebra k φ).simpleRightModule (Q.height (Q.tau v)))
      ((Q.unrolledJacobianZAlgebra k φ).representable (Q.height v)) 3 ≃ₗ[k] k :=
  (h.minimalASResolution Q k (Q.tau v)).asDualityExtThreeEquiv
    (Q.unrolledJacobianZAlgebra k φ) Q v

theorem GinzburgRegular.simpleExtFinite_representable {φ : Q.Potential k}
    (h : Q.GinzburgRegular k φ) (v : Q.LiftVertex) (i : ℤ) (n : ℕ) :
    Module.Finite k (Abelian.Ext.{u}
      ((Q.unrolledJacobianZAlgebra k φ).simpleRightModule (Q.height v))
      ((Q.unrolledJacobianZAlgebra k φ).representable i) n) :=
  (h.minimalASResolution Q k v).extFinite_representable i n

theorem GinzburgRegular.distinguishedExtThree_finrank {φ : Q.Potential k}
    (h : Q.GinzburgRegular k φ) (v : Q.LiftVertex) :
    Module.finrank k (Abelian.Ext.{u}
      ((Q.unrolledJacobianZAlgebra k φ).simpleRightModule (Q.height (Q.tau v)))
      ((Q.unrolledJacobianZAlgebra k φ).representable (Q.height v)) 3)=1 :=
  (h.distinguishedExtThreeEquiv Q k v).finrank_eq.trans (Module.finrank_self k)

theorem GinzburgRegular.distinguishedExtThree_rank {φ : Q.Potential k}
    (h : Q.GinzburgRegular k φ) (v : Q.LiftVertex) :
    Module.rank k (Abelian.Ext.{u}
      ((Q.unrolledJacobianZAlgebra k φ).simpleRightModule (Q.height (Q.tau v)))
      ((Q.unrolledJacobianZAlgebra k φ).representable (Q.height v)) 3)=1 := by
  letI := h.simpleExtFinite_representable Q k (Q.tau v) (Q.height v) 3
  rw [←Module.finrank_eq_rank,h.distinguishedExtThree_finrank Q k v]
  rfl

theorem GinzburgRegular.asExtTotalRank_ge_one {φ : Q.Potential k}
    (h : Q.GinzburgRegular k φ) (v : Q.LiftVertex) :
    1 ≤ (Q.unrolledJacobianZAlgebra k φ).asExtTotalRank Q v := by
  have he := (Q.unrolledJacobianZAlgebra k φ).asExtRank_le_total Q v (Q.tau v) 3
  rw [h.distinguishedExtThree_rank Q k v] at he
  exact he

end ASGinzburg.CutQuiver
