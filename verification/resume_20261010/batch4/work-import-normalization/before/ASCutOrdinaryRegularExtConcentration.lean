import work.ASGinzburgDraft.ASCutOrdinaryRegularHomExactness
import ASGinzburg.ASCutSemisimpleRightDimension

/-! Genuine ordinary Ext concentration follows from the original AS
condition, the homogeneous comparison, and the actual semisimple vertex
decomposition. The target is the ordinary right regular module. -/
namespace ASGinzburg.ZAlgebra
open CategoryTheory CategoryTheory.Limits
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)

 theorem ASRegular.cutOrdinarySimpleExt_regular_eq_zero_other
    (hAS : A.ASRegular Q) (i : Q.Vertex) (n : ℕ) (hn : n ≠ 3)
    (e : Abelian.Ext.{v} (hAS.cutOrdinarySimple A Q (i,0))
      (ModuleCat.of (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ) n) : e = 0 := by
  by_cases hlt : n < 3
  · exact hAS.cutOrdinarySimpleExt_regular_eq_zero_low A Q i n hlt e
  · have heq : n = (n - 4) + 4 := by omega
    subst n
    exact hAS.cutOrdinarySimple_ext_ge_four_eq_zero A Q (i,0) _ _ e

 theorem ASRegular.cutOrdinarySimpleExt_rightRegular_eq_zero_other
    (hAS : A.ASRegular Q) (i : Q.Vertex) (n : ℕ) (hn : n ≠ 3)
    (e : Abelian.Ext.{v} (hAS.cutOrdinarySimple A Q (i,0))
      (ModuleCat.of (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ (hAS.CutGradedAlgebra A Q)) n) : e = 0 := by
  let iso := (rightRegularOppositeLinearEquiv (hAS.CutGradedAlgebra A Q)).toModuleIso
  have hz : e.comp (Abelian.Ext.mk₀ iso.hom) (Nat.add_zero n) = 0 :=
    hAS.cutOrdinarySimpleExt_regular_eq_zero_other A Q i n hn _
  have he := congrArg
    (fun x => x.comp (Abelian.Ext.mk₀ iso.inv) (Nat.add_zero n)) hz
  rw [Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀,
    iso.hom_inv_id, Abelian.Ext.comp_mk₀_id, Abelian.Ext.zero_comp] at he
  exact he

 theorem ASRegular.cutSemisimpleRightExt_rightRegular_eq_zero_other
    (hAS : A.ASRegular Q) (n : ℕ) (hn : n ≠ 3)
    (e : Abelian.Ext.{v} (hAS.cutSemisimpleRightObject A Q)
      (ModuleCat.of (hAS.CutGradedAlgebra A Q)ᵐᵒᵖ (hAS.CutGradedAlgebra A Q)) n) : e = 0 := by
  let iso := hAS.cutSemisimpleRightVertexIso A Q
  have hz : (Abelian.Ext.mk₀ iso.inv).comp e (zero_add n) = 0 := by
    apply (Abelian.Ext.biproductAddEquiv (biproduct.isBilimit
      (fun i : Q.Vertex => hAS.cutOrdinarySimple A Q (i,0))) _ n).injective
    rw [map_zero]
    ext i
    exact hAS.cutOrdinarySimpleExt_rightRegular_eq_zero_other A Q i n hn _
  have he := congrArg
    (fun x => (Abelian.Ext.mk₀ iso.hom).comp x (zero_add n)) hz
  rw [← Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀,
    iso.hom_inv_id, Abelian.Ext.mk₀_id_comp, Abelian.Ext.comp_zero] at he
  exact he

end ASGinzburg.ZAlgebra
