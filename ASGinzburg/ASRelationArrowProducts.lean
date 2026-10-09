import ASGinzburg.ASLastArrowRelationSpan
import ASGinzburg.UnrolledLastArrowProducts
import ASGinzburg.UnrolledPathFiltration

/-! Actual products of path relations with positive paths generate
exactly the last-arrow relation span. This is the concrete IJ formula
in lifted vertex coordinates, before transport to integer components. -/
namespace ASGinzburg.ZAlgebra
universe u v
variable {k : Type u} [Field k] (A : ZAlgebra.{u,v} k) (Q : CutQuiver)
  (R : ∀ w : Q.LiftVertex, A.ASResolution Q w)

def pathRelationArrowProduct (u w : Q.LiftVertex) : Submodule k (Q.UnrolledPathComponent k u w) :=
  Submodule.span k {x | ∃ v : Q.LiftVertex,
    ∃ f : Q.UnrolledPathComponent k u v, A.unrolledPathLinearEvaluation Q R u v f=0 ∧
      ∃ g ∈ Q.unrolledPathFiltration k 1 v w, Q.unrolledPathComp k g f=x}

theorem pathRelation_comp_positive_mem_lastArrowSpan {u v w : Q.LiftVertex}
    (f : Q.UnrolledPathComponent k u v) (hf : A.unrolledPathLinearEvaluation Q R u v f=0)
    (g : Q.UnrolledPathComponent k v w) (hg : g∈Q.unrolledPathFiltration k 1 v w) :
    Q.unrolledPathComp k g f∈A.lastArrowRelationSpan Q R u w := by
  classical
  change g∈Finsupp.supported k k _ at hg
  rw [Finsupp.supported_eq_span_single] at hg
  induction hg using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨q,hq,rfl⟩ := hx
      cases q with
      | nil => simp [CutQuiver.UnrolledPath.length] at hq
      | snoc a q =>
          apply Submodule.subset_span
          refine ⟨a,Q.unrolledPathComp k (Finsupp.single q 1) f,?_,?_⟩
          · rw [A.unrolledPathLinearEvaluation_comp,hf,map_zero]
          · change (Q.unrolledPathComp k (Finsupp.single q 1) f).mapDomain
              (CutQuiver.UnrolledPath.snoc a)=
                Q.unrolledPathComp k (Finsupp.single (CutQuiver.UnrolledPath.snoc a q) 1) f
            rw [←Finsupp.mapDomain_single,Q.unrolledPathComp_mapDomain_snoc]
  | zero => simp
  | add x y hx hy ihx ihy =>
      simpa only [map_add,LinearMap.add_apply] using
        (A.lastArrowRelationSpan Q R u w).add_mem ihx ihy
  | smul c x hx ih =>
      simpa only [map_smul,LinearMap.smul_apply] using
        (A.lastArrowRelationSpan Q R u w).smul_mem c ih

theorem pathRelationArrowProduct_eq_lastArrowSpan (u w : Q.LiftVertex) :
    A.pathRelationArrowProduct Q R u w=A.lastArrowRelationSpan Q R u w := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨v,f,hf,g,hg,rfl⟩
    exact A.pathRelation_comp_positive_mem_lastArrowSpan Q R f hf g hg
  · apply Submodule.span_le.mpr
    rintro x ⟨a,p,hp,rfl⟩
    apply Submodule.subset_span
    refine ⟨Q.incomingSource w a,p,hp,
      Finsupp.single (CutQuiver.UnrolledPath.snoc a (.nil (Q.incomingSource w a))) 1,?_,?_⟩
    · apply Finsupp.single_mem_supported
      simp [CutQuiver.UnrolledPath.length]
    · exact Q.unrolledPathComp_lastArrow k a p

theorem pathRelationArrowProduct_eq_cover_ker (u w : Q.LiftVertex) (huw : u≠w) :
    A.pathRelationArrowProduct Q R u w=LinearMap.ker (A.lastArrowToASFirstTerm Q R u w huw) := by
  rw [A.pathRelationArrowProduct_eq_lastArrowSpan,A.lastArrowRelationSpan_eq_cover_ker]

end ASGinzburg.ZAlgebra
