import ASGinzburg.GinzburgLoopWordCoefficients

/-! The actual path loop differential reads exactly its genuine
original-arrow prefix when a dual last generator is fixed. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem ginzburgPathWordMap_apply_toList {u v : Q.Vertex}
    (f : Q.GinzburgPathComponent k u v) (p : Q.GinzburgPath u v) :
    Q.ginzburgPathWordMap k u v f p.toList=f p :=
  Finsupp.mapDomain_apply (GinzburgPath.toList_injective u v) f p

theorem ginzburgLoopDifferential_dual_path_coeff (v : Q.Vertex)
    (b : Q.Arrow) (hb : Q.source b=v) (p : Q.GinzburgPath v (Q.target b)) :
    Q.ginzburgLoopDifferential k v
      ((GinzburgLastGeneratorData.path Q) ⟨⟨.dual b,hb⟩,p⟩)=
      (Finsupp.single ((Q.originalGinzburgArrowPath b).transport Q hb rfl) (1:k)) p := by
  classical
  rw [←Q.ginzburgPathWordMap_apply_toList k _
    ((GinzburgLastGeneratorData.path Q) ⟨⟨.dual b,hb⟩,p⟩)]
  simp only [GinzburgLastGeneratorData.path,GinzburgPath.transport_toList,GinzburgPath.toList]
  rw [Q.ginzburgLoopDifferential_dual_word_coeff,if_pos hb]
  let q := (Q.originalGinzburgArrowPath b).transport Q hb rfl
  have hq : q.toList=[.original b] := by
    simp [q,originalGinzburgArrowPath,GinzburgPath.toList]
  have he := Finsupp.mapDomain_apply (GinzburgPath.toList_injective v (Q.target b))
    (Finsupp.single q (1:k)) p
  simpa only [Finsupp.mapDomain_single,hq] using he

end ASGinzburg.CutQuiver
