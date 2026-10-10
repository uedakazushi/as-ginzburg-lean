import ASGinzburg.PathOccurrenceContext

/-! The recursive actual contexts retain the full path and count every
occurrence with its multiplicity. -/
namespace ASGinzburg.CutQuiver
variable (Q : CutQuiver)

theorem Path.occurrenceContexts_reconstruct (b : Q.Arrow)
    {i j : Q.Vertex} (p : Q.Path i j) (C : Q.PathOccurrenceContext b i j)
    (hC : C ∈ p.occurrenceContexts Q b) :
    (C.beforePath.comp (Path.snoc (.nil (Q.source b)) b rfl)).comp C.afterPath = p := by
  induction p with
  | nil => simp [Path.occurrenceContexts] at hC
  | @snoc j p a ha ih =>
    simp only [Path.occurrenceContexts] at hC
    rcases List.mem_append.mp hC with hC | hC
    · obtain ⟨D, hD, hDC⟩ := List.mem_map.mp hC
      subst C
      change (D.beforePath.comp (Path.snoc (.nil (Q.source b)) b rfl)).comp
          (Path.snoc D.afterPath a ha) = Path.snoc p a ha
      exact congrArg (fun q => Path.snoc q a ha) (ih D hD)
    · by_cases hab : a = b
      · subst a
        simp at hC
        subst C
        subst j
        simp [Path.transport, Path.comp]
      · simp only [dif_neg hab, List.not_mem_nil] at hC

theorem Path.occurrenceContexts_length (b : Q.Arrow)
    {i j : Q.Vertex} (p : Q.Path i j) :
    (p.occurrenceContexts Q b).length = p.toList.count b := by
  induction p with
  | nil => simp [Path.occurrenceContexts, Path.toList]
  | snoc p a ha ih =>
    by_cases hab : a = b
    · simp [Path.occurrenceContexts, Path.toList, ih, hab, List.count_append]
    · simp [Path.occurrenceContexts, Path.toList, ih, hab, List.count_append]

end ASGinzburg.CutQuiver
