import work.ASGinzburgDraft.PotentialCyclicClass
import ASGinzburg.PathCutGrading
import ASGinzburg.PathLengthFiltration

/-! Every actual closed component supported in cut degree one and in
length at least three represents an actual potential in the cyclic quotient. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

theorem closedPathTrace_potentialCyclicClass_exists (i : Q.Vertex)
    (f : Q.PathComponent k i i)
    (hc : f ∈ Q.pathCutComponent k i i 1)
    (hl : f ∈ Q.pathLengthFiltration k 3 i i) :
    ∃ φ : Q.Potential k, φ.val = Q.closedPathTrace k i f ∧
      Q.potentialCyclicClass k φ = Q.closedPathCyclicClass k i f := by
  have hs : f ∈ Finsupp.supported k k
      {p : Q.Path i i | p.cutDegree = 1 ∧ 3 ≤ p.length} := by
    apply (Finsupp.mem_supported k f).mpr
    intro p hp
    have hcp : (p.cutDegree : ℤ) = 1 := (Finsupp.mem_supported k f).mp hc hp
    have hlp : 3 ≤ p.length := (Finsupp.mem_supported k f).mp hl hp
    exact ⟨by exact_mod_cast hcp, hlp⟩
  rw [Finsupp.supported_eq_span_single] at hs
  clear hc hl
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, rfl⟩ := hx
    refine ⟨⟨traceWord (k := k) p.toList,
      Q.traceWord_mem_potentialSpace k p hp.1 hp.2⟩, ?_, ?_⟩
    · rw [Q.closedPathTrace_single, one_smul]
    · exact Q.potentialCyclicClass_traceWord k i p hp.1 hp.2
  | zero =>
    refine ⟨0, ?_, ?_⟩
    · rw [map_zero]
      rfl
    · rw [map_zero, map_zero]
  | add x y hx hy ihx ihy =>
    obtain ⟨φ, hφ, heφ⟩ := ihx
    obtain ⟨ψ, hψ, heψ⟩ := ihy
    refine ⟨φ + ψ, ?_, ?_⟩
    · change φ.val + ψ.val = _
      rw [map_add, hφ, hψ]
    · rw [map_add, map_add, heφ, heψ]
  | smul c x hx ih =>
    obtain ⟨φ, hφ, heφ⟩ := ih
    refine ⟨c • φ, ?_, ?_⟩
    · change c • φ.val = _
      rw [map_smul, hφ]
    · rw [map_smul, map_smul, heφ]

theorem closedPathTrace_mem_potentialSpace_of_cut_length (i : Q.Vertex)
    (f : Q.PathComponent k i i)
    (hc : f ∈ Q.pathCutComponent k i i 1)
    (hl : f ∈ Q.pathLengthFiltration k 3 i i) :
    Q.closedPathTrace k i f ∈ Q.potentialSpace k := by
  obtain ⟨φ, hφ, _⟩ := Q.closedPathTrace_potentialCyclicClass_exists k i f hc hl
  rw [← hφ]
  exact φ.property

theorem potentialCyclicClass_closedPathTrace_of_cut_length (i : Q.Vertex)
    (f : Q.PathComponent k i i)
    (hc : f ∈ Q.pathCutComponent k i i 1)
    (hl : f ∈ Q.pathLengthFiltration k 3 i i) :
    Q.potentialCyclicClass k ⟨Q.closedPathTrace k i f,
      Q.closedPathTrace_mem_potentialSpace_of_cut_length k i f hc hl⟩ =
      Q.closedPathCyclicClass k i f := by
  obtain ⟨φ, hφ, heφ⟩ := Q.closedPathTrace_potentialCyclicClass_exists k i f hc hl
  have h : (⟨Q.closedPathTrace k i f,
      Q.closedPathTrace_mem_potentialSpace_of_cut_length k i f hc hl⟩ : Q.Potential k) = φ :=
    Subtype.ext hφ.symm
  rw [h]
  exact heφ

end ASGinzburg.CutQuiver
