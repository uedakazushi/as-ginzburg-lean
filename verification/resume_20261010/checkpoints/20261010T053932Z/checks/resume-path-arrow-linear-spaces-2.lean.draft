import work.ASGinzburgDraft.PathArrowSubstitutionInverse
import work.ASGinzburgDraft.PathAutomorphismLengthFiltration
import ASGinzburg.PathCutGrading

/-! Actual length-one path spaces and their leading-component projection.
The cut degree of any arrow is forced by its endpoints. -/
namespace ASGinzburg.CutQuiver
universe u
variable (Q : CutQuiver) (k : Type u) [Field k]

def pathArrowComponent (i j : Q.Vertex) : Submodule k (Q.PathComponent k i j) :=
  Finsupp.supported k k {p | p.length = 1}

noncomputable def pathArrowProjection (i j : Q.Vertex) :
    Q.PathComponent k i j →ₗ[k] Q.PathComponent k i j :=
  Finsupp.linearCombination k (fun p => if p.length = 1 then Finsupp.single p 1 else 0)

@[simp] theorem pathArrowProjection_single (i j : Q.Vertex) (p : Q.Path i j) (c : k) :
    Q.pathArrowProjection k i j (Finsupp.single p c) =
      if p.length = 1 then Finsupp.single p c else 0 := by
  classical
  by_cases H : p.length = 1 <;> simp [pathArrowProjection,H]

theorem pathArrowProjection_mem (i j : Q.Vertex) (f : Q.PathComponent k i j) :
    Q.pathArrowProjection k i j f ∈ Q.pathArrowComponent k i j := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simpa only [map_add] using Submodule.add_mem _ hf hg
  | single p c =>
    rw [pathArrowProjection_single]
    split_ifs with H
    · exact Finsupp.single_mem_supported k c H
    · exact Submodule.zero_mem _

theorem pathArrowProjection_on_arrow (i j : Q.Vertex)
    (f : Q.pathArrowComponent k i j) : Q.pathArrowProjection k i j f.val = f.val := by
  have hf := f.property
  change f.val ∈ Finsupp.supported k k _ at hf
  rw [Finsupp.supported_eq_span_single] at hf
  generalize f.val = x at hf ⊢
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p,hp,rfl⟩ := hx
    change p.length = 1 at hp
    simp [hp]
  | zero => simp
  | add f g hf hg ihf ihg => simp only [map_add,ihf,ihg]
  | smul c f hf ih => simp only [map_smul,ih]

noncomputable def pathArrowBasisElement (a : Q.Arrow) :
    Q.pathArrowComponent k (Q.source a) (Q.target a) :=
  ⟨Q.pathIdentityArrowReplacement k a,Finsupp.single_mem_supported k 1 rfl⟩

def endpointArrowCutDegree (i j : Q.Vertex) : ℕ := if i.val < j.val then 0 else 1

theorem Path.cutDegree_of_length_one {i j : Q.Vertex} (p : Q.Path i j)
    (hp : p.length = 1) : p.cutDegree = Q.endpointArrowCutDegree i j := by
  cases p with
  | nil => simp [Path.length] at hp
  | @snoc j p a ha =>
    cases p with
    | nil =>
      cases H : Q.cut a
      · have h := Q.forward a H
        rw [ha] at h
        simp [Path.cutDegree,CutQuiver.cutDegree,H,endpointArrowCutDegree,h]
      · have h := Q.backward a H
        rw [ha] at h
        have hnot : ¬ i.val < (Q.target a).val := by omega
        simp [Path.cutDegree,CutQuiver.cutDegree,H,endpointArrowCutDegree,hnot]
    | snoc p b hb => simp [Path.length] at hp

theorem endpointArrowCutDegree_arrow (a : Q.Arrow) :
    Q.endpointArrowCutDegree (Q.source a) (Q.target a) = Q.cutDegree a := by
  simpa only [Path.cutDegree,Nat.zero_add] using (Path.cutDegree_of_length_one Q
    (Path.snoc (.nil (Q.source a)) a rfl) rfl).symm

theorem pathArrowComponent_le_cut (i j : Q.Vertex) :
    Q.pathArrowComponent k i j ≤
      Q.pathCutComponent k i j (Q.endpointArrowCutDegree i j : ℤ) := by
  apply Finsupp.supported_mono
  intro p hp
  exact congrArg (fun n : ℕ => (n : ℤ)) (Path.cutDegree_of_length_one Q p hp)

theorem sub_pathArrowProjection_mem_length_two (i j : Q.Vertex) (hij : i ≠ j)
    (f : Q.PathComponent k i j) :
    f - Q.pathArrowProjection k i j f ∈ Q.pathLengthFiltration k 2 i j := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simpa only [map_add,add_sub_add_comm] using Submodule.add_mem _ hf hg
  | single p c =>
    rw [pathArrowProjection_single]
    split_ifs with H
    · simp
    · have hp : 2 ≤ p.length := by
        have Hpos : 1 ≤ p.length := by
          cases p with
          | nil => exact (hij rfl).elim
          | snoc p a ha => simp [Path.length]
        omega
      simpa only [sub_zero] using Finsupp.single_mem_supported k c
        (show p ∈ {p : Q.Path i j | 2 ≤ p.length} from hp)

noncomputable def pathSubstitutionArrowLinearMap (σ : Q.PathArrowReplacement k) (i j : Q.Vertex) :
    Module.End k (Q.pathArrowComponent k i j) :=
  ((Q.pathArrowProjection k i j).comp (Q.pathArrowSubstitutionComponent k σ i j)).restrict
    (fun _ _ => Q.pathArrowProjection_mem k i j _)

end ASGinzburg.CutQuiver
