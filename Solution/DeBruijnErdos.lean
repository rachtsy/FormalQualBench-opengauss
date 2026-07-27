import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Topology.Compactness.Compact

namespace DeBruijnErdos

open SimpleGraph

open Classical in
/-- The de Bruijn-Erdős theorem: If every finite subgraph of G is k-colorable,
then G itself is k-colorable. -/
theorem MainTheorem {V : Type*} (G : SimpleGraph V) (k : ℕ) :
    (∀ s : Finset V, (G.induce (↑s : Set V)).Colorable k) →
    G.Colorable k := by
  intro h
  by_cases hV : IsEmpty V
  · exact Colorable.of_isEmpty k
  rw [not_isEmpty_iff] at hV
  obtain ⟨v₀⟩ := hV
  have hk : 0 < k := by
    obtain ⟨c⟩ := h {v₀}
    exact Nat.pos_of_ne_zero fun h0 => by
      subst h0; exact (c ⟨v₀, Finset.mem_singleton.mpr rfl⟩).elim0
  let t : Finset V → Set (V → Fin k) :=
    fun s => {f | ∀ u ∈ s, ∀ v ∈ s, G.Adj u v → f u ≠ f v}
  suffices (⋂ s, t s).Nonempty by
    obtain ⟨f, hf⟩ := this
    rw [Set.mem_iInter] at hf
    exact ⟨Coloring.mk f fun {u v} hadj =>
      hf {u, v} u (Finset.mem_insert_self u {v}) v
        (Finset.mem_insert_of_mem
          (Finset.mem_singleton.mpr rfl)) hadj⟩
  apply CompactSpace.iInter_nonempty
  · intro s
    have : t s = ⋂ u ∈ (s : Set V), ⋂ v ∈ (s : Set V),
        {f : V → Fin k | G.Adj u v → f u ≠ f v} := by
      ext f; simp [t]
    rw [this]
    apply isClosed_biInter; intro u _
    apply isClosed_biInter; intro v _
    by_cases hadj : G.Adj u v
    · simp only [hadj, true_implies]
      have : {f : V → Fin k | f u ≠ f v} =
          (fun f : V → Fin k => (f u, f v)) ⁻¹'
            {p : Fin k × Fin k | p.1 ≠ p.2} := by
        ext; simp
      rw [this]
      exact (isClosed_discrete _).preimage
        ((continuous_apply u).prodMk (continuous_apply v))
    · convert isClosed_univ (X := V → Fin k)
      ext f; simp [hadj]
  · intro S
    set T := S.biUnion id
    obtain ⟨c⟩ := h T
    refine ⟨fun v => if hv : v ∈ T then c ⟨v, hv⟩
      else ⟨0, hk⟩, ?_⟩
    simp only [Set.mem_iInter]
    intro s hs u hu v hv hadj
    have huT : u ∈ T :=
      Finset.mem_biUnion.mpr ⟨s, hs, hu⟩
    have hvT : v ∈ T :=
      Finset.mem_biUnion.mpr ⟨s, hs, hv⟩
    simp only [dif_pos huT, dif_pos hvT]
    exact c.valid (induce_adj.mpr hadj)

end DeBruijnErdos
