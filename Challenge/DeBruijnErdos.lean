import Mathlib.Combinatorics.SimpleGraph.Coloring

namespace DeBruijnErdos

open SimpleGraph

/-- The de Bruijn-Erdős theorem: If every finite subgraph of G is k-colorable,
then G itself is k-colorable. -/
theorem MainTheorem {V : Type*} (G : SimpleGraph V) (k : ℕ) :
    (∀ s : Finset V, (G.induce (↑s : Set V)).Colorable k) → G.Colorable k := by
  sorry

end DeBruijnErdos