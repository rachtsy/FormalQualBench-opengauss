import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.GroupAction.Transitive
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.PGroup

namespace BurnsidePrimeDegreeTheorem

open MulAction

/--
**Burnside's theorem on transitive permutation groups of prime degree (statement)**.

A transitive permutation group of prime degree is either 2-transitive or has a normal regular
subgroup.
-/
theorem MainTheorem
    {α : Type*} [Fintype α]
    {G : Subgroup (Equiv.Perm α)}
    (htrans : IsPretransitive G α)
    (hp : (Fintype.card α).Prime) :
    IsMultiplyPretransitive G α 2 ∨
      ∃ N : Subgroup G, N.Normal ∧ IsPretransitive N α ∧
        ∀ a : α, MulAction.stabilizer N a = ⊥ := by
  haveI : Fact (Nat.Prime (Fintype.card α)) := ⟨hp⟩
  classical
  set p := Fintype.card α with hp_def
  -- Choose a Sylow p-subgroup P of G
  let P : Sylow p ↥G := default
  by_cases hN : (P : Subgroup ↥G).Normal
  · -- Case: P is normal in G → right disjunct (normal regular subgroup)
    right
    have hp' : Nat.Prime (Nat.card α) := by rwa [Nat.card_eq_fintype_card]
    haveI : IsPreprimitive (↥G) α := IsPreprimitive.of_prime_card hp'
    haveI := hN
    have hp_dvd : p ∣ Nat.card ↥G := by
      have ⟨a⟩ : Nonempty α := Fintype.card_pos_iff.mp (hp_def ▸ hp.pos)
      have h := Subgroup.index_dvd_card (stabilizer (↥G) a)
      rwa [index_stabilizer_of_transitive, Nat.card_eq_fintype_card] at h
    have hPne : (↑P : Subgroup ↥G) ≠ ⊥ := Sylow.ne_bot_of_dvd_card P hp_dvd
    -- P acts transitively via quasiprimitivity
    have hPtrans : IsPretransitive (↥(P : Subgroup ↥G)) α := by
      apply IsPreprimitive.isQuasiPreprimitive.isPretransitive_of_normal
      intro hfix
      apply hPne
      rw [eq_bot_iff]
      intro g hg
      rw [Subgroup.mem_bot]
      have hfixed : ∀ a : α, (g : Equiv.Perm α) a = a := by
        intro a
        exact (hfix ▸ Set.mem_univ a : a ∈ fixedPoints (↥(↑P : Subgroup ↥G)) α) ⟨g, hg⟩
      exact Subtype.ext (Equiv.ext hfixed)
    refine ⟨P.toSubgroup, hN, hPtrans, ?_⟩
    -- P has trivial point stabilizers (acts freely)
    intro a
    sorry
  · -- Case: P is not normal → G is 2-transitive
    left
    sorry

end BurnsidePrimeDegreeTheorem
