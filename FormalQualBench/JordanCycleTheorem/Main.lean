import Mathlib.GroupTheory.GroupAction.Jordan

namespace JordanCycleTheorem

open MulAction

/-- Jordan's theorem (cycle version): if `G ≤ Equiv.Perm α` is preprimitive and contains a cycle
whose support has prime cardinality `p` with `p + 3 ≤ Nat.card α`, then
`alternatingGroup α ≤ G`.

Note: this statement already appears in mathlib as a `proof_wanted` declaration
`alternatingGroup_le_of_isPreprimitive_of_isCycle_mem`. -/
theorem MainTheorem {α : Type*} [Fintype α] [DecidableEq α] {G : Subgroup (Equiv.Perm α)}
    (hG : IsPreprimitive G α) {p : ℕ} (hp : p.Prime) (hp' : p + 3 ≤ Nat.card α)
    {g : Equiv.Perm α} (hgc : g.IsCycle) (hgp : g.support.card = p) (hg : g ∈ G) :
    alternatingGroup α ≤ G := by
  have h2 := hp.two_le
  rcases Nat.lt_or_ge p 4 with hp4 | hp4
  · -- p < 4, so p ∈ {2, 3}
    interval_cases p
    · -- p = 2: g is a swap
      have hsw : g.IsSwap := Equiv.Perm.card_support_eq_two.mp hgp
      have := Equiv.Perm.subgroup_eq_top_of_isPreprimitive_of_isSwap_mem hG g hsw hg
      rw [this]; exact le_top
    · -- p = 3: g is a 3-cycle
      exact Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hG
        (card_support_eq_three_iff.mp hgp) hg
  · -- p ≥ 4 (hence p ≥ 5 since p is prime)
    have hp5 : p ≥ 5 := by
      have : p ≠ 4 := fun h => by subst h; exact absurd hp (by decide)
      omega
    -- It suffices to find a 3-cycle in G
    suffices ∃ (τ : Equiv.Perm α), τ.IsThreeCycle ∧ τ ∈ G by
      obtain ⟨τ, hτ3, hτG⟩ := this
      exact Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hG hτ3 hτG
    -- Step 1: Apply Jordan's criterion to get multiply pretransitivity
    -- Following the proof of alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem
    have hα8 : 8 ≤ Nat.card α := by omega
    have hα4 : 4 < Nat.card α := by omega
    -- Jordan's criterion with s = g.supportᶜ gives at least 4-pretransitivity
    have hmpp : IsMultiplyPreprimitive G α (Nat.card α - p + 1) := by
      have h2 : 2 ≤ Nat.card α - p + 1 := by omega
      obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le' h2
      rw [hn]
      apply hG.isMultiplyPreprimitive (s := (g.supportᶜ : Set α))
      · -- ncard condition
        apply Nat.add_left_cancel
        rw [Set.ncard_add_ncard_compl, Set.ncard_coe_finset, hgp, add_comm]
        omega
      · omega
      · -- fixingSubgroup acts preprimitively on complement (= g.support)
        have := Equiv.Perm.isPretransitive_of_isCycle_mem hgc hg
        apply IsPreprimitive.of_prime_card
        convert hp
        classical
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← hgp]
        apply congr_arg
        ext x
        simp [SubMulAction.mem_ofFixingSubgroup_iff]
    have hmpt : IsMultiplyPretransitive G α 4 := by
      have : Nat.card α - p + 1 ≤ Nat.card α := by omega
      exact isMultiplyPretransitive_of_le (by omega) this
    -- Step 2: Construct a 3-cycle using the commutator trick
    -- G is 4-pretransitive and contains a p-cycle g (p ≥ 5, prime, p + 3 ≤ |α|)
    sorry

end JordanCycleTheorem
