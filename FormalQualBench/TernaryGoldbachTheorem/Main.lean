import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.IntervalCases

namespace TernaryGoldbachTheorem

set_option linter.style.nativeDecide false in
set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 800000 in
private lemma smallCases (n : ℕ) (hodd : n % 2 = 1) (hgt : 5 < n) (hle : n ≤ 100) :
    ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ n = p + q + r := by
  suffices h : ∃ p q r : Fin (n + 1),
      (p : ℕ).Prime ∧ (q : ℕ).Prime ∧ (r : ℕ).Prime ∧ n = ↑p + ↑q + ↑r by
    obtain ⟨p, q, r, hp, hq, hr, hpqr⟩ := h
    exact ⟨↑p, ↑q, ↑r, hp, hq, hr, hpqr⟩
  interval_cases n <;> first | omega | native_decide

private lemma largeCases (n : ℕ) (hodd : n % 2 = 1) (hgt : 100 < n) :
    ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ n = p + q + r := by
  sorry

/-- Helfgott's ternary Goldbach theorem. -/
theorem MainTheorem :
    ∀ n : ℕ,
      n % 2 = 1 →
        5 < n → ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ n = p + q + r := by
  intro n hodd hgt
  by_cases hle : n ≤ 100
  · exact smallCases n hodd hgt hle
  · exact largeCases n hodd (by omega)

end TernaryGoldbachTheorem
