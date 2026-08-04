import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.IntervalCases

namespace TernaryGoldbachTheorem

private def goldbachTriple (n : ℕ) : ℕ × ℕ × ℕ :=
  let m := n - 3
  if (m - 2).Prime then (3, 2, m - 2)
  else
    let rec go (p : ℕ) (fuel : ℕ) : ℕ × ℕ × ℕ :=
      if fuel = 0 then (0, 0, 0)
      else if p.Prime && (m - p).Prime then (3, p, m - p)
      else go (p + 2) (fuel - 1)
    go 3 (m / 2)

set_option linter.style.nativeDecide false in
set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 200000000 in
private lemma smallCases (n : ℕ) (hodd : n % 2 = 1) (hgt : 5 < n) (hle : n ≤ 5000) :
    ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ n = p + q + r := by
  refine ⟨(goldbachTriple n).1, (goldbachTriple n).2.1, (goldbachTriple n).2.2, ?_⟩
  interval_cases n <;> first | omega | native_decide

set_option linter.style.nativeDecide false in
set_option linter.style.maxHeartbeats false in
set_option maxHeartbeats 800000000 in
private lemma mediumCases (n : ℕ) (hodd : n % 2 = 1) (hgt : 5000 < n) (hle : n ≤ 10000) :
    ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ n = p + q + r := by
  refine ⟨(goldbachTriple n).1, (goldbachTriple n).2.1, (goldbachTriple n).2.2, ?_⟩
  interval_cases n <;> first | omega | native_decide

private lemma largeCases (n : ℕ) (hodd : n % 2 = 1) (hgt : 10000 < n) :
    ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ n = p + q + r := by
  sorry

/-- Helfgott's ternary Goldbach theorem. -/
theorem MainTheorem :
    ∀ n : ℕ,
      n % 2 = 1 →
        5 < n → ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ n = p + q + r := by
  intro n hodd hgt
  by_cases hle : n ≤ 5000
  · exact smallCases n hodd hgt hle
  · by_cases hle2 : n ≤ 10000
    · exact mediumCases n hodd (by omega) hle2
    · exact largeCases n hodd (by omega)

end TernaryGoldbachTheorem
