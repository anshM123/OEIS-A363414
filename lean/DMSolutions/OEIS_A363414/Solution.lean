import DMSolutions.OEIS_A363414.Statement
import DMSolutions.OEIS_A363414.Core

/-!
# Solution of `OeisA363414.conjecture_type1_empty`

The statement is that of `FormalConjectures/OEIS/363414.lean` (formal-conjectures pull request
4946), included unmodified as `Statement.lean`. It is stated here with the repository's own
definition `OeisA363414.a`, which agrees with the copy `A363414Core.a` by `rfl`.

Every prime `p` divides `a n` for some `n > 0`: take `n = 3` for `p = 2` (`a 3 = -18`) and
`n = p - 1` for odd `p`.
-/

namespace OeisA363414

theorem a_eq_core : a = A363414Core.a := rfl

theorem conjecture_type1_empty_solved :
    ∀ p : ℕ, p.Prime → ∃ n : ℕ, 0 < n ∧ (p : ℤ) ∣ a n := by
  rw [a_eq_core]
  exact A363414Core.conjecture_type1_empty_core

end OeisA363414
