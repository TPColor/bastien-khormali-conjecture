import Mathlib

/-!
# Lemma 4 proof 1

The elementary exponential estimate used in Lemma 4.
-/

namespace BastienKhormali

/-- **Claim 1.** For every `n ≥ 19`, `2ⁿ > 4n⁴`. -/
theorem claim1_two_pow_gt_four_mul_fourth_pow (n : ℕ) (hn : 19 ≤ n) :
    4 * n ^ 4 < 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have hratio : 19 * (n + 1) ≤ 20 * n := by omega
      have hpow : (19 * (n + 1)) ^ 4 ≤ (20 * n) ^ 4 := by
        exact Nat.pow_le_pow_left hratio 4
      have hstep : (n + 1) ^ 4 < 2 * n ^ 4 := by
        have hn4 : 0 < n ^ 4 := pow_pos (by omega) _
        norm_num [mul_pow] at hpow ⊢
        nlinarith
      calc
        4 * (n + 1) ^ 4 < 2 * (4 * n ^ 4) := by nlinarith
        _ < 2 * 2 ^ n := by omega
        _ = 2 ^ (n + 1) := by rw [pow_succ]; omega

end BastienKhormali
