import Mathlib

/-!
# Lemma 5 proof 1

The comparison of consecutive terms used in the induction for Lemma 5.
-/

namespace BastienKhormali

/-- **Claim 2.** For `n ≥ 7`, twice the `n`th graph-count scale is at most the
`(n + 1)`st scale. -/
theorem claim2_consecutive_scales (n : ℕ) (hn : 7 ≤ n) :
    2 * ((2 : ℝ) ^ n.choose 2 / n.factorial) ≤
      (2 : ℝ) ^ (n + 1).choose 2 / (n + 1).factorial := by
  have hpowNat : 2 * (n + 1) ≤ 2 ^ n := by
    induction n, hn using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
        rw [pow_succ]
        omega
  have hpow : (2 : ℝ) * (n + 1) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast hpowNat
  have hn1 : (0 : ℝ) < n + 1 := by positivity
  have hratio : (2 : ℝ) ≤ (2 : ℝ) ^ n / (n + 1) :=
    (le_div_iff₀ hn1).2 hpow
  have hbase : 0 ≤ (2 : ℝ) ^ n.choose 2 / n.factorial := by positivity
  calc
    2 * ((2 : ℝ) ^ n.choose 2 / n.factorial) =
        ((2 : ℝ) ^ n.choose 2 / n.factorial) * 2 := by ring
    _ ≤ ((2 : ℝ) ^ n.choose 2 / n.factorial) *
        ((2 : ℝ) ^ n / (n + 1)) := mul_le_mul_of_nonneg_left hratio hbase
    _ = (2 : ℝ) ^ (n + 1).choose 2 / (n + 1).factorial := by
      rw [Nat.factorial_succ]
      have hchoose : (n + 1).choose 2 = n.choose 2 + n := by
        rw [Nat.choose]
        simp [Nat.add_comm]
      rw [hchoose, pow_add]
      push_cast
      field_simp

end BastienKhormali
