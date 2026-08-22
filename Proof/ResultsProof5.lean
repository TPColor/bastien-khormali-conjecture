import Proof.ResultsProof4

/-!
# Results proof 5

The asymptotic estimates used for the second main result.
-/

namespace BastienKhormali

private theorem pair_bound_le_exponential_envelope (n : ℕ) :
    (n.choose 2 : ℝ) * (2 : ℝ) ^ (-(n : ℤ) + 4) ≤
      16 * (n : ℝ) ^ 2 / (2 : ℝ) ^ n := by
  have hpower :
      (2 : ℝ) ^ (-(n : ℤ) + 4) = 16 / (2 : ℝ) ^ n := by
    calc
      (2 : ℝ) ^ (-(n : ℤ) + 4) =
          (2 : ℝ) ^ (-(n : ℤ)) * (2 : ℝ) ^ (4 : ℤ) := by
        rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      _ = ((2 : ℝ) ^ n)⁻¹ * 16 := by
        rw [zpow_neg, zpow_natCast]
        norm_num
      _ = 16 / (2 : ℝ) ^ n := by
        rw [div_eq_mul_inv]
        ring
  rw [hpower]
  have hchoose : (n.choose 2 : ℝ) ≤ (n : ℝ) ^ 2 := by
    exact_mod_cast Nat.choose_le_pow n 2
  calc
    (n.choose 2 : ℝ) * (16 / (2 : ℝ) ^ n) =
        16 * (n.choose 2 : ℝ) / (2 : ℝ) ^ n := by ring
    _ ≤ 16 * (n : ℝ) ^ 2 / (2 : ℝ) ^ n := by
      gcongr

theorem resultsProof2_bad_probability_tendsto_zero :
    Filter.Tendsto
      (fun n : ℕ => uniformProbability (fun T : Tournament n => ¬ IsLinkIrregular T.1))
      Filter.atTop (nhds 0) := by
  have hratio :
      Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ 2 / (2 : ℝ) ^ n)
        Filter.atTop (nhds 0) :=
    (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) 2
      (by norm_num : (1 : ℝ) < 2)).tendsto_div_nhds_zero
  have henvelope :
      Filter.Tendsto (fun n : ℕ => 16 * (n : ℝ) ^ 2 / (2 : ℝ) ^ n)
        Filter.atTop (nhds 0) := by
    have hconst :
        Filter.Tendsto (fun _n : ℕ => (16 : ℝ)) Filter.atTop (nhds 16) :=
      tendsto_const_nhds
    simpa [mul_div_assoc] using hconst.mul hratio
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds henvelope
  · exact Filter.Eventually.of_forall fun n => by
      unfold uniformProbability
      positivity
  · filter_upwards [Filter.eventually_ge_atTop (10 : ℕ)] with n hn
    exact (resultsProof1_bad_probability_lt_ge_ten n hn).le.trans
      (pair_bound_le_exponential_envelope n)

end BastienKhormali
