import Proof.Lemma4Proof1
import Proof.External.BuhrmanLiTrompVitanyiCorollary2
import Proof.Lemma1

/-!
# Lemma 4
-/

namespace BastienKhormali

/-- **Lemma 4.** If `n ≥ 8`, then the number `g n` of unlabeled simple graphs is
strictly less than twice `2 ^ choose n 2 / n!`. -/
theorem lemma4_graph_count_bound (n : ℕ) (hn : 8 ≤ n) :
    (g n : ℝ) < 2 * ((2 : ℝ) ^ n.choose 2 / n.factorial) := by
  by_cases hlarge : 19 ≤ n
  · have hNat := claim1_two_pow_gt_four_mul_fourth_pow n hlarge
    have hpow : 4 * (n : ℝ) ^ 4 < (2 : ℝ) ^ n := by
      exact_mod_cast hNat
    have htwo : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) _
    have hratio : 4 * (n : ℝ) ^ 4 / (2 : ℝ) ^ n < 1 :=
      (div_lt_one htwo).2 hpow
    have hbase : 0 < (2 : ℝ) ^ n.choose 2 / n.factorial := by positivity
    have hext := buhrman_li_tromp_vitanyi_bound n
    have hmul :
        (2 : ℝ) ^ n.choose 2 / n.factorial *
            (1 + 4 * (n : ℝ) ^ 4 / (2 : ℝ) ^ n) <
          (2 : ℝ) ^ n.choose 2 / n.factorial * 2 := by
      gcongr
      linarith
    nlinarith
  · have hupper : n ≤ 18 := by omega
    rcases lemma1_values_of_g with
      ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
        h14, h15, h16, h17, h18⟩
    interval_cases n <;>
      norm_num [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
        h13, h14, h15, h16, h17, h18, Nat.choose]

end BastienKhormali
