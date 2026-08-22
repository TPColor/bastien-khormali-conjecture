import Proof.Lemma5
import Proof.Theorem3
import Proof.Lemma2Proof2

/-!
# Results proof 2

The pairwise deletion-isomorphism estimate used in the final union bound.
-/

namespace BastienKhormali

/-- **Claim 9.** If `n ≥ 10` and `u ≠ v`, then
`P(Tₙ - u ≅ Tₙ - v) < 2 ^ (-n + 4)`. -/
theorem claim9_deletion_iso_probability_lt (n : ℕ) (hn : 10 ≤ n)
    (u v : Fin n) (huv : u ≠ v) :
    deletionIsoProbability n u v < (2 : ℝ) ^ (-(n : ℤ) + 4) := by
  have hthree := theorem3_deletion_iso_probability n (by omega) u v huv
  have hfive := lemma5_sum_graph_count_bound (n - 2) (by omega)
  have hfive' :
      (∑ k ∈ Finset.range (n - 1), (g k : ℝ)) <
        4 * ((2 : ℝ) ^ (n - 2).choose 2 / (n - 2).factorial) := by
    simpa [show n - 2 + 1 = n - 1 by omega] using hfive
  have hcoefficient :
      0 < ((n - 2).factorial : ℝ) *
        (2 : ℝ) ^ (-((n - 1).choose 2 : ℤ)) := by positivity
  have hmul := mul_lt_mul_of_pos_left hfive' hcoefficient
  have hbound :
      deletionIsoProbability n u v <
        ((n - 2).factorial : ℝ) *
          (2 : ℝ) ^ (-((n - 1).choose 2 : ℤ)) *
            (4 * ((2 : ℝ) ^ (n - 2).choose 2 / (n - 2).factorial)) :=
    lt_of_le_of_lt hthree hmul
  have hchoose : (n - 1).choose 2 = (n - 2).choose 2 + (n - 2) := by
    rw [show n - 1 = (n - 2) + 1 by omega, Nat.choose]
    simp [Nat.add_comm]
  have hsimplify :
      ((n - 2).factorial : ℝ) *
          (2 : ℝ) ^ (-((n - 1).choose 2 : ℤ)) *
            (4 * ((2 : ℝ) ^ (n - 2).choose 2 / (n - 2).factorial)) =
        (2 : ℝ) ^ (-(n : ℤ) + 4) := by
    have hfac : ((n - 2).factorial : ℝ) ≠ 0 := by positivity
    calc
      ((n - 2).factorial : ℝ) *
            (2 : ℝ) ^ (-((n - 1).choose 2 : ℤ)) *
              (4 * ((2 : ℝ) ^ (n - 2).choose 2 / (n - 2).factorial)) =
          4 * ((2 : ℝ) ^ (-((n - 1).choose 2 : ℤ)) *
            (2 : ℝ) ^ (n - 2).choose 2) := by
        field_simp
      _ = 4 * (2 : ℝ) ^
          (-((n - 1).choose 2 : ℤ) + ((n - 2).choose 2 : ℤ)) := by
        rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      _ = (2 : ℝ) ^ (-(n : ℤ) + 4) := by
        rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℤ) by norm_num,
          ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        congr 1
        rw [hchoose]
        push_cast
        omega
  rwa [hsimplify] at hbound

end BastienKhormali
