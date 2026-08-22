import Proof.Lemma5Proof1
import Proof.Lemma1
import Proof.Lemma4

/-!
# Lemma 5
-/

namespace BastienKhormali

/-- **Lemma 5.** If `n ≥ 7`, then the sum of the unlabeled graph counts through
`n` is less than four times the `n`th graph-count scale. -/
theorem lemma5_sum_graph_count_bound (n : ℕ) (hn : 7 ≤ n) :
    (∑ k ∈ Finset.range (n + 1), (g k : ℝ)) <
      4 * ((2 : ℝ) ^ n.choose 2 / n.factorial) := by
  induction n, hn using Nat.le_induction with
  | base =>
      rcases lemma1_values_of_g with
        ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
          h14, h15, h16, h17, h18⟩
      norm_num [Finset.sum_range_succ, h0, h1, h2, h3, h4, h5, h6, h7, Nat.choose]
  | succ n hn ih =>
      rw [Finset.sum_range_succ]
      have hg := lemma4_graph_count_bound (n + 1) (by omega)
      have hscale := claim2_consecutive_scales n hn
      calc
        (∑ k ∈ Finset.range (n + 1), (g k : ℝ)) + g (n + 1) <
            4 * ((2 : ℝ) ^ n.choose 2 / n.factorial) +
              2 * ((2 : ℝ) ^ (n + 1).choose 2 / (n + 1).factorial) :=
          add_lt_add ih hg
        _ ≤ 4 * ((2 : ℝ) ^ (n + 1).choose 2 / (n + 1).factorial) := by
          linarith

end BastienKhormali
