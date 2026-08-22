import Proof.ResultsProof1
import Proof.Lemma2Proof2
import Proof.ResultsProof2
import Proof.ResultsProof3

/-!
# Results proof 4

The finite-probability estimates used for the first main result.
-/

namespace BastienKhormali

private theorem vertexDeletedIsomorphic_symm {V : Type*} (T : Digraph V) (u v : V) :
    VertexDeletedIsomorphic T u v → VertexDeletedIsomorphic T v u := by
  rintro ⟨e⟩
  exact ⟨e.symm⟩

private theorem not_linkIrregular_iff_exists_deleted_pair {n : ℕ}
    (T : Digraph (Fin n)) (hT : IsTournament T) :
    ¬ IsLinkIrregular T ↔
      ∃ s : TwoSubset (Fin n),
        VertexDeletedIsomorphic T (twoSubsetMin s) (twoSubsetMax s) := by
  constructor
  · intro h
    rw [claim10_tournament_linkIrregular_iff T hT] at h
    push_neg at h
    rcases h with ⟨u, v, huv, hIso⟩
    let s : TwoSubset (Fin n) := ⟨{u, v}, Finset.card_pair huv⟩
    have hmin : twoSubsetMin s = u ∨ twoSubsetMin s = v := by
      have hm := Finset.min'_mem s.1 (Finset.card_pos.mp (by omega : 0 < s.1.card))
      change twoSubsetMin s ∈ ({u, v} : Finset (Fin n)) at hm
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
    have hmax : twoSubsetMax s = u ∨ twoSubsetMax s = v := by
      have hm := Finset.max'_mem s.1 (Finset.card_pos.mp (by omega : 0 < s.1.card))
      change twoSubsetMax s ∈ ({u, v} : Finset (Fin n)) at hm
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
    refine ⟨s, ?_⟩
    rcases hmin with hmin | hmin <;> rcases hmax with hmax | hmax
    · exact (claim8_twoSubsetMin_ne_twoSubsetMax s (hmin.trans hmax.symm)).elim
    · simpa [hmin, hmax] using hIso
    · simpa [hmin, hmax] using vertexDeletedIsomorphic_symm T u v hIso
    · exact (claim8_twoSubsetMin_ne_twoSubsetMax s (hmin.trans hmax.symm)).elim
  · rintro ⟨s, hIso⟩ hLink
    exact (claim10_tournament_linkIrregular_iff T hT).mp hLink
      (twoSubsetMin s) (twoSubsetMax s) (claim8_twoSubsetMin_ne_twoSubsetMax s) hIso

theorem resultsProof1_uniformProbability_add_not {S : Type*} [Fintype S] [Nonempty S]
    (E : S → Prop) :
    uniformProbability E + uniformProbability (fun x => ¬ E x) = 1 := by
  classical
  letI : DecidablePred E := Classical.decPred E
  letI : DecidablePred (fun x => ¬ E x) := Classical.decPred _
  unfold uniformProbability
  rw [← add_div]
  have hcard := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset S)) E
  apply (div_eq_iff (show (Fintype.card S : ℝ) ≠ 0 by positivity)).2
  norm_cast
  simpa using hcard

private theorem bad_probability_le_pair_sum (n : ℕ) :
    uniformProbability (fun T : Tournament n => ¬ IsLinkIrregular T.1) ≤
      ∑ s : TwoSubset (Fin n),
        deletionIsoProbability n (twoSubsetMin s) (twoSubsetMax s) := by
  classical
  rw [show (fun T : Tournament n => ¬ IsLinkIrregular T.1) =
      (fun T : Tournament n => ∃ s : TwoSubset (Fin n),
        VertexDeletedIsomorphic T.1 (twoSubsetMin s) (twoSubsetMax s)) by
    funext T
    exact propext (not_linkIrregular_iff_exists_deleted_pair T.1 T.2)]
  simpa [deletionIsoProbability] using
    (claim3_uniformProbability_exists_le_sum
      (fun s : TwoSubset (Fin n) => fun T : Tournament n =>
        VertexDeletedIsomorphic T.1 (twoSubsetMin s) (twoSubsetMax s)))

private theorem nat_lt_two_pow_sub_four (n : ℕ) (hn : 10 ≤ n) :
    n < 2 ^ (n - 4) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      rw [show n + 1 - 4 = (n - 4) + 1 by omega, pow_succ]
      omega

private theorem choose_two_lt_two_pow_sub_four (n : ℕ) (hn : 10 ≤ n) :
    n.choose 2 < 2 ^ (n - 4) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [Nat.choose]
  | succ n hn ih =>
      have hn_pow := nat_lt_two_pow_sub_four n hn
      have hrec : (n + 1).choose 2 = n + n.choose 2 := by
        rw [Nat.choose]
        simp
      rw [hrec]
      rw [show n + 1 - 4 = (n - 4) + 1 by omega, pow_succ]
      omega

theorem resultsProof1_bad_probability_lt_ge_ten (n : ℕ) (hn : 10 ≤ n) :
    uniformProbability (fun T : Tournament n => ¬ IsLinkIrregular T.1) <
      (n.choose 2 : ℝ) * (2 : ℝ) ^ (-(n : ℤ) + 4) := by
  classical
  let u : Fin n := ⟨0, by omega⟩
  let v : Fin n := ⟨1, by omega⟩
  have huv : u ≠ v := by simp [u, v]
  let s₀ : TwoSubset (Fin n) := ⟨{u, v}, Finset.card_pair huv⟩
  refine lt_of_le_of_lt (bad_probability_le_pair_sum n) ?_
  calc
    (∑ s : TwoSubset (Fin n),
        deletionIsoProbability n (twoSubsetMin s) (twoSubsetMax s)) <
        ∑ _s : TwoSubset (Fin n), (2 : ℝ) ^ (-(n : ℤ) + 4) := by
      apply Finset.sum_lt_sum
      · intro s _
        exact (claim9_deletion_iso_probability_lt n hn
          (twoSubsetMin s) (twoSubsetMax s)
          (claim8_twoSubsetMin_ne_twoSubsetMax s)).le
      · exact ⟨s₀, Finset.mem_univ _, claim9_deletion_iso_probability_lt n hn
          (twoSubsetMin s₀) (twoSubsetMax s₀)
          (claim8_twoSubsetMin_ne_twoSubsetMax s₀)⟩
    _ = (n.choose 2 : ℝ) * (2 : ℝ) ^ (-(n : ℤ) + 4) := by
      simp

theorem resultsProof1_pair_bound_lt_one (n : ℕ) (hn : 10 ≤ n) :
    (n.choose 2 : ℝ) * (2 : ℝ) ^ (-(n : ℤ) + 4) < 1 := by
  have hchoose : n.choose 2 < 2 ^ (n - 4) :=
    choose_two_lt_two_pow_sub_four n hn
  have hexponent : -(n : ℤ) + 4 = -((n - 4 : ℕ) : ℤ) := by
    omega
  rw [hexponent, zpow_neg, zpow_natCast]
  rw [← div_eq_mul_inv]
  apply (div_lt_one (by positivity : (0 : ℝ) < (2 : ℝ) ^ (n - 4))).2
  exact_mod_cast hchoose

theorem resultsProof1_bad_probability_lt_nine :
    uniformProbability (fun T : Tournament 9 => ¬ IsLinkIrregular T.1) < 1 := by
  have hsum := bad_probability_le_pair_sum 9
  have hpair (s : TwoSubset (Fin 9)) :
      deletionIsoProbability 9 (twoSubsetMin s) (twoSubsetMax s) ≤
        (9 - 2).factorial *
          (2 : ℝ) ^ (-((9 - 1).choose 2 : ℤ)) *
            ∑ k ∈ Finset.range (9 - 1), (g k : ℝ) :=
    theorem3_deletion_iso_probability 9 (by norm_num)
      (twoSubsetMin s) (twoSubsetMax s) (claim8_twoSubsetMin_ne_twoSubsetMax s)
  calc
    uniformProbability (fun T : Tournament 9 => ¬ IsLinkIrregular T.1) ≤
        ∑ s : TwoSubset (Fin 9),
          deletionIsoProbability 9 (twoSubsetMin s) (twoSubsetMax s) := hsum
    _ ≤ ∑ _s : TwoSubset (Fin 9),
        (9 - 2).factorial *
          (2 : ℝ) ^ (-((9 - 1).choose 2 : ℤ)) *
            ∑ k ∈ Finset.range (9 - 1), (g k : ℝ) := by
      gcongr with s
      exact hpair s
    _ < 1 := by
      rcases lemma1_values_of_g with
        ⟨h0, h1, h2, h3, h4, h5, h6, h7, _h8, _h9, _h10, _h11, _h12,
          _h13, _h14, _h15, _h16, _h17, _h18⟩
      rw [Finset.sum_const, Finset.card_univ, claim8_card_twoSubset]
      norm_num [Finset.sum_range_succ, h0, h1, h2, h3, h4, h5, h6, h7,
        Nat.choose]

end BastienKhormali
