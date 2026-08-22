import Proof.ResultsProof4
import Proof.ResultsProof5

/-!
# Main results

The two main statements from the informal proof.
-/

namespace BastienKhormali

/-- If `n ≥ 9`, then there exists a link-irregular tournament with `n` vertices. -/
theorem exists_linkIrregular_tournament (n : ℕ) (hn : n ≥ 9) :
    ∃ T : Digraph (Fin n), IsTournament T ∧ IsLinkIrregular T := by
  classical
  have hbad :
      uniformProbability (fun T : Tournament n => ¬ IsLinkIrregular T.1) < 1 := by
    by_cases h9 : n = 9
    · subst n
      exact resultsProof1_bad_probability_lt_nine
    · exact lt_trans (resultsProof1_bad_probability_lt_ge_ten n (by omega))
        (resultsProof1_pair_bound_lt_one n (by omega))
  have hcomplement :=
    resultsProof1_uniformProbability_add_not
      (fun T : Tournament n => IsLinkIrregular T.1)
  have hgood :
      0 < uniformProbability (fun T : Tournament n => IsLinkIrregular T.1) := by
    linarith
  have hcard :
      0 < (Finset.univ.filter fun T : Tournament n => IsLinkIrregular T.1).card := by
    by_contra h
    have hz :
        (Finset.univ.filter fun T : Tournament n => IsLinkIrregular T.1).card = 0 :=
      Nat.eq_zero_of_not_pos h
    unfold uniformProbability at hgood
    rw [hz] at hgood
    norm_num at hgood
  rcases Finset.card_pos.mp hcard with ⟨T, hT⟩
  exact ⟨T.1, T.2, (Finset.mem_filter.mp hT).2⟩

/-- A uniformly random tournament is asymptotically almost surely
link-irregular. -/
theorem random_tournament_is_asymptotically_almost_surely_linkIrregular :
    Filter.Tendsto linkIrregularTournamentProbability Filter.atTop (nhds 1) := by
  have hcomplement :
      linkIrregularTournamentProbability =
        fun n : ℕ => 1 -
          uniformProbability (fun T : Tournament n => ¬ IsLinkIrregular T.1) := by
    funext n
    unfold linkIrregularTournamentProbability
    linarith [resultsProof1_uniformProbability_add_not
      (fun T : Tournament n => IsLinkIrregular T.1)]
  rw [hcomplement]
  have hone :
      Filter.Tendsto (fun _n : ℕ => (1 : ℝ)) Filter.atTop (nhds 1) :=
    tendsto_const_nhds
  simpa using hone.sub resultsProof2_bad_probability_tendsto_zero

end BastienKhormali
