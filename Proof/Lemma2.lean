import Proof.Lemma2Proof1

/-!
# Lemma 2

Statement of Lemma 2 from the informal proof.
-/

namespace BastienKhormali

/-- **Lemma 2.** Let `n ≥ 2`, let `u` and `v` be distinct vertices, and let `φ`
be a bijection from the vertices other than `u` to the vertices other than `v`.
Then `P(Bφ) ≤ 2 ^ (-choose (n - 1) 2 + o₂(σφ))`. -/
theorem lemma2_deletion_iso_via_probability (n : ℕ) (hn : 2 ≤ n)
    (u v : Fin n) (_huv : u ≠ v)
    (φ : {x : Fin n // x ≠ u} ≃ {x : Fin n // x ≠ v}) :
    deletionIsoViaProbability n u v φ ≤
      (2 : ℝ) ^
        (-((n - 1).choose 2 : ℤ) + (cyclePairOrbitCount n u v φ : ℤ)) := by
  classical
  let Event := {T : Tournament n // deletionIsoViaEvent T.1 u v φ}
  by_cases hEvent : Nonempty Event
  · let T₀ : Event := hEvent.some
    let q := permuteTwoSubsets (extendDeletedEquiv u v φ)
    let cut : TwoSubset (Fin n) → Prop := fun s => u ∈ s.1
    let Components := Quotient (partialPermutationSetoid q cut)
    have hwell (T : Event) (a b : TwoSubset (Fin n))
        (hab : Relation.EqvGen (partialPermutationEdge q cut) a b) :
        (¬ (a ∈ tournamentPairSet T.1 ↔ a ∈ tournamentPairSet T₀.1)) =
          (¬ (b ∈ tournamentPairSet T.1 ↔ b ∈ tournamentPairSet T₀.1)) := by
      apply propext
      induction hab with
      | rel a b hab =>
          rcases hab with ⟨ha, rfl⟩
          exact not_congr
            (lemma2Proof1_pair_agreement_propagates n u v φ T.1 T₀.1 T.2 T₀.2 a ha)
      | refl => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    let code : Event → Set Components := fun T =>
      {c | Quotient.lift
        (fun s => ¬ (s ∈ tournamentPairSet T.1 ↔ s ∈ tournamentPairSet T₀.1))
        (hwell T) c}
    have hcode : Function.Injective code := by
      intro T T' hTT'
      apply Subtype.ext
      apply (tournamentPairSetEquiv n).injective
      ext s
      have hc := Set.ext_iff.mp hTT' (Quotient.mk'' s)
      change
        (¬ (s ∈ tournamentPairSet T.1 ↔ s ∈ tournamentPairSet T₀.1)) ↔
          (¬ (s ∈ tournamentPairSet T'.1 ↔ s ∈ tournamentPairSet T₀.1)) at hc
      tauto
    have hcomponent : Fintype.card Components ≤
        n - 1 + cyclePairOrbitCount n u v φ := by
      rw [← Nat.card_eq_fintype_card]
      simpa [Components, q, cut] using lemma2Proof1_component_count_le n u v φ
    have hcardEvent : Fintype.card Event ≤
        2 ^ (n - 1 + cyclePairOrbitCount n u v φ) := by
      calc
        Fintype.card Event ≤ Fintype.card (Set Components) :=
          Fintype.card_le_of_injective code hcode
        _ = 2 ^ Fintype.card Components := Fintype.card_set
        _ ≤ 2 ^ (n - 1 + cyclePairOrbitCount n u v φ) := by
          exact pow_le_pow_right₀ (by omega) hcomponent
    have hfilter :
        (Finset.univ.filter fun T : Tournament n => deletionIsoViaEvent T.1 u v φ).card =
          Fintype.card Event := by
      rw [Fintype.card_subtype]
    have hnum :
        ((Finset.univ.filter fun T : Tournament n =>
          deletionIsoViaEvent T.1 u v φ).card : ℝ) ≤
            (2 : ℝ) ^ (n - 1 + cyclePairOrbitCount n u v φ) := by
      rw [hfilter]
      exact_mod_cast hcardEvent
    have hcardTournament : Fintype.card (Tournament n) = 2 ^ n.choose 2 := by
      calc
        Fintype.card (Tournament n) = Fintype.card (Set (TwoSubset (Fin n))) :=
          Fintype.card_congr (tournamentPairSetEquiv n)
        _ = 2 ^ Fintype.card (TwoSubset (Fin n)) := Fintype.card_set
        _ = 2 ^ n.choose 2 := by rw [claim8_card_twoSubset]
    have hchoose : n.choose 2 = (n - 1).choose 2 + (n - 1) := by
      rw [show n = (n - 1) + 1 by omega, Nat.choose]
      simp [Nat.add_comm]
    have hquotient :
        (2 : ℝ) ^ (n - 1 + cyclePairOrbitCount n u v φ) /
            (2 : ℝ) ^ n.choose 2 =
          (2 : ℝ) ^
            (-((n - 1).choose 2 : ℤ) + (cyclePairOrbitCount n u v φ : ℤ)) := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
      congr 1
      rw [hchoose]
      push_cast
      omega
    unfold deletionIsoViaProbability uniformProbability
    rw [hcardTournament]
    push_cast
    exact (div_le_div_of_nonneg_right hnum (by positivity)).trans_eq hquotient
  · have hzero :
        (Finset.univ.filter fun T : Tournament n => deletionIsoViaEvent T.1 u v φ).card = 0 := by
      apply Finset.card_eq_zero.mpr
      by_contra hne
      obtain ⟨T, hT⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
      exact hEvent ⟨T, hT⟩
    unfold deletionIsoViaProbability uniformProbability
    simp [hzero]
    positivity

end BastienKhormali
