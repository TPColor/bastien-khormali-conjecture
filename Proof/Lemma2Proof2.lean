import Proof.Definitions

/-!
# Lemma 2 proof 2

Elementary facts about the unordered vertex-pair index used in Lemma 2 and Results.
-/

namespace BastienKhormali

/-- The minimum and maximum of a two-element subset are distinct. -/
theorem claim8_twoSubsetMin_ne_twoSubsetMax {n : ℕ} (s : TwoSubset (Fin n)) :
    twoSubsetMin s ≠ twoSubsetMax s := by
  apply ne_of_lt
  exact s.1.min'_lt_max'_of_card (by omega)

/-- An `n`-element vertex set has `choose n 2` unordered pairs. -/
theorem claim8_card_twoSubset (n : ℕ) :
    Fintype.card (TwoSubset (Fin n)) = n.choose 2 := by
  classical
  rw [Fintype.card_subtype]
  calc
    (Finset.univ.filter fun s : Finset (Fin n) => s.card = 2).card =
        (Finset.univ.powersetCard 2).card := by
      congr 1
      ext s
      simp
    _ = n.choose 2 := by simp [Finset.card_powersetCard]

end BastienKhormali
