import Proof.Definitions

/-!
# Results proof 1

The finite union bound used in Theorem 3 and Results.
-/

namespace BastienKhormali

/-- **Claim 3 (uniform finite union bound).** The probability that at least one
event in a finite family occurs is at most the sum of their probabilities. -/
theorem claim3_uniformProbability_exists_le_sum {S I : Type*}
    [Fintype S] [Nonempty S] [Fintype I] (P : I → S → Prop) :
    uniformProbability (fun x => ∃ i, P i x) ≤ ∑ i, uniformProbability (P i) := by
  classical
  have hcard :
      (Finset.univ.filter fun x : S => ∃ i, P i x).card ≤
        ∑ i : I, (Finset.univ.filter fun x : S => P i x).card := by
    calc
      (Finset.univ.filter fun x : S => ∃ i, P i x).card =
          (Finset.univ.biUnion fun i : I => Finset.univ.filter fun x : S => P i x).card := by
        congr 1
        ext x
        simp
      _ ≤ ∑ i : I, (Finset.univ.filter fun x : S => P i x).card :=
        Finset.card_biUnion_le
  unfold uniformProbability
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right ?_ (by positivity)
  norm_cast
  convert hcard using 1
  congr 1
  ext x
  simp

end BastienKhormali
