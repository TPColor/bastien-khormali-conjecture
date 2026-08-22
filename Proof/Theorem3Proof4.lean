import Proof.ResultsProof1

/-!
# Theorem 3 proof 4

The union bound specialized to the deleted-vertex bijections in Theorem 3.
-/

namespace BastienKhormali

set_option maxHeartbeats 1600000 in
/-- **Claim 7.** The probability that one of the specified deleted-vertex
bijections is an isomorphism is at most the sum of the individual probabilities. -/
theorem claim7_deleted_bijection_union_bound (n : ℕ) (u v : Fin n) :
    uniformProbability (fun T : Tournament n =>
        ∃ φ : {x : Fin n // x ≠ u} ≃ {x : Fin n // x ≠ v},
          deletionIsoViaEvent T.1 u v φ) ≤
      ∑ φ : {x : Fin n // x ≠ u} ≃ {x : Fin n // x ≠ v},
        deletionIsoViaProbability n u v φ := by
  exact claim3_uniformProbability_exists_le_sum
    (S := Tournament n)
    (I := {x : Fin n // x ≠ u} ≃ {x : Fin n // x ≠ v})
    (fun φ (T : Tournament n) => deletionIsoViaEvent T.1 u v φ)

end BastienKhormali
