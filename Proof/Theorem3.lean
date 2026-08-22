import Proof.Theorem3Proof1
import Proof.Theorem3Proof3
import Proof.Theorem3Proof4
import Proof.Lemma2

/-!
# Theorem 3
-/

namespace BastienKhormali

set_option maxHeartbeats 1600000 in
/-- **Theorem 3.** For distinct vertices `u` and `v` of a uniformly random
tournament `Tₙ`, the probability that `Tₙ - u` and `Tₙ - v` are isomorphic is
bounded by the stated sum of unlabeled graph counts. -/
theorem theorem3_deletion_iso_probability (n : ℕ) (hn : 2 ≤ n)
    (u v : Fin n) (huv : u ≠ v) :
    deletionIsoProbability n u v ≤
      (n - 2).factorial *
        (2 : ℝ) ^ (-((n - 1).choose 2 : ℤ)) *
          ∑ k ∈ Finset.range (n - 1), (g k : ℝ) := by
  have hevent :
      deletionIsoProbability n u v =
        uniformProbability fun T : Tournament n =>
          ∃ φ : {x : Fin n // x ≠ u} ≃ {x : Fin n // x ≠ v},
            deletionIsoViaEvent T.1 u v φ := by
    unfold deletionIsoProbability
    congr 1
    funext T
    apply propext
    exact claim4_deletionIso_iff_exists_via T.1 u v
  rw [hevent]
  calc
    uniformProbability (fun T : Tournament n =>
        ∃ φ : {x : Fin n // x ≠ u} ≃ {x : Fin n // x ≠ v},
          deletionIsoViaEvent T.1 u v φ) ≤
        ∑ φ : {x : Fin n // x ≠ u} ≃ {x : Fin n // x ≠ v},
          deletionIsoViaProbability n u v φ :=
      claim7_deleted_bijection_union_bound n u v
    _ ≤ ∑ φ : {x : Fin n // x ≠ u} ≃ {x : Fin n // x ≠ v},
        (2 : ℝ) ^
          (-((n - 1).choose 2 : ℤ) + (cyclePairOrbitCount n u v φ : ℤ)) := by
      gcongr with φ
      exact lemma2_deletion_iso_via_probability n hn u v huv φ
    _ = (2 : ℝ) ^ (-((n - 1).choose 2 : ℤ)) *
        ∑ φ : {x : Fin n // x ≠ u} ≃ {x : Fin n // x ≠ v},
          (2 : ℝ) ^ cyclePairOrbitCount n u v φ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro φ _
      rw [← zpow_natCast]
      rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    _ = (n - 2).factorial *
        (2 : ℝ) ^ (-((n - 1).choose 2 : ℤ)) *
          ∑ k ∈ Finset.range (n - 1), (g k : ℝ) := by
      rw [claim6_deleted_bijection_identity n u v huv]
      ring

end BastienKhormali
