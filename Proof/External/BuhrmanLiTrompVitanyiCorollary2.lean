import Proof.Definitions

/-!
# Buhrman--Li--Tromp--Vitányi, Corollary 2

This file isolates the graph-enumeration estimate used as an external theorem in the
informal proof.
-/

namespace BastienKhormali

/-- Buhrman, Li, Tromp, and Vitányi, *Kolmogorov random graphs and the
incompressibility method*, Corollary 2, in the notation of the informal proof. -/
axiom buhrman_li_tromp_vitanyi_bound (n : ℕ) :
    (g n : ℝ) ≤
      (2 : ℝ) ^ n.choose 2 / n.factorial *
        (1 + 4 * (n : ℝ) ^ 4 / (2 : ℝ) ^ n)

end BastienKhormali
