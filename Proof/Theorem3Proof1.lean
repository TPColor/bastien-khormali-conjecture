import Proof.Definitions

/-!
# Theorem 3 proof 1

The event identity used before applying the union bound in Theorem 3.
-/

namespace BastienKhormali

/-- **Claim 4.** `T - u` and `T - v` are isomorphic exactly when some bijection
between their vertex sets realizes an isomorphism. -/
theorem claim4_deletionIso_iff_exists_via {V : Type*} (T : Digraph V) (u v : V) :
    VertexDeletedIsomorphic T u v ↔
      ∃ φ : {x : V // x ≠ u} ≃ {x : V // x ≠ v}, deletionIsoViaEvent T u v φ := by
  constructor
  · rintro ⟨e⟩
    refine ⟨e.toEquiv, ?_⟩
    intro x y
    exact e.map_rel_iff.symm
  · rintro ⟨φ, hφ⟩
    exact ⟨⟨φ, fun {_ _} => (hφ _ _).symm⟩⟩

end BastienKhormali
