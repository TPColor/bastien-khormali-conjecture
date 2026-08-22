import Proof.Definitions

/-!
# Theorem 3 proof 2

The application of general Burnside's lemma to labeled simple graphs.
-/

namespace BastienKhormali

private theorem graphTwoSubsetSet_permute_iff (n : ℕ) (σ : Equiv.Perm (Fin n))
    (G : SimpleGraph (Fin n)) (s : TwoSubset (Fin n)) :
    permuteTwoSubsets σ s ∈ graphTwoSubsetSet (σ • G) ↔
      s ∈ graphTwoSubsetSet G := by
  rcases s with ⟨s, hs⟩
  rcases Finset.card_eq_two.mp hs with ⟨x, y, hxy, rfl⟩
  have hσxy : σ x ≠ σ y := σ.injective.ne hxy
  have hpair :
      permuteTwoSubsets σ (⟨{x, y}, Finset.card_pair hxy⟩ : TwoSubset (Fin n)) =
        ⟨{σ x, σ y}, Finset.card_pair hσxy⟩ := by
    apply Subtype.ext
    ext a
    simp [permuteTwoSubsets, permuteTwoSubsetsHom]
  rw [hpair]
  have hadj : (σ • G).Adj (σ x) (σ y) ↔ G.Adj x y := by
    change G.Adj (σ.symm (σ x)) (σ.symm (σ y)) ↔ G.Adj x y
    simp
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  ·
    by_cases hσ : σ x ≤ σ y
    · simpa [graphTwoSubsetSet, twoSubsetMin, twoSubsetMax, hlt.le,
        min_eq_left hσ, max_eq_right hσ, SimpleGraph.adj_comm] using hadj
    · have hσ' : σ y ≤ σ x := le_of_not_ge hσ
      simpa [graphTwoSubsetSet, twoSubsetMin, twoSubsetMax, hlt.le,
        min_eq_right hσ', max_eq_left hσ', SimpleGraph.adj_comm] using hadj
  ·
    by_cases hσ : σ x ≤ σ y
    · simpa [graphTwoSubsetSet, twoSubsetMin, twoSubsetMax, hgt.le,
        min_eq_left hσ, max_eq_right hσ, SimpleGraph.adj_comm] using hadj
    · have hσ' : σ y ≤ σ x := le_of_not_ge hσ
      simpa [graphTwoSubsetSet, twoSubsetMin, twoSubsetMax, hgt.le,
        min_eq_right hσ', max_eq_left hσ', SimpleGraph.adj_comm] using hadj

private theorem permuteTwoSubsets_zpow (n : ℕ) (σ : Equiv.Perm (Fin n)) (z : ℤ) :
    permuteTwoSubsets (σ ^ z) = (permuteTwoSubsets σ) ^ z := by
  exact map_zpow (permuteTwoSubsetsHom (V := Fin n)) σ z

/-- **Claim 5(a).** A graph fixed by `σ` is obtained by choosing independently
whether each orbit of `σ` on unordered vertex pairs is an edge. -/
theorem claim5_card_fixedGraphs_eq_two_pow_pairOrbitCount (n : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    Nat.card (MulAction.fixedBy (SimpleGraph (Fin n)) σ) = 2 ^ pairOrbitCount σ := by
  classical
  let Q := Quotient (pairOrbitSetoid σ)
  let toOrbitSet : MulAction.fixedBy (SimpleGraph (Fin n)) σ → Set Q := fun G =>
    {q | Quotient.lift (fun s => s ∈ graphTwoSubsetSet G.1) (by
      intro a b hab
      rcases hab with ⟨z, rfl⟩
      have hpow : (σ ^ z) • G.1 = G.1 :=
        MulAction.mem_fixedBy_zpow G.2 z
      rw [← permuteTwoSubsets_zpow]
      apply propext
      simpa [hpow] using
        (graphTwoSubsetSet_permute_iff n (σ ^ z) G.1 a).symm) q}
  let fromOrbitSet : Set Q → MulAction.fixedBy (SimpleGraph (Fin n)) σ := fun A =>
    ⟨twoSubsetSetGraph {s | Quotient.mk'' s ∈ A}, by
      apply (simpleGraphTwoSubsetEquiv n).injective
      change graphTwoSubsetSet (σ • twoSubsetSetGraph {s | Quotient.mk'' s ∈ A}) =
        graphTwoSubsetSet (twoSubsetSetGraph {s | Quotient.mk'' s ∈ A})
      ext s
      let t := permuteTwoSubsets σ.symm s
      have ht := graphTwoSubsetSet_permute_iff n σ
        (twoSubsetSetGraph {s | Quotient.mk'' s ∈ A}) t
      have hperm : permuteTwoSubsets σ t = s := by
        change (permuteTwoSubsetsHom σ) ((permuteTwoSubsetsHom σ.symm) s) = s
        rw [← Equiv.Perm.mul_apply, ← map_mul]
        simp
      rw [hperm] at ht
      rw [ht]
      have hinv := (simpleGraphTwoSubsetEquiv n).apply_symm_apply
        ({r | Quotient.mk'' r ∈ A} : Set (TwoSubset (Fin n)))
      change graphTwoSubsetSet (twoSubsetSetGraph {r | Quotient.mk'' r ∈ A}) =
        {r | Quotient.mk'' r ∈ A} at hinv
      rw [Set.ext_iff.mp hinv t, Set.ext_iff.mp hinv s]
      change Quotient.mk'' t ∈ A ↔ Quotient.mk'' s ∈ A
      have heq : Quotient.mk'' t = (Quotient.mk'' s : Q) := by
        apply Quotient.sound
        refine ⟨1, ?_⟩
        change (permuteTwoSubsets σ) t = s
        exact hperm
      rw [heq]⟩
  let e : MulAction.fixedBy (SimpleGraph (Fin n)) σ ≃ Set Q :=
    { toFun := toOrbitSet
      invFun := fromOrbitSet
      left_inv := by
        intro G
        apply Subtype.ext
        change twoSubsetSetGraph {s | Quotient.mk'' s ∈ toOrbitSet G} = G.1
        have hset : {s | Quotient.mk'' s ∈ toOrbitSet G} = graphTwoSubsetSet G.1 := by
          ext s
          rfl
        rw [hset]
        exact (simpleGraphTwoSubsetEquiv n).symm_apply_apply G.1
      right_inv := by
        intro A
        ext q
        refine Quotient.inductionOn q ?_
        intro s
        change s ∈ graphTwoSubsetSet (twoSubsetSetGraph {t | Quotient.mk'' t ∈ A}) ↔
          Quotient.mk'' s ∈ A
        have h := (simpleGraphTwoSubsetEquiv n).apply_symm_apply
          ({t | Quotient.mk'' t ∈ A} : Set (TwoSubset (Fin n)))
        exact Set.ext_iff.mp h s }
  calc
    Nat.card (MulAction.fixedBy (SimpleGraph (Fin n)) σ) = Nat.card (Set Q) :=
      Nat.card_congr e
    _ = 2 ^ Nat.card Q := by simp
    _ = 2 ^ pairOrbitCount σ := rfl

/-- **Claim 5.** Applying Burnside's lemma to the action of `Sₙ` on labeled
simple graphs gives `∑σ 2 ^ o₂(σ) = n! gₙ`. -/
theorem claim5_burnside_pair_orbit_identity (n : ℕ) :
    ∑ σ : Equiv.Perm (Fin n), 2 ^ pairOrbitCount σ = n.factorial * g n := by
  classical
  have h :
      (∑ σ : Equiv.Perm (Fin n),
          Nat.card (MulAction.fixedBy (SimpleGraph (Fin n)) σ)) =
        Nat.card
            (Quotient
              (MulAction.orbitRel
                (Equiv.Perm (Fin n)) (SimpleGraph (Fin n)))) *
          Nat.card (Equiv.Perm (Fin n)) := by
    letI (σ : Equiv.Perm (Fin n)) :
        Fintype (MulAction.fixedBy (SimpleGraph (Fin n)) σ) :=
      Fintype.ofFinite _
    letI :
        Fintype
          (Quotient
            (MulAction.orbitRel
              (Equiv.Perm (Fin n)) (SimpleGraph (Fin n)))) :=
      Fintype.ofFinite _
    simpa [Nat.card_eq_fintype_card] using
      (MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
        (Equiv.Perm (Fin n)) (SimpleGraph (Fin n)))
  simp_rw [claim5_card_fixedGraphs_eq_two_pow_pairOrbitCount] at h
  simpa [g, simpleGraphIsoSetoid, Fintype.card_perm, mul_comm] using h

end BastienKhormali
