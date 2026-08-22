import Proof.Lemma2Proof2

/-!
# Lemma 2 proof 1

The component-count and orientation-propagation steps used in Lemma 2.
-/

namespace BastienKhormali

private theorem component_from_last_cut {α : Type*} [Fintype α] [DecidableEq α]
    (q : Equiv.Perm α) (cut : α → Prop) (x : α)
    (h : ∃ c, cut c ∧ q.SameCycle c x) :
    ∃ c, cut c ∧ Relation.EqvGen (partialPermutationEdge q cut) (q c) x := by
  classical
  have hex : ∃ i : ℕ, 0 < i ∧ ∃ c, cut c ∧ (q ^ i) c = x := by
    obtain ⟨c, hc, hcx⟩ := h
    obtain ⟨i, hi, -, hix⟩ := hcx.exists_pow_eq q
    exact ⟨i, hi, c, hc, hix⟩
  let i := Nat.find hex
  have hi := Nat.find_spec hex
  obtain ⟨c, hc, hic⟩ := hi.2
  refine ⟨c, hc, ?_⟩
  have hnocut : ∀ j : ℕ, 0 < j → j < i → ¬ cut ((q ^ j) c) := by
    intro j hj0 hji hjcut
    have hsub : 0 < i - j := Nat.sub_pos_of_lt hji
    have hpow : (q ^ (i - j)) ((q ^ j) c) = x := by
      rw [← Equiv.Perm.mul_apply, ← pow_add]
      rw [Nat.sub_add_cancel hji.le, hic]
    have hle : i ≤ i - j := Nat.find_min' hex
      ⟨hsub, (q ^ j) c, hjcut, hpow⟩
    omega
  have hwalk : ∀ j : ℕ, j < i →
      Relation.EqvGen (partialPermutationEdge q cut) (q c) ((q ^ (j + 1)) c) := by
    intro j hj
    induction j with
    | zero => simpa using
        (Relation.EqvGen.refl (r := partialPermutationEdge q cut) (q c))
    | succ j ih =>
        have hji : j < i := Nat.lt_trans (Nat.lt_succ_self j) hj
        have hprev := ih hji
        apply Relation.EqvGen.trans _ _ _ hprev
        apply Relation.EqvGen.rel
        refine ⟨hnocut (j + 1) (by omega) hj, ?_⟩
        simp only [← Equiv.Perm.mul_apply, ← pow_succ']
  have hw := hwalk (i - 1) (by omega)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ i), hic] at hw
  exact hw

private theorem same_component_of_uncut_cycle {α : Type*} [Fintype α] [DecidableEq α]
    (q : Equiv.Perm α) (cut : α → Prop) (x y : α)
    (havoid : ∀ z : ℤ, ¬ cut ((q ^ z) x)) (hxy : q.SameCycle x y) :
    Relation.EqvGen (partialPermutationEdge q cut) x y := by
  classical
  obtain ⟨i, -, -, hpow⟩ := hxy.exists_pow_eq q
  have hwalk : ∀ j : ℕ,
      Relation.EqvGen (partialPermutationEdge q cut) x ((q ^ j) x) := by
    intro j
    induction j with
    | zero => exact Relation.EqvGen.refl _
    | succ j ih =>
        apply Relation.EqvGen.trans _ _ _ ih
        apply Relation.EqvGen.rel
        refine ⟨?_, ?_⟩
        · simpa [zpow_natCast] using havoid (j : ℤ)
        · simp only [← Equiv.Perm.mul_apply, ← pow_succ']
  simpa [hpow] using hwalk i

private theorem cycle_pair_step {V : Type*} [Fintype V] [DecidableEq V]
    (u v : V) (φ : {x : V // x ≠ u} ≃ {x : V // x ≠ v})
    (s : TwoSubset (CycleVertices u v φ)) :
    permuteTwoSubsets (extendDeletedEquiv u v φ)
        ⟨s.1.map (Function.Embedding.subtype _), by simp [s.2]⟩ =
      ⟨(permuteTwoSubsets (cyclePermutation u v φ) s).1.map
          (Function.Embedding.subtype _), by simpa using
            (permuteTwoSubsets (cyclePermutation u v φ) s).2⟩ := by
  let p := extendDeletedEquiv u v φ
  have horbit (x : V) : InPermutationOrbit p u (p x) ↔ InPermutationOrbit p u x := by
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨z - 1, ?_⟩
      calc
        (p ^ (z - 1)) u = (p ^ z) (p.symm u) := by
          rw [zpow_sub_one, Equiv.Perm.mul_apply, Equiv.Perm.inv_def]
        _ = p.symm ((p ^ z) u) := by
          simpa using p.zpow_apply_comm z (-1) (x := u)
        _ = p.symm (p x) := congrArg p.symm hz
        _ = x := by simp
    · rintro ⟨z, hz⟩
      refine ⟨z + 1, ?_⟩
      calc
        (p ^ (z + 1)) u = (p ^ z) (p u) := by
          rw [zpow_add_one, Equiv.Perm.mul_apply]
        _ = p ((p ^ z) u) := p.zpow_apply_comm z 1
        _ = p x := congrArg p hz
  have horbit_symm (x : V) :
      ¬ InPermutationOrbit p u (p.symm x) ↔ ¬ InPermutationOrbit p u x :=
    by simpa using not_congr (horbit (p.symm x)).symm
  apply Subtype.ext
  ext x
  simp [permuteTwoSubsets, permuteTwoSubsetsHom, cyclePermutation, p, horbit_symm]

private theorem cycle_pair_zpow {V : Type*} [Fintype V] [DecidableEq V]
    (u v : V) (φ : {x : V // x ≠ u} ≃ {x : V // x ≠ v})
    (z : ℤ) (s : TwoSubset (CycleVertices u v φ)) :
    ((permuteTwoSubsets (extendDeletedEquiv u v φ)) ^ z)
        ⟨s.1.map (Function.Embedding.subtype _), by simp [s.2]⟩ =
      ⟨(((permuteTwoSubsets (cyclePermutation u v φ)) ^ z) s).1.map
          (Function.Embedding.subtype _), by simpa using
            (((permuteTwoSubsets (cyclePermutation u v φ)) ^ z) s).2⟩ := by
  let embed : TwoSubset (CycleVertices u v φ) → TwoSubset V := fun t =>
    ⟨t.1.map (Function.Embedding.subtype _), by simp [t.2]⟩
  let r := permuteTwoSubsets (cyclePermutation u v φ)
  let q := permuteTwoSubsets (extendDeletedEquiv u v φ)
  have hstep : Function.Semiconj embed r q := by
    intro t
    exact (cycle_pair_step u v φ t).symm
  have hstep_inv : Function.Semiconj embed r.symm q.symm := by
    intro t
    apply q.injective
    rw [q.apply_symm_apply]
    rw [← hstep]
    simp
  cases z with
  | ofNat k =>
      have hiter := hstep.iterate_right k
      unfold Function.Semiconj at hiter
      have hs := hiter s
      simpa [embed, r, q, Equiv.Perm.iterate_eq_pow] using hs.symm
  | negSucc k =>
      have hiter := hstep_inv.iterate_right (k + 1)
      unfold Function.Semiconj at hiter
      have hs := hiter s
      simpa [embed, r, q, Equiv.Perm.iterate_eq_pow, zpow_negSucc] using hs.symm

private theorem pair_preimage_mem {V : Type*} [Fintype V] [DecidableEq V]
    (p : Equiv.Perm V) (u x : V) (s : TwoSubset V) (z : ℤ)
    (hz : (p ^ z) u = x) (hx : x ∈ s.1) :
    u ∈ (((permuteTwoSubsets p) ^ (-z)) s).1 := by
  have hmem : (p ^ z) u ∈ s.1 := by simpa [hz] using hx
  change u ∈ (((permuteTwoSubsetsHom p) ^ (-z)) s).1
  rw [← map_zpow permuteTwoSubsetsHom p (-z)]
  simpa [permuteTwoSubsets, permuteTwoSubsetsHom] using hmem

theorem lemma2Proof1_component_count_le (n : ℕ) (u v : Fin n)
    (φ : {x : Fin n // x ≠ u} ≃ {x : Fin n // x ≠ v}) :
    Nat.card (Quotient (partialPermutationSetoid
      (permuteTwoSubsets (extendDeletedEquiv u v φ)) (fun s => u ∈ s.1))) ≤
      n - 1 + cyclePairOrbitCount n u v φ := by
  classical
  let p := extendDeletedEquiv u v φ
  let q := permuteTwoSubsets p
  let cut : TwoSubset (Fin n) → Prop := fun s => u ∈ s.1
  let embed : TwoSubset (CycleVertices u v φ) → TwoSubset (Fin n) := fun t =>
    ⟨t.1.map (Function.Embedding.subtype _), by simp [t.2]⟩
  let Source := PairsContaining u ⊕
    Quotient (pairOrbitSetoid (cyclePermutation u v φ))
  let Target := Quotient (partialPermutationSetoid q cut)
  have hAvoid (t : TwoSubset (CycleVertices u v φ)) (z : ℤ) :
      ¬ cut ((q ^ z) (embed t)) := by
    rw [show (q ^ z) (embed t) = embed
        (((permuteTwoSubsets (cyclePermutation u v φ)) ^ z) t) by
      exact cycle_pair_zpow u v φ z t]
    simp only [cut, embed, Finset.mem_map, Function.Embedding.coe_subtype]
    rintro ⟨x, hx, hxu⟩
    exact x.2 ⟨0, by simpa using hxu.symm⟩
  have hRespect {a b : TwoSubset (CycleVertices u v φ)}
      (hab : (pairOrbitSetoid (cyclePermutation u v φ)).r a b) :
      Relation.EqvGen (partialPermutationEdge q cut) (embed a) (embed b) := by
    obtain ⟨z, hz⟩ := hab
    apply same_component_of_uncut_cycle q cut (embed a) (embed b) (hAvoid a)
    refine ⟨z, ?_⟩
    rw [show (q ^ z) (embed a) = embed
        (((permuteTwoSubsets (cyclePermutation u v φ)) ^ z) a) by
      exact cycle_pair_zpow u v φ z a]
    exact congrArg embed hz
  let toTarget : Source → Target := fun x => match x with
    | Sum.inl c => Quotient.mk'' (q c.1)
    | Sum.inr o => Quotient.map embed (fun _ _ h => hRespect h) o
  have hsurj : Function.Surjective toTarget := by
    intro component
    refine Quotient.inductionOn component ?_
    intro s
    by_cases hall : ∀ x ∈ s.1, ¬ InPermutationOrbit p u x
    · let e : {x : Fin n // x ∈ s.1} ↪ CycleVertices u v φ :=
        ⟨fun x => ⟨x.1, by simpa [p] using hall x.1 x.2⟩,
          fun x y hxy => Subtype.ext
            (congrArg (fun z : CycleVertices u v φ => z.1) hxy)⟩
      let t : TwoSubset (CycleVertices u v φ) :=
        ⟨s.1.attach.map e, by rw [Finset.card_map]; simp [s.2]⟩
      have hembed : embed t = s := by
        apply Subtype.ext
        ext x
        simp [embed, t, e, p]
        intro hx
        simpa [p] using hall x hx
      refine ⟨Sum.inr (Quotient.mk'' t), ?_⟩
      change Quotient.mk'' (embed t) = Quotient.mk'' s
      rw [hembed]
    · push_neg at hall
      obtain ⟨x, hxs, hxorb⟩ := hall
      obtain ⟨z, hz⟩ := hxorb
      let c : TwoSubset (Fin n) := (q ^ (-z)) s
      have hcutc : cut c := by
        exact pair_preimage_mem p u x s z hz hxs
      have hcycle : q.SameCycle c s := by
        refine ⟨z, ?_⟩
        simp [c]
      obtain ⟨d, hdcut, hds⟩ := component_from_last_cut q cut s ⟨c, hcutc, hcycle⟩
      let d' : PairsContaining u := ⟨d, hdcut⟩
      refine ⟨Sum.inl d', ?_⟩
      exact Quotient.sound hds
  change Nat.card (Quotient (partialPermutationSetoid q cut)) ≤ _
  calc
    Nat.card Target ≤ Nat.card Source :=
      Nat.card_le_card_of_surjective toTarget hsurj
    _ = Nat.card (PairsContaining u) +
        Nat.card (Quotient (pairOrbitSetoid (cyclePermutation u v φ))) :=
      Nat.card_sum
    _ = (n - 1) + cyclePairOrbitCount n u v φ := by
      congr 1
      · simpa using Nat.card_congr (otherVertexPairEquiv u).symm

private theorem pair_agreement_iff {n : ℕ} (T T' : Tournament n)
    (s : TwoSubset (Fin n)) (x y : Fin n) (hx : x ∈ s.1) (hy : y ∈ s.1)
    (hxy : x ≠ y) :
    ((s ∈ tournamentPairSet T ↔ s ∈ tournamentPairSet T') ↔
      (T.1.Adj x y ↔ T'.1.Adj x y)) := by
  classical
  have hs : ({x, y} : Finset (Fin n)) = s.1 := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hx
      · exact hy
    · simp [s.2, hxy]
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · simp [tournamentPairSet, twoSubsetMin, twoSubsetMax, ← hs, hlt.le]
  · have hT := T.2.2 x y hxy
    have hT' := T'.2.2 x y hxy
    simp [tournamentPairSet, twoSubsetMin, twoSubsetMax, ← hs, hgt.le]
    tauto

theorem lemma2Proof1_pair_agreement_propagates (n : ℕ) (u v : Fin n)
    (φ : {x : Fin n // x ≠ u} ≃ {x : Fin n // x ≠ v})
    (T T' : Tournament n)
    (hT : deletionIsoViaEvent T.1 u v φ)
    (hT' : deletionIsoViaEvent T'.1 u v φ)
    (s : TwoSubset (Fin n)) (hsu : u ∉ s.1) :
    ((s ∈ tournamentPairSet T ↔ s ∈ tournamentPairSet T') ↔
      (permuteTwoSubsets (extendDeletedEquiv u v φ) s ∈ tournamentPairSet T ↔
        permuteTwoSubsets (extendDeletedEquiv u v φ) s ∈ tournamentPairSet T')) := by
  classical
  let a := twoSubsetMin s
  let b := twoSubsetMax s
  have ha : a ∈ s.1 := Finset.min'_mem _ _
  have hb : b ∈ s.1 := Finset.max'_mem _ _
  have hab : a ≠ b := claim8_twoSubsetMin_ne_twoSubsetMax s
  have hau : a ≠ u := fun h => hsu (h ▸ ha)
  have hbu : b ≠ u := fun h => hsu (h ▸ hb)
  let p := extendDeletedEquiv u v φ
  let q := permuteTwoSubsets p
  have hpa : p a ∈ (q s).1 := by
    simp [p, q, permuteTwoSubsets, permuteTwoSubsetsHom, ha]
  have hpb : p b ∈ (q s).1 := by
    simp [p, q, permuteTwoSubsets, permuteTwoSubsetsHom, hb]
  have hpab : p a ≠ p b := p.injective.ne hab
  have hmapT : T.1.Adj a b ↔ T.1.Adj (p a) (p b) := by
    simpa [p, extendDeletedEquiv, hau, hbu] using hT ⟨a, hau⟩ ⟨b, hbu⟩
  have hmapT' : T'.1.Adj a b ↔ T'.1.Adj (p a) (p b) := by
    simpa [p, extendDeletedEquiv, hau, hbu] using hT' ⟨a, hau⟩ ⟨b, hbu⟩
  rw [pair_agreement_iff T T' s a b ha hb hab]
  rw [pair_agreement_iff T T' (q s) (p a) (p b) hpa hpb hpab]
  tauto

end BastienKhormali
