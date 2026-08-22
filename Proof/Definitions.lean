import Mathlib

/-!
# Definitions

Definitions used throughout the formalization of the Bastien--Khormali conjecture.
-/

namespace BastienKhormali

/-- A directed graph is a tournament if it has no loops and exactly one directed edge
between every two distinct vertices. -/
def IsTournament {V : Type*} (T : Digraph V) : Prop :=
  (∀ v, ¬ T.Adj v v) ∧
    ∀ (u v : V), u ≠ v →
      (T.Adj u v ∨ T.Adj v u) ∧ ¬ (T.Adj u v ∧ T.Adj v u)

/-- A labeled tournament on the vertex set `Fin n`. -/
abbrev Tournament (n : ℕ) := {T : Digraph (Fin n) // IsTournament T}

noncomputable instance tournamentFintype (n : ℕ) : Fintype (Tournament n) :=
  Fintype.ofFinite (Tournament n)

/-- There is a tournament on `Fin n` for every `n`: orient each pair according to
the linear order on `Fin n`. -/
noncomputable instance tournamentNonempty (n : ℕ) : Nonempty (Tournament n) := by
  let T : Digraph (Fin n) := ⟨fun x y => x < y⟩
  refine ⟨⟨T, ?_⟩⟩
  constructor
  · exact fun x => lt_irrefl x
  · intro x y hxy
    rcases lt_or_gt_of_ne hxy with hlt | hgt
    · exact ⟨Or.inl hlt, fun h => (not_lt_of_ge hlt.le) h.2⟩
    · exact ⟨Or.inr hgt, fun h => (not_lt_of_ge hgt.le) h.1⟩

/-- The directed graphs obtained from `T` by deleting `u` and `v` are isomorphic. -/
def VertexDeletedIsomorphic {V : Type*} (T : Digraph V) (u v : V) : Prop :=
  Nonempty
    (RelIso
      (fun x y : {w : V // w ≠ u} => T.Adj x.1 y.1)
      (fun x y : {w : V // w ≠ v} => T.Adj x.1 y.1))

/-- The neighborhood of a vertex in a directed graph consists of its in-neighbors
and out-neighbors. -/
def Neighborhood {V : Type*} (T : Digraph V) (v : V) : V → Prop :=
  fun x => T.Adj v x ∨ T.Adj x v

/-- The link of `v` is the directed subgraph induced by the neighborhood of `v`. -/
def Link {V : Type*} (T : Digraph V) (v : V) : Digraph {x : V // Neighborhood T v x} :=
  ⟨fun x y => T.Adj x.1 y.1⟩

/-- A directed graph is link-irregular when distinct vertices have nonisomorphic
links. -/
def IsLinkIrregular {V : Type*} (T : Digraph V) : Prop :=
  ∀ (u v : V), u ≠ v →
    ¬ Nonempty (RelIso (Link T u).Adj (Link T v).Adj)

/-- The probability of an event in a uniformly distributed nonempty finite sample
space. -/
noncomputable def uniformProbability {S : Type*} [Fintype S] [Nonempty S]
    (E : S → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter E).card : ℝ) / Fintype.card S

/-- A specified bijection is an isomorphism from `T - u` to `T - v`. This is the
event denoted `Bφ` in the informal proof. -/
def deletionIsoViaEvent {V : Type*} (T : Digraph V) (u v : V)
    (φ : {x : V // x ≠ u} ≃ {x : V // x ≠ v}) : Prop :=
  ∀ x y, T.Adj x.1 y.1 ↔ T.Adj (φ x).1 (φ y).1

/-- Extend a bijection `V \ {u} ≃ V \ {v}` to a permutation of `V` by sending
`u` to `v`. -/
def extendDeletedEquiv {V : Type*} [DecidableEq V] (u v : V)
    (φ : {x : V // x ≠ u} ≃ {x : V // x ≠ v}) : Equiv.Perm V where
  toFun x := if hx : x = u then v else (φ ⟨x, hx⟩).1
  invFun y := if hy : y = v then u else (φ.symm ⟨y, hy⟩).1
  left_inv x := by
    by_cases hx : x = u
    · subst x
      simp
    · have hφ : (φ ⟨x, hx⟩).1 ≠ v := (φ ⟨x, hx⟩).2
      simp [hx, hφ]
  right_inv y := by
    by_cases hy : y = v
    · subst y
      simp
    · have hφ : (φ.symm ⟨y, hy⟩).1 ≠ u := (φ.symm ⟨y, hy⟩).2
      simp [hy, hφ]

/-- Two vertices lie in the same cycle of a permutation when an integral power sends
one to the other. -/
def InPermutationOrbit {V : Type*} (p : Equiv.Perm V) (u x : V) : Prop :=
  ∃ z : ℤ, (p ^ z) u = x

/-- The vertices in directed cycles of the partial functional graph of `φ`. The
extension `u ↦ v` has one extra cycle, containing the path from `v` to `u`; removing
that cycle leaves exactly `Cφ` from the informal proof. -/
abbrev CycleVertices {V : Type*} [DecidableEq V] (u v : V)
    (φ : {x : V // x ≠ u} ≃ {x : V // x ≠ v}) :=
  {x : V // ¬ InPermutationOrbit (extendDeletedEquiv u v φ) u x}

/-- The permutation `σφ : Cφ ≃ Cφ` induced by `φ` on its directed-cycle
vertices. -/
noncomputable def cyclePermutation {V : Type*} [DecidableEq V] (u v : V)
    (φ : {x : V // x ≠ u} ≃ {x : V // x ≠ v}) :
    Equiv.Perm (CycleVertices u v φ) :=
  let p := extendDeletedEquiv u v φ
  p.subtypeEquiv fun x => not_congr <| by
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨z + 1, ?_⟩
      calc
        (p ^ (z + 1)) u = (p ^ z) (p u) := by rw [zpow_add_one, Equiv.Perm.mul_apply]
        _ = p ((p ^ z) u) := p.zpow_apply_comm z 1
        _ = p x := congrArg p hz
    · rintro ⟨z, hz⟩
      refine ⟨z - 1, ?_⟩
      calc
        (p ^ (z - 1)) u = (p ^ z) (p.symm u) := by
          rw [zpow_sub_one, Equiv.Perm.mul_apply, Equiv.Perm.inv_def]
        _ = p.symm ((p ^ z) u) := by
          simpa using p.zpow_apply_comm z (-1) (x := u)
        _ = p.symm (p x) := congrArg p.symm hz
        _ = x := by simp

/-- The probability that `Tₙ - u` and `Tₙ - v` are isomorphic. -/
noncomputable def deletionIsoProbability (n : ℕ) (u v : Fin n) : ℝ :=
  uniformProbability fun T : Tournament n => VertexDeletedIsomorphic T.1 u v

/-- The probability of the event `Bφ`. -/
noncomputable def deletionIsoViaProbability (n : ℕ) (u v : Fin n)
    (φ : {x : Fin n // x ≠ u} ≃ {x : Fin n // x ≠ v}) : ℝ :=
  uniformProbability fun T : Tournament n => deletionIsoViaEvent T.1 u v φ

/-- The probability that a uniformly random labeled tournament on `n` vertices is
link-irregular. -/
noncomputable def linkIrregularTournamentProbability (n : ℕ) : ℝ :=
  uniformProbability fun T : Tournament n => IsLinkIrregular T.1

/-- Relabel a simple graph by a permutation of its vertices. -/
def relabelSimpleGraph {V : Type*} (σ : Equiv.Perm V) (G : SimpleGraph V) :
    SimpleGraph V :=
  G.comap σ.symm

instance simpleGraphPermSMul (V : Type*) : SMul (Equiv.Perm V) (SimpleGraph V) :=
  ⟨relabelSimpleGraph⟩

/-- Vertex permutations act on labeled simple graphs by relabeling. -/
instance simpleGraphPermMulAction (V : Type*) : MulAction (Equiv.Perm V) (SimpleGraph V) where
  one_smul G := by
    ext x y
    rfl
  mul_smul σ τ G := by
    ext x y
    rfl

/-- Isomorphism of simple graphs on a fixed labeled vertex type, expressed as the
orbit relation for vertex relabeling. -/
def simpleGraphIsoSetoid (V : Type*) : Setoid (SimpleGraph V) :=
  MulAction.orbitRel (Equiv.Perm V) (SimpleGraph V)

/-- An unlabeled simple graph with `n` vertices. -/
abbrev UnlabeledGraph (n : ℕ) := Quotient (simpleGraphIsoSetoid (Fin n))

/-- `g n` is the number of simple undirected graphs with `n` unlabeled vertices. -/
noncomputable def g (n : ℕ) : ℕ := Nat.card (UnlabeledGraph n)

/-- The two-element subsets of `V`. -/
abbrev TwoSubset (V : Type*) := {s : Finset V // s.card = 2}

/-- The smaller vertex of a two-element subset of `Fin n`. -/
def twoSubsetMin {n : ℕ} (s : TwoSubset (Fin n)) : Fin n :=
  s.1.min' (Finset.card_pos.mp (by omega))

/-- The larger vertex of a two-element subset of `Fin n`. -/
def twoSubsetMax {n : ℕ} (s : TwoSubset (Fin n)) : Fin n :=
  s.1.max' (Finset.card_pos.mp (by omega))

/-- Encode a labeled tournament by the unordered pairs whose increasing orientation
is present. -/
def tournamentPairSet {n : ℕ} (T : Tournament n) : Set (TwoSubset (Fin n)) :=
  {s | T.1.Adj (twoSubsetMin s) (twoSubsetMax s)}

/-- Construct the tournament whose increasing orientation on `{x,y}` is selected
exactly when `{x,y}` belongs to `A`. -/
noncomputable def pairSetTournament {n : ℕ} (A : Set (TwoSubset (Fin n))) : Tournament n := by
  classical
  let D : Digraph (Fin n) := ⟨fun x y => ∃ hxy : x ≠ y,
    if x < y then
      (⟨{x, y}, Finset.card_pair hxy⟩ : TwoSubset (Fin n)) ∈ A
    else
      (⟨{x, y}, Finset.card_pair hxy⟩ : TwoSubset (Fin n)) ∉ A⟩
  refine ⟨D, ?_⟩
  have hD (x y : Fin n) (hxy : x ≠ y) :
      D.Adj x y ↔
        if x < y then
          (⟨{x, y}, Finset.card_pair hxy⟩ : TwoSubset (Fin n)) ∈ A
        else
          (⟨{x, y}, Finset.card_pair hxy⟩ : TwoSubset (Fin n)) ∉ A := by
    simp [D, hxy]
  constructor
  · intro x
    simp [D]
  · intro x y hxy
    rcases lt_or_gt_of_ne hxy with hlt | hgt
    · rw [hD x y hxy, hD y x (Ne.symm hxy)]
      have hpair :
          (⟨{y, x}, Finset.card_pair (Ne.symm hxy)⟩ : TwoSubset (Fin n)) =
            ⟨{x, y}, Finset.card_pair hxy⟩ := by
        apply Subtype.ext
        simp [Finset.pair_comm]
      by_cases hA : (⟨{x, y}, Finset.card_pair hxy⟩ : TwoSubset (Fin n)) ∈ A <;>
        simp [hlt, not_lt_of_ge hlt.le, hpair, hA]
    · rw [hD x y hxy, hD y x (Ne.symm hxy)]
      have hpair :
          (⟨{y, x}, Finset.card_pair (Ne.symm hxy)⟩ : TwoSubset (Fin n)) =
            ⟨{x, y}, Finset.card_pair hxy⟩ := by
        apply Subtype.ext
        simp [Finset.pair_comm]
      by_cases hA : (⟨{x, y}, Finset.card_pair hxy⟩ : TwoSubset (Fin n)) ∈ A <;>
        simp [hgt, not_lt_of_ge hgt.le, hpair, hA]

/-- Labeled tournaments on `Fin n` are exactly choices of an orientation for each
two-element subset. -/
noncomputable def tournamentPairSetEquiv (n : ℕ) :
    Tournament n ≃ Set (TwoSubset (Fin n)) where
  toFun := tournamentPairSet
  invFun := pairSetTournament
  left_inv T := by
    apply Subtype.ext
    ext x y
    by_cases hxy : x = y
    · subst y
      constructor
      · exact fun h => ((pairSetTournament _).2.1 x h).elim
      · exact fun h => (T.2.1 x h).elim
    · rcases lt_or_gt_of_ne hxy with hlt | hgt
      · simp [pairSetTournament, tournamentPairSet, twoSubsetMin, twoSubsetMax,
          hxy, hlt, min_eq_right hlt.le, max_eq_left hlt.le, Finset.pair_comm]
      · have hTournament := T.2.2 x y hxy
        have hiff : ¬ T.1.Adj y x ↔ T.1.Adj x y := by
          rcases hTournament.1 with h | h
          · exact ⟨fun _ => h, fun hnot hrev => hTournament.2 ⟨hnot, hrev⟩⟩
          · exact ⟨fun hn => (hn h).elim, fun hxy' hrev => hTournament.2 ⟨hxy', hrev⟩⟩
        simpa [pairSetTournament, tournamentPairSet, twoSubsetMin, twoSubsetMax,
          hxy, Ne.symm hxy, hgt, not_lt_of_ge hgt.le,
          min_eq_right hgt.le, max_eq_left hgt.le,
          min_eq_left hgt.le, max_eq_right hgt.le, Finset.pair_comm] using hiff
  right_inv A := by
    ext ⟨s, hs_card⟩
    rcases Finset.card_eq_two.mp hs_card with ⟨x, y, hxy, hs⟩
    subst s
    rcases lt_or_gt_of_ne hxy with hlt | hgt
    · simp [pairSetTournament, tournamentPairSet, twoSubsetMin, twoSubsetMax,
        hxy, hlt, min_eq_right hlt.le, max_eq_left hlt.le, Finset.pair_comm]
    · simp [pairSetTournament, tournamentPairSet, twoSubsetMin, twoSubsetMax,
        Ne.symm hxy, hgt, min_eq_left hgt.le, max_eq_right hgt.le, Finset.pair_comm]

/-- The set of unordered vertex pairs which are edges of a simple graph. -/
def graphTwoSubsetSet {n : ℕ} (G : SimpleGraph (Fin n)) : Set (TwoSubset (Fin n)) :=
  {s | G.Adj (twoSubsetMin s) (twoSubsetMax s)}

/-- The simple graph having exactly the prescribed two-element subsets as edges. -/
def twoSubsetSetGraph {n : ℕ} (A : Set (TwoSubset (Fin n))) : SimpleGraph (Fin n) where
  Adj x y := ∃ hxy : x ≠ y,
    (⟨{x, y}, Finset.card_pair hxy⟩ : TwoSubset (Fin n)) ∈ A
  symm := by
    rintro x y ⟨hxy, hA⟩
    refine ⟨Ne.symm hxy, ?_⟩
    simpa [Finset.pair_comm] using hA
  loopless := by
    intro x hx
    exact hx.choose rfl

/-- Simple graphs on `Fin n` are the same data as sets of two-element subsets. -/
noncomputable def simpleGraphTwoSubsetEquiv (n : ℕ) :
    SimpleGraph (Fin n) ≃ Set (TwoSubset (Fin n)) where
  toFun := graphTwoSubsetSet
  invFun := twoSubsetSetGraph
  left_inv G := by
    ext x y
    by_cases hxy : x = y
    · subst y
      simp [twoSubsetSetGraph]
    · rcases lt_or_gt_of_ne hxy with hlt | hgt
      · simp [twoSubsetSetGraph, graphTwoSubsetSet, twoSubsetMin, twoSubsetMax,
          hxy, hlt.le]
      · simp [twoSubsetSetGraph, graphTwoSubsetSet, twoSubsetMin, twoSubsetMax,
          hxy, hgt.le, SimpleGraph.adj_comm]
  right_inv A := by
    ext ⟨s, hs_card⟩
    rcases Finset.card_eq_two.mp hs_card with ⟨x, y, hxy, hs⟩
    subst s
    rcases lt_or_gt_of_ne hxy with hlt | hgt
    · simp [graphTwoSubsetSet, twoSubsetSetGraph, twoSubsetMin, twoSubsetMax,
        hxy, hlt.le]
    · simp [graphTwoSubsetSet, twoSubsetSetGraph, twoSubsetMin, twoSubsetMax,
        Ne.symm hxy, hgt.le, Finset.pair_comm]

/-- Vertex permutations act functorially on two-element subsets. -/
noncomputable def permuteTwoSubsetsHom {V : Type*} [DecidableEq V] :
    Equiv.Perm V →* Equiv.Perm (TwoSubset V) where
  toFun σ := σ.finsetCongr.subtypeEquiv fun s => by simp
  map_one' := by
    ext s x
    simp
  map_mul' σ τ := by
    ext s x
    simp
    rfl

/-- The permutation induced by `σ` on the two-element subsets. -/
noncomputable def permuteTwoSubsets {V : Type*} [DecidableEq V]
    (σ : Equiv.Perm V) : Equiv.Perm (TwoSubset V) :=
  permuteTwoSubsetsHom σ

/-- Two two-element subsets are equivalent when an integral power of `σ` sends one to
the other. -/
noncomputable def pairOrbitSetoid {V : Type*} [DecidableEq V]
    (σ : Equiv.Perm V) : Setoid (TwoSubset V) where
  r A B := ∃ z : ℤ, ((permuteTwoSubsets σ) ^ z) A = B
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro A
      exact ⟨0, by simp⟩
    · rintro A B ⟨z, hz⟩
      refine ⟨-z, ?_⟩
      rw [← hz]
      simp
    · rintro A B C ⟨z, hz⟩ ⟨w, hw⟩
      refine ⟨w + z, ?_⟩
      rw [zpow_add, Equiv.Perm.mul_apply, hz, hw]

/-- `o₂(σ)`, the number of orbits of the cyclic group generated by `σ` on the
two-element subsets. -/
noncomputable def pairOrbitCount {V : Type*} [Fintype V] [DecidableEq V]
    (σ : Equiv.Perm V) : ℕ :=
  Nat.card (Quotient (pairOrbitSetoid σ))

/-- The quantity `o₂(σφ)` from Lemma 2. -/
noncomputable def cyclePairOrbitCount (n : ℕ) (u v : Fin n)
    (φ : {x : Fin n // x ≠ u} ≃ {x : Fin n // x ≠ v}) : ℕ := by
  classical
  letI : Fintype (CycleVertices u v φ) := Fintype.ofFinite _
  exact pairOrbitCount (cyclePermutation u v φ)

/-- The directed edges left from a permutation after deleting the outgoing edges
at the vertices satisfying `cut`. -/
def partialPermutationEdge {α : Type*} (q : Equiv.Perm α) (cut : α → Prop)
    (x y : α) : Prop :=
  ¬ cut x ∧ q x = y

/-- Components of the partial functional digraph obtained by cutting a permutation. -/
def partialPermutationSetoid {α : Type*} (q : Equiv.Perm α) (cut : α → Prop) :
    Setoid α :=
  Relation.EqvGen.setoid (partialPermutationEdge q cut)

/-- Unordered pairs containing a prescribed vertex. These are precisely the cut
vertices in the functional digraph used in Lemma 2. -/
abbrev PairsContaining {V : Type*} (u : V) :=
  {s : TwoSubset V // u ∈ s.1}

/-- The evident bijection between the other `n - 1` vertices and the unordered
pairs containing `u`. -/
noncomputable def otherVertexPairEquiv {n : ℕ} (u : Fin n) :
    {x : Fin n // x ≠ u} ≃ PairsContaining u := by
  classical
  let other (s : PairsContaining u) : Fin n :=
    (s.1.1.erase u).min' (by
      rw [Finset.nonempty_iff_ne_empty]
      intro he
      have hcard := Finset.card_erase_of_mem s.2
      rw [s.1.2, he] at hcard
      simp at hcard)
  have hother_mem (s : PairsContaining u) : other s ∈ s.1.1.erase u :=
    Finset.min'_mem _ _
  refine
    { toFun := fun x =>
        ⟨⟨{u, x.1}, Finset.card_pair (Ne.symm x.2)⟩, by simp⟩
      invFun := fun s => ⟨other s, by
        exact (Finset.mem_erase.mp (hother_mem s)).1⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    apply Subtype.ext
    have hm := hother_mem
      (⟨⟨{u, x.1}, Finset.card_pair (Ne.symm x.2)⟩, by simp⟩ : PairsContaining u)
    have hm' := Finset.mem_erase.mp hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm'
    rcases hm'.2 with hbad | hgood
    · exact (hm'.1 hbad).elim
    · exact hgood
  · intro s
    apply Subtype.ext
    apply Subtype.ext
    ext y
    constructor
    · intro hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact s.2
      · exact (Finset.mem_erase.mp (hother_mem s)).2
    · intro hy
      by_cases hyu : y = u
      · simp [hyu]
      · have hyErase : y ∈ s.1.1.erase u := Finset.mem_erase.mpr ⟨hyu, hy⟩
        have hcard : (s.1.1.erase u).card = 1 := by
          simpa [s.1.2] using Finset.card_erase_of_mem s.2
        change y ∈ ({u, other s} : Finset (Fin n))
        simp only [Finset.mem_insert, Finset.mem_singleton]
        right
        have hle : (s.1.1.erase u).card ≤ 1 := hcard.le
        exact Finset.card_le_one.mp hle y hyErase (other s) (hother_mem s)


end BastienKhormali
