import Proof.Definitions

/-!
# Results proof 3

The tournament-specific characterization of link irregularity stated in the
introduction. It is proved here rather than used as a definition.
-/

namespace BastienKhormali

/-- For a tournament, the neighborhood of a vertex is exactly the set of all other
vertices. -/
theorem claim10_neighborhood_iff_ne {V : Type*} (T : Digraph V) (hT : IsTournament T)
    (v x : V) :
    Neighborhood T v x ↔ x ≠ v := by
  constructor
  · rintro (h | h) hEq
    · subst x
      exact hT.1 _ h
    · subst x
      exact hT.1 _ h
  · intro hx
    exact (hT.2 v x (Ne.symm hx)).1

/-- The links of two vertices in a tournament are isomorphic if and only if the
corresponding vertex-deleted tournaments are isomorphic. -/
theorem claim10_links_iso_iff_deleted_iso {V : Type*} (T : Digraph V)
    (hT : IsTournament T) (u v : V) :
    Nonempty (RelIso (Link T u).Adj (Link T v).Adj) ↔
      VertexDeletedIsomorphic T u v := by
  let eu : RelIso (Link T u).Adj
      (fun x y : {w : V // w ≠ u} => T.Adj x.1 y.1) :=
    { toEquiv :=
        { toFun := fun x => ⟨x.1, (claim10_neighborhood_iff_ne T hT u x.1).mp x.2⟩
          invFun := fun x => ⟨x.1, (claim10_neighborhood_iff_ne T hT u x.1).mpr x.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      map_rel_iff' := Iff.rfl }
  let ev : RelIso (Link T v).Adj
      (fun x y : {w : V // w ≠ v} => T.Adj x.1 y.1) :=
    { toEquiv :=
        { toFun := fun x => ⟨x.1, (claim10_neighborhood_iff_ne T hT v x.1).mp x.2⟩
          invFun := fun x => ⟨x.1, (claim10_neighborhood_iff_ne T hT v x.1).mpr x.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      map_rel_iff' := Iff.rfl }
  constructor
  · rintro ⟨e⟩
    exact ⟨eu.symm.trans (e.trans ev)⟩
  · rintro ⟨e⟩
    exact ⟨eu.trans (e.trans ev.symm)⟩

/-- The characterization asserted in the introduction: a tournament is
link-irregular exactly when all distinct vertex-deleted subtournaments are
nonisomorphic. -/
theorem claim10_tournament_linkIrregular_iff {V : Type*} (T : Digraph V)
    (hT : IsTournament T) :
    IsLinkIrregular T ↔
      ∀ (u v : V), u ≠ v → ¬ VertexDeletedIsomorphic T u v := by
  unfold IsLinkIrregular
  constructor <;> intro h u v huv hIso
  · exact h u v huv ((claim10_links_iso_iff_deleted_iso T hT u v).mpr hIso)
  · exact h u v huv ((claim10_links_iso_iff_deleted_iso T hT u v).mp hIso)

end BastienKhormali
