import Proof.Theorem3Proof2

/-!
# Theorem 3 proof 3

The decomposition and enumeration of deleted-vertex bijections used in Theorem 3.
-/

open scoped BigOperators

noncomputable section

namespace BastienKhormali

private theorem pairOrbitCount_congr {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (σ : Equiv.Perm α) :
    pairOrbitCount (e.permCongr σ) = pairOrbitCount σ := by
  let ep : TwoSubset α ≃ TwoSubset β :=
    e.finsetCongr.subtypeEquiv fun s => by simp
  have hstep (s : TwoSubset α) :
      ep (permuteTwoSubsets σ s) =
        permuteTwoSubsets (e.permCongr σ) (ep s) := by
    have hinv : (e.permCongr σ).symm = e.permCongr σ.symm := by
      exact (map_inv e.permCongrHom σ).symm
    apply Subtype.ext
    ext x
    simp [ep, permuteTwoSubsets, permuteTwoSubsetsHom, hinv]
  have hz (z : ℤ) (s : TwoSubset α) :
      ep (((permuteTwoSubsets σ) ^ z) s) =
        ((permuteTwoSubsets (e.permCongr σ)) ^ z) (ep s) := by
    have hsem : Function.Semiconj ep (permuteTwoSubsets σ)
        (permuteTwoSubsets (e.permCongr σ)) := hstep
    have hsem_inv : Function.Semiconj ep (permuteTwoSubsets σ).symm
        (permuteTwoSubsets (e.permCongr σ)).symm := by
      intro s
      apply (permuteTwoSubsets (e.permCongr σ)).injective
      rw [(permuteTwoSubsets (e.permCongr σ)).apply_symm_apply]
      rw [← hstep]
      simp
    cases z with
    | ofNat k =>
        simpa [Equiv.Perm.iterate_eq_pow] using hsem.iterate_right k s
    | negSucc k =>
        simpa [Equiv.Perm.iterate_eq_pow, zpow_negSucc] using
          hsem_inv.iterate_right (k + 1) s
  let eqv : Quotient (pairOrbitSetoid σ) ≃
      Quotient (pairOrbitSetoid (e.permCongr σ)) :=
    Quotient.congr ep fun A B => by
      constructor
      · rintro ⟨z, hzAB⟩
        refine ⟨z, ?_⟩
        rw [← hz]
        exact congrArg ep hzAB
      · rintro ⟨z, hzAB⟩
        refine ⟨z, ep.injective ?_⟩
        rw [hz]
        exact hzAB
  exact (Nat.card_congr eqv).symm


private theorem constructed_toList {V : Type*} [Fintype V] [DecidableEq V]
    (u v : V) (_huv : u ≠ v) (r : List V) (hr : (u :: v :: r).Nodup)
    (σ : Equiv.Perm {x : V // x ∉ u :: v :: r}) :
    (List.formPerm (u :: v :: r) * Equiv.Perm.ofSubtype σ).toList u = u :: v :: r := by
  let l := u :: v :: r
  let c := List.formPerm l
  let q := Equiv.Perm.ofSubtype σ
  have hl : l.Nodup := hr
  have hlen : 2 ≤ l.length := by simp [l]
  have hqu : q u = u := by
    apply Equiv.Perm.ofSubtype_apply_of_not_mem
    simp
  have hd : Equiv.Perm.Disjoint c q := by
    intro x
    by_cases hx : x ∈ l
    · right
      apply Equiv.Perm.ofSubtype_apply_of_not_mem
      exact not_not_intro hx
    · left
      exact List.formPerm_apply_of_notMem hx
  have hcu : c.cycleOf u = c := by
    exact (List.isCycle_formPerm hl hlen).cycleOf_eq
      ((List.formPerm_apply_mem_ne_self_iff l hl u (by simp [l])).mpr hlen)
  have hcycle : (c * q).cycleOf u = c := by
    rw [Equiv.Perm.cycleOf_mul_of_apply_right_eq_self hd.commute u hqu, hcu]
  have hiter (i : ℕ) : ((c * q) ^ i) u = (c ^ i) u := by
    rw [hd.commute.mul_pow, Equiv.Perm.mul_apply]
    rw [Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hqu]
  have htolist : c.toList u = l := by
    simpa [c, l] using
      Equiv.Perm.toList_formPerm_nontrivial l hlen hl
  change (c * q).toList u = l
  rw [← htolist]
  simp only [Equiv.Perm.toList, hcycle, hcu]
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    simp only [List.getElem_iterate, Equiv.Perm.iterate_eq_pow]
    exact hiter i

where
  deletedPermEquiv (u v : V) :
      ({x : V // x ≠ u} ≃ {x : V // x ≠ v}) ≃
        {p : Equiv.Perm V // p u = v} := {
    toFun φ := ⟨extendDeletedEquiv u v φ, by simp [extendDeletedEquiv]⟩
    invFun p := p.1.subtypeEquiv fun x => by
      constructor
      · intro hx hpx
        exact hx (p.1.injective (hpx.trans p.2.symm))
      · intro hpx hx
        subst x
        exact hpx p.2
    left_inv φ := by
      ext x
      simp [extendDeletedEquiv, x.2]
    right_inv p := by
      apply Subtype.ext
      ext x
      by_cases hx : x = u
      · subst x
        simp [extendDeletedEquiv, p.2]
      · simp [extendDeletedEquiv, hx]
    }

  permPathEquiv (u v : V) (huv : u ≠ v) :
      {p : Equiv.Perm V // p u = v} ≃
        Σ r : List V, PLift (u :: v :: r).Nodup ×
          Equiv.Perm {x : V // x ∉ u :: v :: r} := by
    classical
    let toPath (p : {p : Equiv.Perm V // p u = v}) : List V :=
      (p.1.toList u).drop 2
    have toPathNodup (p : {p : Equiv.Perm V // p u = v}) :
        (u :: v :: toPath p).Nodup := by
      let l := p.1.toList u
      have hu : u ∈ p.1.support := by
        simp only [Equiv.Perm.mem_support]
        exact p.2.trans_ne (Ne.symm huv)
      have hlen : 2 ≤ l.length :=
        Equiv.Perm.two_le_length_toList_iff_mem_support.mpr hu
      have hzero : l[0] = u := by
        simpa [l] using Equiv.Perm.getElem_toList p.1 u 0
          (by change 0 < l.length; omega)
      have hone : l[1] = v := by
        simpa [l, p.2] using Equiv.Perm.getElem_toList p.1 u 1
          (by change 1 < l.length; omega)
      have htake : l.take 2 = [u, v] := by
        apply List.ext_getElem
        · simp [Nat.min_eq_left hlen]
        · intro i hi₁ hi₂
          simp at hi₂
          interval_cases i
          · simpa using hzero
          · simpa using hone
      have hshape : l = u :: v :: l.drop 2 := by
        calc
          l = l.take 2 ++ l.drop 2 := (List.take_append_drop 2 l).symm
          _ = u :: v :: l.drop 2 := by rw [htake]; rfl
      change (u :: v :: l.drop 2).Nodup
      rw [← hshape]
      exact Equiv.Perm.nodup_toList p.1 u
    let toCyclePerm (p : {p : Equiv.Perm V // p u = v}) :
        Equiv.Perm {x : V // x ∉ u :: v :: toPath p} := by
      let l := p.1.toList u
      have hu : u ∈ p.1.support := by
        simp only [Equiv.Perm.mem_support]
        exact p.2.trans_ne (Ne.symm huv)
      have hlen : 2 ≤ l.length :=
        Equiv.Perm.two_le_length_toList_iff_mem_support.mpr hu
      have hzero : l[0] = u := by
        simpa [l] using Equiv.Perm.getElem_toList p.1 u 0
          (by change 0 < l.length; omega)
      have hone : l[1] = v := by
        simpa [l, p.2] using Equiv.Perm.getElem_toList p.1 u 1
          (by change 1 < l.length; omega)
      have htake : l.take 2 = [u, v] := by
        apply List.ext_getElem
        · simp [Nat.min_eq_left hlen]
        · intro i hi₁ hi₂
          simp at hi₂
          interval_cases i
          · simpa using hzero
          · simpa using hone
      have hshape : l = u :: v :: l.drop 2 := by
        calc
          l = l.take 2 ++ l.drop 2 := (List.take_append_drop 2 l).symm
          _ = u :: v :: l.drop 2 := by rw [htake]; rfl
      apply p.1.subtypeEquiv
      intro x
      dsimp only [toPath]
      change (x ∉ u :: v :: l.drop 2) ↔ (p.1 x ∉ u :: v :: l.drop 2)
      conv_lhs => rw [← hshape]
      conv_rhs => rw [← hshape]
      apply not_congr
      change (x ∈ p.1.toList u) ↔ (p.1 x ∈ p.1.toList u)
      simp only [Equiv.Perm.mem_toList_iff, Equiv.Perm.sameCycle_apply_right]
    refine
      { toFun := fun p => ⟨toPath p, ⟨toPathNodup p⟩, toCyclePerm p⟩
        invFun := fun d =>
          ⟨List.formPerm (u :: v :: d.1) * Equiv.Perm.ofSubtype d.2.2, by
            simp only [Equiv.Perm.mul_apply]
            rw [Equiv.Perm.ofSubtype_apply_of_not_mem]
            · simpa using List.formPerm_apply_getElem (u :: v :: d.1) d.2.1.down 0 (by simp)
            · simp⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro p
      apply Subtype.ext
      ext x
      let l := p.1.toList u
      have hshape : l = u :: v :: l.drop 2 := by
        have hu : u ∈ p.1.support := by
          simp only [Equiv.Perm.mem_support]
          exact p.2.trans_ne (Ne.symm huv)
        have hlen : 2 ≤ l.length :=
          Equiv.Perm.two_le_length_toList_iff_mem_support.mpr hu
        have hzero : l[0] = u := by
          simpa [l] using Equiv.Perm.getElem_toList p.1 u 0
            (by change 0 < l.length; omega)
        have hone : l[1] = v := by
          simpa [l, p.2] using Equiv.Perm.getElem_toList p.1 u 1
            (by change 1 < l.length; omega)
        have htake : l.take 2 = [u, v] := by
          apply List.ext_getElem
          · simp [Nat.min_eq_left hlen]
          · intro i hi₁ hi₂
            simp at hi₂
            interval_cases i
            · simpa using hzero
            · simpa using hone
        calc
          l = l.take 2 ++ l.drop 2 := (List.take_append_drop 2 l).symm
          _ = u :: v :: l.drop 2 := by rw [htake]; rfl
      change (List.formPerm (u :: v :: toPath p) *
        Equiv.Perm.ofSubtype (toCyclePerm p)) x = p.1 x
      dsimp only [toPath]
      have hc : List.formPerm (u :: v :: l.drop 2) = p.1.cycleOf u := by
        rw [← hshape, Equiv.Perm.formPerm_toList]
      have htcp (y : {x : V // x ∉ u :: v :: toPath p}) :
          (toCyclePerm p y).1 = p.1 y.1 := by
        dsimp only [toCyclePerm]
        rfl
      by_cases hx : x ∈ l
      · rw [Equiv.Perm.mul_apply, Equiv.Perm.ofSubtype_apply_of_not_mem]
        · rw [hc]
          apply Equiv.Perm.SameCycle.cycleOf_apply
          exact (Equiv.Perm.mem_toList_iff.mp hx).1
        · change ¬x ∉ u :: v :: l.drop 2
          rw [← hshape]
          exact not_not_intro hx
      · have hxcomp : x ∉ u :: v :: toPath p := by
          dsimp only [toPath]
          change x ∉ u :: v :: l.drop 2
          rwa [← hshape]
        rw [Equiv.Perm.mul_apply,
          Equiv.Perm.ofSubtype_apply_of_mem (toCyclePerm p) hxcomp]
        rw [List.formPerm_apply_of_notMem (toCyclePerm p ⟨x, hxcomp⟩).2]
        exact htcp ⟨x, hxcomp⟩
    · have right_aux (p : {p : Equiv.Perm V // p u = v})
          (r : List V) (hr : (u :: v :: r).Nodup)
          (σ : Equiv.Perm {x : V // x ∉ u :: v :: r})
          (hp : p.1 = List.formPerm (u :: v :: r) * Equiv.Perm.ofSubtype σ)
          (hpath : toPath p = r) :
          (⟨toPath p, ⟨toPathNodup p⟩, toCyclePerm p⟩ :
            Σ r : List V, PLift (u :: v :: r).Nodup ×
              Equiv.Perm {x : V // x ∉ u :: v :: r}) = ⟨r, ⟨hr⟩, σ⟩ := by
        apply Sigma.ext hpath
        cases hpath
        apply heq_of_eq
        have hsigma : toCyclePerm p = σ := by
          apply Equiv.ext
          intro x
          apply Subtype.ext
          have htcp : (toCyclePerm p x).1 = p.1 x.1 := by
            dsimp only [toCyclePerm]
            rfl
          rw [htcp, hp, Equiv.Perm.mul_apply,
            Equiv.Perm.ofSubtype_apply_of_mem σ x.2]
          rw [List.formPerm_apply_of_notMem (σ x).2]
        apply Prod.ext
        · exact Subsingleton.elim _ _
        · exact hsigma
      rintro ⟨r, ⟨hr⟩, σ⟩
      let p : {p : Equiv.Perm V // p u = v} :=
        ⟨List.formPerm (u :: v :: r) * Equiv.Perm.ofSubtype σ, by
          simp only [Equiv.Perm.mul_apply]
          rw [Equiv.Perm.ofSubtype_apply_of_not_mem]
          · simpa using List.formPerm_apply_getElem (u :: v :: r) hr 0 (by simp)
          · simp⟩
      have hrEq : toPath p = r := by
        change (p.1.toList u).drop 2 = r
        have htl : p.1.toList u = u :: v :: r := by
          change (List.formPerm (u :: v :: r) * Equiv.Perm.ofSubtype σ).toList u =
            u :: v :: r
          exact constructed_toList u v huv r hr σ
        rw [htl]
        simp
      exact right_aux p r hr σ rfl hrEq

private theorem cycle_weight (n : ℕ) (u v : Fin n) (huv : u ≠ v)
    (φ : {x : Fin n // x ≠ u} ≃ {x : Fin n // x ≠ v}) :
    cyclePairOrbitCount n u v φ =
      pairOrbitCount
        ((constructed_toList.permPathEquiv u v huv (constructed_toList.deletedPermEquiv u v φ)).2.2) := by
  classical
  let p := extendDeletedEquiv u v φ
  have hp : p u = v := by simp [p, extendDeletedEquiv]
  have hu : u ∈ p.support := by
    simp only [Equiv.Perm.mem_support]
    exact hp.trans_ne (Ne.symm huv)
  let data := constructed_toList.permPathEquiv u v huv (constructed_toList.deletedPermEquiv u v φ)
  have hlist : u :: v :: data.1 = p.toList u := by
    let l := p.toList u
    have hlen : 2 ≤ l.length :=
      Equiv.Perm.two_le_length_toList_iff_mem_support.mpr hu
    have hzero : l[0] = u := by
      simpa [l] using Equiv.Perm.getElem_toList p u 0
        (by change 0 < l.length; omega)
    have hone : l[1] = v := by
      simpa [l, hp] using Equiv.Perm.getElem_toList p u 1
        (by change 1 < l.length; omega)
    have htake : l.take 2 = [u, v] := by
      apply List.ext_getElem
      · simp [Nat.min_eq_left hlen]
      · intro i hi₁ hi₂
        simp at hi₂
        interval_cases i
        · simpa using hzero
        · simpa using hone
    have hshape : l = u :: v :: l.drop 2 := by
      calc
        l = l.take 2 ++ l.drop 2 := (List.take_append_drop 2 l).symm
        _ = u :: v :: l.drop 2 := by rw [htake]; rfl
    change u :: v :: (p.toList u).drop 2 = p.toList u
    exact hshape.symm
  let e : CycleVertices u v φ ≃
      {x : Fin n // x ∉ u :: v :: data.1} :=
    (Equiv.refl (Fin n)).subtypeEquiv fun x => by
      change (¬InPermutationOrbit p u x) ↔ x ∉ u :: v :: data.1
      rw [hlist]
      rw [not_iff_not]
      rw [Equiv.Perm.mem_toList_iff]
      simp only [InPermutationOrbit, Equiv.Perm.SameCycle]
      simp [hu]
  let σ := data.2.2
  have hsigma (x : {x : Fin n // x ∉ u :: v :: data.1}) : (σ x).1 = p x.1 := by
    dsimp [σ, constructed_toList.permPathEquiv,
      constructed_toList.deletedPermEquiv, p]
    rfl
  have hperm : e.permCongr (cyclePermutation u v φ) = σ := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change (cyclePermutation u v φ (e.symm x)).1 = (σ x).1
    rw [hsigma]
    rfl
  change pairOrbitCount (cyclePermutation u v φ) = pairOrbitCount σ
  rw [← hperm, pairOrbitCount_congr]

where
  pathFintype (u v : Fin n) : Fintype {r : List (Fin n) // (u :: v :: r).Nodup} :=
    Fintype.ofInjective
        (fun r => (⟨r.1, r.2.tail.tail⟩ : {l : List (Fin n) // l.Nodup}))
      (by
        intro a b h
        apply Subtype.ext
        exact congrArg (fun z : {l : List (Fin n) // l.Nodup} => z.1) h)

  rawPathEquiv (u v : Fin n) :
      (Σ r : List (Fin n), PLift (u :: v :: r).Nodup ×
          Equiv.Perm {x : Fin n // x ∉ u :: v :: r}) ≃
        (Σ r : {r : List (Fin n) // (u :: v :: r).Nodup},
          Equiv.Perm {x : Fin n // x ∉ u :: v :: r.1}) := {
    toFun d := ⟨⟨d.1, d.2.1.down⟩, d.2.2⟩
    invFun d := ⟨d.1.1, ⟨d.1.2⟩, d.2⟩
    left_inv d := by
      rcases d with ⟨r, ⟨hr⟩, σ⟩
      rfl
    right_inv d := by
      rcases d with ⟨⟨r, hr⟩, σ⟩
      rfl
    }

private theorem card_path_length {V : Type*} [Fintype V] [DecidableEq V]
    (u v : V) (huv : u ≠ v) (m : ℕ) :
    Nat.card {r : List V // (u :: v :: r).Nodup ∧ r.length = m} =
      (Fintype.card V - 2).descFactorial m := by
  classical
  let W := {x : V // x ≠ u ∧ x ≠ v}
  let e : {r : List V // (u :: v :: r).Nodup ∧ r.length = m} ≃ (Fin m ↪ W) := by
    refine
      { toFun := fun r =>
          { toFun := fun i => ⟨r.1.get (Fin.cast r.2.2.symm i), by
                have hn := r.2.1
                have hn1 := List.nodup_cons.mp hn
                have hn2 := List.nodup_cons.mp hn1.2
                have hmem : r.1.get (Fin.cast r.2.2.symm i) ∈ r.1 :=
                  List.get_mem _ _
                have hu_not : u ∉ r.1 := fun h =>
                  hn1.1 (List.mem_cons_of_mem v h)
                have hv_not : v ∉ r.1 := hn2.1
                exact ⟨fun h => hu_not
                    (Eq.mp (congrArg (fun z : V => z ∈ r.1) h) hmem),
                  fun h => hv_not
                    (Eq.mp (congrArg (fun z : V => z ∈ r.1) h) hmem)⟩⟩
            inj' := fun a b h => by
              apply Fin.ext
              have hget : r.1.get (Fin.cast r.2.2.symm a) =
                  r.1.get (Fin.cast r.2.2.symm b) := congrArg Subtype.val h
              have hnd : r.1.Nodup := r.2.1.tail.tail
              have := hnd.get_inj_iff.mp hget
              exact congrArg Fin.val (Fin.cast_injective r.2.2.symm this) }
        invFun := fun f =>
          ⟨List.ofFn (fun i => (f i).1), by
            have hu_not : u ∉ List.ofFn (fun i => (f i).1) := by
              simp only [List.mem_ofFn]
              rintro ⟨i, hi⟩
              exact (f i).2.1 hi
            have hv_not : v ∉ List.ofFn (fun i => (f i).1) := by
              simp only [List.mem_ofFn]
              rintro ⟨i, hi⟩
              exact (f i).2.2 hi
            have hnd : (List.ofFn (fun i => (f i).1)).Nodup := by
              rw [List.nodup_ofFn]
              exact fun a b h => f.injective (Subtype.ext h)
            exact List.nodup_cons.mpr ⟨by simpa [huv] using hu_not,
              List.nodup_cons.mpr ⟨hv_not, hnd⟩⟩, by simp⟩
        left_inv := by
          intro r
          apply Subtype.ext
          apply List.ext_getElem
          · simp [r.2.2]
          · intro i hi₁ hi₂
            simp
        right_inv := by
          intro f
          apply Function.Embedding.ext
          intro i
          apply Subtype.ext
          simp }
  calc
    Nat.card {r : List V // (u :: v :: r).Nodup ∧ r.length = m} =
        Nat.card (Fin m ↪ W) := Nat.card_congr e
    _ = (Fintype.card W).descFactorial m := by
      rw [Nat.card_eq_fintype_card, Fintype.card_embedding_eq]
      simp
    _ = (Fintype.card V - 2).descFactorial m := by
      congr 2
      dsimp [W]
      have hcard : Fintype.card {x : V // x = u ∨ x = v} = 2 :=
        Fintype.card_subtype_eq_or_eq_of_ne huv
      have hcomp := Fintype.card_subtype_compl (p := fun x : V => x = u ∨ x = v)
      rw [hcard] at hcomp
      simpa [not_or] using hcomp

private theorem complement_card (n : ℕ) (u v : Fin n) (r : List (Fin n))
    (hr : (u :: v :: r).Nodup) :
    Fintype.card {x : Fin n // x ∉ u :: v :: r} = n - 2 - r.length := by
  let l := u :: v :: r
  have hmem : Fintype.card {x : Fin n // x ∈ l} = l.length := by
    rw [← Fintype.card_fin l.length]
    exact Fintype.card_congr (hr.getEquiv l).symm
  have hcomp := Fintype.card_subtype_compl (p := fun x : Fin n => x ∈ l)
  rw [hmem] at hcomp
  simp only [Fintype.card_fin] at hcomp
  change Fintype.card {x : Fin n // x ∉ l} = n - 2 - r.length
  rw [hcomp]
  simp only [l, List.length_cons]
  omega

private theorem card_path_fiber (n : ℕ) (u v : Fin n) (huv : u ≠ v)
    (k : Fin (n - 1)) :
    letI := cycle_weight.pathFintype n u v
    Fintype.card {r : {r : List (Fin n) // (u :: v :: r).Nodup} //
      Fintype.card {x : Fin n // x ∉ u :: v :: (r : List (Fin n))} = k.1} =
      (n - 2).choose k.1 * (n - k.1 - 2).factorial := by
  classical
  letI := cycle_weight.pathFintype n u v
  have huvval : u.val ≠ v.val := fun h => huv (Fin.ext h)
  have hn : 2 ≤ n := by omega
  let A := {r : {r : List (Fin n) // (u :: v :: r).Nodup} //
    Fintype.card {x : Fin n // x ∉ u :: v :: (r : List (Fin n))} = k.1}
  let B := {r : List (Fin n) // (u :: v :: r).Nodup ∧
    r.length = n - k.1 - 2}
  letI : Fintype B := Fintype.ofInjective
    (fun r => (⟨r.1, r.2.1.tail.tail⟩ : {l : List (Fin n) // l.Nodup}))
    (by
      intro a b h
      apply Subtype.ext
      exact congrArg (fun z : {l : List (Fin n) // l.Nodup} => z.1) h)
  let e : A ≃ B := by
    refine
      { toFun := fun r => ⟨r.val.val, r.val.property, ?_⟩
        invFun := fun r => ⟨⟨r.1, r.2.1⟩, ?_⟩
        left_inv := by intro r; rfl
        right_inv := by intro r; rfl }
    · have hc := complement_card n u v r.val.val r.val.property
      rw [r.2] at hc
      have hlen : r.val.val.length ≤ n - 2 := by
        have := r.val.property.length_le_card
        simp at this
        omega
      omega
    · rw [complement_card n u v r.1 r.2.1, r.2.2]
      have hk : k.1 ≤ n - 2 := by omega
      omega
  calc
    Fintype.card A = Fintype.card B := Fintype.card_congr e
    _ = Nat.card B := by rw [Nat.card_eq_fintype_card]
    _ = (n - 2).descFactorial (n - k.1 - 2) :=
      by
        change Nat.card {r : List (Fin n) // (u :: v :: r).Nodup ∧
          r.length = n - k.1 - 2} = _
        simpa using card_path_length u v huv (n - k.1 - 2)
    _ = (n - 2).choose k.1 * (n - k.1 - 2).factorial := by
      rw [Nat.descFactorial_eq_factorial_mul_choose]
      have hk : k.1 ≤ n - 2 := by omega
      have hm : n - k.1 - 2 = n - 2 - k.1 := by omega
      rw [hm]
      rw [Nat.choose_symm hk]
      ring

private theorem generic_reindex_fin (α : Type*) [Fintype α] [DecidableEq α] :
    (∑ σ : Equiv.Perm α, (2 : ℝ) ^ pairOrbitCount σ) =
      ∑ τ : Equiv.Perm (Fin (Fintype.card α)), (2 : ℝ) ^ pairOrbitCount τ := by
  let e := Fintype.equivFin α
  rw [← Equiv.sum_comp e.permCongr]
  apply Finset.sum_congr rfl
  intro σ _
  rw [pairOrbitCount_congr]

/-- Group deleted-vertex bijections by their cycle vertices and ordered path from
`v` to `u`. This is the finite reindexing used in Claim 6. -/
theorem deleted_bijection_decomposition (n : ℕ) (u v : Fin n) (huv : u ≠ v) :
    (∑ φ : {x : Fin n // x ≠ u} ≃ {x : Fin n // x ≠ v},
        (2 : ℝ) ^ cyclePairOrbitCount n u v φ) =
      ∑ k ∈ Finset.range (n - 1),
        ((n - 2).choose k : ℝ) * (n - k - 2).factorial *
          ∑ σ : Equiv.Perm (Fin k), (2 : ℝ) ^ pairOrbitCount σ := by
  classical
  let R := {r : List (Fin n) // (u :: v :: r).Nodup}
  letI : Fintype R := cycle_weight.pathFintype n u v
  let D := Σ r : R, Equiv.Perm {x : Fin n // x ∉ u :: v :: r.1}
  let total : ({x : Fin n // x ≠ u} ≃ {x : Fin n // x ≠ v}) ≃ D :=
    (constructed_toList.deletedPermEquiv u v).trans <|
      (constructed_toList.permPathEquiv u v huv).trans (cycle_weight.rawPathEquiv n u v)
  have huvval : u.val ≠ v.val := fun h => huv (Fin.ext h)
  have hn : 2 ≤ n := by omega
  let K (r : R) : Fin (n - 1) :=
    ⟨Fintype.card {x : Fin n // x ∉ u :: v :: r.1}, by
      rw [complement_card n u v r.1 r.2]
      omega⟩
  calc
    (∑ φ : {x : Fin n // x ≠ u} ≃ {x : Fin n // x ≠ v},
        (2 : ℝ) ^ cyclePairOrbitCount n u v φ) =
        ∑ d : D, (2 : ℝ) ^ pairOrbitCount d.2 := by
      rw [← Equiv.sum_comp total]
      apply Finset.sum_congr rfl
      intro φ _
      rw [cycle_weight n u v huv φ]
      rfl
    _ = ∑ r : R, ∑ σ : Equiv.Perm {x : Fin n // x ∉ u :: v :: r.1},
          (2 : ℝ) ^ pairOrbitCount σ := by
      rw [Fintype.sum_sigma]
    _ = ∑ r : R, ∑ σ : Equiv.Perm (Fin (K r).1),
          (2 : ℝ) ^ pairOrbitCount σ := by
      apply Finset.sum_congr rfl
      intro r _
      exact generic_reindex_fin _
    _ = ∑ k : Fin (n - 1),
        ((n - 2).choose k.1 : ℝ) * (n - k.1 - 2).factorial *
          ∑ σ : Equiv.Perm (Fin k.1), (2 : ℝ) ^ pairOrbitCount σ := by
      rw [← Finset.sum_fiberwise Finset.univ K]
      apply Finset.sum_congr rfl
      intro k _
      have hcard : (Finset.univ.filter fun r : R => K r = k).card =
          (n - 2).choose k.1 * (n - k.1 - 2).factorial := by
        rw [← Fintype.card_subtype]
        convert card_path_fiber n u v huv k using 1
        apply Fintype.card_congr
        apply Equiv.subtypeEquivRight
        intro r
        constructor
        · intro h
          exact congrArg Fin.val h
        · intro h
          exact Fin.ext h
      calc
        (∑ r ∈ Finset.univ with K r = k,
            ∑ σ : Equiv.Perm (Fin (K r).1), (2 : ℝ) ^ pairOrbitCount σ) =
            ∑ _r ∈ Finset.univ.filter (fun r : R => K r = k),
              ∑ σ : Equiv.Perm (Fin k.1), (2 : ℝ) ^ pairOrbitCount σ := by
          apply Finset.sum_congr rfl
          intro r hr
          have hkr : K r = k := by simpa using hr
          subst k
          rfl
        _ = ((Finset.univ.filter fun r : R => K r = k).card : ℝ) *
              (∑ σ : Equiv.Perm (Fin k.1), (2 : ℝ) ^ pairOrbitCount σ) := by
          simp
        _ = ((n - 2).choose k.1 : ℝ) * (n - k.1 - 2).factorial *
              ∑ σ : Equiv.Perm (Fin k.1), (2 : ℝ) ^ pairOrbitCount σ := by
          rw [hcard]
          push_cast
          ring
    _ = ∑ k ∈ Finset.range (n - 1),
        ((n - 2).choose k : ℝ) * (n - k - 2).factorial *
          ∑ σ : Equiv.Perm (Fin k), (2 : ℝ) ^ pairOrbitCount σ := by
      simpa using Fin.sum_univ_eq_sum_range
        (fun k : ℕ => ((n - 2).choose k : ℝ) * (n - k - 2).factorial *
          ∑ σ : Equiv.Perm (Fin k), (2 : ℝ) ^ pairOrbitCount σ) (n - 1)

/-- **Claim 6.** The weighted sum over deleted-vertex bijections equals
`(n - 2)!` times the sum of the unlabeled graph counts through `n - 2`. -/
theorem claim6_deleted_bijection_identity (n : ℕ) (u v : Fin n) (huv : u ≠ v) :
    (∑ φ : {x : Fin n // x ≠ u} ≃ {x : Fin n // x ≠ v},
        (2 : ℝ) ^ cyclePairOrbitCount n u v φ) =
      (n - 2).factorial * ∑ k ∈ Finset.range (n - 1), (g k : ℝ) := by
  rw [deleted_bijection_decomposition n u v huv]
  calc
    (∑ k ∈ Finset.range (n - 1),
        ((n - 2).choose k : ℝ) * (n - k - 2).factorial *
          ∑ σ : Equiv.Perm (Fin k), (2 : ℝ) ^ pairOrbitCount σ) =
        ∑ k ∈ Finset.range (n - 1), ((n - 2).factorial : ℝ) * g k := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k ≤ n - 2 := by
        simp only [Finset.mem_range] at hk
        omega
      have hburnsideNat := claim5_burnside_pair_orbit_identity k
      have hburnside :
          (∑ σ : Equiv.Perm (Fin k), (2 : ℝ) ^ pairOrbitCount σ) =
            (k.factorial : ℝ) * g k := by
        exact_mod_cast hburnsideNat
      rw [hburnside]
      have hsub : n - k - 2 = n - 2 - k := by omega
      rw [hsub]
      have hfactorial := Nat.choose_mul_factorial_mul_factorial hk'
      norm_cast at hfactorial ⊢
      nlinarith
    _ = (n - 2).factorial * ∑ k ∈ Finset.range (n - 1), (g k : ℝ) := by
      rw [Finset.mul_sum]

end BastienKhormali
