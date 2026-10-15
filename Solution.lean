module

public import Mathlib
public import Erdos99.Part09CaplessFlaggedAndAssembly

open scoped BigOperators Real
open Filter

@[expose] public noncomputable section

open Classical

namespace Erdos99

lemma track_count (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ ρ : ℝ, 0 < ρ ∧
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ O : Plane, (∀ x ∈ X, dist x O ≤ diam X / 2 + η * diam X) → IsRoundCentre ρ X O →
      ∃ L : ℝ, 0 ≤ L ∧ L ≤ ε * diam X ∧ ∃ sel ⊆ longTracks X L,
        (∀ T ∈ sel, IsSelectedTrack O (diam X) η T) ∧
        ((longTracks X L).card : ℝ) - sel.card ≤ 3 / 5 * (π * diam X - sel.card) + ε * diam X :=
  track_count_assembled ε η hε hη

lemma exists_countingWitness (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      Nonempty (CountingWitness X ε) :=
  exists_countingWitness_of_round track_count ε hε

theorem erdos99_finite_multiplicity :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → HasUnitTriangle X := by
  obtain ⟨ε, hε, hfin⟩ := final_contradiction
  filter_upwards [rhombi_card_lower ε hε, exists_countingWitness ε hε, rhombi_inside_card_le,
    eventually_ge_atTop 2] with n h1 h2 h3 hn2
  intro hfm X hX
  by_contra htri
  obtain ⟨w⟩ := h2 hfm X hX htri
  have hq := h1 hfm X hX htri
  have hD := hX.diam_pos hn2
  have hin := h3 hfm X hX htri (w.long \ w.sel) (Finset.sdiff_subset.trans w.long_subset)
  have hcard : ((w.long \ w.sel).card : ℝ) = (w.long.card : ℝ) - w.sel.card := by
    rw [Finset.card_sdiff_of_subset w.sel_subset, Nat.cast_sub (Finset.card_le_card w.sel_subset)]
  rw [hcard] at hin
  set L := (rhombi X).filter (fun R => ∃ T ∈ tracks X, T ∉ w.long ∧ Crosses T R)
  set Q := (rhombi X).filter (fun R => ∃ T ∈ w.sel, Crosses T R)
  set I := (rhombi X).filter (fun R => ∀ T ∈ tracks X, Crosses T R → T ∈ w.long \ w.sel)
  have hsub : rhombi X ⊆ L ∪ Q ∪ I := by
    intro R hR
    by_cases hL : ∃ T ∈ tracks X, T ∉ w.long ∧ Crosses T R
    · simp [L, hR, hL]
    by_cases hQ : ∃ T ∈ w.sel, Crosses T R
    · simp [Q, hR, hQ]
    refine Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hR, fun T hT hc => ?_⟩)
    refine Finset.mem_sdiff.2 ⟨?_, fun hs => hQ ⟨T, hs, hc⟩⟩
    by_contra hl
    exact hL ⟨T, hT, hl, hc⟩
  have hsplit : ((rhombi X).card : ℝ) ≤ L.card + Q.card + I.card := by
    have := (Finset.card_le_card hsub).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
    exact_mod_cast this
  have hR := (abs_le.1 w.abs_R_sub).2
  refine hfin (diam X) (rhombi X).card w.long.card w.sel.card Q.card w.f w.β w.c₂ w.C₁ w.A hD hq
    (by linarith) w.f_add_c₂_le w.two_fifths (by exact_mod_cast w.C₁_le_c₂) (by positivity)
    (by positivity) (by exact_mod_cast Finset.card_le_card w.sel_subset)
    w.annular_linear w.annular_quadratic ?_
  have := w.short_loss
  linarith

theorem erdos99_of_finite_multiplicity
    (h : ∀ᶠ n in atTop, numOptimalClasses n < ⊤) : Erdos99Conjecture := by
  filter_upwards [h, erdos99_finite_multiplicity, eventually_ge_atTop 2] with n hn hmain hn2
  intro X hX
  exact hmain hn X ((isErdosOptimal_iff_isOptimal hn2 X).1 hX)



end Erdos99

namespace Erdos99

theorem erdos99_finite_multiplicity_explicit :
    ∃ N : ℕ, ∀ n ≥ N, numOptimalClasses n < ⊤ →
      ∀ X : Finset (EuclideanSpace ℝ (Fin 2)),
        X.card = n →
        (∀ x ∈ X, ∀ y ∈ X, x ≠ y → 1 ≤ dist x y) →
        (∀ Y : Finset (EuclideanSpace ℝ (Fin 2)), Y.card = n →
          (∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → 1 ≤ dist x y) →
          Metric.diam (X : Set (EuclideanSpace ℝ (Fin 2))) ≤
            Metric.diam (Y : Set (EuclideanSpace ℝ (Fin 2)))) →
        ∃ a ∈ X, ∃ b ∈ X, ∃ c ∈ X, dist a b = 1 ∧ dist b c = 1 ∧ dist a c = 1 := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 erdos99_finite_multiplicity
  exact ⟨N, fun n hn hfin X hcard hsep hmin =>
    hN n hn hfin X ⟨⟨hcard, hsep⟩, fun Y hY => hmin Y hY.1 hY.2⟩⟩

end Erdos99

end
