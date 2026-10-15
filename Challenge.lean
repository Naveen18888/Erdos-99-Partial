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
        ((longTracks X L).card : ℝ) - sel.card ≤ 3 / 5 * (π * diam X - sel.card) + ε * diam X := sorry

lemma exists_countingWitness (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      Nonempty (CountingWitness X ε) := sorry

theorem erdos99_finite_multiplicity :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → HasUnitTriangle X := sorry

theorem erdos99_of_finite_multiplicity :
    (∀ᶠ n in atTop, numOptimalClasses n < ⊤) → Erdos99Conjecture := sorry

end Erdos99
