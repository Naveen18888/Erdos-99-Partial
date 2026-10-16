module

public import Mathlib

/-!
The finite-multiplicity case of Erdos Problem 99. There is a single threshold N
such that for each n at least N with finitely many congruence classes of optimal
configurations, every optimizer has a unit equilateral triangle. No assertion
is made for n with infinitely many classes. The exact normalization version is
also stated conditionally on eventual finite multiplicity.
-/

open scoped BigOperators Real
open Filter

@[expose] public noncomputable section

open Classical

namespace Erdos99

/-- The Euclidean plane, with its standard Euclidean metric. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Distinct points of the configuration are at distance at least one. -/
def IsSeparated (X : Finset Plane) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, x ≠ y → 1 ≤ dist x y

/-- The diameter of a finite configuration. -/
def diam (X : Finset Plane) : ℝ := Metric.diam (X : Set Plane)

/-- A configuration of n unit-separated points. -/
def Admissible (n : ℕ) (X : Finset Plane) : Prop :=
  X.card = n ∧ IsSeparated X

/-- The infimum of diameters of admissible n-point configurations. -/
def minDiam (n : ℕ) : ℝ := sInf (diam '' {X | Admissible n X})

/-- An admissible configuration minimizing diameter among all admissible configurations. -/
def IsOptimal (n : ℕ) (X : Finset Plane) : Prop :=
  Admissible n X ∧ ∀ Y, Admissible n Y → diam X ≤ diam Y

/-- Congruence under a bijective isometry of the Euclidean plane. -/
def Congruent (X Y : Finset Plane) : Prop :=
  ∃ e : Plane ≃ᵢ Plane, X.image e = Y

/-- The number of congruence classes of optimal configurations, valued in the extended naturals. -/
def numOptimalClasses (n : ℕ) : ℕ∞ :=
  Set.encard {C : Set (Finset Plane) |
    ∃ X, IsOptimal n X ∧ C = {Y | IsOptimal n Y ∧ Congruent X Y}}

/-- Three vertices at pairwise distance one; these equalities force distinctness. -/
def HasUnitTriangle (X : Finset Plane) : Prop :=
  ∃ a ∈ X, ∃ b ∈ X, ∃ c ∈ X, dist a b = 1 ∧ dist b c = 1 ∧ dist a c = 1

/-- Unit separation with at least one pair at distance exactly one. -/
def MinDistOne (X : Finset Plane) : Prop :=
  IsSeparated X ∧ ∃ x ∈ X, ∃ y ∈ X, dist x y = 1

/-- Diameter optimality using the exact minimum-distance-one normalization. -/
def IsErdosOptimal (n : ℕ) (X : Finset Plane) : Prop :=
  X.card = n ∧ MinDistOne X ∧ ∀ Y : Finset Plane, Y.card = n → MinDistOne Y → diam X ≤ diam Y

/-- Every sufficiently large optimizer contains a unit equilateral triangle. -/
def Erdos99Conjecture : Prop :=
  ∀ᶠ n in atTop, ∀ X : Finset Plane, IsErdosOptimal n X → HasUnitTriangle X

/-- The finite-multiplicity assertion, with a uniform sufficiently-large-n threshold. -/
theorem erdos99_finite_multiplicity :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → HasUnitTriangle X := by
  sorry

/-- The same assertion with optimality, separation, diameter and triangle definitions unfolded. -/
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
  sorry

/-- Eventual finite multiplicity implies the original exact-normalization conjecture. -/
theorem erdos99_of_finite_multiplicity
    (h : ∀ᶠ n in atTop, numOptimalClasses n < ⊤) : Erdos99Conjecture := by
  sorry

end Erdos99

end
