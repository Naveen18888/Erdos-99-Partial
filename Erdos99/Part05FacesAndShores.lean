module

public import Mathlib
public import Erdos99.Part01Basics
public import Erdos99.Part03LiftedFanAndDensity
public import Erdos99.Part04RoundnessAndConnectivity

/-!
# Erdős Problem 99 under finite multiplicity — Part 5 of 9: Faces, crosscuts, shores and short sources

This is one of the supporting files of the formalization; the main theorem and a precise
description of what is proved are at the top of `Erdos99.lean`.

The file is divided into the following sections (each `section Name … end Name`); comments
elsewhere in the development refer to these sections by name.

* `FinitePropagation`
* `TokenProcess`
* `FaceConvexity`
* `FacePolygon`
* `ContactFan`
* `PolygonCycle`
* `FaceCapacity`
* `TokenRouting`
* `WindingJump`
* `Crosscut`
* `CrosscutShore`
* `PortCap`
* `PortRay`
* `SourceCap`
* `GateChain`
* `ShoreGeometry`
* `ShortSources`
-/

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `FinitePropagation`
-/

section FinitePropagation

/-!
# WP7 `FinitePropagation`: the token ledger and stability (Verification Guide §9)

This file sets up the accounting of work package WP7 of `TRACK_COUNT_REVISED_PLAN.md`: the
quantities of §9.4, the structure `TokenLedger` (what a token process of depth `K` must deliver)
and the derivation of (S1) from a ledger.  The open geometric inputs and the final output
`stability_bounds` are in `Stability`; the token process itself is in `TokenProcess`.
All results here are proved:

* `TokenLedger.S1`: a token ledger of depth `K` with loss `B` gives (S1),
  `K S_def ≤ p + f₇ + 3 K B`, where `S_def = Δ + ρ/3 + f₇ + f₈ + Q₉/4` (`stabilityDefect`).
  The face part uses the capacities of §8 through `Propagation.netAbsorbed_le_faceNetCap`, and
  the single-emission bound through `Propagation.emitted`.
* `UnitPolygon.marked_card_le_markedCap`: the WP6 capacities in the form used by the ledger.
* `pentagons_add_heptagons_le_pi_mul_diam`: `p + f₇ ≤ σ ≤ u ≤ b ≤ π D` when `Δ ≥ 0`.
* `highIncidence_le`: `Σ_{k ≥ 7} k f_k ≤ 7 f₇ + 8 f₈ + 9 Q₉`.
-/

open scoped BigOperators Real
open Filter Topology EstablishedExternalResults

@[expose] public noncomputable section

open Classical

namespace Erdos99

open Propagation

/-! ## The quantities of §9.4 -/

/-- `Q₉ = Σ_{k ≥ 9} (k - 8) f_k` (truncated subtraction makes the terms with `k ≤ 8` vanish). -/
def highExcess (X : Finset Plane) : ℕ := ∑ᶠ F ∈ exceptionalFaces X, (faceSize X F - 8)

/-- `Hinc = Σ_{k ≥ 7} k f_k`, the number of incidences of unit edges with faces of at least seven
sides. -/
def highIncidence (X : Finset Plane) : ℕ :=
  ∑ᶠ F ∈ {F ∈ contactFaces X | 7 ≤ faceSize X F}, faceSize X F

/-- `S_def = Δ + ρ/3 + f₇ + f₈ + Q₉/4`, the stability defect of §9.4. -/
def stabilityDefect (X : Finset Plane) : ℝ :=
  (lockingDefect X : ℝ) + (returnExcess X : ℝ) / 3 + faceCount X 7 + faceCount X 8 +
    (highExcess X : ℝ) / 4

/-! ## Finite bookkeeping over the exceptional faces -/

section Bookkeeping

variable {X : Finset Plane}

lemma contactFaces_finite (hX : IsSeparated X) : (contactFaces X).Finite :=
  (faces_finite (cUnitEdges_isPlaneGraph hX)).subset (fun _ hF => hF.1)

lemma exceptionalFaces_finite (hX : IsSeparated X) : (exceptionalFaces X).Finite :=
  (contactFaces_finite hX).subset (fun _ hF => hF.1)

/-- For `k ≥ 5`, `f_k` counts the exceptional faces with `k` sides. -/
lemma faceCount_eq_card_filter (hfin : (exceptionalFaces X).Finite) {k : ℕ} (hk : 5 ≤ k) :
    faceCount X k = (hfin.toFinset.filter (fun F => faceSize X F = k)).card := by
  unfold faceCount
  rw [← Set.ncard_coe_finset]
  congr 1
  ext F
  simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq, exceptionalFaces]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2 ▸ hk⟩, h2⟩
  · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩

lemma faceExcess_eq_sum (hfin : (exceptionalFaces X).Finite) :
    faceExcess X = ∑ F ∈ hfin.toFinset, (faceSize X F - 4) := by
  unfold faceExcess; exact finsum_mem_eq_finite_toFinset_sum _ hfin

lemma highExcess_eq_sum (hfin : (exceptionalFaces X).Finite) :
    highExcess X = ∑ F ∈ hfin.toFinset, (faceSize X F - 8) := by
  unfold highExcess; exact finsum_mem_eq_finite_toFinset_sum _ hfin

lemma highIncidence_eq_sum (hfin : (exceptionalFaces X).Finite) :
    highIncidence X = ∑ F ∈ hfin.toFinset.filter (fun F => 7 ≤ faceSize X F), faceSize X F := by
  have hfin' : {F ∈ contactFaces X | 7 ≤ faceSize X F}.Finite :=
    hfin.subset (fun F hF => ⟨hF.1, by have := hF.2; omega⟩)
  unfold highIncidence
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin']
  congr 1
  ext F
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Finset.mem_filter, exceptionalFaces]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by omega⟩, h2⟩
  · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩

/-- **The net face capacity in closed form**: summed over the exceptional faces,
`Σ faceNetCap(k_F) = σ - f₇ - f₈ - Q₉/4`. -/
theorem sum_faceNetCap_eq (hfin : (exceptionalFaces X).Finite) :
    ∑ F ∈ hfin.toFinset, faceNetCap (faceSize X F) =
      (faceExcess X : ℝ) - faceCount X 7 - faceCount X 8 - (highExcess X : ℝ) / 4 := by
  rw [sum_faceNetCap hfin.toFinset (faceSize X)
    (fun F hF => ((Set.Finite.mem_toFinset hfin).1 hF).2), faceExcess_eq_sum hfin,
    highExcess_eq_sum hfin, faceCount_eq_card_filter hfin (by norm_num : 5 ≤ 7),
    faceCount_eq_card_filter hfin (by norm_num : 5 ≤ 8)]
  push_cast
  ring

/-- **High-face incidences**: `Hinc ≤ 7 f₇ + 8 f₈ + 9 Q₉`. -/
theorem highIncidence_le (hX : IsSeparated X) :
    (highIncidence X : ℝ) ≤ 7 * faceCount X 7 + 8 * faceCount X 8 + 9 * highExcess X := by
  have hfin := exceptionalFaces_finite hX
  rw [highIncidence_eq_sum hfin, highExcess_eq_sum hfin,
    faceCount_eq_card_filter hfin (by norm_num : 5 ≤ 7),
    faceCount_eq_card_filter hfin (by norm_num : 5 ≤ 8)]
  push_cast
  exact sum_highIncidence_le hfin.toFinset (faceSize X)

/-- Each exceptional face contributes at least one to `σ`, and pentagons and heptagons are
exceptional faces: `p + f₇ ≤ σ`. -/
theorem pentagons_add_heptagons_le_faceExcess (hX : IsSeparated X) :
    numPentagons X + faceCount X 7 ≤ faceExcess X := by
  have hfin := exceptionalFaces_finite hX
  unfold numPentagons
  rw [faceCount_eq_card_filter hfin (by norm_num : 5 ≤ 5),
    faceCount_eq_card_filter hfin (by norm_num : 5 ≤ 7), faceExcess_eq_sum hfin,
    ← Finset.card_union_of_disjoint (Finset.disjoint_filter.2 (fun F _ h5 h7 => by omega))]
  calc (Finset.filter (fun F => faceSize X F = 5) hfin.toFinset ∪
        Finset.filter (fun F => faceSize X F = 7) hfin.toFinset).card
      ≤ hfin.toFinset.card := Finset.card_le_card (Finset.union_subset
        (Finset.filter_subset _ _) (Finset.filter_subset _ _))
    _ = ∑ F ∈ hfin.toFinset, 1 := by simp
    _ ≤ _ := Finset.sum_le_sum (fun F hF => by
        have := ((Set.Finite.mem_toFinset hfin).1 hF).2; omega)

lemma numUnitHullSides_le (X : Finset Plane) :
    numUnitHullSides X ≤ (hullVertices X).card :=
  (Finset.card_filter_le _ _).trans (card_ccwHullSides_le X)

/-- **`p + f₇ ≤ π D`** (§9.4): `p + f₇ ≤ σ ≤ u - ρ - Δ ≤ u ≤ b ≤ π D` when `Δ ≥ 0`. -/
theorem pentagons_add_heptagons_le_pi_mul_diam (hX : IsSeparated X) (h2 : 2 ≤ X.card)
    (hΔ : 0 ≤ lockingDefect X) :
    ((numPentagons X + faceCount X 7 : ℕ) : ℝ) ≤ π * diam X := by
  have h1 := pentagons_add_heptagons_le_faceExcess hX
  have h3 := numUnitHullSides_le X
  have h4 := hullVertices_card_le_pi_mul_diam hX h2
  unfold lockingDefect at hΔ
  have : (faceExcess X : ℤ) ≤ numUnitHullSides X := by
    have : (0 : ℤ) ≤ returnExcess X := by positivity
    linarith
  have h5 : faceExcess X ≤ (hullVertices X).card := by omega
  calc ((numPentagons X + faceCount X 7 : ℕ) : ℝ) ≤ (hullVertices X).card := by
        exact_mod_cast h1.trans h5
    _ ≤ _ := h4

end Bookkeeping

/-! ## Local capacities in ledger form (WP6 → WP7) -/

/-- **Marked-edge capacity** (WP6 packaged for the ledger): in a closed unit polygon with
`k ≥ 5` pairwise unit-separated vertices, the edges with projection at least `c ≥ 19/20` on a
unit vector number at most `markedCap k`. -/
theorem UnitPolygon.marked_card_le_markedCap {k : ℕ} [NeZero k] (Q : UnitPolygon k) (hk : 5 ≤ k)
    {e : Plane} (he : ‖e‖ = 1) {c : ℝ} (hc : 19 / 20 ≤ c) {M : Finset (Fin k)}
    (hM : ∀ i ∈ M, c ≤ inner ℝ (Q.edge i) e) : (M.card : ℝ) ≤ markedCap k := by
  unfold markedCap
  rcases (show k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ 9 ≤ k by omega) with rfl | rfl | rfl | rfl | h9
  · have := Q.capacity_five he (by linarith) hM
    norm_num; exact_mod_cast this
  · have := Q.capacity_six he hc hM
    norm_num; exact_mod_cast this
  · have := Q.capacity_seven he (by linarith) hM
    norm_num; exact_mod_cast this
  · have := Q.capacity_eight he hc hM
    norm_num; exact_mod_cast this
  · rw [if_neg (by omega), if_neg (by omega)]
    exact Q.capacity_ge_nine h9 he (by linarith) hM

/-! ## The token ledger (§9.1–§9.4) -/

/-- **The accounting delivered by the finite token process of depth `K`** (§9.1–§9.4), with total
loss budget `B` (sources not under control, lost outputs of §9.2, and arrivals at large receivers
of §9.3, each charged to `B`).

* `arr j F` is the number of tokens that have arrived at the exceptional face `F` by the end of
  round `j` (`0 ≤ j ≤ K`); arrivals only accumulate, and the final arrivals at a face are within
  its marked-edge capacity `markedCap` of §8 (arrivals at large receivers are not recorded here
  but charged to `lost`).
* A pentagon re-emits on its second arrival, a heptagon on its third (`Propagation.emitted`);
  the tokens emitted in round `j` are exactly the live frontier after round `j`.
* `capAbs j` and `lost j` are the tokens absorbed at caps and lost by the end of round `j`.
* `conservation`: after every round `1 ≤ j ≤ K`, all but `B` of the `u` unit hull sources are
  absorbed at faces, absorbed at caps, lost, or live. -/
structure TokenLedger (X : Finset Plane) (K : ℕ) (B : ℝ) where
  /-- The exceptional faces are finite in number. -/
  fin : (exceptionalFaces X).Finite
  /-- Arrivals at each exceptional face by the end of each round. -/
  arr : ℕ → Set ℂ → ℕ
  arr_zero : ∀ F, arr 0 F = 0
  arr_mono : ∀ j F, arr j F ≤ arr (j + 1) F
  arr_cap : ∀ F ∈ exceptionalFaces X, (arr K F : ℝ) ≤ markedCap (faceSize X F)
  /-- Tokens absorbed at caps by the end of each round. -/
  capAbs : ℕ → ℝ
  cap_le : ∀ j ≤ K, capAbs j ≤ 2 * (returnExcess X : ℝ) / 3 + B
  /-- Tokens lost by the end of each round. -/
  lost : ℕ → ℝ
  lost_le : ∀ j ≤ K, lost j ≤ B
  conservation : ∀ j ∈ Finset.Icc 1 K,
    (numUnitHullSides X : ℝ) - B ≤
      (∑ F ∈ fin.toFinset, netAbsorbed (faceSize X F) (arr j F)) + capAbs j + lost j +
        ∑ F ∈ fin.toFinset,
          ((emitted (faceSize X F) (arr j F) : ℝ) - emitted (faceSize X F) (arr (j - 1) F))

namespace TokenLedger

variable {X : Finset Plane} {K : ℕ} {B : ℝ} (T : TokenLedger X K B)

lemma arr_mono' {i j : ℕ} (h : i ≤ j) (F : Set ℂ) : T.arr i F ≤ T.arr j F := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (T.arr_mono _ F)

lemma emitted_mono (k : ℕ) {a b : ℕ} (h : a ≤ b) : emitted k a ≤ emitted k b := by
  unfold emitted; split_ifs <;> omega

/-- The live frontier after round `j`: the tokens emitted in round `j`. -/
def frontier (j : ℕ) : ℝ :=
  ∑ F ∈ T.fin.toFinset,
    ((emitted (faceSize X F) (T.arr j F) : ℝ) - emitted (faceSize X F) (T.arr (j - 1) F))

/-- Net face absorption by the end of round `j ≤ K` is at most `σ - f₇ - f₈ - Q₉/4`. -/
lemma faceAbs_le {j : ℕ} (hj : j ≤ K) :
    ∑ F ∈ T.fin.toFinset, netAbsorbed (faceSize X F) (T.arr j F) ≤
      (faceExcess X : ℝ) - faceCount X 7 - faceCount X 8 - (highExcess X : ℝ) / 4 := by
  rw [← sum_faceNetCap_eq T.fin]
  refine Finset.sum_le_sum (fun F hF => ?_)
  have hF' := (Set.Finite.mem_toFinset T.fin).1 hF
  refine netAbsorbed_le_faceNetCap hF'.2 ?_
  exact le_trans (by exact_mod_cast T.arr_mono' hj F) (T.arr_cap F hF')

lemma sum_Icc_sub_pred (g : ℕ → ℝ) (K : ℕ) :
    ∑ j ∈ Finset.Icc 1 K, (g j - g (j - 1)) = g K - g 0 := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    simp only [add_tsub_cancel_right]; ring

lemma emitted_le_indicator (k a : ℕ) :
    (emitted k a : ℝ) ≤ (if k = 5 then 1 else 0) + (if k = 7 then 1 else 0) := by
  unfold emitted
  split_ifs <;> first | omega | norm_num

/-- **Each face emits at most once** (§9.4): the frontiers of rounds `1, …, K` add up to at most
`p + f₇`. -/
lemma sum_frontier_le :
    ∑ j ∈ Finset.Icc 1 K, T.frontier j ≤ ((numPentagons X + faceCount X 7 : ℕ) : ℝ) := by
  unfold frontier
  rw [Finset.sum_comm]
  simp_rw [sum_Icc_sub_pred (fun j => (emitted (faceSize X _) (T.arr j _) : ℝ)), T.arr_zero]
  have h0 : ∀ k, emitted k 0 = 0 := fun k => by unfold emitted; split_ifs <;> omega
  simp only [h0, Nat.cast_zero, sub_zero]
  unfold numPentagons
  rw [faceCount_eq_card_filter T.fin (by norm_num : 5 ≤ 5),
    faceCount_eq_card_filter T.fin (by norm_num : 5 ≤ 7), Finset.card_filter, Finset.card_filter]
  push_cast
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun F _ => emitted_le_indicator _ _)

include T in
/-- **(S1) from the token ledger** (§9.4): `K S_def ≤ p + f₇ + 3 K B`. -/
theorem S1 : (K : ℝ) * stabilityDefect X ≤ ((numPentagons X + faceCount X 7 : ℕ) : ℝ) + K * (3 * B) := by
  refine conservation_S1 K T.frontier (fun j hj => ?_) T.sum_frontier_le
  have hjK : j ≤ K := (Finset.mem_Icc.1 hj).2
  have h := frontier_ge_of_ledger (u := numUnitHullSides X) (σ := faceExcess X)
    (ρ := returnExcess X) (Δ := lockingDefect X) (f₇ := faceCount X 7) (f₈ := faceCount X 8)
    (Q₉ := highExcess X) (Bsrc := B) (B₁ := 0) (B₂ := B) (B₃ := B)
    (by unfold lockingDefect; push_cast; ring) (T.conservation j hj)
    (by linarith [T.faceAbs_le hjK]) (T.cap_le j hjK) (T.lost_le j hjK)
  unfold stabilityDefect frontier
  linarith

end TokenLedger

end Erdos99

end

end FinitePropagation

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `TokenProcess`
-/

section TokenProcess

/-!
# The deterministic finite token process (Verification Guide §9.1)

This file formalizes the *counting* part of the finite token process of §9.1 and shows that it
produces a `TokenLedger` (§9.4) as soon as its geometric bounds hold.

* `TokenProcess X`: every unit hull side of `X` is a source; each source is sent to a first
  receiver (`start`), and every exceptional face that emits sends its single emitted token to a
  receiver (`out`).  A receiver is an exceptional face, a cap, or the loss bin
  (`TokenDest`); a token sent to a face that is not exceptional is counted as lost.
* `TokenProcess.faceArr j F`: the arrivals at the face `F` by the end of round `j`, defined by
  the deterministic recursion of §9.1: pentagons emit on their second arrival, heptagons on their
  third (`Propagation.emitted`), and a token emitted by the end of round `j` arrives in round
  `j + 1`.  `capArr` and `lostArr` count the arrivals at caps and in the loss bin.
* `TokenProcess.conservation`: the **exact** conservation law: after every round `j ≥ 1`,
  the `u` sources are partitioned into the tokens retained at faces, absorbed at caps, lost, and
  the live frontier.
* `TokenProcess.toLedger`: a process whose final face arrivals are within the capacities of §8,
  whose cap arrivals are at most `2ρ/3 + B` and whose losses are at most `B` gives a
  `TokenLedger X K B`.

We also record two facts about the ledger interface itself:

* `TokenLedger.mono`: a ledger with loss `B` is a ledger with any larger loss.
* `TokenLedger.ofDefect`: if `S_def + Q₉ ≤ 3 B` then a ledger of every depth exists.  Together
  with `TokenLedger.S1` this shows that the existence of ledgers with `B = o(D)` is *equivalent*
  to the stability statement `S_def = o(D)`; see `exists_tokenLedger_of_stability`.
* `exists_littleO_of_forall_eventually`: a uniformization lemma turning "for every `η > 0`,
  eventually `≤ η D`" into a single loss budget `B(D) = o(D)`.
-/

open scoped BigOperators Real
open Filter Topology

@[expose] public noncomputable section

open Classical

namespace Erdos99

open Propagation

/-! ## Monotonicity of the ledger in the loss budget -/

/-- A ledger with loss budget `B` is a ledger with any larger loss budget `B'`. -/
def TokenLedger.mono {X : Finset Plane} {K : ℕ} {B B' : ℝ} (T : TokenLedger X K B)
    (h : B ≤ B') : TokenLedger X K B' where
  fin := T.fin
  arr := T.arr
  arr_zero := T.arr_zero
  arr_mono := T.arr_mono
  arr_cap := T.arr_cap
  capAbs := T.capAbs
  cap_le j hj := (T.cap_le j hj).trans (by linarith)
  lost := T.lost
  lost_le j hj := (T.lost_le j hj).trans h
  conservation j hj := le_trans (by linarith) (T.conservation j hj)

/-! ## Receivers and the process -/

/-- The receiver of a token: an exceptional face, a cap, or the loss bin. -/
inductive TokenDest
  | face (F : Set ℂ)
  | cap
  | lost

/-- **The finite token process of §9.1** (its routing data).  The sources are the unit hull
sides; `start p` is the first receiver of the source `p`, and `out G` the receiver of the single
token emitted by the face `G` (if `G` emits at all). -/
structure TokenProcess (X : Finset Plane) where
  /-- The exceptional faces are finite in number. -/
  fin : (exceptionalFaces X).Finite
  /-- The first receiver of each source. -/
  start : Plane × Plane → TokenDest
  /-- The receiver of the token emitted by each face. -/
  out : Set ℂ → TokenDest

namespace TokenProcess

variable {X : Finset Plane} (P : TokenProcess X)

/-- Whether a receiver counts as the face `F`. -/
def toFace (d : TokenDest) (F : Set ℂ) : ℕ := if d = .face F then 1 else 0

/-- Whether a receiver counts as a cap. -/
def toCap (d : TokenDest) : ℕ := if d = .cap then 1 else 0

/-- Whether a receiver counts as lost: the loss bin, or a face that is not exceptional. -/
def toLost (S : Finset (Set ℂ)) : TokenDest → ℕ
  | .face F => if F ∈ S then 0 else 1
  | .cap => 0
  | .lost => 1

/-- Every receiver is exactly one of: an exceptional face, a cap, lost. -/
lemma toFace_sum_add (S : Finset (Set ℂ)) (d : TokenDest) :
    ∑ F ∈ S, toFace d F + toCap d + toLost S d = 1 := by
  cases d with
  | face G =>
    by_cases hG : G ∈ S
    · rw [Finset.sum_eq_single_of_mem G hG (fun F _ hF => by
        simp [toFace, Ne.symm hF])]
      simp [toFace, toCap, toLost, hG]
    · rw [Finset.sum_eq_zero (fun F hF => by
        have : G ≠ F := fun h => hG (h ▸ hF)
        simp [toFace, this])]
      simp [toCap, toLost, hG]
  | cap => simp [toFace, toCap, toLost]
  | lost => simp [toFace, toCap, toLost]

/-- Arrivals at the face `F` by the end of round `j` (the deterministic recursion of §9.1). -/
def faceArr : ℕ → Set ℂ → ℕ
  | 0, _ => 0
  | j + 1, F => ∑ p ∈ unitHullSides X, toFace (P.start p) F +
      ∑ G ∈ P.fin.toFinset, toFace (P.out G) F * emitted (faceSize X G) (faceArr j G)

/-- Arrivals at caps by the end of round `j`. -/
def capArr : ℕ → ℕ
  | 0 => 0
  | j + 1 => ∑ p ∈ unitHullSides X, toCap (P.start p) +
      ∑ G ∈ P.fin.toFinset, toCap (P.out G) * emitted (faceSize X G) (P.faceArr j G)

/-- Tokens lost by the end of round `j`. -/
def lostArr : ℕ → ℕ
  | 0 => 0
  | j + 1 => ∑ p ∈ unitHullSides X, toLost P.fin.toFinset (P.start p) +
      ∑ G ∈ P.fin.toFinset, toLost P.fin.toFinset (P.out G) * emitted (faceSize X G) (P.faceArr j G)

lemma faceArr_zero (F : Set ℂ) : P.faceArr 0 F = 0 := rfl

lemma faceArr_mono (j : ℕ) (F : Set ℂ) : P.faceArr j F ≤ P.faceArr (j + 1) F := by
  induction j generalizing F with
  | zero => exact Nat.zero_le _
  | succ j ih =>
    show _ + _ ≤ _ + _
    gcongr with G
    exact TokenLedger.emitted_mono _ (ih G)

lemma faceArr_mono' {i j : ℕ} (h : i ≤ j) (F : Set ℂ) : P.faceArr i F ≤ P.faceArr j F := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (P.faceArr_mono _ F)

lemma capArr_mono (j : ℕ) : P.capArr j ≤ P.capArr (j + 1) := by
  cases j with
  | zero => exact Nat.zero_le _
  | succ j =>
    show _ + _ ≤ _ + _
    gcongr with G
    exact TokenLedger.emitted_mono _ (P.faceArr_mono j G)

lemma lostArr_mono (j : ℕ) : P.lostArr j ≤ P.lostArr (j + 1) := by
  cases j with
  | zero => exact Nat.zero_le _
  | succ j =>
    show _ + _ ≤ _ + _
    gcongr with G
    exact TokenLedger.emitted_mono _ (P.faceArr_mono j G)

lemma capArr_mono' {i j : ℕ} (h : i ≤ j) : P.capArr i ≤ P.capArr j := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (P.capArr_mono _)

lemma lostArr_mono' {i j : ℕ} (h : i ≤ j) : P.lostArr i ≤ P.lostArr j := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (P.lostArr_mono _)

/-- **Total arrivals** by the end of round `j + 1`: every source arrives somewhere once, and so
does every token emitted by the end of round `j`. -/
lemma total_arrivals (j : ℕ) :
    ∑ F ∈ P.fin.toFinset, P.faceArr (j + 1) F + P.capArr (j + 1) + P.lostArr (j + 1) =
      numUnitHullSides X + ∑ G ∈ P.fin.toFinset, emitted (faceSize X G) (P.faceArr j G) := by
  set S := P.fin.toFinset
  have hsrc : ∑ F ∈ S, ∑ p ∈ unitHullSides X, toFace (P.start p) F +
      ∑ p ∈ unitHullSides X, toCap (P.start p) + ∑ p ∈ unitHullSides X, toLost S (P.start p) =
        numUnitHullSides X := by
    rw [Finset.sum_comm, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    simp only [toFace_sum_add, Finset.sum_const, smul_eq_mul, mul_one]
    rfl
  have hem : ∑ F ∈ S, ∑ G ∈ S, toFace (P.out G) F * emitted (faceSize X G) (P.faceArr j G) +
      ∑ G ∈ S, toCap (P.out G) * emitted (faceSize X G) (P.faceArr j G) +
      ∑ G ∈ S, toLost S (P.out G) * emitted (faceSize X G) (P.faceArr j G) =
        ∑ G ∈ S, emitted (faceSize X G) (P.faceArr j G) := by
    rw [Finset.sum_comm, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun G _ => ?_)
    rw [← Finset.sum_mul, ← add_mul, ← add_mul, toFace_sum_add, one_mul]
  simp only [faceArr, capArr, lostArr, Finset.sum_add_distrib]
  rw [← hsrc, ← hem]
  ring

/-- **Exact conservation** (§9.4): after round `j + 1`, the `u` sources are exactly the tokens
retained at faces, absorbed at caps, lost, and the live frontier (tokens emitted in round
`j + 1`). -/
theorem conservation (j : ℕ) :
    (∑ F ∈ P.fin.toFinset, netAbsorbed (faceSize X F) (P.faceArr (j + 1) F)) +
        (P.capArr (j + 1) : ℝ) + P.lostArr (j + 1) +
        ∑ F ∈ P.fin.toFinset, ((emitted (faceSize X F) (P.faceArr (j + 1) F) : ℝ) -
          emitted (faceSize X F) (P.faceArr j F)) = numUnitHullSides X := by
  have h := P.total_arrivals j
  have hn : ∀ F, netAbsorbed (faceSize X F) (P.faceArr (j + 1) F) =
      (P.faceArr (j + 1) F : ℝ) - emitted (faceSize X F) (P.faceArr (j + 1) F) := fun F => by
    rw [← netAbsorbed_add_emitted (faceSize X F) (P.faceArr (j + 1) F)]; ring
  simp only [hn, Finset.sum_sub_distrib]
  have h' : (∑ F ∈ P.fin.toFinset, (P.faceArr (j + 1) F : ℝ)) + P.capArr (j + 1) +
      P.lostArr (j + 1) = numUnitHullSides X +
        ∑ G ∈ P.fin.toFinset, (emitted (faceSize X G) (P.faceArr j G) : ℝ) := by
    exact_mod_cast h
  linarith

/-- **From the process to the ledger** (§9.1 → §9.4).  If the final arrivals at every exceptional
face are within its capacity of §8, at most `2ρ/3 + B` tokens reach caps and at most `B` are
lost, the process gives a token ledger of depth `K` with loss `B`. -/
def toLedger (K : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hface : ∀ F ∈ exceptionalFaces X, (P.faceArr K F : ℝ) ≤ markedCap (faceSize X F))
    (hcap : (P.capArr K : ℝ) ≤ 2 * (returnExcess X : ℝ) / 3 + B)
    (hlost : (P.lostArr K : ℝ) ≤ B) : TokenLedger X K B where
  fin := P.fin
  arr := P.faceArr
  arr_zero := P.faceArr_zero
  arr_mono := P.faceArr_mono
  arr_cap := hface
  capAbs j := P.capArr j
  cap_le j hj := le_trans (by exact_mod_cast P.capArr_mono' hj) hcap
  lost j := P.lostArr j
  lost_le j hj := le_trans (by exact_mod_cast P.lostArr_mono' hj) hlost
  conservation j hj := by
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by have := (Finset.mem_Icc.1 hj).1; omega⟩
    have := P.conservation i
    simp only [add_tsub_cancel_right]
    linarith

end TokenProcess

/-! ## The ledger interface is equivalent to stability -/

lemma markedCap_nonneg (k : ℕ) : 0 ≤ markedCap k := by
  unfold markedCap
  split_ifs with h1 h2
  · norm_num
  · norm_num
  · have : (9 : ℝ) ≤ k := by exact_mod_cast (show 9 ≤ k by omega)
    linarith

/-- Filling a `k`-face up to the integer part of its capacity absorbs all of its net capacity
except at most `(k - 8)₊`. -/
lemma faceNetCap_sub_le_netAbsorbed_floor {k : ℕ} (hk : 5 ≤ k) :
    faceNetCap k - ((k - 8 : ℕ) : ℝ) ≤ netAbsorbed k ⌊markedCap k⌋₊ := by
  rcases (show k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ 9 ≤ k by omega) with rfl | rfl | rfl | rfl | h9
  · norm_num [faceNetCap, markedCap, netAbsorbed]
  · norm_num [faceNetCap, markedCap, netAbsorbed]
  · norm_num [faceNetCap, markedCap, netAbsorbed]
  · norm_num [faceNetCap, markedCap, netAbsorbed]
  · have hlt := Nat.lt_floor_add_one (markedCap k)
    have hk9 : (9 : ℝ) ≤ k := by exact_mod_cast h9
    have e1 : ((k - 8 : ℕ) : ℝ) = k - 8 := by rw [Nat.cast_sub (by omega)]; norm_num
    rw [faceNetCap_of_nine_le h9]
    unfold netAbsorbed
    rw [if_neg (by omega), if_neg (by omega)]
    have hm : markedCap k = k - 4 - (k - 8) / 4 := by
      unfold markedCap; rw [if_neg (by omega), if_neg (by omega)]
    rw [hm] at hlt ⊢
    rw [e1]
    linarith

/-- **A degenerate ledger from the stability defect.**  If `S_def + Q₉ ≤ 3 B`, a
token ledger of every depth `K` with loss `B` exists: every exceptional face is filled to the
integer part of its capacity in round `1`, the caps absorb `2ρ/3 + B` and `B` tokens are lost.
Together with `TokenLedger.S1` this shows that ledgers with small loss exist exactly when the
stability defect is small, so the ledger interface carries no information beyond (S1). -/
def TokenLedger.ofDefect {X : Finset Plane} (hX : IsSeparated X) (K : ℕ) {B : ℝ}
    (hB : stabilityDefect X + highExcess X ≤ 3 * B) : TokenLedger X K B where
  fin := exceptionalFaces_finite hX
  arr j F := if j = 0 then 0 else ⌊markedCap (faceSize X F)⌋₊
  arr_zero F := by simp
  arr_mono j F := by rw [if_neg (Nat.succ_ne_zero j)]; split_ifs <;> simp
  arr_cap F _ := by
    split_ifs
    · simpa using markedCap_nonneg _
    · exact Nat.floor_le (markedCap_nonneg _)
  capAbs _ := 2 * (returnExcess X : ℝ) / 3 + B
  cap_le _ _ := le_rfl
  lost _ := B
  lost_le _ _ := le_rfl
  conservation j hj := by
    have hj1 : j ≠ 0 := by have := (Finset.mem_Icc.1 hj).1; omega
    set hfin := exceptionalFaces_finite hX
    have hk : ∀ F ∈ hfin.toFinset, 5 ≤ faceSize X F := fun F hF =>
      ((Set.Finite.mem_toFinset hfin).1 hF).2
    -- the frontier is nonnegative
    have hfr : 0 ≤ ∑ F ∈ hfin.toFinset,
        ((emitted (faceSize X F) (if j = 0 then 0 else ⌊markedCap (faceSize X F)⌋₊) : ℝ) -
          emitted (faceSize X F) (if j - 1 = 0 then 0 else ⌊markedCap (faceSize X F)⌋₊)) := by
      refine Finset.sum_nonneg (fun F _ => sub_nonneg.2 ?_)
      have hle : (if j - 1 = 0 then 0 else ⌊markedCap (faceSize X F)⌋₊) ≤
          (if j = 0 then 0 else ⌊markedCap (faceSize X F)⌋₊) := by
        rw [if_neg hj1]; split_ifs <;> simp
      exact_mod_cast TokenLedger.emitted_mono _ hle
    -- the face absorption
    have hface : (faceExcess X : ℝ) - faceCount X 7 - faceCount X 8 - (highExcess X : ℝ) / 4 -
        highExcess X ≤ ∑ F ∈ hfin.toFinset,
          netAbsorbed (faceSize X F) (if j = 0 then 0 else ⌊markedCap (faceSize X F)⌋₊) := by
      rw [← sum_faceNetCap_eq hfin, highExcess_eq_sum hfin]
      push_cast
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_le_sum (fun F hF => ?_)
      rw [if_neg hj1]
      exact faceNetCap_sub_le_netAbsorbed_floor (hk F hF)
    have hu : (numUnitHullSides X : ℝ) =
        faceExcess X + returnExcess X + (lockingDefect X : ℝ) := by
      unfold lockingDefect; push_cast; ring
    unfold stabilityDefect at hB
    linarith

/-- **Uniformization of little-o bounds.**  If for every `η > 0` eventually every `x` with
`P n x` satisfies `Q x (η d(n))`, then a single function `B` with
`B(D)/D → 0` works: eventually every `x` with `P n x` satisfies `Q x (B (d n))`. -/
theorem exists_littleO_of_forall_eventually {α : Type*} (P : ℕ → α → Prop) (d : ℕ → ℝ)
    (Q : α → ℝ → Prop)
    (h : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, ∀ x, P n x → Q x (η * d n)) :
    ∃ B : ℝ → ℝ, Tendsto (fun D => B D / D) atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, ∀ x, P n x → Q x (B (d n)) := by
  have h' : ∀ m : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∀ x, P n x → Q x (1 / ((m : ℝ) + 1) * d n) :=
    fun m => eventually_atTop.1 (h _ (by positivity))
  choose N hN using h'
  set good : ℝ → ℕ → Prop := fun D m => ∀ n < N m, d n < D
  set M : ℝ → ℕ := fun D => Nat.findGreatest (good D) ⌊D⌋₊
  refine ⟨fun D => 1 / ((M D : ℝ) + 1) * D, ?_, ?_⟩
  · -- `M D → ∞`
    have hM : Tendsto M atTop atTop := by
      refine tendsto_atTop.2 (fun m => ?_)
      set C := ∑ n ∈ Finset.range (N m), |d n|
      filter_upwards [eventually_gt_atTop C, eventually_ge_atTop (m : ℝ)] with D hC hm
      refine Nat.le_findGreatest (Nat.le_floor hm) (fun n hn => ?_)
      have : |d n| ≤ C := Finset.single_le_sum (f := fun n => |d n|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.2 hn)
      exact lt_of_le_of_lt ((le_abs_self _).trans this) hC
    have h1 : Tendsto (fun D => 1 / ((M D : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hM
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with D hD
    field_simp
  · filter_upwards [eventually_ge_atTop (N 0)] with n hn x hx
    by_cases h0 : M (d n) = 0
    · have := hN 0 n hn x hx
      simp only [h0]; simpa using this
    · have hg : good (d n) (M (d n)) := Nat.findGreatest_of_ne_zero rfl h0
      have hnN : N (M (d n)) ≤ n := by
        by_contra hlt
        exact lt_irrefl _ (hg n (by omega))
      exact hN _ n hnN x hx

/-- **Stability gives ledgers.**  If the conclusion of `stability_bounds` holds for `Δ, ρ, f₇, f₈`
and `Q₉`, then for every depth `K` the conclusion of `exists_tokenLedger` holds.  (Conversely,
`TokenLedger.S1` derives stability from ledgers, given `Δ ≥ 0`.)  So `exists_tokenLedger` is
equivalent to the stability statement itself. -/
theorem exists_tokenLedger_of_stability
    (h : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      ¬ HasUnitTriangle X →
      (lockingDefect X : ℝ) ≤ η * diam X ∧ (returnExcess X : ℝ) ≤ η * diam X ∧
      (faceCount X 7 : ℝ) ≤ η * diam X ∧ (faceCount X 8 : ℝ) ≤ η * diam X ∧
      (highExcess X : ℝ) ≤ η * diam X) (K : ℕ) :
    ∃ B : ℝ → ℝ, Tendsto (fun D => B D / D) atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
        Nonempty (TokenLedger X K (B (diam X))) := by
  obtain ⟨B, hB, hev⟩ := exists_littleO_of_forall_eventually
    (fun n X => numOptimalClasses n < ⊤ ∧ IsOptimal n X ∧ ¬ HasUnitTriangle X) minDiam
    (fun X b => Nonempty (TokenLedger X K b)) (fun η hη => by
      filter_upwards [h (η / 2) (by positivity)] with n hn X ⟨hfm, hX, htri⟩
      obtain ⟨h1, h2, h3, h4, h5⟩ := hn hfm X hX htri
      have hD : 0 ≤ diam X := Metric.diam_nonneg
      rw [← hX.diam_eq]
      refine ⟨TokenLedger.ofDefect hX.1.2 K ?_⟩
      unfold stabilityDefect
      nlinarith)
  refine ⟨B, hB, ?_⟩
  filter_upwards [hev] with n hn hfm X hX htri
  have := hn X ⟨hfm, hX, htri⟩
  rwa [← hX.diam_eq] at this

end Erdos99

end

end TokenProcess

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `FaceConvexity`
-/

section FaceConvexity

/-!
# Bounded faces of a plane graph with the fan property are convex polygons (Lemma 2.1)

Let `(V, E)` be a straight-line plane graph in `ℂ` with the **fan property**: every vertex that is
not a vertex of the convex hull `K` of `V` has, for every direction, a neighbour strictly on that
side (its unit-neighbour fan has gaps smaller than `π`).  Then every bounded face of the graph is
the interior of a convex polygon whose vertices are vertices of the graph, in strictly convex
position, and whose sides are exactly the boundary edges of the face.

The proof is by visibility.  For `z` in a bounded face `F`, the set of points `w` such that the
segment `[z, w]` misses the drawing is open; it is also closed in `F`: if `[z, w]` first meets the
drawing at `y`, then either `y` lies inside an edge crossing `[z, w]`, or `y` is a vertex which by
the fan property has neighbours strictly on both sides of `[z, w]` (if `y` is not a hull vertex),
or `y` is a hull vertex strictly between two points of `K` (impossible).  In the first two cases
every segment `[z, w']` with `w'` near `w` meets the drawing (`cross_stable`).  Hence `F` is
star-shaped about each of its points, i.e. convex, and the polygon structure follows.
-/

open scoped BigOperators Real
open EstablishedExternalResults Set Complex Filter Topology

@[expose] public noncomputable section

open Classical

namespace Erdos99

/-- The **fan property** of a plane graph: every vertex that is not a vertex of the convex hull
of `V` has, for every direction `ν ≠ 0`, a neighbour strictly to the left of the direction `ν`. -/
def FanCondition (V : Finset ℂ) (E : Finset (Sym2 ℂ)) : Prop :=
  ∀ y ∈ V, y ∉ extremePoints ℝ (convexHull ℝ (V : Set ℂ)) → ∀ ν : ℂ, ν ≠ 0 →
    ∃ y', s(y, y') ∈ E ∧ 0 < ((y' - y) / ν).im

/-! ## Stability of a crossing -/

lemma wc_affine (z w y p : ℂ) (l : ℝ) :
    wc z w (y + (l : ℂ) * (p - y)) = wc z w y + (l : ℂ) * (wc z w p - wc z w y) := by
  simp only [wc]; ring

lemma continuousAt_wc {z w : ℂ} (hzw : z ≠ w) (x : ℂ) :
    ContinuousAt (fun w' => wc z w' x) w := by
  unfold wc
  exact continuousAt_const.div (continuousAt_id.sub continuousAt_const) (sub_ne_zero.2 hzw.symm)

/-- A point whose `wc`-coordinate is real and in `[0, 1]` lies on the segment. -/
lemma mem_segment_of_wc {z w c : ℂ} (hzw : z ≠ w) (him : (wc z w c).im = 0)
    (h0 : 0 ≤ (wc z w c).re) (h1 : (wc z w c).re ≤ 1) : c ∈ segment ℝ z w := by
  rw [segment_eq_image']
  refine ⟨(wc z w c).re, ⟨h0, h1⟩, ?_⟩
  have e := eq_param hzw c
  have hr : wc z w c = ((wc z w c).re : ℂ) := Complex.ext (by simp) (by simp [him])
  show z + (wc z w c).re • (w - z) = c
  rw [Complex.real_smul]
  conv_rhs => rw [e, hr]
  ring

/-- **Stability of a crossing.**  If `y` lies strictly inside `[z, w]` and `a`, `b` lie strictly on
opposite sides of the line `z w`, then every segment `[z, w']` with `w'` close to `w` meets
`[y, a] ∪ [y, b]`. -/
lemma cross_stable {z w y a b : ℂ} (hzw : z ≠ w) (hy : y ∈ openSegment ℝ z w)
    (ha : 0 < (wc z w a).im) (hb : (wc z w b).im < 0) :
    ∀ᶠ w' in 𝓝 w, (segment ℝ z w' ∩ (segment ℝ y a ∪ segment ℝ y b)).Nonempty := by
  -- coordinates of `y` on `[z, w]`
  obtain ⟨s, r, hs, hr, hsr, rfl⟩ := hy
  have hyw : wc z w (s • z + r • w) = (r : ℂ) := by
    have : s • z + r • w = z + (w - z) * (r : ℂ) := by
      rw [Complex.real_smul, Complex.real_smul, show (s : ℂ) = 1 - r by
        rw [← ofReal_one, ← hsr]; push_cast; ring]
      ring
    rw [this, wc_param hzw]
  set y := s • z + r • w with hydef
  set G : ℂ → ℂ → ℂ := fun w' x => wc z w' x
  have hG : ∀ x, ContinuousAt (fun w' => G w' x) w := fun x => continuousAt_wc hzw x
  -- the two candidate crossing points
  set l1 : ℂ → ℝ := fun w' => (G w' y).im / ((G w' y).im - (G w' b).im)
  set l2 : ℂ → ℝ := fun w' => (G w' y).im / ((G w' y).im - (G w' a).im)
  set c1 : ℂ → ℂ := fun w' => y + (l1 w' : ℂ) * (b - y)
  set c2 : ℂ → ℂ := fun w' => y + (l2 w' : ℂ) * (a - y)
  have hGy : (G w y).im = 0 := by simp [G, hyw]
  have hGyre : (G w y).re = r := by simp [G, hyw]
  have hd1 : (G w y).im - (G w b).im ≠ 0 := by rw [hGy]; simp only [G]; linarith
  have hd2 : (G w y).im - (G w a).im ≠ 0 := by rw [hGy]; simp only [G]; linarith
  have hcl1 : ContinuousAt l1 w :=
    (continuous_im.continuousAt.comp (hG y)).div
      ((continuous_im.continuousAt.comp (hG y)).sub (continuous_im.continuousAt.comp (hG b))) hd1
  have hcl2 : ContinuousAt l2 w :=
    (continuous_im.continuousAt.comp (hG y)).div
      ((continuous_im.continuousAt.comp (hG y)).sub (continuous_im.continuousAt.comp (hG a))) hd2
  have hl1w : l1 w = 0 := by simp only [l1]; rw [hGy, zero_div]
  have hl2w : l2 w = 0 := by simp only [l2]; rw [hGy, zero_div]
  -- the real coordinates of the candidate points along `[z, w']`
  set m1 : ℂ → ℝ := fun w' => ((G w' y) + (l1 w' : ℂ) * (G w' b - G w' y)).re
  set m2 : ℂ → ℝ := fun w' => ((G w' y) + (l2 w' : ℂ) * (G w' a - G w' y)).re
  have hcm1 : ContinuousAt m1 w := by
    refine continuous_re.continuousAt.comp ?_
    exact (hG y).add ((continuous_ofReal.continuousAt.comp hcl1).mul ((hG b).sub (hG y)))
  have hcm2 : ContinuousAt m2 w := by
    refine continuous_re.continuousAt.comp ?_
    exact (hG y).add ((continuous_ofReal.continuousAt.comp hcl2).mul ((hG a).sub (hG y)))
  have hm1w : m1 w = r := by simp only [m1]; rw [hl1w]; simp [hGyre]
  have hm2w : m2 w = r := by simp only [m2]; rw [hl2w]; simp [hGyre]
  have hr1 : r < 1 := by linarith
  have e1 : ∀ᶠ w' in 𝓝 w, 0 < (G w' a).im :=
    (continuous_im.continuousAt.comp (hG a)).eventually (lt_mem_nhds ha)
  have e2 : ∀ᶠ w' in 𝓝 w, (G w' b).im < 0 :=
    (continuous_im.continuousAt.comp (hG b)).eventually (gt_mem_nhds hb)
  have e3 : ∀ᶠ w' in 𝓝 w, 0 < m1 w' ∧ m1 w' < 1 := by
    have := hcm1.eventually (Ioo_mem_nhds (show 0 < m1 w by rw [hm1w]; exact hr)
      (show m1 w < 1 by rw [hm1w]; exact hr1))
    exact this.mono fun _ h => h
  have e4 : ∀ᶠ w' in 𝓝 w, 0 < m2 w' ∧ m2 w' < 1 := by
    have := hcm2.eventually (Ioo_mem_nhds (show 0 < m2 w by rw [hm2w]; exact hr)
      (show m2 w < 1 by rw [hm2w]; exact hr1))
    exact this.mono fun _ h => h
  have e5 : ∀ᶠ w' in 𝓝 w, w' ≠ z := (continuousAt_id.eventually_ne hzw.symm)
  filter_upwards [e1, e2, e3, e4, e5] with w' h1 h2 h3 h4 h5
  have hzw' : z ≠ w' := h5.symm
  rcases le_or_gt 0 (G w' y).im with hN | hN
  · -- cross `[y, b]`
    refine ⟨c1 w', ?_, Or.inr ?_⟩
    · have hwc : wc z w' (c1 w') = G w' y + (l1 w' : ℂ) * (G w' b - G w' y) := wc_affine _ _ _ _ _
      have hden : 0 < (G w' y).im - (G w' b).im := by linarith
      refine mem_segment_of_wc hzw' ?_ ?_ ?_
      · rw [hwc]
        simp only [add_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, sub_im, l1]
        have := hden.ne'
        field_simp
        ring
      · rw [hwc]; exact h3.1.le
      · rw [hwc]; exact h3.2.le
    · have hden : 0 < (G w' y).im - (G w' b).im := by linarith
      have hl0 : 0 ≤ l1 w' := div_nonneg hN hden.le
      have hl1 : l1 w' ≤ 1 := by
        rw [div_le_one hden]; linarith
      rw [segment_eq_image']
      exact ⟨l1 w', ⟨hl0, hl1⟩, by simp only [c1, Complex.real_smul]⟩
  · -- cross `[y, a]`
    refine ⟨c2 w', ?_, Or.inl ?_⟩
    · have hwc : wc z w' (c2 w') = G w' y + (l2 w' : ℂ) * (G w' a - G w' y) := wc_affine _ _ _ _ _
      have hden : (G w' y).im - (G w' a).im < 0 := by linarith
      refine mem_segment_of_wc hzw' ?_ ?_ ?_
      · rw [hwc]
        simp only [add_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, sub_im, l2]
        have := hden.ne
        field_simp
        ring
      · rw [hwc]; exact h4.1.le
      · rw [hwc]; exact h4.2.le
    · have hden : (G w' y).im - (G w' a).im < 0 := by linarith
      have hl0 : 0 ≤ l2 w' := div_nonneg_of_nonpos hN.le hden.le
      have hl1 : l2 w' ≤ 1 := by
        rw [div_le_one_of_neg hden]; linarith
      rw [segment_eq_image']
      exact ⟨l2 w', ⟨hl0, hl1⟩, by simp only [c2, Complex.real_smul]⟩

/-! ## Faces lie in the hull; visibility -/

lemma clm_C (f : ℂ →L[ℝ] ℝ) (z : ℂ) : f z = z.re * f 1 + z.im * f I := by
  have e : z = z.re • (1 : ℂ) + z.im • I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [e]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

section Vis

variable {V : Finset ℂ} {E : Finset (Sym2 ℂ)}

lemma drawing_subset_hull (hP : IsPlaneGraph V E) :
    drawing V E ⊆ convexHull ℝ (V : Set ℂ) := by
  rintro z (hz | hz)
  · exact subset_convexHull ℝ _ hz
  · obtain ⟨e, he, hze⟩ := Set.mem_iUnion₂.1 hz
    induction e using Sym2.ind with
    | _ p q =>
    rw [edgeSeg_mk] at hze
    exact (convex_convexHull ℝ _).segment_subset
      (subset_convexHull ℝ _ (hP.mem_V _ he p (Sym2.mem_mk_left _ _)))
      (subset_convexHull ℝ _ (hP.mem_V _ he q (Sym2.mem_mk_right _ _))) hze

lemma face_eq_component {F : Set ℂ} (hF : F ∈ faces V E) {z : ℂ} (hz : z ∈ F) :
    F = connectedComponentIn (drawing V E)ᶜ z := by
  obtain ⟨x, -, rfl⟩ := mem_faces_iff.1 hF
  exact (connectedComponentIn_eq hz)

lemma face_subset_compl {F : Set ℂ} (hF : F ∈ faces V E) : F ⊆ (drawing V E)ᶜ := by
  obtain ⟨x, -, rfl⟩ := mem_faces_iff.1 hF
  exact connectedComponentIn_subset _ _

/-- A preconnected set off the drawing meeting a face lies in the face. -/
lemma subset_face {F : Set ℂ} (hF : F ∈ faces V E) {S : Set ℂ} (hS : IsPreconnected S)
    (hSD : S ⊆ (drawing V E)ᶜ) {z : ℂ} (hzS : z ∈ S) (hzF : z ∈ F) : S ⊆ F := by
  rw [face_eq_component hF hzF]
  exact hS.subset_connectedComponentIn hzS hSD

/-- Points of the closure of a face that are not in the face lie on the drawing. -/
lemma closure_face_diff {F : Set ℂ} (hF : F ∈ faces V E) {z : ℂ} (hz : z ∈ closure F)
    (hzF : z ∉ F) : z ∈ drawing V E := by
  by_contra hD
  obtain ⟨x, -, rfl⟩ := mem_faces_iff.1 hF
  exact hzF (mem_face_of_mem_closure (isClosed_drawing V E).isOpen_compl hz hD)

/-- **Bounded faces lie in the convex hull of the vertices.** -/
lemma boundedFace_subset_hull (hP : IsPlaneGraph V E) {F : Set ℂ} (hF : F ∈ faces V E)
    (hb : Bornology.IsBounded F) : F ⊆ convexHull ℝ (V : Set ℂ) := by
  intro z hzF
  by_contra hzK
  obtain ⟨f, u, hfz, hfK⟩ := geometric_hahn_banach_point_closed (convex_convexHull ℝ _)
    (V.finite_toSet.isClosed_convexHull) hzK
  set d : ℂ := -((f 1 : ℂ) + (f I : ℂ) * I)
  have hfd : f d = -((f 1) ^ 2 + (f I) ^ 2) := by
    rw [clm_C f d]; simp [d]; ring
  -- the ray from `z` in direction `d` avoids the hull
  have hray : ∀ t : ℝ, 0 ≤ t → z + t • d ∉ convexHull ℝ (V : Set ℂ) := by
    intro t ht hK
    have h1 := hfK _ hK
    rw [map_add, map_smul, hfd, smul_eq_mul] at h1
    nlinarith [sq_nonneg (f 1), sq_nonneg (f I)]
  have hS : IsPreconnected ((fun t : ℝ => z + t • d) '' Set.Ici 0) :=
    isPreconnected_Ici.image _ (by fun_prop)
  have hsub := subset_face hF hS (by
      rintro _ ⟨t, ht, rfl⟩ hD
      exact hray t ht (drawing_subset_hull hP hD)) ⟨0, Set.self_mem_Ici, by simp⟩ hzF
  -- `d ≠ 0` since `f ≠ 0`
  have hd : d ≠ 0 := by
    intro h0
    have : f d = 0 := by rw [h0, map_zero]
    rw [hfd] at this
    have h1 : f 1 = 0 := by nlinarith [sq_nonneg (f 1), sq_nonneg (f I)]
    have h2 : f I = 0 := by nlinarith [sq_nonneg (f 1), sq_nonneg (f I)]
    have hf0 : ∀ x, f x = 0 := fun x => by rw [clm_C f x, h1, h2]; ring
    rcases (convexHull ℝ (V : Set ℂ)).eq_empty_or_nonempty with hne | ⟨v, hv⟩
    · have hDe : drawing V E = ∅ := Set.subset_eq_empty (drawing_subset_hull hP) hne
      have hFu : F = Set.univ := by
        rw [face_eq_component hF hzF, hDe, Set.compl_empty, connectedComponentIn_univ,
          PreconnectedSpace.connectedComponent_eq_univ]
      obtain ⟨R, hR⟩ := hb.subset_closedBall 0
      have := hR (hFu ▸ Set.mem_univ ((|R| + 1 : ℝ) : ℂ))
      rw [Metric.mem_closedBall, dist_zero_right, norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)] at this
      linarith [le_abs_self R]
    · have := hfK v hv
      rw [hf0 v] at this
      rw [hf0 z] at hfz
      linarith
  obtain ⟨R, hR⟩ := hb.subset_closedBall z
  have hmem := hsub ⟨(|R| + 1) / ‖d‖, Set.mem_Ici.2 (by positivity), rfl⟩
  have := hR hmem
  rw [Metric.mem_closedBall, dist_eq, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity), div_mul_cancel₀ _ (norm_ne_zero_iff.2 hd)] at this
  linarith [le_abs_self R]

end Vis

section Vis2

variable {V : Finset ℂ} {E : Finset (Sym2 ℂ)}

lemma mem_openSegment_of_ne' {a b z : ℂ} (hz : z ∈ segment ℝ a b) (ha : z ≠ a) (hb : z ≠ b) :
    z ∈ openSegment ℝ a b := by
  rw [← insert_endpoints_openSegment] at hz
  rcases hz with h1 | h1 | h1
  · exact absurd h1 ha
  · exact absurd h1 hb
  · exact h1

lemma mem_segment_line (z d : ℂ) {a b t : ℝ} (ht : t ∈ Set.uIcc a b) :
    z + t • d ∈ segment ℝ (z + a • d) (z + b • d) := by
  have h := image_segment ℝ (AffineMap.lineMap z (z + d) : ℝ →ᵃ[ℝ] ℂ) a b
  have e : ∀ τ : ℝ, (AffineMap.lineMap z (z + d) : ℝ →ᵃ[ℝ] ℂ) τ = z + τ • d := by
    intro τ; rw [AffineMap.lineMap_apply]; simp [vsub_eq_sub, vadd_eq_add]; ring
  rw [e, e] at h
  rw [← h, segment_eq_uIcc]
  exact ⟨t, ht, e t⟩

lemma im_wc_of_real {z w y a : ℂ} (hy : (wc z w y).im = 0) :
    (wc z w a).im = ((a - y) / (w - z)).im := by
  have := wc_sub (a := z) (b := w) a y
  rw [← this, sub_im, hy, sub_zero]

/-- The set of points visible from `z` (the segment from `z` misses the drawing) is open. -/
lemma isOpen_vis (z : ℂ) : IsOpen {w' : ℂ | Disjoint (segment ℝ z w') (drawing V E)} := by
  rw [isOpen_iff_eventually]
  intro w hw
  have hP : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ᶠ p : ℂ × ℝ in 𝓝 (w, t),
      (fun (w' : ℂ) (s : ℝ) => z + s • (w' - z) ∉ drawing V E) p.1 p.2 := by
    intro t ht
    have hc : Continuous fun p : ℂ × ℝ => z + p.2 • (p.1 - z) := by fun_prop
    have hmem : z + t • (w - z) ∈ (drawing V E)ᶜ := by
      intro hD
      refine Set.disjoint_left.1 hw ?_ hD
      rw [segment_eq_image']; exact ⟨t, ht, rfl⟩
    exact hc.continuousAt.eventually ((isClosed_drawing V E).isOpen_compl.mem_nhds hmem)
  filter_upwards [(isCompact_Icc (a := (0:ℝ)) (b := 1)).eventually_forall_of_forall_eventually
    (P := fun (w' : ℂ) (s : ℝ) => z + s • (w' - z) ∉ drawing V E) hP] with w' hw'
  rw [Set.disjoint_left]
  intro p hp hpD
  rw [segment_eq_image'] at hp
  obtain ⟨t, ht, rfl⟩ := hp
  exact hw' t ht hpD

/-- **Visibility is closed off the drawing.**  If `w` is a limit of points visible from `z`, and
`z`, `w` lie in the hull and off the drawing, then `w` is visible from `z`. -/
lemma vis_closed (hP : IsPlaneGraph V E) (hfan : FanCondition V E) {z w : ℂ}
    (hz : z ∉ drawing V E) (hw : w ∉ drawing V E) (hzK : z ∈ convexHull ℝ (V : Set ℂ))
    (hwK : w ∈ convexHull ℝ (V : Set ℂ))
    (hcl : w ∈ closure {w' : ℂ | Disjoint (segment ℝ z w') (drawing V E)}) :
    Disjoint (segment ℝ z w) (drawing V E) := by
  by_contra hmeet
  have hzw : z ≠ w := by
    rintro rfl; apply hmeet; rw [segment_same, Set.disjoint_singleton_left]; exact hz
  set D := drawing V E with hDdef
  set T := {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ z + t • (w - z) ∈ D}
  have hTne : T.Nonempty := by
    rw [Set.not_disjoint_iff] at hmeet
    obtain ⟨p, hp, hpD⟩ := hmeet
    rw [segment_eq_image'] at hp
    obtain ⟨t, ht, rfl⟩ := hp
    exact ⟨t, ht, hpD⟩
  have hTc : IsClosed T :=
    isClosed_Icc.inter ((isClosed_drawing V E).preimage (by fun_prop))
  have hTb : BddBelow T := ⟨0, fun t ht => ht.1.1⟩
  set t0 := sInf T
  have ht0 : t0 ∈ T := hTc.csInf_mem hTne hTb
  have hmin : ∀ t : ℝ, 0 ≤ t → t < t0 → z + t • (w - z) ∉ D := fun t h0 hlt hD =>
    (not_le.2 hlt) (csInf_le hTb ⟨⟨h0, by linarith [ht0.1.2]⟩, hD⟩)
  set y := z + t0 • (w - z) with hydef
  have hyD : y ∈ D := ht0.2
  have ht00 : t0 ≠ 0 := by
    intro h; apply hz; have := hyD; rw [hydef, h, zero_smul, add_zero] at this; exact this
  have ht01 : t0 ≠ 1 := by
    intro h; apply hw; have := hyD; rw [hydef, h, one_smul, add_sub_cancel] at this; exact this
  have hy : y ∈ openSegment ℝ z w := by
    rw [openSegment_eq_image']
    exact ⟨t0, ⟨lt_of_le_of_ne ht0.1.1 (Ne.symm ht00), lt_of_le_of_ne ht0.1.2 ht01⟩, rfl⟩
  have hwz : w - z ≠ 0 := sub_ne_zero.2 hzw.symm
  have hwcy : wc z w y = t0 := by
    rw [hydef, wc, Complex.real_smul, add_sub_cancel_left, mul_div_assoc, div_self hwz, mul_one]
  have hwcy0 : (wc z w y).im = 0 := by rw [hwcy]; simp
  have hseg : ∀ e ∈ E, edgeSeg e ⊆ D := fun e he x hx => Or.inr (Set.mem_iUnion₂.2 ⟨e, he, hx⟩)
  -- two points strictly on both sides of the line, joined to `y` inside the drawing
  have key : ∃ a b : ℂ, 0 < (wc z w a).im ∧ (wc z w b).im < 0 ∧ segment ℝ y a ⊆ D ∧
      segment ℝ y b ⊆ D := by
    by_cases hyV : y ∈ V
    · by_cases hext : y ∈ extremePoints ℝ (convexHull ℝ (V : Set ℂ))
      · exfalso
        have := ((mem_extremePoints.1 hext).2 z hzK w hwK hy).1
        exact hz (this ▸ hyD)
      · obtain ⟨y1, he1, h1⟩ := hfan y hyV hext (w - z) hwz
        obtain ⟨y2, he2, h2⟩ := hfan y hyV hext (-(w - z)) (neg_ne_zero.2 hwz)
        refine ⟨y1, y2, ?_, ?_, hseg _ he1, hseg _ he2⟩
        · rw [im_wc_of_real hwcy0]; exact h1
        · rw [im_wc_of_real hwcy0]
          rw [div_neg, neg_im] at h2
          linarith
    · have hyE : y ∈ ⋃ e ∈ E, edgeSeg e := by
        rcases hyD with h | h
        · exact absurd h hyV
        · exact h
      obtain ⟨e, he, hye⟩ := Set.mem_iUnion₂.1 hyE
      induction e using Sym2.ind with
      | _ p q =>
      have hp := hP.mem_V _ he p (Sym2.mem_mk_left _ _)
      have hq := hP.mem_V _ he q (Sym2.mem_mk_right _ _)
      rw [edgeSeg_mk] at hye
      have hyo : y ∈ openSegment ℝ p q :=
        mem_openSegment_of_ne' hye (fun h => hyV (h ▸ hp)) (fun h => hyV (h ▸ hq))
      obtain ⟨s, r, hs, hr, hsr, hyeq⟩ := hyo
      have hcomb := wc_combo (a := z) (b := w) p q s r hsr
      replace hwcy0 : (wc z w (s • p + r • q)).im = 0 := by rw [hyeq]; exact hwcy0
      rw [hcomb] at hwcy0
      simp only [add_im, im_ofReal_mul] at hwcy0
      have hpq : segment ℝ y p ⊆ D := fun x hx => hseg _ he
        ((convex_segment p q).segment_subset hye (left_mem_segment ℝ p q) hx)
      have hqq : segment ℝ y q ⊆ D := fun x hx => hseg _ he
        ((convex_segment p q).segment_subset hye (right_mem_segment ℝ p q) hx)
      rcases lt_trichotomy (wc z w p).im 0 with hA | hA | hA
      · refine ⟨q, p, ?_, hA, hqq, hpq⟩
        nlinarith
      · exfalso
        have hB : (wc z w q).im = 0 := by
          rw [hA, mul_zero, zero_add] at hwcy0
          rcases mul_eq_zero.1 hwcy0 with h | h
          · linarith
          · exact h
        -- the edge lies on the line `z w`: contradiction with the minimality of `t0`
        set tp := (wc z w p).re
        set tq := (wc z w q).re
        have hpe : p = z + tp • (w - z) := by
          have e1 := eq_param hzw p
          have hr' : wc z w p = (tp : ℂ) := Complex.ext (by simp [tp]) (by simp [hA])
          rw [Complex.real_smul]; conv_lhs => rw [e1, hr']
          ring
        have hqe : q = z + tq • (w - z) := by
          have e1 := eq_param hzw q
          have hr' : wc z w q = (tq : ℂ) := Complex.ext (by simp [tq]) (by simp [hB])
          rw [Complex.real_smul]; conv_lhs => rw [e1, hr']
          ring
        have ht0e : t0 = s * tp + r * tq := by
          have := congrArg Complex.re (hcomb.symm.trans (congrArg (wc z w) hyeq))
          rw [hwcy] at this
          simp only [add_re, re_ofReal_mul, ofReal_re] at this
          linarith
        have hne : tp ≠ tq := by
          intro h
          have : p = q := by rw [hpe, hqe, h]
          rw [this, segment_same] at hye
          exact hyV (hye ▸ hq)
        have hsp : s * tp + r * tp = tp := by rw [← add_mul, hsr, one_mul]
        have hsq : s * tq + r * tq = tq := by rw [← add_mul, hsr, one_mul]
        have hmn : min tp tq < t0 := by
          rcases lt_or_gt_of_ne hne with h | h
          · rw [min_eq_left h.le]; nlinarith [mul_pos hr (sub_pos.2 h)]
          · rw [min_eq_right h.le]; nlinarith [mul_pos hs (sub_pos.2 h)]
        have hmx : t0 < max tp tq := by
          rcases lt_or_gt_of_ne hne with h | h
          · rw [max_eq_right h.le]; nlinarith [mul_pos hs (sub_pos.2 h)]
          · rw [max_eq_left h.le]; nlinarith [mul_pos hr (sub_pos.2 h)]
        have ht0pos : 0 < t0 := lt_of_le_of_ne ht0.1.1 (Ne.symm ht00)
        set t := max (min tp tq) (t0 / 2)
        have ht1 : 0 ≤ t := le_trans (by linarith) (le_max_right _ _)
        have ht2 : t < t0 := max_lt hmn (by linarith)
        have ht3 : t ∈ Set.uIcc tp tq := by
          rw [Set.uIcc, Set.mem_Icc]
          exact ⟨le_max_left _ _, (ht2.trans hmx).le⟩
        refine hmin t ht1 ht2 (hseg _ he ?_)
        rw [edgeSeg_mk, hpe, hqe]
        exact mem_segment_line z (w - z) ht3
      · refine ⟨p, q, hA, ?_, hpq, hqq⟩
        nlinarith
  obtain ⟨a, b, ha, hb, hya, hyb⟩ := key
  have hev := cross_stable hzw hy ha hb
  obtain ⟨w', hw'1, hw'2⟩ := mem_closure_iff_nhds.1 hcl _ hev
  obtain ⟨c, hc1, hc2⟩ := hw'1
  exact Set.disjoint_left.1 hw'2 hc1 (hc2.elim (fun h => hya h) (fun h => hyb h))

/-- **Bounded faces are convex.** -/
theorem boundedFace_convex (hP : IsPlaneGraph V E) (hfan : FanCondition V E) {F : Set ℂ}
    (hF : F ∈ faces V E) (hb : Bornology.IsBounded F) : Convex ℝ F := by
  rw [convex_iff_segment_subset]
  intro z hzF w hwF
  have hFD := face_subset_compl hF
  have hFK := boundedFace_subset_hull hP hF hb
  set Vis := {w' : ℂ | Disjoint (segment ℝ z w') (drawing V E)}
  have hsub : F ⊆ Vis := by
    refine (isPreconnected_connectedComponentIn.subset_of_closure_inter_subset (isOpen_vis z)
      ?_ ?_ : connectedComponentIn (drawing V E)ᶜ z ⊆ Vis) |>.trans' ?_
    · refine ⟨z, mem_connectedComponentIn (hFD hzF), ?_⟩
      show Disjoint (segment ℝ z z) _
      rw [segment_same, Set.disjoint_singleton_left]; exact hFD hzF
    · rintro x ⟨hx1, hx2⟩
      exact vis_closed hP hfan (hFD hzF) (connectedComponentIn_subset _ _ hx2) (hFK hzF)
        (hFK ((face_eq_component hF hzF).symm ▸ hx2)) hx1
    · rw [← face_eq_component hF hzF]
  have hvis : Disjoint (segment ℝ z w) (drawing V E) := hsub hwF
  exact subset_face hF (convex_segment z w).isPreconnected
    (fun x hx hxD => Set.disjoint_left.1 hvis hx hxD) (left_mem_segment ℝ z w) hzF

end Vis2

end Erdos99

end

end FaceConvexity

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `FacePolygon`
-/

section FacePolygon

/-!
# Bounded faces with the fan property are convex polygons (Lemma 2.1)

Let `(V, E)` be a straight-line plane graph in `ℂ` with the fan property.  Every bounded face `F`
is convex (`boundedFace_convex`).  Here we show that it is the interior of the convex hull of a
finite set `S ⊆ V` of points in strictly convex position, and that the boundary edges of `F` are
exactly the sides of this polygon (`boundedFace_polygon`).
-/

open scoped BigOperators Real
open EstablishedExternalResults Set Complex Filter Topology

@[expose] public noncomputable section

open Classical

namespace Erdos99

/-- `[a, b]` is a counterclockwise side of the convex hull of the finite set `S`: all of `S` lies
weakly to the left of the directed line `a → b`. -/
def IsCSide (S : Finset ℂ) (a b : ℂ) : Prop :=
  a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ ∀ c ∈ S, 0 ≤ (wc a b c).im

/-- The sides of the convex polygon spanned by `S`, as unordered pairs. -/
def cSides (S : Finset ℂ) : Finset (Sym2 ℂ) :=
  ((S ×ˢ S).filter (fun p => IsCSide S p.1 p.2)).image (fun p => s(p.1, p.2))

/-! ## Convex geometry -/

lemma mem_openSegment_wc {a b m : ℂ} (hab : a ≠ b) (hm : m ∈ openSegment ℝ a b) :
    (wc a b m).im = 0 ∧ 0 < (wc a b m).re ∧ (wc a b m).re < 1 := by
  obtain ⟨s, r, hs, hr, hsr, rfl⟩ := hm
  have hne : b - a ≠ 0 := sub_ne_zero.2 hab.symm
  have h1 : wc a b a = 0 := by simp [wc]
  have h2 : wc a b b = 1 := by simp [wc, div_self hne]
  rw [wc_combo a b s r hsr, h1, h2]
  refine ⟨by simp, by simp [hr], by simp; linarith⟩

lemma wc_ne_of_im_pos {a b c : ℂ} (h : 0 < (wc a b c).im) : a ≠ b := by
  rintro rfl
  simp [wc] at h

lemma continuous_wc (a b : ℂ) : Continuous (wc a b) := by
  unfold wc
  exact (continuous_id.sub continuous_const).div_const _

lemma convex_wc_im_nonneg (a b : ℂ) : Convex ℝ {z : ℂ | 0 ≤ (wc a b z).im} := by
  intro x hx y hy s t hs ht hst
  show 0 ≤ (wc a b (s • x + t • y)).im
  rw [wc_combo x y s t hst, add_im, im_ofReal_mul, im_ofReal_mul]
  have hx' : 0 ≤ (wc a b x).im := hx
  have hy' : 0 ≤ (wc a b y).im := hy
  positivity

/-- **Half-disc lemma.**  If `F` is open and convex, `a, b ∈ closure F`, `m` lies strictly between
`a` and `b`, and `c ∈ F` lies strictly to the left of `a → b`, then all points near `m` strictly to
the left of `a → b` lie in `F`. -/
lemma halfdisc {F : Set ℂ} (hFc : Convex ℝ F) (hFo : IsOpen F) {a b c m : ℂ}
    (ha : a ∈ closure F) (hb : b ∈ closure F) (hc : c ∈ F) (hm : m ∈ openSegment ℝ a b)
    (hcpos : 0 < (wc a b c).im) : ∀ᶠ z in 𝓝 m, 0 < (wc a b z).im → z ∈ F := by
  have hab := wc_ne_of_im_pos hcpos
  obtain ⟨hm0, hm1, hm2⟩ := mem_openSegment_wc hab hm
  set γ := wc a b c with hγdef
  have hcont := continuous_wc a b
  set t : ℂ → ℝ := fun z => (wc a b z).im / γ.im with htdef
  set ω : ℂ → ℝ := fun z => ((wc a b z).re - t z * γ.re) / (1 - t z) with hωdef
  have ht : Continuous t := (continuous_im.comp hcont).div_const _
  have htm : t m = 0 := by simp [t, hm0]
  have hωc : ContinuousAt ω m := by
    apply ContinuousAt.div
    · exact ((continuous_re.comp hcont).sub (ht.mul continuous_const)).continuousAt
    · exact (continuous_const.sub ht).continuousAt
    · rw [htm]; norm_num
  have hωm : ω m = (wc a b m).re := by simp [ω, htm]
  have h1 : ∀ᶠ z in 𝓝 m, t z < 1 :=
    ht.continuousAt.eventually (gt_mem_nhds (by rw [htm]; norm_num))
  have h2 : ∀ᶠ z in 𝓝 m, ω z ∈ Ioo (0 : ℝ) 1 :=
    hωc.eventually (Ioo_mem_nhds (by rw [hωm]; exact hm1) (by rw [hωm]; exact hm2))
  filter_upwards [h1, h2] with z hz1 hz2 hzpos
  have htpos : 0 < t z := div_pos hzpos hcpos
  set w := a + (ω z : ℂ) * (b - a) with hwdef
  have hw : w ∈ closure F := by
    have hseg : segment ℝ a b ⊆ closure F := hFc.closure.segment_subset ha hb
    apply hseg
    rw [segment_eq_image']
    exact ⟨ω z, Ioo_subset_Icc_self hz2, by beta_reduce; rw [hwdef, Complex.real_smul]⟩
  have h1t : (1 - t z) ≠ 0 := by linarith
  have hwz : wc a b z = (t z : ℂ) * γ + ((1 - t z : ℝ) : ℂ) * (ω z : ℂ) := by
    apply Complex.ext
    · simp only [add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, hωdef]
      field_simp
      ring
    · simp only [add_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, mul_zero, htdef]
      field_simp
  have hz : z = (t z) • c + (1 - t z) • w := by
    have e1 := eq_param hab z
    have e2 := eq_param hab c
    rw [← hγdef] at e2
    calc z = a + (b - a) * wc a b z := e1
      _ = a + (b - a) * ((t z : ℂ) * γ + ((1 - t z : ℝ) : ℂ) * (ω z : ℂ)) := by rw [hwz]
      _ = t z • c + (1 - t z) • w := by
        rw [Complex.real_smul, Complex.real_smul, hwdef, e2]; push_cast; ring
  rw [hz]
  have hcI : c ∈ interior F := by rwa [hFo.interior_eq]
  have := hFc.combo_interior_closure_mem_interior hcI hw htpos (sub_nonneg.2 hz1.le)
    (add_sub_cancel _ _)
  rwa [hFo.interior_eq] at this

/-- An open nonempty set contains a point off any line. -/
lemma exists_off_line {F : Set ℂ} (hFo : IsOpen F) (hFne : F.Nonempty) {a b : ℂ} (hab : a ≠ b) :
    ∃ c ∈ F, (wc a b c).im ≠ 0 := by
  obtain ⟨c0, hc0⟩ := hFne
  by_cases h : (wc a b c0).im = 0
  · obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hFo c0 hc0
    have hne : b - a ≠ 0 := sub_ne_zero.2 hab.symm
    have hn : 0 < ‖b - a‖ := norm_pos_iff.2 hne
    set δ : ℝ := ε / (2 * ‖b - a‖)
    have hδ : 0 < δ := by positivity
    refine ⟨c0 + (δ : ℂ) * I * (b - a), hball ?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, norm_mul, norm_I,
        mul_one, Complex.norm_real, Real.norm_of_nonneg hδ.le]
      have : δ * ‖b - a‖ = ε / 2 := by simp only [δ]; field_simp
      rw [this]; linarith
    · have : wc a b (c0 + (δ : ℂ) * I * (b - a)) = wc a b c0 + (δ : ℂ) * I := by
        simp only [wc]; field_simp; ring
      rw [this, add_im, h]
      simp [hδ.ne']
  · exact ⟨c0, hc0, h⟩

/-- Every point of the interior of the hull lies strictly left of a counterclockwise side. -/
lemma side_pos {S : Finset ℂ} {a b : ℂ} (hs : IsCSide S a b) {c : ℂ}
    (hc : c ∈ interior (convexHull ℝ (S : Set ℂ))) : 0 < (wc a b c).im := by
  have hab := hs.2.2.1
  have hsub : convexHull ℝ (S : Set ℂ) ⊆ {z : ℂ | 0 ≤ (wc a b z).im} :=
    convexHull_min (fun z hz => hs.2.2.2 z hz) (convex_wc_im_nonneg a b)
  have h0 : 0 ≤ (wc a b c).im := hsub (interior_subset hc)
  rcases h0.lt_or_eq with h | h
  · exact h
  exfalso
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior c hc
  have hne : b - a ≠ 0 := sub_ne_zero.2 hab.symm
  have hn : 0 < ‖b - a‖ := norm_pos_iff.2 hne
  set δ : ℝ := ε / (2 * ‖b - a‖)
  have hδ : 0 < δ := by positivity
  have hmem : c - (δ : ℂ) * I * (b - a) ∈ interior (convexHull ℝ (S : Set ℂ)) := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul, norm_mul, norm_I,
      mul_one, Complex.norm_real, Real.norm_of_nonneg hδ.le]
    have : δ * ‖b - a‖ = ε / 2 := by simp only [δ]; field_simp
    rw [this]; linarith
  have := hsub (interior_subset hmem)
  have e : wc a b (c - (δ : ℂ) * I * (b - a)) = wc a b c - (δ : ℂ) * I := by
    simp only [wc]; field_simp; ring
  simp only [Set.mem_setOf_eq, e, sub_im, ← h] at this
  simp at this
  linarith

/-- A point of the hull, not in its interior and not in `S`, lies inside a side. -/
lemma exists_side_of_frontier {S : Finset ℂ} (hint : (interior (convexHull ℝ (S : Set ℂ))).Nonempty)
    {m : ℂ} (hm : m ∈ convexHull ℝ (S : Set ℂ)) (hmi : m ∉ interior (convexHull ℝ (S : Set ℂ)))
    (hmS : m ∉ S) : ∃ a b, IsCSide S a b ∧ m ∈ openSegment ℝ a b := by
  set K := convexHull ℝ (S : Set ℂ) with hKdef
  have hKcl : IsClosed K := S.finite_toSet.isCompact_convexHull.isClosed
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point (convex_convexHull ℝ _).interior
    isOpen_interior hmi
  have hKsub : K ⊆ closure (interior K) := by
    rw [(convex_convexHull ℝ _).closure_interior_eq_closure_of_nonempty_interior hint,
      hKcl.closure_eq]
  have hle : ∀ z ∈ K, f z ≤ f m := by
    intro z hz
    have : z ∈ closure {y | f y ≤ f m} := closure_mono (fun y hy => (hf y hy).le) (hKsub hz)
    rwa [(isClosed_le f.continuous continuous_const).closure_eq] at this
  obtain ⟨g, hg⟩ := hint
  have hfg := hf g hg
  set u : ℂ := ⟨f 1, f I⟩ with hudef
  have hfu : ∀ z, f z = ((starRingEnd ℂ) u * z).re := by
    intro z; rw [clm_C]; simp [u]; ring
  have hu : u ≠ 0 := by
    intro h; rw [hfu, hfu, h] at hfg; simp at hfg
  set d := I * u with hddef
  have hd : d ≠ 0 := mul_ne_zero I_ne_zero hu
  have hnu : 0 < normSq u := normSq_pos.2 hu
  have hdiv : ∀ z, (z / d).im = -(f z) / normSq u := by
    intro z
    rw [hfu, div_im, hddef]
    simp only [normSq_mul, normSq_I, one_mul, mul_re, mul_im, I_re, I_im, conj_re, conj_im]
    ring
  obtain ⟨w, hw0, hw1, hwm⟩ := Finset.mem_convexHull'.1 hm
  have hfS : ∀ y ∈ S, f y ≤ f m := fun y hy => hle y (subset_convexHull ℝ _ hy)
  have hfm : f m = ∑ y ∈ S, w y * f y := by
    rw [← hwm, map_sum]
    exact Finset.sum_congr rfl fun y _ => by rw [map_smul, smul_eq_mul]
  have hsum0 : ∑ y ∈ S, w y * (f m - f y) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul, ← hfm, sub_self]
  have hwz : ∀ y ∈ S, f y ≠ f m → w y = 0 := by
    intro y hy hne
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun y hy => mul_nonneg (hw0 y hy)
      (sub_nonneg.2 (hfS y hy)))).1 hsum0 y hy
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd (by linarith) hne
  set T := S.filter (fun y => f y = f m) with hTdef
  have hTne : T.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have : ∑ y ∈ S, w y = 0 := Finset.sum_eq_zero (fun y hy => hwz y hy (fun he => by
      have : y ∈ T := Finset.mem_filter.2 ⟨hy, he⟩
      rw [h] at this; simp at this))
    linarith
  set σ : ℂ → ℝ := fun y => ((y - m) / d).re with hσdef
  obtain ⟨a, haT, hamin⟩ := T.exists_min_image σ hTne
  obtain ⟨b, hbT, hbmax⟩ := T.exists_max_image σ hTne
  have hsumσ : ∑ y ∈ S, w y * σ y = 0 := by
    have h1 : ∑ y ∈ S, w y • ((y - m) / d) = 0 := by
      have : ∑ y ∈ S, w y • ((y - m) / d) = (∑ y ∈ S, w y • y - (∑ y ∈ S, w y) • m) / d := by
        rw [Finset.sum_smul, ← Finset.sum_sub_distrib, Finset.sum_div]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [← smul_sub, smul_div_assoc]
      rw [this, hwm, hw1, one_smul, sub_self, zero_div]
    have h2 := congrArg Complex.re h1
    simpa [σ, Complex.real_smul, Complex.re_sum] using h2
  have hσa : σ a ≤ 0 := by
    have h := Finset.sum_nonneg (s := S) (f := fun y => w y * (σ y - σ a)) (fun y hy => by
      by_cases hyT : f y = f m
      · exact mul_nonneg (hw0 y hy) (sub_nonneg.2 (hamin y (Finset.mem_filter.2 ⟨hy, hyT⟩)))
      · simp only; rw [hwz y hy hyT, zero_mul])
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, hsumσ] at h
    linarith
  have hσb : 0 ≤ σ b := by
    have h := Finset.sum_nonneg (s := S) (f := fun y => w y * (σ b - σ y)) (fun y hy => by
      by_cases hyT : f y = f m
      · exact mul_nonneg (hw0 y hy) (sub_nonneg.2 (hbmax y (Finset.mem_filter.2 ⟨hy, hyT⟩)))
      · simp only; rw [hwz y hy hyT, zero_mul])
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, hsumσ] at h
    linarith
  have hline : ∀ y ∈ T, y = m + (σ y : ℂ) * d := by
    intro y hy
    have hfy : f y = f m := (Finset.mem_filter.1 hy).2
    have him : ((y - m) / d).im = 0 := by
      rw [hdiv, map_sub, hfy, sub_self, neg_zero, zero_div]
    have : (y - m) / d = (σ y : ℂ) := Complex.ext (by simp [σ]) (by simp [him])
    rw [← this]; field_simp; ring
  have haS := (Finset.mem_filter.1 haT).1
  have hbS := (Finset.mem_filter.1 hbT).1
  have hfa : f a = f m := (Finset.mem_filter.1 haT).2
  have ea := hline a haT
  have eb := hline b hbT
  generalize σ a = α at ea hσa
  generalize σ b = β at eb hσb
  have hα : α < 0 := by
    rcases hσa.lt_or_eq with h | h
    · exact h
    · exfalso; apply hmS; rw [h] at ea; simp at ea; rw [← ea]; exact haS
  have hβ : 0 < β := by
    rcases hσb.lt_or_eq with h | h
    · exact h
    · exfalso; apply hmS; rw [← h] at eb; simp at eb; rw [← eb]; exact hbS
  have hfd : f d = 0 := by
    rw [hfu, hddef]; simp [mul_re, mul_im, conj_re, conj_im]; ring
  have hβα' : β - α ≠ 0 := by linarith
  have hβα : ((β - α : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hβα'
  refine ⟨a, b, ⟨haS, hbS, ?_, ?_⟩, ?_⟩
  · intro h
    rw [ea, eb] at h
    have : (α : ℂ) = β := mul_right_cancel₀ hd (add_left_cancel h)
    have : α = β := by exact_mod_cast this
    linarith
  · intro c hc
    have hba : b - a = ((β - α : ℝ) : ℂ) * d := by rw [ea, eb]; push_cast; ring
    rw [wc, hba, div_mul_eq_div_div_swap, Complex.div_ofReal_im, hdiv, map_sub, hfa]
    apply div_nonneg (div_nonneg _ hnu.le) (by linarith)
    linarith [hfS c hc]
  · refine ⟨β / (β - α), -α / (β - α), div_pos hβ (by linarith),
      div_pos (by linarith) (by linarith), by field_simp; ring, ?_⟩
    rw [Complex.real_smul, Complex.real_smul, ea, eb]
    have : ((β - α : ℝ) : ℂ) = (β : ℂ) - α := by push_cast; ring
    rw [this] at hβα
    push_cast
    field_simp
    ring

lemma wc_im_of_mem_segment {a b z : ℂ} (hz : z ∈ segment ℝ a b) : (wc a b z).im = 0 := by
  by_cases hab : a = b
  · subst hab; simp [wc]
  obtain ⟨s, r, hs, hr, hsr, rfl⟩ := hz
  have hne : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
  rw [wc_combo a b s r hsr]
  simp [wc, div_self hne]

lemma convex_wc_im_mul_pos (a b : ℂ) (k : ℝ) : Convex ℝ {z : ℂ | 0 < (wc a b z).im * k} := by
  intro x hx y hy s t hs ht hst
  show 0 < (wc a b (s • x + t • y)).im * k
  rw [wc_combo x y s t hst, add_im, im_ofReal_mul, im_ofReal_mul]
  have hx' : 0 < (wc a b x).im * k := hx
  have hy' : 0 < (wc a b y).im * k := hy
  rcases hs.eq_or_lt with h | h
  · subst h
    rw [zero_add] at hst
    subst hst
    simpa using hy'
  · nlinarith [mul_pos h hx', mul_nonneg ht hy'.le]

section Poly

variable {V : Finset ℂ} {E : Finset (Sym2 ℂ)}

/-- No segment of the drawing leaves a point of a side of a convex face into the face. -/
lemma no_segment_into {F : Set ℂ} (hF : F ∈ faces V E) (hFc : Convex ℝ F) {a b c x y : ℂ}
    (ha : a ∈ closure F) (hb : b ∈ closure F) (hc : c ∈ F) (hcpos : 0 < (wc a b c).im)
    (hx : x ∈ openSegment ℝ a b) (hy : 0 < (wc a b y).im) (hxy : segment ℝ x y ⊆ drawing V E) :
    False := by
  have hab := wc_ne_of_im_pos hcpos
  have hx0 := (mem_openSegment_wc hab hx).1
  obtain ⟨ε, hε, hP⟩ := Metric.eventually_nhds_iff.1
    (halfdisc hFc (isOpen_face hF) ha hb hc hx hcpos)
  set s : ℝ := min (1 / 2) (ε / (2 * (‖y - x‖ + 1)))
  have hs0 : 0 < s := lt_min (by norm_num) (by positivity)
  have hs1 : s ≤ 1 := (min_le_left _ _).trans (by norm_num)
  set z := x + (s : ℂ) * (y - x)
  have hzseg : z ∈ segment ℝ x y := by
    rw [segment_eq_image']; exact ⟨s, ⟨hs0.le, hs1⟩, by simp [z, Complex.real_smul]⟩
  have hzd : dist z x < ε := by
    rw [dist_eq_norm, show z - x = (s : ℂ) * (y - x) by simp [z], norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hs0.le]
    have h1 : s ≤ ε / (2 * (‖y - x‖ + 1)) := min_le_right _ _
    have h2 : 0 ≤ ‖y - x‖ := norm_nonneg _
    calc s * ‖y - x‖ ≤ ε / (2 * (‖y - x‖ + 1)) * ‖y - x‖ := by gcongr
      _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith
  have hzpos : 0 < (wc a b z).im := by
    rw [wc_affine, add_im, hx0, zero_add, im_ofReal_mul, sub_im, hx0, sub_zero]
    exact mul_pos hs0 hy
  exact face_subset_compl hF (hP hzd hzpos) (hxy hzseg)

/-- The extreme points of the closure of a bounded convex face are vertices. -/
lemma extremePoints_closure_face_subset (hP : IsPlaneGraph V E) {F : Set ℂ} (hF : F ∈ faces V E)
    (hFc : Convex ℝ F) {p : ℂ} (hp : p ∈ extremePoints ℝ (closure F)) : p ∈ V := by
  have hFo := isOpen_face hF
  have hFne : F.Nonempty := by
    obtain ⟨x, hx, rfl⟩ := mem_faces_iff.1 hF
    exact ⟨x, mem_connectedComponentIn hx⟩
  have hpK := hp.1
  have hext := (mem_extremePoints.1 hp).2
  -- a point strictly between two points of `closure F` is not extreme
  have hmid : ∀ d : ℂ, d ≠ 0 → p + d ∈ closure F → p - d ∈ closure F → False := by
    intro d hd h1 h2
    have hseg : p ∈ openSegment ℝ (p + d) (p - d) :=
      ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by
        rw [Complex.real_smul, Complex.real_smul]; push_cast; ring⟩
    have := (hext _ h1 _ h2 hseg).1
    exact hd (by linear_combination this)
  have hpF : p ∉ F := by
    intro hpF
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hFo p hpF
    have hd : ((ε / 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : ε / 2 ≠ 0)
    have hn : ‖((ε / 2 : ℝ) : ℂ)‖ < ε := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]; linarith
    refine hmid _ hd (subset_closure (hball ?_)) (subset_closure (hball ?_))
    · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]; exact hn
    · rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg]; exact hn
  have hpD := closure_face_diff hF hpK hpF
  by_contra hpV
  have hpE : p ∈ ⋃ e ∈ E, edgeSeg e := hpD.resolve_left hpV
  obtain ⟨e, he, hpe⟩ := Set.mem_iUnion₂.1 hpE
  set U := ((V : Set ℂ) ∪ ⋃ e' ∈ E.erase e, edgeSeg e')ᶜ with hUdef
  have hUo : IsOpen U := (V.finite_toSet.isClosed.union
    (((E.erase e).finite_toSet).isClosed_biUnion fun e' _ => isClosed_edgeSeg e')).isOpen_compl
  have hpU : p ∈ U := by
    rintro (h | h)
    · exact hpV h
    · obtain ⟨e', he', hpe'⟩ := Set.mem_iUnion₂.1 h
      obtain ⟨hne, he'E⟩ := Finset.mem_erase.1 he'
      exact hpV (hP.mem_V _ he p (hP.inter e he e' he'E (Ne.symm hne) p hpe hpe'))
  have hUD : ∀ z ∈ U, z ∈ drawing V E → z ∈ edgeSeg e := by
    intro z hzU hzD
    rcases hzD with h | h
    · exact absurd (Or.inl h) hzU
    · obtain ⟨e', he', hze'⟩ := Set.mem_iUnion₂.1 h
      by_cases hee : e' = e
      · rw [← hee]; exact hze'
      · exact absurd (Or.inr (Set.mem_iUnion₂.2 ⟨e', Finset.mem_erase.2 ⟨hee, he'⟩, hze'⟩)) hzU
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hUo p hpU
  induction e using Sym2.ind with
  | _ a b =>
  rw [edgeSeg_mk] at hpe
  have hab : a ≠ b := fun h => hP.not_diag _ he (by rw [h]; exact Sym2.mk_isDiag_iff.2 rfl)
  have hpo : p ∈ openSegment ℝ a b := mem_openSegment_of_ne' hpe
    (fun h => hpV (h ▸ hP.mem_V _ he a (Sym2.mem_mk_left _ _)))
    (fun h => hpV (h ▸ hP.mem_V _ he b (Sym2.mem_mk_right _ _)))
  have hp0 := (mem_openSegment_wc hab hpo).1
  obtain ⟨c, hcF, hc0⟩ := exists_off_line hFo hFne hab
  set k := (wc a b c).im with hkdef
  have hk2 : 0 < k ^ 2 := by positivity
  set B := Metric.ball p r ∩ {z : ℂ | 0 < (wc a b z).im * k} with hBdef
  have hBD : B ⊆ (drawing V E)ᶜ := by
    rintro z ⟨hz1, hz2⟩ hzD
    have h0 := wc_im_of_mem_segment (hUD z (hball hz1) hzD)
    simp only [Set.mem_setOf_eq, h0, zero_mul, lt_irrefl] at hz2
  have him : ∀ q : ℂ, ∀ η : ℝ, (wc a b q).im = 0 →
      (wc a b (q + (η : ℂ) * (c - p))).im * k = η * k ^ 2 := by
    intro q η hq
    have e_aff : wc a b (q + (η : ℂ) * (c - p)) = wc a b q + η * (wc a b c - wc a b p) := by
      simp only [wc]; ring
    rw [e_aff, add_im, hq, im_ofReal_mul, sub_im, hp0, ← hkdef]; ring
  have hsmall : ∀ q : ℂ, dist q p < r → (wc a b q).im = 0 → ∀ ε > 0, ∃ η : ℝ, 0 < η ∧ η < 1 ∧
      q + (η : ℂ) * (c - p) ∈ B ∧ dist (q + (η : ℂ) * (c - p)) q < ε := by
    intro q hq hq0 ε hε
    have hm : 0 < min ε (r - dist q p) := lt_min hε (sub_pos.2 hq)
    set η := min (1 / 2) (min ε (r - dist q p) / (2 * (‖c - p‖ + 1))) with hηdef
    have hη : 0 < η := lt_min (by norm_num) (by positivity)
    have hη1 : η < 1 := (min_le_left _ _).trans_lt (by norm_num)
    have hd : dist (q + (η : ℂ) * (c - p)) q = η * ‖c - p‖ := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg hη.le]
    have hlt : η * ‖c - p‖ < min ε (r - dist q p) := by
      have h0 : 0 ≤ ‖c - p‖ := norm_nonneg _
      have h1 : η ≤ min ε (r - dist q p) / (2 * (‖c - p‖ + 1)) := min_le_right _ _
      calc η * ‖c - p‖ ≤ min ε (r - dist q p) / (2 * (‖c - p‖ + 1)) * ‖c - p‖ := by gcongr
        _ < min ε (r - dist q p) := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith
    refine ⟨η, hη, hη1, ⟨?_, ?_⟩, ?_⟩
    · rw [Metric.mem_ball]
      calc _ ≤ dist (q + (η : ℂ) * (c - p)) q + dist q p := dist_triangle _ _ _
        _ < r := by rw [hd]; linarith [min_le_right ε (r - dist q p)]
    · show 0 < (wc a b (q + (η : ℂ) * (c - p))).im * k
      rw [him q η hq0]; positivity
    · rw [hd]; linarith [min_le_left ε (r - dist q p)]
  have hBF : B ⊆ F := by
    obtain ⟨η, hη, hη1, hB, -⟩ := hsmall p (by simp [hr]) hp0 1 one_pos
    have hcI : c ∈ interior F := by rwa [hFo.interior_eq]
    have hzF : p + (η : ℂ) * (c - p) ∈ F := by
      have hmem : p + (η : ℂ) * (c - p) ∈ openSegment ℝ c p :=
        ⟨η, 1 - η, hη, by linarith, by ring, by
          rw [Complex.real_smul, Complex.real_smul]; push_cast; ring⟩
      have := hFc.openSegment_interior_closure_subset_interior hcI hpK hmem
      rw [hFo.interior_eq] at this
      exact this
    exact subset_face hF ((convex_ball p r).inter (convex_wc_im_mul_pos a b k)).isPreconnected
      hBD hB hzF
  have hcl : ∀ q : ℂ, dist q p < r → (wc a b q).im = 0 → q ∈ closure F := by
    intro q hq hq0
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨η, -, -, hB, hd⟩ := hsmall q hq hq0 ε hε
    exact ⟨_, hBF hB, by rw [dist_comm]; exact hd⟩
  have hne : b - a ≠ 0 := sub_ne_zero.2 hab.symm
  have hn : 0 < ‖b - a‖ := norm_pos_iff.2 hne
  set δ : ℝ := r / (2 * ‖b - a‖) with hδdef
  have hδ : 0 < δ := by positivity
  have hdn : ‖(δ : ℂ) * (b - a)‖ < r := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hδ.le]
    have : δ * ‖b - a‖ = r / 2 := by rw [hδdef]; field_simp
    rw [this]; linarith
  refine hmid ((δ : ℂ) * (b - a)) (mul_ne_zero (by exact_mod_cast hδ.ne') hne) ?_ ?_
  · refine hcl _ (by rw [dist_eq_norm, add_sub_cancel_left]; exact hdn) ?_
    have : wc a b (p + (δ : ℂ) * (b - a)) = wc a b p + δ := by
      simp only [wc]; field_simp; ring
    rw [this, add_im, hp0]; simp
  · refine hcl _ (by rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]; exact hdn) ?_
    have : wc a b (p - (δ : ℂ) * (b - a)) = wc a b p - δ := by
      simp only [wc]; field_simp; ring
    rw [this, sub_im, hp0]; simp

/-- Sides of a convex face: no vertex lies inside a side, every edge through the inside of a side
is that side, and the side is an edge. -/
lemma side_edge (hP : IsPlaneGraph V E) (hfan : FanCondition V E) {F : Set ℂ}
    (hF : F ∈ faces V E) (hFc : Convex ℝ F) {S : Finset ℂ} (hSV : S ⊆ V)
    (hS : closure F = convexHull ℝ (S : Set ℂ)) {a b : ℂ} (hs : IsCSide S a b) :
    (∀ x ∈ openSegment ℝ a b, x ∉ V) ∧
    (∀ x ∈ openSegment ℝ a b, ∀ e ∈ E, x ∈ edgeOpenSeg e → e = s(a, b)) ∧ s(a, b) ∈ E := by
  have hFo := isOpen_face hF
  have hFne : F.Nonempty := by
    obtain ⟨x, hx, rfl⟩ := mem_faces_iff.1 hF
    exact ⟨x, mem_connectedComponentIn hx⟩
  have hab := hs.2.2.1
  have hne : b - a ≠ 0 := sub_ne_zero.2 hab.symm
  have hFint : F = interior (convexHull ℝ (S : Set ℂ)) := by
    rw [← hS, hFc.interior_closure_eq_interior_of_nonempty_interior
      (by rw [hFo.interior_eq]; exact hFne), hFo.interior_eq]
  obtain ⟨c, hcF⟩ := hFne
  have hcpos : 0 < (wc a b c).im := side_pos hs (hFint ▸ hcF)
  have haK : a ∈ closure F := hS ▸ subset_convexHull ℝ _ hs.1
  have hbK : b ∈ closure F := hS ▸ subset_convexHull ℝ _ hs.2.1
  have haV : a ∈ V := hSV hs.1
  have hbV : b ∈ V := hSV hs.2.1
  have hseg : ∀ e ∈ E, edgeSeg e ⊆ drawing V E := fun e he x hx =>
    Or.inr (Set.mem_iUnion₂.2 ⟨e, he, hx⟩)
  have hpar : ∀ y, (wc a b y).im = 0 → y = a + (wc a b y).re • (b - a) := by
    intro y hy
    have e1 := eq_param hab y
    have e2 : wc a b y = ((wc a b y).re : ℂ) := Complex.ext (by simp) (by simp [hy])
    rw [Complex.real_smul]
    conv_lhs => rw [e1, e2]
    ring
  have hwa : wc a b a = 0 := by simp [wc]
  have hwb : wc a b b = 1 := by simp [wc, div_self hne]
  -- (i) no vertex inside the side
  have hV : ∀ x ∈ openSegment ℝ a b, x ∉ V := by
    intro x hx hxV
    have hxa : x ≠ a := fun h => hab (left_mem_openSegment_iff.1 (h ▸ hx))
    have hext : x ∉ extremePoints ℝ (convexHull ℝ (V : Set ℂ)) := fun h =>
      hxa ((mem_extremePoints.1 h).2 a (subset_convexHull ℝ _ haV) b
        (subset_convexHull ℝ _ hbV) hx).1.symm
    obtain ⟨y', hE, hpos⟩ := hfan x hxV hext (b - a) hne
    have hx0 := (mem_openSegment_wc hab hx).1
    have hy' : 0 < (wc a b y').im := by
      have := wc_sub (a := a) (b := b) y' x
      rw [← this, sub_im, hx0, sub_zero] at hpos
      exact hpos
    exact no_segment_into hF hFc haK hbK hcF hcpos hx hy' (hseg _ hE)
  -- (ii) every edge through the inside of the side is the side
  have hE : ∀ x ∈ openSegment ℝ a b, ∀ e ∈ E, x ∈ edgeOpenSeg e → e = s(a, b) := by
    intro x hx e he hxe
    induction e using Sym2.ind with
    | _ p q =>
    rw [edgeOpenSeg_mk] at hxe
    have hpV := hP.mem_V _ he p (Sym2.mem_mk_left _ _)
    have hqV := hP.mem_V _ he q (Sym2.mem_mk_right _ _)
    have hxs := openSegment_subset_segment ℝ p q hxe
    have hp0 : (wc a b p).im ≤ 0 := by
      by_contra h
      push_neg at h
      exact no_segment_into hF hFc haK hbK hcF hcpos hx h (fun z hz => hseg _ he
        ((convex_segment p q).segment_subset hxs (left_mem_segment ℝ p q) hz))
    have hq0 : (wc a b q).im ≤ 0 := by
      by_contra h
      push_neg at h
      exact no_segment_into hF hFc haK hbK hcF hcpos hx h (fun z hz => hseg _ he
        ((convex_segment p q).segment_subset hxs (right_mem_segment ℝ p q) hz))
    obtain ⟨hx0, hx1, hx2⟩ := mem_openSegment_wc hab hx
    obtain ⟨s, r, hs0, hr0, hsr, hxeq⟩ := hxe
    have hcomb := wc_combo (a := a) (b := b) p q s r hsr
    rw [hxeq] at hcomb
    have him := congrArg Complex.im hcomb
    have hre := congrArg Complex.re hcomb
    simp only [add_im, im_ofReal_mul, add_re, re_ofReal_mul] at him hre
    have hpi : (wc a b p).im = 0 := by nlinarith
    have hqi : (wc a b q).im = 0 := by nlinarith
    set tp := (wc a b p).re
    set tq := (wc a b q).re
    have hpe := hpar p hpi
    have hqe := hpar q hqi
    have hnot : ∀ y ∈ V, (wc a b y).im = 0 → (wc a b y).re ≤ 0 ∨ 1 ≤ (wc a b y).re := by
      intro y hyV hy0
      by_contra h
      push_neg at h
      apply hV y _ hyV
      refine ⟨1 - (wc a b y).re, (wc a b y).re, by linarith, h.1, by ring, ?_⟩
      conv_rhs => rw [hpar y hy0]
      rw [Complex.real_smul, Complex.real_smul, Complex.real_smul]; push_cast; ring
    have hmemV : ∀ y ∈ V, y ∈ segment ℝ p q → y = p ∨ y = q := fun y hyV hy =>
      Sym2.mem_iff.1 (hP.vertex_mem _ he y hyV hy)
    rcases hnot p hpV hpi with hp | hp <;> rcases hnot q hqV hqi with hq | hq
    · nlinarith
    · have haS : a ∈ segment ℝ p q := by
        have h := mem_segment_line a (b - a) (a := tp) (b := tq) (t := 0) (Set.mem_uIcc.2 (Or.inl ⟨hp, by linarith⟩))
        rw [← hpe, ← hqe, zero_smul, add_zero] at h
        exact h
      have hbS : b ∈ segment ℝ p q := by
        have h := mem_segment_line a (b - a) (a := tp) (b := tq) (t := 1) (Set.mem_uIcc.2 (Or.inl ⟨by linarith, hq⟩))
        rw [← hpe, ← hqe, one_smul, add_sub_cancel] at h
        exact h
      have h1 : a = p := by
        rcases hmemV a haV haS with h | h
        · exact h
        · exfalso; have : tq = 0 := by simp only [tq, ← h, hwa, zero_re]
          linarith
      have h2 : b = q := by
        rcases hmemV b hbV hbS with h | h
        · exfalso; have : tp = 1 := by simp only [tp, ← h, hwb, one_re]
          linarith
        · exact h
      rw [h1, h2]
    · have haS : a ∈ segment ℝ p q := by
        have h := mem_segment_line a (b - a) (a := tp) (b := tq) (t := 0) (Set.mem_uIcc.2 (Or.inr ⟨hq, by linarith⟩))
        rw [← hpe, ← hqe, zero_smul, add_zero] at h
        exact h
      have hbS : b ∈ segment ℝ p q := by
        have h := mem_segment_line a (b - a) (a := tp) (b := tq) (t := 1) (Set.mem_uIcc.2 (Or.inr ⟨by linarith, hp⟩))
        rw [← hpe, ← hqe, one_smul, add_sub_cancel] at h
        exact h
      have h1 : a = q := by
        rcases hmemV a haV haS with h | h
        · exfalso; have : tp = 0 := by simp only [tp, ← h, hwa, zero_re]
          linarith
        · exact h
      have h2 : b = p := by
        rcases hmemV b hbV hbS with h | h
        · exact h
        · exfalso; have : tq = 1 := by simp only [tq, ← h, hwb, one_re]
          linarith
      rw [h1, h2, Sym2.eq_swap]
    · nlinarith
  refine ⟨hV, hE, ?_⟩
  -- (iii) the side is an edge
  set m := (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b with hmdef
  have hm : m ∈ openSegment ℝ a b := ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
  have hmK : m ∈ closure F := hFc.closure.segment_subset haK hbK (openSegment_subset_segment ℝ a b hm)
  have hmF : m ∉ F := by
    intro h
    have := side_pos hs (hFint ▸ h)
    rw [(mem_openSegment_wc hab hm).1] at this
    exact lt_irrefl _ this
  have hmD := closure_face_diff hF hmK hmF
  have hmV := hV m hm
  obtain ⟨e, he, hme⟩ := Set.mem_iUnion₂.1 (hmD.resolve_left hmV)
  have := hE m hm e he (by
    induction e using Sym2.ind with
    | _ p q =>
    rw [edgeSeg_mk] at hme
    rw [edgeOpenSeg_mk]
    exact mem_openSegment_of_ne' hme
      (fun h => hmV (h ▸ hP.mem_V _ he p (Sym2.mem_mk_left _ _)))
      (fun h => hmV (h ▸ hP.mem_V _ he q (Sym2.mem_mk_right _ _))))
  rw [← this]; exact he

/-- **Lemma 2.1 (faces are convex polygons).**  A bounded face of a plane graph with the fan
property is the interior of the convex hull of a set `S` of vertices in strictly convex position,
and its boundary edges are exactly the sides of this polygon. -/
theorem boundedFace_polygon (hP : IsPlaneGraph V E) (hfan : FanCondition V E) {F : Set ℂ}
    (hF : F ∈ faces V E) (hb : Bornology.IsBounded F) :
    ∃ S : Finset ℂ, S ⊆ V ∧ (∀ s ∈ S, s ∈ extremePoints ℝ (convexHull ℝ (S : Set ℂ))) ∧
      F = interior (convexHull ℝ (S : Set ℂ)) ∧ bdryEdges E F = cSides S := by
  have hFo := isOpen_face hF
  have hFc := boundedFace_convex hP hfan hF hb
  have hFne : F.Nonempty := by
    obtain ⟨x, hx, rfl⟩ := mem_faces_iff.1 hF
    exact ⟨x, mem_connectedComponentIn hx⟩
  set K := closure F with hKdef
  have hKc : IsCompact K := hb.isCompact_closure
  have hKconv : Convex ℝ K := hFc.closure
  set S := V.filter (fun x => x ∈ extremePoints ℝ K) with hSdef
  have hSe : (S : Set ℂ) = extremePoints ℝ K := by
    ext x
    simp only [hSdef, Finset.coe_filter, Set.mem_setOf_eq]
    exact ⟨fun h => h.2, fun h => ⟨extremePoints_closure_face_subset hP hF hFc h, h⟩⟩
  have hKS : K = convexHull ℝ (S : Set ℂ) := by
    have h1 := closure_convexHull_extremePoints hKc hKconv
    rw [← hSe, (S.finite_toSet.isCompact_convexHull.isClosed).closure_eq] at h1
    exact h1.symm
  have hFint : F = interior (convexHull ℝ (S : Set ℂ)) := by
    rw [← hKS, hKdef, hFc.interior_closure_eq_interior_of_nonempty_interior
      (by rw [hFo.interior_eq]; exact hFne), hFo.interior_eq]
  refine ⟨S, Finset.filter_subset _ _, ?_, hFint, ?_⟩
  · intro x hx
    rw [← hKS, ← hSe]; exact hx
  ext e
  simp only [bdryEdges, Finset.mem_filter]
  constructor
  · rintro ⟨heE, m, hm1, hm2⟩
    induction e using Sym2.ind with
    | _ p q =>
    have hpq : p ≠ q := fun h => hP.not_diag _ heE (by rw [h]; exact Sym2.mk_isDiag_iff.2 rfl)
    rw [edgeOpenSeg_mk] at hm1
    have hmD : m ∈ drawing V E :=
      Or.inr (Set.mem_iUnion₂.2 ⟨s(p, q), heE, openSegment_subset_segment ℝ p q hm1⟩)
    have hmF : m ∉ F := fun h => face_subset_compl hF h hmD
    have hmS : m ∉ S := by
      intro h
      have hmV : m ∈ V := Finset.mem_of_mem_filter _ h
      have := hP.vertex_mem _ heE m hmV (openSegment_subset_segment ℝ p q hm1)
      rcases Sym2.mem_iff.1 this with rfl | rfl
      · exact hpq (left_mem_openSegment_iff.1 hm1)
      · exact hpq (right_mem_openSegment_iff.1 hm1)
    obtain ⟨a, b, hs, hmab⟩ := exists_side_of_frontier (hFint ▸ hFne) (hKS ▸ hm2)
      (hFint ▸ hmF) hmS
    have := (side_edge hP hfan hF hFc (Finset.filter_subset _ _) hKS hs).2.1 m hmab _ heE hm1
    rw [this]
    exact Finset.mem_image.2 ⟨(a, b), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hs.1, hs.2.1⟩, hs⟩,
      rfl⟩
  · intro he
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.1 he
    have hs : IsCSide S a b := (Finset.mem_filter.1 hab).2
    refine ⟨(side_edge hP hfan hF hFc (Finset.filter_subset _ _) hKS hs).2.2, (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b, ?_, ?_⟩
    · rw [edgeOpenSeg_mk]; exact ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
    · show _ ∈ K
      rw [hKS]
      exact (convex_convexHull ℝ _) (subset_convexHull ℝ _ hs.1) (subset_convexHull ℝ _ hs.2.1)
        (by norm_num) (by norm_num) (by norm_num)

end Poly

end Erdos99

end

end FacePolygon

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `ContactFan`
-/

section ContactFan

/-!
# The fan property of the contact graph (Lemma 2.1)

Under finite multiplicity, every point of an optimal set `X` which is not a vertex of the convex
hull has, for every direction, a unit neighbour strictly on that side.  Otherwise moving that one
point in the opposite direction would not shorten any unit pair and would not touch any diameter
pair (a point with a diameter partner is a hull vertex), contradicting the strict first-order
release `false_of_strict_velocity`.

Consequently the bounded faces of the contact graph, and of the augmented graph, are convex.
-/

open scoped BigOperators Real
open EstablishedExternalResults Set Complex Filter Topology

@[expose] public noncomputable section

open Classical

namespace Erdos99

lemma inner_I_mul_eq (d ν : ℂ) : inner ℝ d (I * ν) = (d * (starRingEnd ℂ) ν).im := by
  rw [Complex.inner]
  simp only [mul_re, mul_im, conj_re, conj_im, I_re, I_im]
  ring

lemma div_im_pos_iff {d ν : ℂ} (hν : ν ≠ 0) :
    0 < (d / ν).im ↔ 0 < (d * (starRingEnd ℂ) ν).im := by
  have hn : 0 < normSq ν := normSq_pos.2 hν
  rw [div_im]
  simp only [mul_im, conj_re, conj_im]
  constructor
  · intro h
    have : 0 < (d.im * ν.re - d.re * ν.im) / normSq ν := by
      rw [sub_div]; linarith
    have := (div_pos_iff_of_pos_right hn).1 this
    linarith
  · intro h
    have : 0 < (d.im * ν.re - d.re * ν.im) / normSq ν := div_pos (by linarith) hn
    rw [sub_div] at this; linarith

lemma mem_hullVertices_of_isHV {X : Finset Plane} {x : Plane} (hx : x ∈ X)
    (h : toC x ∈ extremePoints ℝ (convexHull ℝ ((cVerts X : Finset ℂ) : Set ℂ))) :
    x ∈ hullVertices X := by
  refine Finset.mem_filter.2 ⟨hx, ?_⟩
  have e : toC.symm '' convexHull ℝ (toC '' (X : Set Plane)) =
      convexHull ℝ (toC.symm '' (toC '' (X : Set Plane))) :=
    LinearMap.image_convexHull toC.symm.toLinearEquiv.toLinearMap _
  have h1 : toC.symm (toC x) ∈ toC.symm '' extremePoints ℝ
      (convexHull ℝ (toC '' (X : Set Plane))) := ⟨toC x, by
        rw [cVerts, Finset.coe_image] at h; exact h, rfl⟩
  rw [image_extremePoints, e, Set.image_image] at h1
  simpa using h1

/-- **Fan property of the contact graph** (Lemma 2.1). -/
theorem cUnitEdges_fan {n : ℕ} (hn : 2 ≤ n) (hfm : numOptimalClasses n < ⊤) {X : Finset Plane}
    (hX : IsOptimal n X) : FanCondition (cVerts X) (cUnitEdges X) := by
  intro y hy hext ν hν
  by_contra hno
  push_neg at hno
  have hyX : toC.symm y ∈ X := mem_cVerts.1 hy
  set x := toC.symm y with hxdef
  have hyx : toC x = y := by simp [hxdef]
  have hxH : x ∉ hullVertices X := fun h => hext (hyx ▸ isHV_toC h)
  set w : Plane := toC.symm (I * ν)
  have hw : w ≠ 0 := by
    simp only [w, ne_eq, LinearIsometryEquiv.map_eq_zero_iff, mul_eq_zero, I_ne_zero, false_or]
    exact hν
  refine false_of_strict_velocity hn hfm hX (fun p => if p = x then w else 0) ?_ ?_ ?_
  · -- no unit pair is shortened
    have key : ∀ q ∈ X, dist x q = 1 → 0 ≤ inner ℝ (x - q) w := by
      intro q hq hd
      have hE : s(y, toC q) ∈ cUnitEdges X := by
        rw [cUnitEdges, mem_unitPairs]
        refine ⟨hy, Finset.mem_image_of_mem _ hq, ?_⟩
        rw [← hyx, dist_toC]; exact hd
      have h1 := hno (toC q) hE
      have h2 : ¬ 0 < ((toC q - y) * (starRingEnd ℂ) ν).im := fun h =>
        (not_lt.2 h1) ((div_im_pos_iff hν).2 h)
      have h3 : inner ℝ (q - x) w = inner ℝ (toC q - y) (I * ν) := by
        rw [← toC.inner_map_map, map_sub, hyx]; simp [w]
      rw [inner_I_mul_eq] at h3
      rw [← neg_sub, inner_neg_left]
      linarith [not_lt.1 h2]
    intro p hp q hq hd
    beta_reduce
    by_cases hpx : p = x
    · have hqx : q ≠ x := by rintro rfl; rw [hpx] at hd; simp at hd
      rw [if_pos hpx, if_neg hqx, sub_zero, hpx]
      exact key q hq (hpx ▸ hd)
    · by_cases hqx : q = x
      · rw [if_neg hpx, if_pos hqx, zero_sub, inner_neg_right, hqx]
        have := key p hp (by rw [dist_comm, ← hqx]; exact hd)
        rw [← neg_sub, inner_neg_left] at this
        linarith
      · simp [hpx, hqx]
  · -- diameter pairs avoid `x`
    intro p hp q hq hd
    left
    have hpq : p ≠ q := by
      rintro rfl; simp at hd; exact (hX.diam_pos hn).ne' hd.symm
    have hpx : p ≠ x := by
      rintro rfl; exact hxH (mem_hullVertices_of_diam hp hq hpq hd)
    have hqx : q ≠ x := by
      rintro rfl; exact hxH (mem_hullVertices_of_diam hq hp hpq.symm (by rw [dist_comm]; exact hd))
    simp [hpx, hqx]
  · -- the velocity is not constant
    have hcard : 1 < X.card := by rw [hX.1.1]; omega
    obtain ⟨q, hq, hqx⟩ := Finset.exists_mem_ne hcard x
    exact ⟨x, hyX, q, hq, by simp [hqx, hw]⟩

lemma FanCondition.mono {V : Finset ℂ} {E E' : Finset (Sym2 ℂ)} (h : FanCondition V E)
    (hEE : E ⊆ E') : FanCondition V E' := by
  intro y hy hext ν hν
  obtain ⟨y', h1, h2⟩ := h y hy hext ν hν
  exact ⟨y', hEE h1, h2⟩

/-- Fan property of the augmented graph. -/
theorem augEdges_fan {n : ℕ} (hn : 2 ≤ n) (hfm : numOptimalClasses n < ⊤) {X : Finset Plane}
    (hX : IsOptimal n X) : FanCondition (cVerts X) (augEdges X) :=
  (cUnitEdges_fan hn hfm hX).mono Finset.subset_union_left

/-- **Lemma 2.1: every bounded face of the contact graph is convex.** -/
theorem contactFace_convex :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      ∀ F ∈ contactFaces X, Convex ℝ F := by
  filter_upwards [eventually_ge_atTop 2] with n hn hfm X hX F hF
  exact boundedFace_convex (cUnitEdges_isPlaneGraph hX.1.2) (cUnitEdges_fan hn hfm hX) hF.1 hF.2

/-- Every bounded face of the augmented graph (old faces and caps) is convex. -/
theorem augFace_convex :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      ∀ F ∈ augFaces X, Convex ℝ F := by
  filter_upwards [augEdges_isPlaneGraph, eventually_ge_atTop 2] with n hP hn hfm X hX F hF
  exact boundedFace_convex (hP hfm X hX) (augEdges_fan hn hfm hX) hF.1 hF.2


/-! ## Counting the sides of a convex polygon -/

lemma toC_eq (x : Plane) : toC x = (x 0 : ℂ) + (x 1 : ℂ) * I := by
  simp [toC, Complex.orthonormalBasisOneI]

lemma im_wc_toC (v w y : Plane) :
    (wc (toC v) (toC w) (toC y)).im = det2 (w - v) (y - v) / normSq (toC w - toC v) := by
  rw [wc, div_im, toC_eq, toC_eq, toC_eq]
  simp [det2, normSq_apply]
  ring

lemma wc_im_swap (a b c : ℂ) : (wc b a c).im = -(wc a b c).im := by
  by_cases h : a = b
  · subst h; simp [wc]
  have h1 : a - b ≠ 0 := sub_ne_zero.2 h
  have h2 : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  have : wc b a c = 1 - wc a b c := by
    simp only [wc]; field_simp; ring
  rw [this, sub_im, one_im, zero_sub]

/-- A finite set on a line spans a hull with empty interior. -/
lemma not_interior_of_line {S : Finset ℂ} {a b : ℂ} (hab : a ≠ b)
    (h : ∀ c ∈ S, (wc a b c).im = 0) : ¬ (interior (convexHull ℝ (S : Set ℂ))).Nonempty := by
  intro hne
  obtain ⟨c, hc, hc0⟩ := exists_off_line isOpen_interior hne hab
  have hsub : convexHull ℝ (S : Set ℂ) ⊆ {z | (wc a b z).im = 0} := by
    refine convexHull_min (fun z hz => h z hz) ?_
    intro x hx y hy s t hs ht hst
    have hx' : (wc a b x).im = 0 := hx
    have hy' : (wc a b y).im = 0 := hy
    show (wc a b (s • x + t • y)).im = 0
    rw [wc_combo x y s t hst, add_im, im_ofReal_mul, im_ofReal_mul, hx', hy']
    ring
  exact hc0 (hsub (interior_subset hc))

lemma three_le_card_of_interior {S : Finset ℂ}
    (hne : (interior (convexHull ℝ (S : Set ℂ))).Nonempty) : 3 ≤ S.card := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨a, b, hab, hS⟩ : ∃ a b : ℂ, a ≠ b ∧ ∀ c ∈ S, c = a ∨ c = b := by
    interval_cases h : S.card
    · rw [Finset.card_eq_zero] at h; exact ⟨0, 1, zero_ne_one, by simp [h]⟩
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 h; exact ⟨a, a + 1, by simp, by simp⟩
    · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 h; exact ⟨a, b, hab, by simp⟩
  refine not_interior_of_line hab (fun c hc => ?_) hne
  have hne : b - a ≠ 0 := sub_ne_zero.2 hab.symm
  rcases hS c hc with h | h <;> rw [h]
  · simp [wc]
  · simp [wc, div_self hne]

lemma cVerts_image_symm (S : Finset ℂ) : cVerts (S.image toC.symm) = S := by
  rw [cVerts, Finset.image_image]
  simp [Function.comp_def]

/-- A convex polygon in strictly convex position has as many sides as vertices. -/
theorem card_cSides {S : Finset ℂ}
    (hext : ∀ s ∈ S, s ∈ extremePoints ℝ (convexHull ℝ (S : Set ℂ)))
    (hint : (interior (convexHull ℝ (S : Set ℂ))).Nonempty) : (cSides S).card = S.card := by
  set P := S.image toC.symm with hPdef
  have hcP : cVerts P = S := cVerts_image_symm S
  have hPcard : P.card = S.card := Finset.card_image_of_injective _ toC.symm.injective
  have hmemP : ∀ v, v ∈ P ↔ toC v ∈ S := by
    intro v
    rw [hPdef, Finset.mem_image]
    constructor
    · rintro ⟨z, hz, rfl⟩; simpa using hz
    · intro h; exact ⟨toC v, h, by simp⟩
  have hhv : hullVertices P = P := by
    apply Finset.filter_true_of_mem
    intro x hx
    have := mem_hullVertices_of_isHV hx (by rw [hcP]; exact hext _ ((hmemP x).1 hx))
    exact (Finset.mem_filter.1 this).2
  have h3 : 3 ≤ (hullVertices P).card := by
    rw [hhv, hPcard]; exact three_le_card_of_interior hint
  have hside : ∀ v w : Plane, IsCcwHullSide P v w ↔ IsCSide S (toC v) (toC w) := by
    intro v w
    unfold IsCcwHullSide IsCSide
    rw [hhv, hmemP, hmemP]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      have hn : 0 < normSq (toC w - toC v) :=
        normSq_pos.2 (sub_ne_zero.2 (fun h => h3 (toC.injective h).symm))
      refine ⟨h1, h2, fun h => h3 (toC.injective h), fun c hc => ?_⟩
      have hc' : toC.symm c ∈ P := (hmemP _).2 (by simpa using hc)
      have := im_wc_toC v w (toC.symm c)
      rw [LinearIsometryEquiv.apply_symm_apply] at this
      rw [this]
      exact div_nonneg (h4 _ hc') hn.le
    · rintro ⟨h1, h2, h3, h4⟩
      have hn : 0 < normSq (toC w - toC v) := normSq_pos.2 (sub_ne_zero.2 (Ne.symm h3))
      refine ⟨h1, h2, fun h => h3 (by rw [h]), fun y hy => ?_⟩
      have := h4 _ ((hmemP y).1 hy)
      rw [im_wc_toC] at this
      exact (div_nonneg_iff.1 this).elim (fun h => h.1) (fun h => absurd h.2 (not_le.2 hn))
  set OS := (S ×ˢ S).filter (fun p => IsCSide S p.1 p.2) with hOS
  have h1 : OS.card = (ccwHullSides P).card := by
    symm
    refine Finset.card_bij (fun p _ => (toC p.1, toC p.2)) ?_ ?_ ?_
    · intro p hp
      have := (hside _ _).1 (mem_ccwHullSides.1 hp)
      exact Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨this.1, this.2.1⟩, this⟩
    · intro p _ q _ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (toC.injective h.1) (toC.injective h.2)
    · intro q hq
      have hq' := (Finset.mem_filter.1 hq).2
      refine ⟨(toC.symm q.1, toC.symm q.2), mem_ccwHullSides.2 ((hside _ _).2 (by simpa using hq')),
        by simp⟩
  have h2 : (cSides S).card = OS.card := by
    apply Finset.card_image_of_injOn
    rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' h
    have hs : IsCSide S a b := (Finset.mem_filter.1 hab).2
    have hs' : IsCSide S a' b' := (Finset.mem_filter.1 hab').2
    simp only at h
    rcases Sym2.eq_iff.1 h with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2]
    · exfalso
      subst e1 e2
      refine not_interior_of_line hs.2.2.1 (fun c hc => ?_) hint
      have f1 := hs.2.2.2 c hc
      have f2 := hs'.2.2.2 c hc
      rw [wc_im_swap] at f2
      linarith
  rw [h2, h1, card_ccwHullSides h3, hhv, hPcard]

/-! ## Faces of the contact graph and of the augmented graph -/

/-- **Lemma 2.1 (faces are convex unit polygons).**  Every bounded face `F` of the contact graph is
the interior of the convex hull of a set `S` of at least three points of `X`, in strictly convex
position; the boundary unit edges of `F` are exactly the sides of this polygon, so `F` is a
convex unit `k`-gon with `k = faceSize X F = |S|`. -/
theorem contactFace_polygon :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      ∀ F ∈ contactFaces X, ∃ S : Finset ℂ, S ⊆ cVerts X ∧ 3 ≤ S.card ∧
        (∀ s ∈ S, s ∈ extremePoints ℝ (convexHull ℝ (S : Set ℂ))) ∧
        F = interior (convexHull ℝ (S : Set ℂ)) ∧ bdryEdges (cUnitEdges X) F = cSides S ∧
        faceSize X F = S.card := by
  filter_upwards [eventually_ge_atTop 2] with n hn hfm X hX F hF
  obtain ⟨S, hSV, hext, hFint, hbd⟩ :=
    boundedFace_polygon (cUnitEdges_isPlaneGraph hX.1.2) (cUnitEdges_fan hn hfm hX) hF.1 hF.2
  have hFne : F.Nonempty := by
    obtain ⟨x, hx, rfl⟩ := mem_faces_iff.1 hF.1
    exact ⟨x, mem_connectedComponentIn hx⟩
  have hint : (interior (convexHull ℝ (S : Set ℂ))).Nonempty := hFint ▸ hFne
  refine ⟨S, hSV, three_le_card_of_interior hint, hext, hFint, hbd, ?_⟩
  rw [faceSize, hbd, card_cSides hext hint]

/-- **Lemma 2.1 for the augmented graph.**  Every bounded face of the augmented graph (an old face
or a cap) is the interior of a convex polygon with vertices in `X`, in strictly convex position,
whose sides are exactly its boundary edges (unit edges and hull sides). -/
theorem augFace_polygon :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      ∀ F ∈ augFaces X, ∃ S : Finset ℂ, S ⊆ cVerts X ∧ 3 ≤ S.card ∧
        (∀ s ∈ S, s ∈ extremePoints ℝ (convexHull ℝ (S : Set ℂ))) ∧
        F = interior (convexHull ℝ (S : Set ℂ)) ∧ bdryEdges (augEdges X) F = cSides S ∧
        (bdryEdges (augEdges X) F).card = S.card := by
  filter_upwards [augEdges_isPlaneGraph, eventually_ge_atTop 2] with n hP hn hfm X hX F hF
  obtain ⟨S, hSV, hext, hFint, hbd⟩ :=
    boundedFace_polygon (hP hfm X hX) (augEdges_fan hn hfm hX) hF.1 hF.2
  have hFne : F.Nonempty := by
    obtain ⟨x, hx, rfl⟩ := mem_faces_iff.1 hF.1
    exact ⟨x, mem_connectedComponentIn hx⟩
  have hint : (interior (convexHull ℝ (S : Set ℂ))).Nonempty := hFint ▸ hFne
  refine ⟨S, hSV, three_le_card_of_interior hint, hext, hFint, hbd, ?_⟩
  rw [hbd, card_cSides hext hint]


/-! ## Old faces and caps -/

lemma isCSide_of_ccw {X : Finset Plane} {v w : Plane} (hs : IsCcwHullSide X v w) :
    IsCSide (cVerts X) (toC v) (toC w) := by
  have hvX := mem_of_mem_hullVertices hs.1
  have hwX := mem_of_mem_hullVertices hs.2.1
  have hn : 0 < normSq (toC w - toC v) :=
    normSq_pos.2 (sub_ne_zero.2 (fun h => hs.2.2.1 (toC.injective h).symm))
  refine ⟨Finset.mem_image_of_mem _ hvX, Finset.mem_image_of_mem _ hwX,
    fun h => hs.2.2.1 (toC.injective h), fun c hc => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hc
  rw [im_wc_toC]
  exact div_nonneg (hs.2.2.2 y hy) hn.le

lemma drawing_mono {V : Finset ℂ} {E E' : Finset (Sym2 ℂ)} (h : E ⊆ E') :
    drawing V E ⊆ drawing V E' := by
  rintro z (hz | hz)
  · exact Or.inl hz
  · obtain ⟨e, he, hze⟩ := Set.mem_iUnion₂.1 hz
    exact Or.inr (Set.mem_iUnion₂.2 ⟨e, h he, hze⟩)

/-- Points of the interior of the hull avoid the hull sides. -/
lemma not_mem_hullSide_of_interior {X : Finset Plane} {e : Sym2 ℂ} (he : e ∈ hullSideEdges X)
    {z : ℂ} (hz : z ∈ interior (convexHull ℝ ((cVerts X : Finset ℂ) : Set ℂ))) :
    z ∉ edgeSeg e := by
  obtain ⟨v, w, hs, rfl⟩ := hullSideEdges_cases he
  intro hze
  rw [edgeSeg_mk] at hze
  have h1 := side_pos (isCSide_of_ccw hs) hz
  rw [wc_im_of_mem_segment hze] at h1
  exact lt_irrefl _ h1

/-- The bounded faces of the contact graph are faces of the augmented graph. -/
theorem contactFaces_subset_augFaces :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      contactFaces X ⊆ augFaces X := by
  filter_upwards with n _ X hX F hF
  have hP := cUnitEdges_isPlaneGraph hX.1.2
  have hFint : F ⊆ interior (convexHull ℝ ((cVerts X : Finset ℂ) : Set ℂ)) :=
    interior_maximal (boundedFace_subset_hull hP hF.1 hF.2) (isOpen_face hF.1)
  have hFaug : F ⊆ (drawing (cVerts X) (augEdges X))ᶜ := by
    intro z hz hzD
    rcases hzD with h | h
    · exact face_subset_compl hF.1 hz (Or.inl h)
    · obtain ⟨e, he, hze⟩ := Set.mem_iUnion₂.1 h
      rcases Finset.mem_union.1 he with he | he
      · exact face_subset_compl hF.1 hz (Or.inr (Set.mem_iUnion₂.2 ⟨e, he, hze⟩))
      · exact not_mem_hullSide_of_interior he (hFint hz) hze
  obtain ⟨z0, hz0, hFeq⟩ := mem_faces_iff.1 hF.1
  have hz0F : z0 ∈ F := hFeq ▸ mem_connectedComponentIn hz0
  set G := connectedComponentIn (drawing (cVerts X) (augEdges X))ᶜ z0 with hGdef
  have hG : G ∈ faces (cVerts X) (augEdges X) := mem_faces_iff.2 ⟨z0, hFaug hz0F, rfl⟩
  have hpc : IsPreconnected F := hFeq ▸ isPreconnected_connectedComponentIn
  have hFG : F ⊆ G := hpc.subset_connectedComponentIn hz0F hFaug
  have hGF : G ⊆ F := subset_face hF.1 isPreconnected_connectedComponentIn
    (fun z hz hzD => connectedComponentIn_subset _ _ hz (drawing_mono Finset.subset_union_left hzD))
    (mem_connectedComponentIn (hFaug hz0F)) hz0F
  have hFG' : F = G := hFG.antisymm hGF
  exact ⟨hFG' ▸ hG, hF.2⟩

/-- Every bounded face of the augmented graph is an old face or the cap of a non-unit hull
side. -/
theorem augFace_cases :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      ∀ F ∈ augFaces X, F ∈ contactFaces X ∨
        ∃ p ∈ ccwHullSides X, 1 < dist p.1 p.2 ∧ IsCap X p.1 p.2 F := by
  filter_upwards with n _ X hX F hF
  by_contra hcon
  push_neg at hcon
  obtain ⟨hnot, hnocap⟩ := hcon
  apply hnot
  obtain ⟨z0, hz0, hFeq⟩ := mem_faces_iff.1 hF.1
  have hz0F : z0 ∈ F := hFeq ▸ mem_connectedComponentIn hz0
  have hFc : F ⊆ (drawing (cVerts X) (cUnitEdges X))ᶜ := fun z hz hzD =>
    face_subset_compl hF.1 hz (drawing_mono Finset.subset_union_left hzD)
  set G := connectedComponentIn (drawing (cVerts X) (cUnitEdges X))ᶜ z0 with hGdef
  have hG : G ∈ faces (cVerts X) (cUnitEdges X) := mem_faces_iff.2 ⟨z0, hFc hz0F, rfl⟩
  have hpc : IsPreconnected F := hFeq ▸ isPreconnected_connectedComponentIn
  have hFG : F ⊆ G := hpc.subset_connectedComponentIn hz0F hFc
  have hfr : ∀ z ∈ G, z ∈ closure F → z ∈ F := by
    intro z hzG hzcl
    by_contra hzF
    have hzD := closure_face_diff hF.1 hzcl hzF
    have hzC : z ∉ drawing (cVerts X) (cUnitEdges X) := connectedComponentIn_subset _ _ hzG
    rcases hzD with h | h
    · exact hzC (Or.inl h)
    obtain ⟨e, he, hze⟩ := Set.mem_iUnion₂.1 h
    rcases Finset.mem_union.1 he with he' | he'
    · exact hzC (Or.inr (Set.mem_iUnion₂.2 ⟨e, he', hze⟩))
    obtain ⟨v, w, hs, rfl⟩ := hullSideEdges_cases he'
    have hvX := mem_of_mem_hullVertices hs.1
    have hwX := mem_of_mem_hullVertices hs.2.1
    have hd1 : 1 ≤ dist v w := hX.1.2 v hvX w hwX hs.2.2.1
    have hdne : dist v w ≠ 1 := by
      intro h1
      refine hzC (Or.inr (Set.mem_iUnion₂.2 ⟨s(toC v, toC w), ?_, hze⟩))
      rw [cUnitEdges, mem_unitPairs]
      exact ⟨Finset.mem_image_of_mem _ hvX, Finset.mem_image_of_mem _ hwX,
        by rw [dist_toC]; exact h1⟩
    refine hnocap (v, w) (mem_ccwHullSides.2 hs) (lt_of_le_of_ne hd1 (Ne.symm hdne)) ⟨hF, ?_⟩
    refine Finset.mem_filter.2 ⟨he, z, ?_, hzcl⟩
    rw [edgeOpenSeg_mk]
    rw [edgeSeg_mk] at hze
    exact mem_openSegment_of_ne' hze
      (fun h => hzC (Or.inl (h ▸ Finset.mem_image_of_mem _ hvX)))
      (fun h => hzC (Or.inl (h ▸ Finset.mem_image_of_mem _ hwX)))
  have hGF : G ⊆ F := by
    refine IsPreconnected.subset_left_of_subset_union (isOpen_face hF.1) isClosed_closure.isOpen_compl
      (Disjoint.mono_left subset_closure disjoint_compl_right) ?_
      ⟨z0, mem_connectedComponentIn (hFc hz0F), hz0F⟩ isPreconnected_connectedComponentIn
    intro z hz
    by_cases h : z ∈ closure F
    · exact Or.inl (hfr z hz h)
    · exact Or.inr h
  have hFG' : F = G := hFG.antisymm hGF
  exact ⟨hFG' ▸ hG, hF.2⟩

end Erdos99

end

end ContactFan

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `PolygonCycle`
-/

section PolygonCycle

/-!
# The sides of a convex polygon form one cycle

Let `S ⊆ ℂ` be a finite set in strictly convex position whose convex hull has nonempty interior.
The (counterclockwise) sides `IsCSide S a b` of its convex hull form a single cycle through all
the points of `S`: there is a `|S|`-periodic enumeration `v : ℕ → ℂ` of `S`, injective on
`[0, |S|)`, such that `IsCSide S a b` holds exactly for the consecutive pairs `(v i, v (i + 1))`
(`exists_cyclic_enum`).

This is what is needed to turn a contact face (Lemma 2.1, `contactFace_polygon`) into a closed
unit polygon in the sense of the local capacities of §8 (`UnitPolygon`).

The proof works with a point `c` in the interior:

* every side `a → b` turns positively around `c`, and no point of `S` lies strictly inside the
  angle `∠ a c b` (`not_mem_cone`);
* no two points of `S` lie on one ray from `c` (`eq_of_same_ray`);
* hence every point has exactly one successor and one predecessor;
* a cycle of positive turns cannot stay in a closed half-plane through `c`
  (`no_cycle_halfplane`, via a pseudo-angle), so the orbit of one point under the successor map
  passes through every point of `S`.
-/

open scoped BigOperators Real
open EstablishedExternalResults Set Complex Filter Topology

@[expose] public noncomputable section

open Classical

namespace Erdos99

namespace PolyCycle

/-- The cross product of two plane vectors, given as complex numbers. -/
def tcr (u v : ℂ) : ℝ := u.re * v.im - u.im * v.re

/-- The dot product of two plane vectors, given as complex numbers. -/
def tdot (u v : ℂ) : ℝ := u.re * v.re + u.im * v.im

lemma wc_im_eq (a b z : ℂ) : (wc a b z).im = tcr (b - a) (z - a) / normSq (b - a) := by
  simp only [wc, div_im, tcr, sub_re, sub_im]; ring

lemma tdot_sq_add_tcr_sq (Y V : ℂ) : tdot Y V ^ 2 + tcr Y V ^ 2 = normSq Y * normSq V := by
  simp only [tdot, tcr, normSq_apply]; ring

/-- A pseudo-angle on the closed upper half-plane, increasing with the angle. -/
def pang (y1 y2 : ℝ) : ℝ := -y1 / (|y1| + y2)

lemma pang_lt {y1 y2 z1 z2 : ℝ} (hy2 : 0 ≤ y2) (hz2 : 0 ≤ z2) (hy : y1 ≠ 0 ∨ y2 ≠ 0)
    (hz : z1 ≠ 0 ∨ z2 ≠ 0) (h : y2 * z1 < y1 * z2) : pang y1 y2 < pang z1 z2 := by
  have hpy : 0 < |y1| + y2 := by
    rcases hy with h | h
    · have := abs_pos.2 h; linarith
    · have : 0 < y2 := lt_of_le_of_ne hy2 (Ne.symm h); positivity
  have hpz : 0 < |z1| + z2 := by
    rcases hz with h | h
    · have := abs_pos.2 h; linarith
    · have : 0 < z2 := lt_of_le_of_ne hz2 (Ne.symm h); positivity
  unfold pang
  rw [div_lt_div_iff₀ hpy hpz]
  rcases le_or_gt 0 y1 with h1 | h1 <;> rcases le_or_gt 0 z1 with h2 | h2
  · rw [abs_of_nonneg h1, abs_of_nonneg h2]; nlinarith
  · rw [abs_of_nonneg h1] at hpy ⊢
    rw [abs_of_neg h2]
    nlinarith [mul_pos (neg_pos.2 h2) hpy, mul_nonneg h1 hz2]
  · nlinarith [mul_nonneg (neg_nonneg.2 h1.le) hz2, mul_nonneg hy2 h2]
  · rw [abs_of_neg h1, abs_of_neg h2]; nlinarith

/-- **A cycle of positive turns does not stay in a closed half-plane.** -/
lemma no_cycle_halfplane {V : ℂ} (hV : V ≠ 0) {A : ℕ → ℂ} {m : ℕ} (hm : 0 < m)
    (hper : A m = A 0) (hturn : ∀ i < m, 0 < tcr (A i) (A (i + 1)))
    (hT : ∀ i ≤ m, A i ≠ 0 ∧ tcr (A i) V ≤ 0) : False := by
  set f : ℕ → ℝ := fun i => pang (tdot (A i) V) (-tcr (A i) V) with hf
  have hnz : ∀ i ≤ m, tdot (A i) V ≠ 0 ∨ -tcr (A i) V ≠ 0 := by
    intro i hi
    by_contra hcon
    push_neg at hcon
    have h := tdot_sq_add_tcr_sq (A i) V
    rw [hcon.1, neg_eq_zero.1 hcon.2] at h
    have hV' : normSq V ≠ 0 := by rwa [Ne, normSq_eq_zero]
    have : normSq (A i) = 0 := by
      have : normSq (A i) * normSq V = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_right hV'
    exact (hT i hi).1 (normSq_eq_zero.1 this)
  have hstep : ∀ i < m, f i < f (i + 1) := by
    intro i hi
    refine pang_lt (neg_nonneg.2 (hT i hi.le).2) (neg_nonneg.2 (hT (i + 1) hi).2) (hnz i hi.le)
      (hnz (i + 1) hi) ?_
    have hV' : 0 < normSq V := normSq_pos.2 hV
    have e : tdot (A i) V * -tcr (A (i + 1)) V - -tcr (A i) V * tdot (A (i + 1)) V =
        tcr (A i) (A (i + 1)) * normSq V := by
      simp only [tdot, tcr, normSq_apply]; ring
    nlinarith [hturn i hi]
  have hmono : ∀ j, 0 < j → j ≤ m → f 0 < f j := by
    intro j hj hjm
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · exact hstep 0 hm
      · exact (ih hj0 (by omega)).trans (hstep j (by omega))
  have := hmono m hm le_rfl
  rw [hf] at this
  simp only [hper] at this
  exact lt_irrefl _ this

/-- Two vectors on the same side of a third which are collinear point the same way. -/
lemma tdot_pos_of_collinear {W U U' : ℂ} (h1 : 0 < tcr W U) (h2 : 0 < tcr W U')
    (h0 : tcr U U' = 0) : 0 < tdot U U' := by
  have e : tcr W U' * normSq U = tdot U U' * tcr W U + tcr U U' * tdot W U := by
    simp only [tdot, tcr, normSq_apply]; ring
  rw [h0, zero_mul, add_zero] at e
  have hU : U ≠ 0 := by rintro rfl; simp [tcr] at h1
  have := normSq_pos.2 hU
  by_contra hneg
  push_neg at hneg
  nlinarith [mul_pos h2 this]

section Polygon

variable {S : Finset ℂ} (hext : ∀ s ∈ S, s ∈ extremePoints ℝ (convexHull ℝ (S : Set ℂ)))
  {c : ℂ} (hc : c ∈ interior (convexHull ℝ (S : Set ℂ)))

include hext

lemma extreme_eq {x p q : ℂ} (hx : x ∈ S) (hp : p ∈ convexHull ℝ (S : Set ℂ))
    (hq : q ∈ convexHull ℝ (S : Set ℂ)) (h : x ∈ openSegment ℝ p q) : p = x ∧ q = x :=
  (mem_extremePoints.1 (hext x hx)).2 p hp q hq h

include hc

lemma center_ne {x : ℂ} (hx : x ∈ S) : x ≠ c := by
  rintro rfl
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x hc
  have h1 : x + ((ε / 2 : ℝ) : ℂ) ∈ convexHull ℝ (S : Set ℂ) := interior_subset (hball (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]; linarith))
  have h2 : x - ((ε / 2 : ℝ) : ℂ) ∈ convexHull ℝ (S : Set ℂ) := interior_subset (hball (by
    rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]; linarith))
  have hseg : x ∈ openSegment ℝ (x - ((ε / 2 : ℝ) : ℂ)) (x + ((ε / 2 : ℝ) : ℂ)) :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by
      simp only [Complex.real_smul]; push_cast; ring⟩
  have := (extreme_eq hext hx h2 h1 hseg).1
  have h3 : ((ε / 2 : ℝ) : ℂ) = 0 := by linear_combination -this
  have : (ε / 2 : ℝ) = 0 := by exact_mod_cast h3
  linarith

omit hext in
/-- Every side turns positively around an interior point. -/
lemma tcr_pos_of_side {a b : ℂ} (hs : IsCSide S a b) : 0 < tcr (a - c) (b - c) := by
  have h := side_pos hs hc
  rw [wc_im_eq] at h
  have hn : 0 < normSq (b - a) := normSq_pos.2 (sub_ne_zero.2 hs.2.2.1.symm)
  have h' : 0 < tcr (b - a) (c - a) := by
    by_contra hneg; push_neg at hneg
    exact absurd h (not_lt.2 (div_nonpos_of_nonpos_of_nonneg hneg hn.le))
  have e : tcr (b - a) (c - a) = tcr (a - c) (b - c) := by
    simp only [tcr, sub_re, sub_im]; ring
  linarith

/-- **No point of `S` lies strictly inside the angle of a side.** -/
lemma not_mem_cone {a b x : ℂ} (hs : IsCSide S a b) (hx : x ∈ S)
    (h1 : 0 < tcr (a - c) (x - c)) (h2 : 0 < tcr (x - c) (b - c)) : False := by
  set A := a - c
  set B := b - c
  set X := x - c
  have hAB := tcr_pos_of_side hc hs
  set l := tcr X B / tcr A B with hl
  set μ := tcr A X / tcr A B with hμ
  have hl0 : 0 < l := div_pos h2 hAB
  have hμ0 : 0 < μ := div_pos h1 hAB
  have key : X * (tcr A B : ℂ) = (tcr X B : ℂ) * A + (tcr A X : ℂ) * B := by
    apply Complex.ext <;>
    simp only [tcr, add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im] <;> ring
  have hABne : (tcr A B : ℂ) ≠ 0 := by exact_mod_cast hAB.ne'
  have hX : X = (l : ℂ) * A + (μ : ℂ) * B := by
    rw [hl, hμ]; push_cast
    field_simp
    linear_combination key
  -- `x` lies weakly to the left of `a → b`, so `l + μ ≤ 1`
  have hleft := hs.2.2.2 x hx
  rw [wc_im_eq] at hleft
  have hn : 0 < normSq (b - a) := normSq_pos.2 (sub_ne_zero.2 hs.2.2.1.symm)
  have hcr : 0 ≤ tcr (b - a) (x - a) := by
    by_contra hneg; push_neg at hneg
    exact absurd hleft (not_le.2 (div_neg_of_neg_of_pos hneg hn))
  have e1 : b - a = B - A := by simp [A, B]
  have e2 : x - a = X - A := by simp [A, X]
  have hsum : l + μ ≤ 1 := by
    rw [e1, e2, hX] at hcr
    have : tcr (B - A) ((l : ℂ) * A + (μ : ℂ) * B - A) = (1 - l - μ) * tcr A B := by
      simp only [tcr, sub_re, sub_im, add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im]
      ring
    rw [this] at hcr
    by_contra hlt; push_neg at hlt
    nlinarith
  have hl1 : l < 1 := by linarith
  -- `x` lies in the open segment from `a` to a point of `[c, b]`
  set y := c + ((μ / (1 - l) : ℝ) : ℂ) * B with hy
  have hyK : y ∈ convexHull ℝ (S : Set ℂ) := by
    have hcK : c ∈ convexHull ℝ (S : Set ℂ) := interior_subset hc
    have hbK : b ∈ convexHull ℝ (S : Set ℂ) := subset_convexHull ℝ _ hs.2.1
    have ht0 : 0 ≤ μ / (1 - l) := div_nonneg hμ0.le (by linarith)
    have ht1 : μ / (1 - l) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have := (convex_convexHull ℝ (S : Set ℂ)) hcK hbK (sub_nonneg.2 ht1) ht0 (by ring)
    convert this using 1
    simp only [hy, B, Complex.real_smul]; push_cast; ring
  have haK : a ∈ convexHull ℝ (S : Set ℂ) := subset_convexHull ℝ _ hs.1
  have hseg : x ∈ openSegment ℝ a y := by
    refine ⟨l, 1 - l, hl0, by linarith, by ring, ?_⟩
    have hx' : x = c + X := by simp [X]
    rw [hx', hX]
    simp only [hy, A, Complex.real_smul]
    have : ((1 - l : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (show (1 - l) ≠ 0 by linarith)
    push_cast at this ⊢
    field_simp
    ring
  have hax := (extreme_eq hext hx haK hyK hseg).1
  have : tcr A X = 0 := by simp only [A, X, hax, tcr]; ring
  linarith

/-- **No two points of `S` lie on one ray from `c`.** -/
lemma eq_of_same_ray {x y : ℂ} (hx : x ∈ S) (hy : y ∈ S) (h0 : tcr (x - c) (y - c) = 0)
    (hd : 0 < tdot (x - c) (y - c)) : x = y := by
  set X := x - c
  set Y := y - c
  have hYne : Y ≠ 0 := sub_ne_zero.2 (center_ne hext hc hy)
  have hY : 0 < normSq Y := normSq_pos.2 hYne
  set t := tdot X Y / normSq Y with ht
  have ht0 : 0 < t := div_pos hd hY
  have h0' : X.re * Y.im - X.im * Y.re = 0 := h0
  have key : X * (normSq Y : ℂ) = (tdot X Y : ℂ) * Y := by
    apply Complex.ext
    · simp only [tdot, normSq_apply, mul_re, ofReal_re, ofReal_im]
      linear_combination Y.im * h0'
    · simp only [tdot, normSq_apply, mul_im, ofReal_re, ofReal_im]
      linear_combination (-Y.re) * h0'
  have hYc : (normSq Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  have hXt : X = (t : ℂ) * Y := by
    rw [ht]; push_cast
    field_simp
    linear_combination key
  have hcK : c ∈ convexHull ℝ (S : Set ℂ) := interior_subset hc
  have hxK : x ∈ convexHull ℝ (S : Set ℂ) := subset_convexHull ℝ _ hx
  have hyK : y ∈ convexHull ℝ (S : Set ℂ) := subset_convexHull ℝ _ hy
  have hxe : x = c + (t : ℂ) * (y - c) := by rw [← hXt]; simp [X]
  rcases lt_trichotomy t 1 with hlt | heq | hgt
  · -- `x` lies strictly between `c` and `y`
    have hseg : x ∈ openSegment ℝ c y := by
      refine ⟨1 - t, t, by linarith, ht0, by ring, ?_⟩
      rw [hxe]; simp only [Complex.real_smul]; push_cast; ring
    exact absurd (extreme_eq hext hx hcK hyK hseg).1 (center_ne hext hc hx).symm
  · rw [hxe, heq]; simp
  · -- `y` lies strictly between `c` and `x`
    have hseg : y ∈ openSegment ℝ c x := by
      refine ⟨1 - 1 / t, 1 / t, by rw [sub_pos, div_lt_one ht0]; exact hgt, by positivity,
        by ring, ?_⟩
      rw [hxe]; simp only [Complex.real_smul]
      have : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
      push_cast
      field_simp
      ring
    exact absurd (extreme_eq hext hy hcK hxK hseg).1 (center_ne hext hc hy).symm

/-- Uniqueness of the successor. -/
lemma side_succ_unique {a b b' : ℂ} (hs : IsCSide S a b) (hs' : IsCSide S a b') : b = b' := by
  have h1 := tcr_pos_of_side hc hs
  have h2 := tcr_pos_of_side hc hs'
  rcases lt_trichotomy (tcr (b - c) (b' - c)) 0 with hlt | heq | hgt
  · exact (not_mem_cone hext hc hs hs'.2.1 h2 (by
      have : tcr (b' - c) (b - c) = -tcr (b - c) (b' - c) := by simp only [tcr]; ring
      linarith)).elim
  · exact eq_of_same_ray hext hc hs.2.1 hs'.2.1 heq (tdot_pos_of_collinear h1 h2 heq)
  · exact (not_mem_cone hext hc hs' hs.2.1 h1 hgt).elim

/-- Uniqueness of the predecessor. -/
lemma side_pred_unique {a a' b : ℂ} (hs : IsCSide S a b) (hs' : IsCSide S a' b) : a = a' := by
  have h1 := tcr_pos_of_side hc hs
  have h2 := tcr_pos_of_side hc hs'
  rcases lt_trichotomy (tcr (a - c) (a' - c)) 0 with hlt | heq | hgt
  · exact (not_mem_cone hext hc hs' hs.1 (by
      have : tcr (a' - c) (a - c) = -tcr (a - c) (a' - c) := by simp only [tcr]; ring
      linarith) h1).elim
  · have k1 : 0 < tcr (-(b - c)) (a - c) := by
      have : tcr (-(b - c)) (a - c) = tcr (a - c) (b - c) := by simp only [tcr, neg_re, neg_im]; ring
      linarith
    have k2 : 0 < tcr (-(b - c)) (a' - c) := by
      have : tcr (-(b - c)) (a' - c) = tcr (a' - c) (b - c) := by
        simp only [tcr, neg_re, neg_im]; ring
      linarith
    exact eq_of_same_ray hext hc hs.1 hs'.1 heq (tdot_pos_of_collinear k1 k2 heq)
  · exact (not_mem_cone hext hc hs hs'.1 hgt h2).elim

end Polygon

/-! ## The successor map and the single cycle -/

section Cycle

variable {S : Finset ℂ} (hext : ∀ s ∈ S, s ∈ extremePoints ℝ (convexHull ℝ (S : Set ℂ)))
  (hint : (interior (convexHull ℝ (S : Set ℂ))).Nonempty)

include hext hint

/-- Every point of `S` starts a side. -/
lemma exists_side {a : ℂ} (ha : a ∈ S) : ∃ b, IsCSide S a b := by
  obtain ⟨c, hc⟩ := hint
  set OS := (S ×ˢ S).filter (fun p => IsCSide S p.1 p.2) with hOS
  have h1 : (cSides S).card = S.card := card_cSides hext ⟨c, hc⟩
  have h2 : S.card ≤ OS.card := by
    rw [← h1]; exact Finset.card_image_le
  have h3 : (OS.image Prod.fst).card = OS.card := by
    refine Finset.card_image_of_injOn ?_
    rintro ⟨p1, p2⟩ hp ⟨q1, q2⟩ hq (h : p1 = q1)
    have hp' : IsCSide S p1 p2 := (Finset.mem_filter.1 hp).2
    have hq' : IsCSide S q1 q2 := (Finset.mem_filter.1 hq).2
    subst h
    rw [side_succ_unique hext hc hp' hq']
  have hsub : OS.image Prod.fst ⊆ S := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
    exact (Finset.mem_filter.1 hp).2.1
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [h3]; exact h2)
  rw [← heq] at ha
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 ha
  exact ⟨p.2, (Finset.mem_filter.1 hp).2⟩

omit hext hint in
/-- The successor of a point along the boundary (an arbitrary value off `S`). -/
def nxt (S : Finset ℂ) (a : ℂ) : ℂ := if h : ∃ b, IsCSide S a b then h.choose else a

lemma nxt_side {a : ℂ} (ha : a ∈ S) : IsCSide S a (nxt S a) := by
  have h := exists_side hext hint ha
  rw [nxt, dif_pos h]; exact h.choose_spec

lemma nxt_mem {a : ℂ} (ha : a ∈ S) : nxt S a ∈ S := (nxt_side hext hint ha).2.1

lemma iterate_nxt_mem {a : ℂ} (ha : a ∈ S) (i : ℕ) : (nxt S)^[i] a ∈ S := by
  induction i with
  | zero => exact ha
  | succ i ih => rw [Function.iterate_succ_apply']; exact nxt_mem hext hint ih

lemma nxt_injOn {a a' : ℂ} (ha : a ∈ S) (ha' : a' ∈ S) (h : nxt S a = nxt S a') : a = a' := by
  obtain ⟨c, hc⟩ := hint
  have h1 := nxt_side hext ⟨c, hc⟩ ha
  have h2 := nxt_side hext ⟨c, hc⟩ ha'
  rw [← h] at h2
  exact side_pred_unique hext hc h1 h2

lemma iterate_nxt_cancel {p q : ℂ} (hp : p ∈ S) (hq : q ∈ S) (i : ℕ)
    (h : (nxt S)^[i] p = (nxt S)^[i] q) : p = q := by
  induction i generalizing p q with
  | zero => exact h
  | succ i ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply] at h
    exact nxt_injOn hext hint hp hq (ih (nxt_mem hext hint hp) (nxt_mem hext hint hq) h)

/-- The orbit of a point returns to it. -/
lemma exists_return {a : ℂ} (ha : a ∈ S) : ∃ m, 0 < m ∧ (nxt S)^[m] a = a := by
  obtain ⟨i, hi, j, hj, hij, h⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (S.card + 1)) (t := S) (f := fun i => (nxt S)^[i] a)
    (by simp) (fun i _ => iterate_nxt_mem hext hint ha i)
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · refine ⟨j - i, by omega, ?_⟩
    have e : j = i + (j - i) := by omega
    rw [e, Function.iterate_add_apply] at h
    exact (iterate_nxt_cancel hext hint ha (iterate_nxt_mem hext hint ha _) i h).symm
  · refine ⟨i - j, by omega, ?_⟩
    have e : i = j + (i - j) := by omega
    rw [e, Function.iterate_add_apply] at h
    exact iterate_nxt_cancel hext hint (iterate_nxt_mem hext hint ha _) ha j h

/-- **The orbit of any point under the successor map passes through all of `S`.** -/
lemma orbit_covers {a0 : ℂ} (ha0 : a0 ∈ S) {m : ℕ} (hm : 0 < m) (hret : (nxt S)^[m] a0 = a0)
    {x : ℂ} (hx : x ∈ S) : ∃ i < m, (nxt S)^[i] a0 = x := by
  obtain ⟨c, hc⟩ := hint
  by_contra hcon
  push_neg at hcon
  have hper : ∀ i, (nxt S)^[i + m] a0 = (nxt S)^[i] a0 := by
    intro i; rw [Function.iterate_add_apply, hret]
  have hne : ∀ i, (nxt S)^[i] a0 ≠ x := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      rcases lt_or_ge i m with hi | hi
      · exact hcon i hi
      · have e : i = (i - m) + m := by omega
        rw [e, hper]; exact ih _ (by omega)
  set A : ℕ → ℂ := fun i => (nxt S)^[i] a0 - c with hA
  have hmem : ∀ i, (nxt S)^[i] a0 ∈ S := iterate_nxt_mem hext ⟨c, hc⟩ ha0
  have hturn : ∀ i, 0 < tcr (A i) (A (i + 1)) := by
    intro i
    simp only [hA, Function.iterate_succ_apply']
    exact tcr_pos_of_side hc (nxt_side hext ⟨c, hc⟩ (hmem i))
  have hA0 : ∀ i, A i ≠ 0 := fun i => sub_ne_zero.2 (center_ne hext hc (hmem i))
  have hX0 : x - c ≠ 0 := sub_ne_zero.2 (center_ne hext hc hx)
  have hAper : A m = A 0 := by simp only [hA, hret, Function.iterate_zero, id]
  -- once `x` is to the left of some `A i`, it stays to the left
  have hstep : ∀ i, 0 < tcr (A i) (x - c) → 0 < tcr (A (i + 1)) (x - c) := by
    intro i h1
    have hs := nxt_side hext ⟨c, hc⟩ (hmem i)
    have hAB := tcr_pos_of_side hc hs
    have e1 : A (i + 1) = nxt S ((nxt S)^[i] a0) - c := by
      simp only [hA, Function.iterate_succ_apply']
    rw [e1]
    rcases lt_trichotomy (tcr (nxt S ((nxt S)^[i] a0) - c) (x - c)) 0 with hlt | heq | hgt
    · exact (not_mem_cone hext hc hs hx h1 (by
        have : tcr (x - c) (nxt S ((nxt S)^[i] a0) - c) =
            -tcr (nxt S ((nxt S)^[i] a0) - c) (x - c) := by simp only [tcr]; ring
        linarith)).elim
    · have hd := tdot_pos_of_collinear hAB h1 heq
      have := eq_of_same_ray hext hc (nxt_mem hext ⟨c, hc⟩ (hmem i)) hx heq hd
      exact absurd (by rw [Function.iterate_succ_apply']; exact this) (hne (i + 1))
    · exact hgt
  by_cases hcase : ∃ i ≤ m, 0 < tcr (A i) (x - c)
  · obtain ⟨i, him, hi⟩ := hcase
    have hall : ∀ j, i ≤ j → 0 < tcr (A j) (x - c) := by
      intro j hij
      induction j, hij using Nat.le_induction with
      | base => exact hi
      | succ j _ ih => exact hstep j ih
    refine no_cycle_halfplane (V := -(x - c)) (neg_ne_zero.2 hX0) hm hAper
      (fun i _ => hturn i) (fun j _ => ⟨hA0 j, ?_⟩)
    have hj := hall (j + m) (by omega)
    have e : A (j + m) = A j := by simp only [hA, hper]
    rw [e] at hj
    have : tcr (A j) (-(x - c)) = -tcr (A j) (x - c) := by simp only [tcr, neg_re, neg_im]; ring
    linarith
  · push_neg at hcase
    exact no_cycle_halfplane hX0 hm hAper (fun i _ => hturn i) (fun j hj => ⟨hA0 j, hcase j hj⟩)

/-- **The sides of a convex polygon form a single cycle.**  A finite set `S ⊆ ℂ` in strictly
convex position whose hull has nonempty interior admits a `|S|`-periodic enumeration `v`,
injective on `[0, |S|)`, whose consecutive pairs are exactly the counterclockwise sides. -/
theorem exists_cyclic_enum : ∃ v : ℕ → ℂ, (∀ i, v (i + S.card) = v i) ∧ (∀ i, v i ∈ S) ∧
    Set.InjOn v (Set.Iio S.card) ∧ ∀ a b, IsCSide S a b ↔ ∃ i, v i = a ∧ v (i + 1) = b := by
  have h3 := three_le_card_of_interior hint
  obtain ⟨a0, ha0⟩ : S.Nonempty := Finset.card_pos.1 (by omega)
  have hex : ∃ m, 0 < m ∧ (nxt S)^[m] a0 = a0 := exists_return hext hint ha0
  set m := Nat.find hex with hmdef
  have hm : 0 < m ∧ (nxt S)^[m] a0 = a0 := Nat.find_spec hex
  have hmin : ∀ k, 0 < k → k < m → (nxt S)^[k] a0 ≠ a0 := fun k hk hkm h =>
    Nat.find_min hex hkm ⟨hk, h⟩
  set v : ℕ → ℂ := fun i => (nxt S)^[i] a0 with hv
  have hmem : ∀ i, v i ∈ S := iterate_nxt_mem hext hint ha0
  have hinj : Set.InjOn v (Set.Iio m) := by
    intro i hi j hj h
    simp only [Set.mem_Iio] at hi hj
    by_contra hij
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · have e : j = i + (j - i) := by omega
      simp only [hv] at h
      rw [e, Function.iterate_add_apply] at h
      exact hmin (j - i) (by omega) (by omega)
        (iterate_nxt_cancel hext hint (iterate_nxt_mem hext hint ha0 _) ha0 i h.symm)
    · have e : i = j + (i - j) := by omega
      simp only [hv] at h
      rw [e, Function.iterate_add_apply] at h
      exact hmin (i - j) (by omega) (by omega)
        (iterate_nxt_cancel hext hint (iterate_nxt_mem hext hint ha0 _) ha0 j h)
  have hcard : S.card = m := by
    have himg : (Finset.range m).image v = S := by
      refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx; exact hmem i
      · refine Finset.card_le_card (fun x hx => ?_)
        obtain ⟨i, hi, rfl⟩ := orbit_covers hext hint ha0 hm.1 hm.2 hx
        exact Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, rfl⟩
    rw [← himg, Finset.card_image_of_injOn (fun i hi j hj h => hinj (by simpa using hi)
      (by simpa using hj) h), Finset.card_range]
  refine ⟨v, fun i => ?_, hmem, hcard ▸ hinj, fun a b => ⟨fun hs => ?_, ?_⟩⟩
  · simp only [hv, hcard, Function.iterate_add_apply, hm.2]
  · obtain ⟨i, -, hi⟩ := orbit_covers hext hint ha0 hm.1 hm.2 hs.1
    refine ⟨i, hi, ?_⟩
    obtain ⟨c, hc⟩ := hint
    simp only [hv, Function.iterate_succ_apply']
    rw [hi]
    exact side_succ_unique hext hc (nxt_side hext ⟨c, hc⟩ hs.1) hs
  · rintro ⟨i, rfl, rfl⟩
    simp only [hv, Function.iterate_succ_apply']
    exact nxt_side hext hint (hmem i)

end Cycle

end PolyCycle

end Erdos99

end

end PolygonCycle

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `FaceCapacity`
-/

section FaceCapacity

/-!
# Local capacities at the exceptional faces (Verification Guide §8, applied in §9.3)

The local capacities of WP6 (`UnitPolygon.marked_card_le_markedCap`) are stated for closed unit
polygons `UnitPolygon k` given by a cyclic list of vertices.  Here they are transferred to the
exceptional faces of an optimal configuration:

* `orientedSides X F`: the counterclockwise oriented boundary sides `(a, b)` of a face `F`
  (the unit edge `s(a, b)` bounds `F`, and `F` lies strictly to the left of `a → b`);
* `exceptionalFace_unitPolygon`: eventually every exceptional face with `k` sides is a closed
  unit polygon `Q : UnitPolygon k` whose consecutive vertex pairs are exactly its oriented
  sides (Lemma 2.1, `contactFace_polygon`, together with the single-cycle theorem
  `PolyCycle.exists_cyclic_enum`);
* `exceptionalFace_marked_card_le`: **the capacity bound at a face.**  Eventually, at every
  exceptional face `F`, any set of oriented sides of `F` whose directions all have projection at
  least `19/20` on one unit vector has at most `markedCap (faceSize X F)` elements.

This is the form in which the capacities are applied to the arrivals of the token process of §9
(`TokenRouting`).
-/

open scoped BigOperators Real
open EstablishedExternalResults Set Complex Filter Topology

@[expose] public noncomputable section

open Classical

namespace Erdos99

open Propagation

/-- The counterclockwise oriented boundary sides of a face `F` of the contact graph: the pairs
`(a, b)` such that `s(a, b)` is a boundary unit edge of `F` and `F` lies strictly to the left of
the directed segment `a → b`. -/
def orientedSides (X : Finset Plane) (F : Set ℂ) : Finset (ℂ × ℂ) :=
  ((cVerts X) ×ˢ (cVerts X)).filter (fun ab => s(ab.1, ab.2) ∈ bdryEdges (cUnitEdges X) F ∧
    ∀ z ∈ F, 0 < (wc ab.1 ab.2 z).im)

/-- An oriented side of the polygon face `F = int conv S` is a counterclockwise side of `S`. -/
lemma isCSide_of_mem_orientedSides {X : Finset Plane} {F : Set ℂ} {S : Finset ℂ}
    (hFint : F = interior (convexHull ℝ (S : Set ℂ))) (hbd : bdryEdges (cUnitEdges X) F = cSides S)
    (hne : F.Nonempty) {ab : ℂ × ℂ} (h : ab ∈ orientedSides X F) : IsCSide S ab.1 ab.2 := by
  obtain ⟨-, hmem, hleft⟩ := Finset.mem_filter.1 h
  rw [hbd] at hmem
  obtain ⟨⟨p, q⟩, hpq, he⟩ := Finset.mem_image.1 hmem
  have hs : IsCSide S p q := (Finset.mem_filter.1 hpq).2
  rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hs
  · exfalso
    obtain ⟨z, hz⟩ := hne
    have h1 := side_pos hs (hFint ▸ hz)
    have h2 := hleft z hz
    rw [wc_im_swap] at h1
    linarith

lemma periodic_mod {v : ℕ → ℂ} {k : ℕ} (hper : ∀ i, v (i + k) = v i) (n : ℕ) :
    v (n % k) = v n := by
  conv_rhs => rw [← Nat.mod_add_div n k]
  generalize n / k = q
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.mul_succ, ← add_assoc, hper, ih]

/-- **Exceptional faces are closed unit polygons.**  Eventually, every exceptional face `F` with
`k = faceSize X F` sides is a `UnitPolygon k` whose consecutive vertex pairs (in `ℂ`) are exactly
the oriented sides of `F`. -/
theorem exceptionalFace_unitPolygon :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ∀ F ∈ exceptionalFaces X,
      ∃ (h : NeZero (faceSize X F)) (Q : @UnitPolygon (faceSize X F) h),
        ∀ ab ∈ orientedSides X F, ∃ i : Fin (faceSize X F),
          toC (Q.P i) = ab.1 ∧ toC (Q.P (i + 1)) = ab.2 := by
  filter_upwards [contactFace_polygon] with n hpoly hfm X hX F hF
  obtain ⟨S, hSV, h3, hext, hFint, hbd, hsize⟩ := hpoly hfm X hX F hF.1
  have hne : F.Nonempty := by
    obtain ⟨x, hx, rfl⟩ := mem_faces_iff.1 hF.1.1
    exact ⟨x, mem_connectedComponentIn hx⟩
  have hint : (interior (convexHull ℝ (S : Set ℂ))).Nonempty := hFint ▸ hne
  obtain ⟨v, hper, hvS, hinj, hside⟩ := PolyCycle.exists_cyclic_enum hext hint
  rw [hsize]
  have hk : NeZero S.card := ⟨by omega⟩
  have hmod := periodic_mod hper
  have hsucc : ∀ i : Fin S.card, v ((i + 1 : Fin S.card) : ℕ) = v ((i : ℕ) + 1) := by
    intro i
    rw [Fin.val_add, hmod, Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  have hvX : ∀ i, toC.symm (v i) ∈ X := by
    intro i
    obtain ⟨x, hx, hxe⟩ := Finset.mem_image.1 (hSV (hvS i))
    rw [← hxe, LinearIsometryEquiv.symm_apply_apply]; exact hx
  let Q : UnitPolygon S.card :=
    { P := fun i => toC.symm (v i)
      unit_edge := by
        intro i
        simp only
        rw [hsucc]
        have hs : IsCSide S (v i) (v (i + 1)) := (hside _ _).2 ⟨i, rfl, rfl⟩
        have hmem : s(v i, v (i + 1)) ∈ cUnitEdges X := by
          have : s(v i, v (i + 1)) ∈ cSides S :=
            Finset.mem_image.2 ⟨(v i, v (i + 1)),
              Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hs.1, hs.2.1⟩, hs⟩, rfl⟩
          rw [← hbd] at this
          exact (Finset.mem_filter.1 this).1
        have hd := (mem_unitPairs.1 hmem).2.2
        rw [← map_sub, LinearIsometryEquiv.norm_map, ← dist_eq_norm, dist_comm]
        exact hd
      sep := by
        intro i j hij
        have hne' : v i ≠ v j := fun h => hij (Fin.ext (hinj (Set.mem_Iio.2 i.2)
          (Set.mem_Iio.2 j.2) h))
        exact hX.1.2 _ (hvX i) _ (hvX j) (fun h => hne' (toC.symm.injective h)) }
  refine ⟨hk, Q, fun ab hab => ?_⟩
  obtain ⟨i, hi1, hi2⟩ := (hside _ _).1 (isCSide_of_mem_orientedSides hFint hbd hne hab)
  refine ⟨⟨i % S.card, Nat.mod_lt _ (by omega)⟩, ?_, ?_⟩
  · show toC (toC.symm (v (i % S.card))) = ab.1
    rw [LinearIsometryEquiv.apply_symm_apply, hmod, hi1]
  · show toC (toC.symm (v ((⟨i % S.card, _⟩ + 1 : Fin S.card) : ℕ))) = ab.2
    rw [LinearIsometryEquiv.apply_symm_apply, hsucc, ← hmod, Nat.add_mod, Nat.mod_mod,
      ← Nat.add_mod, hmod, hi2]

/-- **The local capacity bound at an exceptional face** (WP6 applied to the faces).  Eventually,
at every exceptional face `F`, a set `M` of oriented sides of `F` whose direction vectors all have
projection at least `19/20` on one unit vector `e` has at most `markedCap (faceSize X F)`
elements. -/
theorem exceptionalFace_marked_card_le :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ∀ F ∈ exceptionalFaces X,
      ∀ e : ℂ, ‖e‖ = 1 → ∀ M ⊆ orientedSides X F,
        (∀ ab ∈ M, 19 / 20 ≤ inner ℝ (ab.2 - ab.1) e) →
          (M.card : ℝ) ≤ markedCap (faceSize X F) := by
  filter_upwards [exceptionalFace_unitPolygon] with n hpoly hfm X hX F hF e he M hM hmark
  obtain ⟨hk, Q, hQ⟩ := hpoly hfm X hX F hF
  set k := faceSize X F
  set M' : Finset (Fin k) := Finset.univ.filter
    (fun i => (toC (Q.P i), toC (Q.P (i + 1))) ∈ M) with hM'
  have hsub : M ⊆ M'.image (fun i => (toC (Q.P i), toC (Q.P (i + 1)))) := by
    intro ab hab
    obtain ⟨i, h1, h2⟩ := hQ ab (hM hab)
    refine Finset.mem_image.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · rw [h1, h2]; exact hab
    · rw [h1, h2]
  have hcard : M.card ≤ M'.card := (Finset.card_le_card hsub).trans Finset.card_image_le
  have he' : ‖toC.symm e‖ = 1 := by rw [LinearIsometryEquiv.norm_map]; exact he
  have hmark' : ∀ i ∈ M', 19 / 20 ≤ inner ℝ (Q.edge i) (toC.symm e) := by
    intro i hi
    have := hmark _ (Finset.mem_filter.1 hi).2
    simp only at this
    rw [← map_sub, ← LinearIsometryEquiv.apply_symm_apply toC e,
      LinearIsometryEquiv.inner_map_map] at this
    simpa [UnitPolygon.edge] using this
  have := Q.marked_card_le_markedCap hF.2 he' le_rfl hmark'
  calc (M.card : ℝ) ≤ M'.card := by exact_mod_cast hcard
    _ ≤ markedCap k := this

end Erdos99

end

end FaceCapacity

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `TokenRouting`
-/

section TokenRouting

/-!
# Arrivals through marked edges (Verification Guide §9.1, §9.3: applying the capacities)

The face condition of the token process of §9 (every exceptional face receives at most its
capacity `markedCap` of §8) is a consequence of the way tokens arrive: each token enters its
receiving face `F` through an edge of `F` (the terminal edge of the track it travels along),
different tokens use different edges ("track incidences used by the process are distinct"), and,
at a receiver that is not set aside as large, all these edges point nearly in one direction (the
incoming face vectors are near the positive tangent of the sources, and the sources of one small
receiver have tangents differing by `o(1)`).

This file makes this precise and proves that it implies the face condition:

* `TokenProcess.arrivals P j F`: the tokens arriving at `F` by the end of round `j + 1`, namely
  the sources sent to `F` and the faces that emit by the end of round `j` towards `F`;
  `faceArr_succ_eq_card` shows that `faceArr (j + 1) F` is exactly its cardinality.
* `TokenProcess.Entry X`: entry data, the oriented edge through which each token enters its
  receiver.
* `TokenProcess.MarkedArrivals P E j F`: the arrivals at `F` enter through pairwise distinct
  oriented sides of `F` whose directions all have projection at least `19/20` on one unit vector.
* `TokenProcess.faceArr_le_markedCap`: eventually, marked arrivals at an exceptional face
  respect its capacity (from `exceptionalFace_marked_card_le`, i.e. WP6 applied to the faces).
* `exists_tokenProcess_of_marked`: the face condition of `exists_tokenProcess` follows from marked
  arrivals at every exceptional face.
-/

open scoped BigOperators Real
open Filter Topology

@[expose] public noncomputable section

open Classical

namespace Erdos99

open Propagation

namespace TokenProcess

variable {X : Finset Plane} (P : TokenProcess X)

/-- The tokens arriving at the face `F` by the end of round `j + 1`: the sources (unit hull
sides) whose first receiver is `F`, and the exceptional faces that have emitted by the end of
round `j` and send their token to `F`. -/
def arrivals (j : ℕ) (F : Set ℂ) : Finset ((Plane × Plane) ⊕ Set ℂ) :=
  ((unitHullSides X).filter (fun p => P.start p = .face F)).disjSum
    (P.fin.toFinset.filter (fun G => P.out G = .face F ∧ emitted (faceSize X G) (P.faceArr j G) = 1))

lemma emitted_eq_zero_or_one (k a : ℕ) : emitted k a = 0 ∨ emitted k a = 1 := by
  unfold emitted; split_ifs <;> simp

/-- The arrivals at a face by the end of round `j + 1` are counted by `faceArr (j + 1)`. -/
theorem faceArr_succ_eq_card (j : ℕ) (F : Set ℂ) :
    P.faceArr (j + 1) F = (P.arrivals j F).card := by
  rw [arrivals, Finset.card_disjSum, Finset.card_filter, Finset.card_filter]
  show ∑ p ∈ unitHullSides X, toFace (P.start p) F +
      ∑ G ∈ P.fin.toFinset, toFace (P.out G) F * emitted (faceSize X G) (P.faceArr j G) = _
  congr 1
  refine Finset.sum_congr rfl (fun G _ => ?_)
  unfold toFace
  rcases emitted_eq_zero_or_one (faceSize X G) (P.faceArr j G) with h | h <;>
    · rw [h]; split_ifs <;> simp_all

/-- Entry data of a token process: the oriented edge (in `ℂ`) through which each source and each
emitted token enters its receiver. -/
structure Entry (X : Finset Plane) where
  /-- The entry edge of the token of a source. -/
  src : Plane × Plane → ℂ × ℂ
  /-- The entry edge of the token emitted by a face. -/
  emit : Set ℂ → ℂ × ℂ

/-- The entry edge of a token. -/
def Entry.edge {X : Finset Plane} (E : Entry X) : (Plane × Plane) ⊕ Set ℂ → ℂ × ℂ :=
  Sum.elim E.src E.emit

/-- **Marked arrivals at `F` by the end of round `j + 1`**: the arriving tokens enter through
pairwise distinct oriented sides of `F`, whose directions all have projection at least `19/20` on
one unit vector `e`. -/
def MarkedArrivals (E : Entry X) (j : ℕ) (F : Set ℂ) : Prop :=
  Set.InjOn E.edge (P.arrivals j F) ∧ ∃ e : ℂ, ‖e‖ = 1 ∧ ∀ t ∈ P.arrivals j F,
    E.edge t ∈ orientedSides X F ∧ 19 / 20 ≤ inner ℝ ((E.edge t).2 - (E.edge t).1) e

end TokenProcess

/-- **Marked arrivals respect the local capacities.**  Eventually, for every token process with
entry data, a face that receives its tokens through marked edges has received at most its
capacity `markedCap` of §8. -/
theorem TokenProcess.faceArr_le_markedCap :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ∀ (P : TokenProcess X)
      (E : TokenProcess.Entry X) (j : ℕ), ∀ F ∈ exceptionalFaces X, P.MarkedArrivals E j F →
        (P.faceArr (j + 1) F : ℝ) ≤ markedCap (faceSize X F) := by
  filter_upwards [exceptionalFace_marked_card_le] with n hcap hfm X hX P E j F hF hmk
  obtain ⟨hinj, e, he, hmark⟩ := hmk
  rw [P.faceArr_succ_eq_card, ← Finset.card_image_of_injOn hinj]
  refine hcap hfm X hX F hF e he _ (fun ab hab => ?_) (fun ab hab => ?_)
  · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hab
    exact (hmark t ht).1
  · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hab
    exact (hmark t ht).2

/-- **The face condition from marked arrivals.**  If, eventually, every configuration admits a
token process with entry data whose arrivals at every exceptional face are marked after `K + 1`
rounds, whose cap arrivals are at most `2ρ/3 + ηD` and whose losses are at most the number of
long sources plus `ηD`, then the conclusion of `exists_tokenProcess` holds at depth `K + 1`. -/
theorem exists_tokenProcess_of_marked (K : ℕ) (η : ℝ)
    (h : ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∃ (P : TokenProcess X) (E : TokenProcess.Entry X),
        (∀ F ∈ exceptionalFaces X, P.MarkedArrivals E K F) ∧
        (P.capArr (K + 1) : ℝ) ≤ 2 * (returnExcess X : ℝ) / 3 + η * diam X ∧
        (P.lostArr (K + 1) : ℝ) ≤ (((unitHullSides X).filter
          (fun p => diam X ^ (19 / 20 : ℝ) ≤ srcLen X s(p.1, p.2))).card : ℝ) + η * diam X) :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∃ P : TokenProcess X,
        (∀ F ∈ exceptionalFaces X, (P.faceArr (K + 1) F : ℝ) ≤ markedCap (faceSize X F)) ∧
        (P.capArr (K + 1) : ℝ) ≤ 2 * (returnExcess X : ℝ) / 3 + η * diam X ∧
        (P.lostArr (K + 1) : ℝ) ≤ (((unitHullSides X).filter
          (fun p => diam X ^ (19 / 20 : ℝ) ≤ srcLen X s(p.1, p.2))).card : ℝ) + η * diam X := by
  filter_upwards [h, TokenProcess.faceArr_le_markedCap] with n hn hcap hfm X hX htri
  obtain ⟨P, E, hmk, hc, hl⟩ := hn hfm X hX htri
  exact ⟨P, fun F hF => hcap hfm X hX P E K F hF (hmk F hF), hc, hl⟩

/-- The trivial process (every token is lost) of a separated configuration. -/
def TokenProcess.trivial {X : Finset Plane} (hX : IsSeparated X) : TokenProcess X where
  fin := exceptionalFaces_finite hX
  start _ := .lost
  out _ := .lost

end Erdos99

end

end TokenRouting

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `WindingJump`
-/

section WindingJump

/-!
# The exact jump of the winding sum across an edge

For a closed polygonal path `Γ = pre ++ A :: B :: post` whose edge `[A, B]` has a midpoint `m`
not on the rest of the path, two points `x`, `y` joined by a segment through `m` that meets the
path only at `m`, with `x` to the left and `y` to the right of `A → B`, have winding sums differing
by exactly `2π`.
-/

open scoped Real ComplexConjugate
open Complex Set Metric

@[expose] public noncomputable section

namespace EstablishedExternalResults

lemma windSum_append (x : ℂ) : ∀ (l₁ : List ℂ) (v : ℂ) (l₂ : List ℂ),
    windSum x (l₁ ++ v :: l₂) = windSum x (l₁ ++ [v]) + windSum x (v :: l₂)
  | [], v, l₂ => by simp [windSum]
  | [a], v, l₂ => by simp [windSum]
  | a :: b :: l₁, v, l₂ => by
    have ih := windSum_append x (b :: l₁) v l₂
    simp only [List.cons_append, windSum] at ih ⊢
    rw [ih]; ring

lemma polyline_append : ∀ (l₁ : List ℂ) (v : ℂ) (l₂ : List ℂ),
    polyline (l₁ ++ v :: l₂) = polyline (l₁ ++ [v]) ∪ polyline (v :: l₂)
  | [], v, l₂ => by
    simp only [List.nil_append, polyline]
    rw [union_eq_right.2]
    intro z hz; rw [mem_singleton_iff] at hz; subst hz; exact head_mem_polyline _ _
  | [a], v, l₂ => by
    simp only [List.cons_append, List.nil_append, polyline]
    congr 1
    exact (union_eq_left.2 (singleton_subset_iff.2 (right_mem_segment ℝ a v))).symm
  | a :: b :: l₁, v, l₂ => by
    have ih := polyline_append (b :: l₁) v l₂
    simp only [List.cons_append, polyline] at ih ⊢
    rw [ih, union_assoc]

lemma continuousAt_windSum' (x : ℂ) (l : List ℂ) (hx : x ∉ polyline l) :
    ContinuousAt (fun y => windSum y l) x := by
  cases l with
  | nil => simp only [windSum]; exact continuousAt_const
  | cons u l => exact continuousAt_windSum x u l hx

/-- Bounds for the jump of the winding sum across an edge in arbitrary position. -/
lemma windSum_jump_bounds {pre post : List ℂ} {A B : ℂ} (hAB : A ≠ B)
    (hm : (A + B) / 2 ∉ polyline (pre ++ [A]) ∪ polyline (B :: post)) :
    ∃ r > 0, ∀ x y : ℂ, dist x ((A + B) / 2) < r → dist y ((A + B) / 2) < r →
      0 < (wc A B x).im → (wc A B y).im < 0 →
      0 < windSum x (pre ++ A :: B :: post) - windSum y (pre ++ A :: B :: post) ∧
      windSum x (pre ++ A :: B :: post) - windSum y (pre ++ A :: B :: post) < 3 * π := by
  set m := (A + B) / 2 with hmdef
  rw [mem_union, not_or] at hm
  set F : ℂ → ℝ := fun z => windSum z (pre ++ [A]) + windSum z (B :: post) with hF
  have hFc : ContinuousAt F m :=
    (continuousAt_windSum' m _ hm.1).add (continuousAt_windSum m B post hm.2)
  have hsplit : ∀ z, windSum z (pre ++ A :: B :: post) =
      F z + arg ((B - z) / (A - z)) := by
    intro z
    rw [windSum_append z pre A (B :: post)]
    simp only [hF, windSum]; ring
  obtain ⟨δ, hδ, hδg⟩ := Metric.continuousAt_iff.mp hFc (π / 2) (by positivity)
  have hba : 0 < ‖B - A‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hAB.symm)
  have hwm : wc A B m = 1 / 2 := by
    have : B - A ≠ 0 := sub_ne_zero.mpr hAB.symm
    simp only [wc, hmdef]; field_simp; ring
  refine ⟨min δ (‖B - A‖ / 2), lt_min hδ (by positivity), ?_⟩
  have key : ∀ x : ℂ, dist x m < min δ (‖B - A‖ / 2) →
      ‖wc A B x - 1 / 2‖ < 1 / 2 ∧ arg ((B - x) / (A - x)) = arg ((wc A B x - 1) / wc A B x) ∧
        |F x - F m| < π / 2 := by
    intro x hx
    have hx1 := hx.trans_le (min_le_left _ _)
    have hx2 := hx.trans_le (min_le_right _ _)
    have hn := norm_wc_sub hAB x m
    rw [hwm] at hn
    have hw : ‖wc A B x - 1 / 2‖ < 1 / 2 := by
      by_contra hc; push_neg at hc
      have : ‖B - A‖ / 2 ≤ dist x m := by rw [← hn]; nlinarith
      linarith
    refine ⟨hw, ?_, ?_⟩
    · have hw0 : wc A B x ≠ 0 := by rintro h0; rw [h0] at hw; norm_num at hw
      congr 1
      conv_lhs => rw [eq_param hAB x]
      exact div_param_eq hAB hw0
    · have := hδg hx1
      rwa [Real.dist_eq] at this
  intro x y hx hy hxi hyi
  obtain ⟨hwx, ex, gx⟩ := key x hx
  obtain ⟨hwy, ey, gy⟩ := key y hy
  have h1 := arg_quot_gt hwx hxi
  have h2 := arg_quot_lt hwy hyi
  have h3 := arg_le_pi ((wc A B x - 1) / wc A B x)
  have h4 := neg_pi_lt_arg ((wc A B y - 1) / wc A B y)
  rw [hsplit, hsplit, ex, ey]
  rw [abs_lt] at gx gy
  constructor <;> linarith

lemma wc_im_scale {A B m x : ℂ} (hm : wc A B m = 1 / 2) (ε : ℝ) :
    (wc A B (m + ε * (x - m))).im = ε * (wc A B x).im := by
  have h1 : wc A B (m + ε * (x - m)) = wc A B m + ε * (wc A B x - wc A B m) := by
    simp only [wc]; ring
  rw [h1, hm]
  simp

/-- **Exact jump of the winding sum.**  Let `Γ = pre ++ A :: B :: post` be a closed polygonal
path whose edge `[A, B]` has midpoint `m` off the rest of the path.  If the segment `[y, x]`
passes through `m`, meets `Γ` only at `m`, and `x`, `y` lie to the left and right of `A → B`, then
the winding sums at `x` and `y` differ by exactly `2π`. -/
theorem windSum_jump_exact {u : ℂ} {l pre post : List ℂ} {A B x y : ℂ} (hAB : A ≠ B)
    (hsplit : u :: l = pre ++ A :: B :: post) (hc : (u :: l).getLast (by simp) = u)
    (hm : (A + B) / 2 ∉ polyline (pre ++ [A]) ∪ polyline (B :: post))
    (hmseg : (A + B) / 2 ∈ segment ℝ y x)
    (hseg : ∀ z ∈ segment ℝ y x, z ∈ polyline (u :: l) → z = (A + B) / 2)
    (hxi : 0 < (wc A B x).im) (hyi : (wc A B y).im < 0) :
    windSum x (u :: l) - windSum y (u :: l) = 2 * π := by
  set m := (A + B) / 2 with hmdef
  have hwm : wc A B m = 1 / 2 := by
    have : B - A ≠ 0 := sub_ne_zero.mpr hAB.symm
    simp only [wc, hmdef]; field_simp; ring
  have hmΓ : m ∈ polyline (u :: l) := by
    rw [hsplit, polyline_append]
    right; left
    exact ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by
      simp only [hmdef, Complex.real_smul]; push_cast; ring⟩
  have hxm : x ≠ m := by
    rintro rfl; rw [hwm] at hxi; norm_num at hxi
  have hym : y ≠ m := by
    rintro rfl; rw [hwm] at hyi; norm_num at hyi
  have hxΓ : x ∉ polyline (u :: l) := fun h => hxm (hseg x (right_mem_segment ℝ y x) h)
  have hyΓ : y ∉ polyline (u :: l) := fun h => hym (hseg y (left_mem_segment ℝ y x) h)
  obtain ⟨r, hr, hjump⟩ := windSum_jump_bounds (pre := pre) (post := post) hAB hm
  -- points near `m` on the two halves of the segment
  have hpos : 0 < ‖x - m‖ + ‖y - m‖ + 1 := by positivity
  set ε : ℝ := min 1 (r / (2 * (‖x - m‖ + ‖y - m‖ + 1))) with hε
  have hε0 : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεr : ε * (‖x - m‖ + ‖y - m‖ + 1) ≤ r / 2 := by
    have := min_le_right 1 (r / (2 * (‖x - m‖ + ‖y - m‖ + 1)))
    rw [← hε, le_div_iff₀ (by positivity)] at this
    linarith
  set x' := m + (ε : ℂ) * (x - m)
  set y' := m + (ε : ℂ) * (y - m)
  have hdx : dist x' m < r := by
    rw [dist_eq_norm, show x' - m = (ε : ℂ) * (x - m) by simp [x'], norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hε0.le]
    nlinarith [norm_nonneg (y - m)]
  have hdy : dist y' m < r := by
    rw [dist_eq_norm, show y' - m = (ε : ℂ) * (y - m) by simp [y'], norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hε0.le]
    nlinarith [norm_nonneg (x - m)]
  have hx'i : 0 < (wc A B x').im := by rw [wc_im_scale hwm]; positivity
  have hy'i : (wc A B y').im < 0 := by rw [wc_im_scale hwm]; nlinarith
  obtain ⟨hlo, hhi⟩ := hjump x' y' hdx hdy hx'i hy'i
  rw [← hsplit] at hlo hhi
  -- the winding sum is constant from `x'` to `x` and from `y'` to `y`
  have hmx : segment ℝ m x ⊆ segment ℝ y x :=
    (convex_segment y x).segment_subset hmseg (right_mem_segment ℝ y x)
  have hmy : segment ℝ m y ⊆ segment ℝ y x :=
    (convex_segment y x).segment_subset hmseg (left_mem_segment ℝ y x)
  have side : ∀ p : ℂ, p ≠ m → segment ℝ m p ⊆ segment ℝ y x →
      windSum (m + (ε : ℂ) * (p - m)) (u :: l) = windSum p (u :: l) := by
    intro p hp hsub
    have hq : m + (ε : ℂ) * (p - m) ∈ segment ℝ m p :=
      ⟨1 - ε, ε, by linarith, hε0.le, by ring, by
        simp only [Complex.real_smul]; push_cast; ring⟩
    have hsub' : segment ℝ (m + (ε : ℂ) * (p - m)) p ⊆ segment ℝ m p :=
      (convex_segment m p).segment_subset hq (right_mem_segment ℝ m p)
    refine windSum_eq_of_isPreconnected (convex_segment _ p).isPreconnected u l hc ?_
      (left_mem_segment ℝ _ p) (right_mem_segment ℝ _ p)
    intro z hz hzΓ
    have hzm := hseg z (hsub (hsub' hz)) hzΓ
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
    have : a • (m + (ε : ℂ) * (p - m)) + b • p - m = ((a * ε + b : ℝ) : ℂ) * (p - m) := by
      simp only [Complex.real_smul]
      have hab' : (a : ℂ) + b = 1 := by exact_mod_cast hab
      push_cast
      linear_combination m * hab'
    rw [← sub_eq_zero, this, mul_eq_zero, sub_eq_zero] at hzm
    rcases hzm with h | h
    · have : a * ε + b = 0 := by exact_mod_cast h
      have : a * ε = 0 := by nlinarith [mul_nonneg ha hε0.le]
      have ha0 : a = 0 := by
        rcases mul_eq_zero.1 this with h | h
        · exact h
        · exact absurd h hε0.ne'
      have hb0 : b = 0 := by nlinarith [mul_nonneg ha hε0.le]
      rw [ha0, hb0] at hab; norm_num at hab
    · exact hp h
  have ex := side x hxm hmx
  have ey := side y hym hmy
  rw [ex, ey] at hlo hhi
  obtain ⟨a, ha⟩ := windSum_mem_int x u l hxΓ hc
  obtain ⟨b, hb⟩ := windSum_mem_int y u l hyΓ hc
  rw [ha, hb] at hlo hhi ⊢
  have hπ := Real.pi_pos
  have h1 : (0 : ℝ) < (a - b : ℤ) := by
    push_cast; nlinarith
  have h2 : ((a - b : ℤ) : ℝ) < 2 := by
    push_cast; nlinarith
  have h1' : 0 < a - b := by exact_mod_cast h1
  have h2' : a - b < 2 := by exact_mod_cast h2
  have : a - b = 1 := by omega
  have : (a : ℝ) - b = 1 := by exact_mod_cast this
  linear_combination 2 * π * this

end EstablishedExternalResults
end

end WindingJump

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `Crosscut`
-/

section Crosscut

/-!
# The shore of a crosscut

A chain of unit "gates" `{a l, a l + u}` (`l ≤ k`), consecutive gates spanning unit rhombi, is
closed up into a polygon: the spine through the gate midpoints, two short pieces leaving the
first and last gate through regions avoided by the configuration, and three further segments in
such regions.  Winding numbers about this polygon cut the configuration into a nonempty proper
part `S` such that every unit pair joining `S` to its complement is a gate, crossed always in
the same direction.  Moreover `S` lies in every half-plane containing all vertices of the
polygon.
-/

open scoped BigOperators Real ComplexConjugate
open Set EstablishedExternalResults

@[expose] public noncomputable section

open Classical

namespace Erdos99

/-! ## Transporting polygonal paths to `ℂ` -/

lemma toC_image_segment (x y : Plane) : toC '' segment ℝ x y = segment ℝ (toC x) (toC y) := by
  have h := image_segment ℝ (toC.toLinearEquiv.toLinearMap.toAffineMap) x y
  simpa using h

lemma polyline_map_toC_subset {H : Set Plane} : ∀ (x : Plane) (l : List Plane),
    List.IsChain (fun x y => segment ℝ x y ⊆ H) (x :: l) → x ∈ H →
      polyline ((x :: l).map toC) ⊆ toC '' H
  | x, [], _, hx => by simp [polyline, hx]
  | x, y :: l, h, _ => by
    rw [List.isChain_cons_cons] at h
    simp only [List.map_cons, polyline]
    refine union_subset ?_ ?_
    · rw [← toC_image_segment]; exact image_mono h.1
    · have := polyline_map_toC_subset y l h.2 (h.1 (right_mem_segment ℝ x y))
      simpa using this

lemma inner_toC_re (a b : Plane) : ((toC a) * conj (toC b)).re = inner ℝ b a := by
  rw [← toC.inner_map_map b a, Complex.inner]

/-! ## Zig-zag lists -/

/-- `A a, B a, A (a+1), B (a+1), …` (`n` pairs). -/
def zig (A B : ℕ → Plane) : ℕ → ℕ → List Plane
  | _, 0 => []
  | a, n + 1 => A a :: B a :: zig A B (a + 1) n

lemma zig_split (A B : ℕ → Plane) : ∀ (n a m : ℕ),
    zig A B a (n + (m + 1)) = zig A B a n ++ A (a + n) :: B (a + n) :: zig A B (a + n + 1) m
  | 0, a, m => by simp [zig]
  | n + 1, a, m => by
    have e : zig A B a (n + 1 + (m + 1)) = A a :: B a :: zig A B (a + 1) (n + (m + 1)) := by
      rw [show n + 1 + (m + 1) = (n + (m + 1)) + 1 by omega]; rfl
    rw [e, zig_split A B n (a + 1) m, show a + 1 + n = a + (n + 1) by omega]
    rfl

lemma chain_zig (R : Plane → Plane → Prop) (A B : ℕ → Plane) (Z : Plane) (rest : List Plane)
    (hZ : List.IsChain R (Z :: rest)) : ∀ (n a : ℕ),
    (∀ j, a ≤ j → j < a + n → R (A j) (B j)) →
    (∀ j, a ≤ j → j + 1 < a + n → R (B j) (A (j + 1))) →
    (0 < n → R (B (a + n - 1)) Z) → List.IsChain R (zig A B a n ++ Z :: rest)
  | 0, a, _, _, _ => by simpa [zig] using hZ
  | n + 1, a, h1, h2, h3 => by
    simp only [zig, List.cons_append]
    rw [List.isChain_cons_cons]
    refine ⟨h1 a le_rfl (by omega), ?_⟩
    have ih := chain_zig R A B Z rest hZ n (a + 1) (fun j hj hj' => h1 j (by omega) (by omega))
      (fun j hj hj' => h2 j (by omega) (by omega))
      (fun hn => by
        have := h3 (by omega); rwa [show a + (n + 1) - 1 = a + 1 + n - 1 by omega] at this)
    cases n with
    | zero =>
      simp only [zig, List.nil_append, List.isChain_cons_cons]
      exact ⟨by simpa using h3 (by omega), hZ⟩
    | succ n =>
      simp only [zig, List.cons_append] at ih ⊢
      rw [List.isChain_cons_cons]
      exact ⟨h2 a le_rfl (by omega), ih⟩

lemma chain_cons_zig (R : Plane → Plane → Prop) (A B : ℕ → Plane) (P Z : Plane)
    (rest : List Plane) (hZ : List.IsChain R (Z :: rest)) (n a : ℕ)
    (h0 : 0 < n → R P (A a)) (h0' : n = 0 → R P Z)
    (h1 : ∀ j, a ≤ j → j < a + n → R (A j) (B j))
    (h2 : ∀ j, a ≤ j → j + 1 < a + n → R (B j) (A (j + 1)))
    (h3 : 0 < n → R (B (a + n - 1)) Z) : List.IsChain R (P :: (zig A B a n ++ Z :: rest)) := by
  have hc := chain_zig R A B Z rest hZ n a h1 h2 h3
  cases n with
  | zero =>
    simp only [zig, List.nil_append] at hc ⊢
    rw [List.isChain_cons_cons]; exact ⟨h0' rfl, hc⟩
  | succ n =>
    simp only [zig, List.cons_append] at hc ⊢
    rw [List.isChain_cons_cons]
    exact ⟨h0 (by omega), hc⟩

/-! ## Rhombus coordinates -/

lemma frame_decomp {u N : Plane} (hu : ‖u‖ = 1) (hN : N = rot u ∨ N = -rot u) (w : Plane) :
    w = inner ℝ w u • u + inner ℝ w N • N := by
  have h := norm_sq_coord u
  rw [hu] at h
  rcases hN with rfl | rfl
  all_goals
    rw [plane_ext_iff]
    simp only [inner_neg_right, smul_neg, PiLp.add_apply, PiLp.smul_apply,
      smul_eq_mul, inner_coord, rot, PiLp.neg_apply]
    simp
    constructor
    · linear_combination (w 0) * h
    · linear_combination (w 1) * h

lemma inner_sq_add_inner_N_sq {u N : Plane} (hN : N = rot u ∨ N = -rot u) (w : Plane) :
    inner ℝ w u ^ 2 + inner ℝ w N ^ 2 = ‖w‖ ^ 2 * ‖u‖ ^ 2 := by
  rcases hN with rfl | rfl
  · exact inner_sq_add_inner_rot_sq u w
  · rw [inner_neg_right, neg_sq]; exact inner_sq_add_inner_rot_sq u w

lemma inner_N_gt {u N w : Plane} (hu : ‖u‖ = 1) (hN : N = rot u ∨ N = -rot u) (hw : ‖w‖ = 1)
    (hi : |inner ℝ w u| < 1 / 2) : 3 / 4 < inner ℝ w N ^ 2 := by
  have h := inner_sq_add_inner_N_sq hN w
  rw [hu, hw] at h
  have : inner ℝ w u ^ 2 < 1 / 4 := by
    have := abs_lt.1 hi; nlinarith
  linarith

lemma mid_add_mem_para {u N w a : Plane} (hu : ‖u‖ = 1) (hN : N = rot u ∨ N = -rot u)
    (hw : ‖w‖ = 1) (hi : |inner ℝ w u| < 1 / 2) (hp : 0 < inner ℝ w N) {s : ℝ} (hs0 : 0 < s)
    (hs1 : s ≤ 1 / 4) : a + (1 / 2 : ℝ) • u + s • N ∈ paraOpen a u w := by
  have hg := inner_N_gt hu hN hw hi
  set c := inner ℝ w N
  set d := inner ℝ w u
  have hc1 : 1 / 2 < c := by nlinarith
  have hdec := frame_decomp hu hN w
  refine ⟨1 / 2 - s / c * d, s / c, ?_, ?_, by positivity, ?_, ?_⟩
  · have : s / c * |d| < 1 / 2 := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]; nlinarith [abs_nonneg d]
    have := neg_abs_le d
    have : s / c * d ≤ s / c * |d| := mul_le_mul_of_nonneg_left (le_abs_self d) (by positivity)
    linarith
  · have : -(s / c * d) < 1 / 2 := by
      have h1 : s / c * |d| < 1 / 2 := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]; nlinarith [abs_nonneg d]
      have : -(s / c * d) ≤ s / c * |d| := by
        rw [← mul_neg]; exact mul_le_mul_of_nonneg_left (neg_le_abs d) (by positivity)
      linarith
    linarith
  · rw [div_lt_one (by linarith)]; linarith
  · conv_lhs => rw [show s • N = (s / c) • (c • N) by rw [smul_smul, div_mul_cancel₀ _ (by linarith)]]
    have : c • N = w - d • u := by rw [hdec]; simp [c, d]
    rw [this]
    module

lemma mid_sub_mem_para {u N w a : Plane} (hu : ‖u‖ = 1) (hN : N = rot u ∨ N = -rot u)
    (hw : ‖w‖ = 1) (hi : |inner ℝ w u| < 1 / 2) (hp : 0 < inner ℝ w N) {s : ℝ} (hs0 : 0 < s)
    (hs1 : s ≤ 1 / 4) : a + w + (1 / 2 : ℝ) • u - s • N ∈ paraOpen a u w := by
  have hg := inner_N_gt hu hN hw hi
  set c := inner ℝ w N
  set d := inner ℝ w u
  have hc1 : 1 / 2 < c := by nlinarith
  have hdec := frame_decomp hu hN w
  have hsc : s / c < 1 / 2 := by rw [div_lt_iff₀ (by linarith)]; linarith
  have h1 : s / c * |d| < 1 / 2 := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]; nlinarith [abs_nonneg d]
  have h2 : s / c * d ≤ s / c * |d| := mul_le_mul_of_nonneg_left (le_abs_self d) (by positivity)
  have h3 : -(s / c * d) ≤ s / c * |d| := by
    rw [← mul_neg]; exact mul_le_mul_of_nonneg_left (neg_le_abs d) (by positivity)
  refine ⟨1 / 2 + s / c * d, 1 - s / c, by linarith, by linarith, by linarith, by
    have : 0 < s / c := by positivity
    linarith, ?_⟩
  conv_lhs => rw [show s • N = (s / c) • (c • N) by rw [smul_smul, div_mul_cancel₀ _ (by linarith)]]
  have : c • N = w - d • u := by rw [hdec]; simp [c, d]
  rw [this]
  module

/-! ## Further helpers -/

lemma toC_apply' (x : Plane) : toC x = (x 0 : ℂ) + (x 1 : ℂ) * Complex.I := by
  simp [toC, Complex.orthonormalBasisOneI, Complex.basisOneI]

lemma toC_rot (u : Plane) : toC (rot u) = Complex.I * toC u := by
  rw [toC_apply', toC_apply']
  simp [rot]
  ring_nf
  simp [Complex.I_sq]

lemma mem_zig {A B : ℕ → Plane} : ∀ (n a : ℕ) (V : Plane), V ∈ zig A B a n →
    ∃ j, a ≤ j ∧ j < a + n ∧ (V = A j ∨ V = B j)
  | 0, a, V, h => by simp [zig] at h
  | n + 1, a, V, h => by
    simp only [zig, List.mem_cons] at h
    rcases h with rfl | rfl | h
    · exact ⟨a, le_rfl, by omega, Or.inl rfl⟩
    · exact ⟨a, le_rfl, by omega, Or.inr rfl⟩
    · obtain ⟨j, h1, h2, h3⟩ := mem_zig n (a + 1) V h
      exact ⟨j, by omega, by omega, h3⟩

/-- No point of a separated set lies in the open parallelogram of one of its unit rhombi. -/
lemma not_mem_paraOpen_of_rhombus {X : Finset Plane} (hX : IsSeparated X) {a u w : Plane}
    (hV : ({a, a + u, a + w, a + u + w} : Finset Plane) ⊆ X) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (hi : |inner ℝ u w| < 1 / 2) {x : Plane} (hx : x ∈ X) : x ∉ paraOpen a u w := by
  have h := cr_ne_zero_of_rep hu hw hi
  intro hxo
  have hxV := mem_of_mem_paraClosed hX hu hw hV hx (paraOpen_subset_paraClosed a u w hxo)
  refine not_mem_paraOpen_of_mem_sides h ?_ hxo
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxV
  rcases hxV with rfl | rfl | rfl | rfl
  · exact Or.inl (left_mem_segment ℝ _ _)
  · exact Or.inl (right_mem_segment ℝ _ _)
  · exact Or.inr (Or.inr (Or.inr (right_mem_segment ℝ _ _)))
  · exact Or.inr (Or.inl (right_mem_segment ℝ _ _))

lemma mid_mem_segment (p u : Plane) : p + (1 / 2 : ℝ) • u ∈ segment ℝ p (p + u) :=
  add_smul_mem_segment p u (by norm_num) (by norm_num)

lemma mid_not_mem {X : Finset Plane} (hX : IsSeparated X) {p u : Plane} (hu : ‖u‖ = 1)
    (hp : p ∈ X) : p + (1 / 2 : ℝ) • u ∉ X := by
  intro h
  have hne : p + (1 / 2 : ℝ) • u ≠ p := by
    intro he
    have : (1 / 2 : ℝ) • u = 0 := by
      have := congrArg (fun z => z - p) he; simpa using this
    rw [smul_eq_zero] at this
    rcases this with h0 | h0
    · norm_num at h0
    · rw [h0, norm_zero] at hu; norm_num at hu
  have := hX _ h p hp hne
  rw [dist_eq_norm, show p + (1 / 2 : ℝ) • u - p = (1 / 2 : ℝ) • u by abel, norm_smul, hu] at this
  norm_num at this

/-- The heights of the gate midpoints increase strictly. -/
lemma mid_inner_strictMono {u N : Plane} {k : ℕ} {a w : ℕ → Plane}
    (hstep : ∀ l < k, a (l + 1) = a l + w l ∧ ‖w l‖ = 1 ∧ |inner ℝ (w l) u| < 1 / 2 ∧
      0 < inner ℝ (w l) N) :
    ∀ i j, i < j → j ≤ k → inner ℝ (a i + (1 / 2 : ℝ) • u) N < inner ℝ (a j + (1 / 2 : ℝ) • u) N := by
  intro i j hij hjk
  induction j, hij using Nat.le_induction with
  | base =>
    obtain ⟨e, -, -, hp⟩ := hstep i (by omega)
    rw [e, show a i + w i + (1 / 2 : ℝ) • u = (a i + (1 / 2 : ℝ) • u) + w i by abel,
      inner_add_left (a i + (1 / 2 : ℝ) • u) (w i)]
    linarith
  | succ j hj ih =>
    obtain ⟨e, -, -, hp⟩ := hstep j (by omega)
    have := ih (by omega)
    rw [e, show a j + w j + (1 / 2 : ℝ) • u = (a j + (1 / 2 : ℝ) • u) + w j by abel,
      inner_add_left (a j + (1 / 2 : ℝ) • u) (w j)]
    linarith

end Erdos99
end

end Crosscut

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `CrosscutShore`
-/

section CrosscutShore

/-!
# The shore of a crosscut: main statement

See `Crosscut` for the setting.
-/

open scoped BigOperators Real ComplexConjugate
open Set EstablishedExternalResults

@[expose] public noncomputable section

open Classical

namespace Erdos99

lemma wc_gate_im {m u N : Plane} (hu : ‖u‖ = 1) (σ : ℝ) (ε : ℝ) (hε : ε = 1 ∨ ε = -1)
    (hN : N = ε • rot u) :
    (wc (toC (m - (1 / 4 : ℝ) • N)) (toC (m + (1 / 4 : ℝ) • N)) (toC (m + σ • u))).im =
      -2 * σ * ε := by
  have hU : toC u ≠ 0 := by
    intro h; have := congrArg norm h; rw [norm_toC, hu, norm_zero] at this; norm_num at this
  have hε2 : (ε : ℂ) ^ 2 = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hε0 : (ε : ℂ) ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have e : wc (toC (m - (1 / 4 : ℝ) • N)) (toC (m + (1 / 4 : ℝ) • N)) (toC (m + σ • u)) =
      (1 / 2 : ℂ) - 2 * σ * ε * Complex.I := by
    rw [wc, hN]
    simp only [map_sub, map_add, map_smul, toC_rot, Complex.real_smul]
    push_cast
    have hden : toC m + 1 / 4 * (↑ε * (Complex.I * toC u)) -
        (toC m - 1 / 4 * (↑ε * (Complex.I * toC u))) = (ε : ℂ) * Complex.I * toC u / 2 := by
      ring
    rw [hden, div_eq_iff (by simp [hU, hε0, Complex.I_ne_zero])]
    linear_combination (-(σ:ℂ) * toC u) * hε2 + (σ * ε ^ 2 * toC u) * Complex.I_sq
  rw [e]
  simp

lemma vertex_lower {A B : ℕ → Plane} {Ps Pe Qe Qs ω : Plane} {c : ℝ} {k : ℕ}
    (h1 : c ≤ inner ℝ Ps ω) (h2 : c ≤ inner ℝ Pe ω) (h3 : c ≤ inner ℝ Qe ω)
    (h4 : c ≤ inner ℝ Qs ω) (h5 : ∀ j < k + 1, c ≤ inner ℝ (A j) ω ∧ c ≤ inner ℝ (B j) ω) :
    ∀ V ∈ Ps :: (zig A B 0 (k + 1) ++ [Pe, Qe, Qs, Ps]), c ≤ inner ℝ V ω := by
  intro V hV
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hV
  rcases hV with rfl | hV | rfl | rfl | rfl | rfl
  · exact h1
  · obtain ⟨j, -, hj, rfl | rfl⟩ := mem_zig _ _ _ hV
    · exact (h5 j (by omega)).1
    · exact (h5 j (by omega)).2
  · exact h2
  · exact h3
  · exact h4
  · exact h1

lemma half_sum_eq (p u : Plane) : (1 / 2 : ℝ) • (p + (p + u)) = p + (1 / 2 : ℝ) • u := by
  module

lemma mem_segment_line_plane {m d y : Plane} {s1 s2 : ℝ}
    (hy : y ∈ segment ℝ (m + s1 • d) (m + s2 • d)) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ y = m + ((1 - θ) * s1 + θ * s2) • d := by
  obtain ⟨α, β, hα, hβ, hab, rfl⟩ := hy
  refine ⟨β, hβ, by linarith, ?_⟩
  rw [show α = 1 - β by linarith]
  module

set_option maxHeartbeats 1600000 in
/-- **The shore of a crosscut.**  Let `{a l, a l + u}` (`l ≤ k`) be unit gates of a separated set
`X`, consecutive gates spanning unit rhombi with steps `w l` of positive height along the unit
normal `N` of `u`.  Suppose a set `Safe`, avoided by `X` and by all unit segments of `X`,
contains the outward normal pieces of length one at the first and last gate midpoints and three
segments `Pₑ Qₑ`, `Qₑ Qₛ`, `Qₛ Pₛ` closing up the polygon.  Then a nonempty proper part `S` of
`X` has all its unit connections to the complement equal to one vector `z = ±u`, and lies in
every closed half-plane containing the vertices of the polygon. -/
theorem shore_of_crosscut {X : Finset Plane} (hX : IsSeparated X) {u N : Plane} (hu : ‖u‖ = 1)
    (hN : N = rot u ∨ N = -rot u) {k : ℕ} (a w : ℕ → Plane)
    (hgate : ∀ l ≤ k, a l ∈ X ∧ a l + u ∈ X)
    (hstep : ∀ l < k, a (l + 1) = a l + w l ∧ ‖w l‖ = 1 ∧ |inner ℝ (w l) u| < 1 / 2 ∧
      0 < inner ℝ (w l) N)
    (Safe : Set Plane) (hSX : ∀ x ∈ X, x ∉ Safe)
    (hSU : ∀ p ∈ X, ∀ q ∈ X, dist p q = 1 → Disjoint (segment ℝ p q) Safe)
    (hstart : ∀ s : ℝ, 0 < s → s ≤ 1 → a 0 + (1 / 2 : ℝ) • u - s • N ∈ Safe)
    (hend : ∀ s : ℝ, 0 < s → s ≤ 1 → a k + (1 / 2 : ℝ) • u + s • N ∈ Safe)
    (Qe Qs : Plane) (h1 : segment ℝ (a k + (1 / 2 : ℝ) • u + N) Qe ⊆ Safe)
    (h2 : segment ℝ Qe Qs ⊆ Safe) (h3 : segment ℝ Qs (a 0 + (1 / 2 : ℝ) • u - N) ⊆ Safe) :
    ∃ S ⊆ X, S.Nonempty ∧ (∃ q ∈ X, q ∉ S) ∧ ∃ z : Plane, (z = u ∨ z = -u) ∧
      (∀ p ∈ S, ∀ q ∈ X, q ∉ S → dist p q = 1 → p - q = z) ∧
      ∀ p ∈ S, ∀ (ω : Plane) (c : ℝ),
        c ≤ inner ℝ (a 0 + (1 / 2 : ℝ) • u - N) ω → c ≤ inner ℝ (a k + (1 / 2 : ℝ) • u + N) ω →
        c ≤ inner ℝ Qe ω → c ≤ inner ℝ Qs ω →
        (∀ l ≤ k, c ≤ inner ℝ (a l + (1 / 2 : ℝ) • u - (1 / 4 : ℝ) • N) ω ∧
          c ≤ inner ℝ (a l + (1 / 2 : ℝ) • u + (1 / 4 : ℝ) • N) ω) →
        c ≤ inner ℝ p ω := by
  -- notation
  obtain ⟨mid, hmid⟩ : ∃ mid : ℕ → Plane, mid = fun l => a l + (1 / 2 : ℝ) • u := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℕ → Plane, A = fun l => mid l - (1 / 4 : ℝ) • N := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℕ → Plane, B = fun l => mid l + (1 / 4 : ℝ) • N := ⟨_, rfl⟩
  obtain ⟨Ps, hPs⟩ : ∃ Ps : Plane, Ps = mid 0 - N := ⟨_, rfl⟩
  obtain ⟨Pe, hPe⟩ : ∃ Pe : Plane, Pe = mid k + N := ⟨_, rfl⟩
  obtain ⟨Safe', hSafe'⟩ : ∃ Safe' : Set Plane,
      Safe' = Safe ∪ {y | ∃ l < k, y ∈ paraOpen (a l) u (w l)} := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : Set Plane, M = {y | ∃ l ≤ k, y = mid l} := ⟨_, rfl⟩
  have hmidl : ∀ l, mid l = a l + (1 / 2 : ℝ) • u := fun l => by rw [hmid]
  have hAl : ∀ l, A l = mid l - (1 / 4 : ℝ) • N := fun l => by rw [hA]
  have hBl : ∀ l, B l = mid l + (1 / 4 : ℝ) • N := fun l => by rw [hB]
  have hNn : ‖N‖ = 1 := by rcases hN with rfl | rfl <;> simp [norm_rot, hu]
  -- rhombi
  have hrh : ∀ l < k, ({a l, a l + u, a l + w l, a l + u + w l} : Finset Plane) ⊆ X := by
    intro l hl
    obtain ⟨e, -, -, -⟩ := hstep l hl
    obtain ⟨g1, g2⟩ := hgate l hl.le
    obtain ⟨g3, g4⟩ := hgate (l + 1) hl
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact g1
    · exact g2
    · rw [← e]; exact g3
    · rw [show a l + u + w l = a (l + 1) + u by rw [e]; abel]; exact g4
  have hiw : ∀ l < k, |inner ℝ u (w l)| < 1 / 2 := fun l hl => by
    rw [real_inner_comm]; exact (hstep l hl).2.2.1
  -- the safe region
  have hSX' : ∀ x ∈ X, x ∉ Safe' := by
    intro x hx hxS
    rw [hSafe'] at hxS
    rcases hxS with hxS | ⟨l, hl, hxl⟩
    · exact hSX x hx hxS
    · exact not_mem_paraOpen_of_rhombus hX (hrh l hl) hu (hstep l hl).2.1 (hiw l hl) hx hxl
  have hSU' : ∀ p ∈ X, ∀ q ∈ X, dist p q = 1 → Disjoint (segment ℝ p q) Safe' := by
    intro p hp q hq hpq
    rw [hSafe', Set.disjoint_union_right]
    refine ⟨hSU p hp q hq hpq, ?_⟩
    rw [Set.disjoint_left]
    rintro y hy ⟨l, hl, hyl⟩
    exact Set.disjoint_left.1 (unit_seg_disjoint_paraOpen hX (hrh l hl) hu (hstep l hl).2.1
      (hiw l hl) hp hq hpq) hy hyl
  have hpara : ∀ l < k, paraOpen (a l) u (w l) ⊆ Safe' := fun l hl y hy => by
    rw [hSafe']; exact Or.inr ⟨l, hl, hy⟩
  have hSafe_sub : Safe ⊆ Safe' := fun y hy => by rw [hSafe']; exact Or.inl hy
  -- midpoints
  have hmidX : ∀ l ≤ k, mid l ∉ X := fun l hl => by
    rw [hmidl]; exact mid_not_mem hX hu (hgate l hl).1
  have hmidS : ∀ l ≤ k, mid l ∉ Safe' := by
    intro l hl hS
    have hseg : mid l ∈ segment ℝ (a l) (a l + u) := by rw [hmidl]; exact mid_mem_segment _ _
    have hd : dist (a l) (a l + u) = 1 := by
      rw [dist_eq_norm, show a l - (a l + u) = -u by abel, norm_neg, hu]
    exact Set.disjoint_left.1 (hSU' _ (hgate l hl).1 _ (hgate l hl).2 hd) hseg hS
  have hmid_inj : ∀ i ≤ k, ∀ j ≤ k, mid i = mid j → i = j := by
    intro i hi j hj he
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := mid_inner_strictMono hstep i j h hj
      rw [← hmidl, ← hmidl, he] at this; exact lt_irrefl _ this
    · have := mid_inner_strictMono hstep j i h hi
      rw [← hmidl, ← hmidl, he] at this; exact lt_irrefl _ this
  -- segments of the polygon
  have hup : ∀ j < k, ∀ s : ℝ, 0 < s → s ≤ 1 / 4 → mid j + s • N ∈ Safe' := by
    intro j hj s hs0 hs1
    obtain ⟨-, hw, hi, hp⟩ := hstep j hj
    apply hpara j hj
    rw [hmidl]; exact mid_add_mem_para hu hN hw hi hp hs0 hs1
  have hdown : ∀ j < k, ∀ s : ℝ, 0 < s → s ≤ 1 / 4 → mid (j + 1) - s • N ∈ Safe' := by
    intro j hj s hs0 hs1
    obtain ⟨e, hw, hi, hp⟩ := hstep j hj
    apply hpara j hj
    rw [hmidl, e]; exact mid_sub_mem_para hu hN hw hi hp hs0 hs1
  have F1 : ∀ j ≤ k, segment ℝ (A j) (B j) ⊆ Safe' ∪ {mid j} := by
    intro j hj y hy
    rw [hAl, hBl, sub_eq_add_neg, ← neg_smul] at hy
    obtain ⟨θ, hθ0, hθ1, rfl⟩ := mem_segment_line_plane hy
    set s := (1 - θ) * -(1 / 4 : ℝ) + θ * (1 / 4) with hs
    rcases lt_trichotomy s 0 with hlt | heq | hgt
    · left
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · apply hSafe_sub
        have := hstart (-s) (by linarith) (by nlinarith)
        rw [hmidl]; rwa [neg_smul, sub_neg_eq_add] at this
      · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        have := hdown i (by omega) (-s) (by linarith) (by nlinarith)
        rwa [neg_smul, sub_neg_eq_add] at this
    · right; rw [heq, zero_smul, add_zero]; rfl
    · left
      rcases lt_or_eq_of_le hj with hjk | rfl
      · exact hup j hjk s hgt (by nlinarith)
      · apply hSafe_sub
        have := hend s hgt (by nlinarith)
        rw [hmidl]; exact this
  have F2 : ∀ j < k, segment ℝ (B j) (A (j + 1)) ⊆ Safe' := by
    intro j hj
    obtain ⟨e, hw, hi, hp⟩ := hstep j hj
    have hb : B j ∈ paraOpen (a j) u (w j) := by
      rw [hBl, hmidl]; exact mid_add_mem_para hu hN hw hi hp (by norm_num) le_rfl
    have ha : A (j + 1) ∈ paraOpen (a j) u (w j) := by
      rw [hAl, hmidl, e]; exact mid_sub_mem_para hu hN hw hi hp (by norm_num) le_rfl
    exact ((convex_paraOpen _ _ _).segment_subset hb ha).trans (hpara j hj)
  have F3 : segment ℝ Ps (A 0) ⊆ Safe' := by
    intro y hy
    rw [hPs, hAl, sub_eq_add_neg, sub_eq_add_neg, ← neg_smul,
      show -N = (-1 : ℝ) • N by simp] at hy
    obtain ⟨θ, hθ0, hθ1, rfl⟩ := mem_segment_line_plane hy
    apply hSafe_sub
    have := hstart (-((1 - θ) * (-1) + θ * -(1 / 4))) (by nlinarith) (by nlinarith)
    rw [hmidl]; rwa [neg_smul, sub_neg_eq_add] at this
  have F4 : segment ℝ (B k) Pe ⊆ Safe' := by
    intro y hy
    have e : mid k + N = mid k + (1 : ℝ) • N := by rw [one_smul]
    rw [hPe, hBl, e] at hy
    obtain ⟨θ, hθ0, hθ1, rfl⟩ := mem_segment_line_plane hy
    apply hSafe_sub
    have := hend ((1 - θ) * (1 / 4) + θ * 1) (by nlinarith) (by nlinarith)
    rw [hmidl]; exact this
  -- the polygon
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : List Plane, Γ = Ps :: (zig A B 0 (k + 1) ++ Pe :: [Qe, Qs, Ps]) :=
    ⟨_, rfl⟩
  have hPsS : Ps ∈ Safe' := by
    apply hSafe_sub
    have := hstart 1 one_pos le_rfl
    rw [hPs, hmidl]; simpa using this
  have hZchain : ∀ T : Set Plane, Safe' ⊆ T →
      List.IsChain (fun x y => segment ℝ x y ⊆ T) (Pe :: [Qe, Qs, Ps]) := by
    intro T hT
    simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
    refine ⟨?_, ?_, ?_⟩
    · rw [hPe, hmidl]; exact (h1.trans hSafe_sub).trans hT
    · exact (h2.trans hSafe_sub).trans hT
    · rw [hPs, hmidl]; exact (h3.trans hSafe_sub).trans hT
  have hMsub : ∀ j ≤ k, mid j ∈ M := fun j hj => by rw [hM]; exact ⟨j, hj, rfl⟩
  have hall : polyline (Γ.map toC) ⊆ toC '' (Safe' ∪ M) := by
    rw [hΓ]
    refine polyline_map_toC_subset _ _ ?_ (Or.inl hPsS)
    refine chain_cons_zig _ A B Ps Pe [Qe, Qs, Ps] (hZchain _ subset_union_left) (k + 1) 0
      (fun _ => F3.trans subset_union_left) (fun h => by omega)
      (fun j _ hj => (F1 j (by omega)).trans (union_subset_union_right _
        (singleton_subset_iff.2 (hMsub j (by omega)))))
      (fun j _ hj => (F2 j (by omega)).trans subset_union_left)
      (fun _ => by simpa using F4.trans subset_union_left)
  have hexcl : ∀ l ≤ k,
      polyline (((Ps :: zig A B 0 l) ++ [A l]).map toC) ∪
        polyline ((B l :: (zig A B (l + 1) (k - l) ++ Pe :: [Qe, Qs, Ps])).map toC) ⊆
        toC '' (Safe' ∪ (M \ {mid l})) := by
    intro l hl
    have hF1' : ∀ j ≤ k, j ≠ l → segment ℝ (A j) (B j) ⊆ Safe' ∪ (M \ {mid l}) := by
      intro j hj hjl
      refine (F1 j hj).trans (union_subset_union_right _ (singleton_subset_iff.2 ⟨hMsub j hj, ?_⟩))
      intro he; exact hjl (hmid_inj j hj l hl he)
    refine union_subset ?_ ?_
    · refine polyline_map_toC_subset _ _ ?_ (Or.inl hPsS)
      exact chain_cons_zig _ A B Ps (A l) [] (List.isChain_singleton _) l 0
        (fun _ => F3.trans subset_union_left)
        (fun h => by subst h; exact F3.trans subset_union_left)
        (fun j _ hj => hF1' j (by omega) (by omega))
        (fun j _ hj => (F2 j (by omega)).trans subset_union_left)
        (fun h => by
          have := F2 (l - 1) (by omega)
          rw [show l - 1 + 1 = l by omega] at this
          simpa using this.trans subset_union_left)
    · refine polyline_map_toC_subset _ _ ?_ (Or.inl ?_)
      · exact chain_cons_zig _ A B (B l) Pe [Qe, Qs, Ps] (hZchain _ subset_union_left) (k - l) (l + 1)
          (fun h => (F2 l (by omega)).trans subset_union_left)
          (fun h => by
            have : l = k := by omega
            subst this; exact F4.trans subset_union_left)
          (fun j hj hj' => hF1' j (by omega) (by omega))
          (fun j _ hj => (F2 j (by omega)).trans subset_union_left)
          (fun h => by
            rw [show l + 1 + (k - l) - 1 = k by omega]; exact F4.trans subset_union_left)
      · rcases lt_or_eq_of_le hl with hlk | rfl
        · rw [hBl]; exact hup l hlk _ (by norm_num) le_rfl
        · apply hSafe_sub
          have := hend (1 / 4) (by norm_num) (by norm_num)
          rw [hBl, hmidl]; exact this
  have hsplit : ∀ l ≤ k, Γ = (Ps :: zig A B 0 l) ++ A l :: B l ::
      (zig A B (l + 1) (k - l) ++ Pe :: [Qe, Qs, Ps]) := by
    intro l hl
    have := zig_split A B l 0 (k - l)
    rw [show l + (k - l + 1) = k + 1 by omega, zero_add] at this
    rw [hΓ, this]
    simp
  -- winding numbers
  obtain ⟨Γc, hΓc⟩ : ∃ Γc : List ℂ, Γc = Γ.map toC := ⟨_, rfl⟩
  rw [← hΓc] at hall
  have hlast : Γc.getLast (by simp [hΓc, hΓ]) = toC Ps := by
    subst hΓc; simp [hΓ]
  obtain ⟨P0, tl, hP0⟩ : ∃ P0 tl, Γc = P0 :: tl := ⟨toC Ps, _, by rw [hΓc, hΓ, List.map_cons]⟩
  have hP0' : P0 = toC Ps := by
    have := congrArg List.head? hP0
    rw [hΓc, hΓ] at this; simp at this; exact this.symm
  have hclosed : (P0 :: tl).getLast (by simp) = P0 := by
    have h := hlast
    simp only [hP0] at h
    rw [h, hP0']
  obtain ⟨W, hW⟩ : ∃ W : Plane → ℝ, W = fun x => windSum (toC x) (P0 :: tl) := ⟨_, rfl⟩
  have hXΓ : ∀ x ∈ X, toC x ∉ polyline (P0 :: tl) := by
    intro x hx hxp
    rw [← hP0] at hxp
    obtain ⟨y, hy, hyx⟩ := hall hxp
    rw [toC.injective hyx] at hy
    rcases hy with hy | hy
    · exact hSX' x hx hy
    · rw [hM] at hy
      obtain ⟨l, hl, rfl⟩ := hy
      exact hmidX l hl hx
  have hcross : ∀ p ∈ X, ∀ q ∈ X, dist p q = 1 → ∀ y ∈ segment ℝ p q,
      toC y ∈ polyline (P0 :: tl) → ∃ l ≤ k, y = mid l ∧ s(p, q) = s(a l, a l + u) := by
    intro p hp q hq hpq y hy hyp
    rw [← hP0] at hyp
    obtain ⟨y', hy', hyy⟩ := hall hyp
    rw [toC.injective hyy] at hy'
    rcases hy' with hy' | hy'
    · exact absurd hy' (Set.disjoint_left.1 (hSU' p hp q hq hpq) hy)
    · rw [hM] at hy'
      obtain ⟨l, hl, rfl⟩ := hy'
      refine ⟨l, hl, rfl, ?_⟩
      by_contra hne
      have hd : dist (a l) (a l + u) = 1 := by
        rw [dist_eq_norm, show a l - (a l + u) = -u by abel, norm_neg, hu]
      have hm := mid_mem_segment (a l) u
      rw [← hmidl] at hm
      rcases unit_seg_inter hX hp hq (hgate l hl).1 (hgate l hl).2 hpq hd hne hy hm with h | h
      · exact hmidX l hl (h ▸ hp)
      · exact hmidX l hl (h ▸ hq)
  have hconst : ∀ p ∈ X, ∀ q ∈ X, dist p q = 1 → W p ≠ W q →
      ∃ l ≤ k, s(p, q) = s(a l, a l + u) := by
    intro p hp q hq hpq hne
    by_contra hno
    push_neg at hno
    apply hne
    rw [hW]
    refine windSum_eq_of_isPreconnected (convex_segment (toC p) (toC q)).isPreconnected P0 tl
      hclosed ?_ (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
    intro y hy hyp
    rw [← toC_image_segment] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    obtain ⟨l, hl, -, he⟩ := hcross p hp q hq hpq y' hy' hyp
    exact hno l hl he
  -- the jump at each gate
  obtain ⟨ε, hε, hNε⟩ : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ N = ε • rot u := by
    rcases hN with h | h
    · exact ⟨1, Or.inl rfl, by rw [h, one_smul]⟩
    · exact ⟨-1, Or.inr rfl, by rw [h, neg_one_smul]⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = -ε / 2 := ⟨_, rfl⟩
  have hpair : ∀ l, (mid l + σ • u = a l ∧ mid l + (-σ) • u = a l + u) ∨
      (mid l + σ • u = a l + u ∧ mid l + (-σ) • u = a l) := by
    intro l
    rcases hε with rfl | rfl
    · left; rw [hmidl, hσ]; constructor <;> module
    · right; rw [hmidl, hσ]; constructor <;> module
  have hxy : ∀ l ≤ k, mid l + σ • u ∈ X ∧ mid l + (-σ) • u ∈ X ∧
      s(mid l + (-σ) • u, mid l + σ • u) = s(a l, a l + u) ∧
      dist (mid l + (-σ) • u) (mid l + σ • u) = 1 := by
    intro l hl
    have hd : dist (a l) (a l + u) = 1 := by
      rw [dist_eq_norm, show a l - (a l + u) = -u by abel, norm_neg, hu]
    rcases hpair l with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2]
      exact ⟨(hgate l hl).1, (hgate l hl).2, Sym2.eq_swap, by rw [dist_comm]; exact hd⟩
    · rw [e1, e2]; exact ⟨(hgate l hl).2, (hgate l hl).1, rfl, hd⟩
  have hjump : ∀ l ≤ k, W (mid l + σ • u) - W (mid l + (-σ) • u) = 2 * π := by
    intro l hl
    obtain ⟨hxX, hyX, hpq, hd⟩ := hxy l hl
    have hA' : A l = mid l - (1 / 4 : ℝ) • N := hAl l
    have hB' : B l = mid l + (1 / 4 : ℝ) • N := hBl l
    have hsplitc : P0 :: tl = ((Ps :: zig A B 0 l).map toC) ++ toC (A l) :: toC (B l) ::
        ((zig A B (l + 1) (k - l) ++ Pe :: [Qe, Qs, Ps]).map toC) := by
      rw [← hP0, hΓc, hsplit l hl]; simp
    have hAB : toC (A l) ≠ toC (B l) := by
      intro h
      have := toC.injective h
      rw [hA', hB'] at this
      have h4 : (1 / 2 : ℝ) • N = 0 := by
        have := congrArg (fun v => v - (mid l - (1 / 4 : ℝ) • N)) this
        simp only [sub_self] at this
        rw [show mid l + (1 / 4 : ℝ) • N - (mid l - (1 / 4 : ℝ) • N) = (1 / 2 : ℝ) • N by module]
          at this
        exact this.symm
      rw [smul_eq_zero] at h4
      rcases h4 with h4 | h4
      · norm_num at h4
      · rw [h4, norm_zero] at hNn; norm_num at hNn
    have hmC : (toC (A l) + toC (B l)) / 2 = toC (mid l) := by
      rw [hA', hB', map_sub, map_add]; ring
    rw [hW]
    show windSum _ (P0 :: tl) - windSum _ (P0 :: tl) = 2 * π
    refine windSum_jump_exact hAB hsplitc hclosed ?_ ?_ ?_ ?_ ?_
    · rw [hmC]
      intro hm
      have hm' : toC (mid l) ∈ polyline (((Ps :: zig A B 0 l) ++ [A l]).map toC) ∪
          polyline ((B l :: (zig A B (l + 1) (k - l) ++ Pe :: [Qe, Qs, Ps])).map toC) := by
        simpa using hm
      obtain ⟨y, hy, hyy⟩ := hexcl l hl hm'
      rw [toC.injective hyy] at hy
      rcases hy with hy | ⟨-, hy⟩
      · exact hmidS l hl hy
      · exact hy rfl
    · rw [hmC, ← toC_image_segment]
      refine ⟨mid l, ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by module⟩, rfl⟩
    · rw [hmC]
      intro z' hz' hzp
      rw [← toC_image_segment] at hz'
      obtain ⟨y', hy', rfl⟩ := hz'
      obtain ⟨l', hl', rfl, he⟩ := hcross _ hyX _ hxX hd y' hy' hzp
      rw [hpq] at he
      congr 1
      have e1 := congrArg Erdos99.mid he
      rw [mid_mk, mid_mk] at e1
      rw [hmidl, hmidl, ← half_sum_eq, ← half_sum_eq, e1]
    · rw [hA', hB', wc_gate_im hu σ ε hε hNε, hσ]
      rcases hε with rfl | rfl <;> norm_num
    · rw [hA', hB', wc_gate_im hu (-σ) ε hε hNε, hσ]
      rcases hε with rfl | rfl <;> norm_num
  -- location of points with nonzero winding number
  have hloc : ∀ p : Plane, W p ≠ 0 → ∀ (ω : Plane) (c : ℝ),
      c ≤ inner ℝ (a 0 + (1 / 2 : ℝ) • u - N) ω → c ≤ inner ℝ (a k + (1 / 2 : ℝ) • u + N) ω →
      c ≤ inner ℝ Qe ω → c ≤ inner ℝ Qs ω →
      (∀ l ≤ k, c ≤ inner ℝ (a l + (1 / 2 : ℝ) • u - (1 / 4 : ℝ) • N) ω ∧
        c ≤ inner ℝ (a l + (1 / 2 : ℝ) • u + (1 / 4 : ℝ) • N) ω) →
      c ≤ inner ℝ p ω := by
    intro p hWp ω c b1 b2 b3 b4 b5
    by_contra hlt
    push_neg at hlt
    apply hWp
    rw [hW]
    refine windSum_eq_zero_of_half (ω := toC ω) P0 tl hclosed ?_
    intro v hv
    rw [← hP0, hΓc] at hv
    obtain ⟨V, hV, rfl⟩ := List.mem_map.1 hv
    rw [← map_sub toC V p, inner_toC_re (V - p) ω, inner_sub_right, real_inner_comm V ω,
      real_inner_comm p ω]
    have hb5 : ∀ j < k + 1, c ≤ inner ℝ (A j) ω ∧ c ≤ inner ℝ (B j) ω := by
      intro j hj
      rw [hAl, hBl, hmidl]; exact b5 j (by omega)
    have hb1 : c ≤ inner ℝ Ps ω := by rw [hPs, hmidl]; exact b1
    have hb2 : c ≤ inner ℝ Pe ω := by rw [hPe, hmidl]; exact b2
    rw [hΓ] at hV
    have hVc := vertex_lower hb1 hb2 b3 b4 hb5 V hV
    linarith only [hVc, hlt]
  -- edges where the winding number increases are gates crossed in the direction `-ε u`
  have hinc : ∀ p ∈ X, ∀ q ∈ X, dist p q = 1 → W p < W q → p - q = ε • u := by
    intro p hp q hq hpq hWpq
    obtain ⟨l, hl, he⟩ := hconst p hp q hq hpq hWpq.ne
    obtain ⟨-, -, he', -⟩ := hxy l hl
    have hj := hjump l hl
    rw [← he'] at he
    rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hσ]; module
    · exfalso; linarith [Real.pi_pos]
  obtain ⟨hxpX, hxmX, -, -⟩ := hxy 0 (Nat.zero_le k)
  have hj0 := hjump 0 (Nat.zero_le k)
  have hεu : ε • u = u ∨ ε • u = -u := by
    rcases hε with rfl | rfl
    · left; simp
    · right; simp
  rcases le_or_gt (W (mid 0 + σ • u)) 0 with hneg | hpos
  · refine ⟨X.filter (fun x => W x ≤ W (mid 0 + (-σ) • u)), Finset.filter_subset _ _,
      ⟨_, Finset.mem_filter.2 ⟨hxmX, le_rfl⟩⟩,
      ⟨_, hxpX, fun h => by
        have := (Finset.mem_filter.1 h).2
        linarith [Real.pi_pos]⟩, ε • u, hεu, ?_, ?_⟩
    · intro p hp q hq hqS hpq
      have h1 := (Finset.mem_filter.1 hp).2
      have h2 : ¬ W q ≤ W (mid 0 + (-σ) • u) := fun h => hqS (Finset.mem_filter.2 ⟨hq, h⟩)
      exact hinc p (Finset.mem_filter.1 hp).1 q hq hpq (by linarith)
    · intro p hp
      have h1 := (Finset.mem_filter.1 hp).2
      exact hloc p (by linarith [Real.pi_pos])
  · refine ⟨X.filter (fun x => W (mid 0 + σ • u) ≤ W x), Finset.filter_subset _ _,
      ⟨_, Finset.mem_filter.2 ⟨hxpX, le_rfl⟩⟩,
      ⟨_, hxmX, fun h => by
        have := (Finset.mem_filter.1 h).2
        linarith [Real.pi_pos]⟩, -(ε • u), ?_, ?_, ?_⟩
    · rcases hεu with h | h <;> rw [h] <;> simp
    · intro p hp q hq hqS hpq
      have h1 := (Finset.mem_filter.1 hp).2
      have h2 : ¬ W (mid 0 + σ • u) ≤ W q := fun h => hqS (Finset.mem_filter.2 ⟨hq, h⟩)
      have := hinc q hq p (Finset.mem_filter.1 hp).1 (by rw [dist_comm]; exact hpq)
        (by linarith)
      rw [← this]; abel
    · intro p hp
      have h1 := (Finset.mem_filter.1 hp).2
      exact hloc p (by linarith)

end Erdos99
end

end CrosscutShore

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `PortCap`
-/

section PortCap

/-!
# The cap of a two-edge hull return

Let `(b, x, c)` be a two-edge hull return of a separated set `X`: `|b x| = |x c| = 1 < |b c|`, and
`X` lies in a closed half-plane bounded by the line `b c`.  The open triangle `b x c` together
with the open segment `b c` (the *cap*) contains no point of `X` and meets no unit segment of `X`.
-/

open scoped BigOperators Real
open Set

@[expose] public noncomputable section

open Classical

namespace Erdos99

/-- The open triangle with vertices `b, x, c`. -/
def openTri (b x c : Plane) : Set Plane :=
  {z | ∃ α β γ : ℝ, 0 < α ∧ 0 < β ∧ 0 < γ ∧ α + β + γ = 1 ∧ z = α • b + β • x + γ • c}

lemma openTri_comm (b x c : Plane) : openTri b x c = openTri c x b := by
  ext z
  constructor
  · rintro ⟨α, β, γ, h1, h2, h3, h4, rfl⟩
    exact ⟨γ, β, α, h3, h2, h1, by linarith, by abel⟩
  · rintro ⟨α, β, γ, h1, h2, h3, h4, rfl⟩
    exact ⟨γ, β, α, h3, h2, h1, by linarith, by abel⟩

lemma det2_add_right (d a b : Plane) : det2 d (a + b) = det2 d a + det2 d b := by
  simp [det2]; ring

/-- A combination `α b + β x + γ c` with `α, γ > 0` is within distance `< 1` of `x`. -/
lemma dist_comb_lt {b x c : Plane} (hbx : dist b x = 1) (hxc : dist x c = 1)
    (hbc : 1 < dist b c) {α β γ : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) (hγ : 0 < γ)
    (hs : α + β + γ = 1) : dist (α • b + β • x + γ • c) x < α + γ := by
  have e1 := dist_sq_coord b x
  have e2 := dist_sq_coord x c
  have e3 := dist_sq_coord b c
  rw [hbx] at e1; rw [hxc] at e2
  have e3' : 1 < dist b c ^ 2 := by nlinarith
  rw [e3] at e3'
  obtain rfl : β = 1 - α - γ := by linarith
  have hz := dist_sq_coord (α • b + (1 - α - γ) • x + γ • c) x
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hz
  have key : dist (α • b + (1 - α - γ) • x + γ • c) x ^ 2 < (α + γ) ^ 2 := by
    rw [hz]
    set P := (b 0 - x 0) * (c 0 - x 0) + (b 1 - x 1) * (c 1 - x 1)
    have hP : P < 1 / 2 := by simp only [P]; nlinarith
    have hid : (α * b 0 + (1 - α - γ) * x 0 + γ * c 0 - x 0) ^ 2 +
        (α * b 1 + (1 - α - γ) * x 1 + γ * c 1 - x 1) ^ 2 =
        α ^ 2 * ((b 0 - x 0) ^ 2 + (b 1 - x 1) ^ 2) +
          γ ^ 2 * ((x 0 - c 0) ^ 2 + (x 1 - c 1) ^ 2) + 2 * α * γ * P := by
      simp only [P]; ring
    rw [hid, ← e1, ← e2]
    nlinarith [mul_pos hα hγ]
  exact lt_of_pow_lt_pow_left₀ 2 (by linarith) key

section Cap

variable {X : Finset Plane} (hX : IsSeparated X) {b x c : Plane} (hb : b ∈ X) (hx : x ∈ X)
  (hc : c ∈ X) (hbx : dist b x = 1) (hxc : dist x c = 1) (hbc : 1 < dist b c) {ε : ℝ}
  (hε : ε = 1 ∨ ε = -1) (hhalf : ∀ z ∈ X, 0 ≤ ε * det2 (c - b) (z - b))
  (hdeg : det2 (c - b) (x - b) ≠ 0)

include hX hx hbx hxc hbc hdeg in
/-- No point of `X` lies in the cap. -/
lemma not_mem_cap_of_mem {z : Plane} (hz : z ∈ X) {α β γ : ℝ} (hα : 0 < α) (hβ : 0 ≤ β)
    (hγ : 0 < γ) (hs : α + β + γ = 1) (hze : z = α • b + β • x + γ • c) : False := by
  have hd := dist_comb_lt hbx hxc hbc hα hβ hγ hs
  rw [← hze] at hd
  replace hd : dist z x < 1 := by linarith
  have hzx : z = x := by
    by_contra hne
    exact absurd (hX z hz x hx hne) (not_le.2 hd)
  have hdet : det2 (c - b) (z - b) = β * det2 (c - b) (x - b) := by
    rw [hze]
    simp only [det2, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    rw [show α = 1 - β - γ by linarith]; ring
  rw [hzx] at hdet
  have : β = 1 := by
    have := mul_right_cancel₀ hdeg (show 1 * det2 (c - b) (x - b) = β * det2 (c - b) (x - b) by
      rw [one_mul]; exact hdet)
    linarith
  linarith


/-- A point of `X` on a unit segment of `X` is one of its endpoints. -/
lemma eq_endpoint_of_mem_segment {X : Finset Plane} (hX : IsSeparated X) {p q y : Plane}
    (hp : p ∈ X) (hq : q ∈ X) (hy : y ∈ X) (hpq : dist p q = 1) (hys : y ∈ segment ℝ p q) :
    y = p ∨ y = q := by
  by_contra h
  push_neg at h
  have e := dist_add_dist_of_mem_segment hys
  have h1 := hX y hy p hp h.1
  have h2 := hX y hy q hq h.2
  rw [dist_comm p y] at e
  linarith

/-- The affine functional `g` of the half-plane is affine along segments. -/
lemma det2_segment {d b p q y : Plane} (hy : y ∈ segment ℝ p q) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ y = p + t • (q - p) ∧
      det2 d (y - b) = (1 - t) * det2 d (p - b) + t * det2 d (q - b) := by
  obtain ⟨a, t, ha, ht, hat, rfl⟩ := hy
  refine ⟨t, ht, by linarith, ?_, ?_⟩
  · rw [show a = 1 - t by linarith]; module
  · rw [show a = 1 - t by linarith]
    simp only [det2, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring

include hX hx hbx hxc hbc hε hhalf hdeg in
/-- No unit segment of `X` meets the open segment `b c`. -/
lemma unit_seg_not_meet_base {p q : Plane} (hp : p ∈ X) (hq : q ∈ X) (hpq : dist p q = 1)
    {y : Plane} (hys : y ∈ segment ℝ p q) (hyb : y ∈ openSegment ℝ b c) : False := by
  obtain ⟨α, γ, hα, hγ, hαγ, rfl⟩ := hyb
  have hcb : c - b ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; subst h; rw [dist_self] at hbc; linarith
  obtain ⟨t, ht0, ht1, hyt, hdet⟩ := det2_segment (d := c - b) (b := b) hys
  have hy0 : det2 (c - b) (α • b + γ • c - b) = 0 := by
    simp only [det2, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    rw [show α = 1 - γ by linarith]; ring
  have gp := hhalf p hp
  have gq := hhalf q hq
  have hcap : ∀ z ∈ X, ∀ l : ℝ, 0 < l → l < 1 → z = (1 - l) • b + l • c → False := by
    intro z hz l hl0 hl1 hze
    exact not_mem_cap_of_mem hX hx hbx hxc hbc hdeg hz (α := 1 - l) (β := 0) (γ := l)
      (by linarith) le_rfl hl0 (by ring) (by rw [hze]; simp)
  -- endpoints
  rcases eq_or_lt_of_le ht0 with rfl | ht0'
  · simp only [zero_smul, add_zero] at hyt
    exact hcap p hp γ hγ (by linarith) (by rw [← hyt, show α = 1 - γ by linarith])
  rcases eq_or_lt_of_le ht1 with rfl | ht1'
  · rw [one_smul, add_sub_cancel] at hyt
    exact hcap q hq γ hγ (by linarith) (by rw [← hyt, show α = 1 - γ by linarith])
  -- interior: both endpoints on the line `b c`
  rw [hy0] at hdet
  have hp0 : det2 (c - b) (p - b) = 0 := by
    rcases hε with rfl | rfl <;> nlinarith
  have hq0 : det2 (c - b) (q - b) = 0 := by
    rcases hε with rfl | rfl <;> nlinarith
  obtain ⟨l, hl⟩ := eq_smul_of_det2_eq_zero hcb hp0
  obtain ⟨m, hm⟩ := eq_smul_of_det2_eq_zero hcb hq0
  have hl' : l ≤ 0 ∨ 1 ≤ l := by
    by_contra h; push_neg at h
    exact hcap p hp l h.1 h.2 (by rw [show p = b + (p - b) by abel, hl]; module)
  have hm' : m ≤ 0 ∨ 1 ≤ m := by
    by_contra h; push_neg at h
    exact hcap q hq m h.1 h.2 (by rw [show q = b + (q - b) by abel, hm]; module)
  have hyl : α • b + γ • c - b = ((1 - t) * l + t * m) • (c - b) := by
    rw [hyt, show p + t • (q - p) - b = (1 - t) • (p - b) + t • (q - b) by module, hl, hm]
    module
  have hγeq : γ = (1 - t) * l + t * m := by
    have e2 : α • b + γ • c - b = γ • (c - b) := by
      rw [show α = 1 - γ by linarith]; module
    rw [e2] at hyl
    exact smul_left_injective ℝ hcb hyl
  have hpqn : dist p q = |l - m| * dist b c := by
    rw [dist_eq_norm, show p - q = (p - b) - (q - b) by abel, hl, hm, ← sub_smul, norm_smul,
      Real.norm_eq_abs, dist_comm, dist_eq_norm]
  rw [hpq] at hpqn
  have hlm : |l - m| < 1 := by
    by_contra h; push_neg at h
    nlinarith [dist_nonneg (x := b) (y := c)]
  rw [abs_lt] at hlm
  rcases hl' with hl' | hl' <;> rcases hm' with hm' | hm'
  · nlinarith
  · linarith
  · linarith
  · nlinarith

lemma det2_comb_sub {b x c : Plane} {α β γ : ℝ} (hs : α + β + γ = 1) :
    det2 (c - b) (α • b + β • x + γ • c - b) = β * det2 (c - b) (x - b) := by
  simp only [det2, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  rw [show α = 1 - β - γ by linarith]; ring

include hx hbx hxc hbc hε hhalf hdeg in
/-- A unit segment of `X` starting at the apex `x` does not meet the open triangle. -/
lemma unit_seg_from_apex {q : Plane} (hq : q ∈ X) (hxq : dist x q = 1) {z : Plane}
    (hzs : z ∈ segment ℝ x q) (hzT : z ∈ openTri b x c) : False := by
  obtain ⟨α, β, γ, hα, hβ, hγ, hs, rfl⟩ := hzT
  obtain ⟨t, ht0, ht1, hzt, hdet⟩ := det2_segment (d := c - b) (b := b) hzs
  rw [det2_comb_sub hs] at hdet
  have hd := dist_comb_lt hbx hxc hbc hα hβ.le hγ hs
  have hdt : dist (α • b + β • x + γ • c) x = t := by
    rw [hzt, dist_eq_norm, add_sub_cancel_left, norm_smul, ← dist_eq_norm, dist_comm, hxq,
      Real.norm_eq_abs, abs_of_nonneg ht0, mul_one]
  rw [hdt] at hd
  have hH : 0 < ε * det2 (c - b) (x - b) := by
    have := hhalf x hx
    rcases lt_or_eq_of_le this with h | h
    · exact h
    · exfalso; rcases hε with rfl | rfl <;> simp at h <;> exact hdeg (by linarith)
  have hG := hhalf q hq
  have key : t * (ε * det2 (c - b) (q - b)) = (β - 1 + t) * (ε * det2 (c - b) (x - b)) := by
    linear_combination -ε * hdet
  have : (β - 1 + t) * (ε * det2 (c - b) (x - b)) < 0 :=
    mul_neg_of_neg_of_pos (by linarith) hH
  nlinarith

omit hX in
lemma det2_comb_sub' {b x c : Plane} {α β γ : ℝ} (hs : α + β + γ = 1) :
    det2 (x - b) (α • b + β • x + γ • c - b) = γ * det2 (x - b) (c - b) := by
  simp only [det2, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  rw [show α = 1 - β - γ by linarith]; ring

/-- Cramer's rule in barycentric form. -/
lemma cramer_bary {b x c : Plane} (hD : det2 (x - b) (c - b) ≠ 0) (y : Plane) :
    y = (1 - det2 (c - b) (y - b) / det2 (c - b) (x - b) -
        det2 (x - b) (y - b) / det2 (x - b) (c - b)) • b +
      (det2 (c - b) (y - b) / det2 (c - b) (x - b)) • x +
      (det2 (x - b) (y - b) / det2 (x - b) (c - b)) • c := by
  have e1 : det2 (c - b) (y - b) / det2 (c - b) (x - b) =
      det2 (y - b) (c - b) / det2 (x - b) (c - b) := by
    rw [show det2 (c - b) (y - b) = -det2 (y - b) (c - b) by unfold det2; ring,
      show det2 (c - b) (x - b) = -det2 (x - b) (c - b) by unfold det2; ring, neg_div_neg_eq]
  rw [e1]
  generalize hDd : det2 (x - b) (c - b) = Dd at hD
  have key : Dd • (y - b) = det2 (y - b) (c - b) • (x - b) + det2 (x - b) (y - b) • (c - b) := by
    rw [← hDd, plane_ext_iff]
    simp only [det2, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    constructor <;> ring
  generalize hB : det2 (y - b) (c - b) = B at key
  generalize hG : det2 (x - b) (y - b) = G at key
  have : y - b = (B / Dd) • (x - b) + (G / Dd) • (c - b) := by
    apply smul_right_injective Plane hD
    simp only [smul_add, smul_smul]
    rw [key, mul_div_cancel₀ _ hD, mul_div_cancel₀ _ hD]
  calc y = b + (y - b) := by abel
    _ = _ := by rw [this]; module

lemma det2_line (d p q b : Plane) (t : ℝ) :
    det2 d (p + t • (q - p) - b) = det2 d (p - b) + t * (det2 d (q - b) - det2 d (p - b)) := by
  simp only [det2, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring

/-- Two unit segments from `b` sharing a point other than `b` coincide. -/
lemma eq_of_segments_from {b x q y : Plane} (hbx : dist b x = 1) (hbq : dist b q = 1)
    (hyx : y ∈ segment ℝ b x) (hyq : y ∈ segment ℝ b q) (hyb : y ≠ b) : q = x := by
  obtain ⟨s, hs0, hs1, hys, -⟩ := det2_segment (d := 0) (b := 0) hyx
  obtain ⟨t, ht0, ht1, hyt, -⟩ := det2_segment (d := 0) (b := 0) hyq
  have n1 : dist y b = s := by
    rw [hys, dist_eq_norm, add_sub_cancel_left, norm_smul, ← dist_eq_norm, dist_comm, hbx,
      Real.norm_eq_abs, abs_of_nonneg hs0, mul_one]
  have n2 : dist y b = t := by
    rw [hyt, dist_eq_norm, add_sub_cancel_left, norm_smul, ← dist_eq_norm, dist_comm, hbq,
      Real.norm_eq_abs, abs_of_nonneg ht0, mul_one]
  have hst : s = t := n1.symm.trans n2
  have hs : 0 < s := by
    rw [← n1]; exact dist_pos.2 hyb
  have : s • (x - b) = s • (q - b) := by
    have := hys.symm.trans hyt
    rw [← hst] at this
    exact add_left_cancel this
  have := smul_right_injective Plane hs.ne' this
  rw [sub_left_inj] at this
  exact this.symm

include hX hb hx hc hbx hxc hbc hε hhalf hdeg in
/-- A unit segment of `X` whose far endpoint is not a vertex of the triangle, and whose near
endpoint is not the apex, does not meet the open triangle: following it towards the far endpoint
it must leave the triangle through a side, which is impossible. -/
lemma unit_seg_exit {p q : Plane} (hp : p ∈ X) (hq : q ∈ X) (hpq : dist p q = 1) {z : Plane}
    (hzs : z ∈ segment ℝ p q) (hzT : z ∈ openTri b x c) (hqb : q ≠ b) (hqx : q ≠ x)
    (hqc : q ≠ c) (hpx : p ≠ x) : False := by
  have hD : det2 (x - b) (c - b) ≠ 0 := by
    intro h; apply hdeg; unfold det2 at h ⊢; linarith
  have hpq' : p ≠ q := by
    intro h; rw [h, dist_self] at hpq; norm_num at hpq
  set Bf : Plane → ℝ := fun y => det2 (c - b) (y - b) / det2 (c - b) (x - b) with hBf
  set Gf : Plane → ℝ := fun y => det2 (x - b) (y - b) / det2 (x - b) (c - b) with hGf
  have hcr : ∀ y, y = (1 - Bf y - Gf y) • b + Bf y • x + Gf y • c := fun y => cramer_bary hD y
  obtain ⟨t0, ht00, ht01, hzt, -⟩ := det2_segment (d := 0) (b := 0) hzs
  set F : ℝ → ℝ := fun t => min (1 - Bf (p + t • (q - p)) - Gf (p + t • (q - p)))
    (min (Bf (p + t • (q - p))) (Gf (p + t • (q - p)))) with hF
  have hBl : ∀ t : ℝ, Bf (p + t • (q - p)) = Bf p + t * (Bf q - Bf p) := by
    intro t; simp only [hBf]; rw [det2_line]; field_simp
  have hGl : ∀ t : ℝ, Gf (p + t • (q - p)) = Gf p + t * (Gf q - Gf p) := by
    intro t; simp only [hGf]; rw [det2_line]; field_simp
  have hFc : Continuous F := by
    have e : F = fun t => min (1 - (Bf p + t * (Bf q - Bf p)) - (Gf p + t * (Gf q - Gf p)))
        (min (Bf p + t * (Bf q - Bf p)) (Gf p + t * (Gf q - Gf p))) := by
      funext t; simp only [hF, hBl, hGl]
    rw [e]; fun_prop
  -- positivity at `t0`
  obtain ⟨α, β, γ, hα, hβ, hγ, hs, hze⟩ := hzT
  have hFt0 : 0 < F t0 := by
    have hb' : Bf z = β := by
      simp only [hBf]; rw [hze, det2_comb_sub hs]; field_simp
    have hg' : Gf z = γ := by
      simp only [hGf]; rw [hze, det2_comb_sub' hs]; field_simp
    simp only [hF]; rw [← hzt, hb', hg']
    refine lt_min (by linarith) (lt_min hβ hγ)
  -- nonpositivity at `1`
  have hF1 : F 1 ≤ 0 := by
    by_contra hpos
    push_neg at hpos
    simp only [hF, one_smul, add_sub_cancel] at hpos
    obtain ⟨h1, h2⟩ := lt_min_iff.1 hpos
    obtain ⟨h2, h3⟩ := lt_min_iff.1 h2
    exact not_mem_cap_of_mem hX hx hbx hxc hbc hdeg hq h1 h2.le h3 (by ring) (hcr q)
  obtain ⟨t1, ⟨ht1a, ht1b⟩, hFt1⟩ := intermediate_value_Icc' ht01 hFc.continuousOn ⟨hF1, hFt0.le⟩
  have ht1pos : 0 < t1 := by
    rcases eq_or_lt_of_le ht1a with h | h
    · rw [← h] at hFt1; linarith
    · linarith
  set y := p + t1 • (q - p) with hy
  have hys : y ∈ segment ℝ p q :=
    ⟨1 - t1, t1, by linarith, ht1pos.le, by ring, by rw [hy]; module⟩
  have hyp : y ≠ p := by
    intro h
    have : t1 • (q - p) = 0 := by rw [hy] at h; simpa using h
    rcases smul_eq_zero.1 this with h' | h'
    · linarith
    · exact hpq' (sub_eq_zero.1 h').symm
  have hmin : 0 ≤ 1 - Bf y - Gf y ∧ 0 ≤ Bf y ∧ 0 ≤ Gf y := by
    have := hFt1.symm.le
    simp only [hF] at this
    exact ⟨(le_min_iff.1 this).1, (le_min_iff.1 (le_min_iff.1 this).2).1,
      (le_min_iff.1 (le_min_iff.1 this).2).2⟩
  have hzero : 1 - Bf y - Gf y = 0 ∨ Bf y = 0 ∨ Gf y = 0 := by
    have h := hFt1
    simp only [hF] at h
    rcases min_choice (1 - Bf y - Gf y) (min (Bf y) (Gf y)) with h' | h'
    · left; rw [h'] at h; exact h
    · right
      rw [h'] at h
      rcases min_choice (Bf y) (Gf y) with h'' | h''
      · left; rw [h''] at h; exact h
      · right; rw [h''] at h; exact h
  obtain ⟨hA0, hB0, hG0⟩ := hmin
  have hyc := hcr y
  rcases hzero with h0 | h0 | h0
  · -- on the side `x c`
    have hseg : y ∈ segment ℝ x c := ⟨Bf y, Gf y, hB0, hG0, by linarith, by
      rw [h0, zero_smul, zero_add] at hyc; exact hyc.symm⟩
    by_cases hpc : p = c
    · subst hpc
      exact hqx (eq_of_segments_from (by rw [dist_comm]; exact hxc) hpq
        (segment_symm ℝ x p ▸ hseg) hys hyp)
    · exact Set.disjoint_left.1 (unit_segments_disjoint hX hp hq hx hc hpq hxc hpx hpc hqx hqc)
        hys hseg
  · -- on the base `b c`
    have hyc' : y = (1 - Gf y) • b + Gf y • c := by
      rw [h0, zero_smul, add_zero, sub_zero] at hyc; exact hyc
    rcases eq_or_lt_of_le hG0 with hG | hG
    · rw [← hG, zero_smul, add_zero, sub_zero, one_smul] at hyc'
      rcases eq_endpoint_of_mem_segment hX hp hq (hyc' ▸ hb) hpq (hyc' ▸ hys) with h | h
      · exact hyp h
      · exact hqb (h.symm.trans hyc')
    rcases eq_or_lt_of_le (show 0 ≤ 1 - Gf y by linarith) with hA | hA
    · have hy1 : y = c := by rw [hyc', ← hA, zero_smul, zero_add, show Gf y = 1 by linarith,
        one_smul]
      rcases eq_endpoint_of_mem_segment hX hp hq (hy1 ▸ hc) hpq (hy1 ▸ hys) with h | h
      · exact hyp h
      · exact hqc (h.symm.trans hy1)
    exact unit_seg_not_meet_base hX hx hbx hxc hbc hε hhalf hdeg hp hq hpq hys
      ⟨1 - Gf y, Gf y, hA, hG, by ring, hyc'.symm⟩
  · -- on the side `b x`
    have hseg : y ∈ segment ℝ b x := ⟨1 - Bf y - Gf y, Bf y, hA0, hB0, by linarith, by
      rw [h0, zero_smul, add_zero] at hyc; rw [h0]; exact hyc.symm⟩
    by_cases hpb : p = b
    · subst hpb
      exact hqx (eq_of_segments_from hbx hpq hseg hys hyp)
    · exact Set.disjoint_left.1 (unit_segments_disjoint hX hp hq hb hx hpq hbx hpb hpx hqb hqx)
        hys hseg

omit hX in
/-- A point of the open triangle is not on the side `b x`. -/
lemma openTri_not_mem_side {z : Plane} (hD : det2 (x - b) (c - b) ≠ 0) (hz : z ∈ openTri b x c)
    (hzs : z ∈ segment ℝ b x) : False := by
  obtain ⟨α, β, γ, hα, hβ, hγ, hs, rfl⟩ := hz
  obtain ⟨t, -, -, -, hdet⟩ := det2_segment (d := x - b) (b := b) hzs
  rw [det2_comb_sub' hs, sub_self] at hdet
  have h0 : det2 (x - b) (x - b) = 0 := by unfold det2; ring
  have h1 : det2 (x - b) 0 = 0 := by unfold det2; simp
  rw [h0, h1] at hdet
  simp at hdet
  rcases hdet with h | h
  · linarith
  · exact hD h

include hX hb hx hc hbx hxc hbc hε hhalf hdeg in
/-- **No unit segment meets the cap.** -/
lemma unit_seg_disjoint_cap {p q : Plane} (hp : p ∈ X) (hq : q ∈ X) (hpq : dist p q = 1) :
    Disjoint (segment ℝ p q) (openTri b x c ∪ openSegment ℝ b c) := by
  have hD : det2 (x - b) (c - b) ≠ 0 := by
    intro h; apply hdeg; unfold det2 at h ⊢; linarith
  have hD' : det2 (x - c) (b - c) ≠ 0 := by
    intro h; apply hD; unfold det2 at h ⊢; simp only [PiLp.sub_apply] at h ⊢; linarith
  have hpq' : p ≠ q := by
    intro h; rw [h, dist_self] at hpq; norm_num at hpq
  rw [Set.disjoint_union_right]
  refine ⟨Set.disjoint_left.2 fun z hzs hzT => ?_, Set.disjoint_left.2 fun z hzs hzB =>
    unit_seg_not_meet_base hX hx hbx hxc hbc hε hhalf hdeg hp hq hpq hzs hzB⟩
  have hside1 : z ∉ segment ℝ b x := fun h => openTri_not_mem_side hD hzT h
  have hside2 : z ∉ segment ℝ x c := fun h => by
    rw [openTri_comm] at hzT
    exact openTri_not_mem_side hD' hzT (segment_symm ℝ x c ▸ h)
  have hbc' : dist b c ≠ 1 := by linarith
  -- the main case analysis
  have main : ∀ p q : Plane, p ∈ X → q ∈ X → dist p q = 1 → z ∈ segment ℝ p q →
      q ≠ b → q ≠ x → q ≠ c → False := by
    intro p q hp hq hpq hzs hqb hqx hqc
    by_cases hpx : p = x
    · subst hpx
      exact unit_seg_from_apex hp hbx hxc hbc hε hhalf hdeg hq hpq hzs hzT
    · exact unit_seg_exit hX hb hx hc hbx hxc hbc hε hhalf hdeg hp hq hpq hzs hzT hqb hqx hqc hpx
  by_cases hq' : q = b ∨ q = x ∨ q = c
  · by_cases hp' : p = b ∨ p = x ∨ p = c
    · rcases hp' with rfl | rfl | rfl <;> rcases hq' with rfl | rfl | rfl
      · exact hpq' rfl
      · exact hside1 hzs
      · exact hbc' hpq
      · exact hside1 (segment_symm ℝ p q ▸ hzs)
      · exact hpq' rfl
      · exact hside2 hzs
      · exact hbc' (by rw [dist_comm]; exact hpq)
      · exact hside2 (segment_symm ℝ p q ▸ hzs)
      · exact hpq' rfl
    · push_neg at hp'
      exact main q p hq hp (by rw [dist_comm]; exact hpq) (segment_symm ℝ p q ▸ hzs) hp'.1
        hp'.2.1 hp'.2.2
  · push_neg at hq'
    exact main p q hp hq hpq hzs hq'.1 hq'.2.1 hq'.2.2

end Cap

end Erdos99
end

end PortCap

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `PortRay`
-/

section PortRay

/-!
# The normal ray through the cap of a two-edge return

If a unit rhombus of `X` sits on a port `b x` of a two-edge hull return `(b, x, c)`, it lies on the
side of the port away from the cap, and the normal ray from the midpoint of the port into the cap
leaves the half-plane of `X` before length one.
-/

open scoped BigOperators Real
open Set

@[expose] public noncomputable section

open Classical

namespace Erdos99

lemma det2_frame (d w e : Plane) (he : ‖e‖ = 1) :
    det2 d w = inner ℝ w e * det2 d e + inner ℝ w (rot e) * inner ℝ d e := by
  have h := norm_sq_coord e
  rw [he] at h
  rw [inner_rot_coord, inner_coord, inner_coord]
  unfold det2
  linear_combination (d 0 * w 1 - d 1 * w 0) * h

/-- The sign computation behind `port_ray`: the rhombus on a port lies away from the cap. -/
lemma port_sign_alg {ε σ A B H0 κ : ℝ} (hε : ε = 1 ∨ ε = -1) (hσ : σ = 1 ∨ σ = -1)
    (hAB : A ^ 2 + B ^ 2 = 1) (hA : A ^ 2 < 1 / 4) (hσB : 0 < σ * B) (hh : 0 < ε * H0)
    (hL : H0 ^ 2 + κ ^ 2 = 2 * κ) (hκ : 1 / 2 < κ) (hw : 0 ≤ ε * (A * H0 + B * κ)) : σ = ε := by
  have key : ∀ B' H' : ℝ, 0 < B' → 0 < H' → H' ^ 2 = H0 ^ 2 → B' ^ 2 = B ^ 2 →
      B' * κ ≤ |A| * H' → False := by
    intro B' H' hB' hH' hH2 hB2 hle
    have h1 : (B' * κ) ^ 2 ≤ (|A| * H') ^ 2 := pow_le_pow_left₀ (by positivity) hle 2
    rw [mul_pow, mul_pow, sq_abs, hH2, hB2] at h1
    nlinarith
  rcases hε with rfl | rfl <;> rcases hσ with rfl | rfl
  · rfl
  · exfalso
    refine key (-B) H0 (by linarith) (by linarith) rfl (by ring) ?_
    nlinarith [le_abs_self A, neg_abs_le A]
  · exfalso
    refine key B (-H0) (by linarith) (by linarith) (by ring) rfl ?_
    nlinarith [le_abs_self A, neg_abs_le A]
  · rfl

/-- Normal form of a gate on the port `b x`. -/
lemma port_normalize {X : Finset Plane} {b x a u w0 N : Plane} (hN : N = rot u ∨ N = -rot u)
    (hea : s(b, x) = s(a, a + u)) (ha1 : a + w0 ∈ X) (ha2 : a + u + w0 ∈ X)
    (hw0u : |inner ℝ w0 u| < 1 / 2) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ N = σ • rot (x - b) ∧
      a + (1 / 2 : ℝ) • u = b + (1 / 2 : ℝ) • (x - b) ∧ b + w0 ∈ X ∧
      |inner ℝ w0 (x - b)| < 1 / 2 := by
  have hNs : ∃ τ : ℝ, (τ = 1 ∨ τ = -1) ∧ N = τ • rot u := by
    rcases hN with h | h
    · exact ⟨1, Or.inl rfl, by rw [h, one_smul]⟩
    · exact ⟨-1, Or.inr rfl, by rw [h, neg_one_smul]⟩
  obtain ⟨τ, hτ, hNτ⟩ := hNs
  rcases Sym2.eq_iff.1 hea with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hxb : x - b = u := by rw [h1, h2]; abel
    refine ⟨τ, hτ, by rw [hxb]; exact hNτ, by rw [hxb, h1], by rw [h1]; exact ha1,
      by rw [hxb]; exact hw0u⟩
  · have hxb : x - b = -u := by rw [h1, h2]; abel
    refine ⟨-τ, by rcases hτ with rfl | rfl <;> norm_num, ?_, ?_, ?_, ?_⟩
    · rw [hxb, rot_neg, hNτ]; module
    · rw [hxb, h1]; module
    · rw [h1]; exact ha2
    · rw [hxb, inner_neg_right, abs_neg]; exact hw0u

/-- The barycentric bookkeeping behind `port_ray`. -/
lemma ray_bary_alg {h κ s Bc Gc : ℝ} (hh : 0 < h) (hκ : 1 / 2 < κ) (hs : 0 < s)
    (hB : Bc * h = h / 2 - s * κ) (hG : Gc * h = s) :
    (h / 2 - s * κ < 0) ∨ (Bc = 0 ∧ 0 < Gc ∧ 0 < 1 - Bc - Gc) ∨
      (0 < Bc ∧ 0 < Gc ∧ 0 < 1 - Bc - Gc) := by
  have hGpos : 0 < Gc := by
    by_contra hc; push_neg at hc; nlinarith
  have hA : (1 - Bc - Gc) * h = h / 2 + s * (κ - 1) := by linear_combination -hB - hG
  rcases lt_trichotomy (h / 2 - s * κ) 0 with hneg | hzero | hpos
  · exact Or.inl hneg
  · right; left
    have hB0 : Bc = 0 := by
      have : Bc * h = 0 := by rw [hB, hzero]
      rcases mul_eq_zero.1 this with h' | h'
      · exact h'
      · linarith
    refine ⟨hB0, hGpos, ?_⟩
    have : 0 < h / 2 + s * (κ - 1) := by nlinarith
    by_contra hc; push_neg at hc; nlinarith
  · right; right
    have hBpos : 0 < Bc := by
      by_contra hc; push_neg at hc; nlinarith
    refine ⟨hBpos, hGpos, ?_⟩
    have : 0 < h / 2 + s * (κ - 1) := by
      rcases le_or_gt 1 κ with hk | hk
      · nlinarith
      · nlinarith
    by_contra hc; push_neg at hc; nlinarith

lemma ray_end_alg {σ H0 κ : ℝ} (hσ2 : σ ^ 2 = 1) (hL : H0 ^ 2 + κ ^ 2 = 2 * κ)
    (hκ : 1 / 2 < κ) : σ * (H0 / 2 - 1 * σ * κ) < 0 := by
  have hH2 : (σ * H0) ^ 2 = 2 * κ - κ ^ 2 := by rw [mul_pow, hσ2, one_mul]; linarith
  have h4 : (σ * H0) ^ 2 < (2 * κ) ^ 2 := by rw [hH2]; nlinarith
  have h5 : σ * H0 < 2 * κ := lt_of_pow_lt_pow_left₀ 2 (by linarith) h4
  have e : σ * (H0 / 2 - 1 * σ * κ) = σ * H0 / 2 - κ := by linear_combination (-κ) * hσ2
  rw [e]; linarith

section Ray

variable {X : Finset Plane} (hX : IsSeparated X) {b x c : Plane} (hb : b ∈ X) (hx : x ∈ X)
  (hc : c ∈ X) (hbx : dist b x = 1) (hxc : dist x c = 1) (hbc : 1 < dist b c) {ε : ℝ}
  (hε : ε = 1 ∨ ε = -1) (hhalf : ∀ z ∈ X, 0 ≤ ε * det2 (c - b) (z - b))
  (hdeg : det2 (c - b) (x - b) ≠ 0)

include hx hbx hxc hbc hε hhalf hdeg in
/-- **The ray through the cap.**  If a unit rhombus of `X` sits on the port `b x` (gate
`{a, a + u}`, step `w₀` in the direction `N` normal to `u`), then the normal ray from the midpoint
of the port away from the rhombus runs through the cap and leaves the half-plane of `X` before
length one. -/
lemma port_ray {a u w0 N : Plane} (hN : N = rot u ∨ N = -rot u)
    (hea : s(b, x) = s(a, a + u)) (ha1 : a + w0 ∈ X) (ha2 : a + u + w0 ∈ X) (hw0 : ‖w0‖ = 1)
    (hw0u : |inner ℝ w0 u| < 1 / 2) (hw0N : 0 < inner ℝ w0 N) :
    (∀ s : ℝ, 0 < s → s ≤ 1 → a + (1 / 2 : ℝ) • u - s • N ∈
      (openTri b x c ∪ openSegment ℝ b c) ∪ {z | ε * det2 (c - b) (z - b) < 0}) ∧
    ε * det2 (c - b) (a + (1 / 2 : ℝ) • u - N - b) < 0 := by
  obtain ⟨σ, hσ, hNσ, hmid, hbw, hA⟩ := port_normalize hN hea ha1 ha2 hw0u
  have hen : ‖x - b‖ = 1 := by rw [← dist_eq_norm, dist_comm]; exact hbx
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = inner ℝ (c - b) (x - b) := ⟨_, rfl⟩
  obtain ⟨H0, hH0⟩ : ∃ H0, H0 = det2 (c - b) (x - b) := ⟨_, rfl⟩
  rw [← hH0] at hdeg
  have e1 := dist_sq_coord b x
  have e2 := dist_sq_coord x c
  have e3 := dist_sq_coord b c
  rw [hbx] at e1; rw [hxc] at e2
  have hκv : 2 * κ = dist b c ^ 2 := by
    rw [hκ, inner_coord]
    simp only [PiLp.sub_apply]
    linear_combination (-1 : ℝ) * e1 + e2 - e3
  have hL : H0 ^ 2 + κ ^ 2 = 2 * κ := by
    rw [hκv, hH0, hκ, inner_coord, e3]
    unfold det2
    simp only [PiLp.sub_apply]
    linear_combination (-((c 0 - b 0) ^ 2 + (c 1 - b 1) ^ 2)) * e1
  have hκ1 : 1 / 2 < κ := by nlinarith
  have hhpos : 0 < ε * H0 := by
    have := hhalf x hx
    rw [← hH0] at this
    rcases lt_or_eq_of_le this with h | h
    · exact h
    · exfalso; rcases hε with rfl | rfl <;> simp at h <;> exact hdeg (by linarith)
  have hε2 : ε ^ 2 = 1 := by rcases hε with rfl | rfl <;> norm_num
  -- frame coordinates of `w₀`
  have hAB : inner ℝ w0 (x - b) ^ 2 + inner ℝ w0 (rot (x - b)) ^ 2 = 1 := by
    have := inner_sq_add_inner_rot_sq (x - b) w0
    rw [hen, hw0] at this; simpa using this
  have hA2 : inner ℝ w0 (x - b) ^ 2 < 1 / 4 := by
    have := abs_lt.1 hA; nlinarith
  have hσB : 0 < σ * inner ℝ w0 (rot (x - b)) := by
    rw [hNσ, inner_smul_right] at hw0N; exact hw0N
  have hw0b : 0 ≤ ε * (inner ℝ w0 (x - b) * H0 + inner ℝ w0 (rot (x - b)) * κ) := by
    have := hhalf _ hbw
    rw [add_sub_cancel_left, det2_frame (c - b) w0 (x - b) hen, ← hH0, ← hκ] at this
    exact this
  have hσε : σ = ε := port_sign_alg hε hσ hAB hA2 hσB hhpos hL hκ1 hw0b
  subst hσε
  -- the ray
  have hD : det2 (x - b) (c - b) = -H0 := by rw [hH0]; unfold det2; ring
  have hD0 : det2 (x - b) (c - b) ≠ 0 := by rw [hD]; exact neg_ne_zero.2 hdeg
  have hy : ∀ s : ℝ, a + (1 / 2 : ℝ) • u - s • N - b =
      (1 / 2 : ℝ) • (x - b) - (s * σ) • rot (x - b) := by
    intro s; rw [hmid, hNσ]; module
  have hg : ∀ s : ℝ, det2 (c - b) (a + (1 / 2 : ℝ) • u - s • N - b) = H0 / 2 - s * σ * κ := by
    intro s
    rw [hy, det2_sub_right, det2_smul_right, det2_smul_right, det2_rot, ← hH0, ← hκ]
    ring
  have hgam : ∀ s : ℝ, det2 (x - b) (a + (1 / 2 : ℝ) • u - s • N - b) = -(s * σ) := by
    intro s
    rw [hy, det2_sub_right, det2_smul_right, det2_smul_right, det2_rot,
      real_inner_self_eq_norm_sq, hen]
    have : det2 (x - b) (x - b) = 0 := by unfold det2; ring
    rw [this]; ring
  refine ⟨fun s hs0 hs1 => ?_, ?_⟩
  · have hcr := cramer_bary hD0 (a + (1 / 2 : ℝ) • u - s • N)
    rw [hg s, hgam s, ← hH0, hD] at hcr
    set Bc := (H0 / 2 - s * σ * κ) / H0 with hBc
    set Gc := -(s * σ) / -H0 with hGc
    have hBv : Bc * (σ * H0) = σ * H0 / 2 - s * κ := by
      rw [hBc]; field_simp; linear_combination (-2 * s * κ) * hε2
    have hGv : Gc * (σ * H0) = s := by
      rw [hGc]; field_simp; linear_combination hε2
    rcases ray_bary_alg hhpos hκ1 hs0 hBv hGv with hneg | ⟨hB0, hG, hA'⟩ | ⟨hB, hG, hA'⟩
    · right
      show σ * det2 (c - b) (a + (1 / 2 : ℝ) • u - s • N - b) < 0
      rw [hg s]
      have e : σ * (H0 / 2 - s * σ * κ) = σ * H0 / 2 - s * κ := by
        linear_combination (-(s * κ)) * hε2
      rw [e]; exact hneg
    · left; right
      refine ⟨1 - Bc - Gc, Gc, hA', hG, by rw [hB0]; ring, ?_⟩
      rw [hcr, hB0, zero_smul, add_zero]
    · left; left
      exact ⟨1 - Bc - Gc, Bc, Gc, hA', hB, hG, by ring, hcr⟩
  · have := hg 1
    rw [one_smul] at this
    rw [this]
    exact ray_end_alg hε2 hL hκ1

end Ray

end Erdos99
end

end PortRay

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `SourceCap`
-/

section SourceCap

/-!
# The cap of a source edge

For a source edge `e = {a, a + u}` of `X` (a unit hull side or a port of a two-edge hull return)
carrying a unit rhombus on the side `N`, there is a hull side `(v, w)` and a region `C` (the
cap), avoided by `X` and by all unit segments of `X`, such that the normal ray from the midpoint
of `e` away from the rhombus runs through `C` and then beyond the line `v w`.
-/

open scoped BigOperators Real
open Set

@[expose] public noncomputable section

open Classical

namespace Erdos99

lemma rot_smul' (t : ℝ) (z : Plane) : rot (t • z) = t • rot z := by
  rw [plane_ext_iff]; simp [rot]

/-- If the edge is parallel to the supporting line `v w`, the normal ray leaves the half-plane at
once. -/
lemma ray_out_of_parallel {X : Finset Plane} {d v a u w0 N a' : Plane}
    (hN : N = rot u ∨ N = -rot u) (hhalf : ∀ z ∈ X, 0 ≤ det2 d (z - v))
    (hpar : det2 d u = 0) (hwv : d ≠ 0) (ha : det2 d (a - v) = 0)
    (ha' : det2 d (a' - v) = 0) (ha'X : a' + w0 ∈ X) (hw0N : 0 < inner ℝ w0 N) :
    ∀ s : ℝ, 0 < s → det2 d (a + (1 / 2 : ℝ) • u - s • N - v) < 0 := by
  intro s hs
  obtain ⟨t, ht⟩ := eq_smul_of_det2_eq_zero hwv hpar
  obtain ⟨ν, hν, hNν⟩ : ∃ ν : ℝ, (ν = 1 ∨ ν = -1) ∧ N = ν • rot u := by
    rcases hN with h | h
    · exact ⟨1, Or.inl rfl, by rw [h, one_smul]⟩
    · exact ⟨-1, Or.inr rfl, by rw [h, neg_one_smul]⟩
  have hw0 : 0 ≤ det2 (d) w0 := by
    have := hhalf _ ha'X
    rwa [show a' + w0 - v = (a' - v) + w0 by abel, det2_add_right, ha', zero_add] at this
  have hN' : inner ℝ w0 N = ν * t * det2 (d) w0 := by
    rw [hNν, ht, rot_smul', inner_smul_right, inner_smul_right, inner_rot_eq_det2]; ring
  rw [hN'] at hw0N
  have hpos : 0 < ν * t := by
    rcases lt_or_eq_of_le hw0 with h | h
    · exact pos_of_mul_pos_left hw0N h.le
    · rw [← h, mul_zero] at hw0N; exact absurd hw0N (lt_irrefl 0)
  have hdN : det2 (d) N = ν * t * ‖d‖ ^ 2 := by
    rw [hNν, ht, rot_smul', det2_smul_right, det2_smul_right, det2_rot,
      real_inner_self_eq_norm_sq]; ring
  have hn : 0 < ‖d‖ ^ 2 := by positivity
  have e : det2 (d) (a + (1 / 2 : ℝ) • u - s • N - v) =
      det2 (d) (a - v) + (1 / 2) * det2 (d) u - s * det2 (d) N := by
    simp only [det2, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring
  rw [e, ha, hpar, hdN]
  nlinarith [mul_pos hpos hn]

/-- The cap of a port `b x` of a two-edge return `(b, x, c)`, in the half-plane
`ε det(c - b, z - b) ≥ 0` of `X`. -/
lemma port_cap_full {X : Finset Plane} (hX : IsSeparated X) {b x c : Plane} (hb : b ∈ X)
    (hx : x ∈ X) (hc : c ∈ X) (hbx : dist b x = 1) (hxc : dist x c = 1) (hbc : 1 < dist b c)
    {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (hhalf : ∀ z ∈ X, 0 ≤ ε * det2 (c - b) (z - b))
    {a u w0 N : Plane} (hN : N = rot u ∨ N = -rot u) (hea : s(b, x) = s(a, a + u))
    (ha1 : a + w0 ∈ X) (ha2 : a + u + w0 ∈ X) (hw0 : ‖w0‖ = 1) (hw0u : |inner ℝ w0 u| < 1 / 2)
    (hw0N : 0 < inner ℝ w0 N) :
    ∃ C : Set Plane, (∀ z ∈ X, z ∉ C) ∧
      (∀ p ∈ X, ∀ q ∈ X, dist p q = 1 → Disjoint (segment ℝ p q) C) ∧
      (∀ s : ℝ, 0 < s → s ≤ 1 → a + (1 / 2 : ℝ) • u - s • N ∈
        C ∪ {z | ε * det2 (c - b) (z - b) < 0}) ∧
      ε * det2 (c - b) (a + (1 / 2 : ℝ) • u - N - b) < 0 := by
  by_cases hdeg : det2 (c - b) (x - b) = 0
  · -- degenerate return: the port lies on the hull side
    refine ⟨∅, fun z _ h => h, fun p _ q _ _ => Set.disjoint_empty _, ?_, ?_⟩
    · have hd : ε • (c - b) ≠ 0 := by
        refine smul_ne_zero (by rcases hε with rfl | rfl <;> norm_num) ?_
        intro h; rw [sub_eq_zero] at h; rw [h, dist_self] at hbc; linarith
      obtain ⟨σ, -, -, -, hbw, -⟩ := port_normalize hN hea ha1 ha2 hw0u
      have hhalf' : ∀ z ∈ X, 0 ≤ det2 (ε • (c - b)) (z - b) := fun z hz => by
        rw [det2_smul_left]; exact hhalf z hz
      have hline : ∀ y, y = b ∨ y = x → det2 (ε • (c - b)) (y - b) = 0 := by
        rintro y (rfl | rfl)
        · rw [sub_self]; simp [det2]
        · rw [det2_smul_left, hdeg, mul_zero]
      have hab : (a = b ∨ a = x) ∧ (u = x - b ∨ u = b - x) := by
        rcases Sym2.eq_iff.1 hea with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨Or.inl h1.symm, Or.inl (by rw [h2, h1]; abel)⟩
        · exact ⟨Or.inr h2.symm, Or.inr (by rw [h1, h2]; abel)⟩
      have hpar : det2 (ε • (c - b)) u = 0 := by
        rcases hab.2 with h | h
        · rw [h]; exact hline x (Or.inr rfl)
        · rw [h, show b - x = -(x - b) by abel, show -(x - b) = (-1 : ℝ) • (x - b) by simp,
            det2_smul_right, hline x (Or.inr rfl), mul_zero]
      have hray := ray_out_of_parallel hN hhalf' hpar hd (hline a hab.1)
        (hline b (Or.inl rfl)) (by rw [show b + w0 = b + w0 by rfl]; exact hbw) hw0N
      intro s hs0 _
      right
      have := hray s hs0
      rw [det2_smul_left] at this
      exact this
    · obtain ⟨σ, -, -, -, hbw, -⟩ := port_normalize hN hea ha1 ha2 hw0u
      have hd : ε • (c - b) ≠ 0 := by
        refine smul_ne_zero (by rcases hε with rfl | rfl <;> norm_num) ?_
        intro h; rw [sub_eq_zero] at h; rw [h, dist_self] at hbc; linarith
      have hhalf' : ∀ z ∈ X, 0 ≤ det2 (ε • (c - b)) (z - b) := fun z hz => by
        rw [det2_smul_left]; exact hhalf z hz
      have hline : ∀ y, y = b ∨ y = x → det2 (ε • (c - b)) (y - b) = 0 := by
        rintro y (rfl | rfl)
        · rw [sub_self]; simp [det2]
        · rw [det2_smul_left, hdeg, mul_zero]
      have hab : (a = b ∨ a = x) ∧ (u = x - b ∨ u = b - x) := by
        rcases Sym2.eq_iff.1 hea with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨Or.inl h1.symm, Or.inl (by rw [h2, h1]; abel)⟩
        · exact ⟨Or.inr h2.symm, Or.inr (by rw [h1, h2]; abel)⟩
      have hpar : det2 (ε • (c - b)) u = 0 := by
        rcases hab.2 with h | h
        · rw [h]; exact hline x (Or.inr rfl)
        · rw [h, show b - x = -(x - b) by abel, show -(x - b) = (-1 : ℝ) • (x - b) by simp,
            det2_smul_right, hline x (Or.inr rfl), mul_zero]
      have := ray_out_of_parallel hN hhalf' hpar hd (hline a hab.1)
        (hline b (Or.inl rfl)) hbw hw0N 1 one_pos
      rw [one_smul, det2_smul_left] at this
      exact this
  · refine ⟨openTri b x c ∪ openSegment ℝ b c, ?_, ?_, ?_, ?_⟩
    · rintro z hz (⟨α, β, γ, hα, hβ, hγ, hs, hze⟩ | ⟨α, γ, hα, hγ, hs, hze⟩)
      · exact not_mem_cap_of_mem hX hx hbx hxc hbc hdeg hz hα hβ.le hγ hs hze
      · exact not_mem_cap_of_mem hX hx hbx hxc hbc hdeg hz (β := 0) hα le_rfl hγ (by linarith)
          (by rw [← hze]; simp)
    · intro p hp q hq hpq
      exact unit_seg_disjoint_cap hX hb hx hc hbx hxc hbc hε hhalf hdeg hp hq hpq
    · exact (port_ray hx hbx hxc hbc hε hhalf hdeg hN hea ha1 ha2 hw0 hw0u hw0N).1
    · exact (port_ray hx hbx hxc hbc hε hhalf hdeg hN hea ha1 ha2 hw0 hw0u hw0N).2

lemma inner_port {v x w : Plane} (h1 : dist v x = 1) (h2 : dist x w = 1) :
    inner ℝ (x - v) (w - v) = ‖w - v‖ ^ 2 / 2 := by
  have e := norm_sub_sq_real (x - v) (w - v)
  rw [show x - v - (w - v) = x - w by abel, ← dist_eq_norm, ← dist_eq_norm, h2, dist_comm, h1]
    at e
  linarith

lemma norm_le_two_abs_inner {u v w : Plane} (h : |inner ℝ u (w - v)| = ‖w - v‖ ^ 2 / 2)
    (h1 : 1 ≤ ‖w - v‖) : ‖w - v‖ ≤ 2 * |inner ℝ u (w - v)| := by
  rw [h]; nlinarith

/-- **The cap of a source edge.** -/
theorem source_cap {X : Finset Plane} (hX : IsSeparated X)
    {e : Sym2 Plane} (he : e ∈ sourceEdges X) {a u w0 N : Plane}
    (hN : N = rot u ∨ N = -rot u) (hea : e = s(a, a + u)) (ha1 : a + w0 ∈ X)
    (ha2 : a + u + w0 ∈ X) (hw0 : ‖w0‖ = 1) (hw0u : |inner ℝ w0 u| < 1 / 2)
    (hw0N : 0 < inner ℝ w0 N) :
    ∃ v w : Plane, ∃ C : Set Plane, IsCcwHullSide X v w ∧
      (∀ z ∈ X, z ∉ C) ∧
      (∀ p ∈ X, ∀ q ∈ X, dist p q = 1 → Disjoint (segment ℝ p q) C) ∧
      (∀ s : ℝ, 0 < s → s ≤ 1 → a + (1 / 2 : ℝ) • u - s • N ∈
        C ∪ {z | det2 (w - v) (z - v) < 0}) ∧
      det2 (w - v) (a + (1 / 2 : ℝ) • u - N - v) < 0 ∧
      dist a v ≤ 2 ∧ ‖w - v‖ ≤ 2 * |inner ℝ u (w - v)| := by
  unfold sourceEdges at he
  simp only [Finset.mem_union, Finset.mem_image] at he
  rcases he with (⟨⟨v, w⟩, hvw, rfl⟩ | ⟨⟨v, x, w⟩, ht, rfl⟩) | ⟨⟨v, x, w⟩, ht, rfl⟩
  · -- a unit hull side
    simp only at hea
    obtain ⟨h1, hd⟩ := Finset.mem_filter.1 hvw
    obtain ⟨-, hside⟩ := Finset.mem_filter.1 h1
    simp only at hd hside
    have hhalf := hside.2.2.2
    have hcases : (a = v ∧ w - v = u) ∨ (a = w ∧ w - v = -u) := by
      rcases Sym2.eq_iff.1 hea with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1.symm, by rw [h1, h2]; abel⟩
      · exact Or.inr ⟨h2.symm, by rw [h1, h2]; abel⟩
    have hwv : w - v ≠ 0 := by
      intro h; rw [sub_eq_zero] at h; rw [h, dist_self] at hd; norm_num at hd
    have hpar : det2 (w - v) u = 0 := by
      rcases hcases with ⟨-, h⟩ | ⟨-, h⟩
      · rw [h]; unfold det2; ring
      · rw [show u = -(w - v) by rw [h, neg_neg]]; unfold det2; simp; ring
    have ha : det2 (w - v) (a - v) = 0 := by
      rcases hcases with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · simp [det2]
      · unfold det2; ring
    have hray := ray_out_of_parallel hN hhalf hpar hwv ha ha ha1 hw0N
    have hnorm : ‖w - v‖ = 1 := by rw [← dist_eq_norm, dist_comm]; exact hd
    refine ⟨v, w, ∅, hside, fun z _ h => h, fun p _ q _ _ => Set.disjoint_empty _,
      fun s hs0 _ => Or.inr (hray s hs0), by simpa using hray 1 one_pos, ?_, ?_⟩
    · rcases hcases with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · rw [dist_self]; norm_num
      · rw [dist_comm, hd]; norm_num
    · rw [hnorm]
      rcases hcases with ⟨-, h⟩ | ⟨-, h⟩
      · rw [h, real_inner_self_eq_norm_sq, ← h, hnorm]; norm_num
      · rw [h, inner_neg_right, real_inner_self_eq_norm_sq, abs_neg,
          show ‖u‖ = ‖w - v‖ by rw [h, norm_neg], hnorm]; norm_num
  · -- the port `v x` of a two-edge return
    simp only at hea
    obtain ⟨hmem, hside, h1, h2, h3⟩ := Finset.mem_filter.1 ht
    simp only [Finset.mem_product] at hmem
    simp only at hside h1 h2 h3
    obtain ⟨hv, hx, hw⟩ := hmem
    obtain ⟨C, hC1, hC2, hC3, hC4⟩ := port_cap_full hX hv hx hw h1 h2 h3 (ε := 1) (Or.inl rfl)
      (fun z hz => by rw [one_mul]; exact hside.2.2.2 z hz) hN hea ha1 ha2 hw0 hw0u hw0N
    simp only [one_mul] at hC3 hC4
    have hcases : (a = v ∧ u = x - v) ∨ (a = x ∧ u = -(x - v)) := by
      rcases Sym2.eq_iff.1 hea with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact Or.inl ⟨e1.symm, by rw [e2, e1]; abel⟩
      · exact Or.inr ⟨e2.symm, by rw [e1, e2]; abel⟩
    refine ⟨v, w, C, hside, hC1, hC2, hC3, hC4, ?_, ?_⟩
    · rcases hcases with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · rw [dist_self]; norm_num
      · rw [dist_comm, h1]; norm_num
    · refine norm_le_two_abs_inner ?_ (by rw [← dist_eq_norm, dist_comm]; exact h3.le)
      rcases hcases with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · rw [inner_port h1 h2, abs_of_nonneg (by positivity)]
      · rw [inner_neg_left, inner_port h1 h2, abs_neg, abs_of_nonneg (by positivity)]
  · -- the port `x w` of a two-edge return
    simp only at hea
    obtain ⟨hmem, hside, h1, h2, h3⟩ := Finset.mem_filter.1 ht
    simp only [Finset.mem_product] at hmem
    simp only at hside h1 h2 h3
    obtain ⟨hv, hx, hw⟩ := hmem
    have hconv : ∀ z, -1 * det2 (v - w) (z - w) = det2 (w - v) (z - v) := by
      intro z; simp only [det2, PiLp.sub_apply]; ring
    obtain ⟨C, hC1, hC2, hC3, hC4⟩ := port_cap_full hX hw hx hv (by rw [dist_comm]; exact h2)
      (by rw [dist_comm]; exact h1) (by rw [dist_comm]; exact h3) (ε := -1) (Or.inr rfl)
      (fun z hz => by rw [hconv]; exact hside.2.2.2 z hz) hN (by rw [Sym2.eq_swap]; exact hea)
      ha1 ha2 hw0 hw0u hw0N
    simp only [hconv] at hC3 hC4
    have hcases : (a = x ∧ u = w - x) ∨ (a = w ∧ u = -(w - x)) := by
      rcases Sym2.eq_iff.1 hea with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact Or.inl ⟨e1.symm, by rw [e2, e1]; abel⟩
      · exact Or.inr ⟨e2.symm, by rw [e1, e2]; abel⟩
    have hip : inner ℝ (w - x) (w - v) = ‖w - v‖ ^ 2 / 2 := by
      rw [show w - x = -(x - w) by abel, show w - v = -(v - w) by abel, inner_neg_neg,
        inner_port (by rw [dist_comm]; exact h2) (by rw [dist_comm]; exact h1), norm_neg]
    refine ⟨v, w, C, hside, hC1, hC2, hC3, hC4, ?_, ?_⟩
    · rcases hcases with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · rw [dist_comm, h1]; norm_num
      · have := dist_triangle a x v
        rw [dist_comm a x, h2, dist_comm x v, h1] at this
        linarith
    · refine norm_le_two_abs_inner ?_ (by rw [← dist_eq_norm, dist_comm]; exact h3.le)
      rcases hcases with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · rw [hip, abs_of_nonneg (by positivity)]
      · rw [inner_neg_left, hip, abs_neg, abs_of_nonneg (by positivity)]

end Erdos99
end

end SourceCap

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `GateChain`
-/

section GateChain

/-!
# The gate chain of a track between two terminal edges

A track joining two distinct terminal edges `e, e'` is a chain of unit "gates"
`{a l, a l + u}` (`l ≤ k`) with `e` the first and `e'` the last gate, consecutive gates spanning
unit rhombi whose steps `w l` all point to the same side `J u` of the gates.  The number `k` of
steps is at most the number of rhombi on the track.
-/

open scoped BigOperators Real

@[expose] public noncomputable section

open Classical

namespace Erdos99

/-- A terminal edge of a track is its lowest or its highest edge. -/
lemma terminal_min_or_max {X : Finset Plane} (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X)
    {T : Finset (Sym2 Plane)} (hT : T ∈ tracks X) {u : Plane} (hu : ‖u‖ = 1)
    (hdir : ∀ e ∈ T, DirOf u e) {m top : Sym2 Plane} (hm : m ∈ T)
    (hmin : ∀ f ∈ T, ht u m ≤ ht u f) (htop : top ∈ T) (hmax : ∀ f ∈ T, ht u f ≤ ht u top)
    {f : Sym2 Plane} (hfT : f ∈ T) (hterm : IsTerminal X f) : f = m ∨ f = top := by
  by_contra hne
  push_neg at hne
  obtain ⟨hfm, hft⟩ := hne
  have hup : upE X u f ≠ f := by
    intro hfix
    obtain ⟨j, hj⟩ := mem_range_iterate hX htri hT hu hdir hm hmin htop
    obtain ⟨i, hi⟩ := mem_range_iterate hX htri hT hu hdir hm hmin hfT
    rcases le_total i j with hij | hij
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
      rw [add_comm, Function.iterate_add_apply, hi, Function.iterate_fixed hfix] at hj
      exact hft hj
    · rcases iterate_upE_mono hX htri hT hu hdir hm j i hij with h | h
      · rw [hi, hj] at h; exact hft h
      · rw [hi, hj] at h; have := hmax f hfT; linarith [aStar_pos]
  obtain ⟨oup, hltup⟩ := upE_spec hup
  have hex : ∃ k, (upE X u)^[k] m = f := mem_range_iterate hX htri hT hu hdir hm hmin hfT
  set k := Nat.find hex
  have hk : (upE X u)^[k] m = f := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro h0; rw [h0] at hk; exact hfm hk.symm
  obtain ⟨k', hk'⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  set g := (upE X u)^[k'] m
  have hgf : upE X u g = f := by
    rw [← hk, hk', Function.iterate_succ_apply']
  have hgne : g ≠ f := fun h => Nat.find_min hex (show k' < k by omega) h
  have hug : upE X u g ≠ g := by rw [hgf]; exact hgne.symm
  obtain ⟨odown, hltdown⟩ := upE_spec hug
  rw [hgf] at odown hltdown
  have := hterm _ _ oup (oppositeSides_symm odown)
  rw [this] at hltup
  linarith

lemma mem_X_of_mem_unitEdges {X : Finset Plane} {e : Sym2 Plane} (he : e ∈ unitEdges X)
    {z : Plane} (hz : z ∈ e) : z ∈ X := by
  obtain ⟨⟨p, q⟩, hp, rfl⟩ := Finset.mem_image.1 he
  simp only [Finset.mem_filter, Finset.mem_product] at hp
  rcases Sym2.mem_iff.1 hz with rfl | rfl
  · exact hp.1.1
  · exact hp.1.2

lemma gate_form {u : Plane} {g : Sym2 Plane} (hd : DirOf u g) :
    ∃ p : Plane, g = s(p, p + u) := by
  have hg : s(g.out.1, g.out.2) = g := Quot.out_eq g
  rcases hd with h | h
  · refine ⟨g.out.2, ?_⟩
    have : g.out.1 = g.out.2 + u := by rw [← h, dv]; abel
    calc g = s(g.out.1, g.out.2) := hg.symm
      _ = s(g.out.2, g.out.2 + u) := by rw [this, Sym2.eq_swap]
  · refine ⟨g.out.1, ?_⟩
    have : g.out.2 = g.out.1 + u := by
      have h' : g.out.1 - g.out.2 = -u := h
      rw [← neg_neg u, ← h']; abel
    calc g = s(g.out.1, g.out.2) := hg.symm
      _ = s(g.out.1, g.out.1 + u) := by rw [this]

lemma gate_unique {u p q : Plane} (hu : u ≠ 0) (h : s(p, p + u) = s(q, q + u)) : p = q := by
  rcases Sym2.eq_iff.1 h with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact h1
  · exfalso; apply hu
    have h3 : q + u + u = q := by rw [← h1]; exact h2
    have : u + u = 0 := by
      calc u + u = (q + u + u) - q := by abel
        _ = 0 := by rw [h3]; abel
    have h2u : (2 : ℝ) • u = 0 := by rw [two_smul]; exact this
    exact (smul_eq_zero.1 h2u).resolve_left two_ne_zero

/-- The step between consecutive gates across a rhombus. -/
lemma gate_step {X : Finset Plane} (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X)
    {u p q : Plane} (hu : ‖u‖ = 1) (o : OppositeSides X s(p, p + u) s(q, q + u)) :
    ‖q - p‖ = 1 ∧ |inner ℝ (q - p) u| < 1 / 2 ∧
      ht u s(q, q + u) - ht u s(p, p + u) = inner ℝ (q - p) (rot u) := by
  have hu0 : u ≠ 0 := by intro h; rw [h, norm_zero] at hu; norm_num at hu
  obtain ⟨a, b, c, d, hR, he, hf⟩ := oppositeSides_data hX htri o
  have hdir : DirOf u s(a, b) := by
    rw [← he]
    rcases dv_mk p (p + u) with h | h
    · right; rw [h]; abel
    · left; rw [h]; abel
  obtain ⟨g, i, n⟩ := hR.step hdir
  have hpara := hR.para
  have key : d - a = q - p := by
    rcases Sym2.eq_iff.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · -- `a = p`, `b = p + u`
      have hcd : c - d = u := by
        have : c - d = b - a := by rw [sub_eq_sub_iff_add_eq_add, add_comm c a, hpara, add_comm]
        rw [this, ← h1, ← h2]; abel
      rcases Sym2.eq_iff.1 hf with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · exfalso; apply hu0
        have : c - d = -u := by rw [← h3, ← h4]; abel
        have h2u : u + u = 0 := by
          calc u + u = (c - d) + u := by rw [hcd]
            _ = 0 := by rw [this]; abel
        have : (2 : ℝ) • u = 0 := by rw [two_smul]; exact h2u
        exact (smul_eq_zero.1 this).resolve_left two_ne_zero
      · rw [← h3, ← h1]
    · -- `a = p + u`, `b = p`
      have hcd : c - d = -u := by
        have : c - d = b - a := by rw [sub_eq_sub_iff_add_eq_add, add_comm c a, hpara, add_comm]
        rw [this, ← h1, ← h2]; abel
      rcases Sym2.eq_iff.1 hf with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · rw [← h4, ← h2]; abel
      · exfalso; apply hu0
        have : c - d = u := by rw [← h3, ← h4]; abel
        have h2u : u + u = 0 := by
          calc u + u = u - -u := by abel
            _ = 0 := by rw [← hcd, this]; abel
        have : (2 : ℝ) • u = 0 := by rw [two_smul]; exact h2u
        exact (smul_eq_zero.1 this).resolve_left two_ne_zero
  rw [key] at g i n
  refine ⟨n, i, ?_⟩
  rw [he, hf]; exact g

/-- Orient a track so that a given terminal edge is its lowest edge. -/
lemma exists_orientation {X : Finset Plane} (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X)
    {e : Sym2 Plane} (heR : e ∈ rhombusEdges X) (he : IsTerminal X e) :
    ∃ u : Plane, ‖u‖ = 1 ∧ (∀ f ∈ trackOf X e, DirOf u f) ∧
      ∀ f ∈ trackOf X e, ht u e ≤ ht u f := by
  set T := trackOf X e
  have hT : T ∈ tracks X := trackOf_mem_tracks heR
  have heT : e ∈ T := mem_trackOf_self heR
  have hu0 : ‖dv e‖ = 1 := norm_dv_of_mem_unitEdges (Finset.mem_filter.1 heR).1
  have hdir0 : ∀ f ∈ T, DirOf (dv e) f := fun f hf => sameDir_of_mem_trackOf hf
  obtain ⟨m, hm, hmin⟩ := T.exists_min_image (ht (dv e)) ⟨e, heT⟩
  obtain ⟨top, htop, hmax⟩ := T.exists_max_image (ht (dv e)) ⟨e, heT⟩
  rcases terminal_min_or_max hX htri hT hu0 hdir0 hm hmin htop hmax heT he with h | h
  · exact ⟨dv e, hu0, hdir0, fun f hf => h ▸ hmin f hf⟩
  · refine ⟨-dv e, by rw [norm_neg, hu0], fun f hf => ?_, fun f hf => ?_⟩
    · rcases hdir0 f hf with h' | h'
      · right; rw [h', neg_neg]
      · left; exact h'
    · have hneg : ∀ g, ht (-dv e) g = -ht (dv e) g := fun g => by
        rw [ht, ht, rot_neg, inner_neg_right]
      rw [hneg, hneg]
      have := hmax f hf
      rw [← h] at this
      linarith

/-- **The gate chain of a track between two terminal edges.** -/
theorem exists_gate_chain {X : Finset Plane} (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X)
    {e e' : Sym2 Plane} (he : IsTerminal X e) (hne : e ≠ e') (hmem : e' ∈ trackOf X e) :
    ∃ (u : Plane) (k : ℕ) (a w : ℕ → Plane), ‖u‖ = 1 ∧ 0 < k ∧
      k ≤ trackLength X (trackOf X e) ∧
      (∀ l ≤ k, a l ∈ X ∧ a l + u ∈ X) ∧
      (∀ l < k, a (l + 1) = a l + w l ∧ ‖w l‖ = 1 ∧ |inner ℝ (w l) u| < 1 / 2 ∧
        0 < inner ℝ (w l) (rot u)) ∧
      e = s(a 0, a 0 + u) ∧ e' = s(a k, a k + u) := by
  obtain ⟨he'R, heq⟩ := mem_trackOf.1 hmem
  have heR : e ∈ rhombusEdges X := mem_rhombusEdges_of_eqvGen heq he'R
  set T := trackOf X e with hTdef
  have hT : T ∈ tracks X := trackOf_mem_tracks heR
  have heT : e ∈ T := mem_trackOf_self heR
  obtain ⟨u, hu, hdir, hlow⟩ := exists_orientation hX htri heR he
  have hu0 : u ≠ 0 := by intro h; rw [h, norm_zero] at hu; norm_num at hu
  -- the sweep from `e`
  set f : ℕ → Sym2 Plane := fun l => (upE X u)^[l] e with hf
  have hfT : ∀ l, f l ∈ T := fun l => iterate_upE_mem hT heT l
  have hex : ∃ k, f k = e' := mem_range_iterate hX htri hT hu hdir heT hlow hmem
  set k := Nat.find hex with hk
  have hfk : f k = e' := Nat.find_spec hex
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exfalso; rw [h] at hfk; exact hne hfk
    · exact h
  have hstepE : ∀ l < k, OppositeSides X (f l) (f (l + 1)) ∧ ht u (f l) < ht u (f (l + 1)) := by
    intro l hl
    have hsucc : f (l + 1) = upE X u (f l) := by
      simp only [hf]; rw [Function.iterate_succ_apply']
    have hne' : upE X u (f l) ≠ f l := by
      intro hfix
      have hconst : ∀ j, f (l + j) = f l := by
        intro j
        simp only [hf]
        rw [add_comm, Function.iterate_add_apply, Function.iterate_fixed hfix]
      have := hconst (k - l)
      rw [show l + (k - l) = k by omega, hfk] at this
      exact Nat.find_min hex hl this.symm
    rw [hsucc]; exact upE_spec hne'
  -- gate points
  have hform : ∀ l, ∃ p : Plane, f l = s(p, p + u) := fun l => gate_form (hdir _ (hfT l))
  choose a ha using hform
  have hunit : ∀ l, f l ∈ unitEdges X := fun l =>
    (Finset.mem_filter.1 (mem_trackOf.1 (hfT l)).1).1
  have hgateX : ∀ l, a l ∈ X ∧ a l + u ∈ X := by
    intro l
    have h := ha l
    exact ⟨mem_X_of_mem_unitEdges (hunit l) (by rw [h]; exact Sym2.mem_mk_left _ _),
      mem_X_of_mem_unitEdges (hunit l) (by rw [h]; exact Sym2.mem_mk_right _ _)⟩
  have hsteps : ∀ l < k, ‖a (l + 1) - a l‖ = 1 ∧ |inner ℝ (a (l + 1) - a l) u| < 1 / 2 ∧
      0 < inner ℝ (a (l + 1) - a l) (rot u) := by
    intro l hl
    obtain ⟨o, hlt⟩ := hstepE l hl
    rw [ha l, ha (l + 1)] at o hlt
    obtain ⟨n, i, g⟩ := gate_step hX htri hu o
    exact ⟨n, i, by rw [← g]; linarith⟩
  -- heights of the gates
  set h : ℕ → ℝ := fun l => inner ℝ (a l) (rot u) with hh
  have hhmono : ∀ l < k, h l < h (l + 1) := by
    intro l hl
    have := (hsteps l hl).2.2
    simp only [hh]
    rw [inner_sub_left] at this
    linarith
  have hhstrict : ∀ i j, i < j → j ≤ k → h i < h j := by
    intro i j hij hjk
    induction j, hij using Nat.le_induction with
    | base => exact hhmono i (by omega)
    | succ j hij ih => exact (ih (by omega)).trans (hhmono j (by omega))
  have hht : ∀ l, ∀ z ∈ f l, inner ℝ z (rot u) = h l := by
    intro l z hz
    rw [ha l] at hz
    rcases Sym2.mem_iff.1 hz with rfl | rfl
    · rfl
    · simp only [hh]; rw [inner_add_left, inner_rot_self, add_zero]
  -- rhombi on the chain
  have hR : ∀ l, l < k → ∃ R ∈ rhombi X, (∀ z ∈ f l, z ∈ R) ∧
      ∀ z ∈ R, z ∈ f l ∨ z ∈ f (l + 1) := by
    intro l hl
    obtain ⟨p, q, r, t, hRm, -, -, -, -, h1, h2⟩ := (hstepE l hl).1
    refine ⟨{p, q, r, t}, hRm, fun z hz => ?_, fun z hz => ?_⟩
    · rw [h1] at hz
      rcases Sym2.mem_iff.1 hz with rfl | rfl <;> simp
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rw [h1, h2]
      rcases hz with rfl | rfl | rfl | rfl <;> simp
  choose! R hRmem hRf hRsub using hR
  have hk_le : k ≤ trackLength X T := by
    unfold trackLength
    have hmaps : ∀ l ∈ Finset.range k, R l ∈ (rhombi X).filter (Crosses T) := by
      intro l hl
      have hl' := Finset.mem_range.1 hl
      exact Finset.mem_filter.2 ⟨hRmem l hl', f l, hfT l, hRf l hl'⟩
    have hinj : Set.InjOn R (Finset.range k : Set ℕ) := by
      intro i hi j hj hij
      have hi' : i < k := Finset.mem_range.1 hi
      have hj' : j < k := Finset.mem_range.1 hj
      have hai : a i ∈ R j := by
        rw [← hij]; exact hRf i hi' _ (by rw [ha i]; exact Sym2.mem_mk_left _ _)
      have haj : a j ∈ R i := by
        rw [hij]; exact hRf j hj' _ (by rw [ha j]; exact Sym2.mem_mk_left _ _)
      have h1 : h i = h j ∨ h i = h (j + 1) := by
        rcases hRsub j hj' _ hai with hz | hz
        · left; exact (hht j _ hz)
        · right; exact (hht (j + 1) _ hz)
      have h2 : h j = h i ∨ h j = h (i + 1) := by
        rcases hRsub i hi' _ haj with hz | hz
        · left; exact (hht i _ hz)
        · right; exact (hht (i + 1) _ hz)
      have hinjh : ∀ i j, i ≤ k → j ≤ k → h i = h j → i = j := by
        intro i j hi hj he
        rcases lt_trichotomy i j with hlt | heq | hgt
        · exact absurd he (hhstrict i j hlt hj).ne
        · exact heq
        · exact absurd he.symm (hhstrict j i hgt hi).ne
      rcases h1 with h1 | h1
      · exact hinjh i j hi'.le hj'.le h1
      · have := hinjh i (j + 1) hi'.le (by omega) h1
        rcases h2 with h2 | h2
        · exact (hinjh j i hj'.le hi'.le h2).symm
        · have := hinjh j (i + 1) hj'.le (by omega) h2
          omega
    have := Finset.card_le_card_of_injOn R
      (fun l hl => Finset.mem_coe.2 (hmaps l (Finset.mem_coe.1 hl))) hinj
    simpa using this
  refine ⟨u, k, a, fun l => a (l + 1) - a l, hu, hk0, hk_le, fun l _ => hgateX l,
    fun l hl => ⟨by show a (l + 1) = a l + (a (l + 1) - a l); abel, hsteps l hl⟩, ?_, ?_⟩
  · have := ha 0
    simpa [hf] using this
  · rw [← ha k, hfk]

end Erdos99
end

end GateChain

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `ShoreGeometry`
-/

section ShoreGeometry

/-!
# The shore of a short source track

If a short track joins two distinct source edges of a separated set lying in a disc of radius
`D/2 + η D` about `O` and reaching `D/2 - δ D` in every direction, then the gates of the track,
the source caps at its two ends and three long segments outside the hull form a crosscut whose
shore `S` lies near the boundary point `O + (D/2) ν`, where `ν` points from `O` to the first gate.
-/

open scoped BigOperators Real
open Set Filter

@[expose] public noncomputable section

open Classical

namespace Erdos99

lemma isTerminal_of_mem_sourceEdges {X : Finset Plane} (hX : IsSeparated X)
    (htri : ¬ HasUnitTriangle X) {e : Sym2 Plane} (he : e ∈ sourceEdges X) : IsTerminal X e := by
  unfold sourceEdges at he
  simp only [Finset.mem_union, Finset.mem_image] at he
  rcases he with (⟨⟨v, w⟩, hvw, rfl⟩ | ⟨⟨v, x, w⟩, ht, rfl⟩) | ⟨⟨v, x, w⟩, ht, rfl⟩
  · exact isTerminal_of_mem_unitHullSides hX htri hvw
  · exact (isTerminal_of_mem_twoEdgeReturns hX htri ht).1
  · exact (isTerminal_of_mem_twoEdgeReturns hX htri ht).2

lemma chain_norm_le {u : Plane} {k : ℕ} {a w : ℕ → Plane}
    (hstep : ∀ l < k, a (l + 1) = a l + w l ∧ ‖w l‖ = 1 ∧ |inner ℝ (w l) u| < 1 / 2 ∧
      0 < inner ℝ (w l) (rot u)) :
    ∀ l ≤ k, ‖a l - a 0‖ ≤ l := by
  intro l
  induction l with
  | zero => intro _; simp
  | succ l ih =>
    intro hl
    obtain ⟨h1, h2, -⟩ := hstep l (by omega)
    rw [h1, show a l + w l - a 0 = (a l - a 0) + w l by abel]
    have := ih (by omega)
    calc ‖a l - a 0 + w l‖ ≤ ‖a l - a 0‖ + ‖w l‖ := norm_add_le _ _
      _ ≤ ((l + 1 : ℕ) : ℝ) := by push_cast; linarith

lemma det2_add_right' (d x y : Plane) : det2 d (x + y) = det2 d x + det2 d y := by
  unfold det2; simp; ring

lemma det2_sub_right' (d x y : Plane) : det2 d (x - y) = det2 d x - det2 d y := by
  unfold det2; simp; ring

lemma det2_smul_right' (d x : Plane) (t : ℝ) : det2 d (t • x) = t * det2 d x := by
  unfold det2; simp; ring

lemma abs_det2_le (d x : Plane) : |det2 d x| ≤ ‖d‖ * ‖x‖ := by
  rw [← inner_rot_eq_det2]
  refine (abs_real_inner_le_norm _ _).trans ?_
  rw [norm_rot, mul_comm]

/-- The support bound at a hull side: points near `v` lie far out in the outward normal
direction of the side. -/
lemma side_far {X : Finset Plane} {v w O : Plane} {D δ : ℝ} (hs : IsCcwHullSide X v w)
    (hsupp : ∀ n : Plane, ‖n‖ = 1 → ∃ x ∈ X, D / 2 - δ * D ≤ inner ℝ (x - O) n)
    {y : Plane} {R : ℝ} (hy : ‖y - v‖ ≤ R) :
    (D / 2 - δ * D - R) * ‖w - v‖ ≤ -det2 (w - v) (y - O) := by
  have hvw := hs.2.2.1
  set d := w - v with hd
  have hL : 0 < ‖d‖ := norm_pos_iff.2 (sub_ne_zero.2 hvw.symm)
  obtain ⟨x, hx, hxn⟩ := hsupp (-(‖d‖⁻¹) • rot d) (by
    rw [norm_smul, norm_neg, norm_inv, norm_norm, norm_rot, inv_mul_cancel₀ hL.ne'])
  rw [real_inner_smul_right, inner_rot_eq_det2] at hxn
  have h1 := hs.2.2.2 x hx
  have h2 := abs_det2_le d (y - v)
  rw [abs_le] at h2
  have e : det2 d (y - O) = det2 d (x - O) - det2 d (x - v) + det2 d (y - v) := by
    rw [← det2_sub_right', ← det2_add_right']; congr 1; abel
  have h3 : (D / 2 - δ * D) * ‖d‖ ≤ -det2 d (x - O) := by
    have := mul_le_mul_of_nonneg_right hxn hL.le
    rwa [show -‖d‖⁻¹ * det2 d (x - O) * ‖d‖ = -det2 d (x - O) by field_simp] at this
  have h4 := mul_le_mul_of_nonneg_left hy hL.le
  nlinarith

lemma inner_lower {O ν m y : Plane} (hν : ‖ν‖ = 1) {R : ℝ} (hy : ‖y - m‖ ≤ R) :
    inner ℝ (m - O) ν - R ≤ inner ℝ (y - O) ν := by
  have e : inner ℝ (y - O) ν = inner ℝ (m - O) ν + inner ℝ (y - m) ν := by
    rw [← inner_add_left]; congr 1; abel
  have h := abs_real_inner_le_norm (y - m) ν
  rw [hν, mul_one, abs_le] at h
  linarith [h.1]

lemma two_fifths {u d ν : Plane} (hu : ‖u‖ = 1) (hν : ‖ν‖ = 1) (hd : 0 < ‖d‖)
    (hud : ‖d‖ ≤ 2 * |inner ℝ u d|) (hdν : (1 - 1 / 200) * ‖d‖ ≤ -det2 d ν) :
    2 / 5 ≤ |inner ℝ u (rot ν)| := by
  set L := ‖d‖
  set g := rot ν - L⁻¹ • d with hg
  have hrn : ‖rot ν‖ = 1 := by rw [norm_rot, hν]
  have hdn : ‖L⁻¹ • d‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hd.ne']
  have hin : inner ℝ (rot ν) d = -det2 d ν := by
    rw [real_inner_comm, inner_rot_eq_det2, det2_swap]
  have hg2 : ‖g‖ ^ 2 ≤ 1 / 100 := by
    rw [hg, norm_sub_sq_real, hrn, hdn, real_inner_smul_right, hin]
    have : (1 - 1 / 200) ≤ L⁻¹ * -det2 d ν := by
      rw [le_inv_mul_iff₀ hd]; linarith
    nlinarith
  have hg1 : ‖g‖ ≤ 1 / 10 := by nlinarith [norm_nonneg g]
  have e : inner ℝ u (rot ν) = L⁻¹ * inner ℝ u d + inner ℝ u g := by
    rw [hg, inner_sub_right, real_inner_smul_right]; ring
  have h1 : 1 / 2 ≤ |L⁻¹ * inner ℝ u d| := by
    rw [abs_mul, abs_inv, abs_norm, le_inv_mul_iff₀ hd]; linarith
  have h2 := abs_real_inner_le_norm u g
  rw [hu, one_mul] at h2
  rw [e]
  have := abs_sub_abs_le_abs_sub (L⁻¹ * inner ℝ u d) (-inner ℝ u g)
  rw [sub_neg_eq_add, abs_neg] at this
  linarith

lemma near_point {x ν : Plane} {D η δ : ℝ} (hν : ‖ν‖ = 1) (hD : 0 ≤ D) (hx : ‖x‖ ≤ D / 2 + η * D)
    (hxν : D / 2 - 2 * δ * D ≤ inner ℝ x ν) :
    ‖x - (D / 2) • ν‖ ^ 2 ≤ D ^ 2 * (η + η ^ 2 + 2 * δ) := by
  rw [norm_sub_sq_real, norm_smul, real_inner_smul_right, hν, Real.norm_eq_abs, mul_one,
    sq_abs]
  have h0 := norm_nonneg x
  have h1 : ‖x‖ ^ 2 ≤ (D / 2 + η * D) ^ 2 := pow_le_pow_left₀ h0 hx 2
  have h2 := mul_le_mul_of_nonneg_left hxν hD
  nlinarith

lemma diam_dir {x y ν : Plane} {D η δ : ℝ} (hν : ‖ν‖ = 1) (hD : 0 < D) (hδ0 : 0 < δ)
    (hδ : δ ≤ 1 / 10 ^ 12) (hη0 : 0 ≤ η) (hηδ : η ≤ δ)
    (hx : ‖x‖ ≤ D / 2 + η * D) (hy : ‖y‖ ≤ D / 2 + η * D)
    (hxν : D / 2 - 2 * δ * D ≤ inner ℝ x ν) (hxy : ‖x - y‖ = D) :
    ‖(x - y) - D • ν‖ ≤ D / 100 := by
  set r := x - (D / 2) • ν with hr
  have hr2 := near_point hν hD.le hx hxν
  have hrb : ‖r‖ ≤ D / 10 ^ 5 := by
    have : D ^ 2 * (η + η ^ 2 + 2 * δ) ≤ (D / 10 ^ 5) ^ 2 := by
      have : η + η ^ 2 + 2 * δ ≤ 1 / 10 ^ 10 := by nlinarith
      nlinarith
    nlinarith [norm_nonneg r]
  set dd := x - y with hdd
  have e1 : ‖y‖ ^ 2 = ‖x‖ ^ 2 - 2 * inner ℝ x dd + ‖dd‖ ^ 2 := by
    rw [← norm_sub_sq_real, hdd, sub_sub_cancel]
  have e2 : inner ℝ x dd = (D / 2) * inner ℝ ν dd + inner ℝ r dd := by
    rw [hr, inner_sub_left, real_inner_smul_left]; ring
  have e3 : inner ℝ r dd ≤ ‖r‖ * D := by
    have := real_inner_le_norm r dd; rwa [hxy] at this
  have hxn : inner ℝ x ν ≤ ‖x‖ := by
    have := real_inner_le_norm x ν; rwa [hν, mul_one] at this
  have hp : 0 ≤ D / 2 - 2 * δ * D := by nlinarith
  have e4 : (D / 2 - 2 * δ * D) ^ 2 ≤ ‖x‖ ^ 2 := pow_le_pow_left₀ hp (hxν.trans hxn) 2
  have e5 : ‖y‖ ^ 2 ≤ (D / 2 + η * D) ^ 2 := pow_le_pow_left₀ (norm_nonneg y) hy 2
  have e6 : ‖dd - D • ν‖ ^ 2 = ‖dd‖ ^ 2 - 2 * (D * inner ℝ ν dd) + D ^ 2 := by
    rw [norm_sub_sq_real, norm_smul, real_inner_smul_right, hν, real_inner_comm,
      Real.norm_eq_abs, abs_of_pos hD]; ring
  rw [hxy] at e1 e6
  have e7 : ‖r‖ * D ≤ D / 10 ^ 5 * D := mul_le_mul_of_nonneg_right hrb hD.le
  have hfin : ‖dd - D • ν‖ ^ 2 ≤ (D / 100) ^ 2 := by
    rw [e6]
    have : η + η ^ 2 + 2 * δ ≤ 1 / 10 ^ 10 := by nlinarith
    nlinarith
  nlinarith [norm_nonneg (dd - D • ν)]

lemma halfplane_avoid {X : Finset Plane} {v w : Plane} (hs : IsCcwHullSide X v w) :
    (∀ z ∈ X, z ∉ {z | det2 (w - v) (z - v) < 0}) ∧
      ∀ p ∈ X, ∀ q ∈ X, Disjoint (segment ℝ p q) {z | det2 (w - v) (z - v) < 0} := by
  refine ⟨fun z hz h => ?_, fun p hp q hq => ?_⟩
  · have := hs.2.2.2 z hz
    simp only [mem_setOf_eq] at h
    linarith
  · rw [Set.disjoint_left]
    rintro z ⟨α, β, hα, hβ, hab, rfl⟩ h
    simp only [mem_setOf_eq] at h
    have h1 := hs.2.2.2 p hp
    have h2 := hs.2.2.2 q hq
    have e : α • p + β • q - v = α • (p - v) + β • (q - v) := by
      obtain rfl : α = 1 - β := by linarith
      module
    rw [e, det2_add_right', det2_smul_right', det2_smul_right'] at h
    nlinarith [mul_nonneg hα h1, mul_nonneg hβ h2]

lemma ball_avoid {X : Finset Plane} {O : Plane} {r : ℝ} (hball : ∀ x ∈ X, dist x O ≤ r) :
    (∀ z ∈ X, z ∉ {z | r < dist z O}) ∧
      ∀ p ∈ X, ∀ q ∈ X, Disjoint (segment ℝ p q) {z | r < dist z O} := by
  refine ⟨fun z hz h => ?_, fun p hp q hq => ?_⟩
  · simp only [mem_setOf_eq] at h
    linarith [hball z hz]
  · have hsub : segment ℝ p q ⊆ Metric.closedBall O r :=
      (convex_closedBall O r).segment_subset (Metric.mem_closedBall.2 (hball p hp))
        (Metric.mem_closedBall.2 (hball q hq))
    rw [Set.disjoint_left]
    intro z hz h
    have := Metric.mem_closedBall.1 (hsub hz)
    simp only [mem_setOf_eq] at h
    linarith

lemma seg_ray_halfplane {d v P ν : Plane} {T : ℝ} (hP : det2 d (P - v) < 0)
    (hν : det2 d ν ≤ 0) (hT : 0 ≤ T) :
    segment ℝ P (P + T • ν) ⊆ {z | det2 d (z - v) < 0} := by
  rintro z ⟨α, β, hα, hβ, hab, rfl⟩
  simp only [mem_setOf_eq]
  have e : α • P + β • (P + T • ν) - v = (P - v) + (β * T) • ν := by
    obtain rfl : α = 1 - β := by linarith
    module
  rw [e, det2_add_right', det2_smul_right']
  nlinarith [mul_nonneg hβ hT]

set_option maxHeartbeats 1600000 in
/-- **The shore of a short source track, deterministic form.** -/
theorem shore_geometry_core {X : Finset Plane} (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X)
    {O : Plane} {D η δ : ℝ} (hD : 0 < D) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 10 ^ 12) (hη0 : 0 ≤ η)
    (hηδ : η ≤ δ) (hball : ∀ x ∈ X, dist x O ≤ D / 2 + η * D)
    (hsupp : ∀ n : Plane, ‖n‖ = 1 → ∃ x ∈ X, D / 2 - δ * D ≤ inner ℝ (x - O) n)
    {e e' : Sym2 Plane} (he : e ∈ sourceEdges X) (he' : e' ∈ sourceEdges X) (hne : e ≠ e')
    (hmem : e' ∈ trackOf X e) (hlen : (srcLen X e : ℝ) + 10 ≤ δ * D) :
    ∃ S ⊆ X, S.Nonempty ∧ (∃ q ∈ X, q ∉ S) ∧ ∃ ν z : Plane, ‖ν‖ = 1 ∧ ‖z‖ = 1 ∧
      2 / 5 ≤ |inner ℝ z (rot ν)| ∧
      (∀ p ∈ S, ∀ q ∈ X, q ∉ S → dist p q = 1 → p - q = z) ∧
      (∀ p ∈ S, ‖p - (O + (D / 2) • ν)‖ ≤ D / 100) ∧
      (∀ p ∈ S, ∀ q ∈ X, q ∉ S → dist p q = D → ‖(p - q) - D • ν‖ ≤ D / 100) := by
  obtain ⟨u, k, a, w, hu, hk, hkT, hgate, hstep, hea, hea'⟩ :=
    exists_gate_chain hX htri (isTerminal_of_mem_sourceEdges hX htri he) hne hmem
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hkD : ((j + 1 : ℕ) : ℝ) + 10 ≤ δ * D := by
    have : ((j + 1 : ℕ) : ℝ) ≤ srcLen X e := by unfold srcLen; exact_mod_cast hkT
    linarith
  push_cast at hkD
  have hDbig : 10 ≤ δ * D := by
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  have hδD : δ * D ≤ D / 10 ^ 12 := by
    have := mul_le_mul_of_nonneg_right hδ hD.le; linarith
  have hηD : η * D ≤ δ * D := mul_le_mul_of_nonneg_right hηδ hD.le
  have hηD0 : 0 ≤ η * D := mul_nonneg hη0 hD.le
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have h0a := (hgate 0 (by omega)).1
  obtain ⟨N, hN⟩ : ∃ N : Plane, N = rot u := ⟨_, rfl⟩
  have hNn : ‖N‖ = 1 := by rw [hN, norm_rot, hu]
  have hun : ‖(1 / 2 : ℝ) • u‖ = 1 / 2 := by rw [norm_smul, hu]; norm_num
  have hstep' : ∀ l < j + 1, a (l + 1) = a l + w l ∧ ‖w l‖ = 1 ∧ |inner ℝ (w l) u| < 1 / 2 ∧
      0 < inner ℝ (w l) N := by rw [hN]; exact hstep
  -- the cap at `e`
  obtain ⟨hs0, hw0n, hw0u, hw0N⟩ := hstep' 0 (by omega)
  have g1 := hgate 1 (by omega)
  obtain ⟨v1, w1, C1, hs1, hC1X, hC1U, hray1, hP1, hav1, hL1⟩ :=
    source_cap hX he (Or.inl hN) hea (by rw [← hs0]; exact g1.1)
      (by rw [show a 0 + u + w 0 = a 0 + w 0 + u by abel, ← hs0]; exact g1.2) hw0n hw0u hw0N
  -- the cap at `e'`
  obtain ⟨hsj, hwjn, hwju, hwjN⟩ := hstep' j (by omega)
  have gj := hgate j (by omega)
  obtain ⟨v2, w2, C2, hs2, hC2X, hC2U, hray2, hP2, hav2, -⟩ :=
    source_cap hX he' (N := -N) (w0 := -w j) (Or.inr (by rw [hN])) hea'
      (by rw [hsj, show a j + w j + -w j = a j by abel]; exact gj.1)
      (by rw [hsj, show a j + w j + u + -w j = a j + u by abel]; exact gj.2)
      (by rw [norm_neg, hwjn]) (by rw [inner_neg_left, abs_neg]; exact hwju)
      (by rw [inner_neg_neg]; exact hwjN)
  rw [sub_neg_eq_add] at hP2
  -- the first gate midpoint
  obtain ⟨mid0, hmid0⟩ : ∃ m : Plane, m = a 0 + (1 / 2 : ℝ) • u := ⟨_, rfl⟩
  have hmv1 : ‖mid0 - v1‖ ≤ 5 / 2 := by
    rw [hmid0, show a 0 + (1 / 2 : ℝ) • u - v1 = (a 0 - v1) + (1 / 2 : ℝ) • u by abel]
    refine (norm_add_le _ _).trans ?_
    rw [← dist_eq_norm, hun]; linarith
  have hchain := chain_norm_le hstep
  have hmv2 : ‖mid0 - v2‖ ≤ j + 1 + 5 / 2 := by
    rw [hmid0, show a 0 + (1 / 2 : ℝ) • u - v2 =
      (a 0 - a (j + 1)) + ((a (j + 1) - v2) + (1 / 2 : ℝ) • u) by abel]
    refine (norm_add_le _ _).trans ?_
    have h1 := norm_add_le (a (j + 1) - v2) ((1 / 2 : ℝ) • u)
    rw [← dist_eq_norm, hun] at h1
    rw [← norm_neg, neg_sub]
    have h2 := hchain (j + 1) le_rfl
    push_cast at h2
    linarith
  have hL1p : 0 < ‖w1 - v1‖ := norm_pos_iff.2 (sub_ne_zero.2 hs1.2.2.1.symm)
  have hL2p : 0 < ‖w2 - v2‖ := norm_pos_iff.2 (sub_ne_zero.2 hs2.2.2.1.symm)
  have hf1 := side_far hs1 hsupp hmv1
  have hf2 := side_far hs2 hsupp hmv2
  -- the direction `ν`
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ‖mid0 - O‖ := ⟨_, rfl⟩
  have hMlow : D / 2 - δ * D - 5 / 2 ≤ M := by
    have h := abs_det2_le (w1 - v1) (mid0 - O)
    rw [abs_le, ← hM] at h
    have : (D / 2 - δ * D - 5 / 2) * ‖w1 - v1‖ ≤ M * ‖w1 - v1‖ := by nlinarith
    exact le_of_mul_le_mul_right this hL1p
  have hMup : M ≤ D / 2 + η * D + 1 / 2 := by
    rw [hM, hmid0, show a 0 + (1 / 2 : ℝ) • u - O = (a 0 - O) + (1 / 2 : ℝ) • u by abel]
    refine (norm_add_le _ _).trans ?_
    rw [← dist_eq_norm, hun]; linarith [hball _ h0a]
  have hMp : 0 < M := by linarith
  obtain ⟨ν, hν⟩ : ∃ ν : Plane, ν = M⁻¹ • (mid0 - O) := ⟨_, rfl⟩
  have hνn : ‖ν‖ = 1 := by
    rw [hν, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hMp, ← hM, inv_mul_cancel₀ hMp.ne']
  have hmν : inner ℝ (mid0 - O) ν = M := by
    rw [hν, real_inner_smul_right, real_inner_self_eq_norm_sq, ← hM]; field_simp
  have hdν : ∀ d : Plane, det2 d ν = M⁻¹ * det2 d (mid0 - O) := fun d => by
    rw [hν, det2_smul_right']
  have hdet1 : det2 (w1 - v1) ν ≤ 0 := by
    rw [hdν]
    have : 0 ≤ (D / 2 - δ * D - 5 / 2) * ‖w1 - v1‖ := by
      apply mul_nonneg _ hL1p.le; linarith
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 hMp.le) (by linarith)
  have hdet2 : det2 (w2 - v2) ν ≤ 0 := by
    rw [hdν]
    have : 0 ≤ (D / 2 - δ * D - (j + 1 + 5 / 2)) * ‖w2 - v2‖ := by
      apply mul_nonneg _ hL2p.le; linarith
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 hMp.le) (by linarith)
  have hlow : ∀ y : Plane, ‖y - mid0‖ ≤ j + 2 → D / 2 - 2 * δ * D ≤ inner ℝ (y - O) ν := by
    intro y hy
    have := inner_lower (O := O) hνn hy
    rw [hmν] at this
    linarith
  -- the closing points
  obtain ⟨Ps, hPs⟩ : ∃ P : Plane, P = a 0 + (1 / 2 : ℝ) • u - N := ⟨_, rfl⟩
  obtain ⟨Pe, hPe⟩ : ∃ P : Plane, P = a (j + 1) + (1 / 2 : ℝ) • u + N := ⟨_, rfl⟩
  have hPsl : D / 2 - 2 * δ * D ≤ inner ℝ (Ps - O) ν := hlow Ps (by
    rw [hPs, hmid0, show a 0 + (1 / 2 : ℝ) • u - N - (a 0 + (1 / 2 : ℝ) • u) = -N by abel,
      norm_neg, hNn]; linarith)
  have hPel : D / 2 - 2 * δ * D ≤ inner ℝ (Pe - O) ν := hlow Pe (by
    rw [hPe, hmid0, show a (j + 1) + (1 / 2 : ℝ) • u + N - (a 0 + (1 / 2 : ℝ) • u) =
      (a (j + 1) - a 0) + N by abel]
    refine (norm_add_le _ _).trans ?_
    have h2 := hchain (j + 1) le_rfl
    push_cast at h2
    rw [hNn]; linarith)
  have hQ : ∀ P : Plane, inner ℝ (P + D • ν - O) ν = inner ℝ (P - O) ν + D := by
    intro P
    rw [show P + D • ν - O = (P - O) + D • ν by abel, inner_add_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, hνn]; ring
  -- the safe region
  obtain ⟨H1, hH1⟩ : ∃ H : Set Plane, H = {z | det2 (w1 - v1) (z - v1) < 0} := ⟨_, rfl⟩
  obtain ⟨H2, hH2⟩ : ∃ H : Set Plane, H = {z | det2 (w2 - v2) (z - v2) < 0} := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : Set Plane, F = {z | D / 2 + η * D < dist z O} := ⟨_, rfl⟩
  have aH1 := halfplane_avoid hs1
  have aH2 := halfplane_avoid hs2
  have aF := ball_avoid hball
  rw [← hH1] at aH1
  rw [← hH2] at aH2
  rw [← hF] at aF
  have hSX : ∀ x ∈ X, x ∉ C1 ∪ C2 ∪ H1 ∪ H2 ∪ F := by
    intro x hx h
    rcases h with (((h | h) | h) | h) | h
    · exact hC1X x hx h
    · exact hC2X x hx h
    · exact aH1.1 x hx h
    · exact aH2.1 x hx h
    · exact aF.1 x hx h
  have hSU : ∀ p ∈ X, ∀ q ∈ X, dist p q = 1 →
      Disjoint (segment ℝ p q) (C1 ∪ C2 ∪ H1 ∪ H2 ∪ F) := by
    intro p hp q hq hpq
    simp only [Set.disjoint_union_right]
    exact ⟨⟨⟨⟨hC1U p hp q hq hpq, hC2U p hp q hq hpq⟩, aH1.2 p hp q hq⟩, aH2.2 p hp q hq⟩,
      aF.2 p hp q hq⟩
  have hstart : ∀ s : ℝ, 0 < s → s ≤ 1 → a 0 + (1 / 2 : ℝ) • u - s • N ∈
      C1 ∪ C2 ∪ H1 ∪ H2 ∪ F := by
    intro s hs0 hs1'
    rcases hray1 s hs0 hs1' with h | h
    · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
    · exact Or.inl (Or.inl (Or.inr (by rw [hH1]; exact h)))
  have hend : ∀ s : ℝ, 0 < s → s ≤ 1 → a (j + 1) + (1 / 2 : ℝ) • u + s • N ∈
      C1 ∪ C2 ∪ H1 ∪ H2 ∪ F := by
    intro s hs0 hs1'
    have h := hray2 s hs0 hs1'
    rw [smul_neg, sub_neg_eq_add] at h
    rcases h with h | h
    · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
    · exact Or.inl (Or.inr (by rw [hH2]; exact h))
  have hseg1 : segment ℝ (a (j + 1) + (1 / 2 : ℝ) • u + N) (Pe + D • ν) ⊆
      C1 ∪ C2 ∪ H1 ∪ H2 ∪ F := by
    rw [← hPe]
    intro z hz
    refine Or.inl (Or.inr ?_)
    rw [hH2]
    exact seg_ray_halfplane (by rw [hPe]; exact hP2) hdet2 hD.le hz
  have hseg3 : segment ℝ (Ps + D • ν) (a 0 + (1 / 2 : ℝ) • u - N) ⊆
      C1 ∪ C2 ∪ H1 ∪ H2 ∪ F := by
    rw [← hPs, segment_symm]
    intro z hz
    refine Or.inl (Or.inl (Or.inr ?_))
    rw [hH1]
    exact seg_ray_halfplane (by rw [hPs]; exact hP1) hdet1 hD.le hz
  have hseg2 : segment ℝ (Pe + D • ν) (Ps + D • ν) ⊆ C1 ∪ C2 ∪ H1 ∪ H2 ∪ F := by
    rintro z ⟨α, β, hα, hβ, hab, rfl⟩
    refine Or.inr ?_
    rw [hF]
    simp only [mem_setOf_eq]
    have e : α • (Pe + D • ν) + β • (Ps + D • ν) - O = α • (Pe - O) + β • (Ps - O) + D • ν := by
      obtain rfl : α = 1 - β := by linarith
      module
    have hi : inner ℝ (α • (Pe + D • ν) + β • (Ps + D • ν) - O) ν =
        α * inner ℝ (Pe - O) ν + β * inner ℝ (Ps - O) ν + D := by
      rw [e, inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
        real_inner_smul_left, real_inner_self_eq_norm_sq, hνn]; ring
    have hle := real_inner_le_norm (α • (Pe + D • ν) + β • (Ps + D • ν) - O) ν
    rw [hνn, mul_one, ← dist_eq_norm, hi] at hle
    have h1 : 0 ≤ α * inner ℝ (Pe - O) ν := mul_nonneg hα (by linarith)
    have h2 : 0 ≤ β * inner ℝ (Ps - O) ν := mul_nonneg hβ (by linarith)
    linarith
  obtain ⟨S, hS, hSne, hSq, z, hz, hunit, hloc⟩ := shore_of_crosscut hX hu (Or.inl hN) a w hgate
    hstep' (C1 ∪ C2 ∪ H1 ∪ H2 ∪ F) hSX hSU hstart hend (Pe + D • ν) (Ps + D • ν) hseg1 hseg2
    hseg3
  have hzn : ‖z‖ = 1 := by rcases hz with rfl | rfl <;> simp [hu]
  have hzu : |inner ℝ z (rot ν)| = |inner ℝ u (rot ν)| := by
    rcases hz with rfl | rfl <;> simp [inner_neg_left]
  -- location of the shore
  have hloc' : ∀ p ∈ S, D / 2 - 2 * δ * D ≤ inner ℝ (p - O) ν := by
    intro p hp
    have key : ∀ y : Plane, D / 2 - 2 * δ * D ≤ inner ℝ (y - O) ν →
        inner ℝ O ν + (D / 2 - 2 * δ * D) ≤ inner ℝ y ν := by
      intro y hy
      rw [inner_sub_left] at hy; linarith
    have h := hloc p hp ν (inner ℝ O ν + (D / 2 - 2 * δ * D))
      (key _ (by rw [← hPs]; exact hPsl)) (key _ (by rw [← hPe]; exact hPel))
      (key _ (by rw [hQ]; linarith)) (key _ (by rw [hQ]; linarith)) (fun l hl => by
        have h2 := hchain l hl
        constructor
        · refine key _ (hlow _ ?_)
          rw [hmid0, show a l + (1 / 2 : ℝ) • u - (1 / 4 : ℝ) • N - (a 0 + (1 / 2 : ℝ) • u) =
            (a l - a 0) + (-(1 / 4 : ℝ)) • N by module]
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, hNn]
          have : (l : ℝ) ≤ j + 1 := by exact_mod_cast hl
          norm_num; linarith
        · refine key _ (hlow _ ?_)
          rw [hmid0, show a l + (1 / 2 : ℝ) • u + (1 / 4 : ℝ) • N - (a 0 + (1 / 2 : ℝ) • u) =
            (a l - a 0) + (1 / 4 : ℝ) • N by module]
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, hNn]
          have : (l : ℝ) ≤ j + 1 := by exact_mod_cast hl
          norm_num; linarith)
    rw [inner_sub_left]; linarith
  have hsmall : η + η ^ 2 + 2 * δ ≤ 1 / 10 ^ 4 := by nlinarith
  refine ⟨S, hS, hSne, hSq, ν, z, hνn, hzn, ?_, hunit, ?_, ?_⟩
  · rw [hzu]
    refine two_fifths hu hνn hL1p hL1 ?_
    rw [hdν]
    have h1 : (D / 2 - δ * D - 5 / 2) ≥ (1 - 1 / 200) * M := by nlinarith
    have h2 : (1 - 1 / 200) * ‖w1 - v1‖ * M ≤ -det2 (w1 - v1) (mid0 - O) := by nlinarith
    rw [← mul_le_mul_iff_of_pos_right hMp]
    calc (1 - 1 / 200) * ‖w1 - v1‖ * M ≤ -det2 (w1 - v1) (mid0 - O) := h2
      _ = -(M⁻¹ * det2 (w1 - v1) (mid0 - O)) * M := by field_simp
  · intro p hp
    have hb : ‖p - O‖ ≤ D / 2 + η * D := by rw [← dist_eq_norm]; exact hball p (hS hp)
    have h := near_point hνn hD.le hb (hloc' p hp)
    rw [show p - O - (D / 2) • ν = p - (O + (D / 2) • ν) by abel] at h
    have : D ^ 2 * (η + η ^ 2 + 2 * δ) ≤ (D / 100) ^ 2 := by nlinarith
    nlinarith [norm_nonneg (p - (O + (D / 2) • ν))]
  · intro p hp q hq _ hpq
    have hb : ‖p - O‖ ≤ D / 2 + η * D := by rw [← dist_eq_norm]; exact hball p (hS hp)
    have hb' : ‖q - O‖ ≤ D / 2 + η * D := by rw [← dist_eq_norm]; exact hball q hq
    have h := diam_dir hνn hD hδ0 hδ hη0 hηδ hb hb' (hloc' p hp)
      (by rw [sub_sub_sub_cancel_right, ← dist_eq_norm, hpq])
    rwa [sub_sub_sub_cancel_right] at h

/-- **The shore of a short source track (asymptotic form).**  For large optimal configurations
without unit triangles, a track with fewer than `D^{19/20}` rhombi joining two distinct source
edges cuts off a shore `S` as described in `exists_shore_geometry`. -/
theorem shore_geometry_eventually : ∀ᶠ n in atTop, ∀ X, IsOptimal n X →
    ¬ HasUnitTriangle X → ∀ e ∈ sourceEdges X, ∀ e' ∈ sourceEdges X, e ≠ e' →
      (srcLen X e : ℝ) < diam X ^ (19 / 20 : ℝ) → e' ∈ trackOf X e →
      ∃ S ⊆ X, S.Nonempty ∧ (∃ q ∈ X, q ∉ S) ∧ ∃ o ν z : Plane, ‖ν‖ = 1 ∧ ‖z‖ = 1 ∧
        2 / 5 ≤ |inner ℝ z (rot ν)| ∧
        (∀ p ∈ S, ∀ q ∈ X, q ∉ S → dist p q = 1 → p - q = z) ∧
        (∀ p ∈ S, ‖p - (o + (diam X / 2) • ν)‖ ≤ diam X / 100) ∧
        (∀ p ∈ S, ∀ q ∈ X, q ∉ S → dist p q = diam X →
          ‖(p - q) - diam X • ν‖ ≤ diam X / 100) := by
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 1 / 10 ^ 12 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδ1 : δ ≤ 1 / 2 := by rw [hδ]; norm_num
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = δ ^ 2 / 100 := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hη]; positivity
  have hηδ : η ≤ δ := by rw [hη]; nlinarith
  filter_upwards [round_center_of_optimal η hη0, eventually_ge_atTop 2,
    tendsto_minDiam.eventually_ge_atTop (max (1 / η) ((2 / δ) ^ 20))] with n hO hn hD
  intro X hX htri e he e' he' hne hlen hmem
  obtain ⟨O, hball⟩ := hO X hX
  rw [← hX.diam_eq] at hD
  have hDpos : 0 < diam X := hX.diam_pos hn
  have hlat : π * diam X ^ 2 / 4 ≤ X.card * (√3 / 2) := by
    have h := minDiam_sq_le n (by omega)
    rw [← hX.diam_eq] at h
    unfold aStar at h
    rw [le_div_iff₀ Real.pi_pos] at h
    rw [hX.1.1]; linarith
  have hηD : 1 ≤ η * diam X := by
    have h := (le_max_left _ _).trans hD
    rw [div_le_iff₀ hη0] at h; linarith
  have hsupp : ∀ ν : Plane, ‖ν‖ = 1 → ∃ x ∈ X, diam X / 2 - δ * diam X ≤ inner ℝ (x - O) ν :=
    fun ν hν => exists_support_ge hX.1.2 hν hDpos hδ0 hδ1 hη.le hηD hlat hball
  -- largeness: `D^{19/20} + 10 ≤ δ D`
  have hD0 : 0 ≤ diam X := hDpos.le
  have hpow : ∀ k : ℕ, (diam X ^ (1 / 20 : ℝ)) ^ k = diam X ^ ((k : ℝ) / 20) := fun k => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hD0]; ring_nf
  set t := diam X ^ (1 / 20 : ℝ) with ht_def
  have ht20 : t ^ 20 = diam X := by rw [hpow]; norm_num
  have hL : diam X ^ (19 / 20 : ℝ) = t ^ 19 := by rw [hpow]; norm_num
  have ht : 2 / δ ≤ t := by
    have h0 : 0 ≤ 2 / δ := by positivity
    have h1 := Real.rpow_le_rpow (pow_nonneg h0 20) ((le_max_right _ _).trans hD)
      (by norm_num : (0 : ℝ) ≤ 1 / 20)
    have e : ((2 / δ) ^ 20) ^ (1 / 20 : ℝ) = 2 / δ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul h0]; norm_num
    rwa [e] at h1
  have ht10 : 10 ≤ t := by
    have : (10 : ℝ) ≤ 2 / δ := by rw [hδ]; norm_num
    linarith
  have hlen' : (srcLen X e : ℝ) + 10 ≤ δ * diam X := by
    rw [hL] at hlen
    rw [← ht20]
    have h1 : 2 ≤ δ * t := by rwa [div_le_iff₀ hδ0, mul_comm] at ht
    have h2 : t ≤ t ^ 19 := le_self_pow₀ (by linarith) (by norm_num)
    have h3 : δ * t ^ 20 = (δ * t) * t ^ 19 := by ring
    have h4 : 2 * t ^ 19 ≤ (δ * t) * t ^ 19 := mul_le_mul_of_nonneg_right h1 (by positivity)
    linarith
  obtain ⟨S, hS, hSne, hSq, ν, z, hν, hz, hzν, hunit, hloc, hdiam⟩ :=
    shore_geometry_core hX.1.2 htri hDpos hδ0 hδ.le hη0.le hηδ hball hsupp he he' hne hmem hlen'
  exact ⟨S, hS, hSne, hSq, O, ν, z, hν, hz, hzν, hunit, hloc, hdiam⟩

end Erdos99
end

end ShoreGeometry

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `ShortSources`
-/

section ShortSources

/-!
# Lemma 3.4: short sources and release

**Lemma 3.4 (Short sources and release).**  Take `L = D^{19/20}`.  All but `o(D)` unit hull sides
and all but `o(D)` two-edge hull returns have a selected track shorter than `L`.  The selected
source tracks are distinct.  None can terminate on another hull return whose length is
`B₀ = o(D)`.

We formalize it as three theorems about large optimal configurations with finite multiplicity
and without unit triangles:

* `short_unit_sources`: for every `ε > 0`, at most `ε D` unit hull sides lie on a track with at
  least `D^{19/20}` rhombi;
* `short_two_edge_sources`: for every `ε > 0`, at most `ε D` two-edge hull returns have both
  ports on tracks with at least `D^{19/20}` rhombi;
* `short_source_release`: a track with fewer than `D^{19/20}` rhombi through a source edge (a unit
  hull side or a port of a two-edge return) contains no other source edge.  In particular the
  selected short source tracks are pairwise distinct.  (The release assertion is formalized for the
  hull returns of length `B₀ ≤ 2` defined in `HullSides`.)

## Structure of the proof

The supply part follows the manuscript: clustering of long track directions (Lemma 3.3, proved
in `Clustering` from the rhombus angle-excess bound (1)) with
tolerance `D^{-1/4}` and cutoff `L`, the spread of hull directions (Lemma 3.2), the fact that a
track has at most two terminal edges (`HullSides`), and the
chord-direction estimate for two-edge returns (`Directions`).

The release part reduces, via `rotation_conditions_of_shore` and `false_of_shore_rotation`
(`RotationRelease`), to the geometry of the shore cut off by a short
track joining two sources.

The angle-excess half of equation (1), `rhombus_defect_sum`, is proved: the rhombi of a
separated set have pairwise disjoint open parallelograms inside the convex hull
(`RhombusArea`), whose total area is at most `π D² / 4` by the
isodiametric inequality (`Isodiametric`), while their number is at
least `n - O(D)`.

The crosscut (shore) construction in the proof of Lemma 3.4, `exists_shore_geometry`, is proved
in `ShoreGeometry`: the gates of the track, the caps of its two source
edges (`SourceCap`) and three long segments outside the hull form a
crosscut (`CrosscutShore`), and the outer and inner roundness of the
hull (`round_center_of_optimal`, `exists_support_ge`) locate the shore near a boundary point.

Lemma 3.2 (`hull_direction_spread`) is proved in `HullSpread`, with
error term `D^{-1/9}` in place of the manuscript's `D^{-1/4}` (which relies on Bonnesen's
inequality); the weaker rate suffices for the counting below, which therefore works at the scale
`t = D^{1/180}`.
-/

open scoped BigOperators Real
open Filter

@[expose] public noncomputable section

open Classical

namespace Erdos99

/-! ## Lemma 3.2 -/

/- The manuscript's form of Lemma 3.2 has the error term `D^{-1/4}`, which it derives from
Bonnesen's inequality (inner and outer radii `D/2 ± O(√D)`):

theorem hull_direction_spread : ∃ C : ℝ, ∀ᶠ n in atTop, ∀ X, IsOptimal n X →
    ∀ (Cs : Finset ℂ) (ρ : ℝ), 0 ≤ ρ →
      (((ccwHullSides X).filter (fun p => ∃ c ∈ Cs, ‖dir6 (p.2 - p.1) - c‖ ≤ ρ)).card : ℝ) ≤
        C * diam X * Cs.card * (ρ + diam X ^ (-(1 / 4 : ℝ)))

Bonnesen's inequality is not available here, so this statement is replaced by the version below
with error term `D^{-1/9}` (proved in `HullSpread` from the roundness
rates `D/2 + 22 D^{2/3}` and `D/2 - 100 D^{7/9}` that the project does prove).  It suffices for
Lemma 3.4: the proofs below work at the scale `t = D^{1/180}`. -/

/-- **Lemma 3.2 (spread of boundary directions).**  The number of hull sides (all of which have
length at least one) whose counterclockwise directions, taken modulo `π/3`, lie within `ρ` of
one of `M` given directions is `O(D M (ρ + D^{-1/9}))`. -/
theorem hull_direction_spread : ∃ C : ℝ, ∀ᶠ n in atTop, ∀ X, IsOptimal n X →
    ∀ (Cs : Finset ℂ) (ρ : ℝ), 0 ≤ ρ →
      (((ccwHullSides X).filter (fun p => ∃ c ∈ Cs, ‖dir6 (p.2 - p.1) - c‖ ≤ ρ)).card : ℝ) ≤
        C * diam X * Cs.card * (ρ + diam X ^ (-(1 / 9 : ℝ))) :=
  hull_direction_spread_rate

/-- **Equation (1), angle-excess part.**  `∑_Q (α_Q - π/3) = O(D)`; in terms of rhombus
defects (each at most `48 (α_Q - π/3)`), the total defect is `O(D)`. -/
theorem rhombus_defect_sum : ∃ C : ℝ, ∀ᶠ n in atTop, numOptimalClasses n < ⊤ →
    ∀ X, IsOptimal n X → ¬ HasUnitTriangle X → ∑ Q ∈ rhombi X, rhombusDefect Q ≤ C * diam X := by
  obtain ⟨C, hC⟩ := rhombi_card_ge
  refine ⟨1024 * aStar * C, ?_⟩
  filter_upwards [hC, eventually_ge_atTop 1] with n h hn hfm X hX htri
  have hq := (h hfm X hX htri).2
  have hne : X.Nonempty := by rw [← Finset.card_pos, hX.1.1]; omega
  have hs := sum_rhombusDefect_le hX.1.2 htri hne
  have hc := cDensity_mul_le hX hn
  have ha : 0 < aStar := by unfold aStar; positivity
  have hca : cDensity * aStar = π / 4 := by
    unfold cDensity aStar
    have h3 : (0:ℝ) < √3 := by positivity
    field_simp; norm_num
  have harea : π * diam X ^ 2 / 4 ≤ aStar * n := by
    have := mul_le_mul_of_nonneg_left hc ha.le
    nlinarith
  have hq' : aStar * ((n : ℝ) - C * diam X) ≤ aStar * (rhombi X).card :=
    mul_le_mul_of_nonneg_left hq ha.le
  nlinarith

/-- **The shore of a short source track (proof of Lemma 3.4, release part).**  If a track with
fewer than `D^{19/20}` rhombi joins two distinct source edges, then the spine of the track and the
paths inside its terminal caps form a crosscut of the hull; the points `S` of `X` beyond it on the
side of the shorter hull arc form a nonempty proper subset such that

* all unit pairs joining `S` to its complement, oriented into `S`, equal one unit vector `z`;
* `S` lies near one boundary point `o + (D/2) ν` of the nearly round hull (`|ν| = 1`), and every
  diameter joining `S` to its complement is close to `D ν` (errors `o(D)`, here `≤ D/100`);
* the source cap gives `|z · J ν| ≥ 2/5`.

These are the geometric facts asserted in the manuscript's proof; they are proved in
`ShoreGeometry` (`shore_geometry_eventually`). -/
theorem exists_shore_geometry : ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
    ¬ HasUnitTriangle X → ∀ e ∈ sourceEdges X, ∀ e' ∈ sourceEdges X, e ≠ e' →
      (srcLen X e : ℝ) < diam X ^ (19 / 20 : ℝ) → e' ∈ trackOf X e →
      ∃ S ⊆ X, S.Nonempty ∧ (∃ q ∈ X, q ∉ S) ∧ ∃ o ν z : Plane, ‖ν‖ = 1 ∧ ‖z‖ = 1 ∧
        2 / 5 ≤ |inner ℝ z (rot ν)| ∧
        (∀ p ∈ S, ∀ q ∈ X, q ∉ S → dist p q = 1 → p - q = z) ∧
        (∀ p ∈ S, ‖p - (o + (diam X / 2) • ν)‖ ≤ diam X / 100) ∧
        (∀ p ∈ S, ∀ q ∈ X, q ∉ S → dist p q = diam X →
          ‖(p - q) - diam X • ν‖ ≤ diam X / 100) := by
  filter_upwards [shore_geometry_eventually] with n h _ using h

/-! ## Counting lemmas -/

/-- At most two ordered pairs represent a given unordered pair. -/
lemma card_filter_mk_eq_le_two (s : Finset (Plane × Plane)) (e : Sym2 Plane) :
    (s.filter (fun p => s(p.1, p.2) = e)).card ≤ 2 := by
  induction e using Sym2.ind with
  | h x y =>
    refine (Finset.card_le_card (t := {(x, y), (y, x)}) ?_).trans Finset.card_le_two
    intro p hp
    obtain ⟨-, hp⟩ := Finset.mem_filter.1 hp
    rcases Sym2.eq_iff.1 hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp [Prod.ext_iff, h1, h2]
    · simp [Prod.ext_iff, h1, h2]

/-- A family of objects mapped to terminal edges on tracks of `Disc`, at most two-to-one,
has at most `4 |Disc|` members. -/
lemma card_le_four_mul_of_terminal {α : Type*} {X : Finset Plane} (hX : IsSeparated X)
    (htri : ¬ HasUnitTriangle X) {Disc : Finset (Finset (Sym2 Plane))} (hD : Disc ⊆ tracks X)
    (s : Finset α) (g : α → Sym2 Plane)
    (hg : ∀ a ∈ s, IsTerminal X (g a) ∧ ∃ T ∈ Disc, g a ∈ T)
    (hfib : ∀ e, (s.filter (fun a => g a = e)).card ≤ 2) : s.card ≤ 4 * Disc.card := by
  set E := Disc.biUnion (fun T => T.filter (IsTerminal X))
  have h1 : s.card ≤ 2 * E.card := by
    refine Finset.card_le_mul_card_image_of_maps_to (fun a ha => ?_) 2 (fun e _ => hfib e)
    obtain ⟨ht, T, hT, he⟩ := hg a ha
    exact Finset.mem_biUnion.2 ⟨T, hT, Finset.mem_filter.2 ⟨he, ht⟩⟩
  have h2 : E.card ≤ 2 * Disc.card := by
    refine Finset.card_biUnion_le.trans ?_
    rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun T hT => card_filter_isTerminal_le_two hX htri (hD hT)
  omega

lemma mid_unique_aux (v0 v1 w0 w1 x0 x1 y0 y1 : ℝ) (e1 : 1 = (v0 - x0) ^ 2 + (v1 - x1) ^ 2)
    (e2 : 1 = (x0 - w0) ^ 2 + (x1 - w1) ^ 2) (e3 : 1 = (v0 - y0) ^ 2 + (v1 - y1) ^ 2)
    (e4 : 1 = (y0 - w0) ^ 2 + (y1 - w1) ^ 2)
    (hdet : (w0 - v0) * (x1 - v1) - (w1 - v1) * (x0 - v0) =
      (w0 - v0) * (y1 - v1) - (w1 - v1) * (y0 - v0))
    (hn : (w0 - v0) ^ 2 + (w1 - v1) ^ 2 ≠ 0) : x0 = y0 ∧ x1 = y1 := by
  have i1 : (w0 - v0) * (x0 - y0) + (w1 - v1) * (x1 - y1) = 0 := by
    linear_combination (-1 / 2) * e1 + (1 / 2) * e2 + (1 / 2) * e3 - (1 / 2) * e4
  have i2 : (w0 - v0) * (x1 - y1) - (w1 - v1) * (x0 - y0) = 0 := by linarith
  constructor
  · have : ((w0 - v0) ^ 2 + (w1 - v1) ^ 2) * (x0 - y0) = 0 := by
      linear_combination (w0 - v0) * i1 - (w1 - v1) * i2
    have := (mul_eq_zero.1 this).resolve_left hn
    linarith
  · have : ((w0 - v0) ^ 2 + (w1 - v1) ^ 2) * (x1 - y1) = 0 := by
      linear_combination (w1 - v1) * i1 + (w0 - v0) * i2
    have := (mul_eq_zero.1 this).resolve_left hn
    linarith

/-- The middle point of a two-edge return is determined by its hull side. -/
lemma twoEdgeReturns_mid_unique {X : Finset Plane} {v x x' w : Plane}
    (h : (v, x, w) ∈ twoEdgeReturns X) (h' : (v, x', w) ∈ twoEdgeReturns X) : x = x' := by
  have H := Finset.mem_filter.1 h
  have H' := Finset.mem_filter.1 h'
  obtain ⟨hm, ⟨-, hx, -, hl⟩, h1, h2, -⟩ := H
  obtain ⟨hm', -, h1', h2', -⟩ := H'
  simp only [Finset.mem_product] at hm hm'
  have d1 := port_det_sq h1 h2
  have d2 := port_det_sq h1' h2'
  have l1 := hl x hm.2.1
  have l2 := hl x' hm'.2.1
  have hdet : det2 (w - v) (x - v) = det2 (w - v) (x' - v) := by
    have : det2 (w - v) (x - v) ^ 2 = det2 (w - v) (x' - v) ^ 2 := by linarith
    have := (sq_eq_sq₀ l1 l2).1 this
    exact this
  have e1 := dist_sq_coord v x; have e2 := dist_sq_coord x w
  have e3 := dist_sq_coord v x'; have e4 := dist_sq_coord x' w
  rw [h1] at e1; rw [h2] at e2; rw [h1'] at e3; rw [h2'] at e4
  have hvw : v ≠ w := by
    rintro rfl
    obtain ⟨-, -, hne, -⟩ := (Finset.mem_filter.1 h).2.1
    exact hne rfl
  unfold det2 at hdet
  simp only [PiLp.sub_apply] at hdet
  have hn : (w 0 - v 0) ^ 2 + (w 1 - v 1) ^ 2 ≠ 0 := by
    intro h0
    apply hvw
    have a := sq_nonneg (w 0 - v 0)
    have b := sq_nonneg (w 1 - v 1)
    have h00 : (w 0 - v 0) ^ 2 = 0 := by linarith
    have h11 : (w 1 - v 1) ^ 2 = 0 := by linarith
    rw [plane_ext_iff]
    exact ⟨(sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h00)).symm,
      (sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h11)).symm⟩
  rw [plane_ext_iff]
  have e1' : 1 = (v 0 - x 0) ^ 2 + (v 1 - x 1) ^ 2 := by linarith
  have e2' : 1 = (x 0 - w 0) ^ 2 + (x 1 - w 1) ^ 2 := by linarith
  have e3' : 1 = (v 0 - x' 0) ^ 2 + (v 1 - x' 1) ^ 2 := by linarith
  have e4' : 1 = (x' 0 - w 0) ^ 2 + (x' 1 - w 1) ^ 2 := by linarith
  exact mid_unique_aux (v 0) (v 1) (w 0) (w 1) (x 0) (x 1) (x' 0) (x' 1) e1' e2' e3' e4' hdet hn

lemma twoEdgeReturns_side {X : Finset Plane} {t : Plane × Plane × Plane}
    (h : t ∈ twoEdgeReturns X) : IsCcwHullSide X t.1 t.2.2 := (Finset.mem_filter.1 h).2.1

/-- Each edge is the first port of at most two two-edge returns. -/
lemma card_filter_port1_le_two (X : Finset Plane) (e : Sym2 Plane) :
    ((twoEdgeReturns X).filter (fun t => s(t.1, t.2.1) = e)).card ≤ 2 := by
  refine (Finset.card_le_card_of_injOn (fun t => (t.1, t.2.1))
    (t := ((twoEdgeReturns X).image (fun t => (t.1, t.2.1))).filter
      (fun p => s(p.1, p.2) = e)) ?_ ?_).trans (card_filter_mk_eq_le_two _ e)
  · intro t ht
    obtain ⟨ht, he⟩ := Finset.mem_filter.1 ht
    exact Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ ht, he⟩
  · intro t ht t' ht' heq
    obtain ⟨ht, -⟩ := Finset.mem_filter.1 ht
    obtain ⟨ht', -⟩ := Finset.mem_filter.1 ht'
    simp only [Prod.mk.injEq] at heq
    obtain ⟨h1, h2⟩ := heq
    have hs := twoEdgeReturns_side ht
    have hs' := twoEdgeReturns_side ht'
    rw [h1] at hs
    have h3 := hs.succ_unique hs'
    exact Prod.ext h1 (Prod.ext h2 h3)

/-- Each edge is the second port of at most two two-edge returns. -/
lemma card_filter_port2_le_two (X : Finset Plane) (e : Sym2 Plane) :
    ((twoEdgeReturns X).filter (fun t => s(t.2.1, t.2.2) = e)).card ≤ 2 := by
  refine (Finset.card_le_card_of_injOn (fun t => (t.2.1, t.2.2))
    (t := ((twoEdgeReturns X).image (fun t => (t.2.1, t.2.2))).filter
      (fun p => s(p.1, p.2) = e)) ?_ ?_).trans (card_filter_mk_eq_le_two _ e)
  · intro t ht
    obtain ⟨ht, he⟩ := Finset.mem_filter.1 ht
    exact Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ ht, he⟩
  · intro t ht t' ht' heq
    obtain ⟨ht, -⟩ := Finset.mem_filter.1 ht
    obtain ⟨ht', -⟩ := Finset.mem_filter.1 ht'
    simp only [Prod.mk.injEq] at heq
    obtain ⟨h1, h2⟩ := heq
    have hs := twoEdgeReturns_side ht
    have hs' := twoEdgeReturns_side ht'
    rw [h2] at hs
    have h3 := hs.pred_unique hs'
    exact Prod.ext h3 (Prod.ext h1 h2)

/-! ## Directions of source tracks -/

lemma dir6_dv_mk' (x y : Plane) : dir6 (dv s(x, y)) = dir6 (y - x) := by
  rw [dir6_dv_mk, ← neg_sub, dir6_neg]

/-- A long source track: its edge lies on it, it is a track, and its direction is the edge's. -/
lemma long_track_facts {X : Finset Plane} {x y : Plane} (h : 0 < srcLen X s(x, y)) :
    trackOf X s(x, y) ∈ tracks X ∧ s(x, y) ∈ trackOf X s(x, y) ∧
      tdir (trackOf X s(x, y)) = dir6 (y - x) := by
  have he := mem_rhombusEdges_of_srcLen_pos h
  have hT := trackOf_mem_tracks he
  have hm := mem_trackOf_self he
  exact ⟨hT, hm, by rw [tdir_eq hT hm, dir6_dv_mk']⟩

/-! ## Asymptotic bookkeeping -/

lemma poly_small {M ε t : ℝ} (hε : 0 < ε) (ht1 : 1 ≤ t) (ht : M / ε ≤ t) {a : ℕ}
    (ha : a ≤ 179) : M * t ^ a ≤ ε * t ^ 180 := by
  have h1 : t ^ a ≤ t ^ 179 := pow_le_pow_right₀ ht1 ha
  have h2 : M ≤ ε * t := by rwa [div_le_iff₀ hε, mul_comm] at ht
  have h3 : 0 ≤ t ^ a := by positivity
  rcases le_or_gt M 0 with hM | hM
  · have : M * t ^ a ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hM h3
    have : 0 ≤ ε * t ^ 180 := by positivity
    linarith
  · calc M * t ^ a ≤ (ε * t) * t ^ 179 := mul_le_mul h2 h1 h3 (by positivity)
      _ = ε * t ^ 180 := by ring

/-- Powers of `t = D^{1/180}`. -/
lemma rpow_frac180 {D : ℝ} (hD : 0 ≤ D) (k : ℕ) :
    (D ^ (1 / 180 : ℝ)) ^ k = D ^ ((k : ℝ) / 180) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hD]; ring_nf

/-- The common setup: positive constants and the eventual largeness of `t = D^{1/180}`. -/
lemma eventually_t_large (t0 : ℝ) :
    ∀ᶠ n in atTop, ∀ X, IsOptimal n X → t0 ≤ diam X ^ (1 / 180 : ℝ) := by
  filter_upwards [tendsto_minDiam.eventually_ge_atTop (max t0 0 ^ 180)] with n hn X hX
  rw [← hX.diam_eq] at hn
  have h0 : 0 ≤ max t0 0 := le_max_right _ _
  have h1 := Real.rpow_le_rpow (pow_nonneg h0 180) hn (by norm_num : (0 : ℝ) ≤ 1 / 180)
  have e : (max t0 0 ^ 180) ^ (1 / 180 : ℝ) = max t0 0 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h0]; norm_num
  rw [e] at h1
  exact (le_max_left _ _).trans h1

/-! ## Lemma 3.4 -/

/-- The data provided by clustering at cutoff `L = t^171 = D^{19/20}` and tolerance
`t^{-45} = D^{-1/4}`, with `t = D^{1/180}`. -/
lemma clustering_at_scale {X : Finset Plane} (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X)
    {C1 C2 t : ℝ} (ht : 1 ≤ t) (hdef : ∑ Q ∈ rhombi X, rhombusDefect Q ≤ C1 * t ^ 180)
    (hs : ((tracks X).card : ℝ) ≤ C2 * t ^ 180) :
    ∃ Disc ⊆ tracks X, ∃ Cs : Finset ℂ, (∀ c ∈ Cs, ‖c‖ = 1) ∧
      (Disc.card : ℝ) ≤ 4 * C1 * t ^ 54 ∧ (Cs.card : ℝ) ≤ 2 * C2 * t ^ 9 ∧
      ∀ T ∈ tracks X, T ∉ Disc → t ^ 171 ≤ trackLength X T →
        ∃ c ∈ Cs, ‖tdir T - c‖ ≤ 2 * (t ^ 45)⁻¹ := by
  have ht0 : 0 < t := by linarith
  obtain ⟨Disc, hDsub, Cs, hCs1, hDcard, hCcard, hcov⟩ :=
    track_clustering hX htri (ε := (t ^ 45)⁻¹) (L := t ^ 171) (by positivity) (by positivity) hdef
  refine ⟨Disc, hDsub, Cs, hCs1, ?_, ?_, hcov⟩
  · have e : (t ^ 45)⁻¹ * t ^ 171 = t ^ 126 := by field_simp
    rw [e] at hDcard
    have h126 : 0 < t ^ 126 := by positivity
    rw [← mul_le_mul_iff_of_pos_right h126]
    calc (Disc.card : ℝ) * t ^ 126 ≤ 4 * (C1 * t ^ 180) := hDcard
      _ = 4 * C1 * t ^ 54 * t ^ 126 := by ring
  · have h171 : 0 < t ^ 171 := by positivity
    rw [← mul_le_mul_iff_of_pos_right h171]
    calc (Cs.card : ℝ) * t ^ 171 ≤ 2 * (tracks X).card := hCcard
      _ ≤ 2 * (C2 * t ^ 180) := by linarith
      _ = 2 * C2 * t ^ 9 * t ^ 171 := by ring

/-- **Lemma 3.4, short sources, unit hull sides.**  For every `ε > 0`, eventually at most `ε D`
unit hull sides lie on tracks with at least `D^{19/20}` rhombi. -/
theorem short_unit_sources (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      (((unitHullSides X).filter
        (fun p => diam X ^ (19 / 20 : ℝ) ≤ srcLen X s(p.1, p.2))).card : ℝ) ≤ ε * diam X := by
  obtain ⟨C1', hC1⟩ := rhombus_defect_sum
  obtain ⟨C2', hC2⟩ := tracks_card_le
  obtain ⟨C3', hC3⟩ := hull_direction_spread
  set C1 := max C1' 1
  set C2 := max C2' 1
  set C3 := max C3' 1
  set M := 16 * C1 + 6 * C2 * C3
  filter_upwards [hC1, hC2, hC3, eventually_t_large (max 1 (M / ε))] with n h1 h2 h3 h4
  intro hfm X hX htri
  set D := diam X
  set t := D ^ (1 / 180 : ℝ)
  have ht : max 1 (M / ε) ≤ t := h4 X hX
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
  have hD0 : 0 ≤ D := Metric.diam_nonneg
  have ht20 : t ^ 180 = D := by rw [rpow_frac180 hD0]; norm_num
  have hL : D ^ (19 / 20 : ℝ) = t ^ 171 := by rw [rpow_frac180 hD0]; norm_num
  have hε' : D ^ (-(1 / 9 : ℝ)) = (t ^ 20)⁻¹ := by
    rw [Real.rpow_neg hD0, rpow_frac180 hD0]; norm_num
  have hsep := hX.1.2
  -- the inputs, with positive constants
  have hdef : ∑ Q ∈ rhombi X, rhombusDefect Q ≤ C1 * t ^ 180 := by
    rw [ht20]; exact (h1 hfm X hX htri).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hD0)
  have hs : ((tracks X).card : ℝ) ≤ C2 * t ^ 180 := by
    rw [ht20]; exact (h2 hfm X hX htri).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hD0)
  obtain ⟨Disc, hDsub, Cs, -, hDcard, hCcard, hcov⟩ :=
    clustering_at_scale hsep htri ht1 hdef hs
  set A := (unitHullSides X).filter (fun p => D ^ (19 / 20 : ℝ) ≤ srcLen X s(p.1, p.2))
  set A1 := A.filter (fun p => trackOf X s(p.1, p.2) ∈ Disc)
  set A2 := A.filter (fun p => trackOf X s(p.1, p.2) ∉ Disc)
  have hsplit : A.card = A1.card + A2.card := (Finset.card_filter_add_card_filter_not _).symm
  have hpos : ∀ p ∈ A, 0 < srcLen X s(p.1, p.2) := by
    intro p hp
    have := (Finset.mem_filter.1 hp).2
    rw [hL] at this
    have h' : (0 : ℝ) < srcLen X s(p.1, p.2) := lt_of_lt_of_le (by positivity) this
    exact_mod_cast h'
  -- sources on discarded tracks
  have hA1 : A1.card ≤ 4 * Disc.card := by
    refine card_le_four_mul_of_terminal hsep htri hDsub A1 (fun p => s(p.1, p.2)) ?_ ?_
    · intro p hp
      obtain ⟨hpA, hpD⟩ := Finset.mem_filter.1 hp
      obtain ⟨-, hm, -⟩ := long_track_facts (hpos p hpA)
      exact ⟨isTerminal_of_mem_unitHullSides hsep htri (Finset.mem_filter.1 hpA).1, _, hpD, hm⟩
    · intro e; exact card_filter_mk_eq_le_two _ e
  -- sources on clustered tracks
  have hA2 : (A2.card : ℝ) ≤ C3 * D * Cs.card * (2 * (t ^ 45)⁻¹ + D ^ (-(1 / 9 : ℝ))) := by
    refine le_trans ?_ ((h3 X hX Cs (2 * (t ^ 45)⁻¹) (by positivity)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hD0) (by positivity))
        (by rw [hε']; positivity)))
    norm_cast
    refine Finset.card_le_card fun p hp => ?_
    obtain ⟨hpA, hpD⟩ := Finset.mem_filter.1 hp
    obtain ⟨hpU, hlong⟩ := Finset.mem_filter.1 hpA
    obtain ⟨hT, -, hdir⟩ := long_track_facts (hpos p hpA)
    rw [hL] at hlong
    obtain ⟨c, hc, hcl⟩ := hcov _ hT hpD hlong
    rw [hdir] at hcl
    exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hpU).1, c, hc, hcl⟩
  rw [hε'] at hA2
  have hA2' : (A2.card : ℝ) ≤ 6 * C2 * C3 * t ^ 169 := by
    have hC3 : 0 ≤ C3 := le_trans zero_le_one (le_max_right _ _)
    have e : C3 * D * Cs.card * (2 * (t ^ 45)⁻¹ + (t ^ 20)⁻¹) =
        C3 * Cs.card * (2 * t ^ 135 + t ^ 160) := by
      rw [← ht20]; field_simp
    have h135 : t ^ 135 ≤ t ^ 160 := pow_le_pow_right₀ ht1 (by norm_num)
    rw [e] at hA2
    calc (A2.card : ℝ) ≤ C3 * Cs.card * (2 * t ^ 135 + t ^ 160) := hA2
      _ ≤ C3 * (2 * C2 * t ^ 9) * (3 * t ^ 160) := by gcongr; linarith
      _ = 6 * C2 * C3 * t ^ 169 := by ring
  have hA1' : (A1.card : ℝ) ≤ 16 * C1 * t ^ 54 := by
    have : (A1.card : ℝ) ≤ 4 * Disc.card := by exact_mod_cast hA1
    linarith
  have hsum : (A.card : ℝ) ≤ M * t ^ 169 := by
    have : (A.card : ℝ) = A1.card + A2.card := by exact_mod_cast hsplit
    have h616 : t ^ 54 ≤ t ^ 169 := pow_le_pow_right₀ ht1 (by norm_num)
    have hC1 : 0 ≤ C1 := le_trans zero_le_one (le_max_right _ _)
    have : 16 * C1 * t ^ 54 ≤ 16 * C1 * t ^ 169 := by gcongr
    simp only [M]; nlinarith
  have := poly_small hε ht1 ((le_max_right _ _).trans ht) (M := M) (a := 169) (by norm_num)
  rw [ht20] at this
  linarith


/-- The square roots used for chord directions. -/
def chordCentres (Cs : Finset ℂ) : Finset ℂ :=
  (Cs ×ˢ Cs).image (fun p => sqrtC (p.1 * p.2)) ∪ (Cs ×ˢ Cs).image (fun p => -sqrtC (p.1 * p.2))

lemma card_chordCentres_le (Cs : Finset ℂ) : (chordCentres Cs).card ≤ 2 * Cs.card ^ 2 := by
  unfold chordCentres
  refine (Finset.card_union_le _ _).trans ?_
  have h1 := Finset.card_image_le (s := Cs ×ˢ Cs) (f := fun p => sqrtC (p.1 * p.2))
  have h2 := Finset.card_image_le (s := Cs ×ˢ Cs) (f := fun p => -sqrtC (p.1 * p.2))
  rw [Finset.card_product] at h1 h2
  nlinarith

/-- **Lemma 3.4, short sources, two-edge returns.**  For every `ε > 0`, eventually at most `ε D`
two-edge hull returns have both ports on tracks with at least `D^{19/20}` rhombi. -/
theorem short_two_edge_sources (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      (((twoEdgeReturns X).filter (fun t => diam X ^ (19 / 20 : ℝ) ≤ srcLen X s(t.1, t.2.1) ∧
        diam X ^ (19 / 20 : ℝ) ≤ srcLen X s(t.2.1, t.2.2))).card : ℝ) ≤ ε * diam X := by
  obtain ⟨C1', hC1⟩ := rhombus_defect_sum
  obtain ⟨C2', hC2⟩ := tracks_card_le
  obtain ⟨C3', hC3⟩ := hull_direction_spread
  set C1 := max C1' 1
  set C2 := max C2' 1
  set C3 := max C3' 1
  set M := 32 * C1 + 40 * C2 ^ 2 * C3
  filter_upwards [hC1, hC2, hC3, eventually_t_large (max 1 (M / ε))] with n h1 h2 h3 h4
  intro hfm X hX htri
  set D := diam X
  set t := D ^ (1 / 180 : ℝ)
  have ht : max 1 (M / ε) ≤ t := h4 X hX
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
  have hD0 : 0 ≤ D := Metric.diam_nonneg
  have ht20 : t ^ 180 = D := by rw [rpow_frac180 hD0]; norm_num
  have hL : D ^ (19 / 20 : ℝ) = t ^ 171 := by rw [rpow_frac180 hD0]; norm_num
  have hε' : D ^ (-(1 / 9 : ℝ)) = (t ^ 20)⁻¹ := by
    rw [Real.rpow_neg hD0, rpow_frac180 hD0]; norm_num
  have hsep := hX.1.2
  have hC1p : 0 ≤ C1 := le_trans zero_le_one (le_max_right _ _)
  have hC2p : 0 ≤ C2 := le_trans zero_le_one (le_max_right _ _)
  have hC3p : 0 ≤ C3 := le_trans zero_le_one (le_max_right _ _)
  have hdef : ∑ Q ∈ rhombi X, rhombusDefect Q ≤ C1 * t ^ 180 := by
    rw [ht20]; exact (h1 hfm X hX htri).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hD0)
  have hs : ((tracks X).card : ℝ) ≤ C2 * t ^ 180 := by
    rw [ht20]; exact (h2 hfm X hX htri).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hD0)
  obtain ⟨Disc, hDsub, Cs, hCs1, hDcard, hCcard, hcov⟩ :=
    clustering_at_scale hsep htri ht1 hdef hs
  set B := (twoEdgeReturns X).filter (fun t => D ^ (19 / 20 : ℝ) ≤ srcLen X s(t.1, t.2.1) ∧
    D ^ (19 / 20 : ℝ) ≤ srcLen X s(t.2.1, t.2.2))
  have hpos : ∀ r ∈ B, 0 < srcLen X s(r.1, r.2.1) ∧ 0 < srcLen X s(r.2.1, r.2.2) := by
    intro r hr
    obtain ⟨-, l1, l2⟩ := Finset.mem_filter.1 hr
    rw [hL] at l1 l2
    have p1 : (0 : ℝ) < srcLen X s(r.1, r.2.1) := lt_of_lt_of_le (by positivity) l1
    have p2 : (0 : ℝ) < srcLen X s(r.2.1, r.2.2) := lt_of_lt_of_le (by positivity) l2
    exact ⟨by exact_mod_cast p1, by exact_mod_cast p2⟩
  have hBsub : B ⊆ twoEdgeReturns X := Finset.filter_subset _ _
  set B1 := B.filter (fun r => trackOf X s(r.1, r.2.1) ∈ Disc)
  set B' := B.filter (fun r => trackOf X s(r.1, r.2.1) ∉ Disc)
  set B2 := B'.filter (fun r => trackOf X s(r.2.1, r.2.2) ∈ Disc)
  set B3 := B'.filter (fun r => trackOf X s(r.2.1, r.2.2) ∉ Disc)
  have hs1 : B.card = B1.card + B'.card := (Finset.card_filter_add_card_filter_not _).symm
  have hs2 : B'.card = B2.card + B3.card := (Finset.card_filter_add_card_filter_not _).symm
  have hB1 : B1.card ≤ 4 * Disc.card := by
    refine card_le_four_mul_of_terminal hsep htri hDsub B1 (fun r => s(r.1, r.2.1)) ?_ ?_
    · intro r hr
      obtain ⟨hrB, hrD⟩ := Finset.mem_filter.1 hr
      obtain ⟨-, hm, -⟩ := long_track_facts (hpos r hrB).1
      exact ⟨(isTerminal_of_mem_twoEdgeReturns hsep htri (hBsub hrB)).1, _, hrD, hm⟩
    · intro e
      exact (Finset.card_le_card (Finset.filter_subset_filter _
        ((Finset.filter_subset _ _).trans hBsub))).trans (card_filter_port1_le_two X e)
  have hB2 : B2.card ≤ 4 * Disc.card := by
    refine card_le_four_mul_of_terminal hsep htri hDsub B2 (fun r => s(r.2.1, r.2.2)) ?_ ?_
    · intro r hr
      obtain ⟨hrB', hrD⟩ := Finset.mem_filter.1 hr
      have hrB := (Finset.mem_filter.1 hrB').1
      obtain ⟨-, hm, -⟩ := long_track_facts (hpos r hrB).2
      exact ⟨(isTerminal_of_mem_twoEdgeReturns hsep htri (hBsub hrB)).2, _, hrD, hm⟩
    · intro e
      refine (Finset.card_le_card (Finset.filter_subset_filter _ ?_)).trans
        (card_filter_port2_le_two X e)
      exact (Finset.filter_subset _ _).trans ((Finset.filter_subset _ _).trans hBsub)
  -- both ports on clustered tracks: the chord direction is clustered
  set ρ := 4 * (t ^ 45)⁻¹
  have hB3 : (B3.card : ℝ) ≤ C3 * D * (chordCentres Cs).card * (ρ + D ^ (-(1 / 9 : ℝ))) := by
    refine le_trans ?_ ((h3 X hX (chordCentres Cs) ρ (by positivity)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hD0) (by positivity))
        (by rw [hε']; positivity)))
    norm_cast
    refine Finset.card_le_card_of_injOn (fun r => (r.1, r.2.2)) ?_ ?_
    · intro r hr
      obtain ⟨hrB', hD2⟩ := Finset.mem_filter.1 hr
      obtain ⟨hrB, hD1⟩ := Finset.mem_filter.1 hrB'
      obtain ⟨hrR, l1, l2⟩ := Finset.mem_filter.1 hrB
      obtain ⟨hm, hside, d1, d2, d3⟩ := Finset.mem_filter.1 hrR
      simp only [Finset.mem_product] at hm
      obtain ⟨hT1, -, hdir1⟩ := long_track_facts (hpos r hrB).1
      obtain ⟨hT2, -, hdir2⟩ := long_track_facts (hpos r hrB).2
      rw [hL] at l1 l2
      obtain ⟨c1, hc1, hcl1⟩ := hcov _ hT1 hD1 l1
      obtain ⟨c2, hc2, hcl2⟩ := hcov _ hT2 hD2 l2
      rw [hdir1] at hcl1
      rw [hdir2] at hcl2
      have n1 : ‖r.2.1 - r.1‖ = 1 := by rw [← dist_eq_norm, dist_comm]; exact d1
      have n2 : ‖r.2.2 - r.2.1‖ = 1 := by rw [← dist_eq_norm, dist_comm]; exact d2
      have hsum : (r.2.1 - r.1) + (r.2.2 - r.2.1) = r.2.2 - r.1 := by abel
      have hne : (r.2.1 - r.1) + (r.2.2 - r.2.1) ≠ 0 := by
        rw [hsum]; exact sub_ne_zero.2 hside.2.2.1.symm
      have key := dir6_chord n1 n2 hne (hCs1 c1 hc1) (hCs1 c2 hc2) hcl1 hcl2
      rw [hsum] at key
      refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hm.1, hm.2.2⟩,
        hside⟩, ?_⟩
      simp only
      rcases key with k | k
      · exact ⟨_, Finset.mem_union_left _ (Finset.mem_image.2 ⟨(c1, c2),
          Finset.mem_product.2 ⟨hc1, hc2⟩, rfl⟩), by simp only [ρ]; linarith⟩
      · exact ⟨_, Finset.mem_union_right _ (Finset.mem_image.2 ⟨(c1, c2),
          Finset.mem_product.2 ⟨hc1, hc2⟩, rfl⟩), by simp only [ρ]; linarith⟩
    · intro r hr r' hr' heq
      simp only [Prod.mk.injEq] at heq
      have m1 := hBsub (Finset.mem_filter.1 (Finset.mem_filter.1 hr).1).1
      have m2 := hBsub (Finset.mem_filter.1 (Finset.mem_filter.1 hr').1).1
      obtain ⟨a, b, c⟩ := r
      obtain ⟨a', b', c'⟩ := r'
      simp only at heq m1 m2 ⊢
      obtain ⟨rfl, rfl⟩ := heq
      rw [twoEdgeReturns_mid_unique m1 m2]
  rw [hε'] at hB3
  have hB3' : (B3.card : ℝ) ≤ 40 * C2 ^ 2 * C3 * t ^ 178 := by
    have e : C3 * D * (chordCentres Cs).card * (ρ + (t ^ 20)⁻¹) =
        C3 * (chordCentres Cs).card * (4 * t ^ 135 + t ^ 160) := by
      simp only [ρ]; rw [← ht20]; field_simp
    have h135 : t ^ 135 ≤ t ^ 160 := pow_le_pow_right₀ ht1 (by norm_num)
    rw [e] at hB3
    have hcc : ((chordCentres Cs).card : ℝ) ≤ 2 * (Cs.card : ℝ) ^ 2 := by
      exact_mod_cast card_chordCentres_le Cs
    have hCs0 : (0 : ℝ) ≤ Cs.card := by positivity
    have hsq : (Cs.card : ℝ) ^ 2 ≤ (2 * C2 * t ^ 9) ^ 2 := pow_le_pow_left₀ hCs0 hCcard 2
    calc (B3.card : ℝ) ≤ C3 * (chordCentres Cs).card * (4 * t ^ 135 + t ^ 160) := hB3
      _ ≤ C3 * (2 * (2 * C2 * t ^ 9) ^ 2) * (5 * t ^ 160) := by gcongr <;> linarith
      _ = 40 * C2 ^ 2 * C3 * t ^ 178 := by ring
  have hDc : (Disc.card : ℝ) ≤ 4 * C1 * t ^ 54 := hDcard
  have hsum : (B.card : ℝ) ≤ M * t ^ 178 := by
    have e1 : (B.card : ℝ) = B1.card + B2.card + B3.card := by
      have := hs1; rw [hs2] at this; push_cast [this]; ring
    have b1 : (B1.card : ℝ) ≤ 4 * Disc.card := by exact_mod_cast hB1
    have b2 : (B2.card : ℝ) ≤ 4 * Disc.card := by exact_mod_cast hB2
    have h617 : t ^ 54 ≤ t ^ 178 := pow_le_pow_right₀ ht1 (by norm_num)
    have : 32 * C1 * t ^ 54 ≤ 32 * C1 * t ^ 178 := by gcongr
    simp only [M]; nlinarith
  have := poly_small hε ht1 ((le_max_right _ _).trans ht) (M := M) (a := 178) (by norm_num)
  rw [ht20] at this
  linarith

/-- **Lemma 3.4, release.**  Eventually, a track with fewer than `D^{19/20}` rhombi through a
source edge (a unit hull side or a port of a two-edge return) contains no other source edge.  In
particular the selected short source tracks are pairwise distinct. -/
theorem short_source_release :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ e ∈ sourceEdges X, ∀ e' ∈ sourceEdges X, e ≠ e' →
        (srcLen X e : ℝ) < diam X ^ (19 / 20 : ℝ) → e' ∉ trackOf X e := by
  filter_upwards [exists_shore_geometry, eventually_ge_atTop 2] with n hsh hn
  intro hfm X hX htri e he e' he' hne hlen hmem
  obtain ⟨S, hS, hne, hpr, o, ν, z, hν, hz, hzτ, hunit, hloc, hdiam⟩ :=
    hsh hfm X hX htri e he e' he' hne hlen hmem
  obtain ⟨a, ω, h1, h2, h3, p, hp, hω, hpa⟩ :=
    rotation_conditions_of_shore (hX.diam_pos hn) hν hz hzτ hunit hloc hdiam hne
  exact false_of_shore_rotation hn hfm hX S a ω h1 h2 h3 ⟨p, hp, hS hp, hω, hpa⟩ hpr

end Erdos99
end

end ShortSources
