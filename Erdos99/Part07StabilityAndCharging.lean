module

public import Mathlib
public import Erdos99.Part03LiftedFanAndDensity
public import Erdos99.Part04RoundnessAndConnectivity
public import Erdos99.Part05FacesAndShores
public import Erdos99.Part06TokensHopsCaps

/-!
# Erdős Problem 99 under finite multiplicity — Part 7 of 9: Stability, the charging graph and pinned polynomials

This is one of the supporting files of the formalization; the main theorem and a precise
description of what is proved are at the top of `Erdos99.lean`.

The file is divided into the following sections (each `section Name … end Name`); comments
elsewhere in the development refer to these sections by name.

* `HopEmission`
* `HopEmissionMain`
* `Stability`
* `DegreeDefect`
* `LocalCharge`
* `BoundaryPortBounds`
* `ChargingGraph`
* `HalfEdgeGraph`
* `TrackChargingGraph`
* `TrackCapBounds`
* `DirectionPinning`
* `PinnedCount`
* `QuadraticResponseH1`
* `QuadraticResponseJ`
* `PinnedPolys`
* `ReturnBudgets`
-/

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `HopEmission`
-/

section HopEmission

/-!
# The emissions of the track-following process (Verification Guide §9.1–§9.3)

This file supplies the ingredients of the emission lemma `exists_hopEmission` of `Stability`
for the track-following process `hopProcess` (`HopProcess`).

* `leftStep_of_oppositeSides`: a rhombus on a unit edge lies on one of its two sides.
* `isTerminal_of_mem_orientedSides`: a side of an exceptional face carries at most one rhombus.
* `hopEmit X`: **the choice of exit edges.**  Each exceptional face `G` emits through the reversal
  of the oriented side of `G` whose reversed direction is closest to the *reference tangent*
  `tangentRef X G`, the direction of the unit hull side nearest to `G`.
  `hopEmit_mem`, `hopEmit_min`: the exit edge is the reversal of an oriented side, minimizing the
  distance to the reference tangent.
* `emission_step`: one emission (§9.1, §8.2): the exit edge of an emitting pentagon or heptagon is
  nearly parallel to the labels of its inputs.
* `errB`, `disB`, `cutB`, `eventually_schedule`: the schedule of angle errors and displacements
  along the scales `Λ_j` (§9.2).
-/

open scoped BigOperators Real
open Filter Topology EstablishedExternalResults

@[expose] public noncomputable section

open Classical

namespace Erdos99

open Propagation

/-! ## Terminal sides of exceptional faces -/

section
variable {X : Finset Plane} (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X)
include hX htri

omit hX htri in
/-- Two parallel unit vectors are equal or opposite. -/
lemma eq_or_eq_neg_of_det2_eq_zero {u w : Plane} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (h : det2 u w = 0) : w = u ∨ w = -u := by
  have e1 := inner_sq_add_inner_rot_sq u w
  rw [hu, hw, inner_rot_eq_det2, h] at e1
  have hi : inner ℝ w u = 1 ∨ inner ℝ w u = -1 := by
    have : (inner ℝ w u - 1) * (inner ℝ w u + 1) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h | h
    · left; linarith
    · right; linarith
  rcases hi with hi | hi
  · left
    have : ‖w - u‖ ^ 2 = 0 := by
      rw [norm_sub_sq_real, hu, hw, hi]; norm_num
    exact sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this))
  · right
    have : ‖w + u‖ ^ 2 = 0 := by
      rw [norm_add_sq_real, hu, hw, hi]; norm_num
    exact eq_neg_of_add_eq_zero_left (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this))

omit hX htri in
/-- A rhombus `a b c d` lies on the left or on the right of its side `a b`. -/
lemma leftStep_of_rhombus {a b c d : Plane} (hR : ({a, b, c, d} : Finset Plane) ∈ rhombi X)
    (hab : dist a b = 1) (hbc : dist b c = 1) (hcd : dist c d = 1) (hda : dist d a = 1)
    (hpara : a + c = b + d) (hbd : b ≠ d) (hac : a ≠ c) :
    ∃ q : Plane × Plane, (LeftStep X (a, b) q ∨ LeftStep X (b, a) q) ∧ s(q.1, q.2) = s(c, d) := by
  have hcd' : c - d = b - a := by
    have : c = b + d - a := by rw [← hpara]; abel
    rw [this]; abel
  rcases lt_trichotomy (det2 (b - a) (d - a)) 0 with hneg | hzero | hpos
  · refine ⟨(c, d), Or.inr ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
    · have : ({b, a, d, c} : Finset Plane) = {a, b, c, d} := by
        ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
      simpa [this] using hR
    · simpa [dist_comm] using hab
    · simpa [dist_comm] using hda
    · simpa [dist_comm] using hcd
    · simpa [dist_comm] using hbc
    · show d - c = a - b
      rw [← neg_sub c d, hcd', neg_sub]
    · show 0 < det2 (a - b) (c - b)
      have e1 : a - b = -(b - a) := by abel
      have e2 : c - b = d - a := by
        have : c = b + d - a := by rw [← hpara]; abel
        rw [this]; abel
      rw [e1, e2, det2_neg_left]; linarith
  · exfalso
    have hu : ‖b - a‖ = 1 := by rw [← dist_eq_norm, dist_comm]; exact hab
    have hw : ‖d - a‖ = 1 := by rw [← dist_eq_norm]; exact hda
    rcases eq_or_eq_neg_of_det2_eq_zero hu hw hzero with h | h
    · exact hbd (by have := congrArg (· + a) h; simpa using this.symm)
    · apply hac
      have hc : c = b + d - a := by rw [← hpara]; abel
      have hd : d = a - (b - a) := by
        have := congrArg (· + a) h; simp only [sub_add_cancel] at this
        rw [this]; abel
      rw [hc, hd]; abel
  · refine ⟨(d, c), Or.inl ⟨?_, hab, hbc, hcd, hda, hcd', hpos⟩, Sym2.eq_swap⟩
    have : ({a, b, c, d} : Finset Plane) = {a, b, c, d} := rfl
    simpa using hR

/-- **A rhombus on a unit edge lies on one of its sides.** -/
lemma leftStep_of_oppositeSides {a b : Plane} {f : Sym2 Plane}
    (h : OppositeSides X s(a, b) f) :
    ∃ q : Plane × Plane, (LeftStep X (a, b) q ∨ LeftStep X (b, a) q) ∧ s(q.1, q.2) = f := by
  obtain ⟨a', b', c, d, hR, h1, h2, h3, h4, he, rfl⟩ := h
  have hd := rhombusData_of_mem hX htri hR h1 h2 h3 h4
  rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact leftStep_of_rhombus hR h1 h2 h3 h4 hd.para hd.distinct.2.2.2.2.1 hd.distinct.2.1
  · obtain ⟨q, hq, hqf⟩ := leftStep_of_rhombus hR h1 h2 h3 h4 hd.para hd.distinct.2.2.2.2.1
      hd.distinct.2.1
    exact ⟨q, hq.symm, hqf⟩

/-- **A side of an exceptional face is terminal**: it carries at most one rhombus (on the side
away from the face). -/
theorem isTerminal_of_mem_orientedSides {G : Set ℂ} (hG : G ∈ exceptionalFaces X) {a b : Plane}
    (h : (toC a, toC b) ∈ orientedSides X G) : IsTerminal X s(a, b) := by
  have hinit := initial_of_mem_orientedSides hX htri hG h
  have side : ∀ f, OppositeSides X s(a, b) f →
      ∃ q : Plane × Plane, LeftStep X (b, a) q ∧ s(q.1, q.2) = f := by
    intro f o
    obtain ⟨q, hq | hq, hqf⟩ := leftStep_of_oppositeSides hX htri o
    · exact absurd ⟨_, hq.rev⟩ hinit
    · exact ⟨q, hq, hqf⟩
  intro f1 f2 o1 o2
  obtain ⟨q1, hq1, rfl⟩ := side f1 o1
  obtain ⟨q2, hq2, rfl⟩ := side f2 o2
  rw [LeftStep.unique hX htri hq1 hq2]

end

/-! ## The choice of exit edges -/

/-- A reference vertex of a face: the starting point of one of its oriented sides. -/
def faceRef (X : Finset Plane) (G : Set ℂ) : Plane :=
  if h : (orientedSides X G).Nonempty then toC.symm h.choose.1 else 0

/-- The unit hull side starting nearest to a point. -/
def nearestHullSide (X : Finset Plane) (z : Plane) : Plane × Plane :=
  if h : (unitHullSides X).Nonempty then
    (Finset.exists_min_image (unitHullSides X) (fun p => dist p.1 z) h).choose
  else (0, 0)

/-- The reference tangent at a face: the direction of the unit hull side nearest to it. -/
def tangentRef (X : Finset Plane) (G : Set ℂ) : Plane := sideDir (nearestHullSide X (faceRef X G))

/-- **The exit edges of the track-following process**: every exceptional face `G` emits through
the reversal of its oriented side whose reversed direction is closest to the reference
tangent. -/
def hopEmit (X : Finset Plane) (G : Set ℂ) : Plane × Plane :=
  if h : (orientedSides X G).Nonempty then
    (toC.symm (Finset.exists_min_image (orientedSides X G)
        (fun ab => ‖(ab.1 - ab.2) - toC (tangentRef X G)‖) h).choose.2,
      toC.symm (Finset.exists_min_image (orientedSides X G)
        (fun ab => ‖(ab.1 - ab.2) - toC (tangentRef X G)‖) h).choose.1)
  else (0, 0)

lemma faceRef_mem {X : Finset Plane} {G : Set ℂ} (h : (orientedSides X G).Nonempty) :
    ∃ ab ∈ orientedSides X G, toC (faceRef X G) = ab.1 := by
  refine ⟨h.choose, h.choose_spec, ?_⟩
  rw [faceRef, dif_pos h, LinearIsometryEquiv.apply_symm_apply]

lemma nearestHullSide_mem {X : Finset Plane} (h : (unitHullSides X).Nonempty) (z : Plane) :
    nearestHullSide X z ∈ unitHullSides X := by
  rw [nearestHullSide, dif_pos h]
  exact (Finset.exists_min_image (unitHullSides X) (fun p => dist p.1 z) h).choose_spec.1

lemma nearestHullSide_le {X : Finset Plane} (z : Plane) {ℓ : Plane × Plane}
    (hℓ : ℓ ∈ unitHullSides X) : dist (nearestHullSide X z).1 z ≤ dist ℓ.1 z := by
  have h : (unitHullSides X).Nonempty := ⟨ℓ, hℓ⟩
  rw [nearestHullSide, dif_pos h]
  exact (Finset.exists_min_image (unitHullSides X) (fun p => dist p.1 z) h).choose_spec.2 ℓ hℓ

lemma hopEmit_mem {X : Finset Plane} {G : Set ℂ} (h : (orientedSides X G).Nonempty) :
    (toC (hopEmit X G).2, toC (hopEmit X G).1) ∈ orientedSides X G := by
  rw [hopEmit, dif_pos h]
  simp only [LinearIsometryEquiv.apply_symm_apply]
  exact (Finset.exists_min_image (orientedSides X G)
    (fun ab => ‖(ab.1 - ab.2) - toC (tangentRef X G)‖) h).choose_spec.1

lemma hopEmit_min {X : Finset Plane} {G : Set ℂ} {ab : ℂ × ℂ} (hab : ab ∈ orientedSides X G) :
    ‖toC ((hopEmit X G).2 - (hopEmit X G).1) - toC (tangentRef X G)‖ ≤
      ‖(ab.1 - ab.2) - toC (tangentRef X G)‖ := by
  have h : (orientedSides X G).Nonempty := ⟨ab, hab⟩
  rw [hopEmit, dif_pos h]
  simp only [map_sub, LinearIsometryEquiv.apply_symm_apply]
  exact (Finset.exists_min_image (orientedSides X G)
    (fun ab => ‖(ab.1 - ab.2) - toC (tangentRef X G)‖) h).choose_spec.2 ab hab

/-! ## Exit edges -/

/-- The sides of a face are unit edges. -/
lemma dist_eq_one_of_mem_orientedSides {X : Finset Plane} {G : Set ℂ} {a b : Plane}
    (h : (toC a, toC b) ∈ orientedSides X G) : dist a b = 1 := by
  obtain ⟨-, hb, -⟩ := Finset.mem_filter.1 h
  have hu := (mem_unitPairs.1 (Finset.mem_filter.1 hb).1).2.2
  rwa [dist_toC] at hu

/-- **The exit edges of distinct live tokens are distinct.** -/
lemma exitEdge_injOn {X : Finset Plane} (hX : IsSeparated X) {emit : Set ℂ → Plane × Plane}
    (hemit : ∀ G ∈ exceptionalFaces X, (toC (emit G).2, toC (emit G).1) ∈ orientedSides X G)
    {T : Set ((Plane × Plane) ⊕ Set ℂ)}
    (hT : ∀ t ∈ T, (∀ p, t = Sum.inl p → p ∈ unitHullSides X) ∧
      (∀ G, t = Sum.inr G → G ∈ exceptionalFaces X)) :
    Set.InjOn (exitEdge emit) T := by
  intro t ht t' ht' hx
  rcases t with p | G <;> rcases t' with p' | G'
  · simp only [exitEdge, Sum.elim_inl, id] at hx; rw [hx]
  · exfalso
    simp only [exitEdge, Sum.elim_inl, Sum.elim_inr, id] at hx
    have hG' := (hT _ ht').2 G' rfl
    have := hemit G' hG'
    rw [← hx] at this
    exact not_mem_orientedSides_of_unitHullSide hX hG'.1 ((hT _ ht).1 p rfl) this
  · exfalso
    simp only [exitEdge, Sum.elim_inl, Sum.elim_inr, id] at hx
    have hG := (hT _ ht).2 G rfl
    have := hemit G hG
    rw [hx] at this
    exact not_mem_orientedSides_of_unitHullSide hX hG.1 ((hT _ ht').1 p' rfl) this
  · simp only [exitEdge, Sum.elim_inr] at hx
    have hG := (hT _ ht).2 G rfl
    have hG' := (hT _ ht').2 G' rfl
    have h1 := hemit G hG
    have h2 := hemit G' hG'
    rw [hx] at h1
    obtain ⟨-, hb1, hl1⟩ := Finset.mem_filter.1 h1
    obtain ⟨-, hb2, hl2⟩ := Finset.mem_filter.1 h2
    have he := (Finset.mem_filter.1 hb1).1
    rw [face_left_unique hX he hG.1.1 hG'.1.1 hb1 hb2 hl1 hl2]

/-! ## One emission (§9.1, §8.2) -/

/-- **One emission step.**  Let `G` be an exceptional pentagon or heptagon of a round
configuration, receiving tokens `i ∈ A` (at least two, resp. three) through pairwise distinct
oriented sides `entry i` whose directions are the directions of the unit exit edges `exit i`.  If
every token carries a label `lab i` (a unit hull side) whose direction is within `δ` of the exit
direction and which starts within `R` of the entry vertex, then the exit edge `hopEmit X G` of `G`
has direction within `√(8 δ') + 4 (R + 7)/D + 4 √(3 δ_round)` of every label, where
`δ' = δ + 4 (R + 7)/D + 4 √(3 δ_round)`. -/
theorem emission_step {X : Finset Plane} {O : Plane} {D η' δr : ℝ}
    (hR : RoundData X O D η' δr)
    (hopp : ∀ G ∈ exceptionalFaces X, (faceSize X G = 5 ∨ faceSize X G = 7) → ∀ e : ℂ,
      ‖e‖ = 1 → ∀ δ : ℝ, 0 ≤ δ → ∀ M ⊆ orientedSides X G, faceSize X G ≤ 2 * M.card + 1 →
      (∀ ab ∈ M, ‖(ab.2 - ab.1) - e‖ ≤ δ) →
      ∃ ab ∈ orientedSides X G, ‖(ab.1 - ab.2) - e‖ ^ 2 ≤ 8 * δ)
    (hdist : ∀ F ∈ exceptionalFaces X, ∀ ab ∈ orientedSides X F, ∀ ab' ∈ orientedSides X F,
      dist ab.1 ab'.1 ≤ faceSize X F)
    {G : Set ℂ} (hG : G ∈ exceptionalFaces X) (hk : faceSize X G = 5 ∨ faceSize X G = 7)
    {ι : Type} (A : Finset ι) (entry : ι → ℂ × ℂ) (exit lab : ι → Plane × Plane)
    (hinj : Set.InjOn entry A) (hcard : faceSize X G ≤ 2 * A.card + 1)
    (hside : ∀ i ∈ A, entry i ∈ orientedSides X G ∧
      (entry i).2 - (entry i).1 = toC (exit i).2 - toC (exit i).1)
    (hunit : ∀ i ∈ A, dist (exit i).1 (exit i).2 = 1)
    (hlab : ∀ i ∈ A, lab i ∈ unitHullSides X) {δ R : ℝ}
    (hdir : ∀ i ∈ A, ‖sideDir (exit i) - sideDir (lab i)‖ ≤ δ)
    (hpos : ∀ i ∈ A, dist (lab i).1 (toC.symm (entry i).1) ≤ R) (hδ : 0 ≤ δ) :
    ∀ i ∈ A, ‖sideDir (hopEmit X G) - sideDir (lab i)‖ ≤
      √(8 * (δ + 4 * (R + 7) / D + 4 * √(3 * δr))) + 4 * (R + 7) / D + 4 * √(3 * δr) := by
  have hD := hR.D_pos
  set ρ := 4 * √(3 * δr) with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  -- the reference tangent
  have hsides : (orientedSides X G).Nonempty := by
    have hA : A.Nonempty := by
      rw [← Finset.card_pos]; rcases hk with h | h <;> omega
    obtain ⟨i, hi⟩ := hA
    exact ⟨_, (hside i hi).1⟩
  obtain ⟨ab₀, hab₀, hz⟩ := faceRef_mem hsides
  set z := faceRef X G
  have hU : (unitHullSides X).Nonempty := by
    have hA : A.Nonempty := by
      rw [← Finset.card_pos]; rcases hk with h | h <;> omega
    obtain ⟨i, hi⟩ := hA
    exact ⟨_, hlab i hi⟩
  set ℓG := nearestHullSide X z
  have hℓG : ℓG ∈ unitHullSides X := nearestHullSide_mem hU z
  have hu : tangentRef X G = sideDir ℓG := rfl
  have hk7 : (faceSize X G : ℝ) ≤ 7 := by rcases hk with h | h <;> rw [h] <;> norm_num
  -- labels are close to the reference tangent
  have hnear : ∀ i ∈ A, ‖sideDir (lab i) - tangentRef X G‖ ≤ 4 * (R + 7) / D + ρ := by
    intro i hi
    have h1 : dist (lab i).1 z ≤ R + 7 := by
      have hz' : dist (toC.symm (entry i).1) z ≤ 7 := by
        have := hdist G hG _ (hside i hi).1 _ hab₀
        rw [← hz] at this
        rw [show dist (toC.symm (entry i).1) z = dist (entry i).1 (toC z) by
          rw [← dist_toC, LinearIsometryEquiv.apply_symm_apply]]
        linarith
      calc dist (lab i).1 z ≤ dist (lab i).1 (toC.symm (entry i).1) +
            dist (toC.symm (entry i).1) z := dist_triangle _ _ _
        _ ≤ R + 7 := add_le_add (hpos i hi) hz'
    have h2 : dist ℓG.1 z ≤ R + 7 := (nearestHullSide_le z (hlab i hi)).trans h1
    have h3 : dist (lab i).1 ℓG.1 ≤ 2 * (R + 7) := by
      have := dist_triangle (lab i).1 z ℓG.1
      rw [dist_comm z] at this
      linarith
    have hs := sideDir_sub_le hR (mem_ccwHullSides.1 (Finset.mem_filter.1 (hlab i hi)).1)
      (mem_ccwHullSides.1 (Finset.mem_filter.1 hℓG).1)
    rw [hu]
    calc ‖sideDir (lab i) - sideDir ℓG‖ ≤ 2 * dist (lab i).1 ℓG.1 / D + 4 * √(3 * δr) := hs
      _ ≤ 2 * (2 * (R + 7)) / D + ρ := by gcongr
      _ = 4 * (R + 7) / D + ρ := by ring
  -- the marked sides
  set δ' := δ + 4 * (R + 7) / D + ρ
  have hδ' : 0 ≤ δ' := by
    have : 0 ≤ R + 7 := by
      obtain ⟨i, hi⟩ : A.Nonempty := by rw [← Finset.card_pos]; rcases hk with h | h <;> omega
      have := hpos i hi; have := dist_nonneg (x := (lab i).1) (y := toC.symm (entry i).1)
      linarith
    positivity
  have hM : ∀ ab ∈ A.image entry, ‖(ab.2 - ab.1) - toC (tangentRef X G)‖ ≤ δ' := by
    intro ab hab
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hab
    rw [(hside i hi).2, ← map_sub, ← sideDir_of_dist_eq_one (hunit i hi), ← map_sub,
      LinearIsometryEquiv.norm_map]
    calc ‖sideDir (exit i) - tangentRef X G‖
        ≤ ‖sideDir (exit i) - sideDir (lab i)‖ + ‖sideDir (lab i) - tangentRef X G‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ δ + (4 * (R + 7) / D + ρ) := add_le_add (hdir i hi) (hnear i hi)
      _ = δ' := by ring
  have hMsub : A.image entry ⊆ orientedSides X G := by
    intro ab hab
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hab
    exact (hside i hi).1
  have hMcard : faceSize X G ≤ 2 * (A.image entry).card + 1 := by
    rw [Finset.card_image_of_injOn hinj]; exact hcard
  have hune : ‖toC (tangentRef X G)‖ = 1 := by
    rw [LinearIsometryEquiv.norm_map, hu]
    exact norm_sideDir (mem_ccwHullSides.1 (Finset.mem_filter.1 hℓG).1).2.2.1
  obtain ⟨ab, hab, habs⟩ := hopp G hG hk _ hune δ' hδ' _ hMsub hMcard hM
  -- the exit edge
  have hmin := hopEmit_min hab
  have hemit := hopEmit_mem hsides
  have hemit1 : dist (hopEmit X G).1 (hopEmit X G).2 = 1 := by
    rw [dist_comm]; exact dist_eq_one_of_mem_orientedSides hemit
  have hout : ‖sideDir (hopEmit X G) - tangentRef X G‖ ≤ √(8 * δ') := by
    rw [sideDir_of_dist_eq_one hemit1, ← LinearIsometryEquiv.norm_map toC, map_sub]
    refine hmin.trans ?_
    rw [← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt habs
  intro i hi
  calc ‖sideDir (hopEmit X G) - sideDir (lab i)‖
      ≤ ‖sideDir (hopEmit X G) - tangentRef X G‖ + ‖tangentRef X G - sideDir (lab i)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ √(8 * δ') + (4 * (R + 7) / D + ρ) := by
        gcongr
        rw [norm_sub_rev]; exact hnear i hi
    _ = _ := by ring

/-! ## The schedule of errors and displacements (§9.2) -/

/-- The angle error allowed after round `m`: `D^{-3 e_m / 2}`. -/
def errB (D : ℝ) (m : ℕ) : ℝ := D ^ (-(3 / 2 * scaleExp m))

/-- The displacement allowed after round `m`: `Λ_m = D^{1 - e_m}`. -/
def disB (D : ℝ) (m : ℕ) : ℝ := D ^ (1 - scaleExp m)

/-- The cutoff for the tracks emitted in round `m`: `Λ_m / 2`. -/
def cutB (D : ℝ) (m : ℕ) : ℝ := D ^ (1 - scaleExp m) / 2

/-- The roundness error `4 √(3 δ)` with `δ = 100 D^{-2/9}`. -/
def roundErr (D : ℝ) : ℝ := 4 * √(3 * (100 * D ^ (-(2 / 9 : ℝ))))

lemma errB_mono {D : ℝ} (hD : 1 ≤ D) {m m' : ℕ} (h : m ≤ m') : errB D m ≤ errB D m' := by
  unfold errB
  exact Real.rpow_le_rpow_of_exponent_le hD (by linarith [scaleExp_anti h])

lemma disB_mono {D : ℝ} (hD : 1 ≤ D) {m m' : ℕ} (h : m ≤ m') : disB D m ≤ disB D m' := by
  unfold disB
  exact Real.rpow_le_rpow_of_exponent_le hD (by linarith [scaleExp_anti h])

lemma errB_nonneg (D : ℝ) (m : ℕ) (hD : 0 ≤ D) : 0 ≤ errB D m := by
  unfold errB; positivity

lemma roundErr_le {D : ℝ} (hD : 1 ≤ D) : roundErr D ≤ 72 * D ^ (-(1 / 9 : ℝ)) := by
  have hD0 : 0 < D := by linarith
  set x := D ^ (-(1 / 9 : ℝ))
  have hx : 0 ≤ x := by positivity
  have hx2 : D ^ (-(2 / 9 : ℝ)) = x ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hD0.le]; norm_num
  unfold roundErr
  rw [hx2]
  have : √(3 * (100 * x ^ 2)) ≤ 18 * x := by
    rw [show 18 * x = √((18 * x) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  linarith

/-- One round of the schedule: the heptagon square root of the input error, plus the tangent
drift over the displacement, stays within the next error bound; and the displacements add up. -/
lemma eventually_schedule_step (k : ℕ) :
    ∀ᶠ D : ℝ in atTop,
      √(8 * (errB D k + 4 * (disB D k + 7) / D + roundErr D)) + 4 * (disB D k + 7) / D +
          roundErr D ≤ errB D (k + 1) ∧
        disB D k + 8 + cutB D (k + 1) ≤ disB D (k + 1) := by
  set a := scaleExp k
  set b := scaleExp (k + 1)
  have hab : a = 4 * b := scaleExp_succ k
  have hb0 : 0 < b := scaleExp_pos _
  have ha1 : a ≤ 1 / 20 := scaleExp_le k
  filter_upwards [eventually_ge_atTop 1,
    eventually_const_mul_rpow_le 133 (α := -(2 * b)) (β := -(3 / 2 * b)) (by linarith),
    eventually_const_mul_rpow_le 4 (α := 1 - a) (β := 1 - b) (by linarith),
    eventually_const_mul_rpow_le 8 (α := 0) (β := 1 - a) (by linarith)] with D hD h1 h2 h3
  have hD0 : 0 < D := by linarith
  set x := D ^ (-a)
  set y := D ^ (-(2 * b))
  have hy0 : 0 ≤ y := by positivity
  have hxy : x = y ^ 2 := by
    show D ^ (-a) = (D ^ (-(2 * b))) ^ 2
    rw [← Real.rpow_natCast, ← Real.rpow_mul hD0.le, hab]
    congr 1; push_cast; ring
  have hy1 : y ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hD (by linarith)
  have hsx : √x = y := by rw [hxy, Real.sqrt_sq hy0]
  have e1 : errB D k ≤ x := Real.rpow_le_rpow_of_exponent_le hD (by linarith [scaleExp_pos k])
  have e2 : 4 * (disB D k + 7) / D ≤ 32 * x := by
    have hd : disB D k / D = x := by
      show D ^ (1 - a) / D = D ^ (-a)
      rw [show (1 - a) = -a + 1 by ring, Real.rpow_add hD0, Real.rpow_one, mul_div_assoc,
        div_self hD0.ne', mul_one]
    have hinv : 1 / D ≤ x := by
      rw [one_div, ← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le hD (by linarith)
    have : 4 * (disB D k + 7) / D = 4 * (disB D k / D) + 28 * (1 / D) := by ring
    rw [this, hd]; linarith
  have e3 : roundErr D ≤ 72 * x := by
    refine (roundErr_le hD).trans ?_
    have : D ^ (-(1 / 9 : ℝ)) ≤ x := Real.rpow_le_rpow_of_exponent_le hD (by linarith)
    linarith
  have hx0 : 0 ≤ x := by positivity
  refine ⟨?_, ?_⟩
  · have hin : 8 * (errB D k + 4 * (disB D k + 7) / D + roundErr D) ≤ 29 ^ 2 * x := by
      have := errB_nonneg D k hD0.le
      nlinarith
    have hsq : √(8 * (errB D k + 4 * (disB D k + 7) / D + roundErr D)) ≤ 29 * y := by
      calc _ ≤ √(29 ^ 2 * x) := Real.sqrt_le_sqrt hin
        _ = 29 * y := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num), hsx]
    have hxy' : x ≤ y := by rw [hxy]; nlinarith
    have : 133 * y ≤ errB D (k + 1) := by
      unfold errB; simpa [y] using h1
    linarith
  · have h7 : 8 ≤ D ^ (1 - a) := by simpa using h3
    have hp : 0 ≤ D ^ (1 - a) := by positivity
    have key : D ^ (1 - a) + 8 + D ^ (1 - b) / 2 ≤ D ^ (1 - b) := by
      have h2' : 4 * D ^ (1 - a) ≤ D ^ (1 - b) := h2
      calc D ^ (1 - a) + 8 + D ^ (1 - b) / 2 ≤ D ^ (1 - a) + D ^ (1 - a) + D ^ (1 - b) / 2 := by
            gcongr
        _ ≤ D ^ (1 - b) := by linarith
    exact key

/-- **The schedule**: eventually every round of depth `≤ K` satisfies the step inequalities, and
the final error and displacement are below `1/100` and `D/100`. -/
lemma eventually_schedule (K : ℕ) :
    ∀ᶠ D : ℝ in atTop, 1 ≤ D ∧ (∀ k < K,
      √(8 * (errB D k + 4 * (disB D k + 7) / D + roundErr D)) + 4 * (disB D k + 7) / D +
          roundErr D ≤ errB D (k + 1) ∧
        disB D k + 8 + cutB D (k + 1) ≤ disB D (k + 1)) ∧
      errB D K ≤ 1 / 100 ∧ disB D K ≤ D / 100 := by
  have hall : ∀ᶠ D : ℝ in atTop, ∀ k ∈ Finset.range K,
      √(8 * (errB D k + 4 * (disB D k + 7) / D + roundErr D)) + 4 * (disB D k + 7) / D +
          roundErr D ≤ errB D (k + 1) ∧
        disB D k + 8 + cutB D (k + 1) ≤ disB D (k + 1) :=
    (Finset.eventually_all _).2 (fun k _ => eventually_schedule_step k)
  have he := scaleExp_pos K
  have he1 := scaleExp_le K
  filter_upwards [eventually_ge_atTop 1, hall,
    eventually_const_mul_rpow_le 100 (α := -(3 / 2 * scaleExp K)) (β := 0) (by linarith),
    eventually_mul_rpow_le 1 (α := 1 - scaleExp K) (δ := 1 / 100) (by linarith)
      (by norm_num)] with D hD hall h1 h2
  refine ⟨hD, fun k hk => hall k (Finset.mem_range.2 hk), ?_, ?_⟩
  · unfold errB
    rw [Real.rpow_zero] at h1
    linarith
  · unfold disB
    linarith

end Erdos99

end

end HopEmission

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `HopEmissionMain`
-/

section HopEmissionMain

/-!
# The emission lemma of the track-following process (Verification Guide §9.1–§9.3)

This file proves the emission lemma `hopEmission_main` (the statement `exists_hopEmission` of
`Stability`) from the ingredients of `HopEmission`, `LongExits`, `TokenLabels`
and the cap capacity `good_cap_tokens_le`.

* The exit edges are `hopEmit X`; the discarded tokens are the sources on long tracks and the
  tokens of faces whose exit track is longer than half the current scale, or which received a
  discarded token (`hopBad`).
* `tokenBound`: by induction on the rounds, every good token present after round `k` carries a
  label (`labelAt`) whose direction is within `errB k` of its exit direction and which starts
  within `disB k` of the far end of its track.
-/

open scoped BigOperators Real
open Filter Topology EstablishedExternalResults

@[expose] public noncomputable section

open Classical

namespace Erdos99

open Propagation

namespace TokenProcess

variable {X : Finset Plane} (P : TokenProcess X)

/-- The tokens reaching a cap by the end of round `j + 1`. -/
def capTokens (j : ℕ) : Finset ((Plane × Plane) ⊕ Set ℂ) :=
  ((unitHullSides X).filter (fun p => P.start p = .cap)).disjSum
    (P.fin.toFinset.filter (fun G => P.out G = .cap ∧ P.Emits j G))

/-- The cap arrivals by the end of round `j + 1` are counted by `capTokens j`. -/
theorem capArr_succ_eq_card (j : ℕ) : P.capArr (j + 1) = (P.capTokens j).card := by
  rw [capTokens, Finset.card_disjSum, Finset.card_filter, Finset.card_filter]
  show ∑ p ∈ unitHullSides X, toCap (P.start p) +
      ∑ G ∈ P.fin.toFinset, toCap (P.out G) * emitted (faceSize X G) (P.faceArr j G) = _
  congr 1
  refine Finset.sum_congr rfl (fun G _ => ?_)
  unfold toCap Emits
  rcases emitted_eq_zero_or_one (faceSize X G) (P.faceArr j G) with h | h <;>
    · rw [h]; split_ifs <;> simp_all

/-- The status of a token no longer changes once it is present. -/
lemma badAt_stable (srcBad : Plane × Plane → Prop) (primBad : ℕ → Set ℂ → Prop) {m n : ℕ}
    (hmn : m ≤ n) {t : (Plane × Plane) ⊕ Set ℂ} (ht : P.Timed m t) :
    P.badAt srcBad primBad n t ↔ P.badAt srcBad primBad m t := by
  rcases t with p | G
  · simp
  · exact P.badAt_inr_stable srcBad primBad hmn ht

end TokenProcess

/-! ## The discarded tokens -/

/-- A source is discarded if its track has at least `D^{19/20}` rhombi. -/
def hopSrcBad (X : Finset Plane) (p : Plane × Plane) : Prop :=
  diam X ^ (19 / 20 : ℝ) ≤ srcLen X s(p.1, p.2)

/-- A face emitting at round `m` is primarily bad if its exit track has at least `Λ_m / 2`
rhombi. -/
def hopPrimBad (X : Finset Plane) (m : ℕ) (G : Set ℂ) : Prop :=
  cutB (diam X) m ≤ srcLen X s((hopEmit X G).1, (hopEmit X G).2)

/-- The discarded tokens after round `K`. -/
def hopBad {X : Finset Plane} (hX : IsSeparated X) (K : ℕ) : (Plane × Plane) ⊕ Set ℂ → Prop :=
  (hopProcess hX (hopEmit X)).badAt (hopSrcBad X) (hopPrimBad X) K

/-- The bound carried by a token after round `k`: its label (after round `K`) has direction within
`errB k` of its exit direction and starts within `disB k` of the far end of its track. -/
def TokBound {X : Finset Plane} (hX : IsSeparated X) (K k : ℕ) (t : (Plane × Plane) ⊕ Set ℂ) :
    Prop :=
  ‖sideDir (exitEdge (hopEmit X) t) - sideDir ((hopProcess hX (hopEmit X)).labelAt K t)‖ ≤
      errB (diam X) k ∧
    dist ((hopProcess hX (hopEmit X)).labelAt K t).1 (hopEnd X (exitEdge (hopEmit X) t)).1 ≤
      disB (diam X) k

/-- The vertices of an oriented side lie in `X`. -/
lemma mem_of_mem_orientedSides {X : Finset Plane} {G : Set ℂ} {a b : Plane}
    (h : (toC a, toC b) ∈ orientedSides X G) : a ∈ X ∧ b ∈ X := by
  obtain ⟨hv, -⟩ := Finset.mem_filter.1 h
  obtain ⟨h1, h2⟩ := Finset.mem_product.1 hv
  exact ⟨by simpa [mem_cVerts] using h1, by simpa [mem_cVerts] using h2⟩

section Main

variable {X : Finset Plane} (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X)
  (hsides : ∀ G ∈ exceptionalFaces X, (orientedSides X G).Nonempty)

include hsides in
lemma hopEmit_mem' : ∀ G ∈ exceptionalFaces X,
    (toC (hopEmit X G).2, toC (hopEmit X G).1) ∈ orientedSides X G :=
  fun G hG => hopEmit_mem (hsides G hG)

/-- The arrivals of the track-following process are sources (unit hull sides) and exceptional
faces. -/
lemma hop_arrivals_mem {j : ℕ} {F : Set ℂ} {t : (Plane × Plane) ⊕ Set ℂ}
    (ht : t ∈ (hopProcess hX (hopEmit X)).arrivals j F) :
    (∀ p, t = Sum.inl p → p ∈ unitHullSides X) ∧ (∀ G, t = Sum.inr G → G ∈ exceptionalFaces X) := by
  refine ⟨fun p hp => ?_, fun G hG => ?_⟩
  · subst hp; exact ((hopProcess hX (hopEmit X)).mem_arrivals_inl.1 ht).1
  · subst hG
    exact (Set.Finite.mem_toFinset _).1 ((hopProcess hX (hopEmit X)).mem_arrivals_inr.1 ht).1

/-- A good source carries the bound of every round. -/
lemma tokBound_inl {K : ℕ} (hD1 : 1 ≤ diam X)
    (h1920 : diam X ^ (19 / 20 : ℝ) ≤ disB (diam X) 0) {p : Plane × Plane}
    (hp : p ∈ unitHullSides X) (hgood : ¬ hopSrcBad X p) (k : ℕ) :
    TokBound hX K k (Sum.inl p) := by
  refine ⟨?_, ?_⟩
  · simp only [exitEdge, Sum.elim_inl, id, TokenProcess.labelAt, sub_self, norm_zero]
    exact errB_nonneg _ _ (by linarith)
  · simp only [exitEdge, Sum.elim_inl, id, TokenProcess.labelAt]
    have hpX : p ∈ X ×ˢ X := (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).1
    rw [dist_comm]
    refine (dist_hopEnd_le hpX).trans ?_
    unfold hopSrcBad at hgood
    push_neg at hgood
    exact hgood.le.trans (h1920.trans (disB_mono hD1 (Nat.zero_le k)))

include htri hsides in
/-- **One round of emissions** (§9.1–§9.2): a face emitting first at round `k + 1`, all of whose
inputs carry the bound of round `k`, emits along a direction within the next error of its label,
and its label starts within `disB k + 8` of the start of its exit edge. -/
lemma hop_emission_round {K k : ℕ} (hk : k < K) {O : Plane} {η' : ℝ}
    (hR : RoundData X O (diam X) η' (100 * diam X ^ (-(2 / 9 : ℝ))))
    (hopp : ∀ G ∈ exceptionalFaces X, (faceSize X G = 5 ∨ faceSize X G = 7) → ∀ e : ℂ,
      ‖e‖ = 1 → ∀ δ : ℝ, 0 ≤ δ → ∀ M ⊆ orientedSides X G, faceSize X G ≤ 2 * M.card + 1 →
      (∀ ab ∈ M, ‖(ab.2 - ab.1) - e‖ ≤ δ) →
      ∃ ab ∈ orientedSides X G, ‖(ab.1 - ab.2) - e‖ ^ 2 ≤ 8 * δ)
    (hdist : ∀ F ∈ exceptionalFaces X, ∀ ab ∈ orientedSides X F, ∀ ab' ∈ orientedSides X F,
      dist ab.1 ab'.1 ≤ faceSize X F)
    {G : Set ℂ} (hG : G ∈ exceptionalFaces X)
    (h1 : (hopProcess hX (hopEmit X)).Emits (k + 1) G)
    (h0 : ¬ (hopProcess hX (hopEmit X)).Emits k G)
    (hin : ∀ s ∈ (hopProcess hX (hopEmit X)).arrivals k G, TokBound hX K k s) :
    ‖sideDir (hopEmit X G) - sideDir ((hopProcess hX (hopEmit X)).labelAt K (Sum.inr G))‖ ≤
      √(8 * (errB (diam X) k + 4 * (disB (diam X) k + 7) / diam X + roundErr (diam X))) +
        4 * (disB (diam X) k + 7) / diam X + roundErr (diam X) ∧
    dist ((hopProcess hX (hopEmit X)).labelAt K (Sum.inr G)).1 (hopEmit X G).1 ≤
      disB (diam X) k + 8 := by
  set P := hopProcess hX (hopEmit X) with hP
  have hemit := hopEmit_mem' hsides
  obtain ⟨hinj, hside⟩ := hopProcess_incidences hX htri (hopEmit X) hemit k G
  have hk57 := P.faceSize_of_emits h1
  have hcard := P.faceSize_le_of_emits h1
  have hfe : P.firstEmit G = k + 1 := P.firstEmit_eq h1 (by simpa using h0)
  have hpar := P.parent_mem h1
  rw [hfe, Nat.add_sub_cancel] at hpar
  have hlabG : P.labelAt K (Sum.inr G) = P.labelAt K (P.parent G) := by
    rw [P.labelAt_stable (show k + 1 ≤ K by omega) (t := Sum.inr G) h1, P.labelAt_succ_inr,
      P.labelAt_stable (show k ≤ K by omega) (P.timed_parent h1)]
  have hunit : ∀ s ∈ P.arrivals k G,
      dist (exitEdge (hopEmit X) s).1 (exitEdge (hopEmit X) s).2 = 1 := by
    intro s hs
    obtain ⟨hs1, hs2⟩ := hop_arrivals_mem hX hs
    rcases s with p | G'
    · exact (Finset.mem_filter.1 (hs1 p rfl)).2
    · rw [dist_comm]; exact dist_eq_one_of_mem_orientedSides (hemit G' (hs2 G' rfl))
  have hlab : ∀ s ∈ P.arrivals k G, P.labelAt K s ∈ unitHullSides X := fun s hs =>
    P.labelAt_mem (P.timed_mono (by omega) (P.timed_of_mem_arrivals hs))
      (hop_arrivals_mem hX hs).1
  have hpos : ∀ s ∈ P.arrivals k G,
      dist (P.labelAt K s).1 (toC.symm ((hopEntry X (hopEmit X)).edge s).1) ≤
        disB (diam X) k := by
    intro s hs
    rw [hopEntry_edge]
    simp only [LinearIsometryEquiv.symm_apply_apply]
    exact (hin s hs).2
  have hstep := emission_step hR hopp hdist hG hk57 (P.arrivals k G)
    (hopEntry X (hopEmit X)).edge (exitEdge (hopEmit X)) (P.labelAt K) hinj hcard hside hunit hlab
    (fun s hs => (hin s hs).1) hpos (errB_nonneg _ _ hR.D_pos.le)
  refine ⟨?_, ?_⟩
  · rw [hlabG]; exact hstep _ hpar
  · rw [hlabG]
    have hs := hside _ hpar
    rw [hopEntry_edge] at hs
    have h7 := hdist G hG _ hs.1 _ (hemit G hG)
    have hfs : (faceSize X G : ℝ) ≤ 7 := by rcases hk57 with h | h <;> rw [h] <;> norm_num
    simp only [dist_toC] at h7
    have h1' : dist (hopEmit X G).2 (hopEmit X G).1 = 1 :=
      dist_eq_one_of_mem_orientedSides (hemit G hG)
    have h2 := (hin _ hpar).2
    calc dist (P.labelAt K (P.parent G)).1 (hopEmit X G).1
        ≤ dist (P.labelAt K (P.parent G)).1 (hopEnd X (exitEdge (hopEmit X) (P.parent G))).1 +
          dist (hopEnd X (exitEdge (hopEmit X) (P.parent G))).1 (hopEmit X G).2 +
          dist (hopEmit X G).2 (hopEmit X G).1 := dist_triangle4 _ _ _ _
      _ ≤ disB (diam X) k + 8 := by linarith

include htri hsides in
/-- **The token bound** (§9.2): every good token present after round `k ≤ K` carries the bound of
round `k`. -/
theorem tokenBound {K : ℕ} {O : Plane} {η' : ℝ}
    (hR : RoundData X O (diam X) η' (100 * diam X ^ (-(2 / 9 : ℝ)))) (hD1 : 1 ≤ diam X)
    (hstep : ∀ k < K,
      √(8 * (errB (diam X) k + 4 * (disB (diam X) k + 7) / diam X + roundErr (diam X))) +
          4 * (disB (diam X) k + 7) / diam X + roundErr (diam X) ≤ errB (diam X) (k + 1) ∧
        disB (diam X) k + 8 + cutB (diam X) (k + 1) ≤ disB (diam X) (k + 1))
    (h1920 : diam X ^ (19 / 20 : ℝ) ≤ disB (diam X) 0)
    (hopp : ∀ G ∈ exceptionalFaces X, (faceSize X G = 5 ∨ faceSize X G = 7) → ∀ e : ℂ,
      ‖e‖ = 1 → ∀ δ : ℝ, 0 ≤ δ → ∀ M ⊆ orientedSides X G, faceSize X G ≤ 2 * M.card + 1 →
      (∀ ab ∈ M, ‖(ab.2 - ab.1) - e‖ ≤ δ) →
      ∃ ab ∈ orientedSides X G, ‖(ab.1 - ab.2) - e‖ ^ 2 ≤ 8 * δ)
    (hdist : ∀ F ∈ exceptionalFaces X, ∀ ab ∈ orientedSides X F, ∀ ab' ∈ orientedSides X F,
      dist ab.1 ab'.1 ≤ faceSize X F) :
    ∀ k ≤ K, ∀ t, (hopProcess hX (hopEmit X)).Timed k t → ¬ hopBad hX K t →
      (∀ p, t = Sum.inl p → p ∈ unitHullSides X) →
      (∀ G, t = Sum.inr G → G ∈ exceptionalFaces X) → TokBound hX K k t := by
  set P := hopProcess hX (hopEmit X) with hP
  intro k
  induction k with
  | zero =>
    intro _ t ht hgood hs _
    rcases t with p | G
    · exact tokBound_inl hX hD1 h1920 (hs p rfl) (by simpa [hopBad] using hgood) 0
    · exact absurd ht (P.not_emits_zero G)
  | succ k ih =>
    intro hk t ht hgood hs hf
    rcases t with p | G
    · exact tokBound_inl hX hD1 h1920 (hs p rfl) (by simpa [hopBad] using hgood) (k + 1)
    · have hG := hf G rfl
      have h1 : P.Emits (k + 1) G := ht
      by_cases h0 : P.Emits k G
      · obtain ⟨a, b⟩ := ih (by omega) (Sum.inr G) h0 hgood hs hf
        exact ⟨a.trans (errB_mono hD1 (Nat.le_succ k)), b.trans (disB_mono hD1 (Nat.le_succ k))⟩
      · have hfe : P.firstEmit G = k + 1 := P.firstEmit_eq h1 (by simpa using h0)
        have hgi := P.good_inputs (hopSrcBad X) (hopPrimBad X) (n := K) (P.emits_mono hk h1)
          hgood
        rw [hfe, Nat.add_sub_cancel] at hgi
        obtain ⟨hprim, hgin⟩ := hgi
        have hin : ∀ s ∈ P.arrivals k G, TokBound hX K k s := by
          intro s hs'
          have hts := P.timed_of_mem_arrivals hs'
          refine ih (by omega) s hts ?_ (hop_arrivals_mem hX hs').1 (hop_arrivals_mem hX hs').2
          show ¬ P.badAt (hopSrcBad X) (hopPrimBad X) K s
          rw [P.badAt_stable _ _ (show k ≤ K by omega) hts]
          exact hgin s hs'
        obtain ⟨hd, hp⟩ := hop_emission_round hX htri hsides (by omega : k < K) hR hopp hdist hG
          h1 h0 hin
        obtain ⟨hs1, hs2⟩ := hstep k (by omega)
        refine ⟨hd.trans hs1, ?_⟩
        show dist (P.labelAt K (Sum.inr G)).1 (hopEnd X (hopEmit X G)).1 ≤ _
        have hemX := mem_of_mem_orientedSides (hopEmit_mem' hsides G hG)
        have hpX : hopEmit X G ∈ X ×ˢ X := Finset.mem_product.2 ⟨hemX.2, hemX.1⟩
        have hlen := dist_hopEnd_le hpX
        unfold hopPrimBad at hprim
        push_neg at hprim
        calc dist (P.labelAt K (Sum.inr G)).1 (hopEnd X (hopEmit X G)).1
            ≤ dist (P.labelAt K (Sum.inr G)).1 (hopEmit X G).1 +
              dist (hopEmit X G).1 (hopEnd X (hopEmit X G)).1 := dist_triangle _ _ _
          _ ≤ disB (diam X) k + 8 + cutB (diam X) (k + 1) := by
              rw [dist_comm (hopEmit X G).1]; linarith
          _ ≤ disB (diam X) (k + 1) := hs2

include hX hsides in
/-- The exit edges are injective on the exceptional faces. -/
lemma hopEmit_injOn {S : Set (Set ℂ)} (hS : S ⊆ exceptionalFaces X) :
    Set.InjOn (hopEmit X) S := by
  intro G hG G' hG' he
  have hT : ∀ t ∈ Sum.inr '' S, (∀ p, t = Sum.inl p → p ∈ unitHullSides X) ∧
      (∀ G, t = Sum.inr G → G ∈ exceptionalFaces X) := by
    rintro t ⟨G0, hG0, rfl⟩
    refine ⟨fun p hp => by simp at hp, fun G hG => ?_⟩
    cases hG; exact hS hG0
  exact Sum.inr_injective (exitEdge_injOn hX (hopEmit_mem' hsides) hT
    (Set.mem_image_of_mem _ hG) (Set.mem_image_of_mem _ hG') he)

include htri hsides in
/-- **Few primarily bad faces** (§9.2): in every round `m ≤ K`, the faces emitting first at round
`m` with good inputs whose exit track is long number at most `ε₁ D`. -/
lemma primBad_count {K : ℕ} {O : Plane} {η' : ℝ}
    (hR : RoundData X O (diam X) η' (100 * diam X ^ (-(2 / 9 : ℝ)))) (hD1 : 1 ≤ diam X)
    (hstep : ∀ k < K,
      √(8 * (errB (diam X) k + 4 * (disB (diam X) k + 7) / diam X + roundErr (diam X))) +
          4 * (disB (diam X) k + 7) / diam X + roundErr (diam X) ≤ errB (diam X) (k + 1) ∧
        disB (diam X) k + 8 + cutB (diam X) (k + 1) ≤ disB (diam X) (k + 1))
    (h1920 : diam X ^ (19 / 20 : ℝ) ≤ disB (diam X) 0)
    (hopp : ∀ G ∈ exceptionalFaces X, (faceSize X G = 5 ∨ faceSize X G = 7) → ∀ e : ℂ,
      ‖e‖ = 1 → ∀ δ : ℝ, 0 ≤ δ → ∀ M ⊆ orientedSides X G, faceSize X G ≤ 2 * M.card + 1 →
      (∀ ab ∈ M, ‖(ab.2 - ab.1) - e‖ ≤ δ) →
      ∃ ab ∈ orientedSides X G, ‖(ab.1 - ab.2) - e‖ ^ 2 ≤ 8 * δ)
    (hdist : ∀ F ∈ exceptionalFaces X, ∀ ab ∈ orientedSides X F, ∀ ab' ∈ orientedSides X F,
      dist ab.1 ab'.1 ≤ faceSize X F) {ε1 : ℝ}
    (hlong : ∀ m ≤ K, ∀ (S : Finset (Set ℂ)) (q lab : Set ℂ → Plane × Plane), Set.InjOn q S →
      (∀ i ∈ S, (q i).1 ≠ (q i).2 ∧ IsTerminal X s((q i).1, (q i).2) ∧
        1 / 2 * diam X ^ (1 - scaleExp m) ≤ srcLen X s((q i).1, (q i).2)) →
      Set.InjOn lab S → (∀ i ∈ S, lab i ∈ ccwHullSides X) →
      (∀ i ∈ S, ‖sideDir (q i) - sideDir (lab i)‖ ≤ 1 * diam X ^ (-(3 / 2 * scaleExp m))) →
      (S.card : ℝ) ≤ ε1 * diam X) :
    ∀ m ≤ K, ((hopProcess hX (hopEmit X)).fin.toFinset.filter (fun G =>
      (hopProcess hX (hopEmit X)).Emits m G ∧ ¬ (hopProcess hX (hopEmit X)).Emits (m - 1) G ∧
      hopPrimBad X m G ∧ ∀ s ∈ (hopProcess hX (hopEmit X)).arrivals (m - 1) G,
        ¬ (hopProcess hX (hopEmit X)).badAt (hopSrcBad X) (hopPrimBad X) (m - 1) s)).card ≤
      ⌊ε1 * diam X⌋₊ := by
  set P := hopProcess hX (hopEmit X) with hP
  have hemit := hopEmit_mem' hsides
  intro m hm
  set S := P.fin.toFinset.filter (fun G => P.Emits m G ∧ ¬ P.Emits (m - 1) G ∧
      hopPrimBad X m G ∧ ∀ s ∈ P.arrivals (m - 1) G,
        ¬ P.badAt (hopSrcBad X) (hopPrimBad X) (m - 1) s) with hS
  have hmem : ∀ G ∈ S, G ∈ exceptionalFaces X ∧ P.Emits m G ∧ ¬ P.Emits (m - 1) G ∧
      hopPrimBad X m G ∧ ∀ s ∈ P.arrivals (m - 1) G,
        ¬ P.badAt (hopSrcBad X) (hopPrimBad X) (m - 1) s := by
    intro G hG
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hG
    exact ⟨(Set.Finite.mem_toFinset _).1 h1, h2⟩
  have hpos : ∀ G ∈ S, 1 ≤ m := by
    intro G hG
    by_contra h0
    obtain ⟨-, h1, -⟩ := hmem G hG
    rw [show m = 0 by omega] at h1
    exact P.not_emits_zero G h1
  apply Nat.le_floor
  refine hlong m hm S (hopEmit X) (fun G => P.labelAt K (Sum.inr G))
    (hopEmit_injOn hX hsides (fun G hG => (hmem G hG).1)) (fun G hG => ?_) ?_ ?_ ?_
  · obtain ⟨hG, -, -, hprim, -⟩ := hmem G hG
    have h1 := dist_eq_one_of_mem_orientedSides (hemit G hG)
    refine ⟨fun h => ?_, ?_, ?_⟩
    · rw [h, dist_self] at h1; norm_num at h1
    · rw [Sym2.eq_swap]; exact isTerminal_of_mem_orientedSides hX htri hG (hemit G hG)
    · unfold hopPrimBad cutB at hprim; linarith
  · intro G hG G' hG' he
    obtain ⟨-, h1, h0, -⟩ := hmem G hG
    obtain ⟨-, h1', h0', -⟩ := hmem G' hG'
    exact P.labelAt_injOn_firstEmit (P.emits_mono hm h1) (P.emits_mono hm h1')
      (P.firstEmit_eq h1 h0) (P.firstEmit_eq h1' h0') he
  · intro G hG
    obtain ⟨-, h1, -⟩ := hmem G hG
    have := P.labelAt_mem (t := Sum.inr G) (P.emits_mono hm h1) (fun p hp => by simp at hp)
    exact (Finset.mem_filter.1 this).1
  · intro G hG
    obtain ⟨hGe, h1, h0, -, hgin⟩ := hmem G hG
    have hm1 := hpos G hG
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at h0 hgin
    have hin : ∀ s ∈ P.arrivals k G, TokBound hX K k s := by
      intro s hs'
      have hts := P.timed_of_mem_arrivals hs'
      refine tokenBound hX htri hsides hR hD1 hstep h1920 hopp hdist k (by omega) s hts ?_
        (hop_arrivals_mem hX hs').1 (hop_arrivals_mem hX hs').2
      show ¬ P.badAt (hopSrcBad X) (hopPrimBad X) K s
      rw [P.badAt_stable _ _ (show k ≤ K by omega) hts]
      exact hgin s hs'
    obtain ⟨hd, -⟩ := hop_emission_round hX htri hsides (by omega : k < K) hR hopp hdist hGe
      h1 h0 hin
    rw [one_mul]
    exact hd.trans (hstep k (by omega)).1

include htri hsides in
/-- The tokens reaching caps: their exit edges are initial unit edges of `X × X` whose tracks end
on a cap. -/
lemma capTokens_facts {j : ℕ} {t : (Plane × Plane) ⊕ Set ℂ}
    (ht : t ∈ (hopProcess hX (hopEmit X)).capTokens j) :
    exitEdge (hopEmit X) t ∈ X ×ˢ X ∧ Initial X (exitEdge (hopEmit X) t) ∧
      dist (exitEdge (hopEmit X) t).1 (exitEdge (hopEmit X) t).2 = 1 ∧
      hopDest X (exitEdge (hopEmit X) t) = .cap ∧
      (hopProcess hX (hopEmit X)).Timed j t ∧ (hopProcess hX (hopEmit X)).dest t = .cap ∧
      (∀ p, t = Sum.inl p → p ∈ unitHullSides X) ∧
      (∀ G, t = Sum.inr G → G ∈ exceptionalFaces X) := by
  rcases t with p | G
  · simp only [TokenProcess.capTokens, Finset.inl_mem_disjSum, Finset.mem_filter] at ht
    obtain ⟨hp, hc⟩ := ht
    refine ⟨(Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).1, initial_of_mem_unitHullSides hp,
      (Finset.mem_filter.1 hp).2, hc, True.intro, hc, fun p' h => ?_, fun G h => by simp at h⟩
    cases h; exact hp
  · simp only [TokenProcess.capTokens, Finset.inr_mem_disjSum, Finset.mem_filter] at ht
    obtain ⟨hGf, hc, he⟩ := ht
    have hG : G ∈ exceptionalFaces X := (Set.Finite.mem_toFinset _).1 hGf
    have hm := hopEmit_mem' hsides G hG
    have hX2 := mem_of_mem_orientedSides hm
    refine ⟨Finset.mem_product.2 ⟨hX2.2, hX2.1⟩, initial_of_mem_orientedSides hX htri hG hm,
      ?_, hc, he, hc, fun p h => by simp at h, fun G' h => ?_⟩
    · rw [dist_comm]; exact dist_eq_one_of_mem_orientedSides hm
    · cases h; exact hG

/-- The bad tokens among a finite family of tokens are at most the number of bad tokens. -/
lemma card_filter_bad_le {X : Finset Plane} (P : TokenProcess X)
    (bad : (Plane × Plane) ⊕ Set ℂ → Prop) (T : Finset ((Plane × Plane) ⊕ Set ℂ))
    (hT : ∀ t ∈ T, (∀ p, t = Sum.inl p → p ∈ unitHullSides X) ∧
      (∀ G, t = Sum.inr G → G ∈ P.fin.toFinset)) :
    (T.filter bad).card ≤ P.numBad bad := by
  unfold TokenProcess.numBad
  rw [← Finset.card_disjSum]
  apply Finset.card_le_card
  intro t ht
  obtain ⟨htT, hb⟩ := Finset.mem_filter.1 ht
  rcases t with p | G
  · simp only [Finset.inl_mem_disjSum, Finset.mem_filter]
    exact ⟨(hT _ htT).1 p rfl, hb⟩
  · simp only [Finset.inr_mem_disjSum, Finset.mem_filter]
    exact ⟨(hT _ htT).2 G rfl, hb⟩

include htri hsides in
/-- **The discarded tokens** (§9.2): at most `S + 2^K · 2 ε₁ D`, where `S` counts the sources on
long tracks. -/
lemma hop_numBad_le {K : ℕ} {O : Plane} {η' : ℝ}
    (hR : RoundData X O (diam X) η' (100 * diam X ^ (-(2 / 9 : ℝ)))) (hD1 : 1 ≤ diam X)
    (hstep : ∀ k < K,
      √(8 * (errB (diam X) k + 4 * (disB (diam X) k + 7) / diam X + roundErr (diam X))) +
          4 * (disB (diam X) k + 7) / diam X + roundErr (diam X) ≤ errB (diam X) (k + 1) ∧
        disB (diam X) k + 8 + cutB (diam X) (k + 1) ≤ disB (diam X) (k + 1))
    (h1920 : diam X ^ (19 / 20 : ℝ) ≤ disB (diam X) 0)
    (hopp : ∀ G ∈ exceptionalFaces X, (faceSize X G = 5 ∨ faceSize X G = 7) → ∀ e : ℂ,
      ‖e‖ = 1 → ∀ δ : ℝ, 0 ≤ δ → ∀ M ⊆ orientedSides X G, faceSize X G ≤ 2 * M.card + 1 →
      (∀ ab ∈ M, ‖(ab.2 - ab.1) - e‖ ≤ δ) →
      ∃ ab ∈ orientedSides X G, ‖(ab.1 - ab.2) - e‖ ^ 2 ≤ 8 * δ)
    (hdist : ∀ F ∈ exceptionalFaces X, ∀ ab ∈ orientedSides X F, ∀ ab' ∈ orientedSides X F,
      dist ab.1 ab'.1 ≤ faceSize X F) {ε1 : ℝ}
    (hlong : ∀ m ≤ K, ∀ (S : Finset (Set ℂ)) (q lab : Set ℂ → Plane × Plane), Set.InjOn q S →
      (∀ i ∈ S, (q i).1 ≠ (q i).2 ∧ IsTerminal X s((q i).1, (q i).2) ∧
        1 / 2 * diam X ^ (1 - scaleExp m) ≤ srcLen X s((q i).1, (q i).2)) →
      Set.InjOn lab S → (∀ i ∈ S, lab i ∈ ccwHullSides X) →
      (∀ i ∈ S, ‖sideDir (q i) - sideDir (lab i)‖ ≤ 1 * diam X ^ (-(3 / 2 * scaleExp m))) →
      (S.card : ℝ) ≤ ε1 * diam X)
    (hshort : (((unitHullSides X).filter
      (fun p => diam X ^ (19 / 20 : ℝ) ≤ srcLen X s(p.1, p.2))).card : ℝ) ≤ ε1 * diam X) :
    ((hopProcess hX (hopEmit X)).numBad (hopBad hX K) : ℝ) ≤ (((unitHullSides X).filter
      (fun p => diam X ^ (19 / 20 : ℝ) ≤ srcLen X s(p.1, p.2))).card : ℝ) +
        2 ^ K * (2 * ε1 * diam X) := by
  set P := hopProcess hX (hopEmit X) with hP
  have hc := P.card_badAt_le (hopSrcBad X) (hopPrimBad X) K ⌊ε1 * diam X⌋₊
    (primBad_count hX htri hsides hR hD1 hstep h1920 hopp hdist hlong)
  have e1 : (unitHullSides X).filter (hopSrcBad X) = (unitHullSides X).filter
      (fun p => diam X ^ (19 / 20 : ℝ) ≤ srcLen X s(p.1, p.2)) := rfl
  rw [e1] at hc
  set S := (unitHullSides X).filter (fun p => diam X ^ (19 / 20 : ℝ) ≤ srcLen X s(p.1, p.2))
  have e2 : (unitHullSides X).filter (fun p => hopBad hX K (Sum.inl p)) = S := by
    refine Finset.filter_congr (fun p _ => ?_)
    unfold hopBad
    rw [P.badAt_inl]
    rfl
  unfold TokenProcess.numBad
  rw [e2]
  have hc' := (Nat.cast_le (α := ℝ)).2 hc
  rw [Nat.cast_mul, Nat.cast_sub Nat.one_le_two_pow, Nat.cast_add] at hc'
  simp only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] at hc'
  have hB : (⌊ε1 * diam X⌋₊ : ℝ) ≤ ε1 * diam X := Nat.floor_le (by nlinarith)
  have h2K : (1 : ℝ) ≤ 2 ^ K := one_le_pow₀ (by norm_num)
  have hF : (((P.fin.toFinset.filter (fun G => hopBad hX K (Sum.inr G))).card : ℕ) : ℝ) ≤
      ((2 : ℝ) ^ K - 1) * (S.card + ⌊ε1 * diam X⌋₊) := hc'
  have h3 : ((2 : ℝ) ^ K - 1) * (S.card + ⌊ε1 * diam X⌋₊) ≤ ((2 : ℝ) ^ K - 1) * (2 * ε1 * diam X) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h4 : ((2 : ℝ) ^ K - 1) * (2 * ε1 * diam X) ≤ 2 ^ K * (2 * ε1 * diam X) := by
    have : 0 ≤ 2 * ε1 * diam X := by nlinarith
    nlinarith
  push_cast
  linarith

include htri hsides in
/-- **The emission lemma for one configuration** (§9.1–§9.3).  Under the schedule inequalities,
the geometric inputs at the exceptional faces, the bound on long sources, the long-exit bound in
every round and the cap capacity, the exit edges `hopEmit X` and the discarded tokens `hopBad`
satisfy the conclusion of `exists_hopEmission`. -/
theorem hopEmission_of_data {K : ℕ} {η : ℝ} (hη : 0 < η) {O : Plane} {η' : ℝ}
    (hR : RoundData X O (diam X) η' (100 * diam X ^ (-(2 / 9 : ℝ)))) (hD1 : 1 ≤ diam X)
    (hstep : ∀ k < K,
      √(8 * (errB (diam X) k + 4 * (disB (diam X) k + 7) / diam X + roundErr (diam X))) +
          4 * (disB (diam X) k + 7) / diam X + roundErr (diam X) ≤ errB (diam X) (k + 1) ∧
        disB (diam X) k + 8 + cutB (diam X) (k + 1) ≤ disB (diam X) (k + 1))
    (h1920 : diam X ^ (19 / 20 : ℝ) ≤ disB (diam X) 0)
    (hopp : ∀ G ∈ exceptionalFaces X, (faceSize X G = 5 ∨ faceSize X G = 7) → ∀ e : ℂ,
      ‖e‖ = 1 → ∀ δ : ℝ, 0 ≤ δ → ∀ M ⊆ orientedSides X G, faceSize X G ≤ 2 * M.card + 1 →
      (∀ ab ∈ M, ‖(ab.2 - ab.1) - e‖ ≤ δ) →
      ∃ ab ∈ orientedSides X G, ‖(ab.1 - ab.2) - e‖ ^ 2 ≤ 8 * δ)
    (hdist : ∀ F ∈ exceptionalFaces X, ∀ ab ∈ orientedSides X F, ∀ ab' ∈ orientedSides X F,
      dist ab.1 ab'.1 ≤ faceSize X F)
    (herrK : errB (diam X) K ≤ 1 / 100) (hdisK : disB (diam X) K ≤ diam X / 100)
    (h7 : 7 ≤ diam X ^ (1 - scaleExp K / 8))
    (hshort : (((unitHullSides X).filter
      (fun p => diam X ^ (19 / 20 : ℝ) ≤ srcLen X s(p.1, p.2))).card : ℝ) ≤
        η / (4 * 2 ^ K) * diam X)
    (hlong : ∀ m ≤ K, ∀ (S : Finset (Set ℂ)) (q lab : Set ℂ → Plane × Plane), Set.InjOn q S →
      (∀ i ∈ S, (q i).1 ≠ (q i).2 ∧ IsTerminal X s((q i).1, (q i).2) ∧
        1 / 2 * diam X ^ (1 - scaleExp m) ≤ srcLen X s((q i).1, (q i).2)) →
      Set.InjOn lab S → (∀ i ∈ S, lab i ∈ ccwHullSides X) →
      (∀ i ∈ S, ‖sideDir (q i) - sideDir (lab i)‖ ≤ 1 * diam X ^ (-(3 / 2 * scaleExp m))) →
      (S.card : ℝ) ≤ η / (4 * 2 ^ K) * diam X)
    (hcap : ∀ (S : Finset ((Plane × Plane) ⊕ Set ℂ))
      (q lab : (Plane × Plane) ⊕ Set ℂ → Plane × Plane), Set.InjOn q S → Set.InjOn lab S →
      (∀ i ∈ S, q i ∈ X ×ˢ X ∧ Initial X (q i) ∧ dist (q i).1 (q i).2 = 1 ∧
        hopDest X (q i) = .cap) →
      (∀ i ∈ S, lab i ∈ unitHullSides X ∧
        ‖sideDir (q i) - sideDir (lab i)‖ ≤ diam X ^ (-(3 / 2 * scaleExp K)) ∧
        dist (lab i).1 (hopEnd X (q i)).1 ≤ diam X ^ (1 - scaleExp K)) →
      (S.card : ℝ) ≤ 2 * (returnExcess X : ℝ) / 3 + η / 4 * diam X) :
    ∃ (emit : Set ℂ → Plane × Plane) (bad : (Plane × Plane) ⊕ Set ℂ → Prop),
      (∀ G ∈ exceptionalFaces X, (toC (emit G).2, toC (emit G).1) ∈ orientedSides X G) ∧
      (∀ F ∈ exceptionalFaces X, (faceSize X F : ℝ) ≤ diam X ^ (1 - scaleExp K / 8) →
        ∀ G, Sum.inr G ∈ ((hopProcess hX emit).arrivals K F).filter (fun t => ¬ bad t) →
          ∃ ℓ ∈ unitHullSides X, ‖sideDir (emit G) - sideDir ℓ‖ ≤ 1 / 100 ∧
            dist ℓ.1 (hopEnd X (emit G)).1 ≤ diam X / 100) ∧
      (∀ F ∈ exceptionalFaces X, diam X ^ (1 - scaleExp K / 8) < faceSize X F →
        ∃ lab : (Plane × Plane) ⊕ Set ℂ → Plane × Plane,
          Set.InjOn lab (((hopProcess hX emit).arrivals K F).filter (fun t => ¬ bad t)) ∧
          ∀ t ∈ ((hopProcess hX emit).arrivals K F).filter (fun t => ¬ bad t),
            lab t ∈ unitHullSides X ∧
            dist (lab t).1 (hopEnd X (exitEdge emit t)).1 ≤ diam X ^ (1 - scaleExp K)) ∧
      ((hopProcess hX emit).capArr (K + 1) : ℝ) ≤
        2 * (returnExcess X : ℝ) / 3 + η * diam X ∧
      ((hopProcess hX emit).numBad bad : ℝ) ≤ (((unitHullSides X).filter
        (fun p => diam X ^ (19 / 20 : ℝ) ≤ srcLen X s(p.1, p.2))).card : ℝ) + η * diam X := by
  set P := hopProcess hX (hopEmit X) with hP
  have hemit := hopEmit_mem' hsides
  have hTB := tokenBound hX htri hsides hR hD1 hstep h1920 hopp hdist K le_rfl
  have hD0 : 0 < diam X := by linarith
  have h2K : (1 : ℝ) ≤ 2 ^ K := one_le_pow₀ (by norm_num)
  have hε1 : 0 ≤ η / (4 * 2 ^ K) := by positivity
  have hε1le : η / (4 * 2 ^ K) ≤ η / 4 :=
    div_le_div_of_nonneg_left hη.le (by norm_num) (by linarith)
  have hprod : (2 : ℝ) ^ K * (2 * (η / (4 * 2 ^ K)) * diam X) = η / 2 * diam X := by
    field_simp; ring
  have hnum := hop_numBad_le hX htri hsides hR hD1 hstep h1920 hopp hdist hlong hshort
  rw [hprod] at hnum
  refine ⟨hopEmit X, hopBad hX K, hemit, ?_, ?_, ?_, ?_⟩
  · intro F hF _ G hGm
    obtain ⟨hGa, hgood⟩ := Finset.mem_filter.1 hGm
    have hmem := hop_arrivals_mem hX hGa
    have hTk := hTB _ (P.timed_of_mem_arrivals hGa) hgood hmem.1 hmem.2
    exact ⟨P.labelAt K (Sum.inr G), P.labelAt_mem (P.timed_of_mem_arrivals hGa) hmem.1,
      hTk.1.trans herrK, hTk.2.trans hdisK⟩
  · intro F hF hFl
    have hnot : ∀ i, ¬ P.Emits i F := by
      intro i hi
      have h57 := P.faceSize_of_emits hi
      have : (faceSize X F : ℝ) ≤ 7 := by rcases h57 with h | h <;> rw [h] <;> norm_num
      linarith
    refine ⟨P.labelAt K, (P.labelAt_injOn hnot).mono
      (fun t ht => (Finset.mem_filter.1 ht).1), fun t ht => ?_⟩
    obtain ⟨hta, hgood⟩ := Finset.mem_filter.1 ht
    have hmem := hop_arrivals_mem hX hta
    have hTk := hTB _ (P.timed_of_mem_arrivals hta) hgood hmem.1 hmem.2
    exact ⟨P.labelAt_mem (P.timed_of_mem_arrivals hta) hmem.1, hTk.2⟩
  · rw [P.capArr_succ_eq_card, ← Finset.card_filter_add_card_filter_not (hopBad hX K)]
    push_cast
    have hinj2 : Set.InjOn (P.labelAt K) ↑((P.capTokens K).filter (fun t => ¬ hopBad hX K t)) :=
      (P.labelAt_injOn_cap K).mono (fun t ht => by
        have f := capTokens_facts hX htri hsides (Finset.mem_filter.1 ht).1
        exact ⟨f.2.2.2.2.1, f.2.2.2.2.2.1⟩)
    have hgoodcap := hcap ((P.capTokens K).filter (fun t => ¬ hopBad hX K t))
      (exitEdge (hopEmit X)) (P.labelAt K)
      (exitEdge_injOn hX hemit (fun t ht =>
        (capTokens_facts hX htri hsides (Finset.mem_filter.1 ht).1).2.2.2.2.2.2))
      hinj2
      (fun t ht => by
        have f := capTokens_facts hX htri hsides (Finset.mem_filter.1 ht).1
        exact ⟨f.1, f.2.1, f.2.2.1, f.2.2.2.1⟩)
      (fun t ht => by
        have f := capTokens_facts hX htri hsides (Finset.mem_filter.1 ht).1
        have hTk := hTB t f.2.2.2.2.1 (Finset.mem_filter.1 ht).2 f.2.2.2.2.2.2.1
          f.2.2.2.2.2.2.2
        exact ⟨P.labelAt_mem f.2.2.2.2.1 f.2.2.2.2.2.2.1, hTk.1, hTk.2⟩)
    have hbadcap : (((P.capTokens K).filter (hopBad hX K)).card : ℝ) ≤
        P.numBad (hopBad hX K) := by
      exact_mod_cast card_filter_bad_le P _ _ (fun t ht => by
        have f := capTokens_facts hX htri hsides ht
        exact ⟨f.2.2.2.2.2.2.1, fun G hG =>
          (Set.Finite.mem_toFinset _).2 (f.2.2.2.2.2.2.2 G hG)⟩)
    have : η / (4 * 2 ^ K) * diam X ≤ η / 4 * diam X := mul_le_mul_of_nonneg_right hε1le hD0.le
    linarith
  · have : 0 ≤ η * diam X := by positivity
    linarith

end Main

/-- **The emission lemma** (`exists_hopEmission` of `Stability`, §9.1–§9.3 of the
Verification Guide), proved from the cap capacity `good_cap_tokens_le` and the proved ingredients:
the schedule, the almost-opposite edges at pentagons and heptagons, the label bookkeeping, the
long-exit bound `long_labelled_exits` and the short-source theorem `short_unit_sources`. -/
theorem hopEmission_main (K : ℕ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, ∀ hX : IsOptimal n X,
      ¬ HasUnitTriangle X →
      ∃ (emit : Set ℂ → Plane × Plane) (bad : (Plane × Plane) ⊕ Set ℂ → Prop),
        (∀ G ∈ exceptionalFaces X, (toC (emit G).2, toC (emit G).1) ∈ orientedSides X G) ∧
        (∀ F ∈ exceptionalFaces X, (faceSize X F : ℝ) ≤ diam X ^ (1 - scaleExp K / 8) →
          ∀ G, Sum.inr G ∈ ((hopProcess hX.1.2 emit).arrivals K F).filter (fun t => ¬ bad t) →
            ∃ ℓ ∈ unitHullSides X, ‖sideDir (emit G) - sideDir ℓ‖ ≤ 1 / 100 ∧
              dist ℓ.1 (hopEnd X (emit G)).1 ≤ diam X / 100) ∧
        (∀ F ∈ exceptionalFaces X, diam X ^ (1 - scaleExp K / 8) < faceSize X F →
          ∃ lab : (Plane × Plane) ⊕ Set ℂ → Plane × Plane,
            Set.InjOn lab (((hopProcess hX.1.2 emit).arrivals K F).filter (fun t => ¬ bad t)) ∧
            ∀ t ∈ ((hopProcess hX.1.2 emit).arrivals K F).filter (fun t => ¬ bad t),
              lab t ∈ unitHullSides X ∧
              dist (lab t).1 (hopEnd X (exitEdge emit t)).1 ≤ diam X ^ (1 - scaleExp K)) ∧
        ((hopProcess hX.1.2 emit).capArr (K + 1) : ℝ) ≤
          2 * (returnExcess X : ℝ) / 3 + η * diam X ∧
        ((hopProcess hX.1.2 emit).numBad bad : ℝ) ≤ (((unitHullSides X).filter
          (fun p => diam X ^ (19 / 20 : ℝ) ≤ srcLen X s(p.1, p.2))).card : ℝ) + η * diam X := by
  have hε1 : 0 < η / (4 * 2 ^ K) := by positivity
  have hlongs := (Finset.eventually_all (Finset.range (K + 1))).2 (fun m _ =>
    long_labelled_exits (c := 1 / 2) (M := 1) (scaleExp_pos m) (scaleExp_le m) (by norm_num) hε1)
  have hsched := tendsto_minDiam.eventually (eventually_schedule K)
  have h7 := tendsto_minDiam.eventually (eventually_const_mul_rpow_le 7 (α := 0)
    (β := 1 - scaleExp K / 8) (by linarith [scaleExp_le K]))
  filter_upwards [hlongs, hsched, h7, short_unit_sources _ hε1,
    good_cap_tokens_le (scaleExp_pos K) (scaleExp_le K) (by positivity : (0 : ℝ) < η / 4),
    eventually_roundData_rate, exceptionalFace_unitPolygon_sides, exists_almostOpposite_side,
    exceptionalFace_orientedSides_dist_le]
    with n hlong hsch h7 hshort hcap hround hpoly hopp hdist
  intro hfm X hX htri
  rw [← hX.diam_eq] at hsch h7
  rw [Real.rpow_zero, mul_one] at h7
  obtain ⟨hD1, hstep, herrK, hdisK⟩ := hsch
  obtain ⟨O, η', hR⟩ := hround X hX
  have hsides : ∀ G ∈ exceptionalFaces X, (orientedSides X G).Nonempty := by
    intro G hG
    obtain ⟨hNZ, Q, -, hall⟩ := hpoly hfm X hX G hG
    exact ⟨_, hall 0⟩
  have h1920 : diam X ^ (19 / 20 : ℝ) ≤ disB (diam X) 0 :=
    Real.rpow_le_rpow_of_exponent_le hD1 (by linarith [scaleExp_le 0])
  exact hopEmission_of_data hX.1.2 htri hsides hη hR hD1 hstep h1920 (hopp hfm X hX)
    (hdist hfm X hX) herrK hdisK h7 (hshort hfm X hX htri)
    (fun m hm S q lab => hlong m (Finset.mem_range.2 (by omega)) hfm X hX htri S q lab)
    (fun S q lab => hcap hfm X hX htri S q lab)

end Erdos99

end

end HopEmissionMain

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `Stability`
-/

section Stability

/-!
# WP7 output: stability (Verification Guide §9.4)

This file derives the WP7 output `stability_bounds` from

* `lockingDefect_nonneg` (output of WP4: `Δ ≥ 0`; proved in `StressLocking` from
  `locking_count`, hence resting on the open fan theorem `lifted_form_no_negative_plane`), and
* `cap_landing` (`CapLanding`, **proved** from `Δ ≥ 0` and the cap geometry: all but `ε D`
  of the good tokens reaching caps arrive through forward sides of the caps of non-unit hull
  sides).

`exists_hopEmission` (the emissions of the track-following token process `hopProcess` of
§9.1–§9.3: a choice of almost-opposite exit edges at the exceptional faces and a set of discarded
tokens, such that the emitted good tokens arriving at small faces carry source labels with nearly
the direction of their exit edge and close to the far end of their track, the good tokens at large
faces carry distinct local source labels, and cap arrivals and discarded tokens are controlled) is
**proved** (`hopEmission_main`, `HopEmissionMain`) from the cap capacity
`good_cap_tokens_le`, which is proved (`CapLanding`) from `cap_landing` and the return
capacities of §8.3.

`exists_hopRouting` (the routing: nearly parallel exit directions at small receivers, two-arc
covering at large receivers) is **proved** from `exists_hopEmission`, the track locality
`dist_hopEnd_le`, tangent regularity `sideDir_sub_le`, roundness and `large_face_two_balls`.

`exists_prunedTokenProcess` (the abstract pruned token process) is **proved** from
`exists_hopRouting` and the incidence properties `hopProcess_incidences`, `hopProcess_lostArr`.

`exists_smallMarkedTokenProcess` (the same with no discarded tokens) is **proved** from it by
pruning (`exists_smallMarkedTokenProcess_of_pruned`).

`exists_markedTokenProcess` (marked arrivals at *every* exceptional face) is **proved** from it and
`Δ ≥ 0` by sending the large receivers to the loss bin (`exists_markedTokenProcess_of_small`).

`exists_tokenProcess` (arrivals within the local capacities) is **proved** from
`exists_markedTokenProcess` and the local capacities at the faces
(`exists_tokenProcess_of_marked`, `exceptionalFace_marked_card_le`).

`exists_tokenLedger` (for every depth `K` there is a loss budget `B(D) = o(D)` such that
eventually every configuration carries a `TokenLedger` of depth `K`) is now **proved** from
`exists_tokenProcess`, the exact conservation law of the process (`TokenProcess.toLedger`), the
proved short-source theorem `short_unit_sources` (which pays for the sources on long tracks), and
the uniformization lemma `exists_littleO_of_forall_eventually`.
-/

open scoped BigOperators Real
open Filter Topology EstablishedExternalResults

@[expose] public noncomputable section

open Classical

namespace Erdos99

open Propagation

/-! ## The geometric inputs and the WP7 output -/

/-- **`Δ ≥ 0`** (output of WP4, from first-order locking, Corollary 2.5 and the exact incidence
identities of WP3).  **Proved** as `lockingDefect_nonneg_eventually` (`StressLocking`) from
`locking_count`; it still rests on the open lemma `first_order_locking` (§7 of the Verification
Guide), the main blocker of the whole route. -/
lemma lockingDefect_nonneg :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      0 ≤ lockingDefect X :=
  lockingDefect_nonneg_eventually

/-- **The emissions of the track-following token process of depth `K + 1`** (§9.1–§9.3 of the
Verification Guide), with the loss tolerance `η D`.  Let `e = e_K` and `B = D^{1 - e/8}`.  In the
track-following process `hopProcess` (`HopProcess`) every source hops along its track to the
exceptional face beyond its far end (or to a cap), and every exceptional face `G` emits through an
exit edge `emit G`.

Eventually every configuration admits a choice of exit edges `emit`, each the reversal of an
oriented side of its face (the *almost-opposite edge* of §9.1), and a set of *bad* (discarded)
tokens, such that, among the **good** tokens arriving after `K + 1` rounds,

* every **emitted** token arriving at an exceptional face with at most `B` sides carries a source
  label: a unit hull side whose direction is within `1/100` of the direction of the exit edge
  (*outgoing face vectors are near the source tangent*) and which starts within `D / 100` of the
  far end of the token's track (*each live token has a route to its source of controlled length*);
* the tokens arriving at each exceptional face with more than `B` sides carry pairwise distinct
  source labels (unit hull sides), each starting within `Λ_K = D^{1 - e_K}` of the far end of
  the token's track (locality);
* at most `2ρ/3 + η D` tokens have reached caps;
* the bad tokens number at most `η D` beyond the number of sources on long tracks (at least
  `D^{19/20}` rhombi).

The two-arc covering at the large faces then follows (`large_face_two_balls`, proved). The tokens
coming directly from the sources need no condition at the small faces: they are
handled by `exists_hopRouting` (their label is the source itself, by locality `dist_hopEnd_le`).

**Proved** as `hopEmission_main` (`HopEmissionMain`): the exit edges are `hopEmit X`
(the reversed side closest to the tangent of the nearest unit hull side), the angle errors and
displacements propagate along the scales `Λ_j = D^{1 - e_j}` (`tokenBound`, via the almost-opposite
sides of pentagons and heptagons, §8.2), labels never split (`TokenLabels`), the long emitted
tracks are few (`long_labelled_exits`), and the caps are controlled by `good_cap_tokens_le`
(proved from the landing lemma `cap_landing` and the return capacities of §8.3). -/
lemma exists_hopEmission (K : ℕ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, ∀ hX : IsOptimal n X,
      ¬ HasUnitTriangle X →
      ∃ (emit : Set ℂ → Plane × Plane) (bad : (Plane × Plane) ⊕ Set ℂ → Prop),
        (∀ G ∈ exceptionalFaces X, (toC (emit G).2, toC (emit G).1) ∈ orientedSides X G) ∧
        (∀ F ∈ exceptionalFaces X, (faceSize X F : ℝ) ≤ diam X ^ (1 - scaleExp K / 8) →
          ∀ G, Sum.inr G ∈ ((hopProcess hX.1.2 emit).arrivals K F).filter (fun t => ¬ bad t) →
            ∃ ℓ ∈ unitHullSides X, ‖sideDir (emit G) - sideDir ℓ‖ ≤ 1 / 100 ∧
              dist ℓ.1 (hopEnd X (emit G)).1 ≤ diam X / 100) ∧
        (∀ F ∈ exceptionalFaces X, diam X ^ (1 - scaleExp K / 8) < faceSize X F →
          ∃ lab : (Plane × Plane) ⊕ Set ℂ → Plane × Plane,
            Set.InjOn lab (((hopProcess hX.1.2 emit).arrivals K F).filter (fun t => ¬ bad t)) ∧
            ∀ t ∈ ((hopProcess hX.1.2 emit).arrivals K F).filter (fun t => ¬ bad t),
              lab t ∈ unitHullSides X ∧
              dist (lab t).1 (hopEnd X (exitEdge emit t)).1 ≤ diam X ^ (1 - scaleExp K)) ∧
        ((hopProcess hX.1.2 emit).capArr (K + 1) : ℝ) ≤
          2 * (returnExcess X : ℝ) / 3 + η * diam X ∧
        ((hopProcess hX.1.2 emit).numBad bad : ℝ) ≤ (((unitHullSides X).filter
          (fun p => diam X ^ (19 / 20 : ℝ) ≤ srcLen X s(p.1, p.2))).card : ℝ) + η * diam X :=
  hopEmission_main K η hη

/-- **The routing of the track-following token process of depth `K + 1`** (§9.1–§9.3 of the
Verification Guide), with the loss tolerance `η D`.  Let `e = e_K` and `B = D^{1 - e/8}`.  In the
track-following process `hopProcess` (`HopProcess`) every source hops along its track to the
exceptional face beyond its far end (or to a cap), and every exceptional face `G` emits through an
exit edge `emit G`; the track incidences it uses are automatically distinct and every token enters
its receiver with exactly the direction of its exit edge (`hopProcess_incidences`, proved), and no
token is lost (`hopProcess_lostArr`, proved).

For some constant `C ≥ 0`, eventually every configuration admits a choice of exit edges `emit`,
each the reversal of an oriented side of its face (the *almost-opposite edge* of §9.1), and a set
of *bad* (discarded) tokens, such that, among the **good** tokens arriving after `K + 1` rounds,

* at every exceptional face with at most `B` sides the exit edges of the arriving tokens all have
  directions with projection at least `19/20` on one unit vector (the positive tangent of the
  sources of that receiver);
* the tokens arriving at each exceptional face with more than `B` sides carry pairwise distinct
  source labels (unit hull sides) whose starting points lie in two balls of radius
  `C D^{1 - e/4}` (the two-arc covering of §9.3, `exceptionalFace_two_balls`);
* at most `2ρ/3 + η D` tokens have reached caps;
* the bad tokens number at most `η D` beyond the number of sources on long tracks (at least
  `D^{19/20}` rhombi; these are paid for by the proved short-source theorem
  `short_unit_sources`).

**Proved** from `exists_hopEmission` (applied with `η / 2`), with `C = 1`: the sources on long
tracks are added to the bad tokens (they are few, `short_unit_sources`); a good source arriving at a small face is
its own label and starts within `D^{19/20} ≤ D / 100` of the far end of its track
(`dist_hopEnd_le`); the far ends of the tracks arriving at one face are within its number of
sides `≤ B ≤ D / 100` of each other (`exceptionalFace_orientedSides_dist_le`); and labels starting
close together have nearly equal directions because the hull is nearly circular
(`eventually_roundData`, `marked_of_labels`).  At the large faces, the labels start within
`Λ_K + 1` of the closure of the face, hence in two balls of radius `D^{1 - e_K/4}`
(`large_face_two_balls`). -/
theorem exists_hopRouting (K : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, ∀ hX : IsOptimal n X,
      ¬ HasUnitTriangle X →
      ∃ (emit : Set ℂ → Plane × Plane) (bad : (Plane × Plane) ⊕ Set ℂ → Prop),
        (∀ G ∈ exceptionalFaces X, (toC (emit G).2, toC (emit G).1) ∈ orientedSides X G) ∧
        (∀ F ∈ exceptionalFaces X, (faceSize X F : ℝ) ≤ diam X ^ (1 - scaleExp K / 8) →
          ∃ e : ℂ, ‖e‖ = 1 ∧
            ∀ t ∈ ((hopProcess hX.1.2 emit).arrivals K F).filter (fun t => ¬ bad t),
              19 / 20 ≤ inner ℝ (toC (exitEdge emit t).2 - toC (exitEdge emit t).1) e) ∧
        (∀ F ∈ exceptionalFaces X, diam X ^ (1 - scaleExp K / 8) < faceSize X F →
          ∃ (lab : (Plane × Plane) ⊕ Set ℂ → Plane × Plane) (c₀ c₁ : Plane),
            Set.InjOn lab (((hopProcess hX.1.2 emit).arrivals K F).filter (fun t => ¬ bad t)) ∧
            ∀ t ∈ ((hopProcess hX.1.2 emit).arrivals K F).filter (fun t => ¬ bad t),
              lab t ∈ unitHullSides X ∧
              (dist (lab t).1 c₀ ≤ C * diam X ^ (1 - scaleExp K / 4) ∨
                dist (lab t).1 c₁ ≤ C * diam X ^ (1 - scaleExp K / 4))) ∧
        ((hopProcess hX.1.2 emit).capArr (K + 1) : ℝ) ≤
          2 * (returnExcess X : ℝ) / 3 + η * diam X ∧
        ((hopProcess hX.1.2 emit).numBad bad : ℝ) ≤ (((unitHullSides X).filter
          (fun p => diam X ^ (19 / 20 : ℝ) ≤ srcLen X s(p.1, p.2))).card : ℝ) + η * diam X := by
  have hev := exists_hopEmission K (η / 2) (half_pos hη)
  refine ⟨1, zero_le_one, ?_⟩
  have hδ0 : (0 : ℝ) < 1 / 480000 := by norm_num
  have hE1 := tendsto_minDiam.eventually (eventually_mul_rpow_le 1 (α := 19 / 20)
    (δ := 1 / 100) (by norm_num) (by norm_num))
  have hE2 := tendsto_minDiam.eventually (eventually_mul_rpow_le 1 (α := 1 - scaleExp K / 8)
    (δ := 1 / 100) (by linarith [scaleExp_pos K]) (by norm_num))
  filter_upwards [hev, short_unit_sources (η / 2) (half_pos hη), eventually_roundData _ hδ0,
    exceptionalFace_orientedSides_dist_le, hE1, hE2, large_face_two_balls K]
    with n hn hshort hround hdist hE1 hE2 htwo
  intro hfm X hX htri
  rw [← hX.diam_eq] at hE1 hE2
  simp only [one_mul] at hE1 hE2
  obtain ⟨emit, bad, hemit, hsmall, hlarge, hcap, hbad⟩ := hn hfm X hX htri
  obtain ⟨O, η', δ, hR, hδ⟩ := hround X hX
  obtain ⟨bad', hbad'⟩ : ∃ b : (Plane × Plane) ⊕ Set ℂ → Prop, b = fun t => bad t ∨
      ∃ p, t = .inl p ∧ diam X ^ (19 / 20 : ℝ) ≤ srcLen X s(p.1, p.2) := ⟨_, rfl⟩
  have hsub : ∀ j F, ((hopProcess hX.1.2 emit).arrivals j F).filter (fun t => ¬ bad' t) ⊆
      ((hopProcess hX.1.2 emit).arrivals j F).filter (fun t => ¬ bad t) := by
    intro j F t ht
    simp only [Finset.mem_filter, hbad', not_or] at ht ⊢
    exact ⟨ht.1, ht.2.1⟩
  refine ⟨emit, bad', hemit, ?_, fun F hF hFl => ?_,
    hcap.trans (by have := hR.D_pos; nlinarith), ?_⟩
  · -- the small faces
    intro F hF hFs
    obtain ⟨-, hside⟩ := hopProcess_incidences hX.1.2 htri emit hemit K F
    have hlab : ∀ t ∈ ((hopProcess hX.1.2 emit).arrivals K F).filter (fun t => ¬ bad' t),
        ∃ ℓ ∈ unitHullSides X, ‖sideDir (exitEdge emit t) - sideDir ℓ‖ ≤ 1 / 100 ∧
          dist ℓ.1 (hopEnd X (exitEdge emit t)).1 ≤ diam X / 100 := by
      intro t ht
      obtain ⟨htA, htb⟩ := Finset.mem_filter.1 ht
      rcases t with p | G
      · have hp : p ∈ unitHullSides X := by
          simp only [hopProcess, TokenProcess.arrivals, Finset.inl_mem_disjSum,
            Finset.mem_filter] at htA
          exact htA.1
        refine ⟨p, hp, by simp [exitEdge], ?_⟩
        have hpX : p ∈ X ×ˢ X := (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).1
        have h1 := dist_hopEnd_le (X := X) hpX
        have hshort' : (srcLen X s(p.1, p.2) : ℝ) < diam X ^ (19 / 20 : ℝ) := by
          by_contra h
          rw [hbad'] at htb
          exact htb (Or.inr ⟨p, rfl, not_lt.1 h⟩)
        simp only [exitEdge, Sum.elim_inl, id]
        rw [dist_comm]
        linarith
      · exact hsmall F hF hFs G (hsub K F ht)
    choose! lab hlabU hlabd hlabp using hlab
    refine marked_of_labels hR _ (exitEdge emit) lab ?_ ?_ hlabd (b := 3 * diam X / 100) ?_ ?_
    · -- exit edges are unit edges
      intro t ht
      obtain ⟨htA, -⟩ := Finset.mem_filter.1 ht
      rcases t with p | G
      · simp only [hopProcess, TokenProcess.arrivals, Finset.inl_mem_disjSum,
          Finset.mem_filter] at htA
        simp only [exitEdge, Sum.elim_inl, id]
        rw [← dist_eq_norm, dist_comm]
        exact (Finset.mem_filter.1 htA.1).2
      · simp only [hopProcess, TokenProcess.arrivals, Finset.inr_mem_disjSum,
          Finset.mem_filter] at htA
        have hG : G ∈ exceptionalFaces X := (Set.Finite.mem_toFinset _).1 htA.1
        obtain ⟨-, hb, -⟩ := Finset.mem_filter.1 (hemit G hG)
        have hu := (mem_unitPairs.1 (Finset.mem_filter.1 hb).1).2.2
        rw [dist_toC] at hu
        simp only [exitEdge, Sum.elim_inr]
        rw [← dist_eq_norm]
        exact hu
    · intro t ht
      exact mem_ccwHullSides.1 (Finset.mem_filter.1 (hlabU t ht)).1
    · intro t ht t' ht'
      have e1 := (hside t (Finset.mem_filter.1 ht).1).1
      have e2 := (hside t' (Finset.mem_filter.1 ht').1).1
      rw [hopEntry_edge] at e1 e2
      have hd := hdist hfm X hX F hF _ e1 _ e2
      simp only [dist_toC] at hd
      calc dist (lab t).1 (lab t').1
          ≤ dist (lab t).1 (hopEnd X (exitEdge emit t)).1 +
            dist (hopEnd X (exitEdge emit t)).1 (hopEnd X (exitEdge emit t')).1 +
            dist (hopEnd X (exitEdge emit t')).1 (lab t').1 := dist_triangle4 _ _ _ _
        _ ≤ diam X / 100 + diam X / 100 + diam X / 100 := by
            gcongr
            · exact hlabp t ht
            · exact hd.trans (hFs.trans (hE2.trans_eq (by ring)))
            · rw [dist_comm]; exact hlabp t' ht'
        _ = 3 * diam X / 100 := by ring
    · have hD := hR.D_pos
      have hsq : √(3 * δ) ≤ 1 / 400 := by
        calc √(3 * δ) ≤ √((1 / 400) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
          _ = 1 / 400 := Real.sqrt_sq (by norm_num)
      have e : 2 * (3 * diam X / 100) / diam X = 6 / 100 := by field_simp; ring
      rw [e]
      linarith
  · -- the large faces: two short arcs
    obtain ⟨lab, hinj, hlab⟩ := hlarge F hF hFl
    obtain ⟨-, hside⟩ := hopProcess_incidences hX.1.2 htri emit hemit K F
    obtain ⟨c₀, c₁, hc⟩ := htwo hfm X hX htri F hF
      (((hopProcess hX.1.2 emit).arrivals K F).filter (fun t => ¬ bad' t)) lab
      (fun t ht => (hlab t (hsub K F ht)).1) (fun t ht => by
        have e1 := (hside t (Finset.mem_filter.1 ht).1).1
        rw [hopEntry_edge] at e1
        obtain ⟨z, hz, hdz⟩ := exists_closure_near_of_mem_orientedSides e1
        refine ⟨z, hz, ?_⟩
        calc dist (lab t).1 z ≤ dist (lab t).1 (hopEnd X (exitEdge emit t)).1 +
              dist (hopEnd X (exitEdge emit t)).1 z := dist_triangle _ _ _
          _ ≤ diam X ^ (1 - scaleExp K) + 1 := add_le_add (hlab t (hsub K F ht)).2 hdz)
    refine ⟨lab, c₀, c₁, hinj.mono (Finset.coe_subset.2 (hsub K F)), fun t ht => ⟨(hlab t
      (hsub K F ht)).1, ?_⟩⟩
    rw [one_mul]
    exact hc t ht
  · -- the bad tokens
    have hshort := hshort hfm X hX htri
    set Lg := (unitHullSides X).filter (fun p => diam X ^ (19 / 20 : ℝ) ≤ srcLen X s(p.1, p.2))
    have h1 : ((unitHullSides X).filter (fun p => bad' (.inl p))).card ≤
        ((unitHullSides X).filter (fun p => bad (.inl p))).card + Lg.card := by
      refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_union, Lg, hbad'] at hp ⊢
      rcases hp.2 with h | ⟨q, hq, hl⟩
      · exact Or.inl ⟨hp.1, h⟩
      · cases hq; exact Or.inr ⟨hp.1, hl⟩
    have h2 : (hopProcess hX.1.2 emit).fin.toFinset.filter (fun G => bad' (.inr G)) =
        (hopProcess hX.1.2 emit).fin.toFinset.filter (fun G => bad (.inr G)) := by
      apply Finset.filter_congr
      intro G _
      simp [hbad']
    have hnb : ((hopProcess hX.1.2 emit).numBad bad' : ℝ) ≤
        (hopProcess hX.1.2 emit).numBad bad + Lg.card := by
      unfold TokenProcess.numBad
      rw [h2]
      have h1' : (((unitHullSides X).filter (fun p => bad' (.inl p))).card : ℝ) ≤
          ((unitHullSides X).filter (fun p => bad (.inl p))).card + Lg.card := by
        exact_mod_cast h1
      push_cast
      linarith
    linarith

/-- **The routing of the finite token process of depth `K + 1`, up to discarded tokens**
(§9.1–§9.3 of the Verification Guide), with the loss tolerance `η D`.  Let `e = e_K` and
`B = D^{1 - e/8}`.  For some constant `C ≥ 0`, eventually every configuration admits a routing
`P : TokenProcess X` of its unit hull sources, together with entry data `E` (the oriented edge
through which each token enters its receiver) and a set of *bad* (discarded) tokens, such that,
among the **good** tokens arriving after `K + 1` rounds,

* the arrivals at every exceptional face with at most `B` sides are *marked*: they enter through
  pairwise distinct oriented sides of the face, all of whose directions have projection at least
  `19/20` on one unit vector (the positive tangent of the sources of that receiver);
* the tokens arriving at each exceptional face with more than `B` sides carry pairwise distinct
  source labels (unit hull sides) whose starting points lie in two balls of radius
  `C D^{1 - e/4}`;
* at most `2ρ/3 + η D` tokens have reached caps;
* the lost tokens together with the bad tokens number at most `η D` beyond the number of sources
  on long tracks.

**Proved** from `exists_hopRouting` with the track-following process `hopProcess`: its entry edges
are distinct oriented sides of the receivers with the directions of the exit edges
(`hopProcess_incidences`), and it loses no token (`hopProcess_lostArr`).

The bad tokens are then discarded by the proved reduction
`exists_smallMarkedTokenProcess_of_pruned` (`TokenPruning`), and the large receivers are sent
to the loss bin by the proved reduction `exists_markedTokenProcess_of_small`
(`LargeRedirect`). -/
theorem exists_prunedTokenProcess (K : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      ¬ HasUnitTriangle X →
      ∃ (P : TokenProcess X) (E : TokenProcess.Entry X) (bad : (Plane × Plane) ⊕ Set ℂ → Prop),
        (∀ F ∈ exceptionalFaces X, (faceSize X F : ℝ) ≤ diam X ^ (1 - scaleExp K / 8) →
          Set.InjOn E.edge ((P.arrivals K F).filter (fun t => ¬ bad t)) ∧
          ∃ e : ℂ, ‖e‖ = 1 ∧ ∀ t ∈ (P.arrivals K F).filter (fun t => ¬ bad t),
            E.edge t ∈ orientedSides X F ∧
              19 / 20 ≤ inner ℝ ((E.edge t).2 - (E.edge t).1) e) ∧
        (∀ F ∈ exceptionalFaces X, diam X ^ (1 - scaleExp K / 8) < faceSize X F →
          ∃ (lab : (Plane × Plane) ⊕ Set ℂ → Plane × Plane) (c₀ c₁ : Plane),
            Set.InjOn lab ((P.arrivals K F).filter (fun t => ¬ bad t)) ∧
            ∀ t ∈ (P.arrivals K F).filter (fun t => ¬ bad t), lab t ∈ unitHullSides X ∧
              (dist (lab t).1 c₀ ≤ C * diam X ^ (1 - scaleExp K / 4) ∨
                dist (lab t).1 c₁ ≤ C * diam X ^ (1 - scaleExp K / 4))) ∧
        (P.capArr (K + 1) : ℝ) ≤ 2 * (returnExcess X : ℝ) / 3 + η * diam X ∧
        (P.lostArr (K + 1) : ℝ) + P.numBad bad ≤ (((unitHullSides X).filter
          (fun p => diam X ^ (19 / 20 : ℝ) ≤ srcLen X s(p.1, p.2))).card : ℝ) + η * diam X := by
  obtain ⟨C, hC, hev⟩ := exists_hopRouting K η hη
  refine ⟨C, hC, ?_⟩
  filter_upwards [hev] with n hn hfm X hX htri
  obtain ⟨emit, bad, hemit, hsmall, hlarge, hcap, hbad⟩ := hn hfm X hX htri
  refine ⟨hopProcess hX.1.2 emit, hopEntry X emit, bad, fun F hF hFs => ?_, hlarge, hcap, ?_⟩
  · obtain ⟨hinj, hside⟩ := hopProcess_incidences hX.1.2 htri emit hemit K F
    obtain ⟨e, he, hdir⟩ := hsmall F hF hFs
    refine ⟨hinj.mono (Finset.coe_subset.2 (Finset.filter_subset _ _)), e, he, fun t ht => ?_⟩
    have h := hside t (Finset.mem_filter.1 ht).1
    refine ⟨h.1, ?_⟩
    rw [h.2]
    exact hdir t ht
  · rw [hopProcess_lostArr, Nat.cast_zero, zero_add]
    exact hbad

/-- **The routing of the finite token process of depth `K + 1` at the small receivers**
(§9.1–§9.3 of the Verification Guide), with the loss tolerance `η D`: the conclusion of
`exists_prunedTokenProcess` with no bad tokens, i.e. with the conditions on *all* arrivals
(marked arrivals at the exceptional faces with at most `B = D^{1 - e_K/8}` sides, distinct source
labels from two balls of radius `C D^{1 - e_K/4}` at the larger ones, cap arrivals at most
`2ρ/3 + η D`, losses at most `#(long sources) + η D`).  Proved from `exists_prunedTokenProcess`
by discarding the bad tokens (`exists_smallMarkedTokenProcess_of_pruned`). -/
theorem exists_smallMarkedTokenProcess (K : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      ¬ HasUnitTriangle X →
      ∃ (P : TokenProcess X) (E : TokenProcess.Entry X),
        (∀ F ∈ exceptionalFaces X, (faceSize X F : ℝ) ≤ diam X ^ (1 - scaleExp K / 8) →
          P.MarkedArrivals E K F) ∧
        (∀ F ∈ exceptionalFaces X, diam X ^ (1 - scaleExp K / 8) < faceSize X F →
          ∃ (lab : (Plane × Plane) ⊕ Set ℂ → Plane × Plane) (c₀ c₁ : Plane),
            Set.InjOn lab (P.arrivals K F) ∧ ∀ t ∈ P.arrivals K F, lab t ∈ unitHullSides X ∧
              (dist (lab t).1 c₀ ≤ C * diam X ^ (1 - scaleExp K / 4) ∨
                dist (lab t).1 c₁ ≤ C * diam X ^ (1 - scaleExp K / 4))) ∧
        (P.capArr (K + 1) : ℝ) ≤ 2 * (returnExcess X : ℝ) / 3 + η * diam X ∧
        (P.lostArr (K + 1) : ℝ) ≤ (((unitHullSides X).filter
          (fun p => diam X ^ (19 / 20 : ℝ) ≤ srcLen X s(p.1, p.2))).card : ℝ) + η * diam X :=
  exists_smallMarkedTokenProcess_of_pruned K η (exists_prunedTokenProcess K η hη)

/-- **The routing of the finite token process of depth `K + 1`** (§9.1–§9.3 of the Verification
Guide), with the loss tolerance `η D`.  Eventually every configuration admits a routing
`P : TokenProcess X` of its unit hull sources, together with entry data `E`, such that

* after `K + 1` rounds the arrivals at every exceptional face are *marked*
  (`TokenProcess.MarkedArrivals`);
* at most `2ρ/3 + η D` tokens have reached caps;
* at most `η D` tokens have been lost, beyond the number of sources on long tracks.

Proved from the routing at the small receivers `exists_smallMarkedTokenProcess` (with `η / 2`)
and `Δ ≥ 0` (`lockingDefect_nonneg`) by sending the large receivers to the loss bin
(`exists_markedTokenProcess_of_small`: they never emit, and their total arrivals are `o(D)` by the
arrival bound `card_le_of_labels_two_balls` and `sum_large_le`). -/
theorem exists_markedTokenProcess (K : ℕ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∃ (P : TokenProcess X) (E : TokenProcess.Entry X),
        (∀ F ∈ exceptionalFaces X, P.MarkedArrivals E K F) ∧
        (P.capArr (K + 1) : ℝ) ≤ 2 * (returnExcess X : ℝ) / 3 + η * diam X ∧
        (P.lostArr (K + 1) : ℝ) ≤ (((unitHullSides X).filter
          (fun p => diam X ^ (19 / 20 : ℝ) ≤ srcLen X s(p.1, p.2))).card : ℝ) + η * diam X :=
  exists_markedTokenProcess_of_small K η hη lockingDefect_nonneg
    (exists_smallMarkedTokenProcess K (η / 2) (half_pos hη))

/-- **The geometric part of the finite token process of depth `K`** (§9.1–§9.3 of the
Verification Guide), with the loss tolerance `η D`.  Eventually every configuration admits a
routing `P : TokenProcess X` of its unit hull sources such that

* after `K` rounds every exceptional face has received at most its capacity `markedCap` of §8;
* at most `2ρ/3 + η D` tokens have reached caps;
* at most `η D` tokens have been lost, beyond the number of sources on long tracks.

Proved from `exists_markedTokenProcess` (the routing with marked arrivals) and the local
capacities at the faces (`exists_tokenProcess_of_marked`); depth `0` is trivial. -/
theorem exists_tokenProcess (K : ℕ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∃ P : TokenProcess X,
        (∀ F ∈ exceptionalFaces X, (P.faceArr K F : ℝ) ≤ markedCap (faceSize X F)) ∧
        (P.capArr K : ℝ) ≤ 2 * (returnExcess X : ℝ) / 3 + η * diam X ∧
        (P.lostArr K : ℝ) ≤ (((unitHullSides X).filter
          (fun p => diam X ^ (19 / 20 : ℝ) ≤ srcLen X s(p.1, p.2))).card : ℝ) + η * diam X := by
  cases K with
  | zero =>
    refine Eventually.of_forall (fun n _ X hX _ => ⟨TokenProcess.trivial hX.1.2, ?_, ?_, ?_⟩)
    · intro F _
      simpa [TokenProcess.faceArr] using markedCap_nonneg _
    · have : 0 ≤ diam X := Metric.diam_nonneg
      simp only [TokenProcess.capArr, CharP.cast_eq_zero]
      positivity
    · have : 0 ≤ diam X := Metric.diam_nonneg
      simp only [TokenProcess.lostArr, CharP.cast_eq_zero]
      positivity
  | succ K => exact exists_tokenProcess_of_marked K η (exists_markedTokenProcess K η hη)

/-- **The finite token process of depth `K`** (§9.1–§9.4 of the Verification Guide).  For every
fixed depth `K` there is a loss budget `B(D) = o(D)` such that, eventually, every admissible
configuration carries a token ledger of depth `K` with loss `B(D)`.

Proved from the open geometric input `exists_tokenProcess` (through the exact conservation law
`TokenProcess.toLedger`), the short-source theorem `short_unit_sources` for the sources on long
tracks, and the uniformization lemma `exists_littleO_of_forall_eventually`. -/
theorem exists_tokenLedger (K : ℕ) :
    ∃ B : ℝ → ℝ, Tendsto (fun D => B D / D) atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
        Nonempty (TokenLedger X K (B (diam X))) := by
  obtain ⟨B, hB, hev⟩ := exists_littleO_of_forall_eventually
    (fun n X => numOptimalClasses n < ⊤ ∧ IsOptimal n X ∧ ¬ HasUnitTriangle X) minDiam
    (fun X b => Nonempty (TokenLedger X K b)) (fun η hη => by
      filter_upwards [exists_tokenProcess K (η / 2) (by positivity),
        short_unit_sources (η / 2) (by positivity)] with n hP hS X ⟨hfm, hX, htri⟩
      obtain ⟨P, hface, hcap, hlost⟩ := hP hfm X hX htri
      have hlong := hS hfm X hX htri
      have hD : 0 ≤ diam X := Metric.diam_nonneg
      rw [← hX.diam_eq]
      exact ⟨P.toLedger K (by positivity) hface (by linarith) (by linarith)⟩)
  refine ⟨B, hB, ?_⟩
  filter_upwards [hev] with n hn hfm X hX htri
  have := hn X ⟨hfm, hX, htri⟩
  rwa [← hX.diam_eq] at this

/-- **Stability** (WP7 output, Verification Guide §9.4).  For every `η > 0`, eventually every
optimal configuration without unit triangles has `Δ, ρ, f₇, f₈, Q₉` and the high-face incidence
sum `Hinc = Σ_{k ≥ 7} k f_k` all at most `η D`.  (Depends on `lockingDefect_nonneg` and
`exists_tokenLedger`.) -/
theorem stability_bounds (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      (lockingDefect X : ℝ) ≤ η * diam X ∧ (returnExcess X : ℝ) ≤ η * diam X ∧
      (faceCount X 7 : ℝ) ≤ η * diam X ∧ (faceCount X 8 : ℝ) ≤ η * diam X ∧
      (highExcess X : ℝ) ≤ η * diam X ∧ (highIncidence X : ℝ) ≤ η * diam X := by
  set η' := η / 13 with hη'
  have hη'0 : 0 < η' := by positivity
  set K : ℕ := ⌈8 * π / η'⌉₊ + 1 with hK
  have hKgt : 8 * π / η' < K := by
    rw [hK]; push_cast; linarith [Nat.le_ceil (8 * π / η')]
  have hK0 : 0 < K := by omega
  obtain ⟨B, hB, hled⟩ := exists_tokenLedger K
  have hB3 : Tendsto (fun D => 3 * B D / D) atTop (𝓝 0) := by
    have := hB.const_mul 3
    rw [mul_zero] at this
    exact this.congr (fun D => by ring)
  have hev := tendsto_minDiam.eventually (stability_eventually hη'0 hKgt hB3)
  filter_upwards [hled, lockingDefect_nonneg, hev, eventually_ge_atTop 2] with
    n hT hΔ hD hn hfm X hX htri
  obtain ⟨T⟩ := hT hfm X hX htri
  have hΔ0 := hΔ hfm X hX htri
  rw [← hX.diam_eq] at hD
  have hsep : IsSeparated X := hX.1.2
  have h2 : 2 ≤ X.card := by rw [hX.1.1]; exact hn
  have hN := pentagons_add_heptagons_le_pi_mul_diam hsep h2 hΔ0
  have hS1 := T.S1
  unfold stabilityDefect at hS1
  obtain ⟨b1, b2, b3, b4, b5⟩ := stability_of_S1 (B := 3 * B (diam X)) hK0
    (by exact_mod_cast hΔ0) (by positivity) (by positivity) (by positivity) (by positivity)
    hS1 hN
  have hI := highIncidence_le hsep
  have hDpos : 0 < diam X := hX.diam_pos hn
  have e : η = 13 * η' := by rw [hη']; ring
  rw [e]
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

end Erdos99

end

end Stability

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `DegreeDefect`
-/

section DegreeDefect

/-!
# The degree identity with a signed defect (Verification Guide §2.2 and §14.1)

Fix a cutoff `L` and a choice of *good faces*: disjoint sets of ordinary good pentagons, good
hexagons and good activated pentagons among the exceptional faces (`GoodFaces`).  With the short
degree `sd(N)` of a node (its number of ports whose track has fewer than `L` rhombi) define

* `Y = Σ_{ordinary pentagons} (sd - 3) + Σ_{hexagons} (sd - 4) + Σ_{activated} (sd - 5)`
  (`GoodFaces.Y`; after saturation this is the sum of the unmarked short degrees minus two);
* `A` the number of activated pentagons;
* `C₁` the number of two-edge hull returns with exactly one short port (`twoReturnsOneShort`);
* `Bface` the total size of the exceptional faces that are not good (`GoodFaces.Bface`);
* `Bunit` the number of unit hull returns whose port is not short (`unitReturnsNoShort`);
* `Btwo` the number of two-edge returns with no short port (`twoReturnsNoShort`).

`degree_defect` proves (D1) together with the bound (E1) of §14.1: with `E` the number of short
tracks,

  `|2E - (u + 2c₂ - C₁ + 3p + 4h + Y + 2A)| ≤ Bface + Bunit + 2 Btwo + 3ρ`.

The proof is the double count `2E = Σ_N sd(N)` (`sum_shortDeg`), split into faces and hull returns.
-/

open scoped BigOperators Real
open Filter

@[expose] public noncomputable section

open Classical

namespace Erdos99

/-- A choice of good faces (Verification Guide §4.1, §10): ordinary good pentagons, good hexagons
and good activated pentagons, all exceptional faces of the stated sizes, the two kinds of
pentagons disjoint. -/
structure GoodFaces (X : Finset Plane) where
  /-- The ordinary good pentagons. -/
  pent : Finset (Set ℂ)
  /-- The good hexagons. -/
  hex : Finset (Set ℂ)
  /-- The good activated pentagons. -/
  act : Finset (Set ℂ)
  pent_sub : ∀ F ∈ pent, F ∈ exceptionalFinset X ∧ faceSize X F = 5
  hex_sub : ∀ F ∈ hex, F ∈ exceptionalFinset X ∧ faceSize X F = 6
  act_sub : ∀ F ∈ act, F ∈ exceptionalFinset X ∧ faceSize X F = 5
  disj : Disjoint pent act

namespace GoodFaces

variable {X : Finset Plane}

/-- All good faces. -/
def good (G : GoodFaces X) : Finset (Set ℂ) := G.pent ∪ G.hex ∪ G.act

/-- `Y = Σ_{pent} (sd - 3) + Σ_{hex} (sd - 4) + Σ_{act} (sd - 5)`, real-valued. -/
def Y (G : GoodFaces X) (L : ℝ) : ℝ :=
  ∑ F ∈ G.pent, ((shortDeg X L (Sum.inl F) : ℝ) - 3) +
    ∑ F ∈ G.hex, ((shortDeg X L (Sum.inl F) : ℝ) - 4) +
    ∑ F ∈ G.act, ((shortDeg X L (Sum.inl F) : ℝ) - 5)

/-- `A`: the number of activated pentagons. -/
def A (G : GoodFaces X) : ℕ := G.act.card

/-- `Bface`: the total number of sides of the exceptional faces that are not good. -/
def Bface (G : GoodFaces X) : ℕ :=
  ∑ F ∈ (exceptionalFinset X).filter (fun F => F ∉ G.good), faceSize X F

end GoodFaces

/-- `E`: the number of tracks (including tracks without rhombi) with fewer than `L` rhombi. -/
def numShortTracks (X : Finset Plane) (L : ℝ) : ℕ :=
  ((allTracks X).filter (fun T => (trackLength X T : ℝ) < L)).card

/-- `C₁`: the number of two-edge hull returns with exactly one short port. -/
def twoReturnsOneShort (X : Finset Plane) (L : ℝ) : ℕ :=
  ((ccwHullSides X).filter
    (fun p => returnLength X p.1 p.2 = 2 ∧ shortDeg X L (Sum.inr p) = 1)).card

/-- `Btwo`: the number of two-edge hull returns with no short port. -/
def twoReturnsNoShort (X : Finset Plane) (L : ℝ) : ℕ :=
  ((ccwHullSides X).filter
    (fun p => returnLength X p.1 p.2 = 2 ∧ shortDeg X L (Sum.inr p) = 0)).card

/-- `Bunit`: the number of unit hull returns whose port is not short. -/
def unitReturnsNoShort (X : Finset Plane) (L : ℝ) : ℕ :=
  ((ccwHullSides X).filter
    (fun p => returnLength X p.1 p.2 = 1 ∧ shortDeg X L (Sum.inr p) = 0)).card

lemma twoReturnsOneShort_le (X : Finset Plane) (L : ℝ) :
    twoReturnsOneShort X L ≤ hullReturns X 2 :=
  Finset.card_le_card (Finset.monotone_filter_right _ fun _ _ h => h.1)

lemma shortDeg_le_portDeg (X : Finset Plane) (L : ℝ) (N : PortNode) :
    shortDeg X L N ≤ portDeg X N :=
  Finset.card_le_card (Finset.monotone_filter_right _ fun _ _ h => h.1)

/-- `2E` splits into the short degrees of the faces and of the hull returns. -/
lemma two_mul_numShortTracks :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ L : ℝ, 2 * numShortTracks X L =
        ∑ F ∈ exceptionalFinset X, shortDeg X L (Sum.inl F) +
          ∑ p ∈ ccwHullSides X, shortDeg X L (Sum.inr p) := by
  filter_upwards [sum_shortDeg] with n h hfm X hX htri L
  rw [numShortTracks, ← h hfm X hX htri L, portNodes, Finset.sum_union (disjoint_portNodes X),
    Finset.sum_map, Finset.sum_map]
  rfl

/-- The face part of the degree identity. -/
lemma face_part {X : Finset Plane} (hX : IsSeparated X) (L : ℝ) (G : GoodFaces X) :
    |(∑ F ∈ exceptionalFinset X, (shortDeg X L (Sum.inl F) : ℝ)) -
      (3 * numPentagons X + 4 * numHexagons X + G.Y L + 2 * G.A)| ≤ G.Bface := by
  set S := exceptionalFinset X
  set sd : Set ℂ → ℝ := fun F => (shortDeg X L (Sum.inl F) : ℝ)
  have hsum : ∀ (t : Finset (Set ℂ)) (g : Set ℂ → ℝ), t ⊆ S →
      ∑ F ∈ t, g F = ∑ F ∈ S, if F ∈ t then g F else 0 := by
    intro t g ht
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 ht]
  have hp : (numPentagons X : ℝ) = ∑ F ∈ S, if faceSize X F = 5 then 1 else 0 := by
    rw [numPentagons, faceCount_eq_card_exceptionalFinset hX le_rfl, Finset.card_filter]
    push_cast; rfl
  have hh : (numHexagons X : ℝ) = ∑ F ∈ S, if faceSize X F = 6 then 1 else 0 := by
    rw [numHexagons, faceCount_eq_card_exceptionalFinset hX (by norm_num), Finset.card_filter]
    push_cast; rfl
  have hA : (G.A : ℝ) = ∑ F ∈ S, if F ∈ G.act then 1 else 0 := by
    rw [← hsum G.act (fun _ => (1 : ℝ)) fun F hF => (G.act_sub F hF).1]
    simp [GoodFaces.A]
  have hY : G.Y L = ∑ F ∈ S, ((if F ∈ G.pent then sd F - 3 else 0) +
      (if F ∈ G.hex then sd F - 4 else 0) + (if F ∈ G.act then sd F - 5 else 0)) := by
    rw [GoodFaces.Y, hsum _ _ fun F hF => (G.pent_sub F hF).1,
      hsum _ _ fun F hF => (G.hex_sub F hF).1, hsum _ _ fun F hF => (G.act_sub F hF).1,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have hB : (G.Bface : ℝ) = ∑ F ∈ S, if F ∈ G.good then 0 else (faceSize X F : ℝ) := by
    rw [GoodFaces.Bface, Finset.sum_filter]
    push_cast
    refine Finset.sum_congr rfl fun F _ => ?_
    split_ifs <;> simp_all
  have key : (∑ F ∈ S, sd F) - (3 * numPentagons X + 4 * numHexagons X + G.Y L + 2 * G.A) =
      ∑ F ∈ S, if F ∈ G.good then 0 else
        sd F - ((if faceSize X F = 5 then 3 else 0) + (if faceSize X F = 6 then 4 else 0)) := by
    rw [hp, hh, hA, hY, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun F hF => ?_
    have hdisj := Finset.disjoint_left.1 G.disj
    by_cases h1 : F ∈ G.pent
    · have := (G.pent_sub F h1).2
      have h2 : F ∉ G.hex := fun h => by have := (G.hex_sub F h).2; omega
      have h3 : F ∉ G.act := hdisj h1
      simp [GoodFaces.good, h1, h2, h3, this]
    by_cases h2 : F ∈ G.hex
    · have := (G.hex_sub F h2).2
      have h3 : F ∉ G.act := fun h => by have := (G.act_sub F h).2; omega
      simp [GoodFaces.good, h1, h2, h3, this]
    by_cases h3 : F ∈ G.act
    · have := (G.act_sub F h3).2
      simp [GoodFaces.good, h1, h2, h3, this]; ring
    simp only [GoodFaces.good, Finset.mem_union, h1, h2, h3, or_self, if_false]
    split_ifs <;> ring
  rw [key, hB]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun F hF => ?_)
  by_cases hg : F ∈ G.good
  · simp [hg]
  · rw [if_neg hg, if_neg hg]
    have h5 := ((mem_exceptionalFinset hX).1 hF).2
    have hle : (shortDeg X L (Sum.inl F) : ℝ) ≤ faceSize X F := by
      have := shortDeg_le_portDeg X L (Sum.inl F)
      rw [portDeg_face ((mem_exceptionalFinset hX).1 hF)] at this
      exact_mod_cast this
    have h5' : (5 : ℝ) ≤ faceSize X F := by exact_mod_cast h5
    have h0 : (0 : ℝ) ≤ shortDeg X L (Sum.inl F) := Nat.cast_nonneg _
    rw [abs_le]
    simp only [sd]
    constructor <;> split_ifs <;> linarith

/-- Pointwise bound for the hull part. -/
lemma hull_pointwise (j s : ℕ) (hs : s ≤ j) (hj : 1 ≤ j) :
    |(s : ℝ) - ((if j = 1 then 1 else 0) + 2 * (if j = 2 then 1 else 0) -
      (if j = 2 ∧ s = 1 then 1 else 0))| ≤
      (if j = 1 ∧ s = 0 then 1 else 0) + 2 * (if j = 2 ∧ s = 0 then 1 else 0) +
        3 * ((j - 2 : ℕ) : ℝ) := by
  obtain rfl | rfl | h := (by omega : j = 1 ∨ j = 2 ∨ 3 ≤ j)
  · interval_cases s <;> norm_num
  · interval_cases s <;> norm_num
  · have h1 : j ≠ 1 := by omega
    have h2 : j ≠ 2 := by omega
    simp only [h1, h2, false_and, if_false]
    have : ((j - 2 : ℕ) : ℝ) = j - 2 := by rw [Nat.cast_sub (by omega)]; norm_num
    rw [this]
    have hs' : (s : ℝ) ≤ j := by exact_mod_cast hs
    have hj' : (3 : ℝ) ≤ j := by exact_mod_cast h
    rw [abs_le]; constructor <;> nlinarith [(Nat.cast_nonneg s : (0:ℝ) ≤ s)]

/-- The hull part of the degree identity. -/
lemma hull_part :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ∀ L : ℝ,
      |(∑ p ∈ ccwHullSides X, (shortDeg X L (Sum.inr p) : ℝ)) -
        (numUnitHullSides X + 2 * hullReturns X 2 - twoReturnsOneShort X L)| ≤
        unitReturnsNoShort X L + 2 * twoReturnsNoShort X L + 3 * returnExcess X := by
  filter_upwards [portDeg_hullSide, two_le_returnLength, hullReturns_one_eventually] with
    n hpd h2 h1 hfm X hX L
  have hc : ∀ (P : Plane × Plane → Prop) [DecidablePred P],
      ((((ccwHullSides X).filter P).card : ℕ) : ℝ) =
      ∑ p ∈ ccwHullSides X, if P p then (1 : ℝ) else 0 := by
    intro P _; rw [Finset.card_filter]; push_cast; rfl
  rw [← h1 hfm X hX, hullReturns, hullReturns, twoReturnsOneShort, unitReturnsNoShort,
    twoReturnsNoShort, hc, hc, hc, hc, hc, returnExcess, Nat.cast_sum, Finset.mul_sum,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp => ?_)
  have hle : shortDeg X L (Sum.inr p) ≤ returnLength X p.1 p.2 := by
    have := shortDeg_le_portDeg X L (Sum.inr p)
    rwa [hpd hfm X hX p hp] at this
  have hge : 1 ≤ returnLength X p.1 p.2 := by
    by_cases hd : dist p.1 p.2 = 1
    · rw [returnLength_of_dist_eq_one hd]
    · have := h2 hfm X hX p hp hd; omega
  exact hull_pointwise _ _ hle hge

/-- **The degree identity (D1) with the defect bound (E1)** (Verification Guide §2.2, §14.1).
For every cutoff `L` and every choice of good faces,
`|2E - (u + 2c₂ - C₁ + 3p + 4h + Y + 2A)| ≤ Bface + Bunit + 2 Btwo + 3ρ`. -/
theorem degree_defect :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ (L : ℝ) (G : GoodFaces X),
        |2 * (numShortTracks X L : ℝ) - (numUnitHullSides X + 2 * hullReturns X 2 -
            twoReturnsOneShort X L + 3 * numPentagons X + 4 * numHexagons X + G.Y L + 2 * G.A)| ≤
          G.Bface + unitReturnsNoShort X L + 2 * twoReturnsNoShort X L + 3 * returnExcess X := by
  filter_upwards [two_mul_numShortTracks, hull_part] with n h2E hhull hfm X hX htri L G
  have hE : 2 * (numShortTracks X L : ℝ) =
      (∑ F ∈ exceptionalFinset X, (shortDeg X L (Sum.inl F) : ℝ)) +
        ∑ p ∈ ccwHullSides X, (shortDeg X L (Sum.inr p) : ℝ) := by
    exact_mod_cast h2E hfm X hX htri L
  have hf := face_part hX.1.2 L G
  have hh := hhull hfm X hX L
  rw [hE]
  calc _ = |((∑ F ∈ exceptionalFinset X, (shortDeg X L (Sum.inl F) : ℝ)) -
        (3 * numPentagons X + 4 * numHexagons X + G.Y L + 2 * G.A)) +
        ((∑ p ∈ ccwHullSides X, (shortDeg X L (Sum.inr p) : ℝ)) -
        (numUnitHullSides X + 2 * hullReturns X 2 - twoReturnsOneShort X L))| := by ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (by linarith)

end Erdos99

end

end DegreeDefect

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `LocalCharge`
-/

section LocalCharge

/-!
# WP11: the local charging ledger on the short graph of good faces (Verification Guide §4, §13.4)

This file proves the purely combinatorial part of the charging argument (original Proposition 5.6,
Verification Guide §§4.2–4.4 and the counting half of §13.4), for an arbitrary finite multigraph
with stubs.

A `StubGraph` has finitely many edges (each with two end vertices; loops and parallel edges are
allowed) and finitely many *stubs* (half-edges with one end vertex; in the application these are
the short track ends at caps, actual or virtual).  Fix a finite vertex set `V` (the good faces)
containing all edge ends, on which every degree is `2`, `3` or `4`.  Put

* `H` the degree-two vertices, `G = V \ H`, `J` the degree-three vertices with an incidence to
  `H`, `K = G \ J`;
* `Y = Σ_{v ∈ V} (deg v - 2)`;
* `C = b(V) + 2 e(H,H)` and `hC = b(H) + 2 e(H,H)`: the cap incidences (each `H–H` edge is
  replaced by two virtual cap stubs);
* `κ(U)` the number of connected components of the subgraph on `U` that carry no stub;
* `Fl` an arbitrary set of *flagged* vertices; a defective `J` vertex is an unflagged one with at
  least two incidences to unflagged `H` vertices (excluded by §13.2), and an exceptional `J–J`
  edge is one neither of whose ends is flagged or has all its `H` incidences flagged (excluded by
  §13.3).

The main result is `StubGraph.charging_ledger`:

  `4 |V| ≤ 5 Y + C + hC + κ(G) + κ(K) + 4 |Fl| + 4 #defective + #exceptional`.

Its proof follows the Guide: the degree identities (C1), (C3), (C4) (`deg_sum_*`), the component
estimate (C2) from the spanning-forest bound `card_le_eIn_add_bIn_add_stubless`, the lower bound
(C5) on the charge `M = e(J,J) + Σ_J 2(i - 1)`, and the charge distribution (C6)
`M ≤ 4 |Fl| + 4 #defective + #exceptional` (`charge_le`).

We also prove `stubless_le_small_add`: components with more than `M` vertices are at most
`|U| / (M + 1)` in number, so `κ(U)` is controlled by the stubless components of size at most `M`.
-/

open scoped BigOperators

@[expose] public noncomputable section

open Classical

namespace Erdos99

namespace LocalCharge

/-- A finite multigraph with stubs: edges `e ∈ E` join `src e` and `tgt e` (loops and parallel
edges allowed), stubs `s ∈ S` are half-edges at `stub s`. -/
structure StubGraph (α : Type*) where
  /-- The edges. -/
  E : Finset ℕ
  /-- The first end of an edge. -/
  src : ℕ → α
  /-- The second end of an edge. -/
  tgt : ℕ → α
  /-- The stubs. -/
  S : Finset ℕ
  /-- The vertex of a stub. -/
  stub : ℕ → α

namespace StubGraph

variable {α : Type*} (g : StubGraph α)

/-! ## Counting functions -/

/-- The number of edge ends at `v` whose other end lies in `B` (a loop at `v ∈ B` counts twice). -/
def inc (v : α) (B : Finset α) : ℕ :=
  (g.E.filter (fun e => g.src e = v ∧ g.tgt e ∈ B)).card +
    (g.E.filter (fun e => g.tgt e = v ∧ g.src e ∈ B)).card

/-- The number of edges from `A` to `B` (ordered by `src`, `tgt`). -/
def eIn (A B : Finset α) : ℕ := (g.E.filter (fun e => g.src e ∈ A ∧ g.tgt e ∈ B)).card

/-- The number of stubs at `v`. -/
def stubs (v : α) : ℕ := (g.S.filter (fun s => g.stub s = v)).card

/-- The number of stubs at vertices of `A`. -/
def bIn (A : Finset α) : ℕ := (g.S.filter (fun s => g.stub s ∈ A)).card

/-- The degree of `v`: edge ends (a loop counts twice) plus stubs. -/
def deg (v : α) : ℕ :=
  (g.E.filter (fun e => g.src e = v)).card + (g.E.filter (fun e => g.tgt e = v)).card + g.stubs v

/-! ## Basic double counting -/

lemma sum_card_filter_eq {β : Type*} (s : Finset ℕ) (f : ℕ → β) (A : Finset β)
    (P : ℕ → Prop) :
    ∑ v ∈ A, (s.filter (fun e => f e = v ∧ P e)).card = (s.filter (fun e => f e ∈ A ∧ P e)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := A) (fun e he => (Finset.mem_filter.1 he).2.1)]
  refine Finset.sum_congr rfl fun v hv => ?_
  congr 1
  ext e
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨he, rfl, hP⟩; exact ⟨⟨he, hv, hP⟩, rfl⟩
  · rintro ⟨⟨he, -, hP⟩, rfl⟩; exact ⟨he, rfl, hP⟩

/-- `Σ_{v ∈ A} inc v B = e(A,B) + e(B,A)`. -/
lemma sum_inc (A B : Finset α) : ∑ v ∈ A, g.inc v B = g.eIn A B + g.eIn B A := by
  unfold inc eIn
  have h1 := sum_card_filter_eq g.E g.src A (fun e => g.tgt e ∈ B)
  have h2 := sum_card_filter_eq g.E g.tgt A (fun e => g.src e ∈ B)
  beta_reduce at h1 h2
  rw [Finset.sum_add_distrib]
  congr 1
  · convert h1 using 4
  · convert h2 using 4
    exact and_comm

lemma sum_stubs (A : Finset α) : ∑ v ∈ A, g.stubs v = g.bIn A := by
  unfold stubs bIn
  have := sum_card_filter_eq g.S g.stub A (fun _ => True)
  simpa using this

lemma inc_union (v : α) {B C : Finset α} (h : Disjoint B C) :
    g.inc v (B ∪ C) = g.inc v B + g.inc v C := by
  unfold inc
  have key : ∀ (f k : ℕ → α), (g.E.filter (fun e => f e = v ∧ k e ∈ B ∪ C)).card =
      (g.E.filter (fun e => f e = v ∧ k e ∈ B)).card +
        (g.E.filter (fun e => f e = v ∧ k e ∈ C)).card := by
    intro f k
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext e; simp only [Finset.mem_filter, Finset.mem_union]; tauto
    · rw [Finset.disjoint_filter]
      intro e _ h1 h2
      exact Finset.disjoint_left.1 h h1.2 h2.2
  rw [key g.src g.tgt, key g.tgt g.src]
  ring

lemma bIn_union {A B : Finset α} (h : Disjoint A B) : g.bIn (A ∪ B) = g.bIn A + g.bIn B := by
  unfold bIn
  rw [← Finset.card_union_of_disjoint]
  · congr 1; ext s; simp only [Finset.mem_filter, Finset.mem_union]; tauto
  · rw [Finset.disjoint_filter]
    intro s _ h1 h2
    exact Finset.disjoint_left.1 h h1 h2

lemma eIn_union_left {A A' B : Finset α} (h : Disjoint A A') :
    g.eIn (A ∪ A') B = g.eIn A B + g.eIn A' B := by
  unfold eIn
  rw [← Finset.card_union_of_disjoint]
  · congr 1; ext s; simp only [Finset.mem_filter, Finset.mem_union]; tauto
  · rw [Finset.disjoint_filter]
    intro s _ h1 h2
    exact Finset.disjoint_left.1 h h1.1 h2.1

lemma eIn_union_right {A B B' : Finset α} (h : Disjoint B B') :
    g.eIn A (B ∪ B') = g.eIn A B + g.eIn A B' := by
  unfold eIn
  rw [← Finset.card_union_of_disjoint]
  · congr 1; ext s; simp only [Finset.mem_filter, Finset.mem_union]; tauto
  · rw [Finset.disjoint_filter]
    intro s _ h1 h2
    exact Finset.disjoint_left.1 h h1.2 h2.2

lemma bIn_mono {A B : Finset α} (h : A ⊆ B) : g.bIn A ≤ g.bIn B :=
  Finset.card_le_card (Finset.monotone_filter_right _ fun _ _ hs => h hs)

lemma inc_mono (v : α) {B C : Finset α} (h : B ⊆ C) : g.inc v B ≤ g.inc v C :=
  add_le_add (Finset.card_le_card (Finset.monotone_filter_right _ fun _ _ hs => ⟨hs.1, h hs.2⟩))
    (Finset.card_le_card (Finset.monotone_filter_right _ fun _ _ hs => ⟨hs.1, h hs.2⟩))

lemma inc_le_deg (v : α) (B : Finset α) : g.inc v B ≤ g.deg v := by
  unfold inc deg
  have h1 : (g.E.filter (fun e => g.src e = v ∧ g.tgt e ∈ B)).card ≤
      (g.E.filter (fun e => g.src e = v)).card :=
    Finset.card_le_card (Finset.monotone_filter_right _ fun _ _ hs => hs.1)
  have h2 : (g.E.filter (fun e => g.tgt e = v ∧ g.src e ∈ B)).card ≤
      (g.E.filter (fun e => g.tgt e = v)).card :=
    Finset.card_le_card (Finset.monotone_filter_right _ fun _ _ hs => hs.1)
  omega

/-- When every edge has both ends in `V`, the degree is `inc v V + stubs v`. -/
lemma deg_eq (V : Finset α) (hE : ∀ e ∈ g.E, g.src e ∈ V ∧ g.tgt e ∈ V) (v : α) :
    g.deg v = g.inc v V + g.stubs v := by
  unfold deg inc
  congr 2
  · congr 1; ext e; simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨h.1, h.2, (hE e h.1).2⟩, fun h => ⟨h.1, h.2.1⟩⟩
  · congr 1; ext e; simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨h.1, h.2, (hE e h.1).1⟩, fun h => ⟨h.1, h.2.1⟩⟩

/-! ## Components and the spanning-forest bound (§13.4) -/

/-- The simple graph spanned by the edges in `F` (loops are dropped). -/
def edgeGraph (F : Finset ℕ) : SimpleGraph α :=
  SimpleGraph.fromEdgeSet ((F.image fun e => s(g.src e, g.tgt e) : Finset (Sym2 α)) : Set (Sym2 α))

/-- The simple graph of the edges with both ends in `U`. -/
def cgraph (U : Finset α) : SimpleGraph α :=
  g.edgeGraph (g.E.filter (fun e => g.src e ∈ U ∧ g.tgt e ∈ U))

/-- `κ(U)`: the number of connected components of the subgraph on `U` that carry no stub. -/
def stubless (U : Finset α) : ℕ :=
  ((U.image (g.cgraph U).connectedComponentMk).filter
    (fun C => ∀ s ∈ g.S, g.stub s ∈ U → (g.cgraph U).connectedComponentMk (g.stub s) ≠ C)).card

/-- The stubless components of the subgraph on `U` with at most `M` vertices. -/
def stublessSmall (U : Finset α) (M : ℕ) : ℕ :=
  ((U.image (g.cgraph U).connectedComponentMk).filter
    (fun C => (∀ s ∈ g.S, g.stub s ∈ U → (g.cgraph U).connectedComponentMk (g.stub s) ≠ C) ∧
      (U.filter (fun x => (g.cgraph U).connectedComponentMk x = C)).card ≤ M)).card

/-- Reachability after adding one edge `ab`. -/
lemma reachable_of_add_edge {G G' : SimpleGraph α} {a b : α}
    (hadj : ∀ x y, G'.Adj x y → G.Adj x y ∨ s(x, y) = s(a, b)) {x y : α}
    (h : G'.Reachable x y) :
    G.Reachable x y ∨ ((G.Reachable x a ∨ G.Reachable x b) ∧ (G.Reachable a y ∨ G.Reachable b y)) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact Or.inl SimpleGraph.Reachable.rfl
  | @cons x z y hxz p ih =>
    rcases hadj x z hxz with hG | hab
    · have hxz' : G.Reachable x z := hG.reachable
      rcases ih with h | ⟨h1, h2⟩
      · exact Or.inl (hxz'.trans h)
      · exact Or.inr ⟨h1.imp (hxz'.trans ·) (hxz'.trans ·), h2⟩
    · right
      rcases Sym2.eq_iff.1 hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · refine ⟨Or.inl SimpleGraph.Reachable.rfl, ?_⟩
        rcases ih with h | ⟨-, h2⟩
        · exact Or.inr h
        · exact h2
      · refine ⟨Or.inr SimpleGraph.Reachable.rfl, ?_⟩
        rcases ih with h | ⟨-, h2⟩
        · exact Or.inl h
        · exact h2

/-- Adding one edge decreases the number of components meeting `U` by at most one. -/
lemma card_image_le_add_edge (U : Finset α) {G G' : SimpleGraph α} {a b : α} (hle : G ≤ G')
    (hadj : ∀ x y, G'.Adj x y → G.Adj x y ∨ s(x, y) = s(a, b)) :
    (U.image G.connectedComponentMk).card ≤ (U.image G'.connectedComponentMk).card + 1 := by
  set T := U.image G.connectedComponentMk
  let φ : G.ConnectedComponent → G'.ConnectedComponent :=
    SimpleGraph.ConnectedComponent.map (SimpleGraph.Hom.ofLE hle)
  have himg : T.image φ = U.image G'.connectedComponentMk := by
    rw [Finset.image_image]
    rfl
  have hinj : Set.InjOn φ (T.erase (G.connectedComponentMk a) : Set G.ConnectedComponent) := by
    intro C₁ h₁ C₂ h₂ h12
    induction C₁ using SimpleGraph.ConnectedComponent.ind with | h x => ?_
    induction C₂ using SimpleGraph.ConnectedComponent.ind with | h y => ?_
    simp only [Finset.coe_erase, Set.mem_diff, Set.mem_singleton_iff] at h₁ h₂
    have hx : ¬ G.Reachable x a := fun h => h₁.2 (SimpleGraph.ConnectedComponent.eq.2 h)
    have hy : ¬ G.Reachable y a := fun h => h₂.2 (SimpleGraph.ConnectedComponent.eq.2 h)
    have hr : G'.Reachable x y := by
      have := h12
      simp only [φ, SimpleGraph.ConnectedComponent.map_mk] at this
      exact SimpleGraph.ConnectedComponent.eq.1 this
    apply SimpleGraph.ConnectedComponent.eq.2
    rcases reachable_of_add_edge hadj hr with h | ⟨h1, h2⟩
    · exact h
    · have hxb : G.Reachable x b := h1.resolve_left hx
      have hby : G.Reachable b y := h2.resolve_left fun h => hy h.symm
      exact hxb.trans hby
  calc T.card ≤ (T.erase (G.connectedComponentMk a)).card + 1 := by
        have := Finset.pred_card_le_card_erase (s := T) (a := G.connectedComponentMk a); omega
    _ = ((T.erase (G.connectedComponentMk a)).image φ).card + 1 := by
        rw [Finset.card_image_of_injOn hinj]
    _ ≤ (T.image φ).card + 1 := by
        gcongr; exact Finset.image_subset_image (Finset.erase_subset _ _)
    _ = _ := by rw [himg]

/-- **Spanning-forest bound.** `|U| ≤ |F| + #(components of the graph of `F` meeting `U`)`. -/
lemma card_le_card_add_components (U : Finset α) (F : Finset ℕ) :
    U.card ≤ F.card + (U.image (g.edgeGraph F).connectedComponentMk).card := by
  induction F using Finset.induction_on with
  | empty =>
    have hbot : g.edgeGraph ∅ = ⊥ := by
      ext x y; simp [edgeGraph]
    rw [hbot, Finset.card_image_of_injective]
    · simp
    · intro x y hxy
      exact SimpleGraph.reachable_bot.1 (SimpleGraph.ConnectedComponent.eq.1 hxy)
  | @insert e F he ih =>
    have hle : g.edgeGraph F ≤ g.edgeGraph (insert e F) := by
      intro x y hxy
      simp only [edgeGraph, SimpleGraph.fromEdgeSet_adj, Finset.coe_image, Set.mem_image,
        Finset.mem_coe] at hxy ⊢
      obtain ⟨⟨f, hf, hfe⟩, hne⟩ := hxy
      exact ⟨⟨f, Finset.mem_insert_of_mem hf, hfe⟩, hne⟩
    have hadj : ∀ x y, (g.edgeGraph (insert e F)).Adj x y →
        (g.edgeGraph F).Adj x y ∨ s(x, y) = s(g.src e, g.tgt e) := by
      intro x y hxy
      simp only [edgeGraph, SimpleGraph.fromEdgeSet_adj, Finset.coe_image, Set.mem_image,
        Finset.mem_coe, Finset.mem_insert] at hxy ⊢
      obtain ⟨⟨f, hf, hfe⟩, hne⟩ := hxy
      rcases hf with rfl | hf
      · exact Or.inr hfe.symm
      · exact Or.inl ⟨⟨f, hf, hfe⟩, hne⟩
    have := card_image_le_add_edge U hle hadj
    rw [Finset.card_insert_of_notMem he]
    omega

/-- **(C2)**: `|U| ≤ e(U,U) + b(U) + κ(U)`. -/
lemma card_le_eIn_add_bIn_add_stubless (U : Finset α) :
    U.card ≤ g.eIn U U + g.bIn U + g.stubless U := by
  set T := U.image (g.cgraph U).connectedComponentMk
  have h1 := g.card_le_card_add_components U (g.E.filter (fun e => g.src e ∈ U ∧ g.tgt e ∈ U))
  have h2 : T.card = (T.filter (fun C => ∀ s ∈ g.S, g.stub s ∈ U →
      (g.cgraph U).connectedComponentMk (g.stub s) ≠ C)).card +
      (T.filter (fun C => ¬ ∀ s ∈ g.S, g.stub s ∈ U →
      (g.cgraph U).connectedComponentMk (g.stub s) ≠ C)).card :=
    (Finset.card_filter_add_card_filter_not _).symm
  have h3 : (T.filter (fun C => ¬ ∀ s ∈ g.S, g.stub s ∈ U →
      (g.cgraph U).connectedComponentMk (g.stub s) ≠ C)).card ≤ g.bIn U := by
    refine (Finset.card_le_card ?_).trans (Finset.card_image_le (f := fun s =>
      (g.cgraph U).connectedComponentMk (g.stub s)) (s := g.S.filter (fun s => g.stub s ∈ U)))
    intro C hC
    simp only [Finset.mem_filter, not_forall, not_not] at hC
    obtain ⟨-, s, hs, hsU, hsC⟩ := hC
    exact Finset.mem_image.2 ⟨s, Finset.mem_filter.2 ⟨hs, hsU⟩, hsC⟩
  have h4 : (T.filter (fun C => ∀ s ∈ g.S, g.stub s ∈ U →
      (g.cgraph U).connectedComponentMk (g.stub s) ≠ C)).card = g.stubless U := rfl
  have h5 : U.card ≤ g.eIn U U + T.card := h1
  omega

/-- Components with more than `M` vertices are at most `|U| / (M+1)` in number:
`(M + 1) κ(U) ≤ (M + 1) κ_{≤ M}(U) + |U|`. -/
lemma stubless_le_small_add (U : Finset α) (M : ℕ) :
    (M + 1) * g.stubless U ≤ (M + 1) * g.stublessSmall U M + U.card := by
  set mk := (g.cgraph U).connectedComponentMk
  set T := U.image mk
  set Q : (g.cgraph U).ConnectedComponent → Prop :=
    fun C => ∀ s ∈ g.S, g.stub s ∈ U → mk (g.stub s) ≠ C
  set fib : (g.cgraph U).ConnectedComponent → ℕ := fun C => (U.filter (fun x => mk x = C)).card
  have hsplit : (T.filter Q).card = ((T.filter Q).filter (fun C => fib C ≤ M)).card +
      ((T.filter Q).filter (fun C => ¬ fib C ≤ M)).card :=
    (Finset.card_filter_add_card_filter_not _).symm
  have hsmall : ((T.filter Q).filter (fun C => fib C ≤ M)).card = g.stublessSmall U M := by
    unfold stublessSmall; rw [Finset.filter_filter]
  have hlarge : (M + 1) * ((T.filter Q).filter (fun C => ¬ fib C ≤ M)).card ≤ U.card := by
    set L := (T.filter Q).filter (fun C => ¬ fib C ≤ M)
    calc (M + 1) * L.card = ∑ C ∈ L, (M + 1) := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ C ∈ L, fib C := Finset.sum_le_sum fun C hC => by
          have := (Finset.mem_filter.1 hC).2; omega
      _ ≤ ∑ C ∈ T, fib C := Finset.sum_le_sum_of_subset
          ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))
      _ = U.card := (Finset.card_eq_sum_card_image mk U).symm
  have : g.stubless U = (T.filter Q).card := rfl
  rw [this, hsplit, ← hsmall]
  nlinarith

/-! ## The vertex classes -/

/-- The degree-two vertices `H`. -/
def Hs (V : Finset α) : Finset α := V.filter (fun v => g.deg v = 2)

/-- The vertices of degree at least three, `G = V \ H`. -/
def Gs (V : Finset α) : Finset α := V.filter (fun v => g.deg v ≠ 2)

/-- The degree-three vertices with at least one incidence to `H`. -/
def Js (V : Finset α) : Finset α := V.filter (fun v => g.deg v = 3 ∧ 0 < g.inc v (g.Hs V))

/-- `K = G \ J`. -/
def Ks (V : Finset α) : Finset α :=
  V.filter (fun v => g.deg v ≠ 2 ∧ ¬ (g.deg v = 3 ∧ 0 < g.inc v (g.Hs V)))

/-- `Y = Σ_{v ∈ V} (deg v - 2)`. -/
def Ysum (V : Finset α) : ℝ := ∑ v ∈ V, ((g.deg v : ℝ) - 2)

/-- A vertex can receive `J–J` edges if it is flagged or all its `H` incidences are flagged. -/
def Qual (V Fl : Finset α) (v : α) : Prop := v ∈ Fl ∨ g.inc v (g.Hs V \ Fl) = 0

/-- Defective `J` vertices: unflagged, with at least two incidences to unflagged `H` vertices
(the pattern excluded by §13.2). -/
def defJ (V Fl : Finset α) : ℕ :=
  ((g.Js V).filter (fun v => v ∉ Fl ∧ 2 ≤ g.inc v (g.Hs V \ Fl))).card

/-- Exceptional `J–J` edges: neither end can receive them (the pattern excluded by §13.3). -/
def excE (V Fl : Finset α) : ℕ :=
  (g.E.filter (fun e => g.src e ∈ g.Js V ∧ g.tgt e ∈ g.Js V ∧
    ¬ g.Qual V Fl (g.src e) ∧ ¬ g.Qual V Fl (g.tgt e))).card

lemma disjoint_Hs_Gs (V : Finset α) : Disjoint (g.Hs V) (g.Gs V) := by
  rw [Hs, Gs]; exact Finset.disjoint_filter_filter_not _ _ _

lemma Hs_union_Gs (V : Finset α) : g.Hs V ∪ g.Gs V = V := Finset.filter_union_filter_not_eq _ _

lemma disjoint_Js_Ks (V : Finset α) : Disjoint (g.Js V) (g.Ks V) := by
  rw [Finset.disjoint_left]
  intro v h1 h2
  exact (Finset.mem_filter.1 h2).2.2 (Finset.mem_filter.1 h1).2

lemma Js_union_Ks (V : Finset α) : g.Js V ∪ g.Ks V = g.Gs V := by
  ext v
  simp only [Js, Ks, Gs, Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨hv, h3, -⟩ | ⟨hv, h2, -⟩)
    · exact ⟨hv, by omega⟩
    · exact ⟨hv, h2⟩
  · rintro ⟨hv, h2⟩
    by_cases h : g.deg v = 3 ∧ 0 < g.inc v (g.Hs V)
    · exact Or.inl ⟨hv, h⟩
    · exact Or.inr ⟨hv, h2, h⟩

lemma Js_subset (V : Finset α) : g.Js V ⊆ V := Finset.filter_subset _ _
lemma Ks_subset (V : Finset α) : g.Ks V ⊆ V := Finset.filter_subset _ _
lemma Hs_subset (V : Finset α) : g.Hs V ⊆ V := Finset.filter_subset _ _

lemma disjoint_Hs_Js (V : Finset α) : Disjoint (g.Hs V) (g.Js V) :=
  (g.disjoint_Hs_Gs V).mono_right (by rw [← g.Js_union_Ks]; exact Finset.subset_union_left)

/-! ## The degree identities (C1), (C3), (C4) -/

section Ledger

variable (V Fl : Finset α) (hE : ∀ e ∈ g.E, g.src e ∈ V ∧ g.tgt e ∈ V)
  (hdeg : ∀ v ∈ V, 2 ≤ g.deg v ∧ g.deg v ≤ 4)

include hE in
/-- Degree sum over a set `A ⊆ V`, split by the classes `H, J, K`. -/
lemma deg_sum_split (A : Finset α) :
    ∑ v ∈ A, g.deg v = ∑ v ∈ A, g.inc v (g.Hs V) + ∑ v ∈ A, g.inc v (g.Js V) +
      ∑ v ∈ A, g.inc v (g.Ks V) + g.bIn A := by
  have hV : V = g.Hs V ∪ (g.Js V ∪ g.Ks V) := by rw [g.Js_union_Ks, g.Hs_union_Gs]
  have hd1 : Disjoint (g.Hs V) (g.Js V ∪ g.Ks V) := by rw [g.Js_union_Ks]; exact g.disjoint_Hs_Gs V
  rw [← g.sum_stubs, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [g.deg_eq V hE v]
  conv_lhs => rw [hV, g.inc_union v hd1, g.inc_union v (g.disjoint_Js_Ks V)]
  ring

include hdeg in
lemma inc_K_H_le (v : α) (hv : v ∈ g.Ks V) : g.inc v (g.Hs V) + 12 ≤ 4 * g.deg v := by
  simp only [Ks, Finset.mem_filter] at hv
  obtain ⟨hvV, h2, h3⟩ := hv
  have := hdeg v hvV
  have hle := g.inc_le_deg v (g.Hs V)
  by_cases h : g.deg v = 3
  · have : g.inc v (g.Hs V) = 0 := by by_contra h0; exact h3 ⟨h, Nat.pos_of_ne_zero h0⟩
    omega
  · omega


lemma deg_of_mem_Hs {V : Finset α} {v : α} (hv : v ∈ g.Hs V) : g.deg v = 2 :=
  (Finset.mem_filter.1 hv).2

lemma deg_of_mem_Js {V : Finset α} {v : α} (hv : v ∈ g.Js V) : g.deg v = 3 :=
  (Finset.mem_filter.1 hv).2.1

/-- The charge `M = e(J,J) + Σ_J 2 (inc v H - 1)`. -/
def charge (V : Finset α) : ℝ :=
  g.eIn (g.Js V) (g.Js V) + ∑ v ∈ g.Js V, (2 * (g.inc v (g.Hs V) : ℝ) - 2)

include hE hdeg in
/-- **(C5)**: `M ≥ 4|V| - 5Y - hC - C - κ(G) - κ(K)`, from the degree identities (C1), (C3), (C4)
and the component estimates (C2). -/
theorem charge_lower :
    4 * (V.card : ℝ) - 5 * g.Ysum V - (g.bIn (g.Hs V) + 2 * g.eIn (g.Hs V) (g.Hs V)) -
      (g.bIn V + 2 * g.eIn (g.Hs V) (g.Hs V)) - g.stubless (g.Gs V) - g.stubless (g.Ks V) ≤
      g.charge V := by
  have hdHG := g.disjoint_Hs_Gs V
  have hdJK := g.disjoint_Js_Ks V
  have hcV : V.card = (g.Hs V).card + (g.Gs V).card := by
    have := Finset.card_union_of_disjoint hdHG; rwa [g.Hs_union_Gs] at this
  have hcG : (g.Gs V).card = (g.Js V).card + (g.Ks V).card := by
    have := Finset.card_union_of_disjoint hdJK; rwa [g.Js_union_Ks] at this
  have hbV : g.bIn V = g.bIn (g.Hs V) + g.bIn (g.Gs V) := by
    have := g.bIn_union hdHG; rwa [g.Hs_union_Gs] at this
  have hbG : g.bIn (g.Gs V) = g.bIn (g.Js V) + g.bIn (g.Ks V) := by
    have := g.bIn_union hdJK; rwa [g.Js_union_Ks] at this
  have sH := g.deg_sum_split V hE (g.Hs V)
  have sJ := g.deg_sum_split V hE (g.Js V)
  have sK := g.deg_sum_split V hE (g.Ks V)
  have dH : ∑ v ∈ g.Hs V, g.deg v = 2 * (g.Hs V).card := by
    rw [Finset.sum_congr rfl fun v hv => g.deg_of_mem_Hs hv, Finset.sum_const, smul_eq_mul,
      mul_comm]
  have dJ : ∑ v ∈ g.Js V, g.deg v = 3 * (g.Js V).card := by
    rw [Finset.sum_congr rfl fun v hv => g.deg_of_mem_Js hv, Finset.sum_const, smul_eq_mul,
      mul_comm]
  have hKle : ∑ v ∈ g.Ks V, g.inc v (g.Hs V) + 12 * (g.Ks V).card ≤
      4 * ∑ v ∈ g.Ks V, g.deg v := by
    rw [Finset.mul_sum, show 12 * (g.Ks V).card = ∑ v ∈ g.Ks V, 12 by simp [mul_comm],
      ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun v hv => g.inc_K_H_le V hdeg v hv
  have iHH := g.sum_inc (g.Hs V) (g.Hs V)
  have iHJ := g.sum_inc (g.Hs V) (g.Js V)
  have iJH := g.sum_inc (g.Js V) (g.Hs V)
  have iHK := g.sum_inc (g.Hs V) (g.Ks V)
  have iKH := g.sum_inc (g.Ks V) (g.Hs V)
  have iJJ := g.sum_inc (g.Js V) (g.Js V)
  have iJK := g.sum_inc (g.Js V) (g.Ks V)
  have iKJ := g.sum_inc (g.Ks V) (g.Js V)
  have iKK := g.sum_inc (g.Ks V) (g.Ks V)
  have cG := g.card_le_eIn_add_bIn_add_stubless (g.Gs V)
  have cK := g.card_le_eIn_add_bIn_add_stubless (g.Ks V)
  have eGG : g.eIn (g.Gs V) (g.Gs V) = g.eIn (g.Js V) (g.Js V) + g.eIn (g.Js V) (g.Ks V) +
      g.eIn (g.Ks V) (g.Js V) + g.eIn (g.Ks V) (g.Ks V) := by
    have h1 := g.eIn_union_left (B := g.Js V ∪ g.Ks V) hdJK
    have h2 := g.eIn_union_right (A := g.Js V) hdJK
    have h3 := g.eIn_union_right (A := g.Ks V) hdJK
    rw [h2, h3, g.Js_union_Ks] at h1
    rw [h1]; ring
  have hY : g.Ysum V = ((∑ v ∈ g.Js V, g.deg v : ℕ) : ℝ) + ((∑ v ∈ g.Ks V, g.deg v : ℕ) : ℝ) -
      2 * (g.Gs V).card := by
    unfold Ysum
    have h1 := Finset.sum_union hdHG (f := fun v => (g.deg v : ℝ) - 2)
    rw [g.Hs_union_Gs] at h1
    have h2 := Finset.sum_union hdJK (f := fun v => (g.deg v : ℝ) - 2)
    rw [g.Js_union_Ks] at h2
    have h0 : ∑ v ∈ g.Hs V, ((g.deg v : ℝ) - 2) = 0 :=
      Finset.sum_eq_zero fun v hv => by rw [g.deg_of_mem_Hs hv]; norm_num
    rw [h1, h2, h0, hcG]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    push_cast; ring
  have hM : g.charge V = (g.eIn (g.Js V) (g.Js V) : ℝ) +
      2 * ((∑ v ∈ g.Js V, g.inc v (g.Hs V) : ℕ) : ℝ) - 2 * (g.Js V).card := by
    unfold charge
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_const, nsmul_eq_mul]
    push_cast; ring
  rw [hM, hY]
  rify at hcV hcG hbV hbG sH sJ sK dH dJ hKle iHH iHJ iJH iHK iKH iJJ iJK iKJ iKK cG cK eGG
  push_cast
  linarith
/-! ## The charge distribution (C6) -/

/-- Per-vertex bound of the charge distribution: for `v ∈ J` receiving `a ≤ inc v J` edges, and
`a = 0` unless `v` can receive edges. -/
lemma charge_vertex_le (V Fl : Finset α) (v : α) (hv : v ∈ g.Js V) (a : ℕ)
    (ha : a ≤ g.inc v (g.Js V)) (ha0 : ¬ g.Qual V Fl v → a = 0) :
    2 * g.inc v (g.Hs V) + a ≤ 2 + 4 * (if v ∈ Fl then 1 else 0) + 2 * g.inc v (g.Hs V ∩ Fl) +
      4 * (if v ∉ Fl ∧ 2 ≤ g.inc v (g.Hs V \ Fl) then 1 else 0) := by
  have hd3 := g.deg_of_mem_Js hv
  have hpos : 0 < g.inc v (g.Hs V) := (Finset.mem_filter.1 hv).2.2
  have hHJ : g.inc v (g.Hs V) + g.inc v (g.Js V) ≤ 3 := by
    rw [← g.inc_union v (g.disjoint_Hs_Js V), ← hd3]; exact g.inc_le_deg v _
  have hsplit : g.inc v (g.Hs V) = g.inc v (g.Hs V ∩ Fl) + g.inc v (g.Hs V \ Fl) := by
    have := g.inc_union v (Finset.disjoint_sdiff_inter (g.Hs V) Fl)
    rw [Finset.sdiff_union_inter] at this
    omega
  unfold Qual at ha0
  by_cases hF : v ∈ Fl
  · simp only [hF, if_true, not_true_eq_false, false_and, if_false]
    omega
  · simp only [hF, if_false, not_false_eq_true, true_and, false_or] at ha0 ⊢
    by_cases h2 : 2 ≤ g.inc v (g.Hs V \ Fl)
    · have := ha0 (by omega)
      simp only [h2, if_true]; omega
    · simp only [h2, if_false]
      by_cases h1 : g.inc v (g.Hs V \ Fl) = 0
      · omega
      · have := ha0 h1; omega

/-- **(C6)**: the charge is at most `4 |Fl| + 4 #defective + #exceptional`.  `J–J` edges are
assigned to an end that can receive them; a flagged `J` keeps at most `4`, an unflagged `J`
passes at most `2` to each incidence with a flagged `H`, and a flagged `H` (degree two) receives at
most `4`. -/
theorem charge_le (V Fl : Finset α) :
    g.charge V ≤ 4 * Fl.card + 4 * g.defJ V Fl + g.excE V Fl := by
  set J := g.Js V
  set Q := g.Qual V Fl
  set E1 := g.E.filter (fun e => g.src e ∈ J ∧ g.tgt e ∈ J ∧ Q (g.src e))
  set E2 := g.E.filter (fun e => g.src e ∈ J ∧ g.tgt e ∈ J ∧ ¬ Q (g.src e) ∧ Q (g.tgt e))
  set a : α → ℕ := fun v => (E1.filter (fun e => g.src e = v)).card +
    (E2.filter (fun e => g.tgt e = v)).card
  -- the edges of `J` split into assigned and exceptional ones
  have hJJ : g.eIn J J = ∑ v ∈ J, a v + g.excE V Fl := by
    have h1 : E1.card = ∑ v ∈ J, (E1.filter (fun e => g.src e = v)).card :=
      Finset.card_eq_sum_card_fiberwise fun e he => (Finset.mem_filter.1 he).2.1
    have h2 : E2.card = ∑ v ∈ J, (E2.filter (fun e => g.tgt e = v)).card :=
      Finset.card_eq_sum_card_fiberwise fun e he => (Finset.mem_filter.1 he).2.2.1
    have h3 : g.eIn J J = E1.card + E2.card + g.excE V Fl := by
      unfold eIn excE
      rw [← Finset.card_union_of_disjoint, ← Finset.card_union_of_disjoint]
      · congr 1; ext e; simp only [E1, E2, Q, Finset.mem_union, Finset.mem_filter]; tauto
      · rw [Finset.disjoint_left]; intro e h h'
        simp only [E1, E2, Q, Finset.mem_union, Finset.mem_filter] at h h'
        rcases h with h | h <;> tauto
      · rw [Finset.disjoint_left]; intro e h h'
        simp only [E1, E2, Q, Finset.mem_filter] at h h'
        tauto
    rw [h3, h1, h2, Finset.sum_add_distrib]
  have ha : ∀ v, a v ≤ g.inc v J := fun v =>
    add_le_add
      (Finset.card_le_card fun e he => by
        simp only [E1, Finset.mem_filter] at he ⊢; exact ⟨he.1.1, he.2, he.1.2.2.1⟩)
      (Finset.card_le_card fun e he => by
        simp only [E2, Finset.mem_filter] at he ⊢; exact ⟨he.1.1, he.2, he.1.2.1⟩)
  have ha0 : ∀ v, ¬ Q v → a v = 0 := by
    intro v hv
    simp only [a, Nat.add_eq_zero_iff, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    constructor
    · intro e he hsv
      simp only [E1, Finset.mem_filter] at he
      exact hv (hsv ▸ he.2.2.2)
    · intro e he htv
      simp only [E2, Finset.mem_filter] at he
      exact hv (htv ▸ he.2.2.2.2)
  -- the per-vertex bound, summed
  have hsum := Finset.sum_le_sum fun v (hv : v ∈ J) =>
    g.charge_vertex_le V Fl v hv (a v) (ha v) (ha0 v)
  have hL : ∑ v ∈ J, (2 * g.inc v (g.Hs V) + a v) =
      2 * ∑ v ∈ J, g.inc v (g.Hs V) + ∑ v ∈ J, a v := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hR : ∑ v ∈ J, (2 + 4 * (if v ∈ Fl then 1 else 0) + 2 * g.inc v (g.Hs V ∩ Fl) +
      4 * (if v ∉ Fl ∧ 2 ≤ g.inc v (g.Hs V \ Fl) then 1 else 0)) =
      2 * J.card + 4 * (J.filter (fun v => v ∈ Fl)).card +
        2 * ∑ v ∈ J, g.inc v (g.Hs V ∩ Fl) + 4 * g.defJ V Fl := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_boole, Finset.sum_boole,
      Finset.sum_const, smul_eq_mul]
    simp only [Nat.cast_id]
    rw [mul_comm J.card 2]
    rfl
  rw [hL, hR] at hsum
  -- flagged `H` vertices receive at most `4`
  have hHF : ∑ v ∈ J, g.inc v (g.Hs V ∩ Fl) ≤ 2 * (g.Hs V ∩ Fl).card := by
    have e1 := g.sum_inc J (g.Hs V ∩ Fl)
    have e2 := g.sum_inc (g.Hs V ∩ Fl) J
    have e3 : ∑ w ∈ g.Hs V ∩ Fl, g.inc w J ≤ ∑ w ∈ g.Hs V ∩ Fl, g.deg w :=
      Finset.sum_le_sum fun w _ => g.inc_le_deg w J
    have e4 : ∑ w ∈ g.Hs V ∩ Fl, g.deg w = 2 * (g.Hs V ∩ Fl).card := by
      rw [Finset.sum_congr rfl fun w hw => g.deg_of_mem_Hs (Finset.mem_inter.1 hw).1,
        Finset.sum_const, smul_eq_mul, mul_comm]
    omega
  have hFl : (J.filter (fun v => v ∈ Fl)).card + (g.Hs V ∩ Fl).card ≤ Fl.card := by
    rw [← Finset.card_union_of_disjoint]
    · refine Finset.card_le_card fun v hv => ?_
      rcases Finset.mem_union.1 hv with h | h
      · exact (Finset.mem_filter.1 h).2
      · exact (Finset.mem_inter.1 h).2
    · rw [Finset.disjoint_left]
      intro v h1 h2
      exact Finset.disjoint_left.1 (g.disjoint_Hs_Js V) (Finset.mem_inter.1 h2).1
        (Finset.mem_filter.1 h1).1
  have hM : g.charge V = (g.eIn J J : ℝ) + 2 * ((∑ v ∈ J, g.inc v (g.Hs V) : ℕ) : ℝ) -
      2 * J.card := by
    unfold charge
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_const, nsmul_eq_mul]
    push_cast; ring
  rw [hM, hJJ]
  rify at hsum hHF hFl
  push_cast at hsum ⊢
  linarith

include hE hdeg in
/-- **The local charging ledger** (Verification Guide (C1)–(C6)).  For a finite multigraph with
stubs whose edges lie in `V` and whose degrees on `V` are `2`, `3` or `4`, and any set `Fl` of
flagged vertices:

  `4 |V| ≤ 5 Y + C + hC + κ(G) + κ(K) + 4 |Fl| + 4 #defective + #exceptional`,

with `C = b(V) + 2 e(H,H)` and `hC = b(H) + 2 e(H,H)` (each `H–H` edge replaced by two virtual
cap stubs). -/
theorem charging_ledger :
    4 * (V.card : ℝ) ≤ 5 * g.Ysum V + (g.bIn V + 2 * g.eIn (g.Hs V) (g.Hs V)) +
      (g.bIn (g.Hs V) + 2 * g.eIn (g.Hs V) (g.Hs V)) + g.stubless (g.Gs V) +
      g.stubless (g.Ks V) + 4 * Fl.card + 4 * g.defJ V Fl + g.excE V Fl := by
  have h1 := g.charge_lower V hE hdeg
  have h2 := g.charge_le V Fl
  linarith

end Ledger

end StubGraph

end LocalCharge

end Erdos99

end

end LocalCharge

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `BoundaryPortBounds`
-/

section BoundaryPortBounds

/-!
# WP5: boundary port bounds (Verification Guide §6)

This file supplies the boundary geometry of `TRACK_COUNT_REVISED_PLAN.md`, WP5, with explicit
error terms instead of `o(1)`.

* §6.1, the normalised estimate (B1): `normalized_endpoint_bound` (in any real inner product
  space) and its coordinate form `normalized_endpoint_bound_coord`; the averaging of spine steps,
  `spine_average_bounds`;
* §6.2, the macroscopic-port margin: `macroscopic_port_margin`, with the explicit
  `k_λ = min (1/10) (a*³ λ² / 8)`;
* §6.3, three macroscopic ports cannot nearly cancel: `three_ports_projection` (the exact
  statement), `three_ports_inner` (pairwise scalar products `-1/2`) and the quantitative
  `three_ports_noncancel`, which gives the explicit constant `η_λ = min 1 k`
  (no compactness argument is needed);
* §6.4, selected ports belong to distinct tracks: the inequality `selected_ends_ineq` and the
  track-level statement `selected_port_unique`: a track with at least `λ D` rhombi has at most one
  selected port (edge and outgoing normal) once the flag tolerance and the endpoint error are small
  compared with `a* λ`;
* §6.5, the length estimates: `length_ratio_bounds` and `normalized_length_le`;
* the interface with the existing annular statement: `IsSelectedTrack.mono`,
  `isSelectedTrack_of_port` and `mem_longTracks_of_le`.
-/

open scoped BigOperators Real
open ComplexConjugate

@[expose] public noncomputable section

open Classical

namespace Erdos99

namespace BoundaryPort

/-! ## §6.1: the normalised estimate (B1) -/

/-- **(B1)**, vector form. Let `ν` be a unit radial direction and let a track's terminal midpoints
`x, y` satisfy `|x / D - ν / 2| ≤ δ` and `|y / D| ≤ 1/2 + δ` (positions relative to the centre).
If `y - x = r w`, then with `ℓ = r / D`,
`ℓ² |w|² + ℓ (ν · w) ≤ 2 δ + 4 δ²`. -/
theorem normalized_endpoint_bound {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {ν w x y : V} {D r δ : ℝ} (hν : ‖ν‖ = 1)
    (hx : ‖D⁻¹ • x - (1 / 2 : ℝ) • ν‖ ≤ δ) (hy : ‖D⁻¹ • y‖ ≤ 1 / 2 + δ) (hxy : y - x = r • w) :
    (r / D) ^ 2 * ‖w‖ ^ 2 + (r / D) * inner ℝ ν w ≤ 2 * δ + 4 * δ ^ 2 := by
  set e := D⁻¹ • x - (1 / 2 : ℝ) • ν
  have hyD : D⁻¹ • y = ((1 / 2 : ℝ) • ν + (r / D) • w) + e := by
    have : y = x + r • w := by rw [← hxy]; abel
    rw [this, smul_add, smul_smul, show D⁻¹ * r = r / D by ring]
    simp only [e]
    abel
  have hnorm : ‖(1 / 2 : ℝ) • ν + (r / D) • w‖ ≤ 1 / 2 + 2 * δ := by
    have h := norm_sub_le (D⁻¹ • y) e
    have h' : D⁻¹ • y - e = (1 / 2 : ℝ) • ν + (r / D) • w := by rw [hyD]; abel
    rw [h'] at h
    linarith
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right, hν] at hsq
  rw [Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), Real.norm_eq_abs] at hsq
  simp only [mul_pow, sq_abs] at hsq
  nlinarith

/-- **(B1)**, coordinate form in the plane. If the normalised displacement is
`w = s n + t (J n)` with `n` a unit normal, and `a = n · ν`, `b = (J n) · ν`, then
`ℓ² (s² + t²) + ℓ (a s + b t) ≤ 2 δ + 4 δ²`. -/
theorem normalized_endpoint_bound_coord {ν n x y : Plane} {D r δ s t : ℝ}
    (hν : ‖ν‖ = 1) (hn : ‖n‖ = 1)
    (hx : ‖D⁻¹ • x - (1 / 2 : ℝ) • ν‖ ≤ δ) (hy : ‖D⁻¹ • y‖ ≤ 1 / 2 + δ)
    (hxy : y - x = r • (s • n + t • rot n)) :
    (r / D) ^ 2 * (s ^ 2 + t ^ 2) +
      (r / D) * (inner ℝ n ν * s + inner ℝ (rot n) ν * t) ≤ 2 * δ + 4 * δ ^ 2 := by
  have h := normalized_endpoint_bound hν hx hy hxy
  have hw : ‖s • n + t • rot n‖ ^ 2 = s ^ 2 + t ^ 2 := by
    have e := norm_sq_frame hn (s • n + t • rot n)
    rw [e, inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_smul_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq, norm_rot, hn]
    have h0 : inner ℝ n (rot n) = 0 := by
      rw [inner_rot_coord]; ring
    have h0' : inner ℝ (rot n) n = 0 := by rw [real_inner_comm]; exact h0
    rw [h0, h0']; ring
  have hi : inner ℝ ν (s • n + t • rot n) = inner ℝ n ν * s + inner ℝ (rot n) ν * t := by
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, real_inner_comm n ν,
      real_inner_comm (rot n) ν]; ring
  rw [hw, hi] at h
  exact h

/-- The averaging step of §6.1: if each of the `r ≥ 1` spine steps `v_i` of a track has normal
projection at least `a*` and transverse projection at most `1/2` in absolute value, then so does
their average `w = (1/r) Σ v_i`; that is, `s ≥ a*` and `|t| ≤ 1/2`. -/
theorem spine_average_bounds {ι : Type*} {S : Finset ι} (hS : S.Nonempty) (v : ι → Plane)
    (n : Plane) (h1 : ∀ i ∈ S, aStar ≤ inner ℝ (v i) n)
    (h2 : ∀ i ∈ S, |inner ℝ (v i) (rot n)| ≤ 1 / 2) :
    aStar ≤ inner ℝ ((S.card : ℝ)⁻¹ • ∑ i ∈ S, v i) n ∧
      |inner ℝ ((S.card : ℝ)⁻¹ • ∑ i ∈ S, v i) (rot n)| ≤ 1 / 2 := by
  have hc : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  rw [real_inner_smul_left, real_inner_smul_left, sum_inner, sum_inner]
  constructor
  · rw [inv_mul_eq_div, le_div_iff₀ hc]
    have := Finset.card_nsmul_le_sum S (fun i => inner ℝ (v i) n) aStar h1
    rw [nsmul_eq_mul] at this; linarith
  · rw [abs_mul, abs_inv, abs_of_pos hc, inv_mul_eq_div, div_le_iff₀ hc]
    have h3 := Finset.abs_sum_le_sum_abs (fun i => inner ℝ (v i) (rot n)) S
    have h4 := Finset.sum_le_card_nsmul S (fun i => |inner ℝ (v i) (rot n)|) (1 / 2) h2
    rw [nsmul_eq_mul] at h4; linarith

/-! ## §6.2: the macroscopic-port margin -/

lemma aStar_sq : aStar ^ 2 = 3 / 4 := by
  unfold aStar; rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num

lemma aStar_lt_one : aStar < 1 := by
  have := aStar_sq; have := aStar_pos; nlinarith

lemma one_le_sqrt_three : 1 ≤ √3 := by
  rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)

/-- **The macroscopic-port margin** (Verification Guide §6.2). Fix `0 < λ ≤ 1`. Suppose a track of
normalised length `ℓ = r / D ≥ λ` leaves a boundary port with `a = z · τ` (`a² + b² = 1`), its
normalised displacement has coordinates `s ≥ a*`, `|t| ≤ 1/2`, and (B1) holds with
`2 δ + 4 δ² ≤ a*² λ² / 4`. Then `a < 1/2 - k_λ` with `k_λ = min (1/10) (a*³ λ² / 8)`. -/
theorem macroscopic_port_margin {a b s t ℓ lam δ : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (hab : a ^ 2 + b ^ 2 = 1) (hs : aStar ≤ s) (ht : |t| ≤ 1 / 2) (hℓ : lam ≤ ℓ)
    (hδ : 2 * δ + 4 * δ ^ 2 ≤ aStar ^ 2 * lam ^ 2 / 4)
    (hB1 : ℓ ^ 2 * (s ^ 2 + t ^ 2) + ℓ * (a * s + b * t) ≤ 2 * δ + 4 * δ ^ 2) :
    a < 1 / 2 - min (1 / 10) (aStar ^ 3 * lam ^ 2 / 8) := by
  obtain ⟨k, hkdef⟩ : ∃ k, k = min (1 / 10) (aStar ^ 3 * lam ^ 2 / 8) := ⟨_, rfl⟩
  rw [← hkdef]
  have ha0 := aStar_pos
  have ha1 := aStar_lt_one
  have hasq := aStar_sq
  have hk1 : k ≤ 1 / 10 := hkdef ▸ min_le_left _ _
  have hk2 : k ≤ aStar ^ 3 * lam ^ 2 / 8 := hkdef ▸ min_le_right _ _
  have hk0 : 0 < k := hkdef ▸ lt_min (by norm_num) (by positivity)
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le hlam0 hℓ
  by_contra hcon
  push_neg at hcon
  have ha_nn : 0 ≤ a := by linarith
  -- `|b| ≤ a* + k`
  have hb : |b| ≤ aStar + k := by
    have h1 : (1 / 2 - k) ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (by linarith) hcon 2
    have h3 : √3 = 2 * aStar := by rw [show aStar = √3 / 2 from rfl]; ring
    have h2 : b ^ 2 ≤ (aStar + k) ^ 2 := by
      have e1 : (aStar + k) ^ 2 = 3 / 4 + √3 * k + k ^ 2 := by
        have : (aStar + k) ^ 2 = aStar ^ 2 + (2 * aStar) * k + k ^ 2 := by ring
        rw [this, hasq, ← h3]
      have e2 : k ≤ √3 * k := le_mul_of_one_le_left hk0.le one_le_sqrt_three
      have e3 : (1 / 2 - k) ^ 2 = 1 / 4 - k + k ^ 2 := by ring
      linarith [sq_nonneg k]
    exact abs_le.2 (abs_le_of_sq_le_sq' h2 (by positivity))
  -- `a s + b t ≥ -2 k`
  have hlin : -(2 * k) ≤ a * s + b * t := by
    have h1 : a * aStar ≤ a * s := mul_le_mul_of_nonneg_left hs ha_nn
    have h2 : -(|b| * (1 / 2)) ≤ b * t := by
      have : |b * t| ≤ |b| * (1 / 2) := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left ht (abs_nonneg b)
      linarith [neg_abs_le (b * t)]
    have h3 := mul_le_mul_of_nonneg_right hcon ha0.le
    have h4 : k * aStar ≤ k := by
      have := mul_le_mul_of_nonneg_left ha1.le hk0.le; linarith
    linarith
  have hst : aStar ^ 2 ≤ s ^ 2 + t ^ 2 := by
    have := pow_le_pow_left₀ ha0.le hs 2
    linarith [sq_nonneg t]
  have hmain : aStar ^ 2 * ℓ ^ 2 ≤ aStar ^ 2 * lam ^ 2 / 4 + 2 * k * ℓ := by
    have e1 : ℓ ^ 2 * aStar ^ 2 ≤ ℓ ^ 2 * (s ^ 2 + t ^ 2) :=
      mul_le_mul_of_nonneg_left hst (by positivity)
    have e2 := mul_le_mul_of_nonneg_left hlin hℓ0.le
    linarith
  have hk3 : 2 * k * ℓ ≤ aStar ^ 2 * (aStar * lam ^ 2 * ℓ / 4) := by
    have := mul_le_mul_of_nonneg_right (by linarith : 2 * k ≤ aStar ^ 3 * lam ^ 2 / 4) hℓ0.le
    linarith [show aStar ^ 3 * lam ^ 2 / 4 * ℓ = aStar ^ 2 * (aStar * lam ^ 2 * ℓ / 4) by ring]
  have hlam2 : lam ^ 2 ≤ lam := by
    have := mul_le_mul_of_nonneg_left hlam1 hlam0.le
    linarith [show lam * lam = lam ^ 2 by ring]
  have h5 : ℓ ^ 2 ≤ lam ^ 2 / 4 + aStar * lam ^ 2 * ℓ / 4 := by
    have : aStar ^ 2 * ℓ ^ 2 ≤ aStar ^ 2 * (lam ^ 2 / 4 + aStar * lam ^ 2 * ℓ / 4) := by
      linarith [show aStar ^ 2 * (lam ^ 2 / 4 + aStar * lam ^ 2 * ℓ / 4) =
        aStar ^ 2 * lam ^ 2 / 4 + aStar ^ 2 * (aStar * lam ^ 2 * ℓ / 4) by ring]
    exact le_of_mul_le_mul_left this (by positivity)
  have h6 : aStar * lam ^ 2 * ℓ ≤ lam * ℓ := by
    have e1 := mul_le_mul_of_nonneg_right hlam2 (by positivity : (0 : ℝ) ≤ aStar * ℓ)
    have e2 := mul_le_mul_of_nonneg_right ha1.le (by positivity : (0 : ℝ) ≤ lam * ℓ)
    nlinarith
  have h7 : lam * lam ≤ lam * ℓ := mul_le_mul_of_nonneg_left hℓ hlam0.le
  have h8 : lam * ℓ ≤ ℓ * ℓ := mul_le_mul_of_nonneg_right hℓ hℓ0.le
  have h9 : 0 < lam * ℓ := by positivity
  nlinarith

/-! ## §6.3: three macroscopic ports cannot nearly cancel -/

/-- For three unit complex numbers, `c₁² + c₂² + c₃² = S² - 2 c₁ c₂ c₃ conj S` with
`S = c₁ + c₂ + c₃`. -/
lemma sum_sq_unit_identity {c1 c2 c3 : ℂ} (h1 : c1 * conj c1 = 1) (h2 : c2 * conj c2 = 1)
    (h3 : c3 * conj c3 = 1) :
    c1 ^ 2 + c2 ^ 2 + c3 ^ 2 =
      (c1 + c2 + c3) ^ 2 - 2 * (c1 * c2 * c3) * conj (c1 + c2 + c3) := by
  simp only [map_add]
  linear_combination (2 * c2 * c3) * h1 + (2 * c1 * c3) * h2 + (2 * c1 * c2) * h3

/-- The real part of `c₁² + c₂² + c₃²` for unit `c_j` is at least `-|S|² - 2|S|`. -/
lemma sum_sq_unit_re_ge {c1 c2 c3 : ℂ} (h1 : ‖c1‖ = 1) (h2 : ‖c2‖ = 1) (h3 : ‖c3‖ = 1) :
    -(‖c1 + c2 + c3‖ ^ 2) - 2 * ‖c1 + c2 + c3‖ ≤ (c1 ^ 2 + c2 ^ 2 + c3 ^ 2).re := by
  have m : ∀ c : ℂ, ‖c‖ = 1 → c * conj c = 1 := fun c hc => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]; simp
  rw [sum_sq_unit_identity (m _ h1) (m _ h2) (m _ h3), Complex.sub_re]
  set S := c1 + c2 + c3
  have e1 : -(‖S‖ ^ 2) ≤ (S ^ 2).re := by
    have := Complex.abs_re_le_norm (S ^ 2)
    rw [norm_pow] at this
    linarith [neg_abs_le (S ^ 2).re]
  have e2 : (2 * (c1 * c2 * c3) * conj S).re ≤ 2 * ‖S‖ := by
    have := Complex.re_le_norm (2 * (c1 * c2 * c3) * conj S)
    rw [norm_mul, norm_mul, norm_mul, norm_mul, h1, h2, h3, Complex.norm_conj] at this
    simpa using this
  linarith

/-- The real-variable core of §6.3: projections `x_j ∈ [-1, 1/2 - k]` with
`|Σ x_j| ≤ s` and `Σ x_j² ≥ (3 - s² - 2 s)/2` force `s ≥ min 1 k`. -/
lemma three_ports_real {x1 x2 x3 s k : ℝ} (hk : 0 < k) (hs : 0 ≤ s)
    (h1 : -1 ≤ x1) (h2 : -1 ≤ x2) (h3 : -1 ≤ x3)
    (u1 : x1 ≤ 1 / 2 - k) (u2 : x2 ≤ 1 / 2 - k) (u3 : x3 ≤ 1 / 2 - k)
    (hsum : |x1 + x2 + x3| ≤ s) (hsq : (3 - s ^ 2 - 2 * s) / 2 ≤ x1 ^ 2 + x2 ^ 2 + x3 ^ 2) :
    min 1 k ≤ s := by
  by_contra hcon
  push_neg at hcon
  have hs1 : s < 1 := lt_of_lt_of_le hcon (min_le_left _ _) |> fun h => by
    rcases lt_min_iff.1 (by simpa using hcon) with ⟨a, _⟩; exact a
  have hsk : s < k := by rcases lt_min_iff.1 (by simpa using hcon) with ⟨_, b⟩; exact b
  have hs' := abs_le.1 hsum
  have p1 : k * (x1 + 1) ≤ (x1 + 1) * (1 / 2 - x1) := by nlinarith
  have p2 : k * (x2 + 1) ≤ (x2 + 1) * (1 / 2 - x2) := by nlinarith
  have p3 : k * (x3 + 1) ≤ (x3 + 1) * (1 / 2 - x3) := by nlinarith
  nlinarith

/-- **Three macroscopic ports cannot nearly cancel** (Verification Guide §6.3, quantitative form).
If three unit vectors `u₁, u₂, u₃` all have projection at most `1/2 - k` on a unit tangent `τ`
(`k > 0`), then `|u₁ + u₂ + u₃| ≥ min 1 k`. This is the constant `η_λ` of the Guide, obtained
explicitly rather than by compactness. -/
theorem three_ports_noncancel {u1 u2 u3 τ : Plane} {k : ℝ} (hk : 0 < k) (hu1 : ‖u1‖ = 1)
    (hu2 : ‖u2‖ = 1) (hu3 : ‖u3‖ = 1) (hτ : ‖τ‖ = 1)
    (h1 : inner ℝ u1 τ ≤ 1 / 2 - k) (h2 : inner ℝ u2 τ ≤ 1 / 2 - k)
    (h3 : inner ℝ u3 τ ≤ 1 / 2 - k) :
    min 1 k ≤ ‖u1 + u2 + u3‖ := by
  -- complex coordinates in the frame `(τ, J τ)`
  let c : Plane → ℂ := fun u => ⟨inner ℝ u τ, inner ℝ u (rot τ)⟩
  have hc : ∀ u : Plane, ‖c u‖ = ‖u‖ := fun u => by
    have e := inner_sq_add_inner_rot_sq τ u
    rw [hτ, one_pow, mul_one] at e
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← e, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_apply]
    ring
  have hcadd : c (u1 + u2 + u3) = c u1 + c u2 + c u3 := by
    apply Complex.ext <;> simp [c, inner_add_left]
  have hsq : ∀ u : Plane, ‖u‖ = 1 → ((c u) ^ 2).re = 2 * inner ℝ u τ ^ 2 - 1 := fun u hu => by
    have e := inner_sq_add_inner_rot_sq τ u
    rw [hτ, hu] at e
    simp only [c, pow_two, Complex.mul_re]
    nlinarith
  have hre := sum_sq_unit_re_ge (c1 := c u1) (c2 := c u2) (c3 := c u3) (by rw [hc]; exact hu1)
    (by rw [hc]; exact hu2) (by rw [hc]; exact hu3)
  rw [← hcadd, hc, Complex.add_re, Complex.add_re, hsq u1 hu1, hsq u2 hu2, hsq u3 hu3] at hre
  have hb : ∀ u : Plane, ‖u‖ = 1 → -1 ≤ inner ℝ u τ := fun u hu => by
    have := abs_real_inner_le_norm u τ
    rw [hu, hτ, one_mul] at this
    linarith [neg_abs_le (inner ℝ u τ)]
  have hsum : |inner ℝ u1 τ + inner ℝ u2 τ + inner ℝ u3 τ| ≤ ‖u1 + u2 + u3‖ := by
    have := abs_real_inner_le_norm (u1 + u2 + u3) τ
    rw [hτ, mul_one, inner_add_left, inner_add_left] at this
    exact this
  exact three_ports_real hk (norm_nonneg _) (hb u1 hu1) (hb u2 hu2) (hb u3 hu3) h1 h2 h3 hsum
    (by linarith)

/-- **Three unit vectors with zero sum** (Verification Guide §6.3, exact form): for any unit
tangent `τ`, at least one of them has projection at least `1/2` on `τ`. -/
theorem three_ports_projection {u1 u2 u3 τ : Plane} (hu1 : ‖u1‖ = 1) (hu2 : ‖u2‖ = 1)
    (hu3 : ‖u3‖ = 1) (hτ : ‖τ‖ = 1) (h0 : u1 + u2 + u3 = 0) :
    1 / 2 ≤ inner ℝ u1 τ ∨ 1 / 2 ≤ inner ℝ u2 τ ∨ 1 / 2 ≤ inner ℝ u3 τ := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  set m := max (inner ℝ u1 τ) (max (inner ℝ u2 τ) (inner ℝ u3 τ)) with hm
  have hm1 : inner ℝ u1 τ ≤ m := le_max_left _ _
  have hm2 : inner ℝ u2 τ ≤ m := (le_max_left _ _).trans (le_max_right _ _)
  have hm3 : inner ℝ u3 τ ≤ m := (le_max_right _ _).trans (le_max_right _ _)
  have hk : 0 < 1 / 2 - m := by
    have : m < 1 / 2 := max_lt h1 (max_lt h2 h3)
    linarith
  have := three_ports_noncancel hk hu1 hu2 hu3 hτ (by linarith) (by linarith) (by linarith)
  rw [h0, norm_zero] at this
  exact absurd this (not_le.2 (lt_min one_pos hk))

/-- Three unit vectors with zero sum have pairwise scalar products `-1/2`. -/
theorem three_ports_inner {u1 u2 u3 : Plane} (hu1 : ‖u1‖ = 1) (hu2 : ‖u2‖ = 1)
    (hu3 : ‖u3‖ = 1) (h0 : u1 + u2 + u3 = 0) : inner ℝ u1 u2 = -1 / 2 := by
  have h : u1 + u2 = -u3 := eq_neg_of_add_eq_zero_left h0
  have e := norm_add_sq_real u1 u2
  rw [h, norm_neg, hu1, hu2, hu3] at e
  linarith

/-! ## §6.4: selected ports belong to distinct tracks -/

/-- The endpoint inequality of §6.4: if `x, y` lie within `δ D` of the points `O + (D/2) ν_x`,
`O + (D/2) ν_y` of the circle of radius `D / 2`, and the flags give `n · ν_x ≥ -θ` and
`n · ν_y ≤ θ`, then `n · (y - x) ≤ (θ + 2 δ) D`. -/
theorem selected_ends_ineq {x y νx νy n O : Plane} {D θ δ : ℝ} (hD : 0 ≤ D) (hn : ‖n‖ = 1)
    (hx : ‖x - O - (D / 2) • νx‖ ≤ δ * D) (hy : ‖y - O - (D / 2) • νy‖ ≤ δ * D)
    (hfx : -θ ≤ inner ℝ n νx) (hfy : inner ℝ n νy ≤ θ) :
    inner ℝ (y - x) n ≤ (θ + 2 * δ) * D := by
  have e : y - x = (y - O - (D / 2) • νy) - (x - O - (D / 2) • νx) + (D / 2) • (νy - νx) := by
    rw [smul_sub]; abel
  have b1 : inner ℝ (y - O - (D / 2) • νy) n ≤ δ * D := by
    have := real_inner_le_norm (y - O - (D / 2) • νy) n
    rw [hn, mul_one] at this; linarith
  have b2 : -(δ * D) ≤ inner ℝ (x - O - (D / 2) • νx) n := by
    have := abs_real_inner_le_norm (x - O - (D / 2) • νx) n
    rw [hn, mul_one] at this; linarith [neg_abs_le (inner ℝ (x - O - (D / 2) • νx) n)]
  have key : inner ℝ (y - x) n = inner ℝ (y - O - (D / 2) • νy) n -
      inner ℝ (x - O - (D / 2) • νx) n + D / 2 * (inner ℝ νy n - inner ℝ νx n) := by
    rw [e]; simp only [inner_add_left, inner_sub_left, real_inner_smul_left]
  rw [key, real_inner_comm n νy, real_inner_comm n νx]
  nlinarith

/-- The extent of a track in a separated normal direction: if the heights `n · m_f` of the edges
of `T` are pairwise more than `a*` apart and lie between those of `e` and `e'`, then
`n · (m_{e'} - m_e) ≥ a* r(T)`. -/
lemma track_extent_ge {X : Finset Plane} (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X)
    {T : Finset (Sym2 Plane)} (hT : T ∈ tracks X) {n : Plane} {e e' : Sym2 Plane} (he : e ∈ T)
    (hsep : ∀ f1 ∈ T, ∀ f2 ∈ T, f1 ≠ f2 → aStar < |inner ℝ (mid f1 - mid f2) n|)
    (hlow : ∀ f ∈ T, inner ℝ (mid e) n ≤ inner ℝ (mid f) n)
    (hhigh : ∀ f ∈ T, inner ℝ (mid f) n ≤ inner ℝ (mid e') n) :
    aStar * trackLength X T ≤ inner ℝ (mid e' - mid e) n := by
  have hap := aStar_pos
  set g : Sym2 Plane → ℝ := fun f => inner ℝ (mid f) n / aStar
  set S := T.image g
  have hinj : Set.InjOn g T := fun f1 hf1 f2 hf2 h12 => by
    by_contra hne
    have := hsep f1 hf1 f2 hf2 hne
    simp only [g] at h12
    rw [div_left_inj' hap.ne'] at h12
    rw [inner_sub_left, h12, sub_self, abs_zero] at this
    linarith
  have hS : S.card = T.card := Finset.card_image_of_injOn hinj
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_spread_of_separated_real S ⟨_, Finset.mem_image_of_mem _ he⟩
    (by
      simp only [S, Finset.mem_image]
      rintro _ ⟨f1, hf1, rfl⟩ _ ⟨f2, hf2, rfl⟩ hne
      have hf : f1 ≠ f2 := fun h => hne (by rw [h])
      have := hsep f1 hf1 f2 hf2 hf
      simp only [g]
      rw [← sub_div, abs_div, abs_of_pos hap, le_div_iff₀ hap, ← inner_sub_left]
      linarith)
  obtain ⟨f1, hf1, rfl⟩ := Finset.mem_image.1 hx
  obtain ⟨f2, hf2, rfl⟩ := Finset.mem_image.1 hy
  have h12 := trackLength_add_one_le_card hX htri hT
  have h12' : (trackLength X T : ℝ) + 1 ≤ T.card := by exact_mod_cast h12
  rw [hS] at hxy
  have hle : g f2 - g f1 ≤ (inner ℝ (mid e') n - inner ℝ (mid e) n) / aStar := by
    have : g f2 - g f1 = (inner ℝ (mid f2) n - inner ℝ (mid f1) n) / aStar := by
      simp only [g]; ring
    rw [this]
    exact div_le_div_of_nonneg_right (by linarith [hlow f1 hf1, hhigh f2 hf2]) hap.le
  rw [inner_sub_left]
  have : (trackLength X T : ℝ) ≤ (inner ℝ (mid e') n - inner ℝ (mid e) n) / aStar := by linarith
  rwa [le_div_iff₀ hap, mul_comm] at this

/-- **Selected ports belong to distinct tracks** (Verification Guide §6.4). Let `T` be a track with
at least `λ D` rhombi. A *selected port* of `T` is an edge `e ∈ T` with an outgoing unit
normal `n = ± J(dv e)` (all of `T` lies on the `n` side of `e`), whose midpoint is within `δ D` of a
point `O + (D/2) ν` of the circle of radius `D/2`, and with flag `n · ν ≥ -θ`. If
`θ < a* λ / 4` and `δ < a* λ / 8`, then `T` has at most one selected port: any two coincide, edge
and normal. Hence the map from selected ports to tracks is injective. -/
theorem selected_port_unique {X : Finset Plane} (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X)
    {T : Finset (Sym2 Plane)} (hT : T ∈ tracks X) {O : Plane} {D lam θ δ : ℝ} (hD : 0 < D)
    (hlen : lam * D ≤ trackLength X T) (hθ : θ < aStar * lam / 4)
    (hδ : δ < aStar * lam / 8)
    {e e' : Sym2 Plane} (he : e ∈ T) (he' : e' ∈ T) {ν ν' n n' : Plane}
    (hn : n = rot (dv e) ∨ n = -rot (dv e))
    (hn' : n' = rot (dv e') ∨ n' = -rot (dv e'))
    (hm : ‖mid e - O - (D / 2) • ν‖ ≤ δ * D) (hm' : ‖mid e' - O - (D / 2) • ν'‖ ≤ δ * D)
    (hf : -θ ≤ inner ℝ n ν) (hf' : -θ ≤ inner ℝ n' ν')
    (hside : ∀ f ∈ T, 0 ≤ inner ℝ (mid f - mid e) n)
    (hside' : ∀ f ∈ T, 0 ≤ inner ℝ (mid f - mid e') n') :
    e = e' ∧ n = n' := by
  have hap := aStar_pos
  set u := dv e with hu_def
  have hu : ‖u‖ = 1 := norm_dv_of_mem_unitEdges (mem_unitEdges_of_mem_tracks hT he)
  have hTe := eq_trackOf_of_mem hT he
  have hdir : ∀ f ∈ T, DirOf u f := fun f hf => by
    rw [hTe] at hf; exact sameDir_of_mem_trackOf hf
  have hnrot : n = rot u ∨ n = -rot u := hn
  have hn'rot : n' = rot u ∨ n' = -rot u := by
    rcases hdir e' he' with h | h <;> rcases hn' with h' | h'
    · left; rw [h', h]
    · right; rw [h', h]
    · right; rw [h', h, rot_neg]
    · left; rw [h', h, rot_neg, neg_neg]
  have hnorm : ‖n‖ = 1 := by rcases hnrot with h | h <;> rw [h] <;> simp [norm_rot, hu]
  -- heights along `n` are `a*`-separated
  have hsep : ∀ f1 ∈ T, ∀ f2 ∈ T, f1 ≠ f2 → aStar < |inner ℝ (mid f1 - mid f2) n| := by
    intro f1 hf1 f2 hf2 hne
    have := ht_sep hX htri hT hu hdir hf1 hf2 hne
    have e2 : inner ℝ (mid f1 - mid f2) (rot u) = ht u f1 - ht u f2 := by
      simp only [ht, inner_sub_left]
    rcases hnrot with h | h <;> rw [h]
    · rwa [e2]
    · rwa [inner_neg_right, abs_neg, e2]
  have hnn : n' = n ∨ n' = -n := by
    rcases hnrot with h | h <;> rcases hn'rot with h' | h'
    · left; rw [h, h']
    · right; rw [h, h']
    · right; rw [h, h', neg_neg]
    · left; rw [h, h']
  rcases hnn with hnn | hnn
  · -- both ports face the same way: both edges are lowest, hence equal
    subst hnn
    refine ⟨?_, rfl⟩
    by_contra hne
    have h1 := hside e' he'
    have h2 := hside' e he
    have h3 := hsep e he e' he' hne
    have h4 : inner ℝ (mid e - mid e') n' = 0 := by
      have : inner ℝ (mid e - mid e') n' = -inner ℝ (mid e' - mid e) n' := by
        rw [← inner_neg_left, neg_sub]
      linarith
    rw [h4, abs_zero] at h3
    linarith
  · -- opposite ports of one track: the track is too long for both flags
    exfalso
    subst hnn
    have hlow : ∀ f ∈ T, inner ℝ (mid e) n ≤ inner ℝ (mid f) n := fun f hf => by
      have := hside f hf; rw [inner_sub_left] at this; linarith
    have hhigh : ∀ f ∈ T, inner ℝ (mid f) n ≤ inner ℝ (mid e') n := fun f hf => by
      have := hside' f hf; rw [inner_neg_right, inner_sub_left] at this; linarith
    have hext := track_extent_ge hX htri hT he hsep hlow hhigh
    have hfy : inner ℝ n ν' ≤ θ := by rw [inner_neg_left] at hf'; linarith
    have hup := selected_ends_ineq hD.le hnorm hm hm' hf hfy
    have h1 : aStar * (lam * D) ≤ aStar * trackLength X T := mul_le_mul_of_nonneg_left hlen hap.le
    have h2 : (θ + 2 * δ) * D < aStar * lam / 2 * D := by
      apply mul_lt_mul_of_pos_right _ hD; linarith
    nlinarith

/-! ## §6.5: the length estimates -/

/-- The ratio bounds of §6.5: for `s ≥ a*` and `|t| ≤ 1/2`,
`|t| / (s² + t²) ≤ 1/2` and `s / (s² + t²) ≤ 1 / a*`. -/
theorem length_ratio_bounds {s t : ℝ} (hs : aStar ≤ s) (ht : |t| ≤ 1 / 2) :
    |t| / (s ^ 2 + t ^ 2) ≤ 1 / 2 ∧ s / (s ^ 2 + t ^ 2) ≤ 1 / aStar := by
  have hap := aStar_pos
  have hasq := aStar_sq
  have hs0 : 0 < s := lt_of_lt_of_le hap hs
  have hpos : 0 < s ^ 2 + t ^ 2 := by positivity
  have hs2 : 3 / 4 ≤ s ^ 2 := by rw [← hasq]; exact pow_le_pow_left₀ hap.le hs 2
  constructor
  · rw [div_le_iff₀ hpos]
    have key : 0 ≤ (1 / 2 - |t|) * (3 / 2 - |t|) := mul_nonneg (by linarith) (by linarith)
    rw [← sq_abs t]
    nlinarith [abs_nonneg t]
  · rw [div_le_div_iff₀ hpos hap]
    nlinarith [sq_nonneg t]

/-- **The length estimate of §6.5.** If (B1) holds with right-hand side `E ≥ 0`
(`E = 2 δ + 4 δ²`), with `ℓ ≥ λ > 0`, `s ≥ a*`, `|t| ≤ 1/2`, `|b| ≤ 1`, and the flag gives
`a ≥ -θ` with `θ ≥ 0`, then `ℓ ≤ 1/2 + θ / a* + E / (λ a*²)`. -/
theorem normalized_length_le {a b s t ℓ lam θ E : ℝ} (hlam : 0 < lam) (hℓ : lam ≤ ℓ)
    (hs : aStar ≤ s) (ht : |t| ≤ 1 / 2) (hb : |b| ≤ 1) (hθ : 0 ≤ θ) (ha : -θ ≤ a) (hE : 0 ≤ E)
    (hB1 : ℓ ^ 2 * (s ^ 2 + t ^ 2) + ℓ * (a * s + b * t) ≤ E) :
    ℓ ≤ 1 / 2 + θ / aStar + E / (lam * aStar ^ 2) := by
  have hap := aStar_pos
  have hs0 : 0 < s := lt_of_lt_of_le hap hs
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le hlam hℓ
  obtain ⟨r1, r2⟩ := length_ratio_bounds hs ht
  set Q := s ^ 2 + t ^ 2 with hQ
  have hQ0 : 0 < Q := by positivity
  have hQa : aStar ^ 2 ≤ Q := by
    have := pow_le_pow_left₀ hap.le hs 2; nlinarith [sq_nonneg t]
  set c := θ / aStar + 1 / 2 with hc
  -- `-(a s + b t) ≤ c Q`
  have hs' : s ≤ Q / aStar := by
    rw [div_le_div_iff₀ hQ0 hap] at r2; rw [le_div_iff₀ hap]; linarith
  have ht' : |t| ≤ Q / 2 := by rw [div_le_iff₀ hQ0] at r1; linarith
  have hlin : -(a * s + b * t) ≤ c * Q := by
    have e1 : -(a * s) ≤ θ * s := by nlinarith
    have e2 : θ * s ≤ θ * (Q / aStar) := mul_le_mul_of_nonneg_left hs' hθ
    have e3 : -(b * t) ≤ |t| := by
      have : |b * t| ≤ |t| := by
        rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg t) hb
      linarith [neg_abs_le (b * t)]
    have e4 : θ * (Q / aStar) = θ / aStar * Q := by ring
    rw [hc]; nlinarith
  by_cases hcl : ℓ ≤ c
  · have : 0 ≤ E / (lam * aStar ^ 2) := by positivity
    linarith
  · push_neg at hcl
    have hE' : lam * aStar ^ 2 * (ℓ - c) ≤ E := by
      have e1 : ℓ * Q * (ℓ - c) ≤ E := by nlinarith
      have e2 : lam * aStar ^ 2 ≤ ℓ * Q := mul_le_mul hℓ hQa (by positivity) hℓ0.le
      nlinarith
    have : ℓ - c ≤ E / (lam * aStar ^ 2) := by rw [le_div_iff₀ (by positivity)]; linarith
    linarith

/-! ## Interface with the annular statement -/

/-- `IsSelectedTrack` is monotone in the tolerance. -/
theorem IsSelectedTrack.mono {O : Plane} {D η η' : ℝ} {T : Finset (Sym2 Plane)} (hD : 0 ≤ D)
    (hη : η ≤ η') (h : IsSelectedTrack O D η T) : IsSelectedTrack O D η' T := by
  obtain ⟨e, he, ν, n, hν, hn, hm, hf, hside⟩ := h
  exact ⟨e, he, ν, n, hν, hn, hm.trans (mul_le_mul_of_nonneg_right hη hD), by linarith, hside⟩

/-- **A selected port gives a selected track.** If `e ∈ T` is a port with outgoing normal
`n = ± J(dv e)`, endpoint error at most `δ D` and flag `n · ν ≥ -θ`, with `θ, δ ≤ η`, then `T`
satisfies `IsSelectedTrack O D η`, the hypothesis of the annular estimates of Lemma 6.1. -/
theorem isSelectedTrack_of_port {O : Plane} {D θ δ η : ℝ} {T : Finset (Sym2 Plane)} (hD : 0 ≤ D)
    (hθ : θ ≤ η) (hδ : δ ≤ η) {e : Sym2 Plane} (he : e ∈ T) {ν n : Plane} (hν : ‖ν‖ = 1)
    (hn : n = rot (dv e) ∨ n = -rot (dv e)) (hm : ‖mid e - O - (D / 2) • ν‖ ≤ δ * D)
    (hf : -θ ≤ inner ℝ n ν) (hside : ∀ f ∈ T, 0 ≤ inner ℝ (mid f - mid e) n) :
    IsSelectedTrack O D η T :=
  ⟨e, he, ν, n, hν, hn, hm.trans (mul_le_mul_of_nonneg_right hδ hD), by linarith, hside⟩

/-- A track with at least `L` rhombi lies in `longTracks X L`. -/
theorem mem_longTracks_of_le {X : Finset Plane} {T : Finset (Sym2 Plane)} {L : ℝ}
    (hT : T ∈ tracks X) (hL : L ≤ trackLength X T) : T ∈ longTracks X L :=
  Finset.mem_filter.2 ⟨hT, hL⟩

end BoundaryPort

end Erdos99
end

end BoundaryPortBounds

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `ChargingGraph`
-/

section ChargingGraph

/-!
# The charging graph of the good faces (Verification Guide §4, §6.4, §13; WP11)

This file connects the abstract charging ledger of `LocalCharge` with the configuration.

After saturation (§10) every good face carries a fixed number of *marked* ports: one at an ordinary
good pentagon, two at a good hexagon, three at a good activated pentagon (`GoodFaces.marks`).  The
remaining short ports form a multigraph on the good faces, with stubs for the short ports whose
track ends at a cap or at an omitted face (virtual caps).  A `ChargingGraph` records such a
multigraph: its degree at a good face `F` is the short degree of `F` minus the marks of `F`, and lies
in `{2, 3, 4}`.  It also records the set of *flagged* faces (faces with a retained macroscopic port
satisfying `z · τ ≥ -θ`, §4.4).

* `GoodFaces.Y_eq_sum_good`: `Y = Σ_{good} (sd - marks - 2)`, so `Y` is the degree surplus
  `Σ (deg - 2)` of any charging graph (`ChargingGraph.Ysum_eq`).
* `GoodFaces.numExceptional_le`: `f ≤ |good| + Bface`.
* `ChargingGraph.four_f_le`: the charging inequality in the form needed for (D5),

    `4 f ≤ 5 Y + C + hC + κ_{≤M}(G) + κ_{≤M}(K) + 2 |good| / (M + 1) + 4 |Fl|
      + 4 #defective + #exceptional + 4 Bface`,

  proved from `LocalCharge.StubGraph.charging_ledger` and the large-component bound.
* The geometric input of the charging argument, `charging_graph_exists`, is stated and reduced
  to its one-scale version `charging_graph_local` in `ChargingCutoff`.
* `flaggedPort_face_unique`: two flagged faces never share a track (§6.4), so the flagged tracks
  form a set of selected tracks of the same cardinality.
-/

open scoped BigOperators Real
open Filter

@[expose] public noncomputable section

open Classical

namespace Erdos99

open LocalCharge

namespace GoodFaces

variable {X : Finset Plane}

/-- The number of marked ports of a good face: one at an ordinary pentagon, two at a hexagon,
three at an activated pentagon. -/
def marks (G : GoodFaces X) (F : Set ℂ) : ℕ :=
  if F ∈ G.pent then 1 else if F ∈ G.hex then 2 else 3

lemma disjoint_pent_hex (G : GoodFaces X) : Disjoint G.pent G.hex := by
  rw [Finset.disjoint_left]
  intro F h1 h2
  have := (G.pent_sub F h1).2
  rw [(G.hex_sub F h2).2] at this
  norm_num at this

lemma disjoint_hex_act (G : GoodFaces X) : Disjoint G.hex G.act := by
  rw [Finset.disjoint_left]
  intro F h1 h2
  have := (G.hex_sub F h1).2
  rw [(G.act_sub F h2).2] at this
  norm_num at this

/-- `Y = Σ_{good} (sd - marks - 2)`. -/
lemma Y_eq_sum_good (G : GoodFaces X) (L : ℝ) :
    G.Y L = ∑ F ∈ G.good, ((shortDeg X L (Sum.inl F) : ℝ) - G.marks F - 2) := by
  have h1 : Disjoint (G.pent ∪ G.hex) G.act :=
    Finset.disjoint_union_left.2 ⟨G.disj, G.disjoint_hex_act⟩
  rw [good, Finset.sum_union h1, Finset.sum_union G.disjoint_pent_hex, Y]
  congr 1
  · congr 1
    · refine Finset.sum_congr rfl fun F hF => ?_
      simp only [marks, hF, if_true]; push_cast; ring
    · refine Finset.sum_congr rfl fun F hF => ?_
      have : F ∉ G.pent := fun h => Finset.disjoint_left.1 G.disjoint_pent_hex h hF
      simp only [marks, this, hF, if_true, if_false]; push_cast; ring
  · refine Finset.sum_congr rfl fun F hF => ?_
    have h1 : F ∉ G.pent := fun h => Finset.disjoint_left.1 G.disj h hF
    have h2 : F ∉ G.hex := fun h => Finset.disjoint_left.1 G.disjoint_hex_act h hF
    simp only [marks, h1, h2, if_false]; push_cast; ring

lemma good_subset (G : GoodFaces X) : G.good ⊆ exceptionalFinset X := by
  intro F hF
  simp only [good, Finset.mem_union] at hF
  rcases hF with (h | h) | h
  · exact (G.pent_sub F h).1
  · exact (G.hex_sub F h).1
  · exact (G.act_sub F h).1

lemma numExceptional_eq_card {X : Finset Plane} (hX : IsSeparated X) :
    numExceptional X = (exceptionalFinset X).card := by
  rw [numExceptional, ← coe_exceptionalFinset hX, Set.ncard_coe_finset]

/-- `|good| ≤ f`. -/
lemma card_good_le (hX : IsSeparated X) (G : GoodFaces X) : G.good.card ≤ numExceptional X := by
  rw [numExceptional_eq_card hX]; exact Finset.card_le_card G.good_subset

/-- `f ≤ |good| + Bface`: every exceptional face that is not good has at least one side. -/
lemma numExceptional_le (hX : IsSeparated X) (G : GoodFaces X) :
    numExceptional X ≤ G.good.card + G.Bface := by
  rw [numExceptional_eq_card hX, ← Finset.card_filter_add_card_filter_not (fun F => F ∈ G.good)]
  refine add_le_add (Finset.card_le_card fun F hF => (Finset.mem_filter.1 hF).2) ?_
  rw [Bface, Finset.card_eq_sum_ones]
  refine Finset.sum_le_sum fun F hF => ?_
  have := ((mem_exceptionalFinset hX).1 (Finset.mem_filter.1 hF).1).2
  omega

end GoodFaces

/-- **A charging graph** for the cutoff `L` and the good faces `G` (Verification Guide §4.1–§4.2):
a finite multigraph with stubs on the good faces, whose degree at every good face is its short
degree minus its marks and lies in `{2, 3, 4}`, together with a set of flagged faces. -/
structure ChargingGraph (X : Finset Plane) (L : ℝ) (G : GoodFaces X) where
  /-- The multigraph of unmarked short tracks between good faces, with stubs at (actual or
  virtual) caps. -/
  g : StubGraph (Set ℂ)
  /-- The flagged faces. -/
  flagged : Finset (Set ℂ)
  edges_good : ∀ e ∈ g.E, g.src e ∈ G.good ∧ g.tgt e ∈ G.good
  deg_add_marks : ∀ F ∈ G.good, g.deg F + G.marks F = shortDeg X L (Sum.inl F)
  deg_mem : ∀ F ∈ G.good, 2 ≤ g.deg F ∧ g.deg F ≤ 4

namespace ChargingGraph

variable {X : Finset Plane} {L : ℝ} {G : GoodFaces X} (cg : ChargingGraph X L G)

/-- `C`: the cap incidences of the good faces, each `H–H` edge counted as two virtual caps. -/
def capInc : ℝ := cg.g.bIn G.good + 2 * cg.g.eIn (cg.g.Hs G.good) (cg.g.Hs G.good)

/-- `hC`: the cap incidences of the degree-two good faces. -/
def hCapInc : ℝ :=
  cg.g.bIn (cg.g.Hs G.good) + 2 * cg.g.eIn (cg.g.Hs G.good) (cg.g.Hs G.good)

/-- The pinned patterns of §13: capless components with at most `M` faces of `G` and of `K`,
defective `J` faces (four units of charge each) and exceptional `J–J` edges. -/
def pinned (M : ℕ) : ℝ :=
  cg.g.stublessSmall (cg.g.Gs G.good) M + cg.g.stublessSmall (cg.g.Ks G.good) M +
    4 * cg.g.defJ G.good cg.flagged + cg.g.excE G.good cg.flagged

/-- `Y` is the degree surplus of the charging graph. -/
lemma Ysum_eq : cg.g.Ysum G.good = G.Y L := by
  rw [G.Y_eq_sum_good, StubGraph.Ysum]
  refine Finset.sum_congr rfl fun F hF => ?_
  rw [← cg.deg_add_marks F hF]; push_cast; ring

/-- **The charging inequality from a charging graph**: for every `M`,

  `4 f ≤ 5 Y + C + hC + 2 |good| / (M + 1) + pinned + 4 |Fl| + 4 Bface`. -/
theorem four_f_le (hX : IsSeparated X) (M : ℕ) :
    4 * (numExceptional X : ℝ) ≤ 5 * G.Y L + cg.capInc + cg.hCapInc +
      2 * G.good.card / (M + 1) + cg.pinned M + 4 * cg.flagged.card + 4 * G.Bface := by
  have hled := cg.g.charging_ledger G.good cg.flagged cg.edges_good cg.deg_mem
  rw [cg.Ysum_eq] at hled
  have hG := cg.g.stubless_le_small_add (cg.g.Gs G.good) M
  have hK := cg.g.stubless_le_small_add (cg.g.Ks G.good) M
  have hGc : (cg.g.Gs G.good).card ≤ G.good.card := Finset.card_le_card (Finset.filter_subset _ _)
  have hKc : (cg.g.Ks G.good).card ≤ G.good.card := Finset.card_le_card (Finset.filter_subset _ _)
  have hf := G.numExceptional_le hX
  have hM : (0 : ℝ) < M + 1 := by positivity
  have hG' : (cg.g.stubless (cg.g.Gs G.good) : ℝ) ≤
      cg.g.stublessSmall (cg.g.Gs G.good) M + G.good.card / (M + 1) := by
    rw [← sub_le_iff_le_add', le_div_iff₀ hM]
    have : ((M + 1) * cg.g.stubless (cg.g.Gs G.good) : ℝ) ≤
        (M + 1) * cg.g.stublessSmall (cg.g.Gs G.good) M + G.good.card := by
      exact_mod_cast hG.trans (by omega)
    nlinarith
  have hK' : (cg.g.stubless (cg.g.Ks G.good) : ℝ) ≤
      cg.g.stublessSmall (cg.g.Ks G.good) M + G.good.card / (M + 1) := by
    rw [← sub_le_iff_le_add', le_div_iff₀ hM]
    have : ((M + 1) * cg.g.stubless (cg.g.Ks G.good) : ℝ) ≤
        (M + 1) * cg.g.stublessSmall (cg.g.Ks G.good) M + G.good.card := by
      exact_mod_cast hK.trans (by omega)
    nlinarith
  have hf' : (numExceptional X : ℝ) ≤ G.good.card + G.Bface := by exact_mod_cast hf
  unfold capInc hCapInc pinned
  have h2 : 2 * (G.good.card : ℝ) / (M + 1) = G.good.card / (M + 1) + G.good.card / (M + 1) := by
    ring
  rw [h2]
  linarith

end ChargingGraph

/-- **A flagged port** of the face `F` on the track `T` (Verification Guide §4.4, §6.4): `T` has at
least `λ D` rhombi and an edge `e` that is a port of `F`, with outgoing unit normal `n = ± J(dv e)`
(all of `T` lies on the `n` side of `e`), whose midpoint is within `δ D` of a point `O + (D/2) ν` of
the circle of radius `D/2`, and with flag `n · ν ≥ -θ` (that is, `z · τ ≥ -θ`). -/
def IsFlaggedPort (X : Finset Plane) (O : Plane) (D lam θ δ : ℝ) (F : Set ℂ)
    (T : Finset (Sym2 Plane)) : Prop :=
  lam * D ≤ trackLength X T ∧ ∃ e ∈ T, IsPort X (Sum.inl F) e ∧ ∃ ν n : Plane, ‖ν‖ = 1 ∧
    (n = rot (dv e) ∨ n = -rot (dv e)) ∧ ‖mid e - O - (D / 2) • ν‖ ≤ δ * D ∧
    -θ ≤ inner ℝ n ν ∧ ∀ f ∈ T, 0 ≤ inner ℝ (mid f - mid e) n

/-- **Flagged faces have distinct tracks** (Verification Guide §6.4).  If `θ < a* λ / 4` and
`δ < a* λ / 8`, two faces with flagged ports on the same track coincide: by
`BoundaryPort.selected_port_unique` the two ports are the same edge, and an edge of a track with
rhombi is a port of at most one face (`card_ports_add_card_rhombiAt`). -/
theorem flaggedPort_face_unique :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ (O : Plane) (D lam θ δ : ℝ) (F F' : Set ℂ) (T : Finset (Sym2 Plane)), 0 < D →
      θ < aStar * lam / 4 → δ < aStar * lam / 8 → T ∈ tracks X →
      IsFlaggedPort X O D lam θ δ F T → IsFlaggedPort X O D lam θ δ F' T → F = F' := by
  filter_upwards [card_ports_add_card_rhombiAt] with n hports hfm X hX htri O D lam θ δ F F' T hD
    hθ hδ hT hF hF'
  obtain ⟨hlen, e, he, hp, ν, nn, hν, hn, hm, hf, hside⟩ := hF
  obtain ⟨-, e', he', hp', ν', nn', hν', hn', hm', hf', hside'⟩ := hF'
  have hsep := hX.1.2
  obtain ⟨rfl, -⟩ := BoundaryPort.selected_port_unique hsep htri hT hD hlen hθ hδ he he' hn hn'
    hm hm' hf hf' hside hside'
  by_contra hne
  have heR : e ∈ rhombusEdges X := by
    have := he; rw [eq_trackOf_of_mem hT he] at this; exact (mem_trackOf.1 this).1
  have heU : e ∈ unitEdges X := (Finset.mem_filter.1 heR).1
  obtain ⟨e2, a, b, c, d, hR, -, -, -, -, hab, -⟩ := (Finset.mem_filter.1 heR).2
  have hRat : ({a, b, c, d} : Finset Plane) ∈ rhombiAt X e := by
    refine Finset.mem_filter.2 ⟨hR, fun x hx => ?_⟩
    rw [hab, Sym2.mem_iff] at hx
    rcases hx with rfl | rfl <;> simp
  have h2 := hports hfm X hX htri e heU
  have hnode : ∀ G : Set ℂ, IsPort X (Sum.inl G) e → Sum.inl G ∈ ports X e := fun G hG =>
    Finset.mem_filter.2 ⟨Finset.mem_union_left _ (Finset.mem_map_of_mem _
      ((mem_exceptionalFinset hsep).2 hG.1)), hG⟩
  have hc2 : 1 < (ports X e).card :=
    Finset.one_lt_card.2 ⟨Sum.inl F, hnode F hp, Sum.inl F', hnode F' hp', by simpa using hne⟩
  have hc1 : 0 < (rhombiAt X e).card := Finset.card_pos.2 ⟨_, hRat⟩
  omega

end Erdos99

end

end ChargingGraph

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `HalfEdgeGraph`
-/

section HalfEdgeGraph

/-!
# Stub graphs from half-edges

A finite set `P` of *half-edges* with a vertex map `v` and a partial matching `mate` (defined on the
half-edges satisfying `mated`) determines a `StubGraph`: every matched pair `{q, mate q}` becomes
an edge from `v q` to `v (mate q)`, and every unmatched half-edge `q` becomes a stub at `v q`.

* `StubGraph.ofHalfEdges`: the construction (half-edges are numbered through `P.toList`; the edge
  of a matched pair is numbered by the smaller of the two numbers).
* `StubGraph.deg_ofHalfEdges`: the degree of a vertex `a` is the number of half-edges at `a`.
* `StubGraph.ofHalfEdges_edges_mem`: both ends of every edge are vertices of half-edges.

This is used in `TrackChargingGraph` with the unmarked short ports of the good faces as
half-edges, matched along their tracks.
-/

open scoped BigOperators

@[expose] public noncomputable section

open Classical

namespace Erdos99

namespace LocalCharge

namespace StubGraph

variable {α β : Type*} [Inhabited β]

/-- The `i`-th half-edge of `P` (in the order of `P.toList`). -/
def hEnum (P : Finset β) (i : ℕ) : β := P.toList.getD i default

/-- The number of the half-edge `q` in `P.toList`. -/
def hIdx (P : Finset β) (q : β) : ℕ := P.toList.idxOf q

variable (P : Finset β)

omit [Inhabited β] in
lemma hIdx_lt {q : β} (hq : q ∈ P) : hIdx P q < P.card := by
  rw [hIdx, ← Finset.length_toList]; exact List.idxOf_lt_length_iff.2 (Finset.mem_toList.2 hq)

lemma hEnum_hIdx {q : β} (hq : q ∈ P) : hEnum P (hIdx P q) = q := by
  have h := hIdx_lt P hq
  rw [← Finset.length_toList] at h
  unfold hEnum hIdx at *
  rw [List.getD_eq_getElem _ _ h]
  exact List.getElem_idxOf h

lemma hEnum_mem {i : ℕ} (hi : i < P.card) : hEnum P i ∈ P := by
  rw [← Finset.length_toList] at hi
  rw [hEnum, List.getD_eq_getElem _ _ hi]
  exact Finset.mem_toList.1 (List.getElem_mem hi)

lemma hIdx_hEnum {i : ℕ} (hi : i < P.card) : hIdx P (hEnum P i) = i := by
  rw [← Finset.length_toList] at hi
  unfold hEnum hIdx
  rw [List.getD_eq_getElem _ _ hi]
  exact List.Nodup.idxOf_getElem (Finset.nodup_toList P) i hi

lemma hIdx_injOn {q q' : β} (hq : q ∈ P) (hq' : q' ∈ P) (h : hIdx P q = hIdx P q') : q = q' := by
  rw [← hEnum_hIdx P hq, ← hEnum_hIdx P hq', h]

variable (v : β → α) (mate : β → β) (mated : β → Prop)

/-- **The stub graph of a set of half-edges with a partial matching.**  Edges are numbered by the
smaller number of their two half-edges; stubs by the number of the unmatched half-edge. -/
def ofHalfEdges : StubGraph α where
  E := (Finset.range P.card).filter
    (fun i => mated (hEnum P i) ∧ i < hIdx P (mate (hEnum P i)))
  src i := v (hEnum P i)
  tgt i := v (mate (hEnum P i))
  S := (Finset.range P.card).filter (fun i => ¬ mated (hEnum P i))
  stub i := v (hEnum P i)

/-- The matching is a fixed-point-free involution on the matched half-edges of `P`. -/
def IsMatching : Prop :=
  ∀ q ∈ P, mated q → mate q ∈ P ∧ mate q ≠ q ∧ mate (mate q) = q ∧ mated (mate q)

variable {P v mate mated}

/-- Both ends of every edge are vertices of half-edges of `P`. -/
lemma ofHalfEdges_edges_mem (hM : IsMatching P mate mated) :
    ∀ e ∈ (ofHalfEdges P v mate mated).E, (ofHalfEdges P v mate mated).src e ∈ P.image v ∧
      (ofHalfEdges P v mate mated).tgt e ∈ P.image v := by
  intro i hi
  simp only [ofHalfEdges, Finset.mem_filter, Finset.mem_range] at hi
  have hm := hEnum_mem P hi.1
  exact ⟨Finset.mem_image_of_mem _ hm, Finset.mem_image_of_mem _ (hM _ hm hi.2.1).1⟩

/-- Every stub sits at a vertex of a half-edge of `P`. -/
lemma ofHalfEdges_stub_mem :
    ∀ s ∈ (ofHalfEdges P v mate mated).S, (ofHalfEdges P v mate mated).stub s ∈ P.image v := by
  intro i hi
  simp only [ofHalfEdges, Finset.mem_filter, Finset.mem_range] at hi
  exact Finset.mem_image_of_mem _ (hEnum_mem P hi.1)

/-- **The degree of a vertex is its number of half-edges.** -/
theorem deg_ofHalfEdges (hM : IsMatching P mate mated) (a : α) :
    (ofHalfEdges P v mate mated).deg a = (P.filter (fun q => v q = a)).card := by
  set g := ofHalfEdges P v mate mated
  -- the three classes of half-edges at `a`
  have h1 : (g.E.filter (fun e => g.src e = a)).card =
      (P.filter (fun q => v q = a ∧ mated q ∧ hIdx P q < hIdx P (mate q))).card := by
    refine Finset.card_nbij' (hEnum P) (hIdx P) ?_ ?_ ?_ ?_
    · intro i hi
      simp only [g, ofHalfEdges, Finset.coe_filter, Finset.mem_filter, Finset.mem_range, Set.mem_setOf_eq] at hi
      simp only [Finset.coe_filter, Set.mem_setOf_eq]
      exact ⟨hEnum_mem P hi.1.1, hi.2, hi.1.2.1, by rw [hIdx_hEnum P hi.1.1]; exact hi.1.2.2⟩
    · intro q hq
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hq
      simp only [g, ofHalfEdges, Finset.coe_filter, Finset.mem_filter, Finset.mem_range, Set.mem_setOf_eq,
        hEnum_hIdx P hq.1]
      exact ⟨⟨hIdx_lt P hq.1, hq.2.2.1, hq.2.2.2⟩, hq.2.1⟩
    · intro i hi
      simp only [g, ofHalfEdges, Finset.coe_filter, Finset.mem_filter, Finset.mem_range, Set.mem_setOf_eq] at hi
      exact hIdx_hEnum P hi.1.1
    · intro q hq
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hq
      exact hEnum_hIdx P hq.1
  have h2 : (g.E.filter (fun e => g.tgt e = a)).card =
      (P.filter (fun q => v q = a ∧ mated q ∧ hIdx P (mate q) < hIdx P q)).card := by
    refine Finset.card_nbij' (fun i => mate (hEnum P i)) (fun q => hIdx P (mate q)) ?_ ?_ ?_ ?_
    · intro i hi
      simp only [g, ofHalfEdges, Finset.coe_filter, Finset.mem_filter, Finset.mem_range, Set.mem_setOf_eq] at hi
      simp only [Finset.coe_filter, Set.mem_setOf_eq]
      have hm := hEnum_mem P hi.1.1
      obtain ⟨hm1, -, hm3, hm4⟩ := hM _ hm hi.1.2.1
      refine ⟨hm1, hi.2, hm4, ?_⟩
      rw [hm3, hIdx_hEnum P hi.1.1]; exact hi.1.2.2
    · intro q hq
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hq
      obtain ⟨hm1, -, hm3, hm4⟩ := hM _ hq.1 hq.2.2.1
      simp only [g, ofHalfEdges, Finset.coe_filter, Finset.mem_filter, Finset.mem_range, Set.mem_setOf_eq,
        hEnum_hIdx P hm1, hm3]
      exact ⟨⟨hIdx_lt P hm1, hm4, hq.2.2.2⟩, hq.2.1⟩
    · intro i hi
      simp only [g, ofHalfEdges, Finset.coe_filter, Finset.mem_filter, Finset.mem_range, Set.mem_setOf_eq] at hi
      obtain ⟨-, -, hm3, -⟩ := hM _ (hEnum_mem P hi.1.1) hi.1.2.1
      simp only [hm3, hIdx_hEnum P hi.1.1]
    · intro q hq
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hq
      obtain ⟨hm1, -, hm3, -⟩ := hM _ hq.1 hq.2.2.1
      simp only [hEnum_hIdx P hm1, hm3]
  have h3 : g.stubs a = (P.filter (fun q => v q = a ∧ ¬ mated q)).card := by
    refine Finset.card_nbij' (hEnum P) (hIdx P) ?_ ?_ ?_ ?_
    · intro i hi
      simp only [g, ofHalfEdges, Finset.coe_filter, Finset.mem_filter, Finset.mem_range, Set.mem_setOf_eq] at hi
      simp only [Finset.coe_filter, Set.mem_setOf_eq]
      exact ⟨hEnum_mem P hi.1.1, hi.2, hi.1.2⟩
    · intro q hq
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hq
      simp only [g, ofHalfEdges, Finset.coe_filter, Finset.mem_filter, Finset.mem_range, Set.mem_setOf_eq,
        hEnum_hIdx P hq.1]
      exact ⟨⟨hIdx_lt P hq.1, hq.2.2⟩, hq.2.1⟩
    · intro i hi
      simp only [g, ofHalfEdges, Finset.coe_filter, Finset.mem_filter, Finset.mem_range, Set.mem_setOf_eq] at hi
      exact hIdx_hEnum P hi.1.1
    · intro q hq
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hq
      exact hEnum_hIdx P hq.1
  rw [deg, h1, h2, h3]
  -- the three classes partition the half-edges at `a`
  rw [← Finset.card_union_of_disjoint, ← Finset.card_union_of_disjoint]
  · congr 1
    ext q
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ((⟨h, h', -⟩ | ⟨h, h', -⟩) | ⟨h, h', -⟩) <;> exact ⟨h, h'⟩
    · rintro ⟨hq, hv⟩
      by_cases hm : mated q
      · obtain ⟨hm1, hm2, -, -⟩ := hM _ hq hm
        have hne : hIdx P q ≠ hIdx P (mate q) := fun h => hm2 (hIdx_injOn P hm1 hq h.symm)
        rcases lt_or_gt_of_ne hne with h | h
        · exact Or.inl (Or.inl ⟨hq, hv, hm, h⟩)
        · exact Or.inl (Or.inr ⟨hq, hv, hm, h⟩)
      · exact Or.inr ⟨hq, hv, hm⟩
  · rw [Finset.disjoint_left]
    intro q hq hq'
    simp only [Finset.mem_union, Finset.mem_filter] at hq hq'
    rcases hq with ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ <;> exact hq'.2.2 h
  · rw [Finset.disjoint_left]
    intro q hq hq'
    simp only [Finset.mem_filter] at hq hq'
    omega

/-- The stubs at vertices of `A` are the unmatched half-edges at vertices of `A`. -/
theorem bIn_ofHalfEdges (A : Finset α) :
    (ofHalfEdges P v mate mated).bIn A = (P.filter (fun q => ¬ mated q ∧ v q ∈ A)).card := by
  refine Finset.card_nbij' (hEnum P) (hIdx P) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [ofHalfEdges, Finset.coe_filter, Finset.mem_filter, Finset.mem_range,
      Set.mem_setOf_eq] at hi
    simp only [Finset.coe_filter, Set.mem_setOf_eq]
    exact ⟨hEnum_mem P hi.1.1, hi.1.2, hi.2⟩
  · intro q hq
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hq
    simp only [ofHalfEdges, Finset.coe_filter, Finset.mem_filter, Finset.mem_range,
      Set.mem_setOf_eq, hEnum_hIdx P hq.1]
    exact ⟨⟨hIdx_lt P hq.1, hq.2.1⟩, hq.2.2⟩
  · intro i hi
    simp only [ofHalfEdges, Finset.coe_filter, Finset.mem_filter, Finset.mem_range,
      Set.mem_setOf_eq] at hi
    exact hIdx_hEnum P hi.1.1
  · intro q hq
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hq
    exact hEnum_hIdx P hq.1

end StubGraph

end LocalCharge

end Erdos99

end

end HalfEdgeGraph

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `TrackChargingGraph`
-/

section TrackChargingGraph

/-!
# The charging graph of the short tracks (Verification Guide §4.1)

This file builds the charging graph of §4.1 from the actual tracks of a configuration.

Fix a cutoff `L`, good faces `G` and a *marking* `mk`: for every good face `F` a set `mk F` of
short ports of `F` (the marked ports of saturation, §10).  The half-edges are the pairs `(F, e)`
with `F` good and `e` an unmarked short port of `F` (`unmarkedPorts`).  Every track has exactly two
ends (`card_trackEnds`); the half-edge `(F, e)` is *matched* with the other end of the track of `e`
if that end is again an unmarked short port of a good face.  Matched pairs become edges and the
remaining half-edges become stubs: these are the short tracks ending at a cap, at an omitted face
or at a marked port (the actual and virtual caps of §4.1).

* `otherEnd X q`: the other end of the track through the port `q`.
* `trackGraph X L G mk`: the stub graph of the unmarked short ports.
* `trackGraph_deg`: the degree of a good face is its number of unmarked short ports.
* `trackChargingGraph`: if every good face has exactly `marks F` marked short ports and short degree
  between `marks F + 2` and `marks F + 4`, the track graph is a `ChargingGraph`.
-/

open scoped BigOperators

@[expose] public noncomputable section

open Classical

namespace Erdos99

open LocalCharge

/-- The short ports of the face `F`: its ports whose (possibly rhombus-free) track has fewer than
`L` rhombi.  Their number is `shortDeg X L (Sum.inl F)`. -/
def shortPorts (X : Finset Plane) (L : ℝ) (F : Set ℂ) : Finset (Sym2 Plane) :=
  (unitEdges X).filter (fun e => IsPort X (Sum.inl F) e ∧ (trackLength X (allTrackOf X e) : ℝ) < L)

lemma card_shortPorts (X : Finset Plane) (L : ℝ) (F : Set ℂ) :
    (shortPorts X L F).card = shortDeg X L (Sum.inl F) := rfl

/-- The other end of the track through the port `e` of the face `F`. -/
def otherEnd (X : Finset Plane) (q : Set ℂ × Sym2 Plane) : PortNode × Sym2 Plane :=
  if h : ((trackEnds X (allTrackOf X q.2)).erase (Sum.inl q.1, q.2)).Nonempty then h.choose
  else (Sum.inl q.1, q.2)

/-- The face of a node (`∅` for a hull side). -/
def nodeFace : PortNode → Set ℂ := Sum.elim id (fun _ => ∅)

/-- The half-edges of the track graph: the unmarked short ports of the good faces. -/
def unmarkedPorts (X : Finset Plane) (L : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane)) :
    Finset (Set ℂ × Sym2 Plane) :=
  (G.good ×ˢ unitEdges X).filter (fun q => q.2 ∈ shortPorts X L q.1 ∧ q.2 ∉ mk q.1)

/-- The half-edge at the other end of the track. -/
def trackMate (X : Finset Plane) (q : Set ℂ × Sym2 Plane) : Set ℂ × Sym2 Plane :=
  (nodeFace (otherEnd X q).1, (otherEnd X q).2)

/-- A half-edge is matched if the other end of its track is again a half-edge. -/
def TrackMated (X : Finset Plane) (L : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane))
    (q : Set ℂ × Sym2 Plane) : Prop :=
  (otherEnd X q).1 = Sum.inl (nodeFace (otherEnd X q).1) ∧ trackMate X q ∈ unmarkedPorts X L G mk

/-- **The track graph** (§4.1): edges are the short tracks joining two unmarked ports of good faces;
stubs are the other unmarked short ports of good faces. -/
def trackGraph (X : Finset Plane) (L : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane)) :
    StubGraph (Set ℂ) :=
  StubGraph.ofHalfEdges (unmarkedPorts X L G mk) Prod.fst (trackMate X) (TrackMated X L G mk)

/-- The two ends of the track through a port `e` of an exceptional face `F` are `(F, e)` and
`otherEnd X (F, e)`, and these are distinct. -/
lemma trackEnds_eq_otherEnd {X : Finset Plane}
    (hends : ∀ T ∈ allTracks X, (trackEnds X T).card = 2) {F : Set ℂ} {e : Sym2 Plane}
    (hF : F ∈ exceptionalFinset X) (he : e ∈ unitEdges X) (hp : IsPort X (Sum.inl F) e) :
    trackEnds X (allTrackOf X e) = {(Sum.inl F, e), otherEnd X (F, e)} ∧
      otherEnd X (F, e) ≠ (Sum.inl F, e) := by
  set s := trackEnds X (allTrackOf X e)
  have hmem : (Sum.inl F, e) ∈ s := by
    refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨?_, mem_allTrackOf_self he⟩, hp⟩
    exact Finset.mem_union_left _ (Finset.mem_map_of_mem _ hF)
  have hc : (s.erase (Sum.inl F, e)).card = 1 := by
    rw [Finset.card_erase_of_mem hmem, hends _ (allTrackOf_mem_allTracks he)]
  obtain ⟨o, ho⟩ := Finset.card_eq_one.1 hc
  have hne : (s.erase (Sum.inl F, e)).Nonempty := by rw [ho]; exact Finset.singleton_nonempty o
  have hoth : otherEnd X (F, e) = o := by
    have : otherEnd X (F, e) = hne.choose := dif_pos hne
    rw [this]
    have h2 : ∀ x ∈ s.erase (Sum.inl F, e), x = o := fun x hx => by
      rw [ho] at hx; exact Finset.mem_singleton.1 hx
    exact h2 _ hne.choose_spec
  have hoe : o ∈ s.erase (Sum.inl F, e) := by rw [ho]; exact Finset.mem_singleton_self o
  refine ⟨?_, hoth ▸ Finset.ne_of_mem_erase hoe⟩
  rw [hoth]
  ext x
  constructor
  · intro hx
    by_cases hxe : x = (Sum.inl F, e)
    · rw [hxe]; exact Finset.mem_insert_self _ _
    · have : x ∈ s.erase (Sum.inl F, e) := Finset.mem_erase.2 ⟨hxe, hx⟩
      rw [ho] at this
      rw [Finset.mem_singleton.1 this]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  · intro hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact hmem
    · rw [Finset.mem_singleton.1 hx]; exact Finset.mem_of_mem_erase hoe

lemma mem_unmarkedPorts {X : Finset Plane} {L : ℝ} {G : GoodFaces X}
    {mk : Set ℂ → Finset (Sym2 Plane)} {q : Set ℂ × Sym2 Plane} :
    q ∈ unmarkedPorts X L G mk ↔ q.1 ∈ G.good ∧ q.2 ∈ shortPorts X L q.1 ∧ q.2 ∉ mk q.1 := by
  rw [unmarkedPorts, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨h1, -⟩, h2, h3⟩; exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, (Finset.mem_filter.1 h2).1⟩, h2, h3⟩

/-- **The track matching is an involution** (each short track has exactly two ends). -/
theorem trackMate_isMatching {X : Finset Plane}
    (hends : ∀ T ∈ allTracks X, (trackEnds X T).card = 2) (L : ℝ) (G : GoodFaces X)
    (mk : Set ℂ → Finset (Sym2 Plane)) :
    StubGraph.IsMatching (unmarkedPorts X L G mk) (trackMate X) (TrackMated X L G mk) := by
  rintro ⟨F, e⟩ hq ⟨hleft, hmP⟩
  obtain ⟨hF, hsh, -⟩ := mem_unmarkedPorts.1 hq
  have hsh' := Finset.mem_filter.1 hsh
  have hFe := G.good_subset hF
  obtain ⟨hT, hne⟩ := trackEnds_eq_otherEnd hends hFe hsh'.1 hsh'.2.1
  -- the other end `(F', e')`
  set o := otherEnd X (F, e) with ho
  set F' := nodeFace o.1
  set e' := o.2
  have hoF : o = (Sum.inl F', e') := Prod.ext hleft rfl
  have hmate : trackMate X (F, e) = (F', e') := rfl
  rw [hmate] at hmP ⊢
  obtain ⟨hF', hsh2, -⟩ := mem_unmarkedPorts.1 hmP
  have hsh2' := Finset.mem_filter.1 hsh2
  -- `e'` lies on the track of `e`
  have hoT : o ∈ trackEnds X (allTrackOf X e) := by rw [hT]; simp
  have he'T : e' ∈ allTrackOf X e := (Finset.mem_product.1 (Finset.mem_filter.1 hoT).1).2
  have htr : allTrackOf X e' = allTrackOf X e :=
    (eq_allTrackOf_of_mem (allTrackOf_mem_allTracks hsh'.1) he'T).symm
  obtain ⟨hT', hne'⟩ := trackEnds_eq_otherEnd hends (G.good_subset hF') hsh2'.1 hsh2'.2.1
  rw [htr, hT, hoF] at hT'
  have hdist : (Sum.inl F', e') ≠ ((Sum.inl F, e) : PortNode × Sym2 Plane) := hoF ▸ hne
  -- the other end of `(F', e')` is `(F, e)`
  have hback : otherEnd X (F', e') = (Sum.inl F, e) := by
    have h1 : otherEnd X (F', e') ∈ ({(Sum.inl F, e), (Sum.inl F', e')} :
        Finset (PortNode × Sym2 Plane)) := by rw [hT']; simp
    rcases Finset.mem_insert.1 h1 with h | h
    · exact h
    · exact absurd (Finset.mem_singleton.1 h) hne'
  have hmate2 : trackMate X (F', e') = (F, e) := by
    simp only [trackMate, hback, nodeFace, Sum.elim_inl, id]
  refine ⟨hmP, ?_, hmate2, ?_, ?_⟩
  · intro h
    apply hdist
    rw [Prod.mk.injEq] at h
    rw [h.1, h.2]
  · rw [hback]; rfl
  · show trackMate X (F', e') ∈ _
    rw [hmate2]; exact hq

/-- **Degrees in the track graph**: the degree of a face is its number of unmarked short ports. -/
theorem trackGraph_deg {X : Finset Plane}
    (hends : ∀ T ∈ allTracks X, (trackEnds X T).card = 2) (L : ℝ) (G : GoodFaces X)
    (mk : Set ℂ → Finset (Sym2 Plane)) {F : Set ℂ} (hF : F ∈ G.good) :
    (trackGraph X L G mk).deg F = (shortPorts X L F \ mk F).card := by
  rw [trackGraph, StubGraph.deg_ofHalfEdges (trackMate_isMatching hends L G mk)]
  refine Finset.card_nbij' Prod.snd (fun e => (F, e)) ?_ ?_ ?_ ?_
  · intro q hq
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hq
    obtain ⟨hq, rfl⟩ := hq
    obtain ⟨-, h2, h3⟩ := mem_unmarkedPorts.1 hq
    exact Finset.mem_sdiff.2 ⟨h2, h3⟩
  · intro e he
    obtain ⟨h2, h3⟩ := Finset.mem_sdiff.1 he
    exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨mem_unmarkedPorts.2 ⟨hF, h2, h3⟩, rfl⟩)
  · intro q hq
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hq
    obtain ⟨-, rfl⟩ := hq
    rfl
  · intro e _
    rfl

/-- The ends of the edges of the track graph are good faces. -/
theorem trackGraph_edges_good {X : Finset Plane}
    (hends : ∀ T ∈ allTracks X, (trackEnds X T).card = 2) (L : ℝ) (G : GoodFaces X)
    (mk : Set ℂ → Finset (Sym2 Plane)) :
    ∀ e ∈ (trackGraph X L G mk).E,
      (trackGraph X L G mk).src e ∈ G.good ∧ (trackGraph X L G mk).tgt e ∈ G.good := by
  intro e he
  obtain ⟨h1, h2⟩ := StubGraph.ofHalfEdges_edges_mem (trackMate_isMatching hends L G mk) e he
  have hsub : (unmarkedPorts X L G mk).image Prod.fst ⊆ G.good := by
    intro F hF
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hF
    exact (mem_unmarkedPorts.1 hq).1
  exact ⟨hsub h1, hsub h2⟩

/-- A marking with `marks F` short ports at each good face `F`. -/
def IsMarking (X : Finset Plane) (L : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane)) :
    Prop :=
  ∀ F ∈ G.good, mk F ⊆ shortPorts X L F ∧ (mk F).card = G.marks F

/-- After deleting the marked tracks, every good face keeps between two and four short ports. -/
def DegreeWindow (X : Finset Plane) (L : ℝ) (G : GoodFaces X) : Prop :=
  ∀ F ∈ G.good, G.marks F + 2 ≤ shortDeg X L (Sum.inl F) ∧ shortDeg X L (Sum.inl F) ≤ G.marks F + 4

/-- **The charging graph of the short tracks** (§4.1): for a marking with `marks F` short ports at
every good face and short degrees in the window `[marks F + 2, marks F + 4]`, the track graph with
the flagged faces `Fl` is a `ChargingGraph`. -/
def trackChargingGraph {X : Finset Plane}
    (hends : ∀ T ∈ allTracks X, (trackEnds X T).card = 2) {L : ℝ} {G : GoodFaces X}
    {mk : Set ℂ → Finset (Sym2 Plane)} (hmk : IsMarking X L G mk) (hwin : DegreeWindow X L G)
    (Fl : Finset (Set ℂ)) : ChargingGraph X L G where
  g := trackGraph X L G mk
  flagged := Fl
  edges_good := trackGraph_edges_good hends L G mk
  deg_add_marks := by
    intro F hF
    rw [trackGraph_deg hends L G mk hF, Finset.card_sdiff_of_subset (hmk F hF).1,
      (hmk F hF).2, card_shortPorts]
    have := (hwin F hF).1
    omega
  deg_mem := by
    intro F hF
    rw [trackGraph_deg hends L G mk hF, Finset.card_sdiff_of_subset (hmk F hF).1,
      (hmk F hF).2, card_shortPorts]
    have := hwin F hF
    omega

lemma trackChargingGraph_g {X : Finset Plane}
    (hends : ∀ T ∈ allTracks X, (trackEnds X T).card = 2) {L : ℝ} {G : GoodFaces X}
    {mk : Set ℂ → Finset (Sym2 Plane)} (hmk : IsMarking X L G mk) (hwin : DegreeWindow X L G)
    (Fl : Finset (Set ℂ)) : (trackChargingGraph hends hmk hwin Fl).g = trackGraph X L G mk := rfl

end Erdos99

end

end TrackChargingGraph

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `TrackCapBounds`
-/

section TrackCapBounds

/-!
# Cap incidences of the track graph (Verification Guide §4.4, (C7))

The stubs of the track graph (`trackGraph`) are the unmarked short ports of the good faces whose
track does not end at another unmarked short port of a good face.  This file classifies them by the
other end of their track and bounds the cap incidences `C` and `hC` of (C7).

The other end of the track is

* a hull side with a return of at most one edge (a *unit stub*);
* a two-edge return with exactly one short port (a *`C₁` stub*);
* a two-edge return with two short ports (or none);
* a hull return of at least three edges;
* an exceptional face that is not good (an *omitted* face: a virtual cap);
* a marked port of a good face (a *marked stub*).

Since every track has exactly two ends, distinct stubs have distinct other ends (`otherEnd_injOn`),
so each class is bounded by the number of short ports at the corresponding nodes:

* the stubs at two-edge returns number at most `2 c₂ - C₁`, of which at most `C₁` are `C₁` stubs;
* the stubs at longer returns number at most `3 ρ` (`ρ = Σ_j (j - 2) c_j`);
* the stubs at omitted faces number at most `Bface`.

Consequently (`trackGraph_capInc_le`, `trackGraph_hCapInc_le`)

  `C ≤ 2 c₂ - C₁ + (unit stubs) + (marked stubs) + 2 e_HH + 3 ρ + Bface`,
  `hC ≤ 2 (c₂ - C₁) + (unit, marked and C₁ stubs at H) + 2 e_HH + 3 ρ + Bface`.

So (C7) reduces to the statement that few unmarked short tracks from good faces end at unit hull
sides or at marked ports, that few `C₁` caps feed degree-two faces (§13.5), and that there are few
`H–H` edges (§13.1); `ρ` and `Bface` are small by stability and by the choice of the good faces.
-/

open scoped BigOperators

@[expose] public noncomputable section

open Classical

namespace Erdos99

open LocalCharge

variable {X : Finset Plane} {L : ℝ} {G : GoodFaces X} {mk : Set ℂ → Finset (Sym2 Plane)}

/-! ## The other end of a port -/

/-- The ports of exceptional faces, as pairs `(F, e)`. -/
def facePorts (X : Finset Plane) : Set (Set ℂ × Sym2 Plane) :=
  {q | q.1 ∈ exceptionalFinset X ∧ q.2 ∈ unitEdges X ∧ IsPort X (Sum.inl q.1) q.2}

lemma unmarkedPorts_subset_facePorts : ↑(unmarkedPorts X L G mk) ⊆ facePorts X := by
  intro q hq
  obtain ⟨h1, h2, -⟩ := mem_unmarkedPorts.1 hq
  have h2' := Finset.mem_filter.1 h2
  exact ⟨G.good_subset h1, h2'.1, h2'.2.1⟩

lemma mem_trackEnds {T : Finset (Sym2 Plane)} {r : PortNode × Sym2 Plane} :
    r ∈ trackEnds X T ↔ r.1 ∈ portNodes X ∧ r.2 ∈ T ∧ IsPort X r.1 r.2 := by
  rw [trackEnds, Finset.mem_filter, Finset.mem_product, and_assoc]

/-- The other end of a port of an exceptional face is an end of the same track. -/
lemma otherEnd_mem_trackEnds (hends : ∀ T ∈ allTracks X, (trackEnds X T).card = 2)
    {q : Set ℂ × Sym2 Plane} (hq : q ∈ facePorts X) :
    otherEnd X q ∈ trackEnds X (allTrackOf X q.2) := by
  obtain ⟨F, e⟩ := q
  obtain ⟨hF, he, hp⟩ := hq
  rw [(trackEnds_eq_otherEnd hends hF he hp).1]
  exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

/-- The other end of a port lies on the same track, so it is a unit edge with the same track. -/
lemma otherEnd_track (hends : ∀ T ∈ allTracks X, (trackEnds X T).card = 2)
    {q : Set ℂ × Sym2 Plane} (hq : q ∈ facePorts X) :
    (otherEnd X q).1 ∈ portNodes X ∧ (otherEnd X q).2 ∈ unitEdges X ∧
      IsPort X (otherEnd X q).1 (otherEnd X q).2 ∧
      allTrackOf X (otherEnd X q).2 = allTrackOf X q.2 := by
  obtain ⟨h1, h2, h3⟩ := mem_trackEnds.1 (otherEnd_mem_trackEnds hends hq)
  have hT := allTrackOf_mem_allTracks hq.2.1
  exact ⟨h1, allTracks_subset_unitEdges hT h2, h3, (eq_allTrackOf_of_mem hT h2).symm⟩

/-- **Distinct ports have distinct other ends** (every track has exactly two ends). -/
theorem otherEnd_injOn (hends : ∀ T ∈ allTracks X, (trackEnds X T).card = 2) :
    Set.InjOn (otherEnd X) (facePorts X) := by
  rintro ⟨F1, e1⟩ h1 ⟨F2, e2⟩ h2 heq
  obtain ⟨hT1, hne1⟩ := trackEnds_eq_otherEnd hends h1.1 h1.2.1 h1.2.2
  obtain ⟨hT2, -⟩ := trackEnds_eq_otherEnd hends h2.1 h2.2.1 h2.2.2
  have htr1 := (otherEnd_track hends h1).2.2.2
  have htr2 := (otherEnd_track hends h2).2.2.2
  simp only at htr1 htr2
  rw [heq] at htr1 hT1 hne1
  rw [← htr1, htr2, hT2] at hT1
  have hmem : ((Sum.inl F1, e1) : PortNode × Sym2 Plane) ∈
      ({(Sum.inl F2, e2), otherEnd X (F2, e2)} : Finset (PortNode × Sym2 Plane)) := by
    rw [hT1]; exact Finset.mem_insert_self _ _
  rcases Finset.mem_insert.1 hmem with h | h
  · simp only [Prod.mk.injEq, Sum.inl.injEq] at h
    rw [h.1, h.2]
  · exact absurd (Finset.mem_singleton.1 h).symm hne1

/-! ## Short ends at a class of nodes -/

/-- The short port incidences `(N, e)` at the nodes `N` satisfying `R`. -/
def shortEnds (X : Finset Plane) (L : ℝ) (R : PortNode → Prop) : Finset (PortNode × Sym2 Plane) :=
  (((portNodes X).filter R) ×ˢ unitEdges X).filter
    (fun r => IsPort X r.1 r.2 ∧ (trackLength X (allTrackOf X r.2) : ℝ) < L)

lemma card_shortEnds (R : PortNode → Prop) :
    (shortEnds X L R).card = ∑ N ∈ (portNodes X).filter R, shortDeg X L N := by
  rw [shortEnds, Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun N _ => ?_
  rw [shortDeg, Finset.card_filter]

/-- A set of unmarked ports whose other ends lie at nodes satisfying `R` has at most as many
elements as there are short ports at these nodes. -/
theorem card_le_shortEnds (hends : ∀ T ∈ allTracks X, (trackEnds X T).card = 2)
    {Q : Finset (Set ℂ × Sym2 Plane)} (hQ : Q ⊆ unmarkedPorts X L G mk) {R : PortNode → Prop}
    (hR : ∀ q ∈ Q, R (otherEnd X q).1) : Q.card ≤ (shortEnds X L R).card := by
  refine Finset.card_le_card_of_injOn (otherEnd X) ?_ ?_
  · intro q hq
    have hqP := hQ hq
    have hfp := unmarkedPorts_subset_facePorts hqP
    obtain ⟨h1, h2, h3, h4⟩ := otherEnd_track hends hfp
    obtain ⟨-, hsh, -⟩ := mem_unmarkedPorts.1 hqP
    refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨h1, hR q hq⟩, h2⟩, h3, ?_⟩
    rw [h4]; exact (Finset.mem_filter.1 hsh).2.2
  · exact (otherEnd_injOn hends).mono fun q hq => unmarkedPorts_subset_facePorts (hQ hq)

lemma sum_portNodes_inr (f : PortNode → ℕ) (Q : Plane × Plane → Prop) :
    ∑ N ∈ (portNodes X).filter (fun N => ∃ p, N = Sum.inr p ∧ Q p), f N =
      ∑ p ∈ (ccwHullSides X).filter Q, f (Sum.inr p) := by
  rw [Finset.sum_filter, portNodes, Finset.sum_union (disjoint_portNodes X), Finset.sum_map,
    Finset.sum_map, Finset.sum_filter]
  simp

lemma sum_portNodes_inl (f : PortNode → ℕ) (Q : Set ℂ → Prop) :
    ∑ N ∈ (portNodes X).filter (fun N => ∃ F, N = Sum.inl F ∧ Q F), f N =
      ∑ F ∈ (exceptionalFinset X).filter Q, f (Sum.inl F) := by
  rw [Finset.sum_filter, portNodes, Finset.sum_union (disjoint_portNodes X), Finset.sum_map,
    Finset.sum_map, Finset.sum_filter]
  simp

/-! ## The classes of stubs -/

/-- The stubs of the track graph at the faces of `V`: unmatched unmarked short ports. -/
def stubsAt (X : Finset Plane) (L : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane))
    (V : Finset (Set ℂ)) : Finset (Set ℂ × Sym2 Plane) :=
  (unmarkedPorts X L G mk).filter (fun q => ¬ TrackMated X L G mk q ∧ q.1 ∈ V)

/-- The stubs at `V` whose track ends at a node satisfying `K`. -/
def stubsTo (X : Finset Plane) (L : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane))
    (V : Finset (Set ℂ)) (K : PortNode × Sym2 Plane → Prop) : Finset (Set ℂ × Sym2 Plane) :=
  (stubsAt X L G mk V).filter (fun q => K (otherEnd X q))

/-- The track ends at a hull side whose return has at most one edge. -/
def UnitEnd (X : Finset Plane) (r : PortNode × Sym2 Plane) : Prop :=
  ∃ p, r.1 = Sum.inr p ∧ returnLength X p.1 p.2 ≤ 1

/-- The track ends at a two-edge return with exactly one short port (a `C₁` cap). -/
def OneShortEnd (X : Finset Plane) (L : ℝ) (r : PortNode × Sym2 Plane) : Prop :=
  ∃ p, r.1 = Sum.inr p ∧ returnLength X p.1 p.2 = 2 ∧ shortDeg X L (Sum.inr p) = 1

/-- The track ends at a two-edge return whose number of short ports is not one. -/
def TwoShortEnd (X : Finset Plane) (L : ℝ) (r : PortNode × Sym2 Plane) : Prop :=
  ∃ p, r.1 = Sum.inr p ∧ returnLength X p.1 p.2 = 2 ∧ shortDeg X L (Sum.inr p) ≠ 1

/-- The track ends at a hull return of at least three edges. -/
def LongReturnEnd (X : Finset Plane) (r : PortNode × Sym2 Plane) : Prop :=
  ∃ p, r.1 = Sum.inr p ∧ 3 ≤ returnLength X p.1 p.2

/-- The track ends at an exceptional face that is not good (a virtual cap). -/
def OmittedEnd (G : GoodFaces X) (r : PortNode × Sym2 Plane) : Prop :=
  ∃ F, r.1 = Sum.inl F ∧ F ∉ G.good

/-- The track ends at a marked port of a good face. -/
def MarkedEnd (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane)) (r : PortNode × Sym2 Plane) :
    Prop :=
  ∃ F, r.1 = Sum.inl F ∧ F ∈ G.good ∧ r.2 ∈ mk F

lemma stubsAt_subset (V : Finset (Set ℂ)) : stubsAt X L G mk V ⊆ unmarkedPorts X L G mk :=
  Finset.filter_subset _ _

lemma stubsTo_subset (V : Finset (Set ℂ)) (K : PortNode × Sym2 Plane → Prop) :
    stubsTo X L G mk V K ⊆ unmarkedPorts X L G mk :=
  (Finset.filter_subset _ _).trans (stubsAt_subset V)

lemma stubsTo_mono {V W : Finset (Set ℂ)} (h : V ⊆ W) (K : PortNode × Sym2 Plane → Prop) :
    stubsTo X L G mk V K ⊆ stubsTo X L G mk W K := by
  intro q hq
  simp only [stubsTo, stubsAt, Finset.mem_filter] at hq ⊢
  exact ⟨⟨hq.1.1, hq.1.2.1, h hq.1.2.2⟩, hq.2⟩

/-- **Classification of the stubs** by the other end of their track. -/
theorem stub_cases (hends : ∀ T ∈ allTracks X, (trackEnds X T).card = 2) {V : Finset (Set ℂ)}
    {q : Set ℂ × Sym2 Plane} (hq : q ∈ stubsAt X L G mk V) :
    UnitEnd X (otherEnd X q) ∨ OneShortEnd X L (otherEnd X q) ∨ TwoShortEnd X L (otherEnd X q) ∨
      LongReturnEnd X (otherEnd X q) ∨ OmittedEnd G (otherEnd X q) ∨
      MarkedEnd G mk (otherEnd X q) := by
  obtain ⟨hqP, hnm, -⟩ := Finset.mem_filter.1 hq
  set r := otherEnd X q with hr
  rcases hr1 : r.1 with F | p
  · by_cases hF : F ∈ G.good
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨F, hr1, hF, ?_⟩))))
      by_contra hmk
      apply hnm
      have hfp := unmarkedPorts_subset_facePorts hqP
      obtain ⟨-, h2, h3, h4⟩ := otherEnd_track hends hfp
      rw [← hr, hr1] at h3
      rw [← hr] at h2 h4
      obtain ⟨-, hsh, -⟩ := mem_unmarkedPorts.1 hqP
      refine ⟨by rw [← hr, hr1]; rfl, ?_⟩
      have hm : trackMate X q = (F, r.2) := by
        simp only [trackMate, ← hr, hr1, nodeFace, Sum.elim_inl, id]
      rw [hm]
      refine mem_unmarkedPorts.2 ⟨hF, Finset.mem_filter.2 ⟨h2, h3, ?_⟩, hmk⟩
      rw [h4]; exact (Finset.mem_filter.1 hsh).2.2
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨F, hr1, hF⟩))))
  · rcases Nat.lt_or_ge (returnLength X p.1 p.2) 2 with h | h
    · exact Or.inl ⟨p, hr1, by omega⟩
    · rcases Nat.lt_or_ge (returnLength X p.1 p.2) 3 with h' | h'
      · by_cases hs : shortDeg X L (Sum.inr p) = 1
        · exact Or.inr (Or.inl ⟨p, hr1, by omega, hs⟩)
        · exact Or.inr (Or.inr (Or.inl ⟨p, hr1, by omega, hs⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hr1, h'⟩)))

/-- The stubs at `V` split into the six classes. -/
theorem card_stubsAt_le (hends : ∀ T ∈ allTracks X, (trackEnds X T).card = 2)
    (V : Finset (Set ℂ)) :
    (stubsAt X L G mk V).card ≤ (stubsTo X L G mk V (UnitEnd X)).card +
      (stubsTo X L G mk V (OneShortEnd X L)).card + (stubsTo X L G mk V (TwoShortEnd X L)).card +
      (stubsTo X L G mk V (LongReturnEnd X)).card + (stubsTo X L G mk V (OmittedEnd G)).card +
      (stubsTo X L G mk V (MarkedEnd G mk)).card := by
  have hsub : stubsAt X L G mk V ⊆ stubsTo X L G mk V (UnitEnd X) ∪
      stubsTo X L G mk V (OneShortEnd X L) ∪ stubsTo X L G mk V (TwoShortEnd X L) ∪
      stubsTo X L G mk V (LongReturnEnd X) ∪ stubsTo X L G mk V (OmittedEnd G) ∪
      stubsTo X L G mk V (MarkedEnd G mk) := by
    intro q hq
    simp only [Finset.mem_union, stubsTo, Finset.mem_filter]
    rcases stub_cases hends hq with h | h | h | h | h | h <;> tauto
  refine (Finset.card_le_card hsub).trans ?_
  refine (Finset.card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
  refine (Finset.card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
  refine (Finset.card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
  refine (Finset.card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
  exact Finset.card_union_le _ _

/-! ## Bounds for the classes -/

/-- The stubs at omitted faces number at most `Bface`. -/
theorem card_stubsTo_omitted_le (hX : IsSeparated X)
    (hends : ∀ T ∈ allTracks X, (trackEnds X T).card = 2) (V : Finset (Set ℂ)) :
    (stubsTo X L G mk V (OmittedEnd G)).card ≤ G.Bface := by
  have h := card_le_shortEnds hends (stubsTo_subset (L := L) (G := G) (mk := mk) V (OmittedEnd G))
    (R := fun N => ∃ F, N = Sum.inl F ∧ F ∉ G.good) (fun q hq => (Finset.mem_filter.1 hq).2)
  rw [card_shortEnds, sum_portNodes_inl] at h
  set A := (exceptionalFinset X).filter (fun F => F ∉ G.good) with hA
  have h' : (stubsTo X L G mk V (OmittedEnd G)).card ≤ ∑ F ∈ A, shortDeg X L (Sum.inl F) :=
    h.trans (le_of_eq (Finset.sum_congr (by ext; simp [hA]) (fun _ _ => rfl)))
  refine h'.trans ?_
  calc ∑ F ∈ A, shortDeg X L (Sum.inl F) ≤ ∑ F ∈ A, faceSize X F := by
        refine Finset.sum_le_sum fun F hF => ?_
        rw [← portDeg_face ((mem_exceptionalFinset hX).1 (Finset.mem_filter.1 hF).1)]
        exact shortDeg_le_portDeg X L _
    _ = G.Bface := by rw [GoodFaces.Bface]

/-- The stubs at `C₁` caps number at most `C₁`. -/
theorem card_stubsTo_oneShort_le (hends : ∀ T ∈ allTracks X, (trackEnds X T).card = 2)
    (V : Finset (Set ℂ)) :
    (stubsTo X L G mk V (OneShortEnd X L)).card ≤ twoReturnsOneShort X L := by
  have h := card_le_shortEnds hends (stubsTo_subset (L := L) (G := G) (mk := mk) V (OneShortEnd X L))
    (R := fun N => ∃ p, N = Sum.inr p ∧
      (returnLength X p.1 p.2 = 2 ∧ shortDeg X L (Sum.inr p) = 1))
    (fun q hq => (Finset.mem_filter.1 hq).2)
  rw [card_shortEnds, sum_portNodes_inr] at h
  refine h.trans (le_of_eq ?_)
  rw [twoReturnsOneShort, Finset.card_eq_sum_ones]
  exact Finset.sum_congr (by ext; simp) fun p hp => (Finset.mem_filter.1 hp).2.2

/-- The stubs at two-edge returns with a number of short ports other than one number at most
`2 (c₂ - C₁)`. -/
theorem card_stubsTo_twoShort_le
    (hdeg : ∀ p ∈ ccwHullSides X, portDeg X (Sum.inr p) = returnLength X p.1 p.2)
    (hends : ∀ T ∈ allTracks X, (trackEnds X T).card = 2) (V : Finset (Set ℂ)) :
    (stubsTo X L G mk V (TwoShortEnd X L)).card + 2 * twoReturnsOneShort X L ≤
      2 * hullReturns X 2 := by
  set A := (ccwHullSides X).filter (fun p => returnLength X p.1 p.2 = 2 ∧
    shortDeg X L (Sum.inr p) ≠ 1) with hA
  have h := card_le_shortEnds hends (stubsTo_subset (L := L) (G := G) (mk := mk) V (TwoShortEnd X L))
    (R := fun N => ∃ p, N = Sum.inr p ∧
      (returnLength X p.1 p.2 = 2 ∧ shortDeg X L (Sum.inr p) ≠ 1))
    (fun q hq => (Finset.mem_filter.1 hq).2)
  rw [card_shortEnds, sum_portNodes_inr] at h
  have h' : (stubsTo X L G mk V (TwoShortEnd X L)).card ≤ ∑ p ∈ A, shortDeg X L (Sum.inr p) :=
    h.trans (le_of_eq (Finset.sum_congr (by ext; simp [hA]) (fun _ _ => rfl)))
  have hsplit : hullReturns X 2 = A.card + twoReturnsOneShort X L := by
    rw [hullReturns, twoReturnsOneShort, ← Finset.card_union_of_disjoint]
    · congr 1
      ext p
      simp only [hA, Finset.mem_filter, Finset.mem_union]
      tauto
    · rw [Finset.disjoint_left]
      intro p h1 h2
      exact (Finset.mem_filter.1 h1).2.2 (Finset.mem_filter.1 h2).2.2
  have hle : ∑ p ∈ A, shortDeg X L (Sum.inr p) ≤ 2 * A.card := by
    rw [mul_comm, Finset.card_eq_sum_ones, Finset.sum_mul]
    refine Finset.sum_le_sum fun p hp => ?_
    obtain ⟨hp1, hp2, -⟩ := Finset.mem_filter.1 hp
    have := shortDeg_le_portDeg X L (Sum.inr p)
    rw [hdeg p hp1, hp2] at this
    omega
  omega

/-- The stubs at hull returns of at least three edges number at most `3 ρ`. -/
theorem card_stubsTo_longReturn_le
    (hdeg : ∀ p ∈ ccwHullSides X, portDeg X (Sum.inr p) = returnLength X p.1 p.2)
    (hends : ∀ T ∈ allTracks X, (trackEnds X T).card = 2) (V : Finset (Set ℂ)) :
    (stubsTo X L G mk V (LongReturnEnd X)).card ≤ 3 * returnExcess X := by
  set A := (ccwHullSides X).filter (fun p => 3 ≤ returnLength X p.1 p.2) with hA
  have h := card_le_shortEnds hends
    (stubsTo_subset (L := L) (G := G) (mk := mk) V (LongReturnEnd X))
    (R := fun N => ∃ p, N = Sum.inr p ∧ 3 ≤ returnLength X p.1 p.2)
    (fun q hq => (Finset.mem_filter.1 hq).2)
  rw [card_shortEnds, sum_portNodes_inr] at h
  have h' : (stubsTo X L G mk V (LongReturnEnd X)).card ≤ ∑ p ∈ A, shortDeg X L (Sum.inr p) :=
    h.trans (le_of_eq (Finset.sum_congr (by ext; simp [hA]) (fun _ _ => rfl)))
  refine h'.trans ?_
  calc ∑ p ∈ A, shortDeg X L (Sum.inr p)
      ≤ ∑ p ∈ A, 3 * (returnLength X p.1 p.2 - 2) := by
        refine Finset.sum_le_sum fun p hp => ?_
        obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
        have := shortDeg_le_portDeg X L (Sum.inr p)
        rw [hdeg p hp1] at this
        omega
    _ ≤ ∑ p ∈ ccwHullSides X, 3 * (returnLength X p.1 p.2 - 2) :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = 3 * returnExcess X := by rw [returnExcess, Finset.mul_sum]

/-! ## The cap bounds -/

/-- The stubs of the track graph at the faces of `V ⊆ good` are the stubs counted by `stubsAt`. -/
theorem trackGraph_bIn (V : Finset (Set ℂ)) :
    (trackGraph X L G mk).bIn V = (stubsAt X L G mk V).card := by
  rw [trackGraph, StubGraph.bIn_ofHalfEdges]
  rfl

/-- **The cap bound `C` for the track graph**:

  `C + C₁ ≤ 2 c₂ + (unit stubs) + (marked stubs) + 2 e_HH + 3 ρ + Bface`. -/
theorem trackGraph_capInc_le (hX : IsSeparated X)
    (hdeg : ∀ p ∈ ccwHullSides X, portDeg X (Sum.inr p) = returnLength X p.1 p.2)
    (hends : ∀ T ∈ allTracks X, (trackEnds X T).card = 2) :
    (trackGraph X L G mk).bIn G.good +
        2 * (trackGraph X L G mk).eIn ((trackGraph X L G mk).Hs G.good)
          ((trackGraph X L G mk).Hs G.good) + twoReturnsOneShort X L ≤
      2 * hullReturns X 2 + (stubsTo X L G mk G.good (UnitEnd X)).card +
        (stubsTo X L G mk G.good (MarkedEnd G mk)).card +
        2 * (trackGraph X L G mk).eIn ((trackGraph X L G mk).Hs G.good)
          ((trackGraph X L G mk).Hs G.good) + 3 * returnExcess X + G.Bface := by
  rw [trackGraph_bIn]
  have h1 := card_stubsAt_le (L := L) (G := G) (mk := mk) hends G.good
  have h2 := card_stubsTo_omitted_le (L := L) (G := G) (mk := mk) hX hends G.good
  have h3 := card_stubsTo_oneShort_le (L := L) (G := G) (mk := mk) hends G.good
  have h4 := card_stubsTo_twoShort_le (L := L) (G := G) (mk := mk) hdeg hends G.good
  have h5 := card_stubsTo_longReturn_le (L := L) (G := G) (mk := mk) hdeg hends G.good
  omega

/-- **The cap bound `hC` for the track graph**:

  `hC + 2 C₁ ≤ 2 c₂ + (unit, C₁ and marked stubs at H) + 2 e_HH + 3 ρ + Bface`. -/
theorem trackGraph_hCapInc_le (hX : IsSeparated X)
    (hdeg : ∀ p ∈ ccwHullSides X, portDeg X (Sum.inr p) = returnLength X p.1 p.2)
    (hends : ∀ T ∈ allTracks X, (trackEnds X T).card = 2) :
    (trackGraph X L G mk).bIn ((trackGraph X L G mk).Hs G.good) +
        2 * (trackGraph X L G mk).eIn ((trackGraph X L G mk).Hs G.good)
          ((trackGraph X L G mk).Hs G.good) + 2 * twoReturnsOneShort X L ≤
      2 * hullReturns X 2 +
        (stubsTo X L G mk ((trackGraph X L G mk).Hs G.good) (UnitEnd X)).card +
        (stubsTo X L G mk ((trackGraph X L G mk).Hs G.good) (OneShortEnd X L)).card +
        (stubsTo X L G mk ((trackGraph X L G mk).Hs G.good) (MarkedEnd G mk)).card +
        2 * (trackGraph X L G mk).eIn ((trackGraph X L G mk).Hs G.good)
          ((trackGraph X L G mk).Hs G.good) + 3 * returnExcess X + G.Bface := by
  set H := (trackGraph X L G mk).Hs G.good
  rw [trackGraph_bIn]
  have h1 := card_stubsAt_le (L := L) (G := G) (mk := mk) hends H
  have h2 := card_stubsTo_omitted_le (L := L) (G := G) (mk := mk) hX hends H
  have h4 := card_stubsTo_twoShort_le (L := L) (G := G) (mk := mk) hdeg hends H
  have h5 := card_stubsTo_longReturn_le (L := L) (G := G) (mk := mk) hdeg hends H
  omega

end Erdos99

end

end TrackCapBounds

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `DirectionPinning`
-/

section DirectionPinning

/-!
# Uniform direction pinning: the approximate-to-exact step (Verification Guide §12.4)

The local exclusion calculations of §13 produce, for each bounded pattern, a necessary polynomial
equation `p(ζ) = 0` for the common unit tangent `ζ`, whose coefficients depend continuously on the
data of the pattern.  In the actual configuration these equations only hold approximately, and the
coefficients vary.  This file proves the uniform statement that turns approximate equations into
pinned directions, without any compactness argument on the parameter family:

* `coeffPoly c`: the polynomial `∑ cᵢ Xⁱ` of a coefficient vector `c : Fin (d + 1) → ℂ`
  (with the sup norm on coefficient vectors);
* `exists_eval_nat_lower` (Vandermonde bound): some value `p(j)`, `j ∈ {0, …, d}`, is at least
  `β ‖c‖`;
* `norm_eval_ge_of_roots`: comparison of `|p(z)|` and `|p(y)|` through the factorization over the
  roots;
* `uniform_lower_bound_off_roots`: **a polynomial of degree at most `d` is bounded below by
  `κ ‖c‖` on the closed unit disc at distance at least `w` from its roots**, with `κ > 0`
  depending only on `d` and `w`;
* `near_roots_of_small_eval`: **uniform pinning**: for coefficient vectors `c` within `μ` of a
  vector `c₀` with `‖c₀‖ ≥ m₀`, every point `z` of the unit disc with `|p_c(z)| < r` lies within `w`
  of one of the at most `d` roots of `p_{c₀}` (`card_roots_toFinset_le`).  Here `r, μ > 0` depend
  only on `d`, `w` and `m₀`.

Applied with `c₀` the coefficients of a cluster centre (of which there are boundedly many, with a
bound independent of the tolerances, Lemma 3.3), this pins the source direction of every pattern
to at most `d` arcs of width `w` per cluster pattern, as required in §12.5.
-/

open Polynomial

@[expose] public noncomputable section

namespace Erdos99

namespace DirectionPinning

variable {d : ℕ}

/-- The polynomial `∑ᵢ cᵢ Xⁱ` with coefficient vector `c`. -/
def coeffPoly (c : Fin (d + 1) → ℂ) : ℂ[X] := ∑ i, C (c i) * X ^ (i : ℕ)

lemma eval_coeffPoly (c : Fin (d + 1) → ℂ) (z : ℂ) :
    (coeffPoly c).eval z = ∑ i, c i * z ^ (i : ℕ) := by
  simp [coeffPoly, eval_finset_sum]

lemma natDegree_coeffPoly_le (c : Fin (d + 1) → ℂ) : (coeffPoly c).natDegree ≤ d := by
  unfold coeffPoly
  refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.1 i.2)

lemma coeff_coeffPoly (c : Fin (d + 1) → ℂ) (i : Fin (d + 1)) :
    (coeffPoly c).coeff i = c i := by
  simp only [coeffPoly, finset_sum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have : (i : ℕ) ≠ j := fun h => hji (Fin.ext h).symm
    simp [this]
  · simp

lemma coeffPoly_eq_zero_iff (c : Fin (d + 1) → ℂ) : coeffPoly c = 0 ↔ c = 0 := by
  constructor
  · intro h
    funext i
    rw [← coeff_coeffPoly c i, h, coeff_zero, Pi.zero_apply]
  · rintro rfl
    simp [coeffPoly]

lemma card_roots_toFinset_le (c : Fin (d + 1) → ℂ) : (coeffPoly c).roots.toFinset.card ≤ d :=
  (Multiset.toFinset_card_le _).trans ((card_roots' _).trans (natDegree_coeffPoly_le c))

lemma eval_coeffPoly_smul (t : ℂ) (c : Fin (d + 1) → ℂ) (z : ℂ) :
    (coeffPoly (t • c)).eval z = t * (coeffPoly c).eval z := by
  rw [eval_coeffPoly, eval_coeffPoly, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_assoc]

lemma eval_coeffPoly_sub (c c' : Fin (d + 1) → ℂ) (z : ℂ) :
    (coeffPoly (c - c')).eval z = (coeffPoly c).eval z - (coeffPoly c').eval z := by
  rw [eval_coeffPoly, eval_coeffPoly, eval_coeffPoly, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [sub_mul]

/-- On the closed unit disc, `|p_c(z)| ≤ (d + 1) ‖c‖`. -/
lemma norm_eval_coeffPoly_le (c : Fin (d + 1) → ℂ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖(coeffPoly c).eval z‖ ≤ (d + 1) * ‖c‖ := by
  rw [eval_coeffPoly]
  refine (norm_sum_le _ _).trans ?_
  have : ∀ i ∈ (Finset.univ : Finset (Fin (d + 1))), ‖c i * z ^ (i : ℕ)‖ ≤ ‖c‖ := by
    intro i _
    rw [norm_mul, norm_pow]
    calc ‖c i‖ * ‖z‖ ^ (i : ℕ) ≤ ‖c i‖ * 1 := by
          gcongr
          exact pow_le_one₀ (norm_nonneg _) hz
      _ ≤ ‖c‖ := by rw [mul_one]; exact norm_le_pi_norm c i
  refine (Finset.sum_le_sum this).trans ?_
  simp

/-- **Vandermonde bound**: there is `β > 0` such that for every coefficient vector `c` some value
`p_c(j)`, `j ∈ {0, …, d}`, has modulus at least `β ‖c‖`. -/
lemma exists_eval_nat_lower (d : ℕ) :
    ∃ β > 0, ∀ c : Fin (d + 1) → ℂ, ∃ j : Fin (d + 1),
      β * ‖c‖ ≤ ‖(coeffPoly c).eval ((j : ℕ) : ℂ)‖ := by
  set E : (Fin (d + 1) → ℂ) → (Fin (d + 1) → ℂ) :=
    fun c j => (coeffPoly c).eval ((j : ℕ) : ℂ) with hEdef
  have hEc : Continuous E := by
    refine continuous_pi fun j => ?_
    simp only [hEdef, eval_coeffPoly]
    exact continuous_finset_sum _ fun i _ => (continuous_apply i).mul continuous_const
  have hE0 : ∀ c, E c = 0 → c = 0 := by
    intro c hc
    rw [← coeffPoly_eq_zero_iff]
    refine eq_zero_of_natDegree_lt_card_of_eval_eq_zero (coeffPoly c)
      (f := fun j : Fin (d + 1) => ((j : ℕ) : ℂ)) ?_ (fun j => congrFun hc j) ?_
    · intro i j h
      have h' : ((i : ℕ) : ℂ) = ((j : ℕ) : ℂ) := h
      exact Fin.ext (by exact_mod_cast h')
    · rw [Fintype.card_fin]; exact Nat.lt_succ_of_le (natDegree_coeffPoly_le c)
  have hS := isCompact_sphere (0 : Fin (d + 1) → ℂ) 1
  have hne : (Metric.sphere (0 : Fin (d + 1) → ℂ) 1).Nonempty :=
    (NormedSpace.sphere_nonempty).2 zero_le_one
  obtain ⟨c₀, hc₀, hmin⟩ :=
    hS.exists_isMinOn hne (continuous_norm.comp hEc).continuousOn
  have hc₀n : ‖c₀‖ = 1 := by simpa using hc₀
  have hc₀z : c₀ ≠ 0 := by intro h; rw [h, norm_zero] at hc₀n; exact zero_ne_one hc₀n
  refine ⟨‖E c₀‖, norm_pos_iff.2 fun h => hc₀z (hE0 c₀ h), fun c => ?_⟩
  by_cases hc : c = 0
  · exact ⟨0, by simp [hc]⟩
  set u : Fin (d + 1) → ℂ := ((‖c‖⁻¹ : ℝ) : ℂ) • c with hu
  have hcpos : 0 < ‖c‖ := norm_pos_iff.2 hc
  have hun : ‖u‖ = 1 := by
    rw [hu, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ hcpos.ne']
  have hEu : ‖E c₀‖ ≤ ‖E u‖ := hmin (by simpa using hun)
  have hcu : c = ((‖c‖ : ℝ) : ℂ) • u := by
    rw [hu, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hcpos.ne', Complex.ofReal_one,
      one_smul]
  obtain ⟨j, hj⟩ := Finite.exists_max (fun j => ‖E u j‖)
  refine ⟨j, ?_⟩
  have hnorm : ‖E u‖ ≤ ‖E u j‖ := (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 hj
  have hval : (coeffPoly c).eval ((j : ℕ) : ℂ) = ((‖c‖ : ℝ) : ℂ) * E u j := by
    conv_lhs => rw [hcu]
    rw [eval_coeffPoly_smul]
  rw [hval, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_norm, mul_comm]
  exact mul_le_mul_of_nonneg_left (hEu.trans hnorm) hcpos.le

/-- **Comparison through the roots.**  If `q ‖y - ρ‖ ≤ ‖z - ρ‖` for every root `ρ` of `p ≠ 0`
(with multiplicity), then `q ^ deg p · |p(y)| ≤ |p(z)|`. -/
lemma norm_eval_ge_of_roots {p : ℂ[X]} {z y : ℂ} {q : ℝ} (hq : 0 ≤ q)
    (h : ∀ ρ ∈ p.roots, q * ‖y - ρ‖ ≤ ‖z - ρ‖) :
    q ^ p.natDegree * ‖p.eval y‖ ≤ ‖p.eval z‖ := by
  have hfac := C_leadingCoeff_mul_prod_multiset_X_sub_C (IsAlgClosed.card_roots_eq_natDegree (p := p))
  have hev : ∀ x : ℂ, ‖p.eval x‖ = ‖p.leadingCoeff‖ * (p.roots.map (fun ρ => ‖x - ρ‖)).prod := by
    intro x
    conv_lhs => rw [← hfac]
    rw [eval_mul, eval_C, eval_multiset_prod, norm_mul, Multiset.map_map]
    congr 1
    have := map_multiset_prod (normHom : ℂ →*₀ ℝ) (Multiset.map (eval x ∘ fun a => X - C a) p.roots)
    rw [Multiset.map_map] at this
    rw [show ‖(Multiset.map (eval x ∘ fun a => X - C a) p.roots).prod‖ =
      (normHom : ℂ →*₀ ℝ) (Multiset.map (eval x ∘ fun a => X - C a) p.roots).prod from rfl, this]
    congr 1
    refine Multiset.map_congr rfl fun ρ _ => ?_
    simp
  rw [hev, hev, ← IsAlgClosed.card_roots_eq_natDegree (p := p)]
  have hprod : q ^ Multiset.card p.roots * (p.roots.map (fun ρ => ‖y - ρ‖)).prod =
      (p.roots.map (fun ρ => q * ‖y - ρ‖)).prod := by
    rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate]
  calc q ^ Multiset.card p.roots * (‖p.leadingCoeff‖ * (p.roots.map (fun ρ => ‖y - ρ‖)).prod)
      = ‖p.leadingCoeff‖ * (p.roots.map (fun ρ => q * ‖y - ρ‖)).prod := by rw [← hprod]; ring
    _ ≤ ‖p.leadingCoeff‖ * (p.roots.map (fun ρ => ‖z - ρ‖)).prod := by
        gcongr
        exact Multiset.prod_map_le_prod_map₀ _ _ (fun ρ _ => by positivity) h

/-- **Uniform lower bound away from the roots** (Verification Guide §12.4).  For every degree
bound `d` and every `w > 0` there is `κ > 0` such that every polynomial `p_c = ∑ cᵢ Xⁱ` of degree at
most `d` satisfies `|p_c(z)| ≥ κ ‖c‖` at every point `z` of the closed unit disc whose distance to
every root of `p_c` is at least `w`. -/
theorem uniform_lower_bound_off_roots (d : ℕ) {w : ℝ} (hw : 0 < w) :
    ∃ κ > 0, ∀ (c : Fin (d + 1) → ℂ) (z : ℂ), ‖z‖ ≤ 1 →
      (∀ ρ ∈ (coeffPoly c).roots, w ≤ ‖z - ρ‖) → κ * ‖c‖ ≤ ‖(coeffPoly c).eval z‖ := by
  obtain ⟨β, hβ, hA⟩ := exists_eval_nat_lower d
  set q : ℝ := min (w / (3 * d + 2)) (1 / 2) with hqdef
  have hq0 : 0 < q := lt_min (by positivity) (by norm_num)
  have hq1 : q ≤ 1 := (min_le_right _ _).trans (by norm_num)
  refine ⟨β * q ^ d, by positivity, fun c z hz hroots => ?_⟩
  obtain ⟨j, hj⟩ := hA c
  have hjd : ‖((j : ℕ) : ℂ)‖ ≤ d := by
    rw [Complex.norm_natCast]; exact_mod_cast Nat.lt_succ_iff.1 j.2
  have hcmp : ∀ ρ ∈ (coeffPoly c).roots, q * ‖((j : ℕ) : ℂ) - ρ‖ ≤ ‖z - ρ‖ := by
    intro ρ hρ
    have hyρ : ‖((j : ℕ) : ℂ) - ρ‖ ≤ d + ‖ρ‖ := (norm_sub_le _ _).trans (by linarith)
    have hzρ : ‖ρ‖ - 1 ≤ ‖z - ρ‖ := by
      have := norm_sub_norm_le ρ z
      rw [norm_sub_rev] at this; linarith
    rcases le_or_gt ‖ρ‖ (2 * d + 2) with hsmall | hlarge
    · have hq' : q ≤ w / (3 * d + 2) := min_le_left _ _
      have : q * ‖((j : ℕ) : ℂ) - ρ‖ ≤ w / (3 * d + 2) * (3 * d + 2) := by
        apply mul_le_mul hq' (by linarith) (norm_nonneg _) (by positivity)
      rw [div_mul_cancel₀ _ (by positivity)] at this
      linarith [hroots ρ hρ]
    · have hq' : q ≤ 1 / 2 := min_le_right _ _
      have : q * ‖((j : ℕ) : ℂ) - ρ‖ ≤ 1 / 2 * (d + ‖ρ‖) :=
        mul_le_mul hq' hyρ (norm_nonneg _) (by norm_num)
      linarith
  have hB := norm_eval_ge_of_roots hq0.le hcmp
  have hpow : q ^ d ≤ q ^ (coeffPoly c).natDegree :=
    pow_le_pow_of_le_one hq0.le hq1 (natDegree_coeffPoly_le c)
  calc β * q ^ d * ‖c‖ = q ^ d * (β * ‖c‖) := by ring
    _ ≤ q ^ (coeffPoly c).natDegree * ‖(coeffPoly c).eval ((j : ℕ) : ℂ)‖ :=
        mul_le_mul hpow hj (by positivity) (by positivity)
    _ ≤ _ := hB

/-- **Uniform direction pinning** (Verification Guide §12.4).  For every degree bound `d`, arc
width `w > 0` and coefficient lower bound `m₀ > 0` there are a residual tolerance `r > 0` and a
coefficient tolerance `μ > 0` such that: whenever `‖c₀‖ ≥ m₀` and `‖c - c₀‖ < μ`, every point `z` of
the closed unit disc with `|p_c(z)| < r` lies within `w` of a root of `p_{c₀}`.  (The polynomial
`p_{c₀}` has at most `d` distinct roots, `card_roots_toFinset_le`.) -/
theorem near_roots_of_small_eval (d : ℕ) {w m₀ : ℝ} (hw : 0 < w) (hm₀ : 0 < m₀) :
    ∃ r > 0, ∃ μ > 0, ∀ c₀ c : Fin (d + 1) → ℂ, m₀ ≤ ‖c₀‖ → ‖c - c₀‖ < μ →
      ∀ z : ℂ, ‖z‖ ≤ 1 → ‖(coeffPoly c).eval z‖ < r →
        ∃ ρ ∈ (coeffPoly c₀).roots, ‖z - ρ‖ < w := by
  obtain ⟨κ, hκ, hlow⟩ := uniform_lower_bound_off_roots d hw
  have hd : (0 : ℝ) < d + 1 := by positivity
  refine ⟨κ * m₀ / 2, by positivity, κ * m₀ / (2 * (d + 1)), by positivity, ?_⟩
  intro c₀ c hc₀ hcc z hz hev
  by_contra hcon
  push_neg at hcon
  have h1 := hlow c₀ z hz hcon
  have h2 : ‖(coeffPoly (c - c₀)).eval z‖ ≤ (d + 1) * ‖c - c₀‖ := norm_eval_coeffPoly_le _ hz
  rw [eval_coeffPoly_sub] at h2
  have h3 : ‖(coeffPoly c₀).eval z‖ ≤ ‖(coeffPoly c).eval z‖ +
      ‖(coeffPoly c).eval z - (coeffPoly c₀).eval z‖ := by
    have := norm_sub_le ((coeffPoly c).eval z) ((coeffPoly c).eval z - (coeffPoly c₀).eval z)
    rwa [sub_sub_cancel] at this
  have h4 : (d + 1) * ‖c - c₀‖ < κ * m₀ / 2 := by
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    rw [lt_div_iff₀ (by positivity)] at hcc
    nlinarith
  have h5 : κ * m₀ ≤ κ * ‖c₀‖ := mul_le_mul_of_nonneg_left hc₀ hκ.le
  linarith

end DirectionPinning

end Erdos99

end

end DirectionPinning

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `PinnedCount`
-/

section PinnedCount

/-!
# Pinned directions are few (Verification Guide §12.5)

This file converts the uniform direction pinning of `DirectionPinning` (§12.4) into the
counting statement used by the local exclusion estimates of §13.

* `norm_pow_six_sub_le_of_near`: `|a⁶ - b⁶| ≤ 192 |a - b|` for `|a| = 1`, `|a - b| ≤ 1`;
* `card_sides_near_finset`: the number of hull sides whose unit direction lies within `w` of a
  finite set `S` is at most `C D |S| (w + D^{-1/9})` (from the spread of hull directions,
  `hull_direction_spread_rate`);
* `pinned_directions_few`: **pinned hull directions are few.**  Fix a degree bound `d`, a number
  `N` of coefficient centres (the cluster patterns, whose number does not depend on the tolerances)
  and a lower bound `m₀ > 0` for the centre coefficients.  For every `ε > 0` there are a residual
  tolerance `r > 0` and a coefficient tolerance `μ > 0` such that, eventually, in every optimal
  configuration, any set of hull sides whose unit directions `ζ` satisfy an approximate pinning
  equation `|p_c(ζ)| < r` with coefficients `c` within `μ` of one of the centres has at most `ε D`
  elements.
-/

open Filter Polynomial

@[expose] public noncomputable section

open Classical


namespace Erdos99

open DirectionPinning

/-- `|a⁶ - b⁶| ≤ 192 |a - b|` on the unit circle, for `|a - b| ≤ 1`. -/
lemma norm_pow_six_sub_le_of_near {a b : ℂ} (ha : ‖a‖ = 1) (hab : ‖a - b‖ ≤ 1) :
    ‖a ^ 6 - b ^ 6‖ ≤ 192 * ‖a - b‖ := by
  have hb : ‖b‖ ≤ 2 := by
    have := norm_sub_norm_le a (a - b)
    rw [sub_sub_cancel] at this
    calc ‖b‖ = ‖a - (a - b)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖a‖ + ‖a - b‖ := norm_sub_le _ _
      _ ≤ 2 := by rw [ha]; linarith
  have hfac : a ^ 6 - b ^ 6 =
      (a - b) * (a ^ 5 + a ^ 4 * b + a ^ 3 * b ^ 2 + a ^ 2 * b ^ 3 + a * b ^ 4 + b ^ 5) := by ring
  have hterm : ∀ i j : ℕ, i + j = 5 → ‖a ^ i * b ^ j‖ ≤ 32 := by
    intro i j hij
    rw [norm_mul, norm_pow, norm_pow, ha, one_pow, one_mul]
    calc ‖b‖ ^ j ≤ 2 ^ j := pow_le_pow_left₀ (norm_nonneg _) hb j
      _ ≤ 2 ^ 5 := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = 32 := by norm_num
  have hsum : ‖a ^ 5 + a ^ 4 * b + a ^ 3 * b ^ 2 + a ^ 2 * b ^ 3 + a * b ^ 4 + b ^ 5‖ ≤ 192 := by
    have h0 := hterm 5 0 rfl
    have h1 := hterm 4 1 rfl
    have h2 := hterm 3 2 rfl
    have h3 := hterm 2 3 rfl
    have h4 := hterm 1 4 rfl
    have h5 := hterm 0 5 rfl
    simp only [pow_zero, mul_one, one_mul, pow_one] at h0 h1 h2 h3 h4 h5
    calc _ ≤ ‖a ^ 5 + a ^ 4 * b + a ^ 3 * b ^ 2 + a ^ 2 * b ^ 3 + a * b ^ 4‖ + ‖b ^ 5‖ :=
          norm_add_le _ _
      _ ≤ ‖a ^ 5 + a ^ 4 * b + a ^ 3 * b ^ 2 + a ^ 2 * b ^ 3‖ + ‖a * b ^ 4‖ + ‖b ^ 5‖ := by
          gcongr; exact norm_add_le _ _
      _ ≤ ‖a ^ 5 + a ^ 4 * b + a ^ 3 * b ^ 2‖ + ‖a ^ 2 * b ^ 3‖ + ‖a * b ^ 4‖ + ‖b ^ 5‖ := by
          gcongr; exact norm_add_le _ _
      _ ≤ ‖a ^ 5 + a ^ 4 * b‖ + ‖a ^ 3 * b ^ 2‖ + ‖a ^ 2 * b ^ 3‖ + ‖a * b ^ 4‖ + ‖b ^ 5‖ := by
          gcongr; exact norm_add_le _ _
      _ ≤ ‖a ^ 5‖ + ‖a ^ 4 * b‖ + ‖a ^ 3 * b ^ 2‖ + ‖a ^ 2 * b ^ 3‖ + ‖a * b ^ 4‖ + ‖b ^ 5‖ := by
          gcongr; exact norm_add_le _ _
      _ ≤ 192 := by linarith
  rw [hfac, norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right hsum (norm_nonneg _)

/-- **Hull sides with direction near a finite set** (from the spread of hull directions,
Lemma 3.2).  There is `C ≥ 0` such that eventually, in every optimal configuration, for every finite
set `S ⊆ ℂ` and `0 ≤ w ≤ 1`, at most `C D |S| (w + D^{-1/9})` counterclockwise hull sides have unit
direction within `w` of `S`. -/
theorem card_sides_near_finset : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ X, IsOptimal n X →
    ∀ (S : Finset ℂ) (w : ℝ), 0 ≤ w → w ≤ 1 →
      (((ccwHullSides X).filter (fun p => ∃ s ∈ S, ‖toC (sideDir p) - s‖ ≤ w)).card : ℝ) ≤
        C * diam X * S.card * (w + diam X ^ (-(1 / 9 : ℝ))) := by
  obtain ⟨C₀, hC₀⟩ := hull_direction_spread_rate
  refine ⟨192 * |C₀|, by positivity, ?_⟩
  filter_upwards [hC₀] with n hn X hX S w hw0 hw1
  have h := hn X hX (S.image (· ^ 6)) (192 * w) (by positivity)
  have hc1 : (((ccwHullSides X).filter (fun p => ∃ s ∈ S, ‖toC (sideDir p) - s‖ ≤ w)).card : ℝ) ≤
      C₀ * diam X * (S.image (· ^ 6)).card * (192 * w + diam X ^ (-(1 / 9 : ℝ))) := by
    refine le_trans ?_ h
    refine Nat.cast_le.2 (Finset.card_le_card fun p hp => ?_)
    obtain ⟨hpS, s, hs, hps⟩ := Finset.mem_filter.1 hp
    refine Finset.mem_filter.2 ⟨hpS, s ^ 6, Finset.mem_image_of_mem _ hs, ?_⟩
    have hne : p.1 ≠ p.2 := (Finset.mem_filter.1 hpS).2.2.2.1
    have hu : ‖toC (sideDir p)‖ = 1 := by rw [LinearIsometryEquiv.norm_map]; exact norm_sideDir hne
    rw [dir6_eq_pow_sideDir]
    calc _ ≤ 192 * ‖toC (sideDir p) - s‖ := norm_pow_six_sub_le_of_near hu (hps.trans hw1)
      _ ≤ 192 * w := by linarith
  have hD : 0 ≤ diam X := Metric.diam_nonneg
  have ht : 0 ≤ diam X ^ (-(1 / 9 : ℝ)) := Real.rpow_nonneg hD _
  have himg : ((S.image (· ^ 6)).card : ℝ) ≤ S.card := by exact_mod_cast Finset.card_image_le
  have hk : 0 ≤ diam X * (S.image (· ^ 6)).card * (192 * w + diam X ^ (-(1 / 9 : ℝ))) := by
    positivity
  have h2 : C₀ * diam X * (S.image (· ^ 6)).card * (192 * w + diam X ^ (-(1 / 9 : ℝ))) ≤
      |C₀| * (diam X * (S.image (· ^ 6)).card * (192 * w + diam X ^ (-(1 / 9 : ℝ)))) := by
    rw [mul_assoc, mul_assoc, ← mul_assoc (diam X)]
    exact mul_le_mul_of_nonneg_right (le_abs_self C₀) hk
  have h3 : diam X * (S.image (· ^ 6)).card * (192 * w + diam X ^ (-(1 / 9 : ℝ))) ≤
      192 * (diam X * S.card * (w + diam X ^ (-(1 / 9 : ℝ)))) := by
    have : diam X * (S.image (· ^ 6)).card ≤ diam X * S.card := mul_le_mul_of_nonneg_left himg hD
    have h4 : (192 * w + diam X ^ (-(1 / 9 : ℝ))) ≤ 192 * (w + diam X ^ (-(1 / 9 : ℝ))) := by
      linarith
    calc _ ≤ diam X * S.card * (192 * w + diam X ^ (-(1 / 9 : ℝ))) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ ≤ diam X * S.card * (192 * (w + diam X ^ (-(1 / 9 : ℝ)))) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = _ := by ring
  have h5 := mul_le_mul_of_nonneg_left h3 (abs_nonneg C₀)
  calc _ ≤ _ := hc1
    _ ≤ _ := h2
    _ ≤ |C₀| * (192 * (diam X * S.card * (w + diam X ^ (-(1 / 9 : ℝ))))) := h5
    _ = _ := by ring

/-- **Pinned hull directions are few** (Verification Guide §12.4–§12.5).  Fix a degree bound `d`,
a number `N` of coefficient centres and a lower bound `m₀ > 0` on their coefficient vectors.  For
every `ε > 0` there are tolerances `r, μ > 0` such that eventually, in every optimal configuration,
for all centres `c₀ j` (`j < N`) with `‖c₀ j‖ ≥ m₀`, every set `A` of counterclockwise hull sides
whose unit directions `ζ` each satisfy `|p_c(ζ)| < r` for some coefficient vector `c` within `μ`
of some centre has at most `ε D` elements. -/
theorem pinned_directions_few (d N : ℕ) {ε m₀ : ℝ} (hε : 0 < ε) (hm₀ : 0 < m₀) :
    ∃ r > 0, ∃ μ > 0, ∀ᶠ n in atTop, ∀ X, IsOptimal n X →
      ∀ c₀ : Fin N → Fin (d + 1) → ℂ, (∀ j, m₀ ≤ ‖c₀ j‖) →
      ∀ A ⊆ ccwHullSides X, (∀ p ∈ A, ∃ j c, ‖c - c₀ j‖ < μ ∧
        ‖(coeffPoly c).eval (toC (sideDir p))‖ < r) →
      (A.card : ℝ) ≤ ε * diam X := by
  obtain ⟨C, hC, hcount⟩ := card_sides_near_finset
  set K : ℝ := N * d with hK
  have hK0 : 0 ≤ K := by positivity
  set w : ℝ := min 1 (ε / (2 * (C * K + 1))) with hw
  have hw0 : 0 < w := lt_min one_pos (by positivity)
  have hw1 : w ≤ 1 := min_le_left _ _
  obtain ⟨r, hr, μ, hμ, hpin⟩ := near_roots_of_small_eval d hw0 hm₀
  refine ⟨r, hr, μ, hμ, ?_⟩
  have hsmall : ∀ᶠ n in atTop, minDiam n ^ (-(1 / 9 : ℝ)) ≤ w :=
    ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 9)).comp tendsto_minDiam).eventually
      (Iic_mem_nhds hw0)
  filter_upwards [hcount, hsmall] with n hn hsm X hX c₀ hc₀ A hA hpA
  rw [← hX.diam_eq] at hsm
  set S : Finset ℂ := Finset.univ.biUnion (fun j => (coeffPoly (c₀ j)).roots.toFinset) with hS
  have hScard : (S.card : ℝ) ≤ K := by
    have : S.card ≤ N * d := by
      refine Finset.card_biUnion_le.trans ?_
      calc ∑ j : Fin N, (coeffPoly (c₀ j)).roots.toFinset.card ≤ ∑ _j : Fin N, d :=
            Finset.sum_le_sum fun j _ => card_roots_toFinset_le _
        _ = N * d := by simp
    rw [hK]; exact_mod_cast this
  have hsub : A ⊆ (ccwHullSides X).filter (fun p => ∃ s ∈ S, ‖toC (sideDir p) - s‖ ≤ w) := by
    intro p hp
    refine Finset.mem_filter.2 ⟨hA hp, ?_⟩
    obtain ⟨j, c, hc, hev⟩ := hpA p hp
    have hne : p.1 ≠ p.2 := (Finset.mem_filter.1 (hA hp)).2.2.2.1
    have hu : ‖toC (sideDir p)‖ = 1 := by rw [LinearIsometryEquiv.norm_map]; exact norm_sideDir hne
    obtain ⟨ρ, hρ, hzρ⟩ := hpin (c₀ j) c (hc₀ j) hc _ hu.le hev
    exact ⟨ρ, Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, Multiset.mem_toFinset.2 hρ⟩, hzρ.le⟩
  have h1 : (A.card : ℝ) ≤ C * diam X * S.card * (w + diam X ^ (-(1 / 9 : ℝ))) :=
    (by exact_mod_cast Finset.card_le_card hsub : (A.card : ℝ) ≤ _).trans (hn X hX S w hw0.le hw1)
  have hD : 0 ≤ diam X := Metric.diam_nonneg
  have h2 : C * diam X * S.card * (w + diam X ^ (-(1 / 9 : ℝ))) ≤ C * diam X * K * (2 * w) := by
    have ha : C * diam X * S.card ≤ C * diam X * K :=
      mul_le_mul_of_nonneg_left hScard (by positivity)
    calc _ ≤ C * diam X * K * (w + diam X ^ (-(1 / 9 : ℝ))) :=
          mul_le_mul_of_nonneg_right ha (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h3 : C * K * (2 * w) ≤ ε := by
    have hw' : w ≤ ε / (2 * (C * K + 1)) := min_le_right _ _
    have hCK : 0 ≤ C * K := by positivity
    rw [le_div_iff₀ (by positivity)] at hw'
    nlinarith
  have h4 : C * diam X * K * (2 * w) ≤ ε * diam X := by
    have := mul_le_mul_of_nonneg_right h3 hD
    linarith [show C * diam X * K * (2 * w) = C * K * (2 * w) * diam X by ring]
  linarith

end Erdos99

end

end PinnedCount

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `QuadraticResponseH1`
-/

section QuadraticResponseH1

/-!
# WP9 (continued): the H–H polynomial, its coefficients, and the `J`-receiver asymptotics

This file completes WP9 of `TRACK_COUNT_REVISED_PLAN.md` (Verification Guide §§12.3, 13.1).

* `hhPoly k l Z W`: the H–H expression (H1) multiplied by `ζ³`, as a polynomial in `ζ`;
  `hhPoly_eval` identifies its values on the unit circle and `hhPoly_eval_eq_zero` shows that the
  geometric configuration of §13.1 is a root.
* Coefficient checks: `hhPoly_coeff_six` (the degree-3 coefficient
  `k l (k + l) conj Z conj W (conj Z + conj W)`), `hhPoly_coeff_five_of_Z_eq_zero`,
  `hhPoly_coeff_five_of_W_eq_zero`, `hhPoly_zero_zero`, and the exceptional case
  `hhPoly_one_one_neg`.
* The case analysis for `W = -Z`: `opposite_quadratic_vanishes_iff`, and the final pinning statement
  `hhPoly_eq_zero_iff`: for `k, l ∈ {1, 2}` the polynomial vanishes identically exactly when
  `W = -Z`, `k = l = 1` and `|Z| = 1`; `four_ports_projection` treats that exceptional case.
* `quadratic_root_dichotomy`: the two-branch root asymptotics of a response quadratic along any
  filter, and `J_limit_large`, `J_limit_bounded`, `J_limit_Z_zero`: the limits of the `J`-receiver
  coefficients `a_J / T` and `a_J⋆` along each branch of the `H` response.
-/

open Filter Topology Polynomial ComplexConjugate

@[expose] public section

namespace Erdos99

namespace QuadraticResponse

/-! ## The H–H polynomial (H1) -/

/-- The H–H expression (H1) times `ζ³`, as a polynomial in `ζ`: with `A = k ζ + Z`,
`A⋆ = k + conj Z ζ` (`= ζ a⋆`), `B = l ζ + W`, `B⋆ = l + conj W ζ`, it is
`A A⋆ B B⋆ (A + B)(A⋆ + B⋆) + ζ (A B⋆ - A⋆ B)²`. -/
noncomputable def hhPoly (k l : ℝ) (Z W : ℂ) : ℂ[X] :=
  (C (k : ℂ) * X + C Z) * (C (k : ℂ) + C (conj Z) * X) *
      ((C (l : ℂ) * X + C W) * (C (l : ℂ) + C (conj W) * X)) *
      (((C (k : ℂ) * X + C Z) + (C (l : ℂ) * X + C W)) *
        ((C (k : ℂ) + C (conj Z) * X) + (C (l : ℂ) + C (conj W) * X))) +
    X * ((C (k : ℂ) * X + C Z) * (C (l : ℂ) + C (conj W) * X) -
      (C (k : ℂ) + C (conj Z) * X) * (C (l : ℂ) * X + C W)) ^ 2

/-- On the unit circle, `hhPoly` evaluates to `ζ³` times the (H1) expression with
`a⋆ = k/ζ + conj Z`, `b⋆ = l/ζ + conj W`. -/
theorem hhPoly_eval {ζ : ℂ} (hζ : ‖ζ‖ = 1) (k l : ℝ) (Z W : ℂ) :
    (hhPoly k l Z W).eval ζ = ζ ^ 3 *
      (((k : ℂ) * ζ + Z) * ((k : ℂ) / ζ + conj Z) * (((l : ℂ) * ζ + W) * ((l : ℂ) / ζ + conj W)) *
        ((((k : ℂ) * ζ + Z) + ((l : ℂ) * ζ + W)) * (((k : ℂ) / ζ + conj Z) +
          ((l : ℂ) / ζ + conj W))) +
      (((k : ℂ) * ζ + Z) * ((l : ℂ) / ζ + conj W) - ((k : ℂ) / ζ + conj Z) *
        ((l : ℂ) * ζ + W)) ^ 2) := by
  have hζ0 := ne_zero_of_norm_eq_one hζ
  simp only [hhPoly, eval_add, eval_mul, eval_C, eval_X, eval_pow, eval_sub]
  field_simp

/-- **(H1) as a necessary polynomial equation.** If the three unit circles centred at `0`,
`-(k ζ + Z)` and `l ζ + W` pass through a common point, then `ζ` is a root of `hhPoly k l Z W`. -/
theorem hhPoly_eval_eq_zero {ζ Z W w : ℂ} (k l : ℝ) (hζ : ‖ζ‖ = 1) (hw : ‖w‖ = 1)
    (ha : ‖w + ((k : ℂ) * ζ + Z)‖ = 1) (hb : ‖w - ((l : ℂ) * ζ + W)‖ = 1) :
    (hhPoly k l Z W).eval ζ = 0 := by
  rw [hhPoly_eval hζ, hh_identity_star k l hζ hw ha hb, mul_zero]

/-- Coefficient of `ζ ^ 0` in `hhPoly` (`K, L, Zc, Wc` stand for `k, l, conj Z, conj W`). -/
def hhCoeff0 (K L Z W : ℂ) : ℂ :=
  K * L ^ 2 * Z * W ^ 2 + K * L ^ 2 * Z ^ 2 * W + K ^ 2 * L * Z * W ^ 2 + K ^ 2 * L * Z ^ 2 * W

/-- Coefficient of `ζ ^ 1` in `hhPoly` (`K, L, Zc, Wc` stand for `k, l, conj Z, conj W`). -/
def hhCoeff1 (K L Z Zc W Wc : ℂ) : ℂ :=
  L ^ 2 * Z * Zc * W ^ 2 + L ^ 2 * Z ^ 2 + L ^ 2 * Z ^ 2 * Zc * W - 2 * K * L * Z * W + 2 * K * L
    * Z * W ^ 2 * Wc + 2 * K * L * Z * Zc * W ^ 2 + 2 * K * L * Z ^ 2 * W * Wc + 2 * K * L * Z ^ 2
    * Zc * W + 2 * K * L ^ 3 * Z * W + K * L ^ 3 * Z ^ 2 + K ^ 2 * W ^ 2 + K ^ 2 * Z * W ^ 2 * Wc
    + K ^ 2 * Z ^ 2 * W * Wc + K ^ 2 * L ^ 2 * W ^ 2 + 4 * K ^ 2 * L ^ 2 * Z * W + K ^ 2 * L ^ 2 *
    Z ^ 2 + K ^ 3 * L * W ^ 2 + 2 * K ^ 3 * L * Z * W

/-- Coefficient of `ζ ^ 2` in `hhPoly` (`K, L, Zc, Wc` stand for `k, l, conj Z, conj W`). -/
def hhCoeff2 (K L Z Zc W Wc : ℂ) : ℂ :=
  -2 * L * Z * Zc * W + 2 * L * Z * Zc * W ^ 2 * Wc + L * Z * Zc ^ 2 * W ^ 2 + 2 * L * Z ^ 2 * Wc
    + 2 * L * Z ^ 2 * Zc * W * Wc + L * Z ^ 2 * Zc ^ 2 * W + 2 * L ^ 3 * Z * Zc * W + L ^ 3 * Z ^
    2 * Zc + 2 * K * Zc * W ^ 2 - 2 * K * Z * W * Wc + K * Z * W ^ 2 * Wc ^ 2 + 2 * K * Z * Zc * W
    ^ 2 * Wc + K * Z ^ 2 * W * Wc ^ 2 + 2 * K * Z ^ 2 * Zc * W * Wc + K * L ^ 2 * Zc * W ^ 2 + 4 *
    K * L ^ 2 * Z * W * Wc + 6 * K * L ^ 2 * Z * Zc * W + 2 * K * L ^ 2 * Z ^ 2 * Wc + 2 * K * L ^
    2 * Z ^ 2 * Zc + K * L ^ 4 * Z + 2 * K ^ 2 * L * W ^ 2 * Wc + 2 * K ^ 2 * L * Zc * W ^ 2 + 6 *
    K ^ 2 * L * Z * W * Wc + 4 * K ^ 2 * L * Z * Zc * W + K ^ 2 * L * Z ^ 2 * Wc + 2 * K ^ 2 * L ^
    3 * W + 3 * K ^ 2 * L ^ 3 * Z + K ^ 3 * W ^ 2 * Wc + 2 * K ^ 3 * Z * W * Wc + 3 * K ^ 3 * L ^
    2 * W + 2 * K ^ 3 * L ^ 2 * Z + K ^ 4 * L * W

/-- Coefficient of `ζ ^ 3` in `hhPoly` (`K, L, Zc, Wc` stand for `k, l, conj Z, conj W`). -/
def hhCoeff3 (K L Z Zc W Wc : ℂ) : ℂ :=
  Zc ^ 2 * W ^ 2 - 2 * Z * Zc * W * Wc + Z * Zc * W ^ 2 * Wc ^ 2 + Z * Zc ^ 2 * W ^ 2 * Wc + Z ^ 2
    * Wc ^ 2 + Z ^ 2 * Zc * W * Wc ^ 2 + Z ^ 2 * Zc ^ 2 * W * Wc - 2 * L ^ 2 * Z * Zc + 4 * L ^ 2
    * Z * Zc * W * Wc + 2 * L ^ 2 * Z * Zc ^ 2 * W + 2 * L ^ 2 * Z ^ 2 * Zc * Wc + L ^ 2 * Z ^ 2 *
    Zc ^ 2 + L ^ 4 * Z * Zc + 2 * K * L * Zc * W + 2 * K * L * Zc * W ^ 2 * Wc + K * L * Zc ^ 2 *
    W ^ 2 + 2 * K * L * Z * Wc + 2 * K * L * Z * W * Wc ^ 2 + 8 * K * L * Z * Zc * W * Wc + 2 * K
    * L * Z * Zc ^ 2 * W + K * L * Z ^ 2 * Wc ^ 2 + 2 * K * L * Z ^ 2 * Zc * Wc + 2 * K * L ^ 3 *
    Zc * W + 2 * K * L ^ 3 * Z * Wc + 4 * K * L ^ 3 * Z * Zc - 2 * K ^ 2 * W * Wc + K ^ 2 * W ^ 2
    * Wc ^ 2 + 2 * K ^ 2 * Zc * W ^ 2 * Wc + 2 * K ^ 2 * Z * W * Wc ^ 2 + 4 * K ^ 2 * Z * Zc * W *
    Wc + 4 * K ^ 2 * L ^ 2 * W * Wc + 5 * K ^ 2 * L ^ 2 * Zc * W + 5 * K ^ 2 * L ^ 2 * Z * Wc + 4
    * K ^ 2 * L ^ 2 * Z * Zc + K ^ 2 * L ^ 4 + 4 * K ^ 3 * L * W * Wc + 2 * K ^ 3 * L * Zc * W + 2
    * K ^ 3 * L * Z * Wc + 2 * K ^ 3 * L ^ 3 + K ^ 4 * W * Wc + K ^ 4 * L ^ 2

/-- Coefficient of `ζ ^ 4` in `hhPoly` (`K, L, Zc, Wc` stand for `k, l, conj Z, conj W`). -/
def hhCoeff4 (K L Z Zc W Wc : ℂ) : ℂ :=
  2 * L * Zc ^ 2 * W - 2 * L * Z * Zc * Wc + 2 * L * Z * Zc * W * Wc ^ 2 + 2 * L * Z * Zc ^ 2 * W
    * Wc + L * Z ^ 2 * Zc * Wc ^ 2 + L * Z ^ 2 * Zc ^ 2 * Wc + 2 * L ^ 3 * Z * Zc * Wc + L ^ 3 * Z
    * Zc ^ 2 - 2 * K * Zc * W * Wc + K * Zc * W ^ 2 * Wc ^ 2 + K * Zc ^ 2 * W ^ 2 * Wc + 2 * K * Z
    * Wc ^ 2 + 2 * K * Z * Zc * W * Wc ^ 2 + 2 * K * Z * Zc ^ 2 * W * Wc + 4 * K * L ^ 2 * Zc * W
    * Wc + 2 * K * L ^ 2 * Zc ^ 2 * W + K * L ^ 2 * Z * Wc ^ 2 + 6 * K * L ^ 2 * Z * Zc * Wc + 2 *
    K * L ^ 2 * Z * Zc ^ 2 + K * L ^ 4 * Zc + 2 * K ^ 2 * L * W * Wc ^ 2 + 6 * K ^ 2 * L * Zc * W
    * Wc + K ^ 2 * L * Zc ^ 2 * W + 2 * K ^ 2 * L * Z * Wc ^ 2 + 4 * K ^ 2 * L * Z * Zc * Wc + 2 *
    K ^ 2 * L ^ 3 * Wc + 3 * K ^ 2 * L ^ 3 * Zc + K ^ 3 * W * Wc ^ 2 + 2 * K ^ 3 * Zc * W * Wc + 3
    * K ^ 3 * L ^ 2 * Wc + 2 * K ^ 3 * L ^ 2 * Zc + K ^ 4 * L * Wc

/-- Coefficient of `ζ ^ 5` in `hhPoly` (`K, L, Zc, Wc` stand for `k, l, conj Z, conj W`). -/
def hhCoeff5 (K L Z Zc W Wc : ℂ) : ℂ :=
  L ^ 2 * Zc ^ 2 + L ^ 2 * Z * Zc * Wc ^ 2 + L ^ 2 * Z * Zc ^ 2 * Wc - 2 * K * L * Zc * Wc + 2 * K
    * L * Zc * W * Wc ^ 2 + 2 * K * L * Zc ^ 2 * W * Wc + 2 * K * L * Z * Zc * Wc ^ 2 + 2 * K * L
    * Z * Zc ^ 2 * Wc + 2 * K * L ^ 3 * Zc * Wc + K * L ^ 3 * Zc ^ 2 + K ^ 2 * Wc ^ 2 + K ^ 2 * Zc
    * W * Wc ^ 2 + K ^ 2 * Zc ^ 2 * W * Wc + K ^ 2 * L ^ 2 * Wc ^ 2 + 4 * K ^ 2 * L ^ 2 * Zc * Wc
    + K ^ 2 * L ^ 2 * Zc ^ 2 + K ^ 3 * L * Wc ^ 2 + 2 * K ^ 3 * L * Zc * Wc

/-- Coefficient of `ζ ^ 6` in `hhPoly` (`K, L, Zc, Wc` stand for `k, l, conj Z, conj W`). -/
def hhCoeff6 (K L Zc Wc : ℂ) : ℂ :=
  K * L ^ 2 * Zc * Wc ^ 2 + K * L ^ 2 * Zc ^ 2 * Wc + K ^ 2 * L * Zc * Wc ^ 2 + K ^ 2 * L * Zc ^ 2
    * Wc

/-- The explicit expansion of `hhPoly` (used for the coefficient checks). -/
theorem hhPoly_eq (k l : ℝ) (Z W : ℂ) : hhPoly k l Z W =
    C (hhCoeff6 k l (conj Z) (conj W)) * X ^ 6 + C (hhCoeff5 k l Z (conj Z) W (conj W)) * X ^ 5 +
      C (hhCoeff4 k l Z (conj Z) W (conj W)) * X ^ 4 +
      C (hhCoeff3 k l Z (conj Z) W (conj W)) * X ^ 3 +
      C (hhCoeff2 k l Z (conj Z) W (conj W)) * X ^ 2 +
      C (hhCoeff1 k l Z (conj Z) W (conj W)) * X ^ 1 +
      C (hhCoeff0 k l Z W) * X ^ 0 := by
  simp only [hhPoly, hhCoeff0, hhCoeff1, hhCoeff2, hhCoeff3, hhCoeff4, hhCoeff5, hhCoeff6, map_add,
    map_mul, map_sub, map_pow, map_neg, map_ofNat]
  ring

/-! ## Coefficient checks (Verification Guide §13.1) -/

/-- The top coefficient (degree `3` in `ζ` for the Laurent expression (H1)):
`k l (k + l) conj Z conj W (conj Z + conj W)`. -/
theorem hhPoly_coeff_six (k l : ℝ) (Z W : ℂ) :
    (hhPoly k l Z W).coeff 6 = (k : ℂ) * l * (k + l) * conj Z * conj W * (conj Z + conj W) := by
  rw [hhPoly_eq]
  simp only [coeff_add, coeff_C_mul, coeff_X_pow]
  norm_num [hhCoeff6]
  ring

/-- If `Z = 0`, the next coefficient is `k² (l (k + l) + 1) (conj W)²`. -/
theorem hhPoly_coeff_five_of_Z_eq_zero (k l : ℝ) (W : ℂ) :
    (hhPoly k l 0 W).coeff 5 = (k : ℂ) ^ 2 * (l * (k + l) + 1) * conj W ^ 2 := by
  rw [hhPoly_eq]
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, map_zero]
  norm_num [hhCoeff5]
  ring

/-- If `W = 0`, the next coefficient is `l² (k (k + l) + 1) (conj Z)²` (the symmetric case). -/
theorem hhPoly_coeff_five_of_W_eq_zero (k l : ℝ) (Z : ℂ) :
    (hhPoly k l Z 0).coeff 5 = (l : ℂ) ^ 2 * (k * (k + l) + 1) * conj Z ^ 2 := by
  rw [hhPoly_eq]
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, map_zero]
  norm_num [hhCoeff5]
  ring

/-- If `Z = W = 0`, the (H1) expression is the constant `k² l² (k + l)²`. -/
theorem hhPoly_zero_zero (k l : ℝ) :
    hhPoly k l 0 0 = C ((k : ℂ) ^ 2 * l ^ 2 * (k + l) ^ 2) * X ^ 3 := by
  simp only [hhPoly, map_zero, map_mul, map_pow, map_add]
  ring

/-- The exceptional case `k = l = 1`, `W = -Z`: `hhPoly = 4 (1 - |Z|²)² ζ³`. -/
theorem hhPoly_one_one_neg (Z : ℂ) :
    hhPoly 1 1 Z (-Z) = C (4 * (1 - Z * conj Z) ^ 2) * X ^ 3 := by
  simp only [hhPoly, map_neg, Complex.ofReal_one, map_one, map_mul, map_pow, map_sub,
    map_ofNat]
  ring

/-- The quadratic of the case `W = -Z` (after division by `(k + l)²`), as a function of
`x = Re (ζ conj Z)`, with `r = |Z|`. -/
def oppQuad (k l r x : ℝ) : ℝ :=
  (k ^ 2 + r ^ 2) * (l ^ 2 + r ^ 2) - 4 * r ^ 2 + 2 * (k * (l ^ 2 + r ^ 2) - l * (k ^ 2 + r ^ 2)) * x +
    4 * (1 - k * l) * x ^ 2

/-- For `W = -Z` and `ζ` on the unit circle, `hhPoly` evaluates to `ζ³ (k + l)² q(x)`. -/
theorem hhPoly_neg_eval {ζ : ℂ} (hζ : ‖ζ‖ = 1) (k l : ℝ) (Z : ℂ) :
    (hhPoly k l Z (-Z)).eval ζ =
      ζ ^ 3 * (((k + l) ^ 2 * oppQuad k l ‖Z‖ (ζ * conj Z).re : ℝ) : ℂ) := by
  have hζ0 := ne_zero_of_norm_eq_one hζ
  have hx : (((ζ * conj Z).re : ℝ) : ℂ) = (ζ * conj Z + ζ⁻¹ * Z) / 2 := by
    rw [Complex.re_eq_add_conj, map_mul, Complex.conj_conj, conj_eq_inv hζ]
  have hr : ((‖Z‖ : ℝ) : ℂ) ^ 2 = Z * conj Z := by
    rw [← Complex.ofReal_pow]; exact norm_sq_eq_mul_conj Z
  rw [hhPoly_eval hζ, oppQuad]
  simp only [map_neg]
  push_cast
  rw [hx, hr]
  field_simp
  ring

/-- The case analysis behind §13.1 for `W = -Z`: for `k, l ∈ {1, 2}` and `r > 0`, if the quadratic
vanishes at `x = 0, r, -r` then `k = l = 1` and `r = 1`. -/
theorem oppQuad_three_points {k l r : ℝ} (hk : k = 1 ∨ k = 2) (hl : l = 1 ∨ l = 2) (hr : 0 < r)
    (h0 : oppQuad k l r 0 = 0) (h1 : oppQuad k l r r = 0) (h2 : oppQuad k l r (-r) = 0) :
    k = 1 ∧ l = 1 ∧ r = 1 := by
  unfold oppQuad at h0 h1 h2
  have hc2 : 4 * (1 - k * l) * r ^ 2 = 0 := by linear_combination (h1 + h2 - 2 * h0) / 2
  have hkl : k * l = 1 := by
    have : r ^ 2 ≠ 0 := by positivity
    have := (mul_eq_zero.1 hc2).resolve_right this
    linarith
  have hk1 : k = 1 ∧ l = 1 := by
    rcases hk with rfl | rfl <;> rcases hl with rfl | rfl <;> first | exact ⟨rfl, rfl⟩ | norm_num at hkl
  obtain ⟨rfl, rfl⟩ := hk1
  refine ⟨rfl, rfl, ?_⟩
  have : (r ^ 2 - 1) ^ 2 = 0 := by linear_combination h0
  have h3 : r ^ 2 = 1 := by nlinarith [sq_nonneg (r ^ 2 - 1), pow_eq_zero_iff (n := 2) (a := r ^ 2 - 1) two_ne_zero |>.1 this]
  nlinarith

/-- For `k, l ∈ {1, 2}` and `r > 0`, the `W = -Z` quadratic vanishes on the whole range
`x ∈ [-r, r]` of `Re (ζ conj Z)` exactly when `k = l = 1` and `r = 1`. -/
theorem oppQuad_vanishes_iff {k l r : ℝ} (hk : k = 1 ∨ k = 2) (hl : l = 1 ∨ l = 2) (hr : 0 < r) :
    (∀ x ∈ Set.Icc (-r) r, oppQuad k l r x = 0) ↔ k = 1 ∧ l = 1 ∧ r = 1 := by
  constructor
  · intro h
    exact oppQuad_three_points hk hl hr (h 0 ⟨by linarith, hr.le⟩) (h r ⟨by linarith, le_rfl⟩)
      (h (-r) ⟨le_rfl, by linarith⟩)
  · rintro ⟨rfl, rfl, rfl⟩ x _
    unfold oppQuad; ring

/-- `(Z / |Z|) conj Z = |Z|`. -/
lemma div_norm_mul_conj {Z : ℂ} (hZ : Z ≠ 0) : (Z / (‖Z‖ : ℂ)) * conj Z = ((‖Z‖ : ℝ) : ℂ) := by
  have hr : (‖Z‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 hZ).ne'
  rw [div_mul_eq_mul_div, ← norm_sq_eq_mul_conj]
  push_cast
  field_simp

lemma norm_unit_of_ne_zero {Z : ℂ} (hZ : Z ≠ 0) : ‖Z / (‖Z‖ : ℂ)‖ = 1 := by
  have hr : 0 < ‖Z‖ := norm_pos_iff.2 hZ
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le, div_self hr.ne']

/-- **The pinning statement for H–H adjacency** (Verification Guide §13.1). For `k, l ∈ {1, 2}`,
the polynomial `hhPoly k l Z W` is identically zero exactly in the exceptional case
`W = -Z`, `k = l = 1`, `|Z| = 1`. In every other case it is a nonzero polynomial of degree at
most `6`, so (H1) pins `ζ` to at most six directions. -/
theorem hhPoly_eq_zero_iff {k l : ℝ} (hk : k = 1 ∨ k = 2) (hl : l = 1 ∨ l = 2) (Z W : ℂ) :
    hhPoly k l Z W = 0 ↔ W = -Z ∧ k = 1 ∧ l = 1 ∧ ‖Z‖ = 1 := by
  have hk0 : 0 < k := by rcases hk with rfl | rfl <;> norm_num
  have hl0 : 0 < l := by rcases hl with rfl | rfl <;> norm_num
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk0.ne'
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl0.ne'
  have hkl' : (k : ℂ) + l ≠ 0 := by exact_mod_cast (add_pos hk0 hl0).ne'
  constructor
  · intro h
    by_cases hZ : Z = 0 <;> by_cases hW : W = 0
    · subst hZ hW
      have h3 := congrArg (fun p => coeff p 3) h
      simp only [hhPoly_zero_zero, coeff_C_mul, coeff_X_pow, if_true, mul_one, coeff_zero] at h3
      exact absurd h3 (by simp [hk', hl', hkl'])
    · subst hZ
      have h5 := congrArg (fun p => coeff p 5) h
      simp only [hhPoly_coeff_five_of_Z_eq_zero, coeff_zero] at h5
      have h1 : (l : ℂ) * (k + l) + 1 ≠ 0 := by
        exact_mod_cast (show l * (k + l) + 1 ≠ 0 by positivity)
      exact absurd h5 (by simp [hk', h1, hW])
    · subst hW
      have h5 := congrArg (fun p => coeff p 5) h
      simp only [hhPoly_coeff_five_of_W_eq_zero, coeff_zero] at h5
      have h1 : (k : ℂ) * (k + l) + 1 ≠ 0 := by
        exact_mod_cast (show k * (k + l) + 1 ≠ 0 by positivity)
      exact absurd h5 (by simp [hl', h1, hZ])
    · by_cases hZW : W = -Z
      · subst hZW
        refine ⟨rfl, ?_⟩
        have hr : 0 < ‖Z‖ := norm_pos_iff.2 hZ
        have key : ∀ ζ : ℂ, ‖ζ‖ = 1 → oppQuad k l ‖Z‖ (ζ * conj Z).re = 0 := by
          intro ζ hζ
          have e := hhPoly_neg_eval hζ k l Z
          rw [h, eval_zero] at e
          have hζ3 : ζ ^ 3 ≠ 0 := pow_ne_zero _ (ne_zero_of_norm_eq_one hζ)
          have e2 : (((k + l) ^ 2 * oppQuad k l ‖Z‖ (ζ * conj Z).re : ℝ) : ℂ) = 0 :=
            (mul_eq_zero.1 e.symm).resolve_left hζ3
          have e3 : (k + l) ^ 2 * oppQuad k l ‖Z‖ (ζ * conj Z).re = 0 := by exact_mod_cast e2
          exact (mul_eq_zero.1 e3).resolve_left (by positivity)
        set u := Z / (‖Z‖ : ℂ)
        have hu : ‖u‖ = 1 := norm_unit_of_ne_zero hZ
        have hval : u * conj Z = ((‖Z‖ : ℝ) : ℂ) := div_norm_mul_conj hZ
        have k1 := key u hu
        have k2 := key (-u) (by rw [norm_neg, hu])
        have k3 := key (Complex.I * u) (by rw [norm_mul, Complex.norm_I, hu, one_mul])
        rw [hval, Complex.ofReal_re] at k1
        rw [neg_mul, hval, Complex.neg_re, Complex.ofReal_re] at k2
        rw [mul_assoc, hval, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
          Complex.ofReal_im] at k3
        norm_num at k3
        exact oppQuad_three_points hk hl hr k3 k1 k2
      · exfalso
        have h6 := congrArg (fun p => coeff p 6) h
        simp only [hhPoly_coeff_six, coeff_zero] at h6
        have hZc : conj Z ≠ 0 := by rwa [_root_.map_ne_zero]
        have hWc : conj W ≠ 0 := by rwa [_root_.map_ne_zero]
        have hs : conj Z + conj W ≠ 0 := by
          rw [← map_add, _root_.map_ne_zero]
          intro hs; exact hZW (by linear_combination hs)
        exact absurd h6 (by simp [hk', hl', hkl', hZc, hWc, hs])
  · rintro ⟨rfl, rfl, rfl, hZ⟩
    rw [hhPoly_one_one_neg, mul_conj_eq_one hZ]
    simp

/-- `hhPoly` has degree at most `6`. -/
theorem hhPoly_natDegree_le (k l : ℝ) (Z W : ℂ) : (hhPoly k l Z W).natDegree ≤ 6 := by
  rw [hhPoly_eq]
  compute_degree

/-- **Direction pinning from (H1).** Outside the exceptional case, the unit tangents `ζ`
compatible with an H–H adjacency (`hhPoly_eval_eq_zero`) form a set of at most six points. -/
theorem hh_directions_card_le {k l : ℝ} (hk : k = 1 ∨ k = 2) (hl : l = 1 ∨ l = 2) {Z W : ℂ}
    (hexc : ¬ (W = -Z ∧ k = 1 ∧ l = 1 ∧ ‖Z‖ = 1)) :
    ∃ S : Finset ℂ, S.card ≤ 6 ∧ ∀ ζ w : ℂ, ‖ζ‖ = 1 → ‖w‖ = 1 → ‖w + ((k : ℂ) * ζ + Z)‖ = 1 →
      ‖w - ((l : ℂ) * ζ + W)‖ = 1 → ζ ∈ S := by
  have hne : hhPoly k l Z W ≠ 0 := fun h => hexc ((hhPoly_eq_zero_iff hk hl Z W).1 h)
  refine ⟨(hhPoly k l Z W).roots.toFinset, ?_, ?_⟩
  · exact (Multiset.toFinset_card_le _).trans
      ((card_roots' _).trans (hhPoly_natDegree_le k l Z W))
  · intro ζ w hζ hw ha hb
    rw [Multiset.mem_toFinset, mem_roots hne, IsRoot.def]
    exact hhPoly_eval_eq_zero k l hζ hw ha hb

/-- **The exceptional H–H configuration** (Verification Guide §13.1). If two unit vectors `p, q`
have `|p + q| = 1` (two retained ports with retained sum of norm one), then for every unit tangent
`τ` one of the four vectors `±p, ±q` has projection at least `1/2` on `τ`: the four ports have
successive angular gaps `60°` and `120°`, contradicting the macroscopic-port margin. -/
theorem four_ports_projection {p q τ : ℂ} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hτ : ‖τ‖ = 1)
    (hpq : ‖p + q‖ = 1) :
    1 / 2 ≤ |(p * conj τ).re| ∨ 1 / 2 ≤ |(q * conj τ).re| := by
  set a := p * conj τ
  set b := q * conj τ
  have hτ' : ‖conj τ‖ = 1 := by rw [Complex.norm_conj, hτ]
  have ha : ‖a‖ = 1 := by rw [norm_mul, hp, hτ', one_mul]
  have hb : ‖b‖ = 1 := by rw [norm_mul, hq, hτ', one_mul]
  have hab : ‖a + b‖ = 1 := by rw [← add_mul, norm_mul, hpq, hτ', one_mul]
  have na : a.re ^ 2 + a.im ^ 2 = 1 := by
    have := Complex.sq_norm a; rw [ha, Complex.normSq_apply] at this; nlinarith
  have nb : b.re ^ 2 + b.im ^ 2 = 1 := by
    have := Complex.sq_norm b; rw [hb, Complex.normSq_apply] at this; nlinarith
  have nab : (a.re + b.re) ^ 2 + (a.im + b.im) ^ 2 = 1 := by
    have := Complex.sq_norm (a + b)
    rw [hab, Complex.normSq_apply, Complex.add_re, Complex.add_im] at this; nlinarith
  -- the frame identity `x² + y² + x y = 3/4`
  have hdot : a.re * b.re + a.im * b.im = -1 / 2 := by nlinarith
  have hframe : a.re ^ 2 + b.re ^ 2 + a.re * b.re = 3 / 4 := by
    have h1 : (a.re * b.re + 1 / 2) ^ 2 = (1 - a.re ^ 2) * (1 - b.re ^ 2) := by
      have : a.re * b.re + 1 / 2 = -(a.im * b.im) := by linarith
      rw [this, neg_sq, mul_pow]
      rw [show a.im ^ 2 = 1 - a.re ^ 2 by linarith, show b.im ^ 2 = 1 - b.re ^ 2 by linarith]
    nlinarith
  by_contra h
  push_neg at h
  obtain ⟨h1, h2⟩ := h
  have h1' := abs_lt.1 h1
  have h2' := abs_lt.1 h2
  nlinarith [mul_self_nonneg (a.re + b.re), mul_self_nonneg (a.re - b.re)]

/-! ## Two-stage asymptotics at a `J` receiver (Verification Guide §12.3) -/

/-- **Root dichotomy for a response quadratic along any filter.** Let `T → ∞` along `F`, and let
`a, a⋆` be coefficients with `a / T → A ≠ 0` and `a⋆ → B ≠ 0`. If `w` solves
`a⋆ w² - a a⋆ w + a = 0`, then for every `ε > 0`, eventually either `w / T` is `ε`-close to `A`
or `w` is `ε`-close to `1 / B`. (Taking `F` to be the filter of a subsequence gives the
subsequence form of the Guide.) -/
theorem quadratic_root_dichotomy {ι : Type*} {F : Filter ι} {T : ι → ℝ} (hT : Tendsto T F atTop)
    {a aS w : ι → ℂ} {A B : ℂ} (hA : A ≠ 0) (hB : B ≠ 0)
    (ha : Tendsto (fun i => a i / T i) F (𝓝 A)) (haS : Tendsto aS F (𝓝 B))
    (hw : ∀ᶠ i in F, aS i * w i ^ 2 - a i * aS i * w i + a i = 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in F, ‖w i / T i - A‖ < ε ∨ ‖w i - B⁻¹‖ < ε := by
  set c := ‖B‖ with hc
  set α := ‖A‖ with hα
  have hc0 : 0 < c := norm_pos_iff.2 hB
  have hα0 : 0 < α := norm_pos_iff.2 hA
  set M := 4 / c with hM
  have hM0 : 0 < M := by positivity
  have h1 := Metric.tendsto_nhds.1 haS (c / 2) (by positivity)
  have h2 := Metric.tendsto_nhds.1 ha (min (ε / 2) (α / 2)) (by positivity)
  have h3 := Metric.tendsto_nhds.1 (haS.inv₀ hB) (ε / 2) (by positivity)
  have h4 := hT.eventually (eventually_gt_atTop
    (max (max 0 (4 * M / α)) (max (16 * M / (α * c * ε)) (8 / (c * ε)))))
  filter_upwards [hw, h1, h2, h3, h4] with i hq hi1 hi2 hi3 hi4
  simp only [max_lt_iff] at hi4
  obtain ⟨⟨hT0, hT1⟩, hT2, hT3⟩ := hi4
  rw [dist_eq_norm] at hi1 hi2 hi3
  have hTc : ‖((T i : ℝ) : ℂ)‖ = T i := by rw [Complex.norm_real, Real.norm_of_nonneg hT0.le]
  have hT0' : ((T i : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hT0.ne'
  have haS : c / 2 ≤ ‖aS i‖ := by
    have := norm_sub_norm_le B (B - aS i)
    rw [sub_sub_cancel, norm_sub_rev] at this
    linarith
  have haS0 : aS i ≠ 0 := norm_pos_iff.1 (by linarith)
  have hmin1 : min (ε / 2) (α / 2) ≤ ε / 2 := min_le_left _ _
  have hmin2 : min (ε / 2) (α / 2) ≤ α / 2 := min_le_right _ _
  have haT : α * T i / 2 ≤ ‖a i‖ := by
    have e1 := norm_sub_norm_le A (A - a i / T i)
    rw [sub_sub_cancel, norm_sub_rev] at e1
    have e2 : ‖a i / T i‖ = ‖a i‖ / T i := by rw [norm_div, hTc]
    rw [e2] at e1
    have : α / 2 ≤ ‖a i‖ / T i := by linarith
    rw [le_div_iff₀ hT0] at this
    linarith
  have hfac : (w i - a i) * (aS i * w i - 1) = -w i := response_factor hq
  have hnorm : ‖w i - a i‖ * ‖aS i * w i - 1‖ = ‖w i‖ := by
    rw [← norm_mul, hfac, norm_neg]
  by_cases hwM : ‖w i‖ ≤ M
  · right
    have hwa : α * T i / 4 ≤ ‖w i - a i‖ := by
      have := norm_sub_norm_le (a i) (w i)
      rw [norm_sub_rev] at this
      have : 4 * M / α * α = 4 * M := by field_simp
      nlinarith
    have hwa0 : 0 < ‖w i - a i‖ := lt_of_lt_of_le (by positivity) hwa
    have hb1 : ‖aS i * w i - 1‖ ≤ 4 * M / (α * T i) := by
      rw [le_div_iff₀ (by positivity)]
      have : ‖aS i * w i - 1‖ * (α * T i / 4) ≤ ‖aS i * w i - 1‖ * ‖w i - a i‖ :=
        mul_le_mul_of_nonneg_left hwa (norm_nonneg _)
      nlinarith
    have hb2 : ‖w i - (aS i)⁻¹‖ ≤ 8 * M / (α * c * T i) := by
      have e : w i - (aS i)⁻¹ = (aS i * w i - 1) / aS i := by field_simp
      rw [e, norm_div, div_le_iff₀ (by linarith)]
      calc ‖aS i * w i - 1‖ ≤ 4 * M / (α * T i) := hb1
        _ = 8 * M / (α * c * T i) * (c / 2) := by field_simp; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left haS (by positivity)
    have hb3 : 8 * M / (α * c * T i) < ε / 2 := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ (by positivity)] at hT2
      nlinarith
    calc ‖w i - B⁻¹‖ = ‖(w i - (aS i)⁻¹) + ((aS i)⁻¹ - B⁻¹)‖ := by congr 1; ring
      _ ≤ ‖w i - (aS i)⁻¹‖ + ‖(aS i)⁻¹ - B⁻¹‖ := norm_add_le _ _
      _ < ε := by linarith
  · left
    push_neg at hwM
    have hw0 : 0 < ‖w i‖ := lt_trans hM0 hwM
    have hcw : 1 ≤ c / 4 * ‖w i‖ := by
      have : c / 4 * M = 1 := by rw [hM]; field_simp
      nlinarith
    have hlow : c / 4 * ‖w i‖ ≤ ‖aS i * w i - 1‖ := by
      have := norm_sub_norm_le (aS i * w i) 1
      rw [norm_mul, norm_one] at this
      nlinarith [mul_le_mul_of_nonneg_right haS (norm_nonneg (w i))]
    have hwa : ‖w i - a i‖ ≤ 4 / c := by
      have : ‖w i - a i‖ * (c / 4 * ‖w i‖) ≤ ‖w i‖ :=
        calc ‖w i - a i‖ * (c / 4 * ‖w i‖) ≤ ‖w i - a i‖ * ‖aS i * w i - 1‖ :=
              mul_le_mul_of_nonneg_left hlow (norm_nonneg _)
          _ = ‖w i‖ := hnorm
      rw [le_div_iff₀ hc0]
      nlinarith
    have e : w i / T i - A = (w i - a i) / T i + (a i / T i - A) := by field_simp; ring
    rw [e]
    calc ‖(w i - a i) / T i + (a i / T i - A)‖ ≤ ‖(w i - a i) / T i‖ + ‖a i / T i - A‖ :=
          norm_add_le _ _
      _ < ε := by
        rw [norm_div, hTc]
        have : ‖w i - a i‖ / T i < ε / 2 := by
          rw [div_lt_iff₀ hT0]
          rw [div_lt_iff₀ (by positivity)] at hT3
          have : 4 / c * c = 4 := by field_simp
          nlinarith
        linarith

/-- `(T : ℂ)⁻¹ → 0` as `T → ∞`. -/
lemma tendsto_inv_ofReal {ι : Type*} {F : Filter ι} {T : ι → ℝ} (hT : Tendsto T F atTop) :
    Tendsto (fun i => ((T i : ℝ) : ℂ)⁻¹) F (𝓝 0) := by
  have h := (tendsto_inv_atTop_zero.comp hT)
  have h2 := (Complex.continuous_ofReal.tendsto 0).comp h
  simpa [Function.comp_def] using h2

/-- The `J` coefficients in normalised form: `(l T + v + z) / T = l + v / T + z / T`. -/
lemma J_coeff_div {T : ℝ} (hT : T ≠ 0) (l : ℝ) (v z : ℂ) :
    ((l : ℂ) * T + v + z) / T = l + v * ((T : ℂ))⁻¹ + z / T := by
  have : (T : ℂ) ≠ 0 := by exact_mod_cast hT
  field_simp

/-- **`J` receiver, large branch of the `H` response** (`z / T → k`, `1 / z → 0`):
`a_J / T → l + k` and `a_J⋆ → conj v`. -/
theorem J_limit_large {ι : Type*} {F : Filter ι} {T : ι → ℝ} (hT : Tendsto T F atTop)
    (l : ℝ) (v : ℂ) {k : ℂ} {z : ι → ℂ} (h1 : Tendsto (fun i => z i / T i) F (𝓝 k))
    (h2 : Tendsto (fun i => (z i)⁻¹) F (𝓝 0)) :
    Tendsto (fun i => ((l : ℂ) * T i + v + z i) / T i) F (𝓝 (l + k)) ∧
      Tendsto (fun i => (l : ℂ) / T i + conj v + (z i)⁻¹) F (𝓝 (conj v)) := by
  have hinv := tendsto_inv_ofReal hT
  constructor
  · have h : Tendsto (fun i => (l : ℂ) + v * ((T i : ℝ) : ℂ)⁻¹ + z i / T i) F
        (𝓝 (l + v * 0 + k)) := (tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)).add h1
    rw [mul_zero, add_zero] at h
    refine h.congr' ?_
    filter_upwards [hT.eventually (eventually_gt_atTop 0)] with i hi
    rw [J_coeff_div hi.ne']
  · have h : Tendsto (fun i => (l : ℂ) * ((T i : ℝ) : ℂ)⁻¹ + conj v + (z i)⁻¹) F
        (𝓝 (l * 0 + conj v + 0)) := ((tendsto_const_nhds.mul hinv).add tendsto_const_nhds).add h2
    rw [mul_zero, zero_add, add_zero] at h
    simpa [div_eq_mul_inv] using h

/-- **`J` receiver, bounded branch of the `H` response** (`z → 1 / conj Z`, so `z / T → 0`):
`a_J / T → l` and `a_J⋆ → conj v + conj Z`. -/
theorem J_limit_bounded {ι : Type*} {F : Filter ι} {T : ι → ℝ} (hT : Tendsto T F atTop)
    (l : ℝ) (v : ℂ) {Z : ℂ} (hZ : Z ≠ 0) {z : ι → ℂ}
    (h : Tendsto z F (𝓝 (conj Z)⁻¹)) :
    Tendsto (fun i => ((l : ℂ) * T i + v + z i) / T i) F (𝓝 l) ∧
      Tendsto (fun i => (l : ℂ) / T i + conj v + (z i)⁻¹) F (𝓝 (conj v + conj Z)) := by
  have hinv := tendsto_inv_ofReal hT
  have hZc : (conj Z)⁻¹ ≠ 0 := inv_ne_zero (by rwa [_root_.map_ne_zero])
  constructor
  · have h' : Tendsto (fun i => (l : ℂ) + v * ((T i : ℝ) : ℂ)⁻¹ + z i * ((T i : ℝ) : ℂ)⁻¹) F
        (𝓝 (l + v * 0 + (conj Z)⁻¹ * 0)) :=
      (tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)).add (h.mul hinv)
    rw [mul_zero, mul_zero, add_zero, add_zero] at h'
    refine h'.congr' ?_
    filter_upwards [hT.eventually (eventually_gt_atTop 0)] with i hi
    rw [J_coeff_div hi.ne', div_eq_mul_inv]
  · have h' : Tendsto (fun i => (l : ℂ) * ((T i : ℝ) : ℂ)⁻¹ + conj v + (z i)⁻¹) F
        (𝓝 (l * 0 + conj v + ((conj Z)⁻¹)⁻¹)) :=
      ((tendsto_const_nhds.mul hinv).add tendsto_const_nhds).add (h.inv₀ hZc)
    rw [mul_zero, zero_add, inv_inv] at h'
    simpa [div_eq_mul_inv] using h'

/-- **`J` receiver when `Z = 0`** (`z = T d` with `d ≠ 0`): `a_J / T → l + d` and
`a_J⋆ → conj v`. -/
theorem J_limit_Z_zero {ι : Type*} {F : Filter ι} {T : ι → ℝ} (hT : Tendsto T F atTop)
    (l : ℝ) (v : ℂ) {d : ℂ} (hd : d ≠ 0) :
    Tendsto (fun i => ((l : ℂ) * T i + v + T i * d) / T i) F (𝓝 (l + d)) ∧
      Tendsto (fun i => (l : ℂ) / T i + conj v + ((T i : ℂ) * d)⁻¹) F (𝓝 (conj v)) := by
  have hinv := tendsto_inv_ofReal hT
  refine J_limit_large hT l v ?_ ?_
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [hT.eventually (eventually_gt_atTop 0)] with i hi
    have : ((T i : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hi.ne'
    field_simp
  · have h' : Tendsto (fun i => ((T i : ℝ) : ℂ)⁻¹ * d⁻¹) F (𝓝 (0 * d⁻¹)) :=
      hinv.mul tendsto_const_nhds
    rw [zero_mul] at h'
    exact h'.congr (fun i => by rw [mul_inv])

/-- **The normalised `J` response has limit `0` or `A`.** If `a_J / T → A` with `Re A > 0` and
`a_J⋆ → B ≠ 0` (Verification Guide §12.3; `B ≠ 0` comes from the three-port margin), then every
solution `w` of the `J` response quadratic eventually has `w / T` within `ε` of `A` or of `0`. -/
theorem J_response_dichotomy {ι : Type*} {F : Filter ι} {T : ι → ℝ} (hT : Tendsto T F atTop)
    {a aS w : ι → ℂ} {A B : ℂ} (hA : 0 < A.re) (hB : B ≠ 0)
    (ha : Tendsto (fun i => a i / T i) F (𝓝 A)) (haS : Tendsto aS F (𝓝 B))
    (hw : ∀ᶠ i in F, aS i * w i ^ 2 - a i * aS i * w i + a i = 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in F, ‖w i / T i - A‖ < ε ∨ ‖w i / T i‖ < ε := by
  have hA0 : A ≠ 0 := fun h => by rw [h, Complex.zero_re] at hA; exact lt_irrefl _ hA
  filter_upwards [quadratic_root_dichotomy hT hA0 hB ha haS hw (ε := min ε 1) (by positivity),
    hT.eventually (eventually_gt_atTop ((‖B⁻¹‖ + 1) / ε))] with i h hTi
  have hT0 : 0 < T i := lt_of_le_of_lt (by positivity) hTi
  rcases h with h | h
  · exact Or.inl (lt_of_lt_of_le h (min_le_left _ _))
  · right
    have hwb : ‖w i‖ < ‖B⁻¹‖ + 1 := by
      have := norm_le_insert' (w i) B⁻¹
      have := min_le_right ε 1
      linarith
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hT0.le, div_lt_iff₀ hT0]
    rw [div_lt_iff₀ hε] at hTi
    linarith

/-- A root of `d² - k d + 1 = 0` is nonzero. -/
lemma root_ne_zero {k : ℝ} {d : ℂ} (hd : d ^ 2 - k * d + 1 = 0) : d ≠ 0 := by
  rintro rfl; simp at hd

/-- In the `Z = 0` case the limit `A = l + d` of `a_J / T` has positive real part
(`Re d = k / 2` for `k ∈ {1, 2}`), as `J_response_dichotomy` requires. -/
theorem J_leading_re_pos_Z_zero {l k : ℝ} (hl : 0 < l) (hk : k = 1 ∨ k = 2) {d : ℂ}
    (hd : d ^ 2 - k * d + 1 = 0) : 0 < ((l : ℂ) + d).re := by
  have hk4 : k ^ 2 ≤ 4 := by rcases hk with rfl | rfl <;> norm_num
  have hk0 : 0 < k := by rcases hk with rfl | rfl <;> norm_num
  rw [Complex.add_re, Complex.ofReal_re, re_eq_of_root hk4 hd]
  positivity

end QuadraticResponse

end Erdos99
end

end QuadraticResponseH1

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `QuadraticResponseJ`
-/

section QuadraticResponseJ

/-!
# The algebraic cores of §§13.2–13.4 and of the loop cases

This file proves the algebraic statements behind the local exclusion calculations of Verification
Guide §§13.2–13.4 that were not yet covered by `QuadraticResponseAlgebra` and
`QuadraticResponseH1`.  As there, the large real parameter `T → ∞` stands for the normalised
direction, `a / T → A` is a leading coefficient and `a⋆ → B` a constant coefficient.

* `norm_sum_ge_of_proj_le` / `sum_ne_zero_of_proj_le`: **the quantitative margin of a constant
  coefficient** (§13.2, §13.3).  A sum of vectors whose projections on a unit tangent are all
  `≤ -θ` has norm at least `θ` times the number of summands; in particular it is nonzero.
* `J_two_H_eventually_ne_one` (§13.2): if `a / T → A ≠ 0` and `a⋆ → B ≠ 0` then the leading product
  `a a⋆ ~ A B T` is eventually not `1`, so the unit condition `a a⋆ = 1` at an unflagged `J` with
  two unflagged `H` neighbours cannot hold identically.
* `J_leading_tendsto`, `J_leading_re_pos`, `J_unit_eventually_fails` (§13.2): the leading
  coefficient `l + ∑ ξ j` of `a = l T + v + ∑ z j` has positive real part, and the unit condition
  fails eventually as soon as the constant coefficient `conj v + ∑ β j` is nonzero.
* `jj_cubic_coeff_ne_zero`, `hhExpr_div_cube_tendsto`, `jj_hhExpr_eventually_ne_zero` (§13.3):
  the cubic coefficient `A₁ A₂ (A₁ + A₂) B₁ B₂ (B₁ + B₂)` of the (H1) expression is nonzero when
  `Re Aᵢ > 0` and `B₁ B₂ (B₁ + B₂) ≠ 0`; the (H1) expression divided by `T³` tends to it (the
  squared term has order at most two), so (H1) eventually fails.
* `component_sum_eventually_ne` (§13.4): a sum of responses whose normalised limits have
  nonnegative real part is eventually not equal to `-k₀ T - Z₀` with `k₀ > 0`.
* `hLoopPoly`, `jLoopPoly` (loops in §§13.1, 13.3): an `H` loop gives `k ζ + Z = 0` and a `J` loop
  gives `|l ζ + v| = 1`; both are roots of explicit nonzero polynomials.
-/

open Filter Topology Polynomial ComplexConjugate

@[expose] public section

namespace Erdos99

namespace QuadraticResponse

/-! ## The margin of a constant coefficient -/

/-- **Quantitative margin.**  If every summand `f i` has projection `Re (f i · conj τ) ≤ -θ` on the
unit tangent `τ`, then `‖∑ f i‖ ≥ θ · |s|`. -/
theorem norm_sum_ge_of_proj_le {ι : Type*} (s : Finset ι) (f : ι → ℂ) {τ : ℂ} (hτ : ‖τ‖ = 1)
    {θ : ℝ} (hf : ∀ i ∈ s, (f i * conj τ).re ≤ -θ) : θ * s.card ≤ ‖∑ i ∈ s, f i‖ := by
  have h1 : (∑ i ∈ s, f i * conj τ).re ≤ ∑ _i ∈ s, -θ := by
    rw [Complex.re_sum]; exact Finset.sum_le_sum hf
  rw [Finset.sum_const, nsmul_eq_mul] at h1
  have h2 : ‖∑ i ∈ s, f i * conj τ‖ = ‖∑ i ∈ s, f i‖ := by
    rw [← Finset.sum_mul, norm_mul, Complex.norm_conj, hτ, mul_one]
  have h3 := Complex.re_le_norm (-(∑ i ∈ s, f i * conj τ))
  rw [Complex.neg_re, norm_neg, h2] at h3
  linarith

/-- A nonempty sum of vectors with projections `≤ -θ < 0` on a unit tangent is nonzero. -/
theorem sum_ne_zero_of_proj_le {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (f : ι → ℂ) {τ : ℂ}
    (hτ : ‖τ‖ = 1) {θ : ℝ} (hθ : 0 < θ) (hf : ∀ i ∈ s, (f i * conj τ).re ≤ -θ) :
    ∑ i ∈ s, f i ≠ 0 := by
  intro h
  have := norm_sum_ge_of_proj_le s f hτ hf
  rw [h, norm_zero] at this
  have : (0 : ℝ) < θ * s.card := mul_pos hθ (by exact_mod_cast hs.card_pos)
  linarith

/-! ## §13.2: two unflagged `H` neighbours at an unflagged `J` -/

/-- **§13.2.**  If `a / T → A ≠ 0` and `a⋆ → B ≠ 0` as `T → ∞`, then `‖a a⋆‖ → ∞`; in particular
the unit condition `a a⋆ = 1` eventually fails. -/
theorem J_two_H_eventually_ne_one {ι : Type*} {F : Filter ι} {T : ι → ℝ} (hT : Tendsto T F atTop)
    {a aS : ι → ℂ} {A B : ℂ} (hA : A ≠ 0) (hB : B ≠ 0)
    (ha : Tendsto (fun i => a i / T i) F (𝓝 A)) (haS : Tendsto aS F (𝓝 B)) (M : ℝ) :
    ∀ᶠ i in F, M < ‖a i * aS i‖ ∧ a i * aS i ≠ 1 := by
  have hAB : 0 < ‖A * B‖ := norm_pos_iff.2 (mul_ne_zero hA hB)
  have hlim : Tendsto (fun i => a i / T i * aS i) F (𝓝 (A * B)) := ha.mul haS
  have h1 := Metric.tendsto_nhds.1 hlim (‖A * B‖ / 2) (by positivity)
  have h2 := hT.eventually (eventually_gt_atTop (max 0 (2 * (|M| + 1) / ‖A * B‖)))
  filter_upwards [h1, h2] with i hi hTi
  rw [max_lt_iff] at hTi
  obtain ⟨hT0, hT1⟩ := hTi
  rw [dist_eq_norm] at hi
  have hlow : ‖A * B‖ / 2 ≤ ‖a i / T i * aS i‖ := by
    have := norm_sub_norm_le (A * B) (A * B - a i / T i * aS i)
    rw [sub_sub_cancel, norm_sub_rev] at this
    linarith
  have heq : ‖a i / T i * aS i‖ = ‖a i * aS i‖ / T i := by
    rw [div_mul_eq_mul_div, norm_div, Complex.norm_real, Real.norm_of_nonneg hT0.le]
  rw [heq, le_div_iff₀ hT0] at hlow
  rw [div_lt_iff₀ hAB] at hT1
  have hbig : |M| + 1 < ‖a i * aS i‖ := by nlinarith
  refine ⟨lt_of_le_of_lt (le_abs_self M) (by linarith), fun h => ?_⟩
  rw [h, norm_one] at hbig
  linarith [abs_nonneg M]

/-- **The leading coefficient at a `J` receiver** (§13.2).  If `l > 0` and the incoming responses
`z j` (`j ∈ s`) have normalised limits `z j / T → ξ j` with `Re ξ j ≥ 0`, then
`(l T + v + ∑ z j) / T → l + ∑ ξ j`, whose real part is positive. -/
theorem J_leading_tendsto {ι κ : Type*} {F : Filter ι} {T : ι → ℝ} (hT : Tendsto T F atTop)
    (s : Finset κ) {z : κ → ι → ℂ} {ξ : κ → ℂ}
    (hz : ∀ j ∈ s, Tendsto (fun i => z j i / T i) F (𝓝 (ξ j))) (l : ℝ) (v : ℂ) :
    Tendsto (fun i => ((l : ℂ) * T i + v + ∑ j ∈ s, z j i) / T i) F (𝓝 (l + ∑ j ∈ s, ξ j)) := by
  have hinv := tendsto_inv_ofReal hT
  have h : Tendsto (fun i => (l : ℂ) + v * ((T i : ℝ) : ℂ)⁻¹ + ∑ j ∈ s, z j i / T i) F
      (𝓝 (l + v * 0 + ∑ j ∈ s, ξ j)) :=
    (tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)).add (tendsto_finset_sum s hz)
  rw [mul_zero, add_zero] at h
  refine h.congr' ?_
  filter_upwards [hT.eventually (eventually_gt_atTop 0)] with i hi
  have hT0 : ((T i : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hi.ne'
  rw [← Finset.sum_div]
  field_simp

theorem J_leading_re_pos {κ : Type*} (s : Finset κ) {ξ : κ → ℂ} (hξ : ∀ j ∈ s, 0 ≤ (ξ j).re)
    {l : ℝ} (hl : 0 < l) : 0 < ((l : ℂ) + ∑ j ∈ s, ξ j).re := by
  rw [Complex.add_re, Complex.ofReal_re, Complex.re_sum]
  have := Finset.sum_nonneg hξ
  linarith

/-- **§13.2, complete asymptotic form.**  At an unflagged `J` with retained unit vector `v` and
incoming `H` responses `z j` (`j ∈ s`) with `z j / T → ξ j` (`Re ξ j ≥ 0`) and `(z j)⁻¹ → β j`,
if the constant coefficient `conj v + ∑ β j` is nonzero (the three-port margin), then the unit
condition `a a⋆ = 1` for `a = l T + v + ∑ z j`, `a⋆ = l / T + conj v + ∑ (z j)⁻¹` eventually
fails. -/
theorem J_unit_eventually_fails {ι κ : Type*} {F : Filter ι} {T : ι → ℝ}
    (hT : Tendsto T F atTop) (s : Finset κ) {z : κ → ι → ℂ} {ξ β : κ → ℂ}
    (hz : ∀ j ∈ s, Tendsto (fun i => z j i / T i) F (𝓝 (ξ j))) (hξ : ∀ j ∈ s, 0 ≤ (ξ j).re)
    (hzi : ∀ j ∈ s, Tendsto (fun i => (z j i)⁻¹) F (𝓝 (β j))) {l : ℝ} (hl : 0 < l) (v : ℂ)
    (hB : conj v + ∑ j ∈ s, β j ≠ 0) :
    ∀ᶠ i in F, ((l : ℂ) * T i + v + ∑ j ∈ s, z j i) *
      ((l : ℂ) / T i + conj v + ∑ j ∈ s, (z j i)⁻¹) ≠ 1 := by
  have hA := J_leading_re_pos s hξ hl
  have hA0 : (l : ℂ) + ∑ j ∈ s, ξ j ≠ 0 := fun h => by
    rw [h, Complex.zero_re] at hA; exact lt_irrefl _ hA
  have hinv := tendsto_inv_ofReal hT
  have haS : Tendsto (fun i => (l : ℂ) / T i + conj v + ∑ j ∈ s, (z j i)⁻¹) F
      (𝓝 (conj v + ∑ j ∈ s, β j)) := by
    have h : Tendsto (fun i => (l : ℂ) * ((T i : ℝ) : ℂ)⁻¹ + conj v + ∑ j ∈ s, (z j i)⁻¹) F
        (𝓝 (l * 0 + conj v + ∑ j ∈ s, β j)) :=
      ((tendsto_const_nhds.mul hinv).add tendsto_const_nhds).add (tendsto_finset_sum s hzi)
    rw [mul_zero, zero_add] at h
    simpa [div_eq_mul_inv] using h
  filter_upwards [J_two_H_eventually_ne_one hT hA0 hB (J_leading_tendsto hT s hz l v) haS 0]
    with i hi
  exact hi.2

/-! ## §13.3: adjacent unflagged `J` faces -/

/-- The (H1) expression `a a⋆ b b⋆ (a + b)(a⋆ + b⋆) + (a b⋆ - a⋆ b)²`. -/
def hhExpr (a aS b bS : ℂ) : ℂ := a * aS * (b * bS) * ((a + b) * (aS + bS)) + (a * bS - aS * b) ^ 2

/-- **§13.3, the cubic coefficient.**  If `Re A₁ > 0`, `Re A₂ > 0` and `B₁ B₂ (B₁ + B₂) ≠ 0`, then
`A₁ A₂ (A₁ + A₂) B₁ B₂ (B₁ + B₂) ≠ 0`. -/
theorem jj_cubic_coeff_ne_zero {A₁ A₂ B₁ B₂ : ℂ} (h₁ : 0 < A₁.re) (h₂ : 0 < A₂.re)
    (hB : B₁ * B₂ * (B₁ + B₂) ≠ 0) : A₁ * A₂ * (A₁ + A₂) * (B₁ * B₂ * (B₁ + B₂)) ≠ 0 := by
  have hne : ∀ z : ℂ, 0 < z.re → z ≠ 0 := fun z hz h => by
    rw [h, Complex.zero_re] at hz; exact lt_irrefl _ hz
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (hne _ h₁) (hne _ h₂)) (hne _ ?_)) hB
  rw [Complex.add_re]; linarith

/-- **§13.3, the asymptotics of (H1).**  If `a / T → A₁`, `b / T → A₂`, `a⋆ → B₁`, `b⋆ → B₂`, then
the (H1) expression divided by `T³` tends to `A₁ A₂ (A₁ + A₂) B₁ B₂ (B₁ + B₂)`: the first term is
cubic in `T` and the squared term has order at most two. -/
theorem hhExpr_div_cube_tendsto {ι : Type*} {F : Filter ι} {T : ι → ℝ} (hT : Tendsto T F atTop)
    {a aS b bS : ι → ℂ} {A₁ A₂ B₁ B₂ : ℂ}
    (ha : Tendsto (fun i => a i / T i) F (𝓝 A₁)) (hb : Tendsto (fun i => b i / T i) F (𝓝 A₂))
    (haS : Tendsto aS F (𝓝 B₁)) (hbS : Tendsto bS F (𝓝 B₂)) :
    Tendsto (fun i => hhExpr (a i) (aS i) (b i) (bS i) / (T i : ℂ) ^ 3) F
      (𝓝 (A₁ * A₂ * (A₁ + A₂) * (B₁ * B₂ * (B₁ + B₂)))) := by
  have hinv := tendsto_inv_ofReal hT
  set u : ι → ℂ := fun i => a i / T i
  set v : ι → ℂ := fun i => b i / T i
  have hlim : Tendsto (fun i => u i * aS i * (v i * bS i) * ((u i + v i) * (aS i + bS i)) +
      (u i * bS i - aS i * v i) ^ 2 * ((T i : ℝ) : ℂ)⁻¹) F
      (𝓝 (A₁ * B₁ * (A₂ * B₂) * ((A₁ + A₂) * (B₁ + B₂)) + (A₁ * B₂ - B₁ * A₂) ^ 2 * 0)) :=
    (((ha.mul haS).mul (hb.mul hbS)).mul ((ha.add hb).mul (haS.add hbS))).add
      ((((ha.mul hbS).sub (haS.mul hb)).pow 2).mul hinv)
  rw [mul_zero, add_zero] at hlim
  have e : A₁ * B₁ * (A₂ * B₂) * ((A₁ + A₂) * (B₁ + B₂)) =
      A₁ * A₂ * (A₁ + A₂) * (B₁ * B₂ * (B₁ + B₂)) := by ring
  rw [e] at hlim
  refine hlim.congr' ?_
  filter_upwards [hT.eventually (eventually_gt_atTop 0)] with i hi
  have hT0 : ((T i : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hi.ne'
  simp only [u, v, hhExpr]
  field_simp

/-- **§13.3.**  Under the hypotheses of `jj_cubic_coeff_ne_zero` and the limits of
`hhExpr_div_cube_tendsto`, the (H1) relation eventually fails. -/
theorem jj_hhExpr_eventually_ne_zero {ι : Type*} {F : Filter ι} {T : ι → ℝ}
    (hT : Tendsto T F atTop) {a aS b bS : ι → ℂ} {A₁ A₂ B₁ B₂ : ℂ} (h₁ : 0 < A₁.re)
    (h₂ : 0 < A₂.re) (hB : B₁ * B₂ * (B₁ + B₂) ≠ 0)
    (ha : Tendsto (fun i => a i / T i) F (𝓝 A₁)) (hb : Tendsto (fun i => b i / T i) F (𝓝 A₂))
    (haS : Tendsto aS F (𝓝 B₁)) (hbS : Tendsto bS F (𝓝 B₂)) :
    ∀ᶠ i in F, hhExpr (a i) (aS i) (b i) (bS i) ≠ 0 := by
  have hc := jj_cubic_coeff_ne_zero h₁ h₂ hB
  have hlim := hhExpr_div_cube_tendsto hT ha hb haS hbS
  filter_upwards [hlim.eventually_ne hc] with i hi h
  rw [h, zero_div] at hi
  exact hi rfl

/-! ## §13.4: capless components -/

/-- **§13.4.**  Let `w j` (`j ∈ s`) be the outgoing responses of a capless component, with
normalised limits `w j / T → ξ j` of nonnegative real part.  For `k₀ > 0` and any fixed `Z₀`, the
closure relation `∑ w j = -k₀ T - Z₀` eventually fails. -/
theorem component_sum_eventually_ne {ι κ : Type*} {F : Filter ι} {T : ι → ℝ}
    (hT : Tendsto T F atTop) (s : Finset κ) {w : κ → ι → ℂ} {ξ : κ → ℂ}
    (hw : ∀ j ∈ s, Tendsto (fun i => w j i / T i) F (𝓝 (ξ j))) (hξ : ∀ j ∈ s, 0 ≤ (ξ j).re)
    {k₀ : ℝ} (hk₀ : 0 < k₀) (Z₀ : ℂ) :
    ∀ᶠ i in F, ∑ j ∈ s, w j i ≠ -(k₀ : ℂ) * T i - Z₀ := by
  have hinv := tendsto_inv_ofReal hT
  have hsum : Tendsto (fun i => ∑ j ∈ s, w j i / T i) F (𝓝 (∑ j ∈ s, ξ j)) :=
    tendsto_finset_sum s hw
  have hrhs : Tendsto (fun i => -(k₀ : ℂ) - Z₀ * ((T i : ℝ) : ℂ)⁻¹) F (𝓝 (-(k₀ : ℂ) - Z₀ * 0)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.mul hinv)
  rw [mul_zero, sub_zero] at hrhs
  have hne : ∑ j ∈ s, ξ j ≠ -(k₀ : ℂ) := by
    intro h
    have hre := congrArg Complex.re h
    rw [Complex.re_sum, Complex.neg_re, Complex.ofReal_re] at hre
    have : 0 ≤ ∑ j ∈ s, (ξ j).re := Finset.sum_nonneg hξ
    linarith
  have hdiff := (hsum.sub hrhs).eventually_ne (sub_ne_zero.2 hne)
  filter_upwards [hdiff, hT.eventually (eventually_gt_atTop 0)] with i hi hTi h
  apply hi
  have hT0 : ((T i : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hTi.ne'
  rw [← Finset.sum_div, h]
  field_simp
  ring

/-! ## Loops (§§13.1, 13.3) -/

/-- The polynomial `k X + Z` of an `H` loop (`k ζ + Z = 0`). -/
noncomputable def hLoopPoly (k : ℝ) (Z : ℂ) : ℂ[X] := C (k : ℂ) * X + C Z

theorem hLoopPoly_eval (k : ℝ) (Z ζ : ℂ) : (hLoopPoly k Z).eval ζ = (k : ℂ) * ζ + Z := by
  simp [hLoopPoly]

/-- An `H` loop pins the direction: `hLoopPoly k Z ≠ 0` for `k ≠ 0`. -/
theorem hLoopPoly_ne_zero {k : ℝ} (hk : k ≠ 0) (Z : ℂ) : hLoopPoly k Z ≠ 0 := by
  intro h
  have := congrArg (fun p => p.coeff 1) h
  simp [hLoopPoly, coeff_C] at this
  exact hk this

/-- The polynomial `ζ (|l ζ + v|² - 1)` of a `J` loop, written as a polynomial in `ζ`:
`l v̄ X² + (l² + v v̄ - 1) X + l v`. -/
noncomputable def jLoopPoly (l : ℝ) (v : ℂ) : ℂ[X] :=
  C ((l : ℂ) * conj v) * X ^ 2 + C ((l : ℂ) ^ 2 + v * conj v - 1) * X + C ((l : ℂ) * v)

/-- On the unit circle, `jLoopPoly` evaluates to `ζ (|l ζ + v|² - 1)`. -/
theorem jLoopPoly_eval {ζ : ℂ} (hζ : ‖ζ‖ = 1) (l : ℝ) (v : ℂ) :
    (jLoopPoly l v).eval ζ = ζ * (((‖(l : ℂ) * ζ + v‖ ^ 2 - 1 : ℝ)) : ℂ) := by
  have hζ0 := ne_zero_of_norm_eq_one hζ
  push_cast
  rw [← Complex.ofReal_pow, norm_sq_eq_mul_conj]
  simp only [jLoopPoly, eval_add, eval_mul, eval_C, eval_X, eval_pow, map_add, map_mul,
    Complex.conj_ofReal, conj_eq_inv hζ]
  field_simp
  ring

/-- A `J` loop pins the direction: `jLoopPoly l v ≠ 0` for `l ≠ 0` and `v ≠ 0` (its constant
coefficient is `l v`). -/
theorem jLoopPoly_ne_zero {l : ℝ} (hl : l ≠ 0) {v : ℂ} (hv : v ≠ 0) : jLoopPoly l v ≠ 0 := by
  intro h
  have := congrArg (fun p => p.coeff 0) h
  simp [jLoopPoly, coeff_X, coeff_C] at this
  rcases this with h1 | h1
  · exact hl h1
  · exact hv h1

end QuadraticResponse

end Erdos99
end

end QuadraticResponseJ

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `PinnedPolys`
-/

section PinnedPolys

/-!
# Pinning by explicit polynomials (Verification Guide §§12.5, 13)

This file connects the explicit pinning polynomials of §13 to the counting engine
`pinned_directions_few` (§12.5), which is phrased in terms of coefficient vectors.

* `polyCoeffs d p`: the coefficient vector of `p` in degrees `0, …, d`;
  `coeffPoly_polyCoeffs`: it recovers `p` when `deg p ≤ d`;
* `pinned_polys_few`: **pinning by polynomials of bounded degree.**  The version of
  `pinned_directions_few` in which the centres and the pattern polynomials are polynomials of
  degree `≤ d` (rather than coefficient vectors);
* the coefficient lower bounds needed for the centres: `one_le_norm_capCoeffs` (the cap
  polynomial (H2) of §13.5), `one_le_norm_hLoopCoeffs` (an `H` loop) and `one_le_norm_jLoopCoeffs`
  (a `J` loop);
* `cap_directions_few`, `hLoop_directions_few`, `jLoop_directions_few`: the resulting counting
  statements for these three explicit families.
-/

open Filter Polynomial ComplexConjugate

@[expose] public noncomputable section

open Classical

namespace Erdos99

open DirectionPinning QuadraticResponse

/-- The coefficient vector of the polynomial `p` in degrees `0, …, d`. -/
def polyCoeffs (d : ℕ) (p : ℂ[X]) : Fin (d + 1) → ℂ := fun i => p.coeff i

lemma coeffPoly_polyCoeffs {d : ℕ} {p : ℂ[X]} (hp : p.natDegree ≤ d) :
    coeffPoly (polyCoeffs d p) = p := by
  ext n
  by_cases hn : n ≤ d
  · have := coeff_coeffPoly (polyCoeffs d p) ⟨n, Nat.lt_succ_of_le hn⟩
    simpa [polyCoeffs] using this
  · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (natDegree_coeffPoly_le _) (not_le.1 hn)),
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp (not_le.1 hn))]

lemma norm_coeff_le_norm_polyCoeffs (d : ℕ) (p : ℂ[X]) {i : ℕ} (hi : i ≤ d) :
    ‖p.coeff i‖ ≤ ‖polyCoeffs d p‖ :=
  norm_le_pi_norm (polyCoeffs d p) ⟨i, Nat.lt_succ_of_le hi⟩

/-- **Pinning by polynomials of bounded degree** (Verification Guide §12.5).  Fix a degree bound
`d`, a number `N` of centres and a lower bound `m₀ > 0`.  For every `ε > 0` there are tolerances
`r, μ > 0` such that eventually, in every optimal configuration, for all centre polynomials `p₀ j`
of degree `≤ d` with coefficient vectors of norm `≥ m₀`, every set `A` of counterclockwise hull
sides whose unit directions `ζ` each satisfy `|p(ζ)| < r` for a polynomial `p` of degree `≤ d`
whose coefficients are within `μ` of those of some centre has at most `ε D` elements. -/
theorem pinned_polys_few (d N : ℕ) {ε m₀ : ℝ} (hε : 0 < ε) (hm₀ : 0 < m₀) :
    ∃ r > 0, ∃ μ > 0, ∀ᶠ n in atTop, ∀ X, IsOptimal n X →
      ∀ p₀ : Fin N → ℂ[X], (∀ j, m₀ ≤ ‖polyCoeffs d (p₀ j)‖) →
      ∀ A ⊆ ccwHullSides X, (∀ q ∈ A, ∃ j, ∃ p : ℂ[X], p.natDegree ≤ d ∧
        ‖polyCoeffs d p - polyCoeffs d (p₀ j)‖ < μ ∧ ‖p.eval (toC (sideDir q))‖ < r) →
      (A.card : ℝ) ≤ ε * diam X := by
  obtain ⟨r, hr, μ, hμ, h⟩ := pinned_directions_few d N hε hm₀
  refine ⟨r, hr, μ, hμ, ?_⟩
  filter_upwards [h] with n hn X hX p₀ hp₀ A hA hpin
  refine hn X hX (fun j => polyCoeffs d (p₀ j)) hp₀ A hA fun q hq => ?_
  obtain ⟨j, p, hpd, hc, hev⟩ := hpin q hq
  exact ⟨j, polyCoeffs d p, hc, by rwa [coeffPoly_polyCoeffs hpd]⟩

/-! ## The cap polynomial (H2) -/

lemma capPoly_expand (k : ℝ) (v Z : ℂ) : capPoly k v Z =
    C (conj v * conj Z) * X ^ 4 + C ((k : ℂ) * conj Z + (k : ℂ) * conj v) * X ^ 3 +
      C ((k : ℂ) ^ 2 + v * conj v + Z * conj Z - 1) * X ^ 2 + C ((k : ℂ) * v + (k : ℂ) * Z) * X +
      C (Z * v) := by
  simp only [capPoly, map_add, map_mul, map_sub, map_pow, map_one]
  ring

lemma natDegree_capPoly_le (k : ℝ) (v Z : ℂ) : (capPoly k v Z).natDegree ≤ 4 := by
  rw [capPoly_expand]
  compute_degree

/-- The coefficient vector of the cap polynomial has norm at least `1` when `|v| = 1` and
`k ∈ {1, 2}` (its `ζ²` coefficient is `k² + |Z|²`). -/
lemma one_le_norm_capCoeffs {k : ℝ} (hk : k = 1 ∨ k = 2) {v : ℂ} (hv : ‖v‖ = 1) (Z : ℂ) :
    1 ≤ ‖polyCoeffs 4 (capPoly k v Z)‖ := by
  refine le_trans ?_ (norm_coeff_le_norm_polyCoeffs 4 _ (by norm_num : 2 ≤ 4))
  rw [capPoly_coeff_two, mul_conj_eq_one hv, ← norm_sq_eq_mul_conj]
  have e : (k : ℂ) ^ 2 + 1 + ((‖Z‖ ^ 2 : ℝ) : ℂ) - 1 = ((k ^ 2 + ‖Z‖ ^ 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [e, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have : 1 ≤ k ^ 2 := by rcases hk with rfl | rfl <;> norm_num
  nlinarith [sq_nonneg ‖Z‖]

/-! ## Loop polynomials -/

lemma natDegree_hLoopPoly_le (k : ℝ) (Z : ℂ) : (hLoopPoly k Z).natDegree ≤ 4 := by
  unfold hLoopPoly
  compute_degree
  all_goals norm_num

lemma one_le_norm_hLoopCoeffs {k : ℝ} (hk : k = 1 ∨ k = 2) (Z : ℂ) :
    1 ≤ ‖polyCoeffs 4 (hLoopPoly k Z)‖ := by
  refine le_trans ?_ (norm_coeff_le_norm_polyCoeffs 4 _ (by norm_num : 1 ≤ 4))
  have : (hLoopPoly k Z).coeff 1 = k := by simp [hLoopPoly, coeff_C]
  rw [this, Complex.norm_real]
  rcases hk with rfl | rfl <;> norm_num

lemma natDegree_jLoopPoly_le (l : ℝ) (v : ℂ) : (jLoopPoly l v).natDegree ≤ 4 := by
  unfold jLoopPoly
  compute_degree
  all_goals norm_num

lemma one_le_norm_jLoopCoeffs {l : ℝ} (hl : l = 1 ∨ l = 2) {v : ℂ} (hv : ‖v‖ = 1) :
    1 ≤ ‖polyCoeffs 4 (jLoopPoly l v)‖ := by
  refine le_trans ?_ (norm_coeff_le_norm_polyCoeffs 4 _ (by norm_num : 0 ≤ 4))
  have : (jLoopPoly l v).coeff 0 = l * v := by simp [jLoopPoly, coeff_X, coeff_C]
  rw [this, norm_mul, Complex.norm_real, hv, mul_one]
  rcases hl with rfl | rfl <;> norm_num

/-! ## Counting statements for the explicit families -/

/-- **(H2) pins few directions** (§13.5).  For every number `N` of centres `(k j, v j, Z j)` with
`k j ∈ {1, 2}`, `|v j| = 1` and every `ε > 0`, there are tolerances `r, μ > 0` such that
eventually at most `ε D` hull sides have a direction that is an `r`-approximate root of a cap
polynomial (H2) whose coefficients are within `μ` of those of a centre. -/
theorem cap_directions_few (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∃ μ > 0, ∀ᶠ n in atTop, ∀ X, IsOptimal n X →
      ∀ (k : Fin N → ℝ) (v Z : Fin N → ℂ), (∀ j, k j = 1 ∨ k j = 2) → (∀ j, ‖v j‖ = 1) →
      ∀ A ⊆ ccwHullSides X, (∀ q ∈ A, ∃ j, ∃ (k' : ℝ) (v' Z' : ℂ),
        ‖polyCoeffs 4 (capPoly k' v' Z') - polyCoeffs 4 (capPoly (k j) (v j) (Z j))‖ < μ ∧
        ‖(capPoly k' v' Z').eval (toC (sideDir q))‖ < r) →
      (A.card : ℝ) ≤ ε * diam X := by
  obtain ⟨r, hr, μ, hμ, h⟩ := pinned_polys_few 4 N hε one_pos
  refine ⟨r, hr, μ, hμ, ?_⟩
  filter_upwards [h] with n hn X hX k v Z hk hv A hA hpin
  refine hn X hX (fun j => capPoly (k j) (v j) (Z j))
    (fun j => one_le_norm_capCoeffs (hk j) (hv j) (Z j)) A hA fun q hq => ?_
  obtain ⟨j, k', v', Z', hc, hev⟩ := hpin q hq
  exact ⟨j, capPoly k' v' Z', natDegree_capPoly_le _ _ _, hc, hev⟩

/-- **`H` loops pin few directions** (§13.1). -/
theorem hLoop_directions_few (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∃ μ > 0, ∀ᶠ n in atTop, ∀ X, IsOptimal n X →
      ∀ (k : Fin N → ℝ) (Z : Fin N → ℂ), (∀ j, k j = 1 ∨ k j = 2) →
      ∀ A ⊆ ccwHullSides X, (∀ q ∈ A, ∃ j, ∃ (k' : ℝ) (Z' : ℂ),
        ‖polyCoeffs 4 (hLoopPoly k' Z') - polyCoeffs 4 (hLoopPoly (k j) (Z j))‖ < μ ∧
        ‖(k' : ℂ) * toC (sideDir q) + Z'‖ < r) →
      (A.card : ℝ) ≤ ε * diam X := by
  obtain ⟨r, hr, μ, hμ, h⟩ := pinned_polys_few 4 N hε one_pos
  refine ⟨r, hr, μ, hμ, ?_⟩
  filter_upwards [h] with n hn X hX k Z hk A hA hpin
  refine hn X hX (fun j => hLoopPoly (k j) (Z j))
    (fun j => one_le_norm_hLoopCoeffs (hk j) (Z j)) A hA fun q hq => ?_
  obtain ⟨j, k', Z', hc, hev⟩ := hpin q hq
  exact ⟨j, hLoopPoly k' Z', natDegree_hLoopPoly_le _ _, hc, by rwa [hLoopPoly_eval]⟩

/-- **`J` loops pin few directions** (§13.3): the relation `|l ζ + v| ≈ 1` pins `ζ`. -/
theorem jLoop_directions_few (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∃ μ > 0, ∀ᶠ n in atTop, ∀ X, IsOptimal n X →
      ∀ (l : Fin N → ℝ) (v : Fin N → ℂ), (∀ j, l j = 1 ∨ l j = 2) → (∀ j, ‖v j‖ = 1) →
      ∀ A ⊆ ccwHullSides X, (∀ q ∈ A, ∃ j, ∃ (l' : ℝ) (v' : ℂ),
        ‖polyCoeffs 4 (jLoopPoly l' v') - polyCoeffs 4 (jLoopPoly (l j) (v j))‖ < μ ∧
        |‖(l' : ℂ) * toC (sideDir q) + v'‖ ^ 2 - 1| < r) →
      (A.card : ℝ) ≤ ε * diam X := by
  obtain ⟨r, hr, μ, hμ, h⟩ := pinned_polys_few 4 N hε one_pos
  refine ⟨r, hr, μ, hμ, ?_⟩
  filter_upwards [h] with n hn X hX l v hl hv A hA hpin
  refine hn X hX (fun j => jLoopPoly (l j) (v j))
    (fun j => one_le_norm_jLoopCoeffs (hl j) (hv j)) A hA fun q hq => ?_
  obtain ⟨j, l', v', hc, hev⟩ := hpin q hq
  refine ⟨j, jLoopPoly l' v', natDegree_jLoopPoly_le _ _, hc, ?_⟩
  have hne : q.1 ≠ q.2 := (Finset.mem_filter.1 (hA hq)).2.2.2.1
  have hu : ‖toC (sideDir q)‖ = 1 := by rw [LinearIsometryEquiv.norm_map]; exact norm_sideDir hne
  rw [jLoopPoly_eval hu, norm_mul, hu, one_mul, Complex.norm_real, Real.norm_eq_abs]
  exact hev

end Erdos99

end

end PinnedPolys

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `ReturnBudgets`
-/

section ReturnBudgets

/-!
# The hull-return budgets of saturation (Verification Guide §10)

This file proves the two hull-return parts of the saturation statement `saturation_core`
(`ChargingResidual`) from the short-source theorems (Lemma 3.4):

* `unitReturnsNoShort_small`: for every cutoff fraction `a > 0` and every `ε > 0`, eventually at
  most `ε D` unit hull returns have no short port at the cutoff `a D` (`Bunit ≤ ε D`);
* `twoReturnsNoShort_small`: likewise at most `ε D` two-edge hull returns have no short port
  (`Btwo ≤ ε D`).

The point is that a port which is not short at the cutoff `a D` lies on a track with at least
`a D ≥ D^{19/20}` rhombi (for `D` large), and such sources are few by `short_unit_sources` and
`short_two_edge_sources`.
-/

open scoped BigOperators
open EstablishedExternalResults Filter

@[expose] public noncomputable section

open Classical

namespace Erdos99

/-- The length of the (possibly rhombus-free) track of a unit edge is at most the length of its
rhombus track `srcLen` (they agree on rhombus edges; a rhombus-free edge has length `0`). -/
lemma trackLength_allTrackOf_le_srcLen {X : Finset Plane} (hX : IsSeparated X)
    (htri : ¬ HasUnitTriangle X) {e : Sym2 Plane} (he : e ∈ unitEdges X) :
    trackLength X (allTrackOf X e) ≤ srcLen X e := by
  by_cases hr : e ∈ rhombusEdges X
  · rw [allTrackOf_of_mem_rhombusEdges hr, srcLen]
  · rw [allTrackOf_of_not_mem he hr, trackLength_singleton hX htri he hr]
    exact Nat.zero_le _

/-- For every cutoff fraction `a > 0`, eventually `D^{19/20} ≤ a D` for every optimal
configuration. -/
lemma eventually_rpow_le_mul_diam {a : ℝ} (ha : 0 < a) :
    ∀ᶠ n in atTop, ∀ X, IsOptimal n X → diam X ^ (19 / 20 : ℝ) ≤ a * diam X := by
  have hev : ∀ᶠ n in atTop, max 1 ((1 / a) ^ (20 : ℝ)) ≤ minDiam n :=
    tendsto_minDiam.eventually (eventually_ge_atTop _)
  filter_upwards [hev] with n hn X hX
  rw [← hX.diam_eq] at hn
  set D := diam X
  have hD1 : 1 ≤ D := (le_max_left _ _).trans hn
  have hD0 : 0 < D := by linarith
  have hDa : (1 / a) ^ (20 : ℝ) ≤ D := (le_max_right _ _).trans hn
  -- `D^{1/20} ≥ 1/a`
  have h1 : 1 / a ≤ D ^ (1 / 20 : ℝ) := by
    have := Real.rpow_le_rpow (by positivity) hDa (by norm_num : (0 : ℝ) ≤ 1 / 20)
    rwa [← Real.rpow_mul (by positivity), show (20 : ℝ) * (1 / 20) = 1 by norm_num,
      Real.rpow_one] at this
  have hsplit : D = D ^ (19 / 20 : ℝ) * D ^ (1 / 20 : ℝ) := by
    rw [← Real.rpow_add hD0]; norm_num
  have hpos : 0 < D ^ (19 / 20 : ℝ) := Real.rpow_pos_of_pos hD0 _
  have h2 : 1 ≤ a * D ^ (1 / 20 : ℝ) := by
    rw [div_le_iff₀ ha] at h1; linarith
  calc D ^ (19 / 20 : ℝ) = D ^ (19 / 20 : ℝ) * 1 := (mul_one _).symm
    _ ≤ D ^ (19 / 20 : ℝ) * (a * D ^ (1 / 20 : ℝ)) := mul_le_mul_of_nonneg_left h2 hpos.le
    _ = a * (D ^ (19 / 20 : ℝ) * D ^ (1 / 20 : ℝ)) := by ring
    _ = a * D := by rw [← hsplit]

/-- A port that is not short at the cutoff `L` lies on a track of length at least `L`. -/
lemma le_srcLen_of_not_short {X : Finset Plane} (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X)
    {L : ℝ} {N : PortNode} (h0 : shortDeg X L N = 0) {e : Sym2 Plane} (he : e ∈ unitEdges X)
    (hp : IsPort X N e) : L ≤ srcLen X e := by
  rw [shortDeg, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
  have h := h0 he
  rw [not_and, not_lt] at h
  exact (h hp).trans (by exact_mod_cast trackLength_allTrackOf_le_srcLen hX htri he)

/-- **`Bunit` is small** (Verification Guide §10).  For every cutoff fraction `a > 0` and every
`ε > 0`, eventually at most `ε D` unit hull returns have no short port at the cutoff `a D`. -/
theorem unitReturnsNoShort_small (ε : ℝ) (hε : 0 < ε) {a : ℝ} (ha : 0 < a) :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      (unitReturnsNoShort X (a * diam X) : ℝ) ≤ ε * diam X := by
  filter_upwards [short_unit_sources ε hε, two_le_returnLength, eventually_rpow_le_mul_diam ha]
    with n hsrc h2 hDa hfm X hX htri
  refine le_trans ?_ (hsrc hfm X hX htri)
  rw [unitReturnsNoShort]
  refine Nat.cast_le.2 (Finset.card_le_card fun p hp => ?_)
  obtain ⟨hpS, hret, h0⟩ := Finset.mem_filter.1 hp
  have hd : dist p.1 p.2 = 1 := by
    by_contra hd
    have := h2 hfm X hX p hpS hd
    omega
  have hs := mem_ccwHullSides.1 hpS
  have hvX := mem_of_mem_hullVertices hs.1
  have hwX := mem_of_mem_hullVertices hs.2.1
  have he : s(p.1, p.2) ∈ unitEdges X := mem_unitEdges.2 ⟨hvX, hwX, hd⟩
  have hport : IsPort X (Sum.inr p) s(p.1, p.2) := ⟨hpS, he, by rw [if_pos hd]⟩
  refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hpS, hd⟩, ?_⟩
  exact (hDa X hX).trans (le_srcLen_of_not_short hX.1.2 htri h0 he hport)

/-- Among three points `P₁, P₂, Y`, a pair `{a, b}` of distinct points other than `{P₁, P₂}` is
`{P₁, Y}` or `{Y, P₂}`. -/
lemma sym2_cases_of_three {P₁ P₂ Y a b : ℂ} (ha : a = P₁ ∨ a = P₂ ∨ a = Y)
    (hb : b = P₁ ∨ b = P₂ ∨ b = Y) (hab : a ≠ b) (hne : s(a, b) ≠ s(P₁, P₂)) :
    s(a, b) = s(P₁, Y) ∨ s(a, b) = s(Y, P₂) := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    simp_all [Sym2.eq_swap]

/-- **The two ports of a two-edge return.**  Eventually, every counterclockwise hull side `(v, w)`
whose return has two unit edges comes with a point `x` such that `(v, x, w)` is a two-edge return
and both `[v, x]` and `[x, w]` are ports of the hull side. -/
theorem exists_twoEdgeReturn_ports :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      ∀ p ∈ ccwHullSides X, returnLength X p.1 p.2 = 2 →
        ∃ x, (p.1, x, p.2) ∈ twoEdgeReturns X ∧ IsPort X (Sum.inr p) s(p.1, x) ∧
          IsPort X (Sum.inr p) s(x, p.2) := by
  filter_upwards [portDeg_hullSide, cap_polygon] with n hdeg hcap hfm X hX p hp hret
  have hs := mem_ccwHullSides.1 hp
  have hvX := mem_of_mem_hullVertices hs.1
  have hwX := mem_of_mem_hullVertices hs.2.1
  have hd : dist p.1 p.2 ≠ 1 := fun h => by
    rw [returnLength_of_dist_eq_one h] at hret; norm_num at hret
  have hgt : 1 < dist p.1 p.2 := lt_of_le_of_ne (hX.1.2 _ hvX _ hwX hs.2.2.1) (Ne.symm hd)
  obtain ⟨⟨F0, hF0, huniq⟩, hpoly⟩ := hcap hfm X hX p hp hgt
  obtain ⟨S, hSV, hP1, hP2, -, -, -, hbd, hcard⟩ := hpoly F0 hF0
  rw [hret] at hcard
  set P1 := toC p.1 with hP1def
  set P2 := toC p.2 with hP2def
  have hP12 : P1 ≠ P2 := toC.injective.ne hs.2.2.1
  -- the third vertex of the cap triangle
  have hc : ((S.erase P1).erase P2).card = 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hP12.symm, hP2⟩),
      Finset.card_erase_of_mem hP1, hcard]
  obtain ⟨Y, hYeq⟩ := Finset.card_eq_one.1 hc
  have hYm : Y ∈ (S.erase P1).erase P2 := hYeq ▸ Finset.mem_singleton_self Y
  have hYS : Y ∈ S := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hYm)
  have hSeq : ∀ z ∈ S, z = P1 ∨ z = P2 ∨ z = Y := by
    intro z hz
    by_cases h1 : z = P1
    · exact Or.inl h1
    by_cases h2 : z = P2
    · exact Or.inr (Or.inl h2)
    have : z ∈ (S.erase P1).erase P2 := Finset.mem_erase.2 ⟨h2, Finset.mem_erase.2 ⟨h1, hz⟩⟩
    rw [hYeq] at this
    exact Or.inr (Or.inr (Finset.mem_singleton.1 this))
  -- the hull side is not a unit edge
  have hsideU : s(P1, P2) ∉ cUnitEdges X := by
    intro h; rw [cUnitEdges, mem_unitPairs, hP1def, hP2def, dist_toC] at h; exact hd h.2.2
  -- every port maps to `[P1, Y]` or `[Y, P2]`
  have key : ∀ e ∈ unitEdges X, IsPort X (Sum.inr p) e →
      Sym2.map toC e = s(P1, Y) ∨ Sym2.map toC e = s(Y, P2) := by
    intro e he hpe
    obtain ⟨-, -, hpe⟩ := hpe
    rw [if_neg hd] at hpe
    obtain ⟨F, hF, hb⟩ := hpe
    rw [huniq F hF, hbd] at hb
    obtain ⟨⟨a, b⟩, hab, hab'⟩ := Finset.mem_image.1 hb
    obtain ⟨-, ha, hb2, hne, -⟩ := Finset.mem_filter.1 hab
    rw [← hab']
    refine sym2_cases_of_three (hSeq a ha) (hSeq b hb2) hne fun h => hsideU ?_
    rw [← h, hab']
    exact map_mem_cUnitEdges he
  -- the two ports
  have hpd := hdeg hfm X hX p hp
  rw [hret, portDeg] at hpd
  obtain ⟨e1, e2, h12, hE⟩ := Finset.card_eq_two.1 hpd
  have hmem : ∀ e, e = e1 ∨ e = e2 → e ∈ unitEdges X ∧ IsPort X (Sum.inr p) e := by
    intro e he
    have : e ∈ (unitEdges X).filter (IsPort X (Sum.inr p)) := by
      rw [hE]; rcases he with rfl | rfl <;> simp
    exact Finset.mem_filter.1 this
  have hinj : Sym2.map toC e1 ≠ Sym2.map toC e2 := (Sym2.map.injective toC.injective).ne h12
  have hA : ∃ e ∈ unitEdges X, IsPort X (Sum.inr p) e ∧ Sym2.map toC e = s(P1, Y) := by
    obtain ⟨he1, hp1⟩ := hmem e1 (Or.inl rfl)
    obtain ⟨he2, hp2⟩ := hmem e2 (Or.inr rfl)
    rcases key e1 he1 hp1 with h | h
    · exact ⟨e1, he1, hp1, h⟩
    rcases key e2 he2 hp2 with h' | h'
    · exact ⟨e2, he2, hp2, h'⟩
    · exact absurd (h.trans h'.symm) hinj
  have hB : ∃ e ∈ unitEdges X, IsPort X (Sum.inr p) e ∧ Sym2.map toC e = s(Y, P2) := by
    obtain ⟨he1, hp1⟩ := hmem e1 (Or.inl rfl)
    obtain ⟨he2, hp2⟩ := hmem e2 (Or.inr rfl)
    rcases key e1 he1 hp1 with h | h
    · rcases key e2 he2 hp2 with h' | h'
      · exact absurd (h.trans h'.symm) hinj
      · exact ⟨e2, he2, hp2, h'⟩
    · exact ⟨e1, he1, hp1, h⟩
  -- the third vertex is a point of `X`
  obtain ⟨x, hxX, rfl⟩ := Finset.mem_image.1 (hSV hYS)
  obtain ⟨eA, heA, hpA, hA'⟩ := hA
  obtain ⟨eB, heB, hpB, hB'⟩ := hB
  have hinjm := Sym2.map.injective toC.injective
  have hA2 : eA = s(p.1, x) := hinjm (by rw [hA']; rfl)
  have hB2 : eB = s(x, p.2) := hinjm (by rw [hB']; rfl)
  subst hA2 hB2
  refine ⟨x, ?_, hpA, hpB⟩
  refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hvX, Finset.mem_product.2 ⟨hxX, hwX⟩⟩,
    hs, (mem_unitEdges.1 heA).2.2, (mem_unitEdges.1 heB).2.2, hgt⟩

/-- **`Btwo` is small** (Verification Guide §10).  For every cutoff fraction `a > 0` and every
`ε > 0`, eventually at most `ε D` two-edge hull returns have no short port at the cutoff `a D`. -/
theorem twoReturnsNoShort_small (ε : ℝ) (hε : 0 < ε) {a : ℝ} (ha : 0 < a) :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      (twoReturnsNoShort X (a * diam X) : ℝ) ≤ ε * diam X := by
  filter_upwards [short_two_edge_sources ε hε, exists_twoEdgeReturn_ports,
    eventually_rpow_le_mul_diam ha] with n hsrc htwo hDa hfm X hX htri
  refine le_trans ?_ (hsrc hfm X hX htri)
  rw [twoReturnsNoShort]
  set A := (ccwHullSides X).filter
    (fun p => returnLength X p.1 p.2 = 2 ∧ shortDeg X (a * diam X) (Sum.inr p) = 0)
  have hex : ∀ p ∈ A, ∃ x, (p.1, x, p.2) ∈ twoEdgeReturns X ∧ IsPort X (Sum.inr p) s(p.1, x) ∧
      IsPort X (Sum.inr p) s(x, p.2) := fun p hp =>
    htwo hfm X hX p (Finset.mem_filter.1 hp).1 (Finset.mem_filter.1 hp).2.1
  choose! xf hxf using hex
  refine Nat.cast_le.2 (Finset.card_le_card_of_injOn (fun p => (p.1, xf p, p.2)) ?_ ?_)
  · intro p hp
    obtain ⟨hT, hp1, hp2⟩ := hxf p hp
    have h0 := (Finset.mem_filter.1 hp).2.2
    have hT' := Finset.mem_filter.1 hT
    have he1 : s(p.1, xf p) ∈ unitEdges X :=
      mem_unitEdges.2 ⟨(Finset.mem_product.1 hT'.1).1,
        (Finset.mem_product.1 (Finset.mem_product.1 hT'.1).2).1, hT'.2.2.1⟩
    have he2 : s(xf p, p.2) ∈ unitEdges X :=
      mem_unitEdges.2 ⟨(Finset.mem_product.1 (Finset.mem_product.1 hT'.1).2).1,
        (Finset.mem_product.1 (Finset.mem_product.1 hT'.1).2).2, hT'.2.2.2.1⟩
    refine Finset.mem_filter.2 ⟨hT, ?_, ?_⟩
    · exact (hDa X hX).trans (le_srcLen_of_not_short hX.1.2 htri h0 he1 hp1)
    · exact (hDa X hX).trans (le_srcLen_of_not_short hX.1.2 htri h0 he2 hp2)
  · intro p _ q _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 h.2.2

end Erdos99

end

end ReturnBudgets
