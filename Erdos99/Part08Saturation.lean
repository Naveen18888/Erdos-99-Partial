module

public import Mathlib
public import Erdos99.Part01Basics
public import Erdos99.Part04RoundnessAndConnectivity
public import Erdos99.Part05FacesAndShores
public import Erdos99.Part06TokensHopsCaps
public import Erdos99.Part07StabilityAndCharging

/-!
# Erdős Problem 99 under finite multiplicity — Part 8 of 9: HH-adjacency, one-short faces and saturation

This is one of the supporting files of the formalization; the main theorem and a precise
description of what is proved are at the top of `Erdos99.lean`.

The file is divided into the following sections (each `section Name … end Name`); comments
elsewhere in the development refer to these sections by name.

* `FaceClosure`
* `ChargingResidual`
* `HHAdjacencyAlgebra`
* `HopMargin`
* `HHAdjacencyGeometry`
* `HHAdjacency`
* `CapReflection`
* `OneShortAlgebra`
* `OneShortGeometry`
* `SaturationHop`
* `CaplessGeometry`
* `SaturationProcess`
* `SaturationCount`
* `SaturationLabels`
* `SaturationMarks`
* `SaturationMarked`
* `SaturationWindow`
* `Saturation`
* `OneShortCap`
* `CaplessComponents`
* `CaplessElim`
* `CaplessPoly`
-/

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `FaceClosure`
-/

section FaceClosure

/-!
# The closure equation of a face (Verification Guide §§12–13, geometric reduction)

Every response equation of §§12–13 starts from the closure of a face: the counterclockwise side
vectors of a bounded face of the unit-distance graph sum to zero.  This file proves it for the
oriented sides `orientedSides X F` used throughout (`markedSum`, `IsLabelled`):

* `orientedSides_eq_image`: the oriented sides of a polygon face `F = int conv S` are the pairs
  `(v i, v (i + 1))`, `i < |S|`, of a cyclic enumeration `v` of `S`;
* `card_orientedSides`: an exceptional face has exactly `faceSize X F` oriented sides;
* `orientedSides_sum_eq_zero`: **closure**, `∑_{(a, b)} (b - a) = 0`.
-/

open scoped BigOperators Real
open EstablishedExternalResults Set Complex Filter Topology

@[expose] public noncomputable section

open Classical

namespace Erdos99

/-- The oriented sides of a polygon face `F = int conv S` (with `bdryEdges = cSides S`) are the
consecutive pairs of a cyclic enumeration of `S`. -/
lemma orientedSides_eq_image {X : Finset Plane} {F : Set ℂ} {S : Finset ℂ} (hSV : S ⊆ cVerts X)
    (hFint : F = interior (convexHull ℝ (S : Set ℂ))) (hbd : bdryEdges (cUnitEdges X) F = cSides S)
    (hne : F.Nonempty) {v : ℕ → ℂ} (hper : ∀ i, v (i + S.card) = v i) (hvS : ∀ i, v i ∈ S)
    (hside : ∀ a b, IsCSide S a b ↔ ∃ i, v i = a ∧ v (i + 1) = b) :
    orientedSides X F = (Finset.range S.card).image (fun i => (v i, v (i + 1))) := by
  have hmod := periodic_mod hper
  ext ⟨a, b⟩
  constructor
  · intro h
    obtain ⟨i, hi1, hi2⟩ := (hside a b).1 (isCSide_of_mem_orientedSides hFint hbd hne h)
    have hk : 0 < S.card := by
      obtain ⟨z, hz⟩ := hne
      rw [hFint] at hz
      have : (S : Set ℂ).Nonempty := by
        by_contra h0
        rw [Set.not_nonempty_iff_eq_empty] at h0
        rw [h0, convexHull_empty, interior_empty] at hz
        exact hz
      exact Finset.card_pos.2 (Finset.coe_nonempty.1 this)
    refine Finset.mem_image.2 ⟨i % S.card, Finset.mem_range.2 (Nat.mod_lt _ hk), ?_⟩
    have h2 : v (i % S.card + 1) = v (i + 1) := by
      rw [← hmod (i % S.card + 1), Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, hmod]
    rw [hmod, h2, hi1, hi2]
  · intro h
    obtain ⟨i, -, hi⟩ := Finset.mem_image.1 h
    simp only [Prod.mk.injEq] at hi
    obtain ⟨rfl, rfl⟩ := hi
    have hs : IsCSide S (v i) (v (i + 1)) := (hside _ _).2 ⟨i, rfl, rfl⟩
    refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hSV (hvS i), hSV (hvS (i + 1))⟩, ?_, ?_⟩
    · rw [hbd]
      exact Finset.mem_image.2 ⟨(v i, v (i + 1)),
        Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hs.1, hs.2.1⟩, hs⟩, rfl⟩
    · intro z hz
      exact side_pos hs (hFint ▸ hz)

/-- The oriented sides of an exceptional face and a cyclic enumeration of its vertices. -/
lemma exists_cyclic_orientedSides :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ∀ F ∈ exceptionalFaces X,
      ∃ v : ℕ → ℂ, (∀ i, v (i + faceSize X F) = v i) ∧
        Set.InjOn v (Set.Iio (faceSize X F)) ∧
        orientedSides X F = (Finset.range (faceSize X F)).image (fun i => (v i, v (i + 1))) := by
  filter_upwards [contactFace_polygon] with n hpoly hfm X hX F hF
  obtain ⟨S, hSV, h3, hext, hFint, hbd, hsize⟩ := hpoly hfm X hX F hF.1
  have hne : F.Nonempty := by
    obtain ⟨x, hx, rfl⟩ := mem_faces_iff.1 hF.1.1
    exact ⟨x, mem_connectedComponentIn hx⟩
  have hint : (interior (convexHull ℝ (S : Set ℂ))).Nonempty := hFint ▸ hne
  obtain ⟨v, hper, hvS, hinj, hside⟩ := PolyCycle.exists_cyclic_enum hext hint
  rw [hsize]
  exact ⟨v, hper, hinj, orientedSides_eq_image hSV hFint hbd hne hper hvS hside⟩

/-- An exceptional face has exactly `faceSize X F` oriented sides. -/
theorem card_orientedSides :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ∀ F ∈ exceptionalFaces X,
      (orientedSides X F).card = faceSize X F := by
  filter_upwards [exists_cyclic_orientedSides] with n h hfm X hX F hF
  obtain ⟨v, -, hinj, heq⟩ := h hfm X hX F hF
  rw [heq, Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj hij
  simp only [Prod.mk.injEq] at hij
  exact hinj (Set.mem_Iio.2 (Finset.mem_range.1 hi)) (Set.mem_Iio.2 (Finset.mem_range.1 hj)) hij.1

/-- **Closure of a face.**  The counterclockwise side vectors of an exceptional face sum to
zero. -/
theorem orientedSides_sum_eq_zero :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ∀ F ∈ exceptionalFaces X,
      ∑ ab ∈ orientedSides X F, (ab.2 - ab.1) = 0 := by
  filter_upwards [exists_cyclic_orientedSides] with n h hfm X hX F hF
  obtain ⟨v, hper, hinj, heq⟩ := h hfm X hX F hF
  rw [heq, Finset.sum_image]
  · rw [Finset.sum_range_sub (fun i => v i), ← zero_add (faceSize X F), hper, sub_self]
  · intro i hi j hj hij
    simp only [Prod.mk.injEq] at hij
    exact hinj (Set.mem_Iio.2 (Finset.mem_range.1 hi)) (Set.mem_Iio.2 (Finset.mem_range.1 hj))
      hij.1

end Erdos99

end

end FaceClosure

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `ChargingResidual`
-/

section ChargingResidual

/-!
# The components of the residual charging statement (Verification Guide §§10–13)

This file splits the residual charging statement `charging_tracks_residual`
(`ChargingCutoff`) into its independent mathematical components.

**Interface.**

* `markedSum X F S`: the sum of the counterclockwise side vectors of the face `F` (face on the
  left) over its sides in `S`;
* `IsLabelled X tol G mk` (output of §10): every good face carries a source label, a unit hull
  side; the labels are injective, the marked side vectors of `F` sum to `k τ` up to `tol` (`τ` the
  direction of the label, `k = 2` at hexagons and `k = 1` at pentagons, ordinary or activated), and
  `F` lies within `tol · D` of its label (boundary layer);
* `NoIntermediatePorts X L Λ G` (§4.1, §11.3): no good face has a port on a track whose length lies
  in `[L, Λ)`;
* `IsSaturated` = both;
* `flaggedFaces X O L λ θ δ G`: the good faces having a flagged port on a track with at least `L`
  rhombi (the maximal admissible flagged set);
* `LocalExclusion η Q`: the uniform form of a local exclusion estimate of §13: for every `ε, λ, θ,
  δ > 0` there are a saturation tolerance and a cutoff fraction `a₀` such that for every cutoff
  fraction `a ≤ a₀` the quantity `Q` (evaluated with the maximal flagged set) is eventually at most
  `ε D` for all saturated markings.

**Components.**

* `saturation_core` (§10): saturated faces with labels, marking, degree window and small
  budgets at any fixed cutoff fraction.  Its hull-return budgets `Bunit`, `Btwo` are **proved**
  (`unitReturnsNoShort_small`, `twoReturnsNoShort_small` in `ReturnBudgets`, from the
  short-source theorems); the face part `saturation_faces` is **proved** in `Saturation`;
* `omit_intermediate` (**proved**, §11.3): omitting the good faces with an intermediate port costs at
  most `12 N` in `Bface` (`N` intermediate tracks) and creates no unit or marked stubs;
* `saturation_exists` (**proved** from the two above): the shell density `κ = ε / 24`;
* the five local exclusion estimates: `hh_edges_few` (§13.1, **proved** in `HHAdjacency`),
  `defective_J_few` (§13.2) and `exceptional_JJ_few` (§13.3) (in `FlaggedExclusion`, with a
  centre of two-sided roundness; their algebraic steps are **proved**), `capless_small_few`
  (§13.4, proved in `CaplessSmall`) and `oneShort_H_stubs_few` (§13.5, **proved** in `OneShortCap`, with an
  additive term of twice the number of intermediate tracks);
* monotonicity facts used in the assembly (**proved**): `IsSaturated.mono_tol`,
  `StubGraph.defJ_antitone`, `StubGraph.excE_antitone`.

The assembly `charging_tracks_residual` is in `ChargingCutoff`.

The common engine of the five local exclusion estimates, the approximate-to-exact step of §12.4
and its counting form §12.5, is proved: `DirectionPinning.near_roots_of_small_eval` and
`pinned_directions_few` (`DirectionPinning`, `PinnedCount`).  The algebraic identities of
§§12.1–12.3, 13.1 and 13.5 are in `QuadraticResponseAlgebra` and `QuadraticResponseH1`;
the algebraic cores of §§13.2–13.4 and of the loop cases (the quantitative margin of a constant
coefficient, the failure of the unit condition at a `J` receiver, the nonzero cubic coefficient of
(H1) at adjacent `J` faces, the failure of the closure relation of a capless component) are in
`QuadraticResponseJ`, and `PinnedPolys` restates the counting engine for explicit
polynomials (`pinned_polys_few`) with ready-made counting statements for the cap polynomial (H2)
and the `H`/`J` loop polynomials.
The first steps of the geometric reduction are proved: the closure of a face
(`orientedSides_sum_eq_zero`, `FaceClosure`), the resulting approximate response equation at a
labelled face (`IsLabelled.response`: `‖k τ + Σ_{unmarked sides} (b - a)‖ ≤ tol`) and track
translation (`sameDir_otherEnd`: the two ends of a track carry parallel side vectors).
What each local exclusion estimate still needs is the rest of the geometric reduction of the actual
configuration to these algebraic statements (the response equations at the faces of a pattern,
with errors controlled by the saturation tolerance and the cutoff fraction) and the clustering of
the coefficient data into boundedly many centres.
-/

open scoped BigOperators Real
open Filter

@[expose] public noncomputable section

open Classical

namespace Erdos99

open LocalCharge

/-! ## The saturation interface -/

/-- The sum of the counterclockwise side vectors `b - a` of the face `F` (the face lies to the left
of `a → b`) over the sides whose edge belongs to `S`. -/
def markedSum (X : Finset Plane) (F : Set ℂ) (S : Finset (Sym2 Plane)) : ℂ :=
  ∑ ab ∈ (orientedSides X F).filter (fun ab => ∃ e ∈ S, Sym2.map toC e = s(ab.1, ab.2)),
    (ab.2 - ab.1)

/-- The multiplicity `k` of the marked tangent at a good face: two at a hexagon, one at an
(ordinary or activated) pentagon. -/
def GoodFaces.markMult {X : Finset Plane} (G : GoodFaces X) (F : Set ℂ) : ℂ :=
  if F ∈ G.hex then 2 else 1

/-- **Source labels** (Verification Guide §10, output of saturation): an injective choice of a unit
hull side `lab F` (a source) for every good face `F`, such that the marked side vectors of `F` sum
to `k τ` up to `tol`, where `τ` is the unit direction of `lab F` and `k = markMult F`, and all
vertices of `F` lie within `tol · D` of the start of `lab F`. -/
def IsLabelled (X : Finset Plane) (tol : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane)) :
    Prop :=
  ∃ lab : Set ℂ → Plane × Plane, Set.InjOn lab G.good ∧ ∀ F ∈ G.good,
    lab F ∈ unitHullSides X ∧
    ‖markedSum X F (mk F) - G.markMult F * toC (sideDir (lab F))‖ ≤ tol ∧
    ∀ ab ∈ orientedSides X F, ‖ab.1 - toC (lab F).1‖ ≤ tol * diam X

/-- **The approximate response equation at a labelled face** (geometric reduction of §§12–13).
By closure (`orientedSides_sum_eq_zero`), the unmarked side vectors of a good face `F` sum to minus
its marked sum; with the source label of tolerance `tol` this gives
`‖k τ + Σ_{unmarked sides} (b - a)‖ ≤ tol`, where `τ` is the direction of the label and
`k = markMult F`. -/
theorem IsLabelled.response :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      ∀ (tol : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane)),
        IsLabelled X tol G mk → ∃ lab : Set ℂ → Plane × Plane, Set.InjOn lab G.good ∧
          ∀ F ∈ G.good, lab F ∈ unitHullSides X ∧
            ‖G.markMult F * toC (sideDir (lab F)) +
              ∑ ab ∈ (orientedSides X F).filter
                (fun ab => ¬ ∃ e ∈ mk F, Sym2.map toC e = s(ab.1, ab.2)), (ab.2 - ab.1)‖ ≤ tol := by
  filter_upwards [orientedSides_sum_eq_zero] with n hclo hfm X hX tol G mk hlab
  obtain ⟨lab, hinj, hl⟩ := hlab
  refine ⟨lab, hinj, fun F hF => ⟨(hl F hF).1, ?_⟩⟩
  have h0 := hclo hfm X hX F (((mem_exceptionalFinset hX.1.2).1 (G.good_subset hF)))
  rw [← Finset.sum_filter_add_sum_filter_not (orientedSides X F)
    (fun ab => ∃ e ∈ mk F, Sym2.map toC e = s(ab.1, ab.2))] at h0
  have h1 : ∑ ab ∈ (orientedSides X F).filter
      (fun ab => ¬ ∃ e ∈ mk F, Sym2.map toC e = s(ab.1, ab.2)), (ab.2 - ab.1) =
      - markedSum X F (mk F) := by
    rw [markedSum]; linear_combination h0
  rw [h1, ← sub_eq_add_neg, ← norm_neg, neg_sub]
  exact (hl F hF).2.1

/-- The edges of one (possibly rhombus-free) track are parallel. -/
lemma sameDir_of_mem_allTrackOf {X : Finset Plane} {e f : Sym2 Plane} (he : e ∈ unitEdges X)
    (hf : f ∈ allTrackOf X e) : SameDir e f := by
  by_cases hr : e ∈ rhombusEdges X
  · rw [allTrackOf_of_mem_rhombusEdges hr] at hf
    exact sameDir_of_mem_tracks (Finset.mem_image_of_mem _ hr) (mem_trackOf_self hr) hf
  · rw [allTrackOf_of_not_mem he hr, Finset.mem_singleton] at hf
    rw [hf]; exact SameDir.refl e

/-- **Track translation** (geometric reduction of §§12–13): the port at the other end of the track
through a port `e` of an exceptional face is parallel to `e`.  In particular the two ends of every
edge of the track graph, and of every stub with its cap, carry parallel unit side vectors. -/
lemma sameDir_otherEnd {X : Finset Plane}
    (hends : ∀ T ∈ allTracks X, (trackEnds X T).card = 2) {F : Set ℂ} {e : Sym2 Plane}
    (hF : F ∈ exceptionalFinset X) (he : e ∈ unitEdges X) (hp : IsPort X (Sum.inl F) e) :
    SameDir e (otherEnd X (F, e)).2 := by
  obtain ⟨hT, -⟩ := trackEnds_eq_otherEnd hends hF he hp
  have hmem : otherEnd X (F, e) ∈ trackEnds X (allTrackOf X e) := by rw [hT]; simp
  exact sameDir_of_mem_allTrackOf he (Finset.mem_product.1 (Finset.mem_filter.1 hmem).1).2

/-- No good face has a port whose track has length in the intermediate range `[L, Λ)`. -/
def NoIntermediatePorts (X : Finset Plane) (L Λ : ℝ) (G : GoodFaces X) : Prop :=
  ∀ F ∈ G.good, ∀ e ∈ unitEdges X, IsPort X (Sum.inl F) e →
    (trackLength X (allTrackOf X e) : ℝ) < L ∨ Λ ≤ trackLength X (allTrackOf X e)

/-- **Saturated good faces** for the cutoff `L` and the macroscopic scale `Λ`: no intermediate
ports, and source labels with tolerance `tol`. -/
def IsSaturated (X : Finset Plane) (L Λ tol : ℝ) (G : GoodFaces X)
    (mk : Set ℂ → Finset (Sym2 Plane)) : Prop :=
  NoIntermediatePorts X L Λ G ∧ IsLabelled X tol G mk

lemma IsLabelled.mono_tol {X : Finset Plane} {tol tol' : ℝ} {G : GoodFaces X}
    {mk : Set ℂ → Finset (Sym2 Plane)} (h : IsLabelled X tol G mk) (ht : tol ≤ tol')
    (hD : 0 ≤ diam X) : IsLabelled X tol' G mk := by
  obtain ⟨lab, hinj, hlab⟩ := h
  refine ⟨lab, hinj, fun F hF => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hlab F hF
  exact ⟨h1, h2.trans ht, fun ab hab => (h3 ab hab).trans (mul_le_mul_of_nonneg_right ht hD)⟩

lemma IsSaturated.mono_tol {X : Finset Plane} {L Λ tol tol' : ℝ} {G : GoodFaces X}
    {mk : Set ℂ → Finset (Sym2 Plane)} (h : IsSaturated X L Λ tol G mk) (ht : tol ≤ tol')
    (hD : 0 ≤ diam X) : IsSaturated X L Λ tol' G mk :=
  ⟨h.1, h.2.mono_tol ht hD⟩

/-- **The flagged faces**: the good faces with a flagged port (`IsFlaggedPort`) on a track with at
least `L` rhombi.  This is the largest set of faces admissible as the flagged set. -/
def flaggedFaces (X : Finset Plane) (O : Plane) (L lam θ δ : ℝ) (G : GoodFaces X) :
    Finset (Set ℂ) :=
  G.good.filter (fun F => ∃ T ∈ longTracks X L, IsFlaggedPort X O (diam X) lam θ δ F T)

lemma mem_flaggedFaces {X : Finset Plane} {O : Plane} {L lam θ δ : ℝ} {G : GoodFaces X}
    {F : Set ℂ} (hF : F ∈ flaggedFaces X O L lam θ δ G) :
    ∃ T ∈ longTracks X L, IsFlaggedPort X O (diam X) lam θ δ F T :=
  (Finset.mem_filter.1 hF).2

/-! ## Monotonicity of the pinned patterns in the flagged set -/

namespace LocalCharge.StubGraph

variable {α : Type*} (g : StubGraph α)

lemma qual_mono {V Fl Fl' : Finset α} (h : Fl ⊆ Fl') {v : α} (hq : g.Qual V Fl v) :
    g.Qual V Fl' v := by
  rcases hq with hq | hq
  · exact Or.inl (h hq)
  · right
    have : g.inc v (g.Hs V \ Fl') ≤ g.inc v (g.Hs V \ Fl) :=
      g.inc_mono v (Finset.sdiff_subset_sdiff (subset_refl _) h)
    omega

/-- More flagged faces give fewer defective `J` faces. -/
lemma defJ_antitone {V Fl Fl' : Finset α} (h : Fl ⊆ Fl') : g.defJ V Fl' ≤ g.defJ V Fl := by
  refine Finset.card_le_card fun v hv => ?_
  obtain ⟨hv, hnf, h2⟩ := Finset.mem_filter.1 hv
  refine Finset.mem_filter.2 ⟨hv, fun h' => hnf (h h'), h2.trans ?_⟩
  exact g.inc_mono v (Finset.sdiff_subset_sdiff (subset_refl _) h)

/-- More flagged faces give fewer exceptional `J–J` edges. -/
lemma excE_antitone {V Fl Fl' : Finset α} (h : Fl ⊆ Fl') : g.excE V Fl' ≤ g.excE V Fl := by
  refine Finset.card_le_card fun e he => ?_
  obtain ⟨he, h1, h2, h3, h4⟩ := Finset.mem_filter.1 he
  exact Finset.mem_filter.2 ⟨he, h1, h2, fun hq => h3 (g.qual_mono h hq),
    fun hq => h4 (g.qual_mono h hq)⟩

end LocalCharge.StubGraph

/-! ## Saturation (§10) and the omission of intermediate faces (§11.3) -/

/-- The omitted small exceptional faces: the pentagons and hexagons that are not good. -/
def GoodFaces.omittedSmall {X : Finset Plane} (G : GoodFaces X) : ℕ :=
  ((exceptionalFinset X).filter (fun F => faceSize X F ≤ 6 ∧ F ∉ G.good)).card

/-- **The omitted-face budget splits** into the high-face incidences and the omitted pentagons and
hexagons: `Bface ≤ Σ_{k ≥ 7} k f_k + 6 · #(omitted faces with at most six sides)`. -/
lemma GoodFaces.Bface_le {X : Finset Plane} (hX : IsSeparated X) (G : GoodFaces X) :
    G.Bface ≤ highIncidence X + 6 * G.omittedSmall := by
  have hfin := finite_exceptionalFaces hX
  have hE : exceptionalFinset X = hfin.toFinset := by rw [exceptionalFinset, dif_pos hfin]
  rw [GoodFaces.Bface, ← Finset.sum_filter_add_sum_filter_not _ (fun F => 7 ≤ faceSize X F),
    highIncidence_eq_sum hfin, GoodFaces.omittedSmall, ← hE]
  refine add_le_add ?_ ?_
  · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Nat.zero_le _)
    intro F hF
    simp only [Finset.mem_filter] at hF ⊢
    exact ⟨hF.1.1, hF.2⟩
  · rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    rw [Finset.filter_filter]
    refine (Finset.sum_le_sum (fun F hF => ?_)).trans (le_of_eq (Finset.sum_congr ?_ fun _ _ => rfl))
    · exact (by have := (Finset.mem_filter.1 hF).2.2; omega : faceSize X F ≤ 6)
    · ext F
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, by omega, h2⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h3, by omega⟩

/-- The good faces of `G` satisfying `P`. -/
def GoodFaces.restrict {X : Finset Plane} (G : GoodFaces X) (P : Set ℂ → Prop) : GoodFaces X where
  pent := G.pent.filter P
  hex := G.hex.filter P
  act := G.act.filter P
  pent_sub F hF := G.pent_sub F (Finset.mem_filter.1 hF).1
  hex_sub F hF := G.hex_sub F (Finset.mem_filter.1 hF).1
  act_sub F hF := G.act_sub F (Finset.mem_filter.1 hF).1
  disj := Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) G.disj

lemma GoodFaces.mem_restrict_good {X : Finset Plane} {G : GoodFaces X} {P : Set ℂ → Prop}
    {F : Set ℂ} : F ∈ (G.restrict P).good ↔ F ∈ G.good ∧ P F := by
  simp only [GoodFaces.good, GoodFaces.restrict, Finset.mem_union, Finset.mem_filter]
  tauto

lemma GoodFaces.restrict_good_subset {X : Finset Plane} (G : GoodFaces X) (P : Set ℂ → Prop) :
    (G.restrict P).good ⊆ G.good := fun _ hF => (GoodFaces.mem_restrict_good.1 hF).1

lemma GoodFaces.marks_restrict {X : Finset Plane} {G : GoodFaces X} {P : Set ℂ → Prop}
    {F : Set ℂ} (hP : P F) : (G.restrict P).marks F = G.marks F := by
  simp only [GoodFaces.marks, GoodFaces.restrict, Finset.mem_filter, hP, and_true]

lemma GoodFaces.markMult_restrict {X : Finset Plane} {G : GoodFaces X} {P : Set ℂ → Prop}
    {F : Set ℂ} (hP : P F) : (G.restrict P).markMult F = G.markMult F := by
  simp only [GoodFaces.markMult, GoodFaces.restrict, Finset.mem_filter, hP, and_true]

/-- Restricting the good faces creates no stubs ending at unit hull sides. -/
lemma stubsTo_restrict_unit {X : Finset Plane} {L : ℝ} {G : GoodFaces X} {P : Set ℂ → Prop}
    {mk : Set ℂ → Finset (Sym2 Plane)} :
    stubsTo X L (G.restrict P) mk (G.restrict P).good (UnitEnd X) ⊆
      stubsTo X L G mk G.good (UnitEnd X) := by
  intro q hq
  simp only [stubsTo, stubsAt, Finset.mem_filter] at hq ⊢
  obtain ⟨⟨hq, -, hV⟩, hK⟩ := hq
  obtain ⟨h1, h2, h3⟩ := mem_unmarkedPorts.1 hq
  have hG := G.restrict_good_subset P h1
  refine ⟨⟨mem_unmarkedPorts.2 ⟨hG, h2, h3⟩, ?_, G.restrict_good_subset P hV⟩, hK⟩
  rintro ⟨hl, -⟩
  obtain ⟨p, hp, -⟩ := hK
  rw [hp] at hl
  exact Sum.inr_ne_inl hl

/-- Restricting the good faces creates no stubs ending at marked ports. -/
lemma stubsTo_restrict_marked {X : Finset Plane} {L : ℝ} {G : GoodFaces X} {P : Set ℂ → Prop}
    {mk : Set ℂ → Finset (Sym2 Plane)} :
    stubsTo X L (G.restrict P) mk (G.restrict P).good (MarkedEnd (G.restrict P) mk) ⊆
      stubsTo X L G mk G.good (MarkedEnd G mk) := by
  intro q hq
  simp only [stubsTo, stubsAt, Finset.mem_filter] at hq ⊢
  obtain ⟨⟨hq, -, hV⟩, hK⟩ := hq
  obtain ⟨h1, h2, h3⟩ := mem_unmarkedPorts.1 hq
  obtain ⟨F', hF', hG', hmk'⟩ := hK
  refine ⟨⟨mem_unmarkedPorts.2 ⟨G.restrict_good_subset P h1, h2, h3⟩, ?_,
    G.restrict_good_subset P hV⟩, ⟨F', hF', G.restrict_good_subset P hG', hmk'⟩⟩
  rintro ⟨-, hm⟩
  have hmate : trackMate X q = (F', (otherEnd X q).2) := by
    simp only [trackMate, hF', nodeFace, Sum.elim_inl, id]
  rw [hmate] at hm
  exact (mem_unmarkedPorts.1 hm).2.2 hmk'

/-- **Omitting the faces with intermediate ports** (Verification Guide §11.3).  Given good faces
with a marking, the degree window and source labels at a positive cutoff `L`, the good faces
without ports on tracks of length in `[L, Λ)` are saturated; the omitted faces have at most
`12 N` sides in total (`N` the number of intermediate tracks: each has two ends, and a good face has
at most six sides), and no new stubs end at unit hull sides or marked ports. -/
theorem omit_intermediate {X : Finset Plane} (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X)
    (hends : ∀ T ∈ allTracks X, (trackEnds X T).card = 2) {L Λ tol : ℝ} (hL : 0 < L)
    {G : GoodFaces X} {mk : Set ℂ → Finset (Sym2 Plane)} (hmk : IsMarking X L G mk)
    (hwin : DegreeWindow X L G) (hlab : IsLabelled X tol G mk) :
    ∃ G' : GoodFaces X, IsMarking X L G' mk ∧ DegreeWindow X L G' ∧ IsSaturated X L Λ tol G' mk ∧
      (G'.Bface : ℝ) ≤ G.Bface + 12 * ((longTracks X L \ longTracks X Λ).card : ℝ) ∧
      ((stubsTo X L G' mk G'.good (UnitEnd X)).card +
          (stubsTo X L G' mk G'.good (MarkedEnd G' mk)).card : ℝ) ≤
        (stubsTo X L G mk G.good (UnitEnd X)).card +
          (stubsTo X L G mk G.good (MarkedEnd G mk)).card := by
  set P : Set ℂ → Prop := fun F => ∀ e ∈ unitEdges X, IsPort X (Sum.inl F) e →
    (trackLength X (allTrackOf X e) : ℝ) < L ∨ Λ ≤ trackLength X (allTrackOf X e) with hPdef
  set G' := G.restrict P with hG'
  have hmem : ∀ {F}, F ∈ G'.good ↔ F ∈ G.good ∧ P F := GoodFaces.mem_restrict_good
  refine ⟨G', ?_, ?_, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro F hF
    obtain ⟨hF, hP⟩ := hmem.1 hF
    rw [GoodFaces.marks_restrict hP]; exact hmk F hF
  · intro F hF
    obtain ⟨hF, hP⟩ := hmem.1 hF
    rw [GoodFaces.marks_restrict hP]; exact hwin F hF
  · intro F hF
    exact (hmem.1 hF).2
  · obtain ⟨lab, hinj, hl⟩ := hlab
    refine ⟨lab, hinj.mono fun F hF => (hmem.1 hF).1, fun F hF => ?_⟩
    obtain ⟨hF, hP⟩ := hmem.1 hF
    rw [GoodFaces.markMult_restrict hP]
    exact hl F hF
  · -- the omitted faces
    set R := G.good.filter (fun F => ¬ P F) with hR
    have hsplit : (exceptionalFinset X).filter (fun F => F ∉ G'.good) =
        (exceptionalFinset X).filter (fun F => F ∉ G.good) ∪ R := by
      ext F
      simp only [Finset.mem_filter, Finset.mem_union, hR, hmem]
      constructor
      · rintro ⟨hF, h⟩
        by_cases hg : F ∈ G.good
        · exact Or.inr ⟨hg, fun hP => h ⟨hg, hP⟩⟩
        · exact Or.inl ⟨hF, hg⟩
      · rintro (⟨hF, h⟩ | ⟨hg, hP⟩)
        · exact ⟨hF, fun h' => h h'.1⟩
        · exact ⟨G.good_subset hg, fun h' => hP h'.2⟩
    have hdisj : Disjoint ((exceptionalFinset X).filter (fun F => F ∉ G.good)) R := by
      rw [Finset.disjoint_left]
      intro F h1 h2
      exact (Finset.mem_filter.1 h1).2 (Finset.mem_filter.1 h2).1
    have hBf : G'.Bface = G.Bface + ∑ F ∈ R, faceSize X F := by
      rw [GoodFaces.Bface, GoodFaces.Bface, hsplit, Finset.sum_union hdisj]
    -- every omitted face has at most six sides
    have hsize : ∀ F ∈ G.good, faceSize X F ≤ 6 := by
      intro F hF
      simp only [GoodFaces.good, Finset.mem_union] at hF
      rcases hF with (h | h) | h
      · rw [(G.pent_sub F h).2]; norm_num
      · rw [(G.hex_sub F h).2]
      · rw [(G.act_sub F h).2]; norm_num
    have hsum : ∑ F ∈ R, faceSize X F ≤ 6 * R.card := by
      rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_le_sum fun F hF => hsize F (Finset.mem_filter.1 hF).1
    -- every omitted face is an end of an intermediate track
    set I := longTracks X L \ longTracks X Λ with hI
    have hport : ∀ F ∈ R, ∃ e, e ∈ unitEdges X ∧ IsPort X (Sum.inl F) e ∧
        allTrackOf X e ∈ I := by
      intro F hF
      obtain ⟨hFg, hP⟩ := Finset.mem_filter.1 hF
      simp only [hPdef, not_forall, not_or, not_lt, not_le] at hP
      obtain ⟨e, he, hpe, hLe, hΛe⟩ := hP
      refine ⟨e, he, hpe, Finset.mem_sdiff.2 ⟨?_, ?_⟩⟩
      · rw [longTracks_eq_filter_allTracks hX htri hL]
        exact Finset.mem_filter.2 ⟨allTrackOf_mem_allTracks he, hLe⟩
      · intro h
        exact absurd (Finset.mem_filter.1 h).2 (not_le.2 hΛe)
    choose! ep hep using hport
    have hRcard : R.card ≤ 2 * I.card := by
      have h1 : R.card ≤ (I.biUnion (trackEnds X)).card := by
        refine Finset.card_le_card_of_injOn (fun F => (Sum.inl F, ep F)) ?_ ?_
        · intro F hF
          obtain ⟨he, hpe, hI'⟩ := hep F hF
          refine Finset.mem_biUnion.2 ⟨_, hI', mem_trackEnds.2 ⟨?_, mem_allTrackOf_self he, hpe⟩⟩
          exact Finset.mem_union_left _ (Finset.mem_map_of_mem _
            (G.good_subset (Finset.mem_filter.1 hF).1))
        · intro F _ F' _ h
          simpa using congrArg Prod.fst h
      have h2 : (I.biUnion (trackEnds X)).card ≤ ∑ T ∈ I, (trackEnds X T).card :=
        Finset.card_biUnion_le
      have h3 : ∑ T ∈ I, (trackEnds X T).card = ∑ _T ∈ I, 2 := by
        refine Finset.sum_congr rfl fun T hT => hends T ?_
        exact tracks_subset_allTracks X (Finset.mem_filter.1 (Finset.mem_sdiff.1 hT).1).1
      rw [h3, Finset.sum_const, smul_eq_mul, mul_comm] at h2
      omega
    have : G'.Bface ≤ G.Bface + 12 * I.card := by omega
    exact_mod_cast this
  · have h1 := Finset.card_le_card (stubsTo_restrict_unit (X := X) (L := L) (G := G) (P := P)
      (mk := mk))
    have h2 := Finset.card_le_card (stubsTo_restrict_marked (X := X) (L := L) (G := G) (P := P)
      (mk := mk))
    exact_mod_cast add_le_add h1 h2

/-! ## The local exclusion estimates (§§12–13) -/

/-- A quantity attached to a configuration, a cutoff, good faces, a marking and a flagged set. -/
abbrev ChargeQuantity : Type :=
  (X : Finset Plane) → ℝ → (G : GoodFaces X) → (Set ℂ → Finset (Sym2 Plane)) → Finset (Set ℂ) → ℝ

/-- **The uniform form of a local exclusion estimate** (Verification Guide §§11.2, 12, 13): for
every `ε, λ, θ, δ > 0` there are a saturation tolerance `tol > 0` and a cutoff fraction `a₀ > 0`
such that for every cutoff fraction `0 < a ≤ a₀`, eventually, for every admissible configuration,
every centre `O` of a disc of radius `D/2 + η D` containing it and all saturated good faces with a
marking and the degree window at the cutoff `a D`, the quantity `Q` evaluated with the flagged
faces for `λ, θ, δ` is at most `ε D`. -/
def LocalExclusion (η : ℝ) (Q : ChargeQuantity) : Prop :=
  ∀ ε, 0 < ε → ∀ lam, 0 < lam → ∀ θ δ : ℝ, 0 < θ → 0 < δ →
    ∃ tol, 0 < tol ∧ ∃ a₀, 0 < a₀ ∧ ∀ a, 0 < a → a ≤ a₀ →
      ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
        ∀ O : Plane, (∀ x ∈ X, dist x O ≤ diam X / 2 + η * diam X) →
        ∀ (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane)), IsMarking X (a * diam X) G mk →
          DegreeWindow X (a * diam X) G → IsSaturated X (a * diam X) (lam * diam X) tol G mk →
          Q X (a * diam X) G mk (flaggedFaces X O (a * diam X) lam θ δ G) ≤ ε * diam X

/-- Twice the number of `H–H` edges of the track graph. -/
def qHH : ChargeQuantity := fun X L G mk _ =>
  2 * ((trackGraph X L G mk).eIn ((trackGraph X L G mk).Hs G.good)
    ((trackGraph X L G mk).Hs G.good) : ℝ)

/-- The stubs at degree-two faces whose track ends at a two-edge return with one short port. -/
def qOneShort : ChargeQuantity := fun X L G mk _ =>
  ((stubsTo X L G mk ((trackGraph X L G mk).Hs G.good) (OneShortEnd X L)).card : ℝ)

/-- The capless components with at most `M` faces, in `G` and in `K`. -/
def qCapless (M : ℕ) : ChargeQuantity := fun X L G mk _ =>
  ((trackGraph X L G mk).stublessSmall ((trackGraph X L G mk).Gs G.good) M +
    (trackGraph X L G mk).stublessSmall ((trackGraph X L G mk).Ks G.good) M : ℝ)

/-- Four times the number of defective `J` faces. -/
def qDefJ : ChargeQuantity := fun X L G mk Fl => 4 * ((trackGraph X L G mk).defJ G.good Fl : ℝ)

/-- The exceptional `J–J` edges. -/
def qExcE : ChargeQuantity := fun X L G mk Fl => ((trackGraph X L G mk).excE G.good Fl : ℝ)

/- The estimate `hh_edges_few` (`H–H` adjacency is pinned, Verification Guide §13.1, identity (H1))
is stated and proved from its geometric inputs in `HHAdjacency`. -/

/- The estimates `defective_J_few` (§13.2) and `exceptional_JJ_few` (§13.3) use the margin of the
unflagged faces, which needs the centre `O` of **two-sided** roundness: with only an enclosing disc
of radius `D/2 + η D` about `O`, the ports on the far side of the hull may lie outside the flag
band, and "unflagged" then carries no information.  They are therefore stated in the form
`RoundLocalExclusion` (a roundness defect `ρ` chosen after `ε, λ, θ, δ`, and `O` a centre of
two-sided roundness) in `FlaggedExclusion`, and proved there from the
geometric margin step (`saturated_unflagged_margin`, `UnflaggedMargin`) and the algebraic
exclusion steps `defective_J_core`, `exceptional_JJ_core` (**proved**). -/

/- The estimate `capless_small_few` (small capless components of `G` and `K` are pinned,
Verification Guide §13.4) is stated and proved in `CaplessSmall`, from
`capless_G_few` (`CaplessGFew`) and `capless_K_few`
(`CaplessKFew`), both proved. -/

/- The estimate `oneShort_H_stubs_few` (a one-short-port two-edge cap rarely feeds `H`,
Verification Guide §13.5, identity (H2)) is stated and proved in
`OneShortCap`.  Its bound carries, besides `ε D`, twice the number of
intermediate tracks (with between `a D` and `λ D` rhombi): the other port of such a cap may lie on
an intermediate track, whose direction is not clustered at the macroscopic scale.  The assembly
`charging_tracks_residual` pays for these with the sparse-shell hypothesis. -/

end Erdos99

end

end ChargingResidual

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `HHAdjacencyAlgebra`
-/

section HHAdjacencyAlgebra

/-!
# `H–H` adjacency: combinatorics, algebra and labelled-face data

First part of the proof of `hh_edges_few` (see `HHAdjacency`): the `H–H` ports and faces,
the bound `qHH ≤ 4 · #hhFaces`, the approximate (H1) identity, the pinned-label count, the exclusion
of the degenerate case, and the data (`longSides`, `longSum`, `labDir`, `LabelledBy`) attached to a
labelled good face.
-/

open scoped BigOperators Real
open Filter Polynomial ComplexConjugate

@[expose] public noncomputable section

open Classical

namespace Erdos99

open LocalCharge QuadraticResponse DirectionPinning EstablishedExternalResults

/-! ## Combinatorics of `H–H` edges -/

/-- The `H–H` ports: matched unmarked short ports of degree-two faces whose mate is again at a
degree-two face. -/
def hhPorts (X : Finset Plane) (L : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane)) :
    Finset (Set ℂ × Sym2 Plane) :=
  (unmarkedPorts X L G mk).filter (fun q => TrackMated X L G mk q ∧
    q.1 ∈ (trackGraph X L G mk).Hs G.good ∧ (trackMate X q).1 ∈ (trackGraph X L G mk).Hs G.good)

/-- The faces carrying an `H–H` port. -/
def hhFaces (X : Finset Plane) (L : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane)) :
    Finset (Set ℂ) :=
  (hhPorts X L G mk).image Prod.fst

/-- Twice the number of `H–H` edges is at most four times the number of `H–H` faces. -/
theorem qHH_le_four_mul {X : Finset Plane}
    (hends : ∀ T ∈ allTracks X, (trackEnds X T).card = 2) (L : ℝ) (G : GoodFaces X)
    (mk : Set ℂ → Finset (Sym2 Plane)) (Fl : Finset (Set ℂ)) :
    qHH X L G mk Fl ≤ 4 * ((hhFaces X L G mk).card : ℝ) := by
  set P := unmarkedPorts X L G mk with hP
  set g := trackGraph X L G mk with hg
  have hM := trackMate_isMatching hends L G mk
  -- edges inject into `H–H` ports
  have h1 : g.eIn (g.Hs G.good) (g.Hs G.good) ≤ (hhPorts X L G mk).card := by
    unfold StubGraph.eIn
    refine Finset.card_le_card_of_injOn (StubGraph.hEnum P) ?_ ?_
    · intro i hi
      simp only [Finset.coe_filter, Set.mem_setOf_eq, hg, trackGraph, StubGraph.ofHalfEdges,
        Finset.mem_filter, Finset.mem_range] at hi
      obtain ⟨⟨hiP, hmat, -⟩, hs, ht⟩ := hi
      simp only [Finset.mem_coe, hhPorts, Finset.mem_filter]
      exact ⟨StubGraph.hEnum_mem P hiP, hmat, hs, ht⟩
    · intro i hi j hj hij
      simp only [Finset.coe_filter, Set.mem_setOf_eq, hg, trackGraph, StubGraph.ofHalfEdges,
        Finset.mem_filter, Finset.mem_range] at hi hj
      rw [← StubGraph.hIdx_hEnum P hi.1.1, ← StubGraph.hIdx_hEnum P hj.1.1]
      exact congrArg _ hij
  -- each `H` face carries at most two ports
  have h2 : (hhPorts X L G mk).card ≤ 2 * (hhFaces X L G mk).card := by
    refine Finset.card_le_mul_card_image (f := (Prod.fst : Set ℂ × Sym2 Plane → Set ℂ))
      (hhPorts X L G mk) 2 fun F hF => ?_
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hF
    have hqH : q.1 ∈ g.Hs G.good := (Finset.mem_filter.1 hq).2.2.1
    have hdeg : g.deg q.1 = 2 := (Finset.mem_filter.1 hqH).2
    rw [hg, trackGraph, StubGraph.deg_ofHalfEdges hM] at hdeg
    rw [← hdeg]
    refine Finset.card_le_card fun q' hq' => ?_
    obtain ⟨hq'1, hq'2⟩ := Finset.mem_filter.1 hq'
    exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hq'1).1, hq'2⟩
  have : (g.eIn (g.Hs G.good) (g.Hs G.good) : ℝ) ≤ 2 * (hhFaces X L G mk).card := by
    exact_mod_cast h1.trans h2
  simp only [qHH]
  linarith

/-! ## The approximate (H1) identity -/

/-- The (H1) expression. -/
def hhExpr (a b : ℂ) : ℂ :=
  a * conj a * (b * conj b) * ((a + b) * (conj a + conj b)) + (a * conj b - conj a * b) ^ 2

lemma continuous_hhExpr : Continuous (fun p : ℂ × ℂ => hhExpr p.1 p.2) := by
  unfold hhExpr; fun_prop

lemma hhPoly_eval_eq_hhExpr {τ : ℂ} (hτ : ‖τ‖ = 1) (k l : ℝ) (Z W : ℂ) :
    (hhPoly k l Z W).eval τ = τ ^ 3 * hhExpr ((k : ℂ) * τ + Z) ((l : ℂ) * τ + W) := by
  rw [hhPoly_eval hτ, hhExpr, conj_response hτ, conj_response hτ]

/-- **Approximate (H1).**  For every `r > 0` there is `ε₁ > 0` such that, if unit vectors
`s, u, w` satisfy `‖k τ + s + u + Z‖ ≤ ε₁`, `‖l τ' - s + w + W‖ ≤ ε₁` and `‖τ - τ'‖ ≤ ε₁`, then
`‖hhPoly k l Z W (τ)‖ < r`. -/
theorem approx_H1 {r : ℝ} (hr : 0 < r) :
    ∃ ε₁ > 0, ∀ (k l : ℝ), (k = 1 ∨ k = 2) → (l = 1 ∨ l = 2) → ∀ Z W τ τ' s u w : ℂ,
      ‖Z‖ ≤ 6 → ‖W‖ ≤ 6 → ‖τ‖ = 1 → ‖τ'‖ = 1 → ‖s‖ = 1 → ‖u‖ = 1 → ‖w‖ = 1 →
      ‖(k : ℂ) * τ + s + u + Z‖ ≤ ε₁ → ‖(l : ℂ) * τ' - s + w + W‖ ≤ ε₁ → ‖τ - τ'‖ ≤ ε₁ →
      ‖(hhPoly k l Z W).eval τ‖ < r := by
  set K : Set (ℂ × ℂ) := Metric.closedBall 0 20 ×ˢ Metric.closedBall 0 20
  have hK : IsCompact K := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have huc := hK.uniformContinuousOn_of_continuous continuous_hhExpr.continuousOn
  obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuousOn_iff.1 huc r hr
  refine ⟨min (δ / 4) 1, by positivity, ?_⟩
  intro k l hk hl Z W τ τ' s u w hZ hW hτ hτ' hs hu hw h1 h2 h3
  set ε₁ := min (δ / 4) 1
  have he1 : ε₁ ≤ δ / 4 := min_le_left _ _
  have he2 : ε₁ ≤ 1 := min_le_right _ _
  have hk0 : 0 ≤ k ∧ k ≤ 2 := by rcases hk with rfl | rfl <;> norm_num
  have hl0 : 0 ≤ l ∧ l ≤ 2 := by rcases hl with rfl | rfl <;> norm_num
  have hkn : ‖(k : ℂ)‖ ≤ 2 := by rw [Complex.norm_real, Real.norm_of_nonneg hk0.1]; exact hk0.2
  have hln : ‖(l : ℂ)‖ ≤ 2 := by rw [Complex.norm_real, Real.norm_of_nonneg hl0.1]; exact hl0.2
  set a := (k : ℂ) * τ + Z
  set b := (l : ℂ) * τ + W
  set a' := -(s + u)
  set b' := s - w
  have hzero : hhExpr a' b' = 0 := by
    refine hh_identity hs ?_ ?_
    · rw [show s + a' = -u by simp only [a']; ring, norm_neg, hu]
    · rw [show s - b' = w by simp [b']]; exact hw
  have ha : ‖a‖ ≤ 20 := by
    calc ‖a‖ ≤ ‖(k : ℂ) * τ‖ + ‖Z‖ := norm_add_le _ _
      _ ≤ 2 + 6 := by rw [norm_mul, hτ, mul_one]; linarith
      _ ≤ 20 := by norm_num
  have hb : ‖b‖ ≤ 20 := by
    calc ‖b‖ ≤ ‖(l : ℂ) * τ‖ + ‖W‖ := norm_add_le _ _
      _ ≤ 2 + 6 := by rw [norm_mul, hτ, mul_one]; linarith
      _ ≤ 20 := by norm_num
  have ha' : ‖a'‖ ≤ 20 := by
    have := norm_add_le s u; simp only [a', norm_neg]; linarith
  have hb' : ‖b'‖ ≤ 20 := by
    have := norm_sub_le s w; simp only [b']; linarith
  have hda : ‖a - a'‖ ≤ ε₁ := by
    have : a - a' = (k : ℂ) * τ + s + u + Z := by simp only [a, a']; ring
    rw [this]; exact h1
  have hdb : ‖b - b'‖ ≤ 3 * ε₁ := by
    have : b - b' = ((l : ℂ) * τ' - s + w + W) + (l : ℂ) * (τ - τ') := by
      simp only [b, b']; ring
    rw [this]
    calc _ ≤ ‖(l : ℂ) * τ' - s + w + W‖ + ‖(l : ℂ) * (τ - τ')‖ := norm_add_le _ _
      _ ≤ ε₁ + 2 * ε₁ := by
          rw [norm_mul]
          have := mul_le_mul hln h3 (norm_nonneg _) (by norm_num)
          linarith
      _ = 3 * ε₁ := by ring
  have hmem : (a, b) ∈ K := ⟨by simpa using ha, by simpa using hb⟩
  have hmem' : (a', b') ∈ K := ⟨by simpa using ha', by simpa using hb'⟩
  have hdist : dist (a, b) (a', b') < δ := by
    rw [Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm]
    constructor <;> linarith
  have key := hδu _ hmem _ hmem' hdist
  rw [dist_eq_norm, hzero, sub_zero] at key
  rw [hhPoly_eval_eq_hhExpr hτ, norm_mul, norm_pow, hτ, one_pow, one_mul]
  exact key

/-! ## The counting step -/

/-- Admissible `H–H` data `(k, l, Z, W)`: multiplicities in `{1, 2}`, bounded long-side sums, and
away from the exceptional case `k = l = 1`, `W = -Z`, `|Z| = 1` of `hhPoly_eq_zero_iff`. -/
def HHAdm (κ : ℝ) (d : ℝ × ℝ × ℂ × ℂ) : Prop :=
  (d.1 = 1 ∨ d.1 = 2) ∧ (d.2.1 = 1 ∨ d.2.1 = 2) ∧ ‖d.2.2.1‖ ≤ 6 ∧ ‖d.2.2.2‖ ≤ 6 ∧
    ¬ (d.1 = 1 ∧ d.2.1 = 1 ∧ ‖d.2.2.1 + d.2.2.2‖ < κ ∧ |‖d.2.2.1‖ - 1| < κ)

/-- The coefficient vector of `hhPoly` as an explicit function of the data. -/
def hhCoeffVec (d : ℝ × ℝ × ℂ × ℂ) : Fin 7 → ℂ :=
  ![hhCoeff0 d.1 d.2.1 d.2.2.1 d.2.2.2,
    hhCoeff1 d.1 d.2.1 d.2.2.1 (conj d.2.2.1) d.2.2.2 (conj d.2.2.2),
    hhCoeff2 d.1 d.2.1 d.2.2.1 (conj d.2.2.1) d.2.2.2 (conj d.2.2.2),
    hhCoeff3 d.1 d.2.1 d.2.2.1 (conj d.2.2.1) d.2.2.2 (conj d.2.2.2),
    hhCoeff4 d.1 d.2.1 d.2.2.1 (conj d.2.2.1) d.2.2.2 (conj d.2.2.2),
    hhCoeff5 d.1 d.2.1 d.2.2.1 (conj d.2.2.1) d.2.2.2 (conj d.2.2.2),
    hhCoeff6 d.1 d.2.1 (conj d.2.2.1) (conj d.2.2.2)]

lemma polyCoeffs_hhPoly (d : ℝ × ℝ × ℂ × ℂ) :
    polyCoeffs 6 (hhPoly d.1 d.2.1 d.2.2.1 d.2.2.2) = hhCoeffVec d := by
  ext i
  fin_cases i <;>
    simp [polyCoeffs, hhCoeffVec, hhPoly_eq, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X,
      coeff_C]

lemma continuous_hhCoeffVec : Continuous hhCoeffVec := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact (show Continuous (fun d : ℝ × ℝ × ℂ × ℂ => hhCoeff0 d.1 d.2.1 d.2.2.1 d.2.2.2) by
      unfold hhCoeff0; fun_prop)
  · exact (show Continuous (fun d : ℝ × ℝ × ℂ × ℂ =>
      hhCoeff1 d.1 d.2.1 d.2.2.1 (conj d.2.2.1) d.2.2.2 (conj d.2.2.2)) by unfold hhCoeff1; fun_prop)
  · exact (show Continuous (fun d : ℝ × ℝ × ℂ × ℂ =>
      hhCoeff2 d.1 d.2.1 d.2.2.1 (conj d.2.2.1) d.2.2.2 (conj d.2.2.2)) by unfold hhCoeff2; fun_prop)
  · exact (show Continuous (fun d : ℝ × ℝ × ℂ × ℂ =>
      hhCoeff3 d.1 d.2.1 d.2.2.1 (conj d.2.2.1) d.2.2.2 (conj d.2.2.2)) by unfold hhCoeff3; fun_prop)
  · exact (show Continuous (fun d : ℝ × ℝ × ℂ × ℂ =>
      hhCoeff4 d.1 d.2.1 d.2.2.1 (conj d.2.2.1) d.2.2.2 (conj d.2.2.2)) by unfold hhCoeff4; fun_prop)
  · exact (show Continuous (fun d : ℝ × ℝ × ℂ × ℂ =>
      hhCoeff5 d.1 d.2.1 d.2.2.1 (conj d.2.2.1) d.2.2.2 (conj d.2.2.2)) by unfold hhCoeff5; fun_prop)
  · exact (show Continuous (fun d : ℝ × ℝ × ℂ × ℂ =>
      hhCoeff6 d.1 d.2.1 (conj d.2.2.1) (conj d.2.2.2)) by unfold hhCoeff6; fun_prop)

lemma isCompact_hhAdm {κ : ℝ} : IsCompact {d : ℝ × ℝ × ℂ × ℂ | HHAdm κ d} := by
  have hset : {d : ℝ × ℝ × ℂ × ℂ | HHAdm κ d} = {d | (d.1 = 1 ∨ d.1 = 2) ∧
      (d.2.1 = 1 ∨ d.2.1 = 2) ∧ ‖d.2.2.1‖ ≤ 6 ∧ ‖d.2.2.2‖ ≤ 6 ∧
      (d.1 = 2 ∨ d.2.1 = 2 ∨ κ ≤ ‖d.2.2.1 + d.2.2.2‖ ∨ κ ≤ |‖d.2.2.1‖ - 1|)} := by
    ext d
    simp only [Set.mem_setOf_eq, HHAdm]
    constructor
    · rintro ⟨hk, hl, hZ, hW, hn⟩
      refine ⟨hk, hl, hZ, hW, ?_⟩
      rcases hk with hk | hk
      · rcases hl with hl | hl
        · right; right
          by_contra hc
          push_neg at hc
          exact hn ⟨hk, hl, hc.1, hc.2⟩
        · exact Or.inr (Or.inl hl)
      · exact Or.inl hk
    · rintro ⟨hk, hl, hZ, hW, hn⟩
      refine ⟨hk, hl, hZ, hW, ?_⟩
      rintro ⟨hk1, hl1, h1, h2⟩
      rcases hn with h | h | h | h
      · rw [hk1] at h; norm_num at h
      · rw [hl1] at h; norm_num at h
      · linarith
      · linarith
  rw [hset]
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · simp only [Set.setOf_and, Set.setOf_or]
    repeat' first | apply IsClosed.inter | apply IsClosed.union
    all_goals first
      | exact isClosed_eq (by fun_prop) (by fun_prop)
      | exact isClosed_le (by fun_prop) (by fun_prop)
  · rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨6, fun d hd => ?_⟩
    obtain ⟨hk, hl, hZ, hW, -⟩ := hd
    have hk' : ‖d.1‖ ≤ 6 := by rcases hk with h | h <;> rw [h] <;> norm_num
    have hl' : ‖d.2.1‖ ≤ 6 := by rcases hl with h | h <;> rw [h] <;> norm_num
    simp only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
    exact max_le hk' (max_le hl' (max_le hZ hW))

/-- Admissible data have coefficient vectors bounded away from zero. -/
lemma hhAdm_coeff_lower {κ : ℝ} (hκ : 0 < κ) :
    ∃ m₀ > 0, ∀ d, HHAdm κ d → m₀ ≤ ‖hhCoeffVec d‖ := by
  rcases (Set.eq_empty_or_nonempty {d : ℝ × ℝ × ℂ × ℂ | HHAdm κ d}) with hE | hne
  · refine ⟨1, one_pos, fun d hd => ?_⟩
    have : d ∈ {d : ℝ × ℝ × ℂ × ℂ | HHAdm κ d} := hd
    rw [hE] at this; exact absurd this (Set.notMem_empty _)
  obtain ⟨d₀, hd₀, hmin⟩ := isCompact_hhAdm.exists_isMinOn hne
    (continuous_norm.comp continuous_hhCoeffVec).continuousOn
  refine ⟨‖hhCoeffVec d₀‖, ?_, fun d hd => hmin hd⟩
  rcases (norm_nonneg (hhCoeffVec d₀)).lt_or_eq with h | h
  · exact h
  · exfalso
    obtain ⟨hk, hl, hZ, hW, hn⟩ := hd₀
    have h0 : hhCoeffVec d₀ = 0 := norm_eq_zero.1 h.symm
    have hp : hhPoly d₀.1 d₀.2.1 d₀.2.2.1 d₀.2.2.2 = 0 := by
      rw [← coeffPoly_polyCoeffs (hhPoly_natDegree_le _ _ _ _), polyCoeffs_hhPoly, h0]
      simp [coeffPoly]
    obtain ⟨hW', hk1, hl1, hZ1⟩ := (hhPoly_eq_zero_iff hk hl _ _).1 hp
    refine hn ⟨hk1, hl1, ?_, ?_⟩
    · rw [hW', add_neg_cancel, norm_zero]; exact hκ
    · rw [hZ1, sub_self, abs_zero]; exact hκ

/-- **Pinned labels are few.**  For a bounded number `N` of centres, admissible data near a centre
whose (H1) polynomial is small at the direction of a hull side pins that side: such sides number
at most `ε D`. -/
theorem hh_pinned_count (N : ℕ) {ε κ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) :
    ∃ r > 0, ∃ μ > 0, ∀ᶠ n in atTop, ∀ X, IsOptimal n X →
      ∀ C : Finset (ℝ × ℝ × ℂ × ℂ), C.card ≤ N → ∀ A ⊆ ccwHullSides X,
        (∀ p ∈ A, ∃ d : ℝ × ℝ × ℂ × ℂ, HHAdm κ d ∧ (∃ c ∈ C, ‖d - c‖ < μ) ∧
          ‖(hhPoly d.1 d.2.1 d.2.2.1 d.2.2.2).eval (toC (sideDir p))‖ < r) →
        (A.card : ℝ) ≤ ε * diam X := by
  obtain ⟨m₀, hm₀, hlow⟩ := hhAdm_coeff_lower hκ
  obtain ⟨r, hr, μ, hμ, hpin⟩ := pinned_directions_few 6 N hε hm₀
  have huc := (isCompact_hhAdm (κ := κ)).uniformContinuousOn_of_continuous
    continuous_hhCoeffVec.continuousOn
  obtain ⟨μ₁, hμ₁, hu⟩ := Metric.uniformContinuousOn_iff.1 huc μ hμ
  refine ⟨r, hr, μ₁ / 2, by positivity, ?_⟩
  filter_upwards [hpin] with n hn X hX C hC A hA hp
  set good : Finset (ℝ × ℝ × ℂ × ℂ) := C.filter (fun c => ∃ d, HHAdm κ d ∧ ‖d - c‖ < μ₁ / 2)
    with hgood
  set rc : ℝ × ℝ × ℂ × ℂ → ℝ × ℝ × ℂ × ℂ := fun c =>
    if h : ∃ d, HHAdm κ d ∧ ‖d - c‖ < μ₁ / 2 then h.choose else c with hrcdef
  have hrc : ∀ c ∈ good, HHAdm κ (rc c) ∧ ‖rc c - c‖ < μ₁ / 2 := by
    intro c hc
    have h := (Finset.mem_filter.1 hc).2
    simp only [hrcdef, dif_pos h]
    exact h.choose_spec
  set T : Finset (Fin 7 → ℂ) := good.image (fun c => hhCoeffVec (rc c)) with hTdef
  have hmemgood : ∀ p ∈ A, ∀ d c, HHAdm κ d → c ∈ C → ‖d - c‖ < μ₁ / 2 → c ∈ good :=
    fun p _ d c hd hc hdc => Finset.mem_filter.2 ⟨hc, d, hd, hdc⟩
  rcases T.eq_empty_or_nonempty with hT | ⟨t₀, ht₀⟩
  · have hA0 : A = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun p hpA => ?_
      obtain ⟨d, hd, ⟨c, hc, hdc⟩, -⟩ := hp p hpA
      have h1 : hhCoeffVec (rc c) ∈ T :=
        Finset.mem_image_of_mem _ (hmemgood p hpA d c hd hc hdc)
      rw [hT] at h1; exact Finset.notMem_empty _ h1
    rw [hA0, Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg hε.le Metric.diam_nonneg
  have hTc : T.card ≤ N := Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans hC)
  set c₀ : Fin N → Fin 7 → ℂ := fun j =>
    if h : (j : ℕ) < T.card then (T.equivFin.symm ⟨j, h⟩ : Fin 7 → ℂ) else t₀ with hc₀def
  have hc₀T : ∀ j, c₀ j ∈ T := by
    intro j
    simp only [hc₀def]
    split_ifs
    · exact (T.equivFin.symm _).2
    · exact ht₀
  have hTc₀ : ∀ t (ht : t ∈ T), ∃ j, c₀ j = t := by
    intro t ht
    set i := T.equivFin ⟨t, ht⟩
    refine ⟨⟨i, lt_of_lt_of_le i.2 hTc⟩, ?_⟩
    simp only [hc₀def, dif_pos i.2]
    simp [i]
  refine hn X hX c₀ (fun j => ?_) A hA (fun p hpA => ?_)
  · obtain ⟨c, hc, hce⟩ := Finset.mem_image.1 (hc₀T j)
    rw [← hce]; exact hlow _ (hrc c hc).1
  · obtain ⟨d, hd, ⟨c, hc, hdc⟩, hev⟩ := hp p hpA
    have hcg := hmemgood p hpA d c hd hc hdc
    obtain ⟨j, hj⟩ := hTc₀ _ (Finset.mem_image_of_mem (fun c => hhCoeffVec (rc c)) hcg)
    refine ⟨j, hhCoeffVec d, ?_, ?_⟩
    · rw [hj]
      have hdist : dist d (rc c) < μ₁ := by
        rw [dist_eq_norm]
        have := norm_sub_le (d - c) (rc c - c)
        rw [sub_sub_sub_cancel_right] at this
        linarith [(hrc c hcg).2]
      have := hu d hd (rc c) (hrc c hcg).1 hdist
      rwa [dist_eq_norm] at this
    · rw [← polyCoeffs_hhPoly, coeffPoly_polyCoeffs (hhPoly_natDegree_le _ _ _ _)]
      exact hev

/-! ## The exceptional configuration is excluded by the margin -/

/-- Three roots of the two-circle quadratic: a unit `z` with `|z - S| = 1` is one of two given
distinct such points. -/
lemma two_circle_root_cases {S z z₁ z₂ : ℂ} (hz : ‖z‖ = 1) (hzS : ‖z - S‖ = 1) (h₁ : ‖z₁‖ = 1)
    (h₁S : ‖z₁ - S‖ = 1) (h₂ : ‖z₂‖ = 1) (h₂S : ‖z₂ - S‖ = 1) (hS : S ≠ 0) (h12 : z₁ ≠ z₂) :
    z = z₁ ∨ z = z₂ := by
  have e := two_circle_eq hz hzS
  have e1 := two_circle_eq h₁ h₁S
  have e2 := two_circle_eq h₂ h₂S
  have hsum : conj S * (z₁ + z₂) = S * conj S := by
    have : (z₁ - z₂) * (conj S * (z₁ + z₂) - S * conj S) = 0 := by linear_combination e1 - e2
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 h12))
  have hprod : conj S * (z - z₁) * (z - z₂) = 0 := by
    linear_combination e - e1 + (z₁ - z) * hsum
  have hS' : conj S ≠ 0 := by rwa [_root_.map_ne_zero]
  rcases mul_eq_zero.1 hprod with h | h
  · exact Or.inl (sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left hS'))
  · exact Or.inr (sub_eq_zero.1 h)

/-- The exact degenerate configuration contradicts the margin. -/
lemma degenerate_exact {κ' : ℝ} (hκ' : 0 < κ') {p₁ p₂ q₁ q₂ τ : ℂ} (hp₁ : ‖p₁‖ = 1)
    (hp₂ : ‖p₂‖ = 1) (hq₁ : ‖q₁‖ = 1) (hq₂ : ‖q₂‖ = 1) (hτ : ‖τ‖ = 1)
    (m₁ : (p₁ * conj τ).re ≤ 1 / 2 - κ') (m₂ : (p₂ * conj τ).re ≤ 1 / 2 - κ')
    (m₃ : (q₁ * conj τ).re ≤ 1 / 2 - κ') (m₄ : (q₂ * conj τ).re ≤ 1 / 2 - κ')
    (hsum : (p₁ + p₂) + (q₁ + q₂) = 0) (hZ : ‖p₁ + p₂‖ = 1) : False := by
  set S := -(p₁ + p₂) with hSdef
  have hS : S ≠ 0 := by
    intro h; rw [hSdef, neg_eq_zero] at h; rw [h, norm_zero] at hZ; norm_num at hZ
  have hq2 : q₂ = S - q₁ := by rw [hSdef]; linear_combination hsum
  have hn1 : ‖-p₁ - S‖ = 1 := by rw [hSdef]; simp [hp₂]
  have hn2 : ‖-p₂ - S‖ = 1 := by
    rw [hSdef, show -p₂ - -(p₁ + p₂) = p₁ by ring, hp₁]
  have hq1S : ‖q₁ - S‖ = 1 := by
    rw [show q₁ - S = -q₂ by rw [hq2]; ring, norm_neg, hq₂]
  have hq2S : ‖q₂ - S‖ = 1 := by
    rw [show q₂ - S = -q₁ by rw [hq2]; ring, norm_neg, hq₁]
  have h12 : -p₁ ≠ -p₂ := by
    intro h
    have : p₁ = p₂ := neg_inj.1 h
    rw [this, ← two_mul, norm_mul, hp₂] at hZ; norm_num at hZ
  have hnp₁ : ‖-p₁‖ = 1 := by rw [norm_neg, hp₁]
  have hnp₂ : ‖-p₂‖ = 1 := by rw [norm_neg, hp₂]
  have c1 := two_circle_root_cases hq₁ hq1S hnp₁ hn1 hnp₂ hn2 hS h12
  have c2 := two_circle_root_cases hq₂ hq2S hnp₁ hn1 hnp₂ hn2 hS h12
  -- `{q₁, q₂} = {-p₁, -p₂}`
  have hboth : (q₁ = -p₁ ∨ q₂ = -p₁) ∧ (q₁ = -p₂ ∨ q₂ = -p₂) := by
    rcases c1 with h1 | h1 <;> rcases c2 with h2 | h2
    · exfalso; rw [h1, h2] at hsum
      have : p₂ = p₁ := by linear_combination hsum
      exact h12 (by rw [this])
    · exact ⟨Or.inl h1, Or.inr h2⟩
    · exact ⟨Or.inr h2, Or.inl h1⟩
    · exfalso; rw [h1, h2] at hsum
      have : p₁ = p₂ := by linear_combination hsum
      exact h12 (by rw [this])
  have neg_re : ∀ p : ℂ, ((-p) * conj τ).re = -(p * conj τ).re := fun p => by
    rw [neg_mul, Complex.neg_re]
  rcases four_ports_projection hp₁ hp₂ hτ hZ with h | h
  · have hx : (p₁ * conj τ).re ≤ -(1 / 2) := by
      rcases le_abs'.1 h with h' | h'
      · linarith
      · linarith
    rcases hboth.1 with hq | hq
    · have := neg_re p₁; rw [← hq] at this; linarith
    · have := neg_re p₁; rw [← hq] at this; linarith
  · have hx : (p₂ * conj τ).re ≤ -(1 / 2) := by
      rcases le_abs'.1 h with h' | h'
      · linarith
      · linarith
    rcases hboth.2 with hq | hq
    · have := neg_re p₂; rw [← hq] at this; linarith
    · have := neg_re p₂; rw [← hq] at this; linarith

/-- **The degenerate configuration is excluded.**  If all four long sides `p₁, p₂` (of `F`) and
`q₁, q₂` (of `F'`) have projection at most `1/2 - κ'` on the respective labels `τ, τ'`, and
`τ ≈ τ'`, then `(Z, W) = (p₁ + p₂, q₁ + q₂)` stays away from `W = -Z`, `|Z| = 1`. -/
theorem degenerate_excluded {κ' : ℝ} (hκ' : 0 < κ') :
    ∃ κ > 0, ∃ ρ > 0, ∀ p₁ p₂ q₁ q₂ τ τ' : ℂ, ‖p₁‖ = 1 → ‖p₂‖ = 1 → ‖q₁‖ = 1 → ‖q₂‖ = 1 →
      ‖τ‖ = 1 → ‖τ'‖ = 1 → ‖τ - τ'‖ ≤ ρ →
      (p₁ * conj τ).re ≤ 1 / 2 - κ' → (p₂ * conj τ).re ≤ 1 / 2 - κ' →
      (q₁ * conj τ').re ≤ 1 / 2 - κ' → (q₂ * conj τ').re ≤ 1 / 2 - κ' →
      ¬ (‖(p₁ + p₂) + (q₁ + q₂)‖ < κ ∧ |‖p₁ + p₂‖ - 1| < κ) := by
  set K : Set (ℂ × ℂ × ℂ × ℂ × ℂ × ℂ) := {x | ‖x.1‖ = 1 ∧ ‖x.2.1‖ = 1 ∧ ‖x.2.2.1‖ = 1 ∧
    ‖x.2.2.2.1‖ = 1 ∧ ‖x.2.2.2.2.1‖ = 1 ∧ ‖x.2.2.2.2.2‖ = 1 ∧
    (x.1 * conj x.2.2.2.2.1).re ≤ 1 / 2 - κ' ∧ (x.2.1 * conj x.2.2.2.2.1).re ≤ 1 / 2 - κ' ∧
    (x.2.2.1 * conj x.2.2.2.2.2).re ≤ 1 / 2 - κ' ∧ (x.2.2.2.1 * conj x.2.2.2.2.2).re ≤ 1 / 2 - κ'}
    with hK
  set f : ℂ × ℂ × ℂ × ℂ × ℂ × ℂ → ℝ := fun x =>
    max (max ‖(x.1 + x.2.1) + (x.2.2.1 + x.2.2.2.1)‖ |‖x.1 + x.2.1‖ - 1|)
      ‖x.2.2.2.2.1 - x.2.2.2.2.2‖ with hf
  have hfc : Continuous f := by simp only [hf]; fun_prop
  have hKc : IsClosed K := by
    simp only [hK, Set.setOf_and]
    repeat' apply IsClosed.inter
    all_goals first
      | exact isClosed_eq (by fun_prop) (by fun_prop)
      | exact isClosed_le (by fun_prop) (by fun_prop)
  have hKb : Bornology.IsBounded K := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨1, fun x hx => ?_⟩
    obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := hx
    simp only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, h1, h2, h3, h4, h5, h6,
      max_self, le_refl]
  have hKcpt : IsCompact K := Metric.isCompact_of_isClosed_isBounded hKc hKb
  rcases K.eq_empty_or_nonempty with hE | hne
  · refine ⟨1, one_pos, 1, one_pos, ?_⟩
    intro p₁ p₂ q₁ q₂ τ τ' hp₁ hp₂ hq₁ hq₂ hτ hτ' _ m₁ m₂ m₃ m₄
    have : ((p₁, p₂, q₁, q₂, τ, τ') : ℂ × ℂ × ℂ × ℂ × ℂ × ℂ) ∈ K :=
      ⟨hp₁, hp₂, hq₁, hq₂, hτ, hτ', m₁, m₂, m₃, m₄⟩
    rw [hE] at this; exact absurd this (Set.notMem_empty _)
  obtain ⟨x₀, hx₀, hmin⟩ := hKcpt.exists_isMinOn hne hfc.continuousOn
  set m := f x₀ with hm
  have hm0 : 0 < m := by
    rcases (show 0 ≤ m from le_max_of_le_right (norm_nonneg _)).lt_or_eq with h | h
    · exact h
    · exfalso
      obtain ⟨h1, h2, h3, h4, h5, h6, m₁, m₂, m₃, m₄⟩ := hx₀
      have e1 : ‖(x₀.1 + x₀.2.1) + (x₀.2.2.1 + x₀.2.2.2.1)‖ ≤ 0 := by
        have := le_max_left (max ‖(x₀.1 + x₀.2.1) + (x₀.2.2.1 + x₀.2.2.2.1)‖
          |‖x₀.1 + x₀.2.1‖ - 1|) ‖x₀.2.2.2.2.1 - x₀.2.2.2.2.2‖
        have := le_max_left ‖(x₀.1 + x₀.2.1) + (x₀.2.2.1 + x₀.2.2.2.1)‖ |‖x₀.1 + x₀.2.1‖ - 1|
        rw [hm] at h; simp only [hf] at h; linarith
      have e2 : |‖x₀.1 + x₀.2.1‖ - 1| ≤ 0 := by
        have := le_max_left (max ‖(x₀.1 + x₀.2.1) + (x₀.2.2.1 + x₀.2.2.2.1)‖
          |‖x₀.1 + x₀.2.1‖ - 1|) ‖x₀.2.2.2.2.1 - x₀.2.2.2.2.2‖
        have := le_max_right ‖(x₀.1 + x₀.2.1) + (x₀.2.2.1 + x₀.2.2.2.1)‖ |‖x₀.1 + x₀.2.1‖ - 1|
        rw [hm] at h; simp only [hf] at h; linarith
      have e3 : ‖x₀.2.2.2.2.1 - x₀.2.2.2.2.2‖ ≤ 0 := by
        have := le_max_right (max ‖(x₀.1 + x₀.2.1) + (x₀.2.2.1 + x₀.2.2.2.1)‖
          |‖x₀.1 + x₀.2.1‖ - 1|) ‖x₀.2.2.2.2.1 - x₀.2.2.2.2.2‖
        rw [hm] at h; simp only [hf] at h; linarith
      have hsum := norm_le_zero_iff.1 e1
      have hZ : ‖x₀.1 + x₀.2.1‖ = 1 := by
        have := abs_nonneg (‖x₀.1 + x₀.2.1‖ - 1)
        have : |‖x₀.1 + x₀.2.1‖ - 1| = 0 := le_antisymm e2 this
        rw [abs_eq_zero, sub_eq_zero] at this; exact this
      have hττ : x₀.2.2.2.2.1 = x₀.2.2.2.2.2 := sub_eq_zero.1 (norm_le_zero_iff.1 e3)
      rw [← hττ] at m₃ m₄
      exact degenerate_exact hκ' h1 h2 h3 h4 h5 m₁ m₂ m₃ m₄ hsum hZ
  refine ⟨m / 2, by positivity, m / 2, by positivity, ?_⟩
  intro p₁ p₂ q₁ q₂ τ τ' hp₁ hp₂ hq₁ hq₂ hτ hτ' hρ m₁ m₂ m₃ m₄ ⟨hs, hz⟩
  have hx : ((p₁, p₂, q₁, q₂, τ, τ') : ℂ × ℂ × ℂ × ℂ × ℂ × ℂ) ∈ K :=
    ⟨hp₁, hp₂, hq₁, hq₂, hτ, hτ', m₁, m₂, m₃, m₄⟩
  have := hmin hx
  simp only [Set.mem_setOf_eq] at this
  have hlt : f (p₁, p₂, q₁, q₂, τ, τ') < m := by
    simp only [hf]
    refine max_lt (max_lt (by linarith) (by linarith)) (by linarith)
  linarith

/-! ## The data of a labelled face -/

/-- The multiplicity of the marked tangent, as a real number: two at a hexagon, one at a
pentagon. -/
def GoodFaces.kMult {X : Finset Plane} (G : GoodFaces X) (F : Set ℂ) : ℝ :=
  if F ∈ G.hex then 2 else 1

lemma GoodFaces.kMult_cases {X : Finset Plane} (G : GoodFaces X) (F : Set ℂ) :
    G.kMult F = 1 ∨ G.kMult F = 2 := by
  unfold GoodFaces.kMult; split_ifs <;> simp

lemma GoodFaces.markMult_eq {X : Finset Plane} (G : GoodFaces X) (F : Set ℂ) :
    G.markMult F = (G.kMult F : ℂ) := by
  unfold GoodFaces.markMult GoodFaces.kMult; split_ifs <;> simp

/-- The long sides of a face: its oriented sides whose edge is not a short port. -/
def longSides (X : Finset Plane) (L : ℝ) (F : Set ℂ) : Finset (ℂ × ℂ) :=
  (orientedSides X F).filter (fun ab => ¬ ∃ e ∈ shortPorts X L F, Sym2.map toC e = s(ab.1, ab.2))

/-- The sum of the long side vectors of a face. -/
def longSum (X : Finset Plane) (L : ℝ) (F : Set ℂ) : ℂ :=
  ∑ ab ∈ longSides X L F, (ab.2 - ab.1)

/-- The unit direction of the label of a face. -/
def labDir (lab : Set ℂ → Plane × Plane) (F : Set ℂ) : ℂ := toC (sideDir (lab F))

/-- Source labels with an explicit labelling function (the body of `IsLabelled`). -/
def LabelledBy (X : Finset Plane) (tol : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane))
    (lab : Set ℂ → Plane × Plane) : Prop :=
  Set.InjOn lab G.good ∧ ∀ F ∈ G.good,
    lab F ∈ unitHullSides X ∧
    ‖markedSum X F (mk F) - G.markMult F * toC (sideDir (lab F))‖ ≤ tol ∧
    ∀ ab ∈ orientedSides X F, ‖ab.1 - toC (lab F).1‖ ≤ tol * diam X

lemma isLabelled_iff {X : Finset Plane} {tol : ℝ} {G : GoodFaces X}
    {mk : Set ℂ → Finset (Sym2 Plane)} : IsLabelled X tol G mk ↔ ∃ lab, LabelledBy X tol G mk lab :=
  Iff.rfl

lemma norm_labDir {X : Finset Plane} {tol : ℝ} {G : GoodFaces X}
    {mk : Set ℂ → Finset (Sym2 Plane)} {lab : Set ℂ → Plane × Plane}
    (hlab : LabelledBy X tol G mk lab) {F : Set ℂ} (hF : F ∈ G.good) : ‖labDir lab F‖ = 1 := by
  have h := (hlab.2 F hF).1
  have hp := (Finset.mem_filter.1 h).1
  rw [labDir, LinearIsometryEquiv.norm_map]
  exact norm_sideDir (mem_ccwHullSides.1 hp).2.2.1

lemma hhPorts_fst_good {X : Finset Plane} {L : ℝ} {G : GoodFaces X}
    {mk : Set ℂ → Finset (Sym2 Plane)} {q : Set ℂ × Sym2 Plane} (hq : q ∈ hhPorts X L G mk) :
    q.1 ∈ G.good ∧ (trackMate X q).1 ∈ G.good := by
  obtain ⟨-, -, h1, h2⟩ := Finset.mem_filter.1 hq
  exact ⟨(Finset.mem_filter.1 h1).1, (Finset.mem_filter.1 h2).1⟩

end Erdos99

end

end HHAdjacencyAlgebra

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `HopMargin`
-/

section HopMargin

/-!
# Hops along a track from an initial edge

Auxiliary facts for the macroscopic-port margin (`long_side_margin` in `HHAdjacency`).

* `leftStep_or_of_oppositeSides`: a rhombus through an oriented unit edge lies on its left or on
  its right, i.e. gives a left step from or to the edge.
* `allTrackOf_subset_hop`: the hop from an *initial* oriented edge (no rhombus on its right) visits
  every edge of the track.
* `trackLength_le_hopLen`: hence the number of steps of the hop is at least the number of rhombi on
  the track.
* `hop_displacement`: after `m` steps the hop has moved by at least `a* m` in the direction of the
  left normal of the edge, and by at most `m / 2` along the edge.
-/

open scoped BigOperators Real

@[expose] public noncomputable section

open Classical

namespace Erdos99

/-- A unit rhombus `a b c d` (in cyclic order) gives a left step from `(a, b)` to `(d, c)` or from
`(d, c)` to `(a, b)`, according to the side of `a → b` on which it lies. -/
lemma leftStep_or_of_rhombus {X : Finset Plane} {a b c d : Plane}
    (hR : ({a, b, c, d} : Finset Plane) ∈ rhombi X) (hab : dist a b = 1) (hbc : dist b c = 1)
    (hcd : dist c d = 1) (hda : dist d a = 1) (hpara : a + c = b + d) (hac : a ≠ c)
    (hbd : b ≠ d) : LeftStep X (a, b) (d, c) ∨ LeftStep X (d, c) (a, b) := by
  have hc : c = b + d - a := by rw [← hpara]; abel
  have hcd' : c - d = b - a := by rw [hc]; abel
  set x := b - a with hx
  set y := d - a with hy
  have hx1 : ‖x‖ = 1 := by rw [hx, ← dist_eq_norm, dist_comm]; exact hab
  have hy1 : ‖y‖ = 1 := by rw [hy, ← dist_eq_norm]; exact hda
  have hdet : det2 x y ≠ 0 := by
    intro h0
    have e := inner_sq_add_inner_rot_sq x y
    rw [inner_rot_eq_det2, h0, hx1, hy1] at e
    have hi : inner ℝ y x = 1 ∨ inner ℝ y x = -1 := by
      have : (inner ℝ y x - 1) * (inner ℝ y x + 1) = 0 := by nlinarith
      rcases mul_eq_zero.1 this with h | h
      · left; linarith
      · right; linarith
    rcases hi with hi | hi
    · have : ‖y - x‖ ^ 2 = 0 := by rw [norm_sub_sq_real, hx1, hy1, hi]; ring
      have hyx : y - x = 0 := by simpa using this
      apply hbd
      have : d - b = 0 := by rw [← hyx, hx, hy]; abel
      exact (sub_eq_zero.1 this).symm
    · have : ‖y + x‖ ^ 2 = 0 := by rw [norm_add_sq_real, hx1, hy1, hi]; ring
      have hyx : y + x = 0 := by simpa using this
      apply hac
      rw [hc]
      have : b + d - a - a = 0 := by rw [← hyx, hx, hy]; abel
      exact (sub_eq_zero.1 this).symm
  rcases lt_or_gt_of_ne hdet with hneg | hpos
  · right
    refine ⟨?_, by rw [dist_comm]; exact hcd, by rw [dist_comm]; exact hbc,
      by rw [dist_comm]; exact hab, by rw [dist_comm]; exact hda, ?_, ?_⟩
    · have : ({d, c, b, a} : Finset Plane) = {a, b, c, d} := by
        ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
      simpa [this] using hR
    · show b - a = c - d
      rw [hcd']
    · show 0 < det2 (c - d) (a - d)
      rw [hcd', show a - d = -y by rw [hy]; abel]
      unfold det2 at hneg ⊢
      simp only [PiLp.neg_apply] at hneg ⊢
      linarith
  · left
    exact ⟨hR, hab, hbc, hcd, hda, hcd', hpos⟩

/-- **A rhombus through an oriented edge lies on its left or on its right**: an opposite side `g`
of `s(x, y)` is the edge of a left step from `(x, y)`, or of a left step to `(x, y)`. -/
lemma leftStep_or_of_oppositeSides {X : Finset Plane} (hX : IsSeparated X)
    (htri : ¬ HasUnitTriangle X) {x y : Plane} {g : Sym2 Plane}
    (h : OppositeSides X s(x, y) g) :
    ∃ q : Plane × Plane, s(q.1, q.2) = g ∧ (LeftStep X (x, y) q ∨ LeftStep X q (x, y)) := by
  obtain ⟨a, b, c, d, hR, hab, hbc, hcd, hda, he, rfl⟩ := h
  have hD := rhombusData_of_mem hX htri hR hab hbc hcd hda
  obtain ⟨-, hac, -, -, hbd, -⟩ := hD.distinct
  rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨(d, c), Sym2.eq_swap, leftStep_or_of_rhombus hR hab hbc hcd hda hD.para hac hbd⟩
  · have hR' : ({x, y, d, c} : Finset Plane) ∈ rhombi X := by
      have : ({x, y, d, c} : Finset Plane) = {y, x, c, d} := by
        ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
      rw [this]; exact hR
    have := leftStep_or_of_rhombus hR' (by rw [dist_comm]; exact hab)
      (by rw [dist_comm]; exact hda) (by rw [dist_comm]; exact hcd)
      (by rw [dist_comm]; exact hbc) hD.para.symm hbd hac
    exact ⟨(c, d), rfl, this⟩

/-- **The hop from an initial edge visits the whole track.** -/
lemma allTrackOf_subset_hop {X : Finset Plane} (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X)
    {p : Plane × Plane} (hinit : Initial X p) {m : ℕ}
    (hmv : ∀ k < m, ∃ q, LeftStep X ((stepL X)^[k] p) q)
    (hstop : ¬ ∃ q, LeftStep X ((stepL X)^[m] p) q) :
    allTrackOf X s(p.1, p.2) ⊆ (Finset.range (m + 1)).image
      (fun k => s(((stepL X)^[k] p).1, ((stepL X)^[k] p).2)) := by
  set E := (Finset.range (m + 1)).image
    (fun k => s(((stepL X)^[k] p).1, ((stepL X)^[k] p).2)) with hE
  have hmemE : ∀ k ≤ m, s(((stepL X)^[k] p).1, ((stepL X)^[k] p).2) ∈ E :=
    fun k hk => Finset.mem_image.2 ⟨k, Finset.mem_range.2 (by omega), rfl⟩
  have hcl : ∀ g' ∈ E, ∀ g, OppositeSides X g' g → g ∈ E := by
    intro g' hg' g ho
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hg'
    have hk' := Finset.mem_range.1 hk
    obtain ⟨q, rfl, hcase⟩ := leftStep_or_of_oppositeSides hX htri ho
    rcases hcase with hl | hr
    · by_cases hkm : k < m
      · have hs := stepL_spec (hmv k hkm)
        have := LeftStep.unique hX htri hl hs
        rw [this, ← Function.iterate_succ_apply' (stepL X) k p]
        exact hmemE (k + 1) (by omega)
      · exact absurd ⟨q, by rwa [show k = m by omega] at hl⟩ hstop
    · rcases k with _ | j
      · exact absurd ⟨q, hr⟩ hinit
      · have hs := stepL_spec (hmv j (by omega))
        rw [Function.iterate_succ_apply'] at hr
        have := LeftStep.unique_pred hX htri hr hs
        rw [this]
        exact hmemE j (by omega)
  have key : ∀ x y, Relation.EqvGen (OppositeSides X) x y → (x ∈ E ↔ y ∈ E) := by
    intro x y h
    induction h with
    | rel x y h => exact ⟨fun hx => hcl x hx y h, fun hy => hcl y hy x (oppositeSides_symm h)⟩
    | refl => exact Iff.rfl
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
  intro f hf
  obtain ⟨-, hrel⟩ := Finset.mem_filter.1 hf
  exact (key _ _ hrel).1 (hmemE 0 (Nat.zero_le _))

/-- **The hop from an initial edge is at least as long as the track.** -/
lemma trackLength_le_hopLen {X : Finset Plane} (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X)
    {p : Plane × Plane} (hu : s(p.1, p.2) ∈ unitEdges X) (hinit : Initial X p) {m : ℕ}
    (hmv : ∀ k < m, ∃ q, LeftStep X ((stepL X)^[k] p) q)
    (hstop : ¬ ∃ q, LeftStep X ((stepL X)^[m] p) q) :
    trackLength X (allTrackOf X s(p.1, p.2)) ≤ m := by
  by_cases hR : s(p.1, p.2) ∈ rhombusEdges X
  · have hT : allTrackOf X s(p.1, p.2) ∈ tracks X := by
      rw [allTrackOf_of_mem_rhombusEdges hR]; exact Finset.mem_image_of_mem _ hR
    have h1 := trackLength_add_one_le_card hX htri hT
    have h2 := Finset.card_le_card (allTrackOf_subset_hop hX htri hinit hmv hstop)
    have h3 := Finset.card_image_le (s := Finset.range (m + 1))
      (f := fun k => s(((stepL X)^[k] p).1, ((stepL X)^[k] p).2))
    rw [Finset.card_range] at h3
    omega
  · rw [allTrackOf_of_not_mem hu hR, trackLength_singleton hX htri hu hR]
    exact Nat.zero_le _

/-- The step of a left move is a unit vector at angle less than `π/6` from the left normal. -/
lemma LeftStep.step_bounds {X : Finset Plane} (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X)
    {p q : Plane × Plane} (h : LeftStep X p q) :
    |inner ℝ (q.1 - p.1) (p.2 - p.1)| < 1 / 2 ∧
      aStar < inner ℝ (q.1 - p.1) (rot (p.2 - p.1)) := by
  obtain ⟨hR, h1, h2, h3, h4, hpar, hdet⟩ := h
  set u := p.2 - p.1 with hu_def
  have hu : ‖u‖ = 1 := by rw [hu_def, ← dist_eq_norm, dist_comm]; exact h1
  obtain ⟨d1, d2⟩ := rhombus_diagonals_gt_one hX htri hR h1 h2 h3 h4
  have hw : ‖q.1 - p.1‖ = 1 := by rw [← dist_eq_norm]; exact h4
  have hd : q.2 = p.1 + (q.1 - p.1) + u := by rw [← hpar]; abel
  have hbc : p.2 = p.1 + u := by rw [hu_def]; abel
  rw [dist_eq_norm, hd, show p.1 - (p.1 + (q.1 - p.1) + u) = -((q.1 - p.1) + u) by abel,
    norm_neg] at d1
  rw [dist_eq_norm, hbc, show p.1 + u - q.1 = u - (q.1 - p.1) by abel] at d2
  have e1 : ‖(q.1 - p.1) + u‖ ^ 2 = 2 + 2 * inner ℝ (q.1 - p.1) u := by
    rw [norm_add_sq_real, hw, hu]; ring
  have e2 : ‖u - (q.1 - p.1)‖ ^ 2 = 2 - 2 * inner ℝ (q.1 - p.1) u := by
    rw [norm_sub_sq_real, hw, hu, real_inner_comm]; ring
  have s1 : 1 < ‖(q.1 - p.1) + u‖ ^ 2 := by nlinarith
  have s2 : 1 < ‖u - (q.1 - p.1)‖ ^ 2 := by nlinarith
  have hi : |inner ℝ (q.1 - p.1) u| < 1 / 2 := abs_lt.2 ⟨by linarith, by linarith⟩
  refine ⟨hi, ?_⟩
  have hpos : 0 < inner ℝ (q.1 - p.1) (rot u) := by rw [inner_rot_eq_det2]; exact hdet
  have e := inner_sq_add_inner_rot_sq u (q.1 - p.1)
  rw [hw, hu] at e
  have hsq : inner ℝ (q.1 - p.1) u ^ 2 < 1 / 4 := by
    have := sq_abs (inner ℝ (q.1 - p.1) u)
    nlinarith [abs_nonneg (inner ℝ (q.1 - p.1) u)]
  exact aStar_lt_of_sq hpos (by nlinarith)

/-- **Displacement of the hop**: after `m` moves the hop has advanced by at least `a* m` along the
left normal of the edge and by at most `m / 2` along the edge. -/
lemma hop_displacement {X : Finset Plane} (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X)
    (p : Plane × Plane) {m : ℕ} (hmv : ∀ k < m, ∃ q, LeftStep X ((stepL X)^[k] p) q) :
    aStar * m ≤ inner ℝ (((stepL X)^[m] p).1 - p.1) (rot (p.2 - p.1)) ∧
      |inner ℝ (((stepL X)^[m] p).1 - p.1) (p.2 - p.1)| ≤ m / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun k hk => hmv k (by omega))
    have hs := stepL_spec (hmv m (by omega))
    obtain ⟨b1, b2⟩ := LeftStep.step_bounds hX htri hs
    rw [iterate_stepL_sub] at b1 b2
    rw [Function.iterate_succ_apply']
    set r := (stepL X)^[m] p
    have e : (stepL X r).1 - p.1 = ((stepL X r).1 - r.1) + (r.1 - p.1) := by abel
    rw [e, inner_add_left, inner_add_left]
    push_cast
    constructor
    · linarith
    · calc |inner ℝ ((stepL X r).1 - r.1) (p.2 - p.1) + inner ℝ (r.1 - p.1) (p.2 - p.1)|
          ≤ |inner ℝ ((stepL X r).1 - r.1) (p.2 - p.1)| + |inner ℝ (r.1 - p.1) (p.2 - p.1)| :=
            abs_add_le _ _
        _ ≤ 1 / 2 + m / 2 := by linarith
        _ = (m + 1) / 2 := by ring


lemma inner_rot_rot_eq (x y : Plane) : inner ℝ (rot x) (rot y) = inner ℝ x y := by
  rw [inner_coord, inner_coord]; simp [rot]; ring

/-- **The algebra of the macroscopic-port margin.**  Let `u, τ` be unit vectors with
`⟨u, τ⟩ ≤ -(1/2 - κ)`, and let `Δ` have coordinates `β = ⟨Δ, J u⟩ ≥ a* m` and `|⟨Δ, u⟩| ≤ m / 2`.
If `(D/2) ν + Δ` (with `ν = -J τ`) lies in the disc of radius `D/2 + E`, then
`β² - 2 κ D β ≤ D E + E²`. -/
lemma margin_core {u τ Δ : Plane} (hu : ‖u‖ = 1) (hτ : ‖τ‖ = 1) {κ m D E : ℝ}
    (hκ0 : 0 ≤ κ) (hm : 0 ≤ m) (hD : 0 < D)
    (hβ : aStar * m ≤ inner ℝ Δ (rot u)) (hα : |inner ℝ Δ u| ≤ m / 2)
    (hc : inner ℝ u τ ≤ -(1 / 2 - κ))
    (hZ : ‖(D / 2) • (-rot τ) + Δ‖ ≤ D / 2 + E) :
    inner ℝ Δ (rot u) ^ 2 - 2 * κ * D * inner ℝ Δ (rot u) ≤ D * E + E ^ 2 := by
  set β := inner ℝ Δ (rot u) with hβdef
  set α := inner ℝ Δ u with hαdef
  set c := inner ℝ u τ with hcdef
  set s' := inner ℝ u (rot τ) with hsdef
  have ha := aStar_pos
  have hβ0 : 0 ≤ β := le_trans (mul_nonneg ha.le hm) hβ
  -- frame decompositions
  have hcs : c ^ 2 + s' ^ 2 = 1 := by
    have := inner_sq_add_inner_rot_sq τ u
    rw [hu, hτ] at this; rw [hcdef, hsdef]; linarith
  have hΔ : ‖Δ‖ ^ 2 = α ^ 2 + β ^ 2 := by
    have := inner_sq_add_inner_rot_sq u Δ
    rw [hu] at this; rw [hαdef, hβdef]; linarith
  have hframe : inner ℝ Δ (rot τ) = α * s' + β * c := by
    rw [inner_eq_frame u Δ (rot τ) hu, inner_rot_rot_eq, real_inner_comm u (rot τ),
      real_inner_comm u τ]
  -- the bound on `s'`
  set x := -c with hx
  have hx1 : 1 / 2 - κ ≤ x := by rw [hx]; linarith
  have hs'sq : s' ^ 2 ≤ 3 * (x + 2 * κ) ^ 2 := by
    have : s' ^ 2 = 1 - x ^ 2 := by rw [hx]; nlinarith
    rw [this]; nlinarith
  have hs' : |s'| ≤ √3 * (x + 2 * κ) := by
    have h3 : (√3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hpos : 0 ≤ √3 * (x + 2 * κ) := mul_nonneg (Real.sqrt_nonneg _) (by linarith)
    by_contra hcon
    push_neg at hcon
    have := mul_self_lt_mul_self hpos hcon
    rw [← sq, ← sq, sq_abs, mul_pow, h3] at this
    linarith
  -- the bound on `α`
  have hα' : √3 * |α| ≤ β := by
    have : aStar = √3 / 2 := rfl
    rw [this] at hβ
    nlinarith [Real.sqrt_nonneg 3]
  have h1 : |α * s'| ≤ β * (x + 2 * κ) := by
    rw [abs_mul]
    calc |α| * |s'| ≤ |α| * (√3 * (x + 2 * κ)) :=
          mul_le_mul_of_nonneg_left hs' (abs_nonneg _)
      _ = (√3 * |α|) * (x + 2 * κ) := by ring
      _ ≤ β * (x + 2 * κ) := mul_le_mul_of_nonneg_right hα' (by linarith)
  have hkey : α * s' + β * c ≤ 2 * κ * β := by
    have := le_abs_self (α * s')
    rw [hx] at h1
    linarith
  have hνΔ' : -(κ * D * β) ≤ inner ℝ ((D / 2) • (-rot τ)) Δ := by
    rw [real_inner_smul_left, inner_neg_left, real_inner_comm Δ (rot τ), hframe]
    have := mul_le_mul_of_nonneg_left hkey (by positivity : (0 : ℝ) ≤ D / 2)
    linarith
  have hnorm : ‖(D / 2) • (-rot τ)‖ = D / 2 := by
    rw [norm_smul, norm_neg, norm_rot, hτ, Real.norm_eq_abs, abs_of_pos (by positivity)]; ring
  have hsq := norm_add_sq_real ((D / 2) • (-rot τ)) Δ
  rw [hnorm, hΔ] at hsq
  have hZ2 : ‖(D / 2) • (-rot τ) + Δ‖ ^ 2 ≤ (D / 2 + E) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hZ 2
  nlinarith [sq_nonneg α]

end Erdos99
end

end HopMargin

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `HHAdjacencyGeometry`
-/

section HHAdjacencyGeometry

/-!
# `H–H` adjacency: the geometric inputs

Second part of the proof of `hh_edges_few` (see `HHAdjacency`):

* `longSides_H_pentagon`: a pentagonal degree-two face has zero or two long sides;
* `trackMate_side`: the far end of a matched port carries the opposite side vector, at distance at
  most the length of the track;
* `hh_port_equations`: the closure equations at an `H–H` port;
* `hh_label_locality`: the two faces of an `H–H` port have nearby labels;
* `long_side_margin`: the macroscopic-port margin;
* `long_sides_clustered`: the long side vectors cluster near boundedly many centres.
-/

open scoped BigOperators Real
open Filter Polynomial ComplexConjugate

@[expose] public noncomputable section

open Classical

namespace Erdos99

open LocalCharge QuadraticResponse DirectionPinning EstablishedExternalResults

/-! ## The geometric inputs -/

/-- Basic facts on the sides of a face: every oriented side has length one, and a good face has
at most six oriented sides. -/
theorem face_side_facts :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ∀ G : GoodFaces X,
      ∀ F ∈ G.good, (orientedSides X F).card ≤ 6 ∧ ∀ ab ∈ orientedSides X F, ‖ab.2 - ab.1‖ = 1 := by
  filter_upwards [card_orientedSides] with n hcard hfm X hX G F hF
  have hFe : F ∈ exceptionalFaces X := (mem_exceptionalFinset hX.1.2).1 (G.good_subset hF)
  refine ⟨?_, fun ab hab => ?_⟩
  · rw [hcard hfm X hX F hFe]
    simp only [GoodFaces.good, Finset.mem_union] at hF
    rcases hF with (h | h) | h
    · rw [(G.pent_sub F h).2]; norm_num
    · rw [(G.hex_sub F h).2]
    · rw [(G.act_sub F h).2]; norm_num
  · have hb : s(ab.1, ab.2) ∈ bdryEdges (cUnitEdges X) F := (Finset.mem_filter.1 hab).2.1
    have hc : s(ab.1, ab.2) ∈ cUnitEdges X := (Finset.mem_filter.1 hb).1
    have hd := (mem_unitPairs.1 hc).2.2
    rw [← dist_eq_norm, dist_comm]; exact hd

/-- Every long side of a face comes from a port of the face that is not short. -/
theorem longSide_edge {X : Finset Plane} {L : ℝ} {F : Set ℂ} (hF : F ∈ exceptionalFaces X)
    {ab : ℂ × ℂ} (hab : ab ∈ longSides X L F) :
    ∃ e ∈ unitEdges X, Sym2.map toC e = s(ab.1, ab.2) ∧ IsPort X (Sum.inl F) e ∧
      ¬ (trackLength X (allTrackOf X e) : ℝ) < L := by
  obtain ⟨hos, hnot⟩ := Finset.mem_filter.1 hab
  have hb : s(ab.1, ab.2) ∈ bdryEdges (cUnitEdges X) F := (Finset.mem_filter.1 hos).2.1
  have hc : s(ab.1, ab.2) ∈ cUnitEdges X := (Finset.mem_filter.1 hb).1
  rw [cUnitEdges_eq_image] at hc
  obtain ⟨e, he, hmap⟩ := Finset.mem_image.1 hc
  have hp : IsPort X (Sum.inl F) e := ⟨hF, hmap ▸ hb⟩
  exact ⟨e, he, hmap, hp, fun hlt => hnot ⟨e, Finset.mem_filter.2 ⟨he, hp, hlt⟩, hmap⟩⟩

lemma nonempty_of_mem_exceptionalFaces {X : Finset Plane} {F : Set ℂ}
    (hF : F ∈ exceptionalFaces X) : F.Nonempty := by
  obtain ⟨x, hx, rfl⟩ := mem_faces_iff.1 hF.1.1
  exact ⟨x, mem_connectedComponentIn hx⟩

/-- An unordered side determines its counterclockwise orientation. -/
lemma orientedSides_injOn {X : Finset Plane} {F : Set ℂ} (hne : F.Nonempty) :
    Set.InjOn (fun ab : ℂ × ℂ => s(ab.1, ab.2)) (orientedSides X F) := by
  intro ab hab cd hcd h
  obtain ⟨z, hz⟩ := hne
  have h1 := (Finset.mem_filter.1 hab).2.2 z hz
  have h2 := (Finset.mem_filter.1 hcd).2.2 z hz
  rcases Sym2.eq_iff.1 h with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact Prod.ext e1 e2
  · exfalso
    have hab' : ab.1 ≠ ab.2 := by
      intro he; rw [wc, he, sub_self, div_zero] at h1; simp at h1
    have : wc cd.1 cd.2 z = 1 - wc ab.1 ab.2 z := by
      rw [← e1, ← e2]; exact wc_swap hab' z
    rw [this, Complex.sub_im, Complex.one_im] at h2
    linarith

/-- The oriented sides of an exceptional face correspond to its boundary edges. -/
lemma image_orientedSides_eq :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ∀ F ∈ exceptionalFaces X,
      (orientedSides X F).image (fun ab : ℂ × ℂ => s(ab.1, ab.2)) =
        bdryEdges (cUnitEdges X) F := by
  filter_upwards [card_orientedSides] with n hcard hfm X hX F hF
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro e he
    obtain ⟨ab, hab, rfl⟩ := Finset.mem_image.1 he
    exact (Finset.mem_filter.1 hab).2.1
  · rw [Finset.card_image_of_injOn (orientedSides_injOn (nonempty_of_mem_exceptionalFaces hF)),
      hcard hfm X hX F hF]
    rfl

/-- The number of short sides of a face equals its number of short ports, so
`#longSides = faceSize - shortDeg`. -/
lemma card_longSides :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ∀ (L : ℝ),
      ∀ F ∈ exceptionalFaces X, (longSides X L F).card + (shortPorts X L F).card = faceSize X F := by
  filter_upwards [card_orientedSides, image_orientedSides_eq] with n hcard himg hfm X hX L F hF
  set S := (orientedSides X F).filter
    (fun ab => ∃ e ∈ shortPorts X L F, Sym2.map toC e = s(ab.1, ab.2)) with hS
  have hinj := orientedSides_injOn (X := X) (nonempty_of_mem_exceptionalFaces hF)
  have hSimg : S.image (fun ab : ℂ × ℂ => s(ab.1, ab.2)) = (shortPorts X L F).image (Sym2.map toC) := by
    ext e
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨ab, hab, rfl⟩
      obtain ⟨-, f, hf, hfe⟩ := Finset.mem_filter.1 hab
      exact ⟨f, hf, hfe⟩
    · rintro ⟨f, hf, rfl⟩
      have hp := (Finset.mem_filter.1 hf).2.1
      have hb : Sym2.map toC f ∈ bdryEdges (cUnitEdges X) F := hp.2
      rw [← himg hfm X hX F hF] at hb
      obtain ⟨ab, hab, habe⟩ := Finset.mem_image.1 hb
      exact ⟨ab, Finset.mem_filter.2 ⟨hab, f, hf, habe.symm⟩, habe⟩
  have hScard : S.card = (shortPorts X L F).card := by
    rw [← Finset.card_image_of_injOn (hinj.mono (Finset.filter_subset _ _)), hSimg,
      Finset.card_image_of_injective _ (Sym2.map.injective toC.injective)]
  rw [← hScard, ← hcard hfm X hX F hF, longSides, add_comm]
  exact Finset.card_filter_add_card_filter_not _

/-- **The long sides of a pentagonal `H` face**: none (an activated pentagon) or exactly two (an
ordinary pentagon). -/
theorem longSides_H_pentagon :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ (L : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane)), IsMarking X L G mk →
      ∀ F ∈ (trackGraph X L G mk).Hs G.good, G.kMult F = 1 →
        longSides X L F = ∅ ∨ ∃ ab₁ ∈ longSides X L F, ∃ ab₂ ∈ longSides X L F, ab₁ ≠ ab₂ ∧
          longSides X L F = {ab₁, ab₂} := by
  filter_upwards [card_longSides, card_trackEnds] with n hcl hends hfm X hX htri L G mk hmk F hFH hk
  have hFg : F ∈ G.good := (Finset.mem_filter.1 hFH).1
  have hdeg : (trackGraph X L G mk).deg F = 2 := (Finset.mem_filter.1 hFH).2
  rw [trackGraph_deg (hends hfm X hX htri) L G mk hFg] at hdeg
  obtain ⟨hsub, hcard⟩ := hmk F hFg
  have hsd : (shortPorts X L F).card = 2 + G.marks F := by
    rw [← Finset.card_sdiff_add_card_eq_card hsub, hdeg, hcard]
  have hnhex : F ∉ G.hex := by
    intro h; simp only [GoodFaces.kMult, h, if_true] at hk; norm_num at hk
  have hsep := hX.1.2
  have key : ∀ m, (longSides X L F).card = m → (m = 0 ∨ m = 2) →
      longSides X L F = ∅ ∨ ∃ ab₁ ∈ longSides X L F, ∃ ab₂ ∈ longSides X L F, ab₁ ≠ ab₂ ∧
        longSides X L F = {ab₁, ab₂} := by
    rintro m hm (rfl | rfl)
    · exact Or.inl (Finset.card_eq_zero.1 hm)
    · obtain ⟨x, y, hxy, he⟩ := Finset.card_eq_two.1 hm
      exact Or.inr ⟨x, by simp [he], y, by simp [he], hxy, he⟩
  simp only [GoodFaces.good, Finset.mem_union] at hFg
  rcases hFg with (hp | hh) | ha
  · obtain ⟨hex, h5⟩ := G.pent_sub F hp
    have hl := hcl hfm X hX L F ((mem_exceptionalFinset hsep).1 hex)
    have hm : G.marks F = 1 := by simp [GoodFaces.marks, hp]
    exact key _ rfl (Or.inr (by omega))
  · exact absurd hh hnhex
  · obtain ⟨hex, h5⟩ := G.act_sub F ha
    have hl := hcl hfm X hX L F ((mem_exceptionalFinset hsep).1 hex)
    have hnp : F ∉ G.pent := fun hp => Finset.disjoint_left.1 G.disj hp ha
    have hm : G.marks F = 3 := by simp [GoodFaces.marks, hnp, hnhex]
    exact key _ rfl (Or.inl (by omega))

lemma srcLen_le_trackLength_allTrackOf (X : Finset Plane) (e : Sym2 Plane) :
    srcLen X e ≤ trackLength X (allTrackOf X e) := by
  unfold srcLen trackLength
  refine Finset.card_le_card fun R hR => ?_
  obtain ⟨hR1, f, hf, hsub⟩ := Finset.mem_filter.1 hR
  obtain ⟨hf1, hf2⟩ := mem_trackOf.1 hf
  exact Finset.mem_filter.2 ⟨hR1, f, Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hf1).1, hf2⟩, hsub⟩

/-- **The far end of a matched port** carries the opposite side vector: if `(F, e)` is a port of an
exceptional face whose track ends at a face, then the oriented side of the far face along the far
edge is the reversal (as a vector) of the oriented side of `F` along `e`. -/
theorem trackMate_side :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ F ∈ exceptionalFaces X, ∀ e ∈ unitEdges X, ∀ ab ∈ orientedSides X F,
        Sym2.map toC e = s(ab.1, ab.2) →
        (otherEnd X (F, e)).1 = Sum.inl (nodeFace (otherEnd X (F, e)).1) →
        ∃ ab' ∈ orientedSides X (trackMate X (F, e)).1,
          Sym2.map toC (trackMate X (F, e)).2 = s(ab'.1, ab'.2) ∧
          ab'.2 - ab'.1 = -(ab.2 - ab.1) ∧
          dist ab'.1 ab.2 ≤ trackLength X (allTrackOf X e) := by
  filter_upwards [card_trackEnds, far_end_cases] with n hends hfar hfm X hX htri F hF e he ab hab
    hmap hmated
  have hsep := hX.1.2
  obtain ⟨A, B⟩ := ab
  have hAB := (Finset.mem_product.1 (Finset.mem_filter.1 hab).1)
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hAB.1
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hAB.2
  have hdab : dist a b = 1 := dist_eq_one_of_mem_orientedSides hab
  have hee : e = s(b, a) := by
    have : Sym2.map toC e = Sym2.map toC s(b, a) := by rw [hmap, Sym2.map_mk]; exact Sym2.eq_swap
    exact Sym2.map.injective toC.injective this
  set p : Plane × Plane := (b, a) with hpdef
  have hp : p ∈ X ×ˢ X := Finset.mem_product.2 ⟨hb, ha⟩
  have hpd : dist p.1 p.2 = 1 := by rw [dist_comm]; exact hdab
  have hFf : F ∈ exceptionalFinset X := (mem_exceptionalFinset hsep).2 hF
  have hpF : IsPort X (Sum.inl F) e := ⟨hF, hmap ▸ (Finset.mem_filter.1 hab).2.1⟩
  obtain ⟨hTe, -⟩ := trackEnds_eq_otherEnd (hends hfm X hX htri) hFf he hpF
  set h := hopEnd X p with hhdef
  have hsub : h.2 - h.1 = a - b := hopEnd_sub p
  have hhX := hopEnd_mem hp
  have hmemT : s(h.1, h.2) ∈ allTrackOf X e := by
    obtain ⟨m, hm, hmv, -⟩ := exists_hopLen hp
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · rw [hhdef, ← hm]
      show s(b, a) ∈ allTrackOf X e
      rw [← hee]; exact mem_allTrackOf_self he
    · have h1 := iterate_mem_trackOf hmv m le_rfl hpos
      have h0 : s(p.1, p.2) ∈ rhombusEdges X := (stepL_spec (hmv 0 hpos)).rhombusEdge
      rw [hm] at h1
      rw [hee, allTrackOf_of_mem_rhombusEdges h0]
      exact h1
  have hunitT : s(h.1, h.2) ∈ unitEdges X := (Finset.mem_filter.1 hmemT).1
  -- an end at `s(h.1, h.2)` different from `(F, e)` is the other end
  have hother : ∀ N, (N, s(h.1, h.2)) ∈ trackEnds X (allTrackOf X e) →
      (N, s(h.1, h.2)) ≠ (Sum.inl F, e) → otherEnd X (F, e) = (N, s(h.1, h.2)) := by
    intro N hN hne
    rw [hTe, Finset.mem_insert, Finset.mem_singleton] at hN
    rcases hN with h' | h'
    · exact absurd h' hne
    · exact h'.symm
  by_cases hd : ∃ G ∈ exceptionalFaces X, (toC h.1, toC h.2) ∈ orientedSides X G
  · obtain ⟨G, hG, hGs⟩ := hd
    have hGf : G ∈ exceptionalFinset X := (mem_exceptionalFinset hsep).2 hG
    have hend : (Sum.inl G, s(h.1, h.2)) ∈ trackEnds X (allTrackOf X e) :=
      mem_trackEnds.2 ⟨Finset.mem_union_left _ (Finset.mem_map_of_mem _ hGf), hmemT,
        hG, (Finset.mem_filter.1 hGs).2.1⟩
    have hne : (Sum.inl G, s(h.1, h.2)) ≠ ((Sum.inl F, e) : PortNode × Sym2 Plane) := by
      intro heq
      simp only [Prod.mk.injEq, Sum.inl.injEq] at heq
      obtain ⟨rfl, he2⟩ := heq
      have hs : s((toC h.1, toC h.2).1, (toC h.1, toC h.2).2) =
          s(((toC a, toC b) : ℂ × ℂ).1, ((toC a, toC b) : ℂ × ℂ).2) := by
        have h3 := congrArg (Sym2.map toC) he2
        rw [Sym2.map_mk] at h3
        exact h3.trans hmap
      have := orientedSides_injOn (nonempty_of_mem_exceptionalFaces hG) hGs hab hs
      simp only [Prod.mk.injEq] at this
      have e1 := toC.injective this.1
      have e2 := toC.injective this.2
      rw [e1, e2] at hsub
      have : a = b := by
        have h2 : (2 : ℝ) • (a - b) = 0 := by
          rw [two_smul]; nth_rewrite 1 [← hsub]; abel
        have := (smul_eq_zero.1 h2).resolve_left (by norm_num)
        exact sub_eq_zero.1 this
      rw [this, dist_self] at hdab; norm_num at hdab
    have hoe := hother _ hend hne
    have hmate : trackMate X (F, e) = (G, s(h.1, h.2)) := by
      rw [trackMate, hoe]; rfl
    rw [hmate]
    refine ⟨(toC h.1, toC h.2), hGs, rfl, ?_, ?_⟩
    · simp only
      rw [← map_sub, hsub, map_sub]; ring
    · simp only
      rw [dist_toC]
      refine (dist_hopEnd_le hp).trans ?_
      show ((srcLen X s(b, a) : ℕ) : ℝ) ≤ _
      rw [← hee]
      exact_mod_cast srcLen_le_trackLength_allTrackOf X e
  · exfalso
    have hcap : hopDest X p = .cap := by rw [hopDest, dif_neg hd]
    have hcases := hfar hfm X hX htri p hp hpd hcap
    have key : ∀ P ∈ ccwHullSides X, IsPort X (Sum.inr P) s(h.1, h.2) → False := by
      intro P hP hport
      have hend : (Sum.inr P, s(h.1, h.2)) ∈ trackEnds X (allTrackOf X e) :=
        mem_trackEnds.2 ⟨Finset.mem_union_right _ (Finset.mem_map_of_mem _ hP), hmemT, hport⟩
      have hoe := hother _ hend (by simp)
      rw [hoe] at hmated
      cases hmated
    rcases hcases with hu | ⟨P, hP, hPd, Fc, hc, hbd, -⟩
    · have hP := (Finset.mem_filter.1 hu).1
      refine key _ hP ⟨hP, hunitT, ?_⟩
      rw [if_pos (Finset.mem_filter.1 hu).2]
      exact Sym2.eq_swap
    · exact key P hP ⟨hP, hunitT, by rw [if_neg hPd.ne']; exact ⟨Fc, hc, hbd⟩⟩


/-- The marked sum over the short ports and the long-side sum add up to the closure sum, zero. -/
lemma markedSum_short_add_longSum :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ∀ (L : ℝ),
      ∀ F ∈ exceptionalFaces X, markedSum X F (shortPorts X L F) + longSum X L F = 0 := by
  filter_upwards [orientedSides_sum_eq_zero] with n h hfm X hX L F hF
  rw [markedSum, longSum, longSides, Finset.sum_filter_add_sum_filter_not]
  exact h hfm X hX F hF

lemma markedSum_union {X : Finset Plane} {F : Set ℂ} {S₁ S₂ : Finset (Sym2 Plane)}
    (hd : Disjoint S₁ S₂) : markedSum X F (S₁ ∪ S₂) = markedSum X F S₁ + markedSum X F S₂ := by
  unfold markedSum
  rw [← Finset.sum_union]
  · congr 1
    ext ab
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨h, e, he | he, hm⟩
      · exact Or.inl ⟨h, e, he, hm⟩
      · exact Or.inr ⟨h, e, he, hm⟩
    · rintro (⟨h, e, he, hm⟩ | ⟨h, e, he, hm⟩)
      · exact ⟨h, e, Or.inl he, hm⟩
      · exact ⟨h, e, Or.inr he, hm⟩
  · refine Finset.disjoint_filter.2 fun ab _ ⟨e₁, h₁, m₁⟩ ⟨e₂, h₂, m₂⟩ => ?_
    have : e₁ = e₂ := Sym2.map.injective toC.injective (m₁.trans m₂.symm)
    exact Finset.disjoint_left.1 hd h₁ (this ▸ h₂)

/-- The sides of a face along a set of its ports are in bijection with these ports. -/
lemma card_filter_orientedSides :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ∀ F ∈ exceptionalFaces X,
      ∀ S : Finset (Sym2 Plane), (∀ e ∈ S, IsPort X (Sum.inl F) e) →
        ((orientedSides X F).filter
          (fun ab => ∃ e ∈ S, Sym2.map toC e = s(ab.1, ab.2))).card = S.card := by
  filter_upwards [image_orientedSides_eq] with n himg hfm X hX F hF S hS
  have hinj := orientedSides_injOn (X := X) (nonempty_of_mem_exceptionalFaces hF)
  have hSimg : ((orientedSides X F).filter
      (fun ab => ∃ e ∈ S, Sym2.map toC e = s(ab.1, ab.2))).image
        (fun ab : ℂ × ℂ => s(ab.1, ab.2)) = S.image (Sym2.map toC) := by
    ext e
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨ab, hab, rfl⟩
      obtain ⟨-, f, hf, hfe⟩ := Finset.mem_filter.1 hab
      exact ⟨f, hf, hfe⟩
    · rintro ⟨f, hf, rfl⟩
      have hb : Sym2.map toC f ∈ bdryEdges (cUnitEdges X) F := (hS f hf).2
      rw [← himg hfm X hX F hF] at hb
      obtain ⟨ab, hab, habe⟩ := Finset.mem_image.1 hb
      exact ⟨ab, Finset.mem_filter.2 ⟨hab, f, hf, habe.symm⟩, habe⟩
  rw [← Finset.card_image_of_injOn (hinj.mono (Finset.filter_subset _ _)), hSimg,
    Finset.card_image_of_injective _ (Sym2.map.injective toC.injective)]

/-- **The closure equation at a degree-two face**: given an unmarked short port `e` of a
degree-two good face `F`, with oriented side `ab`, the other unmarked short port gives a unit
vector `u` with `‖k τ + (b - a) + u + Z‖ ≤ tol`. -/
theorem H_face_equation :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ (L tol : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane))
        (lab : Set ℂ → Plane × Plane), IsMarking X L G mk → LabelledBy X tol G mk lab →
      ∀ F ∈ (trackGraph X L G mk).Hs G.good, ∀ e ∈ shortPorts X L F \ mk F,
      ∀ ab ∈ orientedSides X F, Sym2.map toC e = s(ab.1, ab.2) →
        ∃ u : ℂ, ‖u‖ = 1 ∧
          ‖(G.kMult F : ℂ) * labDir lab F + (ab.2 - ab.1) + u + longSum X L F‖ ≤ tol := by
  filter_upwards [card_trackEnds, markedSum_short_add_longSum, card_filter_orientedSides,
    face_side_facts] with n hends hzero hcardf hside hfm X hX htri L tol G mk lab hmk hlab F hFH
    e he ab hab hmap
  have hFg : F ∈ G.good := (Finset.mem_filter.1 hFH).1
  have hdeg : (trackGraph X L G mk).deg F = 2 := (Finset.mem_filter.1 hFH).2
  rw [trackGraph_deg (hends hfm X hX htri) L G mk hFg] at hdeg
  have hsub := (hmk F hFg).1
  have hFe : F ∈ exceptionalFaces X := (mem_exceptionalFinset hX.1.2).1 (G.good_subset hFg)
  set N := shortPorts X L F \ mk F with hN
  have hports : ∀ f ∈ N, IsPort X (Sum.inl F) f :=
    fun f hf => (Finset.mem_filter.1 (Finset.sdiff_subset hf)).2.1
  have hc := hcardf hfm X hX F hFe N hports
  rw [hdeg] at hc
  obtain ⟨x, y, hxy, hxyeq⟩ := Finset.card_eq_two.1 hc
  have habN : ab ∈ (orientedSides X F).filter
      (fun ab => ∃ f ∈ N, Sym2.map toC f = s(ab.1, ab.2)) :=
    Finset.mem_filter.2 ⟨hab, e, he, hmap⟩
  have hsideU := (hside hfm X hX G F hFg).2
  have hxs : x ∈ orientedSides X F := by
    have : x ∈ (orientedSides X F).filter
        (fun ab => ∃ f ∈ N, Sym2.map toC f = s(ab.1, ab.2)) := by rw [hxyeq]; simp
    exact (Finset.mem_filter.1 this).1
  have hys : y ∈ orientedSides X F := by
    have : y ∈ (orientedSides X F).filter
        (fun ab => ∃ f ∈ N, Sym2.map toC f = s(ab.1, ab.2)) := by rw [hxyeq]; simp
    exact (Finset.mem_filter.1 this).1
  have hNsum : markedSum X F N = (x.2 - x.1) + (y.2 - y.1) := by
    rw [markedSum, hxyeq, Finset.sum_pair hxy]
  rw [hxyeq, Finset.mem_insert, Finset.mem_singleton] at habN
  have h0 := hzero hfm X hX L F hFe
  rw [← Finset.union_sdiff_of_subset hsub, markedSum_union Finset.disjoint_sdiff, ← hN,
    hNsum] at h0
  have hl := (hlab.2 F hFg).2.1
  rw [GoodFaces.markMult_eq] at hl
  have key : ∀ v : ℂ, markedSum X F (mk F) + ((ab.2 - ab.1) + v) + longSum X L F = 0 →
      ‖(G.kMult F : ℂ) * labDir lab F + (ab.2 - ab.1) + v + longSum X L F‖ ≤ tol := by
    intro v hv
    calc _ = ‖-(markedSum X F (mk F) - (G.kMult F : ℂ) * toC (sideDir (lab F)))‖ := by
          congr 1; rw [labDir]; linear_combination hv
      _ ≤ tol := by rw [norm_neg]; exact hl
  rcases habN with rfl | rfl
  · exact ⟨_, hsideU y hys, key _ h0⟩
  · exact ⟨_, hsideU x hxs, key _ (by rw [← h0]; ring)⟩

/-- **The equations at an `H–H` port** (closure of both faces, and the two ends of a track carry
opposite side vectors).  At an `H–H` port `(F, e)` with mate `(F', e')` there are unit vectors
`s, u, w` with `‖k τ + s + u + Z‖ ≤ tol` and `‖l τ' - s + w + W‖ ≤ tol`, where `τ, τ'` are the
label directions, `k, l` the multiplicities and `Z, W` the long-side sums of `F, F'`. -/
theorem hh_port_equations :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ (L tol : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane))
        (lab : Set ℂ → Plane × Plane), IsMarking X L G mk → LabelledBy X tol G mk lab →
      ∀ q ∈ hhPorts X L G mk, ∃ s u w : ℂ, ‖s‖ = 1 ∧ ‖u‖ = 1 ∧ ‖w‖ = 1 ∧
        ‖(G.kMult q.1 : ℂ) * labDir lab q.1 + s + u + longSum X L q.1‖ ≤ tol ∧
        ‖(G.kMult (trackMate X q).1 : ℂ) * labDir lab (trackMate X q).1 - s + w +
          longSum X L (trackMate X q).1‖ ≤ tol := by
  filter_upwards [H_face_equation, trackMate_side, image_orientedSides_eq, face_side_facts] with
    n hface hmate himg hside hfm X hX htri L tol G mk lab hmk hlab q hq
  obtain ⟨hqu, hmated, hH1, hH2⟩ := Finset.mem_filter.1 hq
  obtain ⟨F, e⟩ := q
  obtain ⟨hFg, hsp, hnm⟩ := mem_unmarkedPorts.1 hqu
  obtain ⟨he, hpF, -⟩ := Finset.mem_filter.1 hsp
  have hFe : F ∈ exceptionalFaces X := hpF.1
  have hb := hpF.2
  rw [← himg hfm X hX F hFe] at hb
  obtain ⟨ab, hab, habe⟩ := Finset.mem_image.1 hb
  obtain ⟨u, hu, hequ⟩ := hface hfm X hX htri L tol G mk lab hmk hlab F hH1 e
    (Finset.mem_sdiff.2 ⟨hsp, hnm⟩) ab hab habe.symm
  obtain ⟨ab', hab', hmap', hvec, -⟩ := hmate hfm X hX htri F hFe e he ab hab habe.symm hmated.1
  obtain ⟨hFg', hsp', hnm'⟩ := mem_unmarkedPorts.1 hmated.2
  obtain ⟨w, hw, heqw⟩ := hface hfm X hX htri L tol G mk lab hmk hlab _ hH2 _
    (Finset.mem_sdiff.2 ⟨hsp', hnm'⟩) ab' hab' hmap'
  refine ⟨ab.2 - ab.1, u, w, (hside hfm X hX G F hFg).2 ab hab, hu, hw, hequ, ?_⟩
  rw [hvec, ← sub_eq_add_neg] at heqw
  exact heqw

/-- **Label locality**: the two faces of an `H–H` port have nearby label directions. -/
theorem hh_label_locality {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ c > 0, ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ (L tol : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane))
        (lab : Set ℂ → Plane × Plane), L ≤ c * diam X → tol ≤ c → LabelledBy X tol G mk lab →
      ∀ q ∈ hhPorts X L G mk, ‖labDir lab q.1 - labDir lab (trackMate X q).1‖ ≤ ρ := by
  have hκ : (0 : ℝ) < (ρ / 16) ^ 2 / 300 := by positivity
  have ht : Tendsto (fun n => minDiam n ^ (-(2 / 9 : ℝ))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num)).comp tendsto_minDiam
  refine ⟨ρ / 12, by positivity, ?_⟩
  filter_upwards [trackMate_side, image_orientedSides_eq, face_side_facts,
    eventually_roundData_rate, ht.eventually (ge_mem_nhds hκ),
    tendsto_minDiam.eventually_ge_atTop (max 1 (8 / ρ))] with
    n hmate himg hside hround hsmall hD hfm X hX htri L tol G mk lab hL htol hlab q hq
  rw [← hX.diam_eq] at hsmall hD
  set D := diam X with hDdef
  have hD1 : 1 ≤ D := le_trans (le_max_left _ _) hD
  have hDρ : 8 / ρ ≤ D := le_trans (le_max_right _ _) hD
  have hD0 : 0 < D := by linarith
  obtain ⟨hqu, hmated, -, -⟩ := Finset.mem_filter.1 hq
  obtain ⟨F, e⟩ := q
  obtain ⟨hFg, hsp, -⟩ := mem_unmarkedPorts.1 hqu
  obtain ⟨he, hpF, hlen⟩ := Finset.mem_filter.1 hsp
  have hFe : F ∈ exceptionalFaces X := hpF.1
  have hb := hpF.2
  rw [← himg hfm X hX F hFe] at hb
  obtain ⟨ab, hab, habe⟩ := Finset.mem_image.1 hb
  obtain ⟨ab', hab', -, -, hd'⟩ := hmate hfm X hX htri F hFe e he ab hab habe.symm hmated.1
  obtain ⟨hFg', -, -⟩ := mem_unmarkedPorts.1 hmated.2
  have h1 := (hlab.2 F hFg).2.2 ab hab
  have h2 := (hlab.2 _ hFg').2.2 ab' hab'
  have h3 := (hside hfm X hX G F hFg).2 ab hab
  have htD : tol * D ≤ ρ / 12 * D := mul_le_mul_of_nonneg_right htol hD0.le
  have hdist : dist (lab F).1 (lab (trackMate X (F, e)).1).1 ≤ ρ / 4 * D + 1 := by
    rw [← dist_toC, dist_eq_norm]
    have e1 : toC (lab F).1 - toC (lab (trackMate X (F, e)).1).1 =
        -(ab.1 - toC (lab F).1) - (ab.2 - ab.1) + (ab.2 - ab'.1) +
          (ab'.1 - toC (lab (trackMate X (F, e)).1).1) := by ring
    rw [e1]
    have n1 := norm_add_le (-(ab.1 - toC (lab F).1) - (ab.2 - ab.1) + (ab.2 - ab'.1))
      (ab'.1 - toC (lab (trackMate X (F, e)).1).1)
    have n2 := norm_add_le (-(ab.1 - toC (lab F).1) - (ab.2 - ab.1)) (ab.2 - ab'.1)
    have n3 := norm_sub_le (-(ab.1 - toC (lab F).1)) (ab.2 - ab.1)
    rw [norm_neg] at n3
    have n4 : ‖ab.2 - ab'.1‖ ≤ L := by
      rw [← dist_eq_norm, dist_comm]; exact hd'.trans hlen.le
    linarith
  obtain ⟨O, η, hR⟩ := hround X hX
  have hp1 := mem_ccwHullSides.1 (Finset.mem_filter.1 (hlab.2 F hFg).1).1
  have hp2 := mem_ccwHullSides.1 (Finset.mem_filter.1 (hlab.2 _ hFg').1).1
  have hs := sideDir_sub_le hR hp1 hp2
  rw [labDir, labDir, ← map_sub, LinearIsometryEquiv.norm_map]
  refine hs.trans ?_
  have hsq : √(3 * (100 * D ^ (-(2 / 9 : ℝ)))) ≤ ρ / 16 := by
    rw [show ρ / 16 = √((ρ / 16) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hfrac : 2 * dist (lab F).1 (lab (trackMate X (F, e)).1).1 / D ≤ ρ / 2 + ρ / 4 := by
    rw [div_le_iff₀ hD0]
    have : 8 ≤ ρ * D := by rwa [div_le_iff₀ hρ, mul_comm] at hDρ
    nlinarith
  linarith

/-- **The macroscopic-port margin** (Verification Guide §6.2): the long side vectors of a
saturated good face have projection at most `1/2 - κ'` on the direction of its label. -/
theorem long_side_margin' {lam : ℝ} (hlam : 0 < lam) :
    ∃ κ' > 0, ∃ c > 0, ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      ¬ HasUnitTriangle X →
      ∀ (L tol : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane))
        (lab : Set ℂ → Plane × Plane), tol ≤ c →
        NoIntermediatePorts X L (lam * diam X) G → LabelledBy X tol G mk lab →
      ∀ F ∈ G.good, ∀ ab ∈ longSides X L F, ((ab.2 - ab.1) * conj (labDir lab F)).re ≤ 1 / 2 - κ' := by
  set γ := min 1 (lam ^ 2 / 8) with hγdef
  have hγ0 : 0 < γ := lt_min one_pos (by positivity)
  have hγ1 : γ ≤ 1 := min_le_left _ _
  have hγ2 : γ ≤ lam ^ 2 / 8 := min_le_right _ _
  set κ := min (1 / 4 : ℝ) (lam / 8) with hκdef
  have hκ0 : 0 < κ := lt_min (by norm_num) (by positivity)
  have hκ1 : κ ≤ 1 / 4 := min_le_left _ _
  have hκ2 : κ ≤ lam / 8 := min_le_right _ _
  have hthr : (0 : ℝ) < (γ / 4) ^ 2 / 300 := by positivity
  have ht : Tendsto (fun n => minDiam n ^ (-(2 / 9 : ℝ))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num)).comp tendsto_minDiam
  have hasq : aStar ^ 2 = 3 / 4 := by
    unfold aStar; rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have ha0 := aStar_pos
  have hahalf : 1 / 2 ≤ aStar := by nlinarith
  refine ⟨κ, hκ0, γ / 4, by positivity, ?_⟩
  filter_upwards [eventually_roundData_rate, ht.eventually (ge_mem_nhds hthr),
    tendsto_minDiam.eventually_ge_atTop (max 1 (4 / γ))] with
    n hround hsmall hD hfm X hX htri L tol G mk lab htol hNIP hlab F hFg ab hab
  rw [← hX.diam_eq] at hsmall hD
  set D := diam X with hDdef
  have hD1 : 1 ≤ D := le_trans (le_max_left _ _) hD
  have hDγ : 4 / γ ≤ D := le_trans (le_max_right _ _) hD
  have hD0 : 0 < D := by linarith
  have hsep := hX.1.2
  by_contra hlt
  push_neg at hlt
  have hFe : F ∈ exceptionalFaces X := (mem_exceptionalFinset hsep).1 (G.good_subset hFg)
  obtain ⟨e, he, hmap, hp, hnot⟩ := longSide_edge hFe hab
  have hlen : lam * D ≤ trackLength X (allTrackOf X e) := (hNIP F hFg e he hp).resolve_left hnot
  have habo : ab ∈ orientedSides X F := (Finset.mem_filter.1 hab).1
  obtain ⟨A, B⟩ := ab
  have hAB := Finset.mem_product.1 (Finset.mem_filter.1 habo).1
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hAB.1
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hAB.2
  have hdab : dist a b = 1 := dist_eq_one_of_mem_orientedSides habo
  have hee : e = s(b, a) := by
    have : Sym2.map toC e = Sym2.map toC s(b, a) := by rw [hmap, Sym2.map_mk]; exact Sym2.eq_swap
    exact Sym2.map.injective toC.injective this
  set p : Plane × Plane := (b, a) with hpdef
  have hpX : p ∈ X ×ˢ X := Finset.mem_product.2 ⟨hb, ha⟩
  have hinit : Initial X p := initial_of_mem_orientedSides hsep htri hFe habo
  obtain ⟨m, -, hmv, hstop⟩ := exists_hopLen hpX
  have hu' : s(p.1, p.2) ∈ unitEdges X := by
    show s(b, a) ∈ unitEdges X; rw [← hee]; exact he
  have hmL := trackLength_le_hopLen hsep htri hu' hinit hmv hstop
  have hm : lam * D ≤ m := by
    have : allTrackOf X s(p.1, p.2) = allTrackOf X e := by
      show allTrackOf X s(b, a) = _; rw [hee]
    rw [this] at hmL
    exact hlen.trans (by exact_mod_cast hmL)
  obtain ⟨hβ, hα⟩ := hop_displacement hsep htri p hmv
  have hPm : ((stepL X)^[m] p).1 ∈ X := (Finset.mem_product.1 (iterate_stepL_mem hpX m)).1
  obtain ⟨O, η, hR⟩ := hround X hX
  have hball := hR.ball _ hPm
  have hlabF := hlab.2 F hFg
  have hp1 := mem_ccwHullSides.1 (Finset.mem_filter.1 hlabF.1).1
  have hτ : ‖sideDir (lab F)‖ = 1 := norm_sideDir hp1.2.2.1
  have hside := side_normal_near hR hp1
  have hnear := hlabF.2.2 (toC a, toC b) habo
  simp only at hnear
  rw [← map_sub, LinearIsometryEquiv.norm_map] at hnear
  rw [← hDdef] at hball hside hnear
  have hball' : ‖((stepL X)^[m] p).1 - O‖ ≤ D / 2 + η * D := by rw [← dist_eq_norm]; exact hball
  have hu1 : ‖p.2 - p.1‖ = 1 := by
    show ‖a - b‖ = 1; rw [← dist_eq_norm]; exact hdab
  have hc : inner ℝ (p.2 - p.1) (sideDir (lab F)) ≤ -(1 / 2 - κ) := by
    have hre : ((toC b - toC a) * conj (labDir lab F)).re = inner ℝ (b - a) (sideDir (lab F)) := by
      rw [labDir, ← map_sub, Complex.mul_re, Complex.conj_re, Complex.conj_im, toC_re', toC_re',
        toC_im', toC_im', inner_coord]
      ring
    simp only at hlt
    rw [hre] at hlt
    show inner ℝ (a - b) (sideDir (lab F)) ≤ _
    rw [← neg_sub, inner_neg_left]
    linarith
  set δ := 100 * D ^ (-(2 / 9 : ℝ)) with hδdef
  have htolD : 0 ≤ tol * D := le_trans (norm_nonneg _) hnear
  set E := η * D + tol * D + 1 + D * √(3 * δ) with hEdef
  have hE0 : 0 ≤ E := by
    have := hR.η_nonneg
    have : 0 ≤ D * √(3 * δ) := mul_nonneg hD0.le (Real.sqrt_nonneg _)
    positivity
  have hZ : ‖(D / 2) • (-rot (sideDir (lab F))) + (((stepL X)^[m] p).1 - p.1)‖ ≤ D / 2 + E := by
    have e1 : (D / 2) • (-rot (sideDir (lab F))) + (((stepL X)^[m] p).1 - p.1) =
        (((stepL X)^[m] p).1 - O) - (b - a) - (a - (lab F).1) -
          ((lab F).1 - O - (D / 2) • (-rot (sideDir (lab F)))) := by
      show _ = _; simp only [hpdef]; abel
    rw [e1]
    have hba : ‖b - a‖ = 1 := by rw [← dist_eq_norm, dist_comm]; exact hdab
    have n1 := norm_sub_le ((((stepL X)^[m] p).1 - O) - (b - a) - (a - (lab F).1))
      ((lab F).1 - O - (D / 2) • (-rot (sideDir (lab F))))
    have n2 := norm_sub_le ((((stepL X)^[m] p).1 - O) - (b - a)) (a - (lab F).1)
    have n3 := norm_sub_le (((stepL X)^[m] p).1 - O) (b - a)
    linarith
  have core := margin_core hu1 hτ hκ0.le (Nat.cast_nonneg m) hD0 hβ hα hc hZ
  -- the error term is at most `γ D`
  have hsm : D ^ (-(2 / 9 : ℝ)) ≤ (γ / 4) ^ 2 / 300 := hsmall
  have hγ4 : γ / 4 ≤ 1 / 4 := by linarith only [hγ1]
  have hγ40 : 0 ≤ γ / 4 := by positivity
  have hγsq : (γ / 4) ^ 2 ≤ γ / 4 := by nlinarith only [hγ40, hγ4]
  have hδ1 : δ ≤ γ / 4 := by rw [hδdef]; linarith only [hsm, hγsq, sq_nonneg (γ / 4)]
  have hsq : √(3 * δ) ≤ γ / 4 := by
    rw [show γ / 4 = √((γ / 4) ^ 2) by rw [Real.sqrt_sq hγ40]]
    exact Real.sqrt_le_sqrt (by rw [hδdef]; linarith only [hsm])
  have hEγ : E ≤ γ * D := by
    have h1 : η * D ≤ γ / 4 * D := mul_le_mul_of_nonneg_right (hR.η_le.trans hδ1) hD0.le
    have h2 : tol * D ≤ γ / 4 * D := mul_le_mul_of_nonneg_right htol hD0.le
    have h3 : 1 ≤ γ / 4 * D := by
      rw [div_le_iff₀ hγ0] at hDγ; linarith only [hDγ]
    have h4 : D * √(3 * δ) ≤ D * (γ / 4) := mul_le_mul_of_nonneg_left hsq hD0.le
    rw [hEdef]; linarith only [h1, h2, h3, h4]
  set β := inner ℝ (((stepL X)^[m] p).1 - p.1) (rot (p.2 - p.1)) with hβdef
  have hβ1 : aStar * (lam * D) ≤ β := le_trans (mul_le_mul_of_nonneg_left hm ha0.le) hβ
  have hβ2 : 4 * κ * D ≤ β := by
    have h4 : 4 * κ ≤ aStar * lam := by nlinarith only [hκ2, hahalf, hlam]
    have := mul_le_mul_of_nonneg_right h4 hD0.le
    linarith only [this, hβ1]
  have hb0 : 0 ≤ aStar * (lam * D) := by positivity
  have hβ0 : 0 ≤ β := hb0.trans hβ1
  have hlow : (aStar * (lam * D)) ^ 2 / 2 ≤ β ^ 2 - 2 * κ * D * β := by
    have h1 : (aStar * (lam * D)) ^ 2 ≤ β ^ 2 := pow_le_pow_left₀ hb0 hβ1 2
    have h2 := mul_nonneg hβ0 (sub_nonneg.2 hβ2)
    nlinarith only [h1, h2]
  have hup : D * E + E ^ 2 ≤ lam ^ 2 * D ^ 2 / 4 := by
    have h1 := mul_le_mul_of_nonneg_left hEγ hD0.le
    have h2 : E ^ 2 ≤ (γ * D) ^ 2 := pow_le_pow_left₀ hE0 hEγ 2
    have h3 : γ ^ 2 * D ^ 2 ≤ γ * D ^ 2 := by
      have : γ ^ 2 ≤ γ := by nlinarith only [hγ0, hγ1]
      exact mul_le_mul_of_nonneg_right this (sq_nonneg D)
    have h4 : 2 * γ * D ^ 2 ≤ lam ^ 2 / 4 * D ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith only [hγ2]) (sq_nonneg D)
    nlinarith only [h1, h2, h3, h4]
  rw [mul_pow, hasq] at hlow
  have hpos : 0 < lam ^ 2 * D ^ 2 := by positivity
  nlinarith only [hlow, core, hup, hpos]

/-- The macroscopic-port margin, with an (unused) bound on the cutoff `L` (the form used by the
§13 estimates); see `long_side_margin'`. -/
theorem long_side_margin {lam : ℝ} (hlam : 0 < lam) :
    ∃ κ' > 0, ∃ c > 0, ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      ¬ HasUnitTriangle X →
      ∀ (L tol : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane))
        (lab : Set ℂ → Plane × Plane), L ≤ c * diam X → tol ≤ c →
        NoIntermediatePorts X L (lam * diam X) G → LabelledBy X tol G mk lab →
      ∀ F ∈ G.good, ∀ ab ∈ longSides X L F, ((ab.2 - ab.1) * conj (labDir lab F)).re ≤ 1 / 2 - κ' := by
  obtain ⟨κ', hκ', c, hc, h⟩ := long_side_margin' hlam
  refine ⟨κ', hκ', c, hc, ?_⟩
  filter_upwards [h] with n hn hfm X hX htri L tol G mk lab _ htol hNIP hlab
  exact hn hfm X hX htri L tol G mk lab htol hNIP hlab

lemma exists_unit_sixth_root {c : ℂ} (hc : ‖c‖ = 1) : ∃ w : ℂ, ‖w‖ = 1 ∧ w ^ 6 = c := by
  refine ⟨c ^ ((6 : ℂ)⁻¹), ?_, ?_⟩
  · have h : (c ^ ((6 : ℂ)⁻¹)) ^ 6 = c := by exact_mod_cast Complex.cpow_nat_inv_pow c (n := 6) (by norm_num)
    have h2 : ‖c ^ ((6 : ℂ)⁻¹)‖ ^ 6 = 1 := by rw [← norm_pow, h, hc]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h2
  · exact_mod_cast Complex.cpow_nat_inv_pow c (n := 6) (by norm_num)

lemma side_pow_six {X : Finset Plane} {e : Sym2 Plane} (he : e ∈ unitEdges X) {ab : ℂ × ℂ}
    (h : Sym2.map toC e = s(ab.1, ab.2)) :
    ‖ab.2 - ab.1‖ = 1 ∧ (ab.2 - ab.1) ^ 6 = dir6 (dv e) := by
  have hn := norm_dv_of_mem_unitEdges he
  induction e using Sym2.ind with
  | _ x y =>
  rw [Sym2.map_mk] at h
  have hxy : ‖x - y‖ = 1 := by
    rcases dv_mk x y with h' | h' <;> rw [h'] at hn
    · exact hn
    · rwa [norm_sub_rev]
  have hd : dir6 (dv s(x, y)) = (toC x - toC y) ^ 6 := by
    rw [dir6_dv_mk, dir6_of_norm_eq_one hxy, map_sub]
  have hn' : ‖toC x - toC y‖ = 1 := by rw [← map_sub, norm_toC, hxy]
  rw [hd]
  rcases Sym2.eq_iff.1 h with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [← e1, ← e2, norm_sub_rev]; exact ⟨hn', by ring⟩
  · rw [← e1, ← e2]; exact ⟨hn', rfl⟩


/-- **Clustering of the long side vectors** (Lemma 3.3 at the macroscopic scale `λ D`): there is a
bound `N_c` (depending on `λ` only) such that for every tolerance `ε_c`, outside a bounded number of
exceptional faces, every side vector on a track with at least `λ D` rhombi lies within `ε_c` of one
of at most `N_c` vectors. -/
theorem long_sides_clustered {lam : ℝ} (hlam : 0 < lam) :
    ∃ Nc : ℕ, ∀ εc > 0, ∃ M : ℝ, ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      ¬ HasUnitTriangle X → ∃ U : Finset ℂ, U.card ≤ Nc ∧ ∃ Bad : Finset (Set ℂ),
        (Bad.card : ℝ) ≤ M ∧ ∀ F ∈ exceptionalFaces X, F ∉ Bad → ∀ ab ∈ orientedSides X F,
          (∃ e ∈ unitEdges X, Sym2.map toC e = s(ab.1, ab.2) ∧
            lam * diam X ≤ trackLength X (allTrackOf X e)) →
          ∃ u ∈ U, ‖(ab.2 - ab.1) - u‖ ≤ εc := by
  obtain ⟨C1, hC1⟩ := rhombus_defect_sum
  obtain ⟨C2, hC2⟩ := tracks_card_le
  refine ⟨⌊2 * C2 / lam⌋₊ * 6, fun εc hεc => ?_⟩
  set ε' := min (εc / 4) (1 / 4) with hε'
  have hε'0 : 0 < ε' := lt_min (by linarith) (by norm_num)
  refine ⟨2 * (4 * max C1 0 / (ε' * lam)), ?_⟩
  filter_upwards [hC1, hC2, card_trackEnds, tendsto_minDiam.eventually (eventually_ge_atTop 1)]
    with n h1 h2 hends hD hfm X hX htri
  have hD1 : 1 ≤ diam X := by rw [hX.diam_eq]; exact hD
  have hD0 : 0 < diam X := by linarith
  have hsep := hX.1.2
  have hK : ∑ Q ∈ rhombi X, rhombusDefect Q ≤ max C1 0 * diam X :=
    (h1 hfm X hX htri).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hD0.le)
  have hL : 0 < lam * diam X := mul_pos hlam hD0
  obtain ⟨Disc, hDsub, Cs, hCs1, hDcard, hCcard, hcov⟩ :=
    track_clustering hsep htri hε'0 hL hK
  choose! rt hrt1 hrt6 using fun c (hc : c ∈ Cs) => exists_unit_sixth_root (hCs1 c hc)
  refine ⟨(Cs ×ˢ sixRoots).image (fun p => p.2 * rt p.1), ?_, ?_⟩
  · refine Finset.card_image_le.trans ?_
    rw [Finset.card_product]
    have hsix : sixRoots.card ≤ 6 := Finset.card_le_six
    refine Nat.mul_le_mul ?_ hsix
    refine Nat.le_floor ?_
    rw [le_div_iff₀ hlam]
    have := h2 hfm X hX htri
    have h3 : (Cs.card : ℝ) * lam * diam X ≤ 2 * C2 * diam X := by nlinarith
    nlinarith
  refine ⟨(Disc.biUnion (trackEnds X)).image (fun p => nodeFace p.1), ?_, ?_⟩
  · have hc1 : ((Disc.biUnion (trackEnds X)).image (fun p => nodeFace p.1)).card ≤ 2 * Disc.card := by
      refine Finset.card_image_le.trans (Finset.card_biUnion_le.trans ?_)
      rw [Finset.sum_congr rfl (fun T hT => hends hfm X hX htri T
        (tracks_subset_allTracks X (hDsub hT))), Finset.sum_const, smul_eq_mul, mul_comm]
    have hc2 : (Disc.card : ℝ) ≤ 4 * max C1 0 / (ε' * lam) := by
      rw [le_div_iff₀ (mul_pos hε'0 hlam)]
      have : (Disc.card : ℝ) * (ε' * lam) * diam X ≤ 4 * max C1 0 * diam X := by
        nlinarith
      exact le_of_mul_le_mul_right this hD0
    calc _ ≤ ((2 * Disc.card : ℕ) : ℝ) := by exact_mod_cast hc1
      _ ≤ _ := by push_cast; linarith
  · intro F hF hFB ab hab ⟨e, he, hmap, hlen⟩
    have heR : e ∈ rhombusEdges X := by
      by_contra hne
      rw [allTrackOf_of_not_mem he hne, trackLength_singleton hsep htri he hne] at hlen
      push_cast at hlen; linarith
    have hT : allTrackOf X e ∈ tracks X := by
      rw [allTrackOf_of_mem_rhombusEdges heR]; exact Finset.mem_image_of_mem _ heR
    have hnD : allTrackOf X e ∉ Disc := by
      intro hD'
      apply hFB
      have hb : s(ab.1, ab.2) ∈ bdryEdges (cUnitEdges X) F := (Finset.mem_filter.1 hab).2.1
      have hp : IsPort X (Sum.inl F) e := ⟨hF, hmap ▸ hb⟩
      have hFf : F ∈ exceptionalFinset X := (mem_exceptionalFinset hsep).2 hF
      refine Finset.mem_image.2 ⟨(Sum.inl F, e), Finset.mem_biUnion.2 ⟨_, hD', ?_⟩, rfl⟩
      exact Finset.mem_filter.2 ⟨Finset.mem_product.2
        ⟨Finset.mem_union_left _ (Finset.mem_map_of_mem _ hFf), mem_allTrackOf_self he⟩, hp⟩
    obtain ⟨c, hc, hcd⟩ := hcov _ hT hnD hlen
    have heT : e ∈ allTrackOf X e := mem_allTrackOf_self he
    rw [tdir_eq hT heT] at hcd
    obtain ⟨hv1, hv6⟩ := side_pow_six he hmap
    have hr : 2 * ε' ≤ 1 / 2 := by have := min_le_right (εc / 4) (1 / 4); linarith
    obtain ⟨ζ, hζ, hclose⟩ := sixth_root_near hv1 (hrt1 c hc) hr
      (by rw [hv6, hrt6 c hc]; exact hcd)
    refine ⟨ζ * rt c, Finset.mem_image.2 ⟨(c, ζ), Finset.mem_product.2 ⟨hc, hζ⟩, rfl⟩, ?_⟩
    have := min_le_left (εc / 4) (1 / 4)
    linarith

end Erdos99

end

end HHAdjacencyGeometry

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `HHAdjacency`
-/

section HHAdjacency

/-!
# `H–H` adjacency is pinned (Verification Guide §13.1)

This file proves the local exclusion estimate `hh_edges_few`: for every `η > 0`,
`LocalExclusion η qHH` (few edges of the track graph join two degree-two faces).  The proof is
split over `HHAdjacencyAlgebra` (combinatorics, algebra, counting), `HopMargin` (hops
along a track) and `HHAdjacencyGeometry` (the geometric inputs); this file contains the
assembly `hhFaces_few` and `hh_edges_few`.

## Structure of the argument

* **Combinatorics** (`qHH_le_four_mul`): `qHH ≤ 4 · #hhFaces`, where `hhFaces` are the good
  degree-two faces having a short track to another degree-two face (`hhPorts`).
* **Per-port equations** (`hh_port_equations`): at an `H–H` port `(F, e)` with mate `(F', e')`,
  with labels `τ, τ'`, multiplicities `k, l` and long-side sums `Z, W`, there are unit vectors
  `s, u, w` with `‖k τ + s + u + Z‖ ≤ tol` and `‖l τ' - s + w + W‖ ≤ tol` (closure of the two
  faces, and opposite orientation of the two ends of a track).
* **Label locality** (`hh_label_locality`): `τ' ≈ τ`.
* **Approximate (H1)** (`approx_H1`): these equations make `hhPoly k l Z W` small at `τ`.
* **Margin** (`long_side_margin`) and the **degenerate exclusion** (`degenerate_excluded`): the
  identically vanishing case of (H1) cannot occur.
* **Clustering** (`long_sides_clustered`): the long side vectors lie near boundedly many centres.
* **Counting** (`hh_pinned_count`): pinned labels are few.
-/

open scoped BigOperators Real
open Filter Polynomial ComplexConjugate

@[expose] public noncomputable section

open Classical

namespace Erdos99

open LocalCharge QuadraticResponse DirectionPinning EstablishedExternalResults

/-! ## Sums of clustered vectors -/

/-- The sums of at most six vectors of `U` (with multiplicity). -/
def sumCentres (U : Finset ℂ) : Finset ℂ :=
  (Finset.univ : Finset (U → Fin 7)).image (fun m => ∑ u : U, ((m u : ℕ) : ℂ) * (u : ℂ))

lemma card_sumCentres_le (U : Finset ℂ) : (sumCentres U).card ≤ 7 ^ U.card := by
  refine Finset.card_image_le.trans ?_
  simp

/-- A sum of at most six vectors, each within `ε` of `U`, lies within `6 ε` of `sumCentres U`. -/
lemma sum_near_sumCentres {ι : Type*} (S : Finset ι) (v : ι → ℂ) (U : Finset ℂ) {ε : ℝ}
    (hε : 0 ≤ ε) (hS : S.card ≤ 6) (h : ∀ i ∈ S, ∃ u ∈ U, ‖v i - u‖ ≤ ε) :
    ∃ z ∈ sumCentres U, ‖∑ i ∈ S, v i - z‖ ≤ 6 * ε := by
  choose! φ hφU hφ using h
  refine ⟨∑ i ∈ S, φ i, ?_, ?_⟩
  · refine Finset.mem_image.2 ⟨fun u => ⟨(S.filter (fun i => φ i = u)).card, ?_⟩, Finset.mem_univ _,
      ?_⟩
    · have := Finset.card_filter_le S (fun i => φ i = u); omega
    · simp only
      rw [Finset.sum_coe_sort U (fun u => (((S.filter (fun i => φ i = u)).card : ℕ) : ℂ) * u)]
      rw [← Finset.sum_fiberwise_of_maps_to (g := φ) (t := U) (fun i hi => hφU i hi)]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.1 hi).2), Finset.sum_const,
        nsmul_eq_mul]
  · rw [← Finset.sum_sub_distrib]
    calc ‖∑ i ∈ S, (v i - φ i)‖ ≤ ∑ i ∈ S, ‖v i - φ i‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ S, ε := Finset.sum_le_sum hφ
      _ = S.card * ε := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 6 * ε := mul_le_mul_of_nonneg_right (by exact_mod_cast hS) hε

lemma eventually_diam_ge (C : ℝ) : ∀ᶠ n in atTop, ∀ X, IsOptimal n X → C ≤ diam X := by
  filter_upwards [tendsto_minDiam.eventually (eventually_ge_atTop C)] with n hn X hX
  rw [hX.diam_eq]; exact hn

/-- At most two half-edges of the track graph sit at a degree-two face. -/
lemma card_halfEdges_H_le {X : Finset Plane}
    (hends : ∀ T ∈ allTracks X, (trackEnds X T).card = 2) (L : ℝ) (G : GoodFaces X)
    (mk : Set ℂ → Finset (Sym2 Plane)) (B : Finset (Set ℂ)) :
    ((unmarkedPorts X L G mk).filter
      (fun q => q.1 ∈ B ∧ q.1 ∈ (trackGraph X L G mk).Hs G.good)).card ≤ 2 * B.card := by
  have hM := trackMate_isMatching hends L G mk
  refine Finset.card_le_mul_card_image_of_maps_to (f := (Prod.fst : Set ℂ × Sym2 Plane → Set ℂ))
    (fun q hq => (Finset.mem_filter.1 hq).2.1) 2 fun b _ => ?_
  by_cases hb : b ∈ (trackGraph X L G mk).Hs G.good
  · have hdeg : (trackGraph X L G mk).deg b = 2 := (Finset.mem_filter.1 hb).2
    rw [trackGraph, StubGraph.deg_ofHalfEdges hM] at hdeg
    rw [← hdeg]
    refine Finset.card_le_card fun q hq => ?_
    obtain ⟨hq1, hq2⟩ := Finset.mem_filter.1 hq
    exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hq1).1, hq2⟩
  · refine le_trans (le_of_eq ?_) (Nat.zero_le 2)
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro q hq hqb
    exact hb (hqb ▸ (Finset.mem_filter.1 hq).2.2)

/-- The `H–H` faces that lie in `Bad` or have a mate in `Bad` number at most `3 · #Bad`. -/
lemma card_hhExc_le {X : Finset Plane}
    (hends : ∀ T ∈ allTracks X, (trackEnds X T).card = 2) (L : ℝ) (G : GoodFaces X)
    (mk : Set ℂ → Finset (Sym2 Plane)) (Bad : Finset (Set ℂ)) :
    ((hhFaces X L G mk).filter (fun F => F ∈ Bad ∨
      ∃ q ∈ hhPorts X L G mk, q.1 = F ∧ (trackMate X q).1 ∈ Bad)).card ≤ 3 * Bad.card := by
  have hM := trackMate_isMatching hends L G mk
  set Q := (hhPorts X L G mk).filter (fun q => (trackMate X q).1 ∈ Bad)
  have hsub : (hhFaces X L G mk).filter (fun F => F ∈ Bad ∨
      ∃ q ∈ hhPorts X L G mk, q.1 = F ∧ (trackMate X q).1 ∈ Bad) ⊆ Bad ∪ Q.image Prod.fst := by
    intro F hF
    rcases (Finset.mem_filter.1 hF).2 with h | ⟨q, hq, rfl, hqB⟩
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hq, hqB⟩))
  have hQ : Q.card ≤ 2 * Bad.card := by
    refine le_trans ?_ (card_halfEdges_H_le hends L G mk Bad)
    refine Finset.card_le_card_of_injOn (trackMate X) ?_ ?_
    · intro q hq
      obtain ⟨hq, hqB⟩ := Finset.mem_filter.1 hq
      obtain ⟨hqP, hmat, -, hH⟩ := Finset.mem_filter.1 hq
      exact Finset.mem_filter.2 ⟨(hM q hqP hmat).1, hqB, hH⟩
    · intro q hq q' hq' h
      obtain ⟨hqP, hmat, -⟩ := Finset.mem_filter.1 (Finset.mem_filter.1 hq).1
      obtain ⟨hqP', hmat', -⟩ := Finset.mem_filter.1 (Finset.mem_filter.1 hq').1
      rw [← (hM q hqP hmat).2.2.1, ← (hM q' hqP' hmat').2.2.1, h]
  calc _ ≤ (Bad ∪ Q.image Prod.fst).card := Finset.card_le_card hsub
    _ ≤ Bad.card + (Q.image Prod.fst).card := Finset.card_union_le _ _
    _ ≤ Bad.card + Q.card := by have := Finset.card_image_le (s := Q) (f := Prod.fst); omega
    _ ≤ 3 * Bad.card := by omega

lemma norm_longSum_le {X : Finset Plane} {L : ℝ} {F : Set ℂ}
    (hcard : (orientedSides X F).card ≤ 6) (hunit : ∀ ab ∈ orientedSides X F, ‖ab.2 - ab.1‖ = 1) :
    ‖longSum X L F‖ ≤ 6 := by
  have hsub : longSides X L F ⊆ orientedSides X F := Finset.filter_subset _ _
  calc ‖longSum X L F‖ ≤ ∑ ab ∈ longSides X L F, ‖ab.2 - ab.1‖ := norm_sum_le _ _
    _ = ∑ _ab ∈ longSides X L F, (1 : ℝ) := Finset.sum_congr rfl fun ab hab => hunit ab (hsub hab)
    _ = (longSides X L F).card := by simp
    _ ≤ 6 := by exact_mod_cast (Finset.card_le_card hsub).trans hcard

/-! ## Assembly -/

/-- **Few `H–H` faces.**  For every `ε, λ > 0` there are a saturation tolerance and a cutoff
fraction `a₀` such that for every cutoff fraction `a ≤ a₀`, eventually every saturated marking has
at most `ε D` faces carrying an `H–H` port. -/
theorem hhFaces_few {ε lam : ℝ} (hε : 0 < ε) (hlam : 0 < lam) :
    ∃ tol > 0, ∃ a₀ > 0, ∀ a, 0 < a → a ≤ a₀ →
      ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
        ∀ (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane)), IsMarking X (a * diam X) G mk →
          IsSaturated X (a * diam X) (lam * diam X) tol G mk →
          ((hhFaces X (a * diam X) G mk).card : ℝ) ≤ ε * diam X := by
  obtain ⟨Nc, hclus⟩ := long_sides_clustered hlam
  obtain ⟨κ', hκ', c3, hc3, hmarg⟩ := long_side_margin hlam
  obtain ⟨κ0, hκ0, ρ4, hρ4, hdeg⟩ := degenerate_excluded hκ'
  set κ := min κ0 (1 / 2) with hκdef
  have hκ : 0 < κ := lt_min hκ0 (by norm_num)
  have hκ1 : κ ≤ 1 / 2 := min_le_right _ _
  have hκ2 : κ ≤ κ0 := min_le_left _ _
  obtain ⟨r, hr, μ, hμ, hpin⟩ := hh_pinned_count (4 * (7 ^ Nc) ^ 2) (half_pos hε) hκ
  obtain ⟨ε₁, hε₁, hH1⟩ := approx_H1 hr
  obtain ⟨M, hclusM⟩ := hclus (μ / 12) (by positivity)
  obtain ⟨c2, hc2, hloc⟩ := hh_label_locality (lt_min hε₁ hρ4)
  refine ⟨min ε₁ (min c2 c3), lt_min hε₁ (lt_min hc2 hc3), min c2 c3, lt_min hc2 hc3,
    fun a ha hab => ?_⟩
  filter_upwards [hpin, hclusM, hloc, hmarg, hh_port_equations, face_side_facts,
    longSides_H_pentagon, card_trackEnds, eventually_diam_ge (6 * |M| / ε),
    eventually_diam_ge 1] with n hpin hclusM hloc hmarg hport hfacts hpent hends hDbig hD1
  intro hfm X hX htri G mk hmk hsat
  set D := diam X with hDdef
  set L := a * D with hLdef
  have hD : 0 < D := lt_of_lt_of_le one_pos (hD1 X hX)
  obtain ⟨hnoint, lab, hlab⟩ := hsat
  set tol := min ε₁ (min c2 c3) with htoldef
  have htolε : tol ≤ ε₁ := min_le_left _ _
  have htol2 : tol ≤ c2 := (min_le_right _ _).trans (min_le_left _ _)
  have htol3 : tol ≤ c3 := (min_le_right _ _).trans (min_le_right _ _)
  have hL2 : L ≤ c2 * D :=
    mul_le_mul_of_nonneg_right (hab.trans (min_le_left _ _)) hD.le
  have hL3 : L ≤ c3 * D :=
    mul_le_mul_of_nonneg_right (hab.trans (min_le_right _ _)) hD.le
  obtain ⟨U, hU, Bad, hBad, hcl⟩ := hclusM hfm X hX htri
  have hends' := hends hfm X hX htri
  set Exc := (hhFaces X L G mk).filter (fun F => F ∈ Bad ∨
    ∃ q ∈ hhPorts X L G mk, q.1 = F ∧ (trackMate X q).1 ∈ Bad) with hExcdef
  have hExc := card_hhExc_le hends' L G mk Bad
  set Rest := hhFaces X L G mk \ Exc with hRestdef
  have hRestgood : Rest ⊆ G.good := fun F hF => by
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 (Finset.mem_sdiff.1 hF).1
    exact (hhPorts_fst_good hq).1
  set A := Rest.image lab with hAdef
  have hAcard : A.card = Rest.card := Finset.card_image_of_injOn (hlab.1.mono hRestgood)
  have hA : A ⊆ ccwHullSides X := fun p hp => by
    obtain ⟨F, hF, rfl⟩ := Finset.mem_image.1 hp
    exact (Finset.mem_filter.1 (hlab.2 F (hRestgood hF)).1).1
  set C : Finset (ℝ × ℝ × ℂ × ℂ) :=
    ({1, 2} : Finset ℝ) ×ˢ ({1, 2} : Finset ℝ) ×ˢ sumCentres U ×ˢ sumCentres U with hCdef
  have hC : C.card ≤ 4 * (7 ^ Nc) ^ 2 := by
    have h1 : (sumCentres U).card ≤ 7 ^ Nc :=
      (card_sumCentres_le U).trans (Nat.pow_le_pow_right (by norm_num) hU)
    have h2 : (({1, 2} : Finset ℝ)).card ≤ 2 := Finset.card_le_two
    simp only [hCdef, Finset.card_product]
    calc _ ≤ 2 * (2 * ((7 ^ Nc) * (7 ^ Nc))) := by
          gcongr
      _ = 4 * (7 ^ Nc) ^ 2 := by ring
  -- the data at a face of `Rest`
  have hdata : ∀ p ∈ A, ∃ d : ℝ × ℝ × ℂ × ℂ, HHAdm κ d ∧ (∃ c ∈ C, ‖d - c‖ < μ) ∧
      ‖(hhPoly d.1 d.2.1 d.2.2.1 d.2.2.2).eval (toC (sideDir p))‖ < r := by
    intro p hp
    obtain ⟨F, hF, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨hFh, hFnot⟩ := Finset.mem_sdiff.1 hF
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hFh
    set F' := (trackMate X q).1 with hF'def
    obtain ⟨hgF, hgF'⟩ := hhPorts_fst_good hq
    have hHF : q.1 ∈ (trackGraph X L G mk).Hs G.good := (Finset.mem_filter.1 hq).2.2.1
    have hHF' : F' ∈ (trackGraph X L G mk).Hs G.good := (Finset.mem_filter.1 hq).2.2.2
    have hnB : q.1 ∉ Bad := fun h => hFnot (Finset.mem_filter.2 ⟨hFh, Or.inl h⟩)
    have hnB' : F' ∉ Bad := fun h => hFnot (Finset.mem_filter.2 ⟨hFh, Or.inr ⟨q, hq, rfl, h⟩⟩)
    obtain ⟨s, u, w, hs, hu, hw, e1, e2⟩ := hport hfm X hX htri L tol G mk lab hmk hlab q hq
    have hlocq := hloc hfm X hX htri L tol G mk lab hL2 htol2 hlab q hq
    obtain ⟨hcF, huF⟩ := hfacts hfm X hX G q.1 hgF
    obtain ⟨hcF', huF'⟩ := hfacts hfm X hX G F' hgF'
    have hZ6 := norm_longSum_le (L := L) hcF huF
    have hW6 := norm_longSum_le (L := L) hcF' huF'
    have hτ := norm_labDir hlab hgF
    have hτ' := norm_labDir hlab hgF'
    have hexF : ∀ F ∈ G.good, F ∈ exceptionalFaces X := fun F hF =>
      (mem_exceptionalFinset hX.1.2).1 (G.good_subset hF)
    -- every long side is clustered
    have hlongcl : ∀ F ∈ G.good, F ∉ Bad → ∀ ab ∈ longSides X L F,
        ∃ u ∈ U, ‖(ab.2 - ab.1) - u‖ ≤ μ / 12 := by
      intro F hF hFB ab hab
      obtain ⟨e, he, hmap, hport', hlong⟩ := longSide_edge (hexF F hF) hab
      refine hcl F (hexF F hF) hFB ab (Finset.mem_filter.1 hab).1 ⟨e, he, hmap, ?_⟩
      rcases hnoint F hF e he hport' with h | h
      · exact absurd h hlong
      · exact h
    have hcard6 : ∀ F ∈ G.good, (longSides X L F).card ≤ 6 := fun F hF =>
      (Finset.card_le_card (Finset.filter_subset _ _)).trans (hfacts hfm X hX G F hF).1
    obtain ⟨z, hz, hzZ⟩ := sum_near_sumCentres (longSides X L q.1) (fun ab => ab.2 - ab.1) U
      (by positivity) (hcard6 _ hgF) (hlongcl _ hgF hnB)
    obtain ⟨z', hz', hzW⟩ := sum_near_sumCentres (longSides X L F') (fun ab => ab.2 - ab.1) U
      (by positivity) (hcard6 _ hgF') (hlongcl _ hgF' hnB')
    refine ⟨(G.kMult q.1, G.kMult F', longSum X L q.1, longSum X L F'), ⟨G.kMult_cases _,
      G.kMult_cases _, hZ6, hW6, ?_⟩, ⟨(G.kMult q.1, G.kMult F', z, z'), ?_, ?_⟩, ?_⟩
    · -- the degenerate case is excluded
      rintro ⟨hk1, hl1, hZW, hZ1⟩
      simp only at hk1 hl1 hZW hZ1
      rcases hpent hfm X hX htri L G mk hmk q.1 hHF hk1 with h0 | ⟨p₁, hp₁, p₂, hp₂, hp12, hP⟩
      · rw [longSum, h0, Finset.sum_empty, norm_zero, zero_sub, abs_neg, abs_one] at hZ1
        linarith
      rcases hpent hfm X hX htri L G mk hmk F' hHF' hl1 with h0' | ⟨q₁, hq₁, q₂, hq₂, hq12, hQ⟩
      · have hW0 : longSum X L F' = 0 := by rw [longSum, h0', Finset.sum_empty]
        rw [hW0, add_zero] at hZW
        have := abs_lt.1 hZ1
        linarith
      have hZe : longSum X L q.1 = (p₁.2 - p₁.1) + (p₂.2 - p₂.1) := by
        rw [longSum, hP, Finset.sum_pair hp12]
      have hWe : longSum X L F' = (q₁.2 - q₁.1) + (q₂.2 - q₂.1) := by
        rw [longSum, hQ, Finset.sum_pair hq12]
      have hsubF := (Finset.filter_subset _ _ : longSides X L q.1 ⊆ orientedSides X q.1)
      have hsubF' := (Finset.filter_subset _ _ : longSides X L F' ⊆ orientedSides X F')
      have m := hmarg hfm X hX htri L tol G mk lab hL3 htol3 hnoint hlab
      refine hdeg _ _ _ _ _ _ (huF _ (hsubF hp₁)) (huF _ (hsubF hp₂)) (huF' _ (hsubF' hq₁))
        (huF' _ (hsubF' hq₂)) hτ hτ' (hlocq.trans (min_le_right _ _))
        (m _ hgF _ hp₁) (m _ hgF _ hp₂) (m _ hgF' _ hq₁) (m _ hgF' _ hq₂) ⟨?_, ?_⟩
      · rw [← hZe, ← hWe]; linarith
      · rw [← hZe]; linarith
    · simp only [hCdef, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨G.kMult_cases _, G.kMult_cases _, hz, hz'⟩
    · have h1 : ‖longSum X L q.1 - z‖ ≤ μ / 2 := by
        have := hzZ; simp only [longSum] at this ⊢; linarith
      have h2 : ‖longSum X L F' - z'‖ ≤ μ / 2 := by
        have := hzW; simp only [longSum] at this ⊢; linarith
      simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, sub_self, norm_zero]
      refine max_lt hμ (max_lt hμ (max_lt (by linarith) (by linarith)))
    · exact hH1 _ _ (G.kMult_cases _) (G.kMult_cases _) _ _ _ _ s u w hZ6 hW6 hτ hτ' hs hu hw
        (e1.trans htolε) (e2.trans htolε) (hlocq.trans (min_le_left _ _))
  have key := hpin X hX C hC A hA hdata
  have hsplit : (hhFaces X L G mk).card = Rest.card + Exc.card :=
    (Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)).symm
  have hM : (3 * Bad.card : ℝ) ≤ ε / 2 * D := by
    have h1 : (3 * Bad.card : ℝ) ≤ 3 * |M| := by
      have := le_abs_self M; linarith
    have h2 : 6 * |M| / ε ≤ D := hDbig X hX
    have h3 : 6 * |M| ≤ ε * D := by rw [div_le_iff₀ hε] at h2; linarith
    linarith
  have hExc' : (Exc.card : ℝ) ≤ 3 * Bad.card := by exact_mod_cast hExc
  rw [hsplit, Nat.cast_add, ← hAcard]
  linarith


/-- **`H–H` adjacency is pinned** (Verification Guide §13.1, identity (H1)): for every `η > 0`,
few edges of the track graph join two degree-two faces. -/
theorem hh_edges_few (η : ℝ) (_hη : 0 < η) : LocalExclusion η qHH := by
  intro ε hε lam hlam θ δ _ _
  obtain ⟨tol, htol, a₀, ha₀, h⟩ := hhFaces_few (ε := ε / 4) (by positivity) hlam
  refine ⟨tol, htol, a₀, ha₀, fun a ha hab => ?_⟩
  filter_upwards [h a ha hab, card_trackEnds] with n hn hends
  intro hfm X hX htri O _ G mk hmk _ hsat
  have h1 := qHH_le_four_mul (hends hfm X hX htri) (a * diam X) G mk
    (flaggedFaces X O (a * diam X) lam θ δ G)
  have h2 := hn hfm X hX htri G mk hmk hsat
  linarith

end Erdos99

end

end HHAdjacency

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `CapReflection`
-/

section CapReflection

/-!
# The two ports of a two-edge cap are reflections of each other (Verification Guide §13.5)

At a two-edge hull return `(v, x, w)` the cap is the isosceles triangle with apex `x` and unit legs
`x - v`, `w - x`.  The Guide's identity (H2) uses that the second port vector is the reflection of
the first one across the hull chord:

  `w - x = ζ² · conj (x - v)`,  where `ζ = (w - v) / |w - v|`.

This holds exactly (not only up to a locality error); it is proved here.

* `reflect_of_norm_eq`: the identity for two complex numbers `a, b` with `‖a‖ = ‖b‖` and
  `a + b ≠ 0`;
* `twoEdgeReturn_reflect`: the identity at a two-edge hull return.
-/

@[expose] public noncomputable section

open ComplexConjugate Classical

namespace Erdos99

/-- If `‖a‖ = ‖b‖` and `a + b ≠ 0`, then `b` is the reflection of `a` across the line through `0`
and `a + b`: with `ζ = (a + b) / ‖a + b‖`, `b = ζ² · conj a`. -/
theorem reflect_of_norm_eq {a b : ℂ} (hab : ‖a‖ = ‖b‖) (hs : a + b ≠ 0) :
    b = ((a + b) / (‖a + b‖ : ℂ)) ^ 2 * conj a := by
  have hn : (‖a + b‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hs
  have hsq : ((‖a + b‖ : ℂ)) ^ 2 = (a + b) * conj (a + b) := by
    rw [← Complex.mul_conj']
  have ha : a * conj a = b * conj b := by
    rw [Complex.mul_conj', Complex.mul_conj', hab]
  rw [div_pow, hsq]
  have hc : conj (a + b) ≠ 0 := by
    intro h; exact hs (by simpa using congrArg conj h)
  field_simp
  rw [map_add]
  linear_combination -ha

/-- **The ports of a two-edge cap are reflections across the hull chord** (Verification Guide
§13.5).  At a two-edge hull return `(v, x, w)`, with `ζ = (w - v) / |w - v|` the unit direction of
the hull side, the port vectors satisfy `w - x = ζ² · conj (x - v)` exactly. -/
theorem twoEdgeReturn_reflect {X : Finset Plane} {v x w : Plane}
    (h : (v, x, w) ∈ twoEdgeReturns X) :
    toC w - toC x =
      ((toC w - toC v) / (‖toC w - toC v‖ : ℂ)) ^ 2 * conj (toC x - toC v) := by
  obtain ⟨-, -, h1, h2, h3⟩ := Finset.mem_filter.1 h
  have hn1 : ‖toC x - toC v‖ = 1 := by
    rw [← dist_eq_norm, dist_toC, dist_comm]; exact h1
  have hn2 : ‖toC w - toC x‖ = 1 := by
    rw [← dist_eq_norm, dist_toC, dist_comm]; exact h2
  have hs : (toC x - toC v) + (toC w - toC x) = toC w - toC v := by ring
  have hne : (toC x - toC v) + (toC w - toC x) ≠ 0 := by
    rw [hs, sub_ne_zero]
    intro he
    have := congrArg (fun z => dist z (toC v)) he
    simp only [dist_self, dist_toC] at this
    rw [dist_comm] at this
    linarith
  have := reflect_of_norm_eq (hn1.trans hn2.symm) hne
  rwa [hs] at this

end Erdos99

end

end CapReflection

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `OneShortAlgebra`
-/

section OneShortAlgebra

/-!
# Algebra of the one-short-port cap estimate (Verification Guide §13.5)

* `approx_H2`: the approximate cap identity (H2) at the receiving face;
* `cap_reflect_data`: at a two-edge cap whose ports are `e'` and `e''`, every orientation of `e'`
  is `ζ² conj` of some orientation of `e''` (`ζ` the hull direction);
* `cap_pinned_count`: admissible cap data near boundedly many centres pin few hull sides.
-/

open scoped BigOperators Real
open Filter Polynomial ComplexConjugate

@[expose] public noncomputable section

open Classical

namespace Erdos99

open LocalCharge QuadraticResponse DirectionPinning EstablishedExternalResults

/-- **Approximate (H2).** If `‖k τ + ζ² conj c + u + Z‖ ≤ δ` with `u, ζ` unit, `‖Z‖ ≤ 6` and
`‖τ - ζ‖ ≤ δ`, then the cap polynomial is small at `ζ`. -/
lemma approx_H2 {k : ℝ} (hk : k = 1 ∨ k = 2) {τ ζ c u Z : ℂ} (hζ : ‖ζ‖ = 1) (hu : ‖u‖ = 1)
    {δ : ℝ} (h : ‖(k : ℂ) * τ + ζ ^ 2 * conj c + u + Z‖ ≤ δ) (hτ : ‖τ - ζ‖ ≤ δ) :
    ‖(capPoly k c Z).eval ζ‖ ≤ 3 * δ * (2 + 3 * δ) := by
  set w : ℂ := (k : ℂ) * ζ + ζ ^ 2 * conj c + Z with hwdef
  have hk2 : ‖(k : ℂ)‖ ≤ 2 := by
    rw [Complex.norm_real]; rcases hk with rfl | rfl <;> norm_num
  have hwu : ‖w + u‖ ≤ 3 * δ := by
    have e : w + u = ((k : ℂ) * τ + ζ ^ 2 * conj c + u + Z) - (k : ℂ) * (τ - ζ) := by
      rw [hwdef]; ring
    rw [e]
    calc _ ≤ ‖(k : ℂ) * τ + ζ ^ 2 * conj c + u + Z‖ + ‖(k : ℂ) * (τ - ζ)‖ := norm_sub_le _ _
      _ ≤ δ + 2 * δ := by
          rw [norm_mul]
          gcongr
      _ = 3 * δ := by ring
  have h1 : ‖w‖ ≤ 1 + 3 * δ := by
    have := norm_sub_le (w + u) u
    rw [add_sub_cancel_right, hu] at this; linarith
  have h2 : 1 - 3 * δ ≤ ‖w‖ := by
    have := norm_sub_le (w + u) w
    rw [add_sub_cancel_left, hu] at this; linarith
  rw [capPoly_eval hζ, norm_mul, norm_pow, hζ, one_pow, one_mul, Complex.norm_real,
    Real.norm_eq_abs]
  rw [abs_le]
  constructor <;> nlinarith [norm_nonneg w]

/-- **The ports of a one-short-port cap.**  At a two-edge return `(p.1, x, p.2)` with ports `e'`
and `e''`, every orientation `(y₁, y₂)` of `e'` is the reflection `ζ² conj` of an orientation of
`e''`, where `ζ` is the direction of the hull side `p`. -/
lemma cap_reflect_data {X : Finset Plane} {p : Plane × Plane} {x : Plane}
    (h : (p.1, x, p.2) ∈ twoEdgeReturns X) {e' e'' : Sym2 Plane}
    (hcase : (e' = s(p.1, x) ∧ e'' = s(x, p.2)) ∨ (e' = s(x, p.2) ∧ e'' = s(p.1, x)))
    {y₁ y₂ : Plane} (hy : e' = s(y₁, y₂)) :
    ∃ z₁ z₂ : Plane, e'' = s(z₁, z₂) ∧ ‖toC z₂ - toC z₁‖ = 1 ∧
      toC y₂ - toC y₁ = (toC (sideDir p)) ^ 2 * conj (toC z₂ - toC z₁) := by
  have hR := twoEdgeReturn_reflect h
  obtain ⟨-, -, h1, h2, h3⟩ := Finset.mem_filter.1 h
  have hn1 : ‖toC x - toC p.1‖ = 1 := by
    rw [← dist_eq_norm, dist_toC, dist_comm]; exact h1
  have hn2 : ‖toC p.2 - toC x‖ = 1 := by
    rw [← dist_eq_norm, dist_toC, dist_comm]; exact h2
  have hζ : toC (sideDir p) = (toC p.2 - toC p.1) / (‖toC p.2 - toC p.1‖ : ℂ) := by
    rw [sideDir, map_smul, ← map_sub, norm_toC, Complex.real_smul, div_eq_inv_mul]
    push_cast; rfl
  rw [← hζ] at hR
  set ζ := toC (sideDir p) with hζdef
  have hne : p.1 ≠ p.2 := fun he => by rw [he, dist_self] at h3; linarith
  have hζ1 : ‖ζ‖ = 1 := by rw [hζdef, norm_toC]; exact norm_sideDir hne
  have hcc : ζ ^ 2 * conj ζ ^ 2 = 1 := by
    rw [← mul_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq, hζ1]; norm_num
  -- the reverse identity
  have hR' : toC x - toC p.1 = ζ ^ 2 * conj (toC p.2 - toC x) := by
    rw [hR, map_mul, map_pow, Complex.conj_conj, ← mul_assoc, hcc, one_mul]
  rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases Sym2.eq_iff.1 hy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨x, p.2, rfl, hn2, hR'⟩
    · refine ⟨p.2, x, Sym2.eq_swap, by rw [norm_sub_rev]; exact hn2, ?_⟩
      rw [show toC x - toC p.2 = -(toC p.2 - toC x) by ring, map_neg]
      linear_combination -hR'
  · rcases Sym2.eq_iff.1 hy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨p.1, x, rfl, hn1, hR⟩
    · refine ⟨x, p.1, Sym2.eq_swap, by rw [norm_sub_rev]; exact hn1, ?_⟩
      rw [show toC p.1 - toC x = -(toC x - toC p.1) by ring, map_neg]
      linear_combination -hR

/-- Admissible cap data `(k, c, Z)`: `k ∈ {1, 2}`, `c` a unit vector and `‖Z‖ ≤ 6`. -/
def CapAdm (d : ℝ × ℂ × ℂ) : Prop := (d.1 = 1 ∨ d.1 = 2) ∧ ‖d.2.1‖ = 1 ∧ ‖d.2.2‖ ≤ 6

/-- The coefficient vector of the cap polynomial as an explicit function of the data. -/
def capCoeffVec (d : ℝ × ℂ × ℂ) : Fin 5 → ℂ :=
  ![d.2.2 * d.2.1, (d.1 : ℂ) * d.2.1 + (d.1 : ℂ) * d.2.2,
    (d.1 : ℂ) ^ 2 + d.2.1 * conj d.2.1 + d.2.2 * conj d.2.2 - 1,
    (d.1 : ℂ) * conj d.2.2 + (d.1 : ℂ) * conj d.2.1, conj d.2.1 * conj d.2.2]

lemma polyCoeffs_capPoly (d : ℝ × ℂ × ℂ) :
    polyCoeffs 4 (capPoly d.1 d.2.1 d.2.2) = capCoeffVec d := by
  ext i
  simp only [polyCoeffs, capPoly_expand, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  fin_cases i <;> simp [capCoeffVec]

lemma continuous_capCoeffVec : Continuous capCoeffVec := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp only [capCoeffVec] <;> dsimp <;> fun_prop

lemma isCompact_capAdm : IsCompact {d : ℝ × ℂ × ℂ | CapAdm d} := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · simp only [CapAdm, Set.setOf_and, Set.setOf_or]
    repeat' first | apply IsClosed.inter | apply IsClosed.union
    all_goals first
      | exact isClosed_eq (by fun_prop) (by fun_prop)
      | exact isClosed_le (by fun_prop) (by fun_prop)
  · rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨6, fun d hd => ?_⟩
    obtain ⟨hk, hc, hZ⟩ := hd
    have hk' : ‖d.1‖ ≤ 6 := by rcases hk with h | h <;> rw [h] <;> norm_num
    simp only [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
    exact max_le hk' (max_le (by rw [hc]; norm_num) hZ)

/-- **Pinned caps are few.**  For a bounded number `N` of centres, admissible cap data near a
centre whose cap polynomial (H2) is small at the direction of a hull side pins that side: such
sides number at most `ε D`. -/
theorem cap_pinned_count (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∃ μ > 0, ∀ᶠ n in atTop, ∀ X, IsOptimal n X →
      ∀ C : Finset (ℝ × ℂ × ℂ), C.card ≤ N → ∀ A ⊆ ccwHullSides X,
        (∀ p ∈ A, ∃ d : ℝ × ℂ × ℂ, CapAdm d ∧ (∃ c ∈ C, ‖d - c‖ < μ) ∧
          ‖(capPoly d.1 d.2.1 d.2.2).eval (toC (sideDir p))‖ < r) →
        (A.card : ℝ) ≤ ε * diam X := by
  have hlow : ∀ d, CapAdm d → 1 ≤ ‖capCoeffVec d‖ := fun d hd => by
    rw [← polyCoeffs_capPoly]; exact one_le_norm_capCoeffs hd.1 hd.2.1 _
  obtain ⟨r, hr, μ, hμ, hpin⟩ := pinned_directions_few 4 N hε one_pos
  have huc := isCompact_capAdm.uniformContinuousOn_of_continuous
    continuous_capCoeffVec.continuousOn
  obtain ⟨μ₁, hμ₁, hu⟩ := Metric.uniformContinuousOn_iff.1 huc μ hμ
  refine ⟨r, hr, μ₁ / 2, by positivity, ?_⟩
  filter_upwards [hpin] with n hn X hX C hC A hA hp
  set good : Finset (ℝ × ℂ × ℂ) := C.filter (fun c => ∃ d, CapAdm d ∧ ‖d - c‖ < μ₁ / 2)
    with hgood
  set rc : ℝ × ℂ × ℂ → ℝ × ℂ × ℂ := fun c =>
    if h : ∃ d, CapAdm d ∧ ‖d - c‖ < μ₁ / 2 then h.choose else c with hrcdef
  have hrc : ∀ c ∈ good, CapAdm (rc c) ∧ ‖rc c - c‖ < μ₁ / 2 := by
    intro c hc
    have h := (Finset.mem_filter.1 hc).2
    simp only [hrcdef, dif_pos h]
    exact h.choose_spec
  set T : Finset (Fin 5 → ℂ) := good.image (fun c => capCoeffVec (rc c)) with hTdef
  have hmemgood : ∀ d c, CapAdm d → c ∈ C → ‖d - c‖ < μ₁ / 2 → c ∈ good :=
    fun d c hd hc hdc => Finset.mem_filter.2 ⟨hc, d, hd, hdc⟩
  rcases T.eq_empty_or_nonempty with hT | ⟨t₀, ht₀⟩
  · have hA0 : A = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun p hpA => ?_
      obtain ⟨d, hd, ⟨c, hc, hdc⟩, -⟩ := hp p hpA
      have h1 : capCoeffVec (rc c) ∈ T :=
        Finset.mem_image_of_mem _ (hmemgood d c hd hc hdc)
      rw [hT] at h1; exact Finset.notMem_empty _ h1
    rw [hA0, Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg hε.le Metric.diam_nonneg
  have hTc : T.card ≤ N := Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans hC)
  set c₀ : Fin N → Fin 5 → ℂ := fun j =>
    if h : (j : ℕ) < T.card then (T.equivFin.symm ⟨j, h⟩ : Fin 5 → ℂ) else t₀ with hc₀def
  have hc₀T : ∀ j, c₀ j ∈ T := by
    intro j
    simp only [hc₀def]
    split_ifs
    · exact (T.equivFin.symm _).2
    · exact ht₀
  have hTc₀ : ∀ t (ht : t ∈ T), ∃ j, c₀ j = t := by
    intro t ht
    set i := T.equivFin ⟨t, ht⟩
    refine ⟨⟨i, lt_of_lt_of_le i.2 hTc⟩, ?_⟩
    simp only [hc₀def, dif_pos i.2]
    simp [i]
  refine hn X hX c₀ (fun j => ?_) A hA (fun p hpA => ?_)
  · obtain ⟨c, hc, hce⟩ := Finset.mem_image.1 (hc₀T j)
    rw [← hce]; exact hlow _ (hrc c hc).1
  · obtain ⟨d, hd, ⟨c, hc, hdc⟩, hev⟩ := hp p hpA
    have hcg := hmemgood d c hd hc hdc
    obtain ⟨j, hj⟩ := hTc₀ _ (Finset.mem_image_of_mem (fun c => capCoeffVec (rc c)) hcg)
    refine ⟨j, capCoeffVec d, ?_, ?_⟩
    · rw [hj]
      have hdist : dist d (rc c) < μ₁ := by
        rw [dist_eq_norm]
        have := norm_sub_le (d - c) (rc c - c)
        rw [sub_sub_sub_cancel_right] at this
        linarith [(hrc c hcg).2]
      have := hu d hd (rc c) (hrc c hcg).1 hdist
      rwa [dist_eq_norm] at this
    · rw [← polyCoeffs_capPoly, coeffPoly_polyCoeffs (natDegree_capPoly_le _ _ _)]
      exact hev

end Erdos99

end

end OneShortAlgebra

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `OneShortGeometry`
-/

section OneShortGeometry

/-!
# Geometry of the one-short-port cap estimate (Verification Guide §13.5)

* `trackCap_side`: if the track of a port of a face ends at a hull side, the far edge carries the
  opposite side vector (track translation) and lies within the track length;
* `oneShort_cap_ports`: the ports of a two-edge return with one short port are the two legs of the
  cap triangle; the other leg is a port with a long track;
* `hull_ports_clustered`: clustering of the long ports of hull sides (Lemma 3.3 at scale `λ D`);
* `cap_label_locality`: a face whose port track ends near a hull side has label direction close
  to the direction of that hull side.
-/

open scoped BigOperators Real
open Filter Polynomial ComplexConjugate

@[expose] public noncomputable section

open Classical

namespace Erdos99

open LocalCharge QuadraticResponse DirectionPinning EstablishedExternalResults

/-- **The far end of a port at a hull side.**  If the track of the port `(F, e)` of an exceptional
face ends at a hull side, the far edge is `s(y₁, y₂)` with `y₂ - y₁` the reversal of the side
vector of `F` along `e`, and `y₁` lies within the track length of the end of that side. -/
theorem trackCap_side :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ F ∈ exceptionalFaces X, ∀ e ∈ unitEdges X, ∀ ab ∈ orientedSides X F,
        Sym2.map toC e = s(ab.1, ab.2) → ∀ p, (otherEnd X (F, e)).1 = Sum.inr p →
        ∃ y₁ y₂ : Plane, (otherEnd X (F, e)).2 = s(y₁, y₂) ∧
          toC y₂ - toC y₁ = -(ab.2 - ab.1) ∧
          dist (toC y₁) ab.2 ≤ trackLength X (allTrackOf X e) := by
  filter_upwards [card_trackEnds, far_end_cases] with n hends hfar hfm X hX htri F hF e he ab hab
    hmap P₀ hP₀
  have hsep := hX.1.2
  obtain ⟨A, B⟩ := ab
  have hAB := (Finset.mem_product.1 (Finset.mem_filter.1 hab).1)
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hAB.1
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hAB.2
  have hdab : dist a b = 1 := dist_eq_one_of_mem_orientedSides hab
  have hee : e = s(b, a) := by
    have : Sym2.map toC e = Sym2.map toC s(b, a) := by rw [hmap, Sym2.map_mk]; exact Sym2.eq_swap
    exact Sym2.map.injective toC.injective this
  set p : Plane × Plane := (b, a) with hpdef
  have hp : p ∈ X ×ˢ X := Finset.mem_product.2 ⟨hb, ha⟩
  have hpd : dist p.1 p.2 = 1 := by rw [dist_comm]; exact hdab
  have hFf : F ∈ exceptionalFinset X := (mem_exceptionalFinset hsep).2 hF
  have hpF : IsPort X (Sum.inl F) e := ⟨hF, hmap ▸ (Finset.mem_filter.1 hab).2.1⟩
  obtain ⟨hTe, -⟩ := trackEnds_eq_otherEnd (hends hfm X hX htri) hFf he hpF
  set h := hopEnd X p with hhdef
  have hsub : h.2 - h.1 = a - b := hopEnd_sub p
  have hhX := hopEnd_mem hp
  have hmemT : s(h.1, h.2) ∈ allTrackOf X e := by
    obtain ⟨m, hm, hmv, -⟩ := exists_hopLen hp
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · rw [hhdef, ← hm]
      show s(b, a) ∈ allTrackOf X e
      rw [← hee]; exact mem_allTrackOf_self he
    · have h1 := iterate_mem_trackOf hmv m le_rfl hpos
      have h0 : s(p.1, p.2) ∈ rhombusEdges X := (stepL_spec (hmv 0 hpos)).rhombusEdge
      rw [hm] at h1
      rw [hee, allTrackOf_of_mem_rhombusEdges h0]
      exact h1
  have hunitT : s(h.1, h.2) ∈ unitEdges X := (Finset.mem_filter.1 hmemT).1
  -- an end at `s(h.1, h.2)` different from `(F, e)` is the other end
  have hother : ∀ N, (N, s(h.1, h.2)) ∈ trackEnds X (allTrackOf X e) →
      (N, s(h.1, h.2)) ≠ (Sum.inl F, e) → otherEnd X (F, e) = (N, s(h.1, h.2)) := by
    intro N hN hne
    rw [hTe, Finset.mem_insert, Finset.mem_singleton] at hN
    rcases hN with h' | h'
    · exact absurd h' hne
    · exact h'.symm
  by_cases hd : ∃ G ∈ exceptionalFaces X, (toC h.1, toC h.2) ∈ orientedSides X G
  · obtain ⟨G, hG, hGs⟩ := hd
    have hGf : G ∈ exceptionalFinset X := (mem_exceptionalFinset hsep).2 hG
    have hend : (Sum.inl G, s(h.1, h.2)) ∈ trackEnds X (allTrackOf X e) :=
      mem_trackEnds.2 ⟨Finset.mem_union_left _ (Finset.mem_map_of_mem _ hGf), hmemT,
        hG, (Finset.mem_filter.1 hGs).2.1⟩
    have hne : (Sum.inl G, s(h.1, h.2)) ≠ ((Sum.inl F, e) : PortNode × Sym2 Plane) := by
      intro heq
      simp only [Prod.mk.injEq, Sum.inl.injEq] at heq
      obtain ⟨rfl, he2⟩ := heq
      have hs : s((toC h.1, toC h.2).1, (toC h.1, toC h.2).2) =
          s(((toC a, toC b) : ℂ × ℂ).1, ((toC a, toC b) : ℂ × ℂ).2) := by
        have h3 := congrArg (Sym2.map toC) he2
        rw [Sym2.map_mk] at h3
        exact h3.trans hmap
      have := orientedSides_injOn (nonempty_of_mem_exceptionalFaces hG) hGs hab hs
      simp only [Prod.mk.injEq] at this
      have e1 := toC.injective this.1
      have e2 := toC.injective this.2
      rw [e1, e2] at hsub
      have : a = b := by
        have h2 : (2 : ℝ) • (a - b) = 0 := by
          rw [two_smul]; nth_rewrite 1 [← hsub]; abel
        have := (smul_eq_zero.1 h2).resolve_left (by norm_num)
        exact sub_eq_zero.1 this
      rw [this, dist_self] at hdab; norm_num at hdab
    have hoe := hother _ hend hne
    rw [hoe] at hP₀
    exact absurd hP₀ (by simp)
  · have hcap : hopDest X p = .cap := by rw [hopDest, dif_neg hd]
    have hcases := hfar hfm X hX htri p hp hpd hcap
    have key : ∀ P ∈ ccwHullSides X, IsPort X (Sum.inr P) s(h.1, h.2) →
        ∃ y₁ y₂ : Plane, (otherEnd X (F, e)).2 = s(y₁, y₂) ∧
          toC y₂ - toC y₁ = -(((toC a, toC b) : ℂ × ℂ).2 - ((toC a, toC b) : ℂ × ℂ).1) ∧
          dist (toC y₁) ((toC a, toC b) : ℂ × ℂ).2 ≤ trackLength X (allTrackOf X e) := by
      intro P hP hport
      have hend : (Sum.inr P, s(h.1, h.2)) ∈ trackEnds X (allTrackOf X e) :=
        mem_trackEnds.2 ⟨Finset.mem_union_right _ (Finset.mem_map_of_mem _ hP), hmemT, hport⟩
      have hoe := hother _ hend (by simp)
      refine ⟨h.1, h.2, by rw [hoe], ?_, ?_⟩
      · simp only
        rw [← map_sub, hsub, map_sub]; ring
      · simp only
        rw [dist_toC]
        refine (dist_hopEnd_le hp).trans ?_
        show ((srcLen X s(b, a) : ℕ) : ℝ) ≤ _
        rw [← hee]
        exact_mod_cast srcLen_le_trackLength_allTrackOf X e
    rcases hcases with hu | ⟨P, hP, hPd, Fc, hc, hbd, -⟩
    · have hP := (Finset.mem_filter.1 hu).1
      refine key _ hP ⟨hP, hunitT, ?_⟩
      rw [if_pos (Finset.mem_filter.1 hu).2]
      exact Sym2.eq_swap
    · exact key P hP ⟨hP, hunitT, by rw [if_neg hPd.ne']; exact ⟨Fc, hc, hbd⟩⟩

/-- **The ports of a one-short-port cap.**  At a two-edge return `p` with exactly one short port
`e'`, there is a cap apex `x` such that the ports are the two legs `s(p.1, x)`, `s(x, p.2)`; the
leg `e''` other than `e'` is a port whose track has at least `L` rhombi. -/
theorem oneShort_cap_ports :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      ∀ (L : ℝ) (p : Plane × Plane), p ∈ ccwHullSides X → returnLength X p.1 p.2 = 2 →
      shortDeg X L (Sum.inr p) = 1 → ∀ e', e' ∈ unitEdges X → IsPort X (Sum.inr p) e' →
      (trackLength X (allTrackOf X e') : ℝ) < L →
      ∃ x e'', (p.1, x, p.2) ∈ twoEdgeReturns X ∧ e'' ∈ unitEdges X ∧ IsPort X (Sum.inr p) e'' ∧
        L ≤ (trackLength X (allTrackOf X e'') : ℝ) ∧
        ((e' = s(p.1, x) ∧ e'' = s(x, p.2)) ∨ (e' = s(x, p.2) ∧ e'' = s(p.1, x))) := by
  filter_upwards [exists_twoEdgeReturn_ports, portDeg_hullSide] with n hports hdeg hfm X hX L p hp
    hret hsd e' he' hpe' hlen'
  obtain ⟨x, hx, hp1, hp2⟩ := hports hfm X hX p hp hret
  have hpd := hdeg hfm X hX p hp
  rw [hret] at hpd
  obtain ⟨-, -, hd1, -, hd3⟩ := Finset.mem_filter.1 hx
  have hne : s(p.1, x) ≠ s(x, p.2) := by
    intro h
    rcases Sym2.eq_iff.1 h with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [h1, dist_self] at hd1; norm_num at hd1
    · rw [h1, dist_self] at hd3; norm_num at hd3
  have hP : (unitEdges X).filter (IsPort X (Sum.inr p)) = {s(p.1, x), s(x, p.2)} := by
    symm
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro e he
      rw [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl
      · exact Finset.mem_filter.2 ⟨hp1.2.1, hp1⟩
      · exact Finset.mem_filter.2 ⟨hp2.2.1, hp2⟩
    · rw [Finset.card_pair hne]; exact le_of_eq hpd
  have hmem : ∀ e, e ∈ unitEdges X → IsPort X (Sum.inr p) e → e = s(p.1, x) ∨ e = s(x, p.2) := by
    intro e he hpe
    have : e ∈ (unitEdges X).filter (IsPort X (Sum.inr p)) := Finset.mem_filter.2 ⟨he, hpe⟩
    rw [hP, Finset.mem_insert, Finset.mem_singleton] at this
    exact this
  have hlong : ∀ e'', e'' ∈ unitEdges X → IsPort X (Sum.inr p) e'' → e'' ≠ e' →
      L ≤ (trackLength X (allTrackOf X e'') : ℝ) := by
    intro e'' he'' hpe'' hne''
    by_contra hlt
    push_neg at hlt
    exact hne'' (Finset.card_le_one.1 (le_of_eq hsd) _ (Finset.mem_filter.2 ⟨he'', hpe'', hlt⟩) _
      (Finset.mem_filter.2 ⟨he', hpe', hlen'⟩))
  rcases hmem e' he' hpe' with h | h
  · refine ⟨x, s(x, p.2), hx, hp2.2.1, hp2, hlong _ hp2.2.1 hp2 (h ▸ hne.symm), Or.inl ⟨h, rfl⟩⟩
  · refine ⟨x, s(p.1, x), hx, hp1.2.1, hp1, hlong _ hp1.2.1 hp1 (h ▸ hne), Or.inr ⟨h, rfl⟩⟩

/-- **Clustering of the long hull ports** (Lemma 3.3 at the macroscopic scale `λ D`): there is a
bound `N_c` (depending on `λ` only) such that for every tolerance `ε_c`, outside a bounded number of
exceptional hull sides, every port vector of a hull side on a track with at least `λ D` rhombi
lies within `ε_c` of one of at most `N_c` vectors. -/
theorem hull_ports_clustered {lam : ℝ} (hlam : 0 < lam) :
    ∃ Nc : ℕ, ∀ εc > 0, ∃ M : ℝ, ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      ¬ HasUnitTriangle X → ∃ U : Finset ℂ, U.card ≤ Nc ∧ ∃ Bad : Finset (Plane × Plane),
        (Bad.card : ℝ) ≤ M ∧ ∀ p ∈ ccwHullSides X, p ∉ Bad → ∀ z₁ z₂ : Plane,
          s(z₁, z₂) ∈ unitEdges X → IsPort X (Sum.inr p) s(z₁, z₂) →
          lam * diam X ≤ trackLength X (allTrackOf X s(z₁, z₂)) →
          ∃ u ∈ U, ‖(toC z₂ - toC z₁) - u‖ ≤ εc := by
  obtain ⟨C1, hC1⟩ := rhombus_defect_sum
  obtain ⟨C2, hC2⟩ := tracks_card_le
  refine ⟨⌊2 * C2 / lam⌋₊ * 6, fun εc hεc => ?_⟩
  set ε' := min (εc / 4) (1 / 4) with hε'
  have hε'0 : 0 < ε' := lt_min (by linarith) (by norm_num)
  refine ⟨2 * (4 * max C1 0 / (ε' * lam)), ?_⟩
  filter_upwards [hC1, hC2, card_trackEnds, tendsto_minDiam.eventually (eventually_ge_atTop 1)]
    with n h1 h2 hends hD hfm X hX htri
  have hD1 : 1 ≤ diam X := by rw [hX.diam_eq]; exact hD
  have hD0 : 0 < diam X := by linarith
  have hsep := hX.1.2
  have hK : ∑ Q ∈ rhombi X, rhombusDefect Q ≤ max C1 0 * diam X :=
    (h1 hfm X hX htri).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hD0.le)
  have hL : 0 < lam * diam X := mul_pos hlam hD0
  obtain ⟨Disc, hDsub, Cs, hCs1, hDcard, hCcard, hcov⟩ :=
    track_clustering hsep htri hε'0 hL hK
  choose! rt hrt1 hrt6 using fun c (hc : c ∈ Cs) => exists_unit_sixth_root (hCs1 c hc)
  refine ⟨(Cs ×ˢ sixRoots).image (fun p => p.2 * rt p.1), ?_, ?_⟩
  · refine Finset.card_image_le.trans ?_
    rw [Finset.card_product]
    have hsix : sixRoots.card ≤ 6 := Finset.card_le_six
    refine Nat.mul_le_mul ?_ hsix
    refine Nat.le_floor ?_
    rw [le_div_iff₀ hlam]
    have := h2 hfm X hX htri
    have h3 : (Cs.card : ℝ) * lam * diam X ≤ 2 * C2 * diam X := by nlinarith
    nlinarith
  refine ⟨(Disc.biUnion (trackEnds X)).image (fun p => Sum.elim (fun _ => ((0 : Plane), (0 : Plane)))
    id p.1), ?_, ?_⟩
  · have hc1 : ((Disc.biUnion (trackEnds X)).image (fun p => Sum.elim
        (fun _ => ((0 : Plane), (0 : Plane))) id p.1)).card ≤ 2 * Disc.card := by
      refine Finset.card_image_le.trans (Finset.card_biUnion_le.trans ?_)
      rw [Finset.sum_congr rfl (fun T hT => hends hfm X hX htri T
        (tracks_subset_allTracks X (hDsub hT))), Finset.sum_const, smul_eq_mul, mul_comm]
    have hc2 : (Disc.card : ℝ) ≤ 4 * max C1 0 / (ε' * lam) := by
      rw [le_div_iff₀ (mul_pos hε'0 hlam)]
      have : (Disc.card : ℝ) * (ε' * lam) * diam X ≤ 4 * max C1 0 * diam X := by
        nlinarith
      exact le_of_mul_le_mul_right this hD0
    calc _ ≤ ((2 * Disc.card : ℕ) : ℝ) := by exact_mod_cast hc1
      _ ≤ _ := by push_cast; linarith
  · intro p hp hpB z₁ z₂ he hport hlen
    set e := s(z₁, z₂) with hedef
    have heR : e ∈ rhombusEdges X := by
      by_contra hne
      rw [allTrackOf_of_not_mem he hne, trackLength_singleton hsep htri he hne] at hlen
      push_cast at hlen; linarith
    have hT : allTrackOf X e ∈ tracks X := by
      rw [allTrackOf_of_mem_rhombusEdges heR]; exact Finset.mem_image_of_mem _ heR
    have hnD : allTrackOf X e ∉ Disc := by
      intro hD'
      apply hpB
      refine Finset.mem_image.2 ⟨(Sum.inr p, e), Finset.mem_biUnion.2 ⟨_, hD', ?_⟩, rfl⟩
      exact Finset.mem_filter.2 ⟨Finset.mem_product.2
        ⟨Finset.mem_union_right _ (Finset.mem_map_of_mem _ hp), mem_allTrackOf_self he⟩, hport⟩
    obtain ⟨c, hc, hcd⟩ := hcov _ hT hnD hlen
    have heT : e ∈ allTrackOf X e := mem_allTrackOf_self he
    rw [tdir_eq hT heT] at hcd
    have hmap : Sym2.map toC e = s((toC z₁, toC z₂).1, (toC z₁, toC z₂).2) := by
      exact Sym2.map_mk toC (z₁, z₂)
    obtain ⟨hv1, hv6⟩ := side_pow_six he hmap
    have hr : 2 * ε' ≤ 1 / 2 := by have := min_le_right (εc / 4) (1 / 4); linarith
    obtain ⟨ζ, hζ, hclose⟩ := sixth_root_near hv1 (hrt1 c hc) hr
      (by rw [hv6, hrt6 c hc]; exact hcd)
    refine ⟨ζ * rt c, Finset.mem_image.2 ⟨(c, ζ), Finset.mem_product.2 ⟨hc, hζ⟩, rfl⟩, ?_⟩
    have := min_le_left (εc / 4) (1 / 4)
    simp only at hclose
    linarith

/-- **Label locality at a cap**: a good face with a side ending within `L` of a point within `2`
of the start of a hull side `p` has label direction within `ρ` of the direction of `p`. -/
theorem cap_label_locality {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ c > 0, ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ (L tol : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane))
        (lab : Set ℂ → Plane × Plane), L ≤ c * diam X → tol ≤ c → LabelledBy X tol G mk lab →
      ∀ F ∈ G.good, ∀ ab ∈ orientedSides X F, ∀ (p : Plane × Plane) (y : Plane),
        p ∈ ccwHullSides X → dist (toC y) ab.2 ≤ L → dist y p.1 ≤ 2 →
        ‖labDir lab F - toC (sideDir p)‖ ≤ ρ := by
  have hκ : (0 : ℝ) < (ρ / 16) ^ 2 / 300 := by positivity
  have ht : Tendsto (fun n => minDiam n ^ (-(2 / 9 : ℝ))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num)).comp tendsto_minDiam
  refine ⟨ρ / 12, by positivity, ?_⟩
  filter_upwards [eventually_roundData_rate, ht.eventually (ge_mem_nhds hκ),
    tendsto_minDiam.eventually_ge_atTop (max 1 (24 / ρ))] with
    n hround hsmall hD hfm X hX htri L tol G mk lab hL htol hlab F hFg ab hab p y hp hyab hyp
  rw [← hX.diam_eq] at hsmall hD
  set D := diam X with hDdef
  have hD1 : 1 ≤ D := le_trans (le_max_left _ _) hD
  have hDρ : 24 / ρ ≤ D := le_trans (le_max_right _ _) hD
  have hD0 : 0 < D := by linarith
  have h1 := (hlab.2 F hFg).2.2 ab hab
  have hunit : ‖ab.2 - ab.1‖ = 1 := by
    rw [← dist_eq_norm, dist_comm]
    obtain ⟨A, B⟩ := ab
    have hAB := (Finset.mem_product.1 (Finset.mem_filter.1 hab).1)
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hAB.1
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hAB.2
    rw [dist_toC]; exact dist_eq_one_of_mem_orientedSides hab
  have htD : tol * D ≤ ρ / 12 * D := mul_le_mul_of_nonneg_right htol hD0.le
  have hdist : dist (lab F).1 p.1 ≤ ρ / 6 * D + 3 := by
    rw [← dist_toC, dist_eq_norm]
    have e1 : toC (lab F).1 - toC p.1 =
        -(ab.1 - toC (lab F).1) - (ab.2 - ab.1) + (ab.2 - toC y) + (toC y - toC p.1) := by ring
    rw [e1]
    have n1 := norm_add_le (-(ab.1 - toC (lab F).1) - (ab.2 - ab.1) + (ab.2 - toC y))
      (toC y - toC p.1)
    have n2 := norm_add_le (-(ab.1 - toC (lab F).1) - (ab.2 - ab.1)) (ab.2 - toC y)
    have n3 := norm_sub_le (-(ab.1 - toC (lab F).1)) (ab.2 - ab.1)
    rw [norm_neg] at n3
    have n4 : ‖ab.2 - toC y‖ ≤ L := by rw [← dist_eq_norm, dist_comm]; exact hyab
    have n5 : ‖toC y - toC p.1‖ ≤ 2 := by rw [← dist_eq_norm, dist_toC]; exact hyp
    linarith
  obtain ⟨O, η, hR⟩ := hround X hX
  have hp1 := mem_ccwHullSides.1 (Finset.mem_filter.1 (hlab.2 F hFg).1).1
  have hp2 := mem_ccwHullSides.1 hp
  have hs := sideDir_sub_le hR hp1 hp2
  rw [labDir, ← map_sub, LinearIsometryEquiv.norm_map]
  refine hs.trans ?_
  have hsq : √(3 * (100 * D ^ (-(2 / 9 : ℝ)))) ≤ ρ / 16 := by
    rw [show ρ / 16 = √((ρ / 16) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hfrac : 2 * dist (lab F).1 p.1 / D ≤ ρ / 3 + ρ / 4 := by
    rw [div_le_iff₀ hD0]
    have : 24 ≤ ρ * D := by rwa [div_le_iff₀ hρ, mul_comm] at hDρ
    nlinarith
  linarith

end Erdos99

end

end OneShortGeometry

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `SaturationHop`
-/

section SaturationHop

/-!
# Track geometry for the saturated token process (Verification Guide §10)

* `hopEnd_eq_of_stuck`: the hop ends at the first edge with no rhombus on its left.
* `hopEnd_swap`: **reversing a track**: the far end of the reversed far end of the track of an
  initial edge `p` is the reversal of `p`.
* `hopDest_eq_face`: the receiver of a token is the exceptional face on the left of the far end of
  its track.
* `otherEnd_cases`: the other end of the track through a port of an exceptional face is the far end
  of the hop from that port, at an exceptional face or at a hull side.
-/

open scoped BigOperators Real
open Filter Topology

@[expose] public noncomputable section

open Classical

namespace Erdos99

section
variable {X : Finset Plane}

/-- The hop ends at any index where the step is stuck. -/
lemma hopEnd_eq_of_stuck {p : Plane × Plane} (hp : p ∈ X ×ˢ X) {k : ℕ}
    (h : ¬ ∃ q, LeftStep X ((stepL X)^[k] p) q) : hopEnd X p = (stepL X)^[k] p := by
  have h1 := iterate_stepL_stuck h (max k (X ×ˢ X).card) (le_max_left _ _)
  have h2 := iterate_stepL_stuck (k := (X ×ˢ X).card) (hopEnd_terminal hp)
    (max k (X ×ˢ X).card) (le_max_right _ _)
  rw [← h1]
  exact h2.symm

/-- **Reversing a track.**  For an initial edge `p`, the hop from the reversal of the far end of
`p` ends at the reversal of `p`. -/
theorem hopEnd_swap (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X) {p : Plane × Plane}
    (hp : p ∈ X ×ˢ X) (hinit : Initial X p) :
    hopEnd X ((hopEnd X p).2, (hopEnd X p).1) = (p.2, p.1) := by
  obtain ⟨m, hm, hmv, -⟩ := exists_hopLen hp
  have key : ∀ k ≤ m, (stepL X)^[k] (((stepL X)^[m] p).2, ((stepL X)^[m] p).1) =
      (((stepL X)^[m - k] p).2, ((stepL X)^[m - k] p).1) := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih (by omega)]
      have hs : LeftStep X ((stepL X)^[m - (k + 1)] p) ((stepL X)^[m - k] p) := by
        have e : m - k = (m - (k + 1)) + 1 := by omega
        rw [e, Function.iterate_succ_apply']
        exact stepL_spec (hmv _ (by omega))
      have hr := hs.rev
      exact LeftStep.unique hX htri (stepL_spec ⟨_, hr⟩) hr
  have h0 := key m le_rfl
  rw [Nat.sub_self, Function.iterate_zero_apply] at h0
  have hmem : (((stepL X)^[m] p).2, ((stepL X)^[m] p).1) ∈ X ×ˢ X := by
    have := iterate_stepL_mem hp m
    exact Finset.mem_product.2 ⟨(Finset.mem_product.1 this).2, (Finset.mem_product.1 this).1⟩
  rw [← hm, hopEnd_eq_of_stuck hmem (k := m), h0]
  rw [h0]
  rintro ⟨q, hq⟩
  exact hinit ⟨(q.2, q.1), by simpa using hq.rev⟩

/-- **The receiver of a token** is the exceptional face on the left of the far end of its
track. -/
lemma hopDest_eq_face (hX : IsSeparated X) {x : Plane × Plane} {F : Set ℂ}
    (hF : F ∈ exceptionalFaces X)
    (h : (toC (hopEnd X x).1, toC (hopEnd X x).2) ∈ orientedSides X F) :
    hopDest X x = .face F := by
  have hex : ∃ F ∈ exceptionalFaces X,
      (toC (hopEnd X x).1, toC (hopEnd X x).2) ∈ orientedSides X F := ⟨F, hF, h⟩
  rw [hopDest, dif_pos hex]
  congr 1
  obtain ⟨hG, hGs⟩ := hex.choose_spec
  obtain ⟨-, hb1, hl1⟩ := Finset.mem_filter.1 hGs
  obtain ⟨-, hb2, hl2⟩ := Finset.mem_filter.1 h
  exact face_left_unique hX (Finset.mem_filter.1 hb1).1 hG.1.1 hF.1.1 hb1 hb2 hl1 hl2

/-- The edge `s(b, a)` of an oriented side `(a, b)` is a unit edge. -/
lemma mem_unitEdges_of_mem_orientedSides {F : Set ℂ} {a b : Plane}
    (h : (toC a, toC b) ∈ orientedSides X F) : s(b, a) ∈ unitEdges X := by
  have hm := mem_of_mem_orientedSides h
  rw [mem_unitEdges]
  exact ⟨hm.2, hm.1, by rw [dist_comm]; exact dist_eq_one_of_mem_orientedSides h⟩

/-- The edges of the track of an exit edge contain the far end of the hop. -/
lemma hopEnd_mem_allTrackOf {p : Plane × Plane} (hp : p ∈ X ×ˢ X)
    (hu : s(p.1, p.2) ∈ unitEdges X) :
    s((hopEnd X p).1, (hopEnd X p).2) ∈ allTrackOf X s(p.1, p.2) := by
  obtain ⟨m, hm, hmv, -⟩ := exists_hopLen hp
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · rw [← hm]
    exact mem_allTrackOf_self hu
  · have h1 := iterate_mem_trackOf hmv m le_rfl hpos
    have h0 : s(p.1, p.2) ∈ rhombusEdges X := (stepL_spec (hmv 0 hpos)).rhombusEdge
    rw [hm] at h1
    rw [allTrackOf_of_mem_rhombusEdges h0]
    exact h1

/-- The track of the far end of a hop is the track of its exit edge. -/
lemma allTrackOf_hopEnd {p : Plane × Plane} (hp : p ∈ X ×ˢ X)
    (hu : s(p.1, p.2) ∈ unitEdges X) :
    allTrackOf X s((hopEnd X p).1, (hopEnd X p).2) = allTrackOf X s(p.1, p.2) :=
  (eq_allTrackOf_of_mem (allTrackOf_mem_allTracks hu) (hopEnd_mem_allTrackOf hp hu)).symm

end

/-- **The other end of the track through a port of an exceptional face.**  Let `(a, b)` be an
oriented side of the exceptional face `F` and `x = (b, a)` its reversal.  The other end of the track
through `s(b, a)` is at the far end `h` of the hop from `x`: either at the exceptional face `G` on
the left of `h`, or (when the token from `x` goes to a cap) at a hull side `P`, which is either the
unit hull side `(h.2, h.1)` or a non-unit hull side. -/
theorem otherEnd_cases :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ F ∈ exceptionalFaces X, ∀ a b : Plane, (toC a, toC b) ∈ orientedSides X F →
        (∃ G ∈ exceptionalFaces X,
          (toC (hopEnd X (b, a)).1, toC (hopEnd X (b, a)).2) ∈ orientedSides X G ∧
          otherEnd X (F, s(b, a)) =
            (Sum.inl G, s((hopEnd X (b, a)).1, (hopEnd X (b, a)).2))) ∨
        (hopDest X (b, a) = .cap ∧ ∃ P, otherEnd X (F, s(b, a)) =
            (Sum.inr P, s((hopEnd X (b, a)).1, (hopEnd X (b, a)).2)) ∧
          ((P = ((hopEnd X (b, a)).2, (hopEnd X (b, a)).1) ∧ P ∈ unitHullSides X) ∨
            (P ∈ ccwHullSides X ∧ 1 < dist P.1 P.2))) := by
  filter_upwards [card_trackEnds, far_end_cases] with n hends hfar hfm X hX htri F hF a b hab
  have hsep := hX.1.2
  have he : s(b, a) ∈ unitEdges X := mem_unitEdges_of_mem_orientedSides hab
  have hmap : Sym2.map toC s(b, a) = s(toC a, toC b) := by rw [Sym2.map_mk]; exact Sym2.eq_swap
  have hdab : dist a b = 1 := dist_eq_one_of_mem_orientedSides hab
  have hm2 := mem_of_mem_orientedSides hab
  set p : Plane × Plane := (b, a) with hpdef
  have hp : p ∈ X ×ˢ X := Finset.mem_product.2 ⟨hm2.2, hm2.1⟩
  have hpd : dist p.1 p.2 = 1 := by rw [dist_comm]; exact hdab
  have hFf : F ∈ exceptionalFinset X := (mem_exceptionalFinset hsep).2 hF
  have hpF : IsPort X (Sum.inl F) s(b, a) := ⟨hF, hmap ▸ (Finset.mem_filter.1 hab).2.1⟩
  obtain ⟨hTe, -⟩ := trackEnds_eq_otherEnd (hends hfm X hX htri) hFf he hpF
  set h := hopEnd X p with hhdef
  have hsub : h.2 - h.1 = a - b := hopEnd_sub p
  have hmemT : s(h.1, h.2) ∈ allTrackOf X s(b, a) := hopEnd_mem_allTrackOf hp he
  have hunitT : s(h.1, h.2) ∈ unitEdges X := (Finset.mem_filter.1 hmemT).1
  have hother : ∀ N, (N, s(h.1, h.2)) ∈ trackEnds X (allTrackOf X s(b, a)) →
      (N, s(h.1, h.2)) ≠ (Sum.inl F, s(b, a)) → otherEnd X (F, s(b, a)) = (N, s(h.1, h.2)) := by
    intro N hN hne
    rw [hTe, Finset.mem_insert, Finset.mem_singleton] at hN
    rcases hN with h' | h'
    · exact absurd h' hne
    · exact h'.symm
  by_cases hd : ∃ G ∈ exceptionalFaces X, (toC h.1, toC h.2) ∈ orientedSides X G
  · left
    obtain ⟨G, hG, hGs⟩ := hd
    have hGf : G ∈ exceptionalFinset X := (mem_exceptionalFinset hsep).2 hG
    have hend : (Sum.inl G, s(h.1, h.2)) ∈ trackEnds X (allTrackOf X s(b, a)) :=
      mem_trackEnds.2 ⟨Finset.mem_union_left _ (Finset.mem_map_of_mem _ hGf), hmemT,
        hG, (Finset.mem_filter.1 hGs).2.1⟩
    have hne : (Sum.inl G, s(h.1, h.2)) ≠ ((Sum.inl F, s(b, a)) : PortNode × Sym2 Plane) := by
      intro heq
      simp only [Prod.mk.injEq, Sum.inl.injEq] at heq
      obtain ⟨rfl, he2⟩ := heq
      have hs : s((toC h.1, toC h.2).1, (toC h.1, toC h.2).2) =
          s(((toC a, toC b) : ℂ × ℂ).1, ((toC a, toC b) : ℂ × ℂ).2) := by
        have h3 := congrArg (Sym2.map toC) he2
        rw [Sym2.map_mk] at h3
        exact h3.trans hmap
      have := orientedSides_injOn (nonempty_of_mem_exceptionalFaces hG) hGs hab hs
      simp only [Prod.mk.injEq] at this
      have e1 := toC.injective this.1
      have e2 := toC.injective this.2
      rw [e1, e2] at hsub
      have : a = b := by
        have h2 : (2 : ℝ) • (a - b) = 0 := by
          rw [two_smul]; nth_rewrite 1 [← hsub]; abel
        have := (smul_eq_zero.1 h2).resolve_left (by norm_num)
        exact sub_eq_zero.1 this
      rw [this, dist_self] at hdab; norm_num at hdab
    exact ⟨G, hG, hGs, hother _ hend hne⟩
  · right
    have hcap : hopDest X p = .cap := by rw [hopDest, dif_neg hd]
    refine ⟨hcap, ?_⟩
    have hcases := hfar hfm X hX htri p hp hpd hcap
    have key : ∀ P ∈ ccwHullSides X, IsPort X (Sum.inr P) s(h.1, h.2) →
        otherEnd X (F, s(b, a)) = (Sum.inr P, s(h.1, h.2)) := by
      intro P hP hport
      have hend : (Sum.inr P, s(h.1, h.2)) ∈ trackEnds X (allTrackOf X s(b, a)) :=
        mem_trackEnds.2 ⟨Finset.mem_union_right _ (Finset.mem_map_of_mem _ hP), hmemT, hport⟩
      exact hother _ hend (by simp)
    rcases hcases with hu | ⟨P, hP, hPd, Fc, hc, hbd, -⟩
    · have hP := (Finset.mem_filter.1 hu).1
      refine ⟨_, key _ hP ⟨hP, hunitT, ?_⟩, Or.inl ⟨rfl, hu⟩⟩
      rw [if_pos (Finset.mem_filter.1 hu).2]
      exact Sym2.eq_swap
    · exact ⟨P, key P hP ⟨hP, hunitT, by rw [if_neg hPd.ne']; exact ⟨Fc, hc, hbd⟩⟩,
        Or.inr ⟨hP, hPd⟩⟩

end Erdos99

end

end SaturationHop

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `CaplessGeometry`
-/

section CaplessGeometry

/-!
# Capless components: the closure relation of a set of faces (Verification Guide §13.4)

* `portVec X (F, e)`: the counterclockwise side vector of the face `F` along its edge `e`;
* `portVec_mate`: the two ends of a matched short track carry opposite side vectors;
* `markedSum_eq_sum_portVec`: a marked sum is the sum of the side vectors of its ports;
* `set_closure`: for a set `S` of good faces all of whose unmarked short ports are matched, the
  internal ports cancel and `‖Σ_{F ∈ S} (k_F τ_F + Z_F) + Σ_{outgoing ports} p‖ ≤ |S| tol`.
-/

open scoped BigOperators Real
open Filter

@[expose] public noncomputable section

open Classical

namespace Erdos99

open LocalCharge

/-- The counterclockwise side vector of the face `q.1` along the edge `q.2` (zero if `q.2` is not a
side of `q.1`). -/
def portVec (X : Finset Plane) (q : Set ℂ × Sym2 Plane) : ℂ :=
  if h : ∃ ab ∈ orientedSides X q.1, Sym2.map toC q.2 = s(ab.1, ab.2) then
    h.choose.2 - h.choose.1 else 0

lemma portVec_eq {X : Finset Plane} {q : Set ℂ × Sym2 Plane} (hne : q.1.Nonempty)
    {ab : ℂ × ℂ} (hab : ab ∈ orientedSides X q.1) (h : Sym2.map toC q.2 = s(ab.1, ab.2)) :
    portVec X q = ab.2 - ab.1 := by
  have hex : ∃ ab ∈ orientedSides X q.1, Sym2.map toC q.2 = s(ab.1, ab.2) := ⟨ab, hab, h⟩
  rw [portVec, dif_pos hex]
  have hc := hex.choose_spec
  have : hex.choose = ab := orientedSides_injOn hne hc.1 hab (hc.2.symm.trans h)
  rw [this]

/-- A port of an exceptional face is a side of it. -/
lemma exists_side_of_port :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ∀ F : Set ℂ, ∀ e : Sym2 Plane,
      IsPort X (Sum.inl F) e → ∃ ab ∈ orientedSides X F, Sym2.map toC e = s(ab.1, ab.2) := by
  filter_upwards [image_orientedSides_eq] with n himg hfm X hX F e hp
  have hb := hp.2
  rw [← himg hfm X hX F hp.1] at hb
  obtain ⟨ab, hab, habe⟩ := Finset.mem_image.1 hb
  exact ⟨ab, hab, habe.symm⟩

/-- **The two ends of a matched short track carry opposite side vectors.** -/
lemma portVec_mate :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ (L : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane)),
      ∀ q ∈ unmarkedPorts X L G mk, TrackMated X L G mk q →
        portVec X (trackMate X q) = -portVec X q := by
  filter_upwards [trackMate_side, exists_side_of_port] with n hmate hside hfm X hX htri L G mk q hq
    hmated
  obtain ⟨F, e⟩ := q
  obtain ⟨hFg, hsp, -⟩ := mem_unmarkedPorts.1 hq
  obtain ⟨he, hpF, -⟩ := Finset.mem_filter.1 hsp
  obtain ⟨ab, hab, habe⟩ := hside hfm X hX F e hpF
  obtain ⟨ab', hab', hmap', hvec, -⟩ := hmate hfm X hX htri F hpF.1 e he ab hab habe hmated.1
  obtain ⟨hFg', -, -⟩ := mem_unmarkedPorts.1 hmated.2
  have hne' : (trackMate X (F, e)).1.Nonempty :=
    nonempty_of_mem_exceptionalFaces ((mem_exceptionalFinset hX.1.2).1 (G.good_subset hFg'))
  have hne : F.Nonempty := nonempty_of_mem_exceptionalFaces hpF.1
  rw [portVec_eq hne' hab' hmap', portVec_eq (q := (F, e)) hne hab habe, hvec]

/-- **A marked sum is the sum of the side vectors of its ports.** -/
lemma markedSum_eq_sum_portVec :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ∀ F ∈ exceptionalFaces X,
      ∀ S : Finset (Sym2 Plane), (∀ e ∈ S, IsPort X (Sum.inl F) e) →
        markedSum X F S = ∑ e ∈ S, portVec X (F, e) := by
  filter_upwards [exists_side_of_port] with n hside hfm X hX F hF S hS
  have hne : F.Nonempty := nonempty_of_mem_exceptionalFaces hF
  rw [markedSum]
  symm
  refine Finset.sum_bij' (fun e he => (hside hfm X hX F e (hS e he)).choose)
    (fun ab hab => (Finset.mem_filter.1 hab).2.choose) ?_ ?_ ?_ ?_ ?_
  · intro e he
    have hc := (hside hfm X hX F e (hS e he)).choose_spec
    exact Finset.mem_filter.2 ⟨hc.1, e, he, hc.2⟩
  · intro ab hab
    exact (Finset.mem_filter.1 hab).2.choose_spec.1
  · intro e he
    have hc := (hside hfm X hX F e (hS e he)).choose_spec
    have hm : (hside hfm X hX F e (hS e he)).choose ∈ (orientedSides X F).filter
        (fun ab => ∃ e ∈ S, Sym2.map toC e = s(ab.1, ab.2)) :=
      Finset.mem_filter.2 ⟨hc.1, e, he, hc.2⟩
    have hc' := (Finset.mem_filter.1 hm).2.choose_spec
    exact Sym2.map.injective toC.injective (hc'.2.trans hc.2.symm)
  · intro ab hab
    have hc' := (Finset.mem_filter.1 hab).2.choose_spec
    have hc := (hside hfm X hX F _ (hS _ hc'.1)).choose_spec
    exact orientedSides_injOn hne hc.1 (Finset.mem_filter.1 hab).1 (hc.2.symm.trans hc'.2)
  · intro e he
    have hc := (hside hfm X hX F e (hS e he)).choose_spec
    exact portVec_eq (q := (F, e)) hne hc.1 hc.2

/-- The face equation `‖k τ + Σ_{unmarked short ports} p + Z‖ ≤ tol` at a labelled good face. -/
lemma face_closure_portVec :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      ∀ (L tol : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane))
        (lab : Set ℂ → Plane × Plane), IsMarking X L G mk → LabelledBy X tol G mk lab →
      ∀ F ∈ G.good, ‖(G.kMult F : ℂ) * labDir lab F +
        ∑ e ∈ shortPorts X L F \ mk F, portVec X (F, e) + longSum X L F‖ ≤ tol := by
  filter_upwards [markedSum_short_add_longSum, markedSum_eq_sum_portVec] with n hzero hsum hfm X hX
    L tol G mk lab hmk hlab F hFg
  have hFe : F ∈ exceptionalFaces X := (mem_exceptionalFinset hX.1.2).1 (G.good_subset hFg)
  have hsub := (hmk F hFg).1
  have h0 := hzero hfm X hX L F hFe
  rw [← Finset.union_sdiff_of_subset hsub, markedSum_union Finset.disjoint_sdiff,
    hsum hfm X hX F hFe (shortPorts X L F \ mk F)
      (fun e he => (Finset.mem_filter.1 (Finset.sdiff_subset he)).2.1)] at h0
  have hl := (hlab.2 F hFg).2.1
  rw [GoodFaces.markMult_eq] at hl
  calc _ = ‖-(markedSum X F (mk F) - (G.kMult F : ℂ) * toC (sideDir (lab F)))‖ := by
        congr 1; rw [labDir]; linear_combination h0
    _ ≤ tol := by rw [norm_neg]; exact hl

/-- **The closure relation of a set of faces** (Verification Guide §13.4): if every unmarked short
port of a face of `S` is matched, the internal ports cancel and
`‖Σ_{F ∈ S} (k_F τ_F + Z_F) + Σ_{outgoing ports} p‖ ≤ |S| tol`. -/
theorem set_closure :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ (L tol : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane))
        (lab : Set ℂ → Plane × Plane), IsMarking X L G mk → LabelledBy X tol G mk lab →
      ∀ S ⊆ G.good, (∀ q ∈ unmarkedPorts X L G mk, q.1 ∈ S → TrackMated X L G mk q) →
        ‖∑ F ∈ S, ((G.kMult F : ℂ) * labDir lab F + longSum X L F) +
          ∑ q ∈ (unmarkedPorts X L G mk).filter (fun q => q.1 ∈ S ∧ (trackMate X q).1 ∉ S),
            portVec X q‖ ≤ S.card * tol := by
  filter_upwards [face_closure_portVec, portVec_mate, card_trackEnds] with n hface hmate hends hfm X
    hX htri L tol G mk lab hmk hlab S hS hmat
  set P := unmarkedPorts X L G mk with hP
  set PS := P.filter (fun q => q.1 ∈ S) with hPS
  have hM := trackMate_isMatching (hends hfm X hX htri) L G mk
  -- the sum over the half-edges at `S`, face by face
  have hfib : ∑ q ∈ PS, portVec X q = ∑ F ∈ S, ∑ e ∈ shortPorts X L F \ mk F, portVec X (F, e) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := Prod.fst) (t := S)
      (fun q hq => (Finset.mem_filter.1 hq).2)]
    refine Finset.sum_congr rfl fun F hF => ?_
    refine Finset.sum_nbij' Prod.snd (fun e => (F, e)) ?_ ?_ ?_ ?_ ?_
    · intro q hq
      obtain ⟨hq1, rfl⟩ := Finset.mem_filter.1 hq
      obtain ⟨-, h2, h3⟩ := mem_unmarkedPorts.1 (Finset.mem_filter.1 hq1).1
      exact Finset.mem_sdiff.2 ⟨h2, h3⟩
    · intro e he
      obtain ⟨h2, h3⟩ := Finset.mem_sdiff.1 he
      exact Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨mem_unmarkedPorts.2 ⟨hS hF, h2, h3⟩, hF⟩, rfl⟩
    · intro q hq
      obtain ⟨-, rfl⟩ := Finset.mem_filter.1 hq
      rfl
    · intro e _; rfl
    · intro q hq
      obtain ⟨-, rfl⟩ := Finset.mem_filter.1 hq
      rfl
  -- the internal half-edges cancel
  have hint : ∑ q ∈ PS.filter (fun q => ¬ (trackMate X q).1 ∉ S), portVec X q = 0 := by
    refine Finset.sum_involution (fun q _ => trackMate X q) ?_ ?_ ?_ ?_
    · intro q hq
      obtain ⟨hq1, -⟩ := Finset.mem_filter.1 hq
      obtain ⟨hqP, hqS⟩ := Finset.mem_filter.1 hq1
      rw [hmate hfm X hX htri L G mk q hqP (hmat q hqP hqS)]
      ring
    · intro q hq _
      obtain ⟨hq1, -⟩ := Finset.mem_filter.1 hq
      obtain ⟨hqP, hqS⟩ := Finset.mem_filter.1 hq1
      exact (hM q hqP (hmat q hqP hqS)).2.1
    · intro q hq
      obtain ⟨hq1, hin⟩ := Finset.mem_filter.1 hq
      obtain ⟨hqP, hqS⟩ := Finset.mem_filter.1 hq1
      obtain ⟨h1, -, h3, -⟩ := hM q hqP (hmat q hqP hqS)
      refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨h1, not_not.1 hin⟩, ?_⟩
      rw [h3]; exact not_not.2 hqS
    · intro q hq
      obtain ⟨hq1, -⟩ := Finset.mem_filter.1 hq
      obtain ⟨hqP, hqS⟩ := Finset.mem_filter.1 hq1
      exact (hM q hqP (hmat q hqP hqS)).2.2.1
  have hsplit := Finset.sum_filter_add_sum_filter_not PS (fun q => (trackMate X q).1 ∉ S)
    (portVec X)
  rw [hint, add_zero] at hsplit
  have hext : PS.filter (fun q => (trackMate X q).1 ∉ S) =
      P.filter (fun q => q.1 ∈ S ∧ (trackMate X q).1 ∉ S) := by
    rw [hPS, Finset.filter_filter]
  rw [← hext, hsplit, hfib, ← Finset.sum_add_distrib]
  calc _ = ‖∑ F ∈ S, ((G.kMult F : ℂ) * labDir lab F +
        ∑ e ∈ shortPorts X L F \ mk F, portVec X (F, e) + longSum X L F)‖ := by
        congr 1; refine Finset.sum_congr rfl fun F _ => ?_; ring
    _ ≤ ∑ F ∈ S, ‖(G.kMult F : ℂ) * labDir lab F +
        ∑ e ∈ shortPorts X L F \ mk F, portVec X (F, e) + longSum X L F‖ := norm_sum_le _ _
    _ ≤ ∑ _F ∈ S, tol := Finset.sum_le_sum fun F hF => hface hfm X hX L tol G mk lab hmk hlab F (hS hF)
    _ = S.card * tol := by rw [Finset.sum_const, nsmul_eq_mul]

end Erdos99
end

end CaplessGeometry

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `SaturationProcess`
-/

section SaturationProcess

/-!
# The saturated token process: good faces, marks and labels (Verification Guide §10)

The track-following token process `hopProcess` with the exit edges `hopEmit` is stopped after a
round `m + 1`; the discarded tokens are `hopBad hX K`.  Writing `A F` for the tokens arriving at
`F` by the end of round `m + 1`, a face is *clean* if none of them is discarded, and

* an ordinary good pentagon is a clean pentagon with one arrival,
* a good hexagon is a clean hexagon with two arrivals,
* a good activated pentagon is a clean pentagon with two arrivals that has emitted a token which is
  not discarded.

The marked ports of a good face are the entry edges of its arrivals, and its exit edge if it has
emitted (`Sat.mk`); its label is the source label of a retained arrival (`Sat.lab`).

This file proves the combinatorial properties:
* `Sat.lab_injOn`: the labels are injective (labels never split);
* `Sat.stubs_unit_empty`, `Sat.stubs_marked_empty`: no unmarked port of a good face has its track
  ending at a unit hull side or at a marked port of a good face.
-/

open scoped BigOperators Real
open Filter Topology

@[expose] public noncomputable section

open Classical

namespace Erdos99

namespace Sat

open Propagation

variable {X : Finset Plane} (hX : IsSeparated X) (K m : ℕ)

/-- The track-following process with the exit edges `hopEmit`. -/
abbrev proc : TokenProcess X := hopProcess hX (hopEmit X)

/-- A face is clean if no token arriving at it by the end of round `m + 1` is discarded. -/
def Clean (F : Set ℂ) : Prop := ∀ t ∈ (proc hX).arrivals m F, ¬ hopBad hX K t

/-- The saturated good faces. -/
def faces : GoodFaces X where
  pent := (exceptionalFinset X).filter (fun F => faceSize X F = 5 ∧ Clean hX K m F ∧
    ((proc hX).arrivals m F).card = 1)
  hex := (exceptionalFinset X).filter (fun F => faceSize X F = 6 ∧ Clean hX K m F ∧
    ((proc hX).arrivals m F).card = 2)
  act := (exceptionalFinset X).filter (fun F => faceSize X F = 5 ∧ Clean hX K m F ∧
    ((proc hX).arrivals m F).card = 2 ∧ (proc hX).Emits m F ∧ ¬ hopBad hX K (Sum.inr F))
  pent_sub F hF := ⟨(Finset.mem_filter.1 hF).1, (Finset.mem_filter.1 hF).2.1⟩
  hex_sub F hF := ⟨(Finset.mem_filter.1 hF).1, (Finset.mem_filter.1 hF).2.1⟩
  act_sub F hF := ⟨(Finset.mem_filter.1 hF).1, (Finset.mem_filter.1 hF).2.1⟩
  disj := by
    rw [Finset.disjoint_left]
    intro F h1 h2
    have a := (Finset.mem_filter.1 h1).2.2.2
    have b := (Finset.mem_filter.1 h2).2.2.2.1
    omega

/-- The entry edge of a token leaving through `x`: the far end of its track. -/
def entry (X : Finset Plane) (x : Plane × Plane) : Sym2 Plane :=
  s((hopEnd X x).1, (hopEnd X x).2)

/-- The marked ports of a face: the entry edges of its arrivals, and its exit edge if it has
emitted. -/
def mk (F : Set ℂ) : Finset (Sym2 Plane) :=
  ((proc hX).arrivals m F).image (fun t => entry X (exitEdge (hopEmit X) t)) ∪
    (if (proc hX).Emits m F then {s((hopEmit X F).1, (hopEmit X F).2)} else ∅)

/-- The retained arrival of a face: an arrival other than the parent if the face has emitted. -/
def ret (F : Set ℂ) : (Plane × Plane) ⊕ Set ℂ :=
  if (proc hX).Emits m F then
    (if h : (((proc hX).arrivals m F).erase ((proc hX).parent F)).Nonempty then h.choose
      else (proc hX).parent F)
  else (if h : ((proc hX).arrivals m F).Nonempty then h.choose else Sum.inr F)

/-- The label of a face: the source label of its retained arrival. -/
def lab (F : Set ℂ) : Plane × Plane := (proc hX).labelAt K (ret hX m F)

/-! ## Basic facts -/

lemma mem_good {F : Set ℂ} : F ∈ (faces hX K m).good ↔
    F ∈ exceptionalFinset X ∧ Clean hX K m F ∧
      ((faceSize X F = 5 ∧ ((proc hX).arrivals m F).card = 1) ∨
        (faceSize X F = 6 ∧ ((proc hX).arrivals m F).card = 2) ∨
        (faceSize X F = 5 ∧ ((proc hX).arrivals m F).card = 2 ∧ (proc hX).Emits m F ∧
          ¬ hopBad hX K (Sum.inr F))) := by
  simp only [GoodFaces.good, faces, Finset.mem_union, Finset.mem_filter]
  tauto

lemma mem_mk_of_mem_arrivals {F : Set ℂ} {t : (Plane × Plane) ⊕ Set ℂ}
    (ht : t ∈ (proc hX).arrivals m F) : entry X (exitEdge (hopEmit X) t) ∈ mk hX m F :=
  Finset.mem_union_left _ (Finset.mem_image_of_mem _ ht)

lemma mem_mk_of_emits {F : Set ℂ} (h : (proc hX).Emits m F) :
    s((hopEmit X F).1, (hopEmit X F).2) ∈ mk hX m F :=
  Finset.mem_union_right _ (by rw [if_pos h]; exact Finset.mem_singleton_self _)

/-- A good face that has emitted is an activated pentagon. -/
lemma act_of_emits {F : Set ℂ} (hF : F ∈ (faces hX K m).good) (h : (proc hX).Emits m F) :
    F ∈ (faces hX K m).act := by
  obtain ⟨hFe, hcl, h1 | h2 | h3⟩ := (mem_good hX K m).1 hF
  · exfalso
    have a := (proc hX).two_le_faceArr_of_emits h
    have b := (proc hX).faceArr_mono m F
    rw [(proc hX).faceArr_succ_eq_card, h1.2] at b
    omega
  · exfalso
    have := (proc hX).faceSize_of_emits h
    omega
  · exact Finset.mem_filter.2 ⟨hFe, h3.1, hcl, h3.2⟩

/-- The parent of an emitting face arrives by its round of emission. -/
lemma parent_mem_arrivals {F : Set ℂ} (h : (proc hX).Emits m F) :
    (proc hX).parent F ∈ (proc hX).arrivals m F := by
  have hp := (proc hX).parent_mem h
  obtain ⟨-, hle, -⟩ := (proc hX).firstEmit_spec h
  exact (proc hX).arrivals_mono (by omega) F hp

/-- The retained arrival of a good face arrives at it, and differs from the parent if the face has
emitted. -/
lemma ret_spec {F : Set ℂ} (hF : F ∈ (faces hX K m).good) :
    ret hX m F ∈ (proc hX).arrivals m F ∧
      ((proc hX).Emits m F → ret hX m F ≠ (proc hX).parent F) := by
  by_cases h : (proc hX).Emits m F
  · have hact := act_of_emits hX K m hF h
    have hc := (Finset.mem_filter.1 hact).2.2.2.1
    have hpar := parent_mem_arrivals hX m h
    have hne : (((proc hX).arrivals m F).erase ((proc hX).parent F)).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hpar, hc]; norm_num
    have e : ret hX m F = hne.choose := by rw [ret, if_pos h, dif_pos hne]
    rw [e]
    have := hne.choose_spec
    exact ⟨Finset.mem_of_mem_erase this, fun _ => Finset.ne_of_mem_erase this⟩
  · have hne : ((proc hX).arrivals m F).Nonempty := by
      obtain ⟨-, -, h1 | h2 | h3⟩ := (mem_good hX K m).1 hF
      · rw [← Finset.card_pos, h1.2]; norm_num
      · rw [← Finset.card_pos, h2.2]; norm_num
      · exact absurd h3.2.2.1 h
    have e : ret hX m F = hne.choose := by rw [ret, if_neg h, dif_pos hne]
    rw [e]
    exact ⟨hne.choose_spec, fun h' => absurd h' h⟩

/-! ## Labels never split -/

/-- **The labels of the good faces are injective.** -/
theorem lab_injOn (hmK : m ≤ K) : Set.InjOn (lab hX K m) ((faces hX K m).good : Set (Set ℂ)) := by
  set P := proc hX
  -- a descendant of a retained arrival is the arrival itself, or emitted after its face
  have key : ∀ F ∈ (faces hX K m).good, ∀ F' : Set ℂ, ∀ t', t' ∈ P.arrivals m F' →
      P.Desc (ret hX m F) t' → ret hX m F = t' := by
    intro F hF F' t' ht' hd
    obtain ⟨hr, hne⟩ := ret_spec hX K m hF
    rcases Relation.ReflTransGen.cases_head hd with h | ⟨c, ⟨G, rfl, ⟨i, hG⟩, hpar⟩, hct'⟩
    · exact h
    · exfalso
      -- the first step: `G` is the face of the retained arrival
      have hGF : G = F := P.face_eq_of_mem_arrivals (hpar ▸ P.parent_mem hG) hr
      subst hGF
      -- `t'` is timed by round `m`, so `G` has emitted by round `m`
      have hEm : P.Emits m G := by
        rcases t' with p | G'
        · exact absurd (P.desc_inl hct') (by simp)
        · have hG' : P.Emits m G' := (P.mem_arrivals_inr.1 ht').2.2
          by_cases hGG : (Sum.inr G : (Plane × Plane) ⊕ Set ℂ) = Sum.inr G'
          · cases hGG; exact hG'
          · have hlt := P.firstEmit_lt_of_desc hct' rfl rfl hGG
            obtain ⟨h1, -⟩ := P.firstEmit_spec hG
            obtain ⟨-, h2, -⟩ := P.firstEmit_spec hG'
            exact P.emits_mono (by omega) h1
      exact hne hEm hpar.symm
  intro F hF F' hF' he
  have hF0 := (ret_spec hX K m hF).1
  have hF0' := (ret_spec hX K m hF').1
  rcases P.labelAt_chain K _ _ (P.timed_mono hmK (P.timed_of_mem_arrivals hF0))
    (P.timed_mono hmK (P.timed_of_mem_arrivals hF0')) he with h | h
  · exact P.face_eq_of_mem_arrivals hF0 ((key F hF F' _ hF0' h) ▸ hF0')
  · exact (P.face_eq_of_mem_arrivals hF0' ((key F' hF' F _ hF0 h) ▸ hF0)).symm

/-! ## The exit edges of arriving tokens -/

variable {hX}

/-- The receiver of a token is the receiver of the hop from its exit edge. -/
lemma dest_eq_hopDest (t : (Plane × Plane) ⊕ Set ℂ) :
    (proc hX).dest t = hopDest X (exitEdge (hopEmit X) t) := by
  rcases t with p | G <;> rfl

/-- The facts about the exit edge of an arriving token. -/
lemma exit_facts (htri : ¬ HasUnitTriangle X)
    (hsides : ∀ G ∈ exceptionalFaces X, (orientedSides X G).Nonempty) {j : ℕ} {F : Set ℂ}
    {t : (Plane × Plane) ⊕ Set ℂ} (ht : t ∈ (proc hX).arrivals j F) :
    exitEdge (hopEmit X) t ∈ X ×ˢ X ∧ Initial X (exitEdge (hopEmit X) t) ∧
      s((exitEdge (hopEmit X) t).1, (exitEdge (hopEmit X) t).2) ∈ unitEdges X ∧
      hopDest X (exitEdge (hopEmit X) t) = .face F ∧
      (toC (hopEnd X (exitEdge (hopEmit X) t)).1, toC (hopEnd X (exitEdge (hopEmit X) t)).2) ∈
        orientedSides X F := by
  have hd : hopDest X (exitEdge (hopEmit X) t) = .face F := by
    rw [← dest_eq_hopDest]; exact (proc hX).dest_of_mem_arrivals ht
  obtain ⟨h1, h2⟩ := hop_arrivals_mem hX ht
  rcases t with p | G
  · have hp := h1 p rfl
    have hpX : p ∈ X ×ˢ X := (Finset.mem_filter.1 (Finset.mem_filter.1 hp).1).1
    refine ⟨hpX, initial_of_mem_unitHullSides hp, ?_, hd, hopDest_face hd⟩
    rw [mem_unitEdges]
    exact ⟨(Finset.mem_product.1 hpX).1, (Finset.mem_product.1 hpX).2, (Finset.mem_filter.1 hp).2⟩
  · have hG := h2 G rfl
    have hm := hopEmit_mem' hsides G hG
    have hX2 := mem_of_mem_orientedSides hm
    refine ⟨Finset.mem_product.2 ⟨hX2.2, hX2.1⟩, initial_of_mem_orientedSides hX htri hG hm, ?_,
      hd, hopDest_face hd⟩
    have := mem_unitEdges_of_mem_orientedSides hm
    exact this

/-! ## No stubs at unit hull sides or marked ports -/

/-- **No stub ends at a unit hull side**: if the track of an unmarked port of a good face ended at
a unit hull side, the source on that side would arrive at the face through this port. -/
theorem stubs_unit_empty :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, ∀ hX : IsOptimal n X, ¬ HasUnitTriangle X →
      (∀ G ∈ exceptionalFaces X, (orientedSides X G).Nonempty) → ∀ (K m : ℕ) (L : ℝ),
      stubsTo X L (faces hX.1.2 K m) (mk hX.1.2 m) (faces hX.1.2 K m).good (UnitEnd X) = ∅ := by
  filter_upwards [otherEnd_cases, exists_side_of_port, two_le_returnLength] with
    n hcases hside hret hfm X hX htri hsides K m L
  have hsep := hX.1.2
  rw [Finset.eq_empty_iff_forall_notMem]
  rintro ⟨F, e⟩ hq
  simp only [stubsTo, stubsAt, Finset.mem_filter] at hq
  obtain ⟨⟨hun, -, hFg⟩, ⟨P, hP, hPr⟩⟩ := hq
  obtain ⟨-, hsh, hnm⟩ := mem_unmarkedPorts.1 hun
  have hport := (Finset.mem_filter.1 hsh).2.1
  have hF : F ∈ exceptionalFaces X := hport.1
  obtain ⟨ab, hab, hmap⟩ := hside hfm X hX F e hport
  obtain ⟨A, B⟩ := ab
  have hAB := Finset.mem_product.1 (Finset.mem_filter.1 hab).1
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hAB.1
  obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hAB.2
  have hee : e = s(b, a) := by
    have : Sym2.map toC e = Sym2.map toC s(b, a) := by rw [hmap, Sym2.map_mk]; exact Sym2.eq_swap
    exact Sym2.map.injective toC.injective this
  subst hee
  rcases hcases hfm X hX htri F hF a b hab with ⟨G, -, -, hG⟩ | ⟨-, P', hP', hcase⟩
  · rw [hG] at hP; cases hP
  · rw [hP'] at hP
    simp only [Sum.inr.injEq] at hP
    subst hP
    rcases hcase with ⟨rfl, hu⟩ | ⟨hccw, hd⟩
    · -- the source `P` arrives at `F` through `s(b, a)`
      have hm2 := mem_of_mem_orientedSides hab
      have hbaX : ((b, a) : Plane × Plane) ∈ X ×ˢ X := Finset.mem_product.2 ⟨hm2.2, hm2.1⟩
      have hsw := hopEnd_swap hsep htri hbaX (initial_of_mem_orientedSides hsep htri hF hab)
      set P := ((hopEnd X (b, a)).2, (hopEnd X (b, a)).1)
      have hdest : hopDest X P = .face F := hopDest_eq_face hsep hF (by rw [hsw]; exact hab)
      have harr : (Sum.inl P : (Plane × Plane) ⊕ Set ℂ) ∈ (proc hsep).arrivals m F :=
        (proc hsep).mem_arrivals_inl.2 ⟨hu, hdest⟩
      apply hnm
      have := mem_mk_of_mem_arrivals hsep m harr
      simp only [exitEdge, Sum.elim_inl, id, entry] at this
      rw [hsw] at this
      simpa [Sym2.eq_swap] using this
    · exact absurd (hret hfm X hX _ hccw hd.ne') (by omega)

/-- **No stub ends at a marked port of a good face**: a marked port is the entry or exit edge of a
token, and the token would have passed through the unmarked port as well. -/
theorem stubs_marked_empty :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, ∀ hX : IsOptimal n X, ¬ HasUnitTriangle X →
      (∀ G ∈ exceptionalFaces X, (orientedSides X G).Nonempty) → ∀ (K m : ℕ) (L : ℝ),
      stubsTo X L (faces hX.1.2 K m) (mk hX.1.2 m) (faces hX.1.2 K m).good
        (MarkedEnd (faces hX.1.2 K m) (mk hX.1.2 m)) = ∅ := by
  filter_upwards [otherEnd_cases, exists_side_of_port] with
    n hcases hside hfm X hX htri hsides K m L
  have hsep := hX.1.2
  rw [Finset.eq_empty_iff_forall_notMem]
  rintro ⟨F, e⟩ hq
  simp only [stubsTo, stubsAt, Finset.mem_filter] at hq
  obtain ⟨⟨hun, -, hFg⟩, ⟨F', hF'1, hF'g, hF'm⟩⟩ := hq
  obtain ⟨-, hsh, hnm⟩ := mem_unmarkedPorts.1 hun
  have hport := (Finset.mem_filter.1 hsh).2.1
  have hF : F ∈ exceptionalFaces X := hport.1
  obtain ⟨ab, hab, hmap⟩ := hside hfm X hX F e hport
  obtain ⟨A, B⟩ := ab
  have hAB := Finset.mem_product.1 (Finset.mem_filter.1 hab).1
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hAB.1
  obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hAB.2
  have hee : e = s(b, a) := by
    have : Sym2.map toC e = Sym2.map toC s(b, a) := by rw [hmap, Sym2.map_mk]; exact Sym2.eq_swap
    exact Sym2.map.injective toC.injective this
  subst hee
  have hm2 := mem_of_mem_orientedSides hab
  have hbaX : ((b, a) : Plane × Plane) ∈ X ×ˢ X := Finset.mem_product.2 ⟨hm2.2, hm2.1⟩
  have hinit : Initial X (b, a) := initial_of_mem_orientedSides hsep htri hF hab
  set h := hopEnd X (b, a) with hhdef
  rcases hcases hfm X hX htri F hF a b hab with ⟨G, hG, hGs, hoth⟩ | ⟨-, P', hP', -⟩
  · rw [hoth] at hF'1 hF'm
    simp only [Sum.inl.injEq] at hF'1
    subst hF'1
    simp only [mk, Finset.mem_union, Finset.mem_image] at hF'm
    rcases hF'm with ⟨t, ht, hte⟩ | hem
    · -- the port is the entry edge of an arrival `t` at `G`
      obtain ⟨hxX, hxi, -, -, hxs⟩ := exit_facts htri hsides ht
      have hs : s((toC h.1, toC h.2).1, (toC h.1, toC h.2).2) =
          s((toC (hopEnd X (exitEdge (hopEmit X) t)).1,
            toC (hopEnd X (exitEdge (hopEmit X) t)).2).1,
            (toC (hopEnd X (exitEdge (hopEmit X) t)).1,
            toC (hopEnd X (exitEdge (hopEmit X) t)).2).2) := by
        have h3 := congrArg (Sym2.map toC) hte
        simp only [entry, Sym2.map_mk] at h3
        exact h3.symm
      have heq := orientedSides_injOn (nonempty_of_mem_exceptionalFaces hG) hGs hxs hs
      simp only [Prod.mk.injEq] at heq
      have hend : hopEnd X (b, a) = hopEnd X (exitEdge (hopEmit X) t) :=
        Prod.ext (toC.injective heq.1) (toC.injective heq.2)
      have hx := hopEnd_injOn hsep htri hbaX hxX hinit hxi hend
      obtain ⟨h1, h2⟩ := hop_arrivals_mem hsep ht
      rcases t with p | G'
      · simp only [exitEdge, Sum.elim_inl, id] at hx
        have hp := h1 p rfl
        apply not_mem_orientedSides_of_unitHullSide hsep hF.1 hp
        rw [← hx]; exact hab
      · simp only [exitEdge, Sum.elim_inr] at hx
        have hG' := h2 G' rfl
        have hm := hopEmit_mem' hsides G' hG'
        rw [← hx] at hm
        obtain ⟨-, hb1, hl1⟩ := Finset.mem_filter.1 hm
        obtain ⟨-, hb2, hl2⟩ := Finset.mem_filter.1 hab
        have hGF := face_left_unique hsep (Finset.mem_filter.1 hb1).1 hG'.1.1 hF.1.1 hb1 hb2
          hl1 hl2
        subst hGF
        have hEm : (proc hsep).Emits m G' := ((proc hsep).mem_arrivals_inr.1 ht).2.2
        apply hnm
        have := mem_mk_of_emits hsep m hEm
        rw [← hx] at this
        exact this
    · -- the port is the exit edge of the activated face `G`
      by_cases hEm : (proc hsep).Emits m G
      · rw [if_pos hEm, Finset.mem_singleton] at hem
        have hm := hopEmit_mem' hsides G hG
        have hs : s((toC h.1, toC h.2).1, (toC h.1, toC h.2).2) =
            s(((toC (hopEmit X G).2, toC (hopEmit X G).1) : ℂ × ℂ).1,
              ((toC (hopEmit X G).2, toC (hopEmit X G).1) : ℂ × ℂ).2) := by
          have h3 : s(toC h.1, toC h.2) = s(toC (hopEmit X G).1, toC (hopEmit X G).2) := by
            have := congrArg (Sym2.map toC) hem
            simpa [Sym2.map_pair_eq] using this
          show s(toC h.1, toC h.2) = s(toC (hopEmit X G).2, toC (hopEmit X G).1)
          rw [h3]; exact Sym2.eq_swap
        have heq := orientedSides_injOn (nonempty_of_mem_exceptionalFaces hG) hGs hm hs
        simp only [Prod.mk.injEq] at heq
        have hend : hopEnd X (b, a) = ((hopEmit X G).2, (hopEmit X G).1) :=
          Prod.ext (toC.injective heq.1) (toC.injective heq.2)
        have hsw := hopEnd_swap hsep htri hbaX hinit
        rw [hend] at hsw
        simp only at hsw
        have hdest : hopDest X (hopEmit X G) = .face F := hopDest_eq_face hsep hF (by
          rw [show hopEmit X G = ((hopEmit X G).1, (hopEmit X G).2) from rfl, hsw]; exact hab)
        have harr : (Sum.inr G : (Plane × Plane) ⊕ Set ℂ) ∈ (proc hsep).arrivals m F :=
          (proc hsep).mem_arrivals_inr.2 ⟨(Set.Finite.mem_toFinset _).2 hG, hdest, hEm⟩
        apply hnm
        have := mem_mk_of_mem_arrivals hsep m harr
        simp only [exitEdge, Sum.elim_inr, entry] at this
        rw [show hopEmit X G = ((hopEmit X G).1, (hopEmit X G).2) from rfl, hsw] at this
        simpa [Sym2.eq_swap] using this
      · rw [if_neg hEm] at hem
        exact absurd hem (Finset.notMem_empty _)
  · rw [hP'] at hF'1; cases hF'1

end Sat

end Erdos99

end

end SaturationProcess

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `SaturationCount`
-/

section SaturationCount

/-!
# Counting the omitted faces of the saturated process (Verification Guide §10)

The net absorption capacity of the small exceptional faces is one per pentagon and two per
hexagon, while `u = σ + ρ + Δ` with `Δ ≥ 0`.  Token conservation after round `m + 1` therefore
bounds the unused absorption slots of the clean faces by the discarded tokens, the live frontier,
the high-face incidences and the excess of the cap arrivals over `ρ`.

* `Sat.omitted_count`: the number of omitted pentagons and hexagons is at most
  `3 · #bad + 2 · frontier + Hinc + capArr - ρ`.
-/

open scoped BigOperators Real
open Filter Topology

@[expose] public noncomputable section

open Classical

namespace Erdos99

namespace Sat

open Propagation

variable {X : Finset Plane} (hX : IsSeparated X) (K m : ℕ)

/-- The live frontier after round `m + 1`: the tokens emitted in that round. -/
def frontier : ℝ :=
  ∑ F ∈ (proc hX).fin.toFinset, ((emitted (faceSize X F) ((proc hX).faceArr (m + 1) F) : ℝ) -
    emitted (faceSize X F) ((proc hX).faceArr m F))

lemma exceptionalFinset_eq : exceptionalFinset X = (proc hX).fin.toFinset := by
  rw [exceptionalFinset, dif_pos (exceptionalFaces_finite hX)]

lemma emitted_le_one (k a : ℕ) : emitted k a ≤ 1 := by
  rcases TokenProcess.emitted_eq_zero_or_one k a with h | h <;> omega

lemma frontier_term_nonneg (F : Set ℂ) :
    (0 : ℝ) ≤ (emitted (faceSize X F) ((proc hX).faceArr (m + 1) F) : ℝ) -
      emitted (faceSize X F) ((proc hX).faceArr m F) := by
  have := TokenLedger.emitted_mono (faceSize X F) ((proc hX).faceArr_mono m F)
  have : (emitted (faceSize X F) ((proc hX).faceArr m F) : ℝ) ≤
      emitted (faceSize X F) ((proc hX).faceArr (m + 1) F) := by exact_mod_cast this
  linarith

/-- The net absorption at a pentagon or hexagon is at most its capacity plus its discarded
arrivals, minus one if it is clean and deficient. -/
lemma netAbsorbed_le_aux {k a b : ℕ} (hk : k = 5 ∨ k = 6) (hg : a ≤ 2 + b) (d : Prop)
    [Decidable d] (hd : d → b = 0 ∧ ((k = 5 ∧ a = 0) ∨ (k = 6 ∧ a ≤ 1))) :
    netAbsorbed k a + (if d then 1 else 0) ≤ (k : ℝ) - 4 + b := by
  unfold netAbsorbed
  have hgr : (a : ℝ) ≤ 2 + b := by exact_mod_cast hg
  rcases hk with rfl | rfl
  · by_cases hd' : d
    · obtain ⟨hb, h⟩ := hd hd'
      rcases h with ⟨-, ha⟩ | ⟨h, -⟩
      · subst ha hb; norm_num [hd']
      · omega
    · rw [if_neg hd']
      by_cases h2 : 2 ≤ a
      · rw [if_pos ⟨rfl, h2⟩, if_neg (by omega)]; push_cast; linarith
      · rw [if_neg (by omega), if_neg (by omega)]
        have : (a : ℝ) ≤ 1 := by exact_mod_cast (by omega : a ≤ 1)
        have : (0 : ℝ) ≤ b := Nat.cast_nonneg _
        push_cast; linarith
  · rw [if_neg (by omega), if_neg (by omega)]
    by_cases hd' : d
    · obtain ⟨hb, h⟩ := hd hd'
      rcases h with ⟨h, -⟩ | ⟨-, ha⟩
      · omega
      · subst hb
        rw [if_pos hd']
        have : (a : ℝ) ≤ 1 := by exact_mod_cast ha
        push_cast; linarith
    · rw [if_neg hd']; push_cast; linarith

/-- The arrivals at a face are at most its number of sides. -/
lemma card_arrivals_le (htri : ¬ HasUnitTriangle X)
    (hsides : ∀ G ∈ exceptionalFaces X, (orientedSides X G).Nonempty)
    (hcard : ∀ F ∈ exceptionalFaces X, (orientedSides X F).card = faceSize X F)
    {F : Set ℂ} (hF : F ∈ exceptionalFaces X) :
    ((proc hX).arrivals m F).card ≤ faceSize X F := by
  obtain ⟨hinj, hside⟩ := hopProcess_incidences hX htri (hopEmit X) (hopEmit_mem' hsides) m F
  rw [← hcard F hF]
  exact Finset.card_le_card_of_injOn _ (fun t ht => (hside t ht).1) hinj

/-- The discarded arrivals at all faces are at most the discarded tokens. -/
lemma sum_bad_arrivals_le :
    ∑ F ∈ (proc hX).fin.toFinset, (((proc hX).arrivals m F).filter (hopBad hX K)).card ≤
      (proc hX).numBad (hopBad hX K) := by
  set P := proc hX
  have hdisj : (P.fin.toFinset : Set (Set ℂ)).PairwiseDisjoint
      (fun F => (P.arrivals m F).filter (hopBad hX K)) := by
    intro F _ F' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro t ht ht'
    exact hne (P.face_eq_of_mem_arrivals (Finset.mem_filter.1 ht).1 (Finset.mem_filter.1 ht').1)
  rw [← Finset.card_biUnion hdisj]
  have : P.fin.toFinset.biUnion (fun F => (P.arrivals m F).filter (hopBad hX K)) =
      (P.fin.toFinset.biUnion (fun F => P.arrivals m F)).filter (hopBad hX K) := by
    ext t; simp only [Finset.mem_biUnion, Finset.mem_filter]; tauto
  rw [this]
  refine card_filter_bad_le P _ _ (fun t ht => ?_)
  obtain ⟨F, -, htF⟩ := Finset.mem_biUnion.1 ht
  refine ⟨fun p hp => (hop_arrivals_mem hX (hp ▸ htF)).1 p rfl, fun G hG => ?_⟩
  subst hG
  exact (P.mem_arrivals_inr.1 htF).1

/-- **Counting the omitted faces.** -/
theorem omitted_count (htri : ¬ HasUnitTriangle X)
    (hsides : ∀ G ∈ exceptionalFaces X, (orientedSides X G).Nonempty)
    (hcard : ∀ F ∈ exceptionalFaces X, (orientedSides X F).card = faceSize X F)
    (hcap : ∀ F ∈ exceptionalFaces X, faceSize X F ≤ 6 →
      (((proc hX).arrivals m F).filter (fun t => ¬ hopBad hX K t)).card ≤ 2)
    (hΔ : 0 ≤ lockingDefect X) :
    ((faces hX K m).omittedSmall : ℝ) ≤ 3 * ((proc hX).numBad (hopBad hX K) : ℝ) +
      2 * frontier hX m + highIncidence X + (proc hX).capArr (m + 1) - returnExcess X := by
  set P := proc hX with hPdef
  set S := P.fin.toFinset with hSdef
  have hSmem : ∀ {F}, F ∈ S ↔ F ∈ exceptionalFaces X := Set.Finite.mem_toFinset _
  set a : Set ℂ → ℕ := fun F => (P.arrivals m F).card with ha
  set B : Set ℂ → ℕ := fun F => ((P.arrivals m F).filter (hopBad hX K)).card with hB
  have hfa : ∀ F, P.faceArr (m + 1) F = a F := fun F => P.faceArr_succ_eq_card m F
  -- good arrivals at small faces
  have hgB : ∀ F ∈ S, faceSize X F ≤ 6 → a F ≤ 2 + B F := by
    intro F hF h6
    have h1 := hcap F (hSmem.1 hF) h6
    have h2 := Finset.card_filter_add_card_filter_not (s := P.arrivals m F) (hopBad hX K)
    simp only [ha, hB]; omega
  have hclean : ∀ F, Clean hX K m F ↔ B F = 0 := by
    intro F
    show (∀ t ∈ P.arrivals m F, ¬ hopBad hX K t) ↔ _
    rw [hB]
    simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  -- the deficient clean faces
  set Def := S.filter (fun F => faceSize X F ≤ 6 ∧ B F = 0 ∧
    ((faceSize X F = 5 ∧ a F = 0) ∨ (faceSize X F = 6 ∧ a F ≤ 1))) with hDef
  set Dirty := S.filter (fun F => B F ≠ 0) with hDirty
  set Front := S.filter (fun F => emitted (faceSize X F) (P.faceArr (m + 1) F) = 1 ∧
    emitted (faceSize X F) (P.faceArr m F) = 0) with hFront
  set Prim := S.filter (fun F => hopBad hX K (Sum.inr F)) with hPrim
  -- the omitted faces
  have hsub : (exceptionalFinset X).filter (fun F => faceSize X F ≤ 6 ∧ F ∉ (faces hX K m).good)
      ⊆ Dirty ∪ Def ∪ Front ∪ Prim := by
    intro F hF
    rw [exceptionalFinset_eq hX] at hF
    obtain ⟨hFS, h6, hng⟩ := Finset.mem_filter.1 hF
    have h5 : 5 ≤ faceSize X F := (hSmem.1 hFS).2
    simp only [Finset.mem_union, Finset.mem_filter, hDirty, hDef, hFront, hPrim]
    by_cases hb : B F = 0
    · have hcl := (hclean F).2 hb
      have hg := hgB F hFS h6
      have hFe : F ∈ exceptionalFinset X := by rw [exceptionalFinset_eq hX]; exact hFS
      have hng' : ¬ ((faceSize X F = 5 ∧ a F = 1) ∨ (faceSize X F = 6 ∧ a F = 2) ∨
          (faceSize X F = 5 ∧ a F = 2 ∧ P.Emits m F ∧ ¬ hopBad hX K (Sum.inr F))) :=
        fun h => hng ((mem_good hX K m).2 ⟨hFe, hcl, h⟩)
      simp only [not_or] at hng'
      rcases (show faceSize X F = 5 ∨ faceSize X F = 6 by omega) with hk | hk
      · have hng1 := hng'.1
        have hng3 := hng'.2.2
        rw [hk] at hng1 hng3
        simp only [true_and] at hng1 hng3
        rcases (show a F = 0 ∨ a F = 1 ∨ a F = 2 by omega) with h0 | h1 | h2
        · left; left; right; exact ⟨hFS, h6, hb, Or.inl ⟨hk, h0⟩⟩
        · exact absurd h1 hng1
        · by_cases hE : P.Emits m F
          · right; exact ⟨hFS, by_contra fun hbad => hng3 ⟨h2, hE, hbad⟩⟩
          · left; right
            refine ⟨hFS, ?_, ?_⟩
            · rw [hfa, hk]; unfold emitted; rw [if_pos (Or.inl ⟨rfl, by omega⟩)]
            · rcases TokenProcess.emitted_eq_zero_or_one (faceSize X F) (P.faceArr m F) with
                h | h
              · exact h
              · exact absurd h hE
      · have hng2 := hng'.2.1
        rw [hk] at hng2
        simp only [true_and] at hng2
        left; left; right
        exact ⟨hFS, h6, hb, Or.inr ⟨hk, by omega⟩⟩
    · left; left; left; exact ⟨hFS, hb⟩
  -- cardinalities
  have hSB := sum_bad_arrivals_le hX K m
  have hDirtyc : Dirty.card ≤ ∑ F ∈ S, B F := by
    rw [Finset.card_eq_sum_ones]
    calc ∑ F ∈ Dirty, 1 ≤ ∑ F ∈ Dirty, B F :=
          Finset.sum_le_sum fun F hF => by have := (Finset.mem_filter.1 hF).2; omega
      _ ≤ ∑ F ∈ S, B F := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => Nat.zero_le _)
  have hPrimc : Prim.card ≤ P.numBad (hopBad hX K) := by
    unfold TokenProcess.numBad; exact Nat.le_add_left _ _
  have hFrontc : (Front.card : ℝ) ≤ frontier hX m := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, frontier]
    calc ∑ F ∈ Front, ((1 : ℕ) : ℝ)
        = ∑ F ∈ Front, ((emitted (faceSize X F) (P.faceArr (m + 1) F) : ℝ) -
            emitted (faceSize X F) (P.faceArr m F)) := Finset.sum_congr rfl fun F hF => by
          obtain ⟨-, h1, h0⟩ := Finset.mem_filter.1 hF
          rw [h1, h0]; norm_num
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun F _ _ => frontier_term_nonneg hX m F)
  -- conservation
  have hcons := P.conservation m
  rw [hopProcess_lostArr, Nat.cast_zero, add_zero] at hcons
  set S6 := S.filter (fun F => faceSize X F ≤ 6) with hS6
  set S7 := S.filter (fun F => ¬ faceSize X F ≤ 6) with hS7
  have hsplit := Finset.sum_filter_add_sum_filter_not S (fun F => faceSize X F ≤ 6)
    (fun F => netAbsorbed (faceSize X F) (P.faceArr (m + 1) F))
  -- large faces absorb at most their incidences
  have h7 : ∑ F ∈ S7, netAbsorbed (faceSize X F) (P.faceArr (m + 1) F) ≤ highIncidence X := by
    rw [highIncidence_eq_sum (exceptionalFaces_finite hX), Nat.cast_sum]
    have e : (exceptionalFaces_finite hX).toFinset.filter (fun F => 7 ≤ faceSize X F) = S7 := by
      rw [hS7]; refine Finset.filter_congr (fun F _ => ?_); omega
    rw [e]
    refine Finset.sum_le_sum fun F hF => ?_
    obtain ⟨hFS, h7⟩ := Finset.mem_filter.1 hF
    unfold netAbsorbed
    rw [if_neg (by omega), hfa]
    have := card_arrivals_le hX m htri hsides hcard (hSmem.1 hFS)
    have : (a F : ℝ) ≤ faceSize X F := by exact_mod_cast this
    split_ifs <;> linarith
  -- small faces: capacity
  have h6 : ∑ F ∈ S6, netAbsorbed (faceSize X F) (P.faceArr (m + 1) F) + Def.card ≤
      ∑ F ∈ S6, ((faceSize X F : ℝ) - 4) + ∑ F ∈ S6, (B F : ℝ) := by
    have hDef6 : Def = S6.filter (fun F => B F = 0 ∧
        ((faceSize X F = 5 ∧ a F = 0) ∨ (faceSize X F = 6 ∧ a F ≤ 1))) := by
      rw [hDef, hS6, Finset.filter_filter]
    rw [hDef6, Finset.card_filter, Nat.cast_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun F hF => ?_
    obtain ⟨hFS, h6'⟩ := Finset.mem_filter.1 hF
    have h5 : 5 ≤ faceSize X F := (hSmem.1 hFS).2
    rw [hfa]
    push_cast
    exact netAbsorbed_le_aux (by omega) (hgB F hFS h6') _ (fun h => ⟨h.1, h.2⟩)
  -- the counting identity `u = σ + ρ + Δ`
  have hu : (numUnitHullSides X : ℝ) = faceExcess X + returnExcess X + lockingDefect X := by
    unfold lockingDefect; push_cast; ring
  have hσ : ∑ F ∈ S6, ((faceSize X F : ℝ) - 4) ≤ faceExcess X := by
    rw [faceExcess_eq_sum (exceptionalFaces_finite hX), Nat.cast_sum]
    calc ∑ F ∈ S6, ((faceSize X F : ℝ) - 4) = ∑ F ∈ S6, ((faceSize X F - 4 : ℕ) : ℝ) :=
          Finset.sum_congr rfl fun F hF => by
            have := (hSmem.1 (Finset.mem_filter.1 hF).1).2
            rw [Nat.cast_sub (by omega)]; norm_num
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => Nat.cast_nonneg _)
  have hB6 : ∑ F ∈ S6, (B F : ℝ) ≤ ∑ F ∈ S, (B F : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => Nat.cast_nonneg _)
  have hSBr : ∑ F ∈ S, (B F : ℝ) ≤ P.numBad (hopBad hX K) := by exact_mod_cast hSB
  have hΔr : (0 : ℝ) ≤ lockingDefect X := by exact_mod_cast hΔ
  -- assemble
  have hom : ((faces hX K m).omittedSmall : ℝ) ≤ Dirty.card + Def.card + Front.card + Prim.card := by
    have := (Finset.card_le_card hsub).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_right ((Finset.card_union_le _ _).trans
        (Nat.add_le_add_right (Finset.card_union_le _ _) _)) _))
    unfold GoodFaces.omittedSmall
    exact_mod_cast this
  have hDirtyr : (Dirty.card : ℝ) ≤ ∑ F ∈ S, (B F : ℝ) := by exact_mod_cast hDirtyc
  have hPrimr : (Prim.card : ℝ) ≤ P.numBad (hopBad hX K) := by exact_mod_cast hPrimc
  have hcons' : ∑ F ∈ S, netAbsorbed (faceSize X F) (P.faceArr (m + 1) F) +
      (P.capArr (m + 1) : ℝ) + frontier hX m = numUnitHullSides X := by
    rw [frontier]; exact hcons
  linarith

/-- **A round with a small frontier**: since each face emits at most once, the frontiers of the
first `K` rounds sum to at most `p + f₇`, so one of them is at most `(p + f₇) / K`. -/
theorem exists_frontier_le {K : ℕ} (hK : 0 < K) :
    ∃ m < K, frontier hX m * K ≤ (numPentagons X + faceCount X 7 : ℕ) := by
  set P := proc hX
  set S := P.fin.toFinset
  have htel : ∑ m ∈ Finset.range K, frontier hX m =
      ∑ F ∈ S, (emitted (faceSize X F) (P.faceArr K F) : ℝ) := by
    unfold frontier
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun F _ => ?_
    rw [Finset.sum_range_sub (fun j => (emitted (faceSize X F) (P.faceArr j F) : ℝ)) K]
    simp [TokenProcess.faceArr_zero, emitted]
  have hle : ∑ F ∈ S, (emitted (faceSize X F) (P.faceArr K F) : ℝ) ≤
      (numPentagons X + faceCount X 7 : ℕ) := by
    rw [numPentagons, faceCount_eq_card_filter (exceptionalFaces_finite hX) (by norm_num),
      faceCount_eq_card_filter (exceptionalFaces_finite hX) (by norm_num)]
    have hsub : S.filter (fun F => emitted (faceSize X F) (P.faceArr K F) = 1) ⊆
        S.filter (fun F => faceSize X F = 5) ∪ S.filter (fun F => faceSize X F = 7) := by
      intro F hF
      obtain ⟨hFS, h1⟩ := Finset.mem_filter.1 hF
      have := P.faceSize_of_emits (j := K) (G := F) h1
      rcases this with h | h
      · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hFS, h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hFS, h⟩)
    have h1 : ∑ F ∈ S, (emitted (faceSize X F) (P.faceArr K F) : ℝ) =
        (S.filter (fun F => emitted (faceSize X F) (P.faceArr K F) = 1)).card := by
      rw [Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun F _ => ?_
      rcases TokenProcess.emitted_eq_zero_or_one (faceSize X F) (P.faceArr K F) with h | h <;>
        simp [h]
    rw [h1]
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image (Finset.range K) (frontier hX)
    ⟨0, Finset.mem_range.2 hK⟩
  refine ⟨m, Finset.mem_range.1 hm, ?_⟩
  have : frontier hX m * K ≤ ∑ j ∈ Finset.range K, frontier hX j := by
    calc frontier hX m * K = ∑ _j ∈ Finset.range K, frontier hX m := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun j hj => hmin j hj
  linarith

end Sat

end Erdos99

end

end SaturationCount

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `SaturationLabels`
-/

section SaturationLabels

/-!
# Marks and labels of the saturated good faces (Verification Guide §10)

Assuming the token bound of §9.2 (every good token carries a source label with nearly its exit
direction, starting near the far end of its track), this file proves:

* `Sat.card_good_arrivals_le_two`: a pentagon or hexagon receives at most two good tokens (local
  capacity);
* `Sat.isMarking`: the marked ports of the good faces are short and have the right number;
* `Sat.isLabelled`: the labels of the good faces are source labels with the requested tolerance:
  the marked side vectors sum to `k τ` (two positive inputs and one negative output at an activated
  pentagon), and the face lies near the start of its label.
-/

open scoped BigOperators Real
open Filter Topology

@[expose] public noncomputable section

open Classical

namespace Erdos99

namespace Sat

open Propagation

variable {X : Finset Plane} {hX : IsSeparated X} {K m : ℕ}

/-- The direction of a unit edge is its side vector. -/
lemma sideDir_eq_of_dist {x : Plane × Plane} (h : dist x.1 x.2 = 1) : sideDir x = x.2 - x.1 := by
  rw [sideDir, ← dist_eq_norm', h, inv_one, one_smul]

lemma toC_sub_eq_sideDir {x : Plane × Plane} (h : dist x.1 x.2 = 1) :
    toC x.2 - toC x.1 = toC (sideDir x) := by
  rw [sideDir_eq_of_dist h, map_sub]

/-- The cutoff scale grows with the round. -/
lemma cutB_mono {D : ℝ} (hD : 1 ≤ D) {i j : ℕ} (h : i ≤ j) : cutB D i ≤ cutB D j := by
  unfold cutB
  have := Real.rpow_le_rpow_of_exponent_le hD (show 1 - scaleExp i ≤ 1 - scaleExp j by
    linarith [scaleExp_anti h])
  linarith

section Analytic

variable (htri : ¬ HasUnitTriangle X)
  (hsides : ∀ G ∈ exceptionalFaces X, (orientedSides X G).Nonempty) (hmK : m ≤ K)
  (hTB : ∀ t, (proc hX).Timed K t → ¬ hopBad hX K t →
    (∀ p, t = Sum.inl p → p ∈ unitHullSides X) → (∀ G, t = Sum.inr G → G ∈ exceptionalFaces X) →
    TokBound hX K K t)

include hmK hTB in
/-- A good arriving token carries a label with the bound of round `K`. -/
lemma good_tok {F : Set ℂ} {t : (Plane × Plane) ⊕ Set ℂ} (ht : t ∈ (proc hX).arrivals m F)
    (hg : ¬ hopBad hX K t) :
    ‖sideDir (exitEdge (hopEmit X) t) - sideDir ((proc hX).labelAt K t)‖ ≤ errB (diam X) K ∧
      dist ((proc hX).labelAt K t).1 (hopEnd X (exitEdge (hopEmit X) t)).1 ≤ disB (diam X) K ∧
      (proc hX).labelAt K t ∈ unitHullSides X := by
  have hT := (proc hX).timed_mono hmK ((proc hX).timed_of_mem_arrivals ht)
  have hm := hop_arrivals_mem hX ht
  obtain ⟨h1, h2⟩ := hTB t hT hg hm.1 hm.2
  exact ⟨h1, h2, (proc hX).labelAt_mem hT hm.1⟩

variable {O : Plane} {η δ : ℝ} (hR : RoundData X O (diam X) η δ)
  (hdist : ∀ F ∈ exceptionalFaces X, ∀ ab ∈ orientedSides X F, ∀ ab' ∈ orientedSides X F,
    dist ab.1 ab'.1 ≤ faceSize X F)

/-- The label tolerance between two good tokens arriving at one small face. -/
def theta (X : Finset Plane) (K : ℕ) (δ : ℝ) : ℝ :=
  2 * (2 * disB (diam X) K + 6) / diam X + 4 * √(3 * δ)

include htri hsides hmK hTB hR hdist in
/-- **The labels of two good tokens at a small face are close.** -/
lemma label_close {F : Set ℂ} (hF : F ∈ exceptionalFaces X) (h6 : faceSize X F ≤ 6)
    {t t' : (Plane × Plane) ⊕ Set ℂ} (ht : t ∈ (proc hX).arrivals m F) (hg : ¬ hopBad hX K t)
    (ht' : t' ∈ (proc hX).arrivals m F) (hg' : ¬ hopBad hX K t') :
    dist ((proc hX).labelAt K t).1 ((proc hX).labelAt K t').1 ≤ 2 * disB (diam X) K + 6 ∧
    ‖sideDir ((proc hX).labelAt K t) - sideDir ((proc hX).labelAt K t')‖ ≤ theta X K δ := by
  obtain ⟨-, d1, u1⟩ := good_tok hmK hTB ht hg
  obtain ⟨-, d2, u2⟩ := good_tok hmK hTB ht' hg'
  have s1 := (exit_facts htri hsides ht).2.2.2.2
  have s2 := (exit_facts htri hsides ht').2.2.2.2
  have hd := hdist F hF _ s1 _ s2
  simp only [dist_toC] at hd
  have h6' : (faceSize X F : ℝ) ≤ 6 := by exact_mod_cast h6
  have hdl : dist ((proc hX).labelAt K t).1 ((proc hX).labelAt K t').1 ≤
      2 * disB (diam X) K + 6 := by
    calc _ ≤ dist ((proc hX).labelAt K t).1 (hopEnd X (exitEdge (hopEmit X) t)).1 +
          dist (hopEnd X (exitEdge (hopEmit X) t)).1 (hopEnd X (exitEdge (hopEmit X) t')).1 +
          dist (hopEnd X (exitEdge (hopEmit X) t')).1 ((proc hX).labelAt K t').1 :=
          dist_triangle4 _ _ _ _
      _ ≤ disB (diam X) K + 6 + disB (diam X) K := by
          linarith [dist_comm ((proc hX).labelAt K t').1 (hopEnd X (exitEdge (hopEmit X) t')).1]
      _ = _ := by ring
  refine ⟨hdl, ?_⟩
  have hc1 := mem_ccwHullSides.1 (Finset.mem_filter.1 u1).1
  have hc2 := mem_ccwHullSides.1 (Finset.mem_filter.1 u2).1
  refine (sideDir_sub_le hR hc1 hc2).trans ?_
  unfold theta
  have hD := hR.D_pos
  gcongr

include htri hsides hmK hTB hR hdist in
/-- **Local capacity**: a pentagon or hexagon receives at most two good tokens. -/
theorem card_good_arrivals_le_two
    (hcapF : ∀ F ∈ exceptionalFaces X, ∀ e : ℂ, ‖e‖ = 1 → ∀ M ⊆ orientedSides X F,
      (∀ ab ∈ M, 19 / 20 ≤ inner ℝ (ab.2 - ab.1) e) → (M.card : ℝ) ≤ markedCap (faceSize X F))
    (hsmall : errB (diam X) K + theta X K δ ≤ 3 / 10)
    {F : Set ℂ} (hF : F ∈ exceptionalFaces X) (h6 : faceSize X F ≤ 6) :
    (((proc hX).arrivals m F).filter (fun t => ¬ hopBad hX K t)).card ≤ 2 := by
  set S := ((proc hX).arrivals m F).filter (fun t => ¬ hopBad hX K t) with hS
  have hD := hR.D_pos
  obtain ⟨e, he, hmark⟩ := marked_of_labels hR S (exitEdge (hopEmit X)) ((proc hX).labelAt K)
    (a := errB (diam X) K) (b := 2 * disB (diam X) K + 6)
    (fun t ht => by
      have := (exit_facts htri hsides (Finset.mem_filter.1 ht).1).2.2.1
      rw [mem_unitEdges] at this
      rw [← dist_eq_norm', this.2.2])
    (fun t ht => mem_ccwHullSides.1 (Finset.mem_filter.1
      (good_tok hmK hTB (Finset.mem_filter.1 ht).1 (Finset.mem_filter.1 ht).2).2.2).1)
    (fun t ht => (good_tok hmK hTB (Finset.mem_filter.1 ht).1 (Finset.mem_filter.1 ht).2).1)
    (fun t ht t' ht' => (label_close htri hsides hmK hTB hR hdist hF h6
      (Finset.mem_filter.1 ht).1 (Finset.mem_filter.1 ht).2
      (Finset.mem_filter.1 ht').1 (Finset.mem_filter.1 ht').2).1)
    (by unfold theta at hsmall; linarith)
  obtain ⟨hinj, hside⟩ := hopProcess_incidences hX htri (hopEmit X) (hopEmit_mem' hsides) m F
  have hc := hcapF F hF e he (S.image (hopEntry X (hopEmit X)).edge) (fun ab hab => by
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hab
      exact (hside t (Finset.mem_filter.1 ht).1).1)
    (fun ab hab => by
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hab
      rw [(hside t (Finset.mem_filter.1 ht).1).2]
      exact hmark t ht)
  rw [Finset.card_image_of_injOn (hinj.mono (fun t ht => (Finset.mem_filter.1 ht).1))] at hc
  have hcap2 : markedCap (faceSize X F) = 2 := by unfold markedCap; rw [if_pos h6]
  rw [hcap2] at hc
  exact_mod_cast hc

end Analytic

/-! ## Entry edges -/

section Entries

variable (htri : ¬ HasUnitTriangle X)
  (hsides : ∀ G ∈ exceptionalFaces X, (orientedSides X G).Nonempty)

/-- The oriented side through which a token enters its receiver. -/
abbrev side (X : Finset Plane) (t : (Plane × Plane) ⊕ Set ℂ) : ℂ × ℂ :=
  (toC (hopEnd X (exitEdge (hopEmit X) t)).1, toC (hopEnd X (exitEdge (hopEmit X) t)).2)

include htri hsides in
/-- The entry side of an arriving token: an oriented side of the face, parallel to the exit edge,
whose unit edge is the entry edge and has the same track as the exit edge. -/
lemma entry_facts {j : ℕ} {F : Set ℂ} {t : (Plane × Plane) ⊕ Set ℂ}
    (ht : t ∈ (proc hX).arrivals j F) :
    side X t ∈ orientedSides X F ∧
      (side X t).2 - (side X t).1 = toC (sideDir (exitEdge (hopEmit X) t)) ∧
      Sym2.map toC (entry X (exitEdge (hopEmit X) t)) = s((side X t).1, (side X t).2) ∧
      entry X (exitEdge (hopEmit X) t) ∈ unitEdges X ∧
      IsPort X (Sum.inl F) (entry X (exitEdge (hopEmit X) t)) ∧
      trackLength X (allTrackOf X (entry X (exitEdge (hopEmit X) t))) ≤
        srcLen X s((exitEdge (hopEmit X) t).1, (exitEdge (hopEmit X) t).2) := by
  obtain ⟨hxX, -, hu, -, hs⟩ := exit_facts htri hsides ht
  have hd1 : dist (exitEdge (hopEmit X) t).1 (exitEdge (hopEmit X) t).2 = 1 :=
    (mem_unitEdges.1 hu).2.2
  have hF : F ∈ exceptionalFaces X := by
    have hd := (exit_facts htri hsides ht).2.2.2.1
    unfold hopDest at hd
    split_ifs at hd with hex
    cases hd; exact hex.choose_spec.1
  have hmap : Sym2.map toC (entry X (exitEdge (hopEmit X) t)) = s((side X t).1, (side X t).2) := by
    rw [entry, Sym2.map_pair_eq]
  refine ⟨hs, ?_, hmap, ?_, ⟨hF, ?_⟩, ?_⟩
  · rw [← map_sub, hopEnd_sub, map_sub, toC_sub_eq_sideDir hd1]
  · have := mem_unitEdges_of_mem_orientedSides hs
    rw [entry, Sym2.eq_swap]; exact this
  · rw [hmap]; exact (Finset.mem_filter.1 hs).2.1
  · rw [entry, allTrackOf_hopEnd hxX hu]
    exact trackLength_allTrackOf_le_srcLen hX htri hu

include htri hsides in
/-- Distinct arrivals have distinct entry edges. -/
lemma entry_injOn {F : Set ℂ} (hF : F ∈ exceptionalFaces X) :
    Set.InjOn (fun t => entry X (exitEdge (hopEmit X) t)) ((proc hX).arrivals m F) := by
  intro t ht t' ht' he
  obtain ⟨hinj, -⟩ := hopProcess_incidences hX htri (hopEmit X) (hopEmit_mem' hsides) m F
  obtain ⟨s1, -, m1, -⟩ := entry_facts htri hsides ht
  obtain ⟨s2, -, m2, -⟩ := entry_facts htri hsides ht'
  have hs : s((side X t).1, (side X t).2) = s((side X t').1, (side X t').2) := by
    rw [← m1, ← m2]; simp only at he; rw [he]
  have := orientedSides_injOn (nonempty_of_mem_exceptionalFaces hF) s1 s2 hs
  refine hinj ht ht' ?_
  rw [hopEntry_edge, hopEntry_edge]
  exact this

end Entries

/-- **Marked sums from oriented sides.**  If the marked edges `S` and the oriented sides `T` of `F`
correspond to each other, the marked sum is the sum of the side vectors over `T`. -/
lemma markedSum_eq_of {F : Set ℂ} (hne : F.Nonempty) (S : Finset (Sym2 Plane))
    (T : Finset (ℂ × ℂ)) (hT : T ⊆ orientedSides X F)
    (hST : ∀ e ∈ S, ∃ ab ∈ T, Sym2.map toC e = s(ab.1, ab.2))
    (hTS : ∀ ab ∈ T, ∃ e ∈ S, Sym2.map toC e = s(ab.1, ab.2)) :
    markedSum X F S = ∑ ab ∈ T, (ab.2 - ab.1) := by
  unfold markedSum
  congr 1
  ext ab
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hab, e, he, hmap⟩
    obtain ⟨ab', hab', hmap'⟩ := hST e he
    have := orientedSides_injOn hne hab (hT hab') (hmap.symm.trans hmap')
    rw [this]; exact hab'
  · intro hab
    exact ⟨hT hab, hTS ab hab⟩

end Sat

end Erdos99

end

end SaturationLabels

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `SaturationMarks`
-/

section SaturationMarks

/-!
# The marking and the source labels of the saturated good faces (Verification Guide §10)

* `Sat.isMarking`: the marked ports of every good face are short ports, one at an ordinary
  pentagon, two at a hexagon and three at an activated pentagon;
* `Sat.isLabelled`: the labels `Sat.lab` are injective source labels of tolerance `tol`.
-/

open scoped BigOperators Real
open Filter Topology

@[expose] public noncomputable section

open Classical

namespace Erdos99

namespace Sat

open Propagation

variable {X : Finset Plane} {hX : IsSeparated X} {K m : ℕ}

/-- The exit track of a good emitted token is shorter than `Λ_K / 2`. -/
lemma srcLen_lt_of_good_inr (hD1 : 1 ≤ diam X) (hmK : m ≤ K) {G : Set ℂ}
    (hG : (proc hX).Emits m G) (hg : ¬ hopBad hX K (Sum.inr G)) :
    (srcLen X s((hopEmit X G).1, (hopEmit X G).2) : ℝ) < cutB (diam X) K := by
  have h := ((proc hX).good_inputs (hopSrcBad X) (hopPrimBad X) (n := K)
    ((proc hX).emits_mono hmK hG) hg).1
  unfold hopPrimBad at h
  push_neg at h
  obtain ⟨-, hle, -⟩ := (proc hX).firstEmit_spec hG
  exact h.trans_le (cutB_mono hD1 (by omega))

/-- The exit track of a good arriving token is short. -/
lemma srcLen_lt_of_good (hD1 : 1 ≤ diam X) (hmK : m ≤ K) {L : ℝ}
    (hL1 : diam X ^ (19 / 20 : ℝ) ≤ L) (hL2 : cutB (diam X) K ≤ L) {F : Set ℂ}
    {t : (Plane × Plane) ⊕ Set ℂ} (ht : t ∈ (proc hX).arrivals m F) (hg : ¬ hopBad hX K t) :
    (srcLen X s((exitEdge (hopEmit X) t).1, (exitEdge (hopEmit X) t).2) : ℝ) < L := by
  rcases t with p | G
  · have : ¬ hopSrcBad X p := by
      have := hg; unfold hopBad at this; rwa [TokenProcess.badAt_inl] at this
    unfold hopSrcBad at this
    push_neg at this
    exact this.trans_le hL1
  · exact (srcLen_lt_of_good_inr hD1 hmK ((proc hX).mem_arrivals_inr.1 ht).2.2 hg).trans_le hL2

section Analytic

variable (htri : ¬ HasUnitTriangle X)
  (hsides : ∀ G ∈ exceptionalFaces X, (orientedSides X G).Nonempty) (hmK : m ≤ K)
  (hTB : ∀ t, (proc hX).Timed K t → ¬ hopBad hX K t →
    (∀ p, t = Sum.inl p → p ∈ unitHullSides X) → (∀ G, t = Sum.inr G → G ∈ exceptionalFaces X) →
    TokBound hX K K t)
  {O : Plane} {η δ : ℝ} (hR : RoundData X O (diam X) η δ)
  (hdist : ∀ F ∈ exceptionalFaces X, ∀ ab ∈ orientedSides X F, ∀ ab' ∈ orientedSides X F,
    dist ab.1 ab'.1 ≤ faceSize X F)

include hmK in
/-- The token emitted by an activated pentagon carries the label of its parent. -/
lemma emit_label {F : Set ℂ} (hF : F ∈ (faces hX K m).act) :
    (proc hX).labelAt K (Sum.inr F) = (proc hX).labelAt K ((proc hX).parent F) :=
  (proc hX).labelAt_inr ((proc hX).emits_mono hmK (Finset.mem_filter.1 hF).2.2.2.2.1)

include hmK hTB in
lemma emit_tok {F : Set ℂ} (hF : F ∈ (faces hX K m).act) :
    ‖sideDir (hopEmit X F) - sideDir ((proc hX).labelAt K ((proc hX).parent F))‖ ≤
      errB (diam X) K := by
  obtain ⟨hFe, -, -, -, hE, hg⟩ := Finset.mem_filter.1 hF
  have hF' : F ∈ exceptionalFaces X := (mem_exceptionalFinset hX).1 hFe
  have hT : (proc hX).Timed K (Sum.inr F) := (proc hX).emits_mono hmK hE
  have := (hTB (Sum.inr F) hT hg (fun p hp => by simp at hp) (fun G hG => by cases hG; exact hF')).1
  calc _ = ‖sideDir (hopEmit X F) - sideDir ((proc hX).labelAt K (Sum.inr F))‖ := by
        rw [emit_label hmK hF]
    _ ≤ _ := this

include htri hsides hmK hTB hR hdist in
/-- **The exit edge of an activated pentagon is not an entry edge**: its direction is nearly the
negative tangent, while the entries have nearly the positive tangent. -/
lemma emit_ne_entry (hsmall : errB (diam X) K + theta X K δ ≤ 3 / 10) {F : Set ℂ}
    (hF : F ∈ (faces hX K m).act) {t : (Plane × Plane) ⊕ Set ℂ}
    (ht : t ∈ (proc hX).arrivals m F) :
    entry X (exitEdge (hopEmit X) t) ≠ s((hopEmit X F).1, (hopEmit X F).2) := by
  intro he
  obtain ⟨hFe, h5, hcl, -, hE, hgF⟩ := Finset.mem_filter.1 hF
  have hF' : F ∈ exceptionalFaces X := (mem_exceptionalFinset hX).1 hFe
  obtain ⟨s1, v1, m1, -⟩ := entry_facts htri hsides ht
  have hm := hopEmit_mem' hsides F hF'
  have hs : s((side X t).1, (side X t).2) =
      s(((toC (hopEmit X F).2, toC (hopEmit X F).1) : ℂ × ℂ).1,
        ((toC (hopEmit X F).2, toC (hopEmit X F).1) : ℂ × ℂ).2) := by
    rw [← m1, he, Sym2.map_pair_eq]; exact Sym2.eq_swap
  have heq := orientedSides_injOn (nonempty_of_mem_exceptionalFaces hF') s1 hm hs
  rw [heq] at v1
  have hd1 : dist (hopEmit X F).1 (hopEmit X F).2 = 1 := by
    rw [dist_comm]; exact dist_eq_one_of_mem_orientedSides hm
  have hneg : sideDir (exitEdge (hopEmit X) t) = -sideDir (hopEmit X F) := by
    apply toC.injective
    rw [← v1, map_neg, ← toC_sub_eq_sideDir hd1]
    simp only; ring
  have hpar := parent_mem_arrivals hX m hE
  obtain ⟨a1, -, -⟩ := good_tok hmK hTB ht (hcl t ht)
  have a2 := (label_close htri hsides hmK hTB hR hdist hF' (by omega) ht (hcl t ht) hpar
    (hcl _ hpar)).2
  have a3 := emit_tok hmK hTB hF
  have hn : ‖sideDir (hopEmit X F)‖ = 1 := norm_sideDir (by
    intro h; rw [h, dist_self] at hd1; norm_num at hd1)
  have : ‖(2 : ℝ) • sideDir (hopEmit X F)‖ ≤ 2 * errB (diam X) K + theta X K δ := by
    have e : (2 : ℝ) • sideDir (hopEmit X F) =
        -((sideDir (exitEdge (hopEmit X) t) - sideDir ((proc hX).labelAt K t)) +
          (sideDir ((proc hX).labelAt K t) - sideDir ((proc hX).labelAt K ((proc hX).parent F))) +
          (sideDir ((proc hX).labelAt K ((proc hX).parent F)) - sideDir (hopEmit X F))) := by
      rw [hneg, two_smul]; abel
    rw [e, norm_neg]
    refine norm_add₃_le.trans ?_
    rw [norm_sub_rev (sideDir ((proc hX).labelAt K ((proc hX).parent F)))]
    linarith
  rw [norm_smul, hn] at this
  have hth : 0 ≤ theta X K δ := by
    unfold theta
    have := hR.D_pos
    have : 0 ≤ disB (diam X) K := Real.rpow_nonneg hR.D_pos.le _
    positivity
  have : 0 ≤ errB (diam X) K := Real.rpow_nonneg hR.D_pos.le _
  norm_num at *
  linarith

include htri hsides hmK hTB hR hdist in
/-- **The marked sum of a good face**: the entry directions of its arrivals, minus its exit
direction if it has emitted. -/
lemma markedSum_mk (hsmall : errB (diam X) K + theta X K δ ≤ 3 / 10) {F : Set ℂ}
    (hF : F ∈ (faces hX K m).good) :
    markedSum X F (mk hX m F) = ∑ t ∈ (proc hX).arrivals m F,
      toC (sideDir (exitEdge (hopEmit X) t)) -
      (if (proc hX).Emits m F then toC (sideDir (hopEmit X F)) else 0) := by
  have hFe := ((mem_good hX K m).1 hF).1
  have hF' : F ∈ exceptionalFaces X := (mem_exceptionalFinset hX).1 hFe
  have hm := hopEmit_mem' hsides F hF'
  set A := (proc hX).arrivals m F
  set E : Finset (ℂ × ℂ) := if (proc hX).Emits m F then
    {(toC (hopEmit X F).2, toC (hopEmit X F).1)} else ∅ with hE
  have hmapE : Sym2.map toC s((hopEmit X F).1, (hopEmit X F).2) =
      s((toC (hopEmit X F).2, toC (hopEmit X F).1).1, (toC (hopEmit X F).2, toC (hopEmit X F).1).2) := by
    rw [Sym2.map_pair_eq]; exact Sym2.eq_swap
  rw [markedSum_eq_of (nonempty_of_mem_exceptionalFaces hF') _ (A.image (side X) ∪ E)]
  rotate_left
  · intro ab hab
    rcases Finset.mem_union.1 hab with h | h
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 h
      exact (entry_facts htri hsides ht).1
    · rw [hE] at h; split_ifs at h
      · rw [Finset.mem_singleton.1 h]; exact hm
      · exact absurd h (Finset.notMem_empty _)
  · intro e he
    rcases Finset.mem_union.1 he with h | h
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 h
      exact ⟨side X t, Finset.mem_union_left _ (Finset.mem_image_of_mem _ ht),
        (entry_facts htri hsides ht).2.2.1⟩
    · split_ifs at h with hEm
      · rw [Finset.mem_singleton.1 h]
        refine ⟨_, Finset.mem_union_right _ ?_, hmapE⟩
        rw [hE, if_pos hEm]; exact Finset.mem_singleton_self _
      · exact absurd h (Finset.notMem_empty _)
  · intro ab hab
    rcases Finset.mem_union.1 hab with h | h
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 h
      exact ⟨_, mem_mk_of_mem_arrivals hX m ht, (entry_facts htri hsides ht).2.2.1⟩
    · rw [hE] at h; split_ifs at h with hEm
      · rw [Finset.mem_singleton.1 h]
        exact ⟨_, mem_mk_of_emits hX m hEm, hmapE⟩
      · exact absurd h (Finset.notMem_empty _)
  have hdisj : Disjoint (A.image (side X)) E := by
    rw [Finset.disjoint_left]
    intro ab h1 h2
    rw [hE] at h2; split_ifs at h2 with hEm
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 h1
      have hact := act_of_emits hX K m hF hEm
      apply emit_ne_entry htri hsides hmK hTB hR hdist hsmall hact ht
      have h3 := (entry_facts htri hsides ht).2.2.1
      rw [Finset.mem_singleton.1 h2] at h3
      exact Sym2.map.injective toC.injective (h3.trans hmapE.symm)
    · exact absurd h2 (Finset.notMem_empty _)
  obtain ⟨hinj, -⟩ := hopProcess_incidences hX htri (hopEmit X) (hopEmit_mem' hsides) m F
  have hinj' : Set.InjOn (side X) A := by
    intro t ht t' ht' h
    exact hinj ht ht' (by rw [hopEntry_edge, hopEntry_edge]; exact h)
  rw [Finset.sum_union hdisj, Finset.sum_image hinj', sub_eq_add_neg]
  congr 1
  · exact Finset.sum_congr rfl fun t ht => (entry_facts htri hsides ht).2.1
  · rw [hE]
    split_ifs
    · rw [Finset.sum_singleton]
      have hd1 : dist (hopEmit X F).1 (hopEmit X F).2 = 1 := by
        rw [dist_comm]; exact dist_eq_one_of_mem_orientedSides hm
      rw [← toC_sub_eq_sideDir hd1]
      simp only; ring
    · simp

include htri hsides hmK hTB hR hdist in
/-- **The marking** (`IsMarking`): the marked ports of a good face are short ports, as many as its
number of marks. -/
theorem isMarking (hsmall : errB (diam X) K + theta X K δ ≤ 3 / 10) (hD1 : 1 ≤ diam X) {L : ℝ}
    (hL1 : diam X ^ (19 / 20 : ℝ) ≤ L) (hL2 : cutB (diam X) K ≤ L) :
    IsMarking X L (faces hX K m) (mk hX m) := by
  intro F hF
  obtain ⟨hFe, hcl, hcases⟩ := (mem_good hX K m).1 hF
  have hF' : F ∈ exceptionalFaces X := (mem_exceptionalFinset hX).1 hFe
  have hm := hopEmit_mem' hsides F hF'
  set A := (proc hX).arrivals m F
  refine ⟨fun e he => ?_, ?_⟩
  · rcases Finset.mem_union.1 he with h | h
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 h
      obtain ⟨-, -, -, hu, hp, hlen⟩ := entry_facts htri hsides ht
      refine Finset.mem_filter.2 ⟨hu, hp, ?_⟩
      exact (Nat.cast_le.2 hlen).trans_lt (srcLen_lt_of_good hD1 hmK hL1 hL2 ht (hcl t ht))
    · split_ifs at h with hEm
      · rw [Finset.mem_singleton.1 h]
        have hact := act_of_emits hX K m hF hEm
        have hu := mem_unitEdges_of_mem_orientedSides hm
        refine Finset.mem_filter.2 ⟨hu, ⟨hF', ?_⟩, ?_⟩
        · rw [Sym2.map_pair_eq, Sym2.eq_swap]; exact (Finset.mem_filter.1 hm).2.1
        · refine (Nat.cast_le.2 (trackLength_allTrackOf_le_srcLen hX htri hu)).trans_lt ?_
          exact (srcLen_lt_of_good_inr hD1 hmK hEm (Finset.mem_filter.1 hact).2.2.2.2.2).trans_le hL2
      · exact absurd h (Finset.notMem_empty _)
  · have hdisj : Disjoint (A.image (fun t => entry X (exitEdge (hopEmit X) t)))
        (if (proc hX).Emits m F then {s((hopEmit X F).1, (hopEmit X F).2)} else ∅) := by
      split_ifs with hEm
      · rw [Finset.disjoint_singleton_right]
        intro h
        obtain ⟨t, ht, he⟩ := Finset.mem_image.1 h
        exact emit_ne_entry htri hsides hmK hTB hR hdist hsmall (act_of_emits hX K m hF hEm) ht he
      · exact Finset.disjoint_empty_right _
    rw [mk, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn (entry_injOn htri hsides hF')]
    unfold GoodFaces.marks
    rcases hcases with ⟨h5, h1⟩ | ⟨h6, h2⟩ | ⟨h5, h2, hEm, hg⟩
    · have hpent : F ∈ (faces hX K m).pent := Finset.mem_filter.2 ⟨hFe, h5, hcl, h1⟩
      have hEm : ¬ (proc hX).Emits m F := fun hEm =>
        Finset.disjoint_left.1 (faces hX K m).disj hpent (act_of_emits hX K m hF hEm)
      rw [if_neg hEm, if_pos hpent, h1]; rfl
    · have hhex : F ∈ (faces hX K m).hex := Finset.mem_filter.2 ⟨hFe, h6, hcl, h2⟩
      have hEm : ¬ (proc hX).Emits m F := fun hEm => by
        have := (proc hX).faceSize_of_emits hEm; omega
      rw [if_neg hEm, if_neg (Finset.disjoint_right.1 (faces hX K m).disjoint_pent_hex hhex),
        if_pos hhex, h2]; rfl
    · have hact : F ∈ (faces hX K m).act := Finset.mem_filter.2 ⟨hFe, h5, hcl, h2, hEm, hg⟩
      rw [if_pos hEm, if_neg (Finset.disjoint_right.1 (faces hX K m).disj hact),
        if_neg (Finset.disjoint_right.1 (faces hX K m).disjoint_hex_act hact), h2]; rfl

include htri hsides hmK hTB hR hdist in
/-- **Source labels** (`IsLabelled`): the labels of the good faces are injective unit hull sides;
the marked side vectors sum to `k τ` up to `3 (errB + θ)`, and the face lies within
`disB + 6` of the start of its label. -/
theorem isLabelled (hsmall : errB (diam X) K + theta X K δ ≤ 3 / 10) {tol : ℝ}
    (htol : 3 * (errB (diam X) K + theta X K δ) ≤ tol)
    (hvert : disB (diam X) K + 6 ≤ tol * diam X) :
    IsLabelled X tol (faces hX K m) (mk hX m) := by
  have hD := hR.D_pos
  have he0 : 0 ≤ errB (diam X) K := Real.rpow_nonneg hD.le _
  have hth : 0 ≤ theta X K δ := by
    unfold theta
    have : 0 ≤ disB (diam X) K := Real.rpow_nonneg hD.le _
    positivity
  refine ⟨lab hX K m, lab_injOn hX K m hmK, fun F hF => ?_⟩
  obtain ⟨hFe, hcl, hcases⟩ := (mem_good hX K m).1 hF
  have hF' : F ∈ exceptionalFaces X := (mem_exceptionalFinset hX).1 hFe
  have h6 : faceSize X F ≤ 6 := by rcases hcases with h | h | h <;> omega
  obtain ⟨hr, hrpar⟩ := ret_spec hX K m hF
  set r := ret hX m F
  set A := (proc hX).arrivals m F
  obtain ⟨a1, a2, a3⟩ := good_tok hmK hTB hr (hcl r hr)
  have hlab : lab hX K m F = (proc hX).labelAt K r := rfl
  -- every arrival enters nearly along the label
  have hnear : ∀ t ∈ A, ‖toC (sideDir (exitEdge (hopEmit X) t)) -
      toC (sideDir (lab hX K m F))‖ ≤ errB (diam X) K + theta X K δ := by
    intro t ht
    rw [← map_sub, LinearIsometryEquiv.norm_map, hlab]
    have b1 := (good_tok hmK hTB ht (hcl t ht)).1
    have b2 := (label_close htri hsides hmK hTB hR hdist hF' h6 ht (hcl t ht) hr (hcl r hr)).2
    calc _ = ‖(sideDir (exitEdge (hopEmit X) t) - sideDir ((proc hX).labelAt K t)) +
          (sideDir ((proc hX).labelAt K t) - sideDir ((proc hX).labelAt K r))‖ := by
          congr 1; abel
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add b1 b2)
  refine ⟨a3, ?_, ?_⟩
  · rw [markedSum_mk htri hsides hmK hTB hR hdist hsmall hF,
      show (proc hX).arrivals m F = A from rfl]
    unfold GoodFaces.markMult
    rcases hcases with ⟨h5, h1⟩ | ⟨h6', h2⟩ | ⟨h5, h2, hEm, hg⟩
    · have hpent : F ∈ (faces hX K m).pent := Finset.mem_filter.2 ⟨hFe, h5, hcl, h1⟩
      have hEm : ¬ (proc hX).Emits m F := fun hEm =>
        Finset.disjoint_left.1 (faces hX K m).disj hpent (act_of_emits hX K m hF hEm)
      rw [if_neg hEm, if_neg (Finset.disjoint_left.1 (faces hX K m).disjoint_pent_hex hpent)]
      obtain ⟨t, ht⟩ := Finset.card_eq_one.1 h1
      rw [ht, Finset.sum_singleton, sub_zero, one_mul]
      have := hnear t (by rw [ht]; exact Finset.mem_singleton_self t)
      linarith
    · have hhex : F ∈ (faces hX K m).hex := Finset.mem_filter.2 ⟨hFe, h6', hcl, h2⟩
      have hEm : ¬ (proc hX).Emits m F := fun hEm => by
        have := (proc hX).faceSize_of_emits hEm; omega
      rw [if_neg hEm, if_pos hhex, sub_zero]
      have e : ∑ t ∈ A, toC (sideDir (exitEdge (hopEmit X) t)) - 2 * toC (sideDir (lab hX K m F)) =
          ∑ t ∈ A, (toC (sideDir (exitEdge (hopEmit X) t)) - toC (sideDir (lab hX K m F))) := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, h2]; simp [two_mul]
      rw [e]
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum hnear).trans ?_
      rw [Finset.sum_const, h2]
      simp only [nsmul_eq_mul, Nat.cast_ofNat]
      linarith
    · have hact : F ∈ (faces hX K m).act := Finset.mem_filter.2 ⟨hFe, h5, hcl, h2, hEm, hg⟩
      rw [if_pos hEm, if_neg (Finset.disjoint_right.1 (faces hX K m).disjoint_hex_act hact),
        one_mul]
      have hpar := parent_mem_arrivals hX m hEm
      have hr' : r ∈ A.erase ((proc hX).parent F) := Finset.mem_erase.2 ⟨hrpar hEm, hr⟩
      have hc1 : (A.erase ((proc hX).parent F)).card = 1 := by
        rw [Finset.card_erase_of_mem hpar, h2]
      obtain ⟨t, ht⟩ := Finset.card_eq_one.1 hc1
      rw [ht, Finset.mem_singleton] at hr'
      rw [← Finset.add_sum_erase A _ hpar, ht, Finset.sum_singleton, ← hr']
      have c1 := hnear r hr
      obtain ⟨c2, -, -⟩ := good_tok hmK hTB hpar (hcl _ hpar)
      have c3 := emit_tok hmK hTB hact
      have hpw : ‖toC (sideDir (exitEdge (hopEmit X) ((proc hX).parent F))) -
          toC (sideDir (hopEmit X F))‖ ≤ 2 * errB (diam X) K := by
        rw [← map_sub, LinearIsometryEquiv.norm_map]
        calc _ = ‖(sideDir (exitEdge (hopEmit X) ((proc hX).parent F)) -
              sideDir ((proc hX).labelAt K ((proc hX).parent F))) -
            (sideDir (hopEmit X F) - sideDir ((proc hX).labelAt K ((proc hX).parent F)))‖ := by
              congr 1; abel
          _ ≤ _ := (norm_sub_le _ _).trans (by linarith)
      calc _ = ‖(toC (sideDir (exitEdge (hopEmit X) r)) - toC (sideDir (lab hX K m F))) +
            (toC (sideDir (exitEdge (hopEmit X) ((proc hX).parent F))) -
              toC (sideDir (hopEmit X F)))‖ := by congr 1; ring
        _ ≤ _ := (norm_add_le _ _).trans (by linarith)
  · intro ab hab
    have hs := (entry_facts htri hsides hr).1
    have hd := hdist F hF' ab hab _ hs
    have h6' : (faceSize X F : ℝ) ≤ 6 := by exact_mod_cast h6
    rw [← dist_eq_norm, hlab]
    calc dist ab.1 (toC ((proc hX).labelAt K r).1)
        ≤ dist ab.1 (side X r).1 + dist (side X r).1 (toC ((proc hX).labelAt K r).1) :=
          dist_triangle _ _ _
      _ ≤ 6 + disB (diam X) K := by
          refine add_le_add (hd.trans h6') ?_
          simp only [dist_toC]
          rw [dist_comm]; exact a2
      _ ≤ _ := by linarith

end Analytic

end Sat

end Erdos99

end

end SaturationMarks

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `SaturationMarked`
-/

section SaturationMarked

/-!
# Saturated marked good faces (Verification Guide §10)

The token process of §9 is run once more (`hopProcess` with the exit edges `hopEmit`), and stopped
at a round whose live frontier is small.  The good faces are the pentagons and hexagons that
received only good tokens and are full: an ordinary pentagon has one arrival, a hexagon two, an
activated pentagon two arrivals and has emitted.  The marked ports are the entry edges of the
arrivals (and the exit edge of an activated pentagon), and the label of a good face is the source
label of an arrival that was not passed on.

* `saturation_marked`: eventually there are good faces with a marking at the cutoff `a D`, source
  labels of tolerance `tol`, at most `ε D` omitted pentagons and hexagons, and no stubs ending at
  unit hull sides or at marked ports.

The ingredients are `SaturationProcess` (the faces, the injectivity of the labels and the
absence of stubs), `SaturationCount` (the count of the omitted faces by token conservation),
`SaturationLabels` and `SaturationMarks` (the local capacity, the marking and the source
labels), together with the token bound, the bound on discarded tokens and the cap capacity of
`HopEmissionMain`.
-/

open scoped BigOperators Real
open Filter Topology

@[expose] public noncomputable section

open Classical

namespace Erdos99

open Propagation

namespace Sat

/-- **Cap arrivals of the track-following process**: the good tokens reaching caps are bounded by
the cap capacity, the others are discarded. -/
lemma capArr_le {X : Finset Plane} (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X)
    (hsides : ∀ G ∈ exceptionalFaces X, (orientedSides X G).Nonempty) {K : ℕ}
    (hTB : ∀ t, (proc hX).Timed K t → ¬ hopBad hX K t →
      (∀ p, t = Sum.inl p → p ∈ unitHullSides X) →
      (∀ G, t = Sum.inr G → G ∈ exceptionalFaces X) → TokBound hX K K t) {B : ℝ}
    (hcap : ∀ (S : Finset ((Plane × Plane) ⊕ Set ℂ))
      (q lab : (Plane × Plane) ⊕ Set ℂ → Plane × Plane), Set.InjOn q S → Set.InjOn lab S →
      (∀ i ∈ S, q i ∈ X ×ˢ X ∧ Initial X (q i) ∧ dist (q i).1 (q i).2 = 1 ∧
        hopDest X (q i) = .cap) →
      (∀ i ∈ S, lab i ∈ unitHullSides X ∧
        ‖sideDir (q i) - sideDir (lab i)‖ ≤ diam X ^ (-(3 / 2 * scaleExp K)) ∧
        dist (lab i).1 (hopEnd X (q i)).1 ≤ diam X ^ (1 - scaleExp K)) →
      (S.card : ℝ) ≤ B) :
    ((proc hX).capArr (K + 1) : ℝ) ≤ B + (proc hX).numBad (hopBad hX K) := by
  set P := proc hX
  have hemit := hopEmit_mem' hsides
  rw [P.capArr_succ_eq_card, ← Finset.card_filter_add_card_filter_not (hopBad hX K)]
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
  have hbadcap : (((P.capTokens K).filter (hopBad hX K)).card : ℝ) ≤ P.numBad (hopBad hX K) := by
    exact_mod_cast card_filter_bad_le P _ _ (fun t ht => by
      have f := capTokens_facts hX htri hsides ht
      exact ⟨f.2.2.2.2.2.2.1, fun G hG =>
        (Set.Finite.mem_toFinset _).2 (f.2.2.2.2.2.2.2 G hG)⟩)
  linarith

/-- The errors of the saturated process are eventually small: for every `c > 0`, eventually the
direction error, the label tolerance and the relative displacement are at most `c`. -/
lemma eventually_errors_small (K : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ D : ℝ in atTop, errB D K + (2 * (2 * disB D K + 6) / D + roundErr D) ≤ c ∧
      disB D K + 6 ≤ c * D := by
  have he := scaleExp_pos K
  have he1 := scaleExp_le K
  have ht := tendsto_rpow_neg_atTop (y := scaleExp K) he
  filter_upwards [eventually_ge_atTop 1, ht.eventually (ge_mem_nhds (show (0 : ℝ) < c / 89 by
    positivity))] with D hD hx
  have hD0 : 0 < D := by linarith
  set x := D ^ (-scaleExp K) with hxdef
  have hx0 : 0 ≤ x := by positivity
  have e1 : errB D K ≤ x := Real.rpow_le_rpow_of_exponent_le hD (by linarith)
  have hd : disB D K = x * D := by
    show D ^ (1 - scaleExp K) = D ^ (-scaleExp K) * D
    rw [show (1 - scaleExp K) = -scaleExp K + 1 by ring, Real.rpow_add hD0, Real.rpow_one]
  have hinv : 1 / D ≤ x := by
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hD (by linarith)
  have hxD : 1 ≤ x * D := by
    have := mul_le_mul_of_nonneg_right hinv hD0.le
    rwa [one_div, inv_mul_cancel₀ hD0.ne'] at this
  have e2 : 2 * (2 * disB D K + 6) / D ≤ 16 * x := by
    rw [hd]
    have : 2 * (2 * (x * D) + 6) / D = 4 * x + 12 * (1 / D) := by field_simp; ring
    rw [this]; linarith
  have e3 : roundErr D ≤ 72 * x := by
    refine (roundErr_le hD).trans ?_
    have : D ^ (-(1 / 9 : ℝ)) ≤ x := Real.rpow_le_rpow_of_exponent_le hD (by linarith)
    linarith
  refine ⟨by linarith, ?_⟩
  rw [hd]
  have : x * D + 6 ≤ 7 * (x * D) := by linarith
  have h2 : 7 * x ≤ c := by linarith
  nlinarith

end Sat

/-- **Saturated marked good faces** (Verification Guide §10). -/
theorem saturation_marked {ε a tol : ℝ} (hε : 0 < ε) (ha : 0 < a) (htol : 0 < tol) :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∃ (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane)),
        IsMarking X (a * diam X) G mk ∧ IsLabelled X tol G mk ∧
        (G.omittedSmall : ℝ) ≤ ε * diam X ∧
        stubsTo X (a * diam X) G mk G.good (UnitEnd X) = ∅ ∧
        stubsTo X (a * diam X) G mk G.good (MarkedEnd G mk) = ∅ := by
  -- parameters
  set η : ℝ := ε / 10 with hηdef
  have hη : 0 < η := by positivity
  set K : ℕ := ⌈8 * π / ε⌉₊ + 1 with hKdef
  have hK0 : 0 < K := by omega
  have hKgt : 8 * π / ε < K := by
    rw [hKdef]; push_cast; linarith [Nat.le_ceil (8 * π / ε)]
  set ε1 : ℝ := η / (4 * 2 ^ K) with hε1def
  have hε1 : 0 < ε1 := by positivity
  set c : ℝ := min (1 / 10) (tol / 3) with hcdef
  have hc : 0 < c := lt_min (by norm_num) (by positivity)
  -- eventual facts
  have hlongs := (Finset.eventually_all (Finset.range (K + 1))).2 (fun m _ =>
    long_labelled_exits (c := 1 / 2) (M := 1) (scaleExp_pos m) (scaleExp_le m) (by norm_num) hε1)
  have hsched := tendsto_minDiam.eventually (eventually_schedule K)
  have herr := tendsto_minDiam.eventually (Sat.eventually_errors_small K hc)
  have hL1 := tendsto_minDiam.eventually (eventually_mul_rpow_le 1 (α := 19 / 20) (δ := a)
    (by norm_num) ha)
  have hL2 := tendsto_minDiam.eventually (eventually_mul_rpow_le (1 / 2)
    (α := 1 - scaleExp K) (δ := a) (by linarith [scaleExp_pos K]) ha)
  filter_upwards [hlongs, hsched, herr, hL1, hL2, short_unit_sources _ hε1,
    good_cap_tokens_le (scaleExp_pos K) (scaleExp_le K) (by positivity : (0 : ℝ) < η / 4),
    eventually_roundData_rate, exceptionalFace_unitPolygon_sides, exists_almostOpposite_side,
    exceptionalFace_orientedSides_dist_le, exceptionalFace_marked_card_le, card_orientedSides,
    stability_bounds η hη, lockingDefect_nonneg, eventually_ge_atTop 2, Sat.stubs_unit_empty,
    Sat.stubs_marked_empty]
    with n hlong hsch herr hL1 hL2 hshort hcap hround hpoly hopp hdist hcapF hcard hstab hΔ hn2
      hstubU hstubM
  intro hfm X hX htri
  rw [← hX.diam_eq] at hsch herr hL1 hL2
  obtain ⟨hD1, hstep, -, -⟩ := hsch
  obtain ⟨herr, hvert⟩ := herr
  simp only [one_mul] at hL1
  have hsep := hX.1.2
  obtain ⟨O, η', hR⟩ := hround X hX
  have hsides : ∀ G ∈ exceptionalFaces X, (orientedSides X G).Nonempty := by
    intro G hG
    obtain ⟨hNZ, Q, -, hall⟩ := hpoly hfm X hX G hG
    exact ⟨_, hall 0⟩
  have h1920 : diam X ^ (19 / 20 : ℝ) ≤ disB (diam X) 0 :=
    Real.rpow_le_rpow_of_exponent_le hD1 (by linarith [scaleExp_le 0])
  have hD : 0 < diam X := by linarith
  -- the token bound
  have hTB : ∀ t, (Sat.proc hsep).Timed K t → ¬ hopBad hsep K t →
      (∀ p, t = Sum.inl p → p ∈ unitHullSides X) →
      (∀ G, t = Sum.inr G → G ∈ exceptionalFaces X) → TokBound hsep K K t :=
    fun t ht hg h1 h2 => tokenBound hsep htri hsides hR hD1 hstep h1920 (hopp hfm X hX)
      (hdist hfm X hX) K le_rfl t ht hg h1 h2
  -- the round with a small frontier
  obtain ⟨m, hmK, hfront⟩ := Sat.exists_frontier_le hsep hK0
  have hmK' : m ≤ K := hmK.le
  -- the error bounds
  have htheta : Sat.theta X K (100 * diam X ^ (-(2 / 9 : ℝ))) =
      2 * (2 * disB (diam X) K + 6) / diam X + roundErr (diam X) := rfl
  have hsmall : errB (diam X) K + Sat.theta X K (100 * diam X ^ (-(2 / 9 : ℝ))) ≤ 3 / 10 := by
    rw [htheta]; linarith [min_le_left (1 / 10 : ℝ) (tol / 3)]
  have htol' : 3 * (errB (diam X) K + Sat.theta X K (100 * diam X ^ (-(2 / 9 : ℝ)))) ≤ tol := by
    rw [htheta]; linarith [min_le_right (1 / 10 : ℝ) (tol / 3)]
  have hvert' : disB (diam X) K + 6 ≤ tol * diam X := by
    have : c * diam X ≤ tol * diam X :=
      mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (by linarith)) hD.le
    linarith
  have hcutL : cutB (diam X) K ≤ a * diam X := by unfold cutB disB at *; linarith
  refine ⟨Sat.faces hsep K m, Sat.mk hsep m, ?_, ?_, ?_, hstubU hfm X hX htri hsides K m _,
    hstubM hfm X hX htri hsides K m _⟩
  · exact Sat.isMarking htri hsides hmK' hTB hR (hdist hfm X hX) hsmall hD1 hL1 hcutL
  · exact Sat.isLabelled htri hsides hmK' hTB hR (hdist hfm X hX) hsmall htol' hvert'
  · -- the count of the omitted faces
    have hcap2 : ∀ F ∈ exceptionalFaces X, faceSize X F ≤ 6 →
        (((Sat.proc hsep).arrivals m F).filter (fun t => ¬ hopBad hsep K t)).card ≤ 2 :=
      fun F hF h6 => Sat.card_good_arrivals_le_two htri hsides hmK' hTB hR (hdist hfm X hX)
        (hcapF hfm X hX) hsmall hF h6
    have hΔ0 := hΔ hfm X hX htri
    have hcount := Sat.omitted_count hsep K m htri hsides (hcard hfm X hX) hcap2 hΔ0
    -- discarded tokens
    have hnum := hop_numBad_le hsep htri hsides hR hD1 hstep h1920 (hopp hfm X hX)
      (hdist hfm X hX) (fun m hm S q lab => hlong m (Finset.mem_range.2 (by omega)) hfm X hX
        htri S q lab) (hshort hfm X hX htri)
    have hsh := hshort hfm X hX htri
    have hprod : (2 : ℝ) ^ K * (2 * ε1 * diam X) = η / 2 * diam X := by
      rw [hε1def]; field_simp; ring
    rw [hprod] at hnum
    have hε1le : ε1 * diam X ≤ η / 4 * diam X := by
      refine mul_le_mul_of_nonneg_right ?_ hD.le
      rw [hε1def]
      have h2K : (1 : ℝ) ≤ 2 ^ K := one_le_pow₀ (by norm_num)
      exact div_le_div_of_nonneg_left hη.le (by norm_num) (by linarith)
    have hnb : ((Sat.proc hsep).numBad (hopBad hsep K) : ℝ) ≤ η * diam X := by
      have : (((unitHullSides X).filter
          (fun p => diam X ^ (19 / 20 : ℝ) ≤ srcLen X s(p.1, p.2))).card : ℝ) ≤ ε1 * diam X := hsh
      change ((hopProcess hsep (hopEmit X)).numBad (hopBad hsep K) : ℝ) ≤ η * diam X
      linarith
    -- cap arrivals
    have hcapK := Sat.capArr_le hsep htri hsides hTB (hcap hfm X hX htri)
    have hcapm : ((Sat.proc hsep).capArr (m + 1) : ℝ) ≤ (Sat.proc hsep).capArr (K + 1) := by
      exact_mod_cast (Sat.proc hsep).capArr_mono' (by omega)
    -- the frontier
    have h2 : 2 ≤ X.card := by rw [hX.1.1]; exact hn2
    have hpf := pentagons_add_heptagons_le_pi_mul_diam hsep h2 hΔ0
    have hKpos : (0 : ℝ) < K := by exact_mod_cast hK0
    have hfr : Sat.frontier hsep m ≤ ε / 8 * diam X := by
      have h1 : Sat.frontier hsep m * K ≤ π * diam X := hfront.trans hpf
      have hK8 : 8 * π ≤ ε * K := by have := (div_lt_iff₀ hε).1 hKgt; linarith
      have h3 := mul_le_mul_of_nonneg_right hK8 hD.le
      have h2' : Sat.frontier hsep m * K ≤ ε / 8 * diam X * K := by linarith
      exact le_of_mul_le_mul_right h2' hKpos
    -- high faces and returns
    have hI := (hstab hfm X hX htri).2.2.2.2.2
    have hρ : (0 : ℝ) ≤ returnExcess X := Nat.cast_nonneg _
    have hηD : η * diam X = ε / 10 * diam X := by rw [hηdef]
    linarith

end Erdos99

end

end SaturationMarked

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `SaturationWindow`
-/

section SaturationWindow

/-!
# The degree window after saturation (Verification Guide §10, minimum short degrees)

At a labelled good face the marked ports point along the source tangent `τ`.  If the face has too
few short ports at the cutoff `a D`, then at least three (pentagons, hexagons) or one (activated
pentagons) of its unmarked sides lie on tracks with at least `a D` rhombi, and closure of the face
gives one of the equations `k τ + Z ≈ 0` or `|k τ + Z| ≈ 1`, with `Z` the sum of these long side
vectors.  The long sides cluster near boundedly many directions (`long_sides_clustered`), and the
equations pin `τ` (`pinned_polys_few`); with injective labels such faces are few.

* `pinned_polys_finset`: the counting engine for a finite set of centre polynomials;
* `windowPolyA`, `windowPolyB`: the polynomials of the two equations, `k ζ + z` and
  `k z̄ ζ² + (k² + |z|² - 1) ζ + k z` (whose value at a unit `ζ` is `ζ (|k ζ + z|² - 1)`);
* `window_face_equation`: the closure equation at a good face violating the degree window;
* `window_failures_few`: for every cutoff fraction `a > 0` and `ε > 0` there is a tolerance
  `tol₀ > 0` such that, eventually, for every marking at the cutoff `a D` with source labels of
  tolerance `tol₀`, at most `ε D` good faces violate the lower bound of the degree window.
-/

open scoped BigOperators Real
open Filter Polynomial ComplexConjugate

@[expose] public noncomputable section

open Classical

namespace Erdos99

open LocalCharge QuadraticResponse DirectionPinning EstablishedExternalResults

/-! ## The counting engine for a finite set of centres -/

/-- **Pinning by finitely many centre polynomials.**  For a degree bound `d`, a bound `N` on the
number of centres and a lower bound `m₀ > 0` on their coefficient vectors, for every `ε > 0` there
is a tolerance `r > 0` such that eventually every set of counterclockwise hull sides whose
directions are `r`-approximate roots of one of the centres has at most `ε D` elements. -/
theorem pinned_polys_finset (d N : ℕ) {ε m₀ : ℝ} (hε : 0 < ε) (hm₀ : 0 < m₀) :
    ∃ r > 0, ∀ᶠ n in atTop, ∀ X, IsOptimal n X →
      ∀ T : Finset ℂ[X], T.card ≤ N → (∀ p ∈ T, p.natDegree ≤ d ∧ m₀ ≤ ‖polyCoeffs d p‖) →
      ∀ A ⊆ ccwHullSides X, (∀ q ∈ A, ∃ p ∈ T, ‖p.eval (toC (sideDir q))‖ < r) →
      (A.card : ℝ) ≤ ε * diam X := by
  obtain ⟨r, hr, μ, hμ, h⟩ := pinned_polys_few d N hε hm₀
  refine ⟨r, hr, ?_⟩
  filter_upwards [h] with n hn X hX T hTc hT A hA hpin
  rcases T.eq_empty_or_nonempty with rfl | ⟨t₀, ht₀⟩
  · have hA0 : A = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun q hq => ?_
      obtain ⟨p, hp, -⟩ := hpin q hq
      exact Finset.notMem_empty p hp
    rw [hA0, Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg hε.le Metric.diam_nonneg
  set p₀ : Fin N → ℂ[X] := fun j =>
    if h : (j : ℕ) < T.card then (T.equivFin.symm ⟨j, h⟩ : ℂ[X]) else t₀ with hp₀def
  have hp₀T : ∀ j, p₀ j ∈ T := by
    intro j
    simp only [hp₀def]
    split_ifs
    · exact (T.equivFin.symm _).2
    · exact ht₀
  have hTp₀ : ∀ p (hp : p ∈ T), ∃ j, p₀ j = p := by
    intro p hp
    set i := T.equivFin ⟨p, hp⟩
    refine ⟨⟨i, lt_of_lt_of_le i.2 hTc⟩, ?_⟩
    simp only [hp₀def, dif_pos i.2]
    simp [i]
  refine hn X hX p₀ (fun j => (hT _ (hp₀T j)).2) A hA (fun q hq => ?_)
  obtain ⟨p, hp, hev⟩ := hpin q hq
  obtain ⟨j, hj⟩ := hTp₀ p hp
  exact ⟨j, p, (hT p hp).1, by rw [hj, sub_self, norm_zero]; exact hμ, hev⟩

/-! ## The two window polynomials -/

/-- The polynomial `k ζ + z` of the equation `k τ + Z ≈ 0`. -/
def windowPolyA (k : ℝ) (z : ℂ) : ℂ[X] := C (k : ℂ) * X + C z

/-- The polynomial `k z̄ ζ² + (k² + |z|² - 1) ζ + k z` of the equation `|k τ + Z| ≈ 1`. -/
def windowPolyB (k : ℝ) (z : ℂ) : ℂ[X] :=
  C ((k : ℂ) * conj z) * X ^ 2 + C ((k : ℂ) ^ 2 + ((‖z‖ ^ 2 : ℝ) : ℂ) - 1) * X + C ((k : ℂ) * z)

lemma natDegree_windowPolyA_le (k : ℝ) (z : ℂ) : (windowPolyA k z).natDegree ≤ 2 := by
  unfold windowPolyA
  compute_degree
  all_goals norm_num

lemma natDegree_windowPolyB_le (k : ℝ) (z : ℂ) : (windowPolyB k z).natDegree ≤ 2 := by
  unfold windowPolyB
  compute_degree

lemma windowPolyA_eval (k : ℝ) (z τ : ℂ) : (windowPolyA k z).eval τ = (k : ℂ) * τ + z := by
  simp [windowPolyA]

/-- At a unit `ζ`, the second window polynomial is `ζ (|k ζ + z|² - 1)`. -/
lemma windowPolyB_eval (k : ℝ) (z : ℂ) {τ : ℂ} (hτ : ‖τ‖ = 1) :
    (windowPolyB k z).eval τ = τ * (((‖(k : ℂ) * τ + z‖ ^ 2 : ℝ) : ℂ) - 1) := by
  have h1 : τ * conj τ = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hτ]; norm_num
  have h2 : ((‖(k : ℂ) * τ + z‖ ^ 2 : ℝ) : ℂ) = ((k : ℂ) * τ + z) * conj ((k : ℂ) * τ + z) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h3 : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [windowPolyB, eval_add, eval_mul, eval_C, eval_pow, eval_X]
  rw [h2, h3]
  simp only [map_add, map_mul, Complex.conj_ofReal]
  linear_combination (-(k : ℂ) ^ 2 * τ - (k : ℂ) * z) * h1

lemma norm_windowPolyB_eval_le (k : ℝ) (z : ℂ) {τ : ℂ} (hτ : ‖τ‖ = 1) :
    ‖(windowPolyB k z).eval τ‖ ≤ |‖(k : ℂ) * τ + z‖ - 1| * (‖(k : ℂ) * τ + z‖ + 1) := by
  rw [windowPolyB_eval k z hτ, norm_mul, hτ, one_mul]
  have e : ((‖(k : ℂ) * τ + z‖ ^ 2 : ℝ) : ℂ) - 1 =
      (((‖(k : ℂ) * τ + z‖ - 1) * (‖(k : ℂ) * τ + z‖ + 1) : ℝ) : ℂ) := by
    push_cast; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖(k : ℂ) * τ + z‖ + 1)]

lemma one_le_norm_windowPolyA {k : ℝ} (hk : k = 1 ∨ k = 2) (z : ℂ) :
    1 ≤ ‖polyCoeffs 2 (windowPolyA k z)‖ := by
  refine le_trans ?_ (norm_coeff_le_norm_polyCoeffs 2 _ (by norm_num : 1 ≤ 2))
  have : (windowPolyA k z).coeff 1 = k := by simp [windowPolyA, coeff_C]
  rw [this, Complex.norm_real]
  rcases hk with rfl | rfl <;> norm_num

lemma norm_windowPolyB_ge (k : ℝ) (z : ℂ) :
    |k ^ 2 + ‖z‖ ^ 2 - 1| ≤ ‖polyCoeffs 2 (windowPolyB k z)‖ := by
  refine le_trans ?_ (norm_coeff_le_norm_polyCoeffs 2 _ (by norm_num : 1 ≤ 2))
  have : (windowPolyB k z).coeff 1 = ((k ^ 2 + ‖z‖ ^ 2 - 1 : ℝ) : ℂ) := by
    rw [windowPolyB, coeff_add, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
    push_cast; simp
  rw [this, Complex.norm_real, Real.norm_eq_abs]

/-! ## Three long sides cannot nearly cancel (complex form) -/

lemma inner_toC_symm (z τ : ℂ) : inner ℝ (toC.symm z) (toC.symm τ) = (z * conj τ).re := by
  rw [LinearIsometryEquiv.inner_map_map, Complex.inner]
  simp [Complex.mul_re]; ring

/-- **Three macroscopic ports cannot nearly cancel** (Verification Guide §6.3), for unit complex
numbers with projection at most `1/2 - k` on a unit tangent `τ`. -/
lemma three_ports_noncancel_complex {z1 z2 z3 τ : ℂ} {k : ℝ} (hk : 0 < k) (h1 : ‖z1‖ = 1)
    (h2 : ‖z2‖ = 1) (h3 : ‖z3‖ = 1) (hτ : ‖τ‖ = 1) (i1 : (z1 * conj τ).re ≤ 1 / 2 - k)
    (i2 : (z2 * conj τ).re ≤ 1 / 2 - k) (i3 : (z3 * conj τ).re ≤ 1 / 2 - k) :
    min 1 k ≤ ‖z1 + z2 + z3‖ := by
  have h := BoundaryPort.three_ports_noncancel (u1 := toC.symm z1) (u2 := toC.symm z2) (u3 := toC.symm z3)
    (τ := toC.symm τ) hk (by rw [LinearIsometryEquiv.norm_map]; exact h1)
    (by rw [LinearIsometryEquiv.norm_map]; exact h2) (by rw [LinearIsometryEquiv.norm_map]; exact h3)
    (by rw [LinearIsometryEquiv.norm_map]; exact hτ) (by rw [inner_toC_symm]; exact i1)
    (by rw [inner_toC_symm]; exact i2) (by rw [inner_toC_symm]; exact i3)
  rwa [← map_add, ← map_add, LinearIsometryEquiv.norm_map] at h

/-! ## The closure equation at a face violating the degree window -/

/-- **The closure equation at a window failure.**  At a good face `F` with fewer than
`marks F + 2` short ports, either `‖k τ + Z‖ ≤ tol`, or there is a unit vector `u` (the side of the
single unmarked short port) with `‖k τ + u + Z‖ ≤ tol`; in the second case `F` has
`faceSize - marks - 1` long sides.  Here `τ` is the label direction, `k` the multiplicity and `Z`
the long-side sum. -/
theorem window_face_equation :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      ∀ (L tol : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane))
        (lab : Set ℂ → Plane × Plane), IsMarking X L G mk → LabelledBy X tol G mk lab →
      ∀ F ∈ G.good, ¬ G.marks F + 2 ≤ shortDeg X L (Sum.inl F) →
        ‖(G.kMult F : ℂ) * labDir lab F + longSum X L F‖ ≤ tol ∨
        ∃ u : ℂ, ‖u‖ = 1 ∧ ‖(G.kMult F : ℂ) * labDir lab F + u + longSum X L F‖ ≤ tol ∧
          (longSides X L F).card + G.marks F + 1 = faceSize X F := by
  filter_upwards [markedSum_short_add_longSum, card_filter_orientedSides, face_side_facts,
    card_longSides] with n hzero hcardf hside hcl hfm X hX L tol G mk lab hmk hlab F hFg hfail
  have hsub := (hmk F hFg).1
  have hmc := (hmk F hFg).2
  have hFe : F ∈ exceptionalFaces X := (mem_exceptionalFinset hX.1.2).1 (G.good_subset hFg)
  set N := shortPorts X L F \ mk F with hN
  have hNc : N.card + G.marks F = shortDeg X L (Sum.inl F) := by
    rw [hN, ← hmc, Finset.card_sdiff_add_card_eq_card hsub, card_shortPorts]
  have hports : ∀ f ∈ N, IsPort X (Sum.inl F) f :=
    fun f hf => (Finset.mem_filter.1 (Finset.sdiff_subset hf)).2.1
  have hc := hcardf hfm X hX F hFe N hports
  have h0 := hzero hfm X hX L F hFe
  rw [← Finset.union_sdiff_of_subset hsub, markedSum_union Finset.disjoint_sdiff, ← hN] at h0
  have hl := (hlab.2 F hFg).2.1
  rw [GoodFaces.markMult_eq] at hl
  have key : ∀ v : ℂ, markedSum X F (mk F) + v + longSum X L F = 0 →
      ‖(G.kMult F : ℂ) * labDir lab F + v + longSum X L F‖ ≤ tol := by
    intro v hv
    calc _ = ‖-(markedSum X F (mk F) - (G.kMult F : ℂ) * toC (sideDir (lab F)))‖ := by
          congr 1; rw [labDir]; linear_combination hv
      _ ≤ tol := by rw [norm_neg]; exact hl
  have hN1 : N.card ≤ 1 := by omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hN1 with h | h
  · left
    have hN0 : N = ∅ := Finset.card_eq_zero.1 h
    have hms : markedSum X F N = 0 := by rw [hN0, markedSum]; simp
    have := key 0 (by rw [hms] at h0; linear_combination h0)
    simpa using this
  · right
    rw [h] at hc
    obtain ⟨x, hx⟩ := Finset.card_eq_one.1 hc
    have hxs : x ∈ orientedSides X F := by
      have : x ∈ (orientedSides X F).filter
          (fun ab => ∃ f ∈ N, Sym2.map toC f = s(ab.1, ab.2)) := by rw [hx]; simp
      exact (Finset.mem_filter.1 this).1
    have hNsum : markedSum X F N = x.2 - x.1 := by rw [markedSum, hx, Finset.sum_singleton]
    refine ⟨x.2 - x.1, (hside hfm X hX G F hFg).2 x hxs, key _ (by rw [← hNsum]; exact h0), ?_⟩
    have := hcl hfm X hX L F hFe
    rw [card_shortPorts] at this
    omega

/-! ## Few window failures -/

/-- **Few failures of the degree window** (Verification Guide §10).  For every cutoff fraction
`a > 0` and every `ε > 0` there is a tolerance `tol₀ > 0` such that, eventually, for every marking at
the cutoff `a D` with source labels of tolerance `tol₀`, at most `ε D` good faces have fewer than
`marks F + 2` short ports. -/
theorem window_failures_few {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) :
    ∃ tol₀ > 0, ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      ¬ HasUnitTriangle X →
      ∀ (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane)), IsMarking X (a * diam X) G mk →
        IsLabelled X tol₀ G mk →
        ((G.good.filter (fun F => ¬ G.marks F + 2 ≤ shortDeg X (a * diam X) (Sum.inl F))).card :
          ℝ) ≤ ε * diam X := by
  obtain ⟨Nc, hclus⟩ := long_sides_clustered ha
  obtain ⟨κ', hκ', c3, hc3, hmarg⟩ := long_side_margin' ha
  set cm := min 1 κ' with hcmdef
  have hcm0 : 0 < cm := lt_min one_pos hκ'
  have hcm1 : cm ≤ 1 := min_le_left _ _
  set m₀ := min 1 (cm ^ 2 / 4) with hm₀def
  have hm₀ : 0 < m₀ := lt_min one_pos (by positivity)
  obtain ⟨r, hr, hpin⟩ := pinned_polys_finset 2 (2 * 7 ^ Nc + 2 * 7 ^ Nc) (half_pos hε) hm₀
  set εc := min (r / 100) (cm / 24) with hεcdef
  have hεc0 : 0 < εc := lt_min (by positivity) (by positivity)
  have hεc1 : εc ≤ r / 100 := min_le_left _ _
  have hεc2 : εc ≤ cm / 24 := min_le_right _ _
  obtain ⟨M, hclusM⟩ := hclus εc hεc0
  refine ⟨min c3 (r / 100), lt_min hc3 (by positivity), ?_⟩
  filter_upwards [hpin, hclusM, hmarg, window_face_equation, face_side_facts,
    eventually_diam_ge (2 * |M| / ε), eventually_diam_ge 1] with
    n hpin hclusM hmarg hface hfacts hDbig hD1
  intro hfm X hX htri G mk hmk hlab
  set D := diam X with hDdef
  set L := a * D with hLdef
  have hD : 0 < D := lt_of_lt_of_le one_pos (hD1 X hX)
  obtain ⟨lab, hlab⟩ := isLabelled_iff.1 hlab
  set tol := min c3 (r / 100) with htoldef
  have htol3 : tol ≤ c3 := min_le_left _ _
  have htolr : tol ≤ r / 100 := min_le_right _ _
  have htol0 : 0 ≤ tol := le_of_lt (lt_min hc3 (by positivity))
  obtain ⟨U, hU, Bad, hBad, hcl⟩ := hclusM hfm X hX htri
  set Fail := G.good.filter (fun F => ¬ G.marks F + 2 ≤ shortDeg X L (Sum.inl F)) with hFaildef
  set Exc := Fail.filter (fun F => F ∈ Bad) with hExcdef
  set Rest := Fail \ Exc with hRestdef
  have hRestgood : Rest ⊆ G.good := fun F hF =>
    (Finset.mem_filter.1 (Finset.mem_sdiff.1 hF).1).1
  set A := Rest.image lab with hAdef
  have hAcard : A.card = Rest.card := Finset.card_image_of_injOn (hlab.1.mono hRestgood)
  have hA : A ⊆ ccwHullSides X := fun p hp => by
    obtain ⟨F, hF, rfl⟩ := Finset.mem_image.1 hp
    exact (Finset.mem_filter.1 (hlab.2 F (hRestgood hF)).1).1
  -- the centre polynomials
  set K2 : Finset ℝ := {1, 2} with hK2
  set T : Finset ℂ[X] := (K2 ×ˢ sumCentres U).image (fun kz => windowPolyA kz.1 kz.2) ∪
    ((K2 ×ˢ sumCentres U).filter (fun kz => kz.1 = 2 ∨ cm / 2 ≤ ‖kz.2‖)).image
      (fun kz => windowPolyB kz.1 kz.2) with hTdef
  have hsc : (sumCentres U).card ≤ 7 ^ Nc :=
    (card_sumCentres_le U).trans (Nat.pow_le_pow_right (by norm_num) hU)
  have hK2c : K2.card ≤ 2 := Finset.card_le_two
  have hTc : T.card ≤ 2 * 7 ^ Nc + 2 * 7 ^ Nc := by
    refine (Finset.card_union_le _ _).trans (add_le_add ?_ ?_)
    · refine Finset.card_image_le.trans ?_
      rw [Finset.card_product]; exact Nat.mul_le_mul hK2c hsc
    · refine Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans ?_)
      rw [Finset.card_product]; exact Nat.mul_le_mul hK2c hsc
  have hK2mem : ∀ k ∈ K2, k = 1 ∨ k = 2 := by
    intro k hk; simpa [hK2] using hk
  have hTprop : ∀ p ∈ T, p.natDegree ≤ 2 ∧ m₀ ≤ ‖polyCoeffs 2 p‖ := by
    intro p hp
    rcases Finset.mem_union.1 hp with hp | hp
    · obtain ⟨⟨k, z⟩, hkz, rfl⟩ := Finset.mem_image.1 hp
      have hk := hK2mem k (Finset.mem_product.1 hkz).1
      exact ⟨natDegree_windowPolyA_le k z,
        (min_le_left _ _).trans (one_le_norm_windowPolyA hk z)⟩
    · obtain ⟨⟨k, z⟩, hkz, rfl⟩ := Finset.mem_image.1 hp
      obtain ⟨hkz, hcase⟩ := Finset.mem_filter.1 hkz
      have hk := hK2mem k (Finset.mem_product.1 hkz).1
      refine ⟨natDegree_windowPolyB_le k z, le_trans ?_ (norm_windowPolyB_ge k z)⟩
      simp only at hcase
      have h3 : (3 : ℝ) ≤ |2 ^ 2 + ‖z‖ ^ 2 - 1| := by
        rw [abs_of_nonneg (by nlinarith [sq_nonneg ‖z‖])]; nlinarith [sq_nonneg ‖z‖]
      rcases hcase with rfl | hz
      · exact (min_le_left _ _).trans (by linarith)
      · have hz2 : cm ^ 2 / 4 ≤ ‖z‖ ^ 2 := by nlinarith
        rcases hk with rfl | rfl
        · rw [show (1 : ℝ) ^ 2 + ‖z‖ ^ 2 - 1 = ‖z‖ ^ 2 by ring, abs_of_nonneg (by positivity)]
          exact (min_le_right _ _).trans hz2
        · exact (min_le_left _ _).trans (by linarith)
  -- every label of `Rest` is pinned
  have hpinA : ∀ q ∈ A, ∃ p ∈ T, ‖p.eval (toC (sideDir q))‖ < r := by
    intro q hq
    obtain ⟨F, hF, rfl⟩ := Finset.mem_image.1 hq
    obtain ⟨hFf, hFnot⟩ := Finset.mem_sdiff.1 hF
    obtain ⟨hFg, hfail⟩ := Finset.mem_filter.1 hFf
    have hnB : F ∉ Bad := fun h => hFnot (Finset.mem_filter.2 ⟨hFf, h⟩)
    have hFe : F ∈ exceptionalFaces X := (mem_exceptionalFinset hX.1.2).1 (G.good_subset hFg)
    obtain ⟨hcF, huF⟩ := hfacts hfm X hX G F hFg
    have hZ6 := norm_longSum_le (L := L) hcF huF
    have hτ := norm_labDir hlab hFg
    have hτe : labDir lab F = toC (sideDir (lab F)) := rfl
    -- the long sides are clustered
    have hlongcl : ∀ ab ∈ longSides X L F, ∃ u ∈ U, ‖(ab.2 - ab.1) - u‖ ≤ εc := by
      intro ab hab
      obtain ⟨e, he, hmap, -, hlong⟩ := longSide_edge hFe hab
      exact hcl F hFe hnB ab (Finset.mem_filter.1 hab).1 ⟨e, he, hmap, not_lt.1 hlong⟩
    have hcard6 : (longSides X L F).card ≤ 6 :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans hcF
    obtain ⟨z, hz, hzZ⟩ := sum_near_sumCentres (longSides X L F) (fun ab => ab.2 - ab.1) U
      hεc0.le hcard6 hlongcl
    have hzZ' : ‖longSum X L F - z‖ ≤ 6 * εc := by simpa [longSum] using hzZ
    have hk := G.kMult_cases F
    have hkK : G.kMult F ∈ K2 := by rcases hk with h | h <;> simp [hK2, h]
    -- the margin at the long sides of `F`
    have hmF : ∀ ab ∈ longSides X L F, ((ab.2 - ab.1) * conj (labDir lab F)).re ≤ 1 / 2 - κ' :=
      hmarg hfm X hX htri L tol G mk lab htol3 (fun _ _ _ _ _ => lt_or_ge _ _) hlab F hFg
    set k := G.kMult F with hkdef
    set τ := labDir lab F with hτdef
    set Z := longSum X L F with hZdef
    have hkτz : ‖(k : ℂ) * τ + z‖ ≤ 9 := by
      have h1 : ‖(k : ℂ) * τ‖ ≤ 2 := by
        rw [norm_mul, hτ, mul_one, Complex.norm_real, Real.norm_eq_abs]
        rcases hk with h | h <;> rw [h] <;> norm_num
      have h2 : ‖z‖ ≤ 6 + 6 * εc := by
        have := norm_sub_norm_le z Z
        rw [norm_sub_rev] at this; linarith
      have h3 : 6 * εc ≤ 1 := by
        have : εc ≤ 1 / 24 := hεc2.trans (by linarith)
        linarith
      calc _ ≤ ‖(k : ℂ) * τ‖ + ‖z‖ := norm_add_le _ _
        _ ≤ 9 := by linarith
    have hshift : ‖((k : ℂ) * τ + z) - ((k : ℂ) * τ + Z)‖ ≤ 6 * εc := by
      rw [add_sub_add_left_eq_sub, norm_sub_rev]; exact hzZ'
    rcases hface hfm X hX L tol G mk lab hmk hlab F hFg hfail with h | ⟨u, hu, h, hcount⟩
    · -- `k τ + Z ≈ 0`
      refine ⟨windowPolyA k z, Finset.mem_union_left _ (Finset.mem_image.2
        ⟨(k, z), Finset.mem_product.2 ⟨hkK, hz⟩, rfl⟩), ?_⟩
      rw [← hτe, windowPolyA_eval]
      calc ‖(k : ℂ) * τ + z‖ ≤ ‖(k : ℂ) * τ + Z‖ + ‖((k : ℂ) * τ + z) - ((k : ℂ) * τ + Z)‖ :=
            norm_le_norm_add_norm_sub' _ _
        _ ≤ tol + 6 * εc := add_le_add h hshift
        _ < r := by linarith
    · -- `|k τ + Z| ≈ 1`
      have hB : |‖(k : ℂ) * τ + z‖ - 1| ≤ tol + 6 * εc := by
        have e1 : |‖(k : ℂ) * τ + Z‖ - 1| ≤ tol := by
          have := abs_norm_sub_norm_le ((k : ℂ) * τ + Z) (-u)
          rw [norm_neg, hu, sub_neg_eq_add, add_right_comm] at this
          exact this.trans h
        have e2 := abs_norm_sub_norm_le ((k : ℂ) * τ + z) ((k : ℂ) * τ + Z)
        calc _ = |(‖(k : ℂ) * τ + z‖ - ‖(k : ℂ) * τ + Z‖) + (‖(k : ℂ) * τ + Z‖ - 1)| := by
              ring_nf
          _ ≤ |‖(k : ℂ) * τ + z‖ - ‖(k : ℂ) * τ + Z‖| + |‖(k : ℂ) * τ + Z‖ - 1| :=
              abs_add_le _ _
          _ ≤ 6 * εc + tol := add_le_add (e2.trans hshift) e1
          _ = tol + 6 * εc := by ring
      -- the centre is admissible
      have hadm : k = 2 ∨ cm / 2 ≤ ‖z‖ := by
        rcases hk with hk1 | hk2
        · right
          have hZcm : cm ≤ ‖Z‖ := by
            have hnh : F ∉ G.hex := by
              intro hh; rw [hkdef, GoodFaces.kMult, if_pos hh] at hk1; norm_num at hk1
            have hFg' := hFg
            simp only [GoodFaces.good, Finset.mem_union] at hFg'
            rcases hFg' with (hp | hh) | hac
            · -- an ordinary pentagon: three long sides
              have hm : G.marks F = 1 := by simp [GoodFaces.marks, hp]
              have h5 := (G.pent_sub F hp).2
              have h3 : (longSides X L F).card = 3 := by omega
              obtain ⟨x, y, w, hxy, hxw, hyw, hxyw⟩ := Finset.card_eq_three.1 h3
              have hsubF : longSides X L F ⊆ orientedSides X F := Finset.filter_subset _ _
              have hxL : x ∈ longSides X L F := by rw [hxyw]; simp
              have hyL : y ∈ longSides X L F := by rw [hxyw]; simp
              have hwL : w ∈ longSides X L F := by rw [hxyw]; simp
              have hZe : Z = (x.2 - x.1) + (y.2 - y.1) + (w.2 - w.1) := by
                rw [hZdef, longSum, hxyw, Finset.sum_insert (by simp [hxy, hxw]),
                  Finset.sum_pair hyw]
                ring
              rw [hZe]
              exact three_ports_noncancel_complex hκ' (huF x (hsubF hxL)) (huF y (hsubF hyL))
                (huF w (hsubF hwL)) hτ (hmF x hxL) (hmF y hyL) (hmF w hwL)
            · exact absurd hh hnh
            · -- an activated pentagon: one long side
              have hnp : F ∉ G.pent := fun hp => Finset.disjoint_left.1 G.disj hp hac
              have hm : G.marks F = 3 := by simp [GoodFaces.marks, hnp, hnh]
              have h5 := (G.act_sub F hac).2
              have h1 : (longSides X L F).card = 1 := by omega
              obtain ⟨x, hx⟩ := Finset.card_eq_one.1 h1
              have hxs : x ∈ orientedSides X F := by
                have : x ∈ longSides X L F := by rw [hx]; simp
                exact (Finset.mem_filter.1 this).1
              have : Z = x.2 - x.1 := by rw [hZdef, longSum, hx, Finset.sum_singleton]
              rw [this, huF x hxs]; exact hcm1
          have := norm_sub_norm_le Z z
          linarith
        · left; exact hk2
      refine ⟨windowPolyB k z, Finset.mem_union_right _ (Finset.mem_image.2
        ⟨(k, z), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hkK, hz⟩, hadm⟩, rfl⟩), ?_⟩
      rw [← hτe]
      calc ‖(windowPolyB k z).eval τ‖ ≤ |‖(k : ℂ) * τ + z‖ - 1| * (‖(k : ℂ) * τ + z‖ + 1) :=
            norm_windowPolyB_eval_le k z hτ
        _ ≤ (tol + 6 * εc) * 10 :=
            mul_le_mul hB (by linarith) (by positivity) (by positivity)
        _ < r := by nlinarith
  have key := hpin X hX T hTc hTprop A hA hpinA
  have hsplit : Fail.card = Rest.card + Exc.card :=
    (Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)).symm
  have hExc : (Exc.card : ℝ) ≤ M := by
    have : Exc.card ≤ Bad.card := Finset.card_le_card fun F hF => (Finset.mem_filter.1 hF).2
    have h' : (Exc.card : ℝ) ≤ Bad.card := by exact_mod_cast this
    linarith
  have hM : M ≤ ε / 2 * D := by
    have h2 : 2 * |M| / ε ≤ D := hDbig X hX
    have h3 : 2 * |M| ≤ ε * D := by rw [div_le_iff₀ hε] at h2; linarith
    have := le_abs_self M
    linarith
  rw [hsplit, Nat.cast_add, ← hAcard]
  linarith

end Erdos99

end

end SaturationWindow

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `Saturation`
-/

section Saturation

/-!
# Saturation (Verification Guide §10, §11.3)

This file assembles the saturation statements used by the charging argument.

* `saturation_faces` (§10): saturated marked good faces (`saturation_marked`), restricted to the
  faces satisfying the degree window; the faces removed are few (`window_failures_few`).
* `saturation_core` (§10): adds the hull-return budgets (`ReturnBudgets`) and the high faces
  (stability, `GoodFaces.Bface_le`).
* `saturation_exists` (§10, §11.3): omits the faces with intermediate ports
  (`omit_intermediate`).
-/

open scoped BigOperators Real
open Filter

@[expose] public noncomputable section

open Classical

namespace Erdos99

open LocalCharge

/-- The upper bound of the degree window holds at every good face. -/
lemma GoodFaces.shortDeg_le_marks_add_four {X : Finset Plane} (hX : IsSeparated X)
    (G : GoodFaces X) (L : ℝ) {F : Set ℂ} (hF : F ∈ G.good) :
    shortDeg X L (Sum.inl F) ≤ G.marks F + 4 := by
  have hFe : F ∈ exceptionalFaces X := (mem_exceptionalFinset hX).1 (G.good_subset hF)
  have h1 := shortDeg_le_portDeg X L (Sum.inl F)
  rw [portDeg_face hFe] at h1
  refine h1.trans ?_
  simp only [GoodFaces.good, Finset.mem_union] at hF
  unfold GoodFaces.marks
  rcases hF with (h | h) | h
  · have := (G.pent_sub F h).2
    rw [if_pos h]; omega
  · have := (G.hex_sub F h).2
    rw [if_neg (Finset.disjoint_right.1 G.disjoint_pent_hex h), if_pos h]; omega
  · have := (G.act_sub F h).2
    split_ifs <;> omega

/-- **Saturated good faces at a fixed cutoff fraction** (Verification Guide §10).  For every
`ε > 0`, every cutoff fraction `a > 0` and every tolerance `tol > 0`, eventually every admissible
configuration has good faces `G` with a marking `mk` (`marks F` short marked ports at every good
face, the source-labelled tracks of the saturated token process), such that the degree window holds
at the cutoff `a D`, the faces carry injective source labels with tolerance `tol`, at most `ε D`
pentagons and hexagons are omitted, and at most `ε D` unmarked short ports of good faces have their
track ending at a unit hull side or at a marked port of a good face.  (This is the face part of
`saturation_core`; the hull-return part is proved in `ReturnBudgets`, and the omitted faces
with seven or more sides are paid for by stability, `GoodFaces.Bface_le`.) -/
theorem saturation_faces (ε : ℝ) (hε : 0 < ε) (a tol : ℝ) (ha : 0 < a) (htol : 0 < tol) :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∃ (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane)),
        IsMarking X (a * diam X) G mk ∧ DegreeWindow X (a * diam X) G ∧ IsLabelled X tol G mk ∧
        (G.omittedSmall : ℝ) ≤ ε * diam X ∧
        ((stubsTo X (a * diam X) G mk G.good (UnitEnd X)).card +
          (stubsTo X (a * diam X) G mk G.good (MarkedEnd G mk)).card : ℝ) ≤ ε * diam X := by
  obtain ⟨tol₀, htol₀, hwin⟩ := window_failures_few ha (half_pos hε)
  filter_upwards [saturation_marked (half_pos hε) ha (lt_min htol htol₀), hwin,
    eventually_ge_atTop 2] with n hsat hwin hn2 hfm X hX htri
  have hD : 0 < diam X := hX.diam_pos hn2
  obtain ⟨G, mk, hmk, hlab, hom, hsu, hsm⟩ := hsat hfm X hX htri
  have hW := hwin hfm X hX htri G mk hmk (hlab.mono_tol (min_le_right _ _) hD.le)
  set P : Set ℂ → Prop := fun F => G.marks F + 2 ≤ shortDeg X (a * diam X) (Sum.inl F) with hPdef
  set G' := G.restrict P with hG'
  have hmem : ∀ {F}, F ∈ G'.good ↔ F ∈ G.good ∧ P F := GoodFaces.mem_restrict_good
  refine ⟨G', mk, ?_, ?_, ?_, ?_, ?_⟩
  · intro F hF
    obtain ⟨hF, hP⟩ := hmem.1 hF
    rw [GoodFaces.marks_restrict hP]; exact hmk F hF
  · intro F hF
    obtain ⟨hF', hP⟩ := hmem.1 hF
    rw [GoodFaces.marks_restrict hP]
    exact ⟨hP, G.shortDeg_le_marks_add_four hX.1.2 _ hF'⟩
  · obtain ⟨lab, hinj, hl⟩ := hlab.mono_tol (min_le_left _ _) hD.le
    refine ⟨lab, hinj.mono fun F hF => (hmem.1 hF).1, fun F hF => ?_⟩
    obtain ⟨hF, hP⟩ := hmem.1 hF
    rw [GoodFaces.markMult_restrict hP]
    exact hl F hF
  · -- the omitted faces: those of `G` and the window failures
    have hsub : (exceptionalFinset X).filter (fun F => faceSize X F ≤ 6 ∧ F ∉ G'.good) ⊆
        (exceptionalFinset X).filter (fun F => faceSize X F ≤ 6 ∧ F ∉ G.good) ∪
          G.good.filter (fun F => ¬ P F) := by
      intro F hF
      obtain ⟨hFe, hF6, hFg⟩ := Finset.mem_filter.1 hF
      by_cases hg : F ∈ G.good
      · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hg, fun hP => hFg (hmem.2 ⟨hg, hP⟩)⟩)
      · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hFe, hF6, hg⟩)
    have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have h2 : (G'.omittedSmall : ℝ) ≤ G.omittedSmall +
        ((G.good.filter (fun F => ¬ P F)).card : ℝ) := by
      unfold GoodFaces.omittedSmall; exact_mod_cast h1
    linarith
  · have h1 : stubsTo X (a * diam X) G' mk G'.good (UnitEnd X) = ∅ :=
      Finset.subset_empty.1 (hsu ▸ stubsTo_restrict_unit)
    have h2 : stubsTo X (a * diam X) G' mk G'.good (MarkedEnd G' mk) = ∅ :=
      Finset.subset_empty.1 (hsm ▸ stubsTo_restrict_marked)
    rw [h1, h2, Finset.card_empty, Nat.cast_zero, add_zero]
    positivity

/-- **Saturation at a fixed cutoff fraction** (Verification Guide §10).  For every `ε > 0`, every
cutoff fraction `a > 0` and every tolerance `tol > 0`, eventually every admissible configuration has
good faces `G` with a marking `mk` (`marks F` short marked ports at every good face, the
source-labelled tracks of the saturated token process), such that the degree window holds at the
cutoff `a D`, the faces carry injective source labels with tolerance `tol`, the omitted faces have
at most `ε D` sides, at most `ε D` unit (resp. two-edge) hull returns have no short port, and at
most `ε D` unmarked short ports of good faces have their track ending at a unit hull side or at a
marked port of a good face.

The hull-return budgets are proved (`unitReturnsNoShort_small`, `twoReturnsNoShort_small`, from
the short-source theorems), the high faces are paid for by stability (`stability_bounds`,
`GoodFaces.Bface_le`); the face part is `saturation_faces`, proved from `saturation_marked`
(`SaturationMarked`) and `window_failures_few`. -/
theorem saturation_core (ε : ℝ) (hε : 0 < ε) (a tol : ℝ) (ha : 0 < a) (htol : 0 < tol) :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∃ (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane)),
        IsMarking X (a * diam X) G mk ∧ DegreeWindow X (a * diam X) G ∧ IsLabelled X tol G mk ∧
        (G.Bface : ℝ) ≤ ε * diam X ∧ (unitReturnsNoShort X (a * diam X) : ℝ) ≤ ε * diam X ∧
        (twoReturnsNoShort X (a * diam X) : ℝ) ≤ ε * diam X ∧
        ((stubsTo X (a * diam X) G mk G.good (UnitEnd X)).card +
          (stubsTo X (a * diam X) G mk G.good (MarkedEnd G mk)).card : ℝ) ≤ ε * diam X := by
  filter_upwards [saturation_faces (ε / 12) (by positivity) a tol ha htol,
    unitReturnsNoShort_small ε hε ha, twoReturnsNoShort_small ε hε ha,
    stability_bounds (ε / 2) (by positivity), eventually_ge_atTop 2] with
    n hsat hu ht hstab hn2 hfm X hX htri
  obtain ⟨G, mk, hmk, hwin, hlab, hom, hst⟩ := hsat hfm X hX htri
  have hD : 0 < diam X := hX.diam_pos hn2
  have hI := (hstab hfm X hX htri).2.2.2.2.2
  have hB : (G.Bface : ℝ) ≤ highIncidence X + 6 * G.omittedSmall := by
    exact_mod_cast G.Bface_le hX.1.2
  refine ⟨G, mk, hmk, hwin, hlab, by linarith, hu hfm X hX htri, ht hfm X hX htri, ?_⟩
  linarith

/-- **Saturation with a sparse shell** (Verification Guide §10, §11.3).  For every `ε > 0` there
is a shell density `κ > 0` such that for all `0 < a < λ` and `tol > 0`, eventually every admissible
configuration with at most `κ D` tracks of length in `[a D, λ D)` has saturated good faces (no
intermediate ports) with all budgets at most `ε D`. -/
theorem saturation_exists (ε : ℝ) (hε : 0 < ε) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ lam a tol : ℝ, 0 < a → 0 < tol →
      ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
        ((longTracks X (a * diam X) \ longTracks X (lam * diam X)).card : ℝ) ≤ κ * diam X →
        ∃ (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane)),
          IsMarking X (a * diam X) G mk ∧ DegreeWindow X (a * diam X) G ∧
          IsSaturated X (a * diam X) (lam * diam X) tol G mk ∧
          (G.Bface : ℝ) ≤ ε * diam X ∧ (unitReturnsNoShort X (a * diam X) : ℝ) ≤ ε * diam X ∧
          (twoReturnsNoShort X (a * diam X) : ℝ) ≤ ε * diam X ∧
          ((stubsTo X (a * diam X) G mk G.good (UnitEnd X)).card +
            (stubsTo X (a * diam X) G mk G.good (MarkedEnd G mk)).card : ℝ) ≤ ε * diam X := by
  refine ⟨ε / 24, by positivity, fun lam a tol ha htol => ?_⟩
  filter_upwards [saturation_core (ε / 2) (by positivity) a tol ha htol, card_trackEnds,
    eventually_ge_atTop 2] with n hsat hends hn2 hfm X hX htri hsh
  have hD : 0 < diam X := hX.diam_pos hn2
  obtain ⟨G, mk, hmk, hwin, hlab, hBf, hBu, hBt, hst⟩ := hsat hfm X hX htri
  obtain ⟨G', hmk', hwin', hsat', hBf', hst'⟩ :=
    omit_intermediate (Λ := lam * diam X) hX.1.2 htri (hends hfm X hX htri) (mul_pos ha hD) hmk
      hwin hlab
  refine ⟨G', mk, hmk', hwin', hsat', ?_, by linarith, by linarith, by linarith⟩
  linarith

end Erdos99

end

end Saturation

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `OneShortCap`
-/

section OneShortCap

/-!
# A one-short-port two-edge cap rarely feeds `H` (Verification Guide §13.5)

This file proves `oneShort_H_stubs_few`: the stubs at degree-two good faces whose track ends at a
two-edge return with exactly one short port are few, up to the number of intermediate tracks
(tracks with between `a D` and `λ D` rhombi).

## Structure of the argument

At such a stub `(F, e)`, with cap `p = (v, w)` and apex `x`:
* the closure of `F` gives `‖k τ + s + u + Z‖ ≤ tol` (`H_face_equation`), `s` the side of `F`
  along `e`, `u` a unit vector, `Z` the long-side sum of `F`;
* track translation (`trackCap_side`) and the cap reflection (`cap_reflect_data`) give
  `s = ζ² conj c`, where `ζ` is the direction of `p` and `c` is a vector of the other port of the cap;
* label locality (`cap_label_locality`) gives `τ ≈ ζ`, so (H2) is approximately satisfied at `ζ`
  (`approx_H2`);
* the other port of the cap is long; if its track has fewer than `λ D` rhombi the stub is charged to
  an intermediate track (`oneShort_shell_card`), otherwise its vector is clustered
  (`hull_ports_clustered`), as is `Z` (`long_sides_clustered`);
* pinning (`cap_pinned_count`) bounds the remaining caps, and stubs inject into caps
  (`oneShort_cap_injOn`).
-/

open scoped BigOperators Real
open Filter Polynomial ComplexConjugate

@[expose] public noncomputable section

open Classical

namespace Erdos99

open LocalCharge QuadraticResponse DirectionPinning EstablishedExternalResults

/-- The hull side of a node (`(0, 0)` for a face). -/
def nodeSide : PortNode → Plane × Plane := Sum.elim (fun _ => (0, 0)) id

/-- **Stubs inject into their caps**: two stubs ending at the same one-short-port cap coincide. -/
lemma oneShort_cap_injOn {X : Finset Plane}
    (hends : ∀ T ∈ allTracks X, (trackEnds X T).card = 2) (L : ℝ) (G : GoodFaces X)
    (mk : Set ℂ → Finset (Sym2 Plane)) (V : Finset (Set ℂ)) :
    Set.InjOn (fun q => nodeSide (otherEnd X q).1) (stubsTo X L G mk V (OneShortEnd X L)) := by
  have key : ∀ q ∈ stubsTo X L G mk V (OneShortEnd X L), ∃ p, (otherEnd X q).1 = Sum.inr p ∧
      shortDeg X L (Sum.inr p) = 1 ∧ q ∈ facePorts X ∧
      (otherEnd X q).2 ∈ (unitEdges X).filter (fun e => IsPort X (Sum.inr p) e ∧
        (trackLength X (allTrackOf X e) : ℝ) < L) := by
    intro q hq
    obtain ⟨p, hp, -, hsd⟩ := (Finset.mem_filter.1 hq).2
    have hqu := stubsTo_subset V _ hq
    have hfp := unmarkedPorts_subset_facePorts hqu
    obtain ⟨-, h2, h3, h4⟩ := otherEnd_track hends hfp
    obtain ⟨-, hsp, -⟩ := mem_unmarkedPorts.1 hqu
    refine ⟨p, hp, hsd, hfp, Finset.mem_filter.2 ⟨h2, hp ▸ h3, ?_⟩⟩
    rw [h4]; exact (Finset.mem_filter.1 hsp).2.2
  intro q₁ hq₁ q₂ hq₂ h
  obtain ⟨p₁, hp₁, hsd₁, hf₁, hm₁⟩ := key q₁ hq₁
  obtain ⟨p₂, hp₂, hsd₂, hf₂, hm₂⟩ := key q₂ hq₂
  simp only [hp₁, hp₂, nodeSide, Sum.elim_inr, id] at h
  subst h
  have he : (otherEnd X q₁).2 = (otherEnd X q₂).2 :=
    Finset.card_le_one.1 (le_of_eq hsd₁) _ hm₁ _ hm₂
  exact otherEnd_injOn hends hf₁ hf₂ (Prod.ext (hp₁.trans hp₂.symm) he)

/-- **The stubs charged to intermediate tracks**: the stubs whose cap has a port on a track with
between `L` and `Λ` rhombi number at most twice the number of such tracks. -/
lemma oneShort_shell_card {X : Finset Plane} (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X)
    (hends : ∀ T ∈ allTracks X, (trackEnds X T).card = 2) {L : ℝ} (hL : 0 < L) (Λ : ℝ)
    (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane)) (V : Finset (Set ℂ)) :
    ((stubsTo X L G mk V (OneShortEnd X L)).filter (fun q =>
      ∃ e'' ∈ unitEdges X, IsPort X (otherEnd X q).1 e'' ∧
        L ≤ (trackLength X (allTrackOf X e'') : ℝ) ∧
        (trackLength X (allTrackOf X e'') : ℝ) < Λ)).card ≤
      2 * (longTracks X L \ longTracks X Λ).card := by
  set S := (stubsTo X L G mk V (OneShortEnd X L)).filter (fun q =>
      ∃ e'' ∈ unitEdges X, IsPort X (otherEnd X q).1 e'' ∧
        L ≤ (trackLength X (allTrackOf X e'') : ℝ) ∧
        (trackLength X (allTrackOf X e'') : ℝ) < Λ) with hSdef
  set I := longTracks X L \ longTracks X Λ with hIdef
  have hex : ∀ q ∈ S, ∃ e'', e'' ∈ unitEdges X ∧ IsPort X (otherEnd X q).1 e'' ∧
      L ≤ (trackLength X (allTrackOf X e'') : ℝ) ∧ (trackLength X (allTrackOf X e'') : ℝ) < Λ :=
    fun q hq => by
      obtain ⟨e'', h1, h2⟩ := (Finset.mem_filter.1 hq).2
      exact ⟨e'', h1, h2⟩
  choose! ep hep using hex
  have hmaps : ∀ q ∈ S, ((otherEnd X q).1, ep q) ∈ I.biUnion (trackEnds X) := by
    intro q hq
    obtain ⟨he, hport, hL1, hL2⟩ := hep q hq
    have hqu := stubsTo_subset V _ (Finset.mem_filter.1 hq).1
    obtain ⟨h1, -⟩ := otherEnd_track hends (unmarkedPorts_subset_facePorts hqu)
    have heR : ep q ∈ rhombusEdges X := by
      by_contra hne
      rw [allTrackOf_of_not_mem he hne, trackLength_singleton hX htri he hne] at hL1
      push_cast at hL1; linarith
    have hT : allTrackOf X (ep q) ∈ tracks X := by
      rw [allTrackOf_of_mem_rhombusEdges heR]; exact Finset.mem_image_of_mem _ heR
    refine Finset.mem_biUnion.2 ⟨allTrackOf X (ep q), ?_, mem_trackEnds.2
      ⟨h1, mem_allTrackOf_self he, hport⟩⟩
    refine Finset.mem_sdiff.2 ⟨Finset.mem_filter.2 ⟨hT, hL1⟩, fun h => ?_⟩
    have := (Finset.mem_filter.1 h).2
    linarith
  have hinj : Set.InjOn (fun q => ((otherEnd X q).1, ep q)) S := by
    intro q₁ hq₁ q₂ hq₂ h
    have h1 : (otherEnd X q₁).1 = (otherEnd X q₂).1 := (Prod.mk.inj h).1
    exact oneShort_cap_injOn hends L G mk V (Finset.mem_filter.1 hq₁).1
      (Finset.mem_filter.1 hq₂).1 (by simp only [h1])
  calc S.card ≤ (I.biUnion (trackEnds X)).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ ≤ ∑ T ∈ I, (trackEnds X T).card := Finset.card_biUnion_le
    _ = ∑ _T ∈ I, 2 := by
        refine Finset.sum_congr rfl fun T hT => hends T ?_
        exact tracks_subset_allTracks X (Finset.mem_filter.1 (Finset.mem_sdiff.1 hT).1).1
    _ = 2 * I.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- **A one-short-port two-edge cap rarely feeds `H`** (Verification Guide §13.5, (H2)).  For
every `ε, λ > 0` there are a saturation tolerance and a cutoff fraction `a₀` such that for every
cutoff fraction `a ≤ a₀`, eventually, for every saturated marking, the stubs at degree-two faces
whose track ends at a two-edge return with one short port number at most `ε D` plus twice the
number of intermediate tracks (with at least `a D` and fewer than `λ D` rhombi). -/
theorem oneShort_H_stubs_few {ε lam : ℝ} (hε : 0 < ε) (hlam : 0 < lam) :
    ∃ tol > 0, ∃ a₀ > 0, ∀ a, 0 < a → a ≤ a₀ →
      ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
        ∀ (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane)), IsMarking X (a * diam X) G mk →
          IsSaturated X (a * diam X) (lam * diam X) tol G mk →
          ((stubsTo X (a * diam X) G mk ((trackGraph X (a * diam X) G mk).Hs G.good)
            (OneShortEnd X (a * diam X))).card : ℝ) ≤
            ε * diam X + 2 * ((longTracks X (a * diam X) \ longTracks X (lam * diam X)).card) := by
  obtain ⟨NZ, hclusZ⟩ := long_sides_clustered hlam
  obtain ⟨NC, hclusC⟩ := hull_ports_clustered hlam
  obtain ⟨r, hr, μ, hμ, hpin⟩ := cap_pinned_count (2 * (NC * 7 ^ NZ)) (half_pos hε)
  set δ' := min (r / 12) (1 / 3) with hδ'def
  have hδ'0 : 0 < δ' := lt_min (by positivity) (by norm_num)
  have hδ'r : 3 * δ' * (2 + 3 * δ') < r := by
    have h1 : δ' ≤ r / 12 := min_le_left _ _
    have h2 : δ' ≤ 1 / 3 := min_le_right _ _
    nlinarith
  obtain ⟨MZ, hclusZM⟩ := hclusZ (μ / 12) (by positivity)
  obtain ⟨MC, hclusCM⟩ := hclusC (μ / 2) (by positivity)
  obtain ⟨cl, hcl, hloc⟩ := cap_label_locality hδ'0
  refine ⟨min δ' cl, lt_min hδ'0 hcl, cl, hcl, fun a ha hab => ?_⟩
  filter_upwards [hpin, hclusZM, hclusCM, hloc, H_face_equation, trackCap_side, oneShort_cap_ports,
    face_side_facts, image_orientedSides_eq, card_trackEnds,
    eventually_diam_ge ((2 * |MZ| + |MC|) / (ε / 2)), eventually_diam_ge 1] with
    n hpin hclusZM hclusCM hloc hface hcapside hcapports hfacts himg hends hDbig hD1
  intro hfm X hX htri G mk hmk hsat
  set D := diam X with hDdef
  set L := a * D with hLdef
  have hD : 0 < D := lt_of_lt_of_le one_pos (hD1 X hX)
  have hL : 0 < L := mul_pos ha hD
  obtain ⟨hnoint, lab, hlab⟩ := hsat
  set tol := min δ' cl with htoldef
  have htolδ : tol ≤ δ' := min_le_left _ _
  have htolc : tol ≤ cl := min_le_right _ _
  have hLc : L ≤ cl * D := mul_le_mul_of_nonneg_right hab hD.le
  obtain ⟨UZ, hUZ, BadZ, hBadZ, hclZ⟩ := hclusZM hfm X hX htri
  obtain ⟨UC, hUC, BadC, hBadC, hclC⟩ := hclusCM hfm X hX htri
  have hends' := hends hfm X hX htri
  set Hs := (trackGraph X L G mk).Hs G.good with hHsdef
  set S := stubsTo X L G mk Hs (OneShortEnd X L) with hSdef
  set Shell := S.filter (fun q => ∃ e'' ∈ unitEdges X, IsPort X (otherEnd X q).1 e'' ∧
    L ≤ (trackLength X (allTrackOf X e'') : ℝ) ∧
    (trackLength X (allTrackOf X e'') : ℝ) < lam * D) with hShelldef
  set EZ := S.filter (fun q => q.1 ∈ BadZ) with hEZdef
  set EC := S.filter (fun q => nodeSide (otherEnd X q).1 ∈ BadC) with hECdef
  set Rest := S \ (Shell ∪ EZ ∪ EC) with hRestdef
  have hShell : Shell.card ≤ 2 * (longTracks X L \ longTracks X (lam * D)).card :=
    oneShort_shell_card hX.1.2 htri hends' hL (lam * D) G mk Hs
  have hEZ : EZ.card ≤ 2 * BadZ.card := by
    refine le_trans (Finset.card_le_card ?_) (card_halfEdges_H_le hends' L G mk BadZ)
    intro q hq
    obtain ⟨hqS, hqB⟩ := Finset.mem_filter.1 hq
    exact Finset.mem_filter.2 ⟨stubsTo_subset _ _ hqS, hqB,
      (Finset.mem_filter.1 (Finset.mem_filter.1 hqS).1).2.2⟩
  have hinjS := oneShort_cap_injOn hends' L G mk Hs
  have hEC : EC.card ≤ BadC.card := by
    refine Finset.card_le_card_of_injOn (fun q => nodeSide (otherEnd X q).1) ?_ ?_
    · intro q hq; exact (Finset.mem_filter.1 hq).2
    · exact hinjS.mono (fun q hq => (Finset.mem_filter.1 hq).1)
  set A := Rest.image (fun q => nodeSide (otherEnd X q).1) with hAdef
  have hAcard : A.card = Rest.card :=
    Finset.card_image_of_injOn (hinjS.mono (fun q hq => (Finset.mem_sdiff.1 hq).1))
  have hexF : ∀ F ∈ G.good, F ∈ exceptionalFaces X := fun F hF =>
    (mem_exceptionalFinset hX.1.2).1 (G.good_subset hF)
  -- the cap of a stub
  have hcapOf : ∀ q ∈ S, ∃ p0, (otherEnd X q).1 = Sum.inr p0 ∧ p0 ∈ ccwHullSides X := by
    intro q hq
    obtain ⟨p0, hp0, -, -⟩ := (Finset.mem_filter.1 hq).2
    have hqu := stubsTo_subset Hs _ hq
    obtain ⟨-, -, hpe', -⟩ := otherEnd_track hends' (unmarkedPorts_subset_facePorts hqu)
    rw [hp0] at hpe'
    exact ⟨p0, hp0, hpe'.1⟩
  have hA : A ⊆ ccwHullSides X := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨p0, hp0, hp0s⟩ := hcapOf q (Finset.mem_sdiff.1 hq).1
    rw [hp0]; exact hp0s
  set C : Finset (ℝ × ℂ × ℂ) := ({1, 2} : Finset ℝ) ×ˢ UC ×ˢ sumCentres UZ with hCdef
  have hC : C.card ≤ 2 * (NC * 7 ^ NZ) := by
    have h1 : (sumCentres UZ).card ≤ 7 ^ NZ :=
      (card_sumCentres_le UZ).trans (Nat.pow_le_pow_right (by norm_num) hUZ)
    have h2 : (({1, 2} : Finset ℝ)).card ≤ 2 := Finset.card_le_two
    simp only [hCdef, Finset.card_product]
    gcongr
  have hdata : ∀ p ∈ A, ∃ d : ℝ × ℂ × ℂ, CapAdm d ∧ (∃ c ∈ C, ‖d - c‖ < μ) ∧
      ‖(capPoly d.1 d.2.1 d.2.2).eval (toC (sideDir p))‖ < r := by
    intro p hp
    obtain ⟨⟨F, e⟩, hq, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨hqS, hqn⟩ := Finset.mem_sdiff.1 hq
    have hqst := Finset.mem_filter.1 hqS
    have hqu := stubsTo_subset Hs _ hqS
    have hFH : F ∈ Hs := (Finset.mem_filter.1 hqst.1).2.2
    obtain ⟨hFg, hsp, hnm⟩ := mem_unmarkedPorts.1 hqu
    obtain ⟨he, hpF, hlen⟩ := Finset.mem_filter.1 hsp
    have hFe : F ∈ exceptionalFaces X := hpF.1
    have hb := hpF.2
    rw [← himg hfm X hX F hFe] at hb
    obtain ⟨ab, hab, habe⟩ := Finset.mem_image.1 hb
    obtain ⟨u, hu, hequ⟩ := hface hfm X hX htri L tol G mk lab hmk hlab F hFH e
      (Finset.mem_sdiff.2 ⟨hsp, hnm⟩) ab hab habe.symm
    obtain ⟨p0, hp0, hret, hsd⟩ := hqst.2
    have hpp : nodeSide (otherEnd X (F, e)).1 = p0 := by rw [hp0]; rfl
    rw [hpp]
    obtain ⟨y₁, y₂, hy, hyv, hyd⟩ := hcapside hfm X hX htri F hFe e he ab hab habe.symm p0 hp0
    have hfp := unmarkedPorts_subset_facePorts hqu
    obtain ⟨-, he', hpe', htr'⟩ := otherEnd_track hends' hfp
    rw [hp0] at hpe'
    have hp0s : p0 ∈ ccwHullSides X := hpe'.1
    have hshort : (trackLength X (allTrackOf X (otherEnd X (F, e)).2) : ℝ) < L := by
      rw [htr']; exact hlen
    obtain ⟨x, e'', hx, he'', hpe'', hL'', hcase⟩ :=
      hcapports hfm X hX L p0 hp0s hret hsd _ he' hpe' hshort
    obtain ⟨z₁, z₂, hz, hz1, hrefl⟩ := cap_reflect_data hx hcase hy
    -- the other port is macroscopic
    have hlong : lam * D ≤ trackLength X (allTrackOf X e'') := by
      by_contra hlt
      push_neg at hlt
      refine hqn (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.2
        ⟨hqS, e'', he'', ?_, hL'', hlt⟩)))
      rw [hp0]; exact hpe''
    have hnC : p0 ∉ BadC := fun h => hqn (Finset.mem_union_right _
      (Finset.mem_filter.2 ⟨hqS, by rw [hpp]; exact h⟩))
    have hz' : e'' = s(z₂, z₁) := hz.trans Sym2.eq_swap
    obtain ⟨uc, huc, hucd⟩ := hclC p0 hp0s hnC z₂ z₁ (hz' ▸ he'') (hz' ▸ hpe'') (hz' ▸ hlong)
    have hnZ : F ∉ BadZ := fun h => hqn (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_filter.2 ⟨hqS, h⟩)))
    -- clustering of the long sides of `F`
    have hlongcl : ∀ ab ∈ longSides X L F, ∃ u ∈ UZ, ‖(ab.2 - ab.1) - u‖ ≤ μ / 12 := by
      intro ab hab
      obtain ⟨e, he, hmap, hport', hlong'⟩ := longSide_edge (hexF F hFg) hab
      refine hclZ F (hexF F hFg) hnZ ab (Finset.mem_filter.1 hab).1 ⟨e, he, hmap, ?_⟩
      rcases hnoint F hFg e he hport' with h | h
      · exact absurd h hlong'
      · exact h
    have hcard6 : (longSides X L F).card ≤ 6 :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans (hfacts hfm X hX G F hFg).1
    obtain ⟨z, hz, hzZ⟩ := sum_near_sumCentres (longSides X L F) (fun ab => ab.2 - ab.1) UZ
      (by positivity) hcard6 hlongcl
    obtain ⟨hcF, huF⟩ := hfacts hfm X hX G F hFg
    have hZ6 := norm_longSum_le (L := L) hcF huF
    -- locality
    have hy1 : dist y₁ p0.1 ≤ 2 := by
      obtain ⟨-, -, hd1, hd2, -⟩ := Finset.mem_filter.1 hx
      have hmem : y₁ = p0.1 ∨ y₁ = x ∨ y₁ = p0.2 := by
        rcases hcase with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [hy] at h1 <;>
          rcases Sym2.eq_iff.1 h1 with ⟨h2, -⟩ | ⟨h2, -⟩ <;> simp [h2]
      rcases hmem with h | h | h
      · rw [h, dist_self]; norm_num
      · rw [h, dist_comm, hd1]; norm_num
      · rw [h]
        have := dist_triangle p0.2 x p0.1
        rw [dist_comm p0.2 x, hd2, dist_comm x p0.1, hd1] at this
        linarith
    have hloc' := hloc hfm X hX htri L tol G mk lab hLc htolc hlab F hFg ab hab p0 y₁ hp0s
      (hyd.trans hlen.le) hy1
    have hs : ab.2 - ab.1 = (toC (sideDir p0)) ^ 2 * conj (toC z₁ - toC z₂) := by
      have h1 : ab.2 - ab.1 = -(toC y₂ - toC y₁) := by rw [hyv]; ring
      rw [h1, hrefl, show toC z₁ - toC z₂ = -(toC z₂ - toC z₁) by ring, map_neg]
      ring
    rw [hs] at hequ
    have hζ : ‖toC (sideDir p0)‖ = 1 := by
      rw [norm_toC]; exact norm_sideDir (mem_ccwHullSides.1 hp0s).2.2.1
    have hev := approx_H2 (G.kMult_cases F) hζ hu (hequ.trans htolδ) hloc'
    refine ⟨(G.kMult F, toC z₁ - toC z₂, longSum X L F),
      ⟨G.kMult_cases _, by rw [norm_sub_rev]; exact hz1, hZ6⟩, ⟨(G.kMult F, uc, z), ?_, ?_⟩,
      by simp only; linarith⟩
    · simp only [hCdef, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨G.kMult_cases _, huc, hz⟩
    · have h2 : ‖longSum X L F - z‖ ≤ μ / 2 := by
        have := hzZ; simp only [longSum] at this ⊢; linarith
      simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, sub_self, norm_zero]
      exact max_lt hμ (max_lt (by linarith) (by linarith))
  have key := hpin X hX C hC A hA hdata
  have hsub : S ⊆ Rest ∪ (Shell ∪ EZ ∪ EC) := by
    intro q hq
    by_cases h : q ∈ Shell ∪ EZ ∪ EC
    · exact Finset.mem_union_right _ h
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨hq, h⟩)
  have hcount : S.card ≤ Rest.card + Shell.card + EZ.card + EC.card := by
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le Rest (Shell ∪ EZ ∪ EC)
    have h3 := Finset.card_union_le (Shell ∪ EZ) EC
    have h4 := Finset.card_union_le Shell EZ
    omega
  have hM : (2 * BadZ.card + BadC.card : ℝ) ≤ ε / 2 * D := by
    have h1 : (2 * BadZ.card + BadC.card : ℝ) ≤ 2 * |MZ| + |MC| := by
      have := le_abs_self MZ; have := le_abs_self MC; linarith
    have h2 : (2 * |MZ| + |MC|) / (ε / 2) ≤ D := hDbig X hX
    rw [div_le_iff₀ (by positivity)] at h2
    linarith
  have hcount' : (S.card : ℝ) ≤ Rest.card + Shell.card + EZ.card + EC.card := by
    exact_mod_cast hcount
  have hShell' : (Shell.card : ℝ) ≤ 2 * (longTracks X L \ longTracks X (lam * D)).card := by
    exact_mod_cast hShell
  have hEZ' : (EZ.card : ℝ) ≤ 2 * BadZ.card := by exact_mod_cast hEZ
  have hEC' : (EC.card : ℝ) ≤ BadC.card := by exact_mod_cast hEC
  rw [← hAcard] at hcount'
  linarith

end Erdos99

end

end OneShortCap

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `CaplessComponents`
-/

section CaplessComponents

/-!
# Capless components: graph facts and label locality (Verification Guide §13.4)

* `ofHalfEdges_stub_of_not_mated`, `ofHalfEdges_edge_of_mated`: unmatched half-edges are stubs,
  matched half-edges are edges of the stub graph;
* `mated_of_stubless`: at a stubless component every unmarked short port is matched;
* `mate_same_component`: a matched port between two faces of `U` stays in one component of the
  subgraph on `U`;
* `mated_label_dist`: the labels of the two ends of a matched short track are within
  `2 tol D + 1 + L`;
* `component_label_dist`: two faces of a component with at most `M` faces have labels within
  `M (2 tol D + 1 + L)`;
* `labDir_close`: hull sides whose starting points are within `c D` have directions within `ρ`.
-/

open scoped BigOperators Real
open Filter

@[expose] public noncomputable section

open Classical

namespace Erdos99

open LocalCharge

namespace LocalCharge.StubGraph

variable {α β : Type*} [Inhabited β] {P : Finset β} {v : β → α} {mate : β → β} {mated : β → Prop}

/-- An unmatched half-edge is a stub. -/
lemma ofHalfEdges_stub_of_not_mated {q : β} (hq : q ∈ P) (hm : ¬ mated q) :
    ∃ s ∈ (ofHalfEdges P v mate mated).S, (ofHalfEdges P v mate mated).stub s = v q := by
  refine ⟨hIdx P q, ?_, ?_⟩
  · simp only [ofHalfEdges, Finset.mem_filter, Finset.mem_range]
    exact ⟨hIdx_lt P hq, by rw [hEnum_hIdx P hq]; exact hm⟩
  · simp only [ofHalfEdges]; rw [hEnum_hIdx P hq]

/-- A matched half-edge gives an edge joining its vertex to the vertex of its mate. -/
lemma ofHalfEdges_edge_of_mated (hM : IsMatching P mate mated) {q : β} (hq : q ∈ P)
    (hm : mated q) : ∃ e ∈ (ofHalfEdges P v mate mated).E,
      s((ofHalfEdges P v mate mated).src e, (ofHalfEdges P v mate mated).tgt e) =
        s(v q, v (mate q)) := by
  obtain ⟨hmP, hne, hinv, hmm⟩ := hM q hq hm
  have hidx : hIdx P q ≠ hIdx P (mate q) := fun h => hne (hIdx_injOn P hmP hq h.symm)
  rcases lt_or_gt_of_ne hidx with h | h
  · refine ⟨hIdx P q, ?_, ?_⟩
    · simp only [ofHalfEdges, Finset.mem_filter, Finset.mem_range]
      rw [hEnum_hIdx P hq]; exact ⟨hIdx_lt P hq, hm, h⟩
    · simp only [ofHalfEdges]; rw [hEnum_hIdx P hq]
  · refine ⟨hIdx P (mate q), ?_, ?_⟩
    · simp only [ofHalfEdges, Finset.mem_filter, Finset.mem_range]
      rw [hEnum_hIdx P hmP, hinv]; exact ⟨hIdx_lt P hmP, hmm, h⟩
    · simp only [ofHalfEdges]; rw [hEnum_hIdx P hmP, hinv, Sym2.eq_swap]

/-- Every edge comes from a matched half-edge. -/
lemma ofHalfEdges_edge_mated {e : ℕ} (he : e ∈ (ofHalfEdges P v mate mated).E) :
    ∃ q ∈ P, mated q ∧ (ofHalfEdges P v mate mated).src e = v q ∧
      (ofHalfEdges P v mate mated).tgt e = v (mate q) := by
  simp only [ofHalfEdges, Finset.mem_filter, Finset.mem_range] at he ⊢
  exact ⟨hEnum P e, hEnum_mem P he.1, he.2.1, rfl, rfl⟩

end LocalCharge.StubGraph

/-! ## Components of the track graph -/

section components

variable {X : Finset Plane} {L : ℝ} {G : GoodFaces X} {mk : Set ℂ → Finset (Sym2 Plane)}

/-- **At a stubless component every unmarked short port is matched.** -/
lemma mated_of_stubless {U : Finset (Set ℂ)}
    {C : (StubGraph.cgraph (trackGraph X L G mk) U).ConnectedComponent}
    (hC : ∀ s ∈ (trackGraph X L G mk).S, (trackGraph X L G mk).stub s ∈ U →
      (StubGraph.cgraph (trackGraph X L G mk) U).connectedComponentMk
        ((trackGraph X L G mk).stub s) ≠ C)
    {q : Set ℂ × Sym2 Plane} (hq : q ∈ unmarkedPorts X L G mk) (hqU : q.1 ∈ U)
    (hqC : (StubGraph.cgraph (trackGraph X L G mk) U).connectedComponentMk q.1 = C) :
    TrackMated X L G mk q := by
  by_contra hm
  obtain ⟨s, hs, hst⟩ := StubGraph.ofHalfEdges_stub_of_not_mated (v := Prod.fst)
    (mate := trackMate X) hq hm
  have hst' : (trackGraph X L G mk).stub s = q.1 := hst
  exact hC s hs (by rw [hst']; exact hqU) (by rw [hst']; exact hqC)

/-- The ends of an adjacency of the subgraph on `U` lie in `U` and come from a matched port. -/
lemma cgraph_adj_cases {U : Finset (Set ℂ)} {x y : Set ℂ}
    (h : (StubGraph.cgraph (trackGraph X L G mk) U).Adj x y) :
    x ∈ U ∧ y ∈ U ∧ ∃ q ∈ unmarkedPorts X L G mk, TrackMated X L G mk q ∧
      s(x, y) = s(q.1, (trackMate X q).1) := by
  rw [StubGraph.cgraph, StubGraph.edgeGraph, SimpleGraph.fromEdgeSet_adj] at h
  obtain ⟨hmem, -⟩ := h
  obtain ⟨e, he, hexy⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hmem)
  obtain ⟨heE, hsU, htU⟩ := Finset.mem_filter.1 he
  obtain ⟨q, hq, hm, hsrc, htgt⟩ := StubGraph.ofHalfEdges_edge_mated (P := unmarkedPorts X L G mk)
    (v := Prod.fst) (mate := trackMate X) (mated := TrackMated X L G mk) heE
  have hxy : s(x, y) = s((trackGraph X L G mk).src e, (trackGraph X L G mk).tgt e) := hexy.symm
  have hxyU : x ∈ U ∧ y ∈ U := by
    rcases Sym2.eq_iff.1 hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hsU, htU⟩
    · exact ⟨htU, hsU⟩
  refine ⟨hxyU.1, hxyU.2, q, hq, hm, ?_⟩
  rw [hxy]
  simp only [trackGraph] at hsrc htgt ⊢
  rw [hsrc, htgt]

/-- A matched port between two faces of `U` stays in one component. -/
lemma mate_same_component (hends : ∀ T ∈ allTracks X, (trackEnds X T).card = 2)
    {U : Finset (Set ℂ)} {q : Set ℂ × Sym2 Plane} (hq : q ∈ unmarkedPorts X L G mk)
    (hm : TrackMated X L G mk q) (hqU : q.1 ∈ U) (hmU : (trackMate X q).1 ∈ U) :
    (StubGraph.cgraph (trackGraph X L G mk) U).connectedComponentMk q.1 =
      (StubGraph.cgraph (trackGraph X L G mk) U).connectedComponentMk (trackMate X q).1 := by
  by_cases hxy : q.1 = (trackMate X q).1
  · rw [hxy]
  rw [SimpleGraph.ConnectedComponent.eq]
  refine SimpleGraph.Adj.reachable ?_
  rw [StubGraph.cgraph, StubGraph.edgeGraph, SimpleGraph.fromEdgeSet_adj]
  refine ⟨?_, hxy⟩
  obtain ⟨e, he, hee⟩ := StubGraph.ofHalfEdges_edge_of_mated (v := Prod.fst)
    (trackMate_isMatching hends L G mk) hq hm
  refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨e, Finset.mem_filter.2 ⟨he, ?_⟩, hee⟩)
  have h' : s((trackGraph X L G mk).src e, (trackGraph X L G mk).tgt e) =
      s(q.1, (trackMate X q).1) := hee
  rcases Sym2.eq_iff.1 h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]; exact ⟨hqU, hmU⟩
  · rw [h1, h2]; exact ⟨hmU, hqU⟩

end components

/-! ## Label locality -/

/-- **The labels of the two ends of a matched short track are close.** -/
theorem mated_label_dist :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ (L tol : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane))
        (lab : Set ℂ → Plane × Plane), LabelledBy X tol G mk lab →
      ∀ q ∈ unmarkedPorts X L G mk, TrackMated X L G mk q →
        dist (lab q.1).1 (lab (trackMate X q).1).1 ≤ 2 * tol * diam X + 1 + L := by
  filter_upwards [trackMate_side, exists_side_of_port, face_side_facts] with
    n hmate hside hfacts hfm X hX htri L tol G mk lab hlab q hq hmated
  obtain ⟨F, e⟩ := q
  obtain ⟨hFg, hsp, -⟩ := mem_unmarkedPorts.1 hq
  obtain ⟨he, hpF, hlen⟩ := Finset.mem_filter.1 hsp
  obtain ⟨ab, hab, habe⟩ := hside hfm X hX F e hpF
  obtain ⟨ab', hab', -, -, hd'⟩ := hmate hfm X hX htri F hpF.1 e he ab hab habe hmated.1
  obtain ⟨hFg', -, -⟩ := mem_unmarkedPorts.1 hmated.2
  have h1 := (hlab.2 F hFg).2.2 ab hab
  have h2 := (hlab.2 _ hFg').2.2 ab' hab'
  have h3 := (hfacts hfm X hX G F hFg).2 ab hab
  rw [← dist_toC, dist_eq_norm]
  have e1 : toC (lab F).1 - toC (lab (trackMate X (F, e)).1).1 =
      -(ab.1 - toC (lab F).1) - (ab.2 - ab.1) + (ab.2 - ab'.1) +
        (ab'.1 - toC (lab (trackMate X (F, e)).1).1) := by ring
  rw [e1]
  have n1 := norm_add_le (-(ab.1 - toC (lab F).1) - (ab.2 - ab.1) + (ab.2 - ab'.1))
    (ab'.1 - toC (lab (trackMate X (F, e)).1).1)
  have n2 := norm_add_le (-(ab.1 - toC (lab F).1) - (ab.2 - ab.1)) (ab.2 - ab'.1)
  have n3 := norm_sub_le (-(ab.1 - toC (lab F).1)) (ab.2 - ab.1)
  rw [norm_neg] at n3
  have n4 : ‖ab.2 - ab'.1‖ ≤ L := by
    rw [← dist_eq_norm, dist_comm]; exact hd'.trans hlen.le
  linarith

/-- Distances of labels along a walk of the subgraph on `U`. -/
lemma walk_label_dist {X : Finset Plane} {L : ℝ} {G : GoodFaces X}
    {mk : Set ℂ → Finset (Sym2 Plane)} {U : Finset (Set ℂ)} (lab : Set ℂ → Plane × Plane) {δ : ℝ}
    (hadj : ∀ x y, (StubGraph.cgraph (trackGraph X L G mk) U).Adj x y →
      dist (lab x).1 (lab y).1 ≤ δ) {x y : Set ℂ}
    (p : (StubGraph.cgraph (trackGraph X L G mk) U).Walk x y) :
    dist (lab x).1 (lab y).1 ≤ p.length * δ := by
  induction p with
  | nil => simp
  | @cons a b c h p ih =>
    rw [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]
    exact (dist_triangle _ _ _).trans (add_le_add (hadj _ _ h) ih)

/-- The vertices of a walk starting in `U` lie in `U` and in the component of the start. -/
lemma walk_support_mem {X : Finset Plane} {L : ℝ} {G : GoodFaces X}
    {mk : Set ℂ → Finset (Sym2 Plane)} {U : Finset (Set ℂ)} {x y : Set ℂ} (hx : x ∈ U)
    (p : (StubGraph.cgraph (trackGraph X L G mk) U).Walk x y) :
    ∀ v ∈ p.support, v ∈ U ∧ (StubGraph.cgraph (trackGraph X L G mk) U).connectedComponentMk v =
      (StubGraph.cgraph (trackGraph X L G mk) U).connectedComponentMk x := by
  induction p with
  | nil => intro v hv; simp at hv; subst hv; exact ⟨hx, rfl⟩
  | @cons a b c h p ih =>
    intro v hv
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact ⟨hx, rfl⟩
    · obtain ⟨-, hbU, -⟩ := cgraph_adj_cases h
      obtain ⟨hvU, hvc⟩ := ih hbU v hv
      refine ⟨hvU, hvc.trans ?_⟩
      exact (SimpleGraph.ConnectedComponent.eq.2 h.reachable).symm

/-- **Two faces of a small component have nearby labels.** -/
lemma component_label_dist {X : Finset Plane} {L : ℝ} {G : GoodFaces X}
    {mk : Set ℂ → Finset (Sym2 Plane)} {U : Finset (Set ℂ)} (lab : Set ℂ → Plane × Plane) {δ : ℝ}
    (hδ : 0 ≤ δ) (hadj : ∀ x y, (StubGraph.cgraph (trackGraph X L G mk) U).Adj x y →
      dist (lab x).1 (lab y).1 ≤ δ) {M : ℕ} {x y : Set ℂ} (hx : x ∈ U)
    (hxy : (StubGraph.cgraph (trackGraph X L G mk) U).connectedComponentMk x =
      (StubGraph.cgraph (trackGraph X L G mk) U).connectedComponentMk y)
    (hM : (U.filter (fun z => (StubGraph.cgraph (trackGraph X L G mk) U).connectedComponentMk z =
      (StubGraph.cgraph (trackGraph X L G mk) U).connectedComponentMk x)).card ≤ M) :
    dist (lab x).1 (lab y).1 ≤ M * δ := by
  obtain ⟨p⟩ := SimpleGraph.ConnectedComponent.exact hxy
  set q := p.toPath
  have hpath : (q : (StubGraph.cgraph (trackGraph X L G mk) U).Walk x y).IsPath := q.2
  have hsub : (q : (StubGraph.cgraph (trackGraph X L G mk) U).Walk x y).support.toFinset ⊆
      U.filter (fun z => (StubGraph.cgraph (trackGraph X L G mk) U).connectedComponentMk z =
        (StubGraph.cgraph (trackGraph X L G mk) U).connectedComponentMk x) := by
    intro v hv
    obtain ⟨hvU, hvc⟩ := walk_support_mem hx _ v (List.mem_toFinset.1 hv)
    exact Finset.mem_filter.2 ⟨hvU, hvc⟩
  have hlen : (q : (StubGraph.cgraph (trackGraph X L G mk) U).Walk x y).length + 1 ≤ M := by
    rw [← SimpleGraph.Walk.length_support, ← List.toFinset_card_of_nodup hpath.support_nodup]
    exact (Finset.card_le_card hsub).trans hM
  refine (walk_label_dist lab hadj q.1).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ hδ
  exact_mod_cast (Nat.le_succ _).trans hlen

/-- **Hull sides with nearby starting points have nearby directions.** -/
theorem labDir_close {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ c > 0, ∀ᶠ n in atTop, ∀ X, IsOptimal n X → ∀ p ∈ ccwHullSides X, ∀ q ∈ ccwHullSides X,
      dist p.1 q.1 ≤ c * diam X → ‖toC (sideDir p) - toC (sideDir q)‖ ≤ ρ := by
  have hκ : (0 : ℝ) < (ρ / 8) ^ 2 / 300 := by positivity
  have ht : Tendsto (fun n => minDiam n ^ (-(2 / 9 : ℝ))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num)).comp tendsto_minDiam
  refine ⟨ρ / 4, by positivity, ?_⟩
  filter_upwards [eventually_roundData_rate, ht.eventually (ge_mem_nhds hκ),
    tendsto_minDiam.eventually_ge_atTop 1] with n hround hsmall hD1 X hX p hp q hq hpq
  rw [← hX.diam_eq] at hsmall hD1
  have hD0 : 0 < diam X := by linarith
  obtain ⟨O, η, hR⟩ := hround X hX
  have hs := sideDir_sub_le hR (mem_ccwHullSides.1 hp) (mem_ccwHullSides.1 hq)
  rw [← map_sub, LinearIsometryEquiv.norm_map]
  refine hs.trans ?_
  have hsq : √(3 * (100 * diam X ^ (-(2 / 9 : ℝ)))) ≤ ρ / 8 := by
    rw [show ρ / 8 = √((ρ / 8) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hfrac : 2 * dist p.1 q.1 / diam X ≤ ρ / 2 := by
    rw [div_le_iff₀ hD0]; nlinarith
  linarith

/-- **The response relation at a degree-two neighbour**: if a matched port `q` of a good face
ends at a degree-two face `h`, then `‖k_h τ_h - p + u + Z_h‖ ≤ tol` for a unit vector `u`, where
`p = portVec q`. -/
theorem ext_H_equation :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ (L tol : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane))
        (lab : Set ℂ → Plane × Plane), IsMarking X L G mk → LabelledBy X tol G mk lab →
      ∀ q ∈ unmarkedPorts X L G mk, TrackMated X L G mk q →
        (trackMate X q).1 ∈ (trackGraph X L G mk).Hs G.good →
        ∃ u : ℂ, ‖u‖ = 1 ∧ ‖(G.kMult (trackMate X q).1 : ℂ) * labDir lab (trackMate X q).1 -
          portVec X q + u + longSum X L (trackMate X q).1‖ ≤ tol := by
  filter_upwards [H_face_equation, portVec_mate, exists_side_of_port] with n hface hmate hside hfm
    X hX htri L tol G mk lab hmk hlab q hq hm hH
  obtain ⟨hg', hsp', hnm'⟩ := mem_unmarkedPorts.1 hm.2
  obtain ⟨-, hp', -⟩ := Finset.mem_filter.1 hsp'
  obtain ⟨ab, hab, habe⟩ := hside hfm X hX _ _ hp'
  obtain ⟨u, hu, h⟩ := hface hfm X hX htri L tol G mk lab hmk hlab _ hH _
    (Finset.mem_sdiff.2 ⟨hsp', hnm'⟩) ab hab habe
  refine ⟨u, hu, ?_⟩
  have hne : (trackMate X q).1.Nonempty :=
    nonempty_of_mem_exceptionalFaces ((mem_exceptionalFinset hX.1.2).1 (G.good_subset hg'))
  have hv : ab.2 - ab.1 = -portVec X q := by
    rw [← portVec_eq hne hab habe, hmate hfm X hX htri L G mk q hq hm]
  rw [hv, ← sub_eq_add_neg] at h
  exact h

/-- At most four unmarked short ports at a good face (degree window). -/
lemma card_halfEdges_le_four {X : Finset Plane} (hends : ∀ T ∈ allTracks X, (trackEnds X T).card = 2) {L : ℝ}
    {G : GoodFaces X} {mk : Set ℂ → Finset (Sym2 Plane)} (hmk : IsMarking X L G mk)
    (hwin : DegreeWindow X L G) (F : Set ℂ) :
    ((unmarkedPorts X L G mk).filter (fun q => q.1 = F)).card ≤ 4 := by
  by_cases hF : F ∈ G.good
  · have hdeg := trackGraph_deg hends L G mk hF
    rw [trackGraph, StubGraph.deg_ofHalfEdges (trackMate_isMatching hends L G mk)] at hdeg
    rw [hdeg, Finset.card_sdiff_of_subset (hmk F hF).1, (hmk F hF).2, card_shortPorts]
    have := (hwin F hF).2
    omega
  · rw [Finset.card_eq_zero.2]
    · omega
    · rw [Finset.filter_eq_empty_iff]
      intro q hq hqF
      exact hF (hqF ▸ (mem_unmarkedPorts.1 hq).1)

end Erdos99
end

end CaplessComponents

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `CaplessElim`
-/

section CaplessElim

/-!
# Eliminating the responses of a capless component (Verification Guide §12.2, §13.4)

At a capless component of `G` the closure relations of its faces add up to
`k₀ ζ + Z₀ + Σ_i p_i = 0`, where every outgoing port vector `p_i` is a root of the response
quadratic of its (degree-two) neighbour:
`(k_i + ζ conj Z_i) p² - (k_i ζ + Z_i)(k_i + ζ conj Z_i) p + ζ (k_i ζ + Z_i) = 0`
(`QuadraticResponse.two_circle_eq_poly`).

This file eliminates the `p_i` by iterated resultants and produces a polynomial `elimQ` in `ζ`
alone:

* `respQ k Z Zc`: the response quadratic, a polynomial in `p` whose coefficients are polynomials
  in `T` (the variable standing for `ζ`; `Zc` stands for `conj Z`);
* `elimP k Z Zc j ∈ B[T][w]`: the product of `w + Σ_{i<j} p_i` over all root choices (up to
  leading coefficients), defined by `elimP (j+1) = Res_p (q_j(p), elimP j (w + p))`;
* `elimQ k₀ Z₀ k Z Zc m = elimP m (k₀ T + Z₀)`;
* `elimQ_map`: the construction commutes with ring homomorphisms (used for a degree bound that is
  uniform in the data);
* `elimP_eval_eq_zero` (soundness): exact roots with `w + Σ p_i = 0` make `elimP` vanish;
* `exists_roots_of_elimP_eval` (completeness): conversely, when the leading coefficients do not
  vanish, a zero of `elimP` comes from roots.
-/

open Polynomial

@[expose] public noncomputable section

namespace Erdos99

namespace CaplessElim

variable {B : Type*} [CommRing B]

/-- `a(T) = k T + Z`. -/
def respA (k Z : B) : B[X] := C k * X + C Z

/-- `c(T) = k + T Zc` (the leading coefficient of the response quadratic, `Zc = conj Z`). -/
def respC (k Zc : B) : B[X] := C k + X * C Zc

/-- The response quadratic `c(T) p² - a(T) c(T) p + T a(T)`, a polynomial in `p` with coefficients
in `B[T]`. -/
def respQ (k Z Zc : B) : B[X][X] :=
  C (respC k Zc) * X ^ 2 - C (respA k Z * respC k Zc) * X + C (X * respA k Z)

/-- One elimination step: `Res_p (q(p), P(w + p))`, an element of `B[T][w]`. -/
def elimStep (q : B[X][X]) (n : ℕ) (P : B[X][X]) : B[X][X] :=
  resultant (q.map C) (taylor (X : B[X][X]) (P.map C)) 2 n

/-- The iterated elimination: `elimP 0 = w`, `elimP (j+1) = Res_p (q_j(p), elimP j (w + p))`. -/
def elimP (k Z Zc : ℕ → B) : ℕ → B[X][X]
  | 0 => X
  | j + 1 => elimStep (respQ (k j) (Z j) (Zc j)) (2 ^ j) (elimP k Z Zc j)

/-- The eliminated polynomial in `T`: `elimP m` evaluated at `w = k₀ T + Z₀`. -/
def elimQ (k0 Z0 : B) (k Z Zc : ℕ → B) (m : ℕ) : B[X] :=
  (elimP k Z Zc m).eval (respA k0 Z0)

/-! ## Naturality -/

section map

variable {B' : Type*} [CommRing B'] (φ : B →+* B')

lemma respQ_map (k Z Zc : B) :
    (respQ k Z Zc).map (mapRingHom φ) = respQ (φ k) (φ Z) (φ Zc) := by
  simp [respQ, respA, respC]

lemma elimStep_map (q : B[X][X]) (n : ℕ) (P : B[X][X]) :
    (elimStep q n P).map (mapRingHom φ) =
      elimStep (q.map (mapRingHom φ)) n (P.map (mapRingHom φ)) := by
  rw [elimStep, elimStep, ← coe_mapRingHom (f := mapRingHom φ), ← resultant_map_map]
  congr 1
  · rw [coe_mapRingHom, Polynomial.map_map, Polynomial.map_map]
    congr 1
    ext <;> simp
  · rw [coe_mapRingHom, map_taylor, Polynomial.map_map, Polynomial.map_map]
    simp only [coe_mapRingHom, map_X]
    congr 2
    ext <;> simp

lemma elimP_map (k Z Zc : ℕ → B) (j : ℕ) :
    (elimP k Z Zc j).map (mapRingHom φ) = elimP (φ ∘ k) (φ ∘ Z) (φ ∘ Zc) j := by
  induction j with
  | zero => simp [elimP]
  | succ j ih => rw [elimP, elimP, elimStep_map, ih, respQ_map]; rfl

lemma elimQ_map (k0 Z0 : B) (k Z Zc : ℕ → B) (m : ℕ) :
    (elimQ k0 Z0 k Z Zc m).map φ = elimQ (φ k0) (φ Z0) (φ ∘ k) (φ ∘ Z) (φ ∘ Zc) m := by
  rw [elimQ, elimQ, ← elimP_map φ, ← coe_mapRingHom, ← Polynomial.eval_map_apply]
  simp [respA]

end map

/-! ## Degrees -/

lemma hasseDeriv_map' {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S) (p : R[X]) (i : ℕ) :
    hasseDeriv i (p.map f) = (hasseDeriv i p).map f := by
  ext n; simp [hasseDeriv_coeff, coeff_map]

lemma coeff_taylor_map_C (P : B[X][X]) (i : ℕ) :
    (taylor (X : B[X][X]) (P.map C)).coeff i = hasseDeriv i P := by
  rw [taylor_coeff, hasseDeriv_map', eval_map, eval₂_C_X]

/-- The degree of a resultant: if the coefficients of `f` have degree `≤ a` and those of `g` have
degree `≤ b`, then `Res_{m,n}(f, g)` has degree `≤ n a + m b`. -/
lemma natDegree_resultant_le {A : Type*} [CommRing A] (f g : A[X][X]) (m n : ℕ) {a b : ℕ}
    (hf : ∀ i, (f.coeff i).natDegree ≤ a) (hg : ∀ i, (g.coeff i).natDegree ≤ b) :
    (resultant f g m n).natDegree ≤ n * a + m * b := by
  rw [resultant, Matrix.det_apply]
  refine natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
  refine (natDegree_smul_le _ _).trans ?_
  rw [Fin.prod_univ_add]
  refine natDegree_mul_le.trans ?_
  rw [add_comm (n * a)]
  refine add_le_add ?_ ?_
  · refine (natDegree_prod_le _ _).trans ?_
    refine (Finset.sum_le_sum (g := fun _ => b) fun i _ => ?_).trans (by simp)
    simp only [sylvester, Matrix.of_apply, Fin.addCases_left]
    split_ifs
    · exact hg _
    · simp
  · refine (natDegree_prod_le _ _).trans ?_
    refine (Finset.sum_le_sum (g := fun _ => a) fun i _ => ?_).trans (by simp)
    simp only [sylvester, Matrix.of_apply, Fin.addCases_right]
    split_ifs
    · exact hf _
    · simp

lemma natDegree_elimStep_le (q : B[X][X]) {n : ℕ} {P : B[X][X]} (hP : P.natDegree ≤ n) :
    (elimStep q n P).natDegree ≤ 2 * n := by
  have h := natDegree_resultant_le (q.map C) (taylor (X : B[X][X]) (P.map C)) 2 n (a := 0) (b := n)
    (fun i => by rw [coeff_map, natDegree_C]) (fun i => by
      rw [coeff_taylor_map_C]; exact (natDegree_hasseDeriv_le _ _).trans (by omega))
  simpa [elimStep] using h

lemma natDegree_elimP_le (k Z Zc : ℕ → B) (j : ℕ) : (elimP k Z Zc j).natDegree ≤ 2 ^ j := by
  induction j with
  | zero => simp only [elimP, pow_zero]; exact natDegree_X_le
  | succ j ih => rw [elimP, pow_succ, mul_comm]; exact natDegree_elimStep_le _ ih

lemma natDegree_respQ_le (k Z Zc : B) : (respQ k Z Zc).natDegree ≤ 2 := by
  unfold respQ
  compute_degree

/-! ## Soundness and completeness over `ℂ` -/

lemma eval_map_evalRingHom (P : ℂ[X][X]) (ζ x : ℂ) :
    (P.map (evalRingHom ζ)).eval x = (P.eval (C x)).eval ζ := by
  rw [eval_map, ← coe_evalRingHom, ← eval₂_at_apply (evalRingHom ζ) (C x)]
  simp

/-- The evaluation homomorphism `B[T][w] → ℂ` at `T = ζ`, `w = w₀`. -/
def evTw (ζ w0 : ℂ) : ℂ[X][X] →+* ℂ := (evalRingHom ζ).comp (evalRingHom (C w0))

lemma evTw_C (ζ w0 : ℂ) : (evTw ζ w0).comp C = evalRingHom ζ := by
  ext <;> simp [evTw]

lemma evTw_X (ζ w0 : ℂ) : evTw ζ w0 X = w0 := by simp [evTw]

lemma elimStep_evTw (q P : ℂ[X][X]) (n : ℕ) (ζ w0 : ℂ) :
    evTw ζ w0 (elimStep q n P) =
      resultant (q.map (evalRingHom ζ)) (taylor w0 (P.map (evalRingHom ζ))) 2 n := by
  rw [elimStep, ← resultant_map_map, Polynomial.map_map, evTw_C, map_taylor, evTw_X,
    Polynomial.map_map, evTw_C]

lemma evTw_apply (P : ℂ[X][X]) (ζ w0 : ℂ) : evTw ζ w0 P = (P.eval (C w0)).eval ζ := rfl

/-- **Soundness of the elimination**: if `p_i` (`i < j`) are roots of the response quadratics at
`T = ζ` and `w₀ + Σ_{i<j} p_i = 0`, then `elimP j` vanishes at `(ζ, w₀)`. -/
theorem elimP_eval_eq_zero (k Z Zc : ℕ → ℂ) (ζ : ℂ) (p : ℕ → ℂ) (j : ℕ)
    (hp : ∀ i < j, ((respQ (k i) (Z i) (Zc i)).map (evalRingHom ζ)).eval (p i) = 0)
    (w0 : ℂ) (hw : w0 + ∑ i ∈ Finset.range j, p i = 0) :
    ((elimP k Z Zc j).eval (C w0)).eval ζ = 0 := by
  induction j generalizing w0 with
  | zero => simpa [elimP] using hw
  | succ j ih =>
    rw [← evTw_apply, elimP, elimStep_evTw]
    set f := (respQ (k j) (Z j) (Zc j)).map (evalRingHom ζ)
    set g := taylor w0 ((elimP k Z Zc j).map (evalRingHom ζ))
    have hf : f.natDegree ≤ 2 := natDegree_map_le.trans (natDegree_respQ_le _ _ _)
    have hg : g.natDegree ≤ 2 ^ j := by
      rw [natDegree_taylor]; exact natDegree_map_le.trans (natDegree_elimP_le _ _ _ _)
    obtain ⟨a, b, -, -, hab⟩ := exists_mul_add_mul_eq_C_resultant f g hf hg (Or.inl two_ne_zero)
    have h1 : f.eval (p j) = 0 := hp j (Nat.lt_succ_self j)
    have h2 : g.eval (p j) = 0 := by
      simp only [g, taylor_eval, eval_map_evalRingHom]
      refine ih (fun i hi => hp i (Nat.lt_succ_of_lt hi)) _ ?_
      rw [Finset.sum_range_succ] at hw
      linear_combination hw
    have := congrArg (eval (p j)) hab
    simp only [eval_add, eval_mul, h1, h2, zero_mul, add_zero, eval_C] at this
    exact this.symm

/-- **Completeness of the elimination**: if `elimP j` vanishes at `(ζ, w₀)` and the leading
coefficients `c_i(ζ)` (`i < j`) do not vanish, then there are roots `p_i` of the response quadratics
with `w₀ + Σ_{i<j} p_i = 0`. -/
theorem exists_roots_of_elimP_eval (k Z Zc : ℕ → ℂ) (ζ : ℂ) (j : ℕ)
    (hlc : ∀ i < j, (respC (k i) (Zc i)).eval ζ ≠ 0) (w0 : ℂ)
    (h : ((elimP k Z Zc j).eval (C w0)).eval ζ = 0) :
    ∃ p : ℕ → ℂ, (∀ i < j, ((respQ (k i) (Z i) (Zc i)).map (evalRingHom ζ)).eval (p i) = 0) ∧
      w0 + ∑ i ∈ Finset.range j, p i = 0 := by
  induction j generalizing w0 with
  | zero => exact ⟨0, fun i hi => absurd hi (Nat.not_lt_zero _), by simpa [elimP] using h⟩
  | succ j ih =>
    rw [← evTw_apply, elimP, elimStep_evTw] at h
    set f := (respQ (k j) (Z j) (Zc j)).map (evalRingHom ζ) with hfdef
    set g := taylor w0 ((elimP k Z Zc j).map (evalRingHom ζ))
    have hc2 : f.coeff 2 = (respC (k j) (Zc j)).eval ζ := by
      simp [hfdef, respQ]
    have hfdeg : f.natDegree = 2 := by
      refine le_antisymm (natDegree_map_le.trans (natDegree_respQ_le _ _ _)) ?_
      exact le_natDegree_of_ne_zero (by rw [hc2]; exact hlc j (Nat.lt_succ_self j))
    have hg : g.natDegree ≤ 2 ^ j := by
      rw [natDegree_taylor]; exact natDegree_map_le.trans (natDegree_elimP_le _ _ _ _)
    have hres := resultant_eq_prod_eval f g (2 ^ j) hg (IsAlgClosed.splits f)
    rw [hfdeg, h] at hres
    have hlc0 : f.leadingCoeff ≠ 0 := by
      rw [leadingCoeff, hfdeg, hc2]; exact hlc j (Nat.lt_succ_self j)
    have hprod : (f.roots.map g.eval).prod = 0 := by
      rcases mul_eq_zero.1 hres.symm with h0 | h0
      · exact absurd (pow_eq_zero_iff (by positivity) |>.1 h0) hlc0
      · exact h0
    obtain ⟨y, hy, hgy⟩ := Multiset.mem_map.1 (Multiset.prod_eq_zero_iff.1 hprod)
    have hf0 : f ≠ 0 := fun h0 => by rw [h0, natDegree_zero] at hfdeg; exact two_ne_zero hfdeg.symm
    have hfy : f.eval y = 0 := (mem_roots hf0).1 hy
    have hgy' : ((elimP k Z Zc j).eval (C (w0 + y))).eval ζ = 0 := by
      rw [← eval_map_evalRingHom]
      simpa [g, taylor_eval, add_comm] using hgy
    obtain ⟨p, hp, hsum⟩ := ih (fun i hi => hlc i (Nat.lt_succ_of_lt hi)) (w0 + y) hgy'
    refine ⟨Function.update p j y, fun i hi => ?_, ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · rw [Function.update_of_ne hi.ne]; exact hp i hi
      · rw [Function.update_self]; exact hfy
    · rw [Finset.sum_range_succ, Function.update_self,
        Finset.sum_congr rfl (fun i hi => Function.update_of_ne
          (Finset.mem_range.1 hi).ne _ _)]
      linear_combination hsum

end CaplessElim

end Erdos99
end

end CaplessElim

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `CaplessPoly`
-/

section CaplessPoly

/-!
# The capless-component polynomial is not zero (Verification Guide §12.3, §13.4)

* `elimQ_ne_zero`: for `k₀ > 0`, multiplicities `k_i ∈ {1, 2}` and arbitrary retained sums `Z_i`
  (with `Zc_i = conj Z_i`), the eliminated polynomial `elimQ` is not zero.  Along a real parameter
  `T → ∞` every response root has a normalised limit with nonnegative real part
  (`QuadraticResponse.response_leading_re_nonneg`), so `k₀ T + Z₀ + Σ p_i` cannot vanish.
* `capless_solutions_card_le`: a uniform bound `N₀ m` (depending only on the number `m` of
  responses) on the number of unit `ζ` admitting exact unit solutions of the component relations
  `k₀ ζ + Z₀ + Σ p_i = 0`, `k_i ζ + Z_i - p_i + u_i = 0`.
-/

open Polynomial Filter ComplexConjugate

@[expose] public noncomputable section

namespace Erdos99

namespace CaplessElim

open QuadraticResponse

lemma eval_eval_eq_eval_map (P : ℂ[X][X]) (x : ℂ[X]) (T : ℂ) :
    (P.eval x).eval T = ((P.eval (C (x.eval T))).eval T) := by
  rw [← eval_map_evalRingHom, eval_map, ← coe_evalRingHom, eval₂_at_apply]

lemma respC_eval (k Zc T : ℂ) : (respC k Zc).eval T = k + T * Zc := by simp [respC]; ring

lemma respQ_map_eval (k Z Zc T z : ℂ) :
    ((respQ k Z Zc).map (evalRingHom T)).eval z =
      (k + T * Zc) * z ^ 2 - (k * T + Z) * (k + T * Zc) * z + T * (k * T + Z) := by
  simp [respQ, respA, respC]; ring

/-- **The eliminated polynomial is not zero.** -/
theorem elimQ_ne_zero {k0 : ℝ} (hk0 : 0 < k0) (Z0 : ℂ) (k : ℕ → ℝ) (hk : ∀ i, k i = 1 ∨ k i = 2)
    (Z : ℕ → ℂ) (m : ℕ) :
    elimQ (k0 : ℂ) Z0 (fun i => (k i : ℂ)) Z (fun i => conj (Z i)) m ≠ 0 := by
  intro hQ
  -- the leading coefficients eventually do not vanish
  have hlc : ∀ᶠ T : ℝ in atTop, ∀ i < m, (respC (k i : ℂ) (conj (Z i))).eval (T : ℂ) ≠ 0 := by
    have : ∀ i ∈ Finset.range m, ∀ᶠ T : ℝ in atTop,
        (respC (k i : ℂ) (conj (Z i))).eval (T : ℂ) ≠ 0 := by
      intro i _
      have hki : 0 < k i := by rcases hk i with h | h <;> (rw [h]; norm_num)
      by_cases hZ : Z i = 0
      · refine Eventually.of_forall fun T => ?_
        rw [respC_eval, hZ, map_zero, mul_zero, add_zero]
        exact_mod_cast hki.ne'
      · have hZn : 0 < ‖Z i‖ := norm_pos_iff.2 hZ
        filter_upwards [eventually_gt_atTop (3 / ‖Z i‖)] with T hT
        rw [respC_eval]
        intro h0
        have hT0 : 0 < T := lt_trans (by positivity) hT
        have h1 : (T : ℂ) * conj (Z i) = -(k i : ℂ) := by linear_combination h0
        have h2 := congrArg norm h1
        rw [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg hT0.le, norm_neg,
          Complex.norm_real, Real.norm_of_nonneg hki.le] at h2
        have h3 : 3 < T * ‖Z i‖ := by rwa [div_lt_iff₀ hZn] at hT
        have : k i ≤ 2 := by rcases hk i with h | h <;> simp [h]
        linarith
    filter_upwards [(Finset.eventually_all _).2 this] with T hT i hi
    exact hT i (Finset.mem_range.2 hi)
  -- roots for all large `T`
  have hroots : ∀ᶠ T : ℝ in atTop, ∃ p : ℕ → ℂ,
      (∀ i < m, ((respQ (k i : ℂ) (Z i) (conj (Z i))).map (evalRingHom (T : ℂ))).eval (p i) = 0) ∧
        ((k0 : ℂ) * T + Z0) + ∑ i ∈ Finset.range m, p i = 0 := by
    filter_upwards [hlc] with T hT
    have h0 : ((elimP (fun i => (k i : ℂ)) Z (fun i => conj (Z i)) m).eval
        (C ((respA (k0 : ℂ) Z0).eval (T : ℂ)))).eval (T : ℂ) = 0 := by
      rw [← eval_eval_eq_eval_map]
      have : (elimQ (k0 : ℂ) Z0 (fun i => (k i : ℂ)) Z (fun i => conj (Z i)) m).eval (T : ℂ) = 0 := by
        rw [hQ, eval_zero]
      exact this
    obtain ⟨p, hp, hs⟩ := exists_roots_of_elimP_eval _ _ _ _ m hT _ h0
    refine ⟨p, hp, ?_⟩
    simpa [respA] using hs
  choose! pf hpf using fun (T : ℝ) (h : ∃ p : ℕ → ℂ,
      (∀ i < m, ((respQ (k i : ℂ) (Z i) (conj (Z i))).map (evalRingHom (T : ℂ))).eval (p i) = 0) ∧
        ((k0 : ℂ) * T + Z0) + ∑ i ∈ Finset.range m, p i = 0) => h
  have hev : ∀ᶠ T : ℝ in atTop, (∀ i < m,
      ((respQ (k i : ℂ) (Z i) (conj (Z i))).map (evalRingHom (T : ℂ))).eval (pf T i) = 0) ∧
        ((k0 : ℂ) * T + Z0) + ∑ i ∈ Finset.range m, pf T i = 0 := by
    filter_upwards [hroots] with T hT using hpf T hT
  -- normalised limits
  set ε : ℝ := k0 / (2 * (m + 1)) with hεdef
  have hε : 0 < ε := by positivity
  have hlim : ∀ i ∈ Finset.range m, ∀ᶠ T : ℝ in atTop, ∃ ξ : ℂ, 0 ≤ ξ.re ∧
      ‖pf T i / T - ξ‖ < ε := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    have hz : ∀ᶠ T : ℝ in atTop, (((k i : ℝ) : ℂ) / T + conj (Z i)) * pf T i ^ 2 -
        (((k i : ℝ) : ℂ) * T + Z i) * (((k i : ℝ) : ℂ) / T + conj (Z i)) * pf T i +
          (((k i : ℝ) : ℂ) * T + Z i) = 0 := by
      filter_upwards [hev, eventually_gt_atTop 0] with T hT hT0
      have h := hT.1 i hi'
      rw [respQ_map_eval] at h
      have hTc : (T : ℂ) ≠ 0 := by exact_mod_cast hT0.ne'
      field_simp
      linear_combination h
    filter_upwards [response_leading_re_nonneg (hk i) hz hε] with T hT
    obtain ⟨ξ, -, hξ, h⟩ := hT
    exact ⟨ξ, hξ, h⟩
  have hall := (Finset.eventually_all _).2 hlim
  obtain ⟨T, hT, hTl, hT0, hTb⟩ := (hev.and (hall.and ((eventually_gt_atTop 0).and
    (eventually_gt_atTop (2 * ‖Z0‖ / k0 + 1))))).exists
  choose! ξ hξ0 hξ using hTl
  have hTc : (T : ℂ) ≠ 0 := by exact_mod_cast hT0.ne'
  have hsum : (k0 : ℂ) + Z0 / T + ∑ i ∈ Finset.range m, pf T i / T = 0 := by
    have := hT.2
    rw [← Finset.sum_div]
    field_simp
    linear_combination this
  have hre := congrArg Complex.re hsum
  rw [Complex.add_re, Complex.add_re, Complex.re_sum, Complex.ofReal_re, Complex.zero_re] at hre
  have h1 : -(‖Z0‖ / T) ≤ (Z0 / T).re := by
    have := Complex.abs_re_le_norm (Z0 / T)
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hT0.le] at this
    linarith [neg_abs_le (Z0 / T).re]
  have h2 : ∀ i ∈ Finset.range m, -ε ≤ (pf T i / T).re := by
    intro i hi
    have h3 := hξ i hi
    have h4 : |(pf T i / T - ξ i).re| ≤ ‖pf T i / T - ξ i‖ := Complex.abs_re_le_norm _
    rw [Complex.sub_re] at h4
    have := hξ0 i hi
    linarith [neg_abs_le ((pf T i / T).re - (ξ i).re)]
  have h5 : -(m * ε) ≤ ∑ i ∈ Finset.range m, (pf T i / T).re := by
    have := Finset.sum_le_sum h2
    simpa using this
  have h6 : m * ε ≤ k0 / 2 := by
    rw [hεdef, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h7 : ‖Z0‖ / T < k0 / 2 := by
    rw [div_lt_iff₀ hT0]
    have : 2 * ‖Z0‖ / k0 < T := by linarith
    rw [div_lt_iff₀ hk0] at this
    nlinarith
  linarith

/-! ## A degree bound uniform in the data -/

/-- The universal data ring. -/
abbrev UnivRing : Type := MvPolynomial (Fin 2 ⊕ ℕ × Fin 3) ℂ

/-- The eliminated polynomial for universal data. -/
def univElimQ (m : ℕ) : UnivRing[X] :=
  elimQ (MvPolynomial.X (Sum.inl 0)) (MvPolynomial.X (Sum.inl 1))
    (fun i => MvPolynomial.X (Sum.inr (i, 0))) (fun i => MvPolynomial.X (Sum.inr (i, 1)))
    (fun i => MvPolynomial.X (Sum.inr (i, 2))) m

/-- The uniform degree bound for `m` responses. -/
def capDeg (m : ℕ) : ℕ := (univElimQ m).natDegree

lemma natDegree_elimQ_le (k0 Z0 : ℂ) (k Z Zc : ℕ → ℂ) (m : ℕ) :
    (elimQ k0 Z0 k Z Zc m).natDegree ≤ capDeg m := by
  set φ : UnivRing →+* ℂ := MvPolynomial.eval
    (Sum.elim ![k0, Z0] (fun p => ![k p.1, Z p.1, Zc p.1] p.2))
  have h := elimQ_map φ (MvPolynomial.X (Sum.inl 0)) (MvPolynomial.X (Sum.inl 1))
    (fun i => MvPolynomial.X (Sum.inr (i, 0))) (fun i => MvPolynomial.X (Sum.inr (i, 1)))
    (fun i => MvPolynomial.X (Sum.inr (i, 2))) m
  have e : elimQ (φ (MvPolynomial.X (Sum.inl 0))) (φ (MvPolynomial.X (Sum.inl 1)))
      (φ ∘ fun i => MvPolynomial.X (Sum.inr (i, 0))) (φ ∘ fun i => MvPolynomial.X (Sum.inr (i, 1)))
      (φ ∘ fun i => MvPolynomial.X (Sum.inr (i, 2))) m = elimQ k0 Z0 k Z Zc m := by
    congr 1 <;> first | (funext i; simp [φ]) | simp [φ]
  rw [← e, ← h]
  exact natDegree_map_le

/-- **Few exact solutions** (Verification Guide §13.4): for `k₀ > 0`, `k_i ∈ {1, 2}` and arbitrary
`Z₀, Z_i`, at most `capDeg m` unit `ζ` admit unit vectors `p_i, u_i` (`i < m`) with
`k₀ ζ + Z₀ + Σ_{i<m} p_i = 0` and `k_i ζ + Z_i - p_i + u_i = 0`. -/
theorem capless_solutions_card_le {k0 : ℝ} (hk0 : 0 < k0) (Z0 : ℂ) (k : ℕ → ℝ)
    (hk : ∀ i, k i = 1 ∨ k i = 2) (Z : ℕ → ℂ) (m : ℕ) :
    ∃ S : Finset ℂ, S.card ≤ capDeg m ∧ ∀ ζ : ℂ, ‖ζ‖ = 1 → ∀ p u : ℕ → ℂ,
      (∀ i < m, ‖p i‖ = 1 ∧ ‖u i‖ = 1 ∧ (k i : ℂ) * ζ + Z i - p i + u i = 0) →
      (k0 : ℂ) * ζ + Z0 + ∑ i ∈ Finset.range m, p i = 0 → ζ ∈ S := by
  set Q := elimQ (k0 : ℂ) Z0 (fun i => (k i : ℂ)) Z (fun i => conj (Z i)) m
  refine ⟨Q.roots.toFinset, (Multiset.toFinset_card_le _).trans
    ((card_roots' Q).trans (natDegree_elimQ_le _ _ _ _ _ m)), fun ζ hζ p u hpu hsum => ?_⟩
  rw [Multiset.mem_toFinset, mem_roots (elimQ_ne_zero hk0 Z0 k hk Z m)]
  show ((elimP (fun i => (k i : ℂ)) Z (fun i => conj (Z i)) m).eval
    (respA (k0 : ℂ) Z0)).eval ζ = 0
  rw [eval_eval_eq_eval_map]
  refine elimP_eval_eq_zero _ _ _ ζ p m (fun i hi => ?_) _ ?_
  · obtain ⟨hp, hu, he⟩ := hpu i hi
    have hpa : ‖p i - ((k i : ℝ) * ζ + Z i)‖ = 1 := by
      rw [show p i - ((k i : ℝ) * ζ + Z i) = u i by linear_combination -he, hu]
    have := two_circle_eq_poly (k i) hζ hp hpa
    rw [respQ_map_eval]
    linear_combination this
  · simpa [respA] using hsum

end CaplessElim

end Erdos99
end

end CaplessPoly
