module

public import Mathlib
public import Erdos99.Part01Basics

/-!
# Erdős Problem 99 under finite multiplicity — Part 2 of 9: Pinned locking, Minkowski/Hilbert–Lorentz, polytopes and fans

This is one of the supporting files of the formalization; the main theorem and a precise
description of what is proved are at the top of `Erdos99.lean`.

The file is divided into the following sections (each `section Name … end Name`); comments
elsewhere in the development refer to these sections by name.

* `TriLattice`
* `TrackCross`
* `Release`
* `Pinned`
* `ConeFarkas`
* `LockingAbstract`
* `NegativePlane`
* `MinkowskiPlane`
* `HilbertLorentz`
* `Polytope`
* `PolytopeConnected`
* `MixedVolume`
* `FacetLinks`
* `SimplicialFan`
* `FanGeometry`
* `FanApprox`
* `FanConvexity`
* `FanCrossing`
* `FanIntegration`
* `FanCones`
* `FanGradientExists`
-/

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `TriLattice`
-/

section TriLattice

/-!
# The triangular-lattice comparison (Lemma 3.1)

`Dₙ² ≤ 4 a* n / π`: averaging the number of lattice points of the unit triangular lattice in the
translates of a disk of area `n a*` over a fundamental domain shows that some translate contains
at least `n` lattice points.
-/
open scoped BigOperators Real
open Filter

@[expose] public noncomputable section

open Classical

open MeasureTheory

namespace Erdos99

/-- The two generators `(1,0)` and `(1/2, √3/2)` of the unit triangular lattice. -/
noncomputable def triVec : Fin 2 → Plane := ![!₂[1, 0], !₂[1/2, √3/2]]

lemma triVec_linIndep : LinearIndependent ℝ triVec := by
  unfold triVec
  rw [LinearIndependent.pair_iff]
  intro s t h
  have h0 := congrArg (fun v : Plane => v 0) h
  have h1 := congrArg (fun v : Plane => v 1) h
  simp at h0 h1
  subst h1; simp at h0; exact ⟨h0, rfl⟩

/-- The basis of the triangular lattice. -/
noncomputable def triBasis : Module.Basis (Fin 2) ℝ Plane :=
  basisOfLinearIndependentOfCardEqFinrank triVec_linIndep (by simp)

lemma triBasis_apply (i : Fin 2) : triBasis i = triVec i := by
  simp [triBasis]

lemma volume_triFD : volume (ZSpan.fundamentalDomain triBasis) = ENNReal.ofReal aStar := by
  let b₀ := (EuclideanSpace.basisFun (Fin 2) ℝ)
  rw [ZSpan.measure_fundamentalDomain triBasis volume b₀.toBasis]
  have h1 : volume (ZSpan.fundamentalDomain b₀.toBasis) = 1 := by
    rw [measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped b₀.toBasis volume)]
    rw [OrthonormalBasis.coe_toBasis]
    exact b₀.volume_parallelepiped
  rw [h1, mul_one, Module.Basis.det_apply, Matrix.det_fin_two]
  simp [Module.Basis.toMatrix_apply, triBasis_apply, triVec, aStar, b₀]
  rw [abs_of_pos (by positivity)]


/-- The triangular lattice. -/
noncomputable abbrev triLattice : Submodule ℤ Plane := Submodule.span ℤ (Set.range triBasis)

/-- Nonzero vectors of the triangular lattice have length at least one. -/
lemma one_le_norm_of_mem_triLattice {w : Plane} (hw : w ∈ triLattice) (h0 : w ≠ 0) :
    1 ≤ ‖w‖ := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hw
  have hn : ‖∑ i, c i • triBasis i‖ ^ 2 = ((c 0 : ℝ) ^ 2 + c 0 * c 1 + (c 1 : ℝ) ^ 2) := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [triBasis_apply, triVec]
    simp
    rw [abs_of_nonneg (Real.sqrt_nonneg 3)]
    linear_combination (|(c 1 : ℝ)| ^ 2 / 4) * Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num) +
      (3 / 4) * sq_abs (c 1 : ℝ)
  have hc : c ≠ 0 := by rintro rfl; simp at h0
  have hq : (1 : ℤ) ≤ c 0 ^ 2 + c 0 * c 1 + c 1 ^ 2 := by
    have : c 0 ≠ 0 ∨ c 1 ≠ 0 := by
      by_contra h; push_neg at h; exact hc (by ext i; fin_cases i <;> simp [h.1, h.2])
    rcases this with h | h
    · have := (Int.one_le_abs h)
      nlinarith [sq_nonneg (c 0 + 2 * c 1), sq_abs (c 0), sq_nonneg (c 0), sq_nonneg (c 1)]
    · have := (Int.one_le_abs h)
      nlinarith [sq_nonneg (2 * c 0 + c 1), sq_abs (c 1), sq_nonneg (c 0), sq_nonneg (c 1)]
  have hq' : (1 : ℝ) ≤ (c 0 : ℝ) ^ 2 + c 0 * c 1 + (c 1 : ℝ) ^ 2 := by exact_mod_cast hq
  rw [← hn] at hq'
  nlinarith [norm_nonneg (∑ i, c i • triBasis i)]


/-- Averaging over a fundamental domain: if `n · covol ≤ vol(s)` then some translate of `s`
contains `n` points of the triangular lattice. -/
lemma exists_lattice_points_in_translate {s : Set Plane} (hs : MeasurableSet s) {n : ℕ}
    (hn : 1 ≤ n) (h : (n : ENNReal) * ENNReal.ofReal aStar ≤ volume s) :
    ∃ x : Plane, ∃ T : Finset triLattice, T.card = n ∧ ∀ g ∈ T, (g : Plane) + x ∈ s := by
  by_contra hcon
  push_neg at hcon
  haveI : VAddInvariantMeasure triLattice Plane volume :=
    ⟨fun c t _ => by simp [Submodule.vadd_def]⟩
  have fund := ZSpan.isAddFundamentalDomain triBasis (volume : Measure Plane)
  set F := ZSpan.fundamentalDomain triBasis
  set f : Plane → ENNReal := s.indicator 1
  have hf : Measurable f := measurable_one.indicator hs
  -- pointwise bound on the number of lattice translates
  have hpt : ∀ x : Plane, ∑' g : triLattice, f ((g : Plane) + x) ≤ (n - 1 : ℕ) := by
    intro x
    set S : Set triLattice := {g | (g : Plane) + x ∈ s}
    have hS : S.Finite := by
      by_contra hinf
      obtain ⟨T, hT, hTc⟩ := Set.Infinite.exists_subset_card_eq hinf n
      obtain ⟨g, hg, hgs⟩ := hcon x T hTc
      exact hgs (hT hg)
    have hcard : hS.toFinset.card ≤ n - 1 := by
      by_contra hlt
      obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq (s := hS.toFinset) (n := n) (by omega)
      obtain ⟨g, hg, hgs⟩ := hcon x T hTc
      exact hgs ((hS.mem_toFinset).1 (hT hg))
    rw [tsum_eq_sum (s := hS.toFinset) (fun g hg => by
      simp only [Set.Finite.mem_toFinset] at hg
      exact Set.indicator_of_notMem (show (g : Plane) + x ∉ s from hg) 1)]
    calc ∑ g ∈ hS.toFinset, f ((g : Plane) + x) = ∑ g ∈ hS.toFinset, (1 : ENNReal) :=
          Finset.sum_congr rfl fun g hg => by
            simp only [Set.Finite.mem_toFinset] at hg
            exact Set.indicator_of_mem (show (g : Plane) + x ∈ s from hg) 1
      _ = hS.toFinset.card := by simp
      _ ≤ (n - 1 : ℕ) := by exact_mod_cast hcard
  have hvol : volume s ≤ ((n - 1 : ℕ) : ENNReal) * ENNReal.ofReal aStar := by
    calc volume s = ∫⁻ x, f x := (lintegral_indicator_one hs).symm
      _ = ∑' g : triLattice, ∫⁻ x in F, f (-g +ᵥ x) := fund.lintegral_eq_tsum' f
      _ = ∫⁻ x in F, ∑' g : triLattice, f (-g +ᵥ x) := by
          rw [lintegral_tsum]
          intro g
          exact (hf.comp (measurable_const_add _)).aemeasurable
      _ ≤ ∫⁻ _ in F, ((n - 1 : ℕ) : ENNReal) := by
          apply lintegral_mono
          intro x
          show ∑' g : triLattice, f (-g +ᵥ x) ≤ _
          rw [← (Equiv.neg triLattice).tsum_eq]
          simpa [Submodule.vadd_def] using hpt x
      _ = ((n - 1 : ℕ) : ENNReal) * ENNReal.ofReal aStar := by
          rw [setLIntegral_const, volume_triFD]
  have ha : 0 < aStar := by unfold aStar; positivity
  have h2 := h.trans hvol
  rw [ENNReal.mul_le_mul_iff_left (by simpa using ha) ENNReal.ofReal_ne_top] at h2
  have : n ≤ n - 1 := by exact_mod_cast h2
  omega


/-- Lemma 3.1 (triangular-lattice comparison): `Dₙ² ≤ 4 a* n / π = n / c`.  A disk of area
`n a*` has a translate containing `n` points of the unit triangular lattice. -/
theorem minDiam_sq_le (n : ℕ) (hn : 1 ≤ n) : minDiam n ^ 2 ≤ 4 * aStar * n / π := by
  have ha : 0 < aStar := by unfold aStar; positivity
  set D := √(4 * aStar * n / π) with hD
  have hD2 : D ^ 2 = 4 * aStar * n / π := Real.sq_sqrt (by positivity)
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  have hvol : (n : ENNReal) * ENNReal.ofReal aStar ≤ volume (Metric.ball (0 : Plane) (D / 2)) := by
    rw [InnerProductSpace.volume_ball_of_dim_even (k := 1) (by simp)]
    simp only [finrank_euclideanSpace, Fintype.card_fin, pow_one, Nat.factorial_one,
      Nat.cast_one, div_one]
    rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [div_pow, hD2]
    field_simp
    norm_num
  obtain ⟨x, T, hTc, hT⟩ := exists_lattice_points_in_translate measurableSet_ball hn hvol
  have hinj : Function.Injective (fun g : triLattice => (g : Plane) + x) :=
    fun g g' h => Subtype.ext (add_right_cancel h)
  have hadm : Admissible n (T.image (fun g : triLattice => (g : Plane) + x)) := by
    refine ⟨by rw [Finset.card_image_of_injective _ hinj, hTc], ?_⟩
    simp only [IsSeparated, Finset.mem_image]
    rintro _ ⟨g, hg, rfl⟩ _ ⟨g', hg', rfl⟩ hne
    rw [dist_add_right, dist_eq_norm]
    have hgg : g - g' ≠ 0 := fun h => hne (by rw [sub_eq_zero.1 h])
    have := one_le_norm_of_mem_triLattice (g - g').2 (fun h => hgg (Subtype.ext h))
    simpa using this
  have hle : minDiam n ≤ D := by
    refine (minDiam_le_of_admissible hadm).trans (Metric.diam_le_of_forall_dist_le hD0 ?_)
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
    rintro _ ⟨g, hg, rfl⟩ _ ⟨g', hg', rfl⟩
    have h1 := Metric.mem_ball.1 (hT g hg)
    have h2 := Metric.mem_ball.1 (hT g' hg')
    have := dist_triangle_right ((g : Plane) + x) ((g' : Plane) + x) 0
    linarith
  have h0 : 0 ≤ minDiam n := by
    obtain ⟨X, hX⟩ := exists_isOptimal n
    exact hX.diam_eq ▸ Metric.diam_nonneg
  rw [← hD2]
  exact pow_le_pow_left₀ h0 hle 2

end Erdos99
end

end TriLattice

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `TrackCross`
-/

section TrackCross

/-!
# Two tracks cross at most once (Lemma 3.3)

Fix a track `T` with unit-edge direction `±u`.  Each step along `T` (from an edge to the opposite
side of a rhombus, upwards) is a unit vector at angle `< π/6` from the normal `J u`.  Hence the
displacement between the centres of two distinct rhombi on `T` lies in the open double cone of
half-angle `π/6` about `J u`, i.e. it makes an angle `> π/3` with the line `ℝ u`.  If two distinct
tracks `T, T'` (directions `u, w`) crossed in two distinct rhombi, the displacement between their
centres would make an angle `> π/3` with both lines `ℝ u` and `ℝ w`, while these two lines are at
angle `> π/3` from each other: three lines of the plane pairwise at angle `> π/3`, impossible.
-/

open scoped BigOperators Real

@[expose] public noncomputable section

open Classical

namespace Erdos99

/-- The centre of a finite point set (the average of four points for a rhombus). -/
def cen (R : Finset Plane) : Plane := (1 / 4 : ℝ) • ∑ x ∈ R, x

lemma RhombusData.cen_eq {X R : Finset Plane} {a b c d : Plane} (h : RhombusData X R a b c d) :
    cen R = (1 / 2 : ℝ) • (mid s(a, b) + mid s(c, d)) := by
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := h.distinct
  rw [cen, h.eq, mid_mk, mid_mk, Finset.sum_insert (by simp [d1, d2, d3]),
    Finset.sum_insert (by simp [d4, d5]), Finset.sum_insert (by simp [d6]), Finset.sum_singleton]
  module

/-- Closed cone of half-angle `π/6` about `J u`. -/
def ConeLe (u Δ : Plane) : Prop := |inner ℝ Δ u| * √3 ≤ inner ℝ Δ (rot u)

/-- Open cone of half-angle `π/6` about `J u`. -/
def ConeLt (u Δ : Plane) : Prop := |inner ℝ Δ u| * √3 < inner ℝ Δ (rot u)

lemma ConeLe.zero (u : Plane) : ConeLe u 0 := by simp [ConeLe]

lemma ConeLt.le {u Δ : Plane} (h : ConeLt u Δ) : ConeLe u Δ := le_of_lt h

lemma ConeLe.add {u Δ₁ Δ₂ : Plane} (h1 : ConeLe u Δ₁) (h2 : ConeLe u Δ₂) : ConeLe u (Δ₁ + Δ₂) := by
  unfold ConeLe at *
  rw [inner_add_left, inner_add_left]
  have := abs_add_le (inner ℝ Δ₁ u) (inner ℝ Δ₂ u)
  have h3 : (0 : ℝ) ≤ √3 := Real.sqrt_nonneg 3
  nlinarith

lemma ConeLt.add_le {u Δ₁ Δ₂ : Plane} (h1 : ConeLt u Δ₁) (h2 : ConeLe u Δ₂) :
    ConeLt u (Δ₁ + Δ₂) := by
  unfold ConeLe ConeLt at *
  rw [inner_add_left, inner_add_left]
  have := abs_add_le (inner ℝ Δ₁ u) (inner ℝ Δ₂ u)
  have h3 : (0 : ℝ) ≤ √3 := Real.sqrt_nonneg 3
  nlinarith

lemma ConeLe.smul {u Δ : Plane} (h : ConeLe u Δ) {r : ℝ} (hr : 0 ≤ r) : ConeLe u (r • Δ) := by
  unfold ConeLe at *
  rw [inner_smul_left, inner_smul_left, abs_mul]
  simp only [conj_trivial, abs_of_nonneg hr]
  rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h hr

lemma ConeLt.smul {u Δ : Plane} (h : ConeLt u Δ) {r : ℝ} (hr : 0 < r) : ConeLt u (r • Δ) := by
  unfold ConeLt at *
  rw [inner_smul_left, inner_smul_left, abs_mul]
  simp only [conj_trivial, abs_of_pos hr]
  rw [mul_assoc]; exact mul_lt_mul_of_pos_left h hr

/-- A vector strictly inside the double cone about `J u` makes an angle `> π/3` with `ℝ u`. -/
lemma abs_inner_normalize_lt {u Δ : Plane} (hu : ‖u‖ = 1)
    (h : |inner ℝ Δ u| * √3 < |inner ℝ Δ (rot u)|) :
    Δ ≠ 0 ∧ |inner ℝ (‖Δ‖⁻¹ • Δ) u| < 1 / 2 := by
  have hΔ : Δ ≠ 0 := by rintro rfl; simp at h
  refine ⟨hΔ, ?_⟩
  have hn : 0 < ‖Δ‖ := norm_pos_iff.2 hΔ
  have e := inner_sq_add_inner_rot_sq u Δ
  rw [hu] at e
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3' : (0 : ℝ) ≤ √3 := Real.sqrt_nonneg 3
  have hsq : 3 * inner ℝ Δ u ^ 2 < inner ℝ Δ (rot u) ^ 2 := by
    have := mul_self_lt_mul_self (by positivity) h
    rw [← sq_abs (inner ℝ Δ (rot u)), ← sq_abs (inner ℝ Δ u)]; nlinarith
  rw [inner_smul_left, abs_mul]
  simp only [conj_trivial, abs_inv, abs_norm]
  rw [inv_mul_lt_iff₀ hn]
  have h4 : inner ℝ Δ u ^ 2 < (1 / 2 * ‖Δ‖) ^ 2 := by nlinarith
  rw [mul_comm]; exact abs_lt.2 (abs_lt_of_sq_lt_sq' h4 (by positivity))

section
variable {X : Finset Plane} (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X)
  {T : Finset (Sym2 Plane)} (hT : T ∈ tracks X) {u : Plane} (hu : ‖u‖ = 1)
  (hdir : ∀ e ∈ T, DirOf u e)
include hX htri hT hu hdir

omit hT in
/-- A single upward step along a track lies in the open cone about `J u`. -/
lemma step_coneLt {e f : Sym2 Plane} (he : e ∈ T) (o : OppositeSides X e f)
    (hlt : ht u e < ht u f) : ConeLt u (mid f - mid e) := by
  obtain ⟨a, b, c, d, h, rfl, rfl⟩ := oppositeSides_data hX htri o
  obtain ⟨g, i, n⟩ := h.step (hdir _ he)
  have hm : mid s(c, d) - mid s(a, b) = d - a := by
    rw [mid_mk, mid_mk, h.c_eq]; module
  rw [hm]
  have hp : 0 < inner ℝ (d - a) (rot u) := by linarith
  have e := inner_sq_add_inner_rot_sq u (d - a)
  rw [hu, n] at e
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3' : (0 : ℝ) ≤ √3 := Real.sqrt_nonneg 3
  have hq : inner ℝ (d - a) u ^ 2 < 1 / 4 := by
    rw [← sq_abs]; nlinarith [abs_nonneg (inner ℝ (d - a) u)]
  unfold ConeLt
  have hsq : (|inner ℝ (d - a) u| * √3) ^ 2 < inner ℝ (d - a) (rot u) ^ 2 := by
    rw [mul_pow, sq_abs, h3]; nlinarith
  exact (abs_lt_of_sq_lt_sq' hsq hp.le).2

/-- The displacement along a track between two iterates of the upward step lies in the closed
cone about `J u`. -/
lemma iterate_coneLe {m : Sym2 Plane} (hm : m ∈ T) (i j : ℕ) (hij : i ≤ j) :
    ConeLe u (mid ((upE X u)^[j] m) - mid ((upE X u)^[i] m)) := by
  induction j, hij using Nat.le_induction with
  | base => rw [sub_self]; exact ConeLe.zero u
  | succ j hij ih =>
    rw [Function.iterate_succ_apply']
    set x := (upE X u)^[j] m
    have hx : x ∈ T := iterate_upE_mem (u := u) hT hm j
    by_cases h : upE X u x = x
    · rw [h]; exact ih
    · obtain ⟨o, hlt⟩ := upE_spec h
      have hs := step_coneLt hX htri hu hdir hx o hlt
      have : mid (upE X u x) - mid ((upE X u)^[i] m) =
          (mid (upE X u x) - mid x) + (mid x - mid ((upE X u)^[i] m)) := by abel
      rw [this]; exact (hs.add_le ih).le

/-- Crossing data: a rhombus crossed by `T` has a lower and an upper side on `T`, and its centre
is the average of their midpoints. -/
lemma cross_data {R : Finset Plane} (hR : R ∈ rhombi X) (hc : Crosses T R) :
    ∃ e ∈ T, ∃ f ∈ T, OppositeSides X e f ∧ ht u e < ht u f ∧
      (∀ z, z ∈ R ↔ (z ∈ e ∨ z ∈ f)) ∧ cen R = (1 / 2 : ℝ) • (mid e + mid f) := by
  obtain ⟨a, b, c, d, h⟩ := exists_rhombusData hX htri hR
  have key : ∀ {a b c d : Plane}, RhombusData X R a b c d → T = trackOf X s(a, b) →
      ∃ e ∈ T, ∃ f ∈ T, OppositeSides X e f ∧ ht u e < ht u f ∧
        (∀ z, z ∈ R ↔ (z ∈ e ∨ z ∈ f)) ∧ cen R = (1 / 2 : ℝ) • (mid e + mid f) := by
    intro a b c d h hTab
    have hab : s(a, b) ∈ T := hTab ▸ mem_trackOf_self h.rhombusEdge_ab
    have hcd : s(c, d) ∈ T := opp_mem_track hT hab h.opp
    have hmem : ∀ z, z ∈ R ↔ (z ∈ s(a, b) ∨ z ∈ s(c, d)) := fun z => by
      rw [h.eq]; simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.mem_iff]; tauto
    have hgap := step_sq_gap hX htri hu (hdir _ hab) h.opp
    rcases lt_or_gt_of_ne (show ht u s(a, b) ≠ ht u s(c, d) from fun he => by
      rw [he, sub_self] at hgap; norm_num at hgap) with hlt | hlt
    · exact ⟨_, hab, _, hcd, h.opp, hlt, hmem, h.cen_eq⟩
    · exact ⟨_, hcd, _, hab, oppositeSides_symm h.opp, hlt, fun z => (hmem z).trans or_comm,
        by rw [h.cen_eq, add_comm]⟩
  rcases h.crosses hT hc with hTab | hTbc
  · exact key h hTab
  · exact key h.rotate hTbc

/-- The centres of two distinct rhombi on a track differ by a vector in the open double cone
about `J u`. -/
lemma cen_sub_cone {R₁ R₂ : Finset Plane} (hR₁ : R₁ ∈ rhombi X) (hR₂ : R₂ ∈ rhombi X)
    (hc₁ : Crosses T R₁) (hc₂ : Crosses T R₂) (hne : R₁ ≠ R₂) :
    |inner ℝ (cen R₂ - cen R₁) u| * √3 < |inner ℝ (cen R₂ - cen R₁) (rot u)| := by
  obtain ⟨e1, he1, f1, hf1, o1, l1, m1, c1⟩ := cross_data hX htri hT hu hdir hR₁ hc₁
  obtain ⟨e2, he2, f2, hf2, o2, l2, m2, c2⟩ := cross_data hX htri hT hu hdir hR₂ hc₂
  obtain ⟨m, hm, hmin⟩ := T.exists_min_image (ht u) ⟨e1, he1⟩
  obtain ⟨k1, rfl⟩ := mem_range_iterate hX htri hT hu hdir hm hmin he1
  obtain ⟨k2, rfl⟩ := mem_range_iterate hX htri hT hu hdir hm hmin he2
  have hf1' : f1 = (upE X u)^[k1 + 1] m := by
    rw [Function.iterate_succ_apply', upE_eq hX htri hu hdir he1 o1 l1]
  have hf2' : f2 = (upE X u)^[k2 + 1] m := by
    rw [Function.iterate_succ_apply', upE_eq hX htri hu hdir he2 o2 l2]
  have hk : k1 ≠ k2 := by
    rintro rfl
    apply hne
    have : f1 = f2 := by rw [hf1', hf2']
    subst this
    ext z; rw [m1, m2]
  -- the general fact for `k < k'`
  have gen : ∀ {Ra Rb : Finset Plane} {ka kb : ℕ} {fa fb : Sym2 Plane}, ka < kb →
      fa = (upE X u)^[ka + 1] m → fb = (upE X u)^[kb + 1] m →
      OppositeSides X ((upE X u)^[ka] m) fa → ht u ((upE X u)^[ka] m) < ht u fa →
      OppositeSides X ((upE X u)^[kb] m) fb → ht u ((upE X u)^[kb] m) < ht u fb →
      cen Ra = (1 / 2 : ℝ) • (mid ((upE X u)^[ka] m) + mid fa) →
      cen Rb = (1 / 2 : ℝ) • (mid ((upE X u)^[kb] m) + mid fb) →
      ConeLt u (cen Rb - cen Ra) := by
    intro Ra Rb ka kb fa fb hlt hfa hfb oa la ob lb ca cb
    have sa := step_coneLt hX htri hu hdir (iterate_upE_mem (u := u) hT hm ka) oa la
    have sb := step_coneLt hX htri hu hdir (iterate_upE_mem (u := u) hT hm kb) ob lb
    have mid_le := iterate_coneLe hX htri hT hu hdir hm (ka + 1) kb hlt
    rw [← hfa] at mid_le
    have : cen Rb - cen Ra = (1 / 2 : ℝ) • (mid fa - mid ((upE X u)^[ka] m)) +
        ((mid ((upE X u)^[kb] m) - mid fa) +
          (1 / 2 : ℝ) • (mid fb - mid ((upE X u)^[kb] m))) := by
      rw [ca, cb]; module
    rw [this]
    exact (sa.smul (by norm_num)).add_le (mid_le.add (sb.smul (by norm_num)).le)
  rcases lt_or_gt_of_ne hk with h | h
  · have := gen h hf1' hf2' o1 l1 o2 l2 c1 c2
    unfold ConeLt at this
    exact lt_of_lt_of_le this (le_abs_self _)
  · have := gen h hf2' hf1' o2 l2 o1 l1 c2 c1
    unfold ConeLt at this
    rw [← neg_sub, inner_neg_left, inner_neg_left, abs_neg, abs_neg]
    exact lt_of_lt_of_le this (le_abs_self _)

end

/-- **Lemma 3.3 (simplicity of the crossing graph).**  In a separated set without unit triangles,
two distinct tracks cross in at most one rhombus. -/
theorem tracks_cross_at_most_once_of_separated {X : Finset Plane} (hX : IsSeparated X)
    (htri : ¬ HasUnitTriangle X) {T T' : Finset (Sym2 Plane)} (hT : T ∈ tracks X)
    (hT' : T' ∈ tracks X) (hne : T ≠ T') :
    ((rhombi X).filter (fun R => Crosses T R ∧ Crosses T' R)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro R₁ h₁ R₂ h₂
  obtain ⟨hR₁, c₁, c₁'⟩ := Finset.mem_filter.1 h₁
  obtain ⟨hR₂, c₂, c₂'⟩ := Finset.mem_filter.1 h₂
  by_contra hR
  obtain ⟨e0, he0, hu0⟩ := exists_rep_of_mem_tracks hT
  obtain ⟨f0, hf0, hw0⟩ := exists_rep_of_mem_tracks hT'
  have hu : ‖dv e0‖ = 1 := norm_dv_of_mem_unitEdges hu0
  have hw : ‖dv f0‖ = 1 := norm_dv_of_mem_unitEdges hw0
  have hdirT : ∀ e ∈ T, DirOf (dv e0) e := fun e he => by
    rw [eq_trackOf_of_mem hT he0] at he; exact sameDir_of_mem_trackOf he
  have hdirT' : ∀ e ∈ T', DirOf (dv f0) e := fun e he => by
    rw [eq_trackOf_of_mem hT' hf0] at he; exact sameDir_of_mem_trackOf he
  have hadj : (crossingGraph X).Adj T T' := ⟨hne, hT, hT', R₁, hR₁, c₁, c₁'⟩
  have huw := abs_inner_lt_of_adj hX htri hadj he0 hf0
  obtain ⟨hΔ, h1⟩ := abs_inner_normalize_lt hu (cen_sub_cone hX htri hT hu hdirT hR₁ hR₂ c₁ c₂ hR)
  obtain ⟨-, h2⟩ := abs_inner_normalize_lt hw (cen_sub_cone hX htri hT' hw hdirT' hR₁ hR₂ c₁' c₂' hR)
  have hn : ‖‖cen R₂ - cen R₁‖⁻¹ • (cen R₂ - cen R₁)‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hΔ)]
  exact no_three_spread_unit_vectors _ _ _ hn hu hw h1 huw h2

/-! ### Counting tracks -/

/-- The tracks partition the rhombus edges. -/
lemma sum_card_tracks (X : Finset Plane) : ∑ T ∈ tracks X, T.card = (rhombusEdges X).card := by
  rw [← Finset.card_biUnion]
  · congr 1
    ext e
    simp only [Finset.mem_biUnion]
    constructor
    · rintro ⟨T, hT, he⟩
      obtain ⟨e0, -, rfl⟩ := Finset.mem_image.1 hT
      exact (mem_trackOf.1 he).1
    · intro he
      exact ⟨trackOf X e, Finset.mem_image_of_mem _ he, mem_trackOf_self he⟩
  · intro T hT T' hT' hne
    show Disjoint T T'
    rw [Finset.disjoint_left]
    intro e h1 h2
    exact hne ((eq_trackOf_of_mem hT h1).trans (eq_trackOf_of_mem hT' h2).symm)

/-- Each rhombus lies on exactly two tracks, so `∑_T r(T) = 2q`. -/
lemma sum_trackLength {X : Finset Plane} (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X) :
    ∑ T ∈ tracks X, trackLength X T = 2 * (rhombi X).card := by
  unfold trackLength
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm, mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun R hR => ?_
  rw [← Finset.card_filter]
  obtain ⟨T, hT, T', hT', hne, hiff⟩ := rhombus_two_tracks_of_separated hX htri hR
  have : (tracks X).filter (fun T'' => Crosses T'' R) = {T, T'} := by
    ext T''
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩; exact (hiff T'' h1).1 h2
    · rintro (rfl | rfl)
      · exact ⟨hT, (hiff _ hT).2 (Or.inl rfl)⟩
      · exact ⟨hT', (hiff _ hT').2 (Or.inr rfl)⟩
  rw [this, Finset.card_pair hne]

/-- `s + 2q ≤ m`: each track has one more edge than rhombi, and the tracks partition the rhombus
edges. -/
theorem card_tracks_add_two_mul_card_rhombi_le {X : Finset Plane} (hX : IsSeparated X)
    (htri : ¬ HasUnitTriangle X) :
    (tracks X).card + 2 * (rhombi X).card ≤ (unitEdges X).card := by
  have h1 : ∑ T ∈ tracks X, (trackLength X T + 1) ≤ ∑ T ∈ tracks X, T.card :=
    Finset.sum_le_sum fun T hT => trackLength_add_one_le_card hX htri hT
  rw [Finset.sum_add_distrib, sum_trackLength hX htri, sum_card_tracks, Finset.sum_const,
    smul_eq_mul, mul_one] at h1
  have h2 : (rhombusEdges X).card ≤ (unitEdges X).card := Finset.card_le_card (Finset.filter_subset _ _)
  omega

end Erdos99
end

end TrackCross

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `Release`
-/

section Release

/-!
# Releases and finite multiplicity

If `h(n) < ∞`, there is no one-parameter family of optimal configurations along which the
congruence invariant `∑_{p,q} |p - q|²` takes infinitely many values.  As a first application we
prove the boundary part of Lemma 2.1: a boundary point of the hull of a (non-collinear) optimal
configuration is a diameter endpoint (otherwise it could be pushed outwards), hence a hull vertex.
-/

open scoped BigOperators Real

@[expose] public noncomputable section

open Classical

namespace Erdos99

/-- The congruence invariant `∑_{p, q ∈ Y} |p - q|²`. -/
def sqSum (Y : Finset Plane) : ℝ := ∑ p ∈ Y, ∑ q ∈ Y, dist p q ^ 2

lemma sqSum_image (Y : Finset Plane) (e : Plane ≃ᵢ Plane) : sqSum (Y.image e) = sqSum Y := by
  unfold sqSum
  rw [Finset.sum_image (fun x _ y _ h => e.injective h)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_image (fun x _ y _ h => e.injective h)]
  simp [e.dist_eq]

lemma sqSum_congr {X Y : Finset Plane} (h : Congruent X Y) : sqSum X = sqSum Y := by
  obtain ⟨e, rfl⟩ := h; exact (sqSum_image X e).symm

lemma congruent_refl (X : Finset Plane) : Congruent X X :=
  ⟨IsometryEquiv.refl _, by ext; simp [IsometryEquiv.refl]⟩

/-- **Finite multiplicity excludes releases.**  If `h(n) < ∞`, there is no family of optimal
configurations, indexed by an interval, on which `sqSum` is injective. -/
theorem false_of_release {n : ℕ} (hfm : numOptimalClasses n < ⊤) {δ : ℝ} (hδ : 0 < δ)
    (F : ℝ → Finset Plane) (hopt : ∀ t ∈ Set.Ioo 0 δ, IsOptimal n (F t))
    (hinj : Set.InjOn (fun t => sqSum (F t)) (Set.Ioo 0 δ)) : False := by
  set K := {C : Set (Finset Plane) |
    ∃ X, IsOptimal n X ∧ C = {Y | IsOptimal n Y ∧ Congruent X Y}}
  have hK : K.Finite := Set.encard_lt_top_iff.1 hfm
  let g : ℝ → Set (Finset Plane) := fun t => {Y | IsOptimal n Y ∧ Congruent (F t) Y}
  have hsub : g '' Set.Ioo 0 δ ⊆ K := by
    rintro _ ⟨t, ht, rfl⟩; exact ⟨F t, hopt t ht, rfl⟩
  have hginj : Set.InjOn g (Set.Ioo 0 δ) := by
    intro s hs t ht hst
    have : F t ∈ g s := by rw [hst]; exact ⟨hopt t ht, congruent_refl _⟩
    exact hinj hs ht (sqSum_congr this.2)
  exact Set.Ioo_infinite hδ (Set.Finite.of_finite_image (hK.subset hsub) hginj)

lemma sqSum_insert {S : Finset Plane} {z : Plane} (hz : z ∉ S) :
    sqSum (insert z S) = sqSum S + 2 * ∑ q ∈ S, dist z q ^ 2 := by
  unfold sqSum
  rw [Finset.sum_insert hz, Finset.sum_insert hz, dist_self]
  simp only [Finset.sum_insert hz, Finset.sum_add_distrib]
  have : ∑ p ∈ S, dist p z ^ 2 = ∑ q ∈ S, dist z q ^ 2 :=
    Finset.sum_congr rfl fun p _ => by rw [dist_comm]
  rw [this]; ring

lemma dist_add_smul_sq (x y ν : Plane) (t : ℝ) :
    dist (x + t • ν) y ^ 2 = dist x y ^ 2 + 2 * t * inner ℝ (x - y) ν + t ^ 2 * ‖ν‖ ^ 2 := by
  rw [dist_eq_norm, dist_eq_norm, show x + t • ν - y = (x - y) + t • ν by abel,
    norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

/-- A finite planar set that is not collinear has a convex hull with nonempty interior. -/
lemma affineSpan_eq_top_of_not_collinear {s : Set Plane} (h : ¬ Collinear ℝ s) :
    affineSpan ℝ s = ⊤ := by
  by_contra hne
  apply h
  rw [collinear_iff_finrank_le_one]
  have hs : s.Nonempty := by
    by_contra he; rw [Set.not_nonempty_iff_eq_empty] at he; subst he; exact h (collinear_empty _ _)
  have hv : vectorSpan ℝ s ≠ ⊤ := by
    intro hv; apply hne
    rw [← AffineSubspace.direction_eq_top_iff_of_nonempty ((affineSpan_nonempty ℝ).2 hs),
      direction_affineSpan, hv]
  have := Submodule.finrank_lt hv
  simp at this
  omega

/-- A supporting direction at a boundary point of the hull of a non-collinear finite set. -/
lemma exists_support_vector {X : Finset Plane} (hcol : ¬ Collinear ℝ (X : Set Plane)) {x : Plane}
    (hfr : x ∈ frontier (convexHull ℝ (X : Set Plane))) :
    ∃ ν : Plane, ν ≠ 0 ∧ ∀ y ∈ X, inner ℝ ν y ≤ inner ℝ ν x := by
  set K := convexHull ℝ (X : Set Plane)
  have hint : (interior K).Nonempty :=
    interior_convexHull_nonempty_iff_affineSpan_eq_top.2 (affineSpan_eq_top_of_not_collinear hcol)
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point (convex_convexHull ℝ _).interior
    isOpen_interior hfr.2
  set ν := (InnerProductSpace.toDual ℝ Plane).symm f
  have hν : ∀ y, inner ℝ ν y = f y := fun y => InnerProductSpace.toDual_symm_apply
  refine ⟨ν, ?_, fun y hy => ?_⟩
  · intro h0
    obtain ⟨a, ha⟩ := hint
    have := hf a ha
    rw [← hν, ← hν, h0, inner_zero_left, inner_zero_left] at this
    exact lt_irrefl _ this
  · have hyK : y ∈ closure (interior K) := by
      rw [(convex_convexHull ℝ _).closure_interior_eq_closure_of_nonempty_interior hint]
      exact subset_closure (subset_convexHull ℝ _ hy)
    have hcl : closure (interior K) ⊆ {a | f a ≤ f x} :=
      closure_minimal (fun a ha => (hf a ha).le) (isClosed_le f.continuous continuous_const)
    rw [hν, hν]; exact hcl hyK

/-- **Lemma 2.1 (boundary points), diameter part.**  Under finite multiplicity, a boundary point of
the hull of a non-collinear optimal set has a diameter partner: otherwise it could be pushed
outwards along a supporting normal, giving a release. -/
theorem exists_diam_partner_of_frontier {n : ℕ} (hn : 2 ≤ n) (hfm : numOptimalClasses n < ⊤)
    {X : Finset Plane} (hX : IsOptimal n X) (hcol : ¬ Collinear ℝ (X : Set Plane)) {x : Plane}
    (hx : x ∈ X) (hfr : x ∈ frontier (convexHull ℝ (X : Set Plane))) :
    ∃ y ∈ X, dist x y = diam X := by
  by_contra hcon
  push_neg at hcon
  set D := diam X
  have hlt : ∀ y ∈ X, dist x y < D := fun y hy => lt_of_le_of_ne (dist_le_diam hx hy) (hcon y hy)
  obtain ⟨ν, hν0, hν⟩ := exists_support_vector hcol hfr
  have hνpos : 0 < ‖ν‖ := norm_pos_iff.2 hν0
  obtain ⟨y0, hy0, hmin⟩ := Finset.exists_min_image X (fun y => D - dist x y) ⟨x, hx⟩
  set ε := D - dist x y0
  have hε : 0 < ε := by have := hlt y0 hy0; simp only [ε]; linarith
  have hεy : ∀ y ∈ X, dist x y + ε ≤ D := fun y hy => by have := hmin y hy; simp at this; linarith
  set S := X.erase x
  have hSne : S.Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hx, hX.1.1]; omega
  have hinner : ∀ y ∈ X, 0 ≤ inner ℝ (x - y) ν := fun y hy => by
    rw [real_inner_comm, inner_sub_right]; linarith [hν y hy]
  -- distances from the moved point grow
  have hgrow : ∀ t : ℝ, 0 ≤ t → ∀ y ∈ X, dist x y ≤ dist (x + t • ν) y := fun t ht y hy => by
    have h := dist_add_smul_sq x y ν t
    have : dist x y ^ 2 ≤ dist (x + t • ν) y ^ 2 := by
      rw [h]; have := hinner y hy; nlinarith [sq_nonneg t, sq_nonneg ‖ν‖]
    exact (pow_le_pow_iff_left₀ dist_nonneg dist_nonneg two_ne_zero).1 this
  let F : ℝ → Finset Plane := fun t => insert (x + t • ν) S
  have hnot : ∀ t : ℝ, 0 ≤ t → x + t • ν ∉ S := fun t ht hm => by
    obtain ⟨hne, hmX⟩ := Finset.mem_erase.1 hm
    have h1 := hX.1.2 _ hmX _ hx hne
    have h2 := hgrow t ht _ hmX
    rw [dist_self] at h2
    linarith [dist_comm (x + t • ν) x]
  refine false_of_release hfm (δ := ε / ‖ν‖) (div_pos hε hνpos) F (fun t ht => ?_) ?_
  · obtain ⟨ht0, htδ⟩ := ht
    have htν : t * ‖ν‖ < ε := by rwa [lt_div_iff₀ hνpos] at htδ
    have hcard : (F t).card = n := by
      rw [Finset.card_insert_of_notMem (hnot t ht0.le), Finset.card_erase_of_mem hx, hX.1.1]
      omega
    have hsep : IsSeparated (F t) := by
      intro p hp q hq hpq
      simp only [F, Finset.mem_insert] at hp hq
      rcases hp with rfl | hp <;> rcases hq with rfl | hq
      · exact absurd rfl hpq
      · exact (hX.1.2 _ (Finset.mem_of_mem_erase hq) _ hx (Finset.ne_of_mem_erase hq)).trans
          ((dist_comm _ _).le.trans (hgrow t ht0.le _ (Finset.mem_of_mem_erase hq)))
      · rw [dist_comm]
        exact (hX.1.2 _ (Finset.mem_of_mem_erase hp) _ hx (Finset.ne_of_mem_erase hp)).trans
          ((dist_comm _ _).le.trans (hgrow t ht0.le _ (Finset.mem_of_mem_erase hp)))
      · exact hX.1.2 _ (Finset.mem_of_mem_erase hp) _ (Finset.mem_of_mem_erase hq) hpq
    have hdiam : diam (F t) ≤ D := by
      have hD0 : 0 ≤ D := Metric.diam_nonneg
      have hmove : ∀ q ∈ S, dist (x + t • ν) q ≤ D := fun q hq => by
        have hq' := Finset.mem_of_mem_erase hq
        calc dist (x + t • ν) q ≤ dist (x + t • ν) x + dist x q := dist_triangle _ _ _
          _ = t * ‖ν‖ + dist x q := by
            rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht0.le]
          _ ≤ D := by linarith [hεy q hq']
      apply Metric.diam_le_of_forall_dist_le hD0
      intro p hp q hq
      simp only [F, Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hp hq
      rcases hp with rfl | hp <;> rcases hq with rfl | hq
      · simp [hD0]
      · exact hmove q hq
      · rw [dist_comm]; exact hmove p hp
      · exact dist_le_diam (Finset.mem_of_mem_erase hp) (Finset.mem_of_mem_erase hq)
    exact ⟨⟨hcard, hsep⟩, fun Y hY => hdiam.trans (hX.2 Y hY)⟩
  · apply StrictMonoOn.injOn
    intro s hs t ht hst
    simp only [F]
    rw [sqSum_insert (hnot s hs.1.le), sqSum_insert (hnot t ht.1.le)]
    have : ∑ q ∈ S, dist (x + s • ν) q ^ 2 < ∑ q ∈ S, dist (x + t • ν) q ^ 2 := by
      apply Finset.sum_lt_sum_of_nonempty hSne
      intro q hq
      rw [dist_add_smul_sq, dist_add_smul_sq]
      have := hinner q (Finset.mem_of_mem_erase hq)
      have h1 : s ^ 2 * ‖ν‖ ^ 2 < t ^ 2 * ‖ν‖ ^ 2 := by
        apply mul_lt_mul_of_pos_right _ (by positivity)
        exact pow_lt_pow_left₀ hst hs.1.le two_ne_zero
      nlinarith
    linarith

end Erdos99
end

end Release

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `Pinned`
-/

section Pinned

/-!
# Pinned counting (Lemma 2.2, first inequality)

Pin the hull vertices of an optimal configuration.  A velocity that vanishes on the hull vertices
and does not shorten unit pairs integrates along its straight path to a family of optimal
configurations; under finite multiplicity it must vanish.  Hence the unit rows incident with the
interior positively span the `2(n - b)` pinned coordinates, so `m - t_B ≥ 2(n - b) + 1`.
-/

open scoped BigOperators Real

@[expose] public noncomputable section

open Classical Module

namespace Erdos99

/-- A uniform gap: the distances of a finite set that differ from `a` differ by at least `γ`. -/
lemma exists_gap (X : Finset Plane) (a : ℝ) :
    ∃ γ > 0, ∀ p ∈ X, ∀ q ∈ X, dist p q ≠ a → γ ≤ |dist p q - a| := by
  set S := ((X ×ˢ X).filter (fun pq => dist pq.1 pq.2 ≠ a)).image (fun pq => |dist pq.1 pq.2 - a|)
  rcases S.eq_empty_or_nonempty with hS | hS
  · refine ⟨1, one_pos, fun p hp q hq hpq => ?_⟩
    have : |dist p q - a| ∈ S := Finset.mem_image.2 ⟨(p, q), by simp [hp, hq, hpq], rfl⟩
    rw [hS] at this; simp at this
  · refine ⟨S.min' hS, ?_, fun p hp q hq hpq => S.min'_le _
      (Finset.mem_image.2 ⟨(p, q), by simp [hp, hq, hpq], rfl⟩)⟩
    obtain ⟨⟨p, q⟩, hpq, he⟩ := Finset.mem_image.1 (S.min'_mem hS)
    rw [← he]
    simp only [Finset.mem_filter] at hpq
    exact abs_pos.2 (sub_ne_zero.2 hpq.2)

lemma dist_move_sq (p q vp vq : Plane) (t : ℝ) :
    dist (p + t • vp) (q + t • vq) ^ 2 =
      dist p q ^ 2 + 2 * t * inner ℝ (p - q) (vp - vq) + t ^ 2 * ‖vp - vq‖ ^ 2 := by
  rw [dist_eq_norm, dist_eq_norm, show p + t • vp - (q + t • vq) = (p - q) + t • (vp - vq) by
    rw [smul_sub]; abel, norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs]
  ring

lemma dist_move_le (p q vp vq : Plane) (t : ℝ) (ht : 0 ≤ t) :
    |dist (p + t • vp) (q + t • vq) - dist p q| ≤ t * (‖vp‖ + ‖vq‖) := by
  have h1 : dist (p + t • vp) p = t * ‖vp‖ := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht]
  have h2 : dist (q + t • vq) q = t * ‖vq‖ := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht]
  rw [abs_le]
  constructor
  · have := dist_triangle4 p (p + t • vp) (q + t • vq) q
    rw [dist_comm p (p + t • vp), h1, h2] at this; linarith
  · have := dist_triangle4 (p + t • vp) p q (q + t • vq)
    rw [h1, dist_comm q (q + t • vq), h2] at this; linarith

/-- The diameter of a nonempty finite set is attained. -/
lemma exists_dist_eq_diam {X : Finset Plane} (hX : X.Nonempty) :
    ∃ a ∈ X, ∃ b ∈ X, dist a b = diam X := by
  obtain ⟨⟨a, b⟩, hab, hmax⟩ := Finset.exists_max_image (X ×ˢ X) (fun pq => dist pq.1 pq.2)
    (hX.product hX)
  rw [Finset.mem_product] at hab
  refine ⟨a, hab.1, b, hab.2, le_antisymm (dist_le_diam hab.1 hab.2) ?_⟩
  apply Metric.diam_le_of_forall_dist_le dist_nonneg
  intro p hp q hq
  exact hmax (p, q) (Finset.mem_product.2 ⟨hp, hq⟩)

/-- **Pinned locking.**  Under finite multiplicity, a velocity on an optimal set which vanishes on
the hull vertices and does not shorten unit pairs vanishes identically. -/
theorem pinned_locking {n : ℕ} (hn : 2 ≤ n) (hfm : numOptimalClasses n < ⊤) {X : Finset Plane}
    (hX : IsOptimal n X) (v : Plane → Plane) (hv0 : ∀ p ∈ hullVertices X, v p = 0)
    (hunit : ∀ p ∈ X, ∀ q ∈ X, dist p q = 1 → 0 ≤ inner ℝ (p - q) (v p - v q)) :
    ∀ p ∈ X, v p = 0 := by
  by_contra hne
  push_neg at hne
  obtain ⟨p0, hp0, hvp0⟩ := hne
  set D := diam X
  have hD : 0 < D := hX.diam_pos hn
  have hXne : X.Nonempty := ⟨p0, hp0⟩
  -- a hull vertex, where `v` vanishes
  obtain ⟨a, ha, b, hb, hab⟩ := exists_dist_eq_diam hXne
  have hab' : a ≠ b := by rintro rfl; rw [dist_self] at hab; exact hD.ne hab
  have hva : v a = 0 := hv0 a (mem_hullVertices_of_diam ha hb hab' hab)
  set M := ∑ r ∈ X, ‖v r‖
  have hM : ∀ r ∈ X, ‖v r‖ ≤ M := fun r hr =>
    Finset.single_le_sum (f := fun r => ‖v r‖) (fun _ _ => norm_nonneg _) hr
  have hMpos : 0 < M := lt_of_lt_of_le (norm_pos_iff.2 hvp0) (hM p0 hp0)
  obtain ⟨γ1, hγ1, hg1⟩ := exists_gap X 1
  obtain ⟨γ2, hγ2, hg2⟩ := exists_gap X D
  set γ := min γ1 γ2
  have hγ : 0 < γ := lt_min hγ1 hγ2
  set δ1 := γ / (2 * M)
  have hδ1 : 0 < δ1 := div_pos hγ (by linarith)
  let f : ℝ → Plane → Plane := fun t p => p + t • v p
  have hclose : ∀ t ∈ Set.Ioo 0 δ1, ∀ p ∈ X, ∀ q ∈ X,
      |dist (f t p) (f t q) - dist p q| < γ := fun t ht p hp q hq => by
    have h1 := dist_move_le p q (v p) (v q) t ht.1.le
    have h2 : t * (‖v p‖ + ‖v q‖) ≤ t * (2 * M) := by
      apply mul_le_mul_of_nonneg_left _ ht.1.le; linarith [hM p hp, hM q hq]
    have h3 : t * (2 * M) < γ := by
      have := ht.2; rw [lt_div_iff₀ (by linarith)] at this; linarith
    exact lt_of_le_of_lt (h1.trans h2) h3
  have hsep : ∀ t ∈ Set.Ioo 0 δ1, ∀ p ∈ X, ∀ q ∈ X, p ≠ q → 1 ≤ dist (f t p) (f t q) := by
    intro t ht p hp q hq hpq
    by_cases h1 : dist p q = 1
    · have e := dist_move_sq p q (v p) (v q) t
      have := hunit p hp q hq h1
      have hsq : 1 ≤ dist (f t p) (f t q) ^ 2 := by
        simp only [f]; rw [e, h1]; have := ht.1; nlinarith [sq_nonneg (t * ‖v p - v q‖)]
      nlinarith [dist_nonneg (x := f t p) (y := f t q)]
    · have hg := hg1 p hp q hq h1
      have hge := hX.1.2 p hp q hq hpq
      rw [abs_of_nonneg (by linarith)] at hg
      have := abs_lt.1 (hclose t ht p hp q hq)
      have : γ ≤ γ1 := min_le_left _ _
      linarith
  have hupper : ∀ t ∈ Set.Ioo 0 δ1, ∀ p ∈ X, ∀ q ∈ X, dist (f t p) (f t q) ≤ D := by
    intro t ht p hp q hq
    by_cases h2 : dist p q = D
    · have hpq : p ≠ q := by rintro rfl; rw [dist_self] at h2; exact hD.ne h2
      have e1 := hv0 p (mem_hullVertices_of_diam hp hq hpq h2)
      have e2 := hv0 q (mem_hullVertices_of_diam hq hp hpq.symm (by rw [dist_comm]; exact h2))
      simp only [f, e1, e2, smul_zero, add_zero]; exact h2.le
    · have hg := hg2 p hp q hq h2
      have hle := dist_le_diam hp hq
      rw [abs_of_nonpos (by linarith)] at hg
      have := abs_lt.1 (hclose t ht p hp q hq)
      have : γ ≤ γ2 := min_le_right _ _
      linarith
  have hinj : ∀ t ∈ Set.Ioo 0 δ1, Set.InjOn (f t) X := by
    intro t ht p hp q hq he
    by_contra hpq
    have := hsep t ht p hp q hq hpq
    rw [he, dist_self] at this; linarith
  -- the quadratic `sqSum`
  set A := ∑ p ∈ X, ∑ q ∈ X, dist p q ^ 2
  set B := ∑ p ∈ X, ∑ q ∈ X, 2 * inner ℝ (p - q) (v p - v q)
  set C := ∑ p ∈ X, ∑ q ∈ X, ‖v p - v q‖ ^ 2
  have hsq : ∀ t ∈ Set.Ioo 0 δ1, sqSum (X.image (f t)) = A + B * t + C * t ^ 2 := by
    intro t ht
    unfold sqSum
    rw [Finset.sum_image (hinj t ht)]
    simp only [Finset.sum_image (hinj t ht), f, dist_move_sq, A, B, C, Finset.sum_add_distrib,
      Finset.sum_mul]
    congr 1; congr 1
    all_goals refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
  have hC : 0 < C := by
    have h1 : ‖v p0 - v a‖ ^ 2 ≤ ∑ q ∈ X, ‖v p0 - v q‖ ^ 2 :=
      Finset.single_le_sum (f := fun q => ‖v p0 - v q‖ ^ 2) (fun _ _ => sq_nonneg _) ha
    have h2 : ∑ q ∈ X, ‖v p0 - v q‖ ^ 2 ≤ C :=
      Finset.single_le_sum (f := fun p => ∑ q ∈ X, ‖v p - v q‖ ^ 2)
        (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) hp0
    have h3 : 0 < ‖v p0 - v a‖ ^ 2 := by rw [hva, sub_zero]; positivity
    linarith
  set δ0 := if 0 ≤ B then δ1 else min δ1 (-B / (2 * C))
  have hδ0 : 0 < δ0 := by
    simp only [δ0]; split_ifs with h
    · exact hδ1
    · exact lt_min hδ1 (div_pos (by linarith) (by linarith))
  have hδ01 : δ0 ≤ δ1 := by simp only [δ0]; split_ifs <;> simp
  refine false_of_release hfm hδ0 (fun t => X.image (f t)) (fun t ht => ?_) ?_
  · have ht1 : t ∈ Set.Ioo 0 δ1 := ⟨ht.1, ht.2.trans_le hδ01⟩
    have hcard : (X.image (f t)).card = n := by
      rw [Finset.card_image_of_injOn (hinj t ht1), hX.1.1]
    have hsepF : IsSeparated (X.image (f t)) := by
      intro x hx y hy hxy
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hy
      exact hsep t ht1 p hp q hq (fun h => hxy (by rw [h]))
    have hdiam : diam (X.image (f t)) ≤ D := by
      apply Metric.diam_le_of_forall_dist_le hD.le
      intro x hx y hy
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx hy
      obtain ⟨p, hp, rfl⟩ := hx
      obtain ⟨q, hq, rfl⟩ := hy
      exact hupper t ht1 p hp q hq
    exact ⟨⟨hcard, hsepF⟩, fun Y hY => hdiam.trans (hX.2 Y hY)⟩
  · intro s hs t ht hst
    have hs1 : s ∈ Set.Ioo 0 δ1 := ⟨hs.1, hs.2.trans_le hδ01⟩
    have ht1 : t ∈ Set.Ioo 0 δ1 := ⟨ht.1, ht.2.trans_le hδ01⟩
    simp only at hst
    rw [hsq s hs1, hsq t ht1] at hst
    have hfac : (s - t) * (B + C * (s + t)) = 0 := by linear_combination hst
    rcases mul_eq_zero.1 hfac with h | h
    · linarith
    · exfalso
      by_cases hB : 0 ≤ B
      · have : 0 < C * (s + t) := mul_pos hC (by linarith [hs.1, ht.1])
        linarith
      · have hs2 : s < -B / (2 * C) := by
          have := hs.2; simp only [δ0, if_neg hB] at this; exact this.trans_le (min_le_right _ _)
        have ht2 : t < -B / (2 * C) := by
          have := ht.2; simp only [δ0, if_neg hB] at this; exact this.trans_le (min_le_right _ _)
        rw [lt_div_iff₀ (by linarith)] at hs2 ht2
        nlinarith

/-- **Lemma 2.2 (pinned counting), row count.**  If an optimal set has more points than hull
vertices, then under finite multiplicity `m - t_B ≥ 2(n - b) + 1`. -/
theorem pinned_count_of {n : ℕ} (hn : 2 ≤ n) (hfm : numOptimalClasses n < ⊤) {X : Finset Plane}
    (hX : IsOptimal n X) (hb : (hullVertices X).card < n) :
    2 * (n - (hullVertices X).card) + 1 + ((unitEdges X).filter
        (fun e => ∀ x ∈ e, x ∈ hullVertices X)).card ≤ (unitEdges X).card := by
  set I := X \ hullVertices X
  have hI : I.card = n - (hullVertices X).card := by
    have hsub : hullVertices X ⊆ X := Finset.filter_subset _ _
    show (X \ hullVertices X).card = _
    rw [Finset.card_sdiff_of_subset hsub, hX.1.1]
  set E' := (unitEdges X).filter (fun e => ¬ ∀ x ∈ e, x ∈ hullVertices X)
  have hsplit : ((unitEdges X).filter (fun e => ∀ x ∈ e, x ∈ hullVertices X)).card + E'.card =
      (unitEdges X).card := Finset.card_filter_add_card_filter_not _
  let L : (I → Plane) →ₗ[ℝ] (E' → ℝ) :=
    { toFun := fun u e => rowVal (extV I u) e
      map_add' := fun u u' => by
        ext e; simp only [rowVal, map_add, Pi.add_apply]
        rw [show extV I u e.1.out.1 + extV I u' e.1.out.1 - (extV I u e.1.out.2 +
          extV I u' e.1.out.2) = (extV I u e.1.out.1 - extV I u e.1.out.2) +
          (extV I u' e.1.out.1 - extV I u' e.1.out.2) by abel, inner_add_right]
      map_smul' := fun c u => by
        ext e; simp only [rowVal, map_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
        rw [← smul_sub, inner_smul_right] }
  have hcone : ∀ u, (∀ e, 0 ≤ L u e) → u ∈ (⊥ : Submodule ℝ (I → Plane)) := by
    intro u hu
    have hvanish : ∀ p ∈ hullVertices X, extV I u p = 0 := fun p hp => by
      have : p ∉ I := fun h => (Finset.mem_sdiff.1 h).2 hp
      simp [extV, this]
    have hz := pinned_locking hn hfm hX (extV I u) hvanish (fun p hp q hq hpq => by
      by_cases hh : p ∈ hullVertices X ∧ q ∈ hullVertices X
      · rw [hvanish p hh.1, hvanish q hh.2, sub_zero, inner_zero_right]
      · have hU : s(p, q) ∈ unitEdges X := Finset.mem_image.2 ⟨(p, q), by simp [hp, hq, hpq], rfl⟩
        have hE : s(p, q) ∈ E' := Finset.mem_filter.2 ⟨hU, fun hall => hh
          ⟨hall p (Sym2.mem_mk_left _ _), hall q (Sym2.mem_mk_right _ _)⟩⟩
        have := hu ⟨_, hE⟩
        simpa [L, rowVal_mk] using this)
    rw [Submodule.mem_bot]
    funext p
    have := hz p (Finset.mem_sdiff.1 p.2).1
    rwa [extV_mem I u p.2] at this
  have hfr : finrank ℝ (I → Plane) = 2 * I.card := by
    rw [Module.finrank_pi_fintype]; simp [mul_comm]
  have key := finrank_add_one_le_of_cone_trivial L ⊥ bot_le hcone (by
    rw [finrank_bot, hfr, hI]; omega)
  rw [finrank_bot, hfr, Fintype.card_coe] at key
  omega

end Erdos99
end

end Pinned

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `ConeFarkas`
-/

section ConeFarkas

/-!
# Finitely generated cones, Farkas' lemma and Hoffman's bound

Finite-dimensional convex-analysis infrastructure for the second-order step of first-order locking
(Verification Guide §7.4).

* `caratheodory_cone`: conic Carathéodory — a point of a finitely generated cone lies in the cone
  of a linearly independent subfamily.
* `isClosed_coneOf`: finitely generated cones are closed.
* `farkas_finite`: Farkas' lemma for a finite system `aᵢ w + yᵢ ≥ 0`.
* `hoffman_bound`: Hoffman's error bound for such systems.
-/

open scoped BigOperators

@[expose] public noncomputable section

open Classical

namespace Erdos99.Locking

section Cone

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {κ : Type*}

/-- The cone generated by the vectors `g k`, `k ∈ s`. -/
def coneOf (g : κ → F) (s : Finset κ) : Set F :=
  {x | ∃ c : κ → ℝ, (∀ k, 0 ≤ c k) ∧ x = ∑ k ∈ s, c k • g k}

/-- **Conic Carathéodory theorem.** -/
theorem caratheodory_cone (g : κ → F) (s : Finset κ) (x : F) (hx : x ∈ coneOf g s) :
    ∃ t ⊆ s, LinearIndepOn ℝ g (t : Set κ) ∧ x ∈ coneOf g t := by
  induction s using Finset.strongInduction with
  | H s ih =>
  by_cases hind : LinearIndepOn ℝ g (s : Set κ)
  · exact ⟨s, subset_rfl, hind, hx⟩
  obtain ⟨c, hc, rfl⟩ := hx
  obtain ⟨μ, hμ, i, his, hi⟩ := not_linearIndepOn_finset_iff.1 hind
  obtain ⟨μ, hμ, hpos⟩ : ∃ μ : κ → ℝ, ∑ k ∈ s, μ k • g k = 0 ∧ ∃ i ∈ s, 0 < μ i := by
    rcases lt_or_gt_of_ne hi with h | h
    · refine ⟨-μ, by simp [neg_smul, Finset.sum_neg_distrib, hμ], i, his, by simp; linarith⟩
    · exact ⟨μ, hμ, i, his, h⟩
  set S := s.filter (fun k => 0 < μ k)
  have hS : S.Nonempty := by
    obtain ⟨i, his, hi⟩ := hpos; exact ⟨i, Finset.mem_filter.2 ⟨his, hi⟩⟩
  obtain ⟨i0, hi0, hmin⟩ := S.exists_min_image (fun k => c k / μ k) hS
  rw [Finset.mem_filter] at hi0
  set τ := c i0 / μ i0
  have hτ : 0 ≤ τ := div_nonneg (hc i0) hi0.2.le
  set c' : κ → ℝ := fun k => c k - τ * μ k
  have hc' : ∀ k ∈ s, 0 ≤ c' k := by
    intro k hk
    by_cases hk0 : 0 < μ k
    · have := hmin k (Finset.mem_filter.2 ⟨hk, hk0⟩)
      have : τ * μ k ≤ c k := by
        rw [div_le_div_iff₀ hi0.2 hk0] at this
        simp only [τ]; rw [div_mul_eq_mul_div, div_le_iff₀ hi0.2]; linarith
      simp only [c']; linarith
    · push_neg at hk0
      simp only [c']; nlinarith [hc k]
  have hc'0 : c' i0 = 0 := by simp only [c', τ]; rw [div_mul_cancel₀ _ hi0.2.ne', sub_self]
  have hsum : ∑ k ∈ s, c k • g k = ∑ k ∈ s.erase i0, (max 0 (c' k)) • g k := by
    have h1 : ∑ k ∈ s, c k • g k = ∑ k ∈ s, c' k • g k := by
      simp only [c', sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, hμ,
        smul_zero, sub_zero]
    rw [h1, ← Finset.add_sum_erase s _ hi0.1, hc'0, zero_smul, zero_add]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [max_eq_right (hc' k (Finset.mem_of_mem_erase hk))]
  obtain ⟨t, hts, ht, hxt⟩ := ih (s.erase i0) (Finset.erase_ssubset hi0.1)
    ⟨fun k => max 0 (c' k), fun k => le_max_left _ _, hsum⟩
  exact ⟨t, hts.trans (Finset.erase_subset _ _), ht, hxt⟩

lemma isClosed_coneOf_of_indep (g : κ → F) {t : Finset κ} (ht : LinearIndepOn ℝ g (t : Set κ)) :
    IsClosed (coneOf g t) := by
  let L : (t → ℝ) →ₗ[ℝ] F := Fintype.linearCombination ℝ (fun k : t => g k)
  have hL : Function.Injective L :=
    linearIndependent_iff_injective_fintypeLinearCombination.1 ht
  have hemb := LinearMap.isClosedEmbedding_of_injective (f := L) (LinearMap.ker_eq_bot.2 hL)
  have hset : coneOf g t = L '' Set.Ici 0 := by
    ext x; constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨fun k => c k, fun k => hc k, ?_⟩
      simp [L, Fintype.linearCombination_apply, Finset.sum_attach t (fun k => c k • g k)]
    · rintro ⟨c, hc, rfl⟩
      refine ⟨fun k => if h : k ∈ t then c ⟨k, h⟩ else 0, fun k => ?_, ?_⟩
      · by_cases hk : k ∈ t
        · simp only [hk, dif_pos]; exact hc ⟨k, hk⟩
        · simp [hk]
      simp only [L, Fintype.linearCombination_apply]
      rw [← Finset.sum_coe_sort t]
      exact Finset.sum_congr rfl fun k _ => by simp
  rw [hset]
  exact hemb.isClosedMap _ isClosed_Ici

lemma coneOf_mono (g : κ → F) {s t : Finset κ} (h : t ⊆ s) : coneOf g t ⊆ coneOf g s := by
  rintro x ⟨c, hc, rfl⟩
  refine ⟨fun k => if k ∈ t then c k else 0, fun k => by by_cases hk : k ∈ t <;> simp [hk, hc], ?_⟩
  rw [← Finset.sum_subset h (fun k _ hk => by simp [hk])]
  exact Finset.sum_congr rfl fun k hk => by simp [hk]

/-- Finitely generated cones are closed. -/
theorem isClosed_coneOf (g : κ → F) (s : Finset κ) : IsClosed (coneOf g s) := by
  have : coneOf g s = ⋃ (t : Finset κ) (_ : t ∈ s.powerset.filter
      (fun t : Finset κ => LinearIndepOn ℝ g (t : Set κ))), coneOf g t := by
    ext x; constructor
    · intro hx
      obtain ⟨t, hts, ht, hxt⟩ := caratheodory_cone g s x hx
      exact Set.mem_biUnion (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 hts, ht⟩) hxt
    · intro hx
      obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.1 hx
      exact coneOf_mono g (Finset.mem_powerset.1 (Finset.mem_filter.1 ht).1) hxt
  rw [this]
  exact Set.Finite.isClosed_biUnion (Finset.finite_toSet _) fun t ht =>
    isClosed_coneOf_of_indep g (Finset.mem_filter.1 ht).2

lemma convex_coneOf (g : κ → F) (s : Finset κ) : Convex ℝ (coneOf g s) := by
  rintro x ⟨c, hc, rfl⟩ y ⟨d, hd, rfl⟩ α β hα hβ _
  refine ⟨fun k => α * c k + β * d k, fun k => by have := hc k; have := hd k; positivity, ?_⟩
  simp only [add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]

lemma smul_mem_coneOf (g : κ → F) (s : Finset κ) {x : F} (hx : x ∈ coneOf g s) {r : ℝ}
    (hr : 0 ≤ r) : r • x ∈ coneOf g s := by
  obtain ⟨c, hc, rfl⟩ := hx
  refine ⟨fun k => r * c k, fun k => mul_nonneg hr (hc k), ?_⟩
  simp only [Finset.smul_sum, mul_smul]

lemma zero_mem_coneOf (g : κ → F) (s : Finset κ) : (0 : F) ∈ coneOf g s :=
  ⟨0, fun _ => le_rfl, by simp⟩

lemma mem_coneOf_of_mem (g : κ → F) {s : Finset κ} {k : κ} (hk : k ∈ s) : g k ∈ coneOf g s := by
  refine ⟨Pi.single k 1, fun j => ?_, ?_⟩
  · by_cases h : j = k
    · subst h; simp
    · simp [h]
  · rw [Finset.sum_eq_single k (fun j _ hj => by simp [hj]) (fun h => absurd hk h)]
    simp

/-- Separation of a point from a finitely generated cone. -/
lemma exists_dual_of_not_mem_coneOf (g : κ → F) (s : Finset κ) {y : F} (hy : y ∉ coneOf g s) :
    ∃ f : F →L[ℝ] ℝ, (∀ x ∈ coneOf g s, 0 ≤ f x) ∧ f y < 0 := by
  obtain ⟨f, u, hfu, hfb⟩ := geometric_hahn_banach_point_closed (convex_coneOf g s)
    (isClosed_coneOf g s) hy
  have hu : u < 0 := by simpa using hfb 0 (zero_mem_coneOf g s)
  refine ⟨f, fun x hx => ?_, hfu.trans hu⟩
  by_contra hneg; push_neg at hneg
  have := hfb ((u / f x) • x) (smul_mem_coneOf g s hx (div_nonneg_of_nonpos hu.le hneg.le))
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hneg.ne] at this
  exact lt_irrefl _ this

/-- Uniform coefficient bound for independent subfamilies. -/
lemma exists_coeff_bound [Fintype κ] (g : κ → F) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : Finset κ, LinearIndepOn ℝ g (t : Set κ) → ∀ c : κ → ℝ,
      ∀ j ∈ t, |c j| ≤ K * ‖∑ k ∈ t, c k • g k‖ := by
  have h1 : ∀ t : Finset κ, ∃ K : ℝ, 0 ≤ K ∧ (LinearIndepOn ℝ g (t : Set κ) → ∀ c : κ → ℝ,
      ∀ j ∈ t, |c j| ≤ K * ‖∑ k ∈ t, c k • g k‖) := by
    intro t
    by_cases ht : LinearIndepOn ℝ g (t : Set κ)
    · let L : (t → ℝ) →ₗ[ℝ] F := Fintype.linearCombination ℝ (fun k : t => g k)
      have hL : Function.Injective L :=
        linearIndependent_iff_injective_fintypeLinearCombination.1 ht
      obtain ⟨K, hK0, hK⟩ := L.exists_antilipschitzWith (LinearMap.ker_eq_bot.2 hL)
      refine ⟨K, K.2, fun _ c j hj => ?_⟩
      have h := hK.le_mul_dist (fun k : t => c k) 0
      rw [dist_zero_right, map_zero, dist_zero_right] at h
      have hLc : L (fun k : t => c k) = ∑ k ∈ t, c k • g k := by
        simp [L, Fintype.linearCombination_apply, Finset.sum_attach t (fun k => c k • g k)]
      rw [hLc] at h
      have hj' : |c j| ≤ ‖(fun k : t => c k)‖ := by
        have := norm_le_pi_norm (fun k : t => c k) ⟨j, hj⟩
        simpa [Real.norm_eq_abs] using this
      exact hj'.trans h
    · exact ⟨0, le_rfl, fun h => absurd h ht⟩
  choose K hK0 hK using h1
  refine ⟨∑ t ∈ Finset.univ.powerset, K t, Finset.sum_nonneg fun t _ => hK0 t,
    fun t ht c j hj => (hK t ht c j hj).trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact Finset.single_le_sum (f := K) (fun t _ => hK0 t) (Finset.mem_powerset.2 (Finset.subset_univ t))



end Cone

variable {ι : Type*} [Fintype ι]

/-- **Finite Farkas lemma** (inequality form).  If every nonnegative `η` with `∑ ηᵢ aᵢ = 0` has
`∑ ηᵢ yᵢ ≥ 0`, then the system `aᵢ w + yᵢ ≥ 0` is solvable. -/
theorem farkas_finite {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (a : ι → V →ₗ[ℝ] ℝ) (y : ι → ℝ)
    (h : ∀ η : ι → ℝ, (∀ i, 0 ≤ η i) → ∑ i, η i • a i = 0 → 0 ≤ ∑ i, η i * y i) :
    ∃ w, ∀ i, 0 ≤ a i w + y i := by
  set n := Module.finrank ℝ V
  let b := Module.finBasis ℝ V
  let A : V →ₗ[ℝ] (ι → ℝ) := LinearMap.pi a
  let g : ι ⊕ (Fin n ⊕ Fin n) → (ι → ℝ) := fun k => match k with
    | Sum.inl i => Pi.single i 1
    | Sum.inr (Sum.inl k) => A (b k)
    | Sum.inr (Sum.inr k) => -A (b k)
  by_cases hy : y ∈ coneOf g Finset.univ
  · obtain ⟨c, hc, hyc⟩ := hy
    refine ⟨-∑ k, (c (Sum.inr (Sum.inl k)) - c (Sum.inr (Sum.inr k))) • b k, fun i => ?_⟩
    have hyi := congrFun hyc i
    simp only [Fintype.sum_sum_type, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, g,
      Pi.neg_apply, A, LinearMap.pi_apply] at hyi
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)] at hyi
    simp only [map_neg, map_sum, map_smul, smul_eq_mul, Pi.single_eq_same, mul_one] at hyi ⊢
    have := hc (Sum.inl i)
    have e : ∑ x, (c (Sum.inr (Sum.inl x)) - c (Sum.inr (Sum.inr x))) * (a i) (b x) =
        ∑ x, c (Sum.inr (Sum.inl x)) * (a i) (b x) +
          ∑ x, c (Sum.inr (Sum.inr x)) * -(a i) (b x) := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun x _ => by ring
    linarith
  · exfalso
    obtain ⟨f, hf, hfy⟩ := exists_dual_of_not_mem_coneOf g Finset.univ hy
    set η : ι → ℝ := fun i => f (Pi.single i 1)
    have hη : ∀ i, 0 ≤ η i := fun i => hf _ (mem_coneOf_of_mem g (Finset.mem_univ (Sum.inl i)))
    have hfA : ∀ k, f (A (b k)) = 0 := by
      intro k
      have h1 := hf _ (mem_coneOf_of_mem g (Finset.mem_univ (Sum.inr (Sum.inl k))))
      have h2 := hf _ (mem_coneOf_of_mem g (Finset.mem_univ (Sum.inr (Sum.inr k))))
      simp only [g, map_neg] at h1 h2
      linarith
    have hfeval : ∀ z : ι → ℝ, f z = ∑ i, η i * z i := by
      intro z
      conv_lhs => rw [pi_eq_sum_univ z]
      simp only [map_sum, map_smul, smul_eq_mul, η]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm]; congr 2; ext j; simp [Pi.single_apply, eq_comm]
    have hsum : ∑ i, η i • a i = 0 := by
      ext w
      have : f (A w) = 0 := by
        rw [← b.sum_repr w, map_sum, map_sum]
        simp [map_smul, hfA]
      rw [hfeval] at this
      simpa [A, LinearMap.pi_apply] using this
    have := h η hη hsum
    rw [hfeval] at hfy
    linarith

/-- Hoffman's bound at the origin, in a Euclidean space. -/
theorem hoffman_euclid_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (a : ι → E →ₗ[ℝ] ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ y : ι → ℝ, (∃ w, ∀ i, 0 ≤ a i w + y i) →
      ∃ v, (∀ i, 0 ≤ a i v + y i) ∧ ‖v‖ ≤ L * ∑ i, max 0 (-y i) := by
  let g : ι → E := fun i => (InnerProductSpace.toDual ℝ E).symm (LinearMap.toContinuousLinearMap (a i))
  have hg : ∀ i w, inner ℝ (g i) w = a i w := fun i w => by
    simp [g, InnerProductSpace.toDual_symm_apply]
  obtain ⟨K, hK0, hK⟩ := exists_coeff_bound g
  refine ⟨K, hK0, fun y ⟨w0, hw0⟩ => ?_⟩
  set P : Set E := {w | ∀ i, 0 ≤ a i w + y i}
  have hPc : IsClosed P := by
    simp only [P, Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const
      (((a i).continuous_of_finiteDimensional).add continuous_const)
  have hPconv : Convex ℝ P := by
    intro u hu w hw α β hα hβ hαβ i
    have h1 := hu i; have h2 := hw i
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    have : y i = α * y i + β * y i := by rw [← add_mul, hαβ, one_mul]
    nlinarith [mul_nonneg hα h1, mul_nonneg hβ h2]
  obtain ⟨v, hvP, hvmin⟩ := exists_norm_eq_iInf_of_complete_convex ⟨w0, show w0 ∈ P from hw0⟩ hPc.isComplete
    hPconv 0
  have hVI := (norm_eq_iInf_iff_real_inner_le_zero hPconv hvP).1 hvmin
  set J := Finset.univ.filter (fun i => a i v + y i = 0)
  -- KKT: `v` lies in the cone of the active constraint vectors
  have hcone : v ∈ coneOf g J := by
    by_contra hnot
    obtain ⟨f, hf, hfv⟩ := exists_dual_of_not_mem_coneOf g J hnot
    set d := (InnerProductSpace.toDual ℝ E).symm f
    have hd : ∀ x, inner ℝ d x = f x := fun x => by simp [d, InnerProductSpace.toDual_symm_apply]
    have hJd : ∀ j ∈ J, 0 ≤ a j d := by
      intro j hj
      have := hf _ (mem_coneOf_of_mem g hj)
      rw [← hd, real_inner_comm, hg] at this; exact this
    set m := ∑ i ∈ Finset.univ.filter (fun i => a i v + y i ≠ 0), |a i d| / (a i v + y i)
    have hm : 0 ≤ m := Finset.sum_nonneg fun i hi => div_nonneg (abs_nonneg _) (hvP i)
    set ε := 1 / (1 + m)
    have hε : 0 < ε := by positivity
    have hnew : v + ε • d ∈ P := by
      intro i
      rw [map_add, map_smul, smul_eq_mul]
      by_cases hi : a i v + y i = 0
      · have := hJd i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
        nlinarith
      · have hs : 0 < a i v + y i := lt_of_le_of_ne (hvP i) (Ne.symm hi)
        have hle : |a i d| / (a i v + y i) ≤ m :=
          Finset.single_le_sum (f := fun i => |a i d| / (a i v + y i))
            (fun i _ => div_nonneg (abs_nonneg _) (hvP i))
            (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
        rw [div_le_iff₀ hs] at hle
        have h1 : ε * |a i d| ≤ a i v + y i := by
          simp only [ε]
          rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
          nlinarith
        have := neg_abs_le (a i d)
        nlinarith
    have := hVI _ hnew
    rw [zero_sub, add_sub_cancel_left, inner_neg_left, inner_smul_right, real_inner_comm, hd] at this
    nlinarith
  obtain ⟨S, hSJ, hSind, c, hc, hvc⟩ := caratheodory_cone g J v hcone
  have hcoef : ∀ j ∈ S, c j ≤ K * ‖v‖ := by
    intro j hj
    have := hK S hSind c j hj
    rw [← hvc] at this
    exact (le_abs_self _).trans this
  refine ⟨v, hvP, ?_⟩
  have hnorm : ‖v‖ ^ 2 ≤ K * ‖v‖ * ∑ i, max 0 (-y i) := by
    have e1 : ‖v‖ ^ 2 = ∑ j ∈ S, c j * a j v := by
      rw [← real_inner_self_eq_norm_sq]
      nth_rewrite 1 [hvc]
      rw [sum_inner]
      exact Finset.sum_congr rfl fun j _ => by rw [inner_smul_left, hg]; simp
    have e2 : ∀ j ∈ S, a j v = -y j := fun j hj => by
      have := (Finset.mem_filter.1 (hSJ hj)).2; linarith
    rw [e1, Finset.sum_congr rfl fun j hj => by rw [e2 j hj]]
    calc ∑ j ∈ S, c j * -y j ≤ ∑ j ∈ S, (K * ‖v‖) * max 0 (-y j) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have h1 := hcoef j hj
          have h2 := hc j
          have h3 : -y j ≤ max 0 (-y j) := le_max_right _ _
          have h4 : 0 ≤ max 0 (-y j) := le_max_left _ _
          calc c j * -y j ≤ c j * max 0 (-y j) := mul_le_mul_of_nonneg_left h3 h2
            _ ≤ K * ‖v‖ * max 0 (-y j) := mul_le_mul_of_nonneg_right h1 h4
      _ = K * ‖v‖ * ∑ j ∈ S, max 0 (-y j) := by rw [Finset.mul_sum]
      _ ≤ K * ‖v‖ * ∑ i, max 0 (-y i) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            fun i _ _ => le_max_left _ _
  rcases (norm_nonneg v).eq_or_lt with h0 | hpos
  · rw [← h0]; exact mul_nonneg hK0 (Finset.sum_nonneg fun i _ => le_max_left _ _)
  · have : ‖v‖ * ‖v‖ ≤ ‖v‖ * (K * ∑ i, max 0 (-y i)) := by nlinarith
    exact le_of_mul_le_mul_left this hpos


/-- **Hoffman's error bound.**  For a fixed finite family of linear forms on a finite-dimensional
normed space there is a constant `L` such that whenever `aᵢ w + yᵢ ≥ 0` is solvable, every `w₀`
is within `L` times its total violation `∑ᵢ max 0 (-(aᵢ w₀ + yᵢ))` of a solution. -/
theorem hoffman_bound {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (a : ι → V →ₗ[ℝ] ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (y : ι → ℝ) (w₀ : V), (∃ w, ∀ i, 0 ≤ a i w + y i) →
      ∃ w, (∀ i, 0 ≤ a i w + y i) ∧ ‖w - w₀‖ ≤ L * ∑ i, max 0 (-(a i w₀ + y i)) := by
  let e : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) := toEuclidean
  let f : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →L[ℝ] V := e.symm
  let a' : ι → EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →ₗ[ℝ] ℝ :=
    fun i => (a i).comp f.toLinearMap
  obtain ⟨L, hL, h⟩ := hoffman_euclid_zero a'
  refine ⟨‖f‖ * L, mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) hL,
    fun y w₀ ⟨w, hw⟩ => ?_⟩
  have ha' : ∀ i u, a' i u = a i (e.symm u) := fun i u => rfl
  obtain ⟨u, hu, hub⟩ := h (fun i => a i w₀ + y i) ⟨e (w - w₀), fun i => by
    rw [ha', ContinuousLinearEquiv.symm_apply_apply, map_sub]; linarith [hw i]⟩
  refine ⟨w₀ + e.symm u, fun i => ?_, ?_⟩
  · have := hu i; rw [ha'] at this; rw [map_add]; linarith
  · rw [add_sub_cancel_left]
    calc ‖f u‖ ≤ ‖f‖ * ‖u‖ := f.le_opNorm u
      _ ≤ ‖f‖ * (L * ∑ i, max 0 (-(a i w₀ + y i))) :=
          mul_le_mul_of_nonneg_left hub (ContinuousLinearMap.opNorm_nonneg _)
      _ = _ := by ring

end Erdos99.Locking
end

end ConeFarkas

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `LockingAbstract`
-/

section LockingAbstract

/-!
# From stress positivity to second-order feasible displacements (Verification Guide §7.4)

An abstract finite-dimensional statement.  Let `V` be a finite-dimensional real normed space and
let finitely many constraints `0 ≤ aᵢ z + Bᵢ z z` be given (`aᵢ` linear, `Bᵢ` bilinear).  Assume
the *stress sign* property: for every nonnegative self-stress `η` (that is, `η ≥ 0` and
`∑ ηᵢ aᵢ = 0`) the quadratic form `∑ ηᵢ Bᵢ z z` is nonnegative.

Then every first-order feasible direction `v` (`aᵢ v ≥ 0` for all `i`) extends to second order:
for every small `t > 0` there is an exactly feasible `z` with `‖z - t v‖ ≤ M t²`
(`exists_secondOrder_solution`).

The proof uses

* the finite Farkas lemma (`farkas_finite`, `ConeFarkas`),
* Hoffman's error bound for finite systems of linear inequalities (`hoffman_bound`,
  `ConeFarkas`), and
* a contraction-type iteration (a discrete version of Nadler's set-valued fixed point theorem).
-/

open scoped BigOperators

@[expose] public noncomputable section

open Classical

namespace Erdos99.Locking

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ι : Type*} [Fintype ι]

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- The geometric decay of a contraction-type iteration. -/
lemma geom_iter (w : ℕ → V) {c s : ℝ} (hc : 0 ≤ c) (h0 : w 0 = 0)
    (hstep : ∀ k, ‖w (k + 2) - w (k + 1)‖ ≤ c * (‖w (k + 1)‖ + ‖w k‖ + s) * ‖w (k + 1) - w k‖)
    (hsmall : c * (4 * ‖w 1‖ + s) ≤ 1 / 2) :
    ∀ k, ‖w (k + 1) - w k‖ ≤ (1 / 2) ^ k * ‖w 1‖ ∧
      ‖w (k + 1)‖ ≤ 2 * (1 - (1 / 2) ^ (k + 1)) * ‖w 1‖ ∧ ‖w k‖ ≤ 2 * ‖w 1‖ := by
  have hw1 := norm_nonneg (w 1)
  intro k
  induction k with
  | zero => simp [h0]; linarith
  | succ k ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    have hp : (0:ℝ) ≤ (1 / 2) ^ (k + 1) := by positivity
    have hp1 : ((1:ℝ) / 2) ^ (k + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hk1 : ‖w (k + 1)‖ ≤ 2 * ‖w 1‖ := by nlinarith
    have hs : 0 ≤ ‖w (k + 1)‖ + ‖w k‖ + s → c * (‖w (k + 1)‖ + ‖w k‖ + s) ≤ 1 / 2 := by
      intro _
      calc c * (‖w (k + 1)‖ + ‖w k‖ + s) ≤ c * (4 * ‖w 1‖ + s) := by
            apply mul_le_mul_of_nonneg_left _ hc; linarith
        _ ≤ 1 / 2 := hsmall
    have hd := hstep k
    have hnn := norm_nonneg (w (k + 1) - w k)
    have h1 : ‖w (k + 2) - w (k + 1)‖ ≤ (1 / 2) ^ (k + 1) * ‖w 1‖ := by
      by_cases hpos : 0 ≤ ‖w (k + 1)‖ + ‖w k‖ + s
      · have := hs hpos
        calc ‖w (k + 2) - w (k + 1)‖ ≤ c * (‖w (k + 1)‖ + ‖w k‖ + s) * ‖w (k + 1) - w k‖ := hd
          _ ≤ 1 / 2 * ((1 / 2) ^ k * ‖w 1‖) := mul_le_mul this ih1 hnn (by norm_num)
          _ = (1 / 2) ^ (k + 1) * ‖w 1‖ := by ring
      · push_neg at hpos
        have : c * (‖w (k + 1)‖ + ‖w k‖ + s) * ‖w (k + 1) - w k‖ ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hc hpos.le) hnn
        nlinarith
    refine ⟨h1, ?_, hk1⟩
    have := norm_sub_norm_le (w (k + 2)) (w (k + 1))
    have e : ((1:ℝ) / 2) ^ (k + 2) = (1 / 2) ^ (k + 1) / 2 := by ring
    rw [e]
    nlinarith

omit [FiniteDimensional ℝ V] in
/-- A bilinear form is Lipschitz on bounded sets. -/
lemma bilin_sub_le (B : V →L[ℝ] V →L[ℝ] ℝ) (u u' : V) :
    |B u u - B u' u'| ≤ ‖B‖ * (‖u‖ + ‖u'‖) * ‖u - u'‖ := by
  have e : B u u - B u' u' = B (u - u') u + B u' (u - u') := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]; ring
  rw [e]
  have h1 : |B (u - u') u| ≤ ‖B‖ * ‖u - u'‖ * ‖u‖ := by
    have := B.le_opNorm₂ (u - u') u; rwa [Real.norm_eq_abs] at this
  have h2 : |B u' (u - u')| ≤ ‖B‖ * ‖u'‖ * ‖u - u'‖ := by
    have := B.le_opNorm₂ u' (u - u'); rwa [Real.norm_eq_abs] at this
  have := B.opNorm_nonneg
  calc |B (u - u') u + B u' (u - u')| ≤ |B (u - u') u| + |B u' (u - u')| := abs_add_le _ _
    _ ≤ _ := by nlinarith [norm_nonneg u, norm_nonneg u', norm_nonneg (u - u')]

/-- **Second-order extension** (§7.4).  Under the stress-sign hypothesis, every first-order
feasible direction `v` is, to second order, the direction of exactly feasible displacements. -/
theorem exists_secondOrder_solution (a : ι → V →ₗ[ℝ] ℝ) (B : ι → V →L[ℝ] V →L[ℝ] ℝ)
    (hstress : ∀ η : ι → ℝ, (∀ i, 0 ≤ η i) → ∑ i, η i • a i = 0 →
      ∀ z, 0 ≤ ∑ i, η i * B i z z)
    (v : V) (hv : ∀ i, 0 ≤ a i v) :
    ∃ M δ : ℝ, 0 < δ ∧ ∀ t ∈ Set.Ioo 0 δ, ∃ z : V,
      ‖z - t • v‖ ≤ M * t ^ 2 ∧ ∀ i, 0 ≤ a i z + B i z z := by
  obtain ⟨L, hL, hhoff⟩ := hoffman_bound a
  set K := ∑ i, ‖B i‖
  have hK : 0 ≤ K := Finset.sum_nonneg fun i _ => (B i).opNorm_nonneg
  have hBK : ∀ i, ‖B i‖ ≤ K := fun i =>
    Finset.single_le_sum (f := fun i => ‖B i‖) (fun i _ => (B i).opNorm_nonneg) (Finset.mem_univ i)
  have hfeas : ∀ u : V, ∃ w, ∀ i, 0 ≤ a i w + B i u u := fun u =>
    farkas_finite a _ fun η hη hη0 => hstress η hη hη0 u
  set R := L * K * ‖v‖ ^ 2
  have hR : 0 ≤ R := by positivity
  set c := L * K
  have hc : 0 ≤ c := mul_nonneg hL hK
  set δ := min 1 (1 / (4 * (c * (4 * R + 2 * ‖v‖) + 1)))
  have hδ : 0 < δ := lt_min one_pos (by positivity)
  refine ⟨2 * R, δ, hδ, fun t ht => ?_⟩
  have ht0 := ht.1
  have ht1 : t ≤ 1 := ht.2.le.trans (min_le_left _ _)
  have ht2 : t ≤ 1 / (4 * (c * (4 * R + 2 * ‖v‖) + 1)) := ht.2.le.trans (min_le_right _ _)
  have hstep_ex : ∀ u : V, ∃ w, (∀ i, 0 ≤ a i w + B i (t • v + u) (t • v + u)) ∧
      ‖w - u‖ ≤ L * ∑ i, max 0 (-(a i u + B i (t • v + u) (t • v + u))) :=
    fun u => hhoff _ u (hfeas _)
  choose step hstep1 hstep2 using hstep_ex
  set w : ℕ → V := fun k => step^[k] 0
  have hw0 : w 0 = 0 := rfl
  have hwsucc : ∀ k, w (k + 1) = step (w k) := fun k => Function.iterate_succ_apply' _ _ _
  have hw1 : ‖w 1‖ ≤ R * t ^ 2 := by
    have h := hstep2 0
    rw [sub_zero] at h
    refine h.trans ?_
    simp only [map_zero, zero_add, add_zero]
    have : ∑ i, max 0 (-(B i (t • v) (t • v))) ≤ K * (t ^ 2 * ‖v‖ ^ 2) := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => max_le (by positivity) ?_
      have h := (B i).le_opNorm₂ (t • v) (t • v)
      rw [Real.norm_eq_abs, norm_smul, Real.norm_of_nonneg ht0.le] at h
      have := neg_le_abs (B i (t • v) (t • v))
      have := hBK i
      have := (B i).opNorm_nonneg
      nlinarith [norm_nonneg v, sq_nonneg t]
    calc L * ∑ i, max 0 (-(B i (t • v) (t • v))) ≤ L * (K * (t ^ 2 * ‖v‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left this hL
      _ = R * t ^ 2 := by ring
  have hcontr : ∀ k, ‖w (k + 2) - w (k + 1)‖ ≤
      c * (‖w (k + 1)‖ + ‖w k‖ + 2 * t * ‖v‖) * ‖w (k + 1) - w k‖ := by
    intro k
    have h := hstep2 (w (k + 1))
    rw [← hwsucc] at h
    refine h.trans ?_
    have hfe := hstep1 (w k)
    rw [← hwsucc] at hfe
    have hsum : ∑ i, max 0 (-(a i (w (k + 1)) + B i (t • v + w (k + 1)) (t • v + w (k + 1)))) ≤
        K * ((‖w (k + 1)‖ + ‖w k‖ + 2 * t * ‖v‖) * ‖w (k + 1) - w k‖) := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => max_le (by positivity) ?_
      have hb := bilin_sub_le (B i) (t • v + w k) (t • v + w (k + 1))
      have hn1 : ‖t • v + w k‖ ≤ t * ‖v‖ + ‖w k‖ := by
        refine (norm_add_le _ _).trans ?_; rw [norm_smul, Real.norm_of_nonneg ht0.le]
      have hn2 : ‖t • v + w (k + 1)‖ ≤ t * ‖v‖ + ‖w (k + 1)‖ := by
        refine (norm_add_le _ _).trans ?_; rw [norm_smul, Real.norm_of_nonneg ht0.le]
      have hdiff : t • v + w k - (t • v + w (k + 1)) = -(w (k + 1) - w k) := by abel
      rw [hdiff, norm_neg] at hb
      have h1 := (abs_le.1 hb).2
      have h2 := hfe i
      have hnn := norm_nonneg (w (k + 1) - w k)
      have h3 : ‖B i‖ * (‖t • v + w k‖ + ‖t • v + w (k + 1)‖) * ‖w (k + 1) - w k‖ ≤
          ‖B i‖ * ((‖w (k + 1)‖ + ‖w k‖ + 2 * t * ‖v‖) * ‖w (k + 1) - w k‖) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith) (B i).opNorm_nonneg) hnn
      linarith
    calc L * _ ≤ L * (K * ((‖w (k + 1)‖ + ‖w k‖ + 2 * t * ‖v‖) * ‖w (k + 1) - w k‖)) :=
          mul_le_mul_of_nonneg_left hsum hL
      _ = _ := by ring
  have hsmall : c * (4 * ‖w 1‖ + 2 * t * ‖v‖) ≤ 1 / 2 := by
    have h1 : 4 * ‖w 1‖ + 2 * t * ‖v‖ ≤ t * (4 * R + 2 * ‖v‖) := by
      have : R * t ^ 2 ≤ R * t := by
        apply mul_le_mul_of_nonneg_left _ hR; nlinarith
      nlinarith
    have h2 : c * (t * (4 * R + 2 * ‖v‖)) ≤ 1 / 2 := by
      rw [le_div_iff₀ (by positivity)] at ht2
      have hX : 0 ≤ c * (4 * R + 2 * ‖v‖) := by positivity
      nlinarith
    calc c * (4 * ‖w 1‖ + 2 * t * ‖v‖) ≤ c * (t * (4 * R + 2 * ‖v‖)) :=
          mul_le_mul_of_nonneg_left h1 hc
      _ ≤ 1 / 2 := h2
  have hgeo := geom_iter w hc hw0 hcontr hsmall
  have hcauchy : CauchySeq w := by
    refine cauchySeq_of_le_geometric (1 / 2) ‖w 1‖ (by norm_num) fun k => ?_
    rw [dist_eq_norm, ← norm_neg, neg_sub, mul_comm]
    exact (hgeo k).1
  obtain ⟨wl, hwl⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hwl_norm : ‖wl‖ ≤ 2 * ‖w 1‖ :=
    le_of_tendsto hwl.norm (Filter.Eventually.of_forall fun k => (hgeo k).2.2)
  have hcontA : ∀ i, Continuous (a i) := fun i => (a i).continuous_of_finiteDimensional
  have hcontQ : ∀ i, Continuous fun u : V => B i (t • v + u) (t • v + u) := by
    intro i; fun_prop
  have hfeas_lim : ∀ i, 0 ≤ a i wl + B i (t • v + wl) (t • v + wl) := by
    intro i
    have h1 : Filter.Tendsto (fun k => a i (w (k + 1)) + B i (t • v + w k) (t • v + w k))
        Filter.atTop (nhds (a i wl + B i (t • v + wl) (t • v + wl))) := by
      refine Filter.Tendsto.add ?_ (((hcontQ i).tendsto wl).comp hwl)
      exact ((hcontA i).tendsto wl).comp ((Filter.tendsto_add_atTop_iff_nat 1).2 hwl)
    refine ge_of_tendsto h1 (Filter.Eventually.of_forall fun k => ?_)
    have := hstep1 (w k) i
    rw [← hwsucc] at this
    exact this
  refine ⟨t • v + wl, ?_, fun i => ?_⟩
  · rw [add_sub_cancel_left]
    linarith
  · have := hfeas_lim i
    have := hv i
    rw [map_add, map_smul, smul_eq_mul]
    nlinarith

end Erdos99.Locking
end

end LockingAbstract

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `NegativePlane`
-/

section NegativePlane

/-!
# Quadratic forms with no two-dimensional negative-definite restriction

Basic definitions shared by the fan theorem (`FanTheorem`) and Hilbert's argument
(`HilbertLorentz`): the quadratic and bilinear forms of a matrix restricted to a finite index
set, the property `NoNegativePlane`, and its Gram-matrix characterisation.
-/

open scoped BigOperators

@[expose] public noncomputable section

open Classical

namespace Erdos99

variable {ι : Type*}

/-! ## Quadratic forms with no negative plane -/

/-- The quadratic form `∑_{i,j ∈ S} W i j f i f j`. -/
def quadForm (S : Finset ι) (W : ι → ι → ℝ) (f : ι → ℝ) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ S, W i j * f i * f j

/-- The bilinear form `∑_{i,j ∈ S} W i j f i g j` (not necessarily symmetric). -/
def bilinForm (S : Finset ι) (W : ι → ι → ℝ) (f g : ι → ℝ) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ S, W i j * f i * g j

/-- `W` (restricted to `S`) has no two-dimensional subspace on which its quadratic form is
negative definite. -/
def NoNegativePlane (S : Finset ι) (W : ι → ι → ℝ) : Prop :=
  ∀ f g : ι → ℝ, ¬ ∀ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) → quadForm S W (fun i => a * f i + b * g i) < 0

lemma quadForm_eq_bilinForm (S : Finset ι) (W : ι → ι → ℝ) (f : ι → ℝ) :
    quadForm S W f = bilinForm S W f f := rfl

/-- Expansion of the quadratic form on a plane. -/
lemma quadForm_comb (S : Finset ι) (W : ι → ι → ℝ) (f g : ι → ℝ) (a b : ℝ) :
    quadForm S W (fun i => a * f i + b * g i) =
      a ^ 2 * bilinForm S W f f + a * b * (bilinForm S W f g + bilinForm S W g f) +
        b ^ 2 * bilinForm S W g g := by
  unfold quadForm bilinForm
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- A binary quadratic form `A a² + B a b + C b²` with `A < 0` and `4 A C - B² > 0` is negative
definite. -/
lemma binary_neg_of_disc {A B C : ℝ} (hA : A < 0) (hD : 0 < 4 * A * C - B ^ 2) (a b : ℝ)
    (hab : a ≠ 0 ∨ b ≠ 0) : A * a ^ 2 + B * a * b + C * b ^ 2 < 0 := by
  have key : 4 * A * (A * a ^ 2 + B * a * b + C * b ^ 2) =
      (2 * A * a + B * b) ^ 2 + (4 * A * C - B ^ 2) * b ^ 2 := by ring
  have hpos : 0 < (2 * A * a + B * b) ^ 2 + (4 * A * C - B ^ 2) * b ^ 2 := by
    rcases hab with ha | hb
    · by_cases hb : b = 0
      · subst hb
        have : 0 < (2 * A * a) ^ 2 := by
          have : 2 * A * a ≠ 0 := by
            have : A ≠ 0 := hA.ne
            positivity
          positivity
        simpa using this
      · have : 0 < b ^ 2 := by positivity
        have := mul_pos hD this
        nlinarith [sq_nonneg (2 * A * a + B * b)]
    · have : 0 < b ^ 2 := by positivity
      have := mul_pos hD this
      nlinarith [sq_nonneg (2 * A * a + B * b)]
  by_contra h
  push_neg at h
  nlinarith

/-- Gram-matrix characterisation of a negative plane: if the form is negative definite on the
span of `f, g`, then `A < 0` and `4 A C - B² > 0` for its Gram coefficients. -/
lemma gram_of_negPlane {S : Finset ι} {W : ι → ι → ℝ} {f g : ι → ℝ}
    (h : ∀ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) → quadForm S W (fun i => a * f i + b * g i) < 0) :
    bilinForm S W f f < 0 ∧
      0 < 4 * bilinForm S W f f * bilinForm S W g g -
        (bilinForm S W f g + bilinForm S W g f) ^ 2 := by
  set A := bilinForm S W f f
  set B := bilinForm S W f g + bilinForm S W g f
  set C := bilinForm S W g g
  have hq : ∀ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) → A * a ^ 2 + B * a * b + C * b ^ 2 < 0 := by
    intro a b hab
    have := h a b hab
    rw [quadForm_comb] at this
    linarith
  have hA : A < 0 := by simpa using hq 1 0 (Or.inl one_ne_zero)
  refine ⟨hA, ?_⟩
  have h2 := hq B (-2 * A) (Or.inr (by intro h0; apply hA.ne; linarith))
  have : A * B ^ 2 + B * B * (-2 * A) + C * (-2 * A) ^ 2 = A * (4 * A * C - B ^ 2) := by ring
  rw [this] at h2
  by_contra hle
  push_neg at hle
  nlinarith

end Erdos99
end

end NegativePlane

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `MinkowskiPlane`
-/

section MinkowskiPlane

/-!
# The area form of a polygon with prescribed normals (two-dimensional Minkowski inequality)

Fix `k ≥ 3` unit normals `n₀, …, n_{k-1}` in the plane, in counterclockwise order, with
consecutive angular gaps `θ₀, …, θ_{k-1} ∈ (0, π)` summing to `2π`.  For a convex polygon with
these outer normals and support numbers `g₀, …, g_{k-1}`, twice its area is the quadratic form

  `polyForm k θ g = ∑ₘ edgeForm θₘ gₘ gₘ₊₁`,
  `edgeForm θ x y = 2 x y / sin θ - cot θ · (x² + y²)`

(the `m`-th summand is twice the area of the kite cut out by the vertex between sides `m` and
`m + 1`).  The form makes sense for arbitrary ("virtual") support numbers.

Main results:
* `polyForm_noPosPlane`: the form has no two-dimensional positive-definite restriction (it has a
  single positive direction);
* `polyForm_minkowski`: Minkowski's inequality `B(p, g)² ≥ q(p) q(g)` whenever `q(p) > 0`, where
  `B = polyBilin` is the polar form.

The proof is by induction on `k`: merging two consecutive gaps `α, β` with `α + β < π` can only
increase the form (`edgeForm_merge`, an exact sum-of-squares identity), and the base cases are a
triangle (`k = 3`, where the form is a constant times the square of a linear form) and a
parallelogram (`k = 4` with opposite normals, where it is a constant times a product of two linear
forms).
-/

open scoped BigOperators Real

@[expose] public noncomputable section

namespace Erdos99

open Real Finset

/-- Twice the area of the kite at a vertex with exterior angle `θ` between two sides with support
numbers `x, y`. -/
def edgeForm (θ x y : ℝ) : ℝ := 2 * x * y / sin θ - cos θ / sin θ * (x ^ 2 + y ^ 2)

/-- The polar (symmetric bilinear) form of `edgeForm θ`. -/
def edgeBilin (θ x y x' y' : ℝ) : ℝ :=
  (x * y' + x' * y) / sin θ - cos θ / sin θ * (x * x' + y * y')

/-- Twice the area of the (virtual) polygon with gaps `θ` and support numbers `g`. -/
def polyForm (k : ℕ) (θ g : ℕ → ℝ) : ℝ :=
  ∑ m ∈ range k, edgeForm (θ m) (g m) (g ((m + 1) % k))

/-- The polar form of `polyForm`. -/
def polyBilin (k : ℕ) (θ g g' : ℕ → ℝ) : ℝ :=
  ∑ m ∈ range k, edgeBilin (θ m) (g m) (g ((m + 1) % k)) (g' m) (g' ((m + 1) % k))

/-- Admissible gaps: `k ≥ 3` gaps in `(0, π)` with total `2π`. -/
structure ValidGaps (k : ℕ) (θ : ℕ → ℝ) : Prop where
  three_le : 3 ≤ k
  pos : ∀ m < k, 0 < θ m
  lt_pi : ∀ m < k, θ m < π
  sum_eq : ∑ m ∈ range k, θ m = 2 * π

/-- A quadratic form has no two-dimensional positive-definite restriction. -/
def NoPosPlane {α : Type*} (q : (α → ℝ) → ℝ) : Prop :=
  ∀ f g : α → ℝ, ¬ ∀ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) → 0 < q (fun m => a * f m + b * g m)

/-! ## Algebraic facts -/

lemma edgeForm_comb (θ x y x' y' a b : ℝ) :
    edgeForm θ (a * x + b * x') (a * y + b * y') =
      a ^ 2 * edgeForm θ x y + 2 * (a * b) * edgeBilin θ x y x' y' + b ^ 2 * edgeForm θ x' y' := by
  unfold edgeForm edgeBilin
  ring

lemma polyForm_comb (k : ℕ) (θ g g' : ℕ → ℝ) (a b : ℝ) :
    polyForm k θ (fun m => a * g m + b * g' m) =
      a ^ 2 * polyForm k θ g + 2 * (a * b) * polyBilin k θ g g' + b ^ 2 * polyForm k θ g' := by
  unfold polyForm polyBilin
  simp only [edgeForm_comb, Finset.mul_sum, ← Finset.sum_add_distrib]

/-- A quadratic form that factors as `c · L₁ · L₂` with `L₁` linear has no positive plane. -/
lemma noPosPlane_of_factor {α : Type*} (q : (α → ℝ) → ℝ) (c : ℝ) (L₁ L₂ : (α → ℝ) → ℝ)
    (hL : ∀ (a b : ℝ) (f g : α → ℝ), L₁ (fun m => a * f m + b * g m) = a * L₁ f + b * L₁ g)
    (hq : ∀ f, q f = c * L₁ f * L₂ f) : NoPosPlane q := by
  intro f g h
  by_cases hfg : L₁ g ≠ 0 ∨ -L₁ f ≠ 0
  · have := h (L₁ g) (-L₁ f) hfg
    rw [hq, hL] at this
    have h0 : L₁ g * L₁ f + -L₁ f * L₁ g = 0 := by ring
    rw [h0] at this
    simp at this
  · push_neg at hfg
    have := h 1 0 (Or.inl one_ne_zero)
    rw [hq, hL] at this
    have h0 : (1 : ℝ) * L₁ f + 0 * L₁ g = 0 := by
      have : L₁ f = 0 := by linarith [hfg.2]
      rw [this]; ring
    rw [h0] at this
    simp at this

/-- **Merging two gaps.**  For `α, β > 0` with `α + β < π`,
`edgeForm (α + β) x z - edgeForm α x y - edgeForm β y z` is a nonnegative square. -/
lemma edgeForm_merge_eq (α β x y z : ℝ) (h1 : sin α ≠ 0) (h2 : sin β ≠ 0)
    (h3 : sin (α + β) ≠ 0) :
    edgeForm (α + β) x z - edgeForm α x y - edgeForm β y z =
      (sin (α + β) * y - sin β * x - sin α * z) ^ 2 / (sin (α + β) * sin α * sin β) := by
  unfold edgeForm
  have hs := sin_add α β
  have hc := cos_add α β
  field_simp
  rw [hs, hc]
  have e1 := sin_sq_add_cos_sq α
  have e2 := sin_sq_add_cos_sq β
  linear_combination (x ^ 2 * sin β ^ 2) * e1 + (z ^ 2 * sin α ^ 2) * e2

lemma edgeForm_merge {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (hαβ : α + β < π) (x y z : ℝ) :
    edgeForm α x y + edgeForm β y z ≤ edgeForm (α + β) x z := by
  have s1 : 0 < sin α := sin_pos_of_pos_of_lt_pi hα (by linarith)
  have s2 : 0 < sin β := sin_pos_of_pos_of_lt_pi hβ (by linarith)
  have s3 : 0 < sin (α + β) := sin_pos_of_pos_of_lt_pi (by linarith) hαβ
  have := edgeForm_merge_eq α β x y z s1.ne' s2.ne' s3.ne'
  have : 0 ≤ (sin (α + β) * y - sin β * x - sin α * z) ^ 2 / (sin (α + β) * sin α * sin β) := by
    positivity
  linarith

/-- The triangle: the form is `(s₁ g₀ + s₂ g₁ + s₀ g₂)² / (s₀ s₁ s₂)`, `sᵢ = sin θᵢ`. -/
lemma edgeForm_triangle (a b x y z : ℝ) (ha : sin a ≠ 0) (hb : sin b ≠ 0)
    (hc : sin (2 * π - a - b) ≠ 0) :
    edgeForm a x y + edgeForm b y z + edgeForm (2 * π - a - b) z x =
      (sin b * x + sin (2 * π - a - b) * y + sin a * z) ^ 2 /
        (sin a * sin b * sin (2 * π - a - b)) := by
  have hs : sin (2 * π - a - b) = -(sin a * cos b + cos a * sin b) := by
    rw [show 2 * π - a - b = -(a + b) + 2 * π by ring, sin_add_two_pi, sin_neg, sin_add]
  have hco : cos (2 * π - a - b) = cos a * cos b - sin a * sin b := by
    rw [show 2 * π - a - b = -(a + b) + 2 * π by ring, cos_add_two_pi, cos_neg, cos_add]
  unfold edgeForm
  rw [hco]
  rw [hs] at hc ⊢
  have hc' : sin a * cos b + cos a * sin b ≠ 0 := fun h => hc (by rw [h]; ring)
  rw [div_neg, neg_mul, mul_neg, div_neg, div_neg]
  field_simp
  have e1 := sin_sq_add_cos_sq a
  have e2 := sin_sq_add_cos_sq b
  linear_combination (-x ^ 2 * sin b ^ 2) * e1 + (-z ^ 2 * sin a ^ 2) * e2

/-- The parallelogram: gaps `α, π - α, α, π - α`. -/
lemma edgeForm_parallelogram (α g₀ g₁ g₂ g₃ : ℝ) (hs : sin α ≠ 0) :
    edgeForm α g₀ g₁ + edgeForm (π - α) g₁ g₂ + edgeForm α g₂ g₃ + edgeForm (π - α) g₃ g₀ =
      2 / sin α * ((g₀ + g₂) * (g₁ + g₃)) := by
  unfold edgeForm
  rw [sin_pi_sub, cos_pi_sub]
  field_simp
  ring

/-! ## Cyclic rotation -/

lemma sum_range_succ_mod (k : ℕ) (G : ℕ → ℝ) :
    ∑ m ∈ range k, G ((m + 1) % k) = ∑ m ∈ range k, G m := by
  rcases k with _ | n
  · simp
  · rw [Finset.sum_range_succ, Finset.sum_range_succ' G]
    have h1 : ∀ m ∈ range n, G ((m + 1) % (n + 1)) = G (m + 1) := by
      intro m hm
      rw [Nat.mod_eq_of_lt (by simp at hm; omega)]
    rw [Finset.sum_congr rfl h1, Nat.mod_self]

lemma sum_range_rot (k r : ℕ) (G : ℕ → ℝ) :
    ∑ m ∈ range k, G ((m + r) % k) = ∑ m ∈ range k, G m := by
  induction r generalizing G with
  | zero =>
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Nat.add_zero, Nat.mod_eq_of_lt (Finset.mem_range.1 hm)]
  | succ r ih =>
    rw [← ih G, ← sum_range_succ_mod k (fun j => G ((j + r) % k))]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [Nat.mod_add_mod]
    congr 2
    omega

lemma polyForm_rot (k r : ℕ) (θ g : ℕ → ℝ) :
    polyForm k (fun m => θ ((m + r) % k)) (fun m => g ((m + r) % k)) = polyForm k θ g := by
  unfold polyForm
  rw [← sum_range_rot k r (fun j => edgeForm (θ j) (g j) (g ((j + 1) % k)))]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Nat.mod_add_mod]
  congr 3
  omega

lemma ValidGaps.rot {k : ℕ} {θ : ℕ → ℝ} (hv : ValidGaps k θ) (r : ℕ) :
    ValidGaps k (fun m => θ ((m + r) % k)) where
  three_le := hv.three_le
  pos m _ := hv.pos _ (Nat.mod_lt _ (by have := hv.three_le; omega))
  lt_pi m _ := hv.lt_pi _ (Nat.mod_lt _ (by have := hv.three_le; omega))
  sum_eq := by rw [sum_range_rot k r θ]; exact hv.sum_eq

lemma noPosPlane_of_rot {k r : ℕ} {θ : ℕ → ℝ}
    (h : NoPosPlane (polyForm k (fun m => θ ((m + r) % k)))) : NoPosPlane (polyForm k θ) := by
  intro f g hfg
  apply h (fun m => f ((m + r) % k)) (fun m => g ((m + r) % k))
  intro a b hab
  have := hfg a b hab
  rw [← polyForm_rot k r] at this
  exact this

/-! ## Merging the last two gaps -/

/-- Merging the last two gaps `θ_{j}, θ_{j+1}` of a `(j + 2)`-gon into one gap can only increase
the form. -/
lemma polyForm_le_merge (j : ℕ) (θ g : ℕ → ℝ) (hα : 0 < θ j) (hβ : 0 < θ (j + 1))
    (hαβ : θ j + θ (j + 1) < π) :
    polyForm (j + 2) θ g ≤ polyForm (j + 1) (Function.update θ j (θ j + θ (j + 1))) g := by
  unfold polyForm
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
  have h1 : ∑ m ∈ range j, edgeForm (θ m) (g m) (g ((m + 1) % (j + 2))) =
      ∑ m ∈ range j, edgeForm (Function.update θ j (θ j + θ (j + 1)) m) (g m)
        (g ((m + 1) % (j + 1))) := by
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm' := Finset.mem_range.1 hm
    rw [Function.update_of_ne (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  rw [h1, Function.update_self, Nat.mod_eq_of_lt (by omega : j + 1 < j + 2),
    show j + 1 + 1 = j + 2 by ring, Nat.mod_self, Nat.mod_self]
  have := edgeForm_merge hα hβ hαβ (g j) (g (j + 1)) (g 0)
  linarith

lemma ValidGaps.merge {j : ℕ} {θ : ℕ → ℝ} (hv : ValidGaps (j + 2) θ) (hj : 2 ≤ j)
    (hαβ : θ j + θ (j + 1) < π) :
    ValidGaps (j + 1) (Function.update θ j (θ j + θ (j + 1))) where
  three_le := by omega
  pos m hm := by
    rcases eq_or_ne m j with rfl | hne
    · rw [Function.update_self]; linarith [hv.pos m (by omega), hv.pos (m + 1) (by omega)]
    · rw [Function.update_of_ne hne]; exact hv.pos m (by omega)
  lt_pi m hm := by
    rcases eq_or_ne m j with rfl | hne
    · rw [Function.update_self]; exact hαβ
    · rw [Function.update_of_ne hne]; exact hv.lt_pi m (by omega)
  sum_eq := by
    have := hv.sum_eq
    rw [Finset.sum_range_succ, Finset.sum_range_succ] at this
    rw [Finset.sum_range_succ, Function.update_self]
    have h1 : ∑ m ∈ range j, Function.update θ j (θ j + θ (j + 1)) m = ∑ m ∈ range j, θ m :=
      Finset.sum_congr rfl fun m hm => by
        rw [Function.update_of_ne (by have := Finset.mem_range.1 hm; omega)]
    rw [h1]; linarith

/-! ## Base cases -/

lemma polyForm_three (θ g : ℕ → ℝ) :
    polyForm 3 θ g = edgeForm (θ 0) (g 0) (g 1) + edgeForm (θ 1) (g 1) (g 2) +
      edgeForm (θ 2) (g 2) (g 0) := by
  simp [polyForm, Finset.sum_range_succ]

lemma polyForm_four (θ g : ℕ → ℝ) :
    polyForm 4 θ g = edgeForm (θ 0) (g 0) (g 1) + edgeForm (θ 1) (g 1) (g 2) +
      edgeForm (θ 2) (g 2) (g 3) + edgeForm (θ 3) (g 3) (g 0) := by
  simp [polyForm, Finset.sum_range_succ]

lemma noPosPlane_three {θ : ℕ → ℝ} (hv : ValidGaps 3 θ) : NoPosPlane (polyForm 3 θ) := by
  have hsum := hv.sum_eq
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hsum
  have h2 : θ 2 = 2 * π - θ 0 - θ 1 := by linarith
  have hs : ∀ m < 3, sin (θ m) ≠ 0 := fun m hm =>
    (sin_pos_of_pos_of_lt_pi (hv.pos m hm) (hv.lt_pi m hm)).ne'
  have hs2 := hs 2 (by norm_num)
  rw [h2] at hs2
  refine noPosPlane_of_factor _ (1 / (sin (θ 0) * sin (θ 1) * sin (θ 2)))
    (fun g => sin (θ 1) * g 0 + sin (θ 2) * g 1 + sin (θ 0) * g 2)
    (fun g => sin (θ 1) * g 0 + sin (θ 2) * g 1 + sin (θ 0) * g 2) ?_ ?_
  · intro a b f g; ring
  · intro g
    rw [polyForm_three, h2, edgeForm_triangle _ _ _ _ _ (hs 0 (by norm_num)) (hs 1 (by norm_num))
      hs2]
    ring

lemma noPosPlane_parallelogram {θ : ℕ → ℝ} (hv : ValidGaps 4 θ)
    (h01 : θ 1 = π - θ 0) (h12 : θ 2 = θ 0) (h23 : θ 3 = π - θ 0) :
    NoPosPlane (polyForm 4 θ) := by
  have hs : sin (θ 0) ≠ 0 :=
    (sin_pos_of_pos_of_lt_pi (hv.pos 0 (by norm_num)) (hv.lt_pi 0 (by norm_num))).ne'
  refine noPosPlane_of_factor _ (2 / sin (θ 0)) (fun g => g 0 + g 2) (fun g => g 1 + g 3) ?_ ?_
  · intro a b f g; ring
  · intro g
    rw [polyForm_four, h01, h12, h23, edgeForm_parallelogram _ _ _ _ _ hs]
    ring

/-- If no two consecutive gaps (cyclically) sum to less than `π`, the polygon is a
parallelogram. -/
lemma exists_short_pair_or_parallelogram {k : ℕ} {θ : ℕ → ℝ} (hv : ValidGaps k θ) (hk : 4 ≤ k) :
    (∃ m < k, θ m + θ ((m + 1) % k) < π) ∨
      (k = 4 ∧ θ 1 = π - θ 0 ∧ θ 2 = θ 0 ∧ θ 3 = π - θ 0) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hshort, hpar⟩ := hcon
  have hsum2 : ∑ m ∈ range k, (θ m + θ ((m + 1) % k)) = 4 * π := by
    rw [Finset.sum_add_distrib, sum_range_succ_mod k θ, hv.sum_eq]; ring
  have hge : ∑ m ∈ range k, (π : ℝ) ≤ ∑ m ∈ range k, (θ m + θ ((m + 1) % k)) :=
    Finset.sum_le_sum fun m hm => hshort m (Finset.mem_range.1 hm)
  rw [hsum2, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hge
  have hk4 : (k : ℝ) ≤ 4 := by nlinarith [pi_pos]
  have hk' : k = 4 := by
    have : k ≤ 4 := by exact_mod_cast hk4
    omega
  subst hk'
  have hs := hv.sum_eq
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hs
  have a0 := hshort 0 (by norm_num)
  have a1 := hshort 1 (by norm_num)
  have a2 := hshort 2 (by norm_num)
  have a3 := hshort 3 (by norm_num)
  norm_num at a0 a1 a2 a3
  apply hpar rfl <;> linarith

/-! ## The main theorem -/

/-- **The polygon area form has a single positive direction**: for admissible gaps, `polyForm`
has no two-dimensional positive-definite restriction. -/
theorem polyForm_noPosPlane : ∀ (k : ℕ) (θ : ℕ → ℝ), ValidGaps k θ → NoPosPlane (polyForm k θ) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro θ hv
  have hk3 := hv.three_le
  rcases Nat.lt_or_ge k 4 with hk | hk
  · have : k = 3 := by omega
    subst this
    exact noPosPlane_three hv
  rcases exists_short_pair_or_parallelogram hv hk with ⟨m, hm, hshort⟩ | ⟨rfl, h1, h2, h3⟩
  · -- rotate so that the short pair sits at positions `k - 2, k - 1`
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    set r := m + 2 with hr
    set θ' : ℕ → ℝ := fun i => θ ((i + r) % (j + 2)) with hθ'
    have hv' : ValidGaps (j + 2) θ' := hv.rot r
    have e1 : θ' j = θ m := by
      simp only [θ', r]
      rw [show j + (m + 2) = m + (j + 2) by ring, Nat.add_mod_right, Nat.mod_eq_of_lt hm]
    have e2 : θ' (j + 1) = θ ((m + 1) % (j + 2)) := by
      simp only [θ', r]
      rw [show j + 1 + (m + 2) = (m + 1) + (j + 2) by ring, Nat.add_mod_right]
    have hshort' : θ' j + θ' (j + 1) < π := by rw [e1, e2]; exact hshort
    apply noPosPlane_of_rot (r := r)
    have hmerge := ih (j + 1) (by omega) _ (hv'.merge (by omega) hshort')
    intro f g hfg
    apply hmerge f g
    intro a b hab
    exact lt_of_lt_of_le (hfg a b hab)
      (polyForm_le_merge j θ' _ (hv'.pos j (by omega)) (hv'.pos (j + 1) (by omega)) hshort')
  · exact noPosPlane_parallelogram hv h1 h2 h3

/-- **Minkowski's inequality for polygons** (support-number form): if `q(p) > 0` then
`B(p, g)² ≥ q(p) q(g)`. -/
theorem polyForm_minkowski {k : ℕ} {θ : ℕ → ℝ} (hv : ValidGaps k θ) (p g : ℕ → ℝ)
    (hp : 0 < polyForm k θ p) :
    polyForm k θ p * polyForm k θ g ≤ polyBilin k θ p g ^ 2 := by
  by_contra hlt
  push_neg at hlt
  apply polyForm_noPosPlane k θ hv p g
  intro a b hab
  rw [polyForm_comb]
  set A := polyForm k θ p
  set B := polyBilin k θ p g
  set C := polyForm k θ g
  have key : A * (A * a ^ 2 + 2 * (a * b) * B + C * b ^ 2) =
      (A * a + B * b) ^ 2 + (A * C - B ^ 2) * b ^ 2 := by ring
  have hpos : 0 < (A * a + B * b) ^ 2 + (A * C - B ^ 2) * b ^ 2 := by
    rcases eq_or_ne b 0 with hb | hb
    · subst hb
      have ha : a ≠ 0 := by tauto
      have : A * a ≠ 0 := mul_ne_zero hp.ne' ha
      simpa using pow_pos (abs_pos.2 this) 2 |>.trans_eq (sq_abs _)
    · have : 0 < (A * C - B ^ 2) * b ^ 2 := mul_pos (by linarith) (by positivity)
      nlinarith [sq_nonneg (A * a + B * b)]
  have : 0 < A * (A * a ^ 2 + 2 * (a * b) * B + C * b ^ 2) := by rw [key]; exact hpos
  have := (pos_iff_pos_of_mul_pos this).1 hp
  linarith

end Erdos99
end

end MinkowskiPlane

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `HilbertLorentz`
-/

section HilbertLorentz

/-!
# Hilbert's argument: from a Bochner inequality to a single negative direction

This file proves the linear-algebra core of the volume-Hessian theorem (step (e) of §7.3 of the
Verification Guide), in the form used by Hilbert's proof of the Minkowski / Alexandrov–Fenchel
inequality (see also Shenfeld–van Handel's "Bochner method").

Let `H = -W` be a symmetric matrix with nonnegative off-diagonal entries whose positive entries
form a connected graph, and let `h > 0` be a vector with `b = H h > 0`.  If the **Bochner
inequality**

  `fᵀ H f ≤ ∑ᵢ (hᵢ / bᵢ) (H f)ᵢ²`     for all `f`

holds, then `H` is negative semidefinite on the hyperplane `bᵀ f = 0`, and therefore `W` has no
two-dimensional negative-definite restriction (`noNegativePlane_of_bochner`).

Proof: with the weights `Dᵢ = bᵢ / hᵢ`, `h` is an eigenvector of `D⁻¹H` for the eigenvalue `1`.
Maximising the Rayleigh quotient `fᵀHf / ∑ Dᵢ fᵢ²` on the hyperplane gives an eigenvector `y`
with eigenvalue `λ`; if `λ > 0` the Bochner inequality forces `λ ≥ 1`.  The global maximum of the
Rayleigh quotient is attained at a nonnegative vector, and pairing with `h` shows it equals `1`.
So `y` is a global maximiser, hence `y⁺` and `y⁻` are nonnegative eigenvectors; by connectivity
a nonzero one is everywhere positive (Perron–Frobenius), so `y` has constant sign, contradicting
`bᵀ y = 0`.

`noNegativePlane_of_facetForms` then derives the Bochner inequality from a decomposition of the
form into two-dimensional polygon area forms (one per facet) and the two-dimensional Minkowski
inequality `polyForm_minkowski`.
-/

open scoped BigOperators

@[expose] public noncomputable section

open Classical

namespace Erdos99

section Core

variable {κ : Type*} [Fintype κ]

/-- `xᵀ H w`. -/
def matBil (H : κ → κ → ℝ) (x w : κ → ℝ) : ℝ := ∑ i, ∑ j, H i j * x i * w j

/-- The weighted squared norm `∑ Dᵢ xᵢ²`. -/
def wNorm (D : κ → ℝ) (x : κ → ℝ) : ℝ := ∑ i, D i * x i ^ 2

/-- The weighted inner product `∑ Dᵢ xᵢ wᵢ`. -/
def wInner (D : κ → ℝ) (x w : κ → ℝ) : ℝ := ∑ i, D i * x i * w i

lemma matBil_add_smul (H : κ → κ → ℝ) (x w : κ → ℝ) (t : ℝ) :
    matBil H (fun i => x i + t * w i) (fun i => x i + t * w i) =
      matBil H x x + t * (matBil H x w + matBil H w x) + t ^ 2 * matBil H w w := by
  unfold matBil
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma matBil_comm (H : κ → κ → ℝ) (hs : ∀ i j, H i j = H j i) (x w : κ → ℝ) :
    matBil H x w = matBil H w x := by
  unfold matBil
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hs]; ring

lemma wNorm_add_smul (D x w : κ → ℝ) (t : ℝ) :
    wNorm D (fun i => x i + t * w i) = wNorm D x + t * (2 * wInner D x w) + t ^ 2 * wNorm D w := by
  unfold wNorm wInner
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

lemma matBil_smul (H : κ → κ → ℝ) (x : κ → ℝ) (c : ℝ) :
    matBil H (fun i => c * x i) (fun i => c * x i) = c ^ 2 * matBil H x x := by
  unfold matBil
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma wNorm_smul (D x : κ → ℝ) (c : ℝ) : wNorm D (fun i => c * x i) = c ^ 2 * wNorm D x := by
  unfold wNorm
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

lemma wNorm_nonneg {D : κ → ℝ} (hD : ∀ i, 0 < D i) (x : κ → ℝ) : 0 ≤ wNorm D x :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hD i).le (sq_nonneg _)

lemma eq_zero_of_wNorm_eq_zero {D : κ → ℝ} (hD : ∀ i, 0 < D i) {x : κ → ℝ}
    (hx : wNorm D x = 0) (i : κ) : x i = 0 := by
  have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_nonneg (hD i).le (sq_nonneg (x i))).1
    hx i (Finset.mem_univ _)
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h (hD i).ne'
  · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h

/-- If `a t + c t² ≤ 0` for every real `t`, then `a = 0`. -/
lemma eq_zero_of_lin_quad_nonpos {a c : ℝ} (h : ∀ t : ℝ, a * t + c * t ^ 2 ≤ 0) : a = 0 := by
  have h1 := h (a / (1 + |c|))
  have hc : 0 < 1 + |c| := by positivity
  have h2 : a * (a / (1 + |c|)) + c * (a / (1 + |c|)) ^ 2 =
      a ^ 2 * (1 + |c| + c) / (1 + |c|) ^ 2 := by
    field_simp
  rw [h2] at h1
  have h3 : 0 < 1 + |c| + c := by have := neg_abs_le c; linarith
  have h4 : a ^ 2 * (1 + |c| + c) ≤ 0 := by
    have := div_nonpos_iff.1 h1
    rcases this with ⟨_, h⟩ | ⟨h, _⟩
    · nlinarith [sq_nonneg (1 + |c|)]
    · exact h
  have : a ^ 2 ≤ 0 := by nlinarith [sq_nonneg a]
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm this (sq_nonneg a))

/-- **First variation.**  If `y` maximises `xᵀHx - λ ∑ Dᵢxᵢ²` (value `0`) over a set closed under
`y + t w`, then `yᵀHw + wᵀHy = 2 λ ⟨y, w⟩_D`. -/
lemma first_variation (H : κ → κ → ℝ) (D : κ → ℝ) (lam : ℝ) (y w : κ → ℝ)
    (hmax : ∀ t : ℝ, matBil H (fun i => y i + t * w i) (fun i => y i + t * w i) ≤
      lam * wNorm D (fun i => y i + t * w i))
    (hy : matBil H y y = lam * wNorm D y) :
    matBil H y w + matBil H w y = lam * (2 * wInner D y w) := by
  have := eq_zero_of_lin_quad_nonpos (a := matBil H y w + matBil H w y - lam * (2 * wInner D y w))
    (c := matBil H w w - lam * wNorm D w) fun t => by
      have h := hmax t
      rw [matBil_add_smul, wNorm_add_smul] at h
      nlinarith
  linarith

/-- The `i`-th entry of `H x`. -/
def matVec (H : κ → κ → ℝ) (x : κ → ℝ) (i : κ) : ℝ := ∑ j, H i j * x j

lemma matBil_eq_sum_matVec (H : κ → κ → ℝ) (x w : κ → ℝ) :
    matBil H x w = ∑ i, x i * matVec H w i := by
  unfold matBil matVec
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma matBil_eq_sum_matVec' (H : κ → κ → ℝ) (hs : ∀ i j, H i j = H j i) (x w : κ → ℝ) :
    matBil H x w = ∑ j, w j * matVec H x j := by
  rw [matBil_comm H hs, matBil_eq_sum_matVec]

/-- Positivity (Perron–Frobenius): a nonnegative nonzero `v` with `H v = c D v` and connected
positive pattern of `H` is everywhere positive. -/
lemma pos_of_eigen_nonneg (H : κ → κ → ℝ) (D : κ → ℝ) (c : ℝ)
    (hoff : ∀ i j, i ≠ j → 0 ≤ H i j)
    (hconn : ∀ U : Finset κ, U.Nonempty → U ≠ Finset.univ → ∃ i ∈ U, ∃ j ∉ U, 0 < H i j)
    (v : κ → ℝ) (hv0 : ∀ i, 0 ≤ v i) (hv : ∃ i, v i ≠ 0)
    (heig : ∀ i, matVec H v i = c * D i * v i) : ∀ i, 0 < v i := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨i₀, hi₀⟩ := hcon
  set U := Finset.univ.filter (fun i => v i = 0)
  have hU : U.Nonempty := ⟨i₀, by simp [U]; linarith [hv0 i₀]⟩
  have hU' : U ≠ Finset.univ := by
    obtain ⟨k, hk⟩ := hv
    intro h
    have : k ∈ U := h ▸ Finset.mem_univ k
    simp [U] at this
    exact hk this
  obtain ⟨i, hi, j, hj, hij⟩ := hconn U hU hU'
  simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  have hvj : 0 < v j := lt_of_le_of_ne (hv0 j) (Ne.symm hj)
  have h1 := heig i
  rw [hi, mul_zero] at h1
  have hne : i ≠ j := fun h => hj (h ▸ hi)
  have h2 : 0 < matVec H v i := by
    unfold matVec
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    have : 0 ≤ ∑ k ∈ Finset.univ.erase j, H i k * v k := by
      refine Finset.sum_nonneg fun k _ => ?_
      rcases eq_or_ne i k with rfl | hik
      · rw [hi, mul_zero]
      · exact mul_nonneg (hoff i k hik) (hv0 k)
    have : 0 < H i j * v j := mul_pos hij hvj
    linarith
  linarith

/-- **Core of Hilbert's argument** (Fintype version).  Under the hypotheses of the module
docstring, `H` is negative semidefinite on the hyperplane `bᵀ x = 0`. -/
theorem nonpos_on_hyperplane_of_bochner (H : κ → κ → ℝ) (hs : ∀ i j, H i j = H j i)
    (hoff : ∀ i j, i ≠ j → 0 ≤ H i j)
    (hconn : ∀ U : Finset κ, U.Nonempty → U ≠ Finset.univ → ∃ i ∈ U, ∃ j ∉ U, 0 < H i j)
    (h : κ → ℝ) (hh : ∀ i, 0 < h i) (hb : ∀ i, 0 < matVec H h i)
    (hboch : ∀ f, matBil H f f ≤ ∑ i, h i / matVec H h i * matVec H f i ^ 2)
    (x : κ → ℝ) (hx : ∑ i, matVec H h i * x i = 0) : matBil H x x ≤ 0 := by
  set b := matVec H h with hbdef
  set D : κ → ℝ := fun i => b i / h i with hDdef
  have hD : ∀ i, 0 < D i := fun i => div_pos (hb i) (hh i)
  have hDh : ∀ i, D i * h i = b i := fun i => div_mul_cancel₀ _ (hh i).ne'
  by_contra hpos
  push_neg at hpos
  -- the constraint set on the hyperplane
  set V : Set (κ → ℝ) := {z | ∑ i, b i * z i = 0}
  have hVlin : ∀ z w, z ∈ V → w ∈ V → ∀ t : ℝ, (fun i => z i + t * w i) ∈ V := by
    intro z w hz hw t
    simp only [V, Set.mem_setOf_eq] at hz hw ⊢
    simp only [mul_add, Finset.sum_add_distrib]
    rw [hz]
    simp only [mul_left_comm (b _) t, ← Finset.mul_sum, hw, mul_zero, add_zero]
  have hVsmul : ∀ z, z ∈ V → ∀ c : ℝ, (fun i => c * z i) ∈ V := by
    intro z hz c
    simp only [V, Set.mem_setOf_eq] at hz ⊢
    simp only [mul_left_comm (b _) c, ← Finset.mul_sum, hz, mul_zero]
  -- compactness of the unit spheres
  set R : ℝ := ∑ i, (1 + 1 / D i)
  have hsphere_bdd : ∀ z, wNorm D z = 1 → ‖z‖ ≤ R := by
    intro z hz
    have hR : 0 ≤ R := Finset.sum_nonneg fun i _ => by have := hD i; positivity
    refine (pi_norm_le_iff_of_nonneg hR).2 fun i => ?_
    have hzi : D i * z i ^ 2 ≤ 1 := by
      rw [← hz]
      exact Finset.single_le_sum (f := fun i => D i * z i ^ 2)
        (fun i _ => mul_nonneg (hD i).le (sq_nonneg _)) (Finset.mem_univ i)
    have h1 : z i ^ 2 ≤ 1 / D i := by rw [le_div_iff₀ (hD i)]; linarith
    have h2 : |z i| ≤ 1 + 1 / D i := by
      nlinarith [sq_abs (z i), abs_nonneg (z i), sq_nonneg (|z i| - 1)]
    rw [Real.norm_eq_abs]
    calc |z i| ≤ 1 + 1 / D i := h2
      _ ≤ R := Finset.single_le_sum (f := fun i => 1 + 1 / D i)
          (fun i _ => by have := hD i; positivity) (Finset.mem_univ i)
  have hcontQ : Continuous fun z : κ → ℝ => matBil H z z := by
    unfold matBil; fun_prop
  have hcontN : Continuous fun z : κ → ℝ => wNorm D z := by
    unfold wNorm; fun_prop
  have hcontL : Continuous fun z : κ → ℝ => ∑ i, b i * z i := by fun_prop
  -- normalisation
  have hnorm : ∀ z, z ≠ 0 → 0 < wNorm D z := by
    intro z hz
    rcases (wNorm_nonneg hD z).lt_or_eq with h | h
    · exact h
    · exact absurd (funext fun i => eq_zero_of_wNorm_eq_zero hD h.symm i) hz
  have hscale : ∀ z, z ≠ 0 → wNorm D (fun i => (wNorm D z)⁻¹ ^ (1/2 : ℝ) * z i) = 1 := by
    intro z hz
    rw [wNorm_smul]
    have := hnorm z hz
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
    field_simp
  -- maximiser on the hyperplane sphere
  set KV := {z : κ → ℝ | wNorm D z = 1 ∧ ∑ i, b i * z i = 0}
  have hKV : IsCompact KV := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact (isClosed_eq hcontN continuous_const).inter (isClosed_eq hcontL continuous_const)
    · exact (Metric.isBounded_closedBall (x := (0 : κ → ℝ)) (r := R)).subset fun z hz => by
        simpa using hsphere_bdd z hz.1
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp [matBil] at hpos
  set x' := fun i => (wNorm D x)⁻¹ ^ (1/2 : ℝ) * x i
  have hx'K : x' ∈ KV := ⟨hscale x hx0, hVsmul x hx _⟩
  obtain ⟨y, hyK, hymax⟩ := hKV.exists_isMaxOn ⟨x', hx'K⟩ hcontQ.continuousOn
  set lam := matBil H y y
  have hlam_pos : 0 < lam := by
    have h1 : matBil H x' x' ≤ lam := hymax hx'K
    have hq : matBil H x' x' = ((wNorm D x)⁻¹ ^ (1/2 : ℝ)) ^ 2 * matBil H x x := matBil_smul _ _ _
    have : 0 < matBil H x' x' := by
      rw [hq]
      have : 0 < (wNorm D x)⁻¹ ^ (1/2 : ℝ) := by have := hnorm x hx0; positivity
      positivity
    linarith
  -- `xᵀHx ≤ λ N(x)` on the hyperplane
  have hboundV : ∀ z ∈ V, matBil H z z ≤ lam * wNorm D z := by
    intro z hz
    by_cases hz0 : z = 0
    · subst hz0; simp [matBil, wNorm]
    · have hzK : (fun i => (wNorm D z)⁻¹ ^ (1/2 : ℝ) * z i) ∈ KV :=
        ⟨hscale z hz0, hVsmul z hz _⟩
      have h1 := hymax hzK
      simp only [Set.mem_setOf_eq] at h1
      rw [matBil_smul] at h1
      have hN := hnorm z hz0
      have hc : ((wNorm D z)⁻¹ ^ (1/2 : ℝ)) ^ 2 = (wNorm D z)⁻¹ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
      rw [hc] at h1
      have := mul_le_mul_of_nonneg_left h1 hN.le
      rw [← mul_assoc, mul_inv_cancel₀ hN.ne', one_mul] at this
      linarith
  have hyN : wNorm D y = 1 := hyK.1
  have hyV : y ∈ V := hyK.2
  -- eigen equation on the hyperplane: `H y = λ D y`
  have hvar : ∀ w ∈ V, matBil H y w = lam * wInner D y w := by
    intro w hw
    have := first_variation H D lam y w (fun t => hboundV _ (hVlin y w hyV hw t))
      (by rw [hyN, mul_one])
    rw [matBil_comm H hs w y] at this
    linarith
  set r : κ → ℝ := fun i => matVec H y i - lam * D i * y i
  have hr_h : ∑ i, r i * h i = 0 := by
    have h1 : ∑ i, matVec H y i * h i = ∑ i, b i * y i := by
      calc ∑ i, matVec H y i * h i = matBil H h y := by
            rw [matBil_eq_sum_matVec]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
        _ = ∑ i, b i * y i := by
            rw [matBil_eq_sum_matVec' H hs]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have h2 : ∑ i, lam * D i * y i * h i = lam * ∑ i, b i * y i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [← hDh i]; ring
    simp only [r, sub_mul, Finset.sum_sub_distrib, h1, h2]
    rw [show ∑ i, b i * y i = 0 from hyV]; ring
  have hr_w : ∀ w ∈ V, ∑ i, r i * w i = 0 := by
    intro w hw
    have := hvar w hw
    rw [matBil_eq_sum_matVec' H hs] at this
    simp only [r, sub_mul, Finset.sum_sub_distrib]
    have h2 : ∑ i, lam * D i * y i * w i = lam * wInner D y w := by
      rw [wInner, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [h2, ← this, sub_eq_zero]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  haveI : Nonempty κ := by
    by_contra hc
    exact hx0 (funext fun i => absurd ⟨i⟩ hc)
  have hbh : 0 < ∑ i, b i * h i :=
    Finset.sum_pos (fun i _ => mul_pos (hb i) (hh i)) ⟨Classical.arbitrary κ, Finset.mem_univ _⟩
  have hr0 : ∀ i, r i = 0 := by
    set α := (∑ i, b i * r i) / ∑ i, b i * h i
    have hwV : (fun i => r i + (-α) * h i) ∈ V := by
      simp only [V, Set.mem_setOf_eq, mul_add, Finset.sum_add_distrib]
      simp only [mul_left_comm (b _) (-α), ← Finset.mul_sum]
      simp only [α]; field_simp; ring
    have := hr_w _ hwV
    simp only [mul_add, Finset.sum_add_distrib] at this
    have h3 : ∑ i, r i * (-α * h i) = 0 := by
      simp only [mul_left_comm (r _) (-α), ← Finset.mul_sum, hr_h, mul_zero]
    rw [h3, add_zero] at this
    have hsq : ∑ i, r i ^ 2 = 0 := by rw [← this]; simp [sq]
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (r i)).1 hsq i
      (Finset.mem_univ _)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  have heig : ∀ i, matVec H y i = lam * D i * y i := fun i => by
    have := hr0 i; simp only [r] at this; linarith
  -- Bochner forces `λ ≥ 1`
  have hlam1 : 1 ≤ lam := by
    have h1 := hboch y
    have h2 : ∑ i, h i / b i * matVec H y i ^ 2 = lam ^ 2 * wNorm D y := by
      rw [wNorm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [heig i]
      have := hh i; have := hb i
      simp only [D]; field_simp
    rw [h2, hyN] at h1
    nlinarith
  -- the global maximum
  set K := {z : κ → ℝ | wNorm D z = 1}
  have hK : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded (isClosed_eq hcontN continuous_const) ?_
    exact (Metric.isBounded_closedBall (x := (0 : κ → ℝ)) (r := R)).subset fun z hz => by
      simpa using hsphere_bdd z hz
  obtain ⟨z, hzK, hzmax⟩ := hK.exists_isMaxOn ⟨y, hyN⟩ hcontQ.continuousOn
  set mu := matBil H z z
  have hbound : ∀ w, matBil H w w ≤ mu * wNorm D w := by
    intro w
    by_cases hw0 : w = 0
    · subst hw0; simp [matBil, wNorm]
    · have hwK : (fun i => (wNorm D w)⁻¹ ^ (1/2 : ℝ) * w i) ∈ K := hscale w hw0
      have h1 := hzmax hwK
      simp only [Set.mem_setOf_eq] at h1
      rw [matBil_smul] at h1
      have hN := hnorm w hw0
      have hc : ((wNorm D w)⁻¹ ^ (1/2 : ℝ)) ^ 2 = (wNorm D w)⁻¹ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
      rw [hc] at h1
      have := mul_le_mul_of_nonneg_left h1 hN.le
      rw [← mul_assoc, mul_inv_cancel₀ hN.ne', one_mul] at this
      linarith
  have habs_ge : ∀ w : κ → ℝ, matBil H w w ≤ matBil H (fun i => |w i|) (fun i => |w i|) := by
    intro w
    unfold matBil
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    rcases eq_or_ne i j with rfl | hij
    · rw [mul_assoc, mul_assoc, ← abs_mul_abs_self (w i)]
    · rw [mul_assoc, mul_assoc, ← abs_mul (w i) (w j)]
      exact mul_le_mul_of_nonneg_left (le_abs_self _) (hoff i j hij)
  have hwNorm_abs : ∀ w : κ → ℝ, wNorm D (fun i => |w i|) = wNorm D w := by
    intro w; simp [wNorm, sq_abs]
  -- a global maximiser gives an eigenvector
  have hglob_eig : ∀ w, matBil H w w = mu * wNorm D w → ∀ i, matVec H w i = mu * D i * w i := by
    intro w hw
    have hvar' : ∀ v, matBil H w v = mu * wInner D w v := by
      intro v
      have := first_variation H D mu w v (fun t => hbound _) hw
      rw [matBil_comm H hs v w] at this
      linarith
    set r' : κ → ℝ := fun i => matVec H w i - mu * D i * w i
    have : ∑ i, r' i * r' i = 0 := by
      have := hvar' r'
      rw [matBil_eq_sum_matVec' H hs] at this
      simp only [r', sub_mul, Finset.sum_sub_distrib]
      have h2 : ∑ i, mu * D i * w i * r' i = mu * wInner D w r' := by
        rw [wInner, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      rw [h2, ← this, sub_eq_zero]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_self_nonneg (r' i)).1 this i
      (Finset.mem_univ _)
    have := mul_self_eq_zero.1 this
    simp only [r'] at this
    linarith
  -- the global maximum is `1`
  have hmu : mu = 1 := by
    have hzabs : matBil H (fun i => |z i|) (fun i => |z i|) = mu * wNorm D (fun i => |z i|) := by
      apply le_antisymm (hbound _)
      rw [hwNorm_abs, hzK.out, mul_one]
      exact habs_ge z
    have he := hglob_eig _ hzabs
    have h1 : ∑ i, h i * matVec H (fun i => |z i|) i = ∑ i, b i * |z i| := by
      rw [← matBil_eq_sum_matVec, matBil_eq_sum_matVec' H hs]
      exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]
    have h2 : ∑ i, h i * matVec H (fun i => |z i|) i = mu * ∑ i, b i * |z i| := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [he i, ← hDh i]; ring
    have hz0 : ∃ i, z i ≠ 0 := by
      by_contra hc; push_neg at hc
      have : wNorm D z = 0 := by simp [wNorm, hc]
      rw [hzK.out] at this; exact one_ne_zero this
    have hpos : 0 < ∑ i, b i * |z i| := by
      obtain ⟨i, hi⟩ := hz0
      exact Finset.sum_pos' (fun j _ => mul_nonneg (hb j).le (abs_nonneg _))
        ⟨i, Finset.mem_univ _, mul_pos (hb i) (abs_pos.2 hi)⟩
    have : (mu - 1) * ∑ i, b i * |z i| = 0 := by rw [sub_mul, ← h2, h1]; ring
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  have hmu_ge : lam ≤ mu := hzmax hyN
  have hlam : lam = 1 := by linarith
  -- `y` is a global maximiser, so `y⁺` and `y⁻` are nonnegative eigenvectors
  have hy_glob : matBil H y y = mu * wNorm D y := by rw [hyN, hmu, mul_one]; exact hlam
  have hyabs : matBil H (fun i => |y i|) (fun i => |y i|) = mu * wNorm D (fun i => |y i|) := by
    apply le_antisymm (hbound _)
    rw [hwNorm_abs, hyN, mul_one]
    calc mu = matBil H y y := by rw [hy_glob, hyN, mul_one]
      _ ≤ _ := habs_ge y
  have he1 := hglob_eig _ hy_glob
  have he2 := hglob_eig _ hyabs
  have hlin : ∀ (s : ℝ), ∀ i, matVec H (fun j => (|y j| + s * y j) / 2) i =
      mu * D i * ((|y i| + s * y i) / 2) := by
    intro s i
    have : matVec H (fun j => (|y j| + s * y j) / 2) i =
        (matVec H (fun j => |y j|) i + s * matVec H y i) / 2 := by
      unfold matVec
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, he1 i, he2 i]; ring
  have hypos : ∀ s : ℝ, (s = 1 ∨ s = -1) → (∃ i, (|y i| + s * y i) / 2 ≠ 0) →
      ∀ i, 0 < (|y i| + s * y i) / 2 := by
    intro s hs' hne
    refine pos_of_eigen_nonneg H D mu hoff hconn _ (fun i => ?_) hne (hlin s)
    rcases hs' with rfl | rfl
    · have := neg_abs_le (y i); linarith
    · have := le_abs_self (y i); linarith
  have hyV' : ∑ i, b i * y i = 0 := hyV
  have hy0 : ∃ i, y i ≠ 0 := by
    by_contra hc; push_neg at hc
    have : wNorm D y = 0 := by simp [wNorm, hc]
    rw [hyN] at this; exact one_ne_zero this
  by_cases hp : ∃ i, (|y i| + 1 * y i) / 2 ≠ 0
  · by_cases hm : ∃ i, (|y i| + (-1) * y i) / 2 ≠ 0
    · have h1 := hypos 1 (Or.inl rfl) hp
      have h2 := hypos (-1) (Or.inr rfl) hm
      obtain ⟨i⟩ : Nonempty κ := ⟨Classical.choose hy0⟩
      have a1 := h1 i
      have a2 := h2 i
      rcases le_or_gt 0 (y i) with hyi | hyi
      · rw [abs_of_nonneg hyi] at a2; linarith
      · rw [abs_of_neg hyi] at a1; linarith
    · push_neg at hm
      -- `y ≥ 0`
      have hge : ∀ i, 0 ≤ y i := fun i => by
        have := hm i
        have := neg_abs_le (y i)
        have : |y i| = y i := by linarith
        rw [← this]; exact abs_nonneg _
      obtain ⟨i, hi⟩ := hy0
      have : 0 < ∑ i, b i * y i := Finset.sum_pos' (fun j _ => mul_nonneg (hb j).le (hge j))
        ⟨i, Finset.mem_univ _, mul_pos (hb i) (lt_of_le_of_ne (hge i) (Ne.symm hi))⟩
      linarith
  · push_neg at hp
    have hle : ∀ i, y i ≤ 0 := fun i => by
      have := hp i
      have : |y i| = -y i := by linarith
      have := abs_nonneg (y i)
      linarith
    obtain ⟨i, hi⟩ := hy0
    have : ∑ i, b i * y i < 0 := by
      have : 0 < ∑ i, b i * (-y i) := Finset.sum_pos'
        (fun j _ => mul_nonneg (hb j).le (by linarith [hle j]))
        ⟨i, Finset.mem_univ _, mul_pos (hb i) (by
          have := lt_of_le_of_ne (hle i) hi; linarith)⟩
      simp only [mul_neg, Finset.sum_neg_distrib] at this
      linarith
    linarith

end Core

section Finset

variable {ι : Type*}

/-- Extension by zero of a function on the subtype `S`. -/
def extS (S : Finset ι) (f : S → ℝ) (i : ι) : ℝ := if h : i ∈ S then f ⟨i, h⟩ else 0

lemma extS_coe (S : Finset ι) (f : S → ℝ) (i : S) : extS S f i = f i := by
  simp [extS, i.2]

/-- **Hilbert's argument, `Finset` form.**  Let `W` be symmetric with nonpositive off-diagonal
entries on `S`, whose negative entries connect `S`.  Let `h > 0` on `S` with `b = -W h > 0`
on `S`, and assume the Bochner inequality
`-fᵀ W f ≤ ∑ᵢ (hᵢ / bᵢ) (W f)ᵢ²`.  Then `W` has no two-dimensional negative-definite
restriction. -/
theorem noNegativePlane_of_bochner {S : Finset ι} {W : ι → ι → ℝ} (hWs : ∀ i j, W i j = W j i)
    (hneg : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → W i j ≤ 0)
    (hconn : ∀ U ⊆ S, U.Nonempty → U ≠ S → ∃ i ∈ U, ∃ j ∈ S, j ∉ U ∧ W i j < 0)
    (h : ι → ℝ) (hh : ∀ i ∈ S, 0 < h i) (hb : ∀ i ∈ S, 0 < -∑ j ∈ S, W i j * h j)
    (hboch : ∀ f : ι → ℝ, -quadForm S W f ≤
      ∑ i ∈ S, h i / (-∑ j ∈ S, W i j * h j) * (∑ j ∈ S, W i j * f j) ^ 2) :
    NoNegativePlane S W := by
  intro f g hfg
  set c : ι → ℝ := fun i => -∑ j ∈ S, W i j * h j
  -- a vector of the negative plane on the hyperplane `∑ cᵢ xᵢ = 0`
  obtain ⟨x, hxneg, hxc⟩ : ∃ x : ι → ℝ, quadForm S W x < 0 ∧ ∑ i ∈ S, c i * x i = 0 := by
    set α := ∑ i ∈ S, c i * g i
    set β := ∑ i ∈ S, c i * f i
    by_cases hab : α ≠ 0 ∨ -β ≠ 0
    · refine ⟨_, hfg α (-β) hab, ?_⟩
      simp only [mul_add, Finset.sum_add_distrib]
      simp only [mul_left_comm (c _) α, mul_left_comm (c _) (-β), ← Finset.mul_sum]
      ring
    · push_neg at hab
      refine ⟨fun i => 1 * f i + 0 * g i, hfg 1 0 (Or.inl one_ne_zero), ?_⟩
      simp only [one_mul, zero_mul, add_zero]
      linarith [hab.2]
  -- transfer to the subtype
  set H : S → S → ℝ := fun i j => -W i j
  have hHs : ∀ i j, H i j = H j i := fun i j => by simp [H, hWs]
  have hHoff : ∀ i j, i ≠ j → 0 ≤ H i j := fun i j hij => by
    have := hneg i i.2 j j.2 (fun h => hij (Subtype.ext h))
    simp only [H]; linarith
  have hHconn : ∀ U : Finset S, U.Nonempty → U ≠ Finset.univ → ∃ i ∈ U, ∃ j ∉ U, 0 < H i j := by
    intro U hU hU'
    set U' : Finset ι := U.map (Function.Embedding.subtype _)
    have hsub : U' ⊆ S := fun i hi => by
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.1 hi; exact j.2
    have hne : U'.Nonempty := hU.map
    have hne' : U' ≠ S := by
      intro heq
      apply hU'
      ext i
      simp only [Finset.mem_univ, iff_true]
      have : (i : ι) ∈ U' := by rw [heq]; exact i.2
      obtain ⟨j, hj, hji⟩ := Finset.mem_map.1 this
      rwa [show j = i from Subtype.ext hji] at hj
    obtain ⟨i, hi, j, hjS, hjU, hW⟩ := hconn U' hsub hne hne'
    obtain ⟨i', hi', rfl⟩ := Finset.mem_map.1 hi
    refine ⟨i', hi', ⟨j, hjS⟩, fun hj => hjU (Finset.mem_map.2 ⟨_, hj, rfl⟩), ?_⟩
    simp only [H]; simpa using hW
  have hsum : ∀ F : ι → ℝ, ∑ i : S, F i = ∑ i ∈ S, F i := fun F => Finset.sum_coe_sort S F
  have hmatVec : ∀ (y : ι → ℝ) (i : S), matVec H (fun j => y j) i = -∑ j ∈ S, W i j * y j := by
    intro y i
    simp only [matVec, H, neg_mul, Finset.sum_neg_distrib]
    rw [hsum (fun j => W i j * y j)]
  have hmatBil : ∀ y : ι → ℝ, matBil H (fun j => y j) (fun j => y j) = -quadForm S W y := by
    intro y
    simp only [matBil, H, quadForm, neg_mul, Finset.sum_neg_distrib]
    rw [hsum (fun i => ∑ j : S, W i j * y i * y j)]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    exact hsum (fun j => W i j * y i * y j)
  have key := nonpos_on_hyperplane_of_bochner H hHs hHoff hHconn (fun i => h i)
    (fun i => hh i i.2) (fun i => by rw [hmatVec]; exact hb i i.2) (fun f' => by
      have h1 := hboch (extS S f')
      have e2 : matBil H f' f' = -quadForm S W (extS S f') := by
        rw [← hmatBil (extS S f')]; simp only [extS_coe]
      have e3 : ∀ i, matVec H f' i = -∑ j ∈ S, W i j * extS S f' j := fun i => by
        rw [← hmatVec]; simp only [extS_coe]
      rw [e2]
      simp only [e3, hmatVec, neg_sq]
      rw [hsum (fun i => h i / (-∑ j ∈ S, W i j * h j) * (∑ j ∈ S, W i j * extS S f' j) ^ 2)]
      exact h1)
    (fun i => x i) (by
      simp only [hmatVec]
      rw [hsum (fun i => (-∑ j ∈ S, W i j * h j) * x i)]
      exact hxc)
  rw [hmatBil] at key
  linarith

lemma polyBilin_self (k : ℕ) (θ p : ℕ → ℝ) : polyBilin k θ p p = polyForm k θ p := by
  unfold polyBilin polyForm edgeBilin edgeForm
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

/-- **Hilbert's argument from facet area forms.**  Suppose that, for each `i ∈ S`, there is a
two-dimensional polygon area form `qᵢ = polyForm (k i) (θ i)` (admissible gaps) and a map
`Gᵢ` (the induced support numbers in the plane of the `i`-th facet) such that

* `-(W f)ᵢ = Bᵢ(Gᵢ h, Gᵢ f)` (the derivative of the facet area, with `Bᵢ` the polar form),
* `-fᵀ W f = ∑ᵢ hᵢ qᵢ(Gᵢ f)` (symmetry of mixed volumes, `V(f, h, f) = V(h, f, f)`), and
* every facet has positive area, `qᵢ(Gᵢ h) > 0`.

If moreover `W` is symmetric with nonpositive off-diagonal entries whose negative entries connect
`S`, and `h > 0` on `S`, then `W` has no two-dimensional negative-definite restriction.  The
Bochner inequality is obtained facet by facet from Minkowski's inequality `polyForm_minkowski`. -/
theorem noNegativePlane_of_facetForms {S : Finset ι} {W : ι → ι → ℝ}
    (hWs : ∀ i j, W i j = W j i) (hneg : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → W i j ≤ 0)
    (hconn : ∀ U ⊆ S, U.Nonempty → U ≠ S → ∃ i ∈ U, ∃ j ∈ S, j ∉ U ∧ W i j < 0)
    (h : ι → ℝ) (hh : ∀ i ∈ S, 0 < h i)
    (k : ι → ℕ) (θ : ι → ℕ → ℝ) (hθ : ∀ i ∈ S, ValidGaps (k i) (θ i))
    (G : ι → (ι → ℝ) → ℕ → ℝ)
    (hrow : ∀ f : ι → ℝ, ∀ i ∈ S, -∑ j ∈ S, W i j * f j = polyBilin (k i) (θ i) (G i h) (G i f))
    (hsym : ∀ f : ι → ℝ, -quadForm S W f = ∑ i ∈ S, h i * polyForm (k i) (θ i) (G i f))
    (harea : ∀ i ∈ S, 0 < polyForm (k i) (θ i) (G i h)) :
    NoNegativePlane S W := by
  have hb : ∀ i ∈ S, -∑ j ∈ S, W i j * h j = polyForm (k i) (θ i) (G i h) := fun i hi => by
    rw [hrow h i hi, polyBilin_self]
  have hb' : ∀ i ∈ S, 0 < -∑ j ∈ S, W i j * h j := fun i hi => (hb i hi).symm ▸ harea i hi
  refine noNegativePlane_of_bochner hWs hneg hconn h hh hb' fun f => ?_
  rw [hsym f]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [hb i hi]
  have hp := harea i hi
  have hmin := polyForm_minkowski (hθ i hi) (G i h) (G i f) hp
  have hW : (∑ j ∈ S, W i j * f j) ^ 2 = polyBilin (k i) (θ i) (G i h) (G i f) ^ 2 := by
    rw [← hrow f i hi, neg_sq]
  rw [hW, div_mul_eq_mul_div, mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (hh i hi).le
  rw [le_div_iff₀ hp]
  linarith

end Finset

end Erdos99
end

end HilbertLorentz

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `Polytope`
-/

section Polytope

/-!
# Polytopes given by inequalities, and minus their volume Hessians

The polyhedron `polyK S u h = {x : ⟪u k, x⟫ ≤ h k, k ∈ S}` in `ℝ³`, its facets, the condition
that every facet is genuinely present, and minus the support-number volume Hessian
`polytopeHessian` (used in step (e) of the fan theorem, `FanTheorem`).
-/

open scoped BigOperators

@[expose] public noncomputable section

open Classical

namespace Erdos99

/-- Euclidean three-space. -/
abbrev Space3 := EuclideanSpace ℝ (Fin 3)

variable {ι : Type*}

/-! ## Polytopes and their volume Hessians (step (e)) -/

/-- The polyhedron `{x : ⟪u k, x⟫ ≤ h k for all k ∈ S}`. -/
def polyK (S : Finset ι) (u : ι → Space3) (h : ι → ℝ) : Set Space3 :=
  {x | ∀ k ∈ S, inner ℝ (u k) x ≤ h k}

/-- The face of `polyK S u h` in direction `u i`. -/
def polyFacet (S : Finset ι) (u : ι → Space3) (h : ι → ℝ) (i : ι) : Set Space3 :=
  {x | x ∈ polyK S u h ∧ inner ℝ (u i) x = h i}

/-- Every inequality of `polyK S u h` defines a genuine facet: it is attained at a point where all
the other inequalities are strict. -/
def FacetsPresent (S : Finset ι) (u : ι → Space3) (h : ι → ℝ) : Prop :=
  ∀ i ∈ S, ∃ x : Space3, inner ℝ (u i) x = h i ∧ ∀ k ∈ S, k ≠ i → inner ℝ (u k) x < h k

/-- Minus the support-number volume Hessian of the polytope `polyK S u h` (for unit normals
`u`).  Off the diagonal, the entry is `-length(F_i ∩ F_j) / |u_i × u_j|`, with the length of the
common edge measured as the diameter of `F_i ∩ F_j` and `|u_i × u_j| = √(1 - ⟪u_i, u_j⟫²)`.  The
diagonal is determined by `∑_j M i j u_j = 0` (translation invariance of the volume). -/
def polytopeHessian (S : Finset ι) (u : ι → Space3) (h : ι → ℝ) (i j : ι) : ℝ :=
  if i = j then
    ∑ k ∈ S.erase i, Metric.diam (polyFacet S u h i ∩ polyFacet S u h k) /
      √(1 - inner ℝ (u i) (u k) ^ 2) * inner ℝ (u i) (u k)
  else
    -(Metric.diam (polyFacet S u h i ∩ polyFacet S u h j) / √(1 - inner ℝ (u i) (u j) ^ 2))

/-- Minus the volume Hessian is symmetric. -/
lemma polytopeHessian_symm (S : Finset ι) (u : ι → Space3) (h : ι → ℝ) (i j : ι) :
    polytopeHessian S u h i j = polytopeHessian S u h j i := by
  unfold polytopeHessian
  by_cases hij : i = j
  · subst hij; rfl
  · rw [if_neg hij, if_neg (Ne.symm hij), Set.inter_comm, real_inner_comm]

/-- The off-diagonal entries of minus the volume Hessian are nonpositive. -/
lemma polytopeHessian_offdiag_nonpos (S : Finset ι) (u : ι → Space3) (h : ι → ℝ) {i j : ι}
    (hij : i ≠ j) : polytopeHessian S u h i j ≤ 0 := by
  unfold polytopeHessian
  rw [if_neg hij, neg_nonpos]
  exact div_nonneg Metric.diam_nonneg (Real.sqrt_nonneg _)

end Erdos99
end

end Polytope

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `PolytopeConnected`
-/

section PolytopeConnected

/-!
# The facet graph of a polytope is connected

For a bounded polytope `polyK S u h` in `ℝ³` with unit normals all of whose facets are present,
every proper nonempty set `U` of facets shares an edge of positive length with its complement:
some entry `polytopeHessian S u h i j` with `i ∈ U`, `j ∉ U` is negative
(`polytopeHessian_connected_aux`).

Proof.  If not, every facet in `U` meets every facet outside `U` in at most one point, so these
intersections form a finite set `P`.  Choose an interior point `c`, a relative-interior point `p`
of a facet in `U`, and a relative-interior point `q` of a facet outside `U` in general position
(`exists_generic_facet_point`).  Radially projecting the segment `[p, q]` from `c` onto the
boundary (`radP`, built from the gauge `gaugeP`) gives a path from `p` to `q` on the boundary
avoiding `P`.  The parameters at which the path lies on a facet of `U`, resp. outside `U`, are two
closed sets covering `[0, 1]`; by connectedness they meet, at a point of `P`, a contradiction.
-/

open scoped BigOperators
open Filter Topology

@[expose] public noncomputable section

open Classical

namespace Erdos99

variable {ι : Type*}

/-! ## Elementary facts -/

/-- In `ℝ³` any two vectors have a common nonzero orthogonal vector. -/
lemma exists_orth_pair (a b : Space3) :
    ∃ n : Space3, n ≠ 0 ∧ inner ℝ n a = 0 ∧ inner ℝ n b = 0 := by
  let f : Space3 →ₗ[ℝ] (Fin 2 → ℝ) :=
    LinearMap.pi (fun i : Fin 2 => (innerₛₗ ℝ (![a, b] i) : Space3 →ₗ[ℝ] ℝ))
  have hlt : Module.finrank ℝ (Fin 2 → ℝ) < Module.finrank ℝ Space3 := by simp
  have hker := LinearMap.ker_ne_bot_of_finrank_lt hlt (f := f)
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have h0 := congrFun (LinearMap.mem_ker.1 hn) 0
  have h1 := congrFun (LinearMap.mem_ker.1 hn) 1
  simp [f] at h0 h1
  exact ⟨n, hn0, by rw [real_inner_comm]; exact h0, by rw [real_inner_comm]; exact h1⟩

lemma polyK_isClosed (S : Finset ι) (u : ι → Space3) (h : ι → ℝ) : IsClosed (polyK S u h) := by
  have : polyK S u h = ⋂ k ∈ S, {x | inner ℝ (u k) x ≤ h k} := by
    ext x; simp [polyK]
  rw [this]
  exact isClosed_biInter fun k _ => isClosed_le (by fun_prop) continuous_const

lemma polyFacet_isClosed (S : Finset ι) (u : ι → Space3) (h : ι → ℝ) (i : ι) :
    IsClosed (polyFacet S u h i) :=
  (polyK_isClosed S u h).inter (isClosed_eq (by fun_prop) continuous_const)

/-- `a + b t ≠ 0` for all small nonzero `t`, unless `a = b = 0`. -/
lemma eventually_affine_ne_zero (a b : ℝ) (hab : a ≠ 0 ∨ b ≠ 0) :
    ∀ᶠ t in 𝓝[≠] (0 : ℝ), a + b * t ≠ 0 := by
  rcases hab with ha | hb
  · have : ∀ᶠ t in 𝓝 (0 : ℝ), a + b * t ≠ 0 := by
      have hc : Continuous fun t : ℝ => a + b * t := by fun_prop
      have := hc.continuousAt (x := 0) |>.eventually_ne (by simpa using ha)
      exact this
    exact nhdsWithin_le_nhds this
  · by_cases ha : a = 0
    · filter_upwards [self_mem_nhdsWithin] with t ht
      rw [ha, zero_add]
      exact mul_ne_zero hb ht
    · have : ∀ᶠ t in 𝓝 (0 : ℝ), a + b * t ≠ 0 := by
        have hc : Continuous fun t : ℝ => a + b * t := by fun_prop
        exact hc.continuousAt (x := 0) |>.eventually_ne (by simpa using ha)
      exact nhdsWithin_le_nhds this

/-- An interior point of a polytope with at least two facets present. -/
lemma exists_interior_point {S : Finset ι} {u : ι → Space3} {h : ι → ℝ}
    (hfac : FacetsPresent S u h) {a b : ι} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
    ∃ c : Space3, ∀ k ∈ S, inner ℝ (u k) c < h k := by
  choose! p hp1 hp2 using hfac
  refine ⟨(S.card : ℝ)⁻¹ • ∑ i ∈ S, p i, fun k hk => ?_⟩
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.2 ⟨a, ha⟩
  rw [inner_smul_right, inner_sum]
  have hlt : ∑ i ∈ S, inner ℝ (u k) (p i) < ∑ i ∈ S, h k := by
    apply Finset.sum_lt_sum
    · intro i hi
      by_cases hik : k = i
      · subst hik; rw [hp1 k hi]
      · exact (hp2 i hi k hk hik).le
    · obtain ⟨i, hi, hik⟩ : ∃ i ∈ S, k ≠ i := by
        by_cases hka : k = a
        · exact ⟨b, hb, by rw [hka]; exact hab⟩
        · exact ⟨a, ha, hka⟩
      exact ⟨i, hi, hp2 i hi k hk hik⟩
  rw [Finset.sum_const, nsmul_eq_mul] at hlt
  calc (S.card : ℝ)⁻¹ * ∑ i ∈ S, inner ℝ (u k) (p i) < (S.card : ℝ)⁻¹ * (S.card * h k) :=
        mul_lt_mul_of_pos_left hlt (inv_pos.2 hcard)
    _ = h k := by field_simp

/-! ## The gauge and the radial projection onto the boundary -/

section Gauge

variable {S : Finset ι} {u : ι → Space3} {h : ι → ℝ}

/-- The gauge of the polytope with respect to the interior point `c`:
`max_k ⟪u k, d⟫ / (h k - ⟪u k, c⟫)`. -/
def gaugeP (S : Finset ι) (hS : S.Nonempty) (u : ι → Space3) (h : ι → ℝ) (c d : Space3) : ℝ :=
  S.sup' hS (fun k => inner ℝ (u k) d / (h k - inner ℝ (u k) c))

/-- The radial projection of the direction `d` from `c` onto the boundary. -/
def radP (S : Finset ι) (hS : S.Nonempty) (u : ι → Space3) (h : ι → ℝ) (c d : Space3) :
    Space3 :=
  c + (gaugeP S hS u h c d)⁻¹ • d

variable (hS : S.Nonempty) {c : Space3} (hc : ∀ k ∈ S, inner ℝ (u k) c < h k)
include hc

omit hc in
lemma gaugeP_continuous : Continuous (gaugeP S hS u h c) :=
  Continuous.finset_sup'_apply hS fun k _ => by fun_prop

lemma inner_le_gaugeP {k : ι} (hk : k ∈ S) (d : Space3) :
    inner ℝ (u k) d ≤ gaugeP S hS u h c d * (h k - inner ℝ (u k) c) := by
  have h1 := Finset.le_sup' (fun k => inner ℝ (u k) d / (h k - inner ℝ (u k) c)) hk
  rw [← div_le_iff₀ (sub_pos.2 (hc k hk))]
  exact h1

lemma gaugeP_pos (hbdd : Bornology.IsBounded (polyK S u h)) {d : Space3} (hd : d ≠ 0) :
    0 < gaugeP S hS u h c d := by
  by_contra hle
  push_neg at hle
  have hall : ∀ k ∈ S, inner ℝ (u k) d ≤ 0 := fun k hk => by
    have := inner_le_gaugeP hS hc hk d
    have := sub_pos.2 (hc k hk)
    nlinarith
  have hmem : ∀ s : ℝ, 0 ≤ s → c + s • d ∈ polyK S u h := fun s hs k hk => by
    rw [inner_add_right, inner_smul_right]
    nlinarith [hall k hk, hc k hk]
  obtain ⟨R, hR⟩ := hbdd.exists_norm_le
  have hdn : 0 < ‖d‖ := norm_pos_iff.2 hd
  have hR0 : ‖c‖ ≤ R := by simpa using hR _ (hmem 0 le_rfl)
  set s := (R + ‖c‖ + 1) / ‖d‖ with hsdef
  have hs0 : 0 ≤ s := div_nonneg (by linarith [norm_nonneg c]) hdn.le
  have h1 := hR _ (hmem s hs0)
  have h2 : ‖s • d‖ ≤ ‖c + s • d‖ + ‖c‖ := by
    calc ‖s • d‖ = ‖(c + s • d) - c‖ := by rw [add_sub_cancel_left]
      _ ≤ _ := norm_sub_le _ _
  rw [norm_smul, Real.norm_of_nonneg hs0, hsdef, div_mul_cancel₀ _ hdn.ne'] at h2
  linarith

lemma radP_mem_polyK (hbdd : Bornology.IsBounded (polyK S u h)) {d : Space3} (hd : d ≠ 0) :
    radP S hS u h c d ∈ polyK S u h := fun k hk => by
  have hg := gaugeP_pos hS hc hbdd hd
  have h1 := inner_le_gaugeP hS hc hk d
  rw [radP, inner_add_right, inner_smul_right]
  have : (gaugeP S hS u h c d)⁻¹ * inner ℝ (u k) d ≤ h k - inner ℝ (u k) c := by
    rw [inv_mul_le_iff₀ hg]; exact h1
  linarith

lemma radP_mem_facet (hbdd : Bornology.IsBounded (polyK S u h)) {d : Space3} (hd : d ≠ 0) :
    ∃ k ∈ S, radP S hS u h c d ∈ polyFacet S u h k := by
  obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_sup' hS
    (fun k => inner ℝ (u k) d / (h k - inner ℝ (u k) c))
  refine ⟨k, hk, radP_mem_polyK hS hc hbdd hd, ?_⟩
  have hg := gaugeP_pos hS hc hbdd hd
  have hδ := sub_pos.2 (hc k hk)
  have hgk : gaugeP S hS u h c d = inner ℝ (u k) d / (h k - inner ℝ (u k) c) := hkeq
  rw [radP, inner_add_right, inner_smul_right, hgk]
  have hne : inner ℝ (u k) d ≠ 0 := by
    intro h0; rw [hgk, h0, zero_div] at hg; exact lt_irrefl _ hg
  field_simp
  ring

lemma gaugeP_of_mem_facet {i : ι} (hi : i ∈ S) {x : Space3} (hx : x ∈ polyFacet S u h i) :
    gaugeP S hS u h c (x - c) = 1 := by
  apply le_antisymm
  · refine Finset.sup'_le hS _ fun k hk => ?_
    rw [div_le_one (sub_pos.2 (hc k hk)), inner_sub_right]
    linarith [hx.1 k hk]
  · have hδ := sub_pos.2 (hc i hi)
    unfold gaugeP
    refine le_trans ?_ (Finset.le_sup' _ hi)
    simp only [inner_sub_right, hx.2]
    rw [div_self hδ.ne']

lemma radP_of_mem_facet {i : ι} (hi : i ∈ S) {x : Space3} (hx : x ∈ polyFacet S u h i) :
    radP S hS u h c (x - c) = x := by
  rw [radP, gaugeP_of_mem_facet hS hc hi hx, inv_one, one_smul, add_sub_cancel]

end Gauge

/-! ## A relative-interior point in general position -/

/-- On a facet `b` (unit normal), there is a relative-interior point `q` with
`⟪n, q - c⟫ ≠ 0` for each of finitely many nonzero vectors `n`, provided `c` lies strictly on the
inner side of the facet plane. -/
lemma exists_generic_facet_point {S : Finset ι} {u : ι → Space3} {h : ι → ℝ} {b : ι}
    (hub : ‖u b‖ = 1) {q₀ : Space3} (hq₀ : inner ℝ (u b) q₀ = h b)
    (hq₀' : ∀ k ∈ S, k ≠ b → inner ℝ (u k) q₀ < h k) {c : Space3} (hcb : inner ℝ (u b) c < h b)
    (N : Finset Space3) (hN : ∀ n ∈ N, n ≠ 0) :
    ∃ q : Space3, inner ℝ (u b) q = h b ∧ (∀ k ∈ S, k ≠ b → inner ℝ (u k) q < h k) ∧
      ∀ n ∈ N, inner ℝ n (q - c) ≠ 0 := by
  have hub2 : inner ℝ (u b) (u b) = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, hub]; norm_num
  -- projection onto the facet plane direction
  set Pr : Space3 → Space3 := fun v => v - inner ℝ (u b) v • u b with hPr
  have hPr_perp : ∀ v, inner ℝ (u b) (Pr v) = 0 := fun v => by
    simp only [Pr, inner_sub_right, inner_smul_right, hub2, mul_one, sub_self]
  have hPr_symm : ∀ n v, inner ℝ n (Pr v) = inner ℝ (Pr n) v := fun n v => by
    simp only [Pr, inner_sub_right, inner_sub_left, inner_smul_right, inner_smul_left,
      RCLike.conj_to_real, real_inner_comm (u b) n, real_inner_comm v (u b)]
    ring
  set E : Fin 3 → Space3 := fun k => EuclideanSpace.single k 1
  set α : Space3 → ℝ := fun n => inner ℝ n (Pr (E 0))
  set β : Space3 → ℝ := fun n => inner ℝ n (Pr (E 1))
  set γ : Space3 → ℝ := fun n => inner ℝ n (Pr (E 2))
  have hcoef : ∀ n, Pr n ≠ 0 → α n ≠ 0 ∨ β n ≠ 0 ∨ γ n ≠ 0 := by
    intro n hn
    by_contra hcon
    push_neg at hcon
    apply hn
    ext k
    have hk : inner ℝ (Pr n) (E k) = 0 := by
      fin_cases k
      · rw [← hPr_symm]; exact hcon.1
      · rw [← hPr_symm]; exact hcon.2.1
      · rw [← hPr_symm]; exact hcon.2.2
    simpa [E, EuclideanSpace.inner_single_right] using hk
  -- the direction `w = Pr E₀ + s Pr E₁ + t Pr E₂`
  have hs : ∀ᶠ s in 𝓝[≠] (0 : ℝ), ∀ n ∈ N, (α n ≠ 0 ∨ β n ≠ 0) → α n + β n * s ≠ 0 := by
    rw [eventually_all_finset]
    intro n _
    by_cases hab : α n ≠ 0 ∨ β n ≠ 0
    · filter_upwards [eventually_affine_ne_zero _ _ hab] with s hs _ using hs
    · exact Eventually.of_forall fun s h => absurd h hab
  obtain ⟨s, hs⟩ := hs.exists
  have ht : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∀ n ∈ N, Pr n ≠ 0 → (α n + β n * s) + γ n * t ≠ 0 := by
    rw [eventually_all_finset]
    intro n hn
    by_cases hP : Pr n ≠ 0
    · have hab : α n + β n * s ≠ 0 ∨ γ n ≠ 0 := by
        by_cases h1 : α n + β n * s ≠ 0
        · exact Or.inl h1
        · right
          rcases hcoef n hP with h2 | h2 | h2
          · exact absurd (hs n hn (Or.inl h2)) h1
          · exact absurd (hs n hn (Or.inr h2)) h1
          · exact h2
      filter_upwards [eventually_affine_ne_zero _ _ hab] with t ht _ using ht
    · exact Eventually.of_forall fun t h => absurd h hP
  obtain ⟨t, ht⟩ := ht.exists
  set w : Space3 := Pr (E 0) + s • Pr (E 1) + t • Pr (E 2) with hw
  have hw_perp : inner ℝ (u b) w = 0 := by
    simp only [w, inner_add_right, inner_smul_right, hPr_perp, mul_zero, add_zero]
  have hw_n : ∀ n ∈ N, Pr n ≠ 0 → inner ℝ n w ≠ 0 := by
    intro n hn hP
    have := ht n hn hP
    simp only [w, inner_add_right, inner_smul_right]
    simp only [α, β, γ] at this
    rw [mul_comm s, mul_comm t]
    exact this
  -- choose the step `ε`
  have hε : ∀ᶠ ε in 𝓝[≠] (0 : ℝ),
      (∀ n ∈ N, Pr n ≠ 0 → inner ℝ n (q₀ - c) + inner ℝ n w * ε ≠ 0) ∧
      (∀ k ∈ S, k ≠ b → inner ℝ (u k) q₀ + ε * inner ℝ (u k) w < h k) := by
    refine Eventually.and ?_ ?_
    · rw [eventually_all_finset]
      intro n hn
      by_cases hP : Pr n ≠ 0
      · filter_upwards [eventually_affine_ne_zero _ _ (Or.inr (hw_n n hn hP))] with ε hε _
          using hε
      · exact Eventually.of_forall fun ε h => absurd h hP
    · rw [eventually_all_finset]
      intro k hk
      apply nhdsWithin_le_nhds
      by_cases hkb : k = b
      · exact Eventually.of_forall fun ε h => absurd hkb h
      · have hc : Continuous fun ε : ℝ => inner ℝ (u k) q₀ + ε * inner ℝ (u k) w := by fun_prop
        have := hc.continuousAt (x := 0) |>.eventually (gt_mem_nhds (b := h k) (by
          simpa using hq₀' k hk hkb))
        filter_upwards [this] with ε hε _ using hε
  obtain ⟨ε, hε1, hε2⟩ := hε.exists
  refine ⟨q₀ + ε • w, ?_, ?_, ?_⟩
  · rw [inner_add_right, inner_smul_right, hw_perp, mul_zero, add_zero, hq₀]
  · intro k hk hkb
    rw [inner_add_right, inner_smul_right]
    exact hε2 k hk hkb
  · intro n hn
    by_cases hP : Pr n ≠ 0
    · have := hε1 n hn hP
      rw [show q₀ + ε • w - c = (q₀ - c) + ε • w by abel, inner_add_right, inner_smul_right,
        mul_comm]
      exact this
    · push_neg at hP
      -- `n` is a multiple of `u b`
      have hn' : n = inner ℝ (u b) n • u b := by
        have : n - inner ℝ (u b) n • u b = 0 := hP
        exact sub_eq_zero.1 this
      have hcoef0 : inner ℝ (u b) n ≠ 0 := by
        intro h0
        rw [h0, zero_smul] at hn'
        exact hN n hn hn'
      rw [hn', inner_smul_left, RCLike.conj_to_real, inner_sub_right, inner_add_right,
        inner_smul_right, hw_perp, mul_zero, add_zero, hq₀]
      exact mul_ne_zero hcoef0 (sub_pos.2 hcb).ne'

/-! ## Connectivity -/

/-- **The facet graph of a polytope is connected.**  For a bounded polytope with unit normals all
of whose facets are present, every proper nonempty set `U` of facets contains a facet `i` sharing
an edge of positive length with a facet `j ∉ U`, i.e. `polytopeHessian S u h i j < 0`. -/
theorem polytopeHessian_connected_aux {S : Finset ι} {u : ι → Space3} {h : ι → ℝ}
    (hu : ∀ i ∈ S, ‖u i‖ = 1) (hbdd : Bornology.IsBounded (polyK S u h))
    (hfac : FacetsPresent S u h) :
    ∀ U ⊆ S, U.Nonempty → U ≠ S → ∃ i ∈ U, ∃ j ∈ S, j ∉ U ∧ polytopeHessian S u h i j < 0 := by
  intro U hUS hU hU'
  by_contra hcon
  push_neg at hcon
  obtain ⟨a, haU⟩ := hU
  have haS := hUS haU
  obtain ⟨b, hbS, hbU⟩ : ∃ b ∈ S, b ∉ U := by
    by_contra hc
    push_neg at hc
    exact hU' (Finset.Subset.antisymm hUS hc)
  have hab : a ≠ b := fun e => hbU (e ▸ haU)
  have hSne : S.Nonempty := ⟨a, haS⟩
  obtain ⟨c, hc⟩ := exists_interior_point hfac haS hbS hab
  have hfac' := hfac
  choose! pt hpt1 hpt2 using hfac'
  have hpt_facet : ∀ i ∈ S, pt i ∈ polyFacet S u h i := fun i hi =>
    ⟨fun k hk => by
      by_cases hki : k = i
      · subst hki; exact (hpt1 k hi).le
      · exact (hpt2 i hi k hk hki).le, hpt1 i hi⟩
  -- facets in `U` meet facets outside `U` in at most one point
  have hsub : ∀ i ∈ U, ∀ j ∈ S, j ∉ U →
      (polyFacet S u h i ∩ polyFacet S u h j).Subsingleton := by
    intro i hi j hj hjU
    have hiS := hUS hi
    have hij : i ≠ j := fun e => hjU (e ▸ hi)
    have heq : polytopeHessian S u h i j = 0 :=
      le_antisymm (polytopeHessian_offdiag_nonpos S u h hij) (hcon i hi j hj hjU)
    unfold polytopeHessian at heq
    rw [if_neg hij, neg_eq_zero, div_eq_zero_iff] at heq
    rcases heq with hd | hs
    · intro x hx y hy
      have hbdd' : Bornology.IsBounded (polyFacet S u h i ∩ polyFacet S u h j) :=
        hbdd.subset fun z hz => hz.1.1
      have := Metric.dist_le_diam_of_mem hbdd' hx hy
      rw [hd] at this
      exact dist_le_zero.1 this
    · intro x hx y _
      exfalso
      rw [Real.sqrt_eq_zero'] at hs
      set cc := inner ℝ (u i) (u j) with hcc
      have hnorm : ‖u j - cc • u i‖ ^ 2 = 1 - cc ^ 2 := by
        rw [@norm_sub_sq_real, norm_smul, inner_smul_right, hu j hj, hu i hiS, real_inner_comm,
          ← hcc, Real.norm_eq_abs, mul_one, sq_abs]
        ring
      have hzero : u j - cc • u i = 0 := by
        have : ‖u j - cc • u i‖ ^ 2 ≤ 0 := by rw [hnorm]; linarith
        exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1
          (le_antisymm this (sq_nonneg _)))
      have hujc : u j = cc • u i := sub_eq_zero.1 hzero
      have e1 : h j = cc * h i := by
        rw [← hx.2.2, hujc, inner_smul_left, RCLike.conj_to_real, hx.1.2]
      have e2 := hpt2 i hiS j hj (Ne.symm hij)
      rw [hujc, inner_smul_left, RCLike.conj_to_real, hpt1 i hiS] at e2
      linarith
  -- the finite set of such intersection points
  set P : Set Space3 := ⋃ i ∈ U, ⋃ j ∈ S \ U, (polyFacet S u h i ∩ polyFacet S u h j) with hPdef
  have hPfin : P.Finite := by
    refine Set.Finite.biUnion (Finset.finite_toSet U) fun i hi => ?_
    refine Set.Finite.biUnion (Finset.finite_toSet _) fun j hj => ?_
    have hj' := Finset.mem_sdiff.1 hj
    exact (hsub i hi j hj'.1 hj'.2).finite
  -- the base point and the normals
  set p := pt a with hp
  have hpF : p ∈ polyFacet S u h a := hpt_facet a haS
  have hpc : p - c ≠ 0 := by
    intro h0
    have : p = c := sub_eq_zero.1 h0
    have := hc a haS
    rw [← ‹p = c›, hp, hpt1 a haS] at this
    exact lt_irrefl _ this
  set nrm : Space3 → Space3 := fun x => Classical.choose (exists_orth_pair (p - c) (x - c))
  have hnrm : ∀ x, nrm x ≠ 0 ∧ inner ℝ (nrm x) (p - c) = 0 ∧ inner ℝ (nrm x) (x - c) = 0 :=
    fun x => Classical.choose_spec (exists_orth_pair (p - c) (x - c))
  set N : Finset Space3 := insert (nrm p) (hPfin.toFinset.image nrm)
  have hN : ∀ n ∈ N, n ≠ 0 := by
    intro n hn
    rcases Finset.mem_insert.1 hn with rfl | hn
    · exact (hnrm p).1
    · obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 hn
      exact (hnrm x).1
  obtain ⟨q, hqb, hqk, hqN⟩ := exists_generic_facet_point (S := S) (hu b hbS) (hpt1 b hbS)
    (hpt2 b hbS) (hc b hbS) N hN
  have hqF : q ∈ polyFacet S u h b :=
    ⟨fun k hk => by
      by_cases hkb : k = b
      · subst hkb; exact hqb.le
      · exact (hqk k hk hkb).le, hqb⟩
  have hq_star : inner ℝ (nrm p) (q - c) ≠ 0 := hqN _ (Finset.mem_insert_self _ _)
  have hq_P : ∀ x ∈ P, inner ℝ (nrm x) (q - c) ≠ 0 := fun x hx =>
    hqN _ (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨x, hPfin.mem_toFinset.2 hx, rfl⟩))
  -- the path
  set d : ℝ → Space3 := fun t => (1 - t) • (p - c) + t • (q - c) with hd
  have hd0 : d 0 = p - c := by simp [d]
  have hd1 : d 1 = q - c := by simp [d]
  have hdne : ∀ t ∈ Set.Icc (0 : ℝ) 1, d t ≠ 0 := by
    intro t ht h0
    rcases eq_or_lt_of_le ht.1 with h | h
    · subst h; rw [hd0] at h0; exact hpc h0
    · have : inner ℝ (nrm p) (d t) = t * inner ℝ (nrm p) (q - c) := by
        simp only [d, inner_add_right, inner_smul_right, (hnrm p).2.1, mul_zero, zero_add]
      rw [h0, inner_zero_right] at this
      exact mul_ne_zero h.ne' hq_star this.symm
  set γ : ℝ → Space3 := fun t => radP S hSne u h c (d t) with hγ
  have hγ0 : γ 0 = p := by
    simp only [γ, hd0]; exact radP_of_mem_facet hSne hc haS hpF
  have hγ1 : γ 1 = q := by
    simp only [γ, hd1]; exact radP_of_mem_facet hSne hc hbS hqF
  have hγcont : ContinuousOn γ (Set.Icc 0 1) := by
    have hdc : Continuous d := by fun_prop
    have hgc : ContinuousOn (fun t => gaugeP S hSne u h c (d t)) (Set.Icc 0 1) :=
      ((gaugeP_continuous hSne).comp hdc).continuousOn
    have hginv : ContinuousOn (fun t => (gaugeP S hSne u h c (d t))⁻¹) (Set.Icc 0 1) :=
      hgc.inv₀ fun t ht => (gaugeP_pos hSne hc hbdd (hdne t ht)).ne'
    exact continuousOn_const.add (hginv.smul hdc.continuousOn)
  -- the path avoids `P`
  have havoid : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∉ P := by
    intro t ht hP
    rcases eq_or_lt_of_le ht.1 with h0 | hpos
    · subst h0
      rw [hγ0] at hP
      simp only [P, Set.mem_iUnion, Finset.mem_sdiff] at hP
      obtain ⟨i, hi, j, ⟨hjS, hjU⟩, hpi, hpj⟩ := hP
      have hij : i ≠ j := fun e => hjU (e ▸ hi)
      by_cases hia : i = a
      · subst hia
        have := hpt2 i haS j hjS (Ne.symm hij)
        rw [hpj.2] at this
        exact lt_irrefl _ this
      · have := hpt2 a haS i (hUS hi) hia
        rw [hpi.2] at this
        exact lt_irrefl _ this
    · set y := γ t
      have hg := gaugeP_pos hSne hc hbdd (hdne t ht)
      have hy : d t = gaugeP S hSne u h c (d t) • (y - c) := by
        simp only [y, γ, radP, add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hg.ne', one_smul]
      have : inner ℝ (nrm y) (d t) = t * inner ℝ (nrm y) (q - c) := by
        simp only [d, inner_add_right, inner_smul_right, (hnrm y).2.1, mul_zero, zero_add]
      rw [hy, inner_smul_right, (hnrm y).2.2, mul_zero] at this
      exact mul_ne_zero hpos.ne' (hq_P y hP) this.symm
  -- the two closed sets
  set A : Set Space3 := ⋃ i ∈ U, polyFacet S u h i
  set B : Set Space3 := ⋃ j ∈ S \ U, polyFacet S u h j
  have hA : IsClosed A := isClosed_biUnion_finset fun i _ => polyFacet_isClosed S u h i
  have hB : IsClosed B := isClosed_biUnion_finset fun j _ => polyFacet_isClosed S u h j
  have hT1 := hγcont.preimage_isClosed_of_isClosed isClosed_Icc hA
  have hT2 := hγcont.preimage_isClosed_of_isClosed isClosed_Icc hB
  have hcover : Set.Icc (0 : ℝ) 1 ⊆ (Set.Icc 0 1 ∩ γ ⁻¹' A) ∪ (Set.Icc 0 1 ∩ γ ⁻¹' B) := by
    intro t ht
    obtain ⟨k, hk, hkF⟩ := radP_mem_facet hSne hc hbdd (hdne t ht)
    by_cases hkU : k ∈ U
    · exact Or.inl ⟨ht, Set.mem_biUnion hkU hkF⟩
    · exact Or.inr ⟨ht, Set.mem_biUnion (Finset.mem_sdiff.2 ⟨hk, hkU⟩) hkF⟩
  have h0 : (Set.Icc (0 : ℝ) 1 ∩ (Set.Icc 0 1 ∩ γ ⁻¹' A)).Nonempty :=
    ⟨0, ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, by
      simp only [Set.mem_preimage, hγ0]; exact Set.mem_biUnion haU hpF⟩
  have h1 : (Set.Icc (0 : ℝ) 1 ∩ (Set.Icc 0 1 ∩ γ ⁻¹' B)).Nonempty :=
    ⟨1, ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, by
      simp only [Set.mem_preimage, hγ1]
      exact Set.mem_biUnion (Finset.mem_sdiff.2 ⟨hbS, hbU⟩) hqF⟩
  obtain ⟨t, ht, ⟨-, htA⟩, ⟨-, htB⟩⟩ :=
    isPreconnected_closed_iff.1 isPreconnected_Icc _ _ hT1 hT2 hcover h0 h1
  apply havoid t ht
  simp only [Set.mem_preimage, A, B, Set.mem_iUnion] at htA htB
  obtain ⟨i, hi, hti⟩ := htA
  obtain ⟨j, hj, htj⟩ := htB
  exact Set.mem_biUnion hi (Set.mem_biUnion hj ⟨hti, htj⟩)

end Erdos99
end

end PolytopeConnected

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `MixedVolume`
-/

section MixedVolume

/-!
# Symmetry of mixed volumes for triangulated facet links

Fix unit vectors `u i ∈ ℝ³` (`i ∈ S`).  For each `i`, a *link* is a cyclic list of neighbours
`nbr i 0, …, nbr i (k i - 1)` together with gaps `θ i m`; for a polytope with facet normals `u`,
these are the neighbouring facets of facet `i` in cyclic order (after triangulating non-simple
vertices by zero-length edges) and the exterior angles of the facet polygon.  The support numbers
induced in the plane of facet `i` by a vector `f` of support numbers are
`linkSupport u nbr i f m = (f j - ⟪u i, u j⟫ f i) / |u i × u j|` with `j = nbr i m`.

The main result, `linkMixed_symm`, is the symmetry of the mixed volume: the trilinear form

  `N(a, b, c) = ∑ᵢ aᵢ · polyBilin(θ i, G i b, G i c)`

is symmetric in `a` and `b`, as soon as

* each gap `θ i m` is the angle at `u i` of the spherical triangle `(u i, u j, u j')` formed with
  two consecutive neighbours (`sin θ · |u i × u j| |u i × u j'| = det(u i, u j, u j')` and
  `cos θ · |u i × u j| |u i × u j'| = ⟪u j, u j'⟫ - ⟪u i, u j⟫ ⟪u i, u j'⟫`), and
* the flags `(i, nbr i m, nbr i (m + 1))` are exactly the three rotations of a family `T` of
  triangles (each triangle of the triangulated normal fan appears once in the link of each of its
  vertices).

The proof is local: the contribution of one triangle is an explicit trilinear form in the values
at its three vertices (`cornerTerm`), and the sum of its three rotations is symmetric
(`cornerTerm_cyc_symm`, a polynomial identity).  This is the "volume of the corner region" of the
triangle, whose derivative in the support number of a face is the area of that face.

As a consequence (`facetForms_sym_of_row`), the row identity for minus a volume Hessian implies the
identity `-fᵀ M f = ∑ᵢ hᵢ qᵢ(G i f)` needed for Hilbert's argument.
-/

open scoped BigOperators Real

@[expose] public noncomputable section

open Classical Real Finset

namespace Erdos99

variable {ι : Type*}

/-- The determinant `det(x, y, z) = ⟪x, y × z⟫` of three vectors of `ℝ³`. -/
def vol3 (x y z : Space3) : ℝ :=
  x 0 * (y 1 * z 2 - y 2 * z 1) - x 1 * (y 0 * z 2 - y 2 * z 0) + x 2 * (y 0 * z 1 - y 1 * z 0)

lemma vol3_cyc (x y z : Space3) : vol3 y z x = vol3 x y z := by
  unfold vol3; ring

/-- The support numbers induced in the plane of facet `i` by the support numbers `f`:
`(f j - ⟪u i, u j⟫ f i) / |u i × u j|` for the `m`-th neighbour `j = nbr i m`. -/
def linkSupport (u : ι → Space3) (nbr : ι → ℕ → ι) (i : ι) (f : ι → ℝ) (m : ℕ) : ℝ :=
  (f (nbr i m) - inner ℝ (u i) (u (nbr i m)) * f i) / √(1 - inner ℝ (u i) (u (nbr i m)) ^ 2)

/-- The (cleared) contribution of the corner of a triangle at its vertex `i`, with neighbours
`j, k` and `cij = ⟪u i, u j⟫`, `cik = ⟪u i, u k⟫`, `cjk = ⟪u j, u k⟫`. -/
def cornerTerm (cij cik cjk ai bi bj bk ci cj ck : ℝ) : ℝ :=
  ai * ((bj - cij * bi) * (ck - cik * ci) + (cj - cij * ci) * (bk - cik * bi) -
    (cjk - cij * cik) * ((bj - cij * bi) * (cj - cij * ci) / (1 - cij ^ 2) +
      (bk - cik * bi) * (ck - cik * ci) / (1 - cik ^ 2)))

/-- **Local symmetry of the mixed volume.**  The sum of the three rotations of `cornerTerm` over
a triangle is symmetric in the first two arguments `a, b`. -/
lemma cornerTerm_cyc_symm (c12 c13 c23 a1 a2 a3 b1 b2 b3 x1 x2 x3 : ℝ)
    (h12 : 1 - c12 ^ 2 ≠ 0) (h13 : 1 - c13 ^ 2 ≠ 0) (h23 : 1 - c23 ^ 2 ≠ 0) :
    cornerTerm c12 c13 c23 a1 b1 b2 b3 x1 x2 x3 + cornerTerm c23 c12 c13 a2 b2 b3 b1 x2 x3 x1 +
        cornerTerm c13 c23 c12 a3 b3 b1 b2 x3 x1 x2 =
      cornerTerm c12 c13 c23 b1 a1 a2 a3 x1 x2 x3 + cornerTerm c23 c12 c13 b2 a2 a3 a1 x2 x3 x1 +
        cornerTerm c13 c23 c12 b3 a3 a1 a2 x3 x1 x2 := by
  unfold cornerTerm
  field_simp
  ring

/-- One term of `polyBilin` for induced support numbers, in cleared form. -/
lemma edgeBilin_link {θ cij cik cjk sij sik V bi bj bk ci cj ck : ℝ}
    (hsij : sij ^ 2 = 1 - cij ^ 2) (hsik : sik ^ 2 = 1 - cik ^ 2)
    (hsij0 : sij ≠ 0) (hsik0 : sik ≠ 0) (hsin0 : sin θ ≠ 0)
    (hsin : sin θ * (sij * sik) = V) (hcos : cos θ * (sij * sik) = cjk - cij * cik) :
    edgeBilin θ ((bj - cij * bi) / sij) ((bk - cik * bi) / sik) ((cj - cij * ci) / sij)
        ((ck - cik * ci) / sik) =
      cornerTerm cij cik cjk 1 bi bj bk ci cj ck / V := by
  have hV : V ≠ 0 := by rw [← hsin]; exact mul_ne_zero hsin0 (mul_ne_zero hsij0 hsik0)
  have h1 : 1 - cij ^ 2 ≠ 0 := by rw [← hsij]; exact pow_ne_zero 2 hsij0
  have h2 : 1 - cik ^ 2 ≠ 0 := by rw [← hsik]; exact pow_ne_zero 2 hsik0
  have hcos' : cos θ = (cjk - cij * cik) / (sij * sik) := by
    rw [eq_div_iff (mul_ne_zero hsij0 hsik0)]; exact hcos
  have hsin' : sin θ = V / (sij * sik) := by
    rw [eq_div_iff (mul_ne_zero hsij0 hsik0)]; exact hsin
  unfold edgeBilin cornerTerm
  rw [hcos', hsin']
  rw [← hsij, ← hsik]
  field_simp

/-- **Triangulated link data** for unit vectors `u` on `S`: for each `i ∈ S`, `k i` neighbours
`nbr i m` with gaps `θ i m`.  Each gap is the angle at `u i` of the spherical triangle formed with
two consecutive neighbours, and the flags `(i, nbr i m, nbr i (m + 1))` are exactly the three
rotations of the triangles of `T` (the triangles of a triangulated normal fan). -/
structure LinkData (S : Finset ι) (u : ι → Space3) (k : ι → ℕ) (nbr : ι → ℕ → ι)
    (θ : ι → ℕ → ℝ) (T : Finset (ι × ι × ι)) : Prop where
  /-- consecutive neighbours are not parallel to `u i` -/
  nondeg : ∀ i ∈ S, ∀ m < k i, inner ℝ (u i) (u (nbr i m)) ^ 2 < 1
  /-- the gaps are not multiples of `π` -/
  sin_ne : ∀ i ∈ S, ∀ m < k i, sin (θ i m) ≠ 0
  /-- the sine of the gap -/
  sin_eq : ∀ i ∈ S, ∀ m < k i,
    sin (θ i m) * (√(1 - inner ℝ (u i) (u (nbr i m)) ^ 2) *
      √(1 - inner ℝ (u i) (u (nbr i ((m + 1) % k i))) ^ 2)) =
      vol3 (u i) (u (nbr i m)) (u (nbr i ((m + 1) % k i)))
  /-- the cosine of the gap -/
  cos_eq : ∀ i ∈ S, ∀ m < k i,
    cos (θ i m) * (√(1 - inner ℝ (u i) (u (nbr i m)) ^ 2) *
      √(1 - inner ℝ (u i) (u (nbr i ((m + 1) % k i))) ^ 2)) =
      inner ℝ (u (nbr i m)) (u (nbr i ((m + 1) % k i))) -
        inner ℝ (u i) (u (nbr i m)) * inner ℝ (u i) (u (nbr i ((m + 1) % k i)))
  /-- the triangles are nondegenerate -/
  tri_nondeg : ∀ t ∈ T, inner ℝ (u t.1) (u t.2.1) ^ 2 < 1 ∧ inner ℝ (u t.1) (u t.2.2) ^ 2 < 1 ∧
    inner ℝ (u t.2.1) (u t.2.2) ^ 2 < 1
  /-- the flags of the links are the rotations of the triangles -/
  flags : ∀ F : ι → ι → ι → ℝ,
    ∑ i ∈ S, ∑ m ∈ range (k i), F i (nbr i m) (nbr i ((m + 1) % k i)) =
      ∑ t ∈ T, (F t.1 t.2.1 t.2.2 + F t.2.1 t.2.2 t.1 + F t.2.2 t.1 t.2.1)

/-- The local trilinear form of a flag `(i, j, j')`. -/
def flagForm (u : ι → Space3) (a b c : ι → ℝ) (i j j' : ι) : ℝ :=
  cornerTerm (inner ℝ (u i) (u j)) (inner ℝ (u i) (u j')) (inner ℝ (u j) (u j'))
    (a i) (b i) (b j) (b j') (c i) (c j) (c j') / vol3 (u i) (u j) (u j')

/-- The mixed-volume form as a sum of flag forms. -/
lemma linkMixed_eq_flags {S : Finset ι} {u : ι → Space3} {k : ι → ℕ} {nbr : ι → ℕ → ι}
    {θ : ι → ℕ → ℝ} {T : Finset (ι × ι × ι)}
    (hL : LinkData S u k nbr θ T) (a b c : ι → ℝ) :
    ∑ i ∈ S, a i * polyBilin (k i) (θ i) (linkSupport u nbr i b) (linkSupport u nbr i c) =
      ∑ i ∈ S, ∑ m ∈ range (k i), flagForm u a b c i (nbr i m) (nbr i ((m + 1) % k i)) := by
  refine Finset.sum_congr rfl fun i hi => ?_
  unfold polyBilin
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' := Finset.mem_range.1 hm
  have hk : 0 < k i := by omega
  have hm1 : (m + 1) % k i < k i := Nat.mod_lt _ hk
  have hnd := hL.nondeg i hi m hm'
  have hnd' := hL.nondeg i hi _ hm1
  have hs : ∀ x : ℝ, x ^ 2 < 1 → √(1 - x ^ 2) ^ 2 = 1 - x ^ 2 ∧ √(1 - x ^ 2) ≠ 0 := fun x hx =>
    ⟨Real.sq_sqrt (by linarith), (Real.sqrt_pos.2 (by linarith)).ne'⟩
  obtain ⟨hs1, hs1'⟩ := hs _ hnd
  obtain ⟨hs2, hs2'⟩ := hs _ hnd'
  unfold linkSupport flagForm
  rw [edgeBilin_link hs1 hs2 hs1' hs2' (hL.sin_ne i hi m hm') (hL.sin_eq i hi m hm')
    (hL.cos_eq i hi m hm')]
  unfold cornerTerm
  ring

/-- **Symmetry of the mixed volume** for triangulated link data:
`∑ᵢ aᵢ B_i(b, c) = ∑ᵢ bᵢ B_i(a, c)`, where `B_i` is the polar area form of facet `i`
evaluated at the induced support numbers. -/
theorem linkMixed_symm {S : Finset ι} {u : ι → Space3} {k : ι → ℕ} {nbr : ι → ℕ → ι}
    {θ : ι → ℕ → ℝ} {T : Finset (ι × ι × ι)}
    (hL : LinkData S u k nbr θ T) (a b c : ι → ℝ) :
    ∑ i ∈ S, a i * polyBilin (k i) (θ i) (linkSupport u nbr i b) (linkSupport u nbr i c) =
      ∑ i ∈ S, b i * polyBilin (k i) (θ i) (linkSupport u nbr i a) (linkSupport u nbr i c) := by
  rw [linkMixed_eq_flags hL, linkMixed_eq_flags hL, hL.flags, hL.flags]
  refine Finset.sum_congr rfl fun t ht => ?_
  obtain ⟨p, q, r⟩ := t
  obtain ⟨h1, h2, h3⟩ := hL.tri_nondeg _ ht
  simp only at h1 h2 h3 ⊢
  unfold flagForm
  have e1 : vol3 (u q) (u r) (u p) = vol3 (u p) (u q) (u r) := vol3_cyc _ _ _
  have e2 : vol3 (u r) (u p) (u q) = vol3 (u p) (u q) (u r) := by unfold vol3; ring
  rw [e1, e2]
  rw [real_inner_comm (u p) (u q), real_inner_comm (u p) (u r), real_inner_comm (u q) (u r)]
  rw [← add_div, ← add_div, ← add_div, ← add_div]
  congr 1
  exact cornerTerm_cyc_symm _ _ _ _ _ _ _ _ _ _ _ _ (by linarith) (by linarith) (by linarith)

/-- **The mixed-volume identity of the facet decomposition**, derived from the row identity: if
each row of `-M` is the polar area form of facet `i` against `h`, then
`-fᵀ M f = ∑ᵢ hᵢ qᵢ(G i f)`. -/
theorem facetForms_sym_of_row {S : Finset ι} {u : ι → Space3} {k : ι → ℕ} {nbr : ι → ℕ → ι}
    {θ : ι → ℕ → ℝ} {T : Finset (ι × ι × ι)}
    (hL : LinkData S u k nbr θ T) (M : ι → ι → ℝ) (h : ι → ℝ)
    (hrow : ∀ f : ι → ℝ, ∀ i ∈ S, -∑ j ∈ S, M i j * f j =
      polyBilin (k i) (θ i) (linkSupport u nbr i h) (linkSupport u nbr i f))
    (f : ι → ℝ) :
    -quadForm S M f = ∑ i ∈ S, h i * polyForm (k i) (θ i) (linkSupport u nbr i f) := by
  have e1 : -quadForm S M f = ∑ i ∈ S, f i * (-∑ j ∈ S, M i j * f j) := by
    unfold quadForm
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_neg, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e1]
  rw [Finset.sum_congr rfl fun i hi => by rw [hrow f i hi], linkMixed_symm hL]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [polyBilin_self]

end Erdos99
end

end MixedVolume

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `FacetLinks`
-/

section FacetLinks

/-!
# Edge lengths of facet polygons and the rows of minus the volume Hessian

* `edgeLen k θ p m` is the length of the `m`-th edge of the (virtual) polygon with gaps `θ` and
  support numbers `p`, and `polyBilin k θ p g = ∑ₘ edgeLen k θ p m · g m`
  (`polyBilin_eq_sum_edgeLen`).
* `polytopeHessian_row`: the `i`-th row of minus the volume Hessian, applied to `f`, is
  `∑_{j ≠ i} |F_i ∩ F_j| (f j - ⟪u i, u j⟫ f i) / |u i × u j|`.
* `facetRow_of_edges`: hence the row identity of the facet decomposition follows once the link of
  facet `i` lists every facet meeting `F_i` in a segment of positive length, exactly once, with
  the edge lengths of the facet polygon.
-/

open scoped BigOperators Real

@[expose] public noncomputable section

open Classical Real Finset

namespace Erdos99

variable {ι : Type*}

/-- The length of the `m`-th edge of the (virtual) polygon with gaps `θ` (the `m`-th gap lies
between the normals `m` and `m + 1`) and support numbers `p`. -/
def edgeLen (k : ℕ) (θ p : ℕ → ℝ) (m : ℕ) : ℝ :=
  (p ((m + k - 1) % k) - p m * cos (θ ((m + k - 1) % k))) / sin (θ ((m + k - 1) % k)) +
    (p ((m + 1) % k) - p m * cos (θ m)) / sin (θ m)

/-- The polar area form is the sum of the edge lengths times the support numbers. -/
theorem polyBilin_eq_sum_edgeLen (k : ℕ) (θ p g : ℕ → ℝ) :
    polyBilin k θ p g = ∑ m ∈ range k, edgeLen k θ p m * g m := by
  set A : ℕ → ℝ := fun m => p ((m + 1) % k) / sin (θ m) - cos (θ m) / sin (θ m) * p m
  set B : ℕ → ℝ := fun m => p m / sin (θ m) - cos (θ m) / sin (θ m) * p ((m + 1) % k)
  have e1 : polyBilin k θ p g =
      ∑ m ∈ range k, A m * g m + ∑ m ∈ range k, B m * g ((m + 1) % k) := by
    unfold polyBilin edgeBilin
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [A, B]
    ring
  have e2 : ∑ m ∈ range k, B m * g ((m + 1) % k) =
      ∑ m ∈ range k, B ((m + k - 1) % k) * g m := by
    rw [← sum_range_succ_mod k (fun m => B ((m + k - 1) % k) * g m)]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm' := Finset.mem_range.1 hm
    congr 2
    rcases Nat.lt_or_ge (m + 1) k with h | h
    · rw [Nat.mod_eq_of_lt h, show m + 1 + k - 1 = m + k by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt hm']
    · have : m + 1 = k := by omega
      rw [this, Nat.mod_self, show 0 + k - 1 = m by omega, Nat.mod_eq_of_lt hm']
  rw [e1, e2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' := Finset.mem_range.1 hm
  have hk : 0 < k := by omega
  have hidx : ((m + k - 1) % k + 1) % k = m := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0
      rw [show 0 + k - 1 = k - 1 by omega, Nat.mod_eq_of_lt (show k - 1 < k by omega),
        Nat.sub_add_cancel hk,
        Nat.mod_self]
    · rw [show m + k - 1 = (m - 1) + k by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega : m - 1 < k), Nat.sub_add_cancel hpos, Nat.mod_eq_of_lt hm']
  simp only [A, B, edgeLen, hidx]
  ring

/-- The `i`-th row of minus the volume Hessian. -/
theorem polytopeHessian_row (S : Finset ι) (u : ι → Space3) (h : ι → ℝ) {i : ι} (hi : i ∈ S)
    (f : ι → ℝ) :
    -∑ j ∈ S, polytopeHessian S u h i j * f j =
      ∑ j ∈ S.erase i, Metric.diam (polyFacet S u h i ∩ polyFacet S u h j) *
        ((f j - inner ℝ (u i) (u j) * f i) / √(1 - inner ℝ (u i) (u j) ^ 2)) := by
  rw [← Finset.add_sum_erase S _ hi]
  unfold polytopeHessian
  rw [if_pos rfl, Finset.sum_mul, neg_add, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [if_neg (Finset.ne_of_mem_erase hj).symm]
  ring

/-- **The row identity from the edges.**  Suppose the link `nbr i 0, …, nbr i (k i - 1)` of
facet `i` consists of distinct facets `≠ i`, the `m`-th edge of the facet polygon has length
`|F_i ∩ F_{nbr i m}|`, and every other facet meets `F_i` in a set of diameter `0`.  Then the
`i`-th row of minus the volume Hessian is the polar area form of the facet polygon. -/
theorem facetRow_of_edges {S : Finset ι} {u : ι → Space3} {h : ι → ℝ} {k : ι → ℕ}
    {nbr : ι → ℕ → ι} {θ : ι → ℕ → ℝ} (h' : ι → ℝ) {i : ι} (hi : i ∈ S)
    (hmem : ∀ m < k i, nbr i m ∈ S.erase i)
    (hinj : ∀ m < k i, ∀ m' < k i, nbr i m = nbr i m' → m = m')
    (hlen : ∀ m < k i, edgeLen (k i) (θ i) (linkSupport u nbr i h') m =
      Metric.diam (polyFacet S u h i ∩ polyFacet S u h (nbr i m)))
    (hzero : ∀ j ∈ S.erase i, (∀ m < k i, nbr i m ≠ j) →
      Metric.diam (polyFacet S u h i ∩ polyFacet S u h j) = 0)
    (f : ι → ℝ) :
    -∑ j ∈ S, polytopeHessian S u h i j * f j =
      polyBilin (k i) (θ i) (linkSupport u nbr i h') (linkSupport u nbr i f) := by
  rw [polytopeHessian_row S u h hi, polyBilin_eq_sum_edgeLen]
  set I := (range (k i)).image (nbr i)
  have hI : I ⊆ S.erase i := by
    intro j hj
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hj
    exact hmem m (Finset.mem_range.1 hm)
  rw [← Finset.sum_subset hI ?_]
  · rw [Finset.sum_image fun m hm m' hm' e =>
      hinj m (Finset.mem_range.1 hm) m' (Finset.mem_range.1 hm') e]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [hlen m (Finset.mem_range.1 hm)]
    rfl
  · intro j hj hjI
    rw [hzero j hj fun m hm e => hjI (Finset.mem_image.2 ⟨m, Finset.mem_range.2 hm, e⟩),
      zero_mul]

end Erdos99
end

end FacetLinks

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `SimplicialFan`
-/

section SimplicialFan

/-!
# Complete simplicial fans in `ℝ³`

The cone `finCone v τ` over a finite set of rays, complete simplicial fans (`IsSimplicialFan`)
and their edges (`FanEdge`), used by the fan theorem (`FanTheorem`).
-/

open scoped BigOperators

@[expose] public noncomputable section

open Classical

namespace Erdos99

variable {ι : Type*}

/-! ## Simplicial fans -/

/-- The closed cone spanned by the vectors `v i`, `i ∈ τ`. -/
def finCone (v : ι → Space3) (τ : Finset ι) : Set Space3 :=
  {z | ∃ c : ι → ℝ, (∀ i ∈ τ, 0 ≤ c i) ∧ z = ∑ i ∈ τ, c i • v i}

/-- `T` is a complete simplicial fan with rays `v i` (`i ∈ S`): every member of `T` is a set of
three indices whose vectors are linearly independent, the cones over the members of `T` cover
`ℝ³`, and any two of them meet in the cone over their common indices (a common face). -/
structure IsSimplicialFan (S : Finset ι) (v : ι → Space3) (T : Finset (Finset ι)) : Prop where
  subset : ∀ τ ∈ T, τ ⊆ S
  card : ∀ τ ∈ T, τ.card = 3
  indep : ∀ τ ∈ T, LinearIndependent ℝ (fun i : τ => v i)
  complete : ∀ z : Space3, ∃ τ ∈ T, z ∈ finCone v τ
  inter : ∀ τ ∈ T, ∀ τ' ∈ T, finCone v τ ∩ finCone v τ' = finCone v (τ ∩ τ')

/-- `i, j` span an edge (a two-dimensional cone) of the fan `T`. -/
def FanEdge (T : Finset (Finset ι)) (i j : ι) : Prop :=
  i ≠ j ∧ ∃ τ ∈ T, i ∈ τ ∧ j ∈ τ

/-- Positive rescaling of the rays does not change the cones. -/
lemma finCone_smul (v : ι → Space3) (r : ι → ℝ) (τ : Finset ι) (hr : ∀ i ∈ τ, 0 < r i) :
    finCone (fun i => r i • v i) τ = finCone v τ := by
  ext z
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨fun i => c i * r i, fun i hi => mul_nonneg (hc i hi) (hr i hi).le, ?_⟩
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [smul_smul]
  · rintro ⟨c, hc, rfl⟩
    refine ⟨fun i => c i / r i, fun i hi => div_nonneg (hc i hi) (hr i hi).le, ?_⟩
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [smul_smul]
    rw [div_mul_cancel₀ _ (hr i hi).ne']

/-- Positive rescaling of the rays preserves a complete simplicial fan. -/
lemma IsSimplicialFan.smul {S : Finset ι} {v : ι → Space3} {T : Finset (Finset ι)}
    (hfan : IsSimplicialFan S v T) (r : ι → ℝ) (hr : ∀ i ∈ S, 0 < r i) :
    IsSimplicialFan S (fun i => r i • v i) T where
  subset := hfan.subset
  card := hfan.card
  indep := by
    intro τ hτ
    have hli := hfan.indep τ hτ
    have := hli.units_smul (fun i : τ => Units.mk0 (r i) (hr i (hfan.subset τ hτ i.2)).ne')
    convert this using 1
  complete := by
    intro z
    obtain ⟨τ, hτ, hz⟩ := hfan.complete z
    refine ⟨τ, hτ, ?_⟩
    rwa [finCone_smul v r τ fun i hi => hr i (hfan.subset τ hτ hi)]
  inter := by
    intro τ hτ τ' hτ'
    rw [finCone_smul v r τ fun i hi => hr i (hfan.subset τ hτ hi),
      finCone_smul v r τ' fun i hi => hr i (hfan.subset τ' hτ' hi),
      finCone_smul v r (τ ∩ τ') fun i hi =>
        hr i (hfan.subset τ hτ (Finset.mem_inter.1 hi).1)]
    exact hfan.inter τ hτ τ' hτ'


end Erdos99
end

end SimplicialFan

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `FanGeometry`
-/

section FanGeometry

/-!
# Linear algebra in `ℝ³` and elementary facts about simplicial fans

Auxiliary results for `FanApprox`: vectors orthogonal to independent triples, coordinates in
a plane, the inequality `α + β ≤ 1` for unit vectors outside an open cone, closedness of the cones
of a fan, uniqueness of coefficients on a cone, rays outside the cones not containing them
(`IsSimplicialFan.ray_not_mem_finCone`), and the cone on the other side of an edge
(`IsSimplicialFan.exists_cone_other_side`).
-/

open scoped BigOperators
open Filter Topology

@[expose] public noncomputable section

open Classical

namespace Erdos99

variable {ι : Type*}
/-! ## Linear algebra in `ℝ³` -/

/-- A vector orthogonal to three linearly independent vectors of `ℝ³` vanishes. -/
lemma eq_zero_of_inner_three {a b c d : Space3} (hind : LinearIndependent ℝ ![a, b, c])
    (ha : inner ℝ a d = 0) (hb : inner ℝ b d = 0) (hc : inner ℝ c d = 0) : d = 0 := by
  have hspan := hind.span_eq_top_of_card_eq_finrank (by simp)
  have hd : d ∈ (Submodule.span ℝ (Set.range ![a, b, c]))ᗮ := by
    rw [Submodule.mem_orthogonal']
    intro v hv
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨k, rfl⟩
      fin_cases k <;> simp [real_inner_comm, ha, hb, hc]
    · simp
    · intro x y _ _ hx hy; rw [inner_add_right, hx, hy, add_zero]
    · intro r x _ hx; rw [inner_smul_right, hx, mul_zero]
  rw [hspan, Submodule.top_orthogonal_eq_bot] at hd
  simpa using hd

/-- Two unit vectors with `⟪a, b⟫² < 1` and a nonzero common normal are linearly independent. -/
lemma indep_pair_normal {a b n : Space3} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : inner ℝ a b ^ 2 < 1) (hn : n ≠ 0) (hna : inner ℝ a n = 0) (hnb : inner ℝ b n = 0) :
    LinearIndependent ℝ ![a, b, n] := by
  rw [Fintype.linearIndependent_iff]
  intro w hw
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at hw
  have haa : inner ℝ a a = (1:ℝ) := by rw [real_inner_self_eq_norm_sq, ha]; norm_num
  have hbb : inner ℝ b b = (1:ℝ) := by rw [real_inner_self_eq_norm_sq, hb]; norm_num
  have hnn : 0 < inner ℝ n n := real_inner_self_pos.2 hn
  have e1 := congrArg (fun v => inner ℝ a v) hw
  have e2 := congrArg (fun v => inner ℝ b v) hw
  have e3 := congrArg (fun v => inner ℝ n v) hw
  simp only [inner_add_right, inner_smul_right, inner_zero_right] at e1 e2 e3
  rw [real_inner_comm a b] at e2
  rw [real_inner_comm a n, real_inner_comm b n] at e3
  rw [haa, hna] at e1
  rw [hbb, hnb] at e2
  rw [hna, hnb] at e3
  have h2 : w 2 = 0 := by
    have : w 2 * inner ℝ n n = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · linarith
  rw [h2] at e1 e2
  set c := inner ℝ a b
  have h0 : w 0 * (1 - c ^ 2) = 0 := by linear_combination e1 - c * e2
  have h0' : w 0 = 0 := by
    rcases mul_eq_zero.1 h0 with h | h
    · exact h
    · exfalso; linarith
  have h1 : w 1 = 0 := by rw [h0'] at e2; linarith
  intro i; fin_cases i <;> simp [h0', h1, h2]

/-- A vector orthogonal to two independent unit vectors is a multiple of their common normal. -/
lemma eq_smul_normal {a b n d : Space3} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : inner ℝ a b ^ 2 < 1) (hn : n ≠ 0) (hna : inner ℝ a n = 0) (hnb : inner ℝ b n = 0)
    (hda : inner ℝ a d = 0) (hdb : inner ℝ b d = 0) :
    d = (inner ℝ d n / ‖n‖ ^ 2) • n := by
  have hind := indep_pair_normal ha hb hab hn hna hnb
  have hn2 : ‖n‖ ^ 2 ≠ 0 := by positivity
  have := eq_zero_of_inner_three hind (d := d - (inner ℝ d n / ‖n‖ ^ 2) • n)
    (by rw [inner_sub_right, inner_smul_right, hda, hna]; ring)
    (by rw [inner_sub_right, inner_smul_right, hdb, hnb]; ring)
    (by rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, real_inner_comm]
        field_simp; ring)
  exact sub_eq_zero.1 this

/-- A vector orthogonal to the common normal of two independent unit vectors lies in their span. -/
lemma eq_comb_of_inner_normal {a b n v : Space3} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : inner ℝ a b ^ 2 < 1) (hn : n ≠ 0) (hna : inner ℝ a n = 0) (hnb : inner ℝ b n = 0)
    (hv : inner ℝ v n = 0) : ∃ α β : ℝ, v = α • a + β • b := by
  have hind := indep_pair_normal ha hb hab hn hna hnb
  set c := inner ℝ a b with hc
  have hd : (1 - c ^ 2) ≠ 0 := by nlinarith
  have haa : inner ℝ a a = (1:ℝ) := by rw [real_inner_self_eq_norm_sq, ha]; norm_num
  have hbb : inner ℝ b b = (1:ℝ) := by rw [real_inner_self_eq_norm_sq, hb]; norm_num
  have hna' : inner ℝ n a = 0 := by rw [real_inner_comm]; exact hna
  have hnb' : inner ℝ n b = 0 := by rw [real_inner_comm]; exact hnb
  have hnv : inner ℝ n v = 0 := by rw [real_inner_comm]; exact hv
  refine ⟨(inner ℝ a v - c * inner ℝ b v) / (1 - c ^ 2),
    (inner ℝ b v - c * inner ℝ a v) / (1 - c ^ 2), ?_⟩
  have := eq_zero_of_inner_three hind (d := v - ((inner ℝ a v - c * inner ℝ b v) / (1 - c ^ 2)) • a
      - ((inner ℝ b v - c * inner ℝ a v) / (1 - c ^ 2)) • b)
    (by simp only [inner_sub_right, inner_smul_right, haa, ← hc]; field_simp; ring)
    (by simp only [inner_sub_right, inner_smul_right, hbb, real_inner_comm a b, ← hc]
        field_simp; ring)
    (by simp only [inner_sub_right, inner_smul_right, hna', hnb', hnv]; ring)
  rw [sub_sub, sub_eq_zero] at this
  exact this

/-- Unit vectors in the plane of two unit vectors, outside the open cone they span, satisfy
`α + β ≤ 1`. -/
lemma add_le_one_of_unit {α β c : ℝ} (hc : c < 1) (hunit : α ^ 2 + β ^ 2 + 2 * α * β * c = 1)
    (hpos : ¬ (0 < α ∧ 0 < β)) : α + β ≤ 1 := by
  by_contra h
  push_neg at h
  rcases le_or_gt α 0 with h1 | h1
  · nlinarith [mul_nonpos_of_nonpos_of_nonneg h1 (show (0:ℝ) ≤ β by linarith)]
  · have : β ≤ 0 := by
      by_contra h2; exact hpos ⟨h1, by linarith⟩
    nlinarith [mul_nonpos_of_nonneg_of_nonpos h1.le this]

/-- Equality case of `add_le_one_of_unit`. -/
lemma eq_of_add_eq_one_of_unit {α β c : ℝ} (hc : c < 1)
    (hunit : α ^ 2 + β ^ 2 + 2 * α * β * c = 1) (hsum : α + β = 1) :
    (α = 1 ∧ β = 0) ∨ (α = 0 ∧ β = 1) := by
  have hab : α * β * (1 - c) = 0 := by nlinarith
  have hab' : α * β = 0 := by
    rcases mul_eq_zero.1 hab with h | h
    · exact h
    · exfalso; linarith
  rcases mul_eq_zero.1 hab' with h | h
  · right; constructor <;> linarith
  · left; constructor <;> linarith

/-! ## Facts about simplicial fans -/

lemma finCone_eq_coneOf (v : ι → Space3) (τ : Finset ι) : finCone v τ = Locking.coneOf v τ := by
  ext z; constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨fun k => if k ∈ τ then c k else 0, fun k => ?_, ?_⟩
    · by_cases hk : k ∈ τ
      · simp only [hk, if_true]; exact hc k hk
      · simp [hk]
    · exact Finset.sum_congr rfl fun k hk => by simp [hk]
  · rintro ⟨c, hc, rfl⟩; exact ⟨c, fun k _ => hc k, rfl⟩

lemma isClosed_finCone (v : ι → Space3) (τ : Finset ι) : IsClosed (finCone v τ) := by
  rw [finCone_eq_coneOf]; exact Locking.isClosed_coneOf v τ

lemma sum_extend_smul (v : ι → Space3) {B τ : Finset ι} (hB : B ⊆ τ) (c : ι → ℝ) :
    ∑ m ∈ τ, (if m ∈ B then c m else 0) • v m = ∑ m ∈ B, c m • v m := by
  simp only [ite_smul, zero_smul]
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 hB]

lemma sum_indicator_smul (v : ι → Space3) {τ : Finset ι} {k : ι} (hk : k ∈ τ) :
    ∑ m ∈ τ, (if m = k then (1 : ℝ) else 0) • v m = v k := by
  simp only [ite_smul, zero_smul, one_smul]
  rw [Finset.sum_ite_eq' τ k, if_pos hk]

variable {S : Finset ι} {u : ι → Space3} {T : Finset (Finset ι)}

/-- Linear independence of the rays of a cone, in `Finset`-sum form. -/
lemma IsSimplicialFan.coeff_eq_zero (hfan : IsSimplicialFan S u T) {τ : Finset ι} (hτ : τ ∈ T)
    (c : ι → ℝ) (hc : ∑ k ∈ τ, c k • u k = 0) : ∀ k ∈ τ, c k = 0 := by
  have hli := hfan.indep τ hτ
  rw [Fintype.linearIndependent_iff] at hli
  intro k hk
  have := hli (fun i : τ => c i) (by rw [← hc]; exact Finset.sum_coe_sort τ (fun i => c i • u i))
  exact this ⟨k, hk⟩

/-- A ray that belongs to some cone of the fan is not in the cone spanned by a set of rays of a
cone not containing it. -/
lemma IsSimplicialFan.ray_not_mem_finCone (hfan : IsSimplicialFan S u T) {k : ι}
    (hk : ∃ σ ∈ T, k ∈ σ) {τ B : Finset ι} (hτ : τ ∈ T) (hB : B ⊆ τ) (hkB : k ∉ B) :
    u k ∉ finCone u B := by
  rintro ⟨c, hc, hck⟩
  obtain ⟨σ, hσ, hkσ⟩ := hk
  by_cases hkτ : k ∈ τ
  · have := hfan.coeff_eq_zero hτ
      (fun m => (if m ∈ B then c m else 0) - if m = k then 1 else 0) (by
        simp only [sub_smul, Finset.sum_sub_distrib]
        rw [sum_extend_smul u hB, sum_indicator_smul u hkτ, ← hck, sub_self]) k hkτ
    simp [hkB] at this
  · have h1 : u k ∈ finCone u τ :=
      ⟨fun m => if m ∈ B then c m else 0, fun m _ => by
        by_cases hm : m ∈ B
        · simp only [hm, if_true]; exact hc m hm
        · simp [hm], by rw [sum_extend_smul u hB]; exact hck⟩
    have h2 : u k ∈ finCone u σ :=
      ⟨fun m => if m = k then 1 else 0, fun m _ => by dsimp only; split_ifs <;> norm_num,
        (sum_indicator_smul u hkσ).symm⟩
    have h3 : u k ∈ finCone u (τ ∩ σ) := by
      rw [← hfan.inter τ hτ σ hσ]; exact ⟨h1, h2⟩
    obtain ⟨d, _, hdk⟩ := h3
    have hsub : τ ∩ σ ⊆ σ := Finset.inter_subset_right
    have := hfan.coeff_eq_zero hσ
      (fun m => (if m ∈ τ ∩ σ then d m else 0) - if m = k then 1 else 0) (by
        simp only [sub_smul, Finset.sum_sub_distrib]
        rw [sum_extend_smul u hsub, sum_indicator_smul u hkσ, ← hdk, sub_self]) k hkσ
    simp [hkτ] at this

/-- **The cone on the other side of an edge.**  If `i, j` span an edge of the cone `τ` and `n`
is a normal of the plane of `u i, u j` with `τ` on its nonnegative side, then some cone `τ'`
containing `i, j` has a ray strictly on the negative side. -/
lemma IsSimplicialFan.exists_cone_other_side (hfan : IsSimplicialFan S u T) {τ : Finset ι}
    (hτ : τ ∈ T) {i j : ι} (hi : i ∈ τ) (hj : j ∈ τ) (hij : i ≠ j) {n : Space3} (hn : n ≠ 0)
    (hni : inner ℝ (u i) n = 0) (hnj : inner ℝ (u j) n = 0) :
    ∃ τ' ∈ T, i ∈ τ' ∧ j ∈ τ' ∧ ∃ b ∈ τ', inner ℝ (u b) n < 0 := by
  set z := u i + u j
  set y : ℕ → Space3 := fun m => z - (1 / ((m : ℝ) + 1)) • n
  choose τf hτf hyf using fun m : ℕ => hfan.complete (y m)
  obtain ⟨⟨τ', hτ'⟩, hinf⟩ := Finite.exists_infinite_fiber (fun m : ℕ => (⟨τf m, hτf m⟩ : T))
  have hfib : ∀ m ∈ (fun m : ℕ => (⟨τf m, hτf m⟩ : T)) ⁻¹' {⟨τ', hτ'⟩}, τf m = τ' := by
    intro m hm
    simpa using hm
  have hlim : Tendsto y atTop (𝓝 z) := by
    have : Tendsto (fun m : ℕ => (1 / ((m : ℝ) + 1))) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have := (tendsto_const_nhds (x := z)).sub (this.smul_const n)
    simpa [y] using this
  have hfreq : ∃ᶠ m in atTop, y m ∈ finCone u τ' := by
    rw [Nat.frequently_atTop_iff_infinite]
    refine (Set.infinite_coe_iff.1 hinf).mono fun m hm => ?_
    have := hyf m
    rwa [hfib m hm] at this
  have hz : z ∈ finCone u τ' := (isClosed_finCone u τ').mem_of_frequently_of_tendsto hfreq hlim
  have hzτ : z ∈ finCone u τ :=
    ⟨fun m => (if m = i then 1 else 0) + if m = j then 1 else 0,
      fun m _ => by dsimp only; split_ifs <;> norm_num, by
        simp only [add_smul, Finset.sum_add_distrib]
        rw [sum_indicator_smul u hi, sum_indicator_smul u hj]⟩
  have hzI : z ∈ finCone u (τ ∩ τ') := by rw [← hfan.inter τ hτ τ' hτ']; exact ⟨hzτ, hz⟩
  obtain ⟨d, _, hdz⟩ := hzI
  have hsub : τ ∩ τ' ⊆ τ := Finset.inter_subset_left
  have hrel : ∀ k ∈ τ, (if k ∈ τ ∩ τ' then d k else 0) -
      ((if k = i then (1:ℝ) else 0) + if k = j then 1 else 0) = 0 := by
    refine hfan.coeff_eq_zero hτ _ ?_
    simp only [sub_smul, add_smul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [sum_extend_smul u hsub, sum_indicator_smul u hi, sum_indicator_smul u hj, ← hdz, sub_self]
  have hiτ' : i ∈ τ' := by
    by_contra h
    have := hrel i hi
    simp [h, hij] at this
  have hjτ' : j ∈ τ' := by
    by_contra h
    have := hrel j hj
    simp [h, hij.symm] at this
  refine ⟨τ', hτ', hiτ', hjτ', ?_⟩
  obtain ⟨m, hm⟩ := (Set.infinite_coe_iff.1 hinf).nonempty
  have hym := hyf m
  rw [hfib m hm] at hym
  obtain ⟨β, hβ, hβy⟩ := hym
  by_contra hcon
  push_neg at hcon
  have h1 : inner ℝ (y m) n = -(1 / ((m : ℝ) + 1)) * ‖n‖ ^ 2 := by
    simp only [y, z, inner_sub_left, inner_add_left, inner_smul_left, hni, hnj,
      real_inner_self_eq_norm_sq, RCLike.conj_to_real]
    ring
  have h2 : 0 ≤ inner ℝ (y m) n := by
    rw [hβy, sum_inner]
    exact Finset.sum_nonneg fun v hv => by
      rw [inner_smul_left, RCLike.conj_to_real]; exact mul_nonneg (hβ v hv) (hcon v hv)
  have h3 : 0 < ‖n‖ := norm_pos_iff.2 hn
  have h4 : (0 : ℝ) < 1 / ((m : ℝ) + 1) * ‖n‖ ^ 2 := by positivity
  linarith

end Erdos99
end

end FanGeometry

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `FanApprox`
-/

section FanApprox

/-!
# Approximating a fan matrix by polytope Hessians (Verification Guide §7.3 (d), (f))

Let `T` be a complete simplicial fan with distinct unit rays `u i` (`i ∈ S`), every ray of which
belongs to some cone of `T`, and let `W` be a symmetric fan matrix (`W u = 0`, nonpositive
off-diagonal entries supported on fan edges).  Suppose `W` has been integrated to *support data*
(`FanSupport`): a point `g τ` for every cone `τ ∈ T` (the gradient of the piecewise-linear support
function on `τ`) and support numbers `h`, such that

* `⟪u k, g τ⟫ = h k` for `k ∈ τ` and `⟪u k, g τ⟫ ≤ h k` for all `k ∈ S` (convexity);
* two distinct cones sharing the edge `ij` have `‖g τ - g τ'‖ = -W i j |u i × u j|`.

Then the shifted polytopes `K_t = {x : ⟪u k, x⟫ ≤ h k + t}` (`t > 0`) are bounded, have all their
facets present, and their minus volume Hessians converge entrywise to `W` as `t → 0⁺`
(`IsSimplicialFan.matrix_approx_of_support`).  This is steps (d) and (f) of the Guide.  The proof is local:

* across a fan edge `ij` with cones `τ = {i, j, a}` and `τ' = {i, j, b}` (on opposite sides of the
  plane of `u i, u j`, `exists_cone_other_side`), the common edge of the facets `i, j` of `K_t`
  lies within `O(t)` of the segment `[g τ, g τ']` (`edge_dist_le`), and contains translates of
  compact subsegments of it for small `t` (`edge_point_mem`);
* for a non-edge `ij`, the cone containing `u i + u j` pins the common edge to a set of
  diameter `O(t)`, or shows that it is empty (`nonedge_dist_le`).

The hypothesis that every ray lies in a cone of the fan is necessary: a ray in the relative
interior of a two-dimensional cone `ij` with `W i j ≠ 0` forces `F_i ∩ F_j = ∅` in every polytope
in which its facet is present.
-/

open scoped BigOperators
open Filter Topology

@[expose] public noncomputable section

open Classical

namespace Erdos99

variable {ι : Type*}

variable {S : Finset ι} {u : ι → Space3} {T : Finset (Finset ι)}

/-! ## The common edge of two facets of a shifted polytope -/

/-- **Upper bound across a fan edge.**  Let `p₀, p₁` be the gradients on two cones `{i, j, a}`,
`{i, j, b}` on opposite sides of the plane of `u i, u j` (normal `n`).  Any two points of the
common edge of the facets `i, j` of the polytope shifted by `t ≥ 0` are at distance at most
`‖p₀ - p₁‖ + C t`. -/
lemma edge_dist_le {ui uj ua ub n p₀ p₁ x y : Space3} {hi hj ha hb t : ℝ}
    (hui : ‖ui‖ = 1) (huj : ‖uj‖ = 1) (hc : inner ℝ ui uj ^ 2 < 1) (hn : n ≠ 0)
    (hni : inner ℝ ui n = 0) (hnj : inner ℝ uj n = 0)
    (hna : 0 < inner ℝ ua n) (hnb : inner ℝ ub n < 0)
    (hi0 : inner ℝ ui p₀ = hi) (hi1 : inner ℝ ui p₁ = hi)
    (hj0 : inner ℝ uj p₀ = hj) (hj1 : inner ℝ uj p₁ = hj)
    (ha0 : inner ℝ ua p₀ = ha) (ha1 : inner ℝ ua p₁ ≤ ha)
    (hb1 : inner ℝ ub p₁ = hb)
    (hxi : inner ℝ ui x = hi + t) (hxj : inner ℝ uj x = hj + t)
    (hxa : inner ℝ ua x ≤ ha + t) (hxb : inner ℝ ub x ≤ hb + t)
    (hyi : inner ℝ ui y = hi + t) (hyj : inner ℝ uj y = hj + t)
    (hya : inner ℝ ua y ≤ ha + t) (hyb : inner ℝ ub y ≤ hb + t) :
    dist x y ≤ ‖p₀ - p₁‖ + t * (((1 - inner ℝ ua ((1 + inner ℝ ui uj)⁻¹ • (ui + uj))) /
      inner ℝ ua n - (1 - inner ℝ ub ((1 + inner ℝ ui uj)⁻¹ • (ui + uj))) / inner ℝ ub n) * ‖n‖) := by
  set c := inner ℝ ui uj with hcdef
  have hc1 : 1 + c ≠ 0 := by nlinarith
  set e : Space3 := (1 + c)⁻¹ • (ui + uj) with he
  have hui' : inner ℝ ui ui = (1:ℝ) := by rw [real_inner_self_eq_norm_sq, hui]; norm_num
  have huj' : inner ℝ uj uj = (1:ℝ) := by rw [real_inner_self_eq_norm_sq, huj]; norm_num
  have hei : inner ℝ ui e = 1 := by
    rw [he, inner_smul_right, inner_add_right, hui', ← hcdef]; exact inv_mul_cancel₀ hc1
  have hej : inner ℝ uj e = 1 := by
    rw [he, inner_smul_right, inner_add_right, huj', real_inner_comm ui uj, ← hcdef, add_comm c 1]
    exact inv_mul_cancel₀ hc1
  set A := inner ℝ ua n
  set B := inner ℝ ub n
  set Ka := 1 - inner ℝ ua e
  set Kb := 1 - inner ℝ ub e
  -- coordinates along `n`
  have hperp : ∀ d : Space3, inner ℝ ui d = 0 → inner ℝ uj d = 0 →
      d = (inner ℝ d n / ‖n‖ ^ 2) • n := fun d h1 h2 => eq_smul_normal hui huj hc hn hni hnj h1 h2
  have key : ∀ w : Space3, inner ℝ ui w = hi + t → inner ℝ uj w = hj + t →
      inner ℝ ua w ≤ ha + t → inner ℝ ub w ≤ hb + t →
      w - t • e - p₀ = (inner ℝ (w - t • e - p₀) n / ‖n‖ ^ 2) • n ∧
      inner ℝ (w - t • e - p₀) n / ‖n‖ ^ 2 ≤ t * Ka / A ∧
      inner ℝ (p₁ - p₀) n / ‖n‖ ^ 2 + t * Kb / B ≤ inner ℝ (w - t • e - p₀) n / ‖n‖ ^ 2 := by
    intro w hwi hwj hwa hwb
    have hd := hperp (w - t • e - p₀)
      (by rw [inner_sub_right, inner_sub_right, inner_smul_right, hei, hwi, hi0]; ring)
      (by rw [inner_sub_right, inner_sub_right, inner_smul_right, hej, hwj, hj0]; ring)
    have hd1 := hperp (p₁ - p₀) (by rw [inner_sub_right, hi0, hi1, sub_self])
      (by rw [inner_sub_right, hj0, hj1, sub_self])
    refine ⟨hd, ?_, ?_⟩
    · have h1 : inner ℝ ua (w - t • e - p₀) ≤ t * Ka := by
        rw [inner_sub_right, inner_sub_right, inner_smul_right, ha0]; simp only [Ka]; linarith
      rw [hd, inner_smul_right] at h1
      rw [le_div_iff₀ hna]; linarith
    · have h2 : inner ℝ ub (w - t • e - p₀) - inner ℝ ub (p₁ - p₀) ≤ t * Kb := by
        rw [inner_sub_right, inner_sub_right, inner_smul_right, inner_sub_right]
        simp only [Kb]; linarith
      rw [hd, hd1, inner_smul_right, inner_smul_right] at h2
      have : t * Kb / B ≤ inner ℝ (w - t • e - p₀) n / ‖n‖ ^ 2 - inner ℝ (p₁ - p₀) n / ‖n‖ ^ 2 := by
        rw [div_le_iff_of_neg hnb]; linarith
      linarith
  obtain ⟨hx1, hx2, hx3⟩ := key x hxi hxj hxa hxb
  obtain ⟨hy1, hy2, hy3⟩ := key y hyi hyj hya hyb
  set σx := inner ℝ (x - t • e - p₀) n / ‖n‖ ^ 2
  set σy := inner ℝ (y - t • e - p₀) n / ‖n‖ ^ 2
  set ρ := inner ℝ (p₁ - p₀) n / ‖n‖ ^ 2
  have hd1 : p₁ - p₀ = ρ • n := eq_smul_normal hui huj hc hn hni hnj
    (by rw [inner_sub_right, hi0, hi1, sub_self]) (by rw [inner_sub_right, hj0, hj1, sub_self])
  have hρ : ρ ≤ 0 := by
    have : inner ℝ ua (p₁ - p₀) ≤ 0 := by rw [inner_sub_right]; linarith
    rw [hd1, inner_smul_right] at this
    by_contra h; push_neg at h; nlinarith
  have hxy : x - y = (σx - σy) • n := by
    rw [sub_smul, ← hx1, ← hy1]; abel
  have hp : ‖p₀ - p₁‖ = -ρ * ‖n‖ := by
    rw [← neg_sub, norm_neg, hd1, norm_smul, Real.norm_eq_abs, abs_of_nonpos hρ]
  rw [dist_eq_norm, hxy, norm_smul, Real.norm_eq_abs, hp]
  have hab : |σx - σy| ≤ t * Ka / A - ρ - t * Kb / B := by
    rw [abs_le]; constructor <;> linarith
  have hn0 : 0 ≤ ‖n‖ := norm_nonneg _
  have : t * ((Ka / A - Kb / B) * ‖n‖) = (t * Ka / A - t * Kb / B) * ‖n‖ := by ring
  rw [this]
  have := mul_le_mul_of_nonneg_right hab hn0
  linarith

/-- The shift direction `e = (u i + u j) / (1 + ⟪u i, u j⟫)` has `⟪u i, e⟫ = ⟪u j, e⟫ = 1`. -/
lemma inner_shiftDir {ui uj : Space3} (hui : ‖ui‖ = 1) (huj : ‖uj‖ = 1)
    (hc : inner ℝ ui uj ^ 2 < 1) :
    inner ℝ ui ((1 + inner ℝ ui uj)⁻¹ • (ui + uj)) = 1 ∧
      inner ℝ uj ((1 + inner ℝ ui uj)⁻¹ • (ui + uj)) = 1 := by
  have hc1 : 1 + inner ℝ ui uj ≠ 0 := by nlinarith
  have hui' : inner ℝ ui ui = (1:ℝ) := by rw [real_inner_self_eq_norm_sq, hui]; norm_num
  have huj' : inner ℝ uj uj = (1:ℝ) := by rw [real_inner_self_eq_norm_sq, huj]; norm_num
  constructor
  · rw [inner_smul_right, inner_add_right, hui']; exact inv_mul_cancel₀ hc1
  · rw [inner_smul_right, inner_add_right, huj', real_inner_comm ui uj, add_comm _ (1:ℝ)]
    exact inv_mul_cancel₀ hc1

/-- **Lower bound across a fan edge.**  Points of the open segment `(p₀, p₁)`, shifted by
`t e` with `e = (u i + u j) / (1 + ⟪u i, u j⟫)`, lie on the common edge of the facets `i, j` of
the polytope shifted by `t`, for all small `t > 0`. -/
lemma edge_point_eventually {S : Finset ι} {u : ι → Space3} {h : ι → ℝ} {i j : ι}
    (hu : ∀ k ∈ S, ‖u k‖ = 1) (hiS : i ∈ S) (hjS : j ∈ S) (hc : inner ℝ (u i) (u j) ^ 2 < 1)
    (hcone : ∀ k ∈ S, k ≠ i → k ≠ j → ∀ α β : ℝ, u k = α • u i + β • u j → ¬ (0 ≤ α ∧ 0 ≤ β))
    {p₀ p₁ : Space3} (hne : p₀ ≠ p₁) (hp₀ : ∀ k ∈ S, inner ℝ (u k) p₀ ≤ h k)
    (hp₁ : ∀ k ∈ S, inner ℝ (u k) p₁ ≤ h k)
    (hi0 : inner ℝ (u i) p₀ = h i) (hi1 : inner ℝ (u i) p₁ = h i)
    (hj0 : inner ℝ (u j) p₀ = h j) (hj1 : inner ℝ (u j) p₁ = h j)
    {lam : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), p₀ + lam • (p₁ - p₀) + t • ((1 + inner ℝ (u i) (u j))⁻¹ • (u i + u j)) ∈
      polyFacet S u (fun k => h k + t) i ∩ polyFacet S u (fun k => h k + t) j := by
  set c := inner ℝ (u i) (u j) with hcdef
  set e : Space3 := (1 + c)⁻¹ • (u i + u j) with he
  set w := p₀ + lam • (p₁ - p₀) with hw
  obtain ⟨hei, hej⟩ := inner_shiftDir (hu i hiS) (hu j hjS) hc
  have hwk : ∀ k, inner ℝ (u k) w = (1 - lam) * inner ℝ (u k) p₀ + lam * inner ℝ (u k) p₁ := by
    intro k; rw [hw, inner_add_right, inner_smul_right, inner_sub_right]; ring
  have hc1 : c < 1 := by nlinarith
  have hke : ∀ k ∈ S, inner ℝ (u k) p₀ = h k → inner ℝ (u k) p₁ = h k → inner ℝ (u k) e ≤ 1 := by
    intro k hk hk0 hk1
    by_cases hki : k = i
    · subst hki; exact hei.le
    by_cases hkj : k = j
    · subst hkj; exact hej.le
    obtain ⟨n, hn0, hni, hnj⟩ := exists_orth_pair (u i) (u j)
    rw [real_inner_comm] at hni hnj
    have hd := eq_smul_normal (hu i hiS) (hu j hjS) hc hn0 hni hnj (d := p₁ - p₀)
      (by rw [inner_sub_right, hi0, hi1, sub_self]) (by rw [inner_sub_right, hj0, hj1, sub_self])
    set ρ := inner ℝ (p₁ - p₀) n / ‖n‖ ^ 2
    have hρ : ρ ≠ 0 := by
      intro h0; rw [h0, zero_smul, sub_eq_zero] at hd; exact hne hd.symm
    have hkn : inner ℝ (u k) n = 0 := by
      have : inner ℝ (u k) (p₁ - p₀) = 0 := by rw [inner_sub_right, hk0, hk1, sub_self]
      rw [hd, inner_smul_right] at this
      rcases mul_eq_zero.1 this with h0 | h0
      · exact absurd h0 hρ
      · exact h0
    obtain ⟨α, β, hab⟩ := eq_comb_of_inner_normal (hu i hiS) (hu j hjS) hc hn0 hni hnj hkn
    have hpos := hcone k hk hki hkj α β hab
    have hii : inner ℝ (u i) (u i) = (1:ℝ) := by
      rw [real_inner_self_eq_norm_sq, hu i hiS]; norm_num
    have hjj : inner ℝ (u j) (u j) = (1:ℝ) := by
      rw [real_inner_self_eq_norm_sq, hu j hjS]; norm_num
    have hunit : α ^ 2 + β ^ 2 + 2 * α * β * c = 1 := by
      have h1 : inner ℝ (u k) (u k) = (1:ℝ) := by
        rw [real_inner_self_eq_norm_sq, hu k hk]; norm_num
      rw [hab] at h1
      simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
        RCLike.conj_to_real, hii, hjj, real_inner_comm (u i) (u j), ← hcdef] at h1
      linarith
    have hval : inner ℝ (u k) e = α + β := by
      have h1 : inner ℝ (u k) e = α * inner ℝ (u i) e + β * inner ℝ (u j) e := by
        rw [hab, inner_add_left, inner_smul_left, inner_smul_left]; simp
      rw [h1, hei, hej]; ring
    rw [hval]
    exact add_le_one_of_unit hc1 hunit fun h' => hpos ⟨h'.1.le, h'.2.le⟩
  have hK : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ k ∈ S, inner ℝ (u k) (w + t • e) ≤ h k + t := by
    rw [Filter.eventually_all_finset]
    intro k hk
    by_cases hlt : inner ℝ (u k) w < h k
    · have hcont : Tendsto (fun t : ℝ => inner ℝ (u k) (w + t • e) - t) (𝓝[>] 0)
          (𝓝 (inner ℝ (u k) w)) := by
        have := ((by fun_prop : Continuous fun t : ℝ => inner ℝ (u k) (w + t • e) - t).tendsto 0)
        simpa using this.mono_left nhdsWithin_le_nhds
      filter_upwards [hcont.eventually (gt_mem_nhds hlt)] with t ht
      linarith
    · have h0 := hp₀ k hk
      have h1 := hp₁ k hk
      have hwle : inner ℝ (u k) w ≤ h k := by rw [hwk]; nlinarith
      have heq : inner ℝ (u k) w = h k := le_antisymm hwle (not_lt.1 hlt)
      rw [hwk] at heq
      have hk0 : inner ℝ (u k) p₀ = h k := by nlinarith
      have hk1 : inner ℝ (u k) p₁ = h k := by nlinarith
      have := hke k hk hk0 hk1
      filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      rw [inner_add_right, inner_smul_right, hwk, hk0, hk1]
      nlinarith
  filter_upwards [hK] with t ht
  refine ⟨⟨ht, ?_⟩, ⟨ht, ?_⟩⟩
  · rw [inner_add_right, inner_smul_right, hwk, hi0, hi1, hei]; ring
  · rw [inner_add_right, inner_smul_right, hwk, hj0, hj1, hej]; ring

/-! ## Non-edges -/

lemma sum_single_smul (v : ι → Space3) {τ : Finset ι} {k : ι} (hk : k ∈ τ) (a : ℝ) :
    ∑ m ∈ τ, (if m = k then a else 0) • v m = a • v k := by
  simp only [ite_smul, zero_smul]
  rw [Finset.sum_ite_eq' τ k, if_pos hk]

/-- Coefficients with respect to two independent unit vectors are unique. -/
lemma coeff_unique_pair {a b : Space3} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : inner ℝ a b ^ 2 < 1)
    {α β α' β' : ℝ} (h : α • a + β • b = α' • a + β' • b) : α = α' ∧ β = β' := by
  have haa : inner ℝ a a = (1:ℝ) := by rw [real_inner_self_eq_norm_sq, ha]; norm_num
  have hbb : inner ℝ b b = (1:ℝ) := by rw [real_inner_self_eq_norm_sq, hb]; norm_num
  have e1 := congrArg (fun v => inner ℝ a v) h
  have e2 := congrArg (fun v => inner ℝ b v) h
  simp only [inner_add_right, inner_smul_right, haa, hbb, real_inner_comm a b] at e1 e2
  set c := inner ℝ a b
  have h1 : (α - α') * (1 - c ^ 2) = 0 := by linear_combination e1 - c * e2
  have h2 : α = α' := by
    rcases mul_eq_zero.1 h1 with h | h
    · linarith
    · exfalso; nlinarith
  refine ⟨h2, ?_⟩
  subst h2
  have : (β - β') * (1 - c ^ 2) = 0 := by linear_combination e2 - c * e1
  rcases mul_eq_zero.1 this with h | h
  · linarith
  · exfalso; nlinarith

/-- Two distinct rays of a cone of the fan are not parallel. -/
lemma IsSimplicialFan.inner_sq_lt_one (hfan : IsSimplicialFan S u T) (hu : ∀ i ∈ S, ‖u i‖ = 1)
    {τ : Finset ι} (hτ : τ ∈ T) {a b : ι} (ha : a ∈ τ) (hb : b ∈ τ) (hab : a ≠ b) :
    inner ℝ (u a) (u b) ^ 2 < 1 := by
  have hua := hu a (hfan.subset τ hτ ha)
  have hub := hu b (hfan.subset τ hτ hb)
  set c := inner ℝ (u a) (u b) with hc
  by_contra hcon
  push_neg at hcon
  have hcs : |c| ≤ 1 := by
    have := abs_real_inner_le_norm (u a) (u b)
    rw [hua, hub, one_mul] at this; exact this
  have hc2 : c ^ 2 = 1 := by nlinarith [abs_nonneg c, sq_abs c]
  have hsq : ‖u a - c • u b‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      RCLike.conj_to_real, real_inner_self_eq_norm_sq, hua, hub, real_inner_comm (u a) (u b), ← hc]
    nlinarith
  have hzero : u a - c • u b = 0 := by
    rw [← norm_eq_zero]; exact (pow_eq_zero_iff two_ne_zero).1 hsq
  have := hfan.coeff_eq_zero hτ (fun m => (if m = a then 1 else 0) - if m = b then c else 0) (by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [sum_single_smul u ha, sum_single_smul u hb, one_smul]; exact hzero) a ha
  simp [hab] at this

/-- The three rays of a cone of the fan are linearly independent. -/
lemma IsSimplicialFan.indep_three (hfan : IsSimplicialFan S u T) {p q r : ι}
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (hτ : ({p, q, r} : Finset ι) ∈ T) :
    LinearIndependent ℝ ![u p, u q, u r] := by
  rw [Fintype.linearIndependent_iff]
  intro w hw
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at hw
  have hp : p ∈ ({p, q, r} : Finset ι) := by simp
  have hq : q ∈ ({p, q, r} : Finset ι) := by simp
  have hr : r ∈ ({p, q, r} : Finset ι) := by simp
  have key := hfan.coeff_eq_zero hτ
    (fun m => ((if m = p then w 0 else 0) + (if m = q then w 1 else 0)) +
      if m = r then w 2 else 0) (by
      simp only [add_smul, Finset.sum_add_distrib]
      rw [sum_single_smul u hp, sum_single_smul u hq, sum_single_smul u hr]; exact hw)
  have h0 := key p hp
  have h1 := key q hq
  have h2 := key r hr
  simp [hpq, hpr, hqr, hpq.symm, hpr.symm, hqr.symm] at h0 h1 h2
  intro m; fin_cases m <;> simp [h0, h1, h2]

/-- If `u i + u j = α u_a` for unit vectors with `⟪u i, u j⟫² < 1`, then `α < 2`. -/
lemma single_lt_two {ui uj ua : Space3} {α : ℝ} (hui : ‖ui‖ = 1) (huj : ‖uj‖ = 1)
    (hua : ‖ua‖ = 1) (hc : inner ℝ ui uj ^ 2 < 1) (hz : ui + uj = α • ua) : α < 2 := by
  have h1 : inner ℝ (ui + uj) (ui + uj) = 2 + 2 * inner ℝ ui uj := by
    simp only [inner_add_left, inner_add_right, real_inner_self_eq_norm_sq, hui, huj,
      real_inner_comm ui uj]
    ring
  have h2 : inner ℝ (α • ua) (α • ua) = α ^ 2 := by
    simp only [inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq, hua,
      RCLike.conj_to_real]
    ring
  rw [hz, h2] at h1
  have : inner ℝ ui uj < 1 := by nlinarith
  nlinarith

/-- **The planar two-ray case.**  Let `u i + u j = α_a u_a + α_b u_b` with `α_a, α_b > 0`, all
four unit vectors in one plane, `u_a, u_b` independent, and neither `u i` nor `u j` in the open
cone spanned by `u_a, u_b`.  Unless `{u i, u j} = {u_a, u_b}`, `α_a + α_b < 2`. -/
lemma pair_sum_lt_two {ui uj ua ub n : Space3} {αa αb : ℝ} (hui : ‖ui‖ = 1) (huj : ‖uj‖ = 1)
    (hua : ‖ua‖ = 1) (hub : ‖ub‖ = 1) (hcij : inner ℝ ui uj ^ 2 < 1)
    (hcab : inner ℝ ua ub ^ 2 < 1) (hn : n ≠ 0) (hni : inner ℝ ui n = 0)
    (hnj : inner ℝ uj n = 0) (hna : inner ℝ ua n = 0) (hnb : inner ℝ ub n = 0)
    (hz : ui + uj = αa • ua + αb • ub)
    (hi : ∀ l m : ℝ, ui = l • ua + m • ub → ¬ (0 < l ∧ 0 < m))
    (hj : ∀ l m : ℝ, uj = l • ua + m • ub → ¬ (0 < l ∧ 0 < m))
    (hne : ¬ ((ui = ua ∧ uj = ub) ∨ (ui = ub ∧ uj = ua))) : αa + αb < 2 := by
  obtain ⟨li, mi, hi'⟩ := eq_comb_of_inner_normal hua hub hcab hn hna hnb hni
  obtain ⟨lj, mj, hj'⟩ := eq_comb_of_inner_normal hua hub hcab hn hna hnb hnj
  set c := inner ℝ ua ub with hc
  have hc1 : c < 1 := by nlinarith
  have haa : inner ℝ ua ua = (1:ℝ) := by rw [real_inner_self_eq_norm_sq, hua]; norm_num
  have hbb : inner ℝ ub ub = (1:ℝ) := by rw [real_inner_self_eq_norm_sq, hub]; norm_num
  have hunit : ∀ v : Space3, ‖v‖ = 1 → ∀ l m : ℝ, v = l • ua + m • ub →
      l ^ 2 + m ^ 2 + 2 * l * m * c = 1 := by
    intro v hv l m hvlm
    have h1 : inner ℝ v v = (1:ℝ) := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
    rw [hvlm] at h1
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      RCLike.conj_to_real, haa, hbb, real_inner_comm ua ub, ← hc] at h1
    linarith
  have hui1 := hunit ui hui li mi hi'
  have huj1 := hunit uj huj lj mj hj'
  have hcoef : αa = li + lj ∧ αb = mi + mj := by
    refine coeff_unique_pair hua hub hcab ?_
    rw [← hz, hi', hj']; module
  have si := add_le_one_of_unit hc1 hui1 (hi li mi hi')
  have sj := add_le_one_of_unit hc1 huj1 (hj lj mj hj')
  rw [hcoef.1, hcoef.2]
  by_contra hcon
  have ei : li + mi = 1 := by linarith
  have ej : lj + mj = 1 := by linarith
  have hneq : ui ≠ uj := by
    intro h; rw [h, real_inner_self_eq_norm_sq, huj] at hcij; norm_num at hcij
  rcases eq_of_add_eq_one_of_unit hc1 hui1 ei with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
  rcases eq_of_add_eq_one_of_unit hc1 huj1 ej with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · exact hneq (by rw [hi', hj', h1, h2, h3, h4])
  · exact hne (Or.inl ⟨by rw [hi', h1, h2]; simp, by rw [hj', h3, h4]; simp⟩)
  · exact hne (Or.inr ⟨by rw [hi', h1, h2]; simp, by rw [hj', h3, h4]; simp⟩)
  · exact hneq (by rw [hi', hj', h1, h2, h3, h4])

/-- The two-ray case of a non-edge, inside the fan. -/
lemma IsSimplicialFan.two_term_lt_two (hfan : IsSimplicialFan S u T) (hu : ∀ i ∈ S, ‖u i‖ = 1)
    (hinj : ∀ i ∈ S, ∀ j ∈ S, u i = u j → i = j) (hused : ∀ i ∈ S, ∃ τ ∈ T, i ∈ τ)
    {τ : Finset ι} (hτ : τ ∈ T) {i j a b : ι} (hiS : i ∈ S) (hjS : j ∈ S) (hij : i ≠ j)
    (hc : inner ℝ (u i) (u j) ^ 2 < 1) (hne : ¬ FanEdge T i j) (ha : a ∈ τ) (hb : b ∈ τ)
    (hab : a ≠ b) {n : Space3} (hn0 : n ≠ 0) (hni : inner ℝ (u i) n = 0)
    (hnj : inner ℝ (u j) n = 0) {αa αb : ℝ} (hαa : 0 ≤ αa) (hαb : 0 ≤ αb)
    (hpa : 0 < αa → inner ℝ (u a) n = 0) (hpb : 0 < αb → inner ℝ (u b) n = 0)
    (hz : u i + u j = αa • u a + αb • u b) : αa + αb < 2 := by
  have haS := hfan.subset τ hτ ha
  have hbS := hfan.subset τ hτ hb
  rcases eq_or_lt_of_le hαa with h0 | hpa'
  · rw [← h0, zero_smul, zero_add] at hz
    have := single_lt_two (hu i hiS) (hu j hjS) (hu b hbS) hc hz
    linarith
  rcases eq_or_lt_of_le hαb with h0 | hpb'
  · rw [← h0, zero_smul, add_zero] at hz
    have := single_lt_two (hu i hiS) (hu j hjS) (hu a haS) hc hz
    linarith
  have hcab := hfan.inner_sq_lt_one hu hτ ha hb hab
  have hcone : ∀ k ∈ S, ∀ l m : ℝ, u k = l • u a + m • u b → ¬ (0 < l ∧ 0 < m) := by
    intro k hk l m hlm ⟨hl, hm⟩
    by_cases hka : k = a
    · subst hka
      have := (coeff_unique_pair (hu k hk) (hu b hbS) hcab
        (show (1 : ℝ) • u k + (0 : ℝ) • u b = l • u k + m • u b by rw [← hlm]; simp)).2
      linarith
    by_cases hkb : k = b
    · subst hkb
      have := (coeff_unique_pair (hu a haS) (hu k hk) hcab
        (show (0 : ℝ) • u a + (1 : ℝ) • u k = l • u a + m • u k by rw [← hlm]; simp)).1
      linarith
    apply hfan.ray_not_mem_finCone (hused k hk) hτ (B := {a, b})
      (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption)
      (by simp [hka, hkb])
    refine ⟨fun x => if x = a then l else m, fun x hx => by
      dsimp only; split_ifs <;> linarith, ?_⟩
    rw [Finset.sum_pair hab]; simpa [hab.symm] using hlm
  refine pair_sum_lt_two (hu i hiS) (hu j hjS) (hu a haS) (hu b hbS) hc hcab hn0 hni hnj
    (hpa hpa') (hpb hpb') hz (hcone i hiS) (hcone j hjS) ?_
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · have e1 := hinj i hiS a haS h1
    have e2 := hinj j hjS b hbS h2
    subst e1; subst e2
    exact hne ⟨hij, τ, hτ, ha, hb⟩
  · have e1 := hinj i hiS b hbS h1
    have e2 := hinj j hjS a haS h2
    subst e1; subst e2
    exact hne ⟨hij, τ, hτ, hb, ha⟩

/-- **Non-edges.**  If `i, j` do not span an edge of the fan, the common edge of the facets
`i, j` of the polytope shifted by `t > 0` has diameter `O(t)` (in fact it is empty unless the
cone containing `u i + u j` has a ray off the plane of `u i, u j`). -/
lemma IsSimplicialFan.nonedge_dist_le (hfan : IsSimplicialFan S u T)
    (hu : ∀ i ∈ S, ‖u i‖ = 1) (hinj : ∀ i ∈ S, ∀ j ∈ S, u i = u j → i = j)
    (hused : ∀ i ∈ S, ∃ τ ∈ T, i ∈ τ) {g : Finset ι → Space3} {h : ι → ℝ}
    (htight : ∀ τ ∈ T, ∀ k ∈ τ, inner ℝ (u k) (g τ) = h k)
    (hle : ∀ τ ∈ T, ∀ k ∈ S, inner ℝ (u k) (g τ) ≤ h k)
    {i j : ι} (hiS : i ∈ S) (hjS : j ∈ S) (hij : i ≠ j) (hc : inner ℝ (u i) (u j) ^ 2 < 1)
    (hne : ¬ FanEdge T i j) :
    ∃ C : ℝ, ∀ t : ℝ, 0 < t → ∀ x ∈ polyFacet S u (fun k => h k + t) i ∩
      polyFacet S u (fun k => h k + t) j, ∀ y ∈ polyFacet S u (fun k => h k + t) i ∩
      polyFacet S u (fun k => h k + t) j, dist x y ≤ C * t := by
  obtain ⟨τ, hτ, α, hα, hz⟩ := hfan.complete (u i + u j)
  obtain ⟨n, hn0, hni, hnj⟩ := exists_orth_pair (u i) (u j)
  rw [real_inner_comm] at hni hnj
  set sα := ∑ a ∈ τ, α a with hsα
  have hτS := hfan.subset τ hτ
  -- the slack inequality
  have hslack : ∀ t : ℝ, ∀ x ∈ polyFacet S u (fun k => h k + t) i ∩
      polyFacet S u (fun k => h k + t) j,
      ∑ a ∈ τ, α a * (h a + t - inner ℝ (u a) x) ≤ t * (sα - 2) := by
    intro t x ⟨⟨_, hxi⟩, ⟨_, hxj⟩⟩
    have e1 : ∑ a ∈ τ, α a * inner ℝ (u a) x = inner ℝ (u i) x + inner ℝ (u j) x := by
      rw [← inner_add_left, hz, sum_inner]
      exact Finset.sum_congr rfl fun a _ => by rw [inner_smul_left, RCLike.conj_to_real]
    have e2 : ∑ a ∈ τ, α a * h a = inner ℝ (u i) (g τ) + inner ℝ (u j) (g τ) := by
      rw [← inner_add_left, hz, sum_inner]
      exact Finset.sum_congr rfl fun a ha => by
        rw [inner_smul_left, RCLike.conj_to_real, htight τ hτ a ha]
    have e3 : ∑ a ∈ τ, α a * (h a + t - inner ℝ (u a) x) =
        ∑ a ∈ τ, α a * h a + t * sα - ∑ a ∈ τ, α a * inner ℝ (u a) x := by
      rw [hsα, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [e3, e1, e2]
    have := hle τ hτ i hiS
    have := hle τ hτ j hjS
    simp only at hxi hxj
    linarith
  have hslack_nonneg : ∀ t : ℝ, ∀ x ∈ polyFacet S u (fun k => h k + t) i ∩
      polyFacet S u (fun k => h k + t) j, ∀ a ∈ τ, 0 ≤ α a * (h a + t - inner ℝ (u a) x) := by
    intro t x ⟨⟨hxK, _⟩, _⟩ a ha
    have := hxK a (hτS ha)
    exact mul_nonneg (hα a ha) (by simp only at this; linarith)
  have hsα0 : 0 ≤ sα := Finset.sum_nonneg fun a ha => hα a ha
  by_cases hA : ∃ a ∈ τ, 0 < α a ∧ inner ℝ (u a) n ≠ 0
  · obtain ⟨a, ha, hαa, hna⟩ := hA
    refine ⟨sα / α a / |inner ℝ (u a) n| * ‖n‖, fun t ht x hx y hy => ?_⟩
    have hbound : ∀ w ∈ polyFacet S u (fun k => h k + t) i ∩
        polyFacet S u (fun k => h k + t) j,
        0 ≤ h a + t - inner ℝ (u a) w ∧ h a + t - inner ℝ (u a) w ≤ t * sα / α a := by
      intro w hw
      have h1 := hslack t w hw
      have h2 := Finset.single_le_sum (hslack_nonneg t w hw) ha
      have h3 := hslack_nonneg t w hw a ha
      refine ⟨(mul_nonneg_iff_of_pos_left hαa).1 h3, ?_⟩
      rw [le_div_iff₀ hαa]; nlinarith
    obtain ⟨hx1, hx2⟩ := hbound x hx
    obtain ⟨hy1, hy2⟩ := hbound y hy
    obtain ⟨⟨_, hxi⟩, ⟨_, hxj⟩⟩ := hx
    obtain ⟨⟨_, hyi⟩, ⟨_, hyj⟩⟩ := hy
    simp only at hxi hxj hyi hyj
    have hd := eq_smul_normal (hu i hiS) (hu j hjS) hc hn0 hni hnj (d := x - y)
      (by rw [inner_sub_right, hxi, hyi, sub_self]) (by rw [inner_sub_right, hxj, hyj, sub_self])
    set σ := inner ℝ (x - y) n / ‖n‖ ^ 2
    have hσ : |σ| * |inner ℝ (u a) n| ≤ t * sα / α a := by
      have : inner ℝ (u a) (x - y) = σ * inner ℝ (u a) n := by
        conv_lhs => rw [hd]
        rw [inner_smul_right]
      rw [← abs_mul, ← this, inner_sub_right, abs_le]
      constructor <;> linarith
    have hpos : 0 < |inner ℝ (u a) n| := abs_pos.2 hna
    rw [dist_eq_norm, hd, norm_smul, Real.norm_eq_abs]
    have : |σ| ≤ t * sα / α a / |inner ℝ (u a) n| := by rw [le_div_iff₀ hpos]; exact hσ
    calc |σ| * ‖n‖ ≤ t * sα / α a / |inner ℝ (u a) n| * ‖n‖ :=
          mul_le_mul_of_nonneg_right this (norm_nonneg _)
      _ = sα / α a / |inner ℝ (u a) n| * ‖n‖ * t := by ring
  · push_neg at hA
    -- all rays with positive coefficient lie in the plane of `u i, u j`: then `∑ α < 2`
    have hlt : sα < 2 := by
      obtain ⟨p, q, r, hpq, hpr, hqr, rfl⟩ := Finset.card_eq_three.1 (hfan.card _ hτ)
      have hp : p ∈ ({p, q, r} : Finset ι) := by simp
      have hq : q ∈ ({p, q, r} : Finset ι) := by simp
      have hr : r ∈ ({p, q, r} : Finset ι) := by simp
      have hsum : ∀ F : ι → Space3, ∑ m ∈ ({p, q, r} : Finset ι), F m = F p + F q + F r := by
        intro F
        rw [Finset.sum_insert (by simp [hpq, hpr]), Finset.sum_insert (by simp [hqr]),
          Finset.sum_singleton, add_assoc]
      have hsumR : sα = α p + α q + α r := by
        rw [hsα, Finset.sum_insert (by simp [hpq, hpr]), Finset.sum_insert (by simp [hqr]),
          Finset.sum_singleton, add_assoc]
      rw [hsum] at hz
      rw [hsumR]
      have two := fun {a b : ι} (ha : a ∈ ({p, q, r} : Finset ι)) (hb : b ∈ ({p, q, r} : Finset ι))
          (hab : a ≠ b) (hz' : u i + u j = α a • u a + α b • u b) =>
        hfan.two_term_lt_two hu hinj hused hτ hiS hjS hij hc hne ha hb hab hn0 hni hnj
          (hα a ha) (hα b hb) (hA a ha) (hA b hb) hz'
      by_cases hr0 : α r = 0
      · rw [hr0, zero_smul, add_zero] at hz
        have := two hp hq hpq hz; linarith
      by_cases hq0 : α q = 0
      · rw [hq0, zero_smul, add_zero] at hz
        have := two hp hr hpr hz; linarith
      by_cases hp0 : α p = 0
      · rw [hp0, zero_smul, zero_add] at hz
        have := two hq hr hqr hz; linarith
      exfalso
      have hpn := hA p hp (lt_of_le_of_ne (hα p hp) (Ne.symm hp0))
      have hqn := hA q hq (lt_of_le_of_ne (hα q hq) (Ne.symm hq0))
      have hrn := hA r hr (lt_of_le_of_ne (hα r hr) (Ne.symm hr0))
      exact hn0 (eq_zero_of_inner_three (hfan.indep_three hpq hpr hqr hτ) hpn hqn hrn)
    refine ⟨0, fun t ht x hx y _ => ?_⟩
    exfalso
    have h1 := hslack t x hx
    have h2 := Finset.sum_nonneg (hslack_nonneg t x hx)
    nlinarith

/-! ## Boundedness and presence of facets -/

/-- For a complete fan, every polyhedron `{x : ⟪u k, x⟫ ≤ h k}` is bounded. -/
lemma IsSimplicialFan.polyK_bounded (hfan : IsSimplicialFan S u T) (h : ι → ℝ) :
    Bornology.IsBounded (polyK S u h) := by
  choose τf hτf cf hcf hzf using fun y : Space3 => hfan.complete y
  set B : Space3 → ℝ := fun y => ∑ a ∈ τf y, cf y a * h a
  have hB : ∀ y, ∀ x ∈ polyK S u h, inner ℝ y x ≤ B y := by
    intro y x hx
    conv_lhs => rw [hzf y]
    rw [sum_inner]
    refine Finset.sum_le_sum fun a ha => ?_
    rw [inner_smul_left, RCLike.conj_to_real]
    exact mul_le_mul_of_nonneg_left (hx a (hfan.subset _ (hτf y) ha)) (hcf y a ha)
  set R : ℝ := ∑ m : Fin 3, (|B (EuclideanSpace.single m 1)| + |B (-EuclideanSpace.single m 1)|)
  have hcoord : ∀ x ∈ polyK S u h, ∀ m : Fin 3, |x m| ≤ R := by
    intro x hx m
    have h1 := hB (EuclideanSpace.single m 1) x hx
    have h2 := hB (-EuclideanSpace.single m 1) x hx
    rw [EuclideanSpace.inner_single_left] at h1
    rw [inner_neg_left, EuclideanSpace.inner_single_left] at h2
    simp only [map_one, one_mul] at h1 h2
    have hle : |B (EuclideanSpace.single m 1)| + |B (-EuclideanSpace.single m 1)| ≤ R :=
      Finset.single_le_sum (f := fun m : Fin 3 =>
        |B (EuclideanSpace.single m 1)| + |B (-EuclideanSpace.single m 1)|)
        (fun _ _ => by positivity) (Finset.mem_univ m)
    rw [abs_le]
    constructor
    · linarith [le_abs_self (B (-EuclideanSpace.single m 1)), abs_nonneg (B (EuclideanSpace.single m 1))]
    · linarith [le_abs_self (B (EuclideanSpace.single m 1)), abs_nonneg (B (-EuclideanSpace.single m 1))]
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨3 * R, fun x hx => ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hR : 0 ≤ R := le_trans (abs_nonneg _) (hcoord x hx 0)
  calc ‖x‖ = √(∑ m : Fin 3, ‖x m‖ ^ 2) := EuclideanSpace.norm_eq x
    _ ≤ √((3 * R) ^ 2) := by
        apply Real.sqrt_le_sqrt
        simp only [Fin.sum_univ_three, Real.norm_eq_abs]
        have h0 := hcoord x hx 0
        have h1 := hcoord x hx 1
        have h2 := hcoord x hx 2
        nlinarith [abs_nonneg (x 0), abs_nonneg (x 1), abs_nonneg (x 2), sq_abs (x 0),
          sq_abs (x 1), sq_abs (x 2)]
    _ = 3 * R := Real.sqrt_sq (by positivity)

/-- Distinct unit vectors have inner product `< 1`. -/
lemma inner_lt_one_of_ne {a b : Space3} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : a ≠ b) :
    inner ℝ a b < 1 := by
  have h1 := real_inner_le_norm a b
  rw [ha, hb, mul_one] at h1
  rcases lt_or_eq_of_le h1 with h | h
  · exact h
  · exfalso; apply hab
    have : ‖a - b‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right,
        real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_comm a b, h, ha, hb]
      ring
    exact sub_eq_zero.1 (norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 this))

/-- **Step (d): every facet of the shifted polytope is present.**  If `w` is tight on `u i`,
then `w + t u i` strictly satisfies every other shifted inequality. -/
lemma facetsPresent_shift (hu : ∀ i ∈ S, ‖u i‖ = 1)
    (hinj : ∀ i ∈ S, ∀ j ∈ S, u i = u j → i = j) (hused : ∀ i ∈ S, ∃ τ ∈ T, i ∈ τ)
    {g : Finset ι → Space3} {h : ι → ℝ}
    (htight : ∀ τ ∈ T, ∀ k ∈ τ, inner ℝ (u k) (g τ) = h k)
    (hle : ∀ τ ∈ T, ∀ k ∈ S, inner ℝ (u k) (g τ) ≤ h k) {t : ℝ} (ht : 0 < t) :
    FacetsPresent S u (fun k => h k + t) := by
  intro i hi
  obtain ⟨τ, hτ, hiτ⟩ := hused i hi
  refine ⟨g τ + t • u i, ?_, fun k hk hki => ?_⟩
  · rw [inner_add_right, inner_smul_right, htight τ hτ i hiτ, real_inner_self_eq_norm_sq,
      hu i hi]; ring
  · have h1 := inner_lt_one_of_ne (hu k hk) (hu i hi) fun e => hki (hinj k hk i hi e)
    rw [inner_add_right, inner_smul_right]
    have := hle τ hτ k hk
    nlinarith

/-! ## Convergence of the Hessian entries -/

/-- **Support data integrating a fan matrix** (output of steps (b), (c) of the Guide): a point
`g τ` for every cone `τ` (the gradient of the convex piecewise-linear support function on `τ`)
and support numbers `h`, tight on the rays of `τ`, satisfying all the inequalities, and with
jumps `‖g τ - g τ'‖ = -W i j |u i × u j|` across every common edge `ij` of two distinct cones. -/
structure FanSupport (S : Finset ι) (u : ι → Space3) (T : Finset (Finset ι)) (W : ι → ι → ℝ)
    (g : Finset ι → Space3) (h : ι → ℝ) : Prop where
  tight : ∀ τ ∈ T, ∀ k ∈ τ, inner ℝ (u k) (g τ) = h k
  le : ∀ τ ∈ T, ∀ k ∈ S, inner ℝ (u k) (g τ) ≤ h k
  jump : ∀ τ ∈ T, ∀ τ' ∈ T, τ ≠ τ' → ∀ i ∈ τ, ∀ j ∈ τ, i ≠ j → i ∈ τ' → j ∈ τ' →
    ‖g τ - g τ'‖ = -W i j * √(1 - inner ℝ (u i) (u j) ^ 2)

/-- A squeeze for limits from the right at `0`. -/
lemma tendsto_of_bounds {f : ℝ → ℝ} {L C : ℝ} (hup : ∀ t, 0 < t → f t ≤ L + C * t)
    (hlow : ∀ δ > 0, ∀ᶠ t in 𝓝[>] (0 : ℝ), L - δ ≤ f t) :
    Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < ε / (|C| + 1) :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by positivity))
  filter_upwards [hlow (ε / 2) (by positivity), h1, self_mem_nhdsWithin] with t ht1 ht2 ht3
  have ht3' : (0:ℝ) < t := ht3
  rw [Real.dist_eq, abs_lt]
  have hCt : C * t ≤ |C| * t := mul_le_mul_of_nonneg_right (le_abs_self C) ht3'.le
  have : |C| * t < ε := by
    rw [lt_div_iff₀ (by positivity)] at ht2
    nlinarith [abs_nonneg C]
  constructor
  · linarith
  · linarith [hup t ht3']

/-- **Fan edges.**  Across an edge `ij` of the fan, the length of the common edge of the facets
`i, j` of the shifted polytope tends to `-W i j |u i × u j|` as `t → 0⁺`. -/
lemma IsSimplicialFan.edge_diam_tendsto (hfan : IsSimplicialFan S u T)
    (hu : ∀ i ∈ S, ‖u i‖ = 1) (hused : ∀ i ∈ S, ∃ τ ∈ T, i ∈ τ)
    {W : ι → ι → ℝ} {g : Finset ι → Space3} {h : ι → ℝ} (hs : FanSupport S u T W g h)
    {i j : ι} (hiS : i ∈ S) (hjS : j ∈ S) (hij : i ≠ j) (hc : inner ℝ (u i) (u j) ^ 2 < 1)
    (hE : FanEdge T i j) :
    Tendsto (fun t => Metric.diam (polyFacet S u (fun k => h k + t) i ∩
      polyFacet S u (fun k => h k + t) j)) (𝓝[>] (0 : ℝ))
      (𝓝 (-W i j * √(1 - inner ℝ (u i) (u j) ^ 2))) := by
  obtain ⟨_, τ, hτ, hiτ, hjτ⟩ := hE
  have hijτ : ({i, j} : Finset ι) ⊆ τ := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hcard : (τ \ {i, j}).card = 1 := by
    rw [Finset.card_sdiff_of_subset hijτ, hfan.card τ hτ, Finset.card_pair hij]
  obtain ⟨a, ha⟩ := Finset.card_pos.1 (by rw [hcard]; norm_num)
  rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at ha
  obtain ⟨haτ, hane⟩ := ha
  push_neg at hane
  obtain ⟨hai, haj⟩ := hane
  have haS := hfan.subset τ hτ haτ
  obtain ⟨n₀, hn₀, hni₀, hnj₀⟩ := exists_orth_pair (u i) (u j)
  rw [real_inner_comm] at hni₀ hnj₀
  have hna₀ : inner ℝ (u a) n₀ ≠ 0 := by
    intro h0
    obtain ⟨α, β, hab⟩ := eq_comb_of_inner_normal (hu i hiS) (hu j hjS) hc hn₀ hni₀ hnj₀ h0
    have := hfan.coeff_eq_zero hτ (fun m => ((if m = a then 1 else 0) - if m = i then α else 0) -
      if m = j then β else 0) (by
        simp only [sub_smul, Finset.sum_sub_distrib]
        rw [sum_single_smul u haτ, sum_single_smul u hiτ, sum_single_smul u hjτ, one_smul, hab]
        abel) a haτ
    simp [hai, haj] at this
  obtain ⟨n, hn0, hni, hnj, hna⟩ : ∃ n : Space3, n ≠ 0 ∧ inner ℝ (u i) n = 0 ∧
      inner ℝ (u j) n = 0 ∧ 0 < inner ℝ (u a) n := by
    rcases lt_or_gt_of_ne hna₀ with h0 | h0
    · exact ⟨-n₀, neg_ne_zero.2 hn₀, by rw [inner_neg_right, hni₀, neg_zero],
        by rw [inner_neg_right, hnj₀, neg_zero], by rw [inner_neg_right]; linarith⟩
    · exact ⟨n₀, hn₀, hni₀, hnj₀, h0⟩
  obtain ⟨τ', hτ', hiτ', hjτ', b, hbτ', hnb⟩ := hfan.exists_cone_other_side hτ hiτ hjτ hij hn0 hni hnj
  have hbS := hfan.subset τ' hτ' hbτ'
  have hττ' : τ ≠ τ' := by
    intro heq
    subst heq
    have hbi : b ≠ i := by rintro rfl; linarith
    have hbj : b ≠ j := by rintro rfl; linarith
    have hba : b ≠ a := by rintro rfl; linarith
    have h4 : ({i, j, a, b} : Finset ι) ⊆ τ := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
    have := Finset.card_le_card h4
    rw [hfan.card τ hτ, Finset.card_insert_of_notMem (by simp [hij, hai.symm, hbi.symm]),
      Finset.card_insert_of_notMem (by simp [haj.symm, hbj.symm]),
      Finset.card_pair hba.symm] at this
    omega
  have hL := hs.jump τ hτ τ' hτ' hττ' i hiτ j hjτ hij hiτ' hjτ'
  rw [← hL]
  set L := ‖g τ - g τ'‖
  set C := ((1 - inner ℝ (u a) ((1 + inner ℝ (u i) (u j))⁻¹ • (u i + u j))) / inner ℝ (u a) n -
    (1 - inner ℝ (u b) ((1 + inner ℝ (u i) (u j))⁻¹ • (u i + u j))) / inner ℝ (u b) n) * ‖n‖
  have hdist : ∀ t : ℝ, 0 ≤ t → ∀ x ∈ polyFacet S u (fun k => h k + t) i ∩
      polyFacet S u (fun k => h k + t) j, ∀ y ∈ polyFacet S u (fun k => h k + t) i ∩
      polyFacet S u (fun k => h k + t) j, dist x y ≤ L + |C| * t := by
    intro t ht x ⟨⟨hxK, hxi⟩, ⟨_, hxj⟩⟩ y ⟨⟨hyK, hyi⟩, ⟨_, hyj⟩⟩
    have hxa := hxK a haS
    have hxb := hxK b hbS
    have hya := hyK a haS
    have hyb := hyK b hbS
    simp only at hxi hxj hyi hyj hxa hxb hya hyb
    have := edge_dist_le (hu i hiS) (hu j hjS) hc hn0 hni hnj hna hnb
      (hs.tight τ hτ i hiτ) (hs.tight τ' hτ' i hiτ') (hs.tight τ hτ j hjτ)
      (hs.tight τ' hτ' j hjτ') (hs.tight τ hτ a haτ) (hs.le τ' hτ' a haS)
      (hs.tight τ' hτ' b hbτ') hxi hxj hxa hxb hyi hyj hya hyb
    have : t * C ≤ |C| * t := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right (le_abs_self C) ht
    linarith
  have hup : ∀ t, 0 < t → Metric.diam (polyFacet S u (fun k => h k + t) i ∩
      polyFacet S u (fun k => h k + t) j) ≤ L + |C| * t := fun t ht =>
    Metric.diam_le_of_forall_dist_le (by positivity) (hdist t ht.le)
  refine tendsto_of_bounds hup fun δ hδ => ?_
  by_cases hLδ : L ≤ δ
  · exact Filter.Eventually.of_forall fun t =>
      le_trans (by linarith : L - δ ≤ 0) Metric.diam_nonneg
  push_neg at hLδ
  have hLpos : 0 < L := hδ.trans hLδ
  have hne : g τ ≠ g τ' := fun e => by simp [L, e] at hLpos
  have hcone : ∀ k ∈ S, k ≠ i → k ≠ j → ∀ α β : ℝ, u k = α • u i + β • u j →
      ¬ (0 ≤ α ∧ 0 ≤ β) := by
    intro k hk hki hkj α β hab ⟨hα, hβ⟩
    refine hfan.ray_not_mem_finCone (hused k hk) hτ hijτ (by simp [hki, hkj])
      ⟨fun x => if x = i then α else β, fun x _ => by dsimp only; split_ifs <;> assumption, ?_⟩
    rw [Finset.sum_pair hij]; simpa [hij.symm] using hab
  set l₁ := δ / (2 * L)
  have hl₁ : 0 < l₁ := by positivity
  have hl₁' : l₁ < 1 / 2 := by
    rw [div_lt_iff₀ (by positivity)]; linarith
  have ev1 := edge_point_eventually hu hiS hjS hc hcone hne (fun k hk => hs.le τ hτ k hk)
    (fun k hk => hs.le τ' hτ' k hk) (hs.tight τ hτ i hiτ) (hs.tight τ' hτ' i hiτ')
    (hs.tight τ hτ j hjτ) (hs.tight τ' hτ' j hjτ') hl₁ (by linarith)
  have ev2 := edge_point_eventually hu hiS hjS hc hcone hne (fun k hk => hs.le τ hτ k hk)
    (fun k hk => hs.le τ' hτ' k hk) (hs.tight τ hτ i hiτ) (hs.tight τ' hτ' i hiτ')
    (hs.tight τ hτ j hjτ) (hs.tight τ' hτ' j hjτ') (lam := 1 - l₁) (by linarith) (by linarith)
  filter_upwards [ev1, ev2, self_mem_nhdsWithin] with t h1 h2 (ht : 0 < t)
  have hbdd : Bornology.IsBounded (polyFacet S u (fun k => h k + t) i ∩
      polyFacet S u (fun k => h k + t) j) :=
    Metric.isBounded_iff.2 ⟨_, hdist t ht.le⟩
  have hd := Metric.dist_le_diam_of_mem hbdd h1 h2
  have hcalc : dist (g τ + l₁ • (g τ' - g τ) +
      t • ((1 + inner ℝ (u i) (u j))⁻¹ • (u i + u j)))
      (g τ + (1 - l₁) • (g τ' - g τ) + t • ((1 + inner ℝ (u i) (u j))⁻¹ • (u i + u j))) =
      (1 - 2 * l₁) * L := by
    rw [dist_eq_norm]
    have : g τ + l₁ • (g τ' - g τ) + t • ((1 + inner ℝ (u i) (u j))⁻¹ • (u i + u j)) -
        (g τ + (1 - l₁) • (g τ' - g τ) + t • ((1 + inner ℝ (u i) (u j))⁻¹ • (u i + u j))) =
        (1 - 2 * l₁) • (g τ - g τ') := by module
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have : (1 - 2 * l₁) * L = L - δ := by
    simp only [l₁]; field_simp
  linarith

/-- The off-diagonal entries of the shifted polytope Hessians, divided by `|u i × u j|`,
converge to `-W i j`. -/
lemma IsSimplicialFan.diam_div_tendsto (hfan : IsSimplicialFan S u T)
    (hu : ∀ i ∈ S, ‖u i‖ = 1) (hinj : ∀ i ∈ S, ∀ j ∈ S, u i = u j → i = j)
    (hused : ∀ i ∈ S, ∃ τ ∈ T, i ∈ τ) {W : ι → ι → ℝ}
    (hsupp : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → W i j ≠ 0 → FanEdge T i j)
    {g : Finset ι → Space3} {h : ι → ℝ} (hs : FanSupport S u T W g h)
    {i j : ι} (hiS : i ∈ S) (hjS : j ∈ S) (hij : i ≠ j) :
    Tendsto (fun t => Metric.diam (polyFacet S u (fun k => h k + t) i ∩
      polyFacet S u (fun k => h k + t) j) / √(1 - inner ℝ (u i) (u j) ^ 2)) (𝓝[>] (0 : ℝ))
      (𝓝 (-W i j)) := by
  by_cases hc : inner ℝ (u i) (u j) ^ 2 < 1
  · have hs0 : 0 < √(1 - inner ℝ (u i) (u j) ^ 2) := Real.sqrt_pos.2 (by linarith)
    have hlim : Tendsto (fun t => Metric.diam (polyFacet S u (fun k => h k + t) i ∩
        polyFacet S u (fun k => h k + t) j)) (𝓝[>] (0 : ℝ))
        (𝓝 (-W i j * √(1 - inner ℝ (u i) (u j) ^ 2))) := by
      by_cases hE : FanEdge T i j
      · exact hfan.edge_diam_tendsto hu hused hs hiS hjS hij hc hE
      · have hW : W i j = 0 := by
          by_contra h0; exact hE (hsupp i hiS j hjS hij h0)
        rw [hW, neg_zero, zero_mul]
        obtain ⟨C, hC⟩ := hfan.nonedge_dist_le hu hinj hused hs.tight hs.le hiS hjS hij hc hE
        refine tendsto_of_bounds (C := |C|) (fun t ht => ?_) fun δ hδ =>
          Filter.Eventually.of_forall fun t =>
            le_trans (by linarith : (0:ℝ) - δ ≤ 0) Metric.diam_nonneg
        rw [zero_add]
        exact Metric.diam_le_of_forall_dist_le (by positivity) fun x hx y hy =>
          (hC t ht x hx y hy).trans (mul_le_mul_of_nonneg_right (le_abs_self C) ht.le)
    have := hlim.div_const (√(1 - inner ℝ (u i) (u j) ^ 2))
    rwa [mul_div_assoc, div_self hs0.ne', mul_one] at this
  · have hW : W i j = 0 := by
      by_contra h0
      obtain ⟨_, τ, hτ, hiτ, hjτ⟩ := hsupp i hiS j hjS hij h0
      exact hc (hfan.inner_sq_lt_one hu hτ hiτ hjτ hij)
    have : √(1 - inner ℝ (u i) (u j) ^ 2) = 0 := Real.sqrt_eq_zero'.2 (by push_neg at hc; linarith)
    simp only [this, div_zero, hW, neg_zero]
    exact tendsto_const_nhds

/-- **Steps (d) and (f) of the Guide: approximation of a fan matrix by polytope Hessians.**
Given support data integrating `W` (`FanSupport`), the shifted polytopes
`K_t = {x : ⟪u k, x⟫ ≤ h k + t}` are bounded, have all facets present, and for small `t > 0`
their minus volume Hessians are entrywise within `ε` of `W`. -/
theorem IsSimplicialFan.matrix_approx_of_support (hfan : IsSimplicialFan S u T)
    (hu : ∀ i ∈ S, ‖u i‖ = 1) (hinj : ∀ i ∈ S, ∀ j ∈ S, u i = u j → i = j)
    (hused : ∀ i ∈ S, ∃ τ ∈ T, i ∈ τ) {W : ι → ι → ℝ}
    (hsupp : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → W i j ≠ 0 → FanEdge T i j)
    (hker : ∀ i ∈ S, ∑ j ∈ S, W i j • u j = 0)
    {g : Finset ι → Space3} {h : ι → ℝ} (hs : FanSupport S u T W g h) :
    ∀ ε > 0, ∃ h' : ι → ℝ, Bornology.IsBounded (polyK S u h') ∧ FacetsPresent S u h' ∧
      ∀ i ∈ S, ∀ j ∈ S, |polytopeHessian S u h' i j - W i j| < ε := by
  intro ε hε
  have hent : ∀ i ∈ S, ∀ j ∈ S, Tendsto (fun t => polytopeHessian S u (fun k => h k + t) i j)
      (𝓝[>] (0 : ℝ)) (𝓝 (W i j)) := by
    intro i hi j hj
    by_cases hij : i = j
    · subst hij
      have hdiag : W i i = ∑ k ∈ S.erase i, -W i k * inner ℝ (u i) (u k) := by
        have h1 := congrArg (fun v => inner ℝ (u i) v) (hker i hi)
        simp only [inner_sum, inner_smul_right, inner_zero_right] at h1
        rw [← Finset.add_sum_erase S _ hi, real_inner_self_eq_norm_sq, hu i hi] at h1
        have : ∑ k ∈ S.erase i, -W i k * inner ℝ (u i) (u k) =
            -∑ k ∈ S.erase i, W i k * inner ℝ (u i) (u k) := by
          rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun k _ => by ring
        rw [this]; linarith
      rw [hdiag]
      simp only [polytopeHessian]
      refine tendsto_finset_sum _ fun k hk => ?_
      exact (hfan.diam_div_tendsto hu hinj hused hsupp hs hi (Finset.mem_of_mem_erase hk)
        (Finset.ne_of_mem_erase hk).symm).mul_const _
    · simp only [polytopeHessian, if_neg hij]
      have := (hfan.diam_div_tendsto hu hinj hused hsupp hs hi hj hij).neg
      rwa [neg_neg] at this
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ ∀ i ∈ S, ∀ j ∈ S,
      |polytopeHessian S u (fun k => h k + t) i j - W i j| < ε := by
    refine (eventually_mem_nhdsWithin).and ?_
    rw [Filter.eventually_all_finset]
    intro i hi
    rw [Filter.eventually_all_finset]
    intro j hj
    exact (Metric.tendsto_nhds.1 (hent i hi j hj) ε hε).mono fun t ht => by
      rwa [Real.dist_eq] at ht
  obtain ⟨t, ht, hall⟩ := hev.exists
  exact ⟨_, hfan.polyK_bounded _, facetsPresent_shift hu hinj hused hs.tight hs.le ht, hall⟩

end Erdos99
end

end FanApprox

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `FanConvexity`
-/

section FanConvexity

/-!
# Convexity of the integrated fan function (Verification Guide §7.3 (c))

Let `T` be a complete simplicial fan with unit rays `u` and `W` a fan matrix with nonpositive
off-diagonal entries.  Suppose the gradient jumps `-W i j (u i × u j)` have been integrated to
gradients `g τ` (one per cone), i.e. (`FanGradient`):

* `⟪u k, g τ⟫ = ⟪u k, g τ'⟫` whenever `k ∈ τ ∩ τ'` (the piecewise-linear function `H` with gradient
  `g τ` on the cone `τ` is well defined), and
* `g τ' - g τ = -W i j • (u i × u j)`, oriented towards `τ'`, whenever the distinct cones `τ, τ'`
  share the edge `ij`.

Then `H` is convex, and in particular `⟪u k, g τ⟫ ≤ H(u k)` for every cone `τ` and ray `k`
(`FanGradient.inner_le`).  Together with the norm of the jumps this gives the support data
`FanSupport` used in `FanApprox` (`FanGradient.fanSupport`).

The proof of convexity is local-to-global along segments:
* near a point `x` that is not on a line through a ray, `H` is the maximum of the linear
  functions `⟪g ρ, ·⟫` over the cones `ρ ∋ x` (`FanGradient.local_max`), because two such cones
  share an edge and the jump across it is oriented;
* a segment from a generic interior point of `τ` to `u k` meets no line through a ray except at its
  endpoint (`exists_generic_start`);
* a continuous function on an interval which is locally convex, and vanishes near the left end,
  is nonnegative (`nonneg_of_locally_convex`).
-/

open scoped BigOperators
open Filter Topology

@[expose] public noncomputable section

open Classical

namespace Erdos99

variable {ι : Type*}

/-! ## The cross product -/

/-- The cross product in `ℝ³`. -/
def cross3 (a b : Space3) : Space3 :=
  !₂[a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]

/-- The cross product `a × b`, or `b × a`, whichever has positive inner product with `c`
(the normal of the plane of `a, b` pointing towards `c`). -/
def orientedCross (a b c : Space3) : Space3 :=
  if 0 < vol3 a b c then cross3 a b else cross3 b a

lemma cross3_apply_zero (a b : Space3) : cross3 a b 0 = a 1 * b 2 - a 2 * b 1 := by
  simp [cross3]

lemma cross3_apply_one (a b : Space3) : cross3 a b 1 = a 2 * b 0 - a 0 * b 2 := by
  simp [cross3]

lemma cross3_apply_two (a b : Space3) : cross3 a b 2 = a 0 * b 1 - a 1 * b 0 := by
  simp [cross3]

lemma inner_eq_coords (a b : Space3) : inner ℝ a b = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]; ring

lemma inner_cross3 (a b c : Space3) : inner ℝ (cross3 a b) c = vol3 a b c := by
  simp only [inner_eq_coords, cross3_apply_zero, cross3_apply_one, cross3_apply_two, vol3]; ring

lemma inner_cross3_left (a b : Space3) : inner ℝ (cross3 a b) a = 0 := by
  simp only [inner_eq_coords, cross3_apply_zero, cross3_apply_one, cross3_apply_two]; ring

lemma inner_cross3_right (a b : Space3) : inner ℝ (cross3 a b) b = 0 := by
  simp only [inner_eq_coords, cross3_apply_zero, cross3_apply_one, cross3_apply_two]; ring

lemma norm_cross3_sq (a b : Space3) : ‖cross3 a b‖ ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 - inner ℝ a b ^ 2 := by
  rw [← real_inner_self_eq_norm_sq (cross3 a b), ← real_inner_self_eq_norm_sq a,
    ← real_inner_self_eq_norm_sq b]
  simp only [inner_eq_coords, cross3_apply_zero, cross3_apply_one, cross3_apply_two]; ring

lemma cross3_swap (a b : Space3) : cross3 b a = -cross3 a b := by
  ext i; fin_cases i <;> simp [cross3] <;> ring

lemma inner_orientedCross_nonneg (a b c : Space3) : 0 ≤ inner ℝ (orientedCross a b c) c := by
  unfold orientedCross
  split_ifs with h
  · rw [inner_cross3]; exact h.le
  · rw [cross3_swap, inner_neg_left, inner_cross3]; linarith

lemma inner_orientedCross_left (a b c : Space3) : inner ℝ (orientedCross a b c) a = 0 := by
  unfold orientedCross
  split_ifs
  · exact inner_cross3_left a b
  · exact inner_cross3_right b a

lemma inner_orientedCross_right (a b c : Space3) : inner ℝ (orientedCross a b c) b = 0 := by
  unfold orientedCross
  split_ifs
  · exact inner_cross3_right a b
  · exact inner_cross3_left b a

lemma norm_cross3 {a b : Space3} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ‖cross3 a b‖ = √(1 - inner ℝ a b ^ 2) := by
  rw [← Real.sqrt_sq (norm_nonneg (cross3 a b)), norm_cross3_sq, ha, hb]; ring_nf

lemma norm_orientedCross {a b : Space3} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (c : Space3) :
    ‖orientedCross a b c‖ = √(1 - inner ℝ a b ^ 2) := by
  unfold orientedCross
  split_ifs
  · exact norm_cross3 ha hb
  · rw [cross3_swap, norm_neg]; exact norm_cross3 ha hb

/-! ## Integrated gradients -/

/-- **Integrated gradients of a fan matrix**: a gradient `g τ` for every cone, continuous across
common rays, with jump `-W i j • (u i × u j)` (oriented towards the second cone) across every
common edge. -/
structure FanGradient (T : Finset (Finset ι)) (u : ι → Space3) (W : ι → ι → ℝ)
    (g : Finset ι → Space3) : Prop where
  cont : ∀ τ ∈ T, ∀ τ' ∈ T, ∀ k ∈ τ, k ∈ τ' → inner ℝ (u k) (g τ) = inner ℝ (u k) (g τ')
  jump : ∀ τ ∈ T, ∀ τ' ∈ T, τ ≠ τ' → ∀ i ∈ τ, ∀ j ∈ τ, i ≠ j → i ∈ τ' → j ∈ τ' →
    ∀ b ∈ τ', b ≠ i → b ≠ j → g τ' - g τ = (-W i j) • orientedCross (u i) (u j) (u b)

variable {S : Finset ι} {u : ι → Space3} {T : Finset (Finset ι)} {W : ι → ι → ℝ}
  {g : Finset ι → Space3}

/-- The piecewise-linear function with gradient `g ρ` on the cone `ρ`. -/
def fanFun (T : Finset (Finset ι)) (u : ι → Space3) (g : Finset ι → Space3) (x : Space3) : ℝ :=
  if h : ∃ ρ ∈ T, x ∈ finCone u ρ then inner ℝ (g h.choose) x else 0

lemma FanGradient.fanFun_eq (hfan : IsSimplicialFan S u T) (hg : FanGradient T u W g)
    {ρ : Finset ι} (hρ : ρ ∈ T) {x : Space3} (hx : x ∈ finCone u ρ) :
    fanFun T u g x = inner ℝ (g ρ) x := by
  have hex : ∃ ρ ∈ T, x ∈ finCone u ρ := ⟨ρ, hρ, hx⟩
  unfold fanFun
  rw [dif_pos hex]
  obtain ⟨hσ, hxσ⟩ := hex.choose_spec
  set σ := hex.choose
  have hI : x ∈ finCone u (σ ∩ ρ) := by rw [← hfan.inter σ hσ ρ hρ]; exact ⟨hxσ, hx⟩
  obtain ⟨c, -, hc⟩ := hI
  rw [hc, inner_sum, inner_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_inter] at hk
  rw [inner_smul_right, inner_smul_right, real_inner_comm, hg.cont σ hσ ρ hρ k hk.1 hk.2,
    real_inner_comm]

/-- A point not on any line through a ray (in particular nonzero). -/
def FanGeneric (S : Finset ι) (u : ι → Space3) (x : Space3) : Prop :=
  x ≠ 0 ∧ ∀ m ∈ S, ∀ s : ℝ, x ≠ s • u m

/-- Two cones containing a generic point share an edge. -/
lemma IsSimplicialFan.edge_of_generic (hfan : IsSimplicialFan S u T) {ρ ρ' : Finset ι}
    (hρ : ρ ∈ T) (hρ' : ρ' ∈ T) {x : Space3} (hx : FanGeneric S u x) (hxρ : x ∈ finCone u ρ)
    (hxρ' : x ∈ finCone u ρ') : ∃ i ∈ ρ ∩ ρ', ∃ j ∈ ρ ∩ ρ', i ≠ j := by
  have hI : x ∈ finCone u (ρ ∩ ρ') := by rw [← hfan.inter ρ hρ ρ' hρ']; exact ⟨hxρ, hxρ'⟩
  obtain ⟨c, -, hc⟩ := hI
  by_contra hcon
  push_neg at hcon
  rcases (ρ ∩ ρ').eq_empty_or_nonempty with h0 | ⟨m, hm⟩
  · rw [h0, Finset.sum_empty] at hc; exact hx.1 hc
  · have h1 : ρ ∩ ρ' = {m} := Finset.eq_singleton_iff_unique_mem.2 ⟨hm, fun a ha => hcon a ha m hm⟩
    rw [h1, Finset.sum_singleton] at hc
    exact hx.2 m (hfan.subset ρ hρ (Finset.mem_inter.1 hm).1) (c m) hc

/-- Across a common edge, the gradient of a cone dominates the other gradient on the cone. -/
lemma FanGradient.inner_le_of_edge (hfan : IsSimplicialFan S u T) (hg : FanGradient T u W g)
    (hneg : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → W i j ≤ 0) {ρ ρ' : Finset ι} (hρ : ρ ∈ T) (hρ' : ρ' ∈ T)
    {i j : ι} (hi : i ∈ ρ ∩ ρ') (hj : j ∈ ρ ∩ ρ') (hij : i ≠ j) {y : Space3}
    (hy : y ∈ finCone u ρ) : inner ℝ (g ρ') y ≤ inner ℝ (g ρ) y := by
  by_cases hrr : ρ' = ρ
  · rw [hrr]
  rw [Finset.mem_inter] at hi hj
  obtain ⟨c, hc0, hc⟩ := hy
  rw [← sub_nonneg, ← inner_sub_left, hc, inner_sum]
  refine Finset.sum_nonneg fun m hm => ?_
  rw [inner_smul_right]
  refine mul_nonneg (hc0 m hm) ?_
  by_cases hmi : m = i
  · subst hmi
    rw [inner_sub_left, real_inner_comm, hg.cont ρ hρ ρ' hρ' m hi.1 hi.2, real_inner_comm,
      sub_self]
  by_cases hmj : m = j
  · subst hmj
    rw [inner_sub_left, real_inner_comm, hg.cont ρ hρ ρ' hρ' m hj.1 hj.2, real_inner_comm,
      sub_self]
  rw [hg.jump ρ' hρ' ρ hρ hrr i hi.2 j hj.2 hij hi.1 hj.1 m hm hmi hmj, inner_smul_left]
  have hW := hneg i (hfan.subset ρ hρ hi.1) j (hfan.subset ρ hρ hj.1) hij
  have := inner_orientedCross_nonneg (u i) (u j) (u m)
  simp only [RCLike.conj_to_real]
  nlinarith

/-- **Local structure.**  Near a generic point `x`, the fan function is the maximum of the linear
functions `⟪g ρ, ·⟫` over the cones `ρ` containing `x`. -/
lemma FanGradient.local_max (hfan : IsSimplicialFan S u T) (hg : FanGradient T u W g)
    (hneg : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → W i j ≤ 0) {x : Space3} (hx : FanGeneric S u x) :
    ∃ r > 0, ∃ F ⊆ T, ∀ y : Space3, dist y x < r →
      (∀ ρ ∈ F, inner ℝ (g ρ) y ≤ fanFun T u g y) ∧ ∃ ρ ∈ F, fanFun T u g y = inner ℝ (g ρ) y := by
  set F := T.filter (fun ρ => x ∈ finCone u ρ)
  have hU : IsOpen (⋂ ρ ∈ T.filter (fun ρ => x ∉ finCone u ρ), (finCone u ρ)ᶜ) :=
    isOpen_biInter_finset fun ρ _ => (isClosed_finCone u ρ).isOpen_compl
  have hxU : x ∈ ⋂ ρ ∈ T.filter (fun ρ => x ∉ finCone u ρ), (finCone u ρ)ᶜ := by
    simp only [Set.mem_iInter, Set.mem_compl_iff]
    intro ρ hρ
    exact (Finset.mem_filter.1 hρ).2
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU x hxU
  refine ⟨r, hr, F, Finset.filter_subset _ _, fun y hy => ?_⟩
  obtain ⟨ρ, hρ, hyρ⟩ := hfan.complete y
  have hρF : ρ ∈ F := by
    rw [Finset.mem_filter]
    refine ⟨hρ, by_contra fun hxρ => ?_⟩
    have := hball (Metric.mem_ball.2 hy)
    simp only [Set.mem_iInter, Set.mem_compl_iff] at this
    exact this ρ (Finset.mem_filter.2 ⟨hρ, hxρ⟩) hyρ
  have hH := hg.fanFun_eq hfan hρ hyρ
  refine ⟨fun ρ' hρ' => ?_, ρ, hρF, hH⟩
  rw [hH]
  obtain ⟨hρ'T, hxρ'⟩ := Finset.mem_filter.1 hρ'
  obtain ⟨i, hi, j, hj, hij⟩ :=
    hfan.edge_of_generic hρ hρ'T hx (Finset.mem_filter.1 hρF).2 hxρ'
  exact hg.inner_le_of_edge hfan hneg hρ hρ'T hi hj hij hyρ

/-- Near a generic point the fan function is convex. -/
lemma FanGradient.locally_convex (hfan : IsSimplicialFan S u T) (hg : FanGradient T u W g)
    (hneg : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → W i j ≤ 0) {x : Space3} (hx : FanGeneric S u x) :
    ∃ r > 0, ConvexOn ℝ (Metric.ball x r) (fanFun T u g) := by
  obtain ⟨r, hr, F, -, hF⟩ := hg.local_max hfan hneg hx
  refine ⟨r, hr, convex_ball x r, fun y hy z hz a b ha hb hab => ?_⟩
  have hyz : a • y + b • z ∈ Metric.ball x r := convex_ball x r hy hz ha hb hab
  obtain ⟨ρ, hρ, hval⟩ := (hF _ (Metric.mem_ball.1 hyz)).2
  rw [hval, inner_add_right, inner_smul_right, inner_smul_right]
  have h1 := (hF y (Metric.mem_ball.1 hy)).1 ρ hρ
  have h2 := (hF z (Metric.mem_ball.1 hz)).1 ρ hρ
  simp only [smul_eq_mul]
  nlinarith

/-! ## One-dimensional local-to-global convexity -/

/-- A function on `(0, 1)` which is locally convex and vanishes near `0` is nonnegative. -/
lemma nonneg_of_locally_convex {φ : ℝ → ℝ}
    (hloc : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∃ ε > 0, ConvexOn ℝ (Set.Ioo (t - ε) (t + ε)) φ)
    {δ : ℝ} (hδ : 0 < δ) (hzero : ∀ t ∈ Set.Ioo (0 : ℝ) δ, φ t = 0) :
    ∀ t ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ φ t := by
  have hcont : ContinuousOn φ (Set.Ioo 0 1) := by
    intro t ht
    obtain ⟨ε, hε, hc⟩ := hloc t ht
    have h1 := hc.continuousOn_interior
    rw [interior_Ioo] at h1
    exact ((h1 t ⟨by linarith, by linarith⟩).continuousAt
      (Ioo_mem_nhds (by linarith) (by linarith))).continuousWithinAt
  intro t1 ht1
  by_contra hneg
  push_neg at hneg
  obtain ⟨ht10, ht11⟩ := ht1
  set m := min δ t1 with hm
  have hm0 : 0 < m := lt_min hδ ht10
  have hmδ : m ≤ δ := min_le_left _ _
  have hmt : m ≤ t1 := min_le_right _ _
  set a := m / 3 with ha
  set b := 2 * m / 3 with hb
  have hat : a < t1 := by linarith
  set ψ : ℝ → ℝ := fun t => φ t - φ t1 * (t - a) / (t1 - a) with hψ
  have hsub : Set.Icc a t1 ⊆ Set.Ioo 0 1 := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hψc : ContinuousOn ψ (Set.Icc a t1) := by
    refine ((hcont.mono hsub).sub ?_)
    exact (continuousOn_const.mul (continuousOn_id.sub continuousOn_const)).div continuousOn_const
      fun _ _ => by linarith
  have hψa : ψ a = 0 := by
    simp only [hψ, sub_self, mul_zero, zero_div, sub_zero]
    exact hzero a ⟨by positivity, by linarith⟩
  have hψt : ψ t1 = 0 := by
    simp only [hψ]
    rw [mul_div_assoc, div_self (by linarith), mul_one, sub_self]
  have hψb : 0 < ψ b := by
    simp only [hψ]
    rw [hzero b ⟨by positivity, by linarith⟩, zero_sub, neg_pos]
    apply div_neg_of_neg_of_pos _ (by linarith)
    exact mul_neg_of_neg_of_pos hneg (by linarith)
  obtain ⟨c, hc, hcmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 hat.le) hψc
  set M := ψ c
  have hbI : b ∈ Set.Icc a t1 := ⟨by linarith, by linarith⟩
  have hMpos : 0 < M := lt_of_lt_of_le hψb (hcmax hbI)
  set A := Set.Icc a t1 ∩ ψ ⁻¹' {M} with hA
  have hAc : IsClosed A := hψc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hAne : A.Nonempty := ⟨c, hc, rfl⟩
  have hAbdd : BddBelow A := ⟨a, fun t ht => ht.1.1⟩
  set m0 := sInf A
  have hm0A : m0 ∈ A := hAc.csInf_mem hAne hAbdd
  have hm0M : ψ m0 = M := hm0A.2
  have hm0a : a < m0 := by
    rcases eq_or_lt_of_le hm0A.1.1 with h | h
    · rw [← h, hψa] at hm0M; linarith
    · exact h
  have hm0t : m0 < t1 := by
    rcases eq_or_lt_of_le hm0A.1.2 with h | h
    · rw [h, hψt] at hm0M; linarith
    · exact h
  obtain ⟨ε, hε, hconv⟩ := hloc m0 (hsub hm0A.1)
  set η := min ε (min (m0 - a) (t1 - m0)) / 2 with hη
  have hη0 : 0 < η := by
    have : 0 < min ε (min (m0 - a) (t1 - m0)) := lt_min hε (lt_min (by linarith) (by linarith))
    linarith
  have hηε : η < ε := by
    have := min_le_left ε (min (m0 - a) (t1 - m0)); linarith
  have hηa : η < m0 - a := by
    have := min_le_right ε (min (m0 - a) (t1 - m0))
    have := min_le_left (m0 - a) (t1 - m0); linarith
  have hηt : η < t1 - m0 := by
    have := min_le_right ε (min (m0 - a) (t1 - m0))
    have := min_le_right (m0 - a) (t1 - m0); linarith
  have hconvin := hconv.2 (show m0 - η ∈ Set.Ioo (m0 - ε) (m0 + ε) from
    ⟨by linarith, by linarith⟩) (show m0 + η ∈ Set.Ioo (m0 - ε) (m0 + ε) from
    ⟨by linarith, by linarith⟩) (show (0:ℝ) ≤ 1 / 2 by norm_num) (show (0:ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  simp only [smul_eq_mul] at hconvin
  have hmid : 1 / 2 * (m0 - η) + 1 / 2 * (m0 + η) = m0 := by ring
  rw [hmid] at hconvin
  have hl : ψ (m0 - η) ≤ M := hcmax ⟨by linarith, by linarith⟩
  have hr : ψ (m0 + η) ≤ M := hcmax ⟨by linarith, by linarith⟩
  have hlin : ψ m0 ≤ 1 / 2 * ψ (m0 - η) + 1 / 2 * ψ (m0 + η) := by
    simp only [hψ]
    have : φ t1 * (m0 - a) / (t1 - a) = 1 / 2 * (φ t1 * (m0 - η - a) / (t1 - a)) +
        1 / 2 * (φ t1 * (m0 + η - a) / (t1 - a)) := by
      field_simp; ring
    linarith
  have heq : ψ (m0 - η) = M := by linarith
  have hmem : m0 - η ∈ A := ⟨⟨by linarith, by linarith⟩, heq⟩
  have := csInf_le hAbdd hmem
  linarith

/-! ## A generic starting point -/

/-- Two vectors of `ℝ³` have a nonzero common normal. -/
lemma exists_normal_two (a b : Space3) :
    ∃ n : Space3, n ≠ 0 ∧ inner ℝ a n = 0 ∧ inner ℝ b n = 0 := by
  set K : Submodule ℝ Space3 := Submodule.span ℝ {a, b}
  have h1 : Module.finrank ℝ K ≤ 2 := by
    have := finrank_span_le_card (R := ℝ) ({a, b} : Set Space3)
    have h2 : ({a, b} : Set Space3).toFinset.card ≤ 2 := by
      rw [Set.toFinset_insert, Set.toFinset_singleton]; exact Finset.card_le_two
    exact this.trans h2
  have h3 := Submodule.finrank_add_finrank_orthogonal K
  rw [finrank_euclideanSpace, Fintype.card_fin] at h3
  have hne : Kᗮ ≠ ⊥ := by
    intro h; rw [h, finrank_bot] at h3; omega
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨n, hn0, ?_, ?_⟩
  · exact Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (by simp)) hn
  · exact Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (by simp)) hn

open Polynomial in
/-- **A generic starting point.**  Every cone `τ` contains a point `x₀` such that `x₀` lies in no
other cone and the segment from `x₀` to `u k` meets no line through a ray before its endpoint. -/
lemma exists_generic_start (hfan : IsSimplicialFan S u T) {τ : Finset ι} (hτ : τ ∈ T)
    {k : ι} (hk : k ∈ S) :
    ∃ x₀ ∈ finCone u τ, (∀ ρ ∈ T, x₀ ∈ finCone u ρ → ρ = τ) ∧
      ∀ t : ℝ, t < 1 → FanGeneric S u (x₀ + t • (u k - x₀)) := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.1 (hfan.card _ hτ)
  have hind := hfan.indep_three hab hac hbc hτ
  choose n hn0 hnk hnm using fun m : ι => exists_normal_two (u k) (u m)
  set P : ι → ℝ[X] := fun m => C (inner ℝ (n m) (u a)) + C (inner ℝ (n m) (u b)) * X +
    C (inner ℝ (n m) (u c)) * X ^ 2 with hP
  have hPeval : ∀ m s, (P m).eval s = inner ℝ (n m) (u a) + inner ℝ (n m) (u b) * s +
      inner ℝ (n m) (u c) * s ^ 2 := by
    intro m s; simp [hP]
  have hPne : ∀ m, P m ≠ 0 := by
    intro m h
    have h0 := congrArg (fun p => Polynomial.coeff p 0) h
    have h1 := congrArg (fun p => Polynomial.coeff p 1) h
    have h2 := congrArg (fun p => Polynomial.coeff p 2) h
    simp [hP, Polynomial.coeff_X, Polynomial.coeff_C] at h0 h1 h2
    apply hn0 m
    exact eq_zero_of_inner_three hind (by rw [real_inner_comm]; exact h0)
      (by rw [real_inner_comm]; exact h1) (by rw [real_inner_comm]; exact h2)
  have hfin : (⋃ m ∈ S, {s : ℝ | (P m).IsRoot s}).Finite :=
    Set.Finite.biUnion S.finite_toSet fun m _ => Polynomial.finite_setOf_isRoot (hPne m)
  obtain ⟨s, hs0, hsP⟩ := ((Set.Ioi_infinite (0 : ℝ)).diff hfin).nonempty
  simp only [Set.mem_Ioi] at hs0
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, Polynomial.IsRoot.def, not_exists] at hsP
  have hPs : ∀ m ∈ S, inner ℝ (n m) (u a) + inner ℝ (n m) (u b) * s +
      inner ℝ (n m) (u c) * s ^ 2 ≠ 0 := fun m hm => by rw [← hPeval]; exact hsP m hm
  have ha : a ∈ ({a, b, c} : Finset ι) := by simp
  have hb : b ∈ ({a, b, c} : Finset ι) := by simp
  have hc : c ∈ ({a, b, c} : Finset ι) := by simp
  set w : ι → ℝ := fun m => ((if m = a then 1 else 0) + (if m = b then s else 0)) +
    if m = c then s ^ 2 else 0 with hw
  set x₀ : Space3 := u a + s • u b + s ^ 2 • u c with hx₀
  have hsum : ∑ m ∈ ({a, b, c} : Finset ι), w m • u m = x₀ := by
    simp only [hw, add_smul, Finset.sum_add_distrib]
    rw [sum_single_smul u ha, sum_single_smul u hb, sum_single_smul u hc, one_smul]
  refine ⟨x₀, ⟨w, fun m _ => by simp only [hw]; split_ifs <;> positivity, hsum.symm⟩, ?_, ?_⟩
  · intro ρ hρ hxρ
    have hI : x₀ ∈ finCone u ({a, b, c} ∩ ρ) := by
      rw [← hfan.inter _ hτ ρ hρ]
      exact ⟨⟨w, fun m _ => by simp only [hw]; split_ifs <;> positivity, hsum.symm⟩, hxρ⟩
    obtain ⟨d, -, hd⟩ := hI
    have hsub : ({a, b, c} : Finset ι) ∩ ρ ⊆ {a, b, c} := Finset.inter_subset_left
    have key := hfan.coeff_eq_zero hτ (fun m => (if m ∈ ({a, b, c} : Finset ι) ∩ ρ then d m else 0) - w m)
      (by simp only [sub_smul, Finset.sum_sub_distrib]; rw [sum_extend_smul u hsub, ← hd, hsum, sub_self])
    have hsubρ : ({a, b, c} : Finset ι) ⊆ ρ := by
      intro m hm
      by_contra hmρ
      have := key m hm
      have hm' : m ∉ ({a, b, c} : Finset ι) ∩ ρ := fun h => hmρ (Finset.mem_inter.1 h).2
      simp only [hm', if_false, zero_sub, neg_eq_zero, hw] at this
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with rfl | rfl | rfl
      · simp [hab, hac] at this
      · simp [hab.symm, hbc] at this; exact hs0.ne' this
      · simp [hac.symm, hbc.symm] at this; exact hs0.ne' this
    exact (Finset.eq_of_subset_of_card_le hsubρ (by rw [hfan.card _ hτ, hfan.card _ hρ])).symm
  · intro t ht
    have hval : ∀ m ∈ S, inner ℝ (n m) (x₀ + t • (u k - x₀)) ≠ 0 := by
      intro m hm
      have e : inner ℝ (n m) (x₀ + t • (u k - x₀)) = (1 - t) * (inner ℝ (n m) (u a) +
          inner ℝ (n m) (u b) * s + inner ℝ (n m) (u c) * s ^ 2) := by
        have hk' : inner ℝ (n m) (u k) = 0 := by rw [real_inner_comm]; exact hnk m
        simp only [hx₀, inner_add_right, inner_smul_right, inner_sub_right, hk']
        ring
      rw [e]
      exact mul_ne_zero (by linarith) (hPs m hm)
    refine ⟨fun h0 => hval k hk (by rw [h0, inner_zero_right]), fun m hm r hr => hval m hm ?_⟩
    rw [hr, inner_smul_right, real_inner_comm, hnm m, mul_zero]

/-! ## Convexity -/

/-- Every point has a ball around it all of whose points lie in a cone containing the point. -/
lemma IsSimplicialFan.exists_ball_cones (hfan : IsSimplicialFan S u T) (x : Space3) :
    ∃ r > 0, ∀ y : Space3, dist y x < r →
      ∃ ρ ∈ T, x ∈ finCone u ρ ∧ y ∈ finCone u ρ := by
  have hU : IsOpen (⋂ ρ ∈ T.filter (fun ρ => x ∉ finCone u ρ), (finCone u ρ)ᶜ) :=
    isOpen_biInter_finset fun ρ _ => (isClosed_finCone u ρ).isOpen_compl
  have hxU : x ∈ ⋂ ρ ∈ T.filter (fun ρ => x ∉ finCone u ρ), (finCone u ρ)ᶜ := by
    simp only [Set.mem_iInter, Set.mem_compl_iff]
    intro ρ hρ
    exact (Finset.mem_filter.1 hρ).2
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU x hxU
  refine ⟨r, hr, fun y hy => ?_⟩
  obtain ⟨ρ, hρ, hyρ⟩ := hfan.complete y
  refine ⟨ρ, hρ, by_contra fun hxρ => ?_, hyρ⟩
  have := hball (Metric.mem_ball.2 hy)
  simp only [Set.mem_iInter, Set.mem_compl_iff] at this
  exact this ρ (Finset.mem_filter.2 ⟨hρ, hxρ⟩) hyρ

lemma ray_mem_finCone {τ : Finset ι} {k : ι} (hk : k ∈ τ) : u k ∈ finCone u τ :=
  ⟨fun m => if m = k then 1 else 0, fun m _ => by dsimp only; split_ifs <;> norm_num,
    (sum_indicator_smul u hk).symm⟩

/-- Continuity of the fan function at a ray: near `u k`, the fan function is within
`C ‖y - u k‖` of its value at `u k`. -/
lemma FanGradient.near_ray (hfan : IsSimplicialFan S u T) (hg : FanGradient T u W g)
    {k : ι} (hk : ∃ σ ∈ T, k ∈ σ) :
    ∃ r > 0, ∀ y : Space3, dist y (u k) < r → ∃ ρ ∈ T, k ∈ ρ ∧ fanFun T u g y = inner ℝ (g ρ) y := by
  obtain ⟨r, hr, hball⟩ := hfan.exists_ball_cones (u k)
  refine ⟨r, hr, fun y hy => ?_⟩
  obtain ⟨ρ, hρ, hkρ, hyρ⟩ := hball y hy
  refine ⟨ρ, hρ, by_contra fun h => hfan.ray_not_mem_finCone hk hρ subset_rfl h hkρ,
    hg.fanFun_eq hfan hρ hyρ⟩


/-- **Convexity at a ray.**  For every cone `τ` and every ray `u k` lying in a cone of the fan,
`⟪g τ, u k⟫ ≤ H(u k)`. -/
theorem FanGradient.inner_le (hfan : IsSimplicialFan S u T) (hg : FanGradient T u W g)
    (hneg : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → W i j ≤ 0) {τ : Finset ι} (hτ : τ ∈ T) {k : ι} (hk : k ∈ S)
    (hkσ : ∃ σ ∈ T, k ∈ σ) :
    inner ℝ (g τ) (u k) ≤ fanFun T u g (u k) := by
  obtain ⟨x₀, hx₀τ, hx₀uniq, hgen⟩ := exists_generic_start hfan hτ hk
  set v : Space3 := u k - x₀ with hv
  set x : ℝ → Space3 := fun t => x₀ + t • v with hx
  set φ : ℝ → ℝ := fun t => fanFun T u g (x t) - inner ℝ (g τ) (x t) with hφ
  have hdist : ∀ t t' : ℝ, dist (x t') (x t) = |t' - t| * ‖v‖ := by
    intro t t'
    rw [dist_eq_norm]
    have : x t' - x t = (t' - t) • v := by simp only [hx, sub_smul]; abel
    rw [this, norm_smul, Real.norm_eq_abs]
  have hxaff : ∀ t1 t2 a b : ℝ, a + b = 1 → x (a * t1 + b * t2) = a • x t1 + b • x t2 := by
    intro t1 t2 a b hab
    simp only [hx, smul_add, smul_smul, add_smul]
    rw [← add_assoc, add_add_add_comm, ← add_smul, hab, one_smul]
    abel
  have hloc : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∃ ε > 0, ConvexOn ℝ (Set.Ioo (t - ε) (t + ε)) φ := by
    intro t ht
    obtain ⟨r, hr, hconv⟩ := hg.locally_convex hfan hneg (hgen t ht.2)
    refine ⟨r / (‖v‖ + 1), by positivity, convex_Ioo _ _, fun t1 ht1 t2 ht2 a b ha hb hab => ?_⟩
    have hball : ∀ t' ∈ Set.Ioo (t - r / (‖v‖ + 1)) (t + r / (‖v‖ + 1)), x t' ∈ Metric.ball (x t) r := by
      intro t' ht'
      rw [Metric.mem_ball, hdist]
      have h1 : |t' - t| < r / (‖v‖ + 1) := abs_sub_lt_iff.2 ⟨by linarith [ht'.2], by linarith [ht'.1]⟩
      have h2 : |t' - t| * ‖v‖ ≤ |t' - t| * (‖v‖ + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      have h3 : |t' - t| * (‖v‖ + 1) < r := by
        rwa [lt_div_iff₀ (by positivity)] at h1
      linarith
    have hc := hconv.2 (hball t1 ht1) (hball t2 ht2) ha hb hab
    simp only [smul_eq_mul] at hc ⊢
    simp only [hφ]
    rw [hxaff t1 t2 a b hab]
    rw [inner_add_right, inner_smul_right, inner_smul_right]
    nlinarith
  have hzero : ∃ δ > 0, ∀ t ∈ Set.Ioo (0 : ℝ) δ, φ t = 0 := by
    obtain ⟨r, hr, hball⟩ := hfan.exists_ball_cones x₀
    refine ⟨r / (‖v‖ + 1), by positivity, fun t ht => ?_⟩
    have hd : dist (x t) (x 0) < r := by
      rw [hdist, sub_zero, abs_of_pos ht.1]
      have h3 : t * (‖v‖ + 1) < r := by rw [← lt_div_iff₀ (by positivity)]; exact ht.2
      nlinarith [norm_nonneg v]
    have hx0 : x 0 = x₀ := by simp [hx]
    rw [hx0] at hd
    obtain ⟨ρ, hρ, hx₀ρ, hxρ⟩ := hball (x t) hd
    rw [hx₀uniq ρ hρ hx₀ρ] at hxρ
    simp only [hφ]
    rw [hg.fanFun_eq hfan hτ hxρ, sub_self]
  obtain ⟨δ, hδ, hz⟩ := hzero
  have hnn := nonneg_of_locally_convex hloc hδ hz
  -- the limit at `t = 1`
  obtain ⟨r, hr, hray⟩ := hg.near_ray hfan hkσ
  by_contra hcon
  push_neg at hcon
  set D := fanFun T u g (u k) - inner ℝ (g τ) (u k) with hD
  have hDneg : D < 0 := by linarith
  set C := ∑ ρ ∈ T, |inner ℝ (g ρ - g τ) v| with hC
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun ρ _ => abs_nonneg _
  set η := min (1 / 2) (min (r / (‖v‖ + 1)) (-D / (C + 1))) / 2 with hη
  have hm0 : 0 < min (1 / 2 : ℝ) (min (r / (‖v‖ + 1)) (-D / (C + 1))) :=
    lt_min (by norm_num) (lt_min (by positivity) (div_pos (by linarith) (by linarith)))
  have hη0 : 0 < η := by linarith
  have hη1 : η < 1 / 2 := by
    have := min_le_left (1 / 2 : ℝ) (min (r / (‖v‖ + 1)) (-D / (C + 1))); linarith
  have hηr : η < r / (‖v‖ + 1) := by
    have := min_le_right (1 / 2 : ℝ) (min (r / (‖v‖ + 1)) (-D / (C + 1)))
    have := min_le_left (r / (‖v‖ + 1)) (-D / (C + 1)); linarith
  have hηD : η < -D / (C + 1) := by
    have := min_le_right (1 / 2 : ℝ) (min (r / (‖v‖ + 1)) (-D / (C + 1)))
    have := min_le_right (r / (‖v‖ + 1)) (-D / (C + 1)); linarith
  have hxt : x (1 - η) = u k - η • v := by
    simp only [hx, hv, sub_smul, one_smul]; abel
  have hd : dist (x (1 - η)) (u k) < r := by
    rw [hxt, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_pos hη0]
    have h3 : η * (‖v‖ + 1) < r := by rw [← lt_div_iff₀ (by positivity)]; exact hηr
    nlinarith [norm_nonneg v]
  obtain ⟨ρ, hρ, hkρ, hval⟩ := hray _ hd
  have hφt := hnn (1 - η) ⟨by linarith, by linarith⟩
  have hHk : fanFun T u g (u k) = inner ℝ (g ρ) (u k) := hg.fanFun_eq hfan hρ (ray_mem_finCone hkρ)
  have hexp : φ (1 - η) = D - η * inner ℝ (g ρ - g τ) v := by
    simp only [hφ, hD]
    rw [hval, hHk, hxt, inner_sub_right, inner_sub_right, inner_smul_right, inner_smul_right,
      inner_sub_left]
    ring
  have hle : |inner ℝ (g ρ - g τ) v| ≤ C :=
    Finset.single_le_sum (f := fun ρ => |inner ℝ (g ρ - g τ) v|) (fun _ _ => abs_nonneg _) hρ
  have h1 : η * (C + 1) < -D := by rw [← lt_div_iff₀ (by linarith)]; exact hηD
  have h2 : -(η * inner ℝ (g ρ - g τ) v) ≤ η * C := by
    have := neg_abs_le (inner ℝ (g ρ - g τ) v)
    nlinarith
  rw [hexp] at hφt
  nlinarith


/-- **Support data from integrated gradients** (Guide §7.3 (c)). -/
theorem FanGradient.fanSupport (hfan : IsSimplicialFan S u T) (hg : FanGradient T u W g)
    (hu : ∀ i ∈ S, ‖u i‖ = 1) (hused : ∀ i ∈ S, ∃ τ ∈ T, i ∈ τ)
    (hneg : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → W i j ≤ 0) :
    ∃ h : ι → ℝ, FanSupport S u T W g h := by
  refine ⟨fun k => if hk : ∃ σ ∈ T, k ∈ σ then inner ℝ (u k) (g hk.choose) else 0, ?_, ?_, ?_⟩
  · intro τ hτ k hk
    have hex : ∃ σ ∈ T, k ∈ σ := ⟨τ, hτ, hk⟩
    simp only [dif_pos hex]
    exact hg.cont τ hτ _ hex.choose_spec.1 k hk hex.choose_spec.2
  · intro τ hτ k hk
    have hex : ∃ σ ∈ T, k ∈ σ := hused k hk
    simp only [dif_pos hex]
    have h1 := hg.inner_le hfan hneg hτ hk hex
    rw [hg.fanFun_eq hfan hex.choose_spec.1 (ray_mem_finCone hex.choose_spec.2)] at h1
    rw [real_inner_comm (u k), real_inner_comm (u k)] at h1
    exact h1
  · intro τ hτ τ' hτ' hne i hi j hj hij hi' hj'
    have hcard : ((τ'.erase i).erase j).card = 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨Ne.symm hij, hj'⟩),
        Finset.card_erase_of_mem hi', hfan.card τ' hτ']
    obtain ⟨b, hb⟩ := Finset.card_eq_one.1 hcard
    have hbmem : b ∈ (τ'.erase i).erase j := by rw [hb]; exact Finset.mem_singleton_self b
    simp only [Finset.mem_erase] at hbmem
    obtain ⟨hbj, hbi, hbτ'⟩ := hbmem
    have hiS := hfan.subset τ hτ hi
    have hjS := hfan.subset τ hτ hj
    rw [norm_sub_rev, hg.jump τ hτ τ' hτ' hne i hi j hj hij hi' hj' b hbτ' hbi hbj, norm_smul,
      norm_orientedCross (hu i hiS) (hu j hjS), Real.norm_eq_abs,
      abs_of_nonneg (by linarith [hneg i hiS j hjS hij])]

end Erdos99
end

end FanConvexity

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `FanCrossing`
-/

section FanCrossing

/-!
# Crossing counts of segments with cones in `ℝ³`

Auxiliary results for the integration of the gradient jumps of a fan matrix
(`FanIntegration`).

* `stepCross` and `step_indicator_eq` : along a segment, the change of the indicator of
  `{A > 0, B > 0, C > 0}` (three affine functions) is the sum of the signed crossings of the three
  faces.
* `wedgeCross a b x y` : the signed number of crossings of the segment from `x` to `y` with the
  open two-dimensional cone spanned by `a, b`, counted positively in the direction of `a × b`.
* `inCone3_step` : for independent `a, b, c` and a generic segment, the change of the indicator
  of the open cone spanned by `a, b, c` is the signed sum of the crossings of its three faces.
* `exists_avoid_planes` : a nonempty open set is not covered by finitely many planes.
-/

open scoped BigOperators
open Filter Topology

@[expose] public noncomputable section

open Classical

namespace Erdos99

/-! ## Elementary identities for `vol3` -/

lemma vol3_swap (a b c : Space3) : vol3 b a c = -vol3 a b c := by unfold vol3; ring

lemma vol3_comb_left (p q : ℝ) (x y b c : Space3) :
    vol3 (p • x + q • y) b c = p * vol3 x b c + q * vol3 y b c := by
  simp only [vol3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

lemma vol3_comb_mid (p q : ℝ) (a x y c : Space3) :
    vol3 a (p • x + q • y) c = p * vol3 a x c + q * vol3 a y c := by
  simp only [vol3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

lemma vol3_comb_right (p q : ℝ) (a b x y : Space3) :
    vol3 a b (p • x + q • y) = p * vol3 a b x + q * vol3 a b y := by
  simp only [vol3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring

lemma vol3_self_left (a c : Space3) : vol3 a a c = 0 := by unfold vol3; ring

lemma vol3_self_right (a b : Space3) : vol3 a b b = 0 := by unfold vol3; ring

lemma vol3_self_out (a b : Space3) : vol3 a b a = 0 := by unfold vol3; ring

/-- **Cramer's rule** in `ℝ³`. -/
lemma cramer3 (a b c z : Space3) :
    vol3 a b c • z = vol3 z b c • a + vol3 a z c • b + vol3 a b z • c := by
  ext k; fin_cases k <;> simp [vol3] <;> ring

lemma vol3_eq_inner_cross (a b z : Space3) : vol3 a b z = inner ℝ (cross3 a b) z :=
  (inner_cross3 a b z).symm

lemma vol3_cross_self (a b : Space3) : vol3 a b (cross3 a b) = ‖cross3 a b‖ ^ 2 := by
  rw [vol3_eq_inner_cross, real_inner_self_eq_norm_sq]

/-- Two-forms: `F_a(x) F_b(y) - F_a(y) F_b(x) = D · vol(x, y, c)`. -/
lemma vol3_two_form_ab (a b c x y : Space3) :
    vol3 x b c * vol3 a y c - vol3 y b c * vol3 a x c = vol3 a b c * vol3 x y c := by
  unfold vol3; ring

lemma vol3_two_form_bc (a b c x y : Space3) :
    vol3 a x c * vol3 a b y - vol3 a y c * vol3 a b x = vol3 a b c * vol3 x y a := by
  unfold vol3; ring

lemma vol3_two_form_ca (a b c x y : Space3) :
    vol3 a b x * vol3 y b c - vol3 a b y * vol3 x b c = vol3 a b c * vol3 x y b := by
  unfold vol3; ring

/-- `D · vol(z, b, a × b) = F_a(z) ‖a × b‖² + F_c(z) vol(c, b, a × b)`. -/
lemma vol3_wedge_first (a b c z : Space3) :
    vol3 a b c * vol3 z b (cross3 a b) =
      vol3 z b c * vol3 a b (cross3 a b) + vol3 a b z * vol3 c b (cross3 a b) := by
  simp only [vol3, cross3_apply_zero, cross3_apply_one, cross3_apply_two]; ring

/-- `D · vol(a, z, a × b) = F_b(z) ‖a × b‖² + F_c(z) vol(a, c, a × b)`. -/
lemma vol3_wedge_second (a b c z : Space3) :
    vol3 a b c * vol3 a z (cross3 a b) =
      vol3 a z c * vol3 a b (cross3 a b) + vol3 a b z * vol3 a c (cross3 a b) := by
  simp only [vol3, cross3_apply_zero, cross3_apply_one, cross3_apply_two]; ring

/-! ## The one-dimensional step identity -/

/-- The signed crossing of the face `{C = 0, A > 0, B > 0}` by a segment along which the affine
functions `A, B, C` go from `A0, B0, C0` to `A1, B1, C1`. -/
def stepCross (C0 C1 A0 A1 B0 B1 : ℝ) : ℝ :=
  if C0 < 0 ∧ 0 < C1 ∧ 0 < C1 * A0 - C0 * A1 ∧ 0 < C1 * B0 - C0 * B1 then 1
  else if C1 < 0 ∧ 0 < C0 ∧ 0 < C0 * A1 - C1 * A0 ∧ 0 < C0 * B1 - C1 * B0 then -1 else 0

set_option maxHeartbeats 4000000 in
/-- **The step identity.**  Along a generic segment, the change of the indicator of
`{A > 0, B > 0, C > 0}` is the sum of the signed crossings of the three faces. -/
theorem step_indicator_eq {A0 A1 B0 B1 C0 C1 : ℝ} (hA0 : A0 ≠ 0) (hA1 : A1 ≠ 0) (hB0 : B0 ≠ 0)
    (hB1 : B1 ≠ 0) (hC0 : C0 ≠ 0) (hC1 : C1 ≠ 0) (h1 : A0 * B1 - A1 * B0 ≠ 0)
    (h2 : B0 * C1 - B1 * C0 ≠ 0) (h3 : C0 * A1 - C1 * A0 ≠ 0) :
    ((if 0 < A1 ∧ 0 < B1 ∧ 0 < C1 then 1 else 0) -
        (if 0 < A0 ∧ 0 < B0 ∧ 0 < C0 then 1 else 0) : ℝ) =
      stepCross A0 A1 B0 B1 C0 C1 + stepCross B0 B1 C0 C1 A0 A1 +
        stepCross C0 C1 A0 A1 B0 B1 := by
  have e1 : A1 * (B0 * C1 - B1 * C0) + B1 * (C0 * A1 - C1 * A0) +
      C1 * (A0 * B1 - A1 * B0) = 0 := by ring
  have e0 : A0 * (B0 * C1 - B1 * C0) + B0 * (C0 * A1 - C1 * A0) +
      C0 * (A0 * B1 - A1 * B0) = 0 := by ring
  unfold stepCross
  have r1 : A1 * B0 - A0 * B1 = -(A0 * B1 - A1 * B0) := by ring
  have r2 : A1 * C0 - A0 * C1 = (C0 * A1 - C1 * A0) := by ring
  have r3 : B1 * C0 - B0 * C1 = -(B0 * C1 - B1 * C0) := by ring
  have r4 : B1 * A0 - B0 * A1 = (A0 * B1 - A1 * B0) := by ring
  have r5 : C1 * A0 - C0 * A1 = -(C0 * A1 - C1 * A0) := by ring
  have r6 : C1 * B0 - C0 * B1 = (B0 * C1 - B1 * C0) := by ring
  have s1 : A0 * C1 - A1 * C0 = -(C0 * A1 - C1 * A0) := by ring
  have s3 : B0 * A1 - B1 * A0 = -(A0 * B1 - A1 * B0) := by ring
  have s5 : C0 * B1 - C1 * B0 = -(B0 * C1 - B1 * C0) := by ring
  rw [r1, r2, r3, r4, r5, r6, s1, s3, s5]
  generalize A0 * B1 - A1 * B0 = p at *
  generalize B0 * C1 - B1 * C0 = q at *
  generalize C0 * A1 - C1 * A0 = r at *
  rcases hA0.lt_or_gt with a0 | a0 <;> rcases hA1.lt_or_gt with a1 | a1 <;>
  rcases hB0.lt_or_gt with b0 | b0 <;> rcases hB1.lt_or_gt with b1 | b1 <;>
  rcases hC0.lt_or_gt with c0 | c0 <;> rcases hC1.lt_or_gt with c1 | c1 <;>
  rcases h1.lt_or_gt with d1 | d1 <;> rcases h2.lt_or_gt with d2 | d2 <;>
  rcases h3.lt_or_gt with d3 | d3 <;>
  simp [a0, a1, b0, b1, c0, c1, d1, d2, d3, a0.not_gt, a1.not_gt, b0.not_gt, b1.not_gt,
    c0.not_gt, c1.not_gt, d1.not_gt, d2.not_gt, d3.not_gt] <;> nlinarith

/-! ## Crossings of a segment with a wedge -/

/-- The signed crossing of the segment from `x` to `y` with the open cone spanned by `a, b`:
`1` if the segment crosses it in the direction of `a × b`, `-1` in the opposite direction, `0`
if it does not cross it. -/
def wedgeCross (a b x y : Space3) : ℝ :=
  if vol3 a b x < 0 ∧ 0 < vol3 a b y ∧
      0 < vol3 (vol3 a b y • x - vol3 a b x • y) b (cross3 a b) ∧
      0 < vol3 a (vol3 a b y • x - vol3 a b x • y) (cross3 a b) then 1
  else if vol3 a b y < 0 ∧ 0 < vol3 a b x ∧
      vol3 (vol3 a b y • x - vol3 a b x • y) b (cross3 a b) < 0 ∧
      vol3 a (vol3 a b y • x - vol3 a b x • y) (cross3 a b) < 0 then -1 else 0

/-- The sign `±1` of a real number (`-1` for `0`). -/
def sgnR (D : ℝ) : ℝ := if 0 < D then 1 else -1

lemma sgnR_mul_self (D : ℝ) : sgnR D * sgnR D = 1 := by
  unfold sgnR; split_ifs <;> norm_num

/-- The open cone spanned by `a, b, c` (for `vol3 a b c ≠ 0`), in Cramer coordinates. -/
def inCone3 (a b c z : Space3) : Prop :=
  0 < vol3 a b c * vol3 z b c ∧ 0 < vol3 a b c * vol3 a z c ∧ 0 < vol3 a b c * vol3 a b z

lemma iff_of_pos_mul {D X : ℝ} (hD : 0 < D) : (0 < D * X ↔ 0 < X) ∧ (D * X < 0 ↔ X < 0) :=
  ⟨⟨fun h => pos_of_mul_pos_right h hD.le, fun h => mul_pos hD h⟩,
    ⟨fun h => by nlinarith, fun h => mul_neg_of_pos_of_neg hD h⟩⟩

lemma iff_of_neg_mul {D X : ℝ} (hD : D < 0) : (0 < D * X ↔ X < 0) ∧ (D * X < 0 ↔ 0 < X) :=
  ⟨⟨fun h => by nlinarith, fun h => mul_pos_of_neg_of_neg hD h⟩,
    ⟨fun h => by nlinarith, fun h => mul_neg_of_neg_of_pos hD h⟩⟩

lemma ite_three_congr {P1 P2 Q1 Q2 : Prop} [Decidable P1] [Decidable P2] [Decidable Q1]
    [Decidable Q2] (h1 : P1 ↔ Q1) (h2 : P2 ↔ Q2) :
    (if P1 then (1 : ℝ) else if P2 then -1 else 0) = if Q1 then 1 else if Q2 then -1 else 0 := by
  by_cases a : P1
  · rw [if_pos a, if_pos (h1.1 a)]
  · rw [if_neg a, if_neg (fun b => a (h1.2 b))]
    by_cases c : P2
    · rw [if_pos c, if_pos (h2.1 c)]
    · rw [if_neg c, if_neg (fun b => c (h2.2 b))]

lemma ite_three_neg {P1 P2 Q1 Q2 : Prop} [Decidable P1] [Decidable P2] [Decidable Q1]
    [Decidable Q2] (h1 : P1 ↔ Q2) (h2 : P2 ↔ Q1) (hex : ¬ (Q1 ∧ Q2)) :
    (if P1 then (1 : ℝ) else if P2 then -1 else 0) =
      -1 * if Q1 then 1 else if Q2 then -1 else 0 := by
  by_cases a : Q1
  · have : ¬ Q2 := fun b => hex ⟨a, b⟩
    rw [if_neg (fun b => this (h1.1 b)), if_pos (h2.2 a), if_pos a]; ring
  · rw [if_neg a]
    by_cases c : Q2
    · rw [if_pos (h1.2 c), if_pos c]; ring
    · rw [if_neg (fun b => c (h1.1 b)), if_neg (fun b => a (h2.1 b)), if_neg c]; ring

lemma wedge_sign_abstract {D M p q Z1 Z2 X Y : ℝ} (hD : D ≠ 0) (hM : 0 < M)
    (hZ1 : D * Z1 = M * X) (hZ2 : D * Z2 = M * Y) :
    (if p < 0 ∧ 0 < q ∧ 0 < Z1 ∧ 0 < Z2 then (1 : ℝ)
      else if q < 0 ∧ 0 < p ∧ Z1 < 0 ∧ Z2 < 0 then -1 else 0) =
    sgnR D * (if D * p < 0 ∧ 0 < D * q ∧ 0 < D ^ 2 * X ∧ 0 < D ^ 2 * Y then 1
      else if D * q < 0 ∧ 0 < D * p ∧ 0 < D ^ 2 * (-X) ∧ 0 < D ^ 2 * (-Y) then -1 else 0) := by
  have hD2 : 0 < D ^ 2 := by positivity
  have jX := iff_of_pos_mul hD2 (X := X)
  have jX' := iff_of_pos_mul hD2 (X := -X)
  have jY := iff_of_pos_mul hD2 (X := Y)
  have jY' := iff_of_pos_mul hD2 (X := -Y)
  rw [neg_pos] at jX' jY'
  have kX := iff_of_pos_mul hM (X := X)
  have kY := iff_of_pos_mul hM (X := Y)
  rcases hD.lt_or_gt with hneg | hpos
  · have hs : sgnR D = -1 := by unfold sgnR; rw [if_neg (by linarith)]
    rw [hs]
    have i1 := iff_of_neg_mul hneg (X := p)
    have i2 := iff_of_neg_mul hneg (X := q)
    have iZ1 : (0 < Z1 ↔ X < 0) ∧ (Z1 < 0 ↔ 0 < X) := by
      have := iff_of_neg_mul hneg (X := Z1)
      rw [hZ1, kX.1, kX.2] at this
      exact ⟨this.2.symm, this.1.symm⟩
    have iZ2 : (0 < Z2 ↔ Y < 0) ∧ (Z2 < 0 ↔ 0 < Y) := by
      have := iff_of_neg_mul hneg (X := Z2)
      rw [hZ2, kY.1, kY.2] at this
      exact ⟨this.2.symm, this.1.symm⟩
    refine ite_three_neg ?_ ?_ ?_
    · simp only [i1.1, i2.2, iZ1.1, iZ2.1, jX'.1, jY'.1]
      exact ⟨fun ⟨a, b, c, d⟩ => ⟨b, a, c, d⟩, fun ⟨a, b, c, d⟩ => ⟨b, a, c, d⟩⟩
    · simp only [i1.2, i2.1, iZ1.2, iZ2.2, jX.1, jY.1]
      exact ⟨fun ⟨a, b, c, d⟩ => ⟨b, a, c, d⟩, fun ⟨a, b, c, d⟩ => ⟨b, a, c, d⟩⟩
    · rintro ⟨⟨h1, -⟩, ⟨-, h2, -⟩⟩; linarith
  · have hs : sgnR D = 1 := by unfold sgnR; rw [if_pos hpos]
    rw [hs, one_mul]
    have i1 := iff_of_pos_mul hpos (X := p)
    have i2 := iff_of_pos_mul hpos (X := q)
    have iZ1 : (0 < Z1 ↔ 0 < X) ∧ (Z1 < 0 ↔ X < 0) := by
      have := iff_of_pos_mul hpos (X := Z1)
      rw [hZ1, kX.1, kX.2] at this
      exact ⟨this.1.symm, this.2.symm⟩
    have iZ2 : (0 < Z2 ↔ 0 < Y) ∧ (Z2 < 0 ↔ Y < 0) := by
      have := iff_of_pos_mul hpos (X := Z2)
      rw [hZ2, kY.1, kY.2] at this
      exact ⟨this.1.symm, this.2.symm⟩
    refine ite_three_congr ?_ ?_
    · simp only [i1.2, i2.1, iZ1.1, iZ2.1, jX.1, jY.1]
    · simp only [i1.1, i2.2, iZ1.2, iZ2.2, jX'.1, jY'.1]

lemma cross3_ne_zero_of_vol3 {a b c : Space3} (hD : vol3 a b c ≠ 0) : cross3 a b ≠ 0 := by
  intro h; apply hD; rw [vol3_eq_inner_cross, h, inner_zero_left]

lemma vol3_cross_pos {a b : Space3} (h : cross3 a b ≠ 0) : 0 < vol3 a b (cross3 a b) := by
  rw [vol3_cross_self]; positivity

/-- The wedge crossing in Cramer coordinates relative to a third vector `c`. -/
theorem wedgeCross_eq_stepCross {a b c : Space3} (hD : vol3 a b c ≠ 0) (x y : Space3) :
    wedgeCross a b x y = sgnR (vol3 a b c) *
      stepCross (vol3 a b c * vol3 a b x) (vol3 a b c * vol3 a b y)
        (vol3 a b c * vol3 x b c) (vol3 a b c * vol3 y b c)
        (vol3 a b c * vol3 a x c) (vol3 a b c * vol3 a y c) := by
  have hz' : vol3 a b y • x - vol3 a b x • y = vol3 a b y • x + (-vol3 a b x) • y := by
    rw [neg_smul, sub_eq_add_neg]
  have hFc : vol3 a b (vol3 a b y • x - vol3 a b x • y) = 0 := by
    rw [hz', vol3_comb_right]; ring
  have hZ1 : vol3 a b c * vol3 (vol3 a b y • x - vol3 a b x • y) b (cross3 a b) =
      vol3 a b (cross3 a b) * (vol3 a b y * vol3 x b c - vol3 a b x * vol3 y b c) := by
    rw [vol3_wedge_first, hFc, hz', vol3_comb_left]; ring
  have hZ2 : vol3 a b c * vol3 a (vol3 a b y • x - vol3 a b x • y) (cross3 a b) =
      vol3 a b (cross3 a b) * (vol3 a b y * vol3 a x c - vol3 a b x * vol3 a y c) := by
    rw [vol3_wedge_second, hFc, hz', vol3_comb_mid]; ring
  have key := wedge_sign_abstract (p := vol3 a b x) (q := vol3 a b y) hD
    (vol3_cross_pos (cross3_ne_zero_of_vol3 hD)) hZ1 hZ2
  unfold wedgeCross stepCross
  rw [key]
  congr 2 <;> ring_nf

/-! ## The cone step identity -/

lemma ite_inCone3 (a b c z : Space3) : (if inCone3 a b c z then (1 : ℝ) else 0) =
    if 0 < vol3 a b c * vol3 z b c ∧ 0 < vol3 a b c * vol3 a z c ∧ 0 < vol3 a b c * vol3 a b z
    then 1 else 0 :=
  if_congr Iff.rfl rfl rfl

/-- **The cone step identity.**  For independent `a, b, c` and a generic segment from `x` to
`y`, the change of the indicator of the open cone spanned by `a, b, c` is the signed sum of the
crossings of its three faces. -/
theorem inCone3_step {a b c x y : Space3} (hD : vol3 a b c ≠ 0)
    (hxa : vol3 x b c ≠ 0) (hxb : vol3 a x c ≠ 0) (hxc : vol3 a b x ≠ 0)
    (hya : vol3 y b c ≠ 0) (hyb : vol3 a y c ≠ 0) (hyc : vol3 a b y ≠ 0)
    (hxy_a : vol3 x y a ≠ 0) (hxy_b : vol3 x y b ≠ 0) (hxy_c : vol3 x y c ≠ 0) :
    ((if inCone3 a b c y then 1 else 0) - (if inCone3 a b c x then 1 else 0) : ℝ) =
      sgnR (vol3 a b c) * (wedgeCross a b x y + wedgeCross b c x y + wedgeCross c a x y) := by
  have c1 : vol3 b c a = vol3 a b c := by unfold vol3; ring
  have c2 : vol3 c a b = vol3 a b c := by unfold vol3; ring
  have e1 := wedgeCross_eq_stepCross hD x y
  have e2 := wedgeCross_eq_stepCross (a := b) (b := c) (c := a) (by rw [c1]; exact hD) x y
  have e3 := wedgeCross_eq_stepCross (a := c) (b := a) (c := b) (by rw [c2]; exact hD) x y
  have r1 : vol3 b c x = vol3 x b c := by unfold vol3; ring
  have r2 : vol3 b c y = vol3 y b c := by unfold vol3; ring
  have r3 : vol3 x c a = vol3 a x c := by unfold vol3; ring
  have r4 : vol3 y c a = vol3 a y c := by unfold vol3; ring
  have r5 : vol3 b x a = vol3 a b x := by unfold vol3; ring
  have r6 : vol3 b y a = vol3 a b y := by unfold vol3; ring
  have r7 : vol3 c a x = vol3 a x c := by unfold vol3; ring
  have r8 : vol3 c a y = vol3 a y c := by unfold vol3; ring
  have r9 : vol3 x a b = vol3 a b x := by unfold vol3; ring
  have r10 : vol3 y a b = vol3 a b y := by unfold vol3; ring
  have r11 : vol3 c x b = vol3 x b c := by unfold vol3; ring
  have r12 : vol3 c y b = vol3 y b c := by unfold vol3; ring
  rw [c1, r1, r2, r3, r4, r5, r6] at e2
  rw [c2, r7, r8, r9, r10, r11, r12] at e3
  rw [e1, e2, e3]
  have hstep := step_indicator_eq (A0 := vol3 a b c * vol3 x b c) (A1 := vol3 a b c * vol3 y b c)
    (B0 := vol3 a b c * vol3 a x c) (B1 := vol3 a b c * vol3 a y c)
    (C0 := vol3 a b c * vol3 a b x) (C1 := vol3 a b c * vol3 a b y)
    (mul_ne_zero hD hxa) (mul_ne_zero hD hya) (mul_ne_zero hD hxb) (mul_ne_zero hD hyb)
    (mul_ne_zero hD hxc) (mul_ne_zero hD hyc)
    (by
      have : vol3 a b c * vol3 x b c * (vol3 a b c * vol3 a y c) -
          vol3 a b c * vol3 y b c * (vol3 a b c * vol3 a x c) =
          vol3 a b c ^ 2 * (vol3 a b c * vol3 x y c) := by
        linear_combination vol3 a b c ^ 2 * vol3_two_form_ab a b c x y
      rw [this]; exact mul_ne_zero (pow_ne_zero 2 hD) (mul_ne_zero hD hxy_c))
    (by
      have : vol3 a b c * vol3 a x c * (vol3 a b c * vol3 a b y) -
          vol3 a b c * vol3 a y c * (vol3 a b c * vol3 a b x) =
          vol3 a b c ^ 2 * (vol3 a b c * vol3 x y a) := by
        linear_combination vol3 a b c ^ 2 * vol3_two_form_bc a b c x y
      rw [this]; exact mul_ne_zero (pow_ne_zero 2 hD) (mul_ne_zero hD hxy_a))
    (by
      have : vol3 a b c * vol3 a b x * (vol3 a b c * vol3 y b c) -
          vol3 a b c * vol3 a b y * (vol3 a b c * vol3 x b c) =
          vol3 a b c ^ 2 * (vol3 a b c * vol3 x y b) := by
        linear_combination vol3 a b c ^ 2 * vol3_two_form_ca a b c x y
      rw [this]; exact mul_ne_zero (pow_ne_zero 2 hD) (mul_ne_zero hD hxy_b))
  rw [ite_inCone3, ite_inCone3]
  have := sgnR_mul_self (vol3 a b c)
  linear_combination hstep - (stepCross (vol3 a b c * vol3 a b x) (vol3 a b c * vol3 a b y)
    (vol3 a b c * vol3 x b c) (vol3 a b c * vol3 y b c) (vol3 a b c * vol3 a x c)
    (vol3 a b c * vol3 a y c) +
    stepCross (vol3 a b c * vol3 x b c) (vol3 a b c * vol3 y b c) (vol3 a b c * vol3 a x c)
      (vol3 a b c * vol3 a y c) (vol3 a b c * vol3 a b x) (vol3 a b c * vol3 a b y) +
    stepCross (vol3 a b c * vol3 a x c) (vol3 a b c * vol3 a y c) (vol3 a b c * vol3 a b x)
      (vol3 a b c * vol3 a b y) (vol3 a b c * vol3 x b c) (vol3 a b c * vol3 y b c)) * this

/-! ## Crossing points -/

lemma vol3_smul_left (r : ℝ) (w b c : Space3) : vol3 (r • w) b c = r * vol3 w b c := by
  simp only [vol3, PiLp.smul_apply, smul_eq_mul]; ring

lemma vol3_smul_mid (r : ℝ) (a w c : Space3) : vol3 a (r • w) c = r * vol3 a w c := by
  simp only [vol3, PiLp.smul_apply, smul_eq_mul]; ring

/-- The point of the segment from `x` to `y` on the plane `vol3 a b · = 0`. -/
lemma seg_point_eq {p q : ℝ} (hpq : q - p ≠ 0) (x y : Space3) :
    q • x - p • y = (q - p) • (x + (-p / (q - p)) • (y - x)) := by
  ext k
  simp only [PiLp.sub_apply, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
  field_simp
  ring

/-- A nonzero wedge crossing comes from a point of the segment in the closed wedge. -/
theorem wedgeCross_ne_zero {a b x y : Space3} (h : wedgeCross a b x y ≠ 0) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ x + t • (y - x) = α • a + β • b := by
  set p := vol3 a b x
  set q := vol3 a b y
  set N := cross3 a b
  set z := q • x - p • y with hz
  have hz' : z = q • x + (-p) • y := by rw [hz, neg_smul, sub_eq_add_neg]
  have hFc : vol3 a b z = 0 := by rw [hz', vol3_comb_right]; ring
  have key : vol3 a b N • z = vol3 z b N • a + vol3 a z N • b := by
    rw [cramer3 a b N z, hFc, zero_smul, add_zero]
  have hNpos : ∀ r : ℝ, r ≠ 0 → vol3 z b N = r → 0 < vol3 a b N := by
    intro r hr hzr
    refine vol3_cross_pos fun hN0 => hr ?_
    rw [← hzr, show N = cross3 a b from rfl, hN0]; unfold vol3; simp
  unfold wedgeCross at h
  have main : ∀ (hpq : q - p ≠ 0), 0 < vol3 a b N →
      0 ≤ vol3 z b N / (vol3 a b N * (q - p)) → 0 ≤ vol3 a z N / (vol3 a b N * (q - p)) →
      0 ≤ -p / (q - p) → -p / (q - p) ≤ 1 →
      ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ x + t • (y - x) = α • a + β • b := by
    intro hpq hM hα hβ ht0 ht1
    refine ⟨-p / (q - p), ht0, ht1, _, _, hα, hβ, ?_⟩
    have e := seg_point_eq hpq x y
    rw [← hz] at e
    have : (vol3 a b N * (q - p)) • (x + (-p / (q - p)) • (y - x)) =
        vol3 z b N • a + vol3 a z N • b := by
      rw [mul_smul, ← e, key]
    have hne : vol3 a b N * (q - p) ≠ 0 := mul_ne_zero hM.ne' hpq
    calc x + (-p / (q - p)) • (y - x)
        = (vol3 a b N * (q - p))⁻¹ • ((vol3 a b N * (q - p)) •
          (x + (-p / (q - p)) • (y - x))) := by rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
      _ = _ := by
          rw [this, smul_add, smul_smul, smul_smul, div_eq_inv_mul, div_eq_inv_mul]
  split_ifs at h with h1 h2
  · obtain ⟨hp, hq, hZ1, hZ2⟩ := h1
    have hM := hNpos _ hZ1.ne' rfl
    have hqp : 0 < q - p := by linarith
    refine main hqp.ne' hM (div_nonneg hZ1.le (by positivity)) (div_nonneg hZ2.le (by positivity))
      (div_nonneg (by linarith) hqp.le) ?_
    rw [div_le_one hqp]; linarith
  · obtain ⟨hq, hp, hZ1, hZ2⟩ := h2
    have hM := hNpos _ hZ1.ne rfl
    have hqp : q - p < 0 := by linarith
    refine main hqp.ne hM (div_nonneg_of_nonpos hZ1.le (mul_neg_of_pos_of_neg hM hqp).le)
      (div_nonneg_of_nonpos hZ2.le (mul_neg_of_pos_of_neg hM hqp).le)
      (div_nonneg_of_nonpos (by linarith) hqp.le) ?_
    rw [div_le_one_of_neg hqp]; linarith
  · exact absurd rfl h

/-- A segment crossing the plane of `a, b` from the negative to the positive side of `a × b`
inside the open wedge crosses the wedge positively. -/
theorem wedgeCross_eq_one {a b x y : Space3} (hp : vol3 a b x < 0) (hq : 0 < vol3 a b y)
    (hseg : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → 0 < vol3 (x + t • (y - x)) b (cross3 a b) ∧
      0 < vol3 a (x + t • (y - x)) (cross3 a b)) : wedgeCross a b x y = 1 := by
  have hqp : 0 < vol3 a b y - vol3 a b x := by linarith
  have e := seg_point_eq hqp.ne' x y
  have ht0 : 0 ≤ -vol3 a b x / (vol3 a b y - vol3 a b x) := div_nonneg (by linarith) hqp.le
  have ht1 : -vol3 a b x / (vol3 a b y - vol3 a b x) ≤ 1 := by rw [div_le_one hqp]; linarith
  obtain ⟨h1, h2⟩ := hseg _ ht0 ht1
  unfold wedgeCross
  rw [if_pos ⟨hp, hq, by rw [e, vol3_smul_left]; exact mul_pos hqp h1,
    by rw [e, vol3_smul_mid]; exact mul_pos hqp h2⟩]

/-- A segment crossing the plane of `a, b` from the positive to the negative side of `a × b`
inside the open wedge crosses the wedge negatively. -/
theorem wedgeCross_eq_neg_one {a b x y : Space3} (hp : 0 < vol3 a b x) (hq : vol3 a b y < 0)
    (hseg : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → 0 < vol3 (x + t • (y - x)) b (cross3 a b) ∧
      0 < vol3 a (x + t • (y - x)) (cross3 a b)) : wedgeCross a b x y = -1 := by
  have hqp : vol3 a b y - vol3 a b x < 0 := by linarith
  have e := seg_point_eq hqp.ne x y
  have ht0 : 0 ≤ -vol3 a b x / (vol3 a b y - vol3 a b x) :=
    div_nonneg_of_nonpos (by linarith) hqp.le
  have ht1 : -vol3 a b x / (vol3 a b y - vol3 a b x) ≤ 1 := by
    rw [div_le_one_of_neg hqp]; linarith
  obtain ⟨h1, h2⟩ := hseg _ ht0 ht1
  unfold wedgeCross
  rw [if_neg (fun h => by linarith [h.1]), if_pos ⟨hq, hp,
    by rw [e, vol3_smul_left]; exact mul_neg_of_neg_of_pos hqp h1,
    by rw [e, vol3_smul_mid]; exact mul_neg_of_neg_of_pos hqp h2⟩]

/-! ## Avoiding finitely many planes -/

open MeasureTheory in
/-- A nonempty open subset of `ℝ³` contains a point off finitely many planes through the
origin. -/
theorem exists_avoid_planes {U : Set Space3} (hU : IsOpen U) (hne : U.Nonempty)
    (Ns : Finset Space3) : ∃ x ∈ U, ∀ n ∈ Ns, n ≠ 0 → inner ℝ n x ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hnull : ∀ n ∈ Ns, n ≠ 0 → volume {x : Space3 | inner ℝ n x = 0} = 0 := by
    intro n _ hn
    have hker : {x : Space3 | inner ℝ n x = 0} = (LinearMap.ker (innerₛₗ ℝ n) : Set Space3) := by
      ext x; simp
    rw [hker]
    apply Measure.addHaar_submodule
    intro htop
    have : n ∈ LinearMap.ker (innerₛₗ ℝ n) := by rw [htop]; trivial
    simp at this
    exact hn this
  have hsub : U ⊆ ⋃ n ∈ Ns.filter (· ≠ 0), {x : Space3 | inner ℝ n x = 0} := by
    intro x hx
    obtain ⟨n, hn, hn0, hx0⟩ := hcon x hx
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_filter]
    exact ⟨n, ⟨hn, hn0⟩, hx0⟩
  have h0 : volume (⋃ n ∈ Ns.filter (· ≠ 0), {x : Space3 | inner ℝ n x = 0}) = 0 := by
    refine le_antisymm ((measure_biUnion_finset_le _ _).trans ?_) (zero_le _)
    rw [Finset.sum_eq_zero]
    intro n hn
    rw [Finset.mem_filter] at hn
    exact hnull n hn.1 hn.2
  have hpos := hU.measure_pos volume hne
  exact hpos.ne' (measure_mono_null hsub h0)

end Erdos99
end

end FanCrossing

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `FanIntegration`
-/

section FanIntegration

/-!
# Integrating the gradient jumps of a fan matrix (Verification Guide §7.3 (b))

For a complete simplicial fan with unit rays `u` and a fan matrix `W` (`W u = 0`, off-diagonal
support on fan edges), we construct gradients `g τ` (one per cone) with the prescribed jumps
`-W i j • (u i × u j)` across the fan edges (`FanGradient`, `fan_gradient_exists` in `FanGradientExists`).

Instead of integrating the jumps along paths, we write down an explicit potential.  Fix a
generic direction `d`.  For each ordered pair `(i, j)` let `R i j` be the open cone spanned by
`u i, u j, d`, and put

  `Φ(x) = ∑ᵢ ∑ⱼ [x ∈ R i j] · (-½ W i j sgn(det(u i, u j, d))) • (u i × u j)`  (`fanPot`).

Along a generic segment the indicator of `R i j` changes exactly when the segment crosses one of
the three faces of `R i j` (`inCone3_step`).  The crossings of the faces spanned by `u i, d`
cancel after summing over `j`, because `u i × ∑ⱼ W i j u j = 0`; what remains is

  `Φ(y) - Φ(x) = ∑ᵢ ∑ⱼ (-½ W i j · cross(u i, u j; x, y)) • (u i × u j)`   (`fanPot_sub`),

where `cross(u i, u j; x, y)` is the signed number of crossings of the segment with the wedge
spanned by `u i, u j` (`wedgeCross`).  Since the wedges with `W i j ≠ 0` are edges of the fan,
`Φ` is constant on the interior of each cone, and its jumps across fan edges are as prescribed.
The gradient of a cone is the value of `Φ` at a generic interior point.
-/

open scoped BigOperators
open Filter Topology

@[expose] public noncomputable section

open Classical

namespace Erdos99

variable {ι : Type*}

/-! ## Bilinearity of the cross product -/

lemma cross3_add_right (a b c : Space3) : cross3 a (b + c) = cross3 a b + cross3 a c := by
  ext k; fin_cases k <;> simp [cross3] <;> ring

lemma cross3_smul_right (a b : Space3) (r : ℝ) : cross3 a (r • b) = r • cross3 a b := by
  ext k; fin_cases k <;> simp [cross3] <;> ring

lemma cross3_zero_right (a : Space3) : cross3 a 0 = 0 := by
  ext k; fin_cases k <;> simp [cross3]

lemma cross3_self (a : Space3) : cross3 a a = 0 := by
  ext k; fin_cases k <;> simp [cross3] <;> ring

lemma cross3_sum_right (a : Space3) (s : Finset ι) (c : ι → ℝ) (v : ι → Space3) :
    cross3 a (∑ j ∈ s, c j • v j) = ∑ j ∈ s, c j • cross3 a (v j) := by
  induction s using Finset.induction_on with
  | empty => simp [cross3_zero_right]
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk, cross3_add_right, cross3_smul_right, ih]

lemma cross3_sum_left (a : Space3) (s : Finset ι) (c : ι → ℝ) (v : ι → Space3) :
    cross3 (∑ j ∈ s, c j • v j) a = ∑ j ∈ s, c j • cross3 (v j) a := by
  rw [cross3_swap, cross3_sum_right, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [cross3_swap a (v j), smul_neg]

/-! ## The potential -/

variable (S : Finset ι) (u : ι → Space3) (W : ι → ι → ℝ) (d : Space3)

/-- The explicit potential whose values on the cones are the integrated gradients. -/
def fanPot (x : Space3) : Space3 :=
  ∑ i ∈ S, ∑ j ∈ S, if inCone3 (u i) (u j) d x then
    (-(1 / 2) * W i j * sgnR (vol3 (u i) (u j) d)) • cross3 (u i) (u j) else 0

/-- A point off all planes spanned by two rays, or by a ray and `d`. -/
def GenPt (x : Space3) : Prop :=
  (∀ i ∈ S, ∀ j ∈ S, cross3 (u i) (u j) ≠ 0 → vol3 (u i) (u j) x ≠ 0) ∧
    ∀ i ∈ S, vol3 (u i) x d ≠ 0

/-- A generic segment: generic endpoints, and the segment meets no line through a ray or `d`. -/
def GenPair (x y : Space3) : Prop :=
  GenPt S u d x ∧ GenPt S u d y ∧ (∀ i ∈ S, vol3 x y (u i) ≠ 0) ∧ vol3 x y d ≠ 0

variable {S u W d}

lemma ite_sub_ite_smul (P Q : Prop) [Decidable P] [Decidable Q] (v : Space3) :
    ((if P then v else 0) - if Q then v else 0) =
      ((if P then (1 : ℝ) else 0) - if Q then 1 else 0) • v := by
  split_ifs <;> simp

/-- **The jump formula for the potential.**  Along a generic segment, the potential changes by the
signed crossings of the wedges `u i, u j` weighted by `-½ W i j (u i × u j)`. -/
theorem fanPot_sub (hd : ∀ i ∈ S, ∀ j ∈ S, cross3 (u i) (u j) ≠ 0 → vol3 (u i) (u j) d ≠ 0)
    (hWs : ∀ i j, W i j = W j i) (hker : ∀ i ∈ S, ∑ j ∈ S, W i j • u j = 0) {x y : Space3}
    (hxy : GenPair S u d x y) :
    fanPot S u W d y - fanPot S u W d x =
      ∑ i ∈ S, ∑ j ∈ S, (-(1 / 2) * W i j * wedgeCross (u i) (u j) x y) • cross3 (u i) (u j) := by
  obtain ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩, hxyu, hxyd⟩ := hxy
  have hterm : ∀ i ∈ S, ∀ j ∈ S,
      ((if inCone3 (u i) (u j) d y then
        (-(1 / 2) * W i j * sgnR (vol3 (u i) (u j) d)) • cross3 (u i) (u j) else 0) -
      if inCone3 (u i) (u j) d x then
        (-(1 / 2) * W i j * sgnR (vol3 (u i) (u j) d)) • cross3 (u i) (u j) else 0) =
      (-(1 / 2) * W i j * wedgeCross (u i) (u j) x y) • cross3 (u i) (u j) +
      (-(1 / 2) * wedgeCross (u j) d x y) • (W i j • cross3 (u i) (u j)) +
      (-(1 / 2) * wedgeCross d (u i) x y) • (W i j • cross3 (u i) (u j)) := by
    intro i hi j hj
    rw [ite_sub_ite_smul]
    by_cases hN : cross3 (u i) (u j) = 0
    · simp [hN]
    have hD := hd i hi j hj hN
    have swap : ∀ z, vol3 z (u j) d = -vol3 (u j) z d := fun z => by unfold vol3; ring
    have step := inCone3_step (x := x) (y := y) hD
      (by rw [swap]; exact neg_ne_zero.2 (hx2 j hj)) (hx2 i hi) (hx1 i hi j hj hN)
      (by rw [swap]; exact neg_ne_zero.2 (hy2 j hj)) (hy2 i hi) (hy1 i hi j hj hN)
      (hxyu i hi) (hxyu j hj) hxyd
    rw [step, smul_smul]
    have hs := sgnR_mul_self (vol3 (u i) (u j) d)
    simp only [smul_smul, ← add_smul]
    congr 1
    linear_combination (-(1 / 2) * W i j * (wedgeCross (u i) (u j) x y +
      wedgeCross (u j) d x y + wedgeCross d (u i) x y)) * hs
  unfold fanPot
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => hterm i hi j hj]
  simp only [Finset.sum_add_distrib]
  have h3 : ∑ i ∈ S, ∑ j ∈ S,
      (-(1 / 2) * wedgeCross d (u i) x y) • (W i j • cross3 (u i) (u j)) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [← Finset.smul_sum, ← cross3_sum_right, hker i hi, cross3_zero_right, smul_zero]
  have h2 : ∑ i ∈ S, ∑ j ∈ S,
      (-(1 / 2) * wedgeCross (u j) d x y) • (W i j • cross3 (u i) (u j)) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [← Finset.smul_sum]
    have : ∑ i ∈ S, W i j • cross3 (u i) (u j) = cross3 (∑ i ∈ S, W j i • u i) (u j) := by
      rw [cross3_sum_left]
      exact Finset.sum_congr rfl fun i _ => by rw [hWs]
    rw [this, hker j hj, cross3_swap, cross3_zero_right, neg_zero, smul_zero]
  rw [h2, h3, add_zero, add_zero]

end Erdos99
end

end FanIntegration

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `FanCones`
-/

section FanCones

/-!
# Interiors of the cones of a simplicial fan

Auxiliary facts for the integration of fan matrices (`FanGradientExists`): the open cone
`intCone u τ` over the rays of a cone, its description in Cramer coordinates, openness and
convexity, comparison of coefficients, and the facts that fan edges miss the interiors of the cones,
that two fan edges meet only along common rays, and that the two cones on a common edge lie on
opposite sides of its plane.
-/

open scoped BigOperators
open Filter Topology

@[expose] public noncomputable section

open Classical

namespace Erdos99

variable {ι : Type*} {S : Finset ι} {u : ι → Space3} {T : Finset (Finset ι)}

/-! ## Linear algebra -/

lemma cross3_zero_left (a : Space3) : cross3 0 a = 0 := by
  ext k; fin_cases k <;> simp [cross3]

lemma cross3_cross3_self (a b : Space3) :
    cross3 (cross3 a b) a = (inner ℝ a a) • b - (inner ℝ a b) • a := by
  rw [inner_eq_coords a a, inner_eq_coords a b]
  ext k; fin_cases k <;> simp [cross3] <;> ring

/-- Three linearly independent vectors have nonzero determinant. -/
lemma vol3_ne_zero_of_indep {a b c : Space3} (h : LinearIndependent ℝ ![a, b, c]) :
    vol3 a b c ≠ 0 := by
  intro h0
  have hab : cross3 a b = 0 := eq_zero_of_inner_three h
    (by rw [real_inner_comm, inner_cross3_left]) (by rw [real_inner_comm, inner_cross3_right])
    (by rw [real_inner_comm, inner_cross3, h0])
  have ha : a ≠ 0 := by simpa using h.ne_zero 0
  have key := cross3_cross3_self a b
  rw [hab, cross3_zero_left] at key
  rw [Fintype.linearIndependent_iff] at h
  have h1 := h ![-(inner ℝ a b), inner ℝ a a, 0] (by
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, zero_smul, add_zero, neg_smul]
    rw [key]; abel) 1
  simp only [Matrix.cons_val_one] at h1
  exact ha (inner_self_eq_zero.1 h1)

lemma continuous_vol3_left (b c : Space3) : Continuous fun z => vol3 z b c := by
  have : (fun z => vol3 z b c) = fun z => inner ℝ (cross3 b c) z := by
    funext z; rw [inner_cross3]; unfold vol3; ring
  rw [this]; exact continuous_const.inner continuous_id

lemma continuous_vol3_mid (a c : Space3) : Continuous fun z => vol3 a z c := by
  have : (fun z => vol3 a z c) = fun z => inner ℝ (cross3 c a) z := by
    funext z; rw [inner_cross3]; unfold vol3; ring
  rw [this]; exact continuous_const.inner continuous_id

lemma continuous_vol3_right (a b : Space3) : Continuous fun z => vol3 a b z := by
  have : (fun z => vol3 a b z) = fun z => inner ℝ (cross3 a b) z := by
    funext z; rw [inner_cross3]
  rw [this]; exact continuous_const.inner continuous_id

/-! ## Decomposing the cones -/

lemma sum_three {M : Type*} [AddCommMonoid M] (f : ι → M) {a b c : ι} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) : ∑ k ∈ ({a, b, c} : Finset ι), f k = f a + f b + f c := by
  rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
    Finset.sum_singleton, add_assoc]

/-- A cone containing two given rays is spanned by them and a third ray. -/
lemma IsSimplicialFan.exists_third (hfan : IsSimplicialFan S u T) {τ : Finset ι} (hτ : τ ∈ T)
    {i j : ι} (hi : i ∈ τ) (hj : j ∈ τ) (hij : i ≠ j) :
    ∃ a, a ≠ i ∧ a ≠ j ∧ τ = {i, j, a} := by
  have hj' : j ∈ τ.erase i := Finset.mem_erase.2 ⟨hij.symm, hj⟩
  have h1 : ((τ.erase i).erase j).card = 1 := by
    rw [Finset.card_erase_of_mem hj', Finset.card_erase_of_mem hi, hfan.card τ hτ]
  obtain ⟨a, ha⟩ := Finset.card_eq_one.1 h1
  have haτ : a ∈ (τ.erase i).erase j := by rw [ha]; simp
  simp only [Finset.mem_erase] at haτ
  refine ⟨a, haτ.2.1, haτ.1, ?_⟩
  rw [← Finset.insert_erase hi, ← Finset.insert_erase hj', ha]

/-- A cone containing a given ray is spanned by it and two other rays. -/
lemma IsSimplicialFan.exists_two_others (hfan : IsSimplicialFan S u T) {τ : Finset ι}
    (hτ : τ ∈ T) {k : ι} (hk : k ∈ τ) :
    ∃ p q, p ≠ k ∧ q ≠ k ∧ p ≠ q ∧ τ = {k, p, q} := by
  have h1 : (τ.erase k).card = 2 := by rw [Finset.card_erase_of_mem hk, hfan.card τ hτ]
  obtain ⟨p, q, hpq, he⟩ := Finset.card_eq_two.1 h1
  have hp : p ∈ τ.erase k := by rw [he]; simp
  have hq : q ∈ τ.erase k := by rw [he]; simp
  refine ⟨p, q, (Finset.mem_erase.1 hp).1, (Finset.mem_erase.1 hq).1, hpq, ?_⟩
  rw [← Finset.insert_erase hk, he]

lemma IsSimplicialFan.vol3_ne_zero (hfan : IsSimplicialFan S u T) {a b c : ι} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (hτ : ({a, b, c} : Finset ι) ∈ T) :
    vol3 (u a) (u b) (u c) ≠ 0 :=
  vol3_ne_zero_of_indep (hfan.indep_three hab hac hbc hτ)

/-! ## Interiors of cones -/

/-- The open cone spanned by the rays `u k`, `k ∈ τ`. -/
def intCone (u : ι → Space3) (τ : Finset ι) : Set Space3 :=
  {z | ∃ c : ι → ℝ, (∀ k ∈ τ, 0 < c k) ∧ z = ∑ k ∈ τ, c k • u k}

lemma intCone_subset_finCone (τ : Finset ι) : intCone u τ ⊆ finCone u τ := by
  rintro z ⟨c, hc, rfl⟩; exact ⟨c, fun k hk => (hc k hk).le, rfl⟩

lemma finCone_mono {B C : Finset ι} (hBC : B ⊆ C) : finCone u B ⊆ finCone u C := by
  rintro z ⟨c, hc, rfl⟩
  refine ⟨fun m => if m ∈ B then c m else 0, fun m _ => ?_, (sum_extend_smul u hBC c).symm⟩
  dsimp only; split_ifs with h
  · exact hc m h
  · exact le_refl 0

lemma mem_finCone_pair {i j : ι} (hij : i ≠ j) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    α • u i + β • u j ∈ finCone u {i, j} := by
  refine ⟨fun m => if m = i then α else β, fun m _ => by dsimp only; split_ifs <;> assumption, ?_⟩
  rw [Finset.sum_pair hij]; simp [hij.symm]

lemma mem_intCone_three {a b c : ι} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {α β γ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) :
    α • u a + β • u b + γ • u c ∈ intCone u {a, b, c} := by
  refine ⟨fun m => if m = a then α else if m = b then β else γ, fun m hm => ?_, ?_⟩
  · dsimp only; split_ifs <;> assumption
  · rw [sum_three _ hab hac hbc]; simp [hab.symm, hac.symm, hbc.symm]

/-- The open cone over three independent rays in Cramer coordinates. -/
lemma mem_intCone_three_iff {a b c : ι} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hD : vol3 (u a) (u b) (u c) ≠ 0) (z : Space3) :
    z ∈ intCone u {a, b, c} ↔ 0 < vol3 z (u b) (u c) / vol3 (u a) (u b) (u c) ∧
      0 < vol3 (u a) z (u c) / vol3 (u a) (u b) (u c) ∧
      0 < vol3 (u a) (u b) z / vol3 (u a) (u b) (u c) := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [sum_three _ hab hac hbc]
    have e1 : vol3 (w a • u a + w b • u b + w c • u c) (u b) (u c) =
        w a * vol3 (u a) (u b) (u c) := by
      simp only [vol3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    have e2 : vol3 (u a) (w a • u a + w b • u b + w c • u c) (u c) =
        w b * vol3 (u a) (u b) (u c) := by
      simp only [vol3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    have e3 : vol3 (u a) (u b) (w a • u a + w b • u b + w c • u c) =
        w c * vol3 (u a) (u b) (u c) := by
      simp only [vol3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [e1, e2, e3, mul_div_cancel_right₀ _ hD, mul_div_cancel_right₀ _ hD,
      mul_div_cancel_right₀ _ hD]
    exact ⟨hw a (by simp), hw b (by simp), hw c (by simp)⟩
  · rintro ⟨h1, h2, h3⟩
    have hz : z = (vol3 z (u b) (u c) / vol3 (u a) (u b) (u c)) • u a +
        (vol3 (u a) z (u c) / vol3 (u a) (u b) (u c)) • u b +
        (vol3 (u a) (u b) z / vol3 (u a) (u b) (u c)) • u c := by
      have hc := cramer3 (u a) (u b) (u c) z
      calc z = (vol3 (u a) (u b) (u c))⁻¹ • (vol3 (u a) (u b) (u c) • z) := by
            rw [smul_smul, inv_mul_cancel₀ hD, one_smul]
        _ = _ := by
            rw [hc, smul_add, smul_add, smul_smul, smul_smul, smul_smul, div_eq_inv_mul,
              div_eq_inv_mul, div_eq_inv_mul]
    rw [hz]; exact mem_intCone_three hab hac hbc h1 h2 h3

lemma IsSimplicialFan.isOpen_intCone (hfan : IsSimplicialFan S u T) {τ : Finset ι}
    (hτ : τ ∈ T) : IsOpen (intCone u τ) := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.1 (hfan.card _ hτ)
  have hD := hfan.vol3_ne_zero hab hac hbc hτ
  have : intCone u {a, b, c} = {z | 0 < vol3 z (u b) (u c) / vol3 (u a) (u b) (u c)} ∩
      {z | 0 < vol3 (u a) z (u c) / vol3 (u a) (u b) (u c)} ∩
      {z | 0 < vol3 (u a) (u b) z / vol3 (u a) (u b) (u c)} := by
    ext z; rw [mem_intCone_three_iff hab hac hbc hD]; simp [and_assoc]
  rw [this]
  refine ((isOpen_lt continuous_const ?_).inter (isOpen_lt continuous_const ?_)).inter
    (isOpen_lt continuous_const ?_)
  · exact (continuous_vol3_left _ _).div_const _
  · exact (continuous_vol3_mid _ _).div_const _
  · exact (continuous_vol3_right _ _).div_const _

/-- The open cone is convex. -/
lemma intCone_segment {τ : Finset ι} {x y : Space3} (hx : x ∈ intCone u τ)
    (hy : y ∈ intCone u τ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    x + t • (y - x) ∈ intCone u τ := by
  obtain ⟨c, hc, rfl⟩ := hx
  obtain ⟨c', hc', rfl⟩ := hy
  refine ⟨fun k => (1 - t) * c k + t * c' k, fun k hk => ?_, ?_⟩
  · rcases ht1.lt_or_eq with h | h
    · have := mul_pos (sub_pos.2 h) (hc k hk)
      have := mul_nonneg ht0 (hc' k hk).le
      dsimp only; linarith
    · subst h; simp [hc' k hk]
  · simp only [add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum]
    module

/-! ## Coefficients -/

/-- Comparing coefficients: a point of the cone over `B ⊆ σ` has zero `σ`-coefficients outside
`B`. -/
lemma IsSimplicialFan.coeff_zero_of_mem (hfan : IsSimplicialFan S u T) {σ B : Finset ι}
    (hσ : σ ∈ T) (hB : B ⊆ σ) {z : Space3} (hz : z ∈ finCone u B) (c : ι → ℝ)
    (hzc : z = ∑ e ∈ σ, c e • u e) : ∀ e ∈ σ, e ∉ B → c e = 0 := by
  obtain ⟨w, -, hw⟩ := hz
  intro e he heB
  have := hfan.coeff_eq_zero hσ (fun m => (if m ∈ B then w m else 0) - c m) (by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [sum_extend_smul u hB, ← hw, ← hzc, sub_self]) e he
  simpa [heB] using this

/-- An interior point of a cone lies on no proper face. -/
lemma IsSimplicialFan.subset_of_int (hfan : IsSimplicialFan S u T) {τ B : Finset ι}
    (hτ : τ ∈ T) {z : Space3} (hz : z ∈ intCone u τ) (hB : B ⊆ τ) (hzB : z ∈ finCone u B) :
    τ ⊆ B := by
  obtain ⟨c, hc, hzc⟩ := hz
  intro k hk
  by_contra hkB
  have := hfan.coeff_zero_of_mem hτ hB hzB c hzc k hk hkB
  linarith [hc k hk]

/-- **Fan edges miss the interiors of the cones.** -/
lemma IsSimplicialFan.not_mem_edge_of_int (hfan : IsSimplicialFan S u T) {τ : Finset ι}
    (hτ : τ ∈ T) {z : Space3} (hz : z ∈ intCone u τ) {k l : ι} (hkl : FanEdge T k l)
    (hzkl : z ∈ finCone u {k, l}) : False := by
  obtain ⟨hne, σ, hσ, hk, hl⟩ := hkl
  have hsub : ({k, l} : Finset ι) ⊆ σ := by
    intro m hm; simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl <;> assumption
  have hI : z ∈ finCone u (τ ∩ σ) := by
    rw [← hfan.inter τ hτ σ hσ]
    exact ⟨intCone_subset_finCone τ hz, finCone_mono hsub hzkl⟩
  have h1 := hfan.subset_of_int hτ hz Finset.inter_subset_left hI
  have hτσ : τ = σ := Finset.eq_of_subset_of_card_le (h1.trans Finset.inter_subset_right)
    (by rw [hfan.card σ hσ, hfan.card τ hτ])
  subst hτσ
  have h2 := Finset.card_le_card (hfan.subset_of_int hτ hz hsub hzkl)
  rw [hfan.card τ hτ] at h2
  have := Finset.card_le_two (a := k) (b := l)
  omega

/-- **Two fan edges meet only along common rays**: the midpoint direction `u i + u j` of a fan
edge lies on no other fan edge. -/
lemma IsSimplicialFan.edge_mid_not_mem (hfan : IsSimplicialFan S u T) {i j k l : ι}
    (hij : FanEdge T i j) (hkl : FanEdge T k l) (hne : ({k, l} : Finset ι) ≠ {i, j}) :
    u i + u j ∉ finCone u {k, l} := by
  intro hm
  obtain ⟨hij', ρ, hρ, hiρ, hjρ⟩ := hij
  obtain ⟨hkl', σ, hσ, hkσ, hlσ⟩ := hkl
  have hsub : ({k, l} : Finset ι) ⊆ σ := by
    intro m hm; simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl <;> assumption
  have hrep : ∀ τ : Finset ι, i ∈ τ → j ∈ τ →
      u i + u j = ∑ e ∈ τ, ((if e = i then (1 : ℝ) else 0) + if e = j then 1 else 0) • u e := by
    intro τ hi hj
    simp only [add_smul, Finset.sum_add_distrib]
    rw [sum_indicator_smul u hi, sum_indicator_smul u hj]
  have hmρ : u i + u j ∈ finCone u ρ :=
    ⟨_, fun e _ => by split_ifs <;> norm_num, hrep ρ hiρ hjρ⟩
  have hI : u i + u j ∈ finCone u (ρ ∩ σ) := by
    rw [← hfan.inter ρ hρ σ hσ]; exact ⟨hmρ, finCone_mono hsub hm⟩
  have hiσ : i ∈ σ := by
    by_contra h
    have := hfan.coeff_zero_of_mem hρ Finset.inter_subset_left hI _ (hrep ρ hiρ hjρ) i hiρ
      (fun h' => h (Finset.mem_inter.1 h').2)
    simp [hij'] at this
  have hjσ : j ∈ σ := by
    by_contra h
    have := hfan.coeff_zero_of_mem hρ Finset.inter_subset_left hI _ (hrep ρ hiρ hjρ) j hjρ
      (fun h' => h (Finset.mem_inter.1 h').2)
    simp [hij'.symm] at this
  have hi : i ∈ ({k, l} : Finset ι) := by
    by_contra h
    have := hfan.coeff_zero_of_mem hσ hsub hm _ (hrep σ hiσ hjσ) i hiσ h
    simp [hij'] at this
  have hj : j ∈ ({k, l} : Finset ι) := by
    by_contra h
    have := hfan.coeff_zero_of_mem hσ hsub hm _ (hrep σ hiσ hjσ) j hjσ h
    simp [hij'.symm] at this
  apply hne
  symm
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro m hm; simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl <;> assumption
  · rw [Finset.card_pair hij']; exact Finset.card_le_two

/-- **The two cones on a common edge lie on opposite sides of its plane.** -/
lemma IsSimplicialFan.opposite_sides (hfan : IsSimplicialFan S u T) {i j a b : ι}
    (hij : i ≠ j) (hai : a ≠ i) (haj : a ≠ j) (hbi : b ≠ i) (hbj : b ≠ j) (hab : a ≠ b)
    (hτ : ({i, j, a} : Finset ι) ∈ T) (hτ' : ({i, j, b} : Finset ι) ∈ T) :
    vol3 (u i) (u j) (u a) * vol3 (u i) (u j) (u b) < 0 := by
  have hPa := hfan.vol3_ne_zero hij hai.symm haj.symm hτ
  have hPb := hfan.vol3_ne_zero hij hbi.symm hbj.symm hτ'
  by_contra hcon
  push_neg at hcon
  have hprod : 0 < vol3 (u i) (u j) (u a) * vol3 (u i) (u j) (u b) :=
    lt_of_le_of_ne hcon (mul_ne_zero hPa hPb).symm
  set Pb := vol3 (u i) (u j) (u b)
  set α := vol3 (u a) (u j) (u b) / Pb
  set β := vol3 (u i) (u a) (u b) / Pb
  set γ := vol3 (u i) (u j) (u a) / Pb
  have hγ : 0 < γ := by
    have : γ = vol3 (u i) (u j) (u a) * Pb / Pb ^ 2 := by
      simp only [γ]; field_simp
    rw [this]; exact div_pos hprod (by positivity)
  have hua : u a = α • u i + β • u j + γ • u b := by
    have hc := cramer3 (u i) (u j) (u b) (u a)
    calc u a = Pb⁻¹ • (Pb • u a) := by rw [smul_smul, inv_mul_cancel₀ hPb, one_smul]
      _ = _ := by
          rw [hc, smul_add, smul_add, smul_smul, smul_smul, smul_smul]
          simp only [α, β, γ, div_eq_inv_mul]
  set ε := 1 / (1 + |α| + |β|)
  have hden : 0 < 1 + |α| + |β| := by positivity
  have hε : 0 < ε := by positivity
  have hεα : 0 < 1 + ε * α := by
    have : ε * |α| < 1 := by
      rw [div_mul_eq_mul_div, one_mul, div_lt_one hden]; linarith [abs_nonneg β]
    nlinarith [neg_abs_le α, abs_nonneg α]
  have hεβ : 0 < 1 + ε * β := by
    have : ε * |β| < 1 := by
      rw [div_mul_eq_mul_div, one_mul, div_lt_one hden]; linarith [abs_nonneg α]
    nlinarith [neg_abs_le β, abs_nonneg β]
  set w := (1 : ℝ) • u i + (1 : ℝ) • u j + ε • u a
  have hw : w ∈ intCone u {i, j, a} :=
    mem_intCone_three hij hai.symm haj.symm one_pos one_pos hε
  have hw' : w ∈ intCone u {i, j, b} := by
    have : w = (1 + ε * α) • u i + (1 + ε * β) • u j + (ε * γ) • u b := by
      simp only [w, hua]; module
    rw [this]; exact mem_intCone_three hij hbi.symm hbj.symm hεα hεβ (mul_pos hε hγ)
  have hI : w ∈ finCone u ({i, j, a} ∩ {i, j, b}) := by
    rw [← hfan.inter _ hτ _ hτ']
    exact ⟨intCone_subset_finCone _ hw, intCone_subset_finCone _ hw'⟩
  have hsub := hfan.subset_of_int hτ hw Finset.inter_subset_left hI
  have : a ∈ ({i, j, b} : Finset ι) := (Finset.mem_inter.1 (hsub (by simp))).2
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with h | h | h
  · exact hai h
  · exact haj h
  · exact hab h

end Erdos99
end

end FanCones

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `FanGradientExists`
-/

section FanGradientExists

/-!
# Existence of integrated gradients for a fan matrix (Verification Guide §7.3 (b))

`fan_gradient_exists`: for a complete simplicial fan in which every ray lies in a cone, and a
symmetric matrix `W` supported (off the diagonal) on fan edges with `∑ⱼ W i j u j = 0`, there are
gradients `g τ` (one per cone) forming the integrated gradients `FanGradient T u W g`.

The gradient of the cone `τ` is the value of the explicit potential `fanPot` (`FanIntegration`)
at a generic interior point of `τ`.  By the jump formula `fanPot_sub`:

* the potential is constant on generic points of the interior of a cone, since fan edges miss the
  interiors (`IsSimplicialFan.not_mem_edge_of_int`);
* near a ray `u k` only fan edges containing `k` occur, and their jump vectors are orthogonal to
  `u k` (continuity);
* near the midpoint direction `u i + u j` of a common edge of two cones only the wedge `u i, u j`
  occurs (`IsSimplicialFan.edge_mid_not_mem`), and it is crossed once, from the first cone to the
  second (`IsSimplicialFan.opposite_sides`), which gives the prescribed jump.
-/

open scoped BigOperators
open Filter Topology

@[expose] public noncomputable section

open Classical

namespace Erdos99

variable {ι : Type*} {S : Finset ι} {u : ι → Space3} {T : Finset (Finset ι)} {W : ι → ι → ℝ}
  {d : Space3}

/-! ## Generic points -/

lemma vol3_eq_inner_mid (a z c : Space3) : vol3 a z c = inner ℝ (cross3 c a) z := by
  rw [inner_cross3]; unfold vol3; ring

/-- Generic points exist in every nonempty open set, also relative to finitely many given generic
points. -/
lemma exists_genPt_pair (hdS : ∀ i ∈ S, cross3 d (u i) ≠ 0) (hSne : S.Nonempty) {U : Set Space3}
    (hU : IsOpen U) (hne : U.Nonempty) (xs : Finset Space3) (hxs : ∀ x ∈ xs, GenPt S u d x) :
    ∃ y ∈ U, GenPt S u d y ∧ ∀ x ∈ xs, GenPair S u d x y := by
  obtain ⟨y, hyU, hy⟩ := exists_avoid_planes hU hne
    ((S ×ˢ S).image (fun p => cross3 (u p.1) (u p.2)) ∪ S.image (fun i => cross3 d (u i)) ∪
      (xs ×ˢ S).image (fun p => cross3 (u p.2) p.1) ∪ xs.image (fun x => cross3 d x))
  have hgy : GenPt S u d y := by
    refine ⟨fun i hi j hj hN => ?_, fun i hi => ?_⟩
    · rw [vol3_eq_inner_cross]
      exact hy _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_image_of_mem (fun p : ι × ι => cross3 (u p.1) (u p.2))
          (show (i, j) ∈ S ×ˢ S from Finset.mem_product.2 ⟨hi, hj⟩))))) hN
    · rw [vol3_eq_inner_mid]
      exact hy _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_image_of_mem (fun i => cross3 d (u i)) hi)))) (hdS i hi)
  refine ⟨y, hyU, hgy, fun x hx => ⟨hxs x hx, hgy, fun i hi => ?_, ?_⟩⟩
  · have e : vol3 x y (u i) = inner ℝ (cross3 (u i) x) y := by
      rw [inner_cross3]; unfold vol3; ring
    rw [e]
    refine hy _ (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image_of_mem (fun p : Space3 × ι => cross3 (u p.2) p.1)
        (show (x, i) ∈ xs ×ˢ S from Finset.mem_product.2 ⟨hx, hi⟩)))) ?_
    intro h0
    apply (hxs x hx).2 i hi
    rw [vol3_eq_inner_cross, h0, inner_zero_left]
  · have e : vol3 x y d = inner ℝ (cross3 d x) y := by rw [inner_cross3]; unfold vol3; ring
    rw [e]
    refine hy _ (Finset.mem_union_right _ (Finset.mem_image_of_mem (fun x => cross3 d x) hx)) ?_
    intro h0
    obtain ⟨i0, hi0⟩ := hSne
    apply (hxs x hx).2 i0 hi0
    have : vol3 (u i0) x d = -inner ℝ (cross3 d x) (u i0) := by
      rw [inner_cross3]; unfold vol3; ring
    rw [this, h0, inner_zero_left, neg_zero]

/-- If a generic segment meets no wedge `u i, u j` with `W i j ≠ 0`, the potential takes the same
value at its endpoints. -/
lemma fanPot_eq_of_no_cross
    (hd : ∀ i ∈ S, ∀ j ∈ S, cross3 (u i) (u j) ≠ 0 → vol3 (u i) (u j) d ≠ 0)
    (hWs : ∀ i j, W i j = W j i) (hker : ∀ i ∈ S, ∑ j ∈ S, W i j • u j = 0) {x y : Space3}
    (hxy : GenPair S u d x y)
    (hno : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → W i j ≠ 0 → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      x + t • (y - x) ∉ finCone u {i, j}) :
    fanPot S u W d y = fanPot S u W d x := by
  rw [← sub_eq_zero, fanPot_sub hd hWs hker hxy]
  refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_
  by_cases hij : i = j
  · subst hij; rw [cross3_self, smul_zero]
  by_cases hW : W i j = 0
  · simp [hW]
  have : wedgeCross (u i) (u j) x y = 0 := by
    by_contra h
    obtain ⟨t, ht0, ht1, α, β, hα, hβ, he⟩ := wedgeCross_ne_zero h
    exact hno i hi j hj hij hW t ht0 ht1 (by rw [he]; exact mem_finCone_pair hij hα hβ)
  simp [this]

lemma double_sum_single {M : Type*} [AddCommMonoid M] (S : Finset ι) {i j : ι} (hi : i ∈ S)
    (hj : j ∈ S) (A : M) : ∑ i' ∈ S, ∑ j' ∈ S, (if i' = i ∧ j' = j then A else 0) = A := by
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd hj h
  · intro b _ hb; simp [hb]
  · intro h; exact absurd hi h

lemma pair_ne_of {i j i' j' : ι} (hij : i' ≠ j') (h1 : ¬ (i' = i ∧ j' = j))
    (h2 : ¬ (i' = j ∧ j' = i)) : ({i', j'} : Finset ι) ≠ {i, j} := by
  intro heq
  have hi' : i' ∈ ({i, j} : Finset ι) := heq ▸ (by simp)
  have hj' : j' ∈ ({i, j} : Finset ι) := heq ▸ (by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi' hj'
  rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl <;> tauto

/-- A point near `c`: `c + ε v` is within `r` of `c` for `ε = r / (2 (‖v‖ + 1))`. -/
lemma dist_add_smul_lt (c v : Space3) {r : ℝ} (hr : 0 < r) :
    dist (c + (r / (2 * (‖v‖ + 1))) • v) c < r := by
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul,
    Real.norm_of_nonneg (by positivity)]
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith [norm_nonneg v]

/-! ## The integrated gradients -/

/-- **Step (b): integrating the gradient jumps of a fan matrix.**  For a complete simplicial fan
in which every ray lies in some cone, and a symmetric `W` supported off the diagonal on fan edges
with `∑ⱼ W i j u j = 0`, there are integrated gradients `g` (`FanGradient T u W g`). -/
theorem fan_gradient_exists (hfan : IsSimplicialFan S u T) (hused : ∀ i ∈ S, ∃ τ ∈ T, i ∈ τ)
    (hWs : ∀ i j, W i j = W j i)
    (hsupp : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → W i j ≠ 0 → FanEdge T i j)
    (hker : ∀ i ∈ S, ∑ j ∈ S, W i j • u j = 0) :
    ∃ g : Finset ι → Space3, FanGradient T u W g := by
  -- `S` is nonempty
  obtain ⟨τ0, hτ0, -⟩ := hfan.complete 0
  have hSne : S.Nonempty := by
    obtain ⟨a, b, c, -, -, -, he⟩ := Finset.card_eq_three.1 (hfan.card _ hτ0)
    exact ⟨a, hfan.subset _ hτ0 (by rw [he]; simp)⟩
  -- a generic direction `d`
  obtain ⟨d, -, hd0⟩ := exists_avoid_planes isOpen_univ Set.univ_nonempty
    ((S ×ˢ S).image fun p => cross3 (u p.1) (u p.2))
  have hd : ∀ i ∈ S, ∀ j ∈ S, cross3 (u i) (u j) ≠ 0 → vol3 (u i) (u j) d ≠ 0 :=
    fun i hi j hj hN => by
      rw [vol3_eq_inner_cross]
      exact hd0 _ (Finset.mem_image_of_mem (fun p : ι × ι => cross3 (u p.1) (u p.2))
        (show (i, j) ∈ S ×ˢ S from Finset.mem_product.2 ⟨hi, hj⟩)) hN
  have hdS : ∀ i ∈ S, cross3 d (u i) ≠ 0 := by
    intro i hi h0
    obtain ⟨τ, hτ, hiτ⟩ := hused i hi
    obtain ⟨p, q, hpi, hqi, hpq, rfl⟩ := hfan.exists_two_others hτ hiτ
    have hD := hfan.vol3_ne_zero hpi.symm hqi.symm hpq hτ
    have hp : p ∈ S := hfan.subset _ hτ (by simp)
    apply hd i hi p hp (cross3_ne_zero_of_vol3 hD)
    have : vol3 (u i) (u p) d = inner ℝ (cross3 d (u i)) (u p) := by
      rw [inner_cross3]; unfold vol3; ring
    rw [this, h0, inner_zero_left]
  -- generic interior points
  have hex : ∀ τ ∈ T, ∃ x ∈ intCone u τ, GenPt S u d x := by
    intro τ hτ
    have hne : (intCone u τ).Nonempty := by
      obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.1 (hfan.card _ hτ)
      exact ⟨_, mem_intCone_three (u := u) hab hac hbc one_pos one_pos one_pos⟩
    obtain ⟨x, hx, hgx, -⟩ := exists_genPt_pair hdS hSne (hfan.isOpen_intCone hτ) hne ∅
      (by simp)
    exact ⟨x, hx, hgx⟩
  choose! xτ hxτ hgxτ using hex
  -- the potential is constant on the generic points of the interior of a cone
  have hconst : ∀ τ ∈ T, ∀ x ∈ intCone u τ, GenPt S u d x →
      fanPot S u W d x = fanPot S u W d (xτ τ) := by
    intro τ hτ x hx hgx
    obtain ⟨y, hy, -, hpair⟩ := exists_genPt_pair hdS hSne (hfan.isOpen_intCone hτ) ⟨x, hx⟩
      {x, xτ τ} (by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        exacts [hgx, hgxτ τ hτ])
    have key : ∀ z ∈ intCone u τ, GenPair S u d z y → fanPot S u W d y = fanPot S u W d z := by
      intro z hz hzy
      refine fanPot_eq_of_no_cross hd hWs hker hzy fun i hi j hj hij hW t ht0 ht1 hmem => ?_
      exact hfan.not_mem_edge_of_int hτ (intCone_segment hz hy ht0 ht1)
        (hsupp i hi j hj hij hW) hmem
    rw [← key x hx (hpair x (by simp)), key (xτ τ) (hxτ τ hτ) (hpair _ (by simp))]
  refine ⟨fun τ => fanPot S u W d (xτ τ), ⟨?_, ?_⟩⟩
  · ------------------------------------------------------------------ continuity
    intro τ hτ τ' hτ' k hk hk'
    set P := (S ×ˢ S).filter fun p : ι × ι => p.1 ≠ p.2 ∧ W p.1 p.2 ≠ 0 ∧ p.1 ≠ k ∧ p.2 ≠ k
    have hQ : IsClosed (⋃ p ∈ P, finCone u {p.1, p.2}) :=
      isClosed_biUnion_finset fun p _ => isClosed_finCone u _
    have hkQ : u k ∉ ⋃ p ∈ P, finCone u {p.1, p.2} := by
      simp only [Set.mem_iUnion, not_exists]
      intro p hp hmem
      rw [Finset.mem_filter, Finset.mem_product] at hp
      obtain ⟨⟨h1, h2⟩, hne, hW, hk1, hk2⟩ := hp
      obtain ⟨-, σ, hσ, hp1, hp2⟩ := hsupp _ h1 _ h2 hne hW
      refine hfan.ray_not_mem_finCone ⟨τ, hτ, hk⟩ hσ (B := {p.1, p.2}) ?_ ?_ hmem
      · intro m hm; simp only [Finset.mem_insert, Finset.mem_singleton] at hm
        rcases hm with rfl | rfl <;> assumption
      · simp [Ne.symm hk1, Ne.symm hk2]
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hQ.isOpen_compl (u k) hkQ
    have hne_int : ∀ σ ∈ T, k ∈ σ → (intCone u σ ∩ Metric.ball (u k) r).Nonempty := by
      intro σ hσ hkσ
      obtain ⟨p, q, hpk, hqk, hpq, rfl⟩ := hfan.exists_two_others hσ hkσ
      set ε := r / (2 * (‖u p + u q‖ + 1))
      have hε : 0 < ε := by positivity
      refine ⟨(1 : ℝ) • u k + ε • u p + ε • u q,
        mem_intCone_three hpk.symm hqk.symm hpq one_pos hε hε, ?_⟩
      have : (1 : ℝ) • u k + ε • u p + ε • u q = u k + ε • (u p + u q) := by module
      rw [Metric.mem_ball, this]
      exact dist_add_smul_lt _ _ hr
    obtain ⟨x, ⟨hx, hxb⟩, hgx, -⟩ := exists_genPt_pair hdS hSne
      ((hfan.isOpen_intCone hτ).inter Metric.isOpen_ball) (hne_int τ hτ hk) ∅ (by simp)
    obtain ⟨y, ⟨hy, hyb⟩, -, hpair⟩ := exists_genPt_pair hdS hSne
      ((hfan.isOpen_intCone hτ').inter Metric.isOpen_ball) (hne_int τ' hτ' hk') {x}
      (by simpa using hgx)
    have hxy := hpair x (Finset.mem_singleton_self x)
    show inner ℝ (u k) (fanPot S u W d (xτ τ)) = inner ℝ (u k) (fanPot S u W d (xτ τ'))
    rw [← hconst τ hτ x hx hgx, ← hconst τ' hτ' y hy hxy.2.1, eq_comm, ← sub_eq_zero,
      ← inner_sub_right,
      fanPot_sub hd hWs hker hxy, inner_sum]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [inner_sum]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [inner_smul_right]
    by_cases hik : i = k
    · subst hik; rw [real_inner_comm, inner_cross3_left, mul_zero]
    by_cases hjk : j = k
    · subst hjk; rw [real_inner_comm, inner_cross3_right, mul_zero]
    by_cases hij : i = j
    · subst hij; rw [cross3_self, inner_zero_right, mul_zero]
    by_cases hW : W i j = 0
    · simp [hW]
    have : wedgeCross (u i) (u j) x y = 0 := by
      by_contra h
      obtain ⟨t, ht0, ht1, α, β, hα, hβ, he⟩ := wedgeCross_ne_zero h
      have hmem : x + t • (y - x) ∈ Metric.ball (u k) r :=
        (convex_ball (u k) r).add_smul_sub_mem hxb hyb ⟨ht0, ht1⟩
      apply hball hmem
      simp only [Set.mem_iUnion]
      exact ⟨(i, j), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hi, hj⟩, hij, hW, hik, hjk⟩,
        by rw [he]; exact mem_finCone_pair hij hα hβ⟩
    simp [this]
  · ------------------------------------------------------------------ jumps
    intro τ hτ τ' hτ' hne i hi j hj hij hi' hj' b hb hbi hbj
    obtain ⟨a, hai, haj, rfl⟩ := hfan.exists_third hτ hi hj hij
    obtain ⟨b', hb'i, hb'j, rfl⟩ := hfan.exists_third hτ' hi' hj' hij
    have hbb : b = b' := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with h | h | h
      · exact absurd h hbi
      · exact absurd h hbj
      · exact h
    subst hbb
    have hab : a ≠ b := fun h => hne (by rw [h])
    have hiS : i ∈ S := hfan.subset _ hτ (by simp)
    have hjS : j ∈ S := hfan.subset _ hτ (by simp)
    have hPa := hfan.vol3_ne_zero hij hai.symm haj.symm hτ
    have hPb := hfan.vol3_ne_zero hij hbi.symm hbj.symm hτ'
    have hopp := hfan.opposite_sides hij hai haj hbi hbj hab hτ hτ'
    have hN : cross3 (u i) (u j) ≠ 0 := cross3_ne_zero_of_vol3 hPa
    have hNpos : 0 < vol3 (u i) (u j) (cross3 (u i) (u j)) := vol3_cross_pos hN
    have hN'pos : 0 < vol3 (u j) (u i) (cross3 (u j) (u i)) :=
      vol3_cross_pos (by rw [cross3_swap]; exact neg_ne_zero.2 hN)
    -- the other fan edges stay away from `u i + u j`
    set P := (S ×ˢ S).filter fun p : ι × ι =>
      p.1 ≠ p.2 ∧ W p.1 p.2 ≠ 0 ∧ ({p.1, p.2} : Finset ι) ≠ {i, j}
    have hQ : IsClosed (⋃ p ∈ P, finCone u {p.1, p.2}) :=
      isClosed_biUnion_finset fun p _ => isClosed_finCone u _
    have hmQ : u i + u j ∉ ⋃ p ∈ P, finCone u {p.1, p.2} := by
      simp only [Set.mem_iUnion, not_exists]
      intro p hp hmem
      rw [Finset.mem_filter, Finset.mem_product] at hp
      obtain ⟨⟨h1, h2⟩, hne', hW, hpair⟩ := hp
      exact hfan.edge_mid_not_mem ⟨hij, _, hτ, by simp, by simp⟩ (hsupp _ h1 _ h2 hne' hW)
        hpair hmem
    set O := (⋃ p ∈ P, finCone u {p.1, p.2})ᶜ ∩
      {w | 0 < vol3 w (u j) (cross3 (u i) (u j))} ∩ {w | 0 < vol3 (u i) w (cross3 (u i) (u j))} ∩
      {w | 0 < vol3 w (u i) (cross3 (u j) (u i))} ∩ {w | 0 < vol3 (u j) w (cross3 (u j) (u i))}
    have hO : IsOpen O :=
      (((hQ.isOpen_compl.inter (isOpen_lt continuous_const (continuous_vol3_left _ _))).inter
        (isOpen_lt continuous_const (continuous_vol3_mid _ _))).inter
        (isOpen_lt continuous_const (continuous_vol3_left _ _))).inter
        (isOpen_lt continuous_const (continuous_vol3_mid _ _))
    have hmO : u i + u j ∈ O := by
      refine ⟨⟨⟨⟨hmQ, ?_⟩, ?_⟩, ?_⟩, ?_⟩
      · show 0 < vol3 (u i + u j) (u j) (cross3 (u i) (u j))
        have : vol3 (u i + u j) (u j) (cross3 (u i) (u j)) =
            vol3 (u i) (u j) (cross3 (u i) (u j)) := by
          simp only [vol3, PiLp.add_apply]; ring
        rw [this]; exact hNpos
      · show 0 < vol3 (u i) (u i + u j) (cross3 (u i) (u j))
        have : vol3 (u i) (u i + u j) (cross3 (u i) (u j)) =
            vol3 (u i) (u j) (cross3 (u i) (u j)) := by
          simp only [vol3, PiLp.add_apply]; ring
        rw [this]; exact hNpos
      · show 0 < vol3 (u i + u j) (u i) (cross3 (u j) (u i))
        have : vol3 (u i + u j) (u i) (cross3 (u j) (u i)) =
            vol3 (u j) (u i) (cross3 (u j) (u i)) := by
          simp only [vol3, PiLp.add_apply]; ring
        rw [this]; exact hN'pos
      · show 0 < vol3 (u j) (u i + u j) (cross3 (u j) (u i))
        have : vol3 (u j) (u i + u j) (cross3 (u j) (u i)) =
            vol3 (u j) (u i) (cross3 (u j) (u i)) := by
          simp only [vol3, PiLp.add_apply]; ring
        rw [this]; exact hN'pos
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hO _ hmO
    have hne_int : ∀ c, c ≠ i → c ≠ j → ({i, j, c} : Finset ι) ∈ T →
        (intCone u {i, j, c} ∩ Metric.ball (u i + u j) r).Nonempty := by
      intro c hci hcj _
      set ε := r / (2 * (‖u c‖ + 1))
      have hε : 0 < ε := by positivity
      refine ⟨(1 : ℝ) • u i + (1 : ℝ) • u j + ε • u c,
        mem_intCone_three hij hci.symm hcj.symm one_pos one_pos hε, ?_⟩
      have : (1 : ℝ) • u i + (1 : ℝ) • u j + ε • u c = (u i + u j) + ε • u c := by module
      rw [Metric.mem_ball, this]
      exact dist_add_smul_lt _ _ hr
    obtain ⟨x, ⟨hx, hxb⟩, hgx, -⟩ := exists_genPt_pair hdS hSne
      ((hfan.isOpen_intCone hτ).inter Metric.isOpen_ball) (hne_int a hai haj hτ) ∅ (by simp)
    obtain ⟨y, ⟨hy, hyb⟩, -, hpair⟩ := exists_genPt_pair hdS hSne
      ((hfan.isOpen_intCone hτ').inter Metric.isOpen_ball) (hne_int b hbi hbj hτ') {x}
      (by simpa using hgx)
    have hxy := hpair x (Finset.mem_singleton_self x)
    have hseg : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → x + t • (y - x) ∈ O := fun t ht0 ht1 =>
      hball ((convex_ball _ r).add_smul_sub_mem hxb hyb ⟨ht0, ht1⟩)
    -- the potential difference
    have hsum : fanPot S u W d y - fanPot S u W d x =
        (-(1 / 2) * W i j * wedgeCross (u i) (u j) x y) • cross3 (u i) (u j) +
        (-(1 / 2) * W j i * wedgeCross (u j) (u i) x y) • cross3 (u j) (u i) := by
      rw [fanPot_sub hd hWs hker hxy]
      rw [← double_sum_single S hiS hjS ((-(1 / 2) * W i j * wedgeCross (u i) (u j) x y) •
          cross3 (u i) (u j)),
        ← double_sum_single S hjS hiS ((-(1 / 2) * W j i * wedgeCross (u j) (u i) x y) •
          cross3 (u j) (u i)), ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i' hi' => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j' hj' => ?_
      by_cases h1 : i' = i ∧ j' = j
      · obtain ⟨rfl, rfl⟩ := h1
        rw [if_pos ⟨rfl, rfl⟩, if_neg (fun h => hij h.1), add_zero]
      by_cases h2 : i' = j ∧ j' = i
      · obtain ⟨rfl, rfl⟩ := h2
        rw [if_neg h1, if_pos ⟨rfl, rfl⟩, zero_add]
      rw [if_neg h1, if_neg h2, add_zero]
      by_cases hij' : i' = j'
      · subst hij'; rw [cross3_self, smul_zero]
      by_cases hW : W i' j' = 0
      · simp [hW]
      have : wedgeCross (u i') (u j') x y = 0 := by
        by_contra h
        obtain ⟨t, ht0, ht1, α, β, hα, hβ, he⟩ := wedgeCross_ne_zero h
        apply (hseg t ht0 ht1).1.1.1.1
        simp only [Set.mem_iUnion]
        exact ⟨(i', j'), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hi', hj'⟩, hij', hW,
          pair_ne_of hij' h1 h2⟩, by rw [he]; exact mem_finCone_pair hij' hα hβ⟩
      simp [this]
    have hsegij : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        0 < vol3 (x + t • (y - x)) (u j) (cross3 (u i) (u j)) ∧
        0 < vol3 (u i) (x + t • (y - x)) (cross3 (u i) (u j)) :=
      fun t ht0 ht1 => ⟨(hseg t ht0 ht1).1.1.1.2, (hseg t ht0 ht1).1.1.2⟩
    have hsegji : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        0 < vol3 (x + t • (y - x)) (u i) (cross3 (u j) (u i)) ∧
        0 < vol3 (u j) (x + t • (y - x)) (cross3 (u j) (u i)) :=
      fun t ht0 ht1 => ⟨(hseg t ht0 ht1).1.2, (hseg t ht0 ht1).2⟩
    have hxs := ((mem_intCone_three_iff hij hai.symm haj.symm hPa x).1 hx).2.2
    have hys := ((mem_intCone_three_iff hij hbi.symm hbj.symm hPb y).1 hy).2.2
    have hswap : ∀ z, vol3 (u j) (u i) z = -vol3 (u i) (u j) z := fun z => by unfold vol3; ring
    show fanPot S u W d (xτ {i, j, b}) - fanPot S u W d (xτ {i, j, a}) =
      (-W i j) • orientedCross (u i) (u j) (u b)
    rw [← hconst _ hτ x hx hgx, ← hconst _ hτ' y hy hxy.2.1, hsum, hWs j i, cross3_swap (u i) (u j)]
    rcases hPb.lt_or_gt with hPbneg | hPbpos
    · -- `τ'` on the negative side
      have hPapos : 0 < vol3 (u i) (u j) (u a) := by
        by_contra h; push_neg at h; nlinarith [mul_nonneg_of_nonpos_of_nonpos h hPbneg.le]
      have hx0 : 0 < vol3 (u i) (u j) x := by
        rcases div_pos_iff.1 hxs with h | h
        · exact h.1
        · exact absurd h.2 (not_lt.2 hPapos.le)
      have hy0 : vol3 (u i) (u j) y < 0 := by
        rcases div_pos_iff.1 hys with h | h
        · exact absurd h.2 (not_lt.2 hPbneg.le)
        · exact h.1
      rw [wedgeCross_eq_neg_one hx0 hy0 hsegij,
        wedgeCross_eq_one (by rw [hswap]; linarith) (by rw [hswap]; linarith) hsegji]
      unfold orientedCross
      rw [if_neg (not_lt.2 hPbneg.le), cross3_swap (u i) (u j)]
      module
    · -- `τ'` on the positive side
      have hPaneg : vol3 (u i) (u j) (u a) < 0 := by
        by_contra h; push_neg at h; nlinarith [mul_nonneg h hPbpos.le]
      have hx0 : vol3 (u i) (u j) x < 0 := by
        rcases div_pos_iff.1 hxs with h | h
        · exact absurd h.2 (not_lt.2 hPaneg.le)
        · exact h.1
      have hy0 : 0 < vol3 (u i) (u j) y := by
        rcases div_pos_iff.1 hys with h | h
        · exact h.1
        · exact absurd h.2 (not_lt.2 hPbpos.le)
      rw [wedgeCross_eq_one hx0 hy0 hsegij,
        wedgeCross_eq_neg_one (by rw [hswap]; linarith) (by rw [hswap]; linarith) hsegji]
      unfold orientedCross
      rw [if_pos hPbpos]
      module

end Erdos99
end

end FanGradientExists
