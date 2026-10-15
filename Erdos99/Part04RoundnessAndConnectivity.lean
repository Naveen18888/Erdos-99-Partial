module

public import Mathlib
public import Erdos99.Part01Basics
public import Erdos99.Part02LockingAndFans
public import Erdos99.Part03LiftedFanAndDensity

/-!
# Erdős Problem 99 under finite multiplicity — Part 4 of 9: Roundness, contact-graph connectivity and local capacity

This is one of the supporting files of the formalization; the main theorem and a precise
description of what is proved are at the top of `Erdos99.lean`.

The file is divided into the following sections (each `section Name … end Name`); comments
elsewhere in the development refer to these sections by name.

* `Roundness`
* `Winding`
* `Crux`
* `Arc`
* `ContactRelease`
* `RotationRelease`
* `Connected`
* `DirectCountAlgebra`
* `FiniteCutoff`
* `QuadraticResponseAlgebra`
* `Overview`
* `InnerRound`
* `ConvexFaces`
* `HullSpread`
* `PropagationLedger`
* `LocalCapacity`
-/

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `Roundness`
-/

section Roundness

/-!
# Roundness of optimal configurations (Lemma 3.1, outer half)

An optimal `n`-point configuration of diameter `D` lies in a disc of radius `D/2 + o(D)`.

The manuscript derives this from Bonnesen's inequality.  We use instead a quantitative form of
the planar isodiametric inequality, proved directly by polar coordinates:

* `exists_circumcenter`: a compact planar set `K` has a centre `O` of a smallest enclosing disc
  (radius `R`), and for every contact point `a` there is a second contact point `b` with
  `⟪b - O, a - O⟫ ≤ 0`;
* `volume_le_of_pair_deficit`: the polar-coordinate proof of the isodiametric inequality, with an
  improved Pythagorean bound on an interval of angles;
* `volume_le_of_circumradius`: if the circumradius `R` of a compact set of diameter `≤ d`
  exceeds `d/2`, then its area is at most `π d²/4 - κ` with an explicit `κ > 0`.  The proof uses
  polar coordinates about the contact point `a`: on the rays just before the direction of `b`,
  the circumcircle and the disc of radius `d` about `b` force a Pythagorean deficit;
* `round_center_of_optimal`: applied to the union of unit discs about an optimal configuration,
  the area estimate contradicts the lattice bound `c D² ≤ n` unless the configuration lies in a
  disc of radius `D/2 + η D`.
-/

open scoped Real Topology
open MeasureTheory Set Filter

@[expose] public noncomputable section

namespace Erdos99

/-- The polar-coordinate isodiametric bound with a deficit: a measurable set in the closed upper
half-plane whose radial extents along perpendicular rays satisfy `r² + s² ≤ d²`, and
`r² + s² ≤ d² - κ` (together with `r², s² ≤ d² - κ`) for angles in `[θ₁, θ₂]`, has area at most
`π d²/4 - κ (θ₂ - θ₁)/2`. -/
theorem volume_le_of_pair_deficit {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) {d κ θ₁ θ₂ : ℝ}
    (hd : 0 ≤ d) (hκd : κ ≤ d ^ 2) (hθ₁ : 0 ≤ θ₁) (hθ : θ₁ ≤ θ₂)
    (hθ₂ : θ₂ < π / 2)
    (hup : ∀ p ∈ A, 0 ≤ p.2)
    (hray : ∀ θ r, (r * Real.cos θ, r * Real.sin θ) ∈ A → 0 < r → r ≤ d)
    (hpair : ∀ θ r s, 0 < r → 0 < s → (r * Real.cos θ, r * Real.sin θ) ∈ A →
      (s * Real.cos (θ + π / 2), s * Real.sin (θ + π / 2)) ∈ A → r ^ 2 + s ^ 2 ≤ d ^ 2)
    (hdef : ∀ θ ∈ Icc θ₁ θ₂, ∀ r s, 0 < r → 0 < s → (r * Real.cos θ, r * Real.sin θ) ∈ A →
      (s * Real.cos (θ + π / 2), s * Real.sin (θ + π / 2)) ∈ A → r ^ 2 + s ^ 2 ≤ d ^ 2 - κ)
    (hdef₁ : ∀ θ ∈ Icc θ₁ θ₂, ∀ r, 0 < r → (r * Real.cos θ, r * Real.sin θ) ∈ A →
      r ^ 2 ≤ d ^ 2 - κ)
    (hdef₂ : ∀ θ ∈ Icc θ₁ θ₂, ∀ s, 0 < s →
      (s * Real.cos (θ + π / 2), s * Real.sin (θ + π / 2)) ∈ A → s ^ 2 ≤ d ^ 2 - κ) :
    volume A ≤ ENNReal.ofReal (π * d ^ 2 / 4 - κ * (θ₂ - θ₁) / 2) := by
  set P : ℝ → ℝ → ℝ × ℝ := fun r θ => (r * Real.cos θ, r * Real.sin θ) with hP
  set F : ℝ → ENNReal := fun θ =>
    ∫⁻ r in Ioi 0, ENNReal.ofReal r * {r | P r θ ∈ A}.indicator 1 r with hF
  have hmeas : Measurable (fun q : ℝ × ℝ => ENNReal.ofReal q.1 * A.indicator 1 (P q.1 q.2)) := by
    refine (ENNReal.measurable_ofReal.comp measurable_fst).mul ?_
    exact (measurable_one.indicator hA).comp (by fun_prop)
  have hpolar : volume A = ∫⁻ θ in Ioo (-π) π, F θ := by
    rw [← lintegral_indicator_one hA, ← lintegral_comp_polarCoord_symm, polarCoord_target,
      Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ ?_]
    · rw [lintegral_lintegral_swap]
      · refine lintegral_congr fun θ => lintegral_congr fun r => ?_
        simp only [polarCoord_symm_apply, smul_eq_mul, P, Set.indicator, Set.mem_setOf_eq,
          Pi.one_apply]
      · exact hmeas.aemeasurable.congr
          (Filter.Eventually.of_forall fun q => by
            simp only [Function.uncurry, polarCoord_symm_apply, smul_eq_mul, P])
    · exact hmeas.aemeasurable.congr (Filter.Eventually.of_forall fun q => by
        simp only [polarCoord_symm_apply, smul_eq_mul, P])
  -- the lower half-plane contributes nothing
  have hneg : ∀ θ ∈ Ioo (-π) 0, F θ = 0 := by
    intro θ hθ
    have hs : Real.sin θ < 0 := Real.sin_neg_of_neg_of_neg_pi_lt hθ.2 hθ.1
    refine setLIntegral_eq_zero_iff' measurableSet_Ioi ?_ |>.2 ?_
    · exact (ENNReal.measurable_ofReal.mul ((measurable_one.indicator hA).comp
        (by fun_prop))).aemeasurable
    · refine Filter.Eventually.of_forall fun r hr => ?_
      have : P r θ ∉ A := fun h => by
        have := hup _ h; simp only [P] at this; nlinarith [mem_Ioi.1 hr]
      simp [Set.indicator, this]
  -- the pair bound, with a general constant
  have hpairG : ∀ θ (e : ℝ), 0 ≤ e →
      (∀ r, 0 < r → P r θ ∈ A → r ≤ e) → (∀ s, 0 < s → P s (θ + π / 2) ∈ A → s ≤ e) →
      (∀ r s, 0 < r → 0 < s → P r θ ∈ A → P s (θ + π / 2) ∈ A → r ^ 2 + s ^ 2 ≤ e ^ 2) →
      F θ + F (θ + π / 2) ≤ ENNReal.ofReal (e ^ 2 / 2) := by
    intro θ e he h1 h2 h12
    set S := {r | P r θ ∈ A} ∩ Ioi 0
    set T := {r | P r (θ + π / 2) ∈ A} ∩ Ioi 0
    obtain ⟨hsum, h0S, h0T⟩ := sSup_sq_add_sSup_sq_le (S := S) (T := T) he
      (fun r hr => ⟨hr.2, h1 r hr.2 hr.1⟩)
      (fun r hr => ⟨hr.2, h2 r hr.2 hr.1⟩) (fun r hr s hs => h12 r s hr.2 hs.2 hr.1 hs.1)
    have b1 : F θ ≤ ENNReal.ofReal (sSup S ^ 2 / 2) := lintegral_ray_le h0S fun r hr hr0 =>
      le_csSup ⟨e, fun x hx => h1 x hx.2 hx.1⟩ ⟨hr, hr0⟩
    have b2 : F (θ + π / 2) ≤ ENNReal.ofReal (sSup T ^ 2 / 2) :=
      lintegral_ray_le h0T fun r hr hr0 =>
        le_csSup ⟨e, fun x hx => h2 x hx.2 hx.1⟩ ⟨hr, hr0⟩
    calc F θ + F (θ + π / 2) ≤ ENNReal.ofReal (sSup S ^ 2 / 2) + ENNReal.ofReal (sSup T ^ 2 / 2) :=
          add_le_add b1 b2
      _ = ENNReal.ofReal (sSup S ^ 2 / 2 + sSup T ^ 2 / 2) :=
          (ENNReal.ofReal_add (by positivity) (by positivity)).symm
      _ ≤ ENNReal.ofReal (e ^ 2 / 2) := ENNReal.ofReal_le_ofReal (by linarith)
  have hpair1 : ∀ θ, F θ + F (θ + π / 2) ≤ ENNReal.ofReal (d ^ 2 / 2) := fun θ =>
    hpairG θ d hd (fun r hr h => hray θ r h hr) (fun s hs h => hray _ s h hs)
      (fun r s hr hs h1 h2 => hpair θ r s hr hs h1 h2)
  have he0 : 0 ≤ d ^ 2 - κ := by linarith
  have hpair2 : ∀ θ ∈ Icc θ₁ θ₂, F θ + F (θ + π / 2) ≤ ENNReal.ofReal ((d ^ 2 - κ) / 2) := by
    intro θ hθ
    have := hpairG θ √(d ^ 2 - κ) (Real.sqrt_nonneg _)
      (fun r hr h => Real.le_sqrt_of_sq_le (hdef₁ θ hθ r hr h))
      (fun s hs h => Real.le_sqrt_of_sq_le (hdef₂ θ hθ s hs h))
      (fun r s hr hs h1 h2 => by rw [Real.sq_sqrt he0]; exact hdef θ hθ r s hr hs h1 h2)
    rwa [Real.sq_sqrt he0] at this
  -- assemble
  rw [hpolar]
  have hsplit : Ioo (-π) π = Ioo (-π) 0 ∪ (Ico 0 (π / 2) ∪ Ico (π / 2) π) := by
    ext θ; simp only [mem_Ioo, mem_union, mem_Ico]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases h : θ < 0
      · left; exact ⟨h1, h⟩
      · right; by_cases h' : θ < π / 2
        · left; exact ⟨le_of_not_gt h, h'⟩
        · right; exact ⟨le_of_not_gt h', h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> constructor <;> linarith [Real.pi_pos]
  have hshift : ∫⁻ θ in Ico (π / 2) π, F θ = ∫⁻ θ in Ico 0 (π / 2), F (θ + π / 2) := by
    rw [← lintegral_indicator measurableSet_Ico, ← lintegral_indicator measurableSet_Ico,
      ← lintegral_add_right_eq_self (μ := volume) _ (π / 2)]
    refine lintegral_congr fun θ => ?_
    by_cases h : θ ∈ Ico 0 (π / 2)
    · have h' : θ + π / 2 ∈ Ico (π / 2) π := by
        obtain ⟨h1, h2⟩ := h; constructor <;> linarith
      simp [Set.indicator, h, h']
    · have h' : θ + π / 2 ∉ Ico (π / 2) π := by
        intro ⟨h1, h2⟩; exact h ⟨by linarith, by linarith⟩
      simp [Set.indicator, h, h']
  set I := Icc θ₁ θ₂ with hI
  have hIsub : I ⊆ Ico 0 (π / 2) := fun θ hθ => ⟨hθ₁.trans hθ.1, hθ.2.trans_lt hθ₂⟩
  have hbound : ∀ θ, F θ + F (θ + π / 2) ≤
      I.indicator (fun _ => ENNReal.ofReal ((d ^ 2 - κ) / 2)) θ +
        Iᶜ.indicator (fun _ => ENNReal.ofReal (d ^ 2 / 2)) θ := by
    intro θ
    by_cases h : θ ∈ I
    · simp only [Set.indicator_of_mem h, Set.indicator_of_notMem (Set.notMem_compl_iff.2 h),
        add_zero]
      exact hpair2 θ h
    · simp only [Set.indicator_of_notMem h, Set.indicator_of_mem (Set.mem_compl h), zero_add]
      exact hpair1 θ
  have hvolI : volume (Ico 0 (π / 2) ∩ I) = ENNReal.ofReal (θ₂ - θ₁) := by
    rw [Set.inter_eq_right.2 hIsub, Real.volume_Icc]
  have hvolIc : volume (Ico 0 (π / 2) ∩ Iᶜ) = ENNReal.ofReal (π / 2 - (θ₂ - θ₁)) := by
    rw [← Set.diff_eq, measure_diff hIsub measurableSet_Icc.nullMeasurableSet
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top), Real.volume_Ico, Real.volume_Icc,
      sub_zero, ← ENNReal.ofReal_sub _ (by linarith : (0 : ℝ) ≤ θ₂ - θ₁)]
  calc ∫⁻ θ in Ioo (-π) π, F θ
      ≤ (∫⁻ θ in Ioo (-π) 0, F θ) + ((∫⁻ θ in Ico 0 (π / 2), F θ) +
          ∫⁻ θ in Ico (π / 2) π, F θ) := by
        rw [hsplit]
        exact (lintegral_union_le _ _ _).trans (add_le_add le_rfl (lintegral_union_le _ _ _))
    _ = (∫⁻ θ in Ico 0 (π / 2), F θ) + ∫⁻ θ in Ico 0 (π / 2), F (θ + π / 2) := by
        rw [setLIntegral_congr_fun measurableSet_Ioo hneg, lintegral_zero, zero_add, hshift]
    _ ≤ ∫⁻ θ in Ico 0 (π / 2), (F θ + F (θ + π / 2)) := le_lintegral_add _ _
    _ ≤ ∫⁻ θ in Ico 0 (π / 2), (I.indicator (fun _ => ENNReal.ofReal ((d ^ 2 - κ) / 2)) θ +
          Iᶜ.indicator (fun _ => ENNReal.ofReal (d ^ 2 / 2)) θ) := lintegral_mono hbound
    _ = ENNReal.ofReal ((d ^ 2 - κ) / 2) * ENNReal.ofReal (θ₂ - θ₁) +
          ENNReal.ofReal (d ^ 2 / 2) * ENNReal.ofReal (π / 2 - (θ₂ - θ₁)) := by
        rw [lintegral_add_left (measurable_const.indicator measurableSet_Icc),
          lintegral_indicator measurableSet_Icc, lintegral_indicator measurableSet_Icc.compl,
          setLIntegral_const, setLIntegral_const, Measure.restrict_apply measurableSet_Icc,
          Measure.restrict_apply measurableSet_Icc.compl, Set.inter_comm, hvolI,
          Set.inter_comm, hvolIc]
    _ = ENNReal.ofReal (π * d ^ 2 / 4 - κ * (θ₂ - θ₁) / 2) := by
        rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (mul_nonneg (by linarith) (by linarith))
            (mul_nonneg (by positivity) (by linarith))]
        congr 1; ring

/-- The algebraic core of `pair_deficit_geom`, with `cψ, sψ, cδ, sδ` standing for the cosines and
sines of `ψ` and `δ`, and `sθ = sin (ψ - δ)`. -/
lemma pair_deficit_alg {R d B s r G cψ sψ cδ sδ sθ : ℝ} (hR : 0 < R) (hG0 : 0 < G)
    (hGdef : 4 * R ^ 2 - d ^ 2 = G) (hd0 : 0 < d) (hBd : B ≤ d)
    (hψ1 : sψ ^ 2 + cψ ^ 2 = 1) (hδ1 : sδ ^ 2 + cδ ^ 2 = 1)
    (hcψ : 0 ≤ cψ) (hψ : cψ ≤ sψ) (hsψ : 1 / 2 ≤ sψ) (hcψ1 : cψ ≤ 1) (hcδ1 : cδ ≤ 1)
    (hδs : sδ ≤ G / (4 * d ^ 2)) (hδc : 1 - cδ ≤ G / (32 * R ^ 2)) (hsδ : 0 ≤ sδ)
    (hs : 0 ≤ s) (hsd : s ≤ d) (hBψ : B = 2 * R * sψ) (hsθdef : sψ * cδ - cψ * sδ = sθ)
    (hr2 : r ^ 2 ≤ 4 * R ^ 2 * sθ ^ 2) (hq1 : s ^ 2 + B ^ 2 - 2 * s * B * sδ ≤ d ^ 2) :
    r ^ 2 + s ^ 2 ≤ d ^ 2 - sδ * G / 8 := by
  set X := 2 * R * cψ with hX
  have hX2 : X ^ 2 = 4 * R ^ 2 - B ^ 2 := by rw [hX, hBψ]; linear_combination 4 * R ^ 2 * hψ1
  have hX0 : 0 ≤ X := by positivity
  have hX2R : X ≤ 2 * R := by rw [hX]; nlinarith only [hcψ1, hR]
  have hsB : 2 * s * B * sδ ≤ G / 2 := by
    have h1 : s * B ≤ d ^ 2 := by nlinarith only [hsd, hBd, hs, hd0]
    have h2 : sδ * (4 * d ^ 2) ≤ G := by rwa [le_div_iff₀ (by positivity)] at hδs
    nlinarith only [h1, h2, hsδ, hd0]
  have hsX : s ^ 2 ≤ X ^ 2 - G / 2 := by linarith only [hsB, hq1, hX2, hGdef]
  have hGR : G ≤ 4 * R ^ 2 := by nlinarith only [hGdef, hd0]
  have hsX' : s ≤ X - G / (8 * R) := by
    have hGX : G / (8 * R) ≤ X := by
      have h1 : G / 2 ≤ X ^ 2 := by nlinarith only [hsX, hs]
      have h2 : (G / (8 * R)) ^ 2 ≤ G / 2 := by
        rw [div_pow, div_le_iff₀ (by positivity)]
        nlinarith only [hGR, hG0, hR]
      nlinarith only [h1, h2, hX0]
    have hY : s ^ 2 ≤ (X - G / (8 * R)) ^ 2 := by
      have e : (X - G / (8 * R)) ^ 2 = X ^ 2 - X * G / (4 * R) + (G / (8 * R)) ^ 2 := by
        field_simp; ring
      have : X * G / (4 * R) ≤ G / 2 := by
        rw [div_le_iff₀ (by positivity)]; nlinarith only [hX2R, hG0, hR]
      nlinarith only [e, this, hsX, sq_nonneg (G / (8 * R))]
    exact (pow_le_pow_iff_left₀ hs (by linarith) two_ne_zero).1 hY
  have hc' : 2 * R * (1 - cδ) ≤ G / (16 * R) := by
    rw [le_div_iff₀ (by positivity)]
    rw [le_div_iff₀ (by positivity)] at hδc
    nlinarith only [hδc]
  have key : G / (32 * R) ≤ R * (sψ ^ 2 - cψ ^ 2) * sδ + 2 * R * sψ * cψ * cδ - sψ * s := by
    have h1 : 0 ≤ R * (sψ ^ 2 - cψ ^ 2) * sδ := by
      have : 0 ≤ sψ ^ 2 - cψ ^ 2 := by nlinarith only [hψ, hcψ]
      positivity
    have h2 : sψ * (G / (8 * R) - 2 * R * cψ * (1 - cδ)) ≤ 2 * R * sψ * cψ * cδ - sψ * s := by
      have : sψ * (G / (8 * R) - 2 * R * cψ * (1 - cδ)) =
          2 * R * sψ * cψ * cδ - sψ * (X - G / (8 * R)) := by rw [hX]; ring
      rw [this]
      nlinarith only [hsX', hsψ]
    have h3 : G / (16 * R) ≤ G / (8 * R) - 2 * R * cψ * (1 - cδ) := by
      have : 2 * R * cψ * (1 - cδ) ≤ 2 * R * (1 - cδ) := by
        have : 0 ≤ 1 - cδ := by linarith
        have : 0 ≤ 2 * R * (1 - cδ) := by positivity
        nlinarith only [this, hcψ1]
      have e : G / (8 * R) - G / (16 * R) = G / (16 * R) := by field_simp; ring
      linarith
    have h4 : G / (32 * R) ≤ sψ * (G / (16 * R)) := by
      have e : G / (32 * R) = 1 / 2 * (G / (16 * R)) := by field_simp; ring
      rw [e]
      exact mul_le_mul_of_nonneg_right hsψ (by positivity)
    have h5 : sψ * (G / (16 * R)) ≤ sψ * (G / (8 * R) - 2 * R * cψ * (1 - cδ)) :=
      mul_le_mul_of_nonneg_left h3 (by linarith)
    linarith
  have hident : 4 * R ^ 2 * sθ ^ 2 - B ^ 2 =
      4 * R * sδ * (R * (cψ ^ 2 - sψ ^ 2) * sδ - 2 * R * sψ * cψ * cδ) := by
    rw [← hsθdef, hBψ]
    linear_combination (4 * R ^ 2 * sψ ^ 2) * hδ1
  have hfinal : r ^ 2 + s ^ 2 ≤ d ^ 2 - 4 * R * sδ * (R * (sψ ^ 2 - cψ ^ 2) * sδ +
      2 * R * sψ * cψ * cδ - sψ * s) := by
    rw [hBψ] at hq1 hident
    linear_combination hr2 + hq1 + hident
  have : 4 * R * sδ * (G / (32 * R)) = sδ * G / 8 := by field_simp; ring
  nlinarith only [mul_le_mul_of_nonneg_left key (by positivity : 0 ≤ 4 * R * sδ), hfinal, this]

/-- The pointwise Pythagorean deficit.  Coordinates: the contact point is the origin, the
circumcentre is `(0, R)`, and `b = B (cos ψ, sin ψ)` is a second contact point with
`b₂ ≥ R`, `b₁ ≥ 0`.  For the direction `θ = ψ - δ`, a point at distance `r` along the ray `θ`
inside the circumdisc and a point at distance `s` along the ray `θ + π/2` within `d` of `b`
satisfy `r² + s² ≤ d² - sin δ (4R² - d²)/8`. -/
lemma pair_deficit_geom {R d B ψ δ r s : ℝ} (hR : 0 < R)
    (hG : d ^ 2 < 4 * R ^ 2) (hB : 0 < B) (hcψ : 0 ≤ Real.cos ψ)
    (hψ : Real.cos ψ ≤ Real.sin ψ)
    (hbO : (B * Real.cos ψ) ^ 2 + (B * Real.sin ψ - R) ^ 2 = R ^ 2) (hBd : B ≤ d)
    (hδs : Real.sin δ ≤ (4 * R ^ 2 - d ^ 2) / (4 * d ^ 2))
    (hδc : 1 - Real.cos δ ≤ (4 * R ^ 2 - d ^ 2) / (32 * R ^ 2))
    (hsδ : 0 ≤ Real.sin δ)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hsd : s ≤ d)
    (hp : (r * Real.cos (ψ - δ)) ^ 2 + (r * Real.sin (ψ - δ) - R) ^ 2 ≤ R ^ 2)
    (hq : (s * Real.cos (ψ - δ + π / 2) - B * Real.cos ψ) ^ 2 +
      (s * Real.sin (ψ - δ + π / 2) - B * Real.sin ψ) ^ 2 ≤ d ^ 2) :
    r ^ 2 + s ^ 2 ≤ d ^ 2 - Real.sin δ * (4 * R ^ 2 - d ^ 2) / 8 := by
  rw [Real.cos_add_pi_div_two, Real.sin_add_pi_div_two] at hq
  rw [Real.cos_sub] at hp hq
  rw [Real.sin_sub] at hp hq
  have hψ1 := Real.sin_sq_add_cos_sq ψ
  have hδ1 := Real.sin_sq_add_cos_sq δ
  generalize Real.cos ψ = cψ at *
  generalize Real.sin ψ = sψ at *
  generalize Real.cos δ = cδ at *
  generalize Real.sin δ = sδ at *
  generalize hGdef : 4 * R ^ 2 - d ^ 2 = G at *
  have hG0 : 0 < G := by linarith
  have hd0 : 0 < d := hB.trans_le hBd
  have e1 : (cψ * cδ + sψ * sδ) ^ 2 + (sψ * cδ - cψ * sδ) ^ 2 = 1 := by
    linear_combination (sδ ^ 2 + cδ ^ 2) * hψ1 + hδ1
  have e2 : sψ * (cψ * cδ + sψ * sδ) - cψ * (sψ * cδ - cψ * sδ) = sδ := by
    linear_combination sδ * hψ1
  -- `B = 2 R sin ψ`
  have hBψ : B = 2 * R * sψ := by
    have : B * (B - 2 * R * sψ) = 0 := by linear_combination hbO - B ^ 2 * hψ1
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  have hsψ : 1 / 2 ≤ sψ := by
    have h1 : cψ ^ 2 ≤ sψ ^ 2 := by nlinarith only [hψ, hcψ]
    nlinarith only [h1, hψ1, hψ, hcψ]
  have hcψ1 : cψ ≤ 1 := by nlinarith only [hψ1, hcψ]
  have hcδ1 : cδ ≤ 1 := by nlinarith only [hδ1]
  -- the circumdisc bound along the ray `θ`
  generalize hsθdef : sψ * cδ - cψ * sδ = sθ at *
  have hr1 : r ^ 2 ≤ 2 * R * sθ * r := by linear_combination hp - r ^ 2 * e1
  have hr2 : r ^ 2 ≤ 4 * R ^ 2 * sθ ^ 2 := by
    rcases hr.lt_or_eq with h | h
    · have : r ≤ 2 * R * sθ := le_of_mul_le_mul_right (by linarith only [hr1]) h
      nlinarith only [this, hr]
    · rw [← h]; nlinarith only [sq_nonneg (R * sθ)]
  -- the bound from `b` along the ray `θ + π/2`
  have hq1 : s ^ 2 + B ^ 2 - 2 * s * B * sδ ≤ d ^ 2 := by
    linear_combination hq - s ^ 2 * e1 - B ^ 2 * hψ1 + 2 * s * B * e2
  have := pair_deficit_alg hR hG0 hGdef hd0 hBd hψ1 hδ1 hcψ hψ hsψ hcψ1 hcδ1 hδs hδc hsδ hs
    hsd hBψ hsθdef hr2 hq1
  linarith only [this]

/-- Polar form of a point `(β₁, β₂)` with `0 ≤ β₁ ≤ β₂`: its angle lies in `[π/4, π/2]`. -/
lemma exists_angle_of_le {β₁ β₂ : ℝ} (hβ₁ : 0 ≤ β₁) (hβ : β₁ ≤ β₂) (hβ₂ : 0 < β₂) :
    ∃ ψ : ℝ, β₁ = √(β₁ ^ 2 + β₂ ^ 2) * Real.cos ψ ∧ β₂ = √(β₁ ^ 2 + β₂ ^ 2) * Real.sin ψ ∧
      π / 4 ≤ ψ ∧ ψ ≤ π / 2 ∧ 0 ≤ Real.cos ψ ∧ Real.cos ψ ≤ Real.sin ψ := by
  set B := √(β₁ ^ 2 + β₂ ^ 2) with hB
  have hB0 : 0 < B := Real.sqrt_pos.2 (by positivity)
  have hB2 : B ^ 2 = β₁ ^ 2 + β₂ ^ 2 := Real.sq_sqrt (by positivity)
  have hle : β₁ / B ≤ 1 := by
    rw [div_le_one hB0]
    nlinarith [sq_nonneg β₂]
  have hcos : Real.cos (Real.arccos (β₁ / B)) = β₁ / B :=
    Real.cos_arccos (by linarith [div_nonneg hβ₁ hB0.le]) hle
  have hsin : Real.sin (Real.arccos (β₁ / B)) = β₂ / B := by
    rw [Real.sin_arccos]
    have : 1 - (β₁ / B) ^ 2 = (β₂ / B) ^ 2 := by
      field_simp; linarith
    rw [this, Real.sqrt_sq (div_nonneg hβ₂.le hB0.le)]
  refine ⟨Real.arccos (β₁ / B), ?_, ?_, ?_, Real.arccos_le_pi_div_two.2 (div_nonneg hβ₁ hB0.le),
    ?_, ?_⟩
  · rw [hcos]; field_simp
  · rw [hsin]; field_simp
  · by_contra h
    push_neg at h
    have h1 := Real.cos_lt_cos_of_nonneg_of_le_pi_div_two (Real.arccos_nonneg _)
      (by linarith [Real.pi_pos]) h
    have h2 := Real.sin_lt_sin_of_lt_of_le_pi_div_two
      (by linarith [Real.pi_pos, Real.arccos_nonneg (β₁ / B)]) (by linarith [Real.pi_pos]) h
    rw [Real.cos_pi_div_four] at h1
    rw [Real.sin_pi_div_four] at h2
    rw [hcos] at h1; rw [hsin] at h2
    have : β₁ / B ≤ β₂ / B := div_le_div_of_nonneg_right hβ hB0.le
    linarith
  · rw [hcos]; positivity
  · rw [hcos, hsin]; exact div_le_div_of_nonneg_right hβ hB0.le

/-- `volume_le_of_circumradius` in normalised coordinates: the contact point `a` is the origin,
the circumcentre is `(0, R)` and the second contact point is `(β₁, β₂)` with `β₁ ≥ 0`. -/
theorem volume_le_of_circumradius_normalized {A : Set (ℝ × ℝ)} (hA : MeasurableSet A)
    {d R β₁ β₂ : ℝ}
    (hdist : ∀ p ∈ A, ∀ q ∈ A, (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 ≤ d ^ 2)
    (hsub : ∀ p ∈ A, p.1 ^ 2 + (p.2 - R) ^ 2 ≤ R ^ 2)
    (h0 : ((0 : ℝ), (0 : ℝ)) ∈ A) (hb : (β₁, β₂) ∈ A) (hβ₁ : 0 ≤ β₁) (hβ₂ : R ≤ β₂)
    (hbO : β₁ ^ 2 + (β₂ - R) ^ 2 = R ^ 2) (hR : 0 < R) (hRd : R ≤ d)
    (hG : d ^ 2 < 4 * R ^ 2) :
    volume A ≤ ENNReal.ofReal (π * d ^ 2 / 4 -
      Real.sin ((4 * R ^ 2 - d ^ 2) / (16 * d ^ 2) / 2) * (4 * R ^ 2 - d ^ 2) *
        ((4 * R ^ 2 - d ^ 2) / (16 * d ^ 2)) / 32) := by
  have hd0 : 0 < d := hR.trans_le hRd
  have hβ : β₁ ≤ β₂ := by nlinarith
  obtain ⟨ψ, hb1, hb2, hψ4, hψ2, hcψ, hψ⟩ := exists_angle_of_le hβ₁ hβ (hR.trans_le hβ₂)
  set B := √(β₁ ^ 2 + β₂ ^ 2) with hB
  have hB0 : 0 < B := Real.sqrt_pos.2 (by nlinarith)
  have hBd : B ≤ d := by
    have := hdist _ hb _ h0
    simp only [sub_zero] at this
    exact Real.sqrt_le_iff.2 ⟨hd0.le, this⟩
  have hbO' : (B * Real.cos ψ) ^ 2 + (B * Real.sin ψ - R) ^ 2 = R ^ 2 := by
    rw [← hb1, ← hb2]; exact hbO
  set G := 4 * R ^ 2 - d ^ 2 with hGdef
  set δ₀ := G / (16 * d ^ 2) with hδ₀
  have hG0 : 0 < G := by linarith
  have hR2 : R ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ hR.le hRd 2
  have hGup : G ≤ 3 * d ^ 2 := by linarith
  have hδ₀0 : 0 < δ₀ := by positivity
  have hδ₀up : δ₀ ≤ 3 / 16 := by rw [hδ₀, div_le_iff₀ (by positivity)]; linarith
  have hδ₀s : δ₀ ≤ G / (4 * d ^ 2) := by
    rw [hδ₀]; exact div_le_div_of_nonneg_left hG0.le (by positivity) (by linarith)
  have hδ₀c : δ₀ ^ 2 / 2 ≤ G / (32 * R ^ 2) := by
    rw [hδ₀, div_pow, le_div_iff₀ (by positivity)]
    rw [div_div, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have h1 : G * R ^ 2 ≤ 3 * d ^ 2 * d ^ 2 := by
      have := mul_le_mul hGup hR2 (by positivity) (by positivity); linarith
    nlinarith [mul_le_mul_of_nonneg_left h1 hG0.le]
  set κ := Real.sin (δ₀ / 2) * G / 8 with hκ
  have hsin0 : 0 ≤ Real.sin (δ₀ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_gt_three])
  have hκd : κ ≤ d ^ 2 := by
    have := Real.sin_le_one (δ₀ / 2)
    have : κ ≤ 1 * G / 8 := by rw [hκ]; gcongr
    linarith
  have hP : ∀ r θ : ℝ, (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := fun r θ => by
    linear_combination r ^ 2 * Real.sin_sq_add_cos_sq θ
  have hray : ∀ θ r, (r * Real.cos θ, r * Real.sin θ) ∈ A → 0 ≤ r → r ≤ d := by
    intro θ r h hr
    have := hdist _ h _ h0
    simp only [sub_zero, hP] at this
    exact (pow_le_pow_iff_left₀ hr hd0.le two_ne_zero).1 this
  -- the pointwise deficit for directions `θ ∈ [ψ - δ₀, ψ - δ₀/2]`
  have hgeom : ∀ θ ∈ Icc (ψ - δ₀) (ψ - δ₀ / 2), ∀ r s, 0 ≤ r → 0 ≤ s →
      (r * Real.cos θ) ^ 2 + (r * Real.sin θ - R) ^ 2 ≤ R ^ 2 →
      (s * Real.cos (θ + π / 2) - β₁) ^ 2 + (s * Real.sin (θ + π / 2) - β₂) ^ 2 ≤ d ^ 2 →
      s ≤ d → r ^ 2 + s ^ 2 ≤ d ^ 2 - κ := by
    intro θ hθ r s hr hs hp hq hsd
    have hδ1 : δ₀ / 2 ≤ ψ - θ := by linarith [hθ.2]
    have hδ2 : ψ - θ ≤ δ₀ := by linarith [hθ.1]
    have hθe : ψ - (ψ - θ) = θ := by ring
    have hsδ0 : 0 ≤ Real.sin (ψ - θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_gt_three])
    have hδs : Real.sin (ψ - θ) ≤ G / (4 * d ^ 2) :=
      (Real.sin_le (by linarith)).trans (hδ2.trans hδ₀s)
    have hδc : 1 - Real.cos (ψ - θ) ≤ G / (32 * R ^ 2) := by
      have h1 := Real.one_sub_sq_div_two_le_cos (x := ψ - θ)
      have h2 : (ψ - θ) ^ 2 ≤ δ₀ ^ 2 := pow_le_pow_left₀ (by linarith) hδ2 2
      linarith
    have hp' : (r * Real.cos (ψ - (ψ - θ))) ^ 2 + (r * Real.sin (ψ - (ψ - θ)) - R) ^ 2 ≤ R ^ 2 := by
      rw [hθe]; exact hp
    have hq' : (s * Real.cos (ψ - (ψ - θ) + π / 2) - B * Real.cos ψ) ^ 2 +
        (s * Real.sin (ψ - (ψ - θ) + π / 2) - B * Real.sin ψ) ^ 2 ≤ d ^ 2 := by
      rw [hθe, ← hb1, ← hb2]; exact hq
    have h := pair_deficit_geom hR hG hB0 hcψ hψ hbO' hBd hδs hδc hsδ0 hr hs hsd hp' hq'
    have hmono : Real.sin (δ₀ / 2) ≤ Real.sin (ψ - θ) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
        (by linarith [Real.pi_gt_three]) hδ1
    have : Real.sin (δ₀ / 2) * G / 8 ≤ Real.sin (ψ - θ) * G / 8 := by gcongr
    linarith
  have hfinal := volume_le_of_pair_deficit hA (d := d) (κ := κ) (θ₁ := ψ - δ₀)
    (θ₂ := ψ - δ₀ / 2) hd0.le hκd (by linarith [Real.pi_gt_three]) (by linarith)
    (by linarith)
    (fun p hp => by nlinarith [hsub p hp, sq_nonneg p.1])
    (fun θ r h hr => hray θ r h hr.le)
    (fun θ r s hr hs h1 h2 => by
      have := hdist _ h1 _ h2
      rw [Real.cos_add_pi_div_two, Real.sin_add_pi_div_two] at this
      linear_combination this - (r ^ 2 + s ^ 2) * Real.sin_sq_add_cos_sq θ)
    (fun θ hθ r s hr hs h1 h2 => hgeom θ hθ r s hr.le hs.le (hsub _ h1) (hdist _ h2 _ hb)
      (hray _ s h2 hs.le))
    (fun θ hθ r hr h1 => by
      have := hgeom θ hθ r 0 hr.le le_rfl (hsub _ h1)
        (by have := hdist _ hb _ h0; simp only [sub_zero] at this; simpa using this) hd0.le
      linarith)
    (fun θ hθ s hs h2 => by
      have := hgeom θ hθ 0 s le_rfl hs.le (by simp) (hdist _ h2 _ hb) (hray _ s h2 hs.le)
      linarith)
  refine hfinal.trans (le_of_eq ?_)
  congr 1
  rw [hκ]; ring

/-- A rigid motion of the plane, written in coordinates, taking `a` to the origin, `O` to
`(0, R)` and `b` into the closed right half-plane. -/
lemma exists_coord_isometry (a O b : Plane) {R : ℝ} (hR : dist a O = R) :
    ∃ Φ : Plane → ℝ × ℝ, MeasurePreserving Φ volume volume ∧ Continuous Φ ∧
      (∀ x y, ((Φ x).1 - (Φ y).1) ^ 2 + ((Φ x).2 - (Φ y).2) ^ 2 = dist x y ^ 2) ∧
      Φ a = (0, 0) ∧ Φ O = (0, R) ∧ 0 ≤ (Φ b).1 := by
  set w : Plane := R • EuclideanSpace.single 1 1 with hw
  have hnorm : ‖O - a‖ = ‖w‖ := by
    rw [hw, norm_smul, EuclideanSpace.norm_single, norm_one, mul_one, ← dist_eq_norm, dist_comm,
      hR, Real.norm_eq_abs, abs_of_nonneg (hR ▸ dist_nonneg)]
  set ρ := Submodule.reflection (ℝ ∙ ((O - a) - w))ᗮ with hρ
  have hρv : ρ (O - a) = w := Submodule.reflection_sub hnorm
  set e : Plane → ℝ × ℝ := fun p => (p 0, p 1) with he
  have hepres : MeasurePreserving e volume volume :=
    (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (ι := Fin 2))
  set Ψ : Plane → ℝ × ℝ := fun x => e (ρ (x - a)) with hΨ
  have hΨpres : MeasurePreserving Ψ volume volume :=
    hepres.comp (ρ.measurePreserving.comp (measurePreserving_sub_right volume a))
  have hΨc : Continuous Ψ := by
    have : Continuous e := by fun_prop
    exact this.comp (ρ.continuous.comp (continuous_id.sub continuous_const))
  have hΨd : ∀ x y, ((Ψ x).1 - (Ψ y).1) ^ 2 + ((Ψ x).2 - (Ψ y).2) ^ 2 = dist x y ^ 2 := by
    intro x y
    have h1 := dist_sq_coord (ρ (x - a)) (ρ (y - a))
    rw [LinearIsometryEquiv.dist_map, dist_sub_right] at h1
    rw [h1]
  have hΨa : Ψ a = (0, 0) := by simp [hΨ, he]
  have hΨO : Ψ O = (0, R) := by
    simp only [hΨ, he, hρv, hw]
    simp
  by_cases hb : 0 ≤ (Ψ b).1
  · exact ⟨Ψ, hΨpres, hΨc, hΨd, hΨa, hΨO, hb⟩
  · set σ : ℝ × ℝ → ℝ × ℝ := fun p => (-p.1, p.2) with hσ
    have hσpres : MeasurePreserving σ volume volume := by
      have := (Measure.measurePreserving_neg (volume : Measure ℝ)).prod
        (MeasurePreserving.id (volume : Measure ℝ))
      simpa [Measure.volume_eq_prod] using this
    refine ⟨σ ∘ Ψ, hσpres.comp hΨpres, (by fun_prop : Continuous σ).comp hΨc, fun x y => ?_,
      ?_, ?_, ?_⟩
    · simp only [Function.comp, hσ]
      rw [← hΨd x y]; ring
    · simp [hΨa, hσ]
    · simp [hΨO, hσ]
    · simp only [Function.comp, hσ]; linarith

/-- **Quantitative isodiametric inequality.**  Let `K` be a compact planar set of diameter at most
`d`, contained in the closed disc of radius `R` about `O`, with two points `a, b ∈ K` on the
boundary circle such that `⟪b - O, a - O⟫ ≤ 0`.  If `d/2 < R ≤ d`, then
`|K| ≤ π d²/4 - sin(δ₀/2) G δ₀ / 32`, where `G = 4R² - d²` and `δ₀ = G/(16 d²)`. -/
theorem volume_le_of_circumradius {K : Set Plane} (hK : IsCompact K) {d R : ℝ} {O a b : Plane}
    (hdist : ∀ p ∈ K, ∀ q ∈ K, dist p q ≤ d) (hsub : ∀ x ∈ K, dist x O ≤ R)
    (ha : a ∈ K) (hb : b ∈ K) (haO : dist a O = R) (hbO : dist b O = R)
    (hab : inner ℝ (b - O) (a - O) ≤ 0) (hRd : R ≤ d) (hG : d ^ 2 < 4 * R ^ 2) :
    volume K ≤ ENNReal.ofReal (π * d ^ 2 / 4 -
      Real.sin ((4 * R ^ 2 - d ^ 2) / (16 * d ^ 2) / 2) * (4 * R ^ 2 - d ^ 2) *
        ((4 * R ^ 2 - d ^ 2) / (16 * d ^ 2)) / 32) := by
  have hd0 : 0 ≤ d := (dist_self a).symm.le.trans (hdist a ha a ha)
  have hR : 0 < R := by
    rcases (haO ▸ dist_nonneg : 0 ≤ R).lt_or_eq with h | h
    · exact h
    · rw [← h] at hG; nlinarith
  obtain ⟨Φ, hΦpres, hΦc, hΦd, hΦa, hΦO, hΦb⟩ := exists_coord_isometry a O b haO
  have hinj : Function.Injective Φ := by
    intro x y h
    have := hΦd x y
    rw [h, sub_self, sub_self] at this
    exact dist_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (by linarith [sq_nonneg (dist x y)]))
  set A := Φ '' K with hAdef
  have hAc : IsCompact A := hK.image hΦc
  have hvol : volume K = volume A := by
    rw [← hΦpres.measure_preimage hAc.isClosed.measurableSet.nullMeasurableSet, hAdef,
      hinj.preimage_image]
  rw [hvol]
  -- the inner-product condition says `|b - a|² ≥ 2R²`
  have hab2 : 2 * R ^ 2 ≤ dist b a ^ 2 := by
    rw [dist_eq_norm, show b - a = (b - O) - (a - O) by abel, norm_sub_sq_real, ← dist_eq_norm,
      ← dist_eq_norm, hbO, haO]
    linarith
  have hβ := hΦd b O
  have hβa := hΦd b a
  rw [hΦO, hbO] at hβ
  rw [hΦa] at hβa
  simp only [sub_zero] at hβ hβa
  refine volume_le_of_circumradius_normalized hAc.isClosed.measurableSet (β₁ := (Φ b).1)
    (β₂ := (Φ b).2) ?_ ?_ (hΦa ▸ mem_image_of_mem Φ ha) (mem_image_of_mem Φ hb) hΦb ?_ hβ hR hRd hG
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hΦd x y]
    exact pow_le_pow_left₀ dist_nonneg (hdist x hx y hy) 2
  · rintro _ ⟨x, hx, rfl⟩
    have := hΦd x O
    rw [hΦO] at this
    simp only [sub_zero] at this
    rw [this]
    exact pow_le_pow_left₀ dist_nonneg (hsub x hx) 2
  · nlinarith

/-- A smallest enclosing disc: a compact nonempty planar set `K` has a centre `O` and radius `R`
such that `K` lies in the closed disc of radius `R` about `O`, no disc of smaller radius contains
`K`, and there are contact points `a, b ∈ K` with `⟪b - O, a - O⟫ ≤ 0`. -/
lemma exists_circumcenter {K : Set Plane} (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ O : Plane, ∃ R : ℝ, (∀ x ∈ K, dist x O ≤ R) ∧ (∀ O' : Plane, ∃ x ∈ K, R ≤ dist x O') ∧
      ∃ a ∈ K, ∃ b ∈ K, dist a O = R ∧ dist b O = R ∧ inner ℝ (b - O) (a - O) ≤ 0 := by
  have hmax : ∀ O : Plane, ∃ x ∈ K, ∀ y ∈ K, dist y O ≤ dist x O := fun O =>
    hK.exists_isMaxOn hne (continuous_id.dist continuous_const).continuousOn
  choose g hgK hg using hmax
  set f : Plane → ℝ := fun O => dist (g O) O with hf
  have hlip : LipschitzWith 1 f := LipschitzWith.of_le_add fun O O' => by
    have h1 := hg O' (g O) (hgK O)
    have h2 := dist_triangle (g O) O' O
    simp only [hf]; rw [dist_comm O' O] at h2; linarith
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨O, hO, hOmin⟩ := (isCompact_closedBall x0 (f x0)).exists_isMinOn
    ⟨x0, Metric.mem_closedBall_self (dist_nonneg)⟩ hlip.continuous.continuousOn
  have hglob : ∀ O', f O ≤ f O' := by
    intro O'
    have h3 : f O ≤ f x0 := isMinOn_iff.1 hOmin x0 (Metric.mem_closedBall_self dist_nonneg)
    by_cases h : O' ∈ Metric.closedBall x0 (f x0)
    · exact isMinOn_iff.1 hOmin O' h
    · have h1 : f x0 < dist O' x0 := not_le.1 h
      have h2 : dist x0 O' ≤ f O' := hg O' x0 hx0
      rw [dist_comm] at h1
      linarith
  refine ⟨O, f O, hg O, fun O' => ⟨g O', hgK O', hglob O'⟩, g O, hgK O, ?_⟩
  -- a second contact point: a limit of farthest points from `O + t (a - O)`, `t → 0⁺`
  set u := g O - O with hu
  set x : ℕ → Plane := fun n => g (O + (1 / ((n : ℝ) + 1)) • u) with hx
  obtain ⟨b, hb, φ, hφ, hlim⟩ := hK.tendsto_subseq (x := x) (fun n => hgK _)
  have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ.tendsto_atTop
  have key : ∀ n : ℕ, inner ℝ (x n - O) u ≤ (1 / ((n : ℝ) + 1)) * ‖u‖ ^ 2 / 2 ∧
      f O - (1 / ((n : ℝ) + 1)) * ‖u‖ ≤ dist (x n) O := by
    intro n
    set t : ℝ := 1 / ((n : ℝ) + 1)
    have ht0 : 0 < t := by positivity
    have hR : f O ≤ dist (x n) (O + t • u) := hglob _
    have hxO : dist (x n) O ≤ f O := hg O _ (hgK _)
    constructor
    · have e : dist (x n) (O + t • u) ^ 2 = dist (x n) O ^ 2 - 2 * t * inner ℝ (x n - O) u +
          t ^ 2 * ‖u‖ ^ 2 := by
        rw [dist_eq_norm, dist_eq_norm, show x n - (O + t • u) = (x n - O) - t • u by abel,
          norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
        ring
      have h1 : dist (x n) O ^ 2 ≤ dist (x n) (O + t • u) ^ 2 :=
        pow_le_pow_left₀ dist_nonneg (hxO.trans hR) 2
      have : 2 * t * inner ℝ (x n - O) u ≤ t ^ 2 * ‖u‖ ^ 2 := by linarith
      have : t * (2 * inner ℝ (x n - O) u) ≤ t * (t * ‖u‖ ^ 2) := by linarith
      have := le_of_mul_le_mul_left this ht0
      linarith
    · have h1 := dist_triangle (x n) O (O + t • u)
      have h2 : dist O (O + t • u) = t * ‖u‖ := by
        rw [dist_eq_norm, show O - (O + t • u) = -(t • u) by abel, norm_neg, norm_smul,
          Real.norm_eq_abs, abs_of_pos ht0]
      linarith
  refine ⟨b, hb, rfl, ?_, ?_⟩
  · apply le_antisymm (hg O b hb)
    have hc : Tendsto (fun n => dist ((x ∘ φ) n) O) atTop (𝓝 (dist b O)) :=
      hlim.dist tendsto_const_nhds
    have hr : Tendsto (fun n => f O - (1 / ((φ n : ℝ) + 1)) * ‖u‖) atTop
        (𝓝 (f O - 0 * ‖u‖)) :=
      tendsto_const_nhds.sub (ht.mul tendsto_const_nhds)
    simp only [zero_mul, sub_zero] at hr
    exact le_of_tendsto_of_tendsto' hr hc fun n => (key (φ n)).2
  · have hc : Tendsto (fun n => inner ℝ ((x ∘ φ) n - O) u) atTop (𝓝 (inner ℝ (b - O) u)) :=
      (hlim.sub tendsto_const_nhds).inner tendsto_const_nhds
    have hr : Tendsto (fun n => (1 / ((φ n : ℝ) + 1)) * ‖u‖ ^ 2 / 2) atTop
        (𝓝 (0 * ‖u‖ ^ 2 / 2)) :=
      (ht.mul tendsto_const_nhds).div_const 2
    simp only [zero_mul, zero_div] at hr
    exact le_of_tendsto_of_tendsto' hc hr fun n => (key (φ n)).1

/-- The truncated Voronoi cells of a separated set `X` lie in the union of the unit discs about
its points, so this union has area at least `|X| √3/2`. -/
lemma card_mul_le_volume_union {X : Finset Plane} (hX : IsSeparated X) :
    ENNReal.ofReal (X.card * (√3 / 2)) ≤ volume (⋃ p ∈ X, Metric.closedBall p 1) := by
  have hdisj : (X : Set Plane).PairwiseDisjoint (voronoiCell X) := by
    intro p hp q hq hpq
    rw [Function.onFun, Set.disjoint_left]
    intro z hzp hzq
    have a := hzp.2 q hq (Ne.symm hpq)
    have b := hzq.2 p hp hpq
    linarith
  have hsub : (⋃ p ∈ X, voronoiCell X p) ⊆ ⋃ p ∈ X, Metric.closedBall p 1 := by
    refine iUnion₂_mono fun p _ z hz => Metric.mem_closedBall.2 ?_
    have h := hz.1
    have : dist z p < 1 := by nlinarith [dist_nonneg (x := z) (y := p)]
    exact this.le
  have hvol := measure_mono (μ := volume) hsub
  rw [measure_biUnion_finset hdisj fun p _ => measurableSet_voronoiCell X p] at hvol
  have hcard : X.card • ENNReal.ofReal (√3 / 2) ≤ ∑ p ∈ X, volume (voronoiCell X p) :=
    Finset.card_nsmul_le_sum _ _ _ fun p hp => volume_voronoiCell_ge hX hp
  rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at hcard
  exact hcard.trans hvol

/-- The area deficit of `volume_le_of_circumradius` is at least `c d²` once `2R ≥ d (1 + η')`,
where `c = sin(η'/16) η'²/128`. -/
lemma deficit_lower_bound {d R η' : ℝ} (hd : 0 < d) (hη'0 : 0 < η') (hη'1 : η' ≤ 1 / 2)
    (h2R : d * (1 + η') < 2 * R) (hRd : R ≤ d) :
    Real.sin (η' / 16) * η' ^ 2 / 128 * d ^ 2 ≤
      Real.sin ((4 * R ^ 2 - d ^ 2) / (16 * d ^ 2) / 2) * (4 * R ^ 2 - d ^ 2) *
        ((4 * R ^ 2 - d ^ 2) / (16 * d ^ 2)) / 32 := by
  have hG : d ^ 2 * (1 + 2 * η') ≤ 4 * R ^ 2 := by
    nlinarith [mul_self_lt_mul_self (by positivity) h2R, sq_nonneg η', sq_nonneg d]
  have hR2 : R ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ (by nlinarith) hRd 2
  generalize hGdef : 4 * R ^ 2 - d ^ 2 = G
  have hGlow : 2 * η' * d ^ 2 ≤ G := by rw [← hGdef]; linarith
  have hGup : G ≤ 3 * d ^ 2 := by rw [← hGdef]; linarith
  generalize hδ₀ : G / (16 * d ^ 2) = δ₀
  have hδlow : η' / 8 ≤ δ₀ := by
    rw [← hδ₀, le_div_iff₀ (by positivity)]; linarith
  have hδup : δ₀ ≤ 3 / 16 := by
    rw [← hδ₀, div_le_iff₀ (by positivity)]; linarith
  have hsin0 : 0 < Real.sin (η' / 16) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_gt_three])
  have hsin : Real.sin (η' / 16) ≤ Real.sin (δ₀ / 2) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos])
      (by linarith [Real.pi_gt_three]) (by linarith)
  have h2 : Real.sin (η' / 16) * (2 * η' * d ^ 2) ≤ Real.sin (δ₀ / 2) * G :=
    mul_le_mul hsin hGlow (by positivity) (hsin0.le.trans hsin)
  have h3 : Real.sin (η' / 16) * (2 * η' * d ^ 2) * (η' / 8) ≤ Real.sin (δ₀ / 2) * G * δ₀ :=
    mul_le_mul h2 hδlow (by positivity) (mul_nonneg (hsin0.le.trans hsin)
      ((by positivity : (0 : ℝ) ≤ 2 * η' * d ^ 2).trans hGlow))
  linarith only [h3]

/-- **Lemma 3.1 (roundness, outer half).**  For every `η > 0`, eventually every optimal
configuration lies in a disc of radius `D/2 + η D`. -/
theorem round_center_of_optimal (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n in atTop, ∀ X, IsOptimal n X →
      ∃ O : Plane, ∀ x ∈ X, dist x O ≤ diam X / 2 + η * diam X := by
  obtain ⟨η', hη'0, hη'1, hη'η⟩ : ∃ η' : ℝ, 0 < η' ∧ η' ≤ 1 / 2 ∧ η' ≤ η / 2 :=
    ⟨min η 1 / 2, by positivity, by linarith [min_le_right η 1],
      by linarith [min_le_left η 1]⟩
  obtain ⟨c, hc, hc0⟩ : ∃ c : ℝ, c = Real.sin (η' / 16) * η' ^ 2 / 128 ∧ 0 < c :=
    ⟨_, rfl, by
      have := Real.sin_pos_of_pos_of_lt_pi (x := η' / 16) (by positivity)
        (by linarith [Real.pi_gt_three])
      positivity⟩
  filter_upwards [eventually_ge_atTop 2,
    tendsto_minDiam.eventually_ge_atTop (max (2 / η) (π / c))] with n hn hD X hX
  rw [← hX.diam_eq] at hD
  have hD1 : 2 / η ≤ diam X := (le_max_left _ _).trans hD
  have hD2 : π / c ≤ diam X := (le_max_right _ _).trans hD
  have hDpos : 0 < diam X := hX.diam_pos hn
  -- the lattice bound `π D² / 4 ≤ n √3 / 2`
  have hlat : π * diam X ^ 2 / 4 ≤ n * (√3 / 2) := by
    have h := minDiam_sq_le n (by omega)
    rw [← hX.diam_eq] at h
    unfold aStar at h
    rw [le_div_iff₀ Real.pi_pos] at h
    linarith
  have hn0 : (0 : ℝ) < n * (√3 / 2) := by
    have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    positivity
  have hcard := card_mul_le_volume_union hX.1.2
  rw [hX.1.1] at hcard
  obtain ⟨p0, hp0⟩ : X.Nonempty := by
    rw [← Finset.card_pos, hX.1.1]; omega
  generalize hDdef : diam X = D at *
  generalize hK : (⋃ p ∈ X, Metric.closedBall p (1 : ℝ)) = K at hcard
  have hKc : IsCompact K := hK ▸ X.finite_toSet.isCompact_biUnion fun p _ => isCompact_closedBall p 1
  have hXK : ∀ x ∈ X, x ∈ K := fun x hx =>
    hK ▸ mem_biUnion hx (Metric.mem_closedBall_self zero_le_one)
  have hKd : ∀ a ∈ K, ∀ b ∈ K, dist a b ≤ D + 2 := by
    intro a ha b hb
    rw [← hK] at ha hb
    obtain ⟨p, hp, hap⟩ := mem_iUnion₂.1 ha
    obtain ⟨q, hq, hbq⟩ := mem_iUnion₂.1 hb
    have h1 := Metric.mem_closedBall.1 hap
    have h2 := Metric.mem_closedBall.1 hbq
    have h3 := hDdef ▸ dist_le_diam hp hq
    have := dist_triangle4 a p q b
    rw [dist_comm q b] at this
    linarith
  obtain ⟨O, R, hsub, hmin, a, ha, b, hb, haO, hbO, hab⟩ :=
    exists_circumcenter hKc ⟨p0, hXK p0 hp0⟩
  by_cases hR : R ≤ (D + 2) * (1 + η') / 2
  · refine ⟨O, fun x hx => (hsub x (hXK x hx)).trans (hR.trans ?_)⟩
    have : η * D ≥ 2 := by rw [ge_iff_le, ← div_le_iff₀' hη]; exact hD1
    nlinarith only [this, hη'1, mul_le_mul_of_nonneg_right hη'η hDpos.le]
  exfalso
  push_neg at hR
  have hRd : R ≤ D + 2 := by
    obtain ⟨x, hx, hxR⟩ := hmin p0
    exact hxR.trans (hKd x hx p0 (hXK p0 hp0))
  have hdpos : 0 < D + 2 := by linarith
  have h2R : (D + 2) * (1 + η') < 2 * R := by linarith
  have hG' : (D + 2) ^ 2 < 4 * R ^ 2 := by
    nlinarith [mul_self_lt_mul_self (by positivity) h2R, sq_nonneg η']
  have hvol := volume_le_of_circumradius hKc hKd hsub ha hb haO hbO hab hRd hG'
  have hκ := deficit_lower_bound hdpos hη'0 hη'1 h2R hRd
  rw [← hc] at hκ
  have hfin := (ENNReal.ofReal_le_ofReal_iff').1 (hcard.trans hvol)
  have hfin' := hfin.resolve_right (not_le.2 hn0)
  have hcd : c * (D + 2) ^ 2 < π * (D + 2) := by
    nlinarith only [hκ, hfin', hlat, Real.pi_pos]
  have hcd' : c * (D + 2) < π := lt_of_mul_lt_mul_right (by nlinarith only [hcd]) hdpos.le
  have : π ≤ c * D := by rw [div_le_iff₀ hc0] at hD2; linarith
  nlinarith only [this, hcd', hc0]

end Erdos99
end

end Roundness

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `Winding`
-/

section Winding

/-!
# Winding sums: vanishing, jumps, and connected polylines

Three facts about the winding sums `windSum` of closed polygonal paths in `ℂ`:

* `windSum_eq_zero_of_half`: if all vertices of a closed polygonal path lie in an open half-plane
  whose boundary passes through `x`, the winding sum at `x` vanishes;
* `windSum_jump`: points close to the midpoint of an edge, on opposite sides of it, have
  different winding sums (provided the midpoint is not on the rest of the path);
* `isPreconnected_polyline`: a polygonal path is preconnected.
-/

open scoped Real ComplexConjugate
open Complex Set Metric

@[expose] public noncomputable section

namespace EstablishedExternalResults

/-- Argument of a quotient of two complex numbers in the open right half-plane. -/
lemma arg_div_of_re_pos {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) :
    arg (w / z) = arg w - arg z := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  have h1 := abs_arg_lt_pi_div_two_iff.2 (Or.inl hz)
  have h2 := abs_arg_lt_pi_div_two_iff.2 (Or.inl hw)
  have hzpi : arg z ≠ π := by
    intro h; rw [h, abs_of_pos Real.pi_pos] at h1; linarith [Real.pi_pos]
  rw [div_eq_mul_inv, (arg_mul_eq_add_arg_iff hw0 (inv_ne_zero hz0)).2, arg_inv, if_neg hzpi]
  · ring
  · rw [arg_inv, if_neg hzpi]
    rw [abs_lt] at h1 h2
    constructor <;> linarith

/-- Telescoping form of the winding sum for a path in an open half-plane seen from `x`. -/
lemma windSum_eq_of_half {x ω : ℂ} : ∀ (u : ℂ) (l : List ℂ),
    (∀ v ∈ u :: l, 0 < ((v - x) * conj ω).re) →
    windSum x (u :: l) = arg (((u :: l).getLast (by simp) - x) * conj ω) - arg ((u - x) * conj ω)
  | u, [], _ => by simp [windSum]
  | u, v :: l, h => by
    have ih := windSum_eq_of_half v l (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hu := h u (by simp)
    have hv := h v (by simp)
    have hω : conj ω ≠ 0 := by rintro h0; rw [h0, mul_zero] at hu; simp at hu
    have hq : (v - x) / (u - x) = ((v - x) * conj ω) / ((u - x) * conj ω) := by
      rw [mul_div_mul_right _ _ hω]
    simp only [windSum]
    rw [ih, hq, arg_div_of_re_pos hu hv, List.getLast_cons_cons]
    ring

/-- **Vanishing of the winding sum.**  If all vertices of a closed polygonal path lie in an open
half-plane whose boundary line passes through `x`, the winding sum at `x` is zero. -/
lemma windSum_eq_zero_of_half {x ω : ℂ} (u : ℂ) (l : List ℂ)
    (hc : (u :: l).getLast (by simp) = u) (h : ∀ v ∈ u :: l, 0 < ((v - x) * conj ω).re) :
    windSum x (u :: l) = 0 := by
  rw [windSum_eq_of_half u l h, hc, sub_self]

/-- A point in the open half-plane of a closed polygonal path is not on the path. -/
lemma not_mem_polyline_of_half {x ω : ℂ} : ∀ (u : ℂ) (l : List ℂ),
    (∀ v ∈ u :: l, 0 < ((v - x) * conj ω).re) → x ∉ polyline (u :: l)
  | u, [], h => by
    simp only [polyline, mem_singleton_iff]
    rintro rfl; have := h x (by simp); simp at this
  | u, v :: l, h => by
    rintro (hx | hx)
    · obtain ⟨a, c, ha, hc, hac, hxe⟩ := hx
      have hu := h u (by simp)
      have hv := h v (by simp)
      have e : (0 : ℂ) = (a : ℂ) * ((u - x) * conj ω) + (c : ℂ) * ((v - x) * conj ω) := by
        have h1 : (a : ℂ) + c = 1 := by exact_mod_cast hac
        rw [Complex.real_smul, Complex.real_smul] at hxe
        linear_combination -(conj ω) * hxe + x * conj ω * h1
      have := congrArg Complex.re e
      simp only [zero_re, add_re, re_ofReal_mul] at this
      rcases eq_or_lt_of_le ha with h0 | h0
      · subst h0; have : c = 1 := by linarith
        subst this; nlinarith
      · nlinarith [mul_pos h0 hu, mul_nonneg hc hv.le]
    · exact not_mem_polyline_of_half v l (fun y hy => h y (List.mem_cons_of_mem _ hy)) hx

lemma re_im_quot (w : ℂ) :
    ((w - 1) / w).re = (w.re ^ 2 - w.re + w.im ^ 2) / normSq w ∧
      ((w - 1) / w).im = w.im / normSq w := by
  rw [div_re, div_im]
  simp only [sub_re, one_re, sub_im, one_im, sub_zero]
  constructor <;> ring

lemma re_im_aux {w : ℂ} (hw : ‖w - 1 / 2‖ < 1 / 2) : w.re ^ 2 - w.re + w.im ^ 2 < 0 := by
  have h := (sq_lt_sq₀ (norm_nonneg _) (by norm_num)).2 hw
  rw [← normSq_eq_norm_sq, normSq_apply] at h
  simp only [sub_re, sub_im] at h
  norm_num at h
  nlinarith

lemma normSq_pos_of_half {w : ℂ} (hw : ‖w - 1 / 2‖ < 1 / 2) : 0 < normSq w := by
  rw [normSq_pos]
  rintro rfl
  norm_num at hw

lemma arg_quot_gt {w : ℂ} (hw : ‖w - 1 / 2‖ < 1 / 2) (him : 0 < w.im) :
    π / 2 < arg ((w - 1) / w) := by
  obtain ⟨hre, hi⟩ := re_im_quot w
  have hn := normSq_pos_of_half hw
  have h1 : ((w - 1) / w).re < 0 := by rw [hre]; exact div_neg_of_neg_of_pos (re_im_aux hw) hn
  have h2 : 0 < ((w - 1) / w).im := by rw [hi]; exact div_pos him hn
  have h3 : ¬ |arg ((w - 1) / w)| ≤ π / 2 := by rw [abs_arg_le_pi_div_two_iff]; linarith
  rw [abs_of_nonneg (arg_nonneg_iff.2 h2.le)] at h3
  linarith

lemma arg_quot_lt {w : ℂ} (hw : ‖w - 1 / 2‖ < 1 / 2) (him : w.im < 0) :
    arg ((w - 1) / w) < -(π / 2) := by
  obtain ⟨hre, hi⟩ := re_im_quot w
  have hn := normSq_pos_of_half hw
  have h1 : ((w - 1) / w).re < 0 := by rw [hre]; exact div_neg_of_neg_of_pos (re_im_aux hw) hn
  have h2 : ((w - 1) / w).im < 0 := by rw [hi]; exact div_neg_of_neg_of_pos him hn
  have h3 : ¬ |arg ((w - 1) / w)| ≤ π / 2 := by rw [abs_arg_le_pi_div_two_iff]; linarith
  rw [abs_of_neg (arg_neg_iff.2 h2)] at h3
  linarith

/-- **Jump of the winding sum across an edge.**  Points near the midpoint of the first edge
`[a, b]` of a closed polygonal path, on opposite sides of that edge, have different winding
sums, provided the midpoint is not on the rest of the path. -/
lemma windSum_jump {a b : ℂ} (hab : a ≠ b) (l : List ℂ)
    (hm : (a + b) / 2 ∉ polyline (b :: l)) :
    ∃ r > 0, ∀ x y : ℂ, dist x ((a + b) / 2) < r → dist y ((a + b) / 2) < r →
      0 < (wc a b x).im → (wc a b y).im < 0 → windSum x (a :: b :: l) ≠ windSum y (a :: b :: l) := by
  set m := (a + b) / 2 with hmdef
  have hgc := continuousAt_windSum m b l hm
  obtain ⟨δ, hδ, hδg⟩ := Metric.continuousAt_iff.mp hgc (π / 2) (by positivity)
  have hba : 0 < ‖b - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab.symm)
  have hwm : wc a b m = 1 / 2 := by
    have : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
    simp only [wc, hmdef]; field_simp; ring
  refine ⟨min δ (‖b - a‖ / 2), lt_min hδ (by positivity), ?_⟩
  have key : ∀ x : ℂ, dist x m < min δ (‖b - a‖ / 2) →
      ‖wc a b x - 1 / 2‖ < 1 / 2 ∧ windSum x (a :: b :: l) =
        arg ((wc a b x - 1) / wc a b x) + windSum x (b :: l) ∧
        |windSum x (b :: l) - windSum m (b :: l)| < π / 2 := by
    intro x hx
    have hx1 := hx.trans_le (min_le_left _ _)
    have hx2 := hx.trans_le (min_le_right _ _)
    have hn := norm_wc_sub hab x m
    rw [hwm] at hn
    have hw : ‖wc a b x - 1 / 2‖ < 1 / 2 := by
      by_contra hc; push_neg at hc
      have : ‖b - a‖ / 2 ≤ dist x m := by rw [← hn]; nlinarith
      linarith
    refine ⟨hw, ?_, ?_⟩
    · have hw0 : wc a b x ≠ 0 := by rintro h0; rw [h0] at hw; norm_num at hw
      simp only [windSum]
      congr 2
      conv_lhs => rw [eq_param hab x]
      exact div_param_eq hab hw0
    · have := hδg hx1
      rwa [Real.dist_eq] at this
  intro x y hx hy hxi hyi heq
  obtain ⟨hwx, ex, gx⟩ := key x hx
  obtain ⟨hwy, ey, gy⟩ := key y hy
  have h1 := arg_quot_gt hwx hxi
  have h2 := arg_quot_lt hwy hyi
  rw [ex, ey] at heq
  rw [abs_lt] at gx gy
  linarith

/-- A polygonal path is preconnected. -/
lemma isPreconnected_polyline : ∀ (u : ℂ) (l : List ℂ), IsPreconnected (polyline (u :: l))
  | u, [] => by simp only [polyline]; exact isPreconnected_singleton
  | u, v :: l => by
    simp only [polyline]
    exact IsPreconnected.union v (right_mem_segment ℝ u v) (head_mem_polyline v l)
      (convex_segment u v).isPreconnected (isPreconnected_polyline v l)

end EstablishedExternalResults
end

end Winding

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `Crux`
-/

section Crux

/-!
# Paths joining alternating boundary points cross

The planar input to the connectivity of the contact graph (Lemma 2.1).  Let `a₁, a₂` and
`b, b'` be exposed points of a finite planar set `Y`, with `b` and `b'` on opposite sides of the
line `a₁ a₂`.  Then a polygonal path from `a₁` to `a₂` and a polygonal path from `b` to `b'`, all
of whose vertices lie in `Y`, must meet (`paths_cross`).

The proof closes the first path by a slightly dilated copy of the boundary arc of the convex hull
on the side of `b` (the arc is supplied as a list of hull vertices whose consecutive pairs are
supporting edges).  The winding sum of the resulting closed polygon vanishes at `b'`, but not at
`b`: near the dilated hull side issuing from `b` the winding sum jumps (`windSum_jump`).  Since the
second path joins `b` to `b'` without meeting the polygon, this is a contradiction.
-/

open scoped Real ComplexConjugate
open Complex Set Metric EstablishedExternalResults

@[expose] public noncomputable section

namespace Erdos99

/-- The cross product `u × v` of two plane vectors, viewed as complex numbers. -/
def ccr (u v : ℂ) : ℝ := (conj u * v).im

lemma cr_eq (u v : ℂ) : ccr u v = u.re * v.im - u.im * v.re := by
  simp [ccr]; ring

lemma seg_param {x y z : ℂ} (hz : z ∈ segment ℝ x y) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ z = x + (s : ℂ) * (y - x) := by
  rw [segment_eq_image'] at hz
  obtain ⟨s, ⟨hs0, hs1⟩, rfl⟩ := hz
  exact ⟨s, hs0, hs1, by simp only [Complex.real_smul]⟩

lemma mem_segment_of_param {x y : ℂ} {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    x + (s : ℂ) * (y - x) ∈ segment ℝ x y := by
  rw [segment_eq_image']
  exact ⟨s, ⟨hs0, hs1⟩, by simp only [Complex.real_smul]⟩

lemma mem_polyline_of_mem : ∀ (u : ℂ) (l : List ℂ) (z : ℂ), z ∈ u :: l → z ∈ polyline (u :: l)
  | u, [], z, hz => by simp only [List.mem_singleton] at hz; subst hz; simp [polyline]
  | u, v :: l, z, hz => by
    rcases List.mem_cons.1 hz with rfl | hz
    · exact head_mem_polyline _ _
    · exact Or.inr (mem_polyline_of_mem v l z hz)

lemma getLast_mem_polyline (u : ℂ) (l : List ℂ) :
    (u :: l).getLast (by simp) ∈ polyline (u :: l) :=
  mem_polyline_of_mem u l _ (List.getLast_mem _)

/-- Points of a polygonal path lie on a segment joining two consecutive vertices. -/
lemma mem_polyline_of_chain {R : ℂ → ℂ → Prop} : ∀ (u : ℂ) (l : List ℂ), (u :: l).IsChain R →
    ∀ z ∈ polyline (u :: l), (l = [] ∧ z = u) ∨ ∃ x y, R x y ∧ z ∈ segment ℝ x y
  | u, [], _, z, hz => by simp only [polyline, mem_singleton_iff] at hz; exact Or.inl ⟨rfl, hz⟩
  | u, v :: l, hc, z, hz => by
    rw [List.isChain_cons_cons] at hc
    rcases hz with hz | hz
    · exact Or.inr ⟨u, v, hc.1, hz⟩
    · rcases mem_polyline_of_chain v l hc.2 z hz with ⟨rfl, rfl⟩ | h
      · exact Or.inr ⟨u, z, hc.1, right_mem_segment ℝ u z⟩
      · exact Or.inr h

lemma isChain_seg_subset : ∀ (u : ℂ) (l : List ℂ),
    (u :: l).IsChain (fun x y => segment ℝ x y ⊆ polyline (u :: l))
  | u, [] => List.isChain_singleton _
  | u, v :: l => by
    rw [List.isChain_cons_cons]
    refine ⟨fun z hz => Or.inl hz, ?_⟩
    exact (isChain_seg_subset v l).imp fun x y h => h.trans fun z hz => Or.inr hz

lemma isChain_and_mem {α : Type*} {R : α → α → Prop} : ∀ {l : List α}, l.IsChain R →
    l.IsChain (fun x y => R x y ∧ x ∈ l ∧ y ∈ l)
  | [], _ => List.isChain_nil
  | [a], _ => List.isChain_singleton a
  | a :: b :: l, h => by
    rw [List.isChain_cons_cons] at h ⊢
    refine ⟨⟨h.1, by simp, by simp⟩, ?_⟩
    exact (isChain_and_mem h.2).imp fun x y hxy =>
      ⟨hxy.1, List.mem_cons_of_mem _ hxy.2.1, List.mem_cons_of_mem _ hxy.2.2⟩

/-- An affine functional which is nonnegative at the vertices of a polygonal path is nonnegative
along it. -/
lemma polyline_cr_nonneg {Y : Finset ℂ} {c g : ℂ} (hY : ∀ y ∈ Y, 0 ≤ ccr c (y - g)) :
    ∀ (u : ℂ) (l : List ℂ), (∀ v ∈ u :: l, v ∈ Y) → ∀ z ∈ polyline (u :: l), 0 ≤ ccr c (z - g)
  | u, [], hv, z, hz => by
    simp only [polyline, mem_singleton_iff] at hz; subst hz; exact hY z (hv z (by simp))
  | u, v :: l, hv, z, hz => by
    rcases hz with hz | hz
    · obtain ⟨s, hs0, hs1, rfl⟩ := seg_param hz
      have h1 := hY u (hv u (by simp))
      have h2 := hY v (hv v (by simp))
      have e : ccr c (u + (s : ℂ) * (v - u) - g) = (1 - s) * ccr c (u - g) + s * ccr c (v - g) := by
        simp only [cr_eq, add_re, add_im, sub_re, sub_im, mul_re, mul_im, ofReal_re, ofReal_im]
        ring
      rw [e]; nlinarith
    · exact polyline_cr_nonneg hY v l (fun w hw => hv w (List.mem_cons_of_mem _ hw)) z hz

lemma polyline_re_nonpos {Y : Finset ℂ} {c g : ℂ} (hY : ∀ y ∈ Y, (conj c * (y - g)).re ≤ 0) :
    ∀ (u : ℂ) (l : List ℂ), (∀ v ∈ u :: l, v ∈ Y) → ∀ z ∈ polyline (u :: l),
      (conj c * (z - g)).re ≤ 0
  | u, [], hv, z, hz => by
    simp only [polyline, mem_singleton_iff] at hz; subst hz; exact hY z (hv z (by simp))
  | u, v :: l, hv, z, hz => by
    rcases hz with hz | hz
    · obtain ⟨s, hs0, hs1, rfl⟩ := seg_param hz
      have h1 := hY u (hv u (by simp))
      have h2 := hY v (hv v (by simp))
      have e : (conj c * (u + (s : ℂ) * (v - u) - g)).re =
          (1 - s) * (conj c * (u - g)).re + s * (conj c * (v - g)).re := by
        simp only [add_re, sub_re, mul_re, mul_im, ofReal_re, ofReal_im, conj_re, conj_im,
          add_im, sub_im]
        ring
      rw [e]; nlinarith
    · exact polyline_re_nonpos hY v l (fun w hw => hv w (List.mem_cons_of_mem _ hw)) z hz

lemma wc_im_eq (a b z : ℂ) : (wc a b z).im = ccr (b - a) (z - a) / normSq (b - a) := by
  simp only [wc, div_im, cr_eq, normSq_apply]
  ring

/-- The Lagrange identity behind collinearity transfer. -/
lemma cr_lagrange (e B H : ℂ) :
    normSq e * ccr B H = (conj e * B).re * ccr e H - ccr e B * (conj e * H).re := by
  simp only [cr_eq, normSq_apply, mul_re, conj_re, conj_im]
  ring

lemma ev_lin_pos {c d : ℝ} (hc : 0 < c) : ∀ᶠ ε in nhds (0 : ℝ), 0 < c + ε * d := by
  have hcont : Continuous (fun ε : ℝ => c + ε * d) := by fun_prop
  have := hcont.tendsto 0
  simp only [zero_mul, add_zero] at this
  exact this.eventually (lt_mem_nhds hc)

/-- Notation-free form of the dilation `z ↦ z + ε (z - o)` used below. -/
lemma cr_dil (c g o z : ℂ) (ε : ℝ) :
    ccr c (z + (ε : ℂ) * (z - o) - g) = ccr c (z - g) + ε * ccr c (z - o) := by
  simp only [cr_eq, add_re, add_im, sub_re, sub_im, mul_re, mul_im, ofReal_re, ofReal_im]; ring

lemma re_dil (c g o z : ℂ) (ε : ℝ) :
    (conj c * (z + (ε : ℂ) * (z - o) - g)).re =
      (conj c * (z - g)).re + ε * (conj c * (z - o)).re := by
  simp only [add_re, sub_re, mul_re, mul_im, ofReal_re, ofReal_im, conj_re, conj_im, add_im,
    sub_im]; ring

lemma cr_sub_base (c x y z : ℂ) : ccr c (z - x) = ccr c (z - y) + ccr c (y - x) := by
  simp only [cr_eq, sub_re, sub_im]; ring

lemma cr_self' (c : ℂ) : ccr c c = 0 := by simp only [cr_eq]; ring

lemma cr_smul_right (c z : ℂ) (t : ℝ) : ccr c ((t : ℂ) * z) = t * ccr c z := by
  simp only [cr_eq, mul_re, mul_im, ofReal_re, ofReal_im]; ring

lemma cr_smul_left (c z : ℂ) (t : ℝ) : ccr ((t : ℂ) * c) z = t * ccr c z := by
  simp only [cr_eq, mul_re, mul_im, ofReal_re, ofReal_im]; ring

lemma cr_add_right (c z w : ℂ) : ccr c (z + w) = ccr c z + ccr c w := by
  simp only [cr_eq, add_re, add_im]; ring

lemma cr_sub_right (c z w : ℂ) : ccr c (z - w) = ccr c z - ccr c w := by
  simp only [cr_eq, sub_re, sub_im]; ring

lemma cr_neg_right (c z : ℂ) : ccr c (-z) = -ccr c z := by
  simp only [cr_eq, neg_re, neg_im]; ring

lemma cr_swap (c z : ℂ) : ccr z c = -ccr c z := by simp only [cr_eq]; ring

/-- Points of the dilated copy of a supporting edge lie strictly outside it. -/
lemma cr_dil_seg {g g' o z : ℂ} {ε : ℝ}
    (hz : z ∈ segment ℝ (g + (ε : ℂ) * (g - o)) (g' + (ε : ℂ) * (g' - o))) :
    ccr (g' - g) (z - g) = -ε * ccr (g' - g) (o - g) := by
  obtain ⟨s, -, -, rfl⟩ := seg_param hz
  simp only [cr_eq, add_re, add_im, sub_re, sub_im, mul_re, mul_im, ofReal_re, ofReal_im]; ring

lemma re_conj_neg (z w : ℂ) : (z * conj (-w)).re = -(conj w * z).re := by
  simp only [mul_re, conj_re, conj_im, neg_re, neg_im]; ring

lemma re_conj_I (z c : ℂ) : (z * conj (I * c)).re = ccr c z := by
  simp only [cr_eq, mul_re, mul_im, conj_re, conj_im, I_re, I_im]; ring

lemma rad_param1 {a o z : ℂ} {ε : ℝ} (hε : 0 ≤ ε)
    (hz : z ∈ segment ℝ (a + (ε : ℂ) * (a - o)) a) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ ε ∧ z = a + (t : ℂ) * (a - o) := by
  obtain ⟨s, hs0, hs1, rfl⟩ := seg_param hz
  refine ⟨(1 - s) * ε, by nlinarith, by nlinarith, ?_⟩
  push_cast; ring

lemma rad_param2 {a o z : ℂ} {ε : ℝ} (hε : 0 ≤ ε)
    (hz : z ∈ segment ℝ a (a + (ε : ℂ) * (a - o))) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ ε ∧ z = a + (t : ℂ) * (a - o) := by
  obtain ⟨s, hs0, hs1, rfl⟩ := seg_param hz
  refine ⟨s * ε, by nlinarith, by nlinarith, ?_⟩
  push_cast; ring

lemma rad_cr_ge {a o g c : ℂ} {t ε : ℝ} (ht0 : 0 ≤ t) (htε : t ≤ ε) :
    ccr c (a - g) + ε * (-|ccr c (a - o)|) ≤ ccr c (a + (t : ℂ) * (a - o) - g) := by
  have e : ccr c (a + (t : ℂ) * (a - o) - g) = ccr c (a - g) + t * ccr c (a - o) := by
    simp only [cr_eq, add_re, add_im, sub_re, sub_im, mul_re, mul_im, ofReal_re, ofReal_im]; ring
  rw [e]
  have h1 := neg_abs_le (ccr c (a - o))
  have h2 := abs_nonneg (ccr c (a - o))
  nlinarith

lemma cr_eq_zero_of_cr_eq_zero {e B H : ℂ} (he : e ≠ 0) (hB : ccr e B = 0) (hH : ccr e H = 0) :
    ccr B H = 0 := by
  have := cr_lagrange e B H
  rw [hB, hH, mul_zero, zero_mul, sub_zero] at this
  exact (mul_eq_zero.1 this).resolve_left (normSq_pos.2 he).ne'

lemma cr_base_change (b h p : ℂ) : ccr (h - b) (p - b) = ccr (b - p) (h - p) := by
  simp only [cr_eq, sub_re, sub_im]; ring

lemma cr_seg_param (c b x g : ℂ) (s : ℝ) :
    ccr c (b + (s : ℂ) * (x - b) - g) = (1 - s) * ccr c (b - g) + s * ccr c (x - g) := by
  simp only [cr_eq, add_re, add_im, sub_re, sub_im, mul_re, mul_im, ofReal_re, ofReal_im]; ring

set_option maxHeartbeats 1000000 in
/-- **Paths joining alternating boundary points cross.**  See the module docstring.  The list
`(a₂ :: L₁') ++ (h :: L₂')` is the boundary arc of the hull on the side of `b`, running from `a₂`
through `b` (the last element of `a₂ :: L₁'`) and its successor `h` to `a₁`; its consecutive pairs
are supporting edges with `o` strictly inside. -/
theorem paths_cross (Y : Finset ℂ) {a1 a2 b b' h o : ℂ} {P' Q' L1' L2' : List ℂ}
    (hPY : ∀ z ∈ a1 :: P', z ∈ Y) (hPl : (a1 :: P').getLast (by simp) = a2)
    (hQY : ∀ z ∈ b :: Q', z ∈ Y) (hQl : (b :: Q').getLast (by simp) = b')
    (hPQ : Disjoint (polyline (a1 :: P')) (polyline (b :: Q')))
    (hAY : ∀ z ∈ (a2 :: L1') ++ (h :: L2'), z ∈ Y)
    (hnd : ((a2 :: L1') ++ (h :: L2')).Nodup)
    (hL1 : (a2 :: L1').getLast (by simp) = b) (hL2 : (h :: L2').getLast (by simp) = a1)
    (hchain : ((a2 :: L1') ++ (h :: L2')).IsChain
      (fun g g' => (∀ y ∈ Y, 0 ≤ ccr (g' - g) (y - g)) ∧ 0 < ccr (g' - g) (o - g)))
    (hstrict : ∀ g ∈ (a2 :: L1') ++ (h :: L2'), g ≠ b → g ≠ h → 0 < ccr (h - b) (g - b))
    {u1 u2 w' : ℂ} (hu1 : ∀ y ∈ Y, y ≠ a1 → (conj u1 * (y - a1)).re < 0)
    (hu2 : ∀ y ∈ Y, y ≠ a2 → (conj u2 * (y - a2)).re < 0)
    (hw' : ∀ y ∈ Y, y ≠ b' → (conj w' * (y - b')).re < 0)
    (ho : o ∈ openSegment ℝ a1 a2) (hb' : b' ∉ (a2 :: L1') ++ (h :: L2')) : False := by
  classical
  set A := (a2 :: L1') ++ (h :: L2') with hA
  -- basic membership facts
  have hbA : b ∈ A := by
    rw [hA, ← hL1]; exact List.mem_append_left _ (List.getLast_mem _)
  have hhA : h ∈ A := List.mem_append_right _ (by simp)
  have ha1A : a1 ∈ A := by
    rw [hA, ← hL2]; exact List.mem_append_right _ (List.getLast_mem _)
  have ha2A : a2 ∈ A := by simp [hA]
  have hbY := hAY b hbA
  have hhY := hAY h hhA
  have ha1P : a1 ∈ polyline (a1 :: P') := head_mem_polyline _ _
  have ha2P : a2 ∈ polyline (a1 :: P') := hPl ▸ getLast_mem_polyline _ _
  have hbQ : b ∈ polyline (b :: Q') := head_mem_polyline _ _
  have hb'Q : b' ∈ polyline (b :: Q') := hQl ▸ getLast_mem_polyline _ _
  have hba1 : b ≠ a1 := fun e => hPQ.ne_of_mem ha1P hbQ e.symm
  have hba2 : b ≠ a2 := fun e => hPQ.ne_of_mem ha2P hbQ e.symm
  have hnd' := List.nodup_append.1 hnd
  have hbL2 : b ∉ h :: L2' := fun hb => hnd'.2.2 b (by rw [← hL1]; exact List.getLast_mem _) b hb rfl
  have hhL1 : h ∉ a2 :: L1' := fun hh => hnd'.2.2 h hh h (by simp) rfl
  have ha2h : a2 ≠ h := fun e => hhL1 (e ▸ by simp)
  -- the supporting edge `(b, h)`
  have hjun : (∀ y ∈ Y, 0 ≤ ccr (h - b) (y - b)) ∧ 0 < ccr (h - b) (o - b) := by
    have hl : (a2 :: L1').getLast? = some b := by
      rw [List.getLast?_eq_some_getLast (by simp), hL1]
    exact (List.isChain_append.1 hchain).2.2 b (by simp [hl]) h (by simp)
  set κ := ccr (h - b) (o - b) with hκ
  have hκ0 : 0 < κ := hjun.2
  have hbh : b ≠ h := by rintro rfl; rw [hκ, sub_self] at hκ0; simp [cr_eq] at hκ0
  -- the chains of the two parts
  set supp : ℂ → ℂ → Prop :=
    fun g g' => (∀ y ∈ Y, 0 ≤ ccr (g' - g) (y - g)) ∧ 0 < ccr (g' - g) (o - g) with hsupp
  have hc1 : (a2 :: L1').IsChain supp := (List.isChain_append.1 hchain).1
  have hc2 : (h :: L2').IsChain supp := (List.isChain_append.1 hchain).2.1
  -- the centre `o`
  obtain ⟨α, β, hα, hβ, hαβ, hoe⟩ := ho
  have hoe' : o = (α : ℂ) * a1 + (β : ℂ) * a2 := by rw [← hoe, Complex.real_smul, Complex.real_smul]
  have hαβ' : (α : ℂ) + β = 1 := by exact_mod_cast hαβ
  have ha12 : a1 ≠ a2 := fun e =>
    hnd'.2.2 a2 (by simp) a1 (by rw [← hL2]; exact List.getLast_mem _) e.symm
  have hu1o : 0 < (conj u1 * (a1 - o)).re := by
    have e : a1 - o = (β : ℂ) * (a1 - a2) := by rw [hoe']; linear_combination -a1 * hαβ'
    have := hu1 a2 (hAY a2 ha2A) ha12.symm
    rw [e]
    have e2 : (conj u1 * ((β : ℂ) * (a1 - a2))).re = -β * (conj u1 * (a2 - a1)).re := by
      simp only [mul_re, mul_im, ofReal_re, ofReal_im, conj_re, conj_im, sub_re, sub_im]; ring
    rw [e2]; nlinarith
  have hu2o : 0 < (conj u2 * (a2 - o)).re := by
    have e : a2 - o = (α : ℂ) * (a2 - a1) := by rw [hoe']; linear_combination -a2 * hαβ'
    have := hu2 a1 (hAY a1 ha1A) ha12
    rw [e]
    have e2 : (conj u2 * ((α : ℂ) * (a2 - a1))).re = -α * (conj u2 * (a1 - a2)).re := by
      simp only [mul_re, mul_im, ofReal_re, ofReal_im, conj_re, conj_im, sub_re, sub_im]; ring
    rw [e2]; nlinarith
  -- choice of the dilation factor `ε`
  obtain ⟨ε, hε, c1, c2, c3⟩ : ∃ ε : ℝ, 0 < ε ∧
      (∀ g ∈ A, (conj w' * (g - b')).re + ε * (conj w' * (g - o)).re < 0) ∧
      0 < ccr (h - b) (a2 - b) + ε * (-|ccr (h - b) (a2 - o)|) ∧
      (a1 ≠ h → 0 < ccr (h - b) (a1 - b) + ε * (-|ccr (h - b) (a1 - o)|)) := by
    have e1 : ∀ᶠ ε in nhds (0 : ℝ),
        ∀ g ∈ A.toFinset, 0 < -(conj w' * (g - b')).re + ε * (-(conj w' * (g - o)).re) := by
      refine (Filter.eventually_all_finset _).2 fun g hg => ev_lin_pos ?_
      have hgA := List.mem_toFinset.1 hg
      have := hw' g (hAY g hgA) (fun e => hb' (e ▸ hgA))
      linarith
    have e2 := ev_lin_pos (d := -|ccr (h - b) (a2 - o)|)
      (hstrict a2 ha2A hba2.symm ha2h)
    have e3 : ∀ᶠ ε in nhds (0 : ℝ), a1 ≠ h → 0 < ccr (h - b) (a1 - b) + ε * (-|ccr (h - b) (a1 - o)|) := by
      by_cases ha1h : a1 = h
      · exact Filter.Eventually.of_forall fun _ h' => absurd ha1h h'
      · exact (ev_lin_pos (hstrict a1 ha1A hba1.symm ha1h)).mono fun _ hx _ => hx
    have hall := (e1.and (e2.and e3)).filter_mono (nhdsWithin_le_nhds (s := Ioi 0))
    obtain ⟨ε, ⟨h1, h2, h3⟩, hε⟩ := (hall.and self_mem_nhdsWithin).exists
    refine ⟨ε, hε, fun g hg => ?_, h2, h3⟩
    have := h1 g (List.mem_toFinset.2 hg)
    linarith
  -- the dilation about `o`
  set dil : ℂ → ℂ := fun z => z + (ε : ℂ) * (z - o) with hdil
  set R : List ℂ := L2'.map dil ++ (a1 :: P') ++ (a2 :: L1').map dil with hR
  have hRne : R ≠ [] := by simp [hR]
  have hΓl : (dil b :: dil h :: R).getLast (by simp) = dil b := by
    rw [List.getLast_cons (by simp), List.getLast_cons hRne]
    simp only [hR]
    rw [List.getLast_append_of_ne_nil _ (by simp), List.getLast_map (by simp), hL1]
  -- the consecutive pairs of `dil h :: R`
  set Rel0 : ℂ → ℂ → Prop := fun x y =>
    (∃ g g', supp g g' ∧ ((g ∈ a2 :: L1' ∧ g' ∈ a2 :: L1') ∨ (g ∈ h :: L2' ∧ g' ∈ h :: L2')) ∧
      x = dil g ∧ y = dil g') ∨ (x = dil a1 ∧ y = a1) ∨
    (segment ℝ x y ⊆ polyline (a1 :: P') ∧ x ∈ Y ∧ y ∈ Y) ∨ (x = a2 ∧ y = dil a2) with hRel0
  have hchR : (dil h :: R).IsChain Rel0 := by
    have hA2 : ((h :: L2').map dil).IsChain Rel0 := by
      rw [List.isChain_map]
      exact (isChain_and_mem hc2).imp fun x y hxy =>
        Or.inl ⟨x, y, hxy.1, Or.inr ⟨hxy.2.1, hxy.2.2⟩, rfl, rfl⟩
    have hA1 : ((a2 :: L1').map dil).IsChain Rel0 := by
      rw [List.isChain_map]
      exact (isChain_and_mem hc1).imp fun x y hxy =>
        Or.inl ⟨x, y, hxy.1, Or.inl ⟨hxy.2.1, hxy.2.2⟩, rfl, rfl⟩
    have hPc : (a1 :: P').IsChain Rel0 :=
      (isChain_and_mem (isChain_seg_subset a1 P')).imp fun x y hxy =>
        Or.inr (Or.inr (Or.inl ⟨hxy.1, hPY x hxy.2.1, hPY y hxy.2.2⟩))
    have hl2 : ((h :: L2').map dil).getLast? = some (dil a1) := by
      rw [List.getLast?_map, List.getLast?_eq_some_getLast (by simp), hL2]; rfl
    have hlP : (((h :: L2').map dil) ++ (a1 :: P')).getLast? = some a2 := by
      rw [List.getLast?_append_of_ne_nil _ (by simp), List.getLast?_eq_some_getLast (by simp), hPl]
    show (((h :: L2').map dil ++ (a1 :: P')) ++ (a2 :: L1').map dil).IsChain Rel0
    rw [List.isChain_append, List.isChain_append]
    refine ⟨⟨hA2, hPc, ?_⟩, hA1, ?_⟩
    · intro x hx y hy
      rw [hl2, Option.mem_some_iff] at hx
      simp only [List.head?_cons, Option.mem_some_iff] at hy
      exact Or.inr (Or.inl ⟨hx.symm, hy.symm⟩)
    · intro x hx y hy
      rw [hlP, Option.mem_some_iff] at hx
      simp only [List.map_cons, List.head?_cons, Option.mem_some_iff] at hy
      exact Or.inr (Or.inr (Or.inr ⟨hx.symm, hy.symm⟩))
  have hvert : ∀ v ∈ dil b :: dil h :: R, (∃ g ∈ A, v = dil g) ∨ v ∈ a1 :: P' := by
    intro v hv
    simp only [hR, List.mem_cons, List.mem_append, List.mem_map] at hv
    rcases hv with rfl | rfl | ((⟨g, hg, rfl⟩ | rfl | hv) | ⟨g, hg, rfl⟩)
    · exact Or.inl ⟨b, hbA, rfl⟩
    · exact Or.inl ⟨h, hhA, rfl⟩
    · exact Or.inl ⟨g, by simp [hA, hg], rfl⟩
    · exact Or.inr (by simp)
    · exact Or.inr (List.mem_cons_of_mem _ hv)
    · refine Or.inl ⟨g, ?_, rfl⟩
      rcases hg with rfl | hg
      · exact ha2A
      · simp [hA, hg]
  -- the midpoint of the dilated edge `(b, h)`
  set ms := (dil b + dil h) / 2 with hms
  have hF2 : ∀ g g' : ℂ, ccr (g' - g) (ms - g) = (1 + ε) * (ccr (g' - g) (b - g) +
      ccr (g' - g) (h - g)) / 2 - ε * ccr (g' - g) (o - g) := by
    intro g g'
    simp only [hms, hdil, cr_eq, add_re, add_im, sub_re, sub_im, mul_re, mul_im, ofReal_re,
      ofReal_im, div_ofNat_re, div_ofNat_im]
    ring
  have hF1 : ccr (h - b) (ms - b) = -ε * κ := by
    rw [hF2, hκ]; simp only [cr_eq, sub_re, sub_im]; ring
  have hκ' : ccr (h - o) (b - o) = -κ := by
    rw [hκ]; simp only [cr_eq, sub_re, sub_im]; ring
  have hF3 : ccr (h - o) (ms - o) = -((1 + ε) * κ / 2) := by
    have e : κ = -ccr (h - o) (b - o) := by linarith [hκ']
    rw [e]
    simp only [hms, hdil, cr_eq, add_re, add_im, sub_re, sub_im, mul_re, mul_im, ofReal_re,
      ofReal_im, div_ofNat_re, div_ofNat_im]
    ring
  -- (A3) the midpoint `ms` is not on the rest of the polygon
  have hA3 : ms ∉ polyline (dil h :: R) := by
    intro hm
    rcases mem_polyline_of_chain _ _ hchR ms hm with ⟨hR0, -⟩ | ⟨x, y, hxy, hz⟩
    · exact hRne hR0
    rcases hxy with ⟨g, g', hs, hpart, hx, hy⟩ | ⟨hx, hy⟩ | ⟨hsub, -, -⟩ | ⟨hx, hy⟩ <;>
      try rw [hx, hy] at hz
    · -- a dilated edge other than `(b, h)`
      have e1 := cr_dil_seg hz
      rw [hF2] at e1
      have hB := hs.1 b hbY
      have hH := hs.1 h hhY
      have hB0 : ccr (g' - g) (b - g) = 0 := by nlinarith
      have hH0 : ccr (g' - g) (h - g) = 0 := by nlinarith
      have hgg : g' - g ≠ 0 := by
        intro e; have := hs.2; rw [e] at this; simp [cr_eq] at this
      have hgA : g ∈ A ∧ g' ∈ A := by
        rcases hpart with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨List.mem_append_left _ h1, List.mem_append_left _ h2⟩
        · exact ⟨List.mem_append_right _ h1, List.mem_append_right _ h2⟩
      have key : ∀ p ∈ A, p ≠ b → p ≠ h → ccr (g' - g) (b - p) = 0 →
          ccr (g' - g) (h - p) = 0 → False := by
        intro p hp hpb hph h1 h2
        have := hstrict p hp hpb hph
        rw [cr_base_change, cr_eq_zero_of_cr_eq_zero hgg h1 h2] at this
        exact lt_irrefl _ this
      by_cases hg : g = b ∨ g = h
      · by_cases hg' : g' = b ∨ g' = h
        · have hne : g ≠ g' := fun e => hgg (by rw [e, sub_self])
          rcases hg with rfl | rfl <;> rcases hg' with rfl | rfl
          · exact hne rfl
          · rcases hpart with ⟨-, h2⟩ | ⟨h1, -⟩
            · exact hhL1 h2
            · exact hbL2 h1
          · rcases hpart with ⟨h1, -⟩ | ⟨-, h2⟩
            · exact hhL1 h1
            · exact hbL2 h2
          · exact hne rfl
        · push_neg at hg'
          refine key g' hgA.2 hg'.1 hg'.2 ?_ ?_
          · rw [cr_sub_base _ _ g, hB0]; simp only [cr_eq, sub_re, sub_im]; ring
          · rw [cr_sub_base _ _ g, hH0]; simp only [cr_eq, sub_re, sub_im]; ring
      · push_neg at hg
        exact key g hgA.1 hg.1 hg.2 hB0 hH0
    · -- the radial segment at `a₁`
      obtain ⟨t, ht0, htε, hmz⟩ := rad_param1 hε.le hz
      by_cases ha1h : a1 = h
      · have : ccr (h - o) (ms - o) = 0 := by
          rw [hmz, ha1h]
          simp only [cr_eq, add_re, add_im, sub_re, sub_im, mul_re, mul_im, ofReal_re, ofReal_im]
          ring
        rw [this] at hF3
        nlinarith
      · have h1 := rad_cr_ge (c := h - b) (g := b) (o := o) ht0 htε (a := a1)
        have h2 := c3 ha1h
        rw [← hmz, hF1] at h1
        nlinarith
    · -- a segment of the first path
      have := polyline_cr_nonneg hjun.1 a1 P' hPY ms (hsub hz)
      rw [hF1] at this
      nlinarith
    · -- the radial segment at `a₂`
      obtain ⟨t, ht0, htε, hmz⟩ := rad_param2 hε.le hz
      have := rad_cr_ge (c := h - b) (g := b) (o := o) ht0 htε (a := a2)
      rw [← hmz, hF1] at this
      nlinarith
  -- classification of the points of the closed polygon
  have hcase : ∀ z ∈ polyline (dil b :: dil h :: R),
      (∃ g g', supp g g' ∧ ccr (g' - g) (z - g) = -ε * ccr (g' - g) (o - g)) ∨
      (∃ t : ℝ, 0 ≤ t ∧ t ≤ ε ∧ z = a1 + (t : ℂ) * (a1 - o)) ∨ z ∈ polyline (a1 :: P') ∨
      (∃ t : ℝ, 0 ≤ t ∧ t ≤ ε ∧ z = a2 + (t : ℂ) * (a2 - o)) := by
    intro z hz
    rcases hz with hz | hz
    · exact Or.inl ⟨b, h, hjun, cr_dil_seg hz⟩
    rcases mem_polyline_of_chain _ _ hchR z hz with ⟨hR0, -⟩ | ⟨x, y, hxy, hz⟩
    · exact absurd hR0 hRne
    rcases hxy with ⟨g, g', hs, -, hx, hy⟩ | ⟨hx, hy⟩ | ⟨hsub, -, -⟩ | ⟨hx, hy⟩
    · rw [hx, hy] at hz; exact Or.inl ⟨g, g', hs, cr_dil_seg hz⟩
    · rw [hx, hy] at hz; exact Or.inr (Or.inl (rad_param1 hε.le hz))
    · exact Or.inr (Or.inr (Or.inl (hsub hz)))
    · rw [hx, hy] at hz; exact Or.inr (Or.inr (Or.inr (rad_param2 hε.le hz)))
  have hcr0 : ∀ c : ℂ, ccr c (b - b) = 0 := fun c => by simp [cr_eq]
  -- the jump of the winding sum across the dilated edge `(b, h)`
  have hdd : dil h - dil b = ((1 + ε : ℝ) : ℂ) * (h - b) := by
    simp only [hdil]; push_cast; ring
  have hdbh : dil b ≠ dil h := by
    intro e
    have h0 : dil h - dil b = 0 := by rw [e, sub_self]
    rw [hdd] at h0
    rcases mul_eq_zero.1 h0 with h0 | h0
    · norm_cast at h0; linarith
    · exact hbh (sub_eq_zero.1 h0).symm
  have hdilcr : ∀ x, ccr (dil h - dil b) (x - dil b) = (1 + ε) * (ccr (h - b) (x - b) + ε * κ) := by
    intro x
    rw [hκ]
    simp only [hdil, cr_eq, add_re, add_im, sub_re, sub_im, mul_re, mul_im, ofReal_re, ofReal_im]
    ring
  have hnsq : 0 < normSq (dil h - dil b) := normSq_pos.2 (sub_ne_zero.2 hdbh.symm)
  obtain ⟨r, hr, hjump⟩ := windSum_jump hdbh R hA3
  set N := ‖b - ms‖ with hN
  have hN0 : 0 ≤ N := norm_nonneg _
  set τ : ℝ := min (1 / 2) (r / (2 * (N + 1))) with hτ
  have hτ0 : 0 < τ := lt_min (by norm_num) (by positivity)
  have hτ1 : τ ≤ 1 / 2 := min_le_left _ _
  have hτr : τ * N < r := by
    have h1 : τ ≤ r / (2 * (N + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  obtain ⟨xin, hxin⟩ : ∃ x : ℂ, x = ms + (τ : ℂ) * (b - ms) := ⟨_, rfl⟩
  obtain ⟨xout, hxout⟩ : ∃ x : ℂ, x = ms + ((-τ : ℝ) : ℂ) * (b - ms) := ⟨_, rfl⟩
  have hxin_cr : ∀ c g, ccr c (xin - g) = (1 - τ) * ccr c (ms - g) + τ * ccr c (b - g) := by
    intro c g; rw [hxin, cr_seg_param]
  have hxout_cr : ∀ c g, ccr c (xout - g) = (1 - -τ) * ccr c (ms - g) + -τ * ccr c (b - g) := by
    intro c g; rw [hxout, cr_seg_param]
  have hxinb : ccr (h - b) (xin - b) = -((1 - τ) * ε * κ) := by
    rw [hxin_cr, hF1, hcr0]; ring
  have hxoutb : ccr (h - b) (xout - b) = -((1 + τ) * ε * κ) := by
    rw [hxout_cr, hF1, hcr0]; ring
  have hdin : dist xin ms < r := by
    rw [dist_eq_norm, hxin, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hτ0.le]
    exact hτr
  have hdout : dist xout ms < r := by
    rw [dist_eq_norm, hxout, add_sub_cancel_left, norm_mul, Complex.norm_real, norm_neg,
      Real.norm_of_nonneg hτ0.le]
    exact hτr
  have himin : 0 < (wc (dil b) (dil h) xin).im := by
    rw [wc_im_eq, hdilcr, hxinb]
    apply div_pos _ hnsq
    rw [show (1 + ε) * (-((1 - τ) * ε * κ) + ε * κ) = (1 + ε) * (τ * ε * κ) by ring]
    positivity
  have himout : (wc (dil b) (dil h) xout).im < 0 := by
    rw [wc_im_eq, hdilcr, hxoutb]
    apply div_neg_of_neg_of_pos _ hnsq
    rw [show (1 + ε) * (-((1 + τ) * ε * κ) + ε * κ) = -((1 + ε) * (τ * ε * κ)) by ring]
    have : 0 < (1 + ε) * (τ * ε * κ) := by positivity
    linarith
  have hne := hjump xin xout hdin hdout himin himout
  -- the winding sum vanishes at `xout`
  have hW_out : windSum xout (dil b :: dil h :: R) = 0 := by
    refine windSum_eq_zero_of_half (ω := I * (h - b)) _ _ hΓl fun v hv => ?_
    rw [re_conj_I]
    have e : ccr (h - b) (v - xout) = ccr (h - b) (v - b) - ccr (h - b) (xout - b) := by
      simp only [cr_eq, sub_re, sub_im]; ring
    rw [e, hxoutb]
    have hpos : 0 < (1 + τ) * ε * κ := by positivity
    rcases hvert v hv with ⟨g, hg, rfl⟩ | hv
    · have hG := hjun.1 g (hAY g hg)
      have e2 : ccr (h - b) (dil g - b) = (1 + ε) * ccr (h - b) (g - b) - ε * κ := by
        rw [hκ]
        simp only [hdil, cr_eq, add_re, add_im, sub_re, sub_im, mul_re, mul_im, ofReal_re,
          ofReal_im]
        ring
      rw [e2]
      have : 0 ≤ (1 + ε) * ccr (h - b) (g - b) := by positivity
      have : 0 < τ * ε * κ := by positivity
      nlinarith
    · have := hjun.1 v (hPY v hv)
      linarith
  -- the winding sum vanishes at `b'`
  have hW_b' : windSum b' (dil b :: dil h :: R) = 0 := by
    refine windSum_eq_zero_of_half (ω := -w') _ _ hΓl fun v hv => ?_
    rw [re_conj_neg]
    rcases hvert v hv with ⟨g, hg, rfl⟩ | hv
    · have e := re_dil w' b' o g ε
      have := c1 g hg
      simp only [hdil]
      linarith
    · have hvb' : v ≠ b' := fun e => hPQ.ne_of_mem (mem_polyline_of_mem _ _ _ hv) hb'Q e
      have := hw' v (hPY v hv) hvb'
      linarith
  -- (A1) the segment from `b` to `xin` avoids the polygon
  have hA1 : ∀ z ∈ segment ℝ b xin, z ∉ polyline (dil b :: dil h :: R) := by
    intro z hz hzΓ
    obtain ⟨s, hs0, hs1, hzs⟩ := seg_param hz
    have hzb : ∀ c g, ccr c (z - g) = (1 - s) * ccr c (b - g) + s * ccr c (xin - g) := by
      intro c g; rw [hzs, cr_seg_param]
    have hzb' : ccr (h - b) (z - b) = -(s * ((1 - τ) * ε * κ)) := by
      rw [hzb, hxinb, hcr0]; ring
    have hle : ccr (h - b) (z - b) ≤ 0 := by
      rw [hzb']
      have : 0 < (1 - τ) * ε * κ := by
        have : 0 < 1 - τ := by linarith
        positivity
      nlinarith
    rcases hcase z hzΓ with ⟨g, g', hs, he⟩ | ⟨t, ht0, htε, hzt⟩ | hzP | ⟨t, ht0, htε, hzt⟩
    · have hB := hs.1 b hbY
      have hH := hs.1 h hhY
      have hK := hs.2
      rw [hzb, hxin_cr, hF2] at he
      set B := ccr (g' - g) (b - g)
      set H := ccr (g' - g) (h - g)
      set K := ccr (g' - g) (o - g)
      have h1 : 0 ≤ (1 - s) * B := mul_nonneg (by linarith) hB
      have h2 : 0 ≤ s * (1 - τ) * (1 + ε) * (B + H) := by
        have : 0 ≤ 1 - τ := by linarith
        positivity
      have h3 : 0 ≤ s * τ * B := by positivity
      have h4 : 0 < (1 - s * (1 - τ)) * (ε * K) := by
        have : s * (1 - τ) ≤ 1 * (1 - τ) := mul_le_mul_of_nonneg_right hs1 (by linarith)
        have : 0 < 1 - s * (1 - τ) := by linarith
        positivity
      nlinarith
    · by_cases ha1h : a1 = h
      · have e0 : ccr (h - o) (z - o) = 0 := by
          rw [hzt, ha1h]
          simp only [cr_eq, add_re, add_im, sub_re, sub_im, mul_re, mul_im, ofReal_re, ofReal_im]
          ring
        rw [hzb, hxin_cr, hF3, hκ'] at e0
        have q1 : 0 ≤ (1 - s) * (1 - τ) * κ :=
          mul_nonneg (mul_nonneg (by linarith) (by linarith)) hκ0.le
        have q2 : 0 ≤ s * (1 - τ) * (1 + ε) * κ :=
          mul_nonneg (mul_nonneg (mul_nonneg hs0 (by linarith)) (by linarith)) hκ0.le
        have q3 : 0 < τ * κ := mul_pos hτ0 hκ0
        nlinarith
      · have h1 := rad_cr_ge (c := h - b) (g := b) (o := o) ht0 htε (a := a1)
        have h2 := c3 ha1h
        rw [← hzt] at h1
        linarith
    · have hnn := polyline_cr_nonneg hjun.1 a1 P' hPY z hzP
      have hs0' : s = 0 := by
        have : 0 < (1 - τ) * ε * κ := by
          have : 0 < 1 - τ := by linarith
          positivity
        rw [hzb'] at hnn
        nlinarith
      rw [hzs, hs0'] at hzP
      simp only [ofReal_zero, zero_mul, add_zero] at hzP
      exact hPQ.ne_of_mem hzP hbQ rfl
    · have h1 := rad_cr_ge (c := h - b) (g := b) (o := o) ht0 htε (a := a2)
      rw [← hzt] at h1
      linarith
  -- (A2) the second path avoids the polygon
  have hA2 : ∀ z ∈ polyline (b :: Q'), z ∉ polyline (dil b :: dil h :: R) := by
    intro z hzQ hzΓ
    have hzP : z ∉ polyline (a1 :: P') := fun hzP => hPQ.ne_of_mem hzP hzQ rfl
    have hrad : ∀ (a u : ℂ), a ∈ polyline (a1 :: P') → (∀ y ∈ Y, y ≠ a → (conj u * (y - a)).re < 0) →
        0 < (conj u * (a - o)).re → ∀ t : ℝ, 0 ≤ t → z = a + (t : ℂ) * (a - o) → False := by
      intro a u haP hu huo t ht0 hzt
      have hY : ∀ y ∈ Y, (conj u * (y - a)).re ≤ 0 := by
        intro y hy
        by_cases hya : y = a
        · simp [hya]
        · exact (hu y hy hya).le
      have := polyline_re_nonpos hY b Q' hQY z hzQ
      have e : (conj u * (z - a)).re = t * (conj u * (a - o)).re := by
        rw [hzt]
        simp only [add_re, sub_re, mul_re, mul_im, ofReal_re, ofReal_im, conj_re, conj_im,
          add_im, sub_im]
        ring
      rw [e] at this
      have ht : t = 0 := by nlinarith
      rw [hzt, ht] at hzP
      simp only [ofReal_zero, zero_mul, add_zero] at hzP
      exact hzP haP
    rcases hcase z hzΓ with ⟨g, g', hs, he⟩ | ⟨t, ht0, -, hzt⟩ | hzP' | ⟨t, ht0, -, hzt⟩
    · have := polyline_cr_nonneg hs.1 b Q' hQY z hzQ
      have : 0 < ε * ccr (g' - g) (o - g) := mul_pos hε hs.2
      linarith
    · exact hrad a1 u1 ha1P hu1 hu1o t ht0 hzt
    · exact hzP hzP'
    · exact hrad a2 u2 ha2P hu2 hu2o t ht0 hzt
  have hW1 := windSum_eq_of_isPreconnected (convex_segment b xin).isPreconnected _ _ hΓl hA1
    (left_mem_segment ℝ b xin) (right_mem_segment ℝ b xin)
  have hW2 := windSum_eq_of_isPreconnected (isPreconnected_polyline b Q') _ _ hΓl hA2 hbQ hb'Q
  exact hne (by rw [← hW1, hW2, hW_b', hW_out])

end Erdos99
end

end Crux

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `Arc`
-/

section Arc

/-!
# Boundary arcs of finite planar sets, and the crossing lemma for contact paths

For a finite set `Y ⊆ ℂ` and two hull vertices `a₁, a₂`, the hull vertices lying strictly on one
side of the line `a₁ a₂`, listed by angle around a point `o` of the open chord `a₁ a₂`, form
together with `a₂` and `a₁` a chain of supporting edges (`exists_arc`).  Combined with
`paths_cross`, this shows that unit-step paths in a separated set joining `a₁` to `a₂` and joining
two hull vertices on opposite sides of the line `a₁ a₂` must share a vertex (`unit_paths_meet`).
-/

open scoped Real ComplexConjugate
open Complex Set Metric EstablishedExternalResults

@[expose] public noncomputable section

namespace Erdos99

/-- The extreme points of the convex hull of a finite set of complex numbers. -/
abbrev IsHV (Y : Finset ℂ) (z : ℂ) : Prop := z ∈ extremePoints ℝ (convexHull ℝ (Y : Set ℂ))

lemma IsHV.mem {Y : Finset ℂ} {z : ℂ} (h : IsHV Y z) : z ∈ Y := by
  have := extremePoints_convexHull_subset h
  exact_mod_cast this

lemma clm_apply_C (f : ℂ →L[ℝ] ℝ) (z : ℂ) : f z = z.re * f 1 + z.im * f I := by
  have e : z = z.re • (1 : ℂ) + z.im • I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [e]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- Hull vertices of finite sets are exposed. -/
lemma exposed_of_extreme {Y : Finset ℂ} {v : ℂ} (hv : IsHV Y v) :
    ∃ u : ℂ, ∀ y ∈ Y, y ≠ v → (conj u * (y - v)).re < 0 := by
  set t := convexHull ℝ ((Y : Set ℂ) \ {v})
  have hvt : v ∉ t := by
    intro h
    have h1 : v ∈ extremePoints ℝ t :=
      inter_extremePoints_subset_extremePoints_of_subset
        (convexHull_mono diff_subset) ⟨h, hv⟩
    exact (extremePoints_convexHull_subset h1).2 rfl
  obtain ⟨f, u, hfu, hb⟩ := geometric_hahn_banach_point_closed (convex_convexHull ℝ _)
    ((Y.finite_toSet.diff).isCompact_convexHull.isClosed) hvt
  refine ⟨-⟨f 1, f I⟩, fun y hy hyv => ?_⟩
  have := hb y (subset_convexHull ℝ _ ⟨hy, hyv⟩)
  rw [clm_apply_C] at this hfu
  simp only [mul_re, conj_re, conj_im, neg_re, neg_im, sub_re, sub_im]
  nlinarith

/-- If some point of `Y` lies strictly on the negative side of a line, so does a hull vertex. -/
lemma exists_extreme_cr_neg {Y : Finset ℂ} {c g y : ℂ} (hy : y ∈ Y) (hneg : ccr c (y - g) < 0) :
    ∃ v ∈ Y, IsHV Y v ∧ ccr c (v - g) < 0 := by
  by_contra hcon
  push_neg at hcon
  set K := {z : ℂ | 0 ≤ ccr c (z - g)} with hKdef
  have hKc : IsClosed K := by
    have : Continuous (fun z : ℂ => ccr c (z - g)) := by
      simp only [cr_eq]; fun_prop
    exact isClosed_le continuous_const this
  have hKv : Convex ℝ K := by
    intro x hx z hz a b ha hb hab
    obtain rfl : b = 1 - a := by linarith
    simp only [hKdef, mem_setOf_eq, cr_eq, add_re, add_im, sub_re, sub_im, smul_re, smul_im,
      smul_eq_mul] at hx hz ⊢
    have h1 := mul_nonneg ha hx
    have h2 := mul_nonneg hb hz
    nlinarith
  have hsub : extremePoints ℝ (convexHull ℝ (Y : Set ℂ)) ⊆ K := fun v hv =>
    hcon v (IsHV.mem hv) hv
  have hcomp : IsCompact (convexHull ℝ (Y : Set ℂ)) := Y.finite_toSet.isCompact_convexHull
  have hcl := closure_convexHull_extremePoints hcomp (convex_convexHull ℝ _)
  have hy' : y ∈ convexHull ℝ (Y : Set ℂ) := subset_convexHull ℝ _ (by exact_mod_cast hy)
  rw [← hcl] at hy'
  have hyK : y ∈ K := (closure_minimal (convexHull_min hsub hKv) hKc) hy'
  exact absurd hyK (not_le.2 hneg)

/-- A strict convex combination is not an extreme point. -/
lemma not_extreme_comb {K : Set ℂ} (hK : Convex ℝ K) {x p q r : ℂ} (hp : p ∈ K) (hq : q ∈ K)
    (hr : r ∈ K) {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c) (habc : a + b + c = 1)
    (hx : x = (a : ℂ) * p + (b : ℂ) * q + (c : ℂ) * r) (hpx : p ≠ x) :
    x ∉ extremePoints ℝ K := by
  intro hxe
  have hbc : 0 < b + c := by linarith
  have hbc' : (b : ℂ) + c ≠ 0 := by exact_mod_cast hbc.ne'
  set w := ((b / (b + c) : ℝ) : ℂ) * q + ((c / (b + c) : ℝ) : ℂ) * r with hw
  have hwK : w ∈ K := by
    have := hK hq hr (div_nonneg hb.le hbc.le) (div_nonneg hc hbc.le)
      (by field_simp)
    simpa only [hw, Complex.real_smul] using this
  have hseg : x ∈ openSegment ℝ p w := by
    refine ⟨a, b + c, ha, hbc, by linarith, ?_⟩
    rw [hx, Complex.real_smul, Complex.real_smul, hw]
    push_cast
    field_simp
    ring
  exact hpx ((mem_extremePoints.1 hxe).2 p hp w hwK hseg).1

lemma cramer (e1 e2 w : ℂ) :
    (ccr e1 e2 : ℂ) * w = (ccr w e2 : ℂ) * e1 + (ccr e1 w : ℂ) * e2 := by
  apply Complex.ext <;> simp [cr_eq] <;> ring

lemma cr_jacobi (e B H : ℂ) :
    (ccr B H : ℂ) * e + (ccr H e : ℂ) * B + (ccr e B : ℂ) * H = 0 := by
  apply Complex.ext <;> simp [cr_eq] <;> ring

/-- Two hull vertices with no hull vertex angularly between them (as seen from a point `o` of
the hull) span a supporting edge. -/
lemma support_of_no_between {Y : Finset ℂ} {o g g' : ℂ} (ho : o ∈ convexHull ℝ (Y : Set ℂ))
    (hg : IsHV Y g) (hg' : IsHV Y g') (hgg' : 0 < ccr (g - o) (g' - o))
    (hno : ∀ v ∈ Y, IsHV Y v → ¬ (0 < ccr (g - o) (v - o) ∧ 0 < ccr (v - o) (g' - o))) :
    (∀ y ∈ Y, 0 ≤ ccr (g' - g) (y - g)) ∧ 0 < ccr (g' - g) (o - g) := by
  have hK := convex_convexHull ℝ (Y : Set ℂ)
  have hgK := hg.1
  have hg'K := hg'.1
  have hκ : ccr (g' - g) (o - g) = ccr (g - o) (g' - o) := by
    simp only [cr_eq, sub_re, sub_im]; ring
  have hog' : o ≠ g' := by rintro rfl; rw [sub_self] at hgg'; simp [cr_eq] at hgg'
  have hog : o ≠ g := by rintro rfl; rw [sub_self] at hgg'; simp [cr_eq] at hgg'
  refine ⟨fun y hy => ?_, hκ ▸ hgg'⟩
  by_contra hneg
  push_neg at hneg
  obtain ⟨v, hvY, hv, hvneg⟩ := exists_extreme_cr_neg hy hneg
  have hvK := hv.1
  set c := ccr (g - o) (g' - o) with hc
  set A := ccr (v - o) (g' - o) with hA
  set B := ccr (g - o) (v - o) with hB
  have hsum : ccr (g' - g) (v - g) = c - A - B := by
    rw [hc, hA, hB]; simp only [cr_eq, sub_re, sub_im]; ring
  have hcr := cramer (g - o) (g' - o) (v - o)
  rw [← hc, ← hA, ← hB] at hcr
  by_cases hA0 : A ≤ 0
  · have hB0 : 0 < B := by linarith
    have key : (B : ℂ) * g' = ((B - c + A : ℝ) : ℂ) * o + (c : ℂ) * v + ((-A : ℝ) : ℂ) * g := by
      push_cast; linear_combination -hcr
    have hB' : (B : ℂ) ≠ 0 := by exact_mod_cast hB0.ne'
    refine not_extreme_comb hK ho hvK hgK (a := (B - c + A) / B) (b := c / B) (c := -A / B)
      (div_pos (by linarith) hB0) (div_pos hgg' hB0) (div_nonneg (by linarith) hB0.le)
      (by field_simp; ring) ?_ ?_ hg'
    · calc g' = (B : ℂ)⁻¹ * ((B : ℂ) * g') := by field_simp
        _ = _ := by rw [key]; push_cast; ring
    · exact hog'
  · push_neg at hA0
    by_cases hB0 : B ≤ 0
    · have key : (A : ℂ) * g = ((A - c + B : ℝ) : ℂ) * o + (c : ℂ) * v + ((-B : ℝ) : ℂ) * g' := by
        push_cast; linear_combination -hcr
      have hA' : (A : ℂ) ≠ 0 := by exact_mod_cast hA0.ne'
      refine not_extreme_comb hK ho hvK hg'K (a := (A - c + B) / A) (b := c / A) (c := -B / A)
        (div_pos (by linarith) hA0) (div_pos hgg' hA0) (div_nonneg (by linarith) hA0.le)
        (by field_simp; ring) ?_ ?_ hg
      · calc g = (A : ℂ)⁻¹ * ((A : ℂ) * g) := by field_simp
          _ = _ := by rw [key]; push_cast; ring
      · exact hog
    · push_neg at hB0
      exact hno v hvY hv ⟨hB0, hA0⟩

/-- Three hull vertices are never collinear (in the presence of a centre `o`). -/
lemma eq_of_collinear_extreme {Y : Finset ℂ} {o b h g : ℂ} (hb : IsHV Y b) (hh : IsHV Y h)
    (hg : IsHV Y g) (hκ : 0 < ccr (h - b) (o - b)) (hz : ccr (h - b) (g - b) = 0) :
    g = b ∨ g = h := by
  by_contra hne
  push_neg at hne
  have hK := convex_convexHull ℝ (Y : Set ℂ)
  set c := ccr (b - o) (h - o) with hc
  have hc' : c = ccr (h - b) (o - b) := by rw [hc]; simp only [cr_eq, sub_re, sub_im]; ring
  have hc0 : 0 < c := hc' ▸ hκ
  set A := ccr (g - o) (h - o) with hA
  set B := ccr (b - o) (g - o) with hB
  have hsum : c - A - B = 0 := by
    rw [← hz, hc, hA, hB]; simp only [cr_eq, sub_re, sub_im]; ring
  have hcr := cramer (b - o) (h - o) (g - o)
  rw [← hc, ← hA, ← hB] at hcr
  by_cases hA0 : 0 < A
  · by_cases hB0 : 0 < B
    · have key : (c : ℂ) * g = (A : ℂ) * b + (B : ℂ) * h := by
        have : (c : ℂ) - A - B = 0 := by exact_mod_cast hsum
        linear_combination hcr + o * this
      have hc'' : (c : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
      refine not_extreme_comb hK hb.1 hh.1 hh.1 (a := A / c) (b := B / c) (c := 0)
        (div_pos hA0 hc0) (div_pos hB0 hc0) le_rfl (by field_simp; linarith) ?_ hne.1.symm hg
      calc g = (c : ℂ)⁻¹ * ((c : ℂ) * g) := by field_simp
        _ = _ := by rw [key]; push_cast; ring
    · push_neg at hB0
      have hA1 : 0 < A - c := by
        rcases hB0.lt_or_eq with h1 | h1
        · linarith
        · exfalso
          have : (A : ℂ) * (b - g) = 0 := by
            have e1 : (c : ℂ) = A := by exact_mod_cast (by linarith : c = A)
            have e2 : (B : ℂ) = 0 := by exact_mod_cast h1
            linear_combination -hcr + (g - o) * e1 - (h - o) * e2
          rcases mul_eq_zero.1 this with h2 | h2
          · exact hA0.ne' (by exact_mod_cast h2)
          · exact hne.1 (sub_eq_zero.1 h2).symm
      have key : (A : ℂ) * b = (c : ℂ) * g + ((-B : ℝ) : ℂ) * h := by
        have : (c : ℂ) - A - B = 0 := by exact_mod_cast hsum
        push_cast; linear_combination -hcr - o * this
      refine not_extreme_comb hK hg.1 hh.1 hh.1 (a := c / A) (b := -B / A) (c := 0)
        (div_pos hc0 hA0) (div_pos (by linarith) hA0) le_rfl (by field_simp; linarith) ?_
        hne.1 hb
      have hA' : (A : ℂ) ≠ 0 := by exact_mod_cast hA0.ne'
      calc b = (A : ℂ)⁻¹ * ((A : ℂ) * b) := by field_simp
        _ = _ := by rw [key]; push_cast; ring
  · push_neg at hA0
    have hB0 : 0 < B := by linarith
    have hB1 : 0 < B - c := by
      rcases hA0.lt_or_eq with h1 | h1
      · linarith
      · exfalso
        have : (B : ℂ) * (h - g) = 0 := by
          have e1 : (c : ℂ) = B := by exact_mod_cast (by linarith : c = B)
          have e2 : (A : ℂ) = 0 := by exact_mod_cast h1
          linear_combination -hcr + (g - o) * e1 - (b - o) * e2
        rcases mul_eq_zero.1 this with h2 | h2
        · exact hB0.ne' (by exact_mod_cast h2)
        · exact hne.2 (sub_eq_zero.1 h2).symm
    have key : (B : ℂ) * h = (c : ℂ) * g + ((-A : ℝ) : ℂ) * b := by
      have : (c : ℂ) - A - B = 0 := by exact_mod_cast hsum
      push_cast; linear_combination -hcr - o * this
    refine not_extreme_comb hK hg.1 hb.1 hb.1 (a := c / B) (b := -A / B) (c := 0)
      (div_pos hc0 hB0) (div_pos (by linarith) hB0) le_rfl (by field_simp; linarith) ?_
      hne.2 hh
    have hB' : (B : ℂ) ≠ 0 := by exact_mod_cast hB0.ne'
    calc h = (B : ℂ)⁻¹ * ((B : ℂ) * h) := by field_simp
      _ = _ := by rw [key]; push_cast; ring

/-- Consecutive entries of a strictly sorted list leave no list entry strictly between them. -/
lemma isChain_gap {α : Type*} (f : α → ℝ) : ∀ l : List α, l.Pairwise (fun x y => f x < f y) →
    l.IsChain (fun x y => f x < f y ∧ ∀ v ∈ l, f v ≤ f x ∨ f y ≤ f v)
  | [], _ => List.isChain_nil
  | [a], _ => List.isChain_singleton a
  | x :: y :: l, hp => by
    rw [List.isChain_cons_cons]
    have hp' := List.pairwise_cons.1 hp
    refine ⟨⟨hp'.1 y (by simp), fun v hv => ?_⟩, ?_⟩
    · rcases List.mem_cons.1 hv with rfl | hv
      · exact Or.inl le_rfl
      rcases List.mem_cons.1 hv with rfl | hv
      · exact Or.inr le_rfl
      · exact Or.inr (List.pairwise_cons.1 hp'.2 |>.1 v hv).le
    · refine (isChain_and_mem (isChain_gap f (y :: l) hp'.2)).imp fun a b hab => ⟨hab.1.1, ?_⟩
      intro v hv
      rcases List.mem_cons.1 hv with rfl | hv
      · exact Or.inl (hp'.1 a hab.2.1).le
      · exact hab.1.2 v hv

lemma cone_pos {e B H W : ℂ} (hB : 0 < ccr e B) (hH : 0 < ccr e H) (hBH : 0 < ccr B H)
    (h1 : 0 < ccr B W) (h2 : 0 < ccr W H) : 0 < ccr e W := by
  have key : ccr B H * ccr e W = ccr W H * ccr e B + ccr B W * ccr e H := by
    simp only [cr_eq]; ring
  have : 0 < ccr B H * ccr e W := by rw [key]; positivity
  exact pos_of_mul_pos_right this hBH.le

lemma phi_lt_iff {e B H : ℂ} (hB : 0 < ccr e B) (hH : 0 < ccr e H) :
    -(conj e * B).re / ccr e B < -(conj e * H).re / ccr e H ↔ 0 < ccr B H := by
  rw [div_lt_div_iff₀ hB hH]
  have hl := cr_lagrange e B H
  have he : 0 < normSq e := by
    rw [normSq_pos]; rintro rfl; simp [cr_eq] at hB
  constructor
  · intro hlt
    have : 0 < normSq e * ccr B H := by rw [hl]; linarith
    exact pos_of_mul_pos_right this he.le
  · intro h
    have : 0 < normSq e * ccr B H := mul_pos he h
    rw [hl] at this
    linarith

/-- Two hull vertices in the same direction from a point of the hull coincide. -/
lemma eq_of_same_ray_extreme {Y : Finset ℂ} {o e x y : ℂ} (hoH : o ∈ convexHull ℝ (Y : Set ℂ))
    (hxe : IsHV Y x) (hye : IsHV Y y) (hs : 0 < ccr e (x - o)) (ht : 0 < ccr e (y - o))
    (h0 : ccr (x - o) (y - o) = 0) : x = y := by
  have hox : o ≠ x := by rintro rfl; rw [sub_self] at hs; simp [cr_eq] at hs
  have hoy : o ≠ y := by rintro rfl; rw [sub_self] at ht; simp [cr_eq] at ht
  set s := ccr e (x - o)
  set t := ccr e (y - o)
  have hj := cr_jacobi e (x - o) (y - o)
  rw [h0] at hj
  have hj' : (t : ℂ) * (x - o) = (s : ℂ) * (y - o) := by
    have : ccr (y - o) e = -t := by rw [cr_swap]
    rw [this] at hj; push_cast at hj; linear_combination -hj
  have hK := convex_convexHull ℝ (Y : Set ℂ)
  rcases lt_trichotomy s t with hst | hst | hst
  · exfalso
    refine not_extreme_comb hK hoH hye.1 hye.1 (a := 1 - s / t) (b := s / t) (c := 0)
      (by rw [sub_pos, div_lt_one ht]; exact hst) (div_pos hs ht) le_rfl (by ring) ?_ hox hxe
    have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    calc x = (t : ℂ)⁻¹ * ((t : ℂ) * (x - o)) + o := by field_simp; ring
      _ = _ := by rw [hj']; push_cast; field_simp; ring
  · rw [hst] at hj'
    have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    have := mul_left_cancel₀ ht' hj'
    exact sub_left_injective this
  · exfalso
    refine not_extreme_comb hK hoH hxe.1 hxe.1 (a := 1 - t / s) (b := t / s) (c := 0)
      (by rw [sub_pos, div_lt_one hs]; exact hst) (div_pos ht hs) le_rfl (by ring) ?_ hoy hye
    have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    calc y = (s : ℂ)⁻¹ * ((s : ℂ) * (y - o)) + o := by field_simp; ring
      _ = _ := by rw [← hj']; push_cast; field_simp; ring

/-- **The boundary arc.**  For hull vertices `a₁, a₂` of a finite set `Y`, a point `o` of the open
chord `a₁ a₂`, and a hull vertex `b` strictly on the positive side of the line `o a₂`, the hull
vertices on that side, ordered by angle around `o`, form with `a₂` and `a₁` a chain of supporting
edges passing through `b`. -/
theorem exists_arc (Y : Finset ℂ) {a1 a2 b o : ℂ} (ha1 : IsHV Y a1) (ha2 : IsHV Y a2)
    (hb : IsHV Y b) (ho : o ∈ openSegment ℝ a1 a2) (hbp : 0 < ccr (a2 - o) (b - o)) :
    ∃ h : ℂ, ∃ L1' L2' : List ℂ,
      (∀ z ∈ (a2 :: L1') ++ (h :: L2'), z ∈ Y) ∧ ((a2 :: L1') ++ (h :: L2')).Nodup ∧
      (a2 :: L1').getLast (by simp) = b ∧ (h :: L2').getLast (by simp) = a1 ∧
      ((a2 :: L1') ++ (h :: L2')).IsChain
        (fun g g' => (∀ y ∈ Y, 0 ≤ ccr (g' - g) (y - g)) ∧ 0 < ccr (g' - g) (o - g)) ∧
      (∀ g ∈ (a2 :: L1') ++ (h :: L2'), g ≠ b → g ≠ h → 0 < ccr (h - b) (g - b)) ∧
      (∀ g ∈ (a2 :: L1') ++ (h :: L2'), g = a1 ∨ g = a2 ∨ 0 < ccr (a2 - o) (g - o)) := by
  classical
  have hoH : o ∈ convexHull ℝ (Y : Set ℂ) :=
    (convex_convexHull ℝ _).openSegment_subset ha1.1 ha2.1 ho
  obtain ⟨α, β, hα, hβ, hαβ, hoe⟩ := ho
  have hoe' : o = (α : ℂ) * a1 + (β : ℂ) * a2 := by
    rw [← hoe, Complex.real_smul, Complex.real_smul]
  have hαβ' : (α : ℂ) + β = 1 := by exact_mod_cast hαβ
  set e := a2 - o with he
  have hαe : (α : ℂ) * (a1 - o) = -((β : ℂ) * e) := by
    rw [he, hoe']; linear_combination (-((α : ℂ) * a1 + (β : ℂ) * a2)) * hαβ'
  have hcra1 : ∀ z, α * ccr z (a1 - o) = β * ccr e z := by
    intro z
    rw [← cr_smul_right, hαe]
    simp only [cr_eq, neg_re, neg_im, mul_re, mul_im, ofReal_re, ofReal_im]; ring
  have hea1 : ccr e (a1 - o) = 0 := by
    have := hcra1 e
    rw [cr_self'] at this
    have h0 : α * ccr e (a1 - o) = 0 := by rw [this, mul_zero]
    exact (mul_eq_zero.1 h0).resolve_left hα.ne'
  have hea2 : ccr e (a2 - o) = 0 := cr_self' e
  have ha12 : a1 ≠ a2 := by
    rintro rfl
    have : e = 0 := by
      have h1 : (α : ℂ) * e = -((β : ℂ) * e) := hαe
      have h2 : ((α : ℂ) + β) * e = 0 := by linear_combination h1
      rwa [hαβ', one_mul] at h2
    rw [this] at hbp; simp [cr_eq] at hbp
  -- the angular parameter
  set φ : ℂ → ℝ := fun z => -(conj e * (z - o)).re / ccr e (z - o) with hφ
  set V := Y.filter (fun z => IsHV Y z ∧ 0 < ccr e (z - o)) with hVdef
  have hV : ∀ z, z ∈ V ↔ z ∈ Y ∧ IsHV Y z ∧ 0 < ccr e (z - o) := fun z => by
    rw [hVdef, Finset.mem_filter]
  have hbV : b ∈ V := (hV b).2 ⟨hb.mem, hb, hbp⟩
  have hφlt : ∀ x ∈ V, ∀ y ∈ V, φ x < φ y ↔ 0 < ccr (x - o) (y - o) := fun x hx y hy =>
    phi_lt_iff ((hV x).1 hx).2.2 ((hV y).1 hy).2.2
  -- distinct elements of `V` are in distinct directions
  have hinj : ∀ x ∈ V, ∀ y ∈ V, ccr (x - o) (y - o) = 0 → x = y := fun x hx y hy h0 =>
    eq_of_same_ray_extreme hoH ((hV x).1 hx).2.1 ((hV y).1 hy).2.1 ((hV x).1 hx).2.2
      ((hV y).1 hy).2.2 h0
  -- the sorted list of `V`
  set l := V.toList.mergeSort (fun x y => decide (φ x ≤ φ y)) with hl
  have hlmem : ∀ z, z ∈ l ↔ z ∈ V := fun z => by
    rw [(List.mergeSort_perm _ _).mem_iff, Finset.mem_toList]
  have hlnd : l.Nodup := (List.mergeSort_perm _ _).nodup_iff.2 (Finset.nodup_toList V)
  have hlsort : l.Pairwise (fun x y => φ x < φ y) := by
    have hp := List.pairwise_mergeSort (le := fun x y => decide (φ x ≤ φ y))
      (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; linarith)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; exact le_total _ _) V.toList
    refine (hp.and hlnd).imp_of_mem fun {x y} hx hy hxy => ?_
    simp only [decide_eq_true_eq] at hxy
    rcases hxy.1.lt_or_eq with h1 | h1
    · exact h1
    · exfalso
      have hx' := (hlmem x).1 hx
      have hy' := (hlmem y).1 hy
      apply hxy.2
      apply hinj x hx' y hy'
      have hl1 := cr_lagrange e (x - o) (y - o)
      have hφx : φ x = -(conj e * (x - o)).re / ccr e (x - o) := rfl
      have hφy : φ y = -(conj e * (y - o)).re / ccr e (y - o) := rfl
      rw [hφx, hφy, div_eq_div_iff ((hV x).1 hx').2.2.ne' ((hV y).1 hy').2.2.ne'] at h1
      have he0 : 0 < normSq e := by
        rw [normSq_pos]; rintro h0; rw [h0] at hbp; simp [cr_eq] at hbp
      have : normSq e * ccr (x - o) (y - o) = 0 := by rw [hl1]; linarith
      exact (mul_eq_zero.1 this).resolve_left he0.ne'
  have hlne : l ≠ [] := fun h0 => by
    have := (hlmem b).2 hbV
    rw [h0] at this; simp at this
  -- the chain relation
  set Rel : ℂ → ℂ → Prop := fun g g' => IsHV Y g ∧ IsHV Y g' ∧ 0 < ccr (g - o) (g' - o) ∧
    ∀ v ∈ Y, IsHV Y v → ¬ (0 < ccr (g - o) (v - o) ∧ 0 < ccr (v - o) (g' - o)) with hRel
  have hVpos : ∀ x ∈ V, 0 < ccr e (x - o) := fun x hx => ((hV x).1 hx).2.2
  have hVhv : ∀ x ∈ V, IsHV Y x := fun x hx => ((hV x).1 hx).2.1
  have hchl : l.IsChain Rel := by
    refine (isChain_and_mem (isChain_gap φ l hlsort)).imp fun x y hxy => ?_
    obtain ⟨⟨hlt, hgap⟩, hx, hy⟩ := hxy
    have hx' := (hlmem x).1 hx
    have hy' := (hlmem y).1 hy
    have hcxy := (hφlt x hx' y hy').1 hlt
    refine ⟨hVhv x hx', hVhv y hy', hcxy, fun v hvY hv ⟨h1, h2⟩ => ?_⟩
    have hvV : v ∈ V := (hV v).2 ⟨hvY, hv, cone_pos (hVpos x hx') (hVpos y hy') hcxy h1 h2⟩
    have := hgap v ((hlmem v).2 hvV)
    have c1 := (hφlt x hx' v hvV).2 h1
    have c2 := (hφlt v hvV y hy').2 h2
    rcases this with h | h <;> linarith
  obtain ⟨hd, t, hlht⟩ := List.exists_cons_of_ne_nil hlne
  have hfirst : Rel a2 hd := by
    have hdl : hd ∈ l := by rw [hlht]; simp
    have hd' := (hlmem hd).1 hdl
    refine ⟨ha2, hVhv hd hd', hVpos hd hd', fun v hvY hv ⟨h1, h2⟩ => ?_⟩
    have hvV : v ∈ V := (hV v).2 ⟨hvY, hv, h1⟩
    have hvl := (hlmem v).2 hvV
    rw [hlht] at hvl
    rcases List.mem_cons.1 hvl with rfl | hvt
    · rw [cr_self'] at h2; exact lt_irrefl _ h2
    · have hs' := hlsort
      rw [hlht] at hs'
      have c1 := (List.pairwise_cons.1 hs').1 v hvt
      have c2 := (hφlt v hvV hd hd').2 h2
      linarith
  have hpos1 : ∀ z, 0 < ccr e (z - o) ↔ 0 < ccr (z - o) (a1 - o) := by
    intro z
    have hz := hcra1 (z - o)
    constructor
    · intro h
      have : 0 < α * ccr (z - o) (a1 - o) := by rw [hz]; positivity
      exact pos_of_mul_pos_right this hα.le
    · intro h
      have : 0 < β * ccr e (z - o) := by rw [← hz]; positivity
      exact pos_of_mul_pos_right this hβ.le
  have hlast : Rel (l.getLast hlne) a1 := by
    have hltl : l.getLast hlne ∈ l := List.getLast_mem hlne
    have hlt' := (hlmem _).1 hltl
    refine ⟨hVhv _ hlt', ha1, (hpos1 _).1 (hVpos _ hlt'), fun v hvY hv ⟨h1, h2⟩ => ?_⟩
    have hvV : v ∈ V := (hV v).2 ⟨hvY, hv, (hpos1 v).2 h2⟩
    have hvl := (hlmem v).2 hvV
    have hsplit := List.dropLast_append_getLast hlne
    have hs' := hlsort
    rw [← hsplit] at hvl hs'
    rcases List.mem_append.1 hvl with hvd | hvd
    · have c1 := (List.pairwise_append.1 hs').2.2 v hvd (l.getLast hlne) (by simp)
      have c2 := (hφlt _ hlt' v hvV).2 h1
      linarith
    · simp only [List.mem_singleton] at hvd
      rw [hvd, cr_self'] at h1; exact lt_irrefl _ h1
  have hchA : (a2 :: (l ++ [a1])).IsChain Rel := by
    rw [← List.cons_append, List.isChain_append]
    refine ⟨?_, List.isChain_singleton _, ?_⟩
    · rw [List.isChain_cons]
      refine ⟨fun y hy => ?_, hchl⟩
      rw [hlht] at hy
      simp only [List.head?_cons, Option.mem_some_iff] at hy
      exact hy ▸ hfirst
    · intro x hx y hy
      rw [List.getLast?_eq_some_getLast (by simp), List.getLast_cons hlne,
        Option.mem_some_iff] at hx
      simp only [List.head?_cons, Option.mem_some_iff] at hy
      rw [← hx, ← hy]; exact hlast
  have hA0mem : ∀ g ∈ a2 :: (l ++ [a1]), g = a1 ∨ g = a2 ∨ g ∈ V := by
    intro g hg
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hg
    rcases hg with hg | hg | hg
    · exact Or.inr (Or.inl hg)
    · exact Or.inr (Or.inr ((hlmem g).1 hg))
    · exact Or.inl hg
  have hndA : (a2 :: (l ++ [a1])).Nodup := by
    rw [List.nodup_cons, List.nodup_append]
    refine ⟨?_, hlnd, List.nodup_singleton _, ?_⟩
    · intro hm
      rcases List.mem_append.1 hm with hm | hm
      · have := hVpos a2 ((hlmem a2).1 hm); rw [hea2] at this; exact lt_irrefl _ this
      · simp only [List.mem_singleton] at hm; exact ha12 hm.symm
    · intro x hx y hy hxy
      simp only [List.mem_singleton] at hy
      rw [hxy, hy] at hx
      have := hVpos a1 ((hlmem a1).1 hx); rw [hea1] at this; exact lt_irrefl _ this
  obtain ⟨s, t', hst⟩ := List.append_of_mem ((hlmem b).2 hbV)
  have hne' : t' ++ [a1] ≠ [] := by simp
  obtain ⟨h, L2', hL2⟩ := List.exists_cons_of_ne_nil hne'
  have hA0 : (a2 :: (s ++ [b])) ++ (h :: L2') = a2 :: (l ++ [a1]) := by
    rw [← hL2, hst]; simp
  have hbh : Rel b h := by
    have := hchA
    rw [← hA0, List.isChain_append] at this
    refine this.2.2 b ?_ h (by simp)
    rw [← List.cons_append, List.getLast?_append_of_ne_nil _ (by simp)]; simp
  have hsbh := support_of_no_between hoH hbh.1 hbh.2.1 hbh.2.2.1 hbh.2.2.2
  refine ⟨h, s ++ [b], L2', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hA0]
    intro z hz
    rcases hA0mem z hz with rfl | rfl | hz
    exacts [ha1.mem, ha2.mem, ((hV z).1 hz).1]
  · rw [hA0]; exact hndA
  · simp
  · have h1 : (h :: L2').getLast? = some a1 := by rw [← hL2]; simp
    rw [List.getLast?_eq_some_getLast (by simp)] at h1
    exact Option.some_injective _ h1
  · rw [hA0]
    exact hchA.imp fun {g g'} hr => support_of_no_between hoH hr.1 hr.2.1 hr.2.2.1 hr.2.2.2
  · intro g hg hgb hgh
    rw [hA0] at hg
    have hgHV : IsHV Y g := by
      rcases hA0mem g hg with rfl | rfl | hg
      exacts [ha1, ha2, hVhv g hg]
    rcases (hsbh.1 g hgHV.mem).lt_or_eq with h1 | h1
    · exact h1
    · exfalso
      rcases eq_of_collinear_extreme hbh.1 hbh.2.1 hgHV hsbh.2 h1.symm with h2 | h2
      exacts [hgb h2, hgh h2]
  · rw [hA0]
    intro g hg
    rcases hA0mem g hg with rfl | rfl | hg
    exacts [Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr (hVpos g hg))]

lemma cr_chord {a1 a2 o : ℂ} (ho : o ∈ openSegment ℝ a1 a2) : ccr (a2 - o) (a1 - o) = 0 := by
  obtain ⟨α, β, -, -, hαβ, hoe⟩ := ho
  rw [← hoe, Complex.real_smul, Complex.real_smul]
  have hb : β = 1 - α := by linarith
  subst hb
  simp only [cr_eq, sub_re, sub_im, add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im]
  ring

/-- **Unit paths joining alternating hull vertices meet.**  In a separated finite set `Y ⊆ ℂ`,
let `a₁, a₂` be hull vertices, `o` a point of the open chord `a₁ a₂`, and `b, b'` hull vertices
strictly on opposite sides of the line `a₁ a₂`.  Then a unit-step path from `a₁` to `a₂` and a
unit-step path from `b` to `b'` in `Y` share a vertex. -/
theorem unit_paths_meet (Y : Finset ℂ) (hsep : ∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → 1 ≤ dist x y)
    {a1 a2 b b' o : ℂ} (ha1 : IsHV Y a1) (ha2 : IsHV Y a2) (hb : IsHV Y b) (hb'h : IsHV Y b')
    (ho : o ∈ openSegment ℝ a1 a2)
    (hbp : 0 < ccr (a2 - o) (b - o)) (hb'n : ccr (a2 - o) (b' - o) < 0)
    {P' Q' : List ℂ} (hPY : ∀ z ∈ a1 :: P', z ∈ Y) (hPl : (a1 :: P').getLast (by simp) = a2)
    (hQY : ∀ z ∈ b :: Q', z ∈ Y) (hQl : (b :: Q').getLast (by simp) = b')
    (hPc : (a1 :: P').IsChain (fun x y => dist x y = 1))
    (hQc : (b :: Q').IsChain (fun x y => dist x y = 1))
    (hdisj : ∀ x ∈ a1 :: P', ∀ y ∈ b :: Q', x ≠ y) : False := by
  obtain ⟨h, L1', L2', hAY, hnd, hL1, hL2, hchain, hstrict, hside⟩ :=
    exists_arc Y ha1 ha2 hb ho hbp
  obtain ⟨u1, hu1⟩ := exposed_of_extreme ha1
  obtain ⟨u2, hu2⟩ := exposed_of_extreme ha2
  obtain ⟨w', hw'⟩ := exposed_of_extreme hb'h
  have hchord := cr_chord ho
  refine paths_cross Y hPY hPl hQY hQl ?_ hAY hnd hL1 hL2 hchain hstrict hu1 hu2 hw' ho ?_
  · have hP' : P' ≠ [] := by
      rintro rfl
      simp only [List.getLast_singleton] at hPl
      subst hPl
      rw [openSegment_same, mem_singleton_iff] at ho
      subst ho
      rw [sub_self] at hbp; simp [cr_eq] at hbp
    have hQ' : Q' ≠ [] := by
      rintro rfl
      simp only [List.getLast_singleton] at hQl
      subst hQl
      linarith
    rw [Set.disjoint_left]
    intro z hzP hzQ
    rcases mem_polyline_of_chain _ _ (isChain_and_mem hPc) z hzP with
      ⟨hn, -⟩ | ⟨x, y, ⟨hxy, hx, hy⟩, hz1⟩
    · exact hP' hn
    rcases mem_polyline_of_chain _ _ (isChain_and_mem hQc) z hzQ with
      ⟨hn, -⟩ | ⟨x', y', ⟨hxy', hx', hy'⟩, hz2⟩
    · exact hQ' hn
    exact seg_inter_disjoint hsep (hPY x hx) (hPY y hy) (hQY x' hx') (hQY y' hy') hxy hxy'
      (hdisj x hx x' hx') (hdisj x hx y' hy') (hdisj y hy x' hx') (hdisj y hy y' hy') hz1 hz2
  · intro hm
    rcases hside b' hm with h1 | h1 | h1
    · rw [h1, hchord] at hb'n; exact lt_irrefl _ hb'n
    · rw [h1, cr_self'] at hb'n; exact lt_irrefl _ hb'n
    · linarith

end Erdos99
end

end Arc

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `ContactRelease`
-/

section ContactRelease

/-!
# Release sets for a disconnected contact relation

The planar combinatorics behind the connectivity of the contact graph (Lemma 2.1), stated in `ℂ`
for an abstract equivalence relation `R` on a separated finite set `Y` whose classes are joined by
unit-step paths (the contact components).  If `R` has at least two classes, there is a nonempty
proper `R`-closed subset `S ⊆ Y` and a direction `c ≠ 0` such that `p - q` has negative component
along `c` for every pair of hull vertices `p ∈ S`, `q ∉ S` (`exists_release_C`).

Translating `S` along `c` then strictly shortens every diameter crossing between `S` and its
complement, which contradicts finite multiplicity.
-/

open scoped Real ComplexConjugate
open Complex Set Metric EstablishedExternalResults

@[expose] public noncomputable section

namespace Erdos99

lemma not_extreme_comb' {K : Set ℂ} (hK : Convex ℝ K) {x p q r : ℂ} (hp : p ∈ K) (hq : q ∈ K)
    (hr : r ∈ K) {a b c : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hbc : 0 < b + c)
    (habc : a + b + c = 1) (hx : x = (a : ℂ) * p + (b : ℂ) * q + (c : ℂ) * r) (hpx : p ≠ x) :
    x ∉ extremePoints ℝ K := by
  rcases hb.lt_or_eq with hb | hb
  · exact not_extreme_comb hK hp hq hr ha hb hc habc hx hpx
  · subst hb
    refine not_extreme_comb hK hp hr hq ha (by linarith) le_rfl (by linarith) ?_ hpx
    rw [hx]; push_cast; ring

/-- **Release sets.**  See the module docstring. -/
theorem exists_release_C (Y : Finset ℂ) (hsep : ∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → 1 ≤ dist x y)
    (R : ℂ → ℂ → Prop) (hRr : ∀ x, R x x) (hRs : ∀ x y, R x y → R y x)
    (hRt : ∀ x y z, R x y → R y z → R x z)
    (hpath : ∀ x ∈ Y, ∀ y ∈ Y, R x y → ∃ P' : List ℂ, (∀ z ∈ x :: P', z ∈ Y ∧ R x z) ∧
      (x :: P').getLast (by simp) = y ∧ (x :: P').IsChain (fun a b => dist a b = 1))
    (hdis : ∃ x ∈ Y, ∃ y ∈ Y, ¬ R x y) :
    ∃ S : Finset ℂ, S ⊆ Y ∧ (∀ p ∈ S, ∀ q ∈ Y, R p q → q ∈ S) ∧ S.Nonempty ∧
      (∃ q ∈ Y, q ∉ S) ∧ ∃ c : ℂ, c ≠ 0 ∧
        ∀ p ∈ S, ∀ q ∈ Y, q ∉ S → IsHV Y p → IsHV Y q → (conj (p - q) * c).re < 0 := by
  classical
  obtain ⟨x, hx, y, hy, hxy⟩ := hdis
  by_cases hI : ∃ x0 ∈ Y, ∀ p ∈ Y, ∀ p' ∈ Y, R x0 p → R x0 p' → IsHV Y p → IsHV Y p' → p = p'
  · -- a component with at most one hull vertex
    obtain ⟨x0, hx0, huniq⟩ := hI
    have hmiss : ∃ q ∈ Y, ¬ R x0 q := by
      by_cases h1 : R x0 x
      · exact ⟨y, hy, fun h2 => hxy (hRt _ _ _ (hRs _ _ h1) h2)⟩
      · exact ⟨x, hx, h1⟩
    obtain ⟨q0, hq0, hq0n⟩ := hmiss
    have hS : ∀ z, z ∈ Y.filter (R x0) ↔ z ∈ Y ∧ R x0 z := fun z => Finset.mem_filter
    refine ⟨Y.filter (R x0), Finset.filter_subset _ _, fun p hp q hq hpq =>
      (hS q).2 ⟨hq, hRt _ _ _ ((hS p).1 hp).2 hpq⟩, ⟨x0, (hS x0).2 ⟨hx0, hRr x0⟩⟩,
      ⟨q0, hq0, fun h => hq0n ((hS q0).1 h).2⟩, ?_⟩
    by_cases hT : ∃ t ∈ Y.filter (R x0), IsHV Y t
    · obtain ⟨t, htS, htH⟩ := hT
      obtain ⟨u, hu⟩ := exposed_of_extreme htH
      have hq0t : q0 ≠ t := fun h => hq0n (h ▸ ((hS t).1 htS).2)
      refine ⟨-u, fun hu0 => ?_, fun p hp q hq hqS hpH hqH => ?_⟩
      · rw [neg_eq_zero] at hu0
        have := hu q0 hq0 hq0t
        rw [hu0] at this; simp at this
      · have hpt : p = t := huniq p ((hS p).1 hp).1 t ((hS t).1 htS).1 ((hS p).1 hp).2
          ((hS t).1 htS).2 hpH htH
        subst hpt
        have := hu q hq (fun h => hqS (h ▸ hp))
        have e : (conj (p - q) * -u).re = (conj u * (q - p)).re := by
          simp only [mul_re, conj_re, conj_im, neg_re, neg_im, sub_re, sub_im]; ring
        rw [e]; exact this
    · push_neg at hT
      exact ⟨1, one_ne_zero, fun p hp q hq hqS hpH hqH => absurd hpH (hT p hp)⟩
  push_neg at hI
  -- every component has two hull vertices; `t` is a hull vertex outside the component of `x`
  obtain ⟨t, htY, -, -, hyt, -, htH, -, -⟩ := hI y hy
  have hxt : ¬ R x t := fun h => hxy (hRt _ _ _ h (hRs _ _ hyt))
  obtain ⟨u, hu⟩ := exposed_of_extreme htH
  set e := I * u with he
  have hepos : ∀ z ∈ Y, z ≠ t → 0 < ccr e (z - t) := by
    intro z hz hzt
    have := hu z hz hzt
    have e1 : ccr e (z - t) = -(conj u * (z - t)).re := by
      rw [he]; simp only [cr_eq, mul_re, mul_im, I_re, I_im, conj_re, conj_im, sub_re, sub_im]
      ring
    rw [e1]; linarith
  set ψ : ℂ → ℝ := fun z => -(conj e * (z - t)).re / ccr e (z - t) with hψdef
  set K := Y.filter (fun z => R x z ∧ IsHV Y z) with hKdef
  have hK : ∀ z, z ∈ K ↔ z ∈ Y ∧ R x z ∧ IsHV Y z := fun z => by rw [hKdef, Finset.mem_filter]
  have hKt : ∀ z ∈ K, z ≠ t := fun z hz h => hxt (h ▸ ((hK z).1 hz).2.1)
  have hKpos : ∀ z ∈ K, 0 < ccr e (z - t) := fun z hz => hepos z ((hK z).1 hz).1 (hKt z hz)
  obtain ⟨p1, hp1Y, p2, hp2Y, hxp1, hxp2, hp1H, hp2H, hp12⟩ := hI x hx
  have hp1K : p1 ∈ K := (hK p1).2 ⟨hp1Y, hxp1, hp1H⟩
  have hp2K : p2 ∈ K := (hK p2).2 ⟨hp2Y, hxp2, hp2H⟩
  obtain ⟨a1, ha1K, hmax⟩ := K.exists_max_image ψ ⟨p1, hp1K⟩
  obtain ⟨a2, ha2K, hmin⟩ := K.exists_min_image ψ ⟨p1, hp1K⟩
  have hψ : ∀ z ∈ K, ∀ w ∈ K, ψ z < ψ w ↔ 0 < ccr (z - t) (w - t) := fun z hz w hw =>
    phi_lt_iff (hKpos z hz) (hKpos w hw)
  have htH' : t ∈ convexHull ℝ (Y : Set ℂ) := htH.1
  obtain ⟨ha1Y, ha1R, ha1H⟩ := (hK a1).1 ha1K
  obtain ⟨ha2Y, ha2R, ha2H⟩ := (hK a2).1 ha2K
  have hc0 : 0 < ccr (a2 - t) (a1 - t) := by
    rcases (hmin a1 ha1K).lt_or_eq with h | h
    · exact (hψ a2 ha2K a1 ha1K).1 h
    · exfalso
      have e1 : ψ p1 = ψ p2 := by
        have := hmax p1 hp1K; have := hmin p1 hp1K
        have := hmax p2 hp2K; have := hmin p2 hp2K
        linarith
      have h1 : ¬ 0 < ccr (p1 - t) (p2 - t) := fun h' => by
        have := (hψ p1 hp1K p2 hp2K).2 h'; linarith
      have h2 : ¬ 0 < ccr (p2 - t) (p1 - t) := fun h' => by
        have := (hψ p2 hp2K p1 hp1K).2 h'; linarith
      rw [cr_swap] at h2
      have h0 : ccr (p1 - t) (p2 - t) = 0 := by linarith [not_lt.1 h1, not_lt.1 h2]
      exact hp12 (eq_of_same_ray_extreme htH' hp1H hp2H (hKpos p1 hp1K) (hKpos p2 hp2K) h0)
  have ha12 : a1 ≠ a2 := by
    rintro h; rw [h, cr_swap] at hc0
    have : ccr (a2 - t) (a2 - t) = 0 := cr_self' _
    linarith
  -- the component of `x` lies weakly beyond the line `a₂ a₁`, seen from `t`
  set σ : ℂ → ℝ := fun z => ccr (a1 - a2) (z - a2) with hσdef
  have hσt : σ t = ccr (a2 - t) (a1 - t) := by
    rw [hσdef]; simp only [cr_eq, sub_re, sub_im]; ring
  have hfar : ∀ z ∈ K, σ z ≤ 0 := by
    intro z hz
    by_contra hpos
    push_neg at hpos
    obtain ⟨hzY, -, hzH⟩ := (hK z).1 hz
    set c0 := ccr (a2 - t) (a1 - t) with hc0def
    set A := ccr (z - t) (a1 - t) with hA
    set B := ccr (a2 - t) (z - t) with hB
    have hA0 : 0 ≤ A := by
      by_contra h; push_neg at h
      have : 0 < ccr (a1 - t) (z - t) := by rw [cr_swap]; linarith
      have := (hψ a1 ha1K z hz).2 this
      linarith [hmax z hz]
    have hB0 : 0 ≤ B := by
      by_contra h; push_neg at h
      have : 0 < ccr (z - t) (a2 - t) := by rw [cr_swap]; linarith
      have := (hψ z hz a2 ha2K).2 this
      linarith [hmin z hz]
    have hσz : σ z = c0 - A - B := by
      rw [hσdef, hc0def, hA, hB]; simp only [cr_eq, sub_re, sub_im]; ring
    have hcr := cramer (a2 - t) (a1 - t) (z - t)
    rw [← hc0def, ← hA, ← hB] at hcr
    have hAB : 0 < A + B := by
      rcases (add_nonneg hA0 hB0).lt_or_eq with h | h
      · exact h
      · exfalso
        have hA' : A = 0 := by linarith
        have hB' : B = 0 := by linarith
        rw [hA', hB'] at hcr
        push_cast at hcr
        have : (c0 : ℂ) * (z - t) = 0 := by rw [hcr]; ring
        rcases mul_eq_zero.1 this with h1 | h1
        · exact hc0.ne' (by exact_mod_cast h1)
        · exact hKt z hz (sub_eq_zero.1 h1)
    have hc0' : (c0 : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
    refine not_extreme_comb' (convex_convexHull ℝ (Y : Set ℂ)) htH' ha2H.1 ha1H.1
      (a := 1 - (A + B) / c0) (b := A / c0) (c := B / c0)
      (by rw [sub_pos, div_lt_one hc0]; linarith) (div_nonneg hA0 hc0.le)
      (div_nonneg hB0 hc0.le) (by rw [← add_div]; exact div_pos hAB hc0) (by ring) ?_
      (fun h => hKt z hz h.symm) hzH
    calc z = (c0 : ℂ)⁻¹ * ((c0 : ℂ) * (z - t)) + t := by field_simp; ring
      _ = _ := by rw [hcr]; push_cast; field_simp; ring
  -- the release set: components meeting the open side of `t`
  set o := (a1 + a2) / 2 with ho
  have hoseg : o ∈ openSegment ℝ a2 a1 :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by
      rw [ho, Complex.real_smul, Complex.real_smul]; push_cast; ring⟩
  have hside : ∀ z, ccr (a1 - o) (z - o) = σ z / 2 := by
    intro z; rw [ho, hσdef]
    simp only [cr_eq, sub_re, sub_im, add_re, add_im, div_ofNat_re, div_ofNat_im]; ring
  have hnotS : ∀ w ∈ Y, IsHV Y w → 0 < σ w → ¬ R x w := fun w hwY hwH hwσ hRw => by
    have := hfar w ((hK w).2 ⟨hwY, hRw, hwH⟩); linarith
  set S := Y.filter (fun z => ∃ w ∈ Y, IsHV Y w ∧ 0 < σ w ∧ R w z) with hSdef
  have hS : ∀ z, z ∈ S ↔ z ∈ Y ∧ ∃ w ∈ Y, IsHV Y w ∧ 0 < σ w ∧ R w z := fun z => by
    rw [hSdef, Finset.mem_filter]
  refine ⟨S, Finset.filter_subset _ _, fun p hp q hq hpq => ?_, ⟨t, (hS t).2 ⟨htY, t, htY, htH,
    hσt ▸ hc0, hRr t⟩⟩, ⟨a1, ha1Y, fun h => ?_⟩, -(I * (a1 - a2)), ?_, ?_⟩
  · obtain ⟨-, w, hwY, hwH, hwσ, hRw⟩ := (hS p).1 hp
    exact (hS q).2 ⟨hq, w, hwY, hwH, hwσ, hRt _ _ _ hRw hpq⟩
  · obtain ⟨-, w, hwY, hwH, hwσ, hRw⟩ := (hS a1).1 h
    exact hnotS w hwY hwH hwσ (hRt _ _ _ ha1R (hRs _ _ hRw))
  · intro h0
    rw [neg_eq_zero, mul_eq_zero] at h0
    rcases h0 with h0 | h0
    · exact I_ne_zero h0
    · exact ha12 (sub_eq_zero.1 h0)
  · intro p hp q hq hqS hpH hqH
    have hσq : σ q ≤ 0 := by
      by_contra h; push_neg at h
      exact hqS ((hS q).2 ⟨hq, q, hq, hqH, h, hRr q⟩)
    obtain ⟨hpY, w, hwY, hwH, hwσ, hRwp⟩ := (hS p).1 hp
    have hσp : 0 < σ p := by
      by_contra hle
      push_neg at hle
      rcases hle.lt_or_eq with hlt | heq
      · obtain ⟨P', hPmem, hPl, hPc⟩ := hpath a2 ha2Y a1 ha1Y (hRt _ _ _ (hRs _ _ ha2R) ha1R)
        obtain ⟨Q', hQmem, hQl, hQc⟩ := hpath w hwY p hpY hRwp
        refine unit_paths_meet Y hsep ha2H ha1H hwH hpH hoseg (by rw [hside]; linarith)
          (by rw [hside]; linarith) (fun z hz => (hPmem z hz).1) hPl
          (fun z hz => (hQmem z hz).1) hQl hPc hQc ?_
        intro z hz z' hz' hzz
        apply hnotS w hwY hwH hwσ
        have h1 := (hPmem z hz).2
        have h2 := (hQmem z' hz').2
        rw [← hzz] at h2
        exact hRt _ _ _ ha2R (hRt _ _ _ h1 (hRs _ _ h2))
      · have hκ : 0 < ccr (a1 - a2) (t - a2) := by
          have := hc0; rw [← hσt] at this; exact this
        rcases eq_of_collinear_extreme ha2H ha1H hpH hκ heq with h | h
        · exact hnotS w hwY hwH hwσ (hRt _ _ _ ha2R (h ▸ hRs _ _ hRwp))
        · exact hnotS w hwY hwH hwσ (hRt _ _ _ ha1R (h ▸ hRs _ _ hRwp))
    have e1 : (conj (p - q) * -(I * (a1 - a2))).re = -(σ p - σ q) := by
      rw [hσdef]
      simp only [cr_eq, mul_re, mul_im, neg_re, neg_im, I_re, I_im, conj_re, conj_im, sub_re,
        sub_im]
      ring
    rw [e1]; linarith

end Erdos99
end

end ContactRelease

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `RotationRelease`
-/

section RotationRelease

/-!
# Strict first-order releases and rotations of a shore

The release step at the end of Lemma 3.4: a velocity which does not shorten unit pairs, strictly
shortens every diameter pair that it moves, and is not constant, produces (by moving along it for a
short positive time) a one-parameter family of optimal configurations with pairwise different
values of `∑ |p - q|²`.  Under finite multiplicity this is impossible (`false_of_release`).

The special case used in Lemma 3.4 rotates a subset `S` (a "shore") about a point `a`, fixing the
complement.
-/

open scoped BigOperators Real

@[expose] public noncomputable section

open Classical

namespace Erdos99

/-- A uniform negative gap for a real function on a finite set. -/
lemma exists_uniform_neg {α : Type*} (s : Finset α) (g : α → ℝ) :
    ∃ β > 0, ∀ x ∈ s, g x < 0 → g x ≤ -β := by
  by_cases h : (s.filter (fun x => g x < 0)).Nonempty
  · obtain ⟨x0, hx0, hmax⟩ := (s.filter (fun x => g x < 0)).exists_max_image g h
    rw [Finset.mem_filter] at hx0
    refine ⟨-g x0, by linarith [hx0.2], fun x hx hgx => ?_⟩
    have := hmax x (Finset.mem_filter.2 ⟨hx, hgx⟩)
    linarith
  · exact ⟨1, one_pos, fun x hx hgx => absurd ⟨x, Finset.mem_filter.2 ⟨hx, hgx⟩⟩ h⟩

/-- **Strict first-order release.**  Under finite multiplicity, there is no non-constant velocity
on an optimal set which does not shorten unit pairs and which strictly shortens (to first order)
every diameter pair whose endpoints it moves differently. -/
theorem false_of_strict_velocity {n : ℕ} (hn : 2 ≤ n) (hfm : numOptimalClasses n < ⊤)
    {X : Finset Plane} (hX : IsOptimal n X) (v : Plane → Plane)
    (hunit : ∀ p ∈ X, ∀ q ∈ X, dist p q = 1 → 0 ≤ inner ℝ (p - q) (v p - v q))
    (hdiam : ∀ p ∈ X, ∀ q ∈ X, dist p q = diam X →
      v p = v q ∨ inner ℝ (p - q) (v p - v q) < 0)
    (hnc : ∃ p ∈ X, ∃ q ∈ X, v p ≠ v q) : False := by
  obtain ⟨p0, hp0, q0, hq0, hpq0⟩ := hnc
  set D := diam X
  have hD : 0 < D := hX.diam_pos hn
  set M := ∑ r ∈ X, ‖v r‖
  have hM : ∀ r ∈ X, ‖v r‖ ≤ M := fun r hr =>
    Finset.single_le_sum (f := fun r => ‖v r‖) (fun _ _ => norm_nonneg _) hr
  have hMpos : 0 < M := by
    by_contra hle
    push_neg at hle
    have h1 : v p0 = 0 := norm_eq_zero.1 (le_antisymm ((hM p0 hp0).trans hle) (norm_nonneg _))
    have h2 : v q0 = 0 := norm_eq_zero.1 (le_antisymm ((hM q0 hq0).trans hle) (norm_nonneg _))
    exact hpq0 (h1.trans h2.symm)
  obtain ⟨γ1, hγ1, hg1⟩ := exists_gap X 1
  obtain ⟨γ2, hγ2, hg2⟩ := exists_gap X D
  obtain ⟨β, hβ, hgβ⟩ := exists_uniform_neg (X ×ˢ X)
    (fun pq => inner ℝ (pq.1 - pq.2) (v pq.1 - v pq.2))
  set γ := min γ1 γ2
  have hγ : 0 < γ := lt_min hγ1 hγ2
  set δ1 := min (γ / (2 * M)) (β / (2 * M ^ 2))
  have hδ1 : 0 < δ1 := lt_min (div_pos hγ (by linarith)) (div_pos hβ (mul_pos two_pos (pow_pos hMpos 2)))
  let f : ℝ → Plane → Plane := fun t p => p + t • v p
  have hclose : ∀ t ∈ Set.Ioo 0 δ1, ∀ p ∈ X, ∀ q ∈ X,
      |dist (f t p) (f t q) - dist p q| < γ := fun t ht p hp q hq => by
    have h1 := dist_move_le p q (v p) (v q) t ht.1.le
    have h2 : t * (‖v p‖ + ‖v q‖) ≤ t * (2 * M) := by
      apply mul_le_mul_of_nonneg_left _ ht.1.le; linarith [hM p hp, hM q hq]
    have h3 : t * (2 * M) < γ := by
      have := ht.2.trans_le (min_le_left _ _); rw [lt_div_iff₀ (by linarith)] at this; linarith
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
    · rcases hdiam p hp q hq h2 with he | hlt
      · have e := dist_move_sq p q (v p) (v q) t
        have : dist (f t p) (f t q) = dist p q := by
          simp only [f, he, dist_eq_norm]; congr 1; abel
        rw [this, h2]
      · have hB := hgβ (p, q) (Finset.mem_product.2 ⟨hp, hq⟩) hlt
        simp only at hB
        have e := dist_move_sq p q (v p) (v q) t
        have hn2 : ‖v p - v q‖ ≤ 2 * M := by
          have := norm_sub_le (v p) (v q); linarith [hM p hp, hM q hq]
        have hn2' : ‖v p - v q‖ ^ 2 ≤ 4 * M ^ 2 := by
          nlinarith [norm_nonneg (v p - v q)]
        have ht2 : t ≤ β / (2 * M ^ 2) := (ht.2.trans_le (min_le_right _ _)).le
        rw [le_div_iff₀ (mul_pos two_pos (pow_pos hMpos 2))] at ht2
        have hsq : dist (f t p) (f t q) ^ 2 ≤ D ^ 2 := by
          simp only [f]; rw [e, h2]
          have h0 := ht.1
          have : t ^ 2 * ‖v p - v q‖ ^ 2 ≤ t ^ 2 * (4 * M ^ 2) :=
            mul_le_mul_of_nonneg_left hn2' (by positivity)
          nlinarith
        nlinarith [dist_nonneg (x := f t p) (y := f t q)]
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
    have h1 : ‖v p0 - v q0‖ ^ 2 ≤ ∑ q ∈ X, ‖v p0 - v q‖ ^ 2 :=
      Finset.single_le_sum (f := fun q => ‖v p0 - v q‖ ^ 2) (fun _ _ => sq_nonneg _) hq0
    have h2 : ∑ q ∈ X, ‖v p0 - v q‖ ^ 2 ≤ C :=
      Finset.single_le_sum (f := fun p => ∑ q ∈ X, ‖v p - v q‖ ^ 2)
        (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) hp0
    have h3 : 0 < ‖v p0 - v q0‖ ^ 2 := by
      have : v p0 - v q0 ≠ 0 := sub_ne_zero.2 hpq0
      positivity
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
    have hdiamF : diam (X.image (f t)) ≤ D := by
      apply Metric.diam_le_of_forall_dist_le hD.le
      intro x hx y hy
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx hy
      obtain ⟨p, hp, rfl⟩ := hx
      obtain ⟨q, hq, rfl⟩ := hy
      exact hupper t ht1 p hp q hq
    exact ⟨⟨hcard, hsepF⟩, fun Y hY => hdiamF.trans (hX.2 Y hY)⟩
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

lemma rot_sub (x y : Plane) : rot (x - y) = rot x - rot y := by
  rw [plane_ext_iff]; simp [rot]; ring

lemma rot_ne_zero {x : Plane} (hx : x ≠ 0) : rot x ≠ 0 := by
  intro h
  have := norm_rot x
  rw [h, norm_zero] at this
  exact hx (norm_eq_zero.1 this.symm)

/-- **Rotation of a shore.**  Let `S ⊆ X` and rotate `S` about `a` with angular velocity `ω`,
fixing `X \ S`.  If this does not shorten (to first order) any unit pair joining `S` to its
complement, strictly shortens every diameter pair joining `S` to its complement, `S` contains no
diameter pair, and some point actually moves, then finite multiplicity is contradicted. -/
theorem false_of_shore_rotation {n : ℕ} (hn : 2 ≤ n) (hfm : numOptimalClasses n < ⊤)
    {X : Finset Plane} (hX : IsOptimal n X) (S : Finset Plane) (a : Plane) (ω : ℝ)
    (hunit : ∀ p ∈ S, ∀ q ∈ X, q ∉ S → dist p q = 1 → 0 ≤ ω * inner ℝ (p - q) (rot (p - a)))
    (hdiam : ∀ p ∈ S, ∀ q ∈ X, q ∉ S → dist p q = diam X →
      ω * inner ℝ (p - q) (rot (p - a)) < 0)
    (hin : ∀ p ∈ S, ∀ q ∈ S, dist p q ≠ diam X)
    (hmov : ∃ p ∈ S, p ∈ X ∧ ω ≠ 0 ∧ p ≠ a) (hproper : ∃ q ∈ X, q ∉ S) : False := by
  let v : Plane → Plane := fun p => if p ∈ S then ω • rot (p - a) else 0
  have hin' : ∀ p ∈ S, ∀ q ∈ S, inner ℝ (p - q) (v p - v q) = 0 := by
    intro p hp q hq
    simp only [v, if_pos hp, if_pos hq, ← smul_sub, ← rot_sub,
      show p - a - (q - a) = p - q by abel, inner_smul_right, inner_rot_self, mul_zero]
  refine false_of_strict_velocity hn hfm hX v ?_ ?_ ?_
  · intro p hp q hq _
    by_cases hpS : p ∈ S <;> by_cases hqS : q ∈ S
    · exact (hin' p hpS q hqS).ge
    · have := hunit p hpS q hq hqS (by assumption)
      simp only [v, if_pos hpS, if_neg hqS, sub_zero, inner_smul_right]; exact this
    · have := hunit q hqS p hp hpS (by rw [dist_comm]; assumption)
      simp only [v, if_neg hpS, if_pos hqS, zero_sub, inner_neg_right, inner_smul_right]
      have e : inner ℝ (p - q) (rot (q - a)) = -inner ℝ (q - p) (rot (q - a)) := by
        rw [← inner_neg_left, neg_sub]
      rw [e]; linarith
    · simp [v, hpS, hqS]
  · intro p hp q hq hpq
    by_cases hpS : p ∈ S <;> by_cases hqS : q ∈ S
    · exact absurd hpq (hin p hpS q hqS)
    · right
      have := hdiam p hpS q hq hqS hpq
      simp only [v, if_pos hpS, if_neg hqS, sub_zero, inner_smul_right]; exact this
    · right
      have := hdiam q hqS p hp hpS (by rw [dist_comm]; exact hpq)
      simp only [v, if_neg hpS, if_pos hqS, zero_sub, inner_neg_right, inner_smul_right]
      have e : inner ℝ (p - q) (rot (q - a)) = -inner ℝ (q - p) (rot (q - a)) := by
        rw [← inner_neg_left, neg_sub]
      rw [e]; linarith
    · left; simp [v, hpS, hqS]
  · obtain ⟨p, hpS, hpX, hω, hpa⟩ := hmov
    obtain ⟨q, hqX, hqS⟩ := hproper
    refine ⟨p, hpX, q, hqX, ?_⟩
    simp only [v, if_pos hpS, if_neg hqS]
    exact smul_ne_zero hω (rot_ne_zero (sub_ne_zero.2 hpa))

lemma rot_comb (α β : ℝ) (ν e : Plane) :
    rot (α • ν + β • rot ν + e) = α • rot ν - β • ν + rot e := by
  rw [plane_ext_iff]; simp [rot]; constructor <;> ring

/-- **The rotation of a shore (computation).**  Suppose that all unit pairs joining `S` to its
complement are translates of one unit vector `z` (oriented into `S`), that `S` lies within
`D/100` of the boundary point `o + (D/2) ν` (`|ν| = 1`), that every diameter joining `S` to its
complement is within `D/100` of `D ν`, and that `|z · J ν| ≥ 2/5`.  Then rotating `S` about
`a = o + (D/4) ν - σ (D/16) J ν` with angular velocity `σ = sign (z · J ν)` satisfies the
hypotheses of `false_of_shore_rotation`. -/
theorem rotation_conditions_of_shore {X S : Finset Plane} {D : ℝ} (hD : 0 < D) {o ν z : Plane}
    (hν : ‖ν‖ = 1) (hz : ‖z‖ = 1) (hzτ : 2 / 5 ≤ |inner ℝ z (rot ν)|)
    (hunit : ∀ p ∈ S, ∀ q ∈ X, q ∉ S → dist p q = 1 → p - q = z)
    (hloc : ∀ p ∈ S, ‖p - (o + (D / 2) • ν)‖ ≤ D / 100)
    (hdiam : ∀ p ∈ S, ∀ q ∈ X, q ∉ S → dist p q = D → ‖(p - q) - D • ν‖ ≤ D / 100)
    (hne : S.Nonempty) :
    ∃ a : Plane, ∃ ω : ℝ,
      (∀ p ∈ S, ∀ q ∈ X, q ∉ S → dist p q = 1 → 0 ≤ ω * inner ℝ (p - q) (rot (p - a))) ∧
      (∀ p ∈ S, ∀ q ∈ X, q ∉ S → dist p q = D → ω * inner ℝ (p - q) (rot (p - a)) < 0) ∧
      (∀ p ∈ S, ∀ q ∈ S, dist p q ≠ D) ∧ (∃ p ∈ S, ω ≠ 0 ∧ p ≠ a) := by
  set τ := rot ν
  set c := o + (D / 2) • ν
  set σ : ℝ := if 0 ≤ inner ℝ z τ then 1 else -1
  have hσ : σ * inner ℝ z τ = |inner ℝ z τ| := by
    simp only [σ]; split_ifs with h
    · rw [abs_of_nonneg h, one_mul]
    · rw [abs_of_neg (not_le.1 h)]; ring
  have hσ2 : σ * σ = 1 := by simp only [σ]; split_ifs <;> norm_num
  have hσa : |σ| = 1 := by simp only [σ]; split_ifs <;> norm_num
  set a := o + (D / 4) • ν - (σ * D / 16) • τ
  have hpa : ∀ p, p - a = (D / 4) • ν + (σ * D / 16) • rot ν + (p - c) := by
    intro p; simp only [a, c, τ]; module
  have hW : ∀ p, rot (p - a) = (D / 4) • τ - (σ * D / 16) • ν + rot (p - c) := by
    intro p; rw [hpa, rot_comb]
  have hντ : inner ℝ ν τ = 0 := inner_rot_self ν
  have hνν : inner ℝ ν ν = 1 := by rw [real_inner_self_eq_norm_sq, hν]; norm_num
  have hτ : ‖τ‖ = 1 := by rw [norm_rot, hν]
  refine ⟨a, σ, ?_, ?_, ?_, ?_⟩
  · intro p hp q hq hqS h1
    rw [hunit p hp q hq hqS h1, hW, inner_add_right, inner_sub_right, inner_smul_right,
      inner_smul_right]
    have hzν : |inner ℝ z ν| ≤ 1 := by
      have := abs_real_inner_le_norm z ν; rw [hz, hν] at this; linarith
    have hze : |inner ℝ z (rot (p - c))| ≤ D / 100 := by
      have := abs_real_inner_le_norm z (rot (p - c))
      rw [hz, norm_rot, one_mul] at this; linarith [hloc p hp]
    have e1 : σ * (D / 4 * inner ℝ z τ - σ * D / 16 * inner ℝ z ν + inner ℝ z (rot (p - c))) =
        D / 4 * (σ * inner ℝ z τ) - (σ * σ) * (D / 16) * inner ℝ z ν +
          σ * inner ℝ z (rot (p - c)) := by ring
    rw [e1, hσ, hσ2]
    have h3 : |σ * inner ℝ z (rot (p - c))| ≤ D / 100 := by rw [abs_mul, hσa, one_mul]; exact hze
    have h4 := abs_le.1 h3
    have h5 := abs_le.1 hzν
    nlinarith
  · intro p hp q hq hqS h2
    have hd := hdiam p hp q hq hqS h2
    set e' := (p - q) - D • ν
    have hpq : p - q = D • ν + e' := by simp only [e']; abel
    set W := rot (p - a)
    have hWn : ‖W‖ ≤ D / 3 := by
      simp only [W]; rw [hW]
      have t1 := norm_add_le ((D / 4) • τ - (σ * D / 16) • ν) (rot (p - c))
      have t2 := norm_sub_le ((D / 4) • τ) ((σ * D / 16) • ν)
      rw [norm_smul, norm_smul, hτ, hν, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (by positivity : 0 < D / 4), abs_div, abs_mul, hσa, abs_of_pos hD] at t2
      rw [norm_rot] at t1
      have := hloc p hp
      norm_num at t2
      linarith
    have hνW : inner ℝ ν W = -(σ * D / 16) + inner ℝ ν (rot (p - c)) := by
      simp only [W]; rw [hW, inner_add_right, inner_sub_right, inner_smul_right,
        inner_smul_right, hντ, hνν]; ring
    have hνe : |inner ℝ ν (rot (p - c))| ≤ D / 100 := by
      have := abs_real_inner_le_norm ν (rot (p - c))
      rw [hν, norm_rot, one_mul] at this; linarith [hloc p hp]
    have heW : |inner ℝ e' W| ≤ D / 100 * (D / 3) := by
      refine (abs_real_inner_le_norm e' W).trans ?_
      exact mul_le_mul hd hWn (norm_nonneg _) (by positivity)
    rw [hpq, inner_add_left, inner_smul_left, hνW]
    simp only [RCLike.conj_to_real]
    have e1 : σ * (D * (-(σ * D / 16) + inner ℝ ν (rot (p - c))) + inner ℝ e' W) =
        -(σ * σ) * D ^ 2 / 16 + D * (σ * inner ℝ ν (rot (p - c))) + σ * inner ℝ e' W := by ring
    rw [e1, hσ2]
    have h3 : |σ * inner ℝ ν (rot (p - c))| ≤ D / 100 := by rw [abs_mul, hσa, one_mul]; exact hνe
    have h4 : |σ * inner ℝ e' W| ≤ D / 100 * (D / 3) := by rw [abs_mul, hσa, one_mul]; exact heW
    have h5 := abs_le.1 h3
    have h6 := abs_le.1 h4
    have h7 : D * (σ * inner ℝ ν (rot (p - c))) ≤ D * (D / 100) :=
      mul_le_mul_of_nonneg_left h5.2 hD.le
    nlinarith
  · intro p hp q hq hpq
    have h1 := hloc p hp
    have h2 := hloc q hq
    have h3 : dist p c = ‖p - c‖ := dist_eq_norm _ _
    have h4 : dist c q = ‖q - c‖ := by rw [dist_comm]; exact dist_eq_norm _ _
    linarith [dist_triangle p c q]
  · obtain ⟨p, hp⟩ := hne
    refine ⟨p, hp, by simp only [σ]; split_ifs <;> norm_num, fun hpa' => ?_⟩
    have h1 := hloc p hp
    have h2 : inner ℝ (p - c) ν = -(D / 4) := by
      have := hpa p
      rw [show p - a = 0 from sub_eq_zero.2 hpa'] at this
      have h3 : p - c = -((D / 4) • ν + (σ * D / 16) • rot ν) := by
        rw [eq_neg_iff_add_eq_zero, add_comm]; exact this.symm
      rw [h3, inner_neg_left, inner_add_left, inner_smul_left, inner_smul_left,
        real_inner_comm ν (rot ν), inner_rot_self, hνν]
      simp
    have h4 := abs_real_inner_le_norm (p - c) ν
    rw [h2, hν, mul_one, abs_neg, abs_of_pos (by positivity)] at h4
    linarith

end Erdos99
end

end RotationRelease

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `Connected`
-/

section Connected

/-!
# Connectivity of the contact graph (Lemma 2.1)

Under finite multiplicity, the contact graph of an optimal set is connected
(`contactGraph_connected_of_optimal`).  If it were not, `exists_release_C` provides a union `S` of
contact components and a direction `c` such that translating `S` along `c` strictly shortens every
diameter between `S` and its complement, while unit contacts are preserved; this contradicts
`false_of_strict_velocity`.
-/

open scoped Real ComplexConjugate
open Complex Set Metric EstablishedExternalResults

@[expose] public noncomputable section

open Classical

namespace Erdos99

/-- Translating a contact-closed part of an optimal set, so that every diameter between the part
and its complement shortens to first order, contradicts finite multiplicity. -/
theorem false_of_closed_translation {n : ℕ} (hn : 2 ≤ n) (hfm : numOptimalClasses n < ⊤)
    {X : Finset Plane} (hX : IsOptimal n X) (S : Set Plane)
    (hclosed : ∀ p ∈ S, ∀ q ∈ X, dist p q = 1 → q ∈ S)
    (hS : ∃ p ∈ X, p ∈ S) (hSc : ∃ q ∈ X, q ∉ S) (c : Plane) (hc : c ≠ 0)
    (hdiam : ∀ p ∈ X, p ∈ S → ∀ q ∈ X, q ∉ S → dist p q = diam X → inner ℝ (p - q) c < 0) :
    False := by
  refine false_of_strict_velocity hn hfm hX (fun x => if x ∈ S then c else 0) ?_ ?_ ?_
  · intro p hp q hq hpq
    by_cases hpS : p ∈ S
    · have hqS := hclosed p hpS q hq hpq
      simp [hpS, hqS]
    · have hqS : q ∉ S := fun hqS => hpS (hclosed q hqS p hp (by rw [dist_comm]; exact hpq))
      simp [hpS, hqS]
  · intro p hp q hq hpq
    by_cases hpS : p ∈ S <;> by_cases hqS : q ∈ S
    · left; simp [hpS, hqS]
    · right; simp only [hpS, hqS, if_true, if_false, sub_zero]; exact hdiam p hp hpS q hq hqS hpq
    · right
      simp only [hpS, hqS, if_true, if_false, zero_sub, inner_neg_right]
      have := hdiam q hq hqS p hp hpS (by rw [dist_comm]; exact hpq)
      rw [← neg_sub, inner_neg_left] at this; linarith
    · left; simp [hpS, hqS]
  · obtain ⟨p, hp, hpS⟩ := hS
    obtain ⟨q, hq, hqS⟩ := hSc
    exact ⟨p, hp, q, hq, by simp [hpS, hqS, hc]⟩

lemma isHV_toC {X : Finset Plane} {x : Plane} (hx : x ∈ hullVertices X) :
    IsHV (X.image toC) (toC x) := by
  have hxe := (Finset.mem_filter.1 hx).2
  have h1 : toC x ∈ toC '' extremePoints ℝ (convexHull ℝ (X : Set Plane)) := ⟨x, hxe, rfl⟩
  have e : toC '' convexHull ℝ (X : Set Plane) = convexHull ℝ (toC '' (X : Set Plane)) :=
    LinearMap.image_convexHull toC.toLinearEquiv.toLinearMap _
  rw [image_extremePoints, e] at h1
  rw [IsHV, Finset.coe_image]; exact h1

/-- The reachability relation of the contact graph, transported to `ℂ`. -/
def contactRel (X : Finset Plane) (z w : ℂ) : Prop :=
  z = w ∨ ∃ (hp : toC.symm z ∈ X) (hq : toC.symm w ∈ X),
    (contactGraph X).Reachable ⟨toC.symm z, hp⟩ ⟨toC.symm w, hq⟩

/-- **Lemma 2.1 (connectivity).**  Under finite multiplicity the contact graph of an optimal set
with at least two points is connected. -/
theorem contactGraph_connected_of_optimal {n : ℕ} (hn : 2 ≤ n) (hfm : numOptimalClasses n < ⊤)
    {X : Finset Plane} (hX : IsOptimal n X) : (contactGraph X).Connected := by
  have hXne : X.Nonempty := by
    rw [← Finset.card_pos, hX.1.1]; omega
  rw [SimpleGraph.connected_iff]
  refine ⟨?_, ⟨⟨hXne.choose, hXne.choose_spec⟩⟩⟩
  intro u0 v0
  by_contra hnr
  set Y := X.image toC with hYdef
  have hYmem : ∀ z, z ∈ Y ↔ toC.symm z ∈ X := by
    intro z
    rw [hYdef, Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩; simpa using hx
    · intro h; exact ⟨_, h, by simp⟩
  have hsep : ∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → 1 ≤ dist x y := by
    intro x hx y hy hxy
    have hne : toC.symm x ≠ toC.symm y := fun h => hxy (toC.symm.injective h)
    have h := hX.1.2 _ ((hYmem x).1 hx) _ ((hYmem y).1 hy) hne
    rwa [LinearIsometryEquiv.dist_map] at h
  set R := contactRel X with hR
  have hRr : ∀ z, R z z := fun z => Or.inl rfl
  have hRs : ∀ z w, R z w → R w z := by
    rintro z w (rfl | ⟨hp, hq, h⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨hq, hp, h.symm⟩
  have hRt : ∀ z w v, R z w → R w v → R z v := by
    rintro z w v (rfl | ⟨hp, hq, h⟩) h2
    · exact h2
    rcases h2 with rfl | ⟨hq', hr, h'⟩
    · exact Or.inr ⟨hp, hq, h⟩
    · exact Or.inr ⟨hp, hr, h.trans h'⟩
  have hpath : ∀ x ∈ Y, ∀ y ∈ Y, R x y → ∃ P' : List ℂ, (∀ z ∈ x :: P', z ∈ Y ∧ R x z) ∧
      (x :: P').getLast (by simp) = y ∧ (x :: P').IsChain (fun a b => dist a b = 1) := by
    rintro x hx y hy (rfl | ⟨hp, hq, ⟨w⟩⟩)
    · exact ⟨[], fun z hz => by
        simp only [List.mem_singleton] at hz; subst hz; exact ⟨hx, hRr _⟩, rfl,
        List.isChain_singleton _⟩
    set f : X → ℂ := fun v => toC v.1 with hf
    have hfx : f ⟨toC.symm x, hp⟩ = x := by simp [hf]
    have hfy : f ⟨toC.symm y, hq⟩ = y := by simp [hf]
    have hsupp : w.support.map f = x :: w.support.tail.map f := by
      rw [w.support_eq_cons, List.map_cons, hfx]; rfl
    refine ⟨w.support.tail.map f, ?_, ?_, ?_⟩
    · intro z hz
      rw [← hsupp, List.mem_map] at hz
      obtain ⟨v, hv, rfl⟩ := hz
      refine ⟨(hYmem _).2 (by simp [hf]), Or.inr ⟨hp, by simp [hf], ?_⟩⟩
      have hr := (w.takeUntil v hv).reachable
      convert hr using 2
      simp [hf]
    · have : (w.support.map f).getLast (by simp) = y := by
        rw [List.getLast_map, w.getLast_support, hfy]
      simp only [hsupp] at this
      exact this
    · rw [← hsupp, List.isChain_map]
      refine w.isChain_adj_support.imp fun a b hab => ?_
      have : dist (a : Plane) b = 1 := hab
      simpa [hf, LinearIsometryEquiv.dist_map] using this
  have hdis : ∃ x ∈ Y, ∃ y ∈ Y, ¬ R x y := by
    refine ⟨toC u0.1, (hYmem _).2 (by simp), toC v0.1, (hYmem _).2 (by simp), ?_⟩
    rintro (h | ⟨hp, hq, h⟩)
    · apply hnr
      have : u0 = v0 := Subtype.ext (toC.injective h)
      rw [this]
    · apply hnr
      convert h using 2 <;> simp
  obtain ⟨S, hSY, hScl, ⟨s0, hs0⟩, ⟨q0, hq0, hq0S⟩, c, hc, hcS⟩ :=
    exists_release_C Y hsep R hRr hRs hRt hpath hdis
  refine false_of_closed_translation hn hfm hX {p | toC p ∈ S} ?_ ?_ ?_ (toC.symm c) ?_ ?_
  · intro p hp q hq hpq
    have hpX : p ∈ X := by simpa using (hYmem _).1 (hSY hp)
    refine hScl _ hp _ ((hYmem _).2 (by simpa using hq)) (Or.inr ⟨by simpa using hpX,
      by simpa using hq, ?_⟩)
    have hadj : (contactGraph X).Adj ⟨p, hpX⟩ ⟨q, hq⟩ := hpq
    convert hadj.reachable using 2 <;> simp
  · exact ⟨toC.symm s0, (hYmem _).1 (hSY hs0), by simpa using hs0⟩
  · exact ⟨toC.symm q0, (hYmem _).1 hq0, by simpa using hq0S⟩
  · simpa using hc
  · intro p hp hpS q hq hqS hpq
    have hD : 0 < diam X := hX.diam_pos hn
    have hpq' : p ≠ q := by rintro rfl; rw [dist_self] at hpq; linarith
    have hpH := mem_hullVertices_of_diam hp hq hpq' hpq
    have hqH := mem_hullVertices_of_diam hq hp hpq'.symm (by rw [dist_comm]; exact hpq)
    have := hcS _ hpS _ ((hYmem _).2 (by simpa using hq)) hqS (isHV_toC hpH) (isHV_toC hqH)
    rw [← LinearIsometryEquiv.inner_map_map toC, map_sub, LinearIsometryEquiv.apply_symm_apply,
      Complex.inner, mul_comm]
    exact this

end Erdos99
end

end Connected

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `DirectCountAlgebra`
-/

section DirectCountAlgebra

/-!
# WP1: the algebra of the direct `Y` route for `track_count`

This file records, as statements about real numbers, all the linear algebra that the direct
`Y` route (Verification Guide §§2, 4, 14) needs in order to finish `Erdos99.track_count`.
It pins down the exact interface that the geometric parts of the proof have to deliver.

Notation (all quantities are real casts of counts, `Δ` is signed):

* `b` hull sides, `u` unit returns, `c₂` two-edge returns, `v = Σ_{j≥3} c_j`,
  `ρ = Σ_{j≥3} (j-2) c_j`;
* `p, h` exceptional pentagons and hexagons, `fhi = Σ_{k≥7} f_k`, `σhi = Σ_{k≥7} (k-4) f_k`,
  `f = p + h + fhi`, `σ = p + 2h + σhi`, `Δ = u - σ - ρ`;
* `s` all tracks, `E` tracks with fewer than `L` rhombi, `R = s - E`;
* `Y` the unmarked short-degree surplus, `A` good activated pentagons, `C₁` two-edge returns with
  exactly one short port, `P` selected ports, `d` the degree defect defined by (D1).

Main results:

* `two_R_eq` (D2) and `R_le` (D3): the long-track count in terms of `f, Y, A, C₁`;
* `f_add_c₂_le` (D4): the exact perimeter budget `f + c₂ ≤ b`;
* `charge_lower` (C5) and `four_f_le` (D5) with the error `eCharge` of (C8);
* `direct_track_count_algebra` (D6) and its slack identity `direct_track_count_slack`;
* `eR_le` (E1) and `budget_allocation` (§14.2);
* `track_count_of_ledger`: everything combined into the shape of `track_count`.
-/

open scoped Real

@[expose] public section

namespace Erdos99

namespace DirectCount

/-! ## §2.3: eliminating the cycle rank -/

/-- (D2): subtracting the degree identity (D1) from `2s = 2b - Δ + 4f` gives the long-track count
exactly, with no cycle rank and no global component count. -/
theorem two_R_eq (b u c₂ v f p h fhi σhi σ Δ ρ s E R Y A C₁ d : ℝ)
    (hb : b = u + c₂ + v) (hs : 2 * s = 2 * b - Δ + 4 * f) (hf : f = p + h + fhi)
    (hσ : σ = p + 2 * h + σhi) (hΔ : Δ = u - σ - ρ) (hR : R = s - E)
    (hD1 : 2 * E = u + 2 * c₂ - C₁ + 3 * p + 4 * h + Y + 2 * A + d) :
    2 * R = 2 * f - Y - 2 * A + C₁ + σhi + 2 * fhi + ρ + 2 * v - d := by
  subst hR; linarith

/-- The error term of (D3): `eR = (σhi + 2 fhi + ρ + 2v + |d|) / 2`. -/
noncomputable def eR (fhi σhi ρ v d : ℝ) : ℝ := (σhi + 2 * fhi + ρ + 2 * v + |d|) / 2

/-- (D3): `R ≤ f - Y/2 - A + C₁/2 + eR`. -/
theorem R_le {f fhi σhi ρ v R Y A C₁ d : ℝ}
    (h : 2 * R = 2 * f - Y - 2 * A + C₁ + σhi + 2 * fhi + ρ + 2 * v - d) :
    R ≤ f - Y / 2 - A + C₁ / 2 + eR fhi σhi ρ v d := by
  unfold eR
  have := neg_abs_le d
  linarith

/-! ## §2.4: the perimeter budget -/

/-- (D4): from the locking inequality `Δ ≥ 0` (and `f ≤ σ`, which holds termwise since `k - 4 ≥ 1`
for every exceptional face), `f + c₂ ≤ b`. -/
theorem f_add_c₂_le {b u c₂ v f p h fhi σhi σ Δ ρ : ℝ}
    (hb : b = u + c₂ + v) (hf : f = p + h + fhi) (hσ : σ = p + 2 * h + σhi)
    (hΔ : Δ = u - σ - ρ) (hΔ0 : 0 ≤ Δ) (hh : 0 ≤ h) (hhi : fhi ≤ σhi) (hv : 0 ≤ v)
    (hρ : 0 ≤ ρ) :
    f + c₂ ≤ b := by
  linarith

/-! ## §4: the error ledger of the charging argument -/

/-- (C5): the charge `M = eJJ + 2 j₂ + 4 j₃` is bounded below in terms of the good faces, from
(C1), (C3), (C4) and `x ≤ 4 g₂`. Here `H` is the number of degree-two good faces, `g₂` the number
of degree-four good faces, `f_good = |H| + Y - g₂`. -/
theorem charge_lower (H g₂ Y fgood j₁ j₂ j₃ x hC C κG κK eJJ : ℝ)
    (hf : fgood = H + Y - g₂) (hx : x ≤ 4 * g₂)
    (hC1 : 2 * H = j₁ + 2 * j₂ + 3 * j₃ + x + hC)
    (hC3 : g₂ ≤ 3 / 2 * Y + C / 2 + κG - fgood)
    (hC4 : 3 * j₁ + 2 * j₂ + j₃ + x ≤ Y + 2 * eJJ + C - hC + 2 * κK) :
    4 * fgood - 5 * Y - hC - C - κG - κK ≤ eJJ + 2 * j₂ + 4 * j₃ := by
  linarith

/-- The total charging error (C8): `eCharge = κG + κK + eFlag + eCap + eHCap + 4 Bf`. -/
noncomputable def eCharge (κG κK eFlag eCap eHCap Bf : ℝ) : ℝ :=
  κG + κK + eFlag + eCap + eHCap + 4 * Bf

/-- (D5) from (C5)–(C7): `4f ≤ 5Y + 4P + 4c₂ - 3C₁ + eCharge`. Here `M` is the charge,
`f_good = f - Bf` and `C`, `hC` count (actual or virtual) cap incidences. -/
theorem four_f_le {f Bf fgood Y P c₂ C₁ C hC M κG κK eFlag eCap eHCap : ℝ}
    (hfg : fgood = f - Bf)
    (hC5 : 4 * fgood - 5 * Y - hC - C - κG - κK ≤ M)
    (hC6 : M ≤ 4 * P + eFlag)
    (hCap : C ≤ 2 * c₂ - C₁ + eCap) (hHCap : hC ≤ 2 * (c₂ - C₁) + eHCap) :
    4 * f ≤ 5 * Y + 4 * P + 4 * c₂ - 3 * C₁ + eCharge κG κK eFlag eCap eHCap Bf := by
  unfold eCharge
  linarith

/-! ## §2.6: the final linear implication -/

/-- (D6): the final linear implication of the direct route. `B` will be `π D`. -/
theorem direct_track_count_algebra (R P f Y A c₂ C₁ B eR eC : ℝ)
    (hR : R ≤ f - Y / 2 - A + C₁ / 2 + eR)
    (hC : 4 * f ≤ 5 * Y + 4 * P + 4 * c₂ - 3 * C₁ + eC)
    (hA : 0 ≤ A) (hCap : C₁ ≤ c₂) (hBudget : f + c₂ ≤ B) :
    R - P ≤ (3 / 5 : ℝ) * (B - P) + eR + eC / 10 := by
  linarith

/-- The nonnegative-slack certificate behind (D6): the difference of the two sides of (D6) is
`sR + sCh/10 + sCap/5 + (3/5) sBud + A`. -/
theorem direct_track_count_slack (R P f Y A c₂ C₁ B eR eC : ℝ) :
    ((3 / 5 : ℝ) * (B - P) + eR + eC / 10) - (R - P) =
      (f - Y / 2 - A + C₁ / 2 + eR - R) + (5 * Y + 4 * P + 4 * c₂ - 3 * C₁ + eC - 4 * f) / 10 +
        (c₂ - C₁) / 5 + 3 / 5 * (B - f - c₂) + A := by
  ring

/-! ## §14: the degree-defect budget and a numerical allocation -/

/-- The decomposition of the degree defect in §14.1:
`d = dFace - Bunit - 2 Btwo + cLong` gives `|d| ≤ Bface + Bunit + 2 Btwo + 3ρ`. -/
theorem abs_defect_le {d dFace Bface Bunit Btwo cLong ρ : ℝ}
    (hd : d = dFace - Bunit - 2 * Btwo + cLong) (hFace : |dFace| ≤ Bface)
    (hunit : 0 ≤ Bunit) (htwo : 0 ≤ Btwo) (hcL : 0 ≤ cLong) (hcL' : cLong ≤ 3 * ρ) :
    |d| ≤ Bface + Bunit + 2 * Btwo + 3 * ρ := by
  rw [abs_le] at hFace ⊢
  constructor <;> linarith

/-- (E1): `eR ≤ (Hinc + Bface + Bunit + 2 Btwo + 6ρ) / 2`, where `Hinc = Σ_{k≥7} k f_k` bounds
`σhi + 2 fhi = Σ_{k≥7} (k - 2) f_k`, and `v ≤ ρ`. -/
theorem eR_le {fhi σhi ρ v d Hinc Bface Bunit Btwo : ℝ}
    (hHinc : σhi + 2 * fhi ≤ Hinc) (hv : v ≤ ρ)
    (hd : |d| ≤ Bface + Bunit + 2 * Btwo + 3 * ρ) :
    eR fhi σhi ρ v d ≤ (Hinc + Bface + Bunit + 2 * Btwo + 6 * ρ) / 2 := by
  unfold eR
  linarith

/-- The allocation of §14.2: with `η = min (ε/100) (1/100)`, if each of the eleven exceptional
counts is at most `η D`, then `eR + eCharge/10 < ε D`. -/
theorem budget_allocation {ε D : ℝ} (hε : 0 < ε) (hD : 0 < D)
    {fhi σhi ρ v d Hinc Bface Bunit Btwo κG κK eFlag eCap eHCap Bf : ℝ}
    (hHinc : σhi + 2 * fhi ≤ Hinc) (hv : v ≤ ρ)
    (hd : |d| ≤ Bface + Bunit + 2 * Btwo + 3 * ρ)
    (h1 : Hinc ≤ min (ε / 100) (1 / 100) * D) (h2 : Bface ≤ min (ε / 100) (1 / 100) * D)
    (h3 : Bunit ≤ min (ε / 100) (1 / 100) * D) (h4 : Btwo ≤ min (ε / 100) (1 / 100) * D)
    (h5 : ρ ≤ min (ε / 100) (1 / 100) * D) (h6 : κG ≤ min (ε / 100) (1 / 100) * D)
    (h7 : κK ≤ min (ε / 100) (1 / 100) * D) (h8 : eFlag ≤ min (ε / 100) (1 / 100) * D)
    (h9 : eCap ≤ min (ε / 100) (1 / 100) * D) (h10 : eHCap ≤ min (ε / 100) (1 / 100) * D)
    (h11 : Bf ≤ min (ε / 100) (1 / 100) * D) :
    eR fhi σhi ρ v d + eCharge κG κK eFlag eCap eHCap Bf / 10 < ε * D := by
  have hE := eR_le hHinc hv hd
  have hη : min (ε / 100) (1 / 100) * D ≤ ε / 100 * D :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) hD.le
  have hεD : 0 < ε * D := mul_pos hε hD
  unfold eCharge
  linarith

/-! ## Assembly -/

/-- **The direct route, assembled.** If the geometry delivers the exact identities of §2.1, the
degree identity (D1), the locking inequality `Δ ≥ 0`, the perimeter bound `b ≤ π D`, the charging
ledger (C5)–(C7) and the eleven exceptional counts of §14.2 each at most `η D`, then the long-track
count `R` and the number `P` of selected ports satisfy the inequality of `track_count`:
`R - P ≤ (3/5)(π D - P) + ε D`. -/
theorem track_count_of_ledger {ε D : ℝ} (hε : 0 < ε) (hD : 0 < D)
    -- the counts of §2.1
    {b u c₂ v f p h fhi σhi σ Δ ρ s E R Y A C₁ d P : ℝ}
    (hb : b = u + c₂ + v) (hs : 2 * s = 2 * b - Δ + 4 * f) (hf : f = p + h + fhi)
    (hσ : σ = p + 2 * h + σhi) (hΔ : Δ = u - σ - ρ) (hR : R = s - E)
    (hD1 : 2 * E = u + 2 * c₂ - C₁ + 3 * p + 4 * h + Y + 2 * A + d)
    (hΔ0 : 0 ≤ Δ) (hh : 0 ≤ h) (hhi : fhi ≤ σhi) (hv0 : 0 ≤ v) (hv : v ≤ ρ)
    (hbD : b ≤ π * D) (hA : 0 ≤ A) (hC₁ : C₁ ≤ c₂)
    -- the charging ledger of §4
    {H g₂ fgood Bf j₁ j₂ j₃ x hC C κG κK eJJ eFlag eCap eHCap : ℝ}
    (hfg : fgood = f - Bf) (hfH : fgood = H + Y - g₂) (hx : x ≤ 4 * g₂)
    (hC1 : 2 * H = j₁ + 2 * j₂ + 3 * j₃ + x + hC)
    (hC3 : g₂ ≤ 3 / 2 * Y + C / 2 + κG - fgood)
    (hC4 : 3 * j₁ + 2 * j₂ + j₃ + x ≤ Y + 2 * eJJ + C - hC + 2 * κK)
    (hC6 : eJJ + 2 * j₂ + 4 * j₃ ≤ 4 * P + eFlag)
    (hCap : C ≤ 2 * c₂ - C₁ + eCap) (hHCap : hC ≤ 2 * (c₂ - C₁) + eHCap)
    -- the degree-defect budget of §14.1
    {Hinc Bface Bunit Btwo : ℝ}
    (hHinc : σhi + 2 * fhi ≤ Hinc) (hd : |d| ≤ Bface + Bunit + 2 * Btwo + 3 * ρ)
    -- the eleven exceptional counts of §14.2
    (h1 : Hinc ≤ min (ε / 100) (1 / 100) * D) (h2 : Bface ≤ min (ε / 100) (1 / 100) * D)
    (h3 : Bunit ≤ min (ε / 100) (1 / 100) * D) (h4 : Btwo ≤ min (ε / 100) (1 / 100) * D)
    (h5 : ρ ≤ min (ε / 100) (1 / 100) * D) (h6 : κG ≤ min (ε / 100) (1 / 100) * D)
    (h7 : κK ≤ min (ε / 100) (1 / 100) * D) (h8 : eFlag ≤ min (ε / 100) (1 / 100) * D)
    (h9 : eCap ≤ min (ε / 100) (1 / 100) * D) (h10 : eHCap ≤ min (ε / 100) (1 / 100) * D)
    (h11 : Bf ≤ min (ε / 100) (1 / 100) * D) :
    R - P ≤ 3 / 5 * (π * D - P) + ε * D := by
  have hρ : 0 ≤ ρ := hv0.trans hv
  have hD3 := R_le (two_R_eq b u c₂ v f p h fhi σhi σ Δ ρ s E R Y A C₁ d hb hs hf hσ hΔ hR hD1)
  have hD4 := f_add_c₂_le hb hf hσ hΔ hΔ0 hh hhi hv0 hρ
  have hD5 := four_f_le hfg (charge_lower H g₂ Y fgood j₁ j₂ j₃ x hC C κG κK eJJ hfH hx hC1 hC3 hC4)
    hC6 hCap hHCap
  have hD6 := direct_track_count_algebra R P f Y A c₂ C₁ (π * D) _ _ hD3 hD5 hA hC₁
    (hD4.trans hbD)
  have hbud := budget_allocation hε hD hHinc hv hd h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  linarith

end DirectCount

end Erdos99
end

end DirectCountAlgebra

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `FiniteCutoff`
-/

section FiniteCutoff

/-!
# WP2: choosing the cutoff by a finite pigeonhole argument

The measure-theoretic choice of the cutoff `L` in the manuscript is replaced (Verification Guide
§11) by a finite pigeonhole argument on the shells `[a_{i+1} D, a_i D)`. This file proves the
generic pieces:

* `exists_sparse_shell` (§11.1, §16.2): if a finite set of lengths has at most `Cs D` elements and
  `Cs < J δ`, then among the `J` disjoint shells cut out by an antitone sequence `a` one contains at
  most `δ D` lengths;
* `eventually_mul_rpow_le` (§5): `C D^α ≤ δ D` for all large `D`, whenever `α < 1` and `δ > 0`.

The instance for the tracks of an optimal configuration (using the proved bound
`Erdos99.tracks_card_le`) is `Erdos99.exists_sparse_track_shell` in `Overview`.
-/

open Filter

@[expose] public section

namespace Erdos99

/-- The shells `[a (i+1) D, a i D)` of an antitone sequence are pairwise disjoint. -/
theorem shell_disjoint {a : ℕ → ℝ} (ha : Antitone a) {D x : ℝ} (hD : 0 ≤ D) {i j : ℕ}
    (hij : i < j) (hi : a (i + 1) * D ≤ x) (hj : x < a j * D) : False := by
  have : a j * D ≤ a (i + 1) * D := mul_le_mul_of_nonneg_right (ha hij) hD
  linarith

/-- **Finite pigeonhole for cutoffs** (Verification Guide §11.1). Let `T` be a finite set with a
length function `len`, with `|T| ≤ Cs D`. If `Cs < J δ` and `a` is antitone, then some shell
`[a (i+1) D, a i D)` with `i < J` contains at most `δ D` elements of `T`. -/
theorem exists_sparse_shell {ι : Type*} (T : Finset ι) (len : ι → ℝ) {D δ Cs : ℝ} {J : ℕ}
    {a : ℕ → ℝ} (ha : Antitone a) (hD : 0 < D) (hcard : (T.card : ℝ) ≤ Cs * D)
    (hJ : Cs < J * δ) :
    ∃ i < J, ((T.filter fun t => a (i + 1) * D ≤ len t ∧ len t < a i * D).card : ℝ) ≤ δ * D := by
  classical
  by_contra hcon
  push_neg at hcon
  set S : ℕ → Finset ι := fun i => T.filter fun t => a (i + 1) * D ≤ len t ∧ len t < a i * D
  have hdisj : (↑(Finset.range J) : Set ℕ).PairwiseDisjoint S := by
    intro i _ j _ hne
    refine Finset.disjoint_left.2 fun t hti htj => ?_
    obtain ⟨-, hi1, hi2⟩ := Finset.mem_filter.1 hti
    obtain ⟨-, hj1, hj2⟩ := Finset.mem_filter.1 htj
    rcases lt_or_gt_of_ne hne with h | h
    · exact shell_disjoint ha hD.le h hi1 hj2
    · exact shell_disjoint ha hD.le h hj1 hi2
  have hsub : (Finset.range J).biUnion S ⊆ T :=
    Finset.biUnion_subset.2 fun i _ => Finset.filter_subset _ _
  have hle : ∑ i ∈ Finset.range J, (S i).card ≤ T.card := by
    rw [← Finset.card_biUnion hdisj]
    exact Finset.card_le_card hsub
  have hlt : ∑ i ∈ Finset.range J, δ * D < ∑ i ∈ Finset.range J, ((S i).card : ℝ) := by
    apply Finset.sum_lt_sum_of_nonempty
    · refine ⟨0, Finset.mem_range.2 ?_⟩
      rcases Nat.eq_zero_or_pos J with h | h
      · subst h
        have : (0 : ℝ) ≤ T.card := Nat.cast_nonneg _
        have : Cs * D < 0 := by
          have := mul_lt_mul_of_pos_right (show Cs < 0 by simpa using hJ) hD
          simpa using this
        linarith
      · exact h
    · exact fun i hi => hcon i (Finset.mem_range.1 hi)
  have hle' : (∑ i ∈ Finset.range J, ((S i).card : ℝ)) ≤ T.card := by exact_mod_cast hle
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hlt
  have : Cs * D < J * δ * D := mul_lt_mul_of_pos_right hJ hD
  linarith

/-- The asymptotic helper of Verification Guide §5: a power `D^α` with `α < 1` is eventually
negligible against `D`. -/
theorem eventually_mul_rpow_le (C : ℝ) {α δ : ℝ} (hα : α < 1) (hδ : 0 < δ) :
    ∀ᶠ D : ℝ in atTop, C * D ^ α ≤ δ * D := by
  have h := (tendsto_rpow_neg_atTop (y := 1 - α) (by linarith)).const_mul (C / δ)
  rw [mul_zero] at h
  filter_upwards [h.eventually (ge_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    eventually_gt_atTop 0] with D hD hD0
  have h1 : D ^ α = D ^ (-(1 - α)) * D := by
    rw [← Real.rpow_add_one hD0.ne']; ring_nf
  have h2 : C / δ * D ^ (-(1 - α)) * δ = C * D ^ (-(1 - α)) := by field_simp
  rw [h1]
  nlinarith [mul_le_mul_of_nonneg_right hD (le_of_lt (mul_pos hδ hD0))]

end Erdos99
end

end FiniteCutoff

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `QuadraticResponseAlgebra`
-/

section QuadraticResponseAlgebra

/-!
# WP9: the quadratic response algebra

Algebraic identities behind the local exclusion calculations (Verification Guide §§12.1–12.3,
13.1, 13.5). The plane is identified with `ℂ`; `ζ` is the common unit tangent.

* `two_circle_eq` (A1) and `two_circle_eq_zeta`, `two_circle_eq_poly` (A1)/(A2): the response
  equation of an `H` receiver;
* `quadratic_norm` (A3) and `quadratic_root_elim` (A4): elimination of a quadratic variable;
* `response_factor`: the factorisation `(z - a)(a⋆ z - 1) = -z` of the response quadratic;
* `response_asymptotics` (`Z ≠ 0`) and `response_zero_Z`, `re_eq_of_root` (`Z = 0`): the root
  asymptotics along a real parameter `T → ∞`;
* `response_leading_re_nonneg`: every limiting normalised root has nonnegative real part;
* `hh_identity` (H1), `hh_identity_star`, and `hh_identity_opposite` (the case `W = -Z`);
* `capPoly` and `capPoly_eval`, `capPoly_coeff_two`, `capPoly_ne_zero` (H2).
-/

open Filter Polynomial ComplexConjugate

@[expose] public section

namespace Erdos99

namespace QuadraticResponse

/-! ## Unit-circle conjugation -/

lemma mul_conj_eq_one {z : ℂ} (hz : ‖z‖ = 1) : z * conj z = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; simp

lemma ne_zero_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) : z ≠ 0 := by
  rintro rfl; simp at hz

lemma conj_eq_inv {z : ℂ} (hz : ‖z‖ = 1) : conj z = z⁻¹ :=
  eq_inv_of_mul_eq_one_right (mul_conj_eq_one hz)

lemma norm_sq_eq_mul_conj (w : ℂ) : ((‖w‖ ^ 2 : ℝ) : ℂ) = w * conj w := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- On the unit circle, `conj (k ζ + Z) = k / ζ + conj Z`. -/
lemma conj_response {ζ : ℂ} (hζ : ‖ζ‖ = 1) (k : ℝ) (Z : ℂ) :
    conj ((k : ℂ) * ζ + Z) = (k : ℂ) / ζ + conj Z := by
  rw [map_add, map_mul, Complex.conj_ofReal, conj_eq_inv hζ, div_eq_mul_inv]

/-! ## §12.1: the two-circle equation -/

/-- (A1), basic form: if `|z| = 1` and `|z - a| = 1`, then `ā z² - a ā z + a = 0`. -/
theorem two_circle_eq {z a : ℂ} (hz : ‖z‖ = 1) (hza : ‖z - a‖ = 1) :
    conj a * z ^ 2 - a * conj a * z + a = 0 := by
  have h0 := mul_conj_eq_one hz
  have h1 := mul_conj_eq_one hza
  rw [map_sub] at h1
  linear_combination -z * h1 + z * h0 - a * h0

/-- (A1): at an `H` receiver with marked sum `k ζ` and retained sum `Z`, the incoming port `z`
satisfies `a⋆ z² - a a⋆ z + a = 0` with `a = k ζ + Z`, `a⋆ = k / ζ + conj Z`. -/
theorem two_circle_eq_zeta {ζ Z z : ℂ} (k : ℝ) (hζ : ‖ζ‖ = 1) (hz : ‖z‖ = 1)
    (hza : ‖z - ((k : ℂ) * ζ + Z)‖ = 1) :
    ((k : ℂ) / ζ + conj Z) * z ^ 2 - ((k : ℂ) * ζ + Z) * ((k : ℂ) / ζ + conj Z) * z +
      ((k : ℂ) * ζ + Z) = 0 := by
  have := two_circle_eq hz hza
  rwa [conj_response hζ] at this

/-- (A2): the same equation multiplied by `ζ`, an ordinary polynomial equation. -/
theorem two_circle_eq_poly {ζ Z z : ℂ} (k : ℝ) (hζ : ‖ζ‖ = 1) (hz : ‖z‖ = 1)
    (hza : ‖z - ((k : ℂ) * ζ + Z)‖ = 1) :
    ((k : ℂ) + ζ * conj Z) * z ^ 2 - ((k : ℂ) * ζ + Z) * ((k : ℂ) + ζ * conj Z) * z +
      ζ * ((k : ℂ) * ζ + Z) = 0 := by
  have h := two_circle_eq_zeta k hζ hz hza
  have hζ0 := ne_zero_of_norm_eq_one hζ
  have hinv : ζ * ζ⁻¹ = 1 := mul_inv_cancel₀ hζ0
  simp only [div_eq_mul_inv] at h ⊢
  linear_combination ζ * h + ((k : ℂ) * z * Z - (k : ℂ) * z ^ 2 + (k : ℂ) ^ 2 * ζ * z) * hinv

/-! ## §12.2: eliminating quadratic variables -/

/-- (A3): the norm formula for a monic quadratic. If `z² - a z + b = 0`, then
`(U + V z)(U + V (a - z)) = U² + a U V + b V²` (this also covers repeated roots). -/
theorem quadratic_norm {R : Type*} [CommRing R] {z a b U V : R} (h : z ^ 2 - a * z + b = 0) :
    (U + V * z) * (U + V * (a - z)) = U ^ 2 + a * U * V + b * V ^ 2 := by
  linear_combination (-V ^ 2) * h

/-- (A4): if `A z² + B z + C = 0` and `U + V z = 0`, then `A U² - B U V + C V² = 0`
(no division by `A`). -/
theorem quadratic_root_elim {R : Type*} [CommRing R] {z A B C U V : R}
    (h : A * z ^ 2 + B * z + C = 0) (hUV : U + V * z = 0) :
    A * U ^ 2 - B * U * V + C * V ^ 2 = 0 := by
  linear_combination V ^ 2 * h + (A * (U - V * z) - B * V) * hUV

/-! ## §12.3: root asymptotics along a real parameter -/

/-- The response quadratic factors as `(z - a)(a⋆ z - 1) = -z`. -/
theorem response_factor {R : Type*} [CommRing R] {a aS z : R}
    (h : aS * z ^ 2 - a * aS * z + a = 0) : (z - a) * (aS * z - 1) = -z := by
  linear_combination h

/-- Root asymptotics for `Z ≠ 0` (Verification Guide §12.3). Put `a = k T + Z` and
`a⋆ = k / T + conj Z`. If `z T` solves the response quadratic for all large `T`, then for every
`ε > 0`, eventually either `z T / T` is `ε`-close to `k` or `z T` is `ε`-close to `1 / conj Z`.
(Equivalently: along every sequence `T → ∞` some subsequence has `z/T → k`, or `z → 1/conj Z`.) -/
theorem response_asymptotics {k : ℝ} (hk : 0 < k) {Z : ℂ} (hZ : Z ≠ 0) {z : ℝ → ℂ}
    (hz : ∀ᶠ T : ℝ in atTop, ((k : ℂ) / T + conj Z) * z T ^ 2 -
      ((k : ℂ) * T + Z) * ((k : ℂ) / T + conj Z) * z T + ((k : ℂ) * T + Z) = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ‖z T / T - k‖ < ε ∨ ‖z T - (conj Z)⁻¹‖ < ε := by
  set c := ‖Z‖ with hc
  have hc0 : 0 < c := norm_pos_iff.2 hZ
  set M := 4 / c with hM
  have hM0 : 0 < M := by positivity
  filter_upwards [hz, eventually_gt_atTop 0, eventually_gt_atTop (2 * k / c),
    eventually_gt_atTop ((c + M + 4 * M / (ε * c)) / k),
    eventually_gt_atTop (4 * k * M / (ε * c)), eventually_gt_atTop ((4 / c + c) / ε)]
    with T hq hT0 hT1 hT2 hT3 hT4
  set aS : ℂ := (k : ℂ) / T + conj Z with haS
  set a : ℂ := (k : ℂ) * T + Z with ha
  have hfac : (z T - a) * (aS * z T - 1) = -z T := response_factor hq
  have hnorm : ‖z T - a‖ * ‖aS * z T - 1‖ = ‖z T‖ := by rw [← norm_mul, hfac, norm_neg]
  have hkT : ‖(k : ℂ) / T‖ = k / T := by
    rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hk.le,
      Real.norm_of_nonneg hT0.le]
  have hkT' : ‖(k : ℂ) * T‖ = k * T := by
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hk.le,
      Real.norm_of_nonneg hT0.le]
  have hcZ : ‖conj Z‖ = c := Complex.norm_conj Z
  have hcZ0 : conj Z ≠ 0 := by rwa [_root_.map_ne_zero]
  by_cases hzM : ‖z T‖ ≤ M
  · right
    have ha1 : k * T - c ≤ ‖a‖ := by
      have : (k : ℂ) * T = a - Z := by rw [ha]; ring
      have h := norm_sub_le a Z
      rw [← this, hkT'] at h
      linarith
    have hza : k * T - c - M ≤ ‖z T - a‖ := by
      have h := norm_sub_le (a - z T) (-z T)
      rw [sub_neg_eq_add, sub_add_cancel, norm_neg, norm_sub_rev] at h
      linarith
    have hkT2 : c + M + 4 * M / (ε * c) < k * T := by
      have h := hT2
      rw [div_lt_iff₀ hk] at h
      linarith
    have hY : 4 * M / (ε * c) ≤ ‖z T - a‖ := by linarith
    have hY0 : 0 < 4 * M / (ε * c) := by positivity
    have h1 : ‖aS * z T - 1‖ ≤ ε * c / 4 := by
      have hx := norm_nonneg (aS * z T - 1)
      have h2 : ‖aS * z T - 1‖ * (4 * M / (ε * c)) ≤ M := by
        calc _ ≤ ‖aS * z T - 1‖ * ‖z T - a‖ := mul_le_mul_of_nonneg_left hY hx
          _ = ‖z T‖ := by rw [mul_comm, hnorm]
          _ ≤ M := hzM
      have h3 : ‖aS * z T - 1‖ * (4 * M / (ε * c)) = (‖aS * z T - 1‖ / (ε * c / 4)) * M := by
        field_simp
      rw [h3] at h2
      have h4 : ‖aS * z T - 1‖ / (ε * c / 4) ≤ 1 := by
        by_contra hcon
        push_neg at hcon
        nlinarith
      rwa [div_le_one (by positivity)] at h4
    have h2 : ‖(k : ℂ) / T * z T‖ < ε * c / 4 := by
      rw [norm_mul, hkT]
      have : k / T * ‖z T‖ ≤ k / T * M := mul_le_mul_of_nonneg_left hzM (by positivity)
      have h5 : k / T * M < ε * c / 4 := by
        rw [div_lt_iff₀ (by positivity)] at hT3
        rw [div_mul_eq_mul_div, div_lt_iff₀ hT0]
        linarith
      linarith
    have h3 : conj Z * z T - 1 = (aS * z T - 1) - (k : ℂ) / T * z T := by rw [haS]; ring
    have h4 : ‖conj Z * z T - 1‖ < ε * c / 2 := by
      rw [h3]
      have := norm_sub_le (aS * z T - 1) ((k : ℂ) / T * z T)
      linarith
    have h5 : z T - (conj Z)⁻¹ = (conj Z * z T - 1) / conj Z := by field_simp
    rw [h5, norm_div, hcZ, div_lt_iff₀ hc0]
    nlinarith
  · left
    push_neg at hzM
    have hz0 : 0 < ‖z T‖ := hM0.trans hzM
    have hkc : k / T < c / 2 := by
      rw [div_lt_iff₀ hc0] at hT1
      rw [div_lt_iff₀ hT0]
      linarith
    have haS1 : c / 2 ≤ ‖aS‖ := by
      have : conj Z = aS - (k : ℂ) / T := by rw [haS]; ring
      have h := norm_sub_le aS ((k : ℂ) / T)
      rw [← this, hcZ, hkT] at h
      linarith
    have h1 : c / 4 * ‖z T‖ ≤ ‖aS * z T - 1‖ := by
      have h := norm_sub_le (aS * z T - 1) (-1)
      rw [sub_neg_eq_add, sub_add_cancel, norm_neg, norm_one, norm_mul] at h
      have h6 : c / 2 * ‖z T‖ ≤ ‖aS‖ * ‖z T‖ := mul_le_mul_of_nonneg_right haS1 hz0.le
      have h7 : 1 ≤ c / 4 * ‖z T‖ := by
        rw [hM, div_lt_iff₀ hc0] at hzM
        linarith
      linarith
    have hza : ‖z T - a‖ ≤ 4 / c := by
      have h2 : ‖z T - a‖ * (c / 4 * ‖z T‖) ≤ ‖z T‖ := by
        calc _ ≤ ‖z T - a‖ * ‖aS * z T - 1‖ := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
          _ = ‖z T‖ := hnorm
      have h3 : ‖z T - a‖ * (c / 4) ≤ 1 := by
        have : ‖z T - a‖ * (c / 4) * ‖z T‖ ≤ 1 * ‖z T‖ := by linarith
        exact le_of_mul_le_mul_right this hz0
      rw [le_div_iff₀ hc0]
      linarith
    have h5 : z T / T - k = (z T - a + Z) / T := by
      have : (T : ℂ) ≠ 0 := by exact_mod_cast hT0.ne'
      rw [ha]; field_simp; ring
    rw [h5, norm_div, Complex.norm_real, Real.norm_of_nonneg hT0.le, div_lt_iff₀ hT0]
    have h6 := norm_add_le (z T - a) Z
    rw [div_lt_iff₀ hε] at hT4
    linarith

/-- The case `Z = 0` (Verification Guide §12.3): the response quadratic with `a = k T`,
`a⋆ = k / T` is equivalent to `z = T d` with `d² - k d + 1 = 0`. -/
theorem response_zero_Z {k T : ℝ} (hk : k ≠ 0) (hT : T ≠ 0) (z : ℂ) :
    ((k : ℂ) / T) * z ^ 2 - ((k : ℂ) * T) * ((k : ℂ) / T) * z + (k : ℂ) * T = 0 ↔
      (z / T) ^ 2 - k * (z / T) + 1 = 0 := by
  have hT' : (T : ℂ) ≠ 0 := by exact_mod_cast hT
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have key : ((k : ℂ) / T) * z ^ 2 - ((k : ℂ) * T) * ((k : ℂ) / T) * z + (k : ℂ) * T =
      ((k : ℂ) * T) * ((z / T) ^ 2 - k * (z / T) + 1) := by
    field_simp
  rw [key, mul_eq_zero, or_iff_right (mul_ne_zero hk' hT')]

/-- For `k² ≤ 4` (in particular `k = 1, 2`), every root of `d² - k d + 1 = 0` has real part `k/2`. -/
theorem re_eq_of_root {k : ℝ} (hk : k ^ 2 ≤ 4) {d : ℂ} (hd : d ^ 2 - k * d + 1 = 0) :
    d.re = k / 2 := by
  have hre := congrArg Complex.re hd
  have him := congrArg Complex.im hd
  simp [pow_two] at hre him
  -- `him : d.re * d.im + d.im * d.re - k * d.im = 0`, i.e. `d.im (2 d.re - k) = 0`
  have him' : d.im * (2 * d.re - k) = 0 := by linarith
  rcases mul_eq_zero.1 him' with h | h
  · rw [h] at hre
    nlinarith [sq_nonneg (2 * d.re - k)]
  · linarith

/-- **Leading coefficients have nonnegative real part** (Verification Guide §12.3). For `k = 1`
or `2` and any retained sum `Z`, the normalised responses `z T / T` eventually lie within `ε` of a
limit `ξ` that is `0`, `k`, or a root of `d² - k d + 1 = 0`; every such `ξ` has `0 ≤ Re ξ`. -/
theorem response_leading_re_nonneg {k : ℝ} (hk : k = 1 ∨ k = 2) {Z : ℂ} {z : ℝ → ℂ}
    (hz : ∀ᶠ T : ℝ in atTop, ((k : ℂ) / T + conj Z) * z T ^ 2 -
      ((k : ℂ) * T + Z) * ((k : ℂ) / T + conj Z) * z T + ((k : ℂ) * T + Z) = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∃ ξ : ℂ, (ξ = 0 ∨ ξ = k ∨ ξ ^ 2 - k * ξ + 1 = 0) ∧ 0 ≤ ξ.re ∧
      ‖z T / T - ξ‖ < ε := by
  have hk0 : 0 < k := by rcases hk with rfl | rfl <;> norm_num
  have hk4 : k ^ 2 ≤ 4 := by rcases hk with rfl | rfl <;> norm_num
  by_cases hZ : Z = 0
  · subst hZ
    filter_upwards [hz, eventually_gt_atTop 0] with T hq hT
    refine ⟨z T / T, Or.inr (Or.inr ?_), ?_, by simpa using hε⟩
    · refine (response_zero_Z hk0.ne' hT.ne' (z T)).1 ?_
      simpa using hq
    · have hd : (z T / T) ^ 2 - k * (z T / T) + 1 = 0 :=
        (response_zero_Z hk0.ne' hT.ne' (z T)).1 (by simpa using hq)
      rw [re_eq_of_root hk4 hd]; positivity
  · have hc0 : 0 < ‖Z‖ := norm_pos_iff.2 hZ
    filter_upwards [response_asymptotics hk0 hZ hz (ε := min ε ‖Z‖⁻¹) (by positivity),
      eventually_gt_atTop (2 / (ε * ‖Z‖))] with T h hT
    have hT0 : 0 < T := lt_of_le_of_lt (by positivity) hT
    rcases h with h | h
    · exact ⟨k, Or.inr (Or.inl rfl), by simp [hk0.le], lt_of_lt_of_le h (min_le_left _ _)⟩
    · refine ⟨0, Or.inl rfl, le_rfl, ?_⟩
      -- `z T` is close to `1 / conj Z`, hence bounded, so `z T / T` is small
      have hb : ‖z T‖ < 2 * ‖Z‖⁻¹ := by
        have h1 := norm_le_insert' (z T) (conj Z)⁻¹
        have h2 : ‖(conj Z)⁻¹‖ = ‖Z‖⁻¹ := by rw [norm_inv, Complex.norm_conj]
        have h3 : min ε ‖Z‖⁻¹ ≤ ‖Z‖⁻¹ := min_le_right _ _
        rw [h2] at h1
        linarith
      rw [sub_zero, norm_div, Complex.norm_real, Real.norm_of_nonneg hT0.le, div_lt_iff₀ hT0]
      rw [div_lt_iff₀ (by positivity)] at hT
      have : 2 * ‖Z‖⁻¹ * ‖Z‖ = 2 := by field_simp
      nlinarith

/-! ## §13.1: H–H adjacency -/

/-- The ring identity behind (H1): eliminating the shared unit vector `u` (with conjugate `u'`). -/
theorem hh_identity_ring {R : Type*} [CommRing R] {a a' b b' u u' : R}
    (h0 : u * u' = 1) (h1 : u * a' + u' * a + a * a' = 0) (h2 : u * b' + u' * b - b * b' = 0) :
    a * a' * (b * b') * ((a + b) * (a' + b')) + (a * b' - a' * b) ^ 2 = 0 := by
  linear_combination (-(a' * b - a * b') ^ 2) * h0 +
    (a' * b' * (a + b) * b - u * (a' * b - a * b') * b') * h1 +
    (-(a' * b' * (a + b) * a) + u * (a' * b - a * b') * a') * h2

/-- (H1): if three unit circles centred at `0`, `-a` and `b` pass through a common point `w`, then
`a ā b b̄ (a + b)(ā + b̄) + (a b̄ - ā b)² = 0` (the circumradius identity, degenerate cases
included). -/
theorem hh_identity {w a b : ℂ} (hw : ‖w‖ = 1) (ha : ‖w + a‖ = 1) (hb : ‖w - b‖ = 1) :
    a * conj a * (b * conj b) * ((a + b) * (conj a + conj b)) + (a * conj b - conj a * b) ^ 2 =
      0 := by
  have h0 := mul_conj_eq_one hw
  have h1 := mul_conj_eq_one ha
  have h2 := mul_conj_eq_one hb
  rw [map_add] at h1
  rw [map_sub] at h2
  exact hh_identity_ring h0 (by linear_combination h1 - h0) (by linear_combination h0 - h2)

/-- (H1) in the notation of the Guide: `a = k ζ + Z`, `b = l ζ + W`, `a⋆ = k/ζ + conj Z`,
`b⋆ = l/ζ + conj W`, and `a a⋆ b b⋆ (a + b)(a⋆ + b⋆) + (a b⋆ - a⋆ b)² = 0`. -/
theorem hh_identity_star {ζ Z W w : ℂ} (k l : ℝ) (hζ : ‖ζ‖ = 1) (hw : ‖w‖ = 1)
    (ha : ‖w + ((k : ℂ) * ζ + Z)‖ = 1) (hb : ‖w - ((l : ℂ) * ζ + W)‖ = 1) :
    ((k : ℂ) * ζ + Z) * ((k : ℂ) / ζ + conj Z) * (((l : ℂ) * ζ + W) * ((l : ℂ) / ζ + conj W)) *
        ((((k : ℂ) * ζ + Z) + ((l : ℂ) * ζ + W)) * (((k : ℂ) / ζ + conj Z) +
          ((l : ℂ) / ζ + conj W))) +
      (((k : ℂ) * ζ + Z) * ((l : ℂ) / ζ + conj W) - ((k : ℂ) / ζ + conj Z) *
        ((l : ℂ) * ζ + W)) ^ 2 = 0 := by
  have := hh_identity hw ha hb
  rwa [conj_response hζ, conj_response hζ] at this

/-- The case `W = -Z` of (H1): with `r = |Z|` and `x = Re (ζ conj Z)`, the (H1) expression equals
`(k + l)² ((k² + r²)(l² + r²) - 4r² + 2(k(l² + r²) - l(k² + r²)) x + 4(1 - k l) x²)`. -/
theorem hh_identity_opposite {ζ Z : ℂ} (k l : ℝ) (hζ : ‖ζ‖ = 1) :
    ((k : ℂ) * ζ + Z) * conj ((k : ℂ) * ζ + Z) * (((l : ℂ) * ζ - Z) * conj ((l : ℂ) * ζ - Z)) *
        ((((k : ℂ) * ζ + Z) + ((l : ℂ) * ζ - Z)) *
          (conj ((k : ℂ) * ζ + Z) + conj ((l : ℂ) * ζ - Z))) +
      (((k : ℂ) * ζ + Z) * conj ((l : ℂ) * ζ - Z) - conj ((k : ℂ) * ζ + Z) *
        ((l : ℂ) * ζ - Z)) ^ 2 =
    (((k + l) ^ 2 * ((k ^ 2 + ‖Z‖ ^ 2) * (l ^ 2 + ‖Z‖ ^ 2) - 4 * ‖Z‖ ^ 2 +
      2 * (k * (l ^ 2 + ‖Z‖ ^ 2) - l * (k ^ 2 + ‖Z‖ ^ 2)) * (ζ * conj Z).re +
      4 * (1 - k * l) * (ζ * conj Z).re ^ 2) : ℝ) : ℂ) := by
  have hζ0 := ne_zero_of_norm_eq_one hζ
  have hx : (((ζ * conj Z).re : ℝ) : ℂ) = (ζ * conj Z + ζ⁻¹ * Z) / 2 := by
    rw [Complex.re_eq_add_conj, map_mul, Complex.conj_conj, conj_eq_inv hζ]
  have hr : ((‖Z‖ : ℝ) : ℂ) ^ 2 = Z * conj Z := by
    rw [← Complex.ofReal_pow]; exact norm_sq_eq_mul_conj Z
  simp only [map_add, map_sub, map_mul, Complex.conj_ofReal, conj_eq_inv hζ]
  push_cast
  rw [hx, hr]
  field_simp
  ring

/-! ## §13.5: the cap polynomial (H2) -/

/-- The polynomial of (H2), `ζ² (|k ζ + ζ² conj v + Z|² - 1)` written as a polynomial in `ζ`. -/
noncomputable def capPoly (k : ℝ) (v Z : ℂ) : ℂ[X] :=
  (C (k : ℂ) * X + C (conj v) * X ^ 2 + C Z) * (C (k : ℂ) * X + C v + C (conj Z) * X ^ 2) - X ^ 2

/-- On the unit circle, `capPoly` evaluates to `ζ² (|k ζ + ζ² conj v + Z|² - 1)`. -/
theorem capPoly_eval {ζ : ℂ} (hζ : ‖ζ‖ = 1) (k : ℝ) (v Z : ℂ) :
    (capPoly k v Z).eval ζ = ζ ^ 2 * (((‖(k : ℂ) * ζ + ζ ^ 2 * conj v + Z‖ ^ 2 - 1 : ℝ)) : ℂ) := by
  have hζ0 := ne_zero_of_norm_eq_one hζ
  push_cast
  rw [← Complex.ofReal_pow, norm_sq_eq_mul_conj]
  simp only [capPoly, eval_sub, eval_mul, eval_add, eval_C, eval_X, eval_pow, map_add, map_mul,
    map_pow, Complex.conj_ofReal, Complex.conj_conj, conj_eq_inv hζ]
  field_simp

/-- The `ζ²` coefficient of `capPoly` (the constant Fourier coefficient of (H2)) is
`k² + |v|² + |Z|² - 1`. -/
theorem capPoly_coeff_two (k : ℝ) (v Z : ℂ) :
    (capPoly k v Z).coeff 2 = (k : ℂ) ^ 2 + v * conj v + Z * conj Z - 1 := by
  have : capPoly k v Z = C (conj v * conj Z) * X ^ 4 + C ((k : ℂ) * conj Z + (k : ℂ) * conj v) * X ^ 3 +
      C ((k : ℂ) ^ 2 + v * conj v + Z * conj Z - 1) * X ^ 2 + C ((k : ℂ) * v + (k : ℂ) * Z) * X +
      C (Z * v) := by
    simp only [capPoly, map_add, map_mul, map_sub, map_pow, map_one]
    ring
  rw [this]
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
  norm_num

/-- (H2) pins the direction: for `|v| = 1` and `k ≠ 0` the polynomial `capPoly` is nonzero,
because its `ζ²` coefficient is `k² + |Z|² > 0`. -/
theorem capPoly_ne_zero {k : ℝ} (hk : k ≠ 0) {v : ℂ} (hv : ‖v‖ = 1) (Z : ℂ) :
    capPoly k v Z ≠ 0 := by
  intro h
  have h2 := capPoly_coeff_two k v Z
  rw [h, coeff_zero, mul_conj_eq_one hv, ← norm_sq_eq_mul_conj] at h2
  have h3 : ((k ^ 2 + ‖Z‖ ^ 2 : ℝ) : ℂ) = 0 := by push_cast at h2 ⊢; linear_combination -h2
  have h4 : k ^ 2 + ‖Z‖ ^ 2 = 0 := by exact_mod_cast h3
  have : 0 < k ^ 2 := by positivity
  nlinarith [sq_nonneg ‖Z‖]

end QuadraticResponse

end Erdos99
end

end QuadraticResponseAlgebra

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `Overview`
-/

section Overview

/-!
# Erdős Problem 99 under finite multiplicity

This file sets up the formalization of the manuscript *"Erdős 99 under finite multiplicity"*
(`FiniteMultiplicity.pdf`).

## The problem

Erdős Problem 99 asks: let `A ⊆ ℝ²` be a set of `n` points with minimum distance equal to `1`,
chosen to minimise the diameter of `A`. If `n` is sufficiently large, must there be three points
of `A` forming an equilateral triangle of side `1`?  This is `Erdos99.Erdos99Conjecture` below.

## Scope: this is a partial result

The manuscript does **not** prove Erdős Problem 99 in full.  It proves it only under the
additional hypothesis that `h(n)` is finite (Theorem 1.1), where `h(n)` is the quantity of
Erdős Problem 103: the number of incongruent sets of `n` points in `ℝ²` achieving the minimal
diameter (formalized as `Erdos99.numOptimalClasses`).  The case `h(n) = ∞` is explicitly left open by the manuscript, and nothing in
this file claims it.  Accordingly:

* `Erdos99.Erdos99Conjecture` is only a *definition* (a `Prop`) stating the full problem; it is
  never asserted as a theorem here.
* `Erdos99.erdos99_finite_multiplicity` (Theorem 1.1) carries the hypothesis
  `numOptimalClasses n < ⊤`, i.e. `h(n) < ∞`, for each `n`.
* `Erdos99.erdos99_of_finite_multiplicity` derives `Erdos99Conjecture` only from the extra
  assumption that `h(n) < ∞` for all sufficiently large `n`; that assumption is not proved.

## Structure

The development follows the sections of the manuscript.  All steps are proved; the main theorem (now in
`Erdos99.lean`) is assembled from them.  The basic
definitions and the (fully proved) results of §1 are in `Basic`; the
planar diameter-graph bound `t ≤ b` is proved in `DiamGraph`, and the
triangular-lattice comparison of Lemma 3.1 in `TriLattice`.  Further
supporting files:

* `LinAlg`, `Rows`: the positive-span row
  count behind Corollary 2.5 and Lemma 2.2.
* `Release`: finite multiplicity excludes one-parameter families of
  optimal sets ("releases"); boundary points are diameter endpoints (Lemma 2.1).
* `Pinned`: pinned locking and the count `m - t_B ≥ 2(n - b) + 1`.
* `Tracks`, `RhombusGeom`,
  `TrackLength`: rhombi and tracks; two tracks per rhombus, the
  crossing graph is triangle-free, and `r(T) ≤ D / a*` (Lemma 3.3).
* `TrackCross`: two tracks cross at most once, and `s + 2q ≤ m`
  (Lemma 3.3).
* `HullPerimeter`: `b ≤ π D` via Cauchy's formula (Lemma 3.1).
* `Isodiametric`: the planar isodiametric inequality
  `|conv X| ≤ π D² / 4` (Lemma 3.1).
* `Density`: truncated Voronoi cells have area `≥ √3/2`, giving the
  density bound `n ≤ c D² + O(D)` (`card_le_density`, Lemma 3.1).

* `PlaneFaces`, `FaceCount`: Euler-type face
  counting for the plane unit-distance graph, giving `m ≤ 2n - 2` and `3m + 5 ≤ 5n + q`
  (used in Lemma 2.2, `rhombi_card_ge`, which is proved).

The main theorem `erdos99_finite_multiplicity` and the lemmas `track_count`,
`exists_countingWitness` (§§3.4–6) that it uses are stated and proved in
`Erdos99.lean`: `track_count` is derived there from
`track_count_assembled`, which is fully proved (its last ingredients, the algebraic steps of §§13.2–13.3, are in
`FlaggedExclusion`).  The lemma `first_order_locking` records a manuscript statement that the
formal proof of Theorem 1.1 does not use.  The connectivity of the
contact graph (`contactGraph_connected`, Lemma 2.1) is proved, in
`Connected` (with the planar crossing argument in
`Winding`, `Crux`, `Arc` and `ContactRelease`).  (`card_le_density`, Lemma 3.1's density bound, is proved.)

* §1  Statement, optimal configurations, `h(n)`.
* §2  Contact geometry and first-order locking (Lemmas 2.1–2.4, Corollary 2.5).
* §3  Metric estimates, rhombi and tracks (Lemmas 3.1–3.3), Mantel's bound.
* §§3.4–6  The counting data of Propositions 4.5, 5.6 and Lemma 6.1, packaged as
  `Erdos99.CountingWitness`.
* §7  The final numerical contradiction.
-/

open scoped BigOperators Real
open Filter

@[expose] public noncomputable section

open Classical

namespace Erdos99
/-- Lemma 2.1 (unit edges do not cross).  For a separated set, two unit segments with four
distinct endpoints are disjoint.  At a common point `p`, the four distances from `p` to the
endpoints are forced to equal `1/2`, so `p` is the midpoint of both `ab` and `ac`, whence `b = c`. -/
lemma unit_segments_disjoint {X : Finset Plane} (hX : IsSeparated X) {a b c d : Plane}
    (ha : a ∈ X) (hb : b ∈ X) (hc : c ∈ X) (hd : d ∈ X)
    (hab : dist a b = 1) (hcd : dist c d = 1)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    Disjoint (segment ℝ a b) (segment ℝ c d) := by
  rw [Set.disjoint_left]
  intro p hp1 hp2
  have e1 := dist_add_dist_of_mem_segment hp1
  have e2 := dist_add_dist_of_mem_segment hp2
  rw [dist_comm c p] at e2
  have h1 := hX a ha c hc hac
  have h2 := hX a ha d hd had
  have h3 := hX b hb c hc hbc
  have h4 := hX b hb d hd hbd
  have t1 := dist_triangle a p c
  have t2 := dist_triangle a p d
  have t3 := dist_triangle b p c
  have t4 := dist_triangle b p d
  rw [dist_comm b p] at t3 t4
  have s1 : dist a p = 1/2 := by linarith
  have s2 : dist p b = 1/2 := by linarith
  have s3 : dist p c = 1/2 := by linarith
  have hpb : p - a = b - p := by
    have hr : SameRay ℝ (p - a) (b - p) := by
      rw [sameRay_iff_norm_add]
      simp only [sub_add_sub_cancel', ← dist_eq_norm]
      rw [dist_comm p a, dist_comm b p, dist_comm b a]; linarith
    exact hr.eq_of_norm_eq
      (by rw [← dist_eq_norm, ← dist_eq_norm, dist_comm p a, dist_comm b p]; linarith)
  have hpc : p - a = c - p := by
    have hr : SameRay ℝ (p - a) (c - p) := by
      rw [sameRay_iff_norm_add]
      simp only [sub_add_sub_cancel', ← dist_eq_norm]
      rw [dist_comm p a, dist_comm c p, dist_comm c a]; linarith
    exact hr.eq_of_norm_eq
      (by rw [← dist_eq_norm, ← dist_eq_norm, dist_comm p a, dist_comm c p]; linarith)
  exact hbc (by rw [hpb] at hpc; simpa using hpc)

/-- Lemma 2.1 (boundary points).  Under finite multiplicity, every point of an optimal set on the
boundary of its convex hull is a hull vertex and an endpoint of a diameter. -/
lemma boundary_point_hullVertex_and_diam_endpoint :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      ∀ x ∈ X, x ∈ frontier (convexHull ℝ (X : Set Plane)) →
        x ∈ hullVertices X ∧ ∃ y ∈ X, dist x y = diam X := by
  filter_upwards [eventually_not_collinear, eventually_ge_atTop 2] with n hcol hn hfm X hX x hx hfr
  obtain ⟨y, hy, hd⟩ := exists_diam_partner_of_frontier hn hfm hX (hcol X hX) hx hfr
  have hxy : x ≠ y := by
    rintro rfl; rw [dist_self] at hd; exact (hX.diam_pos hn).ne hd
  exact ⟨mem_hullVertices_of_diam hx hy hxy hd, y, hy, hd⟩

/-- Lemma 2.1 (connectivity).  Under finite multiplicity the contact graph of an optimal set is
connected. -/
lemma contactGraph_connected :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      (contactGraph X).Connected := by
  filter_upwards [eventually_ge_atTop 2] with n hn hfm X hX
  exact contactGraph_connected_of_optimal hn hfm hX

/-- Lemma 2.4 together with finite multiplicity: first-order locking.  Every velocity that does
not shorten unit pairs and does not lengthen diameter pairs is trivial.  Derived from
`first_order_locking_of` (`FirstOrderLocking`, WP4). -/
lemma first_order_locking :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      ∀ v : Plane → Plane,
        (∀ x ∈ X, ∀ y ∈ X, dist x y = 1 → 0 ≤ inner ℝ (x - y) (v x - v y)) →
        (∀ x ∈ X, ∀ y ∈ X, dist x y = diam X → inner ℝ (x - y) (v x - v y) ≤ 0) →
        IsTrivialVelocity X v := by
  filter_upwards [eventually_ge_atTop 2, eventually_not_collinear] with n hn hcol hfm X hX v hU hT
  exact first_order_locking_of hn hfm hX (hcol X hX) v hU hT

/-- Corollary 2.5 (locking count), in row-count form: the `m + t` active rows positively span the
`(2n - 3)`-dimensional slice, so `m + t ≥ 2n - 2`. -/
lemma locking_count :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      2 * n ≤ (unitEdges X).card + (diamPairs X).card + 2 := by
  filter_upwards [first_order_locking, tendsto_minDiam.eventually_ge_atTop 2,
    eventually_ge_atTop 2] with n hl hD hn hfm X hX
  have h := card_rows_of_locking (X := X) (by rw [hX.1.1]; exact hn)
    (by rw [hX.diam_eq]; linarith) (hl hfm X hX)
  rwa [hX.1.1] at h

/-! ## §3. Density, rhombi and tracks -/

/-- Lemma 3.1 (Oler's inequality side): `n ≤ c D² + O(D)` for optimal sets.  The proof (truncated
Voronoi cells of area `≥ √3/2` packed into a set of diameter `D + 2`, then the isodiametric
inequality) is in `Density`; one may take `C = 8c`. -/
lemma card_le_density :
    ∃ C : ℝ, ∀ᶠ n in atTop, ∀ X, IsOptimal n X → (n : ℝ) ≤ cDensity * diam X ^ 2 + C * diam X := by
  refine ⟨8 * cDensity, ?_⟩
  filter_upwards [eventually_ge_atTop 2] with n hn X hX
  have h := card_le_density_of_separated hX.1.2 (by rw [hX.1.1]; exact hn)
  rwa [hX.1.1] at h

/-- Lemma 3.1: `b ≤ Per H ≤ π D`.

The hypothesis `2 ≤ n` was added to the earlier statement: for `n = 1` the single point is a hull
vertex while the diameter is `0`, so the bound fails.  The proof (Cauchy's formula on the hull
edges) is in `HullPerimeter`. -/
lemma hullVertices_card_le {n : ℕ} {X : Finset Plane} (hX : IsOptimal n X) (hn : 2 ≤ n) :
    ((hullVertices X).card : ℝ) ≤ π * diam X :=
  hullVertices_card_le_pi_mul_diam hX.1.2 (by rw [hX.1.1]; exact hn)

/-- Lemma 3.1, lattice side, rewritten: `c D² ≤ n` for an optimal `n`-point set. -/
lemma cDensity_mul_le {n : ℕ} {X : Finset Plane} (hX : IsOptimal n X) (hn : 1 ≤ n) :
    cDensity * diam X ^ 2 ≤ n := by
  have h := minDiam_sq_le n hn
  rw [← hX.diam_eq] at h
  have h3 : (0:ℝ) < √3 := by positivity
  unfold cDensity
  unfold aStar at h
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  rw [le_div_iff₀ Real.pi_pos] at h
  nlinarith

/-- Lemma 2.2 (pinned counting): `m - t_B ≥ 2(n - b) + 1`, where `t_B` counts unit pairs with
both endpoints on the hull. -/
lemma pinned_count :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      2 * (n - (hullVertices X).card) + 1 + ((unitEdges X).filter
          (fun e => ∀ x ∈ e, x ∈ hullVertices X)).card ≤ (unitEdges X).card := by
  filter_upwards [tendsto_minDiam.eventually_ge_atTop 4, eventually_ge_atTop 2] with n hD hn hfm X hX
  have hb := hullVertices_card_le hX hn
  have hc := cDensity_mul_le hX (by omega)
  rw [← hX.diam_eq] at hD
  have h3 : √3 < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h3' : (0 : ℝ) < √3 := by positivity
  have hlt : π * diam X < cDensity * diam X ^ 2 := by
    unfold cDensity
    rw [div_mul_eq_mul_div, lt_div_iff₀ (by positivity)]
    have := mul_pos (mul_pos Real.pi_pos (by linarith : (0 : ℝ) < diam X))
      (by linarith : (0 : ℝ) < diam X - 2 * √3)
    nlinarith
  have : ((hullVertices X).card : ℝ) < n := by linarith
  exact pinned_count_of hn hfm hX (by exact_mod_cast this)

/-- Lemma 2.2 (pinned counting combined with Euler's formula for the plane contact graph):
`m = 2n - 2 - (ℓ + σ)/2 ≤ 2n - 2` and `q = n - O(D)` rhombi.

(The bound `m ≤ 2n - 2` is part of the manuscript's Lemma 2.2; it is recorded here because it is
used to count tracks in `tracks_card_le`.) -/
lemma rhombi_card_ge :
    ∃ C : ℝ, ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      ¬ HasUnitTriangle X →
        (unitEdges X).card + 2 ≤ 2 * n ∧ (n : ℝ) - C * diam X ≤ (rhombi X).card := by
  refine ⟨6 * π, ?_⟩
  filter_upwards [pinned_count, eventually_ge_atTop 2] with n hpin hn hfm X hX htri
  have hcard : X.card = n := hX.1.1
  have hne : X.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨c1, c2⟩ := unitEdges_rhombi_counts hX.1.2 htri hne
  rw [hcard] at c1 c2
  refine ⟨c1, ?_⟩
  have hp := hpin hfm X hX
  have hbn : (hullVertices X).card ≤ n := hcard ▸ Finset.card_filter_le _ _
  have hb := hullVertices_card_le hX hn
  have hm : 2 * n + 1 ≤ (unitEdges X).card + 2 * (hullVertices X).card := by omega
  have hm' : (2 * n + 1 : ℝ) ≤ (unitEdges X).card + 2 * (hullVertices X).card := by
    exact_mod_cast hm
  have c2' : (3 * (unitEdges X).card + 5 : ℝ) ≤ 5 * n + (rhombi X).card := by exact_mod_cast c2
  nlinarith

/-- Equation (1): `q ≥ c D² - o(D²)`. -/
lemma rhombi_card_lower (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      ¬ HasUnitTriangle X → (cDensity - ε) * diam X ^ 2 ≤ (rhombi X).card := by
  obtain ⟨C, hC⟩ := rhombi_card_ge
  filter_upwards [hC, tendsto_minDiam.eventually_ge_atTop (|C| / ε + 1),
    eventually_ge_atTop 2] with n h1 h2 hn hfm X hX htri
  have hq := (h1 hfm X hX htri).2
  have hc := cDensity_mul_le hX (by omega)
  rw [← hX.diam_eq] at h2
  have hD : 0 < diam X := hX.diam_pos hn
  have : |C| ≤ ε * diam X := by
    have := (div_le_iff₀ hε).1 (by linarith : |C| / ε ≤ diam X); linarith
  have : C * diam X ≤ ε * diam X ^ 2 := by
    nlinarith [le_abs_self C]
  linarith

/-- Lemma 3.3: every rhombus is crossed by exactly two distinct tracks. -/
lemma rhombus_two_tracks :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ R ∈ rhombi X, ∃ T ∈ tracks X, ∃ T' ∈ tracks X, T ≠ T' ∧
        ∀ T'' ∈ tracks X, Crosses T'' R ↔ (T'' = T ∨ T'' = T') :=
  Eventually.of_forall fun _ _ _ hX htri _ hR => rhombus_two_tracks_of_separated hX.1.2 htri hR

/-- Lemma 3.3: two distinct tracks cross at most once (the crossing graph is simple). -/
lemma tracks_cross_at_most_once :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ T ∈ tracks X, ∀ T' ∈ tracks X, T ≠ T' →
        ((rhombi X).filter (fun R => Crosses T R ∧ Crosses T' R)).card ≤ 1 :=
  Eventually.of_forall fun _ _ _ hX htri _ hT _ hT' hne =>
    tracks_cross_at_most_once_of_separated hX.1.2 htri hT hT' hne

/-- Lemma 3.3: the crossing graph is triangle-free. -/
lemma crossingGraph_cliqueFree :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      (crossingGraph X).CliqueFree 3 :=
  Eventually.of_forall fun _ _ _ hX htri => crossingGraph_cliqueFree_of_separated hX.1.2 htri

/-- Lemma 3.3: `r(T) ≤ D / a*`. -/
lemma trackLength_le :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ T ∈ tracks X, (trackLength X T : ℝ) ≤ diam X / aStar :=
  Eventually.of_forall fun _ _ _ hX htri _ hT => trackLength_le_of_separated hX.1.2 htri hT

/-- Lemma 3.3: there are `s = O(D)` tracks. -/
lemma tracks_card_le :
    ∃ C : ℝ, ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      ¬ HasUnitTriangle X → ((tracks X).card : ℝ) ≤ C * diam X := by
  -- `s + 2q ≤ m` (tracks partition the rhombus edges, `r(T) + 1 ≤ |T|`, `∑ r(T) = 2q`),
  -- `m ≤ 2n - 2` and `q ≥ n - C D`
  obtain ⟨C, hC⟩ := rhombi_card_ge
  refine ⟨2 * C, ?_⟩
  filter_upwards [hC] with n h hfm X hX htri
  obtain ⟨hm, hq⟩ := h hfm X hX htri
  have hs := card_tracks_add_two_mul_card_rhombi_le hX.1.2 htri
  have hm' : ((unitEdges X).card : ℝ) + 2 ≤ 2 * n := by exact_mod_cast hm
  have hs' : ((tracks X).card : ℝ) + 2 * (rhombi X).card ≤ (unitEdges X).card := by
    exact_mod_cast hs
  linarith

/-- Choosing the cutoff by finite pigeonhole (Verification Guide §11; work package WP2 of
`TRACK_COUNT_REVISED_PLAN.md`). There is a constant `Cs` such that for every `δ > 0`, every number
`J` of shells with `Cs < J δ` and every antitone sequence `a` of cutoff fractions, eventually every
admissible configuration has an index `i < J` whose shell — the tracks with at least `a (i+1) D`
but fewer than `a i D` rhombi — contains at most `δ D` tracks. -/
lemma exists_sparse_track_shell :
    ∃ Cs : ℝ, ∀ δ : ℝ, 0 < δ → ∀ J : ℕ, Cs < J * δ → ∀ a : ℕ → ℝ, Antitone a →
      ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
        ∃ i < J, ((longTracks X (a (i + 1) * diam X) \ longTracks X (a i * diam X)).card : ℝ) ≤
          δ * diam X := by
  obtain ⟨C, hC⟩ := tracks_card_le
  refine ⟨C, fun δ _ J hJ a ha => ?_⟩
  filter_upwards [hC, eventually_ge_atTop 2] with n h hn hfm X hX htri
  obtain ⟨i, hi, hle⟩ := exists_sparse_shell (tracks X) (fun T => (trackLength X T : ℝ)) ha
    (hX.diam_pos hn) (h hfm X hX htri) hJ
  refine ⟨i, hi, le_trans ?_ hle⟩
  have hsub : longTracks X (a (i + 1) * diam X) \ longTracks X (a i * diam X) ⊆
      (tracks X).filter (fun T => a (i + 1) * diam X ≤ (trackLength X T : ℝ) ∧
        (trackLength X T : ℝ) < a i * diam X) := by
    intro T hT
    simp only [longTracks, Finset.mem_sdiff, Finset.mem_filter, not_and, not_le] at hT ⊢
    exact ⟨hT.1.1, hT.1.2, hT.2 hT.1.1⟩
  exact_mod_cast Finset.card_le_card hsub

/-- Mantel's bound: a triangle-free simple graph on `v` vertices has at most `v² / 4` edges. -/
lemma mantel {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) : (G.edgeFinset.card : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 / 4 := by
  -- Turán's theorem for `r = 2`, as proved in Mathlib
  obtain ⟨H, _, maxH⟩ := SimpleGraph.exists_isTuranMaximal (V := V) (r := 2) (by norm_num)
  have h1 : G.edgeFinset.card ≤ H.edgeFinset.card := by convert maxH.2 hG
  have h2 := ((SimpleGraph.isTuranMaximal_iff_nonempty_iso_turanGraph (by norm_num)).mp
    maxH).some.card_edgeFinset_eq
  have h3 := SimpleGraph.mul_card_edgeFinset_turanGraph_le (n := Fintype.card V) (r := 2)
  rw [← h2] at h3
  have : 4 * G.edgeFinset.card ≤ Fintype.card V ^ 2 := by omega
  have : (4 * G.edgeFinset.card : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by exact_mod_cast this
  linarith

/-- Lemma 3.3 combined with Mantel's bound: the rhombi all of whose tracks lie in a set `S` of
tracks number at most `|S|² / 4`. -/
lemma rhombi_inside_card_le :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ S ⊆ tracks X,
        (((rhombi X).filter (fun R => ∀ T ∈ tracks X, Crosses T R → T ∈ S)).card : ℝ) ≤
          (S.card : ℝ) ^ 2 / 4 := by
  filter_upwards [tracks_cross_at_most_once] with n hcross hfm X hX htri S hS
  let G : SimpleGraph {T // T ∈ S} :=
    (crossingGraph X).comap (Function.Embedding.subtype (· ∈ S))
  have hG : G.CliqueFree 3 := (crossingGraph_cliqueFree_of_separated hX.1.2 htri).comap
    (SimpleGraph.Embedding.comap _ _)
  have hM := mantel G hG
  rw [Fintype.card_coe] at hM
  refine le_trans ?_ hM
  norm_cast
  refine Finset.card_le_card_of_forall_subsingleton
    (fun R (p : Sym2 {T // T ∈ S}) => ∀ T ∈ p, Crosses T.1 R) ?_ ?_
  · intro R hR
    obtain ⟨hR, hin⟩ := Finset.mem_filter.1 hR
    obtain ⟨T, hT, T', hT', hne, hiff⟩ := rhombus_two_tracks_of_separated hX.1.2 htri hR
    have c1 := (hiff T hT).2 (Or.inl rfl)
    have c2 := (hiff T' hT').2 (Or.inr rfl)
    refine ⟨s(⟨T, hin T hT c1⟩, ⟨T', hin T' hT' c2⟩), ?_, ?_⟩
    · rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact ⟨hne, hT, hT', R, hR, c1, c2⟩
    · intro U hU
      rcases Sym2.mem_iff.1 hU with rfl | rfl
      · exact c1
      · exact c2
  · intro p hp R1 hR1 R2 hR2
    induction p using Sym2.ind with
    | h A B =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hp
      obtain ⟨hne, hA, hB, -⟩ := hp
      have hsub := hcross hfm X hX htri A.1 hA B.1 hB hne
      have m1 : R1 ∈ (rhombi X).filter (fun R => Crosses A.1 R ∧ Crosses B.1 R) :=
        Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hR1.1).1, hR1.2 A (Sym2.mem_mk_left _ _),
          hR1.2 B (Sym2.mem_mk_right _ _)⟩
      have m2 : R2 ∈ (rhombi X).filter (fun R => Crosses A.1 R ∧ Crosses B.1 R) :=
        Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hR2.1).1, hR2.2 A (Sym2.mem_mk_left _ _),
          hR2.2 B (Sym2.mem_mk_right _ _)⟩
      exact Finset.card_le_one.1 hsub _ m1 _ m2

/-! ## §§3.4–6. Boundary propagation, the two-fifths inequality and the annular cost

The output of Lemma 3.4 through Lemma 6.1 used in §7 is packaged in `CountingWitness`.  The
counts `f, β, c₂, C₁, A` refer to exceptional faces, cycle rank, two-edge hull returns and
activated pentagons; at this stage they are recorded only through the inequalities the
manuscript proves for them.  The error terms `o(D)`, `o(D²)` are expressed uniformly with a
parameter `ε`. -/

/-- The counting data of Proposition 4.5, Proposition 5.6 and Lemma 6.1 for a configuration `X`,
with error parameter `ε`.  `long` is the set of tracks remaining after deletion of the short
tracks (`R = |long|`), `sel` the selected tracks of §6 (`P = |sel|`). -/
structure CountingWitness (X : Finset Plane) (ε : ℝ) where
  /-- Number of exceptional faces. -/
  f : ℕ
  /-- Total cycle rank of the hull-containing components of the short terminal graph. -/
  β : ℕ
  /-- Number of two-edge hull returns. -/
  c₂ : ℕ
  /-- Two-edge returns with exactly one short port. -/
  C₁ : ℕ
  /-- Number of activated pentagons. -/
  A : ℕ
  /-- The remaining (non-short) tracks. -/
  long : Finset (Finset (Sym2 Plane))
  /-- The selected tracks. -/
  sel : Finset (Finset (Sym2 Plane))
  long_subset : long ⊆ tracks X
  sel_subset : sel ⊆ long
  /-- (12), Proposition 4.5: `R = f - β + o(D)`. -/
  abs_R_sub : |(long.card : ℝ) - ((f : ℝ) - β)| ≤ ε * diam X
  /-- (12), Proposition 4.5: `f + c₂ ≤ π D + o(D)`. -/
  f_add_c₂_le : (f : ℝ) + c₂ ≤ π * diam X + ε * diam X
  /-- (13), Proposition 5.6 (joint two-fifths inequality). -/
  two_fifths : 2 / 5 * (f : ℝ) + A - ε * diam X ≤ β + 2 / 5 * (sel.card : ℝ) + 2 / 5 * c₂ + 1 / 5 * C₁
  C₁_le_c₂ : C₁ ≤ c₂
  /-- Deleting the short tracks loses only `o(D²)` rhombi. -/
  short_loss : (((rhombi X).filter
      (fun R => ∃ T ∈ tracks X, T ∉ long ∧ Crosses T R)).card : ℝ) ≤ ε * diam X ^ 2
  /-- (11), Lemma 6.1: `Q_P ≤ D P / 2 + o(D²)`. -/
  annular_linear : (((rhombi X).filter (fun R => ∃ T ∈ sel, Crosses T R)).card : ℝ) ≤
      diam X * sel.card / 2 + ε * diam X ^ 2
  /-- (11), Lemma 6.1: `Q_P ≤ c D² / 4 + o(D²)`. -/
  annular_quadratic : (((rhombi X).filter (fun R => ∃ T ∈ sel, Crosses T R)).card : ℝ) ≤
      cDensity / 4 * diam X ^ 2 + ε * diam X ^ 2

/-- Lemma 3.1 (roundness, outer half): an optimal configuration lies in a disc of radius
`D/2 + o(D)`.  (The manuscript obtains `D/2 + O(√D)` from Bonnesen's inequality; the proof here,
in `Roundness`, uses a quantitative isodiametric inequality proved by
polar coordinates about a contact point of the smallest enclosing disc.) -/
lemma exists_round_center (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n in atTop, ∀ X, IsOptimal n X →
      ∃ O : Plane, ∀ x ∈ X, dist x O ≤ diam X / 2 + η * diam X :=
  round_center_of_optimal η hη

/- `track_count` (the track count of §§3.4–5) now lives in
`Erdos99.lean`, where it is derived from `track_count_assembled`
(`TrackCountAssembly`); that file imports this one, so it cannot be stated here. -/

/-- Deleting the tracks with fewer than `L` rhombi loses at most `s L` rhombi. -/
lemma rhombi_short_card_le (X : Finset Plane) {L : ℝ} (hL : 0 ≤ L) :
    (((rhombi X).filter (fun R => ∃ T ∈ tracks X, T ∉ longTracks X L ∧ Crosses T R)).card : ℝ) ≤
      (tracks X).card * L := by
  set Sh := (tracks X).filter (fun T => T ∉ longTracks X L)
  have hsub : (rhombi X).filter (fun R => ∃ T ∈ tracks X, T ∉ longTracks X L ∧ Crosses T R) ⊆
      Sh.biUnion (fun T => (rhombi X).filter (Crosses T)) := by
    intro R hR
    obtain ⟨hR, T, hT, hl, hc⟩ := Finset.mem_filter.1 hR
    exact Finset.mem_biUnion.2 ⟨T, Finset.mem_filter.2 ⟨hT, hl⟩, Finset.mem_filter.2 ⟨hR, hc⟩⟩
  have h1 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have h2 : ∀ T ∈ Sh, (((rhombi X).filter (Crosses T)).card : ℝ) ≤ L := by
    intro T hT
    obtain ⟨hT, hl⟩ := Finset.mem_filter.1 hT
    have : ¬ L ≤ (trackLength X T : ℝ) := fun h => hl (Finset.mem_filter.2 ⟨hT, h⟩)
    unfold trackLength at this
    linarith
  calc _ ≤ ((∑ T ∈ Sh, ((rhombi X).filter (Crosses T)).card : ℕ) : ℝ) := by exact_mod_cast h1
    _ = ∑ T ∈ Sh, (((rhombi X).filter (Crosses T)).card : ℝ) := by push_cast; rfl
    _ ≤ ∑ T ∈ Sh, L := Finset.sum_le_sum h2
    _ = Sh.card * L := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (tracks X).card * L := by
        gcongr
        exact Finset.filter_subset _ _

/-- Sections 3.4–6 of the manuscript: every large triangle-free optimizer with finite
multiplicity admits the counting data, for every error parameter `ε > 0`.

It is assembled from a supply of centres (`hC`: for all `η, ρ > 0`, eventually a centre of a disc
of radius `D/2 + η D` containing the configuration and satisfying the condition `C ρ`, e.g. the
centre of two-sided roundness), the track count for such centres (`htc`, the form of
`track_count`), the loss from deleting short tracks (`rhombi_short_card_le`) and the annular cost
of the selected tracks (Lemma 6.1, `selected_rhombi_bounds`). -/
lemma exists_countingWitness_of_centre (C : ℝ → Finset Plane → Plane → Prop)
    (hC : ∀ η ρ : ℝ, 0 < η → 0 < ρ → ∀ᶠ n in atTop, ∀ X, IsOptimal n X →
      ∃ O : Plane, (∀ x ∈ X, dist x O ≤ diam X / 2 + η * diam X) ∧ C ρ X O)
    (htc : ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ ρ : ℝ, 0 < ρ ∧
      ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
        ∀ O : Plane, (∀ x ∈ X, dist x O ≤ diam X / 2 + η * diam X) → C ρ X O →
        ∃ L : ℝ, 0 ≤ L ∧ L ≤ ε * diam X ∧ ∃ sel ⊆ longTracks X L,
          (∀ T ∈ sel, IsSelectedTrack O (diam X) η T) ∧
          ((longTracks X L).card : ℝ) - sel.card ≤ 3 / 5 * (π * diam X - sel.card) + ε * diam X)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      Nonempty (CountingWitness X ε) := by
  obtain ⟨Ct, hCt⟩ := tracks_card_le
  set C' := max Ct 1 with hC'
  have hC'1 : 1 ≤ C' := le_max_right _ _
  have hC'0 : 0 < C' := by linarith
  set η := min (1 / 8) (ε / (40 * C')) with hηdef
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hη8 : η ≤ 1 / 8 := min_le_left _ _
  have hηε : η * (40 * C') ≤ ε := by
    have := min_le_right (1 / 8) (ε / (40 * C'))
    rw [← hηdef] at this
    rwa [le_div_iff₀ (by positivity)] at this
  set ε' := min (ε / 2) (ε / C') with hε'def
  have hε' : 0 < ε' := lt_min (by positivity) (by positivity)
  have hε'2 : ε' ≤ ε / 2 := min_le_left _ _
  have hε'C : ε' * C' ≤ ε := by
    have := min_le_right (ε / 2) (ε / C')
    rw [← hε'def] at this
    rwa [le_div_iff₀ hC'0] at this
  obtain ⟨ρ, hρ, htcρ⟩ := htc ε' η hε' hη
  filter_upwards [hCt, hC η ρ hη hρ, htcρ,
    tendsto_minDiam.eventually_ge_atTop (3 / η + 2 / ε), eventually_ge_atTop 2]
    with n hCn hround hcount hDbig hn hfm X hX htri
  rw [← hX.diam_eq] at hDbig
  set D := diam X with hDdef
  have hD : 0 < D := hX.diam_pos hn
  have hs : ((tracks X).card : ℝ) ≤ C' * D :=
    (hCn hfm X hX htri).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hD.le)
  have hDη : 3 ≤ η * D := by
    have : 3 / η ≤ D := by linarith [div_pos (by norm_num : (0:ℝ) < 2) hε]
    rwa [div_le_iff₀ hη, mul_comm] at this
  have hDε : 2 ≤ ε * D := by
    have : 2 / ε ≤ D := by linarith [div_pos (by norm_num : (0:ℝ) < 3) hη]
    rwa [div_le_iff₀ hε, mul_comm] at this
  obtain ⟨O, hO, hCO⟩ := hround X hX
  obtain ⟨L, hL0, hLε, sel, hsel, hselT, hK⟩ := hcount hfm X hX htri O hO hCO
  rw [← hDdef] at hO hLε hK hselT
  have hlongT : longTracks X L ⊆ tracks X := Finset.filter_subset _ _
  have h40 : 40 * η ≤ ε := by
    have : 40 * η * 1 ≤ 40 * η * C' := mul_le_mul_of_nonneg_left hC'1 (by positivity)
    linarith
  obtain ⟨hQ1, hQ2⟩ := selected_rhombi_bounds hX.1.2 htri hD hη.le hη8 hDη
    (by intro x hx; have := hO x hx; linarith) (hsel.trans hlongT) hselT
  set R := (longTracks X L).card
  set P := sel.card
  have hPR : (P : ℝ) ≤ R := by exact_mod_cast Finset.card_le_card hsel
  have hPs : (P : ℝ) ≤ C' * D :=
    le_trans (by exact_mod_cast Finset.card_le_card (hsel.trans hlongT)) hs
  -- the numerical data
  set f := max R ⌊π * D⌋₊ with hfdef
  have hRf : R ≤ f := le_max_left _ _
  have hfl : (⌊π * D⌋₊ : ℝ) ≤ f := by exact_mod_cast le_max_right R ⌊π * D⌋₊
  have hfloor := Nat.lt_floor_add_one (π * D)
  have hfloor' := Nat.floor_le (by positivity : 0 ≤ π * D)
  have hε'D : ε' * D ≤ ε / 2 * D := mul_le_mul_of_nonneg_right hε'2 hD.le
  have hεD0 : 0 ≤ ε * D := by positivity
  have hRle : (R : ℝ) ≤ π * D + ε * D := by linarith
  have hfle : (f : ℝ) ≤ π * D + ε * D := by
    rcases max_choice R ⌊π * D⌋₊ with h | h
    · rw [hfdef, h]; exact hRle
    · rw [hfdef, h]; linarith
  have hcast : ((f - R : ℕ) : ℝ) = f - R := Nat.cast_sub hRf
  refine ⟨⟨f, f - R, 0, 0, 0, longTracks X L, sel, hlongT, hsel, ?_, ?_, ?_, le_refl 0, ?_, ?_,
    ?_⟩⟩
  · rw [hcast, sub_sub_cancel, sub_self, abs_zero]; positivity
  · simpa using hfle
  · rw [hcast]; push_cast; linarith
  · have h := rhombi_short_card_le X hL0
    have h2 : ((tracks X).card : ℝ) * L ≤ C' * D * (ε' * D) :=
      mul_le_mul hs hLε hL0 (by positivity)
    have h3 : C' * D * (ε' * D) ≤ ε * D ^ 2 := by
      have := mul_le_mul_of_nonneg_right hε'C (by positivity : 0 ≤ D ^ 2)
      calc C' * D * (ε' * D) = ε' * C' * D ^ 2 := by ring
        _ ≤ ε * D ^ 2 := this
    linarith
  · have h1 : 20 * η * D * P ≤ ε * D ^ 2 := by
      have h5 := mul_le_mul_of_nonneg_left hPs (by positivity : 0 ≤ 20 * η * D)
      have h4 : 20 * η * C' ≤ ε := by nlinarith
      have h6 := mul_le_mul_of_nonneg_right h4 (by positivity : 0 ≤ D ^ 2)
      calc 20 * η * D * P ≤ 20 * η * D * (C' * D) := h5
        _ = 20 * η * C' * D ^ 2 := by ring
        _ ≤ ε * D ^ 2 := h6
    calc _ ≤ (1 / 2 + 20 * η) * D * P := hQ1
      _ = D * P / 2 + 20 * η * D * P := by ring
      _ ≤ D * P / 2 + ε * D ^ 2 := by linarith
  · have := mul_le_mul_of_nonneg_right h40 (by positivity : 0 ≤ D ^ 2)
    calc _ ≤ (cDensity / 4 + 40 * η) * D ^ 2 := hQ2
      _ = cDensity / 4 * D ^ 2 + 40 * η * D ^ 2 := by ring
      _ ≤ cDensity / 4 * D ^ 2 + ε * D ^ 2 := by linarith

/-- `exists_countingWitness_of_centre` for centres of enclosing discs only (no further condition
on the centre). -/
lemma exists_countingWitness_of
    (htc : ∀ ε η : ℝ, 0 < ε → 0 < η →
      ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
        ∀ O : Plane, (∀ x ∈ X, dist x O ≤ diam X / 2 + η * diam X) →
        ∃ L : ℝ, 0 ≤ L ∧ L ≤ ε * diam X ∧ ∃ sel ⊆ longTracks X L,
          (∀ T ∈ sel, IsSelectedTrack O (diam X) η T) ∧
          ((longTracks X L).card : ℝ) - sel.card ≤ 3 / 5 * (π * diam X - sel.card) + ε * diam X)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      Nonempty (CountingWitness X ε) :=
  exists_countingWitness_of_centre (fun _ _ _ => True)
    (fun η _ hη _ => by
      filter_upwards [exists_round_center η hη] with n h X hX
      obtain ⟨O, hO⟩ := h X hX
      exact ⟨O, hO, trivial⟩)
    (fun ε η hε hη => ⟨1, one_pos, by
      filter_upwards [htc ε η hε hη] with n h hfm X hX htri O hO _
      exact h hfm X hX htri O hO⟩) ε hε

/- `exists_countingWitness` (§§3.4–6 from `track_count`) now lives in
`Erdos99.lean`. -/

/-! ## §7. The contradiction -/

/-- The convex function `F(x) = (9/100)(π - x)² + x/2` of §7. -/
def finalF (x : ℝ) : ℝ := 9 / 100 * (π - x) ^ 2 + x / 2

/-- The right endpoint `a = π - (5/3) √(3c)`. -/
def finalA : ℝ := π - 5 / 3 * Real.sqrt (3 * cDensity)

/-- Numerical bounds for `√3`. -/
lemma sqrt3_bounds : 1.732 < √3 ∧ √3 < 1.7321 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- Numerical bounds for the density constant `c = π / (2√3) ≈ 0.9069`. -/
lemma cDensity_bounds : 0.9068 < cDensity ∧ cDensity < 0.907 := by
  obtain ⟨h1, h2⟩ := sqrt3_bounds
  have p1 := Real.pi_gt_d6
  have p2 := Real.pi_lt_d6
  unfold cDensity
  constructor
  · rw [lt_div_iff₀ (by positivity)]; nlinarith
  · rw [div_lt_iff₀ (by positivity)]; nlinarith

/-- The rational certificate: `F(0) < c`. -/
lemma finalF_zero_lt : finalF 0 < cDensity := by
  have := cDensity_bounds.1
  have p2 := Real.pi_lt_d6
  have p1 := Real.pi_gt_d6
  unfold finalF; nlinarith

/-- The rational certificate: `F(a) < c`.  Since `(π - a)² = 25c/3`, this says `a < c/2`. -/
lemma finalF_finalA_lt : finalF finalA < cDensity := by
  obtain ⟨c1, c2⟩ := cDensity_bounds
  have p2 := Real.pi_lt_d6
  have p1 := Real.pi_gt_d6
  have hc0 : 0 < cDensity := by linarith
  set s := Real.sqrt (3 * cDensity) with hs
  have hs2 : s ^ 2 = 3 * cDensity := Real.sq_sqrt (by linarith)
  have hslow : 3 / 5 * (π - cDensity / 2) < s := by
    rw [hs, Real.lt_sqrt (by nlinarith)]; nlinarith
  unfold finalF finalA
  rw [← hs]
  nlinarith

/-- Equation (14): `R - P ≤ (3/5)(π D - P) + o(D)`. -/
lemma eq14 {D ε R P f β c₂ C₁ A : ℝ}
    (hR : R ≤ f - β + ε * D) (hfc : f + c₂ ≤ π * D + ε * D)
    (h25 : 2 / 5 * f + A - ε * D ≤ β + 2 / 5 * P + 2 / 5 * c₂ + 1 / 5 * C₁)
    (hC : C₁ ≤ c₂) (hA : 0 ≤ A) :
    R - P ≤ 3 / 5 * (π * D - P) + 13 / 5 * ε * D := by
  linarith

/-- The final contradiction of §7, with a fixed positive margin: for some `ε > 0` the
inequalities (11)–(14) and Mantel's bound are incompatible. -/
lemma final_contradiction : ∃ ε > 0, ∀ D q R P QP f β c₂ C₁ A : ℝ, 0 < D →
    (cDensity - ε) * D ^ 2 ≤ q →
    R ≤ f - β + ε * D →
    f + c₂ ≤ π * D + ε * D →
    2 / 5 * f + A - ε * D ≤ β + 2 / 5 * P + 2 / 5 * c₂ + 1 / 5 * C₁ →
    C₁ ≤ c₂ → 0 ≤ A → 0 ≤ P → P ≤ R →
    QP ≤ D * P / 2 + ε * D ^ 2 →
    QP ≤ cDensity / 4 * D ^ 2 + ε * D ^ 2 →
    q - QP - ε * D ^ 2 ≤ (R - P) ^ 2 / 4 → False := by
  refine ⟨1 / 1000, by norm_num, ?_⟩
  intro D q R P QP f β c₂ C₁ A hD hq hR hfc h25 hC hA hP0 hPR hQ1 hQ2 hM
  have h14 := eq14 hR hfc h25 hC hA
  set Y := 3 / 5 * (π * D - P) + 13 / 5 * (1 / 1000) * D with hY
  have hY0 : 0 ≤ R - P := by linarith
  have hsq : (R - P) ^ 2 ≤ Y ^ 2 := pow_le_pow_left₀ hY0 h14 2
  obtain ⟨c1, c2⟩ := cDensity_bounds
  have p1 := Real.pi_gt_d4
  have p2 := Real.pi_lt_d4
  have hD2 : 0 < D ^ 2 := by positivity
  have f1 : π ^ 2 * D ^ 2 ≤ 9.8697 * D ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ hD2.le; nlinarith
  have f6 : 3.1415 * D ^ 2 ≤ π * D ^ 2 := mul_le_mul_of_nonneg_right p1.le hD2.le
  have f5 : 0.9068 * D ^ 2 ≤ cDensity * D ^ 2 := mul_le_mul_of_nonneg_right c1.le hD2.le
  -- split the range of `x = P / D` at `9/20` (slightly to the right of `a ≈ 0.39`)
  by_cases hs : P ≤ 9 / 20 * D
  · -- linear branch of (11): `F` is decreasing on `[0, 9/20]`, so `F(x) ≤ F(0) < c`
    have f2 : π * D ^ 2 ≤ 3.1416 * D ^ 2 := mul_le_mul_of_nonneg_right p2.le hD2.le
    have f3 : 0 ≤ P * D := mul_nonneg hP0 hD.le
    have f3' : 3 * (P * D) ≤ π * (P * D) := mul_le_mul_of_nonneg_right (by linarith) f3
    have f4 : 0 ≤ P * (9 / 20 * D - P) := mul_nonneg hP0 (by linarith)
    nlinarith
  · -- quadratic branch of (11): `c/4 + (9/100)(π - x)² < c` for `x ≥ 9/20`
    push_neg at hs
    have hY1 : Y ≤ 3 / 5 * (π - 9 / 20) * D + 13 / 5 * (1 / 1000) * D := by
      rw [hY]; nlinarith
    have hYY : Y ^ 2 ≤ (3 / 5 * (π - 9 / 20) * D + 13 / 5 * (1 / 1000) * D) ^ 2 :=
      pow_le_pow_left₀ (by linarith) hY1 2
    have e : (3 / 5 * (π - 9 / 20) * D + 13 / 5 * (1 / 1000) * D) ^ 2 =
        9 / 25 * (π ^ 2 * D ^ 2) + (2 * (3 / 5) * (13 / 5 / 1000 - 27 / 100)) * (π * D ^ 2) +
          (13 / 5 / 1000 - 27 / 100) ^ 2 * D ^ 2 := by ring
    rw [e] at hYY
    linarith

/- Theorem 1.1 (`erdos99_finite_multiplicity`) and `erdos99_of_finite_multiplicity` now live in
`Erdos99.lean`, after the assembly of the track count. -/

end Erdos99
end

end Overview

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `InnerRound`
-/

section InnerRound

/-!
# Roundness, inner half

If a separated set `X` with `|X| √3/2 ≥ π D²/4` lies in a disc of radius `D/2 + η D` about `O`,
with `η` small compared with `δ²`, then in every direction `ν` some point of `X` reaches
`⟪x - O, ν⟫ ≥ D/2 - δ D`.  Otherwise the union of the unit discs about the points would miss a
rectangle of area `δ² D² / 2` inside the disc of radius `D/2 + η D + 1`.
-/

open scoped BigOperators Real
open Filter MeasureTheory Set

@[expose] public noncomputable section

open Classical

namespace Erdos99

lemma frame_coords {O ν y : Plane} {p q : ℝ} (hν : ‖ν‖ = 1) (hy : y = O + p • ν + q • rot ν) :
    inner ℝ (y - O) ν = p ∧ ‖y - O‖ ^ 2 = p ^ 2 + q ^ 2 := by
  have h := norm_sq_coord ν
  rw [hν] at h
  subst hy
  rw [inner_coord, norm_sq_coord]
  simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, rot]
  simp
  constructor
  · linear_combination (-p) * h
  · linear_combination (-(p ^ 2 + q ^ 2)) * h

lemma inner_le_of_dist_le {O ν x y : Plane} (hν : ‖ν‖ = 1) (hxy : dist y x ≤ 1) :
    inner ℝ (y - O) ν ≤ inner ℝ (x - O) ν + 1 := by
  have : inner ℝ (y - O) ν = inner ℝ (x - O) ν + inner ℝ (y - x) ν := by
    rw [← inner_add_left]; congr 1; abel
  rw [this]
  have := real_inner_le_norm (y - x) ν
  rw [hν, mul_one, ← dist_eq_norm] at this
  linarith

/-- **Inner roundness.**  A separated set of `n` points with `π D²/4 ≤ n √3 / 2` inside the disc
of radius `D/2 + η D` about `O` reaches `D/2 - δ D` in every direction, provided
`η ≤ δ² / 100`, `δ ≤ 1/2` and `η D ≥ 1`. -/
theorem exists_support_ge {X : Finset Plane} (hX : IsSeparated X) {O ν : Plane} {D η δ : ℝ}
    (hν : ‖ν‖ = 1) (hD : 0 < D) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hη : η ≤ δ ^ 2 / 100) (hηD : 1 ≤ η * D)
    (hlat : π * D ^ 2 / 4 ≤ X.card * (√3 / 2))
    (hball : ∀ x ∈ X, dist x O ≤ D / 2 + η * D) :
    ∃ x ∈ X, D / 2 - δ * D ≤ inner ℝ (x - O) ν := by
  by_contra hcon
  push_neg at hcon
  have hη0 : 0 < η := by
    by_contra h; push_neg at h; nlinarith
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = D / 2 + η * D + 1 := ⟨_, rfl⟩
  obtain ⟨h', hh'⟩ : ∃ h' : ℝ, h' = D / 2 - δ * D + 1 := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = δ * D / 2 := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : Set Plane, K = ⋃ p ∈ X, Metric.closedBall p (1 : ℝ) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : Set Plane,
      P = paraOpen (O + h' • ν - c • rot ν) (c • ν) ((2 * c) • rot ν) := ⟨_, rfl⟩
  have hcr : cr (c • ν) ((2 * c) • rot ν) = 2 * c ^ 2 := by
    have h := norm_sq_coord ν
    rw [hν] at h
    simp only [cr, PiLp.smul_apply, smul_eq_mul, rot]
    simp
    linear_combination (-2 * c ^ 2) * h
  have hc0 : 0 < c := by rw [hc]; positivity
  have hcr0 : cr (c • ν) ((2 * c) • rot ν) ≠ 0 := by rw [hcr]; positivity
  -- points of `P`
  have hPpt : ∀ y ∈ P, h' < inner ℝ (y - O) ν ∧ ‖y - O‖ ≤ ρ := by
    rw [hP]
    rintro y ⟨α, β, hα0, hα1, hβ0, hβ1, rfl⟩
    have e : O + h' • ν - c • rot ν + α • (c • ν) + β • ((2 * c) • rot ν) =
        O + (h' + α * c) • ν + ((2 * β - 1) * c) • rot ν := by
      simp only [smul_smul, add_smul]; module
    obtain ⟨e1, e2⟩ := frame_coords hν e
    rw [e] at e1 e2 ⊢
    refine ⟨by rw [e1]; nlinarith, ?_⟩
    have hh0 : 0 < h' := by rw [hh']; nlinarith
    have hq : ((2 * β - 1) * c) ^ 2 ≤ c ^ 2 := by
      have : (2 * β - 1) ^ 2 ≤ 1 := by nlinarith
      nlinarith
    have hp : (h' + α * c) ^ 2 ≤ (h' + c) ^ 2 := by
      have : h' + α * c ≤ h' + c := by nlinarith
      exact pow_le_pow_left₀ (by nlinarith) this 2
    have hfin : (h' + c) ^ 2 + c ^ 2 ≤ ρ ^ 2 := by
      have e3 : (h' + c) ^ 2 + c ^ 2 = (D / 2 + 1) ^ 2 - δ * D * (D / 2 + 1 - δ * D / 2) := by
        subst hh' hc; ring
      have e4 : 0 ≤ δ * D * (D / 2 + 1 - δ * D / 2) := by
        apply mul_nonneg (by positivity); nlinarith only [hδ1, hD, hδ0]
      have e5 : (D / 2 + 1) ^ 2 ≤ ρ ^ 2 := by
        subst hρ; nlinarith only [mul_pos hη0 hD, hD]
      linarith only [e3, e4, e5]
    have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
    have h6 : ‖O + (h' + α * c) • ν + ((2 * β - 1) * c) • rot ν - O‖ ^ 2 ≤ ρ ^ 2 := by
      linarith only [e2, hp, hq, hfin]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hρ0 two_ne_zero).1 h6
  -- points of `K`
  have hKpt : ∀ y ∈ K, inner ℝ (y - O) ν ≤ h' ∧ dist y O ≤ ρ := by
    intro y hy
    rw [hK] at hy
    obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 hy
    have hyx' := Metric.mem_closedBall.1 hyx
    refine ⟨?_, ?_⟩
    · have := inner_le_of_dist_le (O := O) hν hyx'
      have := hcon x hx
      rw [hh']; linarith
    · have := dist_triangle y x O
      have := hball x hx
      rw [hρ]; linarith
  have hdisj : Disjoint K P := by
    rw [Set.disjoint_left]
    intro y hyK hyP
    linarith [(hKpt y hyK).1, (hPpt y hyP).1]
  have hsub : K ∪ P ⊆ Metric.closedBall O ρ := by
    rintro y (hy | hy)
    · exact Metric.mem_closedBall.2 (hKpt y hy).2
    · rw [Metric.mem_closedBall, dist_eq_norm]; exact (hPpt y hy).2
  have hPm : MeasurableSet P := hP ▸ (isOpen_paraOpen hcr0).measurableSet
  have hvol : volume K + volume P ≤ volume (Metric.closedBall O ρ) := by
    rw [← measure_union hdisj hPm]; exact measure_mono hsub
  rw [hP, volume_paraOpen, hcr, EuclideanSpace.volume_closedBall_fin_two] at hvol
  have hcard := card_mul_le_volume_union hX
  rw [← hK] at hcard
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have h2 : ENNReal.ofReal (X.card * (√3 / 2)) + ENNReal.ofReal |2 * c ^ 2| ≤
      ENNReal.ofReal (ρ ^ 2 * π) := by
    have e : ENNReal.ofReal (ρ ^ 2 * π) = ENNReal.ofReal ρ ^ 2 * ENNReal.ofReal π := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hρ0]
    rw [e]
    exact (add_le_add hcard le_rfl).trans hvol
  rw [← ENNReal.ofReal_add (by positivity) (abs_nonneg _),
    ENNReal.ofReal_le_ofReal_iff (by positivity), abs_of_pos (by positivity)] at h2
  -- numerics
  have hηD0 : 0 < η * D := by positivity
  have hD1 : D ≤ η * D ^ 2 := by nlinarith only [hηD, hD]
  have hηs : η ≤ 1 / 400 := by nlinarith only [hη, hδ1, hδ0]
  have hηD2 : (η * D + 1) ^ 2 ≤ 4 * η * (η * D ^ 2) := by nlinarith only [hηD, hηD0]
  have hηD3 : 4 * η * (η * D ^ 2) ≤ η * D ^ 2 := by
    have : 0 ≤ η * D ^ 2 := by positivity
    nlinarith only [this, hηs]
  have hexp : ρ ^ 2 * π = π * D ^ 2 / 4 + π * (η * D ^ 2 + D + (η * D + 1) ^ 2) := by
    rw [hρ]; ring
  have hbig : π * (η * D ^ 2 + D + (η * D + 1) ^ 2) ≤ π * (3 * η * D ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
    linarith only [hD1, hηD2, hηD3]
  have h3 : 2 * c ^ 2 ≤ π * (3 * η * D ^ 2) := by linarith only [h2, hlat, hexp, hbig]
  have h4 : π * (3 * η * D ^ 2) ≤ 4 * (3 * (δ ^ 2 / 100) * D ^ 2) := by
    apply mul_le_mul Real.pi_le_four _ (by positivity) (by norm_num)
    have : 0 ≤ D ^ 2 := by positivity
    nlinarith only [this, hη]
  have h5 : 2 * c ^ 2 = δ ^ 2 * D ^ 2 / 2 := by rw [hc]; ring
  have h6 : 0 < δ ^ 2 * D ^ 2 := by positivity
  linarith only [h3, h4, h5, h6]

end Erdos99
end

end InnerRound

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `ConvexFaces`
-/

section ConvexFaces

/-!
# Lemma 2.1: the augmented contact graph and its faces

For a large optimal set `X` under finite multiplicity (the standing hypotheses of §2):

* `augEdges_isPlaneGraph`: the contact graph with its missing hull sides added is a plane graph;
* `cUnitEdges_connected`, `augEdges_connected`: both graphs are connected;
* `augEdges_twoConnected` (in `TwoConnected.lean`): the augmented graph is `2`-connected;
* `contactFace_polygon`: every bounded face of the contact graph is the interior of a strictly
  convex unit polygon, whose sides are exactly the boundary edges of the face;
* `contactFaces_subset_augFaces`, `augFace_cases`: the bounded faces of the augmented graph are
  the old faces together with the caps of the non-unit hull sides;
* `cap_polygon`: every non-unit hull side `[v, w]` bounds exactly one cap; it is the interior of a
  strictly convex polygon whose sides other than `[v, w]` form a simple path of
  `j = returnLength X v w ≥ 2` unit edges.

Consequences for the counts: `c₁ = u` and `ℓ = 2b - u + ρ` (`hullReturns_one_eventually`,
`outerWalkLength_eq_eventually`).
-/

open scoped BigOperators Real
open EstablishedExternalResults Set Filter

@[expose] public noncomputable section

open Classical

namespace Erdos99

/-! ## Hull sides -/

lemma mem_ccwHullSides {X : Finset Plane} {p : Plane × Plane} :
    p ∈ ccwHullSides X ↔ IsCcwHullSide X p.1 p.2 := by
  unfold ccwHullSides
  simp only [Finset.mem_filter, Finset.mem_product]
  exact ⟨fun h => h.2, fun h => ⟨⟨mem_of_mem_hullVertices h.1, mem_of_mem_hullVertices h.2.1⟩, h⟩⟩

/-- The convex hull of `X` is the convex hull of its vertices. -/
lemma convexHull_hullVertices (X : Finset Plane) :
    convexHull ℝ ((hullVertices X : Finset Plane) : Set Plane) = convexHull ℝ (X : Set Plane) := by
  have e : ((hullVertices X : Finset Plane) : Set Plane) =
      extremePoints ℝ (convexHull ℝ (X : Set Plane)) := by
    ext x
    simp only [hullVertices, Finset.coe_filter, Set.mem_setOf_eq]
    exact ⟨fun h => h.2, fun h => ⟨extremePoints_convexHull_subset h, h⟩⟩
  rw [e]
  have hc := (X.finite_toSet).isCompact_convexHull
  have h := closure_convexHull_extremePoints hc (convex_convexHull ℝ _)
  refine le_antisymm (convexHull_min (extremePoints_subset) (convex_convexHull ℝ _)) ?_
  calc convexHull ℝ (X : Set Plane) = _ := h.symm
    _ ⊆ _ := closure_minimal subset_rfl ?_
  exact ((X.finite_toSet.subset extremePoints_convexHull_subset)).isClosed_convexHull

/-- If all hull vertices lie weakly left of a line through `v`, so does all of `X`. -/
lemma det2_nonneg_of_hullVertices {X : Finset Plane} {d v : Plane}
    (h : ∀ x ∈ hullVertices X, 0 ≤ det2 d (x - v)) : ∀ y ∈ X, 0 ≤ det2 d (y - v) := by
  intro y hy
  have hyc : y ∈ convexHull ℝ ((hullVertices X : Finset Plane) : Set Plane) := by
    rw [convexHull_hullVertices]; exact subset_convexHull ℝ _ hy
  have hconv : Convex ℝ {z : Plane | 0 ≤ det2 d (z - v)} := by
    have : {z : Plane | 0 ≤ det2 d (z - v)} = {z : Plane | det2 d v ≤ det2 d z} := by
      ext z; simp only [Set.mem_setOf_eq, det2_sub_right]; constructor <;> intro <;> linarith
    rw [this]
    refine convex_halfSpace_ge ?_ _
    refine ⟨fun a b => ?_, fun c a => ?_⟩ <;> simp [det2] <;> ring
  exact convexHull_min (fun x hx => h x hx) hconv hyc

/-- Each hull vertex starts exactly one counterclockwise hull side, so there are `b` hull sides. -/
lemma card_ccwHullSides {X : Finset Plane} (hb : 3 ≤ (hullVertices X).card) :
    (ccwHullSides X).card = (hullVertices X).card := by
  refine Finset.card_bij (fun p _ => p.1) (fun p hp => (mem_ccwHullSides.1 hp).1) ?_ ?_
  · intro p hp q hq h
    simp only at h
    have hq' := mem_ccwHullSides.1 hq
    rw [← h] at hq'
    exact Prod.ext h ((mem_ccwHullSides.1 hp).succ_unique hq')
  · intro v hv
    have h2 := two_le_card_hullPairs_fst hv hb
    -- among the hull pairs starting at `v`, at least one has all hull vertices on its left
    by_contra hno
    push_neg at hno
    have hright : ∀ p ∈ (hullPairs X).filter (fun p => p.1 = v),
        IsCcwHullSide X p.2 v := by
      intro p hp
      obtain ⟨hp1, rfl⟩ := Finset.mem_filter.1 hp
      obtain ⟨hoff, hside⟩ := Finset.mem_filter.1 hp1
      obtain ⟨h1, h2', hne⟩ := Finset.mem_offDiag.1 hoff
      rcases hside with hl | hr
      · exfalso
        refine hno p ?_ rfl
        exact mem_ccwHullSides.2 ⟨h1, h2', hne, det2_nonneg_of_hullVertices hl⟩
      · refine ⟨h2', h1, Ne.symm hne, det2_nonneg_of_hullVertices fun x hx => ?_⟩
        have := hr x hx
        have e : det2 (p.1 - p.2) (x - p.2) = -det2 (p.2 - p.1) (x - p.1) := by
          unfold det2; simp; ring
        linarith
    obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.1 (by omega : 1 < ((hullPairs X).filter
      (fun p => p.1 = v)).card)
    have e1 := (Finset.mem_filter.1 hp).2
    have e2 := (Finset.mem_filter.1 hq).2
    have := (hright p hp).pred_unique (hright q hq)
    exact hpq (Prod.ext (e1.trans e2.symm) this)

/-- A non-collinear finite set has at least three hull vertices. -/
lemma three_le_card_hullVertices {X : Finset Plane} (hcol : ¬ Collinear ℝ (X : Set Plane)) :
    3 ≤ (hullVertices X).card := by
  by_contra hlt
  push_neg at hlt
  apply hcol
  have hsub : (X : Set Plane) ⊆ convexHull ℝ ((hullVertices X : Finset Plane) : Set Plane) := by
    rw [convexHull_hullVertices]; exact subset_convexHull ℝ _
  have hc : Collinear ℝ ((hullVertices X : Finset Plane) : Set Plane) := by
    interval_cases h : (hullVertices X).card
    · rw [Finset.card_eq_zero] at h; simp [h, collinear_empty]
    · obtain ⟨a, ha⟩ := Finset.card_eq_one.1 h; simp [ha, collinear_singleton]
    · obtain ⟨a, b, -, ha⟩ := Finset.card_eq_two.1 h; simp [ha, collinear_pair]
  have hA : Collinear ℝ (affineSpan ℝ ((hullVertices X : Finset Plane) : Set Plane) :
      Set Plane) := by
    show Module.rank ℝ (affineSpan ℝ _).direction ≤ 1
    rw [direction_affineSpan]; exact hc
  exact hA.subset (hsub.trans (convexHull_subset_affineSpan _))

/-! ## Geometry of a hull side -/

lemma mem_segment_toC {a b : Plane} {z : ℂ} :
    z ∈ segment ℝ (toC a) (toC b) ↔ toC.symm z ∈ segment ℝ a b := by
  have h := image_segment ℝ (toC.toLinearEquiv.toLinearMap.toAffineMap) a b
  simp only [LinearMap.coe_toAffineMap, LinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toLinearEquiv] at h
  rw [← h]
  constructor
  · rintro ⟨x, hx, rfl⟩; simpa using hx
  · intro h'; exact ⟨_, h', by simp⟩

lemma convex_det2_halfplane (d v : Plane) : Convex ℝ {z : Plane | 0 ≤ det2 d (z - v)} := by
  have : {z : Plane | 0 ≤ det2 d (z - v)} = {z : Plane | det2 d v ≤ det2 d z} := by
    ext z; simp only [Set.mem_setOf_eq, det2_sub_right]; constructor <;> intro <;> linarith
  rw [this]
  refine convex_halfSpace_ge ?_ _
  refine ⟨fun a b => ?_, fun c a => ?_⟩ <;> simp [det2] <;> ring

/-- The convex hull lies to the left of every counterclockwise hull side. -/
lemma hull_subset_halfplane {X : Finset Plane} {v w : Plane} (hs : IsCcwHullSide X v w) :
    convexHull ℝ (X : Set Plane) ⊆ {z : Plane | 0 ≤ det2 (w - v) (z - v)} :=
  convexHull_min (fun y hy => hs.2.2.2 y hy) (convex_det2_halfplane _ _)

lemma det2_segment_zero {v w z : Plane} (hz : z ∈ segment ℝ v w) : det2 (w - v) (z - v) = 0 := by
  obtain ⟨a, b, -, -, hab, rfl⟩ := hz
  have : a • v + b • w - v = b • (w - v) := by
    rw [show a = 1 - b by linarith, sub_smul, one_smul, smul_sub]; abel
  rw [this, det2_smul_right]; unfold det2; ring

/-- A hull side lies on the boundary of the hull. -/
lemma segment_subset_frontier {X : Finset Plane} {v w : Plane} (hs : IsCcwHullSide X v w) :
    segment ℝ v w ⊆ frontier (convexHull ℝ (X : Set Plane)) := by
  intro z hz
  have hvX := mem_of_mem_hullVertices hs.1
  have hwX := mem_of_mem_hullVertices hs.2.1
  have hzK : z ∈ convexHull ℝ (X : Set Plane) :=
    (convex_convexHull ℝ _).segment_subset (subset_convexHull ℝ _ hvX)
      (subset_convexHull ℝ _ hwX) hz
  refine ⟨subset_closure hzK, fun hint => ?_⟩
  have h0 := det2_segment_zero hz
  set d := w - v
  have hd : d ≠ 0 := sub_ne_zero.2 hs.2.2.1.symm
  have hc : Continuous fun ε : ℝ => z - ε • rot d := by fun_prop
  have hint' : z - (0 : ℝ) • rot d ∈ interior (convexHull ℝ (X : Set Plane)) := by
    rw [zero_smul, sub_zero]; exact hint
  have hev := (hc.tendsto 0).eventually (mem_interior_iff_mem_nhds.1 hint')
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hmem := hball (y := δ / 2) (by rw [Real.dist_eq, abs_of_pos (by linarith)]; linarith)
  have := hmem
  have h1 := hull_subset_halfplane hs this
  simp only [Set.mem_setOf_eq] at h1
  have e : det2 d (z - (δ / 2) • rot d - v) = det2 d (z - v) - (δ / 2) * ‖d‖ ^ 2 := by
    rw [show z - (δ / 2) • rot d - v = (z - v) - (δ / 2) • rot d by abel, det2_sub_right,
      det2_smul_right, det2_rot, real_inner_self_eq_norm_sq]
  rw [e, h0] at h1
  have : 0 < ‖d‖ := norm_pos_iff.2 hd
  have := mul_pos (half_pos hδ) (pow_pos this 2)
  linarith

/-- A segment in a closed half-plane touching the boundary line at an inner point lies on the
line. -/
lemma seg_touch {d v a b z : Plane} (ha : 0 ≤ det2 d (a - v)) (hb : 0 ≤ det2 d (b - v))
    (hz : z ∈ openSegment ℝ a b) (h0 : det2 d (z - v) = 0) :
    det2 d (a - v) = 0 ∧ det2 d (b - v) = 0 := by
  obtain ⟨s, r, hs, hr, hsr, rfl⟩ := hz
  have hv : v = s • v + r • v := by rw [← add_smul, hsr, one_smul]
  have e : s • a + r • b - v = s • (a - v) + r • (b - v) := by
    conv_lhs => rw [hv]
    rw [smul_sub, smul_sub]; abel
  rw [e, show det2 d (s • (a - v) + r • (b - v)) = s * det2 d (a - v) + r * det2 d (b - v) by
    simp [det2]; ring] at h0
  constructor <;> nlinarith [mul_nonneg hs.le ha, mul_nonneg hr.le hb]

/-- Points of `X` on the line of a hull side lie on the side. -/
lemma mem_segment_of_det2_zero {X : Finset Plane} {v w : Plane} (hs : IsCcwHullSide X v w)
    {y : Plane} (hy : y ∈ X) (h0 : det2 (w - v) (y - v) = 0) : y ∈ segment ℝ v w := by
  have hd : w - v ≠ 0 := sub_ne_zero.2 hs.2.2.1.symm
  obtain ⟨s, hs'⟩ := eq_smul_of_det2_eq_zero hd h0
  have hvX := mem_of_mem_hullVertices hs.1
  have hwX := mem_of_mem_hullVertices hs.2.1
  have hy' : y = v + s • (w - v) := by rw [← hs']; abel
  rcases lt_or_ge s 0 with hneg | hnn
  · -- `v` would lie strictly between `y` and `w`
    exfalso
    have hyv : y ≠ v := by
      intro h
      rw [h, sub_self] at hs'
      rcases smul_eq_zero.1 hs'.symm with h' | h'
      · linarith
      · exact hd h'
    have h1 : (1 - s) ≠ 0 := by linarith
    refine not_mem_openSegment_of_hull hs.1 hy hwX hyv ⟨1 / (1 - s), -s / (1 - s),
      by apply div_pos <;> linarith, by apply div_pos <;> linarith, by field_simp; ring, ?_⟩
    rw [hy']
    match_scalars <;> field_simp <;> ring
  rcases le_or_gt s 1 with hle | hgt
  · rw [segment_eq_image']
    exact ⟨s, ⟨hnn, hle⟩, hy'.symm⟩
  · -- `w` would lie strictly between `v` and `y`
    exfalso
    refine not_mem_openSegment_of_hull hs.2.1 hvX hy hs.2.2.1 ?_
    refine ⟨1 - 1 / s, 1 / s, by
      rw [sub_pos, div_lt_one (by linarith)]; exact hgt, by positivity, by ring, ?_⟩
    rw [hy']
    have hs0 : s ≠ 0 := by linarith
    match_scalars <;> field_simp <;> ring

/-- If every boundary point of `X` is a hull vertex, no point of `X` lies inside a hull side. -/
lemma no_point_on_side {X : Finset Plane}
    (hB : ∀ x ∈ X, x ∈ frontier (convexHull ℝ (X : Set Plane)) → x ∈ hullVertices X)
    {v w : Plane} (hs : IsCcwHullSide X v w) {x : Plane} (hx : x ∈ X)
    (hxs : x ∈ segment ℝ v w) : x = v ∨ x = w := by
  by_contra h
  push_neg at h
  have hhv := hB x hx (segment_subset_frontier hs hxs)
  have hopen : x ∈ openSegment ℝ v w := by
    rw [← insert_endpoints_openSegment] at hxs
    rcases hxs with h1 | h1 | h1
    · exact absurd h1 h.1
    · exact absurd h1 h.2
    · exact h1
  exact not_mem_openSegment_of_hull hhv (mem_of_mem_hullVertices hs.1)
    (mem_of_mem_hullVertices hs.2.1) h.1.symm hopen

lemma mem_openSegment_of_ne {a b z : Plane} (hz : z ∈ segment ℝ a b) (ha : z ≠ a) (hb : z ≠ b) :
    z ∈ openSegment ℝ a b := by
  rw [← insert_endpoints_openSegment] at hz
  rcases hz with h1 | h1 | h1
  · exact absurd h1 ha
  · exact absurd h1 hb
  · exact h1

/-- A segment between two points of `X` meets a hull side only at common endpoints, unless it is
that side. -/
lemma seg_inter_hull_side {X : Finset Plane}
    (hB : ∀ x ∈ X, x ∈ frontier (convexHull ℝ (X : Set Plane)) → x ∈ hullVertices X)
    {v w : Plane} (hs : IsCcwHullSide X v w) {a b : Plane} (ha : a ∈ X) (hb : b ∈ X)
    (hne : s(a, b) ≠ s(v, w)) {z : Plane} (hza : z ∈ segment ℝ a b)
    (hzs : z ∈ segment ℝ v w) : (z = a ∨ z = b) ∧ (z = v ∨ z = w) := by
  have h1 : z = a ∨ z = b := by
    by_contra hab'
    push_neg at hab'
    have hzo := mem_openSegment_of_ne hza hab'.1 hab'.2
    have hK := hull_subset_halfplane hs
    obtain ⟨da, db⟩ := seg_touch (hK (subset_convexHull ℝ _ ha)) (hK (subset_convexHull ℝ _ hb))
      hzo (det2_segment_zero hzs)
    have ha' := no_point_on_side hB hs ha (mem_segment_of_det2_zero hs ha da)
    have hb' := no_point_on_side hB hs hb (mem_segment_of_det2_zero hs hb db)
    have hab : a ≠ b := by
      rintro rfl
      rw [segment_same] at hza
      exact hab'.1 hza
    apply hne
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
    · exact absurd rfl hab
    · rfl
    · exact Sym2.eq_swap
    · exact absurd rfl hab
  refine ⟨h1, ?_⟩
  rcases h1 with rfl | rfl
  · exact no_point_on_side hB hs ha hzs
  · exact no_point_on_side hB hs hb hzs

lemma cUnitEdges_cases {X : Finset Plane} {e : Sym2 ℂ} (he : e ∈ cUnitEdges X) :
    ∃ a ∈ X, ∃ b ∈ X, dist a b = 1 ∧ e = s(toC a, toC b) := by
  induction e using Sym2.ind with
  | _ z w =>
  obtain ⟨hz, hw, hzw⟩ := mem_unitPairs.1 he
  refine ⟨toC.symm z, mem_cVerts.1 hz, toC.symm w, mem_cVerts.1 hw, ?_, by simp⟩
  rw [LinearIsometryEquiv.dist_map]; exact hzw

lemma hullSideEdges_cases {X : Finset Plane} {e : Sym2 ℂ} (he : e ∈ hullSideEdges X) :
    ∃ v w : Plane, IsCcwHullSide X v w ∧ e = s(toC v, toC w) := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 he
  exact ⟨p.1, p.2, mem_ccwHullSides.1 hp, rfl⟩

lemma mem_edgeSeg_toC {a b : Plane} {z : ℂ} :
    z ∈ edgeSeg s(toC a, toC b) ↔ toC.symm z ∈ segment ℝ a b := by
  rw [edgeSeg_mk, mem_segment_toC]

lemma mem_sym2_toC {a b : Plane} {z : ℂ} (h : toC.symm z = a ∨ toC.symm z = b) :
    z ∈ s(toC a, toC b) := by
  rcases h with h | h
  · rw [← h]; simp
  · rw [← h]; simp

/-- **Lemma 2.1 (the augmented graph is plane).**  For a separated set whose boundary points are
all hull vertices, the contact graph together with all hull sides is a plane graph. -/
theorem augEdges_isPlaneGraph_of {X : Finset Plane} (hX : IsSeparated X)
    (hB : ∀ x ∈ X, x ∈ frontier (convexHull ℝ (X : Set Plane)) → x ∈ hullVertices X) :
    IsPlaneGraph (cVerts X) (augEdges X) := by
  have hP0 := cUnitEdges_isPlaneGraph hX
  have hcases : ∀ e ∈ augEdges X, e ∈ cUnitEdges X ∨ e ∈ hullSideEdges X := fun e he =>
    Finset.mem_union.1 he
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e he v hv
    rcases hcases e he with h | h
    · exact hP0.mem_V e h v hv
    · obtain ⟨a, b, hs, rfl⟩ := hullSideEdges_cases h
      rcases Sym2.mem_iff.1 hv with rfl | rfl
      · exact Finset.mem_image_of_mem _ (mem_of_mem_hullVertices hs.1)
      · exact Finset.mem_image_of_mem _ (mem_of_mem_hullVertices hs.2.1)
  · intro e he
    rcases hcases e he with h | h
    · exact hP0.not_diag e h
    · obtain ⟨a, b, hs, rfl⟩ := hullSideEdges_cases h
      rw [Sym2.mk_isDiag_iff]
      exact fun h' => hs.2.2.1 (toC.injective h')
  · intro e he z hz hze
    rcases hcases e he with h | h
    · exact hP0.vertex_mem e h z hz hze
    · obtain ⟨a, b, hs, rfl⟩ := hullSideEdges_cases h
      exact mem_sym2_toC (no_point_on_side hB hs (mem_cVerts.1 hz) (mem_edgeSeg_toC.1 hze))
  · intro e he e' he' hne z hze hze'
    rcases hcases e he with h | h <;> rcases hcases e' he' with h' | h'
    · exact hP0.inter e h e' h' hne z hze hze'
    · obtain ⟨a, ha, b, hb, -, rfl⟩ := cUnitEdges_cases h
      obtain ⟨v, w, hs, rfl⟩ := hullSideEdges_cases h'
      have hne' : s(a, b) ≠ s(v, w) := fun h2 => hne (by
        rw [show s(toC a, toC b) = Sym2.map toC s(a, b) from rfl, h2]; rfl)
      exact mem_sym2_toC (seg_inter_hull_side hB hs ha hb hne' (mem_edgeSeg_toC.1 hze)
        (mem_edgeSeg_toC.1 hze')).1
    · obtain ⟨v, w, hs, rfl⟩ := hullSideEdges_cases h
      obtain ⟨a, ha, b, hb, -, rfl⟩ := cUnitEdges_cases h'
      have hne' : s(a, b) ≠ s(v, w) := fun h2 => hne (by
        rw [show s(toC a, toC b) = Sym2.map toC s(a, b) from rfl, h2]; rfl)
      exact mem_sym2_toC (seg_inter_hull_side hB hs ha hb hne' (mem_edgeSeg_toC.1 hze')
        (mem_edgeSeg_toC.1 hze)).2
    · obtain ⟨v, w, hs, rfl⟩ := hullSideEdges_cases h
      obtain ⟨v', w', hs', rfl⟩ := hullSideEdges_cases h'
      have hne' : s(v', w') ≠ s(v, w) := fun h2 => hne (by
        rw [show s(toC v', toC w') = Sym2.map toC s(v', w') from rfl, h2]; rfl)
      exact mem_sym2_toC (seg_inter_hull_side hB hs (mem_of_mem_hullVertices hs'.1)
        (mem_of_mem_hullVertices hs'.2.1) hne' (mem_edgeSeg_toC.1 hze')
        (mem_edgeSeg_toC.1 hze)).2

/-- Under finite multiplicity, every boundary point of a large optimal set is a hull vertex. -/
lemma boundary_hullVertex_eventually :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      ∀ x ∈ X, x ∈ frontier (convexHull ℝ (X : Set Plane)) → x ∈ hullVertices X := by
  filter_upwards [eventually_not_collinear, eventually_ge_atTop 2] with n hcol hn hfm X hX x hx hfr
  obtain ⟨y, hy, hd⟩ := exists_diam_partner_of_frontier hn hfm hX (hcol X hX) hx hfr
  have hxy : x ≠ y := by
    rintro rfl; rw [dist_self] at hd; exact (hX.diam_pos hn).ne hd
  exact mem_hullVertices_of_diam hx hy hxy hd


/-! ## The augmented graph -/

/-- Lemma 2.1: the augmented graph (contact graph plus hull sides) is a plane graph. -/
theorem augEdges_isPlaneGraph :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      IsPlaneGraph (cVerts X) (augEdges X) := by
  filter_upwards [boundary_hullVertex_eventually] with n hB hfm X hX
  exact augEdges_isPlaneGraph_of hX.1.2 (hB hfm X hX)

/-- The contact graph of an optimal set, drawn in `ℂ`, is connected. -/
lemma cUnitEdges_connected_of_optimal {n : ℕ} (hn : 2 ≤ n) (hfm : numOptimalClasses n < ⊤)
    {X : Finset Plane} (hX : IsOptimal n X) : GraphConnected (cVerts X) (cUnitEdges X) := by
  have hconn := contactGraph_connected_of_optimal hn hfm hX
  have hXne : X.Nonempty := by rw [← Finset.card_pos, hX.1.1]; omega
  refine ⟨hXne.image _, ?_⟩
  intro z hz w hw
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hz
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hw
  have hr := (SimpleGraph.reachable_iff_reflTransGen _ _).1 (hconn.preconnected ⟨x, hx⟩ ⟨y, hy⟩)
  have key : ∀ a b : X, (contactGraph X).Adj a b → s(toC a.1, toC b.1) ∈ cUnitEdges X := by
    intro a b hab
    have hab' : dist (a : Plane) b = 1 := hab
    unfold cUnitEdges cVerts
    rw [mem_unitPairs]
    exact ⟨Finset.mem_image_of_mem _ a.2, Finset.mem_image_of_mem _ b.2, by rw [dist_toC]; exact hab'⟩
  have h2 : Relation.ReflTransGen (fun z w => s(z, w) ∈ cUnitEdges X)
      (toC (⟨x, hx⟩ : X).1) (toC (⟨y, hy⟩ : X).1) :=
    Relation.ReflTransGen.lift (fun v : X => toC v.1) key hr
  exact h2

/-- Lemma 2.1: the contact graph, drawn in `ℂ`, is connected. -/
theorem cUnitEdges_connected :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      GraphConnected (cVerts X) (cUnitEdges X) := by
  filter_upwards [eventually_ge_atTop 2] with n hn hfm X hX
  exact cUnitEdges_connected_of_optimal hn hfm hX

/-- The augmented graph is connected. -/
theorem augEdges_connected :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      GraphConnected (cVerts X) (augEdges X) := by
  filter_upwards [cUnitEdges_connected] with n h hfm X hX
  obtain ⟨hne, hr⟩ := h hfm X hX
  exact ⟨hne, fun u hu v hv => (hr u hu v hv).mono fun a b hab => Finset.mem_union_left _ hab⟩

end Erdos99

end

end ConvexFaces

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `HullSpread`
-/

section HullSpread

/-!
# Lemma 3.2: spread of hull directions

For a large optimal configuration of diameter `D`, the number of hull sides whose directions
(modulo `π/3`) lie within `ρ` of one of `M` given directions is `O(D M (ρ + D^{-1/9}))`.

The manuscript obtains the error term `D^{-1/4}` from Bonnesen's inequality.  Here the roundness
rates actually proved in the project are used instead:

* `round_center_rate`: the configuration lies in a disc of radius `D/2 + 22 D^{2/3}`
  (quantitative version of `round_center_of_optimal`);
* `exists_support_ge_sharp`: it reaches `D/2 - δ D` in every direction when `η ≤ δ^{3/2}/25`
  (a sharper form of `exists_support_ge`), so one may take `δ = 100 D^{-2/9}`.

A boundary point with outward normal `ν` then lies within `D √(3δ)` of `O + (D/2) ν`.  Hull sides
whose direction is within `ε` of a unit vector `n` therefore project onto `ℝ n` inside an interval
of length `2 D (√(3δ) + ε/2)`; each projects to length at least `1/2`, and at most four hull pairs
cross any level line (`card_crossing_le`), which bounds their number.
-/

open scoped BigOperators Real ComplexConjugate
open Filter MeasureTheory

@[expose] public noncomputable section

open Classical

namespace Erdos99

/-! ## Sixth roots of unity -/

/-- A primitive cube root of unity. -/
def omega3 : ℂ := ⟨-1 / 2, √3 / 2⟩

/-- The sixth roots of unity. -/
def sixRoots : Finset ℂ := {1, omega3, omega3 ^ 2, -1, -omega3, -omega3 ^ 2}

lemma card_sixRoots_le : sixRoots.card ≤ 6 := Finset.card_le_six

/-- If `z⁶` is close to `w⁶` (unit complex numbers), then `z` is close to `ζ w` for a sixth root
of unity `ζ`. -/
lemma omega3_sq : omega3 ^ 2 = ⟨-1 / 2, -(√3 / 2)⟩ := by
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  apply Complex.ext <;> simp [omega3, pow_two] <;> nlinarith

lemma omega3_rel : omega3 ^ 2 + omega3 + 1 = 0 := by
  rw [omega3_sq]; apply Complex.ext <;> simp [omega3]

lemma omega3_cube : omega3 ^ 3 = 1 := by
  have h := omega3_rel
  linear_combination (omega3 - 1) * h

lemma norm_one_sub_omega3 : ‖1 - omega3‖ = √3 := by
  rw [Complex.norm_def]; congr 1
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  simp [Complex.normSq_apply, omega3]; nlinarith

lemma norm_one_sub_omega3_sq : ‖1 - omega3 ^ 2‖ = √3 := by
  rw [Complex.norm_def, omega3_sq]; congr 1
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  simp [Complex.normSq_apply]; nlinarith

lemma norm_omega3 : ‖omega3‖ = 1 := by
  rw [Complex.norm_def]
  have h3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have : Complex.normSq omega3 = 1 := by simp [Complex.normSq_apply, omega3]; nlinarith
  rw [this, Real.sqrt_one]

lemma norm_of_mem_sixRoots {ζ : ℂ} (h : ζ ∈ sixRoots) : ‖ζ‖ = 1 := by
  simp only [sixRoots, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [norm_omega3, norm_pow]

/-- Cube roots: if `‖z³ - u³‖ ≤ r ≤ 1/2` then `z` is within `2r` of `u`, `ω u` or `ω² u`. -/
lemma cube_root_near {z u : ℂ} (hu : ‖u‖ = 1) {r : ℝ} (hr : r ≤ 1 / 2)
    (h : ‖z ^ 3 - u ^ 3‖ ≤ r) :
    ‖z - u‖ ≤ 2 * r ∨ ‖z - omega3 * u‖ ≤ 2 * r ∨ ‖z - omega3 ^ 2 * u‖ ≤ 2 * r := by
  have hfac : z ^ 3 - u ^ 3 = (z - u) * (z - omega3 * u) * (z - omega3 ^ 2 * u) := by
    have h1 := omega3_rel
    have h2 := omega3_cube
    linear_combination (z ^ 2 * u - z * u ^ 2 * omega3) * h1 + u ^ 3 * h2
  rw [hfac, norm_mul, norm_mul] at h
  set d0 := ‖z - u‖
  set d1 := ‖z - omega3 * u‖
  set d2 := ‖z - omega3 ^ 2 * u‖
  have s3 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have s3p : 0 < √3 := by positivity
  have s3l : 1.7 < √3 := by nlinarith
  have t01 : √3 ≤ d0 + d1 := by
    have := norm_sub_le (z - omega3 * u) (z - u)
    rw [show z - omega3 * u - (z - u) = (1 - omega3) * u by ring, norm_mul, hu,
      norm_one_sub_omega3, mul_one] at this
    linarith
  have t02 : √3 ≤ d0 + d2 := by
    have := norm_sub_le (z - omega3 ^ 2 * u) (z - u)
    rw [show z - omega3 ^ 2 * u - (z - u) = (1 - omega3 ^ 2) * u by ring, norm_mul, hu,
      norm_one_sub_omega3_sq, mul_one] at this
    linarith
  have t12 : √3 ≤ d1 + d2 := by
    have := norm_sub_le (z - omega3 ^ 2 * u) (z - omega3 * u)
    rw [show z - omega3 ^ 2 * u - (z - omega3 * u) = omega3 * (1 - omega3) * u by ring,
      norm_mul, norm_mul, hu, norm_one_sub_omega3, norm_omega3, mul_one, one_mul] at this
    linarith
  have n0 : 0 ≤ d0 := norm_nonneg _
  have n1 : 0 ≤ d1 := norm_nonneg _
  have n2 : 0 ≤ d2 := norm_nonneg _
  by_cases c0 : d0 ≤ √3 / 2
  · left
    have h1 : √3 / 2 ≤ d1 := by linarith
    have h2 : √3 / 2 ≤ d2 := by linarith
    have : d0 * (3 / 4) ≤ d0 * d1 * d2 := by
      have : 3 / 4 ≤ d1 * d2 := by nlinarith
      nlinarith
    linarith
  by_cases c1 : d1 ≤ √3 / 2
  · right; left
    have h2 : √3 / 2 ≤ d2 := by linarith
    have : d1 * (3 / 4) ≤ d0 * d1 * d2 := by
      have : 3 / 4 ≤ d0 * d2 := by nlinarith
      nlinarith
    linarith
  by_cases c2 : d2 ≤ √3 / 2
  · right; right
    have : d2 * (3 / 4) ≤ d0 * d1 * d2 := by
      have : 3 / 4 ≤ d0 * d1 := by nlinarith
      nlinarith
    linarith
  exfalso
  push_neg at c0 c1 c2
  have : (√3 / 2) * (√3 / 2) * (√3 / 2) ≤ d0 * d1 * d2 := by
    have := mul_le_mul c0.le c1.le (by positivity) n0
    exact mul_le_mul this c2.le (by positivity) (by positivity)
  nlinarith

lemma sixth_root_near {z w : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) {r : ℝ} (hr : r ≤ 1 / 2)
    (h : ‖z ^ 6 - w ^ 6‖ ≤ r) : ∃ ζ ∈ sixRoots, ‖z - ζ * w‖ ≤ 2 * r := by
  have hfac : z ^ 6 - w ^ 6 = (z ^ 3 - w ^ 3) * (z ^ 3 + w ^ 3) := by ring
  rw [hfac, norm_mul] at h
  have hz3 : ‖z ^ 3‖ = 1 := by rw [norm_pow, hz, one_pow]
  have hw3 : ‖w ^ 3‖ = 1 := by rw [norm_pow, hw, one_pow]
  have htri : 2 ≤ ‖z ^ 3 - w ^ 3‖ + ‖z ^ 3 + w ^ 3‖ := by
    have := norm_sub_le (z ^ 3 + w ^ 3) (z ^ 3 - w ^ 3)
    rw [show z ^ 3 + w ^ 3 - (z ^ 3 - w ^ 3) = 2 * w ^ 3 by ring, norm_mul, hw3] at this
    norm_num at this; linarith
  have n1 := norm_nonneg (z ^ 3 - w ^ 3)
  have n2 := norm_nonneg (z ^ 3 + w ^ 3)
  have hmem : ∀ ζ : ℂ, ζ = 1 ∨ ζ = omega3 ∨ ζ = omega3 ^ 2 ∨ ζ = -1 ∨ ζ = -omega3 ∨
      ζ = -omega3 ^ 2 → ζ ∈ sixRoots := by
    intro ζ hζ
    simp only [sixRoots, Finset.mem_insert, Finset.mem_singleton]; tauto
  rcases le_total ‖z ^ 3 - w ^ 3‖ ‖z ^ 3 + w ^ 3‖ with hle | hle
  · have hA : ‖z ^ 3 - w ^ 3‖ ≤ r := by nlinarith
    rcases cube_root_near hw hr hA with h1 | h1 | h1
    · exact ⟨1, hmem _ (by tauto), by rwa [one_mul]⟩
    · exact ⟨omega3, hmem _ (by tauto), h1⟩
    · exact ⟨omega3 ^ 2, hmem _ (by tauto), h1⟩
  · have hB : ‖z ^ 3 - (-w) ^ 3‖ ≤ r := by
      rw [show z ^ 3 - (-w) ^ 3 = z ^ 3 + w ^ 3 by ring]; nlinarith
    have hw' : ‖-w‖ = 1 := by rw [norm_neg, hw]
    rcases cube_root_near hw' hr hB with h1 | h1 | h1
    · exact ⟨-1, hmem _ (by tauto), by rwa [neg_one_mul]⟩
    · exact ⟨-omega3, hmem _ (by tauto), by rwa [neg_mul, ← mul_neg]⟩
    · exact ⟨-omega3 ^ 2, hmem _ (by tauto), by rwa [neg_mul, ← mul_neg]⟩

/-! ## Projections of hull pairs -/

/-- Hull pairs whose endpoints project into `[a, b]` have total projection at most `4 (b - a)`. -/
lemma sum_abs_inner_subset_le {X : Finset Plane} {S : Finset (Plane × Plane)}
    (hS : S ⊆ hullPairs X) {n : Plane} (hn : ‖n‖ = 1) {a0 b0 : ℝ} (hle : a0 ≤ b0)
    (hab : ∀ p ∈ S, (a0 ≤ inner ℝ p.1 n ∧ inner ℝ p.1 n ≤ b0) ∧
      (a0 ≤ inner ℝ p.2 n ∧ inner ℝ p.2 n ≤ b0)) :
    ∑ p ∈ S, |inner ℝ (p.2 - p.1) n| ≤ 4 * (b0 - a0) := by
  set a : Plane × Plane → ℝ := fun p => min (inner ℝ p.1 n) (inner ℝ p.2 n)
  set b : Plane × Plane → ℝ := fun p => max (inner ℝ p.1 n) (inner ℝ p.2 n)
  have habs : ∀ p : Plane × Plane, |inner ℝ (p.2 - p.1) n| =
      ∫ t, (Set.Ioo (a p) (b p)).indicator (fun _ => (1:ℝ)) t := by
    intro p
    rw [integral_indicator_const _ measurableSet_Ioo, Real.volume_real_Ioo_of_le
      (min_le_max), smul_eq_mul, mul_one, inner_sub_left, max_sub_min_eq_abs]
  simp_rw [habs]
  rw [← integral_finset_sum _ (fun p _ => integrable_indicator_one_Ioo _ _)]
  have hpt : ∀ t, ∑ p ∈ S, (Set.Ioo (a p) (b p)).indicator (fun _ => (1:ℝ)) t ≤
      (Set.Icc a0 b0).indicator (fun _ => (4:ℝ)) t := by
    intro t
    have hsum : ∑ p ∈ S, (Set.Ioo (a p) (b p)).indicator (fun _ => (1:ℝ)) t =
        ((S.filter (CrossesLvl n t)).card : ℝ) := by
      simp only [Set.indicator_apply]
      rw [Finset.sum_boole]
      congr 2
      ext p
      simp only [Finset.mem_filter, a, b, mem_Ioo_min_max_iff, CrossesLvl]
    rw [hsum]
    by_cases ht : t ∈ Set.Icc a0 b0
    · rw [Set.indicator_of_mem ht]
      have := (Finset.card_le_card (Finset.filter_subset_filter (CrossesLvl n t) hS)).trans
        (card_crossing_le (X := X) hn t)
      exact_mod_cast this
    · rw [Set.indicator_of_notMem ht]
      have : S.filter (CrossesLvl n t) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro p hp hc
        unfold CrossesLvl at hc
        rw [← mem_Ioo_min_max_iff] at hc
        apply ht
        obtain ⟨⟨l1, u1⟩, ⟨l2, u2⟩⟩ := hab p hp
        exact ⟨le_trans (le_min l1 l2) hc.1.le, le_trans hc.2.le (max_le u1 u2)⟩
      rw [this]; simp
  refine (integral_mono (integrable_finset_sum _ fun p _ => integrable_indicator_one_Ioo _ _)
    ((integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))) hpt).trans ?_
  rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le hle,
    smul_eq_mul]
  linarith

/-! ## Roundness with rates -/

/-- The deterministic core of `round_center_of_optimal`: with `c = sin(η'/16) η'²/128` and
`π ≤ c D`, an optimal set lies in a disc of radius `(D + 2)(1 + η')/2`. -/
lemma round_core {n : ℕ} {X : Finset Plane} (hX : IsOptimal n X) (hn : 2 ≤ n) {η' : ℝ}
    (hη'0 : 0 < η') (hη'1 : η' ≤ 1 / 2)
    (hD2 : π ≤ Real.sin (η' / 16) * η' ^ 2 / 128 * diam X) :
    ∃ O : Plane, ∀ x ∈ X, dist x O ≤ (diam X + 2) * (1 + η') / 2 := by
  obtain ⟨c, hc, hc0⟩ : ∃ c : ℝ, c = Real.sin (η' / 16) * η' ^ 2 / 128 ∧ 0 < c :=
    ⟨_, rfl, by
      have := Real.sin_pos_of_pos_of_lt_pi (x := η' / 16) (by positivity)
        (by linarith [Real.pi_gt_three])
      positivity⟩
  rw [← hc] at hD2
  have hDpos : 0 < diam X := hX.diam_pos hn
  have hlat : π * diam X ^ 2 / 4 ≤ n * (√3 / 2) := by
    have h := minDiam_sq_le n (by omega)
    rw [← hX.diam_eq] at h
    unfold aStar at h
    rw [le_div_iff₀ Real.pi_pos] at h
    linarith
  have hn0 : (0 : ℝ) < n * (√3 / 2) := by
    have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    positivity
  have hcard := card_mul_le_volume_union hX.1.2
  rw [hX.1.1] at hcard
  obtain ⟨p0, hp0⟩ : X.Nonempty := by
    rw [← Finset.card_pos, hX.1.1]; omega
  generalize hDdef : diam X = D at *
  generalize hK : (⋃ p ∈ X, Metric.closedBall p (1 : ℝ)) = K at hcard
  have hKc : IsCompact K := hK ▸ X.finite_toSet.isCompact_biUnion fun p _ => isCompact_closedBall p 1
  have hXK : ∀ x ∈ X, x ∈ K := fun x hx =>
    hK ▸ Set.mem_biUnion hx (Metric.mem_closedBall_self zero_le_one)
  have hKd : ∀ a ∈ K, ∀ b ∈ K, dist a b ≤ D + 2 := by
    intro a ha b hb
    rw [← hK] at ha hb
    obtain ⟨p, hp, hap⟩ := Set.mem_iUnion₂.1 ha
    obtain ⟨q, hq, hbq⟩ := Set.mem_iUnion₂.1 hb
    have h1 := Metric.mem_closedBall.1 hap
    have h2 := Metric.mem_closedBall.1 hbq
    have h3 := hDdef ▸ dist_le_diam hp hq
    have := dist_triangle4 a p q b
    rw [dist_comm q b] at this
    linarith
  obtain ⟨O, R, hsub, hmin, a, ha, b, hb, haO, hbO, hab⟩ :=
    exists_circumcenter hKc ⟨p0, hXK p0 hp0⟩
  by_cases hR : R ≤ (D + 2) * (1 + η') / 2
  · exact ⟨O, fun x hx => (hsub x (hXK x hx)).trans hR⟩
  exfalso
  push_neg at hR
  have hRd : R ≤ D + 2 := by
    obtain ⟨x, hx, hxR⟩ := hmin p0
    exact hxR.trans (hKd x hx p0 (hXK p0 hp0))
  have hdpos : 0 < D + 2 := by linarith
  have h2R : (D + 2) * (1 + η') < 2 * R := by linarith
  have hG' : (D + 2) ^ 2 < 4 * R ^ 2 := by
    nlinarith [mul_self_lt_mul_self (by positivity) h2R, sq_nonneg η']
  have hvol := volume_le_of_circumradius hKc hKd hsub ha hb haO hbO hab hRd hG'
  have hκ := deficit_lower_bound hdpos hη'0 hη'1 h2R hRd
  rw [← hc] at hκ
  have hfin := (ENNReal.ofReal_le_ofReal_iff').1 (hcard.trans hvol)
  have hfin' := hfin.resolve_right (not_le.2 hn0)
  have hcd : c * (D + 2) ^ 2 < π * (D + 2) := by
    nlinarith only [hκ, hfin', hlat, Real.pi_pos]
  have hcd' : c * (D + 2) < π := lt_of_mul_lt_mul_right (by nlinarith only [hcd]) hdpos.le
  nlinarith only [hD2, hcd', hc0]

/-- **Outer roundness with a rate.**  Eventually every optimal configuration lies in a disc of
radius `D/2 + 22 D^{-1/3} D`. -/
theorem round_center_rate : ∀ᶠ n in atTop, ∀ X, IsOptimal n X →
    ∃ O : Plane, ∀ x ∈ X, dist x O ≤ diam X / 2 + 22 * diam X ^ (-(1 / 3 : ℝ)) * diam X := by
  filter_upwards [eventually_ge_atTop 2, tendsto_minDiam.eventually_ge_atTop (44 ^ 3)]
    with n hn hD X hX
  rw [← hX.diam_eq] at hD
  set D := diam X with hDdef
  have hD0 : 0 < D := by linarith
  set s := D ^ (1 / 3 : ℝ) with hs
  have hs3 : s ^ 3 = D := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hD0.le]; norm_num
  have hs0 : 0 < s := by positivity
  have hs44 : 44 ≤ s := by
    by_contra h; push_neg at h
    have : s ^ 3 < 44 ^ 3 := by gcongr
    linarith
  have hneg : D ^ (-(1 / 3 : ℝ)) = s⁻¹ := by rw [Real.rpow_neg hD0.le]
  rw [hneg]
  set η' := 22 * s⁻¹ with hη'
  have hη'0 : 0 < η' := by positivity
  have hη'1 : η' ≤ 1 / 2 := by
    rw [hη', ← div_eq_mul_inv, div_le_iff₀ hs0]; linarith
  have hsin : η' / (8 * π) ≤ Real.sin (η' / 16) := by
    have := Real.mul_le_sin (x := η' / 16) (by positivity) (by linarith [Real.pi_gt_three])
    calc η' / (8 * π) = 2 / π * (η' / 16) := by field_simp; ring
      _ ≤ _ := this
  have hη'D : η' ^ 3 * D = 22 ^ 3 := by
    rw [hη', ← hs3]; field_simp
  have hpi2 : π ^ 2 * 1024 ≤ 22 ^ 3 := by
    have := Real.pi_lt_d2
    nlinarith [Real.pi_pos]
  have hcD : π ≤ Real.sin (η' / 16) * η' ^ 2 / 128 * D := by
    have h1 : η' / (8 * π) * η' ^ 2 / 128 * D ≤ Real.sin (η' / 16) * η' ^ 2 / 128 * D := by
      gcongr
    refine le_trans ?_ h1
    have e : η' / (8 * π) * η' ^ 2 / 128 * D = 22 ^ 3 / (1024 * π) := by
      rw [← hη'D]; field_simp; ring
    rw [e, le_div_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]
  obtain ⟨O, hO⟩ := round_core hX hn hη'0 hη'1 hcD
  refine ⟨O, fun x hx => (hO x hx).trans ?_⟩
  have h3 : 3 ≤ η' * D := by
    rw [hη', ← hs3]
    have : 22 * s⁻¹ * s ^ 3 = 22 * s ^ 2 := by field_simp
    rw [this]; nlinarith
  nlinarith

/-- **Inner roundness, sharp form.**  As `exists_support_ge`, with the weaker requirement
`η ≤ δ^{3/2} / 25`: a rectangle of height `δD/2` and width `D √δ` fits into the empty cap. -/
theorem exists_support_ge_sharp {X : Finset Plane} (hX : IsSeparated X) {O ν : Plane}
    {D η δ : ℝ} (hν : ‖ν‖ = 1) (hD : 0 < D) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (hη : η ≤ δ * √δ / 25) (hηD : 1 ≤ η * D)
    (hlat : π * D ^ 2 / 4 ≤ X.card * (√3 / 2))
    (hball : ∀ x ∈ X, dist x O ≤ D / 2 + η * D) :
    ∃ x ∈ X, D / 2 - δ * D ≤ inner ℝ (x - O) ν := by
  by_contra hcon
  push_neg at hcon
  have hη0 : 0 < η := by
    by_contra h; push_neg at h; nlinarith
  have hsδ : √δ * √δ = δ := Real.mul_self_sqrt hδ0.le
  have hsδ0 : 0 < √δ := Real.sqrt_pos.2 hδ0
  have hsδ1 : √δ ≤ 1 := by nlinarith
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = D / 2 + η * D + 1 := ⟨_, rfl⟩
  obtain ⟨h', hh'⟩ : ∃ h' : ℝ, h' = D / 2 - δ * D + 1 := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = δ * D / 2 := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = D * √δ / 2 := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : Set Plane, K = ⋃ p ∈ X, Metric.closedBall p (1 : ℝ) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : Set Plane,
      P = paraOpen (O + h' • ν - w • rot ν) (c • ν) ((2 * w) • rot ν) := ⟨_, rfl⟩
  have hcr : cr (c • ν) ((2 * w) • rot ν) = 2 * c * w := by
    have h := norm_sq_coord ν
    rw [hν] at h
    simp only [cr, PiLp.smul_apply, smul_eq_mul, rot]
    simp
    linear_combination (-2 * c * w) * h
  have hc0 : 0 < c := by rw [hc]; positivity
  have hw0 : 0 < w := by rw [hw]; positivity
  have hcr0 : cr (c • ν) ((2 * w) • rot ν) ≠ 0 := by rw [hcr]; positivity
  -- points of `P`
  have hPpt : ∀ y ∈ P, h' < inner ℝ (y - O) ν ∧ ‖y - O‖ ≤ ρ := by
    rw [hP]
    rintro y ⟨α, β, hα0, hα1, hβ0, hβ1, rfl⟩
    have e : O + h' • ν - w • rot ν + α • (c • ν) + β • ((2 * w) • rot ν) =
        O + (h' + α * c) • ν + ((2 * β - 1) * w) • rot ν := by
      simp only [smul_smul, add_smul]; module
    obtain ⟨e1, e2⟩ := frame_coords hν e
    rw [e] at e1 e2 ⊢
    refine ⟨by rw [e1]; nlinarith only [hα0, hc0], ?_⟩
    have hh0 : 0 < h' := by rw [hh']; nlinarith only [hδ1, hD]
    have hq : ((2 * β - 1) * w) ^ 2 ≤ w ^ 2 := by
      have : (2 * β - 1) ^ 2 ≤ 1 := by nlinarith only [hβ0, hβ1]
      rw [mul_pow]; nlinarith only [this, sq_nonneg w]
    have hp : (h' + α * c) ^ 2 ≤ (h' + c) ^ 2 := by
      have : h' + α * c ≤ h' + c := by nlinarith only [hα1, hc0]
      exact pow_le_pow_left₀ (add_nonneg hh0.le (mul_nonneg hα0.le hc0.le)) this 2
    have hfin : (h' + c) ^ 2 + w ^ 2 ≤ ρ ^ 2 := by
      have e3 : (h' + c) ^ 2 + w ^ 2 = (D / 2 + 1) ^ 2 -
          δ * D * (D / 2 + 1 - δ * D / 4 - D / 4) := by
        subst hh' hc hw; ring_nf; rw [Real.sq_sqrt hδ0.le]; ring
      have e4 : 0 ≤ δ * D * (D / 2 + 1 - δ * D / 4 - D / 4) := by
        apply mul_nonneg (by positivity); nlinarith only [hδ1, hD, hδ0]
      have e5 : (D / 2 + 1) ^ 2 ≤ ρ ^ 2 := by
        subst hρ; nlinarith only [mul_pos hη0 hD, hD]
      linarith only [e3, e4, e5]
    have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
    have h6 : ‖O + (h' + α * c) • ν + ((2 * β - 1) * w) • rot ν - O‖ ^ 2 ≤ ρ ^ 2 := by
      linarith only [e2, hp, hq, hfin]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hρ0 two_ne_zero).1 h6
  -- points of `K`
  have hKpt : ∀ y ∈ K, inner ℝ (y - O) ν ≤ h' ∧ dist y O ≤ ρ := by
    intro y hy
    rw [hK] at hy
    obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 hy
    have hyx' := Metric.mem_closedBall.1 hyx
    refine ⟨?_, ?_⟩
    · have := inner_le_of_dist_le (O := O) hν hyx'
      have := hcon x hx
      rw [hh']; linarith
    · have := dist_triangle y x O
      have := hball x hx
      rw [hρ]; linarith
  have hdisj : Disjoint K P := by
    rw [Set.disjoint_left]
    intro y hyK hyP
    linarith [(hKpt y hyK).1, (hPpt y hyP).1]
  have hsub : K ∪ P ⊆ Metric.closedBall O ρ := by
    rintro y (hy | hy)
    · exact Metric.mem_closedBall.2 (hKpt y hy).2
    · rw [Metric.mem_closedBall, dist_eq_norm]; exact (hPpt y hy).2
  have hPm : MeasurableSet P := hP ▸ (isOpen_paraOpen hcr0).measurableSet
  have hvol : volume K + volume P ≤ volume (Metric.closedBall O ρ) := by
    rw [← measure_union hdisj hPm]; exact measure_mono hsub
  rw [hP, volume_paraOpen, hcr, EuclideanSpace.volume_closedBall_fin_two] at hvol
  have hcard := card_mul_le_volume_union hX
  rw [← hK] at hcard
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have h2 : ENNReal.ofReal (X.card * (√3 / 2)) + ENNReal.ofReal |2 * c * w| ≤
      ENNReal.ofReal (ρ ^ 2 * π) := by
    have e : ENNReal.ofReal (ρ ^ 2 * π) = ENNReal.ofReal ρ ^ 2 * ENNReal.ofReal π := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hρ0]
    rw [e]
    exact (add_le_add hcard le_rfl).trans hvol
  rw [← ENNReal.ofReal_add (by positivity) (abs_nonneg _),
    ENNReal.ofReal_le_ofReal_iff (by positivity), abs_of_pos (by positivity)] at h2
  -- numerics
  have hηD0 : 0 < η * D := by positivity
  have hD1 : D ≤ η * D ^ 2 := by nlinarith only [hηD, hD]
  have hηs : η ≤ 1 / 25 := by
    have : δ * √δ ≤ 1 := by nlinarith
    linarith
  have hηD2 : (η * D + 1) ^ 2 ≤ 4 * η * (η * D ^ 2) := by nlinarith only [hηD, hηD0]
  have hηD3 : 4 * η * (η * D ^ 2) ≤ η * D ^ 2 := by
    have : 0 ≤ η * D ^ 2 := by positivity
    nlinarith only [this, hηs]
  have hexp : ρ ^ 2 * π = π * D ^ 2 / 4 + π * (η * D ^ 2 + D + (η * D + 1) ^ 2) := by
    rw [hρ]; ring
  have hbig : π * (η * D ^ 2 + D + (η * D + 1) ^ 2) ≤ π * (3 * η * D ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
    linarith only [hD1, hηD2, hηD3]
  have h3 : 2 * c * w ≤ π * (3 * η * D ^ 2) := by linarith only [h2, hlat, hexp, hbig]
  have h4 : π * (3 * η * D ^ 2) ≤ 4 * (3 * (δ * √δ / 25) * D ^ 2) := by
    apply mul_le_mul Real.pi_le_four _ (by positivity) (by norm_num)
    have : 0 ≤ D ^ 2 := by positivity
    nlinarith only [this, hη]
  have h5 : 2 * c * w = δ * √δ * D ^ 2 / 2 := by rw [hc, hw]; ring
  have h6 : 0 < δ * √δ * D ^ 2 := by positivity
  linarith only [h3, h4, h5, h6]

/-! ## Counting hull sides near a direction -/

/-- The unit direction of a hull side. -/
def sideDir (p : Plane × Plane) : Plane := ‖p.2 - p.1‖⁻¹ • (p.2 - p.1)

/-- The standing geometric hypotheses: `X` lies in the disc of radius `D/2 + η D` about `O` and
reaches `D/2 - δ D` in every direction. -/
structure RoundData (X : Finset Plane) (O : Plane) (D η δ : ℝ) : Prop where
  ball : ∀ x ∈ X, dist x O ≤ D / 2 + η * D
  support : ∀ ν : Plane, ‖ν‖ = 1 → ∃ x ∈ X, D / 2 - δ * D ≤ inner ℝ (x - O) ν
  η_le : η ≤ δ
  η_nonneg : 0 ≤ η
  δ_le : δ ≤ 1
  D_pos : 0 < D

lemma norm_sideDir {p : Plane × Plane} (h : p.1 ≠ p.2) : ‖sideDir p‖ = 1 := by
  have h0 : ‖p.2 - p.1‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 (Ne.symm h))
  rw [sideDir, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ h0]

lemma det2_smul_left (c : ℝ) (d z : Plane) : det2 (c • d) z = c * det2 d z := by
  unfold det2; simp; ring

/-- The outward normal `-rot (sideDir p)` of a counterclockwise hull side supports `X`. -/
lemma inner_sideNormal_nonpos {X : Finset Plane} {p : Plane × Plane} (hp : IsCcwHullSide X p.1 p.2)
    {y : Plane} (hy : y ∈ X) : inner ℝ (y - p.1) (-rot (sideDir p)) ≤ 0 := by
  rw [inner_neg_right, inner_rot_eq_det2, sideDir, det2_smul_left, neg_nonpos]
  exact mul_nonneg (inv_nonneg.2 (norm_nonneg _)) (hp.2.2.2 y hy)

lemma inner_sideNormal_side (p : Plane × Plane) :
    inner ℝ (p.2 - p.1) (-rot (sideDir p)) = 0 := by
  rw [inner_neg_right, inner_rot_eq_det2, sideDir, det2_smul_left, neg_eq_zero]
  unfold det2; ring

/-- Endpoints of a hull side whose direction is within `ε` of `n` project near `⟨O, n⟩`. -/
lemma side_endpoint_proj {X : Finset Plane} {O : Plane} {D η δ : ℝ} (hR : RoundData X O D η δ)
    {p : Plane × Plane} (hp : IsCcwHullSide X p.1 p.2) {n : Plane} (hn : ‖n‖ = 1) {ε : ℝ}
    (hε : ‖sideDir p - n‖ ≤ ε) {x : Plane} (hx : x = p.1 ∨ x = p.2) :
    |inner ℝ (x - O) n| ≤ D * √(3 * δ) + D * ε / 2 := by
  set u := sideDir p with hu
  have hu1 : ‖u‖ = 1 := norm_sideDir hp.2.2.1
  set ν := -rot u with hν
  have hν1 : ‖ν‖ = 1 := by rw [hν, norm_neg, norm_rot, hu1]
  have hxX : x ∈ X := by
    rcases hx with rfl | rfl
    · exact mem_of_mem_hullVertices hp.1
    · exact mem_of_mem_hullVertices hp.2.1
  -- `x` is a support point for `ν`
  have hsupp : ∀ y ∈ X, inner ℝ (y - x) ν ≤ 0 := by
    intro y hy
    rcases hx with rfl | rfl
    · exact inner_sideNormal_nonpos hp hy
    · have e : y - p.2 = (y - p.1) - (p.2 - p.1) := by abel
      rw [e, inner_sub_left, inner_sideNormal_side, sub_zero]
      exact inner_sideNormal_nonpos hp hy
  obtain ⟨y, hyX, hy⟩ := hR.support ν hν1
  have hxν : D / 2 - δ * D ≤ inner ℝ (x - O) ν := by
    have e : x - O = (y - O) - (y - x) := by abel
    rw [e, inner_sub_left]
    linarith [hsupp y hyX]
  have hxO : ‖x - O‖ ≤ D / 2 + η * D := by rw [← dist_eq_norm]; exact hR.ball x hxX
  have hD := hR.D_pos
  -- distance to `O + (D/2) ν`
  set e := x - O - (D / 2) • ν with he
  have he2 : ‖e‖ ^ 2 ≤ 3 * δ * D ^ 2 := by
    have : ‖e‖ ^ 2 = ‖x - O‖ ^ 2 - D * inner ℝ (x - O) ν + D ^ 2 / 4 := by
      rw [he, norm_sub_sq_real, norm_smul, real_inner_smul_right, hν1, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0 : ℝ) < D / 2)]
      ring
    rw [this]
    have h1 : ‖x - O‖ ^ 2 ≤ (D / 2 + η * D) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hxO 2
    have hη := hR.η_le
    have hη0 := hR.η_nonneg
    have hδ := hR.δ_le
    have k1 : D * (D / 2 - δ * D) ≤ D * inner ℝ (x - O) ν := mul_le_mul_of_nonneg_left hxν hD.le
    have k2 : η + η ^ 2 ≤ 2 * δ := by nlinarith
    have k3 : (D / 2 + η * D) ^ 2 - D * (D / 2 - δ * D) + D ^ 2 / 4 =
        D ^ 2 * (η + η ^ 2 + δ) := by ring
    have k4 : D ^ 2 * (η + η ^ 2 + δ) ≤ D ^ 2 * (3 * δ) :=
      mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg D)
    nlinarith
  have hen : ‖e‖ ≤ D * √(3 * δ) := by
    have h3 : 0 ≤ 3 * δ := by have := hR.η_nonneg; have := hR.η_le; linarith
    rw [← Real.sqrt_sq (norm_nonneg e), show D * √(3 * δ) = √(3 * δ * D ^ 2) by
      rw [Real.sqrt_mul h3, Real.sqrt_sq hD.le, mul_comm]]
    exact Real.sqrt_le_sqrt he2
  -- the normal is almost orthogonal to `n`
  have hνn : |inner ℝ ν n| ≤ ε := by
    have e1 : inner ℝ ν n = -inner ℝ n (rot (u - n)) := by
      rw [hν, rot_sub, inner_neg_left, inner_sub_right, real_inner_comm, inner_rot_self]; ring
    rw [e1, abs_neg]
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [hn, norm_rot, one_mul]; exact hε
  have hsplit : inner ℝ (x - O) n = inner ℝ e n + D / 2 * inner ℝ ν n := by
    rw [he, inner_sub_left (x - O) ((D / 2) • ν) n, real_inner_smul_left]; ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  have h1 : |inner ℝ e n| ≤ ‖e‖ := by
    have := abs_real_inner_le_norm e n; rwa [hn, mul_one] at this
  have h2 : |D / 2 * inner ℝ ν n| ≤ D * ε / 2 := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < D / 2)]
    nlinarith
  linarith

/-- A hull side of a separated set, with direction within `3/4` of `n`, projects onto `ℝ n` with
length at least `1/2`. -/
lemma side_proj_ge {X : Finset Plane} (hX : IsSeparated X) {p : Plane × Plane}
    (hp : IsCcwHullSide X p.1 p.2) {n : Plane} (hn : ‖n‖ = 1) {ε : ℝ} (hε1 : ε ≤ 3 / 4)
    (hε : ‖sideDir p - n‖ ≤ ε) : 1 / 2 ≤ |inner ℝ (p.2 - p.1) n| := by
  have hu1 : ‖sideDir p‖ = 1 := norm_sideDir hp.2.2.1
  have hL : 1 ≤ ‖p.2 - p.1‖ := by
    rw [← dist_eq_norm]
    exact hX _ (mem_of_mem_hullVertices hp.2.1) _ (mem_of_mem_hullVertices hp.1)
      (Ne.symm hp.2.2.1)
  have hun : 23 / 32 ≤ inner ℝ (sideDir p) n := by
    have h := norm_sub_sq_real (sideDir p) n
    rw [hu1, hn] at h
    have : ‖sideDir p - n‖ ^ 2 ≤ 9 / 16 := by
      have h0 := norm_nonneg (sideDir p - n)
      nlinarith
    linarith
  have e : inner ℝ (p.2 - p.1) n = ‖p.2 - p.1‖ * inner ℝ (sideDir p) n := by
    have h0 : ‖p.2 - p.1‖ ≠ 0 := by linarith
    rw [sideDir, real_inner_smul_left, ← mul_assoc, mul_inv_cancel₀ h0, one_mul]
  rw [e]
  refine le_trans ?_ (le_abs_self _)
  nlinarith

lemma ccwHullSides_subset_hullPairs (X : Finset Plane) : ccwHullSides X ⊆ hullPairs X := by
  intro p hp
  have h := mem_ccwHullSides.1 hp
  unfold hullPairs
  exact Finset.mem_filter.2 ⟨Finset.mem_offDiag.2 ⟨h.1, h.2.1, h.2.2.1⟩,
    Or.inl fun x hx => h.2.2.2 x (mem_of_mem_hullVertices hx)⟩

/-- The number of hull sides with direction within `ε ≤ 3/4` of a unit vector `n`. -/
lemma card_sides_near_dir {X : Finset Plane} (hX : IsSeparated X) {O : Plane} {D η δ : ℝ}
    (hR : RoundData X O D η δ) {n : Plane} (hn : ‖n‖ = 1) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 3 / 4) :
    (((ccwHullSides X).filter (fun p => ‖sideDir p - n‖ ≤ ε)).card : ℝ) ≤
      16 * (D * √(3 * δ) + D * ε / 2) := by
  set S := (ccwHullSides X).filter (fun p => ‖sideDir p - n‖ ≤ ε) with hS
  set h := D * √(3 * δ) + D * ε / 2 with hh
  have hD := hR.D_pos
  have hh0 : 0 ≤ h := by positivity
  have hmem : ∀ p ∈ S, IsCcwHullSide X p.1 p.2 ∧ ‖sideDir p - n‖ ≤ ε := fun p hp =>
    ⟨mem_ccwHullSides.1 (Finset.mem_filter.1 hp).1, (Finset.mem_filter.1 hp).2⟩
  have hsum := sum_abs_inner_subset_le (X := X) (S := S)
    ((Finset.filter_subset _ _).trans (ccwHullSides_subset_hullPairs X)) hn
    (a0 := inner ℝ O n - h) (b0 := inner ℝ O n + h) (by linarith) (by
      intro p hp
      obtain ⟨hps, hpε⟩ := hmem p hp
      have k : ∀ x, x = p.1 ∨ x = p.2 → inner ℝ O n - h ≤ inner ℝ x n ∧
          inner ℝ x n ≤ inner ℝ O n + h := by
        intro x hx
        have := side_endpoint_proj hR hps hn hpε hx
        rw [inner_sub_left] at this
        constructor <;> linarith [abs_le.1 this]
      exact ⟨k _ (Or.inl rfl), k _ (Or.inr rfl)⟩)
  have hlow : (S.card : ℝ) * (1 / 2) ≤ ∑ p ∈ S, |inner ℝ (p.2 - p.1) n| := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun p hp =>
      side_proj_ge hX (hmem p hp).1 hn hε1 (hmem p hp).2
  linarith

/-- `dir6` of a nonzero vector is the sixth power of its unit direction. -/
lemma dir6_eq_pow_sideDir (p : Plane × Plane) : dir6 (p.2 - p.1) = (toC (sideDir p)) ^ 6 := by
  unfold dir6 sideDir
  rw [map_smul, Complex.real_smul, div_eq_inv_mul, Complex.ofReal_inv]

lemma card_ccwHullSides_le (X : Finset Plane) :
    (ccwHullSides X).card ≤ (hullVertices X).card := by
  refine Finset.card_le_card_of_injOn (fun p => p.1) (fun p hp => (mem_ccwHullSides.1 hp).1) ?_
  intro p hp q hq h
  simp only at h
  have hq' := mem_ccwHullSides.1 hq
  rw [← h] at hq'
  exact Prod.ext h ((mem_ccwHullSides.1 hp).succ_unique hq')

lemma norm_toC_sub_eq (a : Plane) (b : ℂ) : ‖toC a - b‖ = ‖a - toC.symm b‖ := by
  rw [← dist_eq_norm, ← dist_eq_norm, ← toC.symm.dist_map, LinearIsometryEquiv.symm_apply_apply]

/-- Hull sides with direction (mod `π/3`) within `ρ` of a single `c`. -/
lemma card_sides_near_dir6 {X : Finset Plane} (hX : IsSeparated X) (h2 : 2 ≤ X.card) {O : Plane}
    {η δ : ℝ} (hR : RoundData X O (diam X) η δ) (c : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (((ccwHullSides X).filter (fun p => ‖dir6 (p.2 - p.1) - c‖ ≤ ρ)).card : ℝ) ≤
      192 * diam X * (√δ + ρ) := by
  set D := diam X with hDdef
  have hD := hR.D_pos
  have hsδ := Real.sqrt_nonneg δ
  set F := (ccwHullSides X).filter (fun p => ‖dir6 (p.2 - p.1) - c‖ ≤ ρ) with hF
  by_cases hbig : 3 / 16 < ρ
  · have h1 : (F.card : ℝ) ≤ (hullVertices X).card := by
      exact_mod_cast (Finset.card_filter_le _ _).trans (card_ccwHullSides_le X)
    have h3 := hullVertices_card_le_pi_mul_diam hX h2
    have hpi := Real.pi_lt_d2
    nlinarith
  push_neg at hbig
  rcases F.eq_empty_or_nonempty with hF0 | ⟨q, hq⟩
  · rw [hF0, Finset.card_empty, Nat.cast_zero]; positivity
  obtain ⟨hqS, hqc⟩ := Finset.mem_filter.1 hq
  have hqs := mem_ccwHullSides.1 hqS
  set w := toC (sideDir q) with hw
  have hw1 : ‖w‖ = 1 := by rw [hw, norm_toC, norm_sideDir hqs.2.2.1]
  -- every side of `F` has direction close to `ζ w` for a sixth root of unity `ζ`
  have hcover : F ⊆ sixRoots.biUnion (fun ζ => (ccwHullSides X).filter
      (fun p => ‖sideDir p - toC.symm (ζ * w)‖ ≤ 4 * ρ)) := by
    intro p hp
    obtain ⟨hpS, hpc⟩ := Finset.mem_filter.1 hp
    have hps := mem_ccwHullSides.1 hpS
    have hz1 : ‖toC (sideDir p)‖ = 1 := by rw [norm_toC, norm_sideDir hps.2.2.1]
    have h6 : ‖toC (sideDir p) ^ 6 - w ^ 6‖ ≤ 2 * ρ := by
      rw [hw, ← dir6_eq_pow_sideDir, ← dir6_eq_pow_sideDir,
        show dir6 (p.2 - p.1) - dir6 (q.2 - q.1) =
          (dir6 (p.2 - p.1) - c) - (dir6 (q.2 - q.1) - c) by ring]
      refine (norm_sub_le _ _).trans ?_
      linarith
    obtain ⟨ζ, hζ, hnear⟩ := sixth_root_near hz1 hw1 (by linarith) h6
    refine Finset.mem_biUnion.2 ⟨ζ, hζ, Finset.mem_filter.2 ⟨hpS, ?_⟩⟩
    rw [← norm_toC_sub_eq]; linarith
  have hpiece : ∀ ζ ∈ sixRoots, ((((ccwHullSides X).filter
      (fun p => ‖sideDir p - toC.symm (ζ * w)‖ ≤ 4 * ρ)).card : ℕ) : ℝ) ≤
        16 * (D * √(3 * δ) + D * (4 * ρ) / 2) := by
    intro ζ hζ
    have hn : ‖toC.symm (ζ * w)‖ = 1 := by
      rw [LinearIsometryEquiv.norm_map, norm_mul, norm_of_mem_sixRoots hζ, hw1, one_mul]
    exact card_sides_near_dir hX hR hn (by positivity) (by linarith)
  have hcard : (F.card : ℝ) ≤ 6 * (16 * (D * √(3 * δ) + D * (4 * ρ) / 2)) := by
    have h1 : (F.card : ℝ) ≤ ∑ ζ ∈ sixRoots, ((((ccwHullSides X).filter
        (fun p => ‖sideDir p - toC.symm (ζ * w)‖ ≤ 4 * ρ)).card : ℕ) : ℝ) := by
      exact_mod_cast (Finset.card_le_card hcover).trans Finset.card_biUnion_le
    have h2 := Finset.sum_le_sum hpiece
    rw [Finset.sum_const, nsmul_eq_mul] at h2
    have h3 : (sixRoots.card : ℝ) ≤ 6 := by exact_mod_cast card_sixRoots_le
    have h4 : 0 ≤ 16 * (D * √(3 * δ) + D * (4 * ρ) / 2) := by positivity
    nlinarith
  have hs3 : √(3 * δ) ≤ 2 * √δ := by
    rw [Real.sqrt_mul (by norm_num)]
    have : √3 ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    exact mul_le_mul_of_nonneg_right this hsδ
  have : D * √(3 * δ) ≤ D * (2 * √δ) := mul_le_mul_of_nonneg_left hs3 hD.le
  nlinarith

/-- **Spread of hull directions, deterministic form.** -/
theorem hull_direction_spread_of_round {X : Finset Plane} (hX : IsSeparated X)
    (h2 : 2 ≤ X.card) {O : Plane} {η δ : ℝ} (hR : RoundData X O (diam X) η δ)
    (Cs : Finset ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (((ccwHullSides X).filter (fun p => ∃ c ∈ Cs, ‖dir6 (p.2 - p.1) - c‖ ≤ ρ)).card : ℝ) ≤
      192 * diam X * Cs.card * (√δ + ρ) := by
  have hsub : (ccwHullSides X).filter (fun p => ∃ c ∈ Cs, ‖dir6 (p.2 - p.1) - c‖ ≤ ρ) ⊆
      Cs.biUnion (fun c => (ccwHullSides X).filter (fun p => ‖dir6 (p.2 - p.1) - c‖ ≤ ρ)) := by
    intro p hp
    obtain ⟨hpS, c, hc, hpc⟩ := Finset.mem_filter.1 hp
    exact Finset.mem_biUnion.2 ⟨c, hc, Finset.mem_filter.2 ⟨hpS, hpc⟩⟩
  have h1 : (((ccwHullSides X).filter (fun p => ∃ c ∈ Cs, ‖dir6 (p.2 - p.1) - c‖ ≤ ρ)).card : ℝ)
      ≤ ∑ c ∈ Cs, ((((ccwHullSides X).filter
        (fun p => ‖dir6 (p.2 - p.1) - c‖ ≤ ρ)).card : ℕ) : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have h2' := Finset.sum_le_sum fun c (_ : c ∈ Cs) => card_sides_near_dir6 hX h2 hR c hρ
  rw [Finset.sum_const, nsmul_eq_mul] at h2'
  linarith

/-- **Lemma 3.2 (spread of boundary directions), with error term `D^{-1/9}`.** -/
theorem hull_direction_spread_rate : ∃ C : ℝ, ∀ᶠ n in atTop, ∀ X, IsOptimal n X →
    ∀ (Cs : Finset ℂ) (ρ : ℝ), 0 ≤ ρ →
      (((ccwHullSides X).filter (fun p => ∃ c ∈ Cs, ‖dir6 (p.2 - p.1) - c‖ ≤ ρ)).card : ℝ) ≤
        C * diam X * Cs.card * (ρ + diam X ^ (-(1 / 9 : ℝ))) := by
  refine ⟨1920, ?_⟩
  filter_upwards [eventually_ge_atTop 2, round_center_rate,
    tendsto_minDiam.eventually_ge_atTop (20 ^ 9)] with n hn hrc hD X hX Cs ρ hρ
  rw [← hX.diam_eq] at hD
  obtain ⟨O, hO⟩ := hrc X hX
  set D := diam X with hDdef
  have hD0 : 0 < D := by linarith
  set s := D ^ (1 / 9 : ℝ) with hs
  have hs9 : s ^ 9 = D := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hD0.le]; norm_num
  have hs0 : 0 < s := by positivity
  have hs20 : 20 ≤ s := by
    by_contra h; push_neg at h
    have : s ^ 9 < 20 ^ 9 := by gcongr
    linarith
  have h3 : D ^ (-(1 / 3 : ℝ)) = (s ^ 3)⁻¹ := by
    have : s ^ 3 = D ^ (1 / 3 : ℝ) := by
      rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hD0.le]; norm_num
    rw [Real.rpow_neg hD0.le, this]
  have h9 : D ^ (-(1 / 9 : ℝ)) = s⁻¹ := by rw [Real.rpow_neg hD0.le]
  rw [h3] at hO
  rw [h9]
  set η := 22 * (s ^ 3)⁻¹ with hη
  set δ := 100 * (s ^ 2)⁻¹ with hδ
  have hsqδ : √δ = 10 * s⁻¹ := by
    rw [hδ, show (100 : ℝ) * (s ^ 2)⁻¹ = (10 * s⁻¹) ^ 2 by field_simp; norm_num]
    exact Real.sqrt_sq (by positivity)
  have hη0 : 0 ≤ η := by positivity
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 / 2 := by
    rw [hδ, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]; nlinarith
  have hηδ : η ≤ δ := by
    rw [hη, hδ, ← div_eq_mul_inv, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity)
      (by positivity)]
    nlinarith [pow_pos hs0 2]
  have hηδ' : η ≤ δ * √δ / 25 := by
    rw [hsqδ, hη, hδ]
    have : 100 * (s ^ 2)⁻¹ * (10 * s⁻¹) / 25 = 40 * (s ^ 3)⁻¹ := by field_simp; ring
    rw [this]
    have : 0 < (s ^ 3)⁻¹ := by positivity
    linarith
  have hηD : 1 ≤ η * D := by
    rw [hη, ← hs9]
    have : 22 * (s ^ 3)⁻¹ * s ^ 9 = 22 * s ^ 6 := by field_simp
    rw [this]
    have : 1 ≤ s ^ 6 := one_le_pow₀ (by linarith)
    linarith
  have hlat : π * D ^ 2 / 4 ≤ X.card * (√3 / 2) := by
    have h := minDiam_sq_le n (by omega)
    rw [← hX.diam_eq] at h
    unfold aStar at h
    rw [le_div_iff₀ Real.pi_pos] at h
    rw [hX.1.1]
    linarith
  have hR : RoundData X O D η δ :=
    { ball := hO
      support := fun ν hν => exists_support_ge_sharp hX.1.2 hν hD0 hδ0 hδ1 hηδ' hηD hlat hO
      η_le := hηδ
      η_nonneg := hη0
      δ_le := by linarith
      D_pos := hD0 }
  have key := hull_direction_spread_of_round hX.1.2 (by rw [hX.1.1]; exact hn) hR Cs hρ
  rw [hsqδ] at key
  refine key.trans (le_of_eq_of_le rfl ?_)
  have : 0 ≤ D * Cs.card := by positivity
  have hsi : 0 ≤ s⁻¹ := by positivity
  nlinarith

end Erdos99

end

end HullSpread

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `PropagationLedger`
-/

section PropagationLedger

/-!
# WP7, arithmetic layer: the absorption ledger of the finite propagation process

This file contains the configuration-independent part of work package WP7 (`FinitePropagation`,
§9 of the Verification Guide).  Everything here is about real numbers, natural numbers and finite
sets; the geometric statements about an optimal configuration are in `FinitePropagation`.

* **Per-face net absorption** (§9.4 with the capacities of §8.1–§8.2).  A `k`-face that receives
  `a` tokens absorbs `a` of them, except that a pentagon re-emits one token on its second arrival
  and a heptagon re-emits one token on its third arrival (`netAbsorbed k a`).  When `a` is at most
  the marked-edge capacity of §8 (`markedCap k`: `2, 2, 3, 3` for `k = 5, 6, 7, 8` and
  `(k - 4) - (k - 8)/4` for `k ≥ 9`), the net absorption is at most
  `faceNetCap k = (k - 4) - [k = 7] - [k = 8] - (k - 8)₊ / 4` (`netAbsorbed_le_faceNetCap`).
  Summed over the exceptional faces this is `σ - f₇ - f₈ - Q₉/4` (`sum_faceNetCap`).
* **Per-return absorption** (§8.3): at most `2 (j - 2)₊ / 3` tokens per hull return of `j` edges
  (`returnCap_le`), hence at most `2ρ/3` in total.
* **High-face incidences**: `k ≤ 7 [k = 7] + 8 [k = 8] + 9 (k - 8)₊` for `k ≥ 7`
  (`le_highIncidence`), so `Σ_{k ≥ 7} k f_k ≤ 7 f₇ + 8 f₈ + 9 Q₉`.
* **Conservation** (§9.4): the ledger identity at a round gives `F_j ≥ S_def - B`
  (`frontier_ge_of_ledger`), and with the single-emission bound `Σ_j F_j ≤ p + f₇` this yields
  (S1), `K S_def ≤ p + f₇ + K B` (`conservation_S1`), and then the stability bounds
  (`stability_of_S1`, `stability_eventually`).
* **The length scales of §9.2**: `e_j = 1/(20·4^j)`, `Λ_j = D^{1 - e_j}`, the recursion
  `e_{j} = 4 e_{j+1}`, and the `o(D)` statements for the lost-output bound
  (`tendsto_rpow_div_self`, `lossBound_div_tendsto`).
* **Two-arc covering on the circle** (§9.3, second of the three large-receiver lemmas):
  if no three points of a finite set of reals are pairwise at distance `≥ a` (on a line, see the
  docstring), the set is covered by two intervals of length `< 2a` (`two_interval_cover`).
* **Triangle area estimates** (§9.3, first large-receiver lemma): twice the area of a triangle
  changes by at most `24 δ R` when its vertices are moved by `δ` in each coordinate inside the
  square `[-R, R]²` (`triArea_perturb`), and an inscribed triangle with sides `≥ s` in a circle
  of radius `R` has twice its area `≥ s³ / (2R)` (`inscribed_sides_sq`, `triDet_inscribed_ge`).
-/

open scoped BigOperators Real
open Filter Topology

@[expose] public noncomputable section

namespace Erdos99

namespace Propagation

/-! ## Face capacities -/

/-- The marked-edge capacity of a `k`-face from §8.1–§8.2 of the Verification Guide: `2` for
pentagons and hexagons, `3` for heptagons and octagons, and `(k - 4) - (k - 8)/4` for `k ≥ 9`. -/
def markedCap (k : ℕ) : ℝ :=
  if k ≤ 6 then 2 else if k ≤ 8 then 3 else ((k : ℝ) - 4) - ((k : ℝ) - 8) / 4

/-- The number of tokens absorbed (not re-emitted) by a `k`-face receiving `a` tokens: a pentagon
re-emits on its second arrival and a heptagon on its third. -/
def netAbsorbed (k a : ℕ) : ℝ :=
  (a : ℝ) - (if k = 5 ∧ 2 ≤ a then 1 else 0) - (if k = 7 ∧ 3 ≤ a then 1 else 0)

/-- The number of tokens re-emitted by a `k`-face receiving `a` tokens (`0` or `1`). -/
def emitted (k a : ℕ) : ℕ := if (k = 5 ∧ 2 ≤ a) ∨ (k = 7 ∧ 3 ≤ a) then 1 else 0

/-- Net absorption capacity of a `k`-face, `(k - 4) - [k = 7] - [k = 8] - (k - 8)₊ / 4`. -/
def faceNetCap (k : ℕ) : ℝ :=
  ((k : ℝ) - 4) - (if k = 7 then 1 else 0) - (if k = 8 then 1 else 0) - ((k - 8 : ℕ) : ℝ) / 4

lemma faceNetCap_five : faceNetCap 5 = 1 := by norm_num [faceNetCap]
lemma faceNetCap_six : faceNetCap 6 = 2 := by norm_num [faceNetCap]
lemma faceNetCap_seven : faceNetCap 7 = 2 := by norm_num [faceNetCap]
lemma faceNetCap_eight : faceNetCap 8 = 3 := by norm_num [faceNetCap]

lemma faceNetCap_of_nine_le {k : ℕ} (hk : 9 ≤ k) :
    faceNetCap k = ((k : ℝ) - 4) - ((k : ℝ) - 8) / 4 := by
  unfold faceNetCap
  rw [if_neg (by omega), if_neg (by omega), Nat.cast_sub (by omega)]
  push_cast; ring

/-- Received tokens = absorbed + re-emitted. -/
lemma netAbsorbed_add_emitted (k a : ℕ) : netAbsorbed k a + emitted k a = a := by
  unfold netAbsorbed emitted
  by_cases h5 : k = 5 ∧ 2 ≤ a
  · have h7 : ¬ (k = 7 ∧ 3 ≤ a) := by omega
    simp [h5]
  · by_cases h7 : k = 7 ∧ 3 ≤ a
    · simp [h7]
    · simp [h5, h7]

/-- Only pentagons and heptagons emit. -/
lemma emitted_eq_zero {k a : ℕ} (hk : k ≠ 5 ∧ k ≠ 7) : emitted k a = 0 := by
  unfold emitted; rw [if_neg (by omega)]

/-- **Net face absorption** (§9.4): for a face with at least five sides, if the number of
arrivals is within the marked-edge capacity of §8, the net absorption is at most
`faceNetCap k`. -/
theorem netAbsorbed_le_faceNetCap {k a : ℕ} (hk : 5 ≤ k) (ha : (a : ℝ) ≤ markedCap k) :
    netAbsorbed k a ≤ faceNetCap k := by
  unfold markedCap at ha
  rcases (show k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ 9 ≤ k by omega) with rfl | rfl | rfl | rfl | h9
  · norm_num at ha
    have : a ≤ 2 := by exact_mod_cast ha
    rw [faceNetCap_five]; unfold netAbsorbed
    interval_cases a <;> norm_num
  · norm_num at ha
    rw [faceNetCap_six]; unfold netAbsorbed; norm_num; exact ha
  · norm_num at ha
    have : a ≤ 3 := by exact_mod_cast ha
    rw [faceNetCap_seven]; unfold netAbsorbed
    interval_cases a <;> norm_num
  · norm_num at ha
    rw [faceNetCap_eight]; unfold netAbsorbed; norm_num; exact ha
  · rw [if_neg (by omega), if_neg (by omega)] at ha
    rw [faceNetCap_of_nine_le h9]; unfold netAbsorbed
    rw [if_neg (by omega), if_neg (by omega)]; linarith

/-- `faceNetCap k = (k - 4) - [k = 7] - [k = 8] - (k - 8)₊/4`, summed over a finite family of
faces with at least five sides: `σ - f₇ - f₈ - Q₉/4`. -/
theorem sum_faceNetCap {ι : Type*} (s : Finset ι) (size : ι → ℕ) (hs : ∀ i ∈ s, 5 ≤ size i) :
    ∑ i ∈ s, faceNetCap (size i) =
      (∑ i ∈ s, ((size i - 4 : ℕ) : ℝ)) - (s.filter (fun i => size i = 7)).card
        - (s.filter (fun i => size i = 8)).card - (∑ i ∈ s, ((size i - 8 : ℕ) : ℝ)) / 4 := by
  rw [Finset.card_filter, Finset.card_filter, Finset.sum_div]
  push_cast
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have := hs i hi
  unfold faceNetCap
  rw [Nat.cast_sub (by omega : 4 ≤ size i)]
  push_cast
  split_ifs <;> ring

/-! ## Hull-return capacities (§8.3) -/

/-- The absorption capacity of a hull return of `j` unit edges: `0` for `j ≤ 3`, `1` for `j = 4`,
`2` for `j = 5`, and `2 (j - 2)/3` for `j ≥ 6`. -/
def returnCap (j : ℕ) : ℝ :=
  if j ≤ 3 then 0 else if j = 4 then 1 else if j = 5 then 2 else 2 * ((j : ℝ) - 2) / 3

/-- **Cap absorption** (§8.3): `returnCap j ≤ 2 (j - 2)₊ / 3`; summed over the hull sides this is
the cap-absorption bound `2ρ/3`. -/
theorem returnCap_le (j : ℕ) : returnCap j ≤ 2 * ((j - 2 : ℕ) : ℝ) / 3 := by
  unfold returnCap
  split_ifs with h3 h4 h5
  · positivity
  · subst h4; norm_num
  · subst h5; norm_num
  · rw [Nat.cast_sub (by omega)]; push_cast; linarith

theorem sum_returnCap_le {ι : Type*} (s : Finset ι) (len : ι → ℕ) :
    ∑ i ∈ s, returnCap (len i) ≤ 2 * (∑ i ∈ s, ((len i - 2 : ℕ) : ℝ)) / 3 := by
  rw [Finset.mul_sum, Finset.sum_div]
  exact Finset.sum_le_sum (fun i _ => returnCap_le (len i))

/-! ## High-face incidences -/

/-- `k ≤ 7 [k = 7] + 8 [k = 8] + 9 (k - 8)₊` for every `k ≥ 7`. -/
lemma le_highIncidence {k : ℕ} (hk : 7 ≤ k) :
    (k : ℝ) ≤ 7 * (if k = 7 then 1 else 0) + 8 * (if k = 8 then 1 else 0) + 9 * ((k - 8 : ℕ) : ℝ) := by
  rcases (show k = 7 ∨ k = 8 ∨ 9 ≤ k by omega) with rfl | rfl | h9
  · norm_num
  · norm_num
  · rw [if_neg (by omega), if_neg (by omega), Nat.cast_sub (by omega)]
    have : (9 : ℝ) ≤ k := by exact_mod_cast h9
    push_cast; linarith

/-- **The high-face incidence budget** (end of §9.4):
`Σ_{k ≥ 7} k f_k ≤ 7 f₇ + 8 f₈ + 9 Q₉`. -/
theorem sum_highIncidence_le {ι : Type*} (s : Finset ι) (size : ι → ℕ) :
    ∑ i ∈ s.filter (fun i => 7 ≤ size i), (size i : ℝ) ≤
      7 * (s.filter (fun i => size i = 7)).card + 8 * (s.filter (fun i => size i = 8)).card
        + 9 * ∑ i ∈ s, ((size i - 8 : ℕ) : ℝ) := by
  have h7 : (s.filter (fun i => size i = 7)) = (s.filter (fun i => 7 ≤ size i)).filter
      (fun i => size i = 7) := by
    rw [Finset.filter_filter]; congr 1; ext i; omega
  have h8 : (s.filter (fun i => size i = 8)) = (s.filter (fun i => 7 ≤ size i)).filter
      (fun i => size i = 8) := by
    rw [Finset.filter_filter]; congr 1; ext i; omega
  have hQ : ∑ i ∈ s.filter (fun i => 7 ≤ size i), ((size i - 8 : ℕ) : ℝ) ≤
      ∑ i ∈ s, ((size i - 8 : ℕ) : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
  rw [h7, h8, Finset.card_filter, Finset.card_filter]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum]
  have key : ∑ i ∈ s.filter (fun i => 7 ≤ size i), (size i : ℝ) ≤
      ∑ i ∈ s.filter (fun i => 7 ≤ size i), (7 * (if size i = 7 then (1 : ℝ) else 0) +
        8 * (if size i = 8 then 1 else 0) + 9 * ((size i - 8 : ℕ) : ℝ)) :=
    Finset.sum_le_sum (fun i hi => le_highIncidence (Finset.mem_filter.1 hi).2)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at key
  have hQ' : ∑ i ∈ s.filter (fun i => 7 ≤ size i), 9 * ((size i - 8 : ℕ) : ℝ) ≤
      9 * ∑ i ∈ s, ((size i - 8 : ℕ) : ℝ) := by rw [← Finset.mul_sum]; linarith
  linarith

/-! ## Conservation and (S1) -/

/-- **The ledger at one round** (§9.4).  Suppose that the `u - Bsrc` source tokens still under
control are, after some round, either absorbed at faces (`Aface`), absorbed at caps (`Acap`),
lost (`Lost`), or live on the frontier (`F`); that net face absorption is at most
`σ - f₇ - f₈ - Q₉/4 + B₁`, cap absorption at most `2ρ/3 + B₂`, and losses at most `B₃`.  Since
`Δ = u - σ - ρ`, the frontier satisfies `F ≥ S_def - B` with
`S_def = Δ + ρ/3 + f₇ + f₈ + Q₉/4` and `B = Bsrc + B₁ + B₂ + B₃`. -/
theorem frontier_ge_of_ledger {u σ ρ Δ f₇ f₈ Q₉ Aface Acap Lost F Bsrc B₁ B₂ B₃ : ℝ}
    (hΔ : Δ = u - σ - ρ) (hcons : u - Bsrc ≤ Aface + Acap + Lost + F)
    (hface : Aface ≤ σ - f₇ - f₈ - Q₉ / 4 + B₁) (hcap : Acap ≤ 2 * ρ / 3 + B₂)
    (hlost : Lost ≤ B₃) :
    (Δ + ρ / 3 + f₇ + f₈ + Q₉ / 4) - (Bsrc + B₁ + B₂ + B₃) ≤ F := by
  subst hΔ; linarith

/-- **(S1)** (§9.4).  If each of the frontiers `F 1, …, F K` is at least `S - B`, and their total
is at most `N` (each pentagon or heptagon emits at most once, so `N = p + f₇`), then
`K S ≤ N + K B`. -/
theorem conservation_S1 (K : ℕ) (F : ℕ → ℝ) {S B N : ℝ}
    (hF : ∀ j ∈ Finset.Icc 1 K, S - B ≤ F j) (hsum : ∑ j ∈ Finset.Icc 1 K, F j ≤ N) :
    K * S ≤ N + K * B := by
  have h := Finset.card_nsmul_le_sum (Finset.Icc 1 K) F (S - B) hF
  rw [Nat.card_Icc, nsmul_eq_mul] at h
  simp only [add_tsub_cancel_right] at h
  nlinarith

/-- **Stability from (S1).**  If `Δ, ρ, f₇, f₈, Q₉ ≥ 0`, `K ≥ 1`, (S1) holds with `N ≤ π D`, then each
of `Δ, ρ/3, f₇, f₈, Q₉/4` is at most `π D / K + B`. -/
theorem stability_of_S1 {K : ℕ} (hK : 0 < K) {Δ ρ f₇ f₈ Q₉ N B D : ℝ}
    (hΔ : 0 ≤ Δ) (hρ : 0 ≤ ρ) (h7 : 0 ≤ f₇) (h8 : 0 ≤ f₈) (hQ : 0 ≤ Q₉)
    (hS1 : K * (Δ + ρ / 3 + f₇ + f₈ + Q₉ / 4) ≤ N + K * B) (hN : N ≤ π * D) :
    Δ ≤ π * D / K + B ∧ ρ / 3 ≤ π * D / K + B ∧ f₇ ≤ π * D / K + B ∧ f₈ ≤ π * D / K + B ∧
      Q₉ / 4 ≤ π * D / K + B := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hS : Δ + ρ / 3 + f₇ + f₈ + Q₉ / 4 ≤ π * D / K + B := by
    rw [div_add' _ _ _ hK'.ne', le_div_iff₀ hK']; nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- **Choice of the depth `K`, then of `D₀`** (§9.4).  Let `η > 0`.  Choose `K > 8π/η`; if
`B(D)/D → 0` then eventually `B(D) ≤ (η/8) D`, and every quantity bounded by `π D / K + B(D)`
is at most `η D / 4`. -/
theorem stability_eventually {η : ℝ} (hη : 0 < η) {K : ℕ} (hK : 8 * π / η < K) {B : ℝ → ℝ}
    (hB : Tendsto (fun D => B D / D) atTop (𝓝 0)) :
    ∀ᶠ D in atTop, π * D / K + B D ≤ η / 4 * D := by
  have hK0 : (0 : ℝ) < K := lt_trans (by positivity) hK
  have hev : ∀ᶠ D in atTop, B D / D < η / 8 := (tendsto_order.1 hB).2 _ (by positivity)
  filter_upwards [hev, eventually_gt_atTop 0] with D hD hD0
  rw [div_lt_iff₀ hD0] at hD
  have h1 : π / K < η / 8 := by
    rw [div_lt_iff₀ hK0]
    rw [div_lt_iff₀ hη] at hK
    nlinarith
  have h2 : π * D / K = π / K * D := by ring
  rw [h2]
  nlinarith

/-! ## Length scales (§9.2) -/

/-- The exponent `e_j = 1/(20 · 4^j)` of the `j`-th length scale. -/
def scaleExp (j : ℕ) : ℝ := 1 / (20 * 4 ^ j)

/-- The length scale `Λ_j = D^{1 - e_j}`. -/
def scale (D : ℝ) (j : ℕ) : ℝ := D ^ (1 - scaleExp j)

lemma scaleExp_pos (j : ℕ) : 0 < scaleExp j := by unfold scaleExp; positivity

lemma scaleExp_le (j : ℕ) : scaleExp j ≤ 1 / 20 := by
  unfold scaleExp
  apply one_div_le_one_div_of_le (by norm_num)
  have : (1 : ℝ) ≤ 4 ^ j := one_le_pow₀ (by norm_num)
  linarith

/-- `e_j = 4 e_{j+1}`: the input angle error `D^{-e_j/2}` of round `j+1` equals the heptagon
output error `D^{-2 e_{j+1}}` after taking a square root. -/
lemma scaleExp_succ (j : ℕ) : scaleExp j = 4 * scaleExp (j + 1) := by
  unfold scaleExp; rw [pow_succ]; field_simp

lemma scaleExp_anti {i j : ℕ} (h : i ≤ j) : scaleExp j ≤ scaleExp i := by
  unfold scaleExp
  apply one_div_le_one_div_of_le (by positivity)
  have : (4 : ℝ) ^ i ≤ 4 ^ j := pow_le_pow_right₀ (by norm_num) h
  linarith

/-- The scales increase with `j` (for `D ≥ 1`). -/
lemma scale_mono {D : ℝ} (hD : 1 ≤ D) {i j : ℕ} (h : i ≤ j) : scale D i ≤ scale D j := by
  unfold scale
  exact Real.rpow_le_rpow_of_exponent_le hD (by linarith [scaleExp_anti h])

/-- `D^a / D → 0` for every exponent `a < 1`. -/
theorem tendsto_rpow_div_self {a : ℝ} (ha : a < 1) :
    Tendsto (fun D : ℝ => D ^ a / D) atTop (𝓝 0) := by
  have h := tendsto_rpow_neg_atTop (show 0 < 1 - a by linarith)
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with D hD
  rw [Real.rpow_neg hD.le, Real.rpow_sub hD, Real.rpow_one, inv_div]

/-- A finite combination `Σ cᵢ D^{aᵢ}` with all exponents `aᵢ < 1` is `o(D)`. -/
theorem tendsto_sum_rpow_div_self {ι : Type*} (s : Finset ι) (c a : ι → ℝ) (ha : ∀ i ∈ s, a i < 1) :
    Tendsto (fun D : ℝ => (∑ i ∈ s, c i * D ^ a i) / D) atTop (𝓝 0) := by
  have : (fun D : ℝ => (∑ i ∈ s, c i * D ^ a i) / D) = fun D => ∑ i ∈ s, c i * (D ^ a i / D) := by
    funext D; rw [Finset.sum_div]; congr 1; funext i; ring
  rw [this]
  rw [show (0 : ℝ) = ∑ i ∈ s, c i * 0 by simp]
  exact tendsto_finset_sum _ (fun i hi => (tendsto_rpow_div_self (ha i hi)).const_mul (c i))

/-- **The lost-output bound of §9.2–§9.3** has the shape
`B_loss(K, D) = C (Σ_{j ≤ K} (D^{1/4 + e_j} + D^{1 - e_j} + D^{1 - 1/9 + e_j}) + D^{1 - e_K/8})`;
for every fixed `K` and `C` it is `o(D)`.  (All exponents are `< 1` because `e_j ≤ 1/20 < 1/9`.) -/
def lossBound (C : ℝ) (K : ℕ) (D : ℝ) : ℝ :=
  C * (∑ j ∈ Finset.range (K + 1),
      (D ^ (1 / 4 + scaleExp j) + D ^ (1 - scaleExp j) + D ^ (1 - 1 / 9 + scaleExp j))
    + D ^ (1 - scaleExp K / 8))

theorem lossBound_div_tendsto (C : ℝ) (K : ℕ) :
    Tendsto (fun D => lossBound C K D / D) atTop (𝓝 0) := by
  unfold lossBound
  have hsum : Tendsto (fun D : ℝ => (∑ j ∈ Finset.range (K + 1),
      (D ^ (1 / 4 + scaleExp j) + D ^ (1 - scaleExp j) + D ^ (1 - 1 / 9 + scaleExp j))) / D)
      atTop (𝓝 0) := by
    have e : (fun D : ℝ => (∑ j ∈ Finset.range (K + 1),
        (D ^ (1 / 4 + scaleExp j) + D ^ (1 - scaleExp j) + D ^ (1 - 1 / 9 + scaleExp j))) / D) =
        fun D => ∑ j ∈ Finset.range (K + 1), (D ^ (1 / 4 + scaleExp j) / D +
          D ^ (1 - scaleExp j) / D + D ^ (1 - 1 / 9 + scaleExp j) / D) := by
      funext D; rw [Finset.sum_div]; congr 1; funext j; ring
    rw [e, show (0 : ℝ) = ∑ j ∈ Finset.range (K + 1), ((0 : ℝ) + 0 + 0) by simp]
    refine tendsto_finset_sum _ (fun j _ => ?_)
    have h1 := scaleExp_le j
    have h2 := scaleExp_pos j
    exact ((tendsto_rpow_div_self (by linarith)).add (tendsto_rpow_div_self (by linarith))).add
      (tendsto_rpow_div_self (by linarith))
  have hlast := tendsto_rpow_div_self (show 1 - scaleExp K / 8 < 1 by linarith [scaleExp_pos K])
  have := (hsum.add hlast).const_mul C
  rw [add_zero, mul_zero] at this
  refine this.congr (fun D => ?_)
  ring

/-! ## Two-interval covering (§9.3) -/

/-- **Two-interval covering.**  Let `S` be a finite set of reals in which no three points are
pairwise at distance at least `a`.  Then `S` is covered by two intervals of length less than
`2a`: there are `x, y` such that every point of `S` lies within distance `< a` of `x` or of `y`.

(This is the two-arc covering consequence of §9.3, stated for positions along an arc of the hull
parametrised by arc length; on the whole circle it is applied after cutting at a point of `S`.) -/
theorem two_interval_cover (S : Finset ℝ) {a : ℝ}
    (hS : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, a ≤ |x - y| → a ≤ |y - z| → a ≤ |x - z| → False) :
    ∃ x y : ℝ, ∀ s ∈ S, |s - x| < a ∨ |s - y| < a := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, 0, by simp⟩
  set m := S.min' hne
  set M := S.max' hne
  have hm : m ∈ S := S.min'_mem hne
  have hM : M ∈ S := S.max'_mem hne
  by_cases hmM : M - m < a
  · refine ⟨m, m, fun s hs => Or.inl ?_⟩
    have h1 := S.min'_le s hs
    have h2 := S.le_max' s hs
    rw [abs_lt]; constructor <;> linarith
  · push_neg at hmM
    -- every point is within `< a` of `m` or of `M`
    refine ⟨m, M, fun s hs => ?_⟩
    have h1 := S.min'_le s hs
    have h2 := S.le_max' s hs
    by_contra hcon
    push_neg at hcon
    obtain ⟨c1, c2⟩ := hcon
    rw [abs_of_nonneg (by linarith)] at c1
    rw [abs_of_nonpos (by linarith)] at c2
    exact hS m hm s hs M hM (by rw [abs_of_nonpos (by linarith)]; linarith)
      (by rw [abs_of_nonpos (by linarith)]; linarith)
      (by rw [abs_of_nonpos (by linarith)]; linarith)

/-! ## Triangle areas (§9.3) -/

/-- Twice the signed area of the triangle `p q r` in coordinates. -/
def triDet (p q r : ℝ × ℝ) : ℝ := (q.1 - p.1) * (r.2 - p.2) - (r.1 - p.1) * (q.2 - p.2)

/-- `triDet` is unchanged by translations, written out as an identity. -/
lemma triDet_eq (p q r : ℝ × ℝ) :
    triDet p q r = p.1 * q.2 - q.1 * p.2 + q.1 * r.2 - r.1 * q.2 + r.1 * p.2 - p.1 * r.2 := by
  unfold triDet; ring

/-- **Area perturbation.**  Moving one vertex of a triangle by `δ` changes twice its area by at
most `δ` times the distance between the other two vertices (sup norms). -/
lemma triDet_move_first (p p' q r : ℝ × ℝ) :
    |triDet p q r - triDet p' q r| ≤ (|p.1 - p'.1| + |p.2 - p'.2|) * (|q.1 - r.1| + |q.2 - r.2|) := by
  have e : triDet p q r - triDet p' q r = (p.1 - p'.1) * (q.2 - r.2) - (p.2 - p'.2) * (q.1 - r.1) := by
    unfold triDet; ring
  rw [e]
  calc |(p.1 - p'.1) * (q.2 - r.2) - (p.2 - p'.2) * (q.1 - r.1)|
      ≤ |p.1 - p'.1| * |q.2 - r.2| + |p.2 - p'.2| * |q.1 - r.1| := by
        rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
    _ ≤ _ := by
        have := abs_nonneg (p.1 - p'.1); have := abs_nonneg (p.2 - p'.2)
        have := abs_nonneg (q.1 - r.1); have := abs_nonneg (q.2 - r.2)
        nlinarith

lemma triDet_cycle (p q r : ℝ × ℝ) : triDet p q r = triDet q r p := by unfold triDet; ring

/-- **Area perturbation of a triangle** (first large-receiver lemma of §9.3, error part).  If the
three vertices are moved by at most `δ` in each coordinate, and all six points have coordinates
of absolute value at most `R`, then twice the area changes by at most `3 · 2δ · 4R`. -/
theorem triArea_perturb {p q r p' q' r' : ℝ × ℝ} {δ R : ℝ}
    (hp : |p.1 - p'.1| ≤ δ ∧ |p.2 - p'.2| ≤ δ) (hq : |q.1 - q'.1| ≤ δ ∧ |q.2 - q'.2| ≤ δ)
    (hr : |r.1 - r'.1| ≤ δ ∧ |r.2 - r'.2| ≤ δ)
    (hb : ∀ z ∈ ({p, q, r, p', q', r'} : Set (ℝ × ℝ)), |z.1| ≤ R ∧ |z.2| ≤ R) :
    |triDet p q r - triDet p' q' r'| ≤ 3 * (2 * δ) * (4 * R) := by
  have bd : ∀ z ∈ ({p, q, r, p', q', r'} : Set (ℝ × ℝ)), ∀ w ∈ ({p, q, r, p', q', r'} : Set (ℝ × ℝ)),
      |z.1 - w.1| + |z.2 - w.2| ≤ 4 * R := by
    intro z hz w hw
    obtain ⟨a1, a2⟩ := hb z hz; obtain ⟨b1, b2⟩ := hb w hw
    have := abs_sub z.1 w.1; have := abs_sub z.2 w.2
    linarith
  have hδ : 0 ≤ δ := le_trans (abs_nonneg _) hp.1
  have m1 := triDet_move_first p p' q r
  have m2 := triDet_move_first q q' r p'
  have m3 := triDet_move_first r r' p' q'
  have b1 := bd q (by simp) r (by simp)
  have b2 := bd r (by simp) p' (by simp)
  have b3 := bd p' (by simp) q' (by simp)
  have e2 : triDet p' q r = triDet q r p' := triDet_cycle _ _ _
  have e2' : triDet p' q' r = triDet q' r p' := triDet_cycle _ _ _
  have e3 : triDet p' q' r = triDet r p' q' := by unfold triDet; ring
  have e3' : triDet p' q' r' = triDet r' p' q' := by unfold triDet; ring
  have c1 : |triDet p q r - triDet p' q r| ≤ (2 * δ) * (4 * R) :=
    m1.trans (mul_le_mul (by linarith [hp.1, hp.2]) b1 (by positivity) (by linarith))
  have c2 : |triDet p' q r - triDet p' q' r| ≤ (2 * δ) * (4 * R) := by
    rw [e2, e2']
    exact m2.trans (mul_le_mul (by linarith [hq.1, hq.2]) b2 (by positivity) (by linarith))
  have c3 : |triDet p' q' r - triDet p' q' r'| ≤ (2 * δ) * (4 * R) := by
    rw [e3, e3']
    exact m3.trans (mul_le_mul (by linarith [hr.1, hr.2]) b3 (by positivity) (by linarith))
  calc |triDet p q r - triDet p' q' r'|
      = |(triDet p q r - triDet p' q r) + (triDet p' q r - triDet p' q' r) +
          (triDet p' q' r - triDet p' q' r')| := by ring_nf
    _ ≤ |triDet p q r - triDet p' q r| + |triDet p' q r - triDet p' q' r| +
          |triDet p' q' r - triDet p' q' r'| := abs_add_three _ _ _
    _ ≤ _ := by linarith

/-- **Inscribed triangles** (`abc = 4 R · area`, squared): for three points on the circle of radius
`R` about the origin, the product of the squared side lengths is `4 R² triDet²`. -/
theorem inscribed_sides_sq (x1 y1 x2 y2 x3 y3 R : ℝ) (h1 : x1^2 + y1^2 = R^2)
    (h2 : x2^2 + y2^2 = R^2) (h3 : x3^2 + y3^2 = R^2) :
    ((x1-x2)^2+(y1-y2)^2)*((x2-x3)^2+(y2-y3)^2)*((x3-x1)^2+(y3-y1)^2) =
      4*R^2*((x2-x1)*(y3-y1)-(x3-x1)*(y2-y1))^2 := by
  linear_combination (-3*R^2*x2^2 + 6*R^2*x2*x3 - 3*R^2*x3^2 + R^2*y2^2 - 2*R^2*y2*y3 + R^2*y3^2 + x1^2*x2^2 - 2*x1^2*x2*x3 + x1^2*x3^2 + x1^2*y2^2 - 2*x1^2*y2*y3 + x1^2*y3^2 - 2*x1*x2^3 + 2*x1*x2^2*x3 + 2*x1*x2*x3^2 - 2*x1*x2*y2^2 + 4*x1*x2*y2*y3 - 2*x1*x2*y3^2 - 2*x1*x3^3 - 2*x1*x3*y2^2 + 4*x1*x3*y2*y3 - 2*x1*x3*y3^2 + x2^4 - 2*x2^3*x3 + 2*x2^2*x3^2 + x2^2*y1^2 - 2*x2^2*y1*y2 - 2*x2^2*y1*y3 + 2*x2^2*y2^2 + 2*x2^2*y2*y3 + 2*x2^2*y3^2 - 2*x2*x3^3 - 2*x2*x3*y1^2 + 4*x2*x3*y1*y2 + 4*x2*x3*y1*y3 - 2*x2*x3*y2^2 - 8*x2*x3*y2*y3 - 2*x2*x3*y3^2 + x3^4 + x3^2*y1^2 - 2*x3^2*y1*y2 - 2*x3^2*y1*y3 + 2*x3^2*y2^2 + 2*x3^2*y2*y3 + 2*x3^2*y3^2 + y1^2*y2^2 - 2*y1^2*y2*y3 + y1^2*y3^2 - 2*y1*y2^3 + 2*y1*y2^2*y3 + 2*y1*y2*y3^2 - 2*y1*y3^3 + y2^4 + 2*y2^3*y3 - 6*y2^2*y3^2 + 2*y2*y3^3 + y3^4) * h1 + (2*R^4 - 4*R^2*x1^2 - 2*R^2*x1*x2 + 4*R^2*x1*x3 + R^2*x2^2 - 2*R^2*x2*x3 - R^2*x3^2 - 2*R^2*y1*y2 + R^2*y2^2 + 2*R^2*y2*y3 - 5*R^2*y3^2 + 4*x1^2*x2*x3 - 4*x1^2*y2*y3 + 8*x1^2*y3^2 - 2*x1*x2^2*x3 + 2*x1*x2*x3^2 + 4*x1*x2*y1*y3 - 2*x1*x2*y3^2 - 2*x1*x3^3 + 4*x1*x3*y1*y2 - 8*x1*x3*y1*y3 - 2*x1*x3*y2^2 + 4*x1*x3*y2*y3 - 2*x1*x3*y3^2 + x2^2*x3^2 - 2*x2^2*y1*y3 + x2^2*y3^2 - 2*x2*x3^3 + 4*x2*x3*y1*y3 - 2*x2*x3*y3^2 + x3^4 - 2*x3^2*y1*y2 + 2*x3^2*y1*y3 + x3^2*y2^2 - 2*x3^2*y2*y3 + 2*x3^2*y3^2 - 2*y1*y2^2*y3 + 2*y1*y2*y3^2 + 2*y1*y3^3 + y2^2*y3^2 - 2*y2*y3^3 + y3^4) * h2 + (-2*R^4 + 4*R^2*x1^2 + 2*R^2*x1*x2 - 4*R^2*x1*x3 + 4*R^2*x2^2 - 4*R^2*x2*x3 + 2*R^2*x3^2 + 2*R^2*y1*y2 + 2*R^2*y3^2 - 8*x1^2*x2^2 + 4*x1^2*x2*x3 - 4*x1^2*y2*y3 + 4*x1*x2^2*x3 - 2*x1*x2*x3^2 - 8*x1*x2*y1*y2 + 4*x1*x2*y1*y3 + 4*x1*x2*y2*y3 - 2*x1*x2*y3^2 + 4*x1*x3*y1*y2 - 4*x2^2*y1*y3 + 4*x2*x3*y1*y2 - 2*x3^2*y1*y2 - 2*y1*y2*y3^2) * h3

/-- **Three-point area lower bound** (first large-receiver lemma of §9.3, exact part).  Three
points on a circle of radius `R` with pairwise distances at least `s ≥ 0` span a triangle with
`|triDet| ≥ s³ / (2R)`, i.e. area at least `s³ / (4R)`.  (Points on the hull separated by arc
length `≥ a D` have chord distance `≥ c a D`, giving the area `c₀ D² a³` of §9.3.) -/
theorem triDet_inscribed_ge {p q r : ℝ × ℝ} {R s : ℝ} (hR : 0 < R) (hs : 0 ≤ s)
    (hp : p.1 ^ 2 + p.2 ^ 2 = R ^ 2) (hq : q.1 ^ 2 + q.2 ^ 2 = R ^ 2)
    (hr : r.1 ^ 2 + r.2 ^ 2 = R ^ 2)
    (hpq : s ^ 2 ≤ (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2)
    (hqr : s ^ 2 ≤ (q.1 - r.1) ^ 2 + (q.2 - r.2) ^ 2)
    (hrp : s ^ 2 ≤ (r.1 - p.1) ^ 2 + (r.2 - p.2) ^ 2) :
    s ^ 3 / (2 * R) ≤ |triDet p q r| := by
  have hid := inscribed_sides_sq p.1 p.2 q.1 q.2 r.1 r.2 R hp hq hr
  have h6 : (s ^ 3) ^ 2 ≤ (2 * R * |triDet p q r|) ^ 2 := by
    have e : (2 * R * |triDet p q r|) ^ 2 = 4 * R ^ 2 * triDet p q r ^ 2 := by
      rw [mul_pow, sq_abs]; ring
    rw [e]
    unfold triDet
    rw [← hid]
    have a1 : s ^ 2 * s ^ 2 ≤ ((p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2) * ((q.1 - r.1) ^ 2 + (q.2 - r.2) ^ 2) :=
      mul_le_mul hpq hqr (by positivity) (by positivity)
    have a2 := mul_le_mul a1 hrp (by positivity) (by positivity)
    calc (s ^ 3) ^ 2 = s ^ 2 * s ^ 2 * s ^ 2 := by ring
      _ ≤ _ := a2
  have h3 : s ^ 3 ≤ 2 * R * |triDet p q r| :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).1 h6
  rw [div_le_iff₀ (by positivity)]; linarith

end Propagation

end Erdos99

end

end PropagationLedger

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `LocalCapacity`
-/

section LocalCapacity

/-!
# WP6: local polygon capacities (Verification Guide §8, Lemma 4.1 of the manuscript)

A *unit polygon* with `k` vertices is a map `P : Fin k → Plane` (indices mod `k`) with unit edges
`u i = P (i + 1) - P i` and pairwise unit-separated vertices. An edge is *marked* (for a unit
vector `e` and a threshold `c = cos δ`) if `u i · e ≥ c`, i.e. its direction is within `δ` of `e`.

* `UnitPolygon.projection_bound`: `r (1 + c) ≤ k` for `r` marked edges (§8.1);
* `UnitPolygon.capacity_ge_nine`: for `k ≥ 9` and `c ≥ 9/10`, `r ≤ (k - 4) - (k - 8)/4`;
* the small cases (§8.2): `capacity_five` (`r ≤ 2`), `capacity_six` (`r ≤ 2`), `capacity_seven`
  (`r ≤ 3`), `capacity_eight` (`r ≤ 3`), with the explicit modulus `c ≥ 19/20`; the hexagon and
  octagon cases use separation (`half_marked_false`: a limiting doubled path repeats a vertex);
* the coordinate estimates (§8.2): `pentagon_estimate` (two consecutive marked pentagon edges
  force the other three directions within `O(δ)` of `120°, 180°, 240°`) and `heptagon_estimate`
  (three consecutive marked heptagon edges force two further edges within `O(√δ)` of `-e`);
* consecutiveness from convexity: `marked_orderConvex` (for a convex polygon, given by a monotone
  lift of its edge directions with total turning at most `2π`, the marked edges, or the unmarked
  ones, form an interval of indices), and `consecutive_five`, `consecutive_seven`;
* hull returns (§8.3): `return_chord_bound` (`1 ≤ j - r - d r`) and `return_capacity`.

No convexity is needed for the capacity counts themselves: unit edges and separation suffice.
-/

open scoped BigOperators Real

@[expose] public noncomputable section

open Classical

namespace Erdos99

open Fin.NatCast Fin.CommRing

/-- A closed polygon with `k` vertices (indices mod `k`), unit edges and pairwise unit-separated
vertices. -/
structure UnitPolygon (k : ℕ) [NeZero k] where
  /-- The vertices. -/
  P : Fin k → Plane
  unit_edge : ∀ i, ‖P (i + 1) - P i‖ = 1
  sep : ∀ i j, i ≠ j → 1 ≤ dist (P i) (P j)

namespace UnitPolygon

variable {k : ℕ} [NeZero k] (Q : UnitPolygon k)

/-- The `i`-th edge vector `P (i + 1) - P i`. -/
def edge (i : Fin k) : Plane := Q.P (i + 1) - Q.P i

lemma norm_edge (i : Fin k) : ‖Q.edge i‖ = 1 := Q.unit_edge i

/-- Closure: the edge vectors sum to zero. -/
lemma sum_edge : ∑ i, Q.edge i = 0 := by
  simp only [edge, Finset.sum_sub_distrib]
  rw [sub_eq_zero]
  exact Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun _ => rfl)

lemma inner_edge_ge (i : Fin k) {e : Plane} (he : ‖e‖ = 1) : -1 ≤ inner ℝ (Q.edge i) e := by
  have := abs_real_inner_le_norm (Q.edge i) e
  rw [Q.norm_edge, he, one_mul] at this
  linarith [neg_abs_le (inner ℝ (Q.edge i) e)]

lemma sum_inner_edge (e : Plane) : ∑ i, inner ℝ (Q.edge i) e = 0 := by
  rw [← sum_inner, Q.sum_edge, inner_zero_left]

/-- **The projection bound** (Verification Guide §8.1). If `r` edges have projection at least `c`
on a unit vector `e`, then `r (1 + c) ≤ k`. -/
theorem projection_bound {e : Plane} (he : ‖e‖ = 1) {c : ℝ} {M : Finset (Fin k)}
    (hM : ∀ i ∈ M, c ≤ inner ℝ (Q.edge i) e) : (M.card : ℝ) * (1 + c) ≤ k := by
  have hsum := Q.sum_inner_edge e
  rw [← Finset.sum_add_sum_compl M] at hsum
  have h1 : (M.card : ℝ) * c ≤ ∑ i ∈ M, inner ℝ (Q.edge i) e := by
    have := Finset.card_nsmul_le_sum M (fun i => inner ℝ (Q.edge i) e) c hM
    rwa [nsmul_eq_mul] at this
  have h2 : -(Mᶜ.card : ℝ) ≤ ∑ i ∈ Mᶜ, inner ℝ (Q.edge i) e := by
    have := Finset.card_nsmul_le_sum Mᶜ (fun i => inner ℝ (Q.edge i) e) (-1)
      (fun i _ => Q.inner_edge_ge i he)
    rw [nsmul_eq_mul] at this; linarith
  have h3 : (Mᶜ.card : ℝ) = k - M.card := by
    have : M.card ≤ k := by simpa using Finset.card_le_univ M
    rw [Finset.card_compl, Fintype.card_fin, Nat.cast_sub this]
  linarith

/-- **Capacity for `k ≥ 9`** (Verification Guide §8.1). With `c ≥ 9/10`, at most
`(k - 4) - (k - 8)/4` edges are marked. -/
theorem capacity_ge_nine (hk : 9 ≤ k) {e : Plane} (he : ‖e‖ = 1) {c : ℝ} (hc : 9 / 10 ≤ c)
    {M : Finset (Fin k)} (hM : ∀ i ∈ M, c ≤ inner ℝ (Q.edge i) e) :
    (M.card : ℝ) ≤ (k - 4) - (k - 8) / 4 := by
  have h := Q.projection_bound he hM
  have hk' : (9 : ℝ) ≤ k := by exact_mod_cast hk
  have h2 : (M.card : ℝ) * (19 / 10) ≤ k := by
    have : (M.card : ℝ) * (19 / 10) ≤ M.card * (1 + c) :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
    linarith
  linarith

/-- If `M` is a nonempty proper subset of `Fin k`, some `i ∈ M` has `i + 1 ∉ M`. -/
lemma exists_mem_succ_not_mem {M : Finset (Fin k)} (hne : M.Nonempty) (hnu : M ≠ Finset.univ) :
    ∃ i ∈ M, i + 1 ∉ M := by
  by_contra h
  push_neg at h
  obtain ⟨i0, hi0⟩ := hne
  have hall : ∀ n : ℕ, i0 + (n : Fin k) ∈ M := by
    intro n
    induction n with
    | zero => simpa using hi0
    | succ n ih =>
      have := h _ ih
      rwa [Nat.cast_succ, ← add_assoc]
  apply hnu
  ext j
  simp only [Finset.mem_univ, iff_true]
  have := hall (j - i0).val
  rwa [Fin.cast_val_eq_self, add_sub_cancel] at this

/-- Two consecutive edges almost cancelling repeat a vertex: `|u_i + u_{i+1}| < 1` is impossible
when `k ≥ 3`. -/
lemma two_step_ge_one (hk : 3 ≤ k) (i : Fin k) : 1 ≤ ‖Q.edge i + Q.edge (i + 1)‖ := by
  have hne : i + 1 + 1 ≠ i := by
    intro h
    have h2 : ((2 : ℕ) : Fin k) = 0 := by
      have : i + ((2 : ℕ) : Fin k) = i + 0 := by
        rw [add_zero]; nth_rewrite 2 [← h]; push_cast; ring
      exact add_left_cancel this
    rw [Fin.natCast_eq_zero] at h2
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have := Q.sep _ _ hne
  rw [dist_eq_norm] at this
  convert this using 2
  simp only [edge]; abel

/-- **The doubled-path exclusion** (hexagon and octagon cases of §8.2). If exactly half of the
`k ≥ 3` edges are marked with `c ≥ 19/20`, and there are at most four marked edges, then two
consecutive edges nearly cancel, contradicting separation. -/
theorem half_marked_false (hk : 3 ≤ k) {e : Plane} (he : ‖e‖ = 1) {c : ℝ} (hc : 19 / 20 ≤ c)
    {M : Finset (Fin k)} (hM : ∀ i ∈ M, c ≤ inner ℝ (Q.edge i) e)
    (hhalf : 2 * M.card = k) (h4 : M.card ≤ 4) : False := by
  have hMne : M.Nonempty := by
    rw [← Finset.card_pos]; omega
  have hMu : M ≠ Finset.univ := by
    intro h; rw [h, Finset.card_univ, Fintype.card_fin] at hhalf; omega
  obtain ⟨i, hi, hi1⟩ := exists_mem_succ_not_mem hMne hMu
  set m : ℝ := (M.card : ℝ) with hm
  have hm4 : m ≤ 4 := by simp only [hm]; exact_mod_cast h4
  have hkm : (k : ℝ) = 2 * m := by simp only [hm]; exact_mod_cast hhalf.symm
  -- the unmarked edge `i + 1` points nearly along `-e`
  have hsum := Q.sum_inner_edge e
  rw [← Finset.sum_add_sum_compl M] at hsum
  have h1 : m * c ≤ ∑ j ∈ M, inner ℝ (Q.edge j) e := by
    have := Finset.card_nsmul_le_sum M (fun j => inner ℝ (Q.edge j) e) c hM
    rwa [nsmul_eq_mul] at this
  have hi1' : i + 1 ∈ Mᶜ := Finset.mem_compl.2 hi1
  have h2 : ∑ j ∈ Mᶜ, inner ℝ (Q.edge j) e =
      inner ℝ (Q.edge (i + 1)) e + ∑ j ∈ Mᶜ.erase (i + 1), inner ℝ (Q.edge j) e :=
    (Finset.add_sum_erase _ _ hi1').symm
  have h3 : -((Mᶜ.erase (i + 1)).card : ℝ) ≤ ∑ j ∈ Mᶜ.erase (i + 1), inner ℝ (Q.edge j) e := by
    have := Finset.card_nsmul_le_sum (Mᶜ.erase (i + 1)) (fun j => inner ℝ (Q.edge j) e) (-1)
      (fun j _ => Q.inner_edge_ge j he)
    rw [nsmul_eq_mul] at this; linarith
  have h4' : ((Mᶜ.erase (i + 1)).card : ℝ) = m - 1 := by
    rw [Finset.card_erase_of_mem hi1', Finset.card_compl, Fintype.card_fin]
    have : 1 ≤ k - M.card := by omega
    rw [Nat.cast_sub this, Nat.cast_sub (by omega)]
    push_cast; linarith
  have hx : inner ℝ (Q.edge (i + 1)) e ≤ -1 + m * (1 - c) := by linarith
  -- squared distances to `∓ e`
  have hn1 : ‖Q.edge i - e‖ ^ 2 ≤ 2 * (1 - c) := by
    rw [norm_sub_sq_real, Q.norm_edge, he]; linarith [hM i hi]
  have hn2 : ‖Q.edge (i + 1) + e‖ ^ 2 ≤ 2 * m * (1 - c) := by
    rw [norm_add_sq_real, Q.norm_edge, he]; linarith
  have hsplit : Q.edge i + Q.edge (i + 1) = (Q.edge i - e) + (Q.edge (i + 1) + e) := by abel
  have htri := norm_add_le (Q.edge i - e) (Q.edge (i + 1) + e)
  rw [← hsplit] at htri
  have hge := Q.two_step_ge_one hk i
  set x := ‖Q.edge i - e‖
  set y := ‖Q.edge (i + 1) + e‖
  have hx0 : 0 ≤ x := norm_nonneg _
  have hy0 : 0 ≤ y := norm_nonneg _
  have hx2 : x ^ 2 ≤ 1 / 10 := by nlinarith
  have hy2 : y ^ 2 ≤ 4 / 10 := by nlinarith
  have hxy : x * y ≤ 1 / 5 := by nlinarith [sq_nonneg (x * y), mul_self_nonneg (x * y - 1 / 5)]
  nlinarith

/-- Pentagon capacity: with `c > 2/3`, at most two edges are marked. -/
theorem capacity_five (Q : UnitPolygon 5) {e : Plane} (he : ‖e‖ = 1) {c : ℝ} (hc : 2 / 3 < c)
    {M : Finset (Fin 5)} (hM : ∀ i ∈ M, c ≤ inner ℝ (Q.edge i) e) : M.card ≤ 2 := by
  have h := Q.projection_bound he hM
  by_contra hcon
  have : (3 : ℝ) ≤ M.card := by exact_mod_cast (show 3 ≤ M.card by omega)
  push_cast at h
  nlinarith

/-- Heptagon capacity: with `c > 3/4`, at most three edges are marked. -/
theorem capacity_seven (Q : UnitPolygon 7) {e : Plane} (he : ‖e‖ = 1) {c : ℝ} (hc : 3 / 4 < c)
    {M : Finset (Fin 7)} (hM : ∀ i ∈ M, c ≤ inner ℝ (Q.edge i) e) : M.card ≤ 3 := by
  have h := Q.projection_bound he hM
  by_contra hcon
  have : (4 : ℝ) ≤ M.card := by exact_mod_cast (show 4 ≤ M.card by omega)
  push_cast at h
  nlinarith

/-- Hexagon capacity: with `c ≥ 19/20`, at most two edges are marked (three would force a
limiting doubled path with a repeated vertex). -/
theorem capacity_six (Q : UnitPolygon 6) {e : Plane} (he : ‖e‖ = 1) {c : ℝ} (hc : 19 / 20 ≤ c)
    {M : Finset (Fin 6)} (hM : ∀ i ∈ M, c ≤ inner ℝ (Q.edge i) e) :
    M.card ≤ 2 := by
  by_contra hcon
  by_cases h3 : M.card = 3
  · exact Q.half_marked_false (by norm_num) he hc hM (by omega) (by omega)
  · have h := Q.projection_bound he hM
    have : (4 : ℝ) ≤ M.card := by exact_mod_cast (show 4 ≤ M.card by omega)
    push_cast at h
    nlinarith

/-- Octagon capacity: with `c ≥ 19/20`, at most three edges are marked (four would force a
limiting doubled path with a repeated vertex). -/
theorem capacity_eight (Q : UnitPolygon 8) {e : Plane} (he : ‖e‖ = 1) {c : ℝ} (hc : 19 / 20 ≤ c)
    {M : Finset (Fin 8)} (hM : ∀ i ∈ M, c ≤ inner ℝ (Q.edge i) e) :
    M.card ≤ 3 := by
  by_contra hcon
  by_cases h4 : M.card = 4
  · exact Q.half_marked_false (by norm_num) he hc hM (by omega) (by omega)
  · have h := Q.projection_bound he hM
    have : (5 : ℝ) ≤ M.card := by exact_mod_cast (show 5 ≤ M.card by omega)
    push_cast at h
    nlinarith

end UnitPolygon

/-! ## Coordinate estimates (Verification Guide §8.2) -/

namespace LocalCapacity

lemma sqrt3_half_sq : (√3 / 2) ^ 2 = 3 / 4 := by
  rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num

lemma sqrt3_half_bounds : 4 / 5 < √3 / 2 ∧ √3 / 2 < 1 := by
  have h := sqrt3_half_sq
  have h0 : 0 ≤ √3 / 2 := by positivity
  constructor <;> nlinarith

/-- `| |q| - √3/2 | ≤ 3 δ` when `|q² - 3/4| ≤ 2 δ`. -/
lemma abs_sub_sqrt3_half {q δ : ℝ} (hδ : 0 ≤ δ) (h : |q ^ 2 - 3 / 4| ≤ 2 * δ) (hq : 0 ≤ q) :
    |q - √3 / 2| ≤ 3 * δ := by
  obtain ⟨hs1, -⟩ := sqrt3_half_bounds
  have hs := sqrt3_half_sq
  have e : q ^ 2 - 3 / 4 = (q - √3 / 2) * (q + √3 / 2) := by rw [← hs]; ring
  rw [e, abs_mul, abs_of_pos (by linarith : 0 < q + √3 / 2)] at h
  have : |q - √3 / 2| * (4 / 5) ≤ |q - √3 / 2| * (q + √3 / 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  nlinarith [abs_nonneg (q - √3 / 2)]

lemma small_delta {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1 / 100) :
    δ ^ 2 ≤ δ / 100 ∧ (δ + δ ^ 2) ^ 2 ≤ 2 * δ ^ 2 ∧ (δ + δ ^ 2) ^ 2 ≤ δ / 10 := by
  have a1 : δ ^ 2 ≤ δ / 100 := by nlinarith
  have a2 : (δ + δ ^ 2) ^ 2 ≤ 2 * δ ^ 2 := by nlinarith
  exact ⟨a1, a2, by nlinarith⟩

/-- The real-variable core of the pentagon estimate. Coordinates along `(e, J e)`: `X - C = (p₁, q₁)`,
`Y - A = (p₂, q₂)` (unit), `C - A = (g_x, g_y)`; the separations give `p₁ ≥ -1/2 - δ` and
`p₂ ≤ 1/2 + δ`, and `|Y - X| = 1`. -/
lemma pentagon_real {p1 q1 p2 q2 gx gy δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 100)
    (h1 : p1 ^ 2 + q1 ^ 2 = 1) (h2 : p2 ^ 2 + q2 ^ 2 = 1) (hgx1 : 2 - δ ^ 2 ≤ gx) (hgx2 : gx ≤ 2)
    (hgy : |gy| ≤ 2 * δ) (hp1 : -1 / 2 - δ ≤ p1) (hp2 : p2 ≤ 1 / 2 + δ)
    (hXY : (p2 - gx - p1) ^ 2 + (q2 - gy - q1) ^ 2 = 1) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ (p1 + 1 / 2) ^ 2 + (q1 - σ * (√3 / 2)) ^ 2 ≤ (4 * δ) ^ 2 ∧
      (p2 - gx - p1 + 1) ^ 2 + (q2 - gy - q1) ^ 2 ≤ (10 * δ) ^ 2 ∧
      (p2 - 1 / 2) ^ 2 + (q2 - σ * (√3 / 2)) ^ 2 ≤ (4 * δ) ^ 2 := by
  obtain ⟨hs1, hs2⟩ := sqrt3_half_bounds
  obtain ⟨d1, d2, d3⟩ := small_delta hδ0 hδ
  have hsq0 := sq_nonneg δ
  set h := p2 - gx - p1 with hh
  set v := q2 - gy - q1 with hv
  obtain ⟨hh1, -⟩ := abs_le.1 (abs_le_of_sq_le_sq' (show h ^ 2 ≤ 1 ^ 2 by
    linarith [sq_nonneg v]) zero_le_one |> fun h => abs_le.2 h)
  -- `α + α' ≤ δ²` where `α = p₁ + 1/2`, `α' = 1/2 - p₂`
  have hsum : (p1 + 1 / 2) + (1 / 2 - p2) ≤ δ ^ 2 := by linarith
  have ha1 : |p1 + 1 / 2| ≤ δ + δ ^ 2 := abs_le.2 ⟨by linarith, by linarith⟩
  have ha2 : |p2 - 1 / 2| ≤ δ + δ ^ 2 := abs_le.2 ⟨by linarith, by linarith⟩
  have hhp : |h + 1| ≤ 3 * δ := abs_le.2 ⟨by linarith, by linarith⟩
  have sa1 : (p1 + 1 / 2) ^ 2 ≤ (δ + δ ^ 2) ^ 2 := sq_le_sq' (abs_le.1 ha1).1 (abs_le.1 ha1).2
  have sa2 : (p2 - 1 / 2) ^ 2 ≤ (δ + δ ^ 2) ^ 2 := sq_le_sq' (abs_le.1 ha2).1 (abs_le.1 ha2).2
  -- `q₁², q₂²` are within `2δ` of `3/4`
  have hq1 : |q1 ^ 2 - 3 / 4| ≤ 2 * δ := by
    have e : q1 ^ 2 - 3 / 4 = (p1 + 1 / 2) - (p1 + 1 / 2) ^ 2 := by linear_combination h1
    rw [e]
    have := abs_le.1 ha1
    exact abs_le.2 ⟨by linarith, by linarith [sq_nonneg (p1 + 1 / 2)]⟩
  have hq2 : |q2 ^ 2 - 3 / 4| ≤ 2 * δ := by
    have e : q2 ^ 2 - 3 / 4 = -(p2 - 1 / 2) - (p2 - 1 / 2) ^ 2 := by linear_combination h2
    rw [e]
    have := abs_le.1 ha2
    exact abs_le.2 ⟨by linarith, by linarith [sq_nonneg (p2 - 1 / 2)]⟩
  -- `v² ≤ 6δ`
  have hv2 : v ^ 2 ≤ 6 * δ := by
    have e : (1 - h) * (1 + h) = 1 - h ^ 2 := by ring
    have := abs_le.1 hhp
    have m : (1 - h) * (1 + h) ≤ 2 * (3 * δ) :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
    linarith
  have hvb := abs_le.1 (abs_le_of_sq_le_sq' (show v ^ 2 ≤ (1 / 4) ^ 2 by linarith)
    (by norm_num) |> fun h => abs_le.2 h)
  have hgy' := abs_le.1 hgy
  have hqv : q2 - q1 = v + gy := by rw [hv]; ring
  -- the final estimate, for a common sign `σ`
  have key : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → |σ * q1 - √3 / 2| ≤ 3 * δ →
      |σ * q2 - √3 / 2| ≤ 3 * δ →
      (p1 + 1 / 2) ^ 2 + (q1 - σ * (√3 / 2)) ^ 2 ≤ (4 * δ) ^ 2 ∧
      (h + 1) ^ 2 + v ^ 2 ≤ (10 * δ) ^ 2 ∧
      (p2 - 1 / 2) ^ 2 + (q2 - σ * (√3 / 2)) ^ 2 ≤ (4 * δ) ^ 2 := by
    intro σ hσ e1 e2
    have f1 : (q1 - σ * (√3 / 2)) ^ 2 = (σ * q1 - √3 / 2) ^ 2 := by
      rcases hσ with rfl | rfl <;> ring
    have f2 : (q2 - σ * (√3 / 2)) ^ 2 = (σ * q2 - √3 / 2) ^ 2 := by
      rcases hσ with rfl | rfl <;> ring
    have g1 : (σ * q1 - √3 / 2) ^ 2 ≤ (3 * δ) ^ 2 := sq_le_sq' (abs_le.1 e1).1 (abs_le.1 e1).2
    have g2 : (σ * q2 - √3 / 2) ^ 2 ≤ (3 * δ) ^ 2 := sq_le_sq' (abs_le.1 e2).1 (abs_le.1 e2).2
    have g5 : (h + 1) ^ 2 ≤ (3 * δ) ^ 2 := sq_le_sq' (abs_le.1 hhp).1 (abs_le.1 hhp).2
    have hσv : σ * v = (σ * q2 - √3 / 2) - (σ * q1 - √3 / 2) - σ * gy := by
      have : σ * v = σ * (q2 - q1) - σ * gy := by rw [hqv]; ring
      rw [this]; ring
    have hσgy : |σ * gy| ≤ 2 * δ := by
      rw [abs_mul]; rcases hσ with rfl | rfl <;> simpa using hgy
    have hσv' : |σ * v| ≤ 8 * δ := by
      rw [hσv]
      have a1 := abs_sub (σ * q2 - √3 / 2 - (σ * q1 - √3 / 2)) (σ * gy)
      have a2 := abs_sub (σ * q2 - √3 / 2) (σ * q1 - √3 / 2)
      linarith
    have g6 : v ^ 2 ≤ (8 * δ) ^ 2 := by
      have e3 : (σ * v) ^ 2 = v ^ 2 := by rcases hσ with rfl | rfl <;> ring
      rw [← e3]
      exact sq_le_sq' (abs_le.1 hσv').1 (abs_le.1 hσv').2
    refine ⟨by rw [f1]; linarith, by linarith, by rw [f2]; linarith⟩
  rcases le_total 0 q1 with hq1s | hq1s
  · have e1 := abs_le.1 (abs_sub_sqrt3_half hδ0 hq1 hq1s)
    have hq2s : 0 ≤ q2 := by
      by_contra hneg
      push_neg at hneg
      have e2 := abs_le.1 (abs_sub_sqrt3_half hδ0 (by rwa [neg_sq]) (by linarith : 0 ≤ -q2))
      linarith
    refine ⟨1, Or.inl rfl, ?_⟩
    exact key 1 (Or.inl rfl) (by simpa using abs_sub_sqrt3_half hδ0 hq1 hq1s)
      (by simpa using abs_sub_sqrt3_half hδ0 hq2 hq2s)
  · have e1 := abs_le.1 (abs_sub_sqrt3_half hδ0 (by rwa [neg_sq]) (by linarith : 0 ≤ -q1))
    have hq2s : q2 ≤ 0 := by
      by_contra hpos
      push_neg at hpos
      have e2 := abs_le.1 (abs_sub_sqrt3_half hδ0 hq2 hpos.le)
      linarith
    refine ⟨-1, Or.inr rfl, ?_⟩
    exact key (-1) (Or.inr rfl)
      (by simpa [neg_mul, one_mul, sub_eq_add_neg, add_comm] using
        abs_sub_sqrt3_half hδ0 (by rwa [neg_sq]) (by linarith : 0 ≤ -q1))
      (by simpa [neg_mul, one_mul, sub_eq_add_neg, add_comm] using
        abs_sub_sqrt3_half hδ0 (by rwa [neg_sq]) (by linarith : 0 ≤ -q2))

lemma frame_norm_sq {e : Plane} (he : ‖e‖ = 1) (w : Plane) :
    ‖w‖ ^ 2 = inner ℝ w (rot e) ^ 2 + inner ℝ w e ^ 2 := by
  have := inner_sq_add_inner_rot_sq e w
  rw [he] at this; linarith

lemma inner_self_rot (e : Plane) : inner ℝ e (rot e) = 0 := by
  rw [inner_rot_coord]; ring

lemma inner_rot_self (e : Plane) : inner ℝ (rot e) e = 0 := by
  rw [real_inner_comm]; exact inner_self_rot e

/-- A vector is small if both of its coordinates in the frame `(e, J e)` are. -/
lemma norm_le_of_frame {e w : Plane} (he : ‖e‖ = 1) {r : ℝ} (hr : 0 ≤ r)
    (h : inner ℝ w e ^ 2 + inner ℝ w (rot e) ^ 2 ≤ r ^ 2) : ‖w‖ ≤ r := by
  have e1 := frame_norm_sq he w
  exact (pow_le_pow_iff_left₀ (norm_nonneg w) hr two_ne_zero).1 (by linarith)

/-- Frame coordinates of `v - (a e + b J e)`. -/
lemma frame_sub_coords {e : Plane} (he : ‖e‖ = 1) (v : Plane) (a b : ℝ) :
    inner ℝ (v - (a • e + b • rot e)) e = inner ℝ v e - a ∧
      inner ℝ (v - (a • e + b • rot e)) (rot e) = inner ℝ v (rot e) - b := by
  have h1 : inner ℝ e e = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  have h2 : inner ℝ (rot e) (rot e) = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_rot, he]; norm_num
  constructor
  · rw [inner_sub_left, inner_add_left, real_inner_smul_left, real_inner_smul_left, h1,
      inner_rot_self]; ring
  · rw [inner_sub_left, inner_add_left, real_inner_smul_left, real_inner_smul_left, h2,
      inner_self_rot]; ring

/-- For a unit vector `u` with `|u - e| ≤ δ`: `u · e ≥ 1 - δ²/2`. -/
lemma inner_ge_of_close {u e : Plane} (hu : ‖u‖ = 1) (he : ‖e‖ = 1) {δ : ℝ}
    (h : ‖u - e‖ ≤ δ) : 1 - δ ^ 2 / 2 ≤ inner ℝ u e := by
  have e1 := norm_sub_sq_real u e
  rw [hu, he] at e1
  have := pow_le_pow_left₀ (norm_nonneg _) h 2
  linarith

/-- Replacing `u` by a nearby `e` changes `w · u` by at most `|w| δ`. -/
lemma inner_close {u e w : Plane} {δ : ℝ} (h : ‖u - e‖ ≤ δ) :
    |inner ℝ w u - inner ℝ w e| ≤ ‖w‖ * δ := by
  rw [← inner_sub_right]
  exact (abs_real_inner_le_norm w (u - e)).trans (mul_le_mul_of_nonneg_left h (norm_nonneg w))

/-- If `|x - z| = 1` and `|x - z + u| ≥ 1` with `u` a unit vector, then `(x - z) · u ≥ -1/2`
(separation from the vertex before `z`). -/
lemma inner_ge_of_sep {a u : Plane} (ha : ‖a‖ = 1) (hu : ‖u‖ = 1) (h : 1 ≤ ‖a + u‖) :
    -1 / 2 ≤ inner ℝ a u := by
  have e1 := norm_add_sq_real a u
  rw [ha, hu] at e1
  have := pow_le_pow_left₀ zero_le_one h 2
  linarith

/-- **The pentagon estimate** (Verification Guide §8.2). Let `A, B, C, X, Y` be the consecutive
vertices of a unit pentagon whose two consecutive edges `B - A`, `C - B` are within `δ ≤ 1/100` of
the unit vector `e`, and whose vertices `X, Y` are at distance at least `1` from `B`. Then, for a
sign `σ = ±1`, the remaining directed edges are within `O(δ)` of the directions `120°`, `180°`,
`240°` relative to `e` (in the order given by `σ`):
`|(X - C) - (-1/2 e + σ (√3/2) J e)| ≤ 4δ`, `|(Y - X) + e| ≤ 10δ`,
`|(A - Y) - (-1/2 e - σ (√3/2) J e)| ≤ 4δ`. -/
theorem pentagon_estimate {A B C X Y e : Plane} {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 100)
    (he : ‖e‖ = 1) (hAB : ‖B - A‖ = 1) (hBC : ‖C - B‖ = 1) (hu0 : ‖(B - A) - e‖ ≤ δ)
    (hu1 : ‖(C - B) - e‖ ≤ δ) (hCX : ‖X - C‖ = 1) (hXY : ‖Y - X‖ = 1) (hYA : ‖A - Y‖ = 1)
    (hXB : 1 ≤ ‖X - B‖) (hYB : 1 ≤ ‖Y - B‖) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      ‖(X - C) - ((-1 / 2 : ℝ) • e + (σ * (√3 / 2)) • rot e)‖ ≤ 4 * δ ∧
      ‖(Y - X) + e‖ ≤ 10 * δ ∧
      ‖(A - Y) - ((-1 / 2 : ℝ) • e + (-(σ * (√3 / 2))) • rot e)‖ ≤ 4 * δ := by
  have hYA' : ‖Y - A‖ = 1 := by rw [norm_sub_rev]; exact hYA
  -- coordinates of the two marked edges
  have hx0 := inner_ge_of_close hAB he hu0
  have hx1 := inner_ge_of_close hBC he hu1
  have hx0' : inner ℝ (B - A) e ≤ 1 := by
    have := real_inner_le_norm (B - A) e; rw [hAB, he] at this; linarith
  have hx1' : inner ℝ (C - B) e ≤ 1 := by
    have := real_inner_le_norm (C - B) e; rw [hBC, he] at this; linarith
  have hy0 : |inner ℝ (B - A) (rot e)| ≤ δ := by
    have := inner_close (w := rot e) hu0
    rw [real_inner_comm, real_inner_comm e, inner_self_rot, sub_zero, norm_rot, he,
      one_mul] at this
    exact this
  have hy1 : |inner ℝ (C - B) (rot e)| ≤ δ := by
    have := inner_close (w := rot e) hu1
    rw [real_inner_comm, real_inner_comm e, inner_self_rot, sub_zero, norm_rot, he,
      one_mul] at this
    exact this
  -- separation from `B`
  have hp1 : -1 / 2 - δ ≤ inner ℝ (X - C) e := by
    have h1 := inner_ge_of_sep hCX hBC (by
      rw [show X - C + (C - B) = X - B by abel]; exact hXB)
    have h2 := abs_le.1 (inner_close (w := X - C) hu1)
    rw [hCX, one_mul] at h2
    linarith
  have hp2 : inner ℝ (Y - A) e ≤ 1 / 2 + δ := by
    have hAB' : ‖A - B‖ = 1 := by rw [norm_sub_rev]; exact hAB
    have hu0' : ‖(A - B) - (-e)‖ ≤ δ := by
      rw [show A - B - -e = -((B - A) - e) by abel, norm_neg]; exact hu0
    have h1 := inner_ge_of_sep hYA' hAB' (by
      rw [show Y - A + (A - B) = Y - B by abel]; exact hYB)
    have h2 := abs_le.1 (inner_close (w := Y - A) hu0')
    rw [hYA', one_mul, inner_neg_right] at h2
    linarith
  -- apply the real lemma
  have hn := fun v : Plane => frame_norm_sq he v
  have hXYc : (inner ℝ (Y - A) e - inner ℝ (C - A) e - inner ℝ (X - C) e) ^ 2 +
      (inner ℝ (Y - A) (rot e) - inner ℝ (C - A) (rot e) - inner ℝ (X - C) (rot e)) ^ 2 = 1 := by
    have h := hn (Y - X)
    rw [hXY, show Y - X = (Y - A) - (C - A) - (X - C) by abel] at h
    have s3 : ∀ a b c v : Plane, inner ℝ (a - b - c) v = inner ℝ a v - inner ℝ b v - inner ℝ c v :=
      fun a b c v => by rw [inner_sub_left, inner_sub_left]
    rw [s3 (Y - A) (C - A) (X - C) e, s3 (Y - A) (C - A) (X - C) (rot e)] at h
    linarith
  have hgx : inner ℝ (C - A) e = inner ℝ (B - A) e + inner ℝ (C - B) e := by
    rw [← inner_add_left]; congr 1; abel
  have hgy : inner ℝ (C - A) (rot e) = inner ℝ (B - A) (rot e) + inner ℝ (C - B) (rot e) := by
    rw [← inner_add_left]; congr 1; abel
  have h1c : inner ℝ (X - C) e ^ 2 + inner ℝ (X - C) (rot e) ^ 2 = 1 := by
    have := hn (X - C); rw [hCX] at this; linarith
  have h2c : inner ℝ (Y - A) e ^ 2 + inner ℝ (Y - A) (rot e) ^ 2 = 1 := by
    have := hn (Y - A); rw [hYA'] at this; linarith
  obtain ⟨σ, hσ, r1, r2, r3⟩ := pentagon_real hδ0 hδ h1c h2c (by rw [hgx]; linarith)
    (by rw [hgx]; linarith)
    (by rw [hgy]; exact (abs_add_le _ _).trans (by linarith)) hp1 hp2 hXYc
  refine ⟨σ, hσ, ?_, ?_, ?_⟩
  · apply norm_le_of_frame he (by positivity)
    obtain ⟨c1, c2⟩ := frame_sub_coords he (X - C) (-1 / 2) (σ * (√3 / 2))
    rw [c1, c2]; linarith
  · apply norm_le_of_frame he (by positivity)
    have c1 : inner ℝ (Y - X + e) e = inner ℝ (Y - A) e - inner ℝ (C - A) e -
        inner ℝ (X - C) e + 1 := by
      rw [show Y - X + e = (Y - A) - (C - A) - (X - C) + e by abel]
      simp only [inner_add_left, inner_sub_left, real_inner_self_eq_norm_sq, he]; ring
    have c2 : inner ℝ (Y - X + e) (rot e) = inner ℝ (Y - A) (rot e) - inner ℝ (C - A) (rot e) -
        inner ℝ (X - C) (rot e) := by
      rw [show Y - X + e = (Y - A) - (C - A) - (X - C) + e by abel]
      simp only [inner_add_left, inner_sub_left, inner_self_rot]; ring
    rw [c1, c2]; linarith
  · apply norm_le_of_frame he (by positivity)
    obtain ⟨c1, c2⟩ := frame_sub_coords he (A - Y) (-1 / 2) (-(σ * (√3 / 2)))
    have d1 : inner ℝ (A - Y) e = -inner ℝ (Y - A) e := by
      rw [← inner_neg_left, neg_sub]
    have d2 : inner ℝ (A - Y) (rot e) = -inner ℝ (Y - A) (rot e) := by
      rw [← inner_neg_left, neg_sub]
    rw [c1, c2, d1, d2]
    have : (-inner ℝ (Y - A) e - -1 / 2) ^ 2 + (-inner ℝ (Y - A) (rot e) - -(σ * (√3 / 2))) ^ 2 =
        (inner ℝ (Y - A) e - 1 / 2) ^ 2 + (inner ℝ (Y - A) (rot e) - σ * (√3 / 2)) ^ 2 := by ring
    rw [this]; linarith

/-- **The heptagon estimate** (Verification Guide §8.2). Let `P₀, P₁, P₂, P₃` be consecutive
vertices of a unit heptagon whose three edges `P_{i+1} - P_i` are within `δ ≤ 1` of the unit
vector `e`, and let `X₁, X₂, X₃` be the remaining vertices, with `|X₁ - P₂| ≥ 1` and
`|X₃ - P₁| ≥ 1`. Then the two intervening edges are within `O(√δ)` of `-e`:
`|(X₂ - X₁) + e|² ≤ 7δ` and `|(X₃ - X₂) + e|² ≤ 7δ`. -/
theorem heptagon_estimate {P0 P1 P2 P3 X1 X2 X3 e : Plane} {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1)
    (he : ‖e‖ = 1) (h01 : ‖P1 - P0‖ = 1) (h12 : ‖P2 - P1‖ = 1) (h23 : ‖P3 - P2‖ = 1)
    (hu0 : ‖(P1 - P0) - e‖ ≤ δ) (hu1 : ‖(P2 - P1) - e‖ ≤ δ) (hu2 : ‖(P3 - P2) - e‖ ≤ δ)
    (hX1 : ‖X1 - P3‖ = 1) (hX12 : ‖X2 - X1‖ = 1) (hX23 : ‖X3 - X2‖ = 1) (hX30 : ‖P0 - X3‖ = 1)
    (hs1 : 1 ≤ ‖X1 - P2‖) (hs3 : 1 ≤ ‖X3 - P1‖) :
    ‖(X2 - X1) + e‖ ^ 2 ≤ 7 * δ ∧ ‖(X3 - X2) + e‖ ^ 2 ≤ 7 * δ := by
  have hX30' : ‖X3 - P0‖ = 1 := by rw [norm_sub_rev]; exact hX30
  have hδ2 : δ ^ 2 ≤ δ := by nlinarith
  have e0 := inner_ge_of_close h01 he hu0
  have e1 := inner_ge_of_close h12 he hu1
  have e2 := inner_ge_of_close h23 he hu2
  -- separation of `X₁` from `P₂`
  have hp1 : -1 / 2 - δ ≤ inner ℝ (X1 - P3) e := by
    have h1 := inner_ge_of_sep hX1 h23 (by
      rw [show X1 - P3 + (P3 - P2) = X1 - P2 by abel]; exact hs1)
    have h2 := abs_le.1 (inner_close (w := X1 - P3) hu2)
    rw [hX1, one_mul] at h2
    linarith
  -- separation of `X₃` from `P₁`
  have hp3 : inner ℝ (X3 - P0) e ≤ 1 / 2 + δ := by
    have h10 : ‖P0 - P1‖ = 1 := by rw [norm_sub_rev]; exact h01
    have hu0' : ‖(P0 - P1) - (-e)‖ ≤ δ := by
      rw [show P0 - P1 - -e = -((P1 - P0) - e) by abel, norm_neg]; exact hu0
    have h1 := inner_ge_of_sep hX30' h10 (by
      rw [show X3 - P0 + (P0 - P1) = X3 - P1 by abel]; exact hs3)
    have h2 := abs_le.1 (inner_close (w := X3 - P0) hu0')
    rw [hX30', one_mul, inner_neg_right] at h2
    linarith
  have hsum : inner ℝ (X2 - X1) e + inner ℝ (X3 - X2) e =
      inner ℝ (X3 - P0) e - inner ℝ (P1 - P0) e - inner ℝ (P2 - P1) e - inner ℝ (P3 - P2) e -
        inner ℝ (X1 - P3) e := by
    rw [← inner_add_left, ← inner_sub_left, ← inner_sub_left, ← inner_sub_left, ← inner_sub_left]
    congr 1; abel
  have l1 : -1 ≤ inner ℝ (X2 - X1) e := by
    have := abs_real_inner_le_norm (X2 - X1) e; rw [hX12, he] at this
    linarith [neg_abs_le (inner ℝ (X2 - X1) e)]
  have l2 : -1 ≤ inner ℝ (X3 - X2) e := by
    have := abs_real_inner_le_norm (X3 - X2) e; rw [hX23, he] at this
    linarith [neg_abs_le (inner ℝ (X3 - X2) e)]
  have n1 := norm_add_sq_real (X2 - X1) e
  have n2 := norm_add_sq_real (X3 - X2) e
  rw [hX12, he] at n1
  rw [hX23, he] at n2
  constructor <;> linarith

/-! ## Consecutiveness of marked edges from convexity -/

/-- `θ` is within `δ` of the direction `φ`, modulo `2π`. -/
def NearAngle (θ φ δ : ℝ) : Prop := ∃ n : ℤ, |θ - φ - 2 * π * n| ≤ δ

/-- A set of indices is an interval in the order of `Fin k`. -/
def OrdConvex {k : ℕ} (S : Finset (Fin k)) : Prop :=
  ∀ i j l : Fin k, i < j → j < l → i ∈ S → l ∈ S → j ∈ S

instance {k : ℕ} (S : Finset (Fin k)) : Decidable (OrdConvex S) := by
  unfold OrdConvex; infer_instance

/-- The key step: in a convex polygon (monotone direction lift `θ` with total turning at most
`2π`), if the marked edges `i < l` enclose an unmarked edge `j`, then every edge outside `(i, l)`
is marked. -/
lemma near_outside {k : ℕ} {θ : Fin k → ℝ} (hmono : Monotone θ)
    (hwrap : ∀ a b, θ b ≤ θ a + 2 * π) {φ δ : ℝ} (hδ : δ < π) {i j l : Fin k}
    (hij : i < j) (hjl : j < l) (hi : NearAngle (θ i) φ δ) (hl : NearAngle (θ l) φ δ)
    (hj : ¬ NearAngle (θ j) φ δ) (m : Fin k) (hm : m ≤ i ∨ l ≤ m) : NearAngle (θ m) φ δ := by
  obtain ⟨n, hn⟩ := hi
  obtain ⟨n', hn'⟩ := hl
  have hpi := Real.pi_pos
  have hθij := hmono hij.le
  have hθjl := hmono hjl.le
  have hn1 := abs_le.1 hn
  have hn2 := abs_le.1 hn'
  have hw := hwrap i l
  -- `n ≤ n' ≤ n + 1`
  have hge : n ≤ n' := by
    have : (n : ℝ) - 1 < n' := by
      by_contra hc; push_neg at hc
      have : 2 * π * (n' : ℝ) ≤ 2 * π * ((n : ℝ) - 1) := mul_le_mul_of_nonneg_left hc (by positivity)
      nlinarith
    have : n - 1 < n' := by exact_mod_cast this
    omega
  have hle : n' ≤ n + 1 := by
    have : (n' : ℝ) < n + 2 := by
      by_contra hc; push_neg at hc
      have : 2 * π * ((n : ℝ) + 2) ≤ 2 * π * (n' : ℝ) := mul_le_mul_of_nonneg_left hc (by positivity)
      have hw' := hwrap i l
      nlinarith
    have : n' < n + 2 := by exact_mod_cast this
    omega
  have hn'' : n' = n + 1 := by
    rcases (show n' = n ∨ n' = n + 1 by omega) with h | h
    · exfalso; apply hj; refine ⟨n, abs_le.2 ⟨?_, ?_⟩⟩
      · linarith
      · rw [h] at hn2; linarith
    · exact h
  subst hn''
  push_cast at hn2
  rcases hm with hm | hm
  · refine ⟨n, abs_le.2 ⟨?_, ?_⟩⟩
    · have := hwrap m l; linarith
    · have := hmono hm; linarith
  · refine ⟨n + 1, abs_le.2 ⟨?_, ?_⟩⟩
    · have := hmono hm; push_cast; linarith
    · have := hwrap i m; push_cast; linarith

/-- **Marked edges of a convex polygon are consecutive.** Let the edge directions of a convex
polygon be given by a monotone lift `θ` with total turning at most `2π`, and mark the edges whose
direction is within `δ < π` of `φ`. Then the marked indices, or the unmarked ones, form an interval
of `Fin k`; in either case the marked edges are cyclically consecutive. -/
theorem marked_orderConvex {k : ℕ} {θ : Fin k → ℝ} (hmono : Monotone θ)
    (hwrap : ∀ a b, θ b ≤ θ a + 2 * π) {φ δ : ℝ} (hδ : δ < π) :
    OrdConvex (Finset.univ.filter fun i => NearAngle (θ i) φ δ) ∨
      OrdConvex (Finset.univ.filter fun i => NearAngle (θ i) φ δ)ᶜ := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  simp only [OrdConvex, not_forall] at h1 h2
  obtain ⟨i, j, l, hij, hjl, hi, hl, hj⟩ := h1
  obtain ⟨a, b, c, hab, hbc, ha, hc, hb⟩ := h2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl, not_not] at *
  -- `a` and `c` lie strictly between `i` and `l`
  have hai : i < a := by
    by_contra h; push_neg at h
    exact ha (near_outside hmono hwrap hδ hij hjl hi hl hj a (Or.inl h))
  have hcl : c < l := by
    by_contra h; push_neg at h
    exact hc (near_outside hmono hwrap hδ hij hjl hi hl hj c (Or.inr h))
  -- now `i < a < b` with `a` unmarked forces `c > b` to be marked
  exact hc (near_outside hmono hwrap hδ hai hab hi hb ha c (Or.inr hbc.le))

set_option maxRecDepth 100000 in
/-- In a pentagon, two marked edges forming (or complementing) an interval are adjacent. -/
theorem consecutive_five : ∀ M : Finset (Fin 5), M.card = 2 → (OrdConvex M ∨ OrdConvex Mᶜ) →
    ∃ s : Fin 5, M = {s, s + 1} := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- In a heptagon, three marked edges forming (or complementing) an interval are consecutive. -/
theorem consecutive_seven : ∀ M : Finset (Fin 7), M.card = 3 → (OrdConvex M ∨ OrdConvex Mᶜ) →
    ∃ s : Fin 7, M = {s, s + 1, s + 2} := by
  decide +kernel

/-- **Pentagon:** in a convex pentagon (monotone direction lift with total turning at most `2π`),
two marked edges (directions within `δ < π` of `φ`) are consecutive. -/
theorem pentagon_marked_consecutive {θ : Fin 5 → ℝ} (hmono : Monotone θ)
    (hwrap : ∀ a b, θ b ≤ θ a + 2 * π) {φ δ : ℝ} (hδ : δ < π)
    (hcard : (Finset.univ.filter fun i => NearAngle (θ i) φ δ).card = 2) :
    ∃ s : Fin 5, (Finset.univ.filter fun i => NearAngle (θ i) φ δ) = {s, s + 1} :=
  consecutive_five _ hcard (marked_orderConvex hmono hwrap hδ)

/-- **Heptagon:** in a convex heptagon, three marked edges are consecutive. -/
theorem heptagon_marked_consecutive {θ : Fin 7 → ℝ} (hmono : Monotone θ)
    (hwrap : ∀ a b, θ b ≤ θ a + 2 * π) {φ δ : ℝ} (hδ : δ < π)
    (hcard : (Finset.univ.filter fun i => NearAngle (θ i) φ δ).card = 3) :
    ∃ s : Fin 7, (Finset.univ.filter fun i => NearAngle (θ i) φ δ) = {s, s + 1, s + 2} :=
  consecutive_seven _ hcard (marked_orderConvex hmono hwrap hδ)

/-- A direction within `δ ≤ π` of `φ` (mod `2π`) has `cos (θ - φ) ≥ cos δ`, i.e. the unit vector
of angle `θ` has projection at least `cos δ` on the unit vector of angle `φ`. -/
theorem cos_ge_of_nearAngle {θ φ δ : ℝ} (hδ : δ ≤ π) (h : NearAngle θ φ δ) :
    Real.cos δ ≤ Real.cos (θ - φ) := by
  obtain ⟨n, hn⟩ := h
  have e : Real.cos (θ - φ) = Real.cos (|θ - φ - 2 * π * n|) := by
    rw [Real.cos_abs, show θ - φ - 2 * π * n = θ - φ - (n : ℤ) * (2 * π) by ring,
      Real.cos_sub_int_mul_two_pi]
  rw [e]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hδ hn

/-! ## Hull returns (Verification Guide §8.3) -/

/-- **The chord bound for a hull return.** Let `P 0, …, P j` be a path of `j` unit steps whose
chord has projection at least `1` on a unit vector `c`, and let `N` be a set of steps with
projection at most `-d` on `c`. Then `1 ≤ j - r - d r` with `r = |N|`. -/
theorem return_chord_bound {j : ℕ} {P : ℕ → Plane} (hunit : ∀ i < j, ‖P (i + 1) - P i‖ = 1)
    {c : Plane} (hc : ‖c‖ = 1) (hchord : 1 ≤ inner ℝ (P j - P 0) c) {d : ℝ} {N : Finset ℕ}
    (hNj : N ⊆ Finset.range j) (hN : ∀ i ∈ N, inner ℝ (P (i + 1) - P i) c ≤ -d) :
    (1 : ℝ) ≤ j - N.card - d * N.card := by
  have htel : inner ℝ (P j - P 0) c = ∑ i ∈ Finset.range j, inner ℝ (P (i + 1) - P i) c := by
    rw [← sum_inner, Finset.sum_range_sub]
  rw [htel, ← Finset.sum_sdiff hNj] at hchord
  have h1 : ∑ i ∈ N, inner ℝ (P (i + 1) - P i) c ≤ N.card * (-d) := by
    have := Finset.sum_le_card_nsmul N _ (-d) hN
    rwa [nsmul_eq_mul] at this
  have h2 : ∑ i ∈ Finset.range j \ N, inner ℝ (P (i + 1) - P i) c ≤ ((Finset.range j \ N).card : ℝ) := by
    have := Finset.sum_le_card_nsmul (Finset.range j \ N) (fun i => inner ℝ (P (i + 1) - P i) c) 1
      (fun i hi => by
        have hi' := Finset.mem_range.1 (Finset.mem_sdiff.1 hi).1
        have := real_inner_le_norm (P (i + 1) - P i) c
        rw [hunit i hi', hc, one_mul] at this; exact this)
    rwa [nsmul_eq_mul, mul_one] at this
  have h3 : ((Finset.range j \ N).card : ℝ) = j - N.card := by
    rw [Finset.card_sdiff_of_subset hNj, Finset.card_range,
      Nat.cast_sub (by simpa using Finset.card_le_card hNj)]
  linarith

/-- **Short hull returns** (`j ≤ 2`): no step has projection `≤ -d` with `d > 0`. -/
theorem return_capacity_le_two {j : ℕ} (hj : j ≤ 2) {P : ℕ → Plane}
    (hunit : ∀ i < j, ‖P (i + 1) - P i‖ = 1) {c : Plane} (hc : ‖c‖ = 1)
    (hchord : 1 ≤ inner ℝ (P j - P 0) c) {d : ℝ} (hd : 0 < d) {N : Finset ℕ}
    (hNj : N ⊆ Finset.range j) (hN : ∀ i ∈ N, inner ℝ (P (i + 1) - P i) c ≤ -d) : N = ∅ := by
  have h := return_chord_bound hunit hc hchord hNj hN
  rw [← Finset.card_eq_zero]
  by_contra hne
  have h1 : (1 : ℝ) ≤ N.card := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hne
  have h2 : (j : ℝ) ≤ 2 := by exact_mod_cast hj
  nlinarith

/-- Two unit steps close to `c` and `-c` (squared distances at most `1/5`) nearly cancel. -/
lemma pair_cancel {a b c : Plane} (ha : ‖a - c‖ ^ 2 ≤ 1 / 5) (hb : ‖b + c‖ ^ 2 ≤ 1 / 5) :
    ‖a + b‖ < 1 := by
  have t := norm_add_le (a - c) (b + c)
  rw [show a - c + (b + c) = a + b by abel] at t
  set x := ‖a - c‖
  set y := ‖b + c‖
  have hx : 0 ≤ x := norm_nonneg _
  have hy : 0 ≤ y := norm_nonneg _
  have h2 : (x + y) ^ 2 ≤ 4 / 5 := by nlinarith [sq_nonneg (x - y)]
  have h3 : x + y < 1 := by nlinarith
  linarith

/-- **Three-step hull returns** (Verification Guide §8.3): with `9/10 ≤ d` and unit-separated
vertices, no step has projection `≤ -d` (the limiting configuration `e, e, -e` would repeat a
vertex). -/
theorem return_capacity_three {P : ℕ → Plane} (hunit : ∀ i < 3, ‖P (i + 1) - P i‖ = 1)
    (hsep : ∀ a b, a ≤ 3 → b ≤ 3 → a ≠ b → 1 ≤ ‖P a - P b‖) {c : Plane} (hc : ‖c‖ = 1)
    (hchord : 1 ≤ inner ℝ (P 3 - P 0) c) {d : ℝ} (hd : 9 / 10 ≤ d) {N : Finset ℕ}
    (hNj : N ⊆ Finset.range 3) (hN : ∀ i ∈ N, inner ℝ (P (i + 1) - P i) c ≤ -d) : N = ∅ := by
  have h := return_chord_bound hunit hc hchord hNj hN
  by_contra hne
  have hcard : N.card = 1 := by
    have h1 : 1 ≤ N.card := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hne)
    by_contra h2
    have : (2 : ℝ) ≤ N.card := by exact_mod_cast (show 2 ≤ N.card by omega)
    push_cast at h; nlinarith
  obtain ⟨m, rfl⟩ := Finset.card_eq_one.1 hcard
  have hm : m < 3 := Finset.mem_range.1 (hNj (Finset.mem_singleton_self m))
  have hneg := hN m (Finset.mem_singleton_self m)
  have hle1 : ∀ i < 3, inner ℝ (P (i + 1) - P i) c ≤ 1 := fun i hi => by
    have := real_inner_le_norm (P (i + 1) - P i) c; rw [hunit i hi, hc, one_mul] at this
    exact this
  have hsum : inner ℝ (P 3 - P 0) c = inner ℝ (P (0 + 1) - P 0) c +
      inner ℝ (P (1 + 1) - P 1) c + inner ℝ (P (2 + 1) - P 2) c := by
    rw [← inner_add_left, ← inner_add_left]; congr 1; simp only [Nat.reduceAdd, zero_add]; abel
  have h0 := hle1 0 (by norm_num)
  have h1 := hle1 1 (by norm_num)
  have h2 := hle1 2 (by norm_num)
  -- the two other steps have projection at least `d`
  have hpos : ∀ i < 3, i ≠ m → d ≤ inner ℝ (P (i + 1) - P i) c := by
    intro i hi him
    interval_cases m <;> interval_cases i <;> first | exact absurd rfl him | linarith
  have close_pos : ∀ i < 3, d ≤ inner ℝ (P (i + 1) - P i) c →
      ‖(P (i + 1) - P i) - c‖ ^ 2 ≤ 1 / 5 := fun i hi h' => by
    rw [norm_sub_sq_real, hunit i hi, hc]; linarith
  have close_neg : ‖(P (m + 1) - P m) + c‖ ^ 2 ≤ 1 / 5 := by
    rw [norm_add_sq_real, hunit m hm, hc]; linarith
  have s02 : P 2 - P 0 = (P (0 + 1) - P 0) + (P (1 + 1) - P 1) := by
    simp only [Nat.reduceAdd, zero_add]; abel
  have s13 : P 3 - P 1 = (P (1 + 1) - P 1) + (P (2 + 1) - P 2) := by
    simp only [Nat.reduceAdd]; abel
  have hs02 := hsep 2 0 (by norm_num) (by norm_num) (by norm_num)
  have hs13 := hsep 3 1 (by norm_num) (by norm_num) (by norm_num)
  rw [s02] at hs02
  rw [s13] at hs13
  interval_cases m
  · rw [add_comm] at hs02
    exact absurd hs02 (not_le.2 (pair_cancel (close_pos 1 (by norm_num)
      (hpos 1 (by norm_num) (by norm_num))) close_neg))
  · exact absurd hs02 (not_le.2 (pair_cancel (close_pos 0 (by norm_num)
      (hpos 0 (by norm_num) (by norm_num))) close_neg))
  · exact absurd hs13 (not_le.2 (pair_cancel (close_pos 1 (by norm_num)
      (hpos 1 (by norm_num) (by norm_num))) close_neg))

/-- **Longer hull returns** (Verification Guide §8.3): for `j ≥ 4` steps and `d ≥ 9/10`, at most
`2 (j - 2) / 3` steps have projection `≤ -d` (the integer capacities one and two for `j = 4, 5`,
and `(j - 1)/1.9 ≤ 2 (j - 2)/3` for `j ≥ 6`). -/
theorem return_capacity {j : ℕ} (hj : 4 ≤ j) {P : ℕ → Plane}
    (hunit : ∀ i < j, ‖P (i + 1) - P i‖ = 1) {c : Plane} (hc : ‖c‖ = 1)
    (hchord : 1 ≤ inner ℝ (P j - P 0) c) {d : ℝ} (hd : 9 / 10 ≤ d) {N : Finset ℕ}
    (hNj : N ⊆ Finset.range j) (hN : ∀ i ∈ N, inner ℝ (P (i + 1) - P i) c ≤ -d) :
    (N.card : ℝ) ≤ 2 * (j - 2) / 3 := by
  have h := return_chord_bound hunit hc hchord hNj hN
  have hr : (N.card : ℝ) * (19 / 10) ≤ j - 1 := by
    have : (N.card : ℝ) * (19 / 10) ≤ N.card * (1 + d) :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
    linarith
  rcases (show j = 4 ∨ j = 5 ∨ 6 ≤ j by omega) with rfl | rfl | h6
  · have : N.card ≤ 1 := by
      by_contra hc'
      have : (2 : ℝ) ≤ N.card := by exact_mod_cast (show 2 ≤ N.card by omega)
      push_cast at hr; linarith
    have : (N.card : ℝ) ≤ 1 := by exact_mod_cast this
    push_cast; linarith
  · have : N.card ≤ 2 := by
      by_contra hc'
      have : (3 : ℝ) ≤ N.card := by exact_mod_cast (show 3 ≤ N.card by omega)
      push_cast at hr; linarith
    have : (N.card : ℝ) ≤ 2 := by exact_mod_cast this
    push_cast; linarith
  · have : (6 : ℝ) ≤ j := by exact_mod_cast h6
    linarith

end LocalCapacity

end Erdos99
end

end LocalCapacity
