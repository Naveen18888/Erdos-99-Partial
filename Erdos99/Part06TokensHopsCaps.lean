module

public import Mathlib
public import Erdos99.Part01Basics
public import Erdos99.Part02LockingAndFans
public import Erdos99.Part03LiftedFanAndDensity
public import Erdos99.Part04RoundnessAndConnectivity
public import Erdos99.Part05FacesAndShores

/-!
# Erdős Problem 99 under finite multiplicity — Part 6 of 9: Tokens, hops, caps and exact counts

This is one of the supporting files of the formalization; the main theorem and a precise
description of what is proved are at the top of `Erdos99.lean`.

The file is divided into the following sections (each `section Name … end Name`); comments
elsewhere in the development refer to these sections by name.

* `ReceiverArea`
* `ReceiverArrivals`
* `LargeRedirect`
* `TokenPruning`
* `TrackHop`
* `HopProcess`
* `HopDirections`
* `LargeFaceLabels`
* `EmissionGeometry`
* `LongExits`
* `TokenLabels`
* `Caps`
* `CapCount`
* `FaceSides`
* `TrackEdges`
* `PortIncidence`
* `ExactCounts`
* `StressLocking`
* `CapLanding`
-/

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `ReceiverArea`
-/

section ReceiverArea

/-!
# WP7, large receivers: the area of a receiver (Verification Guide §9.3)

§9.3 of the Verification Guide sets large receivers aside by comparing two area estimates:

* a receiver (face) is convex, so if its closure contains three points `p, q, r`, its area is
  at least a fixed multiple of `|det(q - p, r - p)|` (**three-point area lower bound**);
* every face that is not a rhombus has area `O(D)`, because the rhombi already fill all of the
  hull area `≤ π D² / 4` except `O(D)` (**receiver area upper bound**).

This file proves both estimates for the exceptional faces of an optimal configuration:

* `volume_ge_of_mem_closure`: a convex set whose closure contains `p, q, r` has area at least
  `|cr (q - p) (r - p)| / 4`.
* `sum_volume_contactFaces_le`: the faces of the contact graph (pulled back to the plane) have
  total area at most `π D² / 4`.
* `aStar_le_volume_rhombusFace`: each rhombus face has area at least `√3 / 2`.
* `exceptionalFaces_area_le`: **the total area of the exceptional faces is `O(D)`**.
* `exceptionalFace_cr_le`: consequently, any three points of the closure of an exceptional face
  span a parallelogram of area `O(D)`.
* `cr_ge_of_near_circle`: three points within `ε` of a circle of radius `R`, pairwise at least
  `s` apart, span area at least `(s - 2ε)³ / (2R) - 24 ε (R + ε)` (the inscribed-triangle bound
  plus perturbation).
* `two_ball_cover`: a set with no three points pairwise `≥ s` apart lies in two balls of radius
  `s`.
* `exceptionalFace_two_balls`: **the two-arc covering consequence**: points near the hull circle
  that all lie within `δ` of one exceptional face are covered by two balls of radius `s`, as soon
  as the area lower bound exceeds the `O(D)` area bound.
* `card_large_exceptional_le`: given `Δ ≥ 0`, at most `5 π D / B` exceptional faces have more than
  `B` sides.
-/

open scoped BigOperators Real
open Filter Topology MeasureTheory Set EstablishedExternalResults

@[expose] public noncomputable section

open Classical

namespace Erdos99

/-! ## Faces are open and pairwise disjoint -/

section Faces

variable {V : Finset ℂ} {E : Finset (Sym2 ℂ)}

lemma isOpen_of_mem_faces {F : Set ℂ} (hF : F ∈ faces V E) : IsOpen F := by
  obtain ⟨x, -, rfl⟩ := hF
  exact IsOpen.connectedComponentIn (isCompact_drawing V E).isClosed.isOpen_compl

lemma faces_disjoint {F G : Set ℂ} (hF : F ∈ faces V E) (hG : G ∈ faces V E) (h : F ≠ G) :
    Disjoint F G := by
  obtain ⟨x, -, rfl⟩ := hF
  obtain ⟨y, -, rfl⟩ := hG
  refine Set.disjoint_left.2 fun z hzx hzy => h ?_
  rw [connectedComponentIn_eq hzx, connectedComponentIn_eq hzy]

end Faces

/-! ## The three-point area lower bound -/

/-- **Three-point area lower bound.**  A convex set whose closure contains `p, q, r` has area at
least `|cr (q - p) (r - p)| / 4` (it contains the parallelogram spanned by `(q - p)/2` and
`(r - p)/2` at `p`, up to a null set). -/
theorem volume_ge_of_mem_closure {S : Set Plane} (hS : Convex ℝ S) {p q r : Plane}
    (hp : p ∈ closure S) (hq : q ∈ closure S) (hr : r ∈ closure S) :
    ENNReal.ofReal (|cr (q - p) (r - p)| / 4) ≤ volume S := by
  have hc := hS.closure
  have hsub : paraOpen p ((1 / 2 : ℝ) • (q - p)) ((1 / 2 : ℝ) • (r - p)) ⊆ closure S := by
    rintro _ ⟨s, t, h1, h2, h3, h4, rfl⟩
    have hmem := hc.sum_mem (t := (Finset.univ : Finset (Fin 3)))
      (w := ![1 - s / 2 - t / 2, s / 2, t / 2]) (z := ![p, q, r])
      (fun i _ => by fin_cases i <;> simp <;> linarith)
      (by simp [Fin.sum_univ_three]; ring)
      (fun i _ => by fin_cases i <;> simpa)
    convert hmem using 1
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    module
  have hcr : cr ((1 / 2 : ℝ) • (q - p)) ((1 / 2 : ℝ) • (r - p)) = cr (q - p) (r - p) / 4 := by
    simp only [cr, PiLp.smul_apply, smul_eq_mul]; ring
  have hfr : volume (closure S) ≤ volume S := by
    rw [closure_eq_self_union_frontier]
    calc volume (S ∪ frontier S) ≤ volume S + volume (frontier S) := measure_union_le _ _
      _ = volume S := by rw [Convex.addHaar_frontier volume hS, add_zero]
  calc ENNReal.ofReal (|cr (q - p) (r - p)| / 4)
      = volume (paraOpen p ((1 / 2 : ℝ) • (q - p)) ((1 / 2 : ℝ) • (r - p))) := by
        rw [volume_paraOpen, hcr, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 4)]
    _ ≤ volume (closure S) := measure_mono hsub
    _ ≤ volume S := hfr

/-! ## Areas of the faces of the contact graph -/

variable {X : Finset Plane}

lemma convexHull_image_toC (s : Set Plane) :
    convexHull ℝ (toC '' s) = toC '' convexHull ℝ s :=
  (toC.toLinearEquiv.toLinearMap.image_convexHull s).symm

/-- Each rhombus face has area at least `aStar = √3 / 2`. -/
theorem aStar_le_volume_rhombusFace (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X)
    {R : Finset Plane} (hR : R ∈ rhombi X) :
    ENNReal.ofReal aStar ≤ volume (toC ⁻¹' cInterior R) := by
  obtain ⟨a, u, w, hQ, hu, hw, hi⟩ := rhombus_rep hX htri hR
  have hsub : paraOpen a u w ⊆ toC ⁻¹' cInterior R := by
    intro z hz
    refine interior_maximal ?_ (toC.toHomeomorph.isOpenMap _
      (isOpen_paraOpen (cr_ne_zero_of_rep hu hw hi))) ⟨z, hz, rfl⟩
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ convexHull ℝ (R : Set Plane) := by
      rw [hQ]; push_cast
      exact (paraOpen_subset_paraClosed _ _ _).trans (paraClosed_subset_convexHull _ _ _) hy
    show toC y ∈ convexHull ℝ (toC '' (R : Set Plane))
    rw [convexHull_image_toC]
    exact ⟨y, hy', rfl⟩
  calc ENNReal.ofReal aStar ≤ ENNReal.ofReal |cr u w| :=
        ENNReal.ofReal_le_ofReal (aStar_le_abs_cr hu hw hi)
    _ = volume (paraOpen a u w) := (volume_paraOpen _ _ _).symm
    _ ≤ _ := measure_mono hsub

/-- The bounded faces of the contact graph, pulled back to the plane, have total area at most
`π D² / 4`. -/
theorem sum_volume_contactFaces_le (hX : IsSeparated X) (hne : X.Nonempty) :
    ∑ F ∈ (contactFaces_finite hX).toFinset, volume (toC ⁻¹' F) ≤
      ENNReal.ofReal (π * diam X ^ 2 / 4) := by
  set S := (contactFaces_finite hX).toFinset
  have hmemS : ∀ F ∈ S, F ∈ contactFaces X := fun F hF => (Set.Finite.mem_toFinset _).1 hF
  have hdisj : (↑S : Set (Set ℂ)).PairwiseDisjoint (fun F => toC ⁻¹' F) := by
    intro F hF G hG hne
    exact (faces_disjoint (hmemS F hF).1 (hmemS G hG).1 hne).preimage _
  have hsub : (⋃ F ∈ S, toC ⁻¹' F) ⊆ convexHull ℝ (X : Set Plane) := by
    refine Set.iUnion₂_subset fun F hF => ?_
    intro z hz
    have h1 := boundedFace_subset_hull (cUnitEdges_isPlaneGraph hX) (hmemS F hF).1
      (hmemS F hF).2 hz
    have e : ((cVerts X : Finset ℂ) : Set ℂ) = toC '' (X : Set Plane) := by
      unfold cVerts; rw [Finset.coe_image]
    rw [e, convexHull_image_toC] at h1
    obtain ⟨y, hy, hyz⟩ := h1
    have : y = z := toC.injective hyz
    exact this ▸ hy
  calc ∑ F ∈ S, volume (toC ⁻¹' F) = volume (⋃ F ∈ S, toC ⁻¹' F) :=
        (measure_biUnion_finset hdisj fun F hF =>
          ((isOpen_of_mem_faces (hmemS F hF).1).preimage toC.continuous).measurableSet).symm
    _ ≤ volume (convexHull ℝ (X : Set Plane)) := measure_mono hsub
    _ ≤ _ := volume_convexHull_le X hne

/-- The exceptional faces and the rhombi share the hull area: `Area(exceptional) + (√3/2) q ≤
π D² / 4`. -/
theorem sum_volume_exceptional_add_le (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X)
    (hne : X.Nonempty) :
    ∑ F ∈ (exceptionalFaces_finite hX).toFinset, (volume (toC ⁻¹' F)).toReal +
      aStar * (rhombi X).card ≤ π * diam X ^ 2 / 4 := by
  set S := (contactFaces_finite hX).toFinset
  set Ex := (exceptionalFaces_finite hX).toFinset
  set Rh := (rhombi X).image cInterior
  have hExS : Ex ⊆ S := fun F hF => (Set.Finite.mem_toFinset _).2
    ((Set.Finite.mem_toFinset _).1 hF).1
  have hRhS : Rh ⊆ S := by
    intro F hF
    obtain ⟨R, hR, rfl⟩ := Finset.mem_image.1 hF
    exact (Set.Finite.mem_toFinset _).2 (rhombus_mem_rhombusFaces hX htri hR).1.1
  have hdisj : Disjoint Ex Rh := by
    rw [Finset.disjoint_left]
    intro F hF hF'
    obtain ⟨R, hR, rfl⟩ := Finset.mem_image.1 hF'
    have h5 := ((Set.Finite.mem_toFinset _).1 hF).2
    have h4 := (rhombus_mem_rhombusFaces hX htri hR).1.2
    omega
  have hinj : Set.InjOn cInterior (rhombi X : Set (Finset Plane)) := by
    intro R hR R' hR' h
    have e1 := (rhombus_mem_rhombusFaces hX htri hR).2
    have e2 := (rhombus_mem_rhombusFaces hX htri hR').2
    rw [h, ← e2] at e1
    exact Finset.coe_injective (Set.image_injective.2 toC.injective e1)
  have htot := sum_volume_contactFaces_le hX hne
  have hRh : (rhombi X).card * ENNReal.ofReal aStar ≤ ∑ F ∈ Rh, volume (toC ⁻¹' F) := by
    rw [Finset.sum_image hinj]
    calc ((rhombi X).card : ENNReal) * ENNReal.ofReal aStar
        = ∑ R ∈ rhombi X, ENNReal.ofReal aStar := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum fun R hR => aStar_le_volume_rhombusFace hX htri hR
  have hsum : ∑ F ∈ Ex, volume (toC ⁻¹' F) + (rhombi X).card * ENNReal.ofReal aStar ≤
      ENNReal.ofReal (π * diam X ^ 2 / 4) := by
    calc ∑ F ∈ Ex, volume (toC ⁻¹' F) + (rhombi X).card * ENNReal.ofReal aStar
        ≤ ∑ F ∈ Ex, volume (toC ⁻¹' F) + ∑ F ∈ Rh, volume (toC ⁻¹' F) := by gcongr
      _ = ∑ F ∈ Ex ∪ Rh, volume (toC ⁻¹' F) := (Finset.sum_union hdisj).symm
      _ ≤ ∑ F ∈ S, volume (toC ⁻¹' F) :=
          Finset.sum_le_sum_of_subset (Finset.union_subset hExS hRhS)
      _ ≤ _ := htot
  have hfin : ∀ F ∈ Ex, volume (toC ⁻¹' F) ≠ ⊤ := by
    intro F hF
    refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_trans ?_ hsum)
    exact le_add_right (Finset.single_le_sum (f := fun F => volume (toC ⁻¹' F))
      (fun _ _ => zero_le _) hF)
  have hA : ∑ F ∈ Ex, volume (toC ⁻¹' F) ≠ ⊤ := ENNReal.sum_ne_top.2 hfin
  have hB : ((rhombi X).card : ENNReal) * ENNReal.ofReal aStar ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsum
  rw [ENNReal.toReal_add hA hB, ENNReal.toReal_sum hfin, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by unfold aStar; positivity),
    ENNReal.toReal_ofReal (by positivity)] at this
  simpa [mul_comm] using this

/-- **Receiver area upper bound** (§9.3).  The exceptional faces of an optimal configuration
without unit triangles have total area `O(D)`. -/
theorem exceptionalFaces_area_le : ∃ C : ℝ, ∀ᶠ n in atTop, numOptimalClasses n < ⊤ →
    ∀ X (hX : IsOptimal n X), ¬ HasUnitTriangle X →
      ∑ F ∈ (exceptionalFaces_finite hX.1.2).toFinset, (volume (toC ⁻¹' F)).toReal ≤
        C * diam X := by
  obtain ⟨C, hC⟩ := rhombi_card_ge
  refine ⟨aStar * C, ?_⟩
  filter_upwards [hC, eventually_ge_atTop 1] with n h hn hfm X hX htri
  have hq := (h hfm X hX htri).2
  have hne : X.Nonempty := by rw [← Finset.card_pos, hX.1.1]; omega
  have hs := sum_volume_exceptional_add_le hX.1.2 htri hne
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

/-- **Large receivers have flat closures** (§9.3).  Any three points of the closure of an
exceptional face span a parallelogram of area `O(D)`. -/
theorem exceptionalFace_cr_le : ∃ C : ℝ, ∀ᶠ n in atTop, numOptimalClasses n < ⊤ →
    ∀ X, IsOptimal n X → ¬ HasUnitTriangle X → ∀ F ∈ exceptionalFaces X, ∀ p q r : Plane,
      toC p ∈ closure F → toC q ∈ closure F → toC r ∈ closure F →
        |cr (q - p) (r - p)| ≤ C * diam X := by
  obtain ⟨C, hC⟩ := exceptionalFaces_area_le
  refine ⟨4 * C, ?_⟩
  filter_upwards [hC, contactFace_convex] with n h hconv hfm X hX htri F hF p q r hp hq hr
  have hsum := h hfm X hX htri
  have hFc : Convex ℝ (toC ⁻¹' F) :=
    (hconv hfm X hX F hF.1).linear_preimage toC.toLinearEquiv.toLinearMap
  have hcl : closure (toC ⁻¹' F) = toC ⁻¹' closure F :=
    (toC.toHomeomorph.preimage_closure F).symm
  have hvol := volume_ge_of_mem_closure hFc (p := p) (q := q) (r := r) (by rw [hcl]; exact hp)
    (by rw [hcl]; exact hq) (by rw [hcl]; exact hr)
  have hbdd : Bornology.IsBounded (toC ⁻¹' F) :=
    toC.isometry.antilipschitz.isBounded_preimage hF.1.2
  have hlt : volume (toC ⁻¹' F) ≠ ⊤ := hbdd.measure_lt_top.ne
  rw [ENNReal.ofReal_le_iff_le_toReal hlt] at hvol
  have hmem : F ∈ (exceptionalFaces_finite hX.1.2).toFinset := (Set.Finite.mem_toFinset _).2 hF
  have hle := Finset.single_le_sum (f := fun F => (volume (toC ⁻¹' F)).toReal)
    (fun _ _ => ENNReal.toReal_nonneg) hmem
  simp only at hle
  linarith

/-! ## Sources near the circle span large triangles; two-ball covering -/

/-- Coordinates of `p` relative to the centre `O`. -/
def relPt (O p : Plane) : ℝ × ℝ := (p 0 - O 0, p 1 - O 1)

lemma triDet_relPt (O p q r : Plane) :
    Propagation.triDet (relPt O p) (relPt O q) (relPt O r) = cr (q - p) (r - p) := by
  simp only [Propagation.triDet, relPt, cr, PiLp.sub_apply]; ring

lemma abs_coord_sub_le (p q : Plane) (i : Fin 2) : |p i - q i| ≤ dist p q := by
  have h := dist_sq_coord p q
  refine abs_le_of_sq_le_sq' ?_ dist_nonneg |>.elim (fun h1 h2 => abs_le.2 ⟨h1, h2⟩)
  fin_cases i <;> simp <;> nlinarith [sq_nonneg (p 0 - q 0), sq_nonneg (p 1 - q 1)]

/-- The radial projection of `p` onto the circle of radius `R` about `O`. -/
def radialProj (O : Plane) (R : ℝ) (p : Plane) : Plane := O + (R / dist p O) • (p - O)

lemma dist_radialProj_center {O p : Plane} {R : ℝ} (hR : 0 ≤ R) (hp : p ≠ O) :
    dist (radialProj O R p) O = R := by
  have hd : 0 < dist p O := dist_pos.2 hp
  rw [radialProj, dist_eq_norm, add_sub_cancel_left, norm_smul, ← dist_eq_norm,
    Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  field_simp

lemma dist_radialProj {O p : Plane} {R : ℝ} (hp : p ≠ O) :
    dist p (radialProj O R p) = |dist p O - R| := by
  have hd : 0 < dist p O := dist_pos.2 hp
  have e : p - radialProj O R p = (1 - R / dist p O) • (p - O) := by
    rw [radialProj]; module
  rw [dist_eq_norm, e, norm_smul, Real.norm_eq_abs, ← dist_eq_norm p O]
  have h1 : (1 - R / dist p O) * dist p O = dist p O - R := by field_simp
  rw [← h1, abs_mul, abs_of_pos hd]

/-- **Three-point area lower bound near a circle** (§9.3).  Three points within `ε` of the circle
of radius `R` about `O`, pairwise at distance at least `s ≥ 2ε`, span a parallelogram of area at
least `(s - 2ε)³ / (2R) - 24 ε (R + ε)`. -/
theorem cr_ge_of_near_circle {O p q r : Plane} {R ε s : ℝ} (hR : 0 < R) (hε : 0 ≤ ε)
    (hεR : ε < R) (hs : 2 * ε ≤ s)
    (hp : |dist p O - R| ≤ ε) (hq : |dist q O - R| ≤ ε) (hr : |dist r O - R| ≤ ε)
    (hpq : s ≤ dist p q) (hqr : s ≤ dist q r) (hrp : s ≤ dist r p) :
    (s - 2 * ε) ^ 3 / (2 * R) - 24 * ε * (R + ε) ≤ |cr (q - p) (r - p)| := by
  have hne : ∀ x : Plane, |dist x O - R| ≤ ε → x ≠ O := by
    intro x hx hxO
    rw [hxO, dist_self, zero_sub, abs_neg, abs_of_pos hR] at hx
    linarith
  set p' := radialProj O R p
  set q' := radialProj O R q
  set r' := radialProj O R r
  have dp := dist_radialProj (R := R) (hne p hp)
  have dq := dist_radialProj (R := R) (hne q hq)
  have dr := dist_radialProj (R := R) (hne r hr)
  have cp := dist_radialProj_center hR.le (hne p hp)
  have cq := dist_radialProj_center hR.le (hne q hq)
  have cr' := dist_radialProj_center hR.le (hne r hr)
  -- the projected points are still separated
  have sep : ∀ x y : Plane, dist x (radialProj O R x) ≤ ε → dist y (radialProj O R y) ≤ ε →
      s ≤ dist x y → s - 2 * ε ≤ dist (radialProj O R x) (radialProj O R y) := by
    intro x y hx hy hxy
    have := dist_triangle4 x (radialProj O R x) (radialProj O R y) y
    rw [dist_comm (radialProj O R y) y] at this
    linarith
  have s1 := sep p q (dp ▸ hp) (dq ▸ hq) hpq
  have s2 := sep q r (dq ▸ hq) (dr ▸ hr) hqr
  have s3 := sep r p (dr ▸ hr) (dp ▸ hp) hrp
  have sq_of : ∀ x y : Plane, s - 2 * ε ≤ dist x y →
      (s - 2 * ε) ^ 2 ≤ ((relPt O x).1 - (relPt O y).1) ^ 2 + ((relPt O x).2 - (relPt O y).2) ^ 2 := by
    intro x y hxy
    have h := dist_sq_coord x y
    have h2 := pow_le_pow_left₀ (by linarith) hxy 2
    simp only [relPt]
    nlinarith
  have circ : ∀ x : Plane, dist x O = R → (relPt O x).1 ^ 2 + (relPt O x).2 ^ 2 = R ^ 2 := by
    intro x hx
    have h := dist_sq_coord x O
    rw [hx] at h
    simp only [relPt]; linarith
  have hin := Propagation.triDet_inscribed_ge hR (by linarith) (circ p' cp) (circ q' cq)
    (circ r' cr') (sq_of _ _ s1) (sq_of _ _ s2) (sq_of _ _ s3)
  -- perturbation back to the original points
  have close : ∀ x : Plane, dist x (radialProj O R x) ≤ ε →
      |(relPt O x).1 - (relPt O (radialProj O R x)).1| ≤ ε ∧
        |(relPt O x).2 - (relPt O (radialProj O R x)).2| ≤ ε := by
    intro x hx
    simp only [relPt, sub_sub_sub_cancel_right]
    exact ⟨(abs_coord_sub_le _ _ 0).trans hx, (abs_coord_sub_le _ _ 1).trans hx⟩
  have bnd : ∀ x : Plane, dist x O ≤ R + ε → |(relPt O x).1| ≤ R + ε ∧ |(relPt O x).2| ≤ R + ε :=
    fun x hx => ⟨(abs_coord_sub_le _ _ 0).trans hx, (abs_coord_sub_le _ _ 1).trans hx⟩
  have bO : ∀ x : Plane, |dist x O - R| ≤ ε → dist x O ≤ R + ε := fun x hx => by
    have := (abs_le.1 hx).2; linarith
  have bO' : ∀ x : Plane, dist x O = R → dist x O ≤ R + ε := fun x hx => by linarith
  have hpert := Propagation.triArea_perturb (close p (dp ▸ hp)) (close q (dq ▸ hq))
    (close r (dr ▸ hr)) (R := R + ε) (by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
      · exact bnd p (bO p hp)
      · exact bnd q (bO q hq)
      · exact bnd r (bO r hr)
      · exact bnd p' (bO' p' cp)
      · exact bnd q' (bO' q' cq)
      · exact bnd r' (bO' r' cr'))
  rw [triDet_relPt] at hpert hin
  rw [triDet_relPt] at hpert
  have := abs_sub_abs_le_abs_sub (cr (q' - p') (r' - p')) (cr (q - p) (r - p))
  rw [abs_sub_comm] at hpert
  linarith

/-- **Two-ball covering.**  If no three points of `S` are pairwise at distance at least `s`, then
for any `x ∈ S` there is `y ∈ S` such that `S` is covered by the balls of radius `s` about `x`
and `y`. -/
theorem two_ball_cover {α : Type*} [PseudoMetricSpace α] {S : Set α} {s : ℝ}
    (h : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, s ≤ dist x y → s ≤ dist y z → s ≤ dist x z → False) :
    ∀ x ∈ S, ∃ y ∈ S, S ⊆ Metric.ball x s ∪ Metric.ball y s := by
  intro x hx
  by_cases hall : S ⊆ Metric.ball x s
  · exact ⟨x, hx, hall.trans Set.subset_union_left⟩
  · obtain ⟨y, hyS, hy⟩ := Set.not_subset.1 hall
    rw [Metric.mem_ball, not_lt] at hy
    refine ⟨y, hyS, fun z hz => ?_⟩
    by_contra hcon
    simp only [Set.mem_union, Metric.mem_ball, not_or, not_lt] at hcon
    exact h x hx y hyS z hz (by rwa [dist_comm]) (by rw [dist_comm]; exact hcon.2)
      (by rw [dist_comm]; exact hcon.1)

/-- **Large receivers: the two-arc covering consequence** (§9.3).  Eventually, for every
exceptional face `F` of an optimal configuration without unit triangles: if a set `P` of points
lies within `ε` of a circle of radius `R` about `O`, every point of `P` is within `δ` of the
closure of `F`, and the area lower bound
`(s - 4δ - 2ε)³ / (2R) - 24 (ε + δ) (R + ε + δ)` exceeds `C D`, then `P` is covered by two
balls of radius `s` (centred at points of `P`). -/
theorem exceptionalFace_two_balls : ∃ C : ℝ, ∀ᶠ n in atTop, numOptimalClasses n < ⊤ →
    ∀ X, IsOptimal n X → ¬ HasUnitTriangle X → ∀ F ∈ exceptionalFaces X,
    ∀ (O : Plane) (R ε δ s : ℝ), 0 < R → 0 ≤ ε → 0 ≤ δ → ε + δ < R →
      2 * (ε + δ) ≤ s - 2 * δ →
      C * diam X < (s - 2 * δ - 2 * (ε + δ)) ^ 3 / (2 * R) - 24 * (ε + δ) * (R + (ε + δ)) →
      ∀ P : Set Plane, (∀ p ∈ P, |dist p O - R| ≤ ε ∧ ∃ z, toC z ∈ closure F ∧ dist p z ≤ δ) →
      ∀ p₀ ∈ P, ∃ p₁ ∈ P, P ⊆ Metric.ball p₀ s ∪ Metric.ball p₁ s := by
  obtain ⟨C, hC⟩ := exceptionalFace_cr_le
  refine ⟨C, ?_⟩
  filter_upwards [hC] with n h hfm X hX htri F hF O R ε δ s hR hε hδ hεR hs hbig P hP
  refine two_ball_cover fun x hx y hy z hz hxy hyz hxz => ?_
  obtain ⟨hx1, x', hx'F, hxx'⟩ := hP x hx
  obtain ⟨hy1, y', hy'F, hyy'⟩ := hP y hy
  obtain ⟨hz1, z', hz'F, hzz'⟩ := hP z hz
  have near : ∀ w w' : Plane, |dist w O - R| ≤ ε → dist w w' ≤ δ →
      |dist w' O - R| ≤ ε + δ := by
    intro w w' hw hww'
    have t1 := dist_triangle w' w O
    have t2 := dist_triangle w w' O
    rw [dist_comm w' w] at t1
    rw [abs_le] at hw ⊢
    constructor <;> linarith [hw.1, hw.2]
  have far : ∀ w v w' v' : Plane, s ≤ dist w v → dist w w' ≤ δ → dist v v' ≤ δ →
      s - 2 * δ ≤ dist w' v' := by
    intro w v w' v' h1 h2 h3
    have := dist_triangle4 w w' v' v
    rw [dist_comm v' v] at this
    linarith
  have key := cr_ge_of_near_circle (O := O) (p := x') (q := y') (r := z') hR (by linarith)
    hεR hs (near x x' hx1 hxx') (near y y' hy1 hyy') (near z z' hz1 hzz')
    (far x y x' y' hxy hxx' hyy') (far y z y' z' hyz hyy' hzz')
    (far z x z' x' (by rwa [dist_comm]) hzz' hxx')
  have hcr := h hfm X hX htri F hF x' y' z' hx'F hy'F hz'F
  linarith

/-! ## Few receivers have many sides -/

/-- `Σ_{k ≥ 5} k f_k ≤ 5 σ`: every exceptional face has `k ≤ 5 (k - 4)`. -/
theorem sum_faceSize_le_five_faceExcess (hX : IsSeparated X) :
    ∑ F ∈ (exceptionalFaces_finite hX).toFinset, faceSize X F ≤ 5 * faceExcess X := by
  rw [faceExcess_eq_sum (exceptionalFaces_finite hX), Finset.mul_sum]
  refine Finset.sum_le_sum fun F hF => ?_
  have := ((Set.Finite.mem_toFinset _).1 hF).2
  omega

/-- **Large receivers are few** (§9.3).  If `Δ ≥ 0`, then for every `B > 0` the number of
exceptional faces with more than `B` sides is at most `5 π D / B`: indeed
`Σ_{k ≥ 5} k f_k ≤ 5 σ ≤ 5 u ≤ 5 b ≤ 5 π D`. -/
theorem card_large_exceptional_le (hX : IsSeparated X) (h2 : 2 ≤ X.card)
    (hΔ : 0 ≤ lockingDefect X) {B : ℝ} (hB : 0 < B) :
    (((exceptionalFaces_finite hX).toFinset.filter (fun F => B < faceSize X F)).card : ℝ) ≤
      5 * π * diam X / B := by
  set S := (exceptionalFaces_finite hX).toFinset
  have hsum := sum_faceSize_le_five_faceExcess hX
  have h3 := numUnitHullSides_le X
  have h4 := hullVertices_card_le_pi_mul_diam hX h2
  unfold lockingDefect at hΔ
  have hσ : faceExcess X ≤ (hullVertices X).card := by
    have : (0 : ℤ) ≤ returnExcess X := by positivity
    omega
  have hσ' : (faceExcess X : ℝ) ≤ π * diam X := le_trans (by exact_mod_cast hσ) h4
  have hlarge : (((S.filter (fun F => B < faceSize X F)).card : ℝ)) * B ≤
      ∑ F ∈ S, (faceSize X F : ℝ) := by
    calc (((S.filter (fun F => B < faceSize X F)).card : ℝ)) * B
        = ∑ F ∈ S.filter (fun F => B < faceSize X F), B := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ F ∈ S.filter (fun F => B < faceSize X F), (faceSize X F : ℝ) :=
          Finset.sum_le_sum fun F hF => (Finset.mem_filter.1 hF).2.le
      _ ≤ ∑ F ∈ S, (faceSize X F : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => Nat.cast_nonneg _)
  have hsum' : ∑ F ∈ S, (faceSize X F : ℝ) ≤ 5 * faceExcess X := by exact_mod_cast hsum
  rw [le_div_iff₀ hB]
  linarith

end Erdos99

end

end ReceiverArea

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `ReceiverArrivals`
-/

section ReceiverArrivals

/-!
# Large receivers: the arrival bound (Verification Guide §9.3)

§9.3 of the Verification Guide sets the large receivers aside with three separate estimates: the
three-point area lower bound and the two-arc covering consequence (both in `ReceiverArea`),
and an **arrival bound**: a receiver whose arriving labels have their sources in two short arcs of
the hull receives few tokens.  This file proves the arrival bound and the resulting total over
the large receivers.

* `card_hullVertices_ball_le`: at most `2πs + 1` hull vertices of a separated set lie in a closed
  ball of radius `s` (they are in convex position, so Lemma 3.1 applies to them).
* `card_unitHullSides_ball_le`: hence at most `2πs + 1` unit hull sides start in such a ball.
* `card_le_of_labels_two_balls` (**arrival bound**): tokens carrying pairwise distinct source
  labels, whose sources all start in one of two balls of radius `s`, number at most
  `2 (2πs + 1)`.
* `sum_large_le`: if every receiver with more than `B` sides receives at most `M` tokens then,
  given `Δ ≥ 0`, all of them together receive at most `(5πD/B) M`
  (from `card_large_exceptional_le`).
* `large_receiver_total_littleO`: with the choices of §9.3, `B = D^{1 - e/8}` and arrivals in two
  balls of radius `s = C D^{1 - e/4}`, this total is `o(D)`.
-/

open scoped BigOperators Real
open Filter Topology Set EstablishedExternalResults

@[expose] public noncomputable section

open Classical

namespace Erdos99

variable {X : Finset Plane}

/-- **Hull vertices in a ball.**  At most `2πs + 1` hull vertices of a separated set lie in a
closed ball of radius `s ≥ 0`. -/
theorem card_hullVertices_ball_le (hX : IsSeparated X) (p : Plane) {s : ℝ} (hs : 0 ≤ s) :
    (((hullVertices X).filter (fun x => dist x p ≤ s)).card : ℝ) ≤ 2 * π * s + 1 := by
  set Y := (hullVertices X).filter (fun x => dist x p ≤ s) with hY
  have hYX : Y ⊆ X := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hYsep : IsSeparated Y := fun x hx y hy hxy => hX x (hYX hx) y (hYX hy) hxy
  by_cases h2 : 2 ≤ Y.card
  · have hhv : hullVertices Y = Y := by
      refine Finset.filter_true_of_mem (fun x hx => ?_)
      have hxe : x ∈ Set.extremePoints ℝ (convexHull ℝ (X : Set Plane)) :=
        (Finset.mem_filter.1 (Finset.mem_filter.1 hx).1).2
      refine inter_extremePoints_subset_extremePoints_of_subset
        (convexHull_mono (by exact_mod_cast hYX)) ⟨subset_convexHull ℝ _ hx, hxe⟩
    have h1 := hullVertices_card_le_pi_mul_diam hYsep h2
    rw [hhv] at h1
    have hdiam : diam Y ≤ 2 * s := by
      refine Metric.diam_le_of_forall_dist_le (by linarith) (fun x hx y hy => ?_)
      have hx' := (Finset.mem_filter.1 hx).2
      have hy' := (Finset.mem_filter.1 hy).2
      calc dist x y ≤ dist x p + dist p y := dist_triangle _ _ _
        _ ≤ s + s := by rw [dist_comm p y]; exact add_le_add hx' hy'
        _ = 2 * s := by ring
    have := Real.pi_pos
    nlinarith
  · push_neg at h2
    have : (Y.card : ℝ) ≤ 1 := by exact_mod_cast (show Y.card ≤ 1 by omega)
    have := Real.pi_pos
    nlinarith

/-- **Unit hull sides starting in a ball.**  At most `2πs + 1` unit hull sides of a separated set
start in a closed ball of radius `s ≥ 0`. -/
theorem card_unitHullSides_ball_le (hX : IsSeparated X) (p : Plane) {s : ℝ} (hs : 0 ≤ s) :
    (((unitHullSides X).filter (fun q => dist q.1 p ≤ s)).card : ℝ) ≤ 2 * π * s + 1 := by
  refine le_trans ?_ (card_hullVertices_ball_le hX p hs)
  have : ((unitHullSides X).filter (fun q => dist q.1 p ≤ s)).card ≤
      ((hullVertices X).filter (fun x => dist x p ≤ s)).card := by
    refine Finset.card_le_card_of_injOn Prod.fst (fun q hq => ?_) (fun q hq q' hq' h => ?_)
    · obtain ⟨hq1, hq2⟩ := Finset.mem_filter.1 hq
      have hs := mem_ccwHullSides.1 (Finset.mem_filter.1 hq1).1
      exact Finset.mem_filter.2 ⟨hs.1, hq2⟩
    · have hs := mem_ccwHullSides.1 (Finset.mem_filter.1 (Finset.mem_filter.1 hq).1).1
      have hs' := mem_ccwHullSides.1 (Finset.mem_filter.1 (Finset.mem_filter.1 hq').1).1
      have h' : q.1 = q'.1 := h
      rw [← h'] at hs'
      exact Prod.ext h' (hs.succ_unique hs')
  exact_mod_cast this

/-- **The arrival bound** (§9.3).  Tokens carrying pairwise distinct source labels (unit hull
sides), whose sources all start within `s` of one of two points, number at most `2 (2πs + 1)`. -/
theorem card_le_of_labels_two_balls (hX : IsSeparated X) {α : Type*} (A : Finset α)
    (L : α → Plane × Plane) (hL : Set.InjOn L A) (hmem : ∀ t ∈ A, L t ∈ unitHullSides X)
    (p₀ p₁ : Plane) {s : ℝ} (hs : 0 ≤ s)
    (hball : ∀ t ∈ A, dist (L t).1 p₀ ≤ s ∨ dist (L t).1 p₁ ≤ s) :
    (A.card : ℝ) ≤ 2 * (2 * π * s + 1) := by
  have hsub : A.image L ⊆ (unitHullSides X).filter (fun q => dist q.1 p₀ ≤ s) ∪
      (unitHullSides X).filter (fun q => dist q.1 p₁ ≤ s) := by
    intro q hq
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hq
    rcases hball t ht with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hmem t ht, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hmem t ht, h⟩)
  have hcard : A.card ≤ ((unitHullSides X).filter (fun q => dist q.1 p₀ ≤ s)).card +
      ((unitHullSides X).filter (fun q => dist q.1 p₁ ≤ s)).card := by
    rw [← Finset.card_image_of_injOn hL]
    exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have h0 := card_unitHullSides_ball_le hX p₀ hs
  have h1 := card_unitHullSides_ball_le hX p₁ hs
  have : (A.card : ℝ) ≤ ((unitHullSides X).filter (fun q => dist q.1 p₀ ≤ s)).card +
      ((unitHullSides X).filter (fun q => dist q.1 p₁ ≤ s)).card := by exact_mod_cast hcard
  linarith

/-- **Total arrivals at the large receivers.**  If `Δ ≥ 0` and every exceptional face with more
than `B` sides receives at most `M` tokens, then together these faces receive at most
`(5πD/B) M` tokens. -/
theorem sum_large_le (hX : IsSeparated X) (h2 : 2 ≤ X.card) (hΔ : 0 ≤ lockingDefect X)
    {B M : ℝ} (hB : 0 < B) (hM : 0 ≤ M) (a : Set ℂ → ℝ)
    (ha : ∀ F ∈ exceptionalFaces X, B < faceSize X F → a F ≤ M) :
    ∑ F ∈ (exceptionalFaces_finite hX).toFinset.filter (fun F => B < faceSize X F), a F ≤
      5 * π * diam X / B * M := by
  set L := (exceptionalFaces_finite hX).toFinset.filter (fun F => B < faceSize X F)
  calc ∑ F ∈ L, a F ≤ ∑ _F ∈ L, M := Finset.sum_le_sum (fun F hF => by
        obtain ⟨hF1, hF2⟩ := Finset.mem_filter.1 hF
        exact ha F ((Set.Finite.mem_toFinset _).1 hF1) hF2)
    _ = L.card * M := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 5 * π * diam X / B * M :=
        mul_le_mul_of_nonneg_right (card_large_exceptional_le hX h2 hΔ hB) hM

/-- **The large receivers cost `o(D)`** (§9.3).  With `B = D^{1 - e/8}` and at most
`2 (2πs + 1)` arrivals per large receiver, where `s = C D^{1 - e/4}`, the total
`(5πD/B) · 2 (2πs + 1)` is eventually at most `η D`, for every `η > 0`. -/
theorem large_receiver_total_littleO {e C η : ℝ} (he : 0 < e) (he1 : e ≤ 1)
    (hη : 0 < η) :
    ∀ᶠ D : ℝ in atTop, 5 * π * D / D ^ (1 - e / 8) *
      (2 * (2 * π * (C * D ^ (1 - e / 4)) + 1)) ≤ η * D := by
  filter_upwards [eventually_mul_rpow_le (20 * π ^ 2 * C) (α := 1 - e / 8) (by linarith)
      (half_pos hη), eventually_mul_rpow_le (10 * π) (α := e / 8) (by linarith) (half_pos hη),
    eventually_gt_atTop 0] with D h1 h2 hD
  have e1 : D / D ^ (1 - e / 8) = D ^ (e / 8) := by
    rw [div_eq_iff (by positivity), ← Real.rpow_add hD, add_sub_cancel, Real.rpow_one]
  have e2 : D ^ (e / 8) * D ^ (1 - e / 4) = D ^ (1 - e / 8) := by
    rw [← Real.rpow_add hD]; ring_nf
  have : 5 * π * D / D ^ (1 - e / 8) * (2 * (2 * π * (C * D ^ (1 - e / 4)) + 1)) =
      20 * π ^ 2 * C * D ^ (1 - e / 8) + 10 * π * D ^ (e / 8) := by
    rw [mul_div_assoc, e1, ← e2]; ring
  rw [this]
  linarith

end Erdos99

end

end ReceiverArrivals

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `LargeRedirect`
-/

section LargeRedirect

/-!
# Sending the large receivers to the loss bin (Verification Guide §9.3)

§9.3 of the Verification Guide charges all tokens arriving at *large* receivers (exceptional faces
with more than `B_K = D^{1 - e_K/8}` sides) to the lost-incidence budget.  This file carries out
that step on the token process.

* `TokenProcess.redirect P L`: the process `P` in which every token sent to a face satisfying
  `L` is sent to the loss bin instead.
* If no face satisfying `L` can emit (all have more than `7` sides), then the redirected process
  has the same arrivals as `P` at every other face (`faceArr_redirect_of_not`,
  `arrivals_redirect_of_not`), no arrivals at all at the faces satisfying `L`
  (`arrivals_redirect_of`), the same cap arrivals (`capArr_redirect`), and its losses are those of
  `P` plus the arrivals of `P` at the exceptional faces satisfying `L` (`lostArr_redirect`).
* `exists_markedTokenProcess_of_small`: the routing statement of `Stability` follows from a
  routing whose arrivals are marked at the exceptional faces with at most `B_K` sides, and whose
  arrivals at each larger exceptional face carry distinct source labels from two balls of radius
  `C D^{1 - e_K/4}` (the arrival bound `card_le_of_labels_two_balls` and the count
  `sum_large_le`, with `Δ ≥ 0`, then make the total over the large faces `o(D)`).
-/

open scoped BigOperators Real
open Filter Topology

@[expose] public noncomputable section

open Classical

namespace Erdos99

open Propagation

namespace TokenProcess

variable {X : Finset Plane}

/-- Send a token to the loss bin if its receiver is a face satisfying `L`. -/
def redirectDest (L : Set ℂ → Prop) : TokenDest → TokenDest
  | .face F => if L F then .lost else .face F
  | .cap => .cap
  | .lost => .lost

/-- The process `P` with every token sent to a face satisfying `L` sent to the loss bin. -/
def redirect (P : TokenProcess X) (L : Set ℂ → Prop) : TokenProcess X where
  fin := P.fin
  start p := redirectDest L (P.start p)
  out G := redirectDest L (P.out G)

variable (P : TokenProcess X) (L : Set ℂ → Prop)

lemma toFace_redirectDest_of_not {F : Set ℂ} (hF : ¬ L F) (d : TokenDest) :
    toFace (redirectDest L d) F = toFace d F := by
  cases d with
  | face G =>
    by_cases hG : L G
    · have : G ≠ F := fun h => hF (h ▸ hG)
      simp [redirectDest, hG, toFace, this]
    · simp [redirectDest, hG]
  | cap => simp [redirectDest]
  | lost => simp [redirectDest]

lemma redirectDest_ne_face_of {F : Set ℂ} (hF : L F) (d : TokenDest) :
    redirectDest L d ≠ .face F := by
  cases d with
  | face G =>
    by_cases hG : L G
    · simp [redirectDest, hG]
    · have : G ≠ F := fun h => hG (h ▸ hF)
      simp [redirectDest, hG, this]
  | cap => simp [redirectDest]
  | lost => simp [redirectDest]

lemma toCap_redirectDest (d : TokenDest) : toCap (redirectDest L d) = toCap d := by
  cases d with
  | face G => by_cases hG : L G <;> simp [redirectDest, hG, toCap]
  | cap => simp [redirectDest]
  | lost => simp [redirectDest]

lemma toLost_redirectDest (S : Finset (Set ℂ)) (d : TokenDest) :
    toLost S (redirectDest L d) = toLost S d + ∑ F ∈ S.filter L, toFace d F := by
  cases d with
  | face G =>
    by_cases hGS : G ∈ S <;> by_cases hG : L G
    · rw [Finset.sum_eq_single_of_mem G (Finset.mem_filter.2 ⟨hGS, hG⟩)
        (fun F _ hF => by simp [toFace, Ne.symm hF])]
      simp [redirectDest, hG, toLost, toFace, hGS]
    · rw [Finset.sum_eq_zero (fun F hF => by
        have : G ≠ F := fun h => hG (h ▸ (Finset.mem_filter.1 hF).2)
        simp [toFace, this])]
      simp [redirectDest, hG]
    · rw [Finset.sum_eq_zero (fun F hF => by
        have : G ≠ F := fun h => hGS (h ▸ (Finset.mem_filter.1 hF).1)
        simp [toFace, this])]
      simp [redirectDest, hG, toLost, hGS]
    · rw [Finset.sum_eq_zero (fun F hF => by
        have : G ≠ F := fun h => hGS (h ▸ (Finset.mem_filter.1 hF).1)
        simp [toFace, this])]
      simp [redirectDest, hG]
  | cap => simp [redirectDest, toLost, toFace]
  | lost => simp [redirectDest, toLost, toFace]

variable {L}

/-- The faces satisfying `L` never emit. -/
def NoEmit (X : Finset Plane) (L : Set ℂ → Prop) : Prop := ∀ G, L G → 7 < faceSize X G

lemma emitted_eq_zero_of_noEmit (hL : NoEmit X L) {G : Set ℂ} (hG : L G) (a : ℕ) :
    emitted (faceSize X G) a = 0 :=
  emitted_eq_zero ⟨by have := hL G hG; omega, by have := hL G hG; omega⟩

/-- Away from the redirected faces, the redirected process has the same arrivals. -/
theorem faceArr_redirect_of_not (hL : NoEmit X L) (j : ℕ) {F : Set ℂ} (hF : ¬ L F) :
    (P.redirect L).faceArr j F = P.faceArr j F := by
  induction j generalizing F with
  | zero => rfl
  | succ j ih =>
    show ∑ p ∈ unitHullSides X, toFace (redirectDest L (P.start p)) F +
        ∑ G ∈ P.fin.toFinset, toFace (redirectDest L (P.out G)) F *
          emitted (faceSize X G) ((P.redirect L).faceArr j G) = P.faceArr (j + 1) F
    simp only [toFace_redirectDest_of_not L hF]
    show _ = ∑ p ∈ unitHullSides X, toFace (P.start p) F +
        ∑ G ∈ P.fin.toFinset, toFace (P.out G) F * emitted (faceSize X G) (P.faceArr j G)
    congr 1
    refine Finset.sum_congr rfl (fun G _ => ?_)
    by_cases hG : L G
    · rw [emitted_eq_zero_of_noEmit hL hG, emitted_eq_zero_of_noEmit hL hG]
    · rw [ih hG]

/-- Emission is unchanged by the redirection. -/
lemma emitted_redirect (hL : NoEmit X L) (j : ℕ) (G : Set ℂ) :
    emitted (faceSize X G) ((P.redirect L).faceArr j G) = emitted (faceSize X G) (P.faceArr j G) := by
  by_cases hG : L G
  · rw [emitted_eq_zero_of_noEmit hL hG, emitted_eq_zero_of_noEmit hL hG]
  · rw [P.faceArr_redirect_of_not hL j hG]

/-- Away from the redirected faces, the arriving tokens are the same. -/
theorem arrivals_redirect_of_not (hL : NoEmit X L) (j : ℕ) {F : Set ℂ} (hF : ¬ L F) :
    (P.redirect L).arrivals j F = P.arrivals j F := by
  have h1 : ∀ d : TokenDest, redirectDest L d = .face F ↔ d = .face F := by
    intro d
    cases d with
    | face G =>
      by_cases hG : L G
      · have : G ≠ F := fun h => hF (h ▸ hG)
        simp [redirectDest, hG, this]
      · simp [redirectDest, hG]
    | cap => simp [redirectDest]
    | lost => simp [redirectDest]
  unfold arrivals
  congr 1
  · exact Finset.filter_congr (fun p _ => h1 (P.start p))
  · exact Finset.filter_congr (fun G _ => by
      rw [emitted_redirect P hL]; exact and_congr_left' (h1 _))

/-- The redirected faces receive nothing. -/
theorem arrivals_redirect_of {j : ℕ} {F : Set ℂ} (hF : L F) :
    (P.redirect L).arrivals j F = ∅ := by
  unfold arrivals
  simp [redirect, redirectDest_ne_face_of L hF]

/-- The cap arrivals are unchanged. -/
theorem capArr_redirect (hL : NoEmit X L) (j : ℕ) :
    (P.redirect L).capArr j = P.capArr j := by
  cases j with
  | zero => rfl
  | succ j =>
    show ∑ p ∈ unitHullSides X, toCap (redirectDest L (P.start p)) +
        ∑ G ∈ P.fin.toFinset, toCap (redirectDest L (P.out G)) *
          emitted (faceSize X G) ((P.redirect L).faceArr j G) = _
    simp only [toCap_redirectDest, emitted_redirect P hL]
    rfl

/-- The losses grow by the arrivals at the redirected exceptional faces. -/
theorem lostArr_redirect (hL : NoEmit X L) (j : ℕ) :
    (P.redirect L).lostArr j =
      P.lostArr j + ∑ F ∈ P.fin.toFinset.filter L, P.faceArr j F := by
  cases j with
  | zero => simp [lostArr, faceArr]
  | succ j =>
    show ∑ p ∈ unitHullSides X, toLost P.fin.toFinset (redirectDest L (P.start p)) +
        ∑ G ∈ P.fin.toFinset, toLost P.fin.toFinset (redirectDest L (P.out G)) *
          emitted (faceSize X G) ((P.redirect L).faceArr j G) = _
    simp only [toLost_redirectDest, emitted_redirect P hL, add_mul, Finset.sum_add_distrib,
      Finset.sum_mul]
    show _ = (∑ p ∈ unitHullSides X, toLost P.fin.toFinset (P.start p) +
        ∑ G ∈ P.fin.toFinset, toLost P.fin.toFinset (P.out G) *
          emitted (faceSize X G) (P.faceArr j G)) +
      ∑ F ∈ P.fin.toFinset.filter L, (∑ p ∈ unitHullSides X, toFace (P.start p) F +
        ∑ G ∈ P.fin.toFinset, toFace (P.out G) F * emitted (faceSize X G) (P.faceArr j G))
    rw [Finset.sum_add_distrib, Finset.sum_comm (s := unitHullSides X),
      Finset.sum_comm (s := P.fin.toFinset) (t := P.fin.toFinset.filter L)]
    ring

end TokenProcess

/-- **Large receivers go to the loss bin** (§9.3).  Let `e = e_K` and `B = D^{1 - e/8}`.  Suppose
that `Δ ≥ 0` eventually and that, for some `C ≥ 0`, eventually every configuration admits a
routing `P` with entry data `E` such that

* the arrivals after `K + 1` rounds are marked at every exceptional face with at most `B` sides;
* the tokens arriving at each exceptional face with more than `B` sides carry pairwise distinct
  source labels (unit hull sides) starting in two balls of radius `C D^{1 - e/4}`;
* at most `2ρ/3 + (η/2) D` tokens reach caps, and at most `#(long sources) + (η/2) D` are lost.

Then eventually every configuration admits a routing whose arrivals are marked at *every*
exceptional face, with at most `2ρ/3 + η D` cap arrivals and `#(long sources) + η D` losses:
redirect the tokens of the large faces to the loss bin (these faces never emit), and bound their
number by the arrival bound and `sum_large_le`. -/
theorem exists_markedTokenProcess_of_small (K : ℕ) (η : ℝ) (hη : 0 < η)
    (hΔ : ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      0 ≤ lockingDefect X)
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      ¬ HasUnitTriangle X →
      ∃ (P : TokenProcess X) (E : TokenProcess.Entry X),
        (∀ F ∈ exceptionalFaces X, (faceSize X F : ℝ) ≤ diam X ^ (1 - scaleExp K / 8) →
          P.MarkedArrivals E K F) ∧
        (∀ F ∈ exceptionalFaces X, diam X ^ (1 - scaleExp K / 8) < faceSize X F →
          ∃ (lab : (Plane × Plane) ⊕ Set ℂ → Plane × Plane) (c₀ c₁ : Plane),
            Set.InjOn lab (P.arrivals K F) ∧ ∀ t ∈ P.arrivals K F, lab t ∈ unitHullSides X ∧
              (dist (lab t).1 c₀ ≤ C * diam X ^ (1 - scaleExp K / 4) ∨
                dist (lab t).1 c₁ ≤ C * diam X ^ (1 - scaleExp K / 4))) ∧
        (P.capArr (K + 1) : ℝ) ≤ 2 * (returnExcess X : ℝ) / 3 + η / 2 * diam X ∧
        (P.lostArr (K + 1) : ℝ) ≤ (((unitHullSides X).filter
          (fun p => diam X ^ (19 / 20 : ℝ) ≤ srcLen X s(p.1, p.2))).card : ℝ) + η / 2 * diam X) :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∃ (P : TokenProcess X) (E : TokenProcess.Entry X),
        (∀ F ∈ exceptionalFaces X, P.MarkedArrivals E K F) ∧
        (P.capArr (K + 1) : ℝ) ≤ 2 * (returnExcess X : ℝ) / 3 + η * diam X ∧
        (P.lostArr (K + 1) : ℝ) ≤ (((unitHullSides X).filter
          (fun p => diam X ^ (19 / 20 : ℝ) ≤ srcLen X s(p.1, p.2))).card : ℝ) + η * diam X := by
  obtain ⟨C, hC, hev⟩ := h
  set e := scaleExp K with he
  have he0 : 0 < e := scaleExp_pos K
  have he1 : e ≤ 1 := (scaleExp_le K).trans (by norm_num)
  have hB7 : ∀ᶠ D : ℝ in atTop, 7 ≤ D ^ (1 - e / 8) :=
    (tendsto_rpow_atTop (by linarith)).eventually_ge_atTop 7
  have hD : ∀ᶠ D : ℝ in atTop, 0 < D ∧ 7 ≤ D ^ (1 - e / 8) ∧ 5 * π * D / D ^ (1 - e / 8) *
      (2 * (2 * π * (C * D ^ (1 - e / 4)) + 1)) ≤ η / 2 * D :=
    (eventually_gt_atTop 0).and (hB7.and (large_receiver_total_littleO he0 he1 (half_pos hη)))
  filter_upwards [hev, hΔ, tendsto_minDiam.eventually hD, eventually_ge_atTop 2] with
    n hn hΔn hDn hn2 hfm X hX htri
  obtain ⟨P, E, hsmall, hlarge, hcap, hlost⟩ := hn hfm X hX htri
  rw [← hX.diam_eq] at hDn
  obtain ⟨hDpos, hB7', hbound⟩ := hDn
  set D := diam X with hDdef
  set B := D ^ (1 - e / 8) with hBdef
  have hBpos : 0 < B := by positivity
  set L : Set ℂ → Prop := fun F => B < faceSize X F with hL
  have hNE : TokenProcess.NoEmit X L := fun G hG => by
    have : (7 : ℝ) < faceSize X G := lt_of_le_of_lt hB7' hG
    exact_mod_cast this
  have hsep : IsSeparated X := hX.1.2
  have h2 : 2 ≤ X.card := by rw [hX.1.1]; exact hn2
  set s := C * D ^ (1 - e / 4) with hs
  have hs0 : 0 ≤ s := by positivity
  have hηD : η / 2 * D ≤ η * D := by nlinarith
  refine ⟨P.redirect L, E, fun F hF => ?_, ?_, ?_⟩
  · by_cases hLF : L F
    · refine ⟨?_, 1, by simp, ?_⟩
      · rw [P.arrivals_redirect_of hLF]; simp
      · intro t ht
        rw [P.arrivals_redirect_of hLF] at ht
        simp at ht
    · rw [TokenProcess.MarkedArrivals, P.arrivals_redirect_of_not hNE K hLF]
      exact hsmall F hF (not_lt.1 hLF)
  · rw [P.capArr_redirect hNE]; linarith
  · rw [P.lostArr_redirect hNE]
    push_cast
    have hsum : ∑ F ∈ P.fin.toFinset.filter L, (P.faceArr (K + 1) F : ℝ) ≤
        5 * π * D / B * (2 * (2 * π * s + 1)) := by
      refine sum_large_le hsep h2 (hΔn hfm X hX htri) hBpos (by positivity)
        (fun F => (P.faceArr (K + 1) F : ℝ)) (fun F hF hBF => ?_)
      obtain ⟨lab, c₀, c₁, hinj, hmem⟩ := hlarge F hF hBF
      show (P.faceArr (K + 1) F : ℝ) ≤ _
      rw [P.faceArr_succ_eq_card]
      exact card_le_of_labels_two_balls hsep _ lab hinj (fun t ht => (hmem t ht).1) c₀ c₁ hs0
        (fun t ht => (hmem t ht).2)
    linarith

end Erdos99

end

end LargeRedirect

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `TokenPruning`
-/

section TokenPruning

/-!
# Discarding tokens (Verification Guide §9.2)

The process of §9 discards some tokens outright: in round `j` only emitted tracks shorter than
`Λ_j` are retained, the tracks removed by clustering are discarded, and so on; each discarded
token is charged to the lost-incidence budget.  This file shows that discarding is always
harmless for the face conditions:

* `TokenProcess.prune P bad`: the process `P` in which every source and every emitting face whose
  token is *bad* sends its token to the loss bin instead.
* Pruning only removes arrivals: `faceArr_prune_le`, `capArr_prune_le`, and the tokens arriving at
  a face in the pruned process are good tokens arriving there in `P` (`arrivals_prune_subset`).
* The losses grow by at most the number of bad tokens (`lostArr_prune_le`).
* Hence marked arrivals among the good tokens are marked arrivals of the pruned process
  (`MarkedArrivals.of_subset`), and distinct source labels in two balls persist.
* `exists_smallMarkedTokenProcess_of_pruned`: it suffices to build a routing in which only the
  **good** arrivals are controlled, provided the losses plus the number of bad tokens are at most
  `#(long sources) + η D`.
-/

open scoped BigOperators Real
open Filter Topology

@[expose] public noncomputable section

open Classical

namespace Erdos99

open Propagation

namespace TokenProcess

variable {X : Finset Plane}

/-- The process `P` in which the token of every bad source and of every bad emitting face is sent
to the loss bin. -/
def prune (P : TokenProcess X) (bad : (Plane × Plane) ⊕ Set ℂ → Prop) : TokenProcess X where
  fin := P.fin
  start p := if bad (.inl p) then .lost else P.start p
  out G := if bad (.inr G) then .lost else P.out G

variable (P : TokenProcess X) (bad : (Plane × Plane) ⊕ Set ℂ → Prop)

lemma toFace_ite_le (b : Prop) [Decidable b] (d : TokenDest) (F : Set ℂ) :
    toFace (if b then .lost else d) F ≤ toFace d F := by
  split_ifs <;> simp [toFace]

lemma toCap_ite_le (b : Prop) [Decidable b] (d : TokenDest) :
    toCap (if b then .lost else d) ≤ toCap d := by
  split_ifs <;> simp [toCap]

lemma toLost_ite_le (S : Finset (Set ℂ)) (b : Prop) [Decidable b] (d : TokenDest) :
    toLost S (if b then .lost else d) ≤ toLost S d + if b then 1 else 0 := by
  split_ifs <;> simp [toLost]

/-- Pruning only removes arrivals at faces. -/
theorem faceArr_prune_le (j : ℕ) (F : Set ℂ) : (P.prune bad).faceArr j F ≤ P.faceArr j F := by
  induction j generalizing F with
  | zero => exact le_rfl
  | succ j ih =>
    show ∑ p ∈ unitHullSides X, toFace (if bad (.inl p) then .lost else P.start p) F +
        ∑ G ∈ P.fin.toFinset, toFace (if bad (.inr G) then .lost else P.out G) F *
          emitted (faceSize X G) ((P.prune bad).faceArr j G) ≤
      ∑ p ∈ unitHullSides X, toFace (P.start p) F +
        ∑ G ∈ P.fin.toFinset, toFace (P.out G) F * emitted (faceSize X G) (P.faceArr j G)
    gcongr with p _ G _
    · exact toFace_ite_le _ _ _
    · exact toFace_ite_le _ _ _
    · exact TokenLedger.emitted_mono _ (ih G)

lemma emitted_prune_le (j : ℕ) (G : Set ℂ) :
    emitted (faceSize X G) ((P.prune bad).faceArr j G) ≤ emitted (faceSize X G) (P.faceArr j G) :=
  TokenLedger.emitted_mono _ (P.faceArr_prune_le bad j G)

/-- Pruning only removes arrivals at caps. -/
theorem capArr_prune_le (j : ℕ) : (P.prune bad).capArr j ≤ P.capArr j := by
  cases j with
  | zero => exact le_rfl
  | succ j =>
    show ∑ p ∈ unitHullSides X, toCap (if bad (.inl p) then .lost else P.start p) +
        ∑ G ∈ P.fin.toFinset, toCap (if bad (.inr G) then .lost else P.out G) *
          emitted (faceSize X G) ((P.prune bad).faceArr j G) ≤
      ∑ p ∈ unitHullSides X, toCap (P.start p) +
        ∑ G ∈ P.fin.toFinset, toCap (P.out G) * emitted (faceSize X G) (P.faceArr j G)
    gcongr with p _ G _
    · exact toCap_ite_le _ _
    · exact toCap_ite_le _ _
    · exact P.emitted_prune_le bad j G

/-- The number of bad tokens: bad sources and bad exceptional faces. -/
def numBad : ℕ :=
  ((unitHullSides X).filter (fun p => bad (.inl p))).card +
    (P.fin.toFinset.filter (fun G => bad (.inr G))).card

/-- Pruning loses at most the bad tokens. -/
theorem lostArr_prune_le (j : ℕ) : (P.prune bad).lostArr j ≤ P.lostArr j + P.numBad bad := by
  cases j with
  | zero => exact Nat.zero_le _
  | succ j =>
    show ∑ p ∈ unitHullSides X, toLost P.fin.toFinset (if bad (.inl p) then .lost else P.start p) +
        ∑ G ∈ P.fin.toFinset, toLost P.fin.toFinset (if bad (.inr G) then .lost else P.out G) *
          emitted (faceSize X G) ((P.prune bad).faceArr j G) ≤
      (∑ p ∈ unitHullSides X, toLost P.fin.toFinset (P.start p) +
        ∑ G ∈ P.fin.toFinset, toLost P.fin.toFinset (P.out G) *
          emitted (faceSize X G) (P.faceArr j G)) + P.numBad bad
    have h1 : ∑ p ∈ unitHullSides X,
        toLost P.fin.toFinset (if bad (.inl p) then .lost else P.start p) ≤
        ∑ p ∈ unitHullSides X, toLost P.fin.toFinset (P.start p) +
          ((unitHullSides X).filter (fun p => bad (.inl p))).card := by
      rw [Finset.card_filter, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum (fun p _ => toLost_ite_le _ _ _)
    have h2 : ∑ G ∈ P.fin.toFinset, toLost P.fin.toFinset (if bad (.inr G) then .lost else P.out G) *
          emitted (faceSize X G) ((P.prune bad).faceArr j G) ≤
        ∑ G ∈ P.fin.toFinset, toLost P.fin.toFinset (P.out G) *
          emitted (faceSize X G) (P.faceArr j G) +
          (P.fin.toFinset.filter (fun G => bad (.inr G))).card := by
      rw [Finset.card_filter, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum (fun G _ => ?_)
      have he := P.emitted_prune_le bad j G
      have he1 : emitted (faceSize X G) (P.faceArr j G) ≤ 1 := by
        rcases emitted_eq_zero_or_one (faceSize X G) (P.faceArr j G) with h | h <;> omega
      have hl := toLost_ite_le P.fin.toFinset (bad (.inr G)) (P.out G)
      calc toLost P.fin.toFinset (if bad (.inr G) then .lost else P.out G) *
            emitted (faceSize X G) ((P.prune bad).faceArr j G)
          ≤ (toLost P.fin.toFinset (P.out G) + if bad (.inr G) then 1 else 0) *
            emitted (faceSize X G) (P.faceArr j G) := Nat.mul_le_mul hl he
        _ ≤ _ := by
          rw [add_mul]
          gcongr
          split_ifs <;> omega
    unfold numBad
    omega

/-- The tokens arriving at a face in the pruned process are good tokens arriving there in `P`. -/
theorem arrivals_prune_subset (j : ℕ) (F : Set ℂ) :
    (P.prune bad).arrivals j F ⊆ (P.arrivals j F).filter (fun t => ¬ bad t) := by
  intro t ht
  unfold arrivals at ht
  rw [Finset.mem_disjSum] at ht
  rw [Finset.mem_filter]
  rcases ht with ⟨p, hp, rfl⟩ | ⟨G, hG, rfl⟩
  · obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
    change (if bad (.inl p) then TokenDest.lost else P.start p) = .face F at hp2
    split_ifs at hp2 with hb
    exact ⟨Finset.mem_disjSum.2 (Or.inl ⟨p, Finset.mem_filter.2 ⟨hp1, hp2⟩, rfl⟩), hb⟩
  · obtain ⟨hG1, hG2, hG3⟩ := Finset.mem_filter.1 hG
    change (if bad (.inr G) then TokenDest.lost else P.out G) = .face F at hG2
    split_ifs at hG2 with hb
    have he := P.emitted_prune_le bad j G
    have he' : emitted (faceSize X G) (P.faceArr j G) = 1 := by
      rcases emitted_eq_zero_or_one (faceSize X G) (P.faceArr j G) with h | h <;> omega
    exact ⟨Finset.mem_disjSum.2 (Or.inr ⟨G, Finset.mem_filter.2 ⟨hG1, hG2, he'⟩, rfl⟩), hb⟩

end TokenProcess

/-- Arrivals marked within a larger set of tokens are marked. -/
theorem TokenProcess.MarkedArrivals.of_subset {X : Finset Plane} {P : TokenProcess X}
    {E : TokenProcess.Entry X} {j : ℕ} {F : Set ℂ} {A : Finset ((Plane × Plane) ⊕ Set ℂ)}
    (hA : P.arrivals j F ⊆ A) (hinj : Set.InjOn E.edge A)
    (hmark : ∃ e : ℂ, ‖e‖ = 1 ∧ ∀ t ∈ A,
      E.edge t ∈ orientedSides X F ∧ 19 / 20 ≤ inner ℝ ((E.edge t).2 - (E.edge t).1) e) :
    P.MarkedArrivals E j F := by
  obtain ⟨e, he, h⟩ := hmark
  exact ⟨hinj.mono (by exact_mod_cast hA), e, he, fun t ht => h t (hA ht)⟩

/-- **Discarded tokens are harmless** (§9.2).  Let `e = e_K` and `B = D^{1 - e/8}`.  Suppose
that, for some `C ≥ 0`, eventually every configuration admits a routing `P` with entry data `E`
and a set of *bad* tokens such that, among the **good** tokens arriving after `K + 1` rounds,

* the arrivals at every exceptional face with at most `B` sides are marked (pairwise distinct
  entry sides of the face, all with projection at least `19/20` on one unit vector);
* the arrivals at every exceptional face with more than `B` sides carry pairwise distinct source
  labels starting in two balls of radius `C D^{1 - e/4}`;

that at most `2ρ/3 + η D` tokens reach caps, and that the losses plus the number of bad tokens
are at most `#(long sources) + η D`.  Then the same holds with no bad tokens at all, i.e. with
conditions on *all* arrivals: discard the bad tokens (`TokenProcess.prune`). -/
theorem exists_smallMarkedTokenProcess_of_pruned (K : ℕ) (η : ℝ)
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
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
          (fun p => diam X ^ (19 / 20 : ℝ) ≤ srcLen X s(p.1, p.2))).card : ℝ) + η * diam X) :
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
          (fun p => diam X ^ (19 / 20 : ℝ) ≤ srcLen X s(p.1, p.2))).card : ℝ) + η * diam X := by
  obtain ⟨C, hC, hev⟩ := h
  refine ⟨C, hC, ?_⟩
  filter_upwards [hev] with n hn hfm X hX htri
  obtain ⟨P, E, bad, hsmall, hlarge, hcap, hlost⟩ := hn hfm X hX htri
  have hsub := P.arrivals_prune_subset bad K
  refine ⟨P.prune bad, E, fun F hF hBF => ?_, fun F hF hBF => ?_, ?_, ?_⟩
  · obtain ⟨hinj, hmark⟩ := hsmall F hF hBF
    exact TokenProcess.MarkedArrivals.of_subset (hsub F) hinj hmark
  · obtain ⟨lab, c₀, c₁, hinj, hmem⟩ := hlarge F hF hBF
    exact ⟨lab, c₀, c₁, hinj.mono (by exact_mod_cast hsub F), fun t ht => hmem t (hsub F ht)⟩
  · have : ((P.prune bad).capArr (K + 1) : ℝ) ≤ P.capArr (K + 1) := by
      exact_mod_cast P.capArr_prune_le bad (K + 1)
    linarith
  · have : ((P.prune bad).lostArr (K + 1) : ℝ) ≤ P.lostArr (K + 1) + P.numBad bad := by
      exact_mod_cast P.lostArr_prune_le bad (K + 1)
    linarith

end Erdos99

end

end TokenPruning

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `TrackHop`
-/

section TrackHop

/-!
# Following a track to its far end (Verification Guide §9.1)

A token of the finite token process of §9.1 leaves its current position through an oriented unit
edge `p = (a, b)` (its *exit edge*) and travels along the track of `p`, crossing the rhombi on the
left of the edge one after the other, until it reaches the last edge of the track on that side.
This file formalizes this *hop* along a track and proves its basic invariants.

* `LeftStep X p q`: `q` is the side opposite to `p` across a unit rhombus of `X` lying to the left
  of `p`, oriented in the same direction (`q.2 - q.1 = p.2 - p.1`).
* `LeftStep.unique`, `LeftStep.unique_pred`: an oriented edge has at most one rhombus on each
  side, so the step is a partial injection.
* `hopEnd X p`: the far end of the track of `p`, reached by stepping to the left as long as
  possible.  It is a fixed oriented unit edge with **exactly the same direction** as `p`
  (`hopEnd_sub`), and no rhombus lies on its left (`hopEnd_terminal`).
* `dist_hopEnd_le` (**locality**): the far end is within `r(T)` of the exit edge, where
  `r(T) = srcLen X s(p.1, p.2)` is the number of rhombi on the track.
* `hopEnd_injOn` (**distinct track incidences**): exit edges with no rhombus on their right
  (`Initial`) have pairwise distinct far ends.
* `initial_of_mem_unitHullSides`: unit hull sides are initial (nothing of `X` lies to their
  right).
-/

open scoped BigOperators Real

@[expose] public noncomputable section

open Classical

namespace Erdos99

/-- `q` is the side opposite to the oriented unit edge `p` across a unit rhombus
`p.1 - p.2 - q.2 - q.1` of `X` that lies to the left of `p`; `q` is oriented in the same direction
as `p`. -/
def LeftStep (X : Finset Plane) (p q : Plane × Plane) : Prop :=
  ({p.1, p.2, q.2, q.1} : Finset Plane) ∈ rhombi X ∧ dist p.1 p.2 = 1 ∧ dist p.2 q.2 = 1 ∧
    dist q.2 q.1 = 1 ∧ dist q.1 p.1 = 1 ∧ q.2 - q.1 = p.2 - p.1 ∧
    0 < det2 (p.2 - p.1) (q.1 - p.1)

/-- An oriented edge with no rhombus on its right: no left step leads to it. -/
def Initial (X : Finset Plane) (p : Plane × Plane) : Prop := ¬ ∃ q, LeftStep X q p

lemma det2_sub_left' (u v w : Plane) : det2 (u - v) w = det2 u w - det2 v w := by
  unfold det2; simp; ring

lemma det2_neg_right (u v : Plane) : det2 u (-v) = -det2 u v := by
  unfold det2; simp; ring

lemma det2_neg_left (u v : Plane) : det2 (-u) v = -det2 u v := by
  unfold det2; simp; ring

lemma det2_self' (u : Plane) : det2 u u = 0 := by unfold det2; ring

lemma det2_add_right_hop (d a b : Plane) : det2 d (a + b) = det2 d a + det2 d b := by
  unfold det2; simp; ring

section
variable {X : Finset Plane}

lemma LeftStep.mem {p q : Plane × Plane} (h : LeftStep X p q) :
    p.1 ∈ X ∧ p.2 ∈ X ∧ q.1 ∈ X ∧ q.2 ∈ X := by
  have hsub := (Finset.mem_powersetCard.1 (Finset.mem_filter.1 h.1).1).1
  exact ⟨hsub (by simp), hsub (by simp), hsub (by simp), hsub (by simp)⟩

/-- Reversing both edges of a left step gives a left step backwards. -/
lemma LeftStep.rev {p q : Plane × Plane} (h : LeftStep X p q) :
    LeftStep X (q.2, q.1) (p.2, p.1) := by
  obtain ⟨hR, h1, h2, h3, h4, hpar, hdet⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : ({q.2, q.1, p.1, p.2} : Finset Plane) = {p.1, p.2, q.2, q.1} := by
      ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
    simpa [this] using hR
  · simpa [dist_comm] using h3
  · simpa [dist_comm] using h4
  · simpa [dist_comm] using h1
  · simpa [dist_comm] using h2
  · show p.1 - p.2 = q.1 - q.2
    rw [← neg_sub p.2, ← neg_sub q.2, hpar]
  · show 0 < det2 (q.1 - q.2) (p.2 - q.2)
    have e1 : q.1 - q.2 = -(p.2 - p.1) := by rw [← hpar]; abel
    have e2 : p.2 - q.2 = -(q.1 - p.1) := by
      have : q.2 = q.1 + (p.2 - p.1) := by rw [← hpar]; abel
      rw [this]; abel
    rw [e1, e2, det2_neg_neg]; exact hdet

variable (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X)
include hX htri

/-- **An oriented edge has at most one rhombus on its left.** -/
lemma LeftStep.unique {p q q' : Plane × Plane} (h : LeftStep X p q) (h' : LeftStep X p q') :
    q = q' := by
  obtain ⟨hR, h1, h2, h3, h4, hpar, hdet⟩ := h
  obtain ⟨hR', -, h2', h3', h4', hpar', hdet'⟩ := h'
  obtain ⟨-, -, hq1, hq2⟩ := LeftStep.mem ⟨hR, h1, h2, h3, h4, hpar, hdet⟩
  obtain ⟨-, -, hq1', -⟩ := LeftStep.mem ⟨hR', h1, h2', h3', h4', hpar', hdet'⟩
  set u := p.2 - p.1 with hu_def
  have hu : ‖u‖ = 1 := by rw [hu_def, ← dist_eq_norm, dist_comm]; exact h1
  -- the diagonals of the rhombi are longer than one
  have key : ∀ {c d : Plane}, ({p.1, p.2, d, c} : Finset Plane) ∈ rhombi X → dist p.2 d = 1 →
      dist d c = 1 → dist c p.1 = 1 → d - c = u →
      ‖c - p.1‖ = 1 ∧ |inner ℝ (c - p.1) u| < 1 / 2 := by
    intro c d hR h2 h3 h4 hpar
    obtain ⟨d1, d2⟩ := rhombus_diagonals_gt_one hX htri hR h1 h2 h3 h4
    have hw : ‖c - p.1‖ = 1 := by rw [← dist_eq_norm]; exact h4
    have hd : d = p.1 + (c - p.1) + u := by rw [← hpar]; abel
    have hbc : p.2 = p.1 + u := by rw [hu_def]; abel
    rw [dist_eq_norm, hd, show p.1 - (p.1 + (c - p.1) + u) = -((c - p.1) + u) by abel,
      norm_neg] at d1
    rw [dist_eq_norm, hbc, show p.1 + u - c = u - (c - p.1) by abel] at d2
    have e1 : ‖(c - p.1) + u‖ ^ 2 = 2 + 2 * inner ℝ (c - p.1) u := by
      rw [norm_add_sq_real, hw, hu]; ring
    have e2 : ‖u - (c - p.1)‖ ^ 2 = 2 - 2 * inner ℝ (c - p.1) u := by
      rw [norm_sub_sq_real, hw, hu, real_inner_comm]; ring
    have s1 : 1 < ‖(c - p.1) + u‖ ^ 2 := by nlinarith
    have s2 : 1 < ‖u - (c - p.1)‖ ^ 2 := by nlinarith
    refine ⟨hw, abs_lt.2 ⟨by linarith, by linarith⟩⟩
  obtain ⟨n1, i1⟩ := key hR h2 h3 h4 hpar
  obtain ⟨n2, i2⟩ := key hR' h2' h3' h4' hpar'
  have hs : 0 < inner ℝ (q.1 - p.1) (rot u) * inner ℝ (q'.1 - p.1) (rot u) := by
    rw [inner_rot_eq_det2, inner_rot_eq_det2]; exact mul_pos hdet hdet'
  have hclose := norm_sub_lt_one_of_same_side u _ _ hu n1 n2 i1 i2 hs
  have hc : q.1 = q'.1 := by
    by_contra hne
    have := hX _ hq1 _ hq1' hne
    rw [dist_eq_norm, show q.1 - q'.1 = (q.1 - p.1) - (q'.1 - p.1) by abel] at this
    linarith
  have hd : q.2 = q'.2 := by
    rw [show q.2 = q.1 + (q.2 - q.1) by abel, show q'.2 = q'.1 + (q'.2 - q'.1) by abel, hpar,
      hpar', hc]
  exact Prod.ext hc hd

/-- **An oriented edge has at most one rhombus on its right.** -/
lemma LeftStep.unique_pred {p p' q : Plane × Plane} (h : LeftStep X p q) (h' : LeftStep X p' q) :
    p = p' := by
  have := LeftStep.unique hX htri h.rev h'.rev
  simp only [Prod.mk.injEq] at this
  exact Prod.ext this.2 this.1

end

/-! ## The step and the hop -/

/-- One step to the left along the track, if possible. -/
def stepL (X : Finset Plane) (p : Plane × Plane) : Plane × Plane :=
  if h : ∃ q, LeftStep X p q then h.choose else p

/-- **The far end of the track of the oriented edge `p` on its left**: step to the left as long as
possible.  (`|X|²` steps suffice, see `hopEnd_terminal`.) -/
def hopEnd (X : Finset Plane) (p : Plane × Plane) : Plane × Plane :=
  (stepL X)^[(X ×ˢ X).card] p

section
variable {X : Finset Plane}

lemma stepL_spec {p : Plane × Plane} (h : ∃ q, LeftStep X p q) : LeftStep X p (stepL X p) := by
  simp only [stepL, dif_pos h]; exact h.choose_spec

lemma stepL_of_not {p : Plane × Plane} (h : ¬ ∃ q, LeftStep X p q) : stepL X p = p := by
  simp only [stepL, dif_neg h]

lemma stepL_sub (p : Plane × Plane) : (stepL X p).2 - (stepL X p).1 = p.2 - p.1 := by
  by_cases h : ∃ q, LeftStep X p q
  · exact (stepL_spec h).2.2.2.2.2.1
  · rw [stepL_of_not h]

lemma iterate_stepL_sub (p : Plane × Plane) (k : ℕ) :
    ((stepL X)^[k] p).2 - ((stepL X)^[k] p).1 = p.2 - p.1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', stepL_sub, ih]

/-- **The hop preserves the direction exactly** (opposite sides of a rhombus are parallel). -/
lemma hopEnd_sub (p : Plane × Plane) : (hopEnd X p).2 - (hopEnd X p).1 = p.2 - p.1 :=
  iterate_stepL_sub p _

lemma stepL_mem {p : Plane × Plane} (hp : p ∈ X ×ˢ X) : stepL X p ∈ X ×ˢ X := by
  by_cases h : ∃ q, LeftStep X p q
  · obtain ⟨-, -, h1, h2⟩ := (stepL_spec h).mem
    exact Finset.mem_product.2 ⟨h1, h2⟩
  · rwa [stepL_of_not h]

lemma iterate_stepL_mem {p : Plane × Plane} (hp : p ∈ X ×ˢ X) (k : ℕ) :
    (stepL X)^[k] p ∈ X ×ˢ X := by
  induction k with
  | zero => exact hp
  | succ k ih => rw [Function.iterate_succ_apply']; exact stepL_mem ih

lemma hopEnd_mem {p : Plane × Plane} (hp : p ∈ X ×ˢ X) : hopEnd X p ∈ X ×ˢ X :=
  iterate_stepL_mem hp _

/-- Once the step is stuck, it stays stuck. -/
lemma iterate_stepL_stuck {p : Plane × Plane} {k : ℕ} (h : ¬ ∃ q, LeftStep X ((stepL X)^[k] p) q)
    (j : ℕ) (hj : k ≤ j) : (stepL X)^[j] p = (stepL X)^[k] p := by
  induction j, hj using Nat.le_induction with
  | base => rfl
  | succ j _ ih => rw [Function.iterate_succ_apply', ih, stepL_of_not h]

/-- The height of a point relative to the direction `u`. -/
lemma det2_iterate_stepL_lt (p : Plane × Plane) {i j : ℕ} (hij : i < j)
    (hmove : ∀ k < j, ∃ q, LeftStep X ((stepL X)^[k] p) q) :
    det2 (p.2 - p.1) ((stepL X)^[i] p).1 < det2 (p.2 - p.1) ((stepL X)^[j] p).1 := by
  induction j, hij using Nat.le_induction with
  | base =>
    rw [Function.iterate_succ_apply']
    have hs := stepL_spec (hmove i (by omega))
    have := hs.2.2.2.2.2.2
    rw [iterate_stepL_sub, det2_sub_right] at this
    linarith
  | succ j hij ih =>
    have ih := ih (fun k hk => hmove k (by omega))
    rw [Function.iterate_succ_apply']
    have hs := stepL_spec (hmove j (by omega))
    have := hs.2.2.2.2.2.2
    rw [iterate_stepL_sub, det2_sub_right] at this
    linarith

/-- **The hop stops at the far end**: no rhombus lies to the left of `hopEnd X p`. -/
lemma hopEnd_terminal {p : Plane × Plane} (hp : p ∈ X ×ˢ X) : ¬ ∃ q, LeftStep X (hopEnd X p) q := by
  set N := (X ×ˢ X).card
  by_cases hall : ∀ k < N + 1, ∃ q, LeftStep X ((stepL X)^[k] p) q
  · exfalso
    have hinj : Set.InjOn (fun k => (stepL X)^[k] p) (Finset.range (N + 1) : Set ℕ) := by
      intro i hi j hj hij
      simp only [Finset.coe_range, Set.mem_Iio] at hi hj
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · have := det2_iterate_stepL_lt p h (fun k hk => hall k (by omega))
        simp only at hij; rw [hij] at this; exact lt_irrefl _ this
      · have := det2_iterate_stepL_lt p h (fun k hk => hall k (by omega))
        simp only at hij; rw [hij] at this; exact lt_irrefl _ this
    have := Finset.card_le_card_of_injOn _ (fun k _ => iterate_stepL_mem hp k) hinj
    simp only [Finset.card_range] at this
    omega
  · push_neg at hall
    obtain ⟨k, hk, hstuck⟩ := hall
    have hstuck' : ¬ ∃ q, LeftStep X ((stepL X)^[k] p) q := fun ⟨q, hq⟩ => hstuck q hq
    unfold hopEnd
    rw [iterate_stepL_stuck hstuck' N (by omega)]
    exact hstuck'

/-- The number of steps of the hop: the first index at which the step is stuck. -/
lemma exists_hopLen {p : Plane × Plane} (hp : p ∈ X ×ˢ X) :
    ∃ m, (stepL X)^[m] p = hopEnd X p ∧ (∀ k < m, ∃ q, LeftStep X ((stepL X)^[k] p) q) ∧
      ¬ ∃ q, LeftStep X ((stepL X)^[m] p) q := by
  have hex : ∃ m, ¬ ∃ q, LeftStep X ((stepL X)^[m] p) q := ⟨_, hopEnd_terminal hp⟩
  refine ⟨Nat.find hex, ?_, fun k hk => not_not.1 (Nat.find_min hex hk), Nat.find_spec hex⟩
  have hle : Nat.find hex ≤ (X ×ˢ X).card := Nat.find_min' hex (hopEnd_terminal hp)
  unfold hopEnd
  rw [iterate_stepL_stuck (Nat.find_spec hex) _ hle]

end

section
variable {X : Finset Plane} (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X)
include hX htri

/-- **Distinct track incidences**: initial exit edges have distinct far ends. -/
theorem hopEnd_injOn {p p' : Plane × Plane} (hp : p ∈ X ×ˢ X) (hp' : p' ∈ X ×ˢ X)
    (hi : Initial X p) (hi' : Initial X p') (h : hopEnd X p = hopEnd X p') : p = p' := by
  obtain ⟨m, hm, hmv, -⟩ := exists_hopLen hp
  obtain ⟨m', hm', hmv', -⟩ := exists_hopLen hp'
  -- walk back from the common far end
  have back : ∀ i, i ≤ m → i ≤ m' → (stepL X)^[m - i] p = (stepL X)^[m' - i] p' := by
    intro i
    induction i with
    | zero => intro _ _; simp only [Nat.sub_zero]; rw [hm, hm', h]
    | succ i ih =>
      intro hi1 hi2
      have e := ih (by omega) (by omega)
      have s1 := stepL_spec (hmv (m - (i + 1)) (by omega))
      have s2 := stepL_spec (hmv' (m' - (i + 1)) (by omega))
      rw [← Function.iterate_succ_apply' (stepL X), show (m - (i + 1)).succ = m - i by omega,
        e] at s1
      rw [← Function.iterate_succ_apply' (stepL X), show (m' - (i + 1)).succ = m' - i by omega]
        at s2
      exact LeftStep.unique_pred hX htri s1 s2
  rcases le_total m m' with hle | hle
  · have e := back m le_rfl hle
    simp only [Nat.sub_self, Function.iterate_zero, id] at e
    rcases Nat.eq_or_lt_of_le hle with heq | hlt
    · rw [e, heq, Nat.sub_self]; rfl
    · exfalso
      apply hi
      refine ⟨(stepL X)^[m' - m - 1] p', ?_⟩
      have s := stepL_spec (hmv' (m' - m - 1) (by omega))
      rwa [← Function.iterate_succ_apply' (stepL X), show (m' - m - 1).succ = m' - m by omega,
        ← e] at s
  · have e := back m' hle le_rfl
    simp only [Nat.sub_self, Function.iterate_zero, id] at e
    rcases Nat.eq_or_lt_of_le hle with heq | hlt
    · rw [← e, heq, Nat.sub_self]; rfl
    · exfalso
      apply hi'
      refine ⟨(stepL X)^[m - m' - 1] p, ?_⟩
      have s := stepL_spec (hmv (m - m' - 1) (by omega))
      rwa [← Function.iterate_succ_apply' (stepL X), show (m - m' - 1).succ = m - m' by omega,
        e] at s

end

/-! ## Locality -/

section
variable {X : Finset Plane}

lemma LeftStep.opp {p q : Plane × Plane} (h : LeftStep X p q) :
    OppositeSides X s(p.1, p.2) s(q.1, q.2) := by
  obtain ⟨hR, h1, h2, h3, h4, -, -⟩ := h
  exact ⟨p.1, p.2, q.2, q.1, hR, h1, h2, h3, h4, rfl, Sym2.eq_swap⟩

lemma LeftStep.rhombusEdge {p q : Plane × Plane} (h : LeftStep X p q) :
    s(p.1, p.2) ∈ rhombusEdges X := by
  obtain ⟨h1, h2, -, -⟩ := h.mem
  refine Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨p, ?_, rfl⟩, _, h.opp⟩
  simp [h1, h2, h.2.1]

/-- Each move of the hop has length one. -/
lemma LeftStep.dist {p q : Plane × Plane} (h : LeftStep X p q) : dist q.1 p.1 = 1 := h.2.2.2.2.1

/-- The edges visited by the hop lie on the track of the exit edge. -/
lemma iterate_mem_trackOf {p : Plane × Plane} {m : ℕ}
    (hmv : ∀ k < m, ∃ q, LeftStep X ((stepL X)^[k] p) q) (k : ℕ) (hk : k ≤ m) (hm : 0 < m) :
    s(((stepL X)^[k] p).1, ((stepL X)^[k] p).2) ∈ trackOf X s(p.1, p.2) := by
  have h0 : s(p.1, p.2) ∈ rhombusEdges X := (stepL_spec (hmv 0 hm)).rhombusEdge
  induction k with
  | zero => exact mem_trackOf_self h0
  | succ k ih =>
    have ih := ih (by omega)
    have s := stepL_spec (hmv k (by omega))
    rw [Function.iterate_succ_apply']
    obtain ⟨hr, heq⟩ := mem_trackOf.1 ih
    refine mem_trackOf.2 ⟨?_, Relation.EqvGen.trans _ _ _ heq (Relation.EqvGen.rel _ _ s.opp)⟩
    obtain ⟨-, -, h1, h2⟩ := s.mem
    refine Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨_, ?_, rfl⟩, _,
      oppositeSides_symm s.opp⟩
    simp only [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨h1, h2⟩, by rw [dist_comm]; exact s.2.2.2.1⟩

/-- The number of steps of a hop is at most the number of rhombi on the track. -/
lemma hopLen_le_srcLen {p : Plane × Plane} {m : ℕ}
    (hmv : ∀ k < m, ∃ q, LeftStep X ((stepL X)^[k] p) q) : m ≤ srcLen X s(p.1, p.2) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact Nat.zero_le _
  set R : ℕ → Finset Plane := fun k =>
    {((stepL X)^[k] p).1, ((stepL X)^[k] p).2, ((stepL X)^[k + 1] p).2, ((stepL X)^[k + 1] p).1}
  have hR : ∀ k < m, LeftStep X ((stepL X)^[k] p) ((stepL X)^[k + 1] p) := fun k hk => by
    rw [Function.iterate_succ_apply']; exact stepL_spec (hmv k hk)
  unfold srcLen trackLength
  have hinj : Set.InjOn R (Finset.range m : Set ℕ) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    by_contra hne
    -- heights of the vertices of the rhombus `R k`
    have hgt : ∀ k < m, ∀ z ∈ R k, det2 (p.2 - p.1) z = det2 (p.2 - p.1) ((stepL X)^[k] p).1 ∨
        det2 (p.2 - p.1) z = det2 (p.2 - p.1) ((stepL X)^[k + 1] p).1 := by
      intro k hk z hz
      have e1 : ((stepL X)^[k] p).2 = ((stepL X)^[k] p).1 + (p.2 - p.1) := by
        rw [← iterate_stepL_sub (X := X) p k]; abel
      have e2 : ((stepL X)^[k + 1] p).2 = ((stepL X)^[k + 1] p).1 + (p.2 - p.1) := by
        rw [← iterate_stepL_sub (X := X) p (k + 1)]; abel
      simp only [R, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · left; rfl
      · left; rw [e1, det2_add_right_hop, det2_self', add_zero]
      · right; rw [e2, det2_add_right_hop, det2_self', add_zero]
      · right; rfl
    have hmv' : ∀ k < m, ∃ q, LeftStep X ((stepL X)^[k] p) q := hmv
    rcases lt_or_gt_of_ne hne with h | h
    · have hz : ((stepL X)^[i] p).1 ∈ R j := by rw [← hij]; simp [R]
      have a1 := det2_iterate_stepL_lt p h (fun k hk => hmv' k (by omega))
      have a2 := det2_iterate_stepL_lt p (Nat.lt_succ_self j) (fun k hk => hmv' k (by omega))
      rcases hgt j hj _ hz with e | e <;> linarith
    · have hz : ((stepL X)^[j] p).1 ∈ R i := by rw [hij]; simp [R]
      have a1 := det2_iterate_stepL_lt p h (fun k hk => hmv' k (by omega))
      have a2 := det2_iterate_stepL_lt p (Nat.lt_succ_self i) (fun k hk => hmv' k (by omega))
      rcases hgt i hi _ hz with e | e <;> linarith
  have hc := Finset.card_le_card_of_injOn (s := Finset.range m)
    (t := (rhombi X).filter (Crosses (trackOf X s(p.1, p.2)))) R (fun k hk => by
    have hk' : k < m := Finset.mem_range.1 hk
    refine Finset.mem_filter.2 ⟨(hR k hk').1, ?_⟩
    refine ⟨_, iterate_mem_trackOf hmv k hk'.le hm, fun x hx => ?_⟩
    rcases Sym2.mem_iff.1 hx with rfl | rfl <;> simp [R]) hinj
  rw [Finset.card_range] at hc
  exact hc

/-- **Locality of the hop**: the far end of the track lies within `r(T)` of the exit edge. -/
theorem dist_hopEnd_le {p : Plane × Plane} (hp : p ∈ X ×ˢ X) :
    dist (hopEnd X p).1 p.1 ≤ srcLen X s(p.1, p.2) := by
  obtain ⟨m, hm, hmv, -⟩ := exists_hopLen hp
  have hle := hopLen_le_srcLen hmv
  have hd : ∀ k ≤ m, dist ((stepL X)^[k] p).1 p.1 ≤ k := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      have ih := ih (by omega)
      rw [Function.iterate_succ_apply']
      have := (stepL_spec (hmv k (by omega))).dist
      calc dist (stepL X ((stepL X)^[k] p)).1 p.1
          ≤ dist (stepL X ((stepL X)^[k] p)).1 ((stepL X)^[k] p).1 +
            dist ((stepL X)^[k] p).1 p.1 := dist_triangle _ _ _
        _ ≤ 1 + k := by rw [this]; linarith
        _ = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [← hm]
  exact (hd m le_rfl).trans (by exact_mod_cast hle)

end

/-- **Unit hull sides are initial**: no point of `X` lies to the right of a counterclockwise hull
side, so no rhombus does. -/
lemma initial_of_mem_unitHullSides {X : Finset Plane} {p : Plane × Plane}
    (hp : p ∈ unitHullSides X) : Initial X p := by
  rintro ⟨q, hq⟩
  obtain ⟨h1, -⟩ := Finset.mem_filter.1 hp
  obtain ⟨-, -, -, -, hl⟩ := Finset.mem_filter.1 h1
  obtain ⟨hq1, -, -, -⟩ := hq.mem
  have hdet := hq.2.2.2.2.2.2
  have hpar := hq.2.2.2.2.2.1
  -- `q.1` lies strictly to the right of `p`
  have := hl q.1 hq1
  have e : q.1 - p.1 = -(p.1 - q.1) := by abel
  rw [hpar, e, det2_neg_right] at this
  simp only at hdet
  linarith

end Erdos99

end

end TrackHop

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `HopProcess`
-/

section HopProcess

/-!
# The track-following token process (Verification Guide §9.1)

This file builds the routing of the finite token process of §9.1 from the hop along a track
(`TrackHop`) and proves the **distinctness of the track incidences** used by the process.

* `face_left_unique`: an oriented unit edge has at most one face of the contact graph on its
  left.
* `leftStep_face`: the rhombus crossed by a left step is a quadrilateral face lying on the left of
  the edge.
* `initial_of_mem_orientedSides`: the reversal `(b, a)` of an oriented side `(a, b)` of an
  exceptional face is an *initial* edge (no rhombus on its right): the face on that side is the
  exceptional face itself, not a rhombus.
* `not_mem_orientedSides_of_unitHullSide`: no face of the contact graph lies on the outer side of
  a hull side.
* `hopDest X p`: the receiver of a token leaving through the exit edge `p`: the exceptional face
  lying on the left of the far end `hopEnd X p` of its track, if there is one, and a cap otherwise.
* `hopProcess hX emit`: the token process in which every source (unit hull side) hops along its
  track, and every exceptional face `G` emits through the exit edge `emit G`.
  `hopEntry X emit`: its entry edges (the far ends of the tracks, in `ℂ`).
* `hopProcess_incidences`: if every exit edge `emit G` is the reversal of an oriented side of `G`,
  then at every face `F` and in every round, the arriving tokens enter through oriented sides of
  `F`, through **pairwise distinct** edges, each with exactly the direction of its exit edge.
-/

open scoped BigOperators Real
open Filter Topology EstablishedExternalResults

@[expose] public noncomputable section

open Classical

namespace Erdos99

/-! ## Orientation in `ℂ` -/

lemma toC_re' (x : Plane) : (toC x).re = x 0 := by
  simp [toC, Complex.orthonormalBasisOneI, Complex.basisOneI]

lemma toC_im' (x : Plane) : (toC x).im = x 1 := by
  simp [toC, Complex.orthonormalBasisOneI, Complex.basisOneI]

/-- The side of a point relative to a directed edge, in `ℂ` and in the plane. -/
lemma wc_toC_im (a b z : Plane) :
    (wc (toC a) (toC b) (toC z)).im = det2 (b - a) (z - a) / ‖b - a‖ ^ 2 := by
  rw [wc_im_eq, ← map_sub, ← map_sub, Complex.normSq_eq_norm_sq, LinearIsometryEquiv.norm_map]
  unfold ccr det2
  simp [toC_re', toC_im']
  ring

lemma wc_toC_im_pos_iff {a b z : Plane} (hab : a ≠ b) :
    0 < (wc (toC a) (toC b) (toC z)).im ↔ 0 < det2 (b - a) (z - a) := by
  rw [wc_toC_im]
  have : 0 < ‖b - a‖ ^ 2 := by
    have : b - a ≠ 0 := sub_ne_zero.2 hab.symm
    positivity
  exact div_pos_iff_of_pos_right this

lemma wc_toC_im_nonneg_iff {a b z : Plane} (hab : a ≠ b) :
    0 ≤ (wc (toC a) (toC b) (toC z)).im ↔ 0 ≤ det2 (b - a) (z - a) := by
  rw [wc_toC_im]
  have : 0 < ‖b - a‖ ^ 2 := by
    have : b - a ≠ 0 := sub_ne_zero.2 hab.symm
    positivity
  constructor
  · intro h
    have h' := mul_nonneg h this.le
    rwa [div_mul_cancel₀ _ this.ne'] at h'
  · intro h; exact div_nonneg h this.le

/-! ## Faces on the left of an edge -/

section
variable {X : Finset Plane}

/-- **An oriented unit edge has at most one face on its left.** -/
theorem face_left_unique (hX : IsSeparated X) {A B : ℂ} (he : s(A, B) ∈ cUnitEdges X)
    {F₁ F₂ : Set ℂ} (h₁ : F₁ ∈ faces (cVerts X) (cUnitEdges X))
    (h₂ : F₂ ∈ faces (cVerts X) (cUnitEdges X))
    (hb₁ : s(A, B) ∈ bdryEdges (cUnitEdges X) F₁) (hb₂ : s(A, B) ∈ bdryEdges (cUnitEdges X) F₂)
    (hl₁ : ∀ z ∈ F₁, 0 < (wc A B z).im) (hl₂ : ∀ z ∈ F₂, 0 < (wc A B z).im) : F₁ = F₂ := by
  obtain ⟨F, hF⟩ := side_face (cUnitEdges_isPlaneGraph hX) he
  have key : ∀ G ∈ faces (cVerts X) (cUnitEdges X), s(A, B) ∈ bdryEdges (cUnitEdges X) G →
      (∀ z ∈ G, 0 < (wc A B z).im) → G = F := by
    intro G hG hb hl
    obtain ⟨-, z, hz, hzc⟩ := Finset.mem_filter.1 hb
    rw [edgeOpenSeg_mk] at hz
    obtain ⟨ρ, hρ, hF'⟩ := hF z hz
    obtain ⟨y, hyG, hyz⟩ := Metric.mem_closure_iff.1 hzc ρ hρ
    exact hF' G hG y ⟨by rw [Metric.mem_ball, dist_comm]; exact hyz, hyG⟩ (hl y hyG)
  rw [key _ h₁ hb₁ hl₁, key _ h₂ hb₂ hl₂]

variable (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X)
include hX htri

/-- **The rhombus of a left step is a quadrilateral face on the left of the edge.** -/
theorem leftStep_face {p q : Plane × Plane} (h : LeftStep X p q) :
    ∃ F ∈ contactFaces X, faceSize X F = 4 ∧
      s(toC p.1, toC p.2) ∈ bdryEdges (cUnitEdges X) F ∧
      ∀ z ∈ F, 0 < (wc (toC p.1) (toC p.2) z).im := by
  obtain ⟨hR, h1, h2, h3, h4, hpar, hdet⟩ := h
  obtain ⟨ha, hb, hd, hc⟩ := LeftStep.mem ⟨hR, h1, h2, h3, h4, hpar, hdet⟩
  have hcard := (Finset.mem_powersetCard.1 (Finset.mem_filter.1 hR).1).2
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := distinct_of_card_four hcard
  obtain ⟨d1, d2⟩ := rhombus_diagonals_gt_one hX htri hR h1 h2 h3 h4
  have mem : ∀ x ∈ X, toC x ∈ cVerts X := fun x hx => Finset.mem_image_of_mem _ hx
  have inj : ∀ {x y : Plane}, x ≠ y → toC x ≠ toC y := fun hxy h => hxy (toC.injective h)
  obtain ⟨hface, hbdry, hbdd⟩ := unit_rhombus_face (cUnitEdges_isPlaneGraph hX) (cVerts_sep hX)
    (mem _ ha) (mem _ hb) (mem _ hc) (mem _ hd)
    (by rw [dist_toC]; exact h1) (by rw [dist_toC]; exact h2) (by rw [dist_toC]; exact h3)
    (by rw [dist_toC]; exact h4) (by rw [dist_toC]; exact d1.ne') (by rw [dist_toC]; exact d2.ne')
    (inj n2) (inj n5)
  refine ⟨_, ⟨hface, hbdd⟩, ?_, ?_, ?_⟩
  · show (bdryEdges (cUnitEdges X) _).card = 4
    unfold cUnitEdges
    rw [hbdry, card_cycle4 (inj n1) (inj n2) (inj n3) (inj n4) (inj n5) (inj n6)]
  · unfold cUnitEdges; rw [hbdry]; simp
  · intro z hz
    have hab : p.1 ≠ p.2 := n1
    have hS : IsCSide ({toC p.1, toC p.2, toC q.2, toC q.1} : Finset ℂ) (toC p.1) (toC p.2) := by
      refine ⟨by simp, by simp, inj hab, fun c hc' => ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc'
      have e2 : q.2 - p.1 = (q.1 - p.1) + (p.2 - p.1) := by rw [← hpar]; abel
      rcases hc' with rfl | rfl | rfl | rfl
      · rw [wc_toC_im_nonneg_iff hab, sub_self]; unfold det2; simp
      · rw [wc_toC_im_nonneg_iff hab, det2_self']
      · rw [wc_toC_im_nonneg_iff hab, e2, det2_add_right_hop, det2_self', add_zero]
        exact hdet.le
      · rw [wc_toC_im_nonneg_iff hab]; exact hdet.le
    refine side_pos hS ?_
    simpa using hz

/-- **The reversal of an oriented side of an exceptional face is initial**: no rhombus lies on the
side of the exceptional face. -/
theorem initial_of_mem_orientedSides {G : Set ℂ} (hG : G ∈ exceptionalFaces X) {a b : Plane}
    (h : (toC a, toC b) ∈ orientedSides X G) : Initial X (b, a) := by
  rintro ⟨q, hq⟩
  obtain ⟨F, hF, hF4, hbF, hlF⟩ := leftStep_face hX htri hq.rev
  obtain ⟨-, hbG, hlG⟩ := Finset.mem_filter.1 h
  have he : s(toC a, toC b) ∈ cUnitEdges X := (Finset.mem_filter.1 hbG).1
  have := face_left_unique hX he hG.1.1 hF.1 hbG hbF hlG hlF
  have h5 := hG.2
  rw [this, hF4] at h5
  omega

omit htri in
/-- **No face lies on the outer side of a hull side.** -/
theorem not_mem_orientedSides_of_unitHullSide {G : Set ℂ} (hG : G ∈ contactFaces X)
    {p : Plane × Plane} (hp : p ∈ unitHullSides X) :
    (toC p.2, toC p.1) ∉ orientedSides X G := by
  intro h
  obtain ⟨-, -, hlG⟩ := Finset.mem_filter.1 h
  obtain ⟨h1, -⟩ := Finset.mem_filter.1 hp
  obtain ⟨-, -, -, hne, hl⟩ := Finset.mem_filter.1 h1
  obtain ⟨x, hx, hGx⟩ := mem_faces_iff.1 hG.1
  have hxG : x ∈ G := hGx ▸ mem_connectedComponentIn hx
  -- the convex hull lies to the left of the hull side
  have hsub : convexHull ℝ (cVerts X : Set ℂ) ⊆ {z : ℂ | 0 ≤ (wc (toC p.1) (toC p.2) z).im} := by
    refine convexHull_min (fun z hz => ?_) (convex_wc_im_nonneg _ _)
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
    exact (wc_toC_im_nonneg_iff hne).2 (hl y hy)
  have h0 := hsub (boundedFace_subset_hull (cUnitEdges_isPlaneGraph hX) hG.1 hG.2 hxG)
  have h1 := hlG x hxG
  rw [wc_im_swap] at h1
  simp only [Set.mem_setOf_eq] at h0
  linarith

end

/-! ## The process -/

/-- **The receiver of a token leaving through the exit edge `p`**: the exceptional face on the left
of the far end of the track, if there is one, and a cap otherwise. -/
def hopDest (X : Finset Plane) (p : Plane × Plane) : TokenDest :=
  if h : ∃ F ∈ exceptionalFaces X, (toC (hopEnd X p).1, toC (hopEnd X p).2) ∈ orientedSides X F
  then .face h.choose else .cap

/-- **The track-following token process**: every source hops along its track, and every
exceptional face `G` emits through the exit edge `emit G`. -/
def hopProcess {X : Finset Plane} (hX : IsSeparated X) (emit : Set ℂ → Plane × Plane) :
    TokenProcess X where
  fin := exceptionalFaces_finite hX
  start := hopDest X
  out G := hopDest X (emit G)

/-- The entry edges of the track-following process: the far ends of the tracks, in `ℂ`. -/
def hopEntry (X : Finset Plane) (emit : Set ℂ → Plane × Plane) : TokenProcess.Entry X where
  src p := (toC (hopEnd X p).1, toC (hopEnd X p).2)
  emit G := (toC (hopEnd X (emit G)).1, toC (hopEnd X (emit G)).2)

/-- The exit edge of a token: the source itself, or the exit edge of the emitting face. -/
def exitEdge (emit : Set ℂ → Plane × Plane) : (Plane × Plane) ⊕ Set ℂ → Plane × Plane :=
  Sum.elim id emit

lemma hopEntry_edge (X : Finset Plane) (emit : Set ℂ → Plane × Plane)
    (t : (Plane × Plane) ⊕ Set ℂ) :
    (hopEntry X emit).edge t =
      (toC (hopEnd X (exitEdge emit t)).1, toC (hopEnd X (exitEdge emit t)).2) := by
  cases t <;> rfl

lemma hopDest_face {X : Finset Plane} {p : Plane × Plane} {F : Set ℂ} (h : hopDest X p = .face F) :
    (toC (hopEnd X p).1, toC (hopEnd X p).2) ∈ orientedSides X F := by
  unfold hopDest at h
  split_ifs at h with hex
  · cases h; exact hex.choose_spec.2

lemma toLost_hopDest {X : Finset Plane} (hX : IsSeparated X) (p : Plane × Plane) :
    TokenProcess.toLost (exceptionalFaces_finite hX).toFinset (hopDest X p) = 0 := by
  unfold hopDest
  split_ifs with hex
  · simp [TokenProcess.toLost, (Set.Finite.mem_toFinset _).2 hex.choose_spec.1]
  · rfl

/-- **The track-following process loses no token**: every token reaches an exceptional face or a
cap. -/
theorem hopProcess_lostArr {X : Finset Plane} (hX : IsSeparated X) (emit : Set ℂ → Plane × Plane)
    (j : ℕ) : (hopProcess hX emit).lostArr j = 0 := by
  cases j with
  | zero => rfl
  | succ j =>
    show ∑ p ∈ unitHullSides X, TokenProcess.toLost _ (hopDest X p) +
      ∑ G ∈ _, TokenProcess.toLost _ (hopDest X (emit G)) * _ = 0
    simp [toLost_hopDest hX]

/-- **Distinct track incidences** (§9.1).  If every exit edge `emit G` is the reversal of an
oriented side of `G`, then at every face `F` and in every round the arriving tokens of the
track-following process enter through oriented sides of `F`, through pairwise distinct edges, and
each entry edge has exactly the direction of the exit edge of its token. -/
theorem hopProcess_incidences {X : Finset Plane} (hX : IsSeparated X)
    (htri : ¬ HasUnitTriangle X) (emit : Set ℂ → Plane × Plane)
    (hemit : ∀ G ∈ exceptionalFaces X, (toC (emit G).2, toC (emit G).1) ∈ orientedSides X G)
    (j : ℕ) (F : Set ℂ) :
    Set.InjOn (hopEntry X emit).edge ((hopProcess hX emit).arrivals j F) ∧
      ∀ t ∈ (hopProcess hX emit).arrivals j F,
        (hopEntry X emit).edge t ∈ orientedSides X F ∧
        ((hopEntry X emit).edge t).2 - ((hopEntry X emit).edge t).1 =
          toC (exitEdge emit t).2 - toC (exitEdge emit t).1 := by
  set P := hopProcess hX emit
  -- arriving tokens
  have hmem : ∀ t ∈ P.arrivals j F, (∃ p ∈ unitHullSides X, t = .inl p ∧ hopDest X p = .face F) ∨
      (∃ G ∈ exceptionalFaces X, t = .inr G ∧ hopDest X (emit G) = .face F) := by
    intro t ht
    rcases t with p | G
    · left
      simp only [P, TokenProcess.arrivals, Finset.inl_mem_disjSum, Finset.mem_filter] at ht
      exact ⟨p, ht.1, rfl, ht.2⟩
    · right
      simp only [P, TokenProcess.arrivals, Finset.inr_mem_disjSum, Finset.mem_filter] at ht
      exact ⟨G, (Set.Finite.mem_toFinset _).1 ht.1, rfl, ht.2.1⟩
  -- exit edges are initial edges of `X × X`
  have hexit : ∀ t ∈ P.arrivals j F, exitEdge emit t ∈ X ×ˢ X ∧ Initial X (exitEdge emit t) := by
    intro t ht
    rcases hmem t ht with ⟨p, hp, rfl, -⟩ | ⟨G, hG, rfl, -⟩
    · obtain ⟨h1, -⟩ := Finset.mem_filter.1 hp
      exact ⟨(Finset.mem_filter.1 h1).1, initial_of_mem_unitHullSides hp⟩
    · have h := hemit G hG
      obtain ⟨hv, -⟩ := Finset.mem_filter.1 h
      obtain ⟨h2, h1⟩ := Finset.mem_product.1 hv
      refine ⟨Finset.mem_product.2 ⟨?_, ?_⟩, initial_of_mem_orientedSides hX htri hG h⟩
      · simpa [mem_cVerts] using h1
      · simpa [mem_cVerts] using h2
  refine ⟨fun t ht t' ht' heq => ?_, fun t ht => ⟨?_, ?_⟩⟩
  · rw [hopEntry_edge, hopEntry_edge] at heq
    simp only [Prod.mk.injEq] at heq
    have hend : hopEnd X (exitEdge emit t) = hopEnd X (exitEdge emit t') :=
      Prod.ext (toC.injective heq.1) (toC.injective heq.2)
    have hx := hopEnd_injOn hX htri (hexit t ht).1 (hexit t' ht').1 (hexit t ht).2
      (hexit t' ht').2 hend
    rcases hmem t ht with ⟨p, hp, rfl, -⟩ | ⟨G, hG, rfl, -⟩ <;>
      rcases hmem t' ht' with ⟨p', hp', rfl, -⟩ | ⟨G', hG', rfl, -⟩
    · simp only [exitEdge, Sum.elim_inl, id] at hx; rw [hx]
    · exfalso
      simp only [exitEdge, Sum.elim_inl, Sum.elim_inr, id] at hx
      have := hemit G' hG'
      rw [← hx] at this
      exact not_mem_orientedSides_of_unitHullSide hX hG'.1 hp this
    · exfalso
      simp only [exitEdge, Sum.elim_inl, Sum.elim_inr, id] at hx
      have := hemit G hG
      rw [hx] at this
      exact not_mem_orientedSides_of_unitHullSide hX hG.1 hp' this
    · simp only [exitEdge, Sum.elim_inr] at hx
      have h1 := hemit G hG
      have h2 := hemit G' hG'
      rw [hx] at h1
      obtain ⟨-, hb1, hl1⟩ := Finset.mem_filter.1 h1
      obtain ⟨-, hb2, hl2⟩ := Finset.mem_filter.1 h2
      have he := (Finset.mem_filter.1 hb1).1
      rw [face_left_unique hX he hG.1.1 hG'.1.1 hb1 hb2 hl1 hl2]
  · rw [hopEntry_edge]
    rcases hmem t ht with ⟨p, -, rfl, hd⟩ | ⟨G, -, rfl, hd⟩
    · exact hopDest_face hd
    · exact hopDest_face hd
  · rw [hopEntry_edge]
    simp only
    rw [← map_sub, ← map_sub, hopEnd_sub]

end Erdos99

end

end HopProcess

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `HopDirections`
-/

section HopDirections

/-!
# Directions of arriving tokens (Verification Guide §9.1–§9.2)

The face condition of §9.1 asks that the tokens arriving at a small receiver enter through nearly
parallel edges.  This file reduces it to the two invariants the Guide maintains for each live
token: **its direction is near the tangent of its source**, and **its source is near the
receiver**.  The link between the two is the near-circularity of the hull:

* `side_normal_near`: if `X` is round (`RoundData`), each counterclockwise hull side `p` starts
  within `D √(3δ)` of the point `O + (D/2) ν_p` of the circle, where `ν_p` is its outward normal.
* `sideDir_sub_le` (**tangent regularity**): hence two hull sides starting at distance `s` have
  unit directions at distance at most `2 s / D + 4 √(3δ)`.
* `eventually_roundData`: eventually every optimal configuration is round with `δ` as small as
  we like.
* `UnitPolygon.dist_le`: two vertices of a closed unit `k`-gon are at distance at most `k`.
* `marked_of_labels`: tokens whose exit directions are near the tangents of hull sides starting
  close together enter through edges with projection at least `19/20` on one unit vector.
-/

open scoped BigOperators Real
open Filter Topology EstablishedExternalResults

@[expose] public noncomputable section

open Classical

namespace Erdos99

lemma rot_sub_hop (x y : Plane) : rot (x - y) = rot x - rot y := by
  ext i; fin_cases i <;> simp [rot]; ring

/-- A counterclockwise hull side starts near the circle point in the direction of its outward
normal. -/
lemma side_normal_near {X : Finset Plane} {O : Plane} {D η δ : ℝ} (hR : RoundData X O D η δ)
    {p : Plane × Plane} (hp : IsCcwHullSide X p.1 p.2) :
    ‖p.1 - O - (D / 2) • (-rot (sideDir p))‖ ≤ D * √(3 * δ) := by
  set u := sideDir p with hu
  have hu1 : ‖u‖ = 1 := norm_sideDir hp.2.2.1
  set ν := -rot u with hν
  have hν1 : ‖ν‖ = 1 := by rw [hν, norm_neg, norm_rot, hu1]
  have hxX : p.1 ∈ X := mem_of_mem_hullVertices hp.1
  have hsupp : ∀ y ∈ X, inner ℝ (y - p.1) ν ≤ 0 := fun y hy => inner_sideNormal_nonpos hp hy
  obtain ⟨y, hyX, hy⟩ := hR.support ν hν1
  have hxν : D / 2 - δ * D ≤ inner ℝ (p.1 - O) ν := by
    have e : p.1 - O = (y - O) - (y - p.1) := by abel
    rw [e, inner_sub_left]
    linarith [hsupp y hyX]
  have hxO : ‖p.1 - O‖ ≤ D / 2 + η * D := by rw [← dist_eq_norm]; exact hR.ball _ hxX
  have hD := hR.D_pos
  set e := p.1 - O - (D / 2) • ν with he
  have he2 : ‖e‖ ^ 2 ≤ 3 * δ * D ^ 2 := by
    have : ‖e‖ ^ 2 = ‖p.1 - O‖ ^ 2 - D * inner ℝ (p.1 - O) ν + D ^ 2 / 4 := by
      rw [he, norm_sub_sq_real, norm_smul, real_inner_smul_right, hν1, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0 : ℝ) < D / 2)]
      ring
    rw [this]
    have h1 : ‖p.1 - O‖ ^ 2 ≤ (D / 2 + η * D) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hxO 2
    have hη := hR.η_le
    have hη0 := hR.η_nonneg
    have hδ := hR.δ_le
    have k1 : D * (D / 2 - δ * D) ≤ D * inner ℝ (p.1 - O) ν :=
      mul_le_mul_of_nonneg_left hxν hD.le
    have k2 : η + η ^ 2 ≤ 2 * δ := by nlinarith
    have k3 : (D / 2 + η * D) ^ 2 - D * (D / 2 - δ * D) + D ^ 2 / 4 =
        D ^ 2 * (η + η ^ 2 + δ) := by ring
    have k4 : D ^ 2 * (η + η ^ 2 + δ) ≤ D ^ 2 * (3 * δ) :=
      mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg D)
    nlinarith
  have h3 : 0 ≤ 3 * δ := by have := hR.η_nonneg; have := hR.η_le; linarith
  rw [← Real.sqrt_sq (norm_nonneg e), show D * √(3 * δ) = √(3 * δ * D ^ 2) by
    rw [Real.sqrt_mul h3, Real.sqrt_sq hD.le, mul_comm]]
  exact Real.sqrt_le_sqrt he2

/-- **Tangent regularity of a round hull**: hull sides starting at distance `s` have unit
directions at distance at most `2 s / D + 4 √(3δ)`. -/
theorem sideDir_sub_le {X : Finset Plane} {O : Plane} {D η δ : ℝ} (hR : RoundData X O D η δ)
    {p q : Plane × Plane} (hp : IsCcwHullSide X p.1 p.2) (hq : IsCcwHullSide X q.1 q.2) :
    ‖sideDir p - sideDir q‖ ≤ 2 * dist p.1 q.1 / D + 4 * √(3 * δ) := by
  have hD := hR.D_pos
  have h1 := side_normal_near hR hp
  have h2 := side_normal_near hR hq
  have e : (D / 2) • (-rot (sideDir p)) - (D / 2) • (-rot (sideDir q)) =
      -rot ((D / 2) • (sideDir p - sideDir q)) := by
    ext i; fin_cases i <;> simp [rot] <;> ring
  have hn : ‖(D / 2) • (sideDir p - sideDir q)‖ =
      ‖(D / 2) • (-rot (sideDir p)) - (D / 2) • (-rot (sideDir q))‖ := by
    rw [e, norm_neg, norm_rot]
  have htri : ‖(D / 2) • (-rot (sideDir p)) - (D / 2) • (-rot (sideDir q))‖ ≤
      ‖p.1 - O - (D / 2) • (-rot (sideDir p))‖ + dist p.1 q.1 +
        ‖q.1 - O - (D / 2) • (-rot (sideDir q))‖ := by
    rw [dist_eq_norm]
    have : (D / 2) • (-rot (sideDir p)) - (D / 2) • (-rot (sideDir q)) =
        -(p.1 - O - (D / 2) • (-rot (sideDir p))) + (p.1 - q.1) +
          (q.1 - O - (D / 2) • (-rot (sideDir q))) := by abel
    rw [this]
    refine (norm_add_le _ _).trans ?_
    have := norm_add_le (-(p.1 - O - (D / 2) • (-rot (sideDir p)))) (p.1 - q.1)
    rw [norm_neg] at this
    linarith
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < D / 2)] at hn
  have key : D / 2 * ‖sideDir p - sideDir q‖ ≤ dist p.1 q.1 + 2 * (D * √(3 * δ)) := by
    linarith
  rw [div_add' _ _ _ hD.ne', le_div_iff₀ hD]
  nlinarith

/-- Unit vectors at distance at most `ε` have inner product at least `1 - ε² / 2`. -/
lemma inner_ge_of_norm_sub_le {a b : Plane} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) {ε : ℝ}
    (h : ‖a - b‖ ≤ ε) : 1 - ε ^ 2 / 2 ≤ inner ℝ a b := by
  have e := norm_sub_sq_real a b
  rw [ha, hb] at e
  have h0 := norm_nonneg (a - b)
  have : ‖a - b‖ ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ h0 h 2
  linarith

/-- **Eventually optimal configurations are round, with a rate**: they lie in the disc of radius
`D/2 + η D` about some centre and reach `D/2 - δ D` in every direction, with `δ = 100 D^{-2/9}`. -/
theorem eventually_roundData_rate :
    ∀ᶠ n in atTop, ∀ X, IsOptimal n X →
      ∃ O η, RoundData X O (diam X) η (100 * diam X ^ (-(2 / 9 : ℝ))) := by
  filter_upwards [eventually_ge_atTop 2, round_center_rate,
    tendsto_minDiam.eventually_ge_atTop (20 ^ 9)] with n hn hrc hD X hX
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
  rw [h3] at hO
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
    { ball := hO,
      support := fun ν hν => exists_support_ge_sharp hX.1.2 hν hD0 hδ0 hδ1 hηδ' hηD hlat hO,
      η_le := hηδ,
      η_nonneg := hη0,
      δ_le := by linarith,
      D_pos := hD0 }
  refine ⟨O, η, ?_⟩
  have e : 100 * D ^ (-(2 / 9 : ℝ)) = δ := by
    rw [hδ, Real.rpow_neg hD0.le, hs, ← Real.rpow_natCast, ← Real.rpow_mul hD0.le]
    norm_num
  rw [e]
  exact hR

/-- **Eventually optimal configurations are round**, with an arbitrarily small parameter `δ`. -/
theorem eventually_roundData (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ X, IsOptimal n X → ∃ O η δ, RoundData X O (diam X) η δ ∧ δ ≤ ε := by
  filter_upwards [eventually_roundData_rate,
    tendsto_minDiam.eventually_ge_atTop (max 1 ((100 / ε) ^ (9 / 2 : ℝ)))] with n hR hD' X hX
  obtain ⟨O, η, hR⟩ := hR X hX
  refine ⟨O, η, _, hR, ?_⟩
  have hD1 : (1 : ℝ) ≤ minDiam n := (le_max_left _ _).trans hD'
  have hDε : (100 / ε) ^ (9 / 2 : ℝ) ≤ minDiam n := (le_max_right _ _).trans hD'
  rw [← hX.diam_eq] at hD1 hDε
  set D := diam X
  have hD0 : 0 < D := by linarith
  have h29 : 100 / ε ≤ D ^ (2 / 9 : ℝ) := by
    have := Real.rpow_le_rpow (by positivity) hDε (show (0 : ℝ) ≤ 2 / 9 by norm_num)
    rwa [← Real.rpow_mul (by positivity), show (9 / 2 : ℝ) * (2 / 9) = 1 by norm_num,
      Real.rpow_one] at this
  rw [Real.rpow_neg hD0.le, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
  rw [div_le_iff₀ hε] at h29
  linarith

open Fin.NatCast in
/-- Two vertices of a closed unit `k`-gon are at distance at most `k`. -/
lemma UnitPolygon.dist_le {k : ℕ} [NeZero k] (Q : UnitPolygon k) (i j : Fin k) :
    dist (Q.P i) (Q.P j) ≤ k := by
  have step : ∀ m : ℕ, dist (Q.P i) (Q.P (i + (m : Fin k))) ≤ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have h1 : dist (Q.P (i + (m : Fin k))) (Q.P (i + ((m + 1 : ℕ) : Fin k))) = 1 := by
        rw [Nat.cast_succ, ← add_assoc, dist_comm, dist_eq_norm]
        exact Q.unit_edge _
      calc dist (Q.P i) (Q.P (i + ((m + 1 : ℕ) : Fin k)))
          ≤ dist (Q.P i) (Q.P (i + (m : Fin k))) +
            dist (Q.P (i + (m : Fin k))) (Q.P (i + ((m + 1 : ℕ) : Fin k))) := dist_triangle _ _ _
        _ ≤ m + 1 := by rw [h1]; linarith
        _ = ((m + 1 : ℕ) : ℝ) := by push_cast; ring
  have h := step (j - i : Fin k).val
  rw [Fin.cast_val_eq_self, add_sub_cancel] at h
  exact h.trans (by exact_mod_cast (j - i).isLt.le)

/-- **Entry vertices of an exceptional face are close**: eventually, the starting points of two
oriented sides of an exceptional face are at distance at most its number of sides. -/
theorem exceptionalFace_orientedSides_dist_le :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ∀ F ∈ exceptionalFaces X,
      ∀ ab ∈ orientedSides X F, ∀ ab' ∈ orientedSides X F, dist ab.1 ab'.1 ≤ faceSize X F := by
  filter_upwards [exceptionalFace_unitPolygon] with n hpoly hfm X hX F hF ab hab ab' hab'
  obtain ⟨hk, Q, hQ⟩ := hpoly hfm X hX F hF
  obtain ⟨i, hi, -⟩ := hQ ab hab
  obtain ⟨j, hj, -⟩ := hQ ab' hab'
  rw [← hi, ← hj, dist_toC]
  exact Q.dist_le i j

/-- **Marked directions from labels.**  Let `X` be round.  If every token of a finite set `S`
leaves through a unit exit edge whose direction is within `a` of the direction of a hull side
(its *label*), and the labels start pairwise within distance `b`, with
`a + 2 b / D + 4 √(3δ) ≤ 3/10`, then the exit edges all have projection at least `19/20` on one
unit vector. -/
theorem marked_of_labels {X : Finset Plane} {O : Plane} {D η δ : ℝ} (hR : RoundData X O D η δ)
    {ι : Type*} (S : Finset ι) (exit lab : ι → Plane × Plane)
    (hunit : ∀ t ∈ S, ‖(exit t).2 - (exit t).1‖ = 1)
    (hlab : ∀ t ∈ S, IsCcwHullSide X (lab t).1 (lab t).2) {a b : ℝ}
    (hdir : ∀ t ∈ S, ‖sideDir (exit t) - sideDir (lab t)‖ ≤ a)
    (hpos : ∀ t ∈ S, ∀ t' ∈ S, dist (lab t).1 (lab t').1 ≤ b)
    (hsmall : a + 2 * b / D + 4 * √(3 * δ) ≤ 3 / 10) :
    ∃ e : ℂ, ‖e‖ = 1 ∧ ∀ t ∈ S, 19 / 20 ≤ inner ℝ (toC (exit t).2 - toC (exit t).1) e := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨t₀, ht₀⟩
  · exact ⟨1, by simp, fun t ht => absurd ht (Finset.notMem_empty t)⟩
  have he : ‖toC (sideDir (lab t₀))‖ = 1 := by
    rw [LinearIsometryEquiv.norm_map]; exact norm_sideDir (hlab t₀ ht₀).2.2.1
  refine ⟨toC (sideDir (lab t₀)), he, fun t ht => ?_⟩
  have hD := hR.D_pos
  rw [← map_sub, LinearIsometryEquiv.inner_map_map]
  have hexit : (exit t).2 - (exit t).1 = sideDir (exit t) := by
    rw [sideDir, hunit t ht, inv_one, one_smul]
  rw [hexit]
  have hne : (exit t).1 ≠ (exit t).2 := by
    intro h; have := hunit t ht; rw [h, sub_self, norm_zero] at this; norm_num at this
  have h1 : ‖sideDir (exit t) - sideDir (lab t₀)‖ ≤ 3 / 10 := by
    calc ‖sideDir (exit t) - sideDir (lab t₀)‖
        ≤ ‖sideDir (exit t) - sideDir (lab t)‖ + ‖sideDir (lab t) - sideDir (lab t₀)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ a + (2 * dist (lab t).1 (lab t₀).1 / D + 4 * √(3 * δ)) :=
          add_le_add (hdir t ht) (sideDir_sub_le hR (hlab t ht) (hlab t₀ ht₀))
      _ ≤ a + (2 * b / D + 4 * √(3 * δ)) := by
          gcongr; exact hpos t ht t₀ ht₀
      _ ≤ 3 / 10 := by linarith
  have := inner_ge_of_norm_sub_le (norm_sideDir hne) (norm_sideDir (hlab t₀ ht₀).2.2.1) h1
  linarith

end Erdos99

end

end HopDirections

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `LargeFaceLabels`
-/

section LargeFaceLabels

/-!
# Large receivers: two short arcs from locality (Verification Guide §9.3)

§9.3 of the Verification Guide: every arriving source is within `O_K(Λ_K)` of its receiver, so
by the three-point area bound the source positions at one receiver lie in two short arcs.  This
file proves this step for the actual exceptional faces.

* `abs_dist_center_sub_le`: on a round hull the hull vertices are within `D √(3δ)` of the circle
  of radius `D/2`.
* `eventually_const_mul_rpow_le`: `c D^α ≤ D^β` eventually, for `α < β`.
* `large_face_two_balls`: eventually, if hull sides (*labels*) start within `D^{1 - e_K} + 1` of
  the closure of an exceptional face, then their starting points lie in two balls of radius
  `D^{1 - e_K/4}`.
-/

open scoped BigOperators Real
open Filter Topology EstablishedExternalResults

@[expose] public noncomputable section

open Classical

namespace Erdos99

open Propagation

/-- On a round hull, the starting point of a hull side is within `D √(3δ)` of the circle of
radius `D/2` about the centre. -/
lemma abs_dist_center_sub_le {X : Finset Plane} {O : Plane} {D η δ : ℝ}
    (hR : RoundData X O D η δ) {p : Plane × Plane} (hp : IsCcwHullSide X p.1 p.2) :
    |dist p.1 O - D / 2| ≤ D * √(3 * δ) := by
  have h := side_normal_near hR hp
  have hD := hR.D_pos
  have hν : ‖(D / 2) • (-rot (sideDir p))‖ = D / 2 := by
    rw [norm_smul, norm_neg, norm_rot, norm_sideDir hp.2.2.1, Real.norm_eq_abs,
      abs_of_pos (by positivity), mul_one]
  rw [dist_eq_norm, ← hν]
  exact (abs_norm_sub_norm_le _ _).trans h

/-- `c D^α ≤ D^β` eventually, for `α < β`. -/
lemma eventually_const_mul_rpow_le (c : ℝ) {α β : ℝ} (h : α < β) :
    ∀ᶠ D : ℝ in atTop, c * D ^ α ≤ D ^ β := by
  have ht := (tendsto_rpow_neg_atTop (y := β - α) (by linarith)).const_mul c
  rw [mul_zero] at ht
  filter_upwards [ht.eventually (ge_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    eventually_gt_atTop 0] with D hD hD0
  have e : D ^ α = D ^ (-(β - α)) * D ^ β := by
    rw [← Real.rpow_add hD0]; ring_nf
  rw [e, ← mul_assoc]
  have := Real.rpow_pos_of_pos hD0 β
  nlinarith

/-- The starting point of an oriented side of a face is within distance one of the closure of the
face. -/
lemma exists_closure_near_of_mem_orientedSides {X : Finset Plane} {F : Set ℂ} {a b : Plane}
    (h : (toC a, toC b) ∈ orientedSides X F) : ∃ z : Plane, toC z ∈ closure F ∧ dist a z ≤ 1 := by
  obtain ⟨-, hb, -⟩ := Finset.mem_filter.1 h
  obtain ⟨hu, w, hw, hwc⟩ := Finset.mem_filter.1 hb
  have hd := (mem_unitPairs.1 hu).2.2
  rw [edgeOpenSeg_mk, openSegment_eq_image_lineMap] at hw
  obtain ⟨θ, hθ, rfl⟩ := hw
  refine ⟨toC.symm (AffineMap.lineMap (toC a) (toC b) θ), by simpa using hwc, ?_⟩
  rw [← dist_toC, LinearIsometryEquiv.apply_symm_apply, dist_comm, dist_lineMap_left, hd,
    mul_one, Real.norm_eq_abs, abs_of_pos hθ.1]
  exact hθ.2.le

/-- The arithmetic of the two-arc covering at the scales `a = D^{1 - e}`, `b = D^{8/9}`,
`s = D^{1 - e/4}`. -/
lemma two_ball_arith {CF D a b s : ℝ} (hD0 : 0 < D) (ha0 : 0 < a) (hb0 : 0 < b) (hs0 : 0 < s)
    (d1 : 144 * b ≤ D) (d2 : 8 * a ≤ D) (d8' : 8 ≤ D) (d4 : 24 * a ≤ s) (d5 : 216 * b ≤ s)
    (d6 : 24 ≤ s) (k7 : 40 * (|CF| * D ^ 2) ≤ s ^ 3) (k8 : 5 * 3456 * (b * D ^ 2) ≤ s ^ 3)
    (k9 : 5 * 192 * (a * D ^ 2) ≤ s ^ 3) (k10 : 5 * 192 * D ^ 2 ≤ s ^ 3) :
    18 * b + (a + 1) < D / 2 ∧ 2 * (18 * b + (a + 1)) ≤ s - 2 * (a + 1) ∧
      CF * D < (s - 2 * (a + 1) - 2 * (18 * b + (a + 1))) ^ 3 / (2 * (D / 2)) -
        24 * (18 * b + (a + 1)) * (D / 2 + (18 * b + (a + 1))) := by
  set m := 18 * b + (a + 1) with hm
  have hm1 : m < D / 2 := by linarith
  refine ⟨hm1, by linarith, ?_⟩
  have hX3 : s / 2 ≤ s - 2 * (a + 1) - 2 * m := by linarith
  have hcube : (s / 2) ^ 3 ≤ (s - 2 * (a + 1) - 2 * m) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hX3 3
  have e2 : 2 * (D / 2) = D := by ring
  rw [e2]
  have hm0 : 0 ≤ m := by positivity
  have hm' : 24 * m * (D / 2 + m) * D ≤ 24 * m * D * D := by
    have : D / 2 + m ≤ D := by linarith
    have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 24 * m)
    nlinarith
  have h2 : 24 * m * D * D = 432 * (b * D ^ 2) + 24 * (a * D ^ 2) + 24 * D ^ 2 := by
    rw [hm]; ring
  have hCF' : CF * D * D ≤ |CF| * D ^ 2 := by
    have := le_abs_self CF
    nlinarith [sq_nonneg D]
  generalize |CF| * D ^ 2 = A at k7 hCF'
  generalize b * D ^ 2 = B at k8 h2
  generalize a * D ^ 2 = C at k9 h2
  generalize D ^ 2 = E at k10 h2
  have hs3 : 0 < s ^ 3 := by positivity
  have hk : CF * D + 24 * m * (D / 2 + m) < (s / 2) ^ 3 / D := by
    rw [lt_div_iff₀ hD0]
    have e3 : (CF * D + 24 * m * (D / 2 + m)) * D = CF * D * D + 24 * m * (D / 2 + m) * D := by
      ring
    rw [e3, show (s / 2) ^ 3 = s ^ 3 / 8 by ring]
    linarith
  have : (s / 2) ^ 3 / D ≤ (s - 2 * (a + 1) - 2 * m) ^ 3 / D :=
    div_le_div_of_nonneg_right hcube hD0.le
  linarith

/-- **Two short arcs at a large receiver** (§9.3).  Eventually, at every exceptional face `F`,
hull sides (labels) starting within `D^{1 - e_K} + 1` of the closure of `F` start in two balls of
radius `D^{1 - e_K/4}`. -/
theorem large_face_two_balls (K : ℕ) :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ F ∈ exceptionalFaces X, ∀ (S : Finset ((Plane × Plane) ⊕ Set ℂ))
        (lab : (Plane × Plane) ⊕ Set ℂ → Plane × Plane),
        (∀ t ∈ S, lab t ∈ unitHullSides X) →
        (∀ t ∈ S, ∃ z : Plane, toC z ∈ closure F ∧
          dist (lab t).1 z ≤ diam X ^ (1 - scaleExp K) + 1) →
        ∃ c₀ c₁ : Plane, ∀ t ∈ S, dist (lab t).1 c₀ ≤ diam X ^ (1 - scaleExp K / 4) ∨
          dist (lab t).1 c₁ ≤ diam X ^ (1 - scaleExp K / 4) := by
  obtain ⟨CF, hCF⟩ := exceptionalFace_two_balls
  set e := scaleExp K with he
  have he0 : 0 < e := scaleExp_pos K
  have he1 : e ≤ 1 / 20 := scaleExp_le K
  have c1 := eventually_const_mul_rpow_le 144 (show (8 / 9 : ℝ) < 1 by norm_num)
  have c2 := eventually_const_mul_rpow_le 8 (show 1 - e < 1 by linarith)
  have c4 := eventually_const_mul_rpow_le 24 (show 1 - e < 1 - e / 4 by linarith)
  have c5 := eventually_const_mul_rpow_le 216 (show (8 / 9 : ℝ) < 1 - e / 4 by linarith)
  have c6 := eventually_const_mul_rpow_le 24 (show (0 : ℝ) < 1 - e / 4 by linarith)
  have c7 := eventually_const_mul_rpow_le (40 * |CF|) (show (2 : ℝ) < 3 - 3 * e / 4 by linarith)
  have c8 := eventually_const_mul_rpow_le (5 * 3456) (show (26 / 9 : ℝ) < 3 - 3 * e / 4 by
    linarith)
  have c9 := eventually_const_mul_rpow_le (5 * 192) (show 3 - e < 3 - 3 * e / 4 by linarith)
  have c10 := eventually_const_mul_rpow_le (5 * 192) (show (2 : ℝ) < 3 - 3 * e / 4 by linarith)
  filter_upwards [hCF, eventually_roundData_rate, tendsto_minDiam.eventually c1,
    tendsto_minDiam.eventually c2, tendsto_minDiam.eventually c4, tendsto_minDiam.eventually c5,
    tendsto_minDiam.eventually c6, tendsto_minDiam.eventually c7, tendsto_minDiam.eventually c8,
    tendsto_minDiam.eventually c9, tendsto_minDiam.eventually c10,
    tendsto_minDiam.eventually_ge_atTop 8]
    with n hCFn hround d1 d2 d4 d5 d6 d7 d8 d9 d10 d8' hfm X hX htri F hF S lab hlab hnear
  rw [← hX.diam_eq] at d1 d2 d4 d5 d6 d7 d8 d9 d10 d8'
  obtain ⟨O, η, hR⟩ := hround X hX
  set D := diam X with hDdef
  have hD0 : 0 < D := by linarith
  set a := D ^ (1 - e) with ha
  set b := D ^ (8 / 9 : ℝ) with hb
  set s := D ^ (1 - e / 4) with hs
  have ha0 : 0 < a := Real.rpow_pos_of_pos hD0 _
  have hb0 : 0 < b := Real.rpow_pos_of_pos hD0 _
  have hs0 : 0 < s := Real.rpow_pos_of_pos hD0 _
  rw [Real.rpow_zero, mul_one] at d6
  rw [Real.rpow_one] at d1 d2
  -- the hull vertices are within `18 D^{8/9}` of the circle
  have hε : D * √(3 * (100 * D ^ (-(2 / 9 : ℝ)))) ≤ 18 * b := by
    have h1 : √(3 * (100 * D ^ (-(2 / 9 : ℝ)))) ≤ 18 * D ^ (-(1 / 9 : ℝ)) := by
      have hsq : (18 * D ^ (-(1 / 9 : ℝ))) ^ 2 = 324 * D ^ (-(2 / 9 : ℝ)) := by
        rw [mul_pow, ← Real.rpow_natCast (D ^ _) 2, ← Real.rpow_mul hD0.le]; norm_num
      calc √(3 * (100 * D ^ (-(2 / 9 : ℝ)))) ≤ √((18 * D ^ (-(1 / 9 : ℝ))) ^ 2) := by
            apply Real.sqrt_le_sqrt
            rw [hsq]
            have := Real.rpow_pos_of_pos hD0 (-(2 / 9 : ℝ))
            nlinarith
        _ = 18 * D ^ (-(1 / 9 : ℝ)) := Real.sqrt_sq (by positivity)
    have h2 : D * D ^ (-(1 / 9 : ℝ)) = b := by
      rw [hb, ← Real.rpow_one_add' hD0.le (by norm_num)]; norm_num
    calc D * √(3 * (100 * D ^ (-(2 / 9 : ℝ)))) ≤ D * (18 * D ^ (-(1 / 9 : ℝ))) :=
          mul_le_mul_of_nonneg_left h1 hD0.le
      _ = 18 * b := by rw [← h2]; ring
  -- the products of powers
  have p8 : b * D ^ 2 = D ^ (26 / 9 : ℝ) := by
    rw [hb, ← Real.rpow_natCast D 2, ← Real.rpow_add hD0]; norm_num
  have p9 : a * D ^ 2 = D ^ (3 - e) := by
    rw [ha, ← Real.rpow_natCast D 2, ← Real.rpow_add hD0]; ring_nf
  have p2 : D ^ 2 = D ^ (2 : ℝ) := by rw [← Real.rpow_natCast]; norm_num
  have ps : s ^ 3 = D ^ (3 - 3 * e / 4) := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hD0.le]; ring_nf
  -- the set of starting points
  set P : Set Plane := (S.image (fun t => (lab t).1) : Set Plane)
  rcases S.eq_empty_or_nonempty with rfl | ⟨t₀, ht₀⟩
  · exact ⟨0, 0, fun t ht => absurd ht (Finset.notMem_empty t)⟩
  have k7 : 40 * (|CF| * D ^ 2) ≤ s ^ 3 := by rw [← mul_assoc, p2, ps]; exact d7
  have k8 : 5 * 3456 * (b * D ^ 2) ≤ s ^ 3 := by rw [p8, ps]; exact d8
  have k9 : 5 * 192 * (a * D ^ 2) ≤ s ^ 3 := by rw [p9, ps]; exact d9
  have k10 : 5 * 192 * D ^ 2 ≤ s ^ 3 := by rw [p2, ps]; exact d10
  obtain ⟨hm1, hm2, hbig⟩ := two_ball_arith hD0 ha0 hb0 hs0 d1 d2 d8' d4 d5 d6 k7 k8 k9 k10
  have hPprop : ∀ p ∈ P, |dist p O - D / 2| ≤ 18 * b ∧
      ∃ z, toC z ∈ closure F ∧ dist p z ≤ a + 1 := by
    intro p hp
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hp)
    have hcc : IsCcwHullSide X (lab t).1 (lab t).2 :=
      mem_ccwHullSides.1 (Finset.mem_filter.1 (hlab t ht)).1
    exact ⟨(abs_dist_center_sub_le hR hcc).trans hε, hnear t ht⟩
  have hp₀ : (lab t₀).1 ∈ P := Finset.mem_coe.2 (Finset.mem_image.2 ⟨t₀, ht₀, rfl⟩)
  obtain ⟨p₁, -, hcov⟩ := hCFn hfm X hX htri F hF O (D / 2) (18 * b) (a + 1) s (by positivity)
    (by positivity) (by positivity) hm1 hm2 hbig P hPprop _ hp₀
  refine ⟨(lab t₀).1, p₁, fun t ht => ?_⟩
  have hpt : (lab t).1 ∈ P := Finset.mem_coe.2 (Finset.mem_image.2 ⟨t, ht, rfl⟩)
  rcases hcov hpt with h | h
  · exact Or.inl (Metric.mem_ball.1 h).le
  · exact Or.inr (Metric.mem_ball.1 h).le

end Erdos99

end

end LargeFaceLabels

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `EmissionGeometry`
-/

section EmissionGeometry

/-!
# Emission geometry at pentagons and heptagons (Verification Guide §8.2, used in §9.1)

When `r` edges of a closed unit polygon with `2 r + 1` edges (a pentagon, `r = 2`, or a heptagon,
`r = 3`) are within `δ` of one unit vector `e`, some other edge is *almost opposite*: within
`O(√δ)` of `-e`.  This is what lets a pentagon (on its second arrival) or a heptagon (on its third
arrival) re-emit a token along the positive tangent.

* `UnitPolygon.inner_ge_of_adj`: an edge next to an edge within `δ` of `e` has projection at least
  `-1/2 - δ` on `e` (separation of the vertices two steps apart).
* `UnitPolygon.exists_opposite_edge`: the counting argument, given two distinct unmarked edges
  adjacent to marked ones.
* `adj_pair_five`, `adj_pair_seven`: in a `5`-cycle with `2` marked edges (a `7`-cycle with `3`),
  two distinct unmarked edges are adjacent to marked ones.
* `UnitPolygon.pentagon_opposite`, `UnitPolygon.heptagon_opposite`: some edge `u` has
  `‖u + e‖² ≤ 8 δ`.

No convexity is used: unit edges and the separation of the vertices suffice.
-/

open scoped BigOperators Real
open Filter EstablishedExternalResults

@[expose] public noncomputable section

open Classical

namespace Erdos99

open Fin.NatCast Fin.CommRing LocalCapacity

namespace UnitPolygon

variable {k : ℕ} [NeZero k] (Q : UnitPolygon k)

/-- An edge adjacent to an edge within `δ` of `e` has projection at least `-1/2 - δ` on `e`. -/
lemma inner_ge_of_adj (hk : 3 ≤ k) {e : Plane} {δ : ℝ} {a b : Fin k}
    (hab : b = a + 1 ∨ a = b + 1) (hb : ‖Q.edge b - e‖ ≤ δ) :
    -1 / 2 - δ ≤ inner ℝ (Q.edge a) e := by
  have hsep : -1 / 2 ≤ inner ℝ (Q.edge a) (Q.edge b) := by
    rcases hab with rfl | rfl
    · exact inner_ge_of_sep (Q.norm_edge a) (Q.norm_edge _) (Q.two_step_ge_one hk a)
    · have h := Q.two_step_ge_one hk b
      rw [add_comm] at h
      exact inner_ge_of_sep (Q.norm_edge _) (Q.norm_edge b) h
  have hc := abs_le.1 (inner_close (w := Q.edge a) hb)
  rw [Q.norm_edge, one_mul] at hc
  linarith [hc.1]

/-- **The almost-opposite edge, counting form.**  Let `M` be a set of `r ≥ 2` edges of a closed
unit polygon with `2 r + 1` edges, all within `δ` of the unit vector `e`, and let `a ≠ b` be two
edges outside `M`, each adjacent to an edge of `M`.  Then some edge `u` has `‖u + e‖² ≤ 8 δ`. -/
theorem exists_opposite_edge (hk : 3 ≤ k) {e : Plane} (he : ‖e‖ = 1) {δ : ℝ} (hδ0 : 0 ≤ δ)
    {M : Finset (Fin k)} (hMk : 2 * M.card + 1 = k) (hM2 : 2 ≤ M.card)
    (hM : ∀ i ∈ M, ‖Q.edge i - e‖ ≤ δ) {a b : Fin k} (ha : a ∉ M) (hb : b ∉ M) (hab : a ≠ b)
    (hadja : a + 1 ∈ M ∨ a - 1 ∈ M) (hadjb : b + 1 ∈ M ∨ b - 1 ∈ M) :
    ∃ i, ‖Q.edge i + e‖ ^ 2 ≤ 8 * δ := by
  by_cases hbig : 1 / 2 ≤ δ
  · refine ⟨0, ?_⟩
    have h := norm_add_le (Q.edge 0) e
    rw [Q.norm_edge, he] at h
    have h0 := norm_nonneg (Q.edge 0 + e)
    nlinarith
  push_neg at hbig
  by_contra hcon
  push_neg at hcon
  -- every edge has projection greater than `-1 + 4 δ`
  have hlow : ∀ i, -1 + 4 * δ < inner ℝ (Q.edge i) e := by
    intro i
    have h := hcon i
    rw [norm_add_sq_real, Q.norm_edge, he] at h
    linarith
  -- adjacent edges
  have hadj : ∀ x : Fin k, (x + 1 ∈ M ∨ x - 1 ∈ M) → -1 / 2 - δ ≤ inner ℝ (Q.edge x) e := by
    intro x hx
    rcases hx with h | h
    · exact Q.inner_ge_of_adj hk (Or.inl rfl) (hM _ h)
    · exact Q.inner_ge_of_adj hk (Or.inr (by ring)) (hM _ h)
  -- the marked edges
  have hmark : ∀ i ∈ M, 1 - δ ≤ inner ℝ (Q.edge i) e := by
    intro i hi
    have h := inner_ge_of_close (Q.norm_edge i) he (hM i hi)
    nlinarith
  have hsum := Q.sum_inner_edge e
  set f : Fin k → ℝ := fun i => inner ℝ (Q.edge i) e with hf
  set R := (Finset.univ \ M).erase a |>.erase b with hR
  have haR : a ∈ Finset.univ \ M := by simp [ha]
  have hbR : b ∈ (Finset.univ \ M).erase a := by simp [hb, Ne.symm hab]
  have hsplit : ∑ i, f i = ∑ i ∈ M, f i + (f a + (f b + ∑ i ∈ R, f i)) := by
    rw [← Finset.sum_add_sum_compl M, Finset.compl_eq_univ_sdiff,
      ← Finset.add_sum_erase _ _ haR, ← Finset.add_sum_erase _ _ hbR]
  have hRcard : R.card + 1 = M.card := by
    have h1 : (Finset.univ \ M).card = k - M.card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
    have h2 := Finset.card_erase_of_mem haR
    have h3 := Finset.card_erase_of_mem hbR
    rw [hR, h3, h2, h1]
    omega
  have hRne : R.Nonempty := by
    rw [← Finset.card_pos]; omega
  have h1 : (M.card : ℝ) * (1 - δ) ≤ ∑ i ∈ M, f i := by
    have := Finset.card_nsmul_le_sum M f (1 - δ) hmark
    rwa [nsmul_eq_mul] at this
  have h2 : (R.card : ℝ) * (-1 + 4 * δ) < ∑ i ∈ R, f i := by
    have := Finset.sum_lt_sum_of_nonempty hRne (fun i _ => hlow i) (f := fun _ => -1 + 4 * δ)
    rwa [Finset.sum_const, nsmul_eq_mul] at this
  have h3 := hadj a hadja
  have h4 := hadj b hadjb
  have hRc : (R.card : ℝ) + 1 = M.card := by exact_mod_cast hRcard
  have hM2' : (2 : ℝ) ≤ M.card := by exact_mod_cast hM2
  have : ∑ i, f i > 0 := by
    rw [hsplit]
    nlinarith
  rw [hsum] at this
  exact lt_irrefl _ this

end UnitPolygon

set_option maxRecDepth 100000 in
/-- In a `5`-cycle with two marked edges, two distinct unmarked edges are adjacent to marked
ones. -/
theorem adj_pair_five : ∀ M : Finset (Fin 5), M.card = 2 → ∃ a b : Fin 5, a ∉ M ∧ b ∉ M ∧
    a ≠ b ∧ (a + 1 ∈ M ∨ a - 1 ∈ M) ∧ (b + 1 ∈ M ∨ b - 1 ∈ M) := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- In a `7`-cycle with three marked edges, two distinct unmarked edges are adjacent to marked
ones. -/
theorem adj_pair_seven : ∀ M : Finset (Fin 7), M.card = 3 → ∃ a b : Fin 7, a ∉ M ∧ b ∉ M ∧
    a ≠ b ∧ (a + 1 ∈ M ∨ a - 1 ∈ M) ∧ (b + 1 ∈ M ∨ b - 1 ∈ M) := by
  decide +kernel

namespace UnitPolygon

/-- **Pentagon emission** (§8.2).  If two edges of a closed unit pentagon are within `δ` of the
unit vector `e`, some edge `u` has `‖u + e‖² ≤ 8 δ`. -/
theorem pentagon_opposite (Q : UnitPolygon 5) {e : Plane} (he : ‖e‖ = 1) {δ : ℝ} (hδ0 : 0 ≤ δ)
    {M : Finset (Fin 5)} (hcard : 2 ≤ M.card) (hM : ∀ i ∈ M, ‖Q.edge i - e‖ ≤ δ) :
    ∃ i, ‖Q.edge i + e‖ ^ 2 ≤ 8 * δ := by
  obtain ⟨M', hM'M, hM'c⟩ := Finset.exists_subset_card_eq hcard
  obtain ⟨a, b, ha, hb, hab, hadja, hadjb⟩ := adj_pair_five M' hM'c
  exact Q.exists_opposite_edge (by norm_num) he hδ0 (by omega) (by omega)
    (fun i hi => hM i (hM'M hi)) ha hb hab hadja hadjb

/-- **Heptagon emission** (§8.2).  If three edges of a closed unit heptagon are within `δ` of the
unit vector `e`, some edge `u` has `‖u + e‖² ≤ 8 δ`. -/
theorem heptagon_opposite (Q : UnitPolygon 7) {e : Plane} (he : ‖e‖ = 1) {δ : ℝ} (hδ0 : 0 ≤ δ)
    {M : Finset (Fin 7)} (hcard : 3 ≤ M.card) (hM : ∀ i ∈ M, ‖Q.edge i - e‖ ≤ δ) :
    ∃ i, ‖Q.edge i + e‖ ^ 2 ≤ 8 * δ := by
  obtain ⟨M', hM'M, hM'c⟩ := Finset.exists_subset_card_eq hcard
  obtain ⟨a, b, ha, hb, hab, hadja, hadjb⟩ := adj_pair_seven M' hM'c
  exact Q.exists_opposite_edge (by norm_num) he hδ0 (by omega) (by omega)
    (fun i hi => hM i (hM'M hi)) ha hb hab hadja hadjb

/-- For a pentagon or a heptagon: `r` edges within `δ` of `e`, where `k ≤ 2 r + 1`, force an edge
`u` with `‖u + e‖² ≤ 8 δ`. -/
theorem exists_opposite_of_card {k : ℕ} [NeZero k] (Q : UnitPolygon k) (hk : k = 5 ∨ k = 7)
    {e : Plane} (he : ‖e‖ = 1) {δ : ℝ} (hδ0 : 0 ≤ δ) {M : Finset (Fin k)}
    (hcard : k ≤ 2 * M.card + 1) (hM : ∀ i ∈ M, ‖Q.edge i - e‖ ≤ δ) :
    ∃ i, ‖Q.edge i + e‖ ^ 2 ≤ 8 * δ := by
  rcases hk with rfl | rfl
  · exact Q.pentagon_opposite he hδ0 (by omega) hM
  · exact Q.heptagon_opposite he hδ0 (by omega) hM

end UnitPolygon

/-! ## Exceptional faces -/

/-- **Exceptional faces are closed unit polygons, with all their sides.**  Eventually, every
exceptional face `F` with `k = faceSize X F` sides is a `UnitPolygon k` whose consecutive vertex
pairs (in `ℂ`) are exactly the oriented sides of `F`: every oriented side is a consecutive pair, and
every consecutive pair is an oriented side. -/
theorem exceptionalFace_unitPolygon_sides :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ∀ F ∈ exceptionalFaces X,
      ∃ (h : NeZero (faceSize X F)) (Q : @UnitPolygon (faceSize X F) h),
        (∀ ab ∈ orientedSides X F, ∃ i : Fin (faceSize X F),
          toC (Q.P i) = ab.1 ∧ toC (Q.P (i + 1)) = ab.2) ∧
        ∀ i : Fin (faceSize X F), (toC (Q.P i), toC (Q.P (i + 1))) ∈ orientedSides X F := by
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
  have hmemE : ∀ i : ℕ, s(v i, v (i + 1)) ∈ bdryEdges (cUnitEdges X) F := by
    intro i
    have hs : IsCSide S (v i) (v (i + 1)) := (hside _ _).2 ⟨i, rfl, rfl⟩
    have : s(v i, v (i + 1)) ∈ cSides S :=
      Finset.mem_image.2 ⟨(v i, v (i + 1)),
        Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hs.1, hs.2.1⟩, hs⟩, rfl⟩
    rw [← hbd] at this
    exact this
  let Q : UnitPolygon S.card :=
    { P := fun i => toC.symm (v i)
      unit_edge := by
        intro i
        simp only
        rw [hsucc]
        have hmem : s(v i, v (i + 1)) ∈ cUnitEdges X := (Finset.mem_filter.1 (hmemE i)).1
        have hd := (mem_unitPairs.1 hmem).2.2
        rw [← map_sub, LinearIsometryEquiv.norm_map, ← dist_eq_norm, dist_comm]
        exact hd
      sep := by
        intro i j hij
        have hne' : v i ≠ v j := fun h => hij (Fin.ext (hinj (Set.mem_Iio.2 i.2)
          (Set.mem_Iio.2 j.2) h))
        exact hX.1.2 _ (hvX i) _ (hvX j) (fun h => hne' (toC.symm.injective h)) }
  refine ⟨hk, Q, fun ab hab => ?_, fun i => ?_⟩
  · obtain ⟨i, hi1, hi2⟩ := (hside _ _).1 (isCSide_of_mem_orientedSides hFint hbd hne hab)
    refine ⟨⟨i % S.card, Nat.mod_lt _ (by omega)⟩, ?_, ?_⟩
    · show toC (toC.symm (v (i % S.card))) = ab.1
      rw [LinearIsometryEquiv.apply_symm_apply, hmod, hi1]
    · show toC (toC.symm (v ((⟨i % S.card, _⟩ + 1 : Fin S.card) : ℕ))) = ab.2
      rw [LinearIsometryEquiv.apply_symm_apply, hsucc, ← hmod, Nat.add_mod, Nat.mod_mod,
        ← Nat.add_mod, hmod, hi2]
  · show (toC (toC.symm (v i)), toC (toC.symm (v ((i + 1 : Fin S.card) : ℕ)))) ∈ _
    rw [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply, hsucc]
    have hs : IsCSide S (v i) (v (i + 1)) := (hside _ _).2 ⟨i, rfl, rfl⟩
    refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hSV hs.1, hSV hs.2.1⟩, hmemE i,
      fun z hz => side_pos hs (hFint ▸ hz)⟩

/-- **The almost-opposite side of an emitting face** (§8.2 applied to the faces).  Eventually,
let `G` be an exceptional pentagon or heptagon, `e` a unit vector and `M` a set of at least two
(pentagon) or three (heptagon) oriented sides of `G` whose directions are within `δ` of `e`.  Then
some oriented side `(a, b)` of `G` has its reversal `a - b` with `‖(a - b) - e‖² ≤ 8 δ`. -/
theorem exists_almostOpposite_side :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ∀ G ∈ exceptionalFaces X,
      (faceSize X G = 5 ∨ faceSize X G = 7) → ∀ e : ℂ, ‖e‖ = 1 → ∀ δ : ℝ, 0 ≤ δ →
      ∀ M ⊆ orientedSides X G, faceSize X G ≤ 2 * M.card + 1 →
      (∀ ab ∈ M, ‖(ab.2 - ab.1) - e‖ ≤ δ) →
      ∃ ab ∈ orientedSides X G, ‖(ab.1 - ab.2) - e‖ ^ 2 ≤ 8 * δ := by
  filter_upwards [exceptionalFace_unitPolygon_sides] with n hpoly hfm X hX G hG hk e he δ hδ M
    hMG hcard hM
  obtain ⟨hk0, Q, hQ, hQ'⟩ := hpoly hfm X hX G hG
  set k := faceSize X G
  set f : Fin k → ℂ × ℂ := fun i => (toC (Q.P i), toC (Q.P (i + 1)))
  set M' : Finset (Fin k) := Finset.univ.filter (fun i => f i ∈ M)
  have hsub : M ⊆ M'.image f := by
    intro ab hab
    obtain ⟨i, h1, h2⟩ := hQ ab (hMG hab)
    have hfi : f i = ab := Prod.ext h1 h2
    exact Finset.mem_image.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hfi ▸ hab⟩, hfi⟩
  have hcard' : M.card ≤ M'.card := (Finset.card_le_card hsub).trans Finset.card_image_le
  have he' : ‖toC.symm e‖ = 1 := by rw [LinearIsometryEquiv.norm_map]; exact he
  obtain ⟨i, hi⟩ := Q.exists_opposite_of_card hk he' hδ (M := M') (by omega) (by
    intro i hi
    have hfi := (Finset.mem_filter.1 hi).2
    have h := hM _ hfi
    simp only [f] at h
    rw [UnitPolygon.edge, ← LinearIsometryEquiv.norm_map toC, map_sub, map_sub,
      LinearIsometryEquiv.apply_symm_apply]
    exact h)
  refine ⟨f i, hQ' i, ?_⟩
  simp only [f]
  have : toC (Q.P i) - toC (Q.P (i + 1)) - e = -toC (Q.edge i + toC.symm e) := by
    rw [map_add, LinearIsometryEquiv.apply_symm_apply, UnitPolygon.edge, map_sub]; ring
  rw [this, norm_neg, LinearIsometryEquiv.norm_map]
  exact hi

end Erdos99

end

end EmissionGeometry

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `LongExits`
-/

section LongExits

/-!
# Long labelled exits are few (Verification Guide §9.2)

The short-source theorem `short_unit_sources` bounds the number of unit hull sides lying on long
tracks.  In the finite token process of §9 the same bound is needed for the *emitted* tokens: an
exceptional face emits along an exit edge whose direction is close to the tangent of the source
label carried by the token, and the labels of distinct emitted tokens are distinct.

`long_labelled_exits`: fix an exponent `0 < e ≤ 1/20`.  Eventually, any family of oriented terminal
edges lying on tracks with at least `c D^{1-e}` rhombi, labelled injectively by hull sides whose
directions are within `M D^{-3e/2}` of the directions of the edges, has at most `ε D` members.

The proof is that of `short_unit_sources` at the cutoff `L = c D^{1-e}`: clustering of the long
track directions with tolerance `D^{-1/4}` discards `O(D^{1/4+e})` tracks (each with at most two
terminal edges) and leaves `O(D^e)` direction families; by the spread of the hull directions
(`hull_direction_spread`) and the injectivity of the labels, the remaining edges number
`O(D^{1+e} (D^{-1/4} + D^{-3e/2} + D^{-1/9})) = o(D)`.
-/

open scoped BigOperators Real
open Filter

@[expose] public noncomputable section

open Classical

namespace Erdos99

/-- Sixth powers of unit complex numbers are `6`-Lipschitz. -/
lemma norm_pow_six_sub_le {z w : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) :
    ‖z ^ 6 - w ^ 6‖ ≤ 6 * ‖z - w‖ := by
  have e : z ^ 6 - w ^ 6 = (z - w) * (z ^ 5 + z ^ 4 * w + z ^ 3 * w ^ 2 + z ^ 2 * w ^ 3 +
      z * w ^ 4 + w ^ 5) := by ring
  rw [e, norm_mul, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  have h := fun a b : ℂ => norm_add_le a b
  calc ‖z ^ 5 + z ^ 4 * w + z ^ 3 * w ^ 2 + z ^ 2 * w ^ 3 + z * w ^ 4 + w ^ 5‖
      ≤ ‖z ^ 5‖ + ‖z ^ 4 * w‖ + ‖z ^ 3 * w ^ 2‖ + ‖z ^ 2 * w ^ 3‖ + ‖z * w ^ 4‖ + ‖w ^ 5‖ := by
        refine (h _ _).trans ?_
        gcongr
        refine (h _ _).trans ?_
        gcongr
        refine (h _ _).trans ?_
        gcongr
        refine (h _ _).trans ?_
        gcongr
        exact h _ _
    _ = 6 := by simp [norm_pow, hz, hw]; norm_num

/-- `dir6` of oriented edges is `6`-Lipschitz in the unit directions. -/
lemma norm_dir6_sub_le_sideDir {p q : Plane × Plane} (hp : p.1 ≠ p.2) (hq : q.1 ≠ q.2) :
    ‖dir6 (p.2 - p.1) - dir6 (q.2 - q.1)‖ ≤ 6 * ‖sideDir p - sideDir q‖ := by
  rw [dir6_eq_pow_sideDir, dir6_eq_pow_sideDir]
  have h := norm_pow_six_sub_le (z := toC (sideDir p)) (w := toC (sideDir q))
    (by rw [LinearIsometryEquiv.norm_map]; exact norm_sideDir hp)
    (by rw [LinearIsometryEquiv.norm_map]; exact norm_sideDir hq)
  rwa [← map_sub, LinearIsometryEquiv.norm_map] at h

/-- **Long labelled exits are few** (§9.2).  Fix `0 < e ≤ 1/20`, `c > 0`, `M` and `ε > 0`.
Eventually, if `q` maps a finite family `S` injectively to oriented edges, each a terminal edge of
`X` lying on a track with at least `c D^{1-e}` rhombi, and `lab` labels `S` injectively by
counterclockwise hull sides whose directions are within `M D^{-3e/2}` of the directions of the
edges, then `|S| ≤ ε D`. -/
theorem long_labelled_exits {e c M ε : ℝ} (he0 : 0 < e) (he1 : e ≤ 1 / 20) (hc : 0 < c)
    (hε : 0 < ε) :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ {ι : Type} (S : Finset ι) (q lab : ι → Plane × Plane), Set.InjOn q S →
        (∀ i ∈ S, (q i).1 ≠ (q i).2 ∧ IsTerminal X s((q i).1, (q i).2) ∧
          c * diam X ^ (1 - e) ≤ srcLen X s((q i).1, (q i).2)) →
        Set.InjOn lab S → (∀ i ∈ S, lab i ∈ ccwHullSides X) →
        (∀ i ∈ S, ‖sideDir (q i) - sideDir (lab i)‖ ≤ M * diam X ^ (-(3 / 2 * e))) →
        (S.card : ℝ) ≤ ε * diam X := by
  obtain ⟨C1', hC1⟩ := rhombus_defect_sum
  obtain ⟨C2', hC2⟩ := tracks_card_le
  obtain ⟨C3', hC3⟩ := hull_direction_spread
  set C1 := max C1' 1
  set C2 := max C2' 1
  set C3 := max C3' 1
  set M' := max M 0
  have hC1p : 0 < C1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hC2p : 0 < C2 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hC3p : 0 < C3 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hM'0 : 0 ≤ M' := le_max_right _ _
  -- the asymptotic inequalities
  set A := 2 * C2 / c * C3
  have ev1 := eventually_mul_rpow_le (16 * C1 / c) (α := 1 / 4 + e) (δ := ε / 4) (by linarith)
    (by linarith)
  have ev2 := eventually_mul_rpow_le (2 * A) (α := 3 / 4 + e) (δ := ε / 4) (by linarith)
    (by linarith)
  have ev3 := eventually_mul_rpow_le (6 * M' * A) (α := 1 - e / 2) (δ := ε / 4) (by linarith)
    (by linarith)
  have ev4 := eventually_mul_rpow_le A (α := 8 / 9 + e) (δ := ε / 4) (by linarith)
    (by linarith)
  filter_upwards [hC1, hC2, hC3, tendsto_minDiam.eventually ev1, tendsto_minDiam.eventually ev2,
    tendsto_minDiam.eventually ev3, tendsto_minDiam.eventually ev4,
    tendsto_minDiam.eventually_ge_atTop 1] with n h1 h2 h3 e1 e2 e3 e4 hD1
  intro hfm X hX htri ι S q lab hqinj hS hinj hlab hdir
  rw [← hX.diam_eq] at e1 e2 e3 e4 hD1
  set D := diam X
  have hD0 : 0 < D := by linarith
  have hsep := hX.1.2
  have hdef : ∑ Q ∈ rhombi X, rhombusDefect Q ≤ C1 * D :=
    (h1 hfm X hX htri).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hD0.le)
  have hs : ((tracks X).card : ℝ) ≤ C2 * D :=
    (h2 hfm X hX htri).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hD0.le)
  set ε' := D ^ (-(1 / 4 : ℝ))
  set L := c * D ^ (1 - e)
  have hε'0 : 0 < ε' := by positivity
  have hL0 : 0 < L := by positivity
  obtain ⟨Disc, hDsub, Cs, -, hDcard, hCcard, hcov⟩ :=
    track_clustering hsep htri (K := C1 * D) hε'0 hL0 hdef
  -- powers of `D`
  have hεL : ε' * L = c * D ^ (3 / 4 - e) := by
    simp only [ε', L]
    rw [mul_left_comm, ← Real.rpow_add hD0]; ring_nf
  have hDcard' : (Disc.card : ℝ) ≤ 4 * C1 / c * D ^ (1 / 4 + e) := by
    rw [hεL] at hDcard
    have hp : 0 < c * D ^ (3 / 4 - e) := by positivity
    have e' : 4 * C1 / c * D ^ (1 / 4 + e) * (c * D ^ (3 / 4 - e)) = 4 * (C1 * D) := by
      have : D ^ (1 / 4 + e) * D ^ (3 / 4 - e) = D := by
        rw [← Real.rpow_add hD0]; norm_num
      calc 4 * C1 / c * D ^ (1 / 4 + e) * (c * D ^ (3 / 4 - e))
          = 4 * C1 * (D ^ (1 / 4 + e) * D ^ (3 / 4 - e)) := by field_simp
        _ = 4 * (C1 * D) := by rw [this]; ring
    rw [← mul_le_mul_iff_of_pos_right hp, e']
    exact hDcard
  have hCcard' : (Cs.card : ℝ) ≤ 2 * C2 / c * D ^ e := by
    have hp : 0 < L := hL0
    have e' : 2 * C2 / c * D ^ e * L = 2 * (C2 * D) := by
      have : D ^ e * D ^ (1 - e) = D := by
        rw [← Real.rpow_add hD0]; norm_num
      simp only [L]
      calc 2 * C2 / c * D ^ e * (c * D ^ (1 - e)) = 2 * C2 * (D ^ e * D ^ (1 - e)) := by
            field_simp
        _ = 2 * (C2 * D) := by rw [this]; ring
    rw [← mul_le_mul_iff_of_pos_right hp, e']
    linarith
  -- split `S`
  have hpos : ∀ i ∈ S, 0 < srcLen X s((q i).1, (q i).2) := by
    intro i hi
    have h := (hS i hi).2.2
    have : (0 : ℝ) < srcLen X s((q i).1, (q i).2) := lt_of_lt_of_le hL0 h
    exact_mod_cast this
  set S1 := S.filter (fun i => trackOf X s((q i).1, (q i).2) ∈ Disc)
  set S2 := S.filter (fun i => trackOf X s((q i).1, (q i).2) ∉ Disc)
  have hsplit : S.card = S1.card + S2.card := (Finset.card_filter_add_card_filter_not _).symm
  have hS1 : S1.card ≤ 4 * Disc.card := by
    refine card_le_four_mul_of_terminal hsep htri hDsub S1 (fun i => s((q i).1, (q i).2)) ?_ ?_
    · intro i hi
      obtain ⟨hiS, hiD⟩ := Finset.mem_filter.1 hi
      obtain ⟨-, hm, -⟩ := long_track_facts (hpos i hiS)
      exact ⟨(hS i hiS).2.1, _, hiD, hm⟩
    · intro f
      have hinjq : Set.InjOn q (S1.filter (fun i => s((q i).1, (q i).2) = f)) :=
        hqinj.mono (fun i hi => (Finset.mem_filter.1 (Finset.mem_filter.1 hi).1).1)
      rw [← Finset.card_image_of_injOn hinjq]
      refine le_trans (Finset.card_le_card ?_) (card_filter_mk_eq_le_two (S.image q) f)
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨hi1, hi2⟩ := Finset.mem_filter.1 hi
      exact Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ (Finset.mem_filter.1 hi1).1, hi2⟩
  set ρ := 2 * ε' + 6 * (M' * D ^ (-(3 / 2 * e)))
  have hρ0 : 0 ≤ ρ := by positivity
  have hS2 : (S2.card : ℝ) ≤ C3 * D * Cs.card * (ρ + D ^ (-(1 / 9 : ℝ))) := by
    refine le_trans ?_ ((h3 X hX Cs ρ hρ0).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hD0.le)
        (by positivity)) (by positivity)))
    have hmaps : ∀ i ∈ S2, lab i ∈ (ccwHullSides X).filter
        (fun p => ∃ c ∈ Cs, ‖dir6 (p.2 - p.1) - c‖ ≤ ρ) := by
      intro i hi
      obtain ⟨hiS, hiD⟩ := Finset.mem_filter.1 hi
      obtain ⟨hT, -, htd⟩ := long_track_facts (hpos i hiS)
      obtain ⟨c', hc', hcl⟩ := hcov _ hT hiD (by
        have : srcLen X s((q i).1, (q i).2) = trackLength X (trackOf X s((q i).1, (q i).2)) := rfl
        rw [← this]; exact (hS i hiS).2.2)
      rw [htd] at hcl
      refine Finset.mem_filter.2 ⟨hlab i hiS, c', hc', ?_⟩
      have hl := mem_ccwHullSides.1 (hlab i hiS)
      have hq12 : (q i).1 ≠ (q i).2 := (hS i hiS).1
      have hd6 := norm_dir6_sub_le_sideDir hl.2.2.1 hq12
      have hdq : ‖sideDir (lab i) - sideDir (q i)‖ ≤ M' * D ^ (-(3 / 2 * e)) := by
        rw [norm_sub_rev]
        exact (hdir i hiS).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
      calc ‖dir6 ((lab i).2 - (lab i).1) - c'‖
          ≤ ‖dir6 ((lab i).2 - (lab i).1) - dir6 ((q i).2 - (q i).1)‖ +
            ‖dir6 ((q i).2 - (q i).1) - c'‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ 6 * (M' * D ^ (-(3 / 2 * e))) + 2 * ε' := by
            gcongr
            exact hd6.trans (by linarith)
        _ = ρ := by ring
    have := Finset.card_le_card_of_injOn lab hmaps (hinj.mono (Finset.coe_subset.2
      (Finset.filter_subset _ _)))
    exact_mod_cast this
  -- the estimates
  have hρexp : C3 * D * Cs.card * (ρ + D ^ (-(1 / 9 : ℝ))) ≤
      2 * A * D ^ (3 / 4 + e) + 6 * M' * A * D ^ (1 - e / 2) + A * D ^ (8 / 9 + e) := by
    have hCs0 : (0 : ℝ) ≤ Cs.card := Nat.cast_nonneg _
    have k1 : D * D ^ e * D ^ (-(1 / 4 : ℝ)) = D ^ (3 / 4 + e) := by
      rw [← Real.rpow_one_add' hD0.le (by linarith), ← Real.rpow_add hD0]; ring_nf
    have k2 : D * D ^ e * D ^ (-(3 / 2 * e)) = D ^ (1 - e / 2) := by
      rw [← Real.rpow_one_add' hD0.le (by linarith), ← Real.rpow_add hD0]; ring_nf
    have k3 : D * D ^ e * D ^ (-(1 / 9 : ℝ)) = D ^ (8 / 9 + e) := by
      rw [← Real.rpow_one_add' hD0.le (by linarith), ← Real.rpow_add hD0]; ring_nf
    calc C3 * D * Cs.card * (ρ + D ^ (-(1 / 9 : ℝ)))
        ≤ C3 * D * (2 * C2 / c * D ^ e) * (ρ + D ^ (-(1 / 9 : ℝ))) := by gcongr
      _ = A * (2 * (D * D ^ e * ε') + 6 * M' * (D * D ^ e * D ^ (-(3 / 2 * e))) +
            D * D ^ e * D ^ (-(1 / 9 : ℝ))) := by simp only [A, ρ]; ring
      _ = 2 * A * D ^ (3 / 4 + e) + 6 * M' * A * D ^ (1 - e / 2) + A * D ^ (8 / 9 + e) := by
            simp only [ε']; rw [k1, k2, k3]; ring
  have hS1' : (S1.card : ℝ) ≤ 16 * C1 / c * D ^ (1 / 4 + e) := by
    have : (S1.card : ℝ) ≤ 4 * Disc.card := by exact_mod_cast hS1
    have h4 : 4 * (Disc.card : ℝ) ≤ 4 * (4 * C1 / c * D ^ (1 / 4 + e)) := by linarith
    calc (S1.card : ℝ) ≤ 4 * (4 * C1 / c * D ^ (1 / 4 + e)) := this.trans h4
      _ = 16 * C1 / c * D ^ (1 / 4 + e) := by ring
  have hcard : (S.card : ℝ) = S1.card + S2.card := by exact_mod_cast hsplit
  linarith
end Erdos99
end

end LongExits

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `TokenLabels`
-/

section TokenLabels

/-!
# Source labels and discarded tokens of a token process (Verification Guide §9.1–§9.2)

This file contains the configuration-free bookkeeping of the finite token process of §9.1, for an
arbitrary `P : TokenProcess X`.

**Emission times and parents.**  `P.Emits j G` says that the face `G` has emitted by the end of
round `j + 1` (it has received enough tokens by round `j`); `P.firstEmit G` is the first such
round.  Every emitting face `G` has a *parent*: a token `P.parent G` arriving at `G` by the round
of its emission.  The emitted token inherits the label of its parent.

**Labels never split.**  `P.labelAt n` follows parents back to a source.  Distinct parents have
distinct faces, so the tokens carrying one label form a single chain of parents and children
(`labelAt_chain`).  Consequently the labels are injective on the arrivals at every face that never
emits (`labelAt_injOn`), and on the emitted tokens of any one round (`labelAt_injOn_firstEmit`).

**Discarded tokens.**  `P.badAt srcBad primBad n` is the set of bad tokens after round `n`: the
sources with `srcBad`, the emitted tokens with `primBad` at their round of emission, and the
emitted tokens of faces that received a bad token before emitting.  `card_badAt_le` bounds the
number of bad faces by `(2ⁿ - 1) (#bad sources + B)` when at most `B` faces are primarily bad in
each round.
-/

open scoped BigOperators

@[expose] public noncomputable section

open Classical

namespace Erdos99

open Propagation

namespace TokenProcess

variable {X : Finset Plane} (P : TokenProcess X)

/-! ## Emission times -/

/-- The face `G` has emitted by the end of round `j + 1`. -/
def Emits (j : ℕ) (G : Set ℂ) : Prop := emitted (faceSize X G) (P.faceArr j G) = 1

lemma emits_mono {i j : ℕ} (h : i ≤ j) {G : Set ℂ} (hi : P.Emits i G) : P.Emits j G := by
  unfold Emits at *
  have h1 := TokenLedger.emitted_mono (faceSize X G) (P.faceArr_mono' h G)
  rcases emitted_eq_zero_or_one (faceSize X G) (P.faceArr j G) with h2 | h2
  · omega
  · exact h2

lemma not_emits_zero (G : Set ℂ) : ¬ P.Emits 0 G := by
  simp [Emits, faceArr_zero, emitted]

lemma two_le_faceArr_of_emits {j : ℕ} {G : Set ℂ} (h : P.Emits j G) : 2 ≤ P.faceArr j G := by
  unfold Emits emitted at h
  split_ifs at h with h'
  omega

lemma faceSize_of_emits {j : ℕ} {G : Set ℂ} (h : P.Emits j G) :
    faceSize X G = 5 ∨ faceSize X G = 7 := by
  unfold Emits emitted at h
  split_ifs at h with h'
  omega

/-- Arrivals only grow. -/
lemma arrivals_mono {i j : ℕ} (h : i ≤ j) (F : Set ℂ) : P.arrivals i F ⊆ P.arrivals j F := by
  intro t ht
  rcases t with p | G
  · simpa [arrivals] using ht
  · simp only [arrivals, Finset.inr_mem_disjSum, Finset.mem_filter] at ht ⊢
    exact ⟨ht.1, ht.2.1, P.emits_mono h ht.2.2⟩

lemma mem_arrivals_inl {j : ℕ} {F : Set ℂ} {p : Plane × Plane} :
    Sum.inl p ∈ P.arrivals j F ↔ p ∈ unitHullSides X ∧ P.start p = .face F := by
  simp [arrivals]

lemma mem_arrivals_inr {j : ℕ} {F G : Set ℂ} :
    Sum.inr G ∈ P.arrivals j F ↔ G ∈ P.fin.toFinset ∧ P.out G = .face F ∧ P.Emits j G := by
  simp [arrivals, Emits]

/-- The receiver of a token. -/
def dest : (Plane × Plane) ⊕ Set ℂ → TokenDest
  | Sum.inl p => P.start p
  | Sum.inr G => P.out G

lemma dest_of_mem_arrivals {j : ℕ} {F : Set ℂ} {t : (Plane × Plane) ⊕ Set ℂ}
    (ht : t ∈ P.arrivals j F) : P.dest t = .face F := by
  rcases t with p | G
  · exact (P.mem_arrivals_inl.1 ht).2
  · exact (P.mem_arrivals_inr.1 ht).2.1

/-- A token arrives at only one face. -/
lemma face_eq_of_mem_arrivals {j j' : ℕ} {F F' : Set ℂ} {t : (Plane × Plane) ⊕ Set ℂ}
    (ht : t ∈ P.arrivals j F) (ht' : t ∈ P.arrivals j' F') : F = F' := by
  have h1 := P.dest_of_mem_arrivals ht
  rw [P.dest_of_mem_arrivals ht'] at h1
  cases h1; rfl

/-- The first round by which `G` has emitted. -/
def firstEmit (G : Set ℂ) : ℕ := if h : ∃ j, P.Emits j G then Nat.find h else 0

lemma firstEmit_spec {j : ℕ} {G : Set ℂ} (h : P.Emits j G) :
    P.Emits (P.firstEmit G) G ∧ P.firstEmit G ≤ j ∧ 1 ≤ P.firstEmit G := by
  have hex : ∃ j, P.Emits j G := ⟨j, h⟩
  have e : P.firstEmit G = Nat.find hex := dif_pos hex
  rw [e]
  refine ⟨Nat.find_spec hex, Nat.find_min' hex h, ?_⟩
  by_contra h0
  push_neg at h0
  have : Nat.find hex = 0 := by omega
  have h1 := Nat.find_spec hex
  rw [this] at h1
  exact P.not_emits_zero G h1

lemma not_emits_of_lt_firstEmit {j i : ℕ} {G : Set ℂ} (h : P.Emits j G)
    (hi : i < P.firstEmit G) : ¬ P.Emits i G := by
  have hex : ∃ j, P.Emits j G := ⟨j, h⟩
  have e : P.firstEmit G = Nat.find hex := dif_pos hex
  rw [e] at hi
  exact Nat.find_min hex hi

lemma firstEmit_le_iff {j n : ℕ} {G : Set ℂ} (h : P.Emits j G) :
    P.firstEmit G ≤ n ↔ P.Emits n G := by
  constructor
  · intro hn; exact P.emits_mono hn (P.firstEmit_spec h).1
  · intro hn
    by_contra hlt
    push_neg at hlt
    exact P.not_emits_of_lt_firstEmit h hlt hn

lemma arrivals_firstEmit_nonempty {j : ℕ} {G : Set ℂ} (h : P.Emits j G) :
    (P.arrivals (P.firstEmit G - 1) G).Nonempty := by
  obtain ⟨hτ, -, h1⟩ := P.firstEmit_spec h
  have h2 := P.two_le_faceArr_of_emits hτ
  have e : P.firstEmit G = P.firstEmit G - 1 + 1 := by omega
  rw [e, faceArr_succ_eq_card] at h2
  rw [← Finset.card_pos]; omega

/-- A face emitting by round `j + 1` is a pentagon with at least two or a heptagon with at least
three arrivals by round `j`. -/
lemma faceSize_le_of_emits {j : ℕ} {G : Set ℂ} (h : P.Emits (j + 1) G) :
    faceSize X G ≤ 2 * (P.arrivals j G).card + 1 := by
  have h' := h
  unfold Emits emitted at h'
  rw [faceArr_succ_eq_card] at h'
  split_ifs at h' with hc
  omega

/-- The first emission round is the round `m` at which `G` emits but did not before. -/
lemma firstEmit_eq {m : ℕ} {G : Set ℂ} (h : P.Emits m G) (h' : ¬ P.Emits (m - 1) G) :
    P.firstEmit G = m := by
  obtain ⟨-, hle, h1⟩ := P.firstEmit_spec h
  by_contra hne
  have hlt : P.firstEmit G ≤ m - 1 := by omega
  exact h' ((P.firstEmit_le_iff h).1 hlt)

/-! ## Parents and labels -/

/-- The parent of an emitting face: a token arriving at it by the round of its emission. -/
def parent (G : Set ℂ) : (Plane × Plane) ⊕ Set ℂ :=
  if h : (P.arrivals (P.firstEmit G - 1) G).Nonempty then h.choose else Sum.inr G

lemma parent_mem {j : ℕ} {G : Set ℂ} (h : P.Emits j G) :
    P.parent G ∈ P.arrivals (P.firstEmit G - 1) G := by
  have hne := P.arrivals_firstEmit_nonempty h
  rw [parent, dif_pos hne]
  exact hne.choose_spec

/-- Distinct emitting faces have distinct parents. -/
lemma parent_injective {j j' : ℕ} {G G' : Set ℂ} (h : P.Emits j G) (h' : P.Emits j' G')
    (he : P.parent G = P.parent G') : G = G' :=
  P.face_eq_of_mem_arrivals (P.parent_mem h) (he ▸ P.parent_mem h')

/-- The label of a token, following parents back to a source (with fuel `n`). -/
def labelAt : ℕ → (Plane × Plane) ⊕ Set ℂ → Plane × Plane
  | _, Sum.inl p => p
  | 0, Sum.inr _ => (0, 0)
  | n + 1, Sum.inr G => labelAt n (P.parent G)

@[simp] lemma labelAt_inl (n : ℕ) (p : Plane × Plane) : P.labelAt n (Sum.inl p) = p := by
  cases n <;> rfl

lemma labelAt_succ_inr (n : ℕ) (G : Set ℂ) :
    P.labelAt (n + 1) (Sum.inr G) = P.labelAt n (P.parent G) := rfl

/-- A token present by round `n`: a source, or a face that has emitted by round `n`. -/
def Timed (n : ℕ) : (Plane × Plane) ⊕ Set ℂ → Prop
  | Sum.inl _ => True
  | Sum.inr G => P.Emits n G

lemma timed_mono {m n : ℕ} (h : m ≤ n) {t : (Plane × Plane) ⊕ Set ℂ} (ht : P.Timed m t) :
    P.Timed n t := by
  rcases t with p | G
  · exact True.intro
  · exact P.emits_mono h ht

lemma timed_of_mem_arrivals {j : ℕ} {F : Set ℂ} {t : (Plane × Plane) ⊕ Set ℂ}
    (ht : t ∈ P.arrivals j F) : P.Timed j t := by
  rcases t with p | G
  · exact True.intro
  · exact (P.mem_arrivals_inr.1 ht).2.2

/-- The parent of a face emitting by round `n + 1` is present by round `n`. -/
lemma timed_parent {n : ℕ} {G : Set ℂ} (h : P.Emits (n + 1) G) : P.Timed n (P.parent G) := by
  have hm := P.timed_of_mem_arrivals (P.parent_mem h)
  obtain ⟨-, hle, -⟩ := P.firstEmit_spec h
  exact P.timed_mono (by omega) hm

/-- The labels stabilize once the fuel exceeds the round. -/
lemma labelAt_stable {m n : ℕ} (hmn : m ≤ n) {t : (Plane × Plane) ⊕ Set ℂ} (ht : P.Timed m t) :
    P.labelAt n t = P.labelAt m t := by
  induction m generalizing n t with
  | zero =>
    rcases t with p | G
    · simp
    · exact absurd ht (P.not_emits_zero G)
  | succ m ih =>
    rcases t with p | G
    · simp
    · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      rw [labelAt_succ_inr, labelAt_succ_inr]
      exact ih (by omega) (P.timed_parent ht)

/-- The label of an emitted token is the label of its parent. -/
lemma labelAt_inr {n : ℕ} {G : Set ℂ} (h : P.Emits n G) :
    P.labelAt n (Sum.inr G) = P.labelAt n (P.parent G) := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := by
    obtain ⟨-, hle, h1⟩ := P.firstEmit_spec h
    exact ⟨n - 1, by omega⟩
  rw [labelAt_succ_inr, P.labelAt_stable (Nat.le_succ n') (P.timed_parent h)]

/-- Labels are sources. -/
lemma labelAt_mem {n : ℕ} {t : (Plane × Plane) ⊕ Set ℂ} (ht : P.Timed n t)
    (hsrc : ∀ p, t = Sum.inl p → p ∈ unitHullSides X) : P.labelAt n t ∈ unitHullSides X := by
  induction n generalizing t with
  | zero =>
    rcases t with p | G
    · simpa using hsrc p rfl
    · exact absurd ht (P.not_emits_zero G)
  | succ n ih =>
    rcases t with p | G
    · simpa using hsrc p rfl
    · rw [labelAt_succ_inr]
      refine ih (P.timed_parent ht) (fun p hp => ?_)
      have hm := P.parent_mem ht
      rw [hp] at hm
      exact (P.mem_arrivals_inl.1 hm).1

/-- One step of the chain of a label: `b` is the token emitted by the face whose parent is `a`. -/
def Step (a b : (Plane × Plane) ⊕ Set ℂ) : Prop :=
  ∃ G, b = Sum.inr G ∧ (∃ j, P.Emits j G) ∧ P.parent G = a

/-- `b` is `a` or a descendant of `a`. -/
def Desc : (Plane × Plane) ⊕ Set ℂ → (Plane × Plane) ⊕ Set ℂ → Prop :=
  Relation.ReflTransGen P.Step

lemma desc_inl {a : (Plane × Plane) ⊕ Set ℂ} {p : Plane × Plane} (h : P.Desc a (Sum.inl p)) :
    a = Sum.inl p := by
  rcases Relation.ReflTransGen.cases_tail h with h | ⟨b, -, G, hG, -⟩
  · exact h.symm
  · cases hG

/-- The descendants of the parent of `G` (other than itself) descend from the token of `G`. -/
lemma desc_of_desc_parent {j : ℕ} {G : Set ℂ} (hG : P.Emits j G)
    {b : (Plane × Plane) ⊕ Set ℂ} (h : P.Desc (P.parent G) b) :
    b = P.parent G ∨ P.Desc (Sum.inr G) b := by
  rcases Relation.ReflTransGen.cases_head h with h | ⟨c, ⟨G', rfl, ⟨j', hG'⟩, hpar⟩, hcb⟩
  · exact Or.inl h.symm
  · right
    rw [P.parent_injective hG' hG hpar] at hcb
    exact hcb

/-- **Labels never split**: two tokens present by round `n` with the same label lie on one chain
of parents and children. -/
theorem labelAt_chain (n : ℕ) :
    ∀ t t' : (Plane × Plane) ⊕ Set ℂ, P.Timed n t → P.Timed n t' →
      P.labelAt n t = P.labelAt n t' → P.Desc t t' ∨ P.Desc t' t := by
  induction n with
  | zero =>
    intro t t' ht ht' he
    rcases t with p | G
    · rcases t' with p' | G'
      · simp only [labelAt_inl] at he
        exact Or.inl (he ▸ Relation.ReflTransGen.refl)
      · exact absurd ht' (P.not_emits_zero G')
    · exact absurd ht (P.not_emits_zero G)
  | succ n ih =>
    -- the token of an emitting face against any token
    have key : ∀ (G : Set ℂ) (t' : (Plane × Plane) ⊕ Set ℂ), P.Emits (n + 1) G →
        P.Timed n t' → P.labelAt n (P.parent G) = P.labelAt n t' →
        (∀ G', t' ≠ Sum.inr G' ∨ P.parent G' ≠ P.parent G ∨ G' = G) →
        P.Desc (Sum.inr G) t' ∨ P.Desc t' (Sum.inr G) := by
      intro G t' hG ht' he _
      have hstep : P.Step (P.parent G) (Sum.inr G) := ⟨G, rfl, ⟨_, hG⟩, rfl⟩
      rcases ih _ _ (P.timed_parent hG) ht' he with h | h
      · rcases P.desc_of_desc_parent hG h with h' | h'
        · right; rw [h']; exact Relation.ReflTransGen.single hstep
        · left; exact h'
      · right; exact Relation.ReflTransGen.tail h hstep
    intro t t' ht ht' he
    rcases t with p | G
    · rcases t' with p' | G'
      · simp only [labelAt_inl] at he
        exact Or.inl (he ▸ Relation.ReflTransGen.refl)
      · rw [labelAt_succ_inr, labelAt_inl] at he
        have := key G' (Sum.inl p) ht' True.intro (by rw [he]; simp) (fun _ => Or.inl (by simp))
        exact this.symm
    · rcases t' with p' | G'
      · rw [labelAt_succ_inr, labelAt_inl] at he
        exact key G (Sum.inl p') ht True.intro (by rw [he]; simp) (fun _ => Or.inl (by simp))
      · rw [labelAt_succ_inr, labelAt_succ_inr] at he
        have hG' := P.timed_parent ht'
        have hstep' : P.Step (P.parent G') (Sum.inr G') := ⟨G', rfl, ⟨_, ht'⟩, rfl⟩
        rcases ih _ _ (P.timed_parent ht) hG' he with h | h
        · rcases P.desc_of_desc_parent ht h with h' | h'
          · left
            rw [P.parent_injective ht' ht h']
            exact Relation.ReflTransGen.refl
          · left; exact Relation.ReflTransGen.tail h' hstep'
        · rcases P.desc_of_desc_parent ht' h with h' | h'
          · left
            rw [P.parent_injective ht' ht h'.symm]
            exact Relation.ReflTransGen.refl
          · right
            exact Relation.ReflTransGen.tail h' ⟨G, rfl, ⟨_, ht⟩, rfl⟩

/-- A token whose receiver never emits has no descendant other than itself. -/
lemma eq_of_desc_of_not_emits {j : ℕ} {F : Set ℂ} (hF : ∀ i, ¬ P.Emits i F)
    {t t' : (Plane × Plane) ⊕ Set ℂ} (ht : t ∈ P.arrivals j F) (h : P.Desc t t') : t = t' := by
  rcases Relation.ReflTransGen.cases_head h with h | ⟨c, ⟨G, rfl, ⟨i, hG⟩, hpar⟩, -⟩
  · exact h
  · exfalso
    have := P.face_eq_of_mem_arrivals ht (hpar ▸ P.parent_mem hG)
    rw [this] at hF
    exact hF i hG

/-- **Labels are injective at a face that never emits** (e.g. a face with more than seven
sides). -/
theorem labelAt_injOn {n : ℕ} {F : Set ℂ} (hF : ∀ i, ¬ P.Emits i F) :
    Set.InjOn (P.labelAt n) (P.arrivals n F) := by
  intro t ht t' ht' he
  rcases P.labelAt_chain n t t' (P.timed_of_mem_arrivals ht) (P.timed_of_mem_arrivals ht') he
    with h | h
  · exact P.eq_of_desc_of_not_emits hF ht h
  · exact (P.eq_of_desc_of_not_emits hF ht' h).symm

/-- A token reaching a cap has no descendant other than itself. -/
lemma eq_of_desc_of_dest_cap {t t' : (Plane × Plane) ⊕ Set ℂ} (ht : P.dest t = .cap)
    (h : P.Desc t t') : t = t' := by
  rcases Relation.ReflTransGen.cases_head h with h | ⟨c, ⟨G, rfl, ⟨i, hG⟩, hpar⟩, -⟩
  · exact h
  · exfalso
    have := P.dest_of_mem_arrivals (hpar ▸ P.parent_mem hG)
    rw [ht] at this
    cases this

/-- **Labels are injective on the tokens reaching caps.** -/
theorem labelAt_injOn_cap (n : ℕ) :
    Set.InjOn (P.labelAt n) {t | P.Timed n t ∧ P.dest t = .cap} := by
  intro t ht t' ht' he
  rcases P.labelAt_chain n t t' ht.1 ht'.1 he with h | h
  · exact P.eq_of_desc_of_dest_cap ht.2 h
  · exact (P.eq_of_desc_of_dest_cap ht'.2 h).symm

/-- A child is emitted strictly later than its parent face. -/
lemma firstEmit_lt_of_step {G G' : Set ℂ} (h : P.Step (Sum.inr G) (Sum.inr G')) :
    P.Emits (P.firstEmit G' - 1) G ∧ P.firstEmit G < P.firstEmit G' := by
  obtain ⟨G'', hb, ⟨i, hi⟩, hpar⟩ := h
  cases hb
  have hm := P.parent_mem hi
  rw [hpar] at hm
  have hE := (P.mem_arrivals_inr.1 hm).2.2
  obtain ⟨-, -, h1⟩ := P.firstEmit_spec hi
  have := (P.firstEmit_le_iff hE).2 hE
  exact ⟨hE, by omega⟩

/-- Along a chain of descendants, emission times strictly increase. -/
lemma firstEmit_lt_of_desc {a b : (Plane × Plane) ⊕ Set ℂ} (h : P.Desc a b) :
    ∀ {G G' : Set ℂ}, a = Sum.inr G → b = Sum.inr G' → a ≠ b →
      P.firstEmit G < P.firstEmit G' := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro G G' _ _ hne; exact absurd rfl hne
  | @head a c hac hcb ih =>
    intro G G' ha hb _
    subst ha
    rcases c with p | Gc
    · obtain ⟨G'', hc, -⟩ := hac
      cases hc
    · have h1 := (P.firstEmit_lt_of_step hac).2
      by_cases hcb' : (Sum.inr Gc : (Plane × Plane) ⊕ Set ℂ) = Sum.inr G'
      · cases hcb'; exact h1
      · exact h1.trans (ih rfl hb (hb ▸ hcb'))

/-- **Labels are injective on the tokens emitted in one round.** -/
theorem labelAt_injOn_firstEmit {n m : ℕ} {G G' : Set ℂ} (hG : P.Emits n G) (hG' : P.Emits n G')
    (hm : P.firstEmit G = m) (hm' : P.firstEmit G' = m)
    (he : P.labelAt n (Sum.inr G) = P.labelAt n (Sum.inr G')) : G = G' := by
  by_contra hne
  have hne' : (Sum.inr G : (Plane × Plane) ⊕ Set ℂ) ≠ Sum.inr G' := fun h => hne (Sum.inr_injective h)
  rcases P.labelAt_chain n _ _ (show P.Timed n (Sum.inr G) from hG)
    (show P.Timed n (Sum.inr G') from hG') he with h | h
  · have := P.firstEmit_lt_of_desc h rfl rfl hne'
    omega
  · have := P.firstEmit_lt_of_desc h rfl rfl hne'.symm
    omega

/-! ## Discarded tokens -/

section Bad

variable (srcBad : Plane × Plane → Prop) (primBad : ℕ → Set ℂ → Prop)

/-- The bad tokens after round `n`: the bad sources, and the tokens emitted at round `m ≤ n` by a
face that is primarily bad at that round or has received a bad token by then. -/
def badAt : ℕ → (Plane × Plane) ⊕ Set ℂ → Prop
  | _, Sum.inl p => srcBad p
  | 0, Sum.inr _ => False
  | n + 1, Sum.inr G => badAt n (Sum.inr G) ∨ (P.Emits (n + 1) G ∧ ¬ P.Emits n G ∧
      (primBad (n + 1) G ∨ ∃ s ∈ P.arrivals n G, badAt n s))

@[simp] lemma badAt_inl (n : ℕ) (p : Plane × Plane) :
    P.badAt srcBad primBad n (Sum.inl p) ↔ srcBad p := by
  cases n <;> rfl

lemma badAt_succ_inr (n : ℕ) (G : Set ℂ) :
    P.badAt srcBad primBad (n + 1) (Sum.inr G) ↔ P.badAt srcBad primBad n (Sum.inr G) ∨
      (P.Emits (n + 1) G ∧ ¬ P.Emits n G ∧
        (primBad (n + 1) G ∨ ∃ s ∈ P.arrivals n G, P.badAt srcBad primBad n s)) := Iff.rfl

lemma badAt_emits {n : ℕ} {G : Set ℂ} (h : P.badAt srcBad primBad n (Sum.inr G)) :
    P.Emits n G := by
  induction n with
  | zero => exact h.elim
  | succ n ih =>
    rcases (P.badAt_succ_inr srcBad primBad n G).1 h with h | h
    · exact P.emits_mono (Nat.le_succ n) (ih h)
    · exact h.1

lemma badAt_mono {m n : ℕ} (hmn : m ≤ n) {t : (Plane × Plane) ⊕ Set ℂ}
    (h : P.badAt srcBad primBad m t) : P.badAt srcBad primBad n t := by
  induction hmn with
  | refl => exact h
  | step _ ih =>
    rcases t with p | G
    · simpa using ih
    · exact Or.inl ih

/-- Once a face has emitted, its token's status no longer changes. -/
lemma badAt_inr_stable {m n : ℕ} (hmn : m ≤ n) {G : Set ℂ} (hm : P.Emits m G) :
    P.badAt srcBad primBad n (Sum.inr G) ↔ P.badAt srcBad primBad m (Sum.inr G) := by
  induction hmn with
  | refl => exact Iff.rfl
  | @step k hk ih =>
    rw [P.badAt_succ_inr, ih]
    constructor
    · rintro (h | ⟨-, hn, -⟩)
      · exact h
      · exact absurd (P.emits_mono hk hm) hn
    · exact Or.inl

/-- **A good emitted token has good inputs**: if `G` has emitted by round `n` and its token is
not bad, then `G` is not primarily bad at its round of emission `τ`, and no token arriving at `G`
by round `τ` is bad. -/
lemma good_inputs {n : ℕ} {G : Set ℂ} (hG : P.Emits n G)
    (hgood : ¬ P.badAt srcBad primBad n (Sum.inr G)) :
    ¬ primBad (P.firstEmit G) G ∧ ∀ s ∈ P.arrivals (P.firstEmit G - 1) G,
      ¬ P.badAt srcBad primBad (P.firstEmit G - 1) s := by
  obtain ⟨hτ, hle, h1⟩ := P.firstEmit_spec hG
  rw [P.badAt_inr_stable srcBad primBad hle hτ] at hgood
  obtain ⟨k, hk⟩ : ∃ k, P.firstEmit G = k + 1 := ⟨P.firstEmit G - 1, by omega⟩
  rw [hk, P.badAt_succ_inr] at hgood
  rw [hk] at hτ ⊢
  have hnot : ¬ P.Emits k G := P.not_emits_of_lt_firstEmit hG (by omega)
  push_neg at hgood
  obtain ⟨-, h2⟩ := hgood
  have h3 := h2 hτ hnot
  simp only [Nat.add_sub_cancel]
  exact ⟨h3.1, h3.2⟩

/-- **Counting the bad faces.**  If in every round `m ≤ n` at most `B` faces emitting at round `m`
with good inputs are primarily bad, then at most `(2ⁿ - 1) (S + B)` faces have a bad token after
round `n`, where `S` is the number of bad sources. -/
theorem card_badAt_le (n B : ℕ)
    (hB : ∀ m ≤ n, (P.fin.toFinset.filter (fun G => P.Emits m G ∧ ¬ P.Emits (m - 1) G ∧
      primBad m G ∧ ∀ s ∈ P.arrivals (m - 1) G, ¬ P.badAt srcBad primBad (m - 1) s)).card ≤ B) :
    (P.fin.toFinset.filter (fun G => P.badAt srcBad primBad n (Sum.inr G))).card ≤
      (2 ^ n - 1) * (((unitHullSides X).filter srcBad).card + B) := by
  set S := ((unitHullSides X).filter srcBad).card
  induction n with
  | zero =>
    simp only [pow_zero, Nat.sub_self, zero_mul, Nat.le_zero, Finset.card_eq_zero]
    exact Finset.filter_false_of_mem (fun G _ h => h)
  | succ n ih =>
    have ih := ih (fun m hm => hB m (by omega))
    set A := P.fin.toFinset.filter (fun G => P.badAt srcBad primBad n (Sum.inr G))
    set Pr := P.fin.toFinset.filter (fun G => P.Emits (n + 1) G ∧ ¬ P.Emits (n + 1 - 1) G ∧
      primBad (n + 1) G ∧ ∀ s ∈ P.arrivals (n + 1 - 1) G,
        ¬ P.badAt srcBad primBad (n + 1 - 1) s)
    set C := P.fin.toFinset.filter (fun G => ∃ s ∈ P.arrivals n G, P.badAt srcBad primBad n s)
    have hsub : P.fin.toFinset.filter (fun G => P.badAt srcBad primBad (n + 1) (Sum.inr G)) ⊆
        A ∪ Pr ∪ C := by
      intro G hG
      obtain ⟨hGf, hb⟩ := Finset.mem_filter.1 hG
      rcases (P.badAt_succ_inr srcBad primBad n G).1 hb with h | ⟨h1, h2, h3 | h3⟩
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hGf, h⟩))
      · by_cases hs : ∃ s ∈ P.arrivals n G, P.badAt srcBad primBad n s
        · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hGf, hs⟩)
        · push_neg at hs
          exact Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_filter.2 ⟨hGf, h1, by simpa using h2, h3, by simpa using hs⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hGf, h3⟩)
    -- the faces receiving a bad token: inject into the bad tokens
    have hC : C.card ≤ S + A.card := by
      choose! g hg hgb using fun G (hG : G ∈ C) => (Finset.mem_filter.1 hG).2
      have hmaps : ∀ G ∈ C, g G ∈ ((unitHullSides X).filter srcBad).disjSum A := by
        intro G hG
        have hm := hg G hG
        have hb := hgb G hG
        rcases hgG : g G with p | G'
        · rw [hgG] at hm hb
          rw [Finset.inl_mem_disjSum]
          exact Finset.mem_filter.2 ⟨(P.mem_arrivals_inl.1 hm).1, by simpa using hb⟩
        · rw [hgG] at hm hb
          rw [Finset.inr_mem_disjSum]
          exact Finset.mem_filter.2 ⟨(P.mem_arrivals_inr.1 hm).1, hb⟩
      have hinj : Set.InjOn g C := by
        intro G hG G' hG' he
        exact P.face_eq_of_mem_arrivals (hg G hG) (he ▸ hg G' hG')
      have := Finset.card_le_card_of_injOn g hmaps hinj
      rwa [Finset.card_disjSum] at this
    have hPr : Pr.card ≤ B := hB (n + 1) le_rfl
    have h2 : 2 ^ (n + 1) - 1 = 2 * (2 ^ n - 1) + 1 := by
      have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      rw [pow_succ]; omega
    calc _ ≤ (A ∪ Pr ∪ C).card := Finset.card_le_card hsub
      _ ≤ A.card + Pr.card + C.card := by
          refine (Finset.card_union_le _ _).trans ?_
          exact Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ (2 ^ n - 1) * (S + B) + B + (S + (2 ^ n - 1) * (S + B)) := by omega
      _ = (2 ^ (n + 1) - 1) * (S + B) := by rw [h2]; ring

end Bad

end TokenProcess

end Erdos99

end

end TokenLabels

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `Caps`
-/

section Caps

/-!
# Caps of the non-unit hull sides (Lemma 2.1)

For a large optimal set `X` under finite multiplicity:

* `frontier_cHull_subset_augDrawing`: the boundary of the convex hull is covered by the hull
  vertices and the hull sides (every boundary point of `X` is a hull vertex);
* `exists_cap`, `cap_unique`: every hull side bounds exactly one cap (bounded face of the augmented
  graph having the side on its boundary);
* `cap_polygon`: the cap of a non-unit hull side `[v, w]` is the interior of a convex polygon in
  strictly convex position with `j + 1` sides, `j = returnLength X v w ≥ 2`, whose sides are
  exactly its boundary edges;
* consequences for the counts: `c₁ = u` and `ℓ = 2b - u + ρ`.
-/

open scoped BigOperators Real
open EstablishedExternalResults Set Complex Filter Topology

@[expose] public noncomputable section

open Classical

namespace Erdos99

/-- A non-collinear set spans a hull with nonempty interior. -/
lemma interior_cHull_nonempty {X : Finset Plane} (hcol : ¬ Collinear ℝ (X : Set Plane)) :
    (interior (convexHull ℝ ((cVerts X : Finset ℂ) : Set ℂ))).Nonempty := by
  have hne : (X : Set Plane).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    exact hcol (h ▸ collinear_empty ℝ Plane)
  have hP : (interior (convexHull ℝ (X : Set Plane))).Nonempty := by
    rw [interior_convexHull_nonempty_iff_affineSpan_eq_top]
    by_contra htop
    rw [AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ _ _ hne] at htop
    apply hcol
    rw [collinear_iff_finrank_le_one]
    have := Submodule.finrank_lt htop
    rw [finrank_euclideanSpace_fin] at this
    omega
  have e : toC '' convexHull ℝ (X : Set Plane) =
      convexHull ℝ ((cVerts X : Finset ℂ) : Set ℂ) := by
    rw [cVerts, Finset.coe_image]
    exact LinearMap.image_convexHull toC.toLinearEquiv.toLinearMap _
  have := toC.toHomeomorph.image_interior (convexHull ℝ (X : Set Plane))
  simp only [LinearIsometryEquiv.coe_toHomeomorph] at this
  rw [← e, ← this]
  exact hP.image _

/-- **The boundary of the hull is drawn.**  Every boundary point of the convex hull lies on a hull
vertex or on a hull side. -/
theorem frontier_cHull_subset_augDrawing :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      frontier (convexHull ℝ ((cVerts X : Finset ℂ) : Set ℂ)) ⊆
        drawing (cVerts X) (augEdges X) := by
  filter_upwards [boundary_hullVertex_eventually, eventually_not_collinear] with n hB hcol hfm X hX
  have hint := interior_cHull_nonempty (hcol X hX)
  set K := convexHull ℝ ((cVerts X : Finset ℂ) : Set ℂ) with hKdef
  have hKcl : IsClosed K := (cVerts X).finite_toSet.isCompact_convexHull.isClosed
  have eK : toC '' convexHull ℝ (X : Set Plane) = K := by
    rw [hKdef, cVerts, Finset.coe_image]
    exact LinearMap.image_convexHull toC.toLinearEquiv.toLinearMap _
  have hfr : ∀ x : Plane, toC x ∈ frontier K → x ∈ frontier (convexHull ℝ (X : Set Plane)) := by
    intro x hx
    have := toC.toHomeomorph.image_frontier (convexHull ℝ (X : Set Plane))
    simp only [LinearIsometryEquiv.coe_toHomeomorph] at this
    rw [← eK, ← this] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rw [toC.injective hyx] at hy
    exact hy
  intro m hm
  have hmK : m ∈ K := hKcl.frontier_subset hm
  have hmi : m ∉ interior K := hm.2
  by_cases hmV : m ∈ cVerts X
  · exact Or.inl hmV
  obtain ⟨a, b, hs, hmab⟩ := exists_side_of_frontier hint hmK hmi hmV
  have hHV : ∀ c ∈ cVerts X, (wc a b c).im = 0 → toC.symm c ∈ hullVertices X := by
    intro c hc hc0
    apply hB hfm X hX _ (mem_cVerts.1 hc) (hfr _ ?_)
    rw [LinearIsometryEquiv.apply_symm_apply]
    refine ⟨subset_closure (subset_convexHull ℝ _ hc), fun hint' => ?_⟩
    have := side_pos hs hint'
    linarith
  have hne : b - a ≠ 0 := sub_ne_zero.2 hs.2.2.1.symm
  have hwa : (wc a b a).im = 0 := by simp [wc]
  have hwb : (wc a b b).im = 0 := by simp [wc, div_self hne]
  have hccw : IsCcwHullSide X (toC.symm a) (toC.symm b) := by
    refine ⟨hHV a hs.1 hwa, hHV b hs.2.1 hwb, fun h => hs.2.2.1 (toC.symm.injective h),
      fun y hy => ?_⟩
    have h1 := hs.2.2.2 (toC y) (Finset.mem_image_of_mem _ hy)
    have h2 := im_wc_toC (toC.symm a) (toC.symm b) y
    simp only [LinearIsometryEquiv.apply_symm_apply] at h2
    rw [h2] at h1
    have hn : 0 < normSq (b - a) := normSq_pos.2 hne
    exact (div_nonneg_iff.1 h1).elim (fun h => h.1) (fun h => absurd h.2 (not_le.2 hn))
  refine Or.inr (Set.mem_iUnion₂.2 ⟨s(a, b), Finset.mem_union_right _ ?_,
    openSegment_subset_segment ℝ a b hmab⟩)
  exact Finset.mem_image.2 ⟨(toC.symm a, toC.symm b), mem_ccwHullSides.2 hccw, by simp⟩

/-- Near a point inside an edge, the drawing is that edge. -/
lemma exists_ball_drawing {V : Finset ℂ} {E : Finset (Sym2 ℂ)} (hP : IsPlaneGraph V E)
    {e : Sym2 ℂ} (he : e ∈ E) {p : ℂ} (hpV : p ∉ V) (hpe : p ∈ edgeSeg e) :
    ∃ r > 0, ∀ z ∈ Metric.ball p r, z ∈ drawing V E → z ∈ edgeSeg e := by
  set U := ((V : Set ℂ) ∪ ⋃ e' ∈ E.erase e, edgeSeg e')ᶜ with hUdef
  have hUo : IsOpen U := (V.finite_toSet.isClosed.union
    (((E.erase e).finite_toSet).isClosed_biUnion fun e' _ => isClosed_edgeSeg e')).isOpen_compl
  have hpU : p ∈ U := by
    rintro (h | h)
    · exact hpV h
    · obtain ⟨e', he', hpe'⟩ := Set.mem_iUnion₂.1 h
      obtain ⟨hne, he'E⟩ := Finset.mem_erase.1 he'
      exact hpV (hP.mem_V _ he p (hP.inter e he e' he'E (Ne.symm hne) p hpe hpe'))
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hUo p hpU
  refine ⟨r, hr, fun z hz hzD => ?_⟩
  have hzU := hball hz
  rcases hzD with h | h
  · exact absurd (Or.inl h) hzU
  · obtain ⟨e', he', hze'⟩ := Set.mem_iUnion₂.1 h
    by_cases hee : e' = e
    · rw [← hee]; exact hze'
    · exact absurd (Or.inr (Set.mem_iUnion₂.2 ⟨e', Finset.mem_erase.2 ⟨hee, he'⟩, hze'⟩)) hzU

/-- **Every hull side bounds a cap.** -/
theorem exists_cap :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      ∀ p ∈ ccwHullSides X, ∃ F, IsCap X p.1 p.2 F := by
  filter_upwards [augEdges_isPlaneGraph, frontier_cHull_subset_augDrawing,
    eventually_not_collinear] with n hPa hfr hcol hfm X hX p hp
  have hP := hPa hfm X hX
  have hint := interior_cHull_nonempty (hcol X hX)
  have hfrX := hfr hfm X hX
  set K := convexHull ℝ ((cVerts X : Finset ℂ) : Set ℂ) with hKdef
  set D := drawing (cVerts X) (augEdges X) with hDdef
  have hKcl : IsClosed K := (cVerts X).finite_toSet.isCompact_convexHull.isClosed
  have hKsub : K ⊆ closure (interior K) := by
    rw [(convex_convexHull ℝ _).closure_interior_eq_closure_of_nonempty_interior hint,
      hKcl.closure_eq]
  have hs := mem_ccwHullSides.1 hp
  have hcs := isCSide_of_ccw hs
  set a := toC p.1
  set b := toC p.2
  have hab : a ≠ b := hcs.2.2.1
  have hne : b - a ≠ 0 := sub_ne_zero.2 hab.symm
  have hn : 0 < ‖b - a‖ := norm_pos_iff.2 hne
  have he : s(a, b) ∈ augEdges X := Finset.mem_union_right _ (Finset.mem_image.2 ⟨p, hp, rfl⟩)
  set m := (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b with hmdef
  have hm : m ∈ openSegment ℝ a b := ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
  have hmV : m ∉ cVerts X := by
    intro h
    have := hP.vertex_mem _ he m h (openSegment_subset_segment ℝ a b hm)
    rcases Sym2.mem_iff.1 this with h1 | h1
    · rw [h1] at hm; exact hab (left_mem_openSegment_iff.1 hm)
    · rw [h1] at hm; exact hab (right_mem_openSegment_iff.1 hm)
  obtain ⟨r, hr, hball⟩ := exists_ball_drawing hP he hmV (openSegment_subset_segment ℝ a b hm)
  obtain ⟨c, hc⟩ := hint
  have hcpos := side_pos hcs hc
  obtain ⟨r2, hr2, hhalf⟩ := Metric.eventually_nhds_iff.1
    (halfdisc (convex_convexHull ℝ _).interior isOpen_interior (hKsub (subset_convexHull ℝ _ hcs.1))
      (hKsub (subset_convexHull ℝ _ hcs.2.1)) hc hm hcpos)
  have hm0 := (mem_openSegment_wc hab hm).1
  set ρ := min r r2 with hρ
  have hρpos : 0 < ρ := lt_min hr hr2
  set η0 := ρ / (2 * ‖b - a‖) with hη0
  have hη0pos : 0 < η0 := by positivity
  set φ : ℝ → ℂ := fun η => m + (η : ℂ) * I * (b - a) with hφ
  have hφd : ∀ η : ℝ, 0 ≤ η → dist (φ η) m = η * ‖b - a‖ := by
    intro η hη
    rw [dist_eq_norm, hφ]
    simp only [add_sub_cancel_left, norm_mul, Complex.norm_real, norm_I, mul_one,
      Real.norm_of_nonneg hη]
  have hφim : ∀ η : ℝ, (wc a b (φ η)).im = η := by
    intro η
    have : wc a b (φ η) = wc a b m + (η : ℂ) * I := by
      simp only [hφ, wc]; field_simp; ring
    rw [this, add_im, hm0]; simp
  have hφball : ∀ η : ℝ, 0 ≤ η → η < 2 * η0 → dist (φ η) m < ρ := by
    intro η h0 h1
    rw [hφd η h0]
    have : 2 * η0 * ‖b - a‖ = ρ := by rw [hη0]; field_simp
    nlinarith
  set L := φ '' Ioo 0 η0 with hL
  have hLc : IsPreconnected L := isPreconnected_Ioo.image _ (by fun_prop)
  have hLD : L ⊆ Dᶜ := by
    rintro _ ⟨η, hη, rfl⟩ hD
    have hb := hφball η hη.1.le (by linarith [hη.2])
    have := hball _ (lt_of_lt_of_le hb (min_le_left _ _)) hD
    rw [edgeSeg_mk] at this
    have h0 := wc_im_of_mem_segment this
    rw [hφim] at h0
    linarith [hη.1]
  have hz1 : φ (η0 / 2) ∈ L := ⟨η0 / 2, ⟨by positivity, by linarith⟩, rfl⟩
  set G := connectedComponentIn Dᶜ (φ (η0 / 2)) with hGdef
  have hG : G ∈ faces (cVerts X) (augEdges X) := mem_faces_iff.2 ⟨_, hLD hz1, rfl⟩
  have hLG : L ⊆ G := hLc.subset_connectedComponentIn hz1 hLD
  have hz1K : φ (η0 / 2) ∈ interior K := by
    apply hhalf
    · exact lt_of_lt_of_le (hφball _ (by positivity) (by linarith)) (min_le_right _ _)
    · rw [hφim]; positivity
  have hGK : G ⊆ interior K := by
    refine IsPreconnected.subset_left_of_subset_union isOpen_interior hKcl.isOpen_compl
      (Disjoint.mono_left interior_subset disjoint_compl_right) ?_
      ⟨_, mem_connectedComponentIn (hLD hz1), hz1K⟩ isPreconnected_connectedComponentIn
    intro z hz
    by_cases hzK : z ∈ K
    · by_cases hzi : z ∈ interior K
      · exact Or.inl hzi
      · exfalso
        have hzfr : z ∈ frontier K := ⟨subset_closure hzK, hzi⟩
        exact connectedComponentIn_subset _ _ hz (hfrX hzfr)
    · exact Or.inr hzK
  have hGb : Bornology.IsBounded G :=
    ((cVerts X).finite_toSet.isCompact_convexHull.isBounded).subset (hGK.trans interior_subset)
  have hmG : m ∈ closure G := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    set η := min (η0 / 2) (ε / (2 * ‖b - a‖)) with hηdef
    have hη : 0 < η := lt_min (by positivity) (by positivity)
    refine ⟨φ η, hLG ⟨η, ⟨hη, by linarith [min_le_left (η0 / 2) (ε / (2 * ‖b - a‖))]⟩, rfl⟩, ?_⟩
    rw [dist_comm, hφd η hη.le]
    have h1 : η ≤ ε / (2 * ‖b - a‖) := min_le_right _ _
    have h2 : ε / (2 * ‖b - a‖) * ‖b - a‖ = ε / 2 := by field_simp
    nlinarith
  exact ⟨_, ⟨⟨hG, hGb⟩, Finset.mem_filter.2 ⟨he, m, hm, hmG⟩⟩⟩


lemma mem_of_mem_cSides {S : Finset ℂ} {a b : ℂ} (h : s(a, b) ∈ cSides S) : a ∈ S ∧ b ∈ S := by
  obtain ⟨⟨a', b'⟩, hmem, he⟩ := Finset.mem_image.1 h
  have hs' : IsCSide S a' b' := (Finset.mem_filter.1 hmem).2
  rcases Sym2.eq_iff.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h1 ▸ hs'.1, h2 ▸ hs'.2.1⟩
  · exact ⟨h2 ▸ hs'.2.1, h1 ▸ hs'.1⟩

/-- **Every hull side bounds at most one cap.** -/
theorem cap_unique :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      ∀ p ∈ ccwHullSides X, ∀ F₁ F₂, IsCap X p.1 p.2 F₁ → IsCap X p.1 p.2 F₂ → F₁ = F₂ := by
  filter_upwards [augEdges_isPlaneGraph, augFace_polygon] with n hPa hpoly hfm X hX p hp F₁ F₂ h₁ h₂
  have hP := hPa hfm X hX
  have hcs := isCSide_of_ccw (mem_ccwHullSides.1 hp)
  set a := toC p.1
  set b := toC p.2
  have hab : a ≠ b := hcs.2.2.1
  have hne : b - a ≠ 0 := sub_ne_zero.2 hab.symm
  have hn : 0 < ‖b - a‖ := norm_pos_iff.2 hne
  set m := (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b with hmdef
  have hm : m ∈ openSegment ℝ a b := ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
  have key : ∀ F, IsCap X p.1 p.2 F → ∀ᶠ z in 𝓝 m, 0 < (wc a b z).im → z ∈ F := by
    intro F hF
    obtain ⟨S, -, -, -, hFint, hbd, -⟩ := hpoly hfm X hX F hF.1
    have hFo := isOpen_face hF.1.1
    have hFc : Convex ℝ F := hFint ▸ (convex_convexHull ℝ _).interior
    have habS : a ∈ S ∧ b ∈ S := by
      have := hF.2
      rw [hbd] at this
      exact mem_of_mem_cSides this
    have hFne : F.Nonempty := by
      obtain ⟨x, hx, hFx⟩ := mem_faces_iff.1 hF.1.1
      exact ⟨x, hFx ▸ mem_connectedComponentIn hx⟩
    have hcl : closure F = convexHull ℝ (S : Set ℂ) := by
      rw [hFint, (convex_convexHull ℝ _).closure_interior_eq_closure_of_nonempty_interior
        (hFint ▸ hFne), S.finite_toSet.isCompact_convexHull.isClosed.closure_eq]
    obtain ⟨c, hc⟩ := hFne
    have hcK : c ∈ interior (convexHull ℝ ((cVerts X : Finset ℂ) : Set ℂ)) :=
      interior_maximal (boundedFace_subset_hull hP hF.1.1 hF.1.2) hFo hc
    have ha : a ∈ closure F := by rw [hcl]; exact subset_convexHull ℝ _ habS.1
    have hb : b ∈ closure F := by rw [hcl]; exact subset_convexHull ℝ _ habS.2
    exact halfdisc hFc hFo ha hb hc hm (side_pos hcs hcK)
  obtain ⟨ε, hε, hE⟩ := Metric.eventually_nhds_iff.1 ((key F₁ h₁).and (key F₂ h₂))
  set η : ℝ := ε / (2 * ‖b - a‖) with hηdef
  have hη : 0 < η := by positivity
  set z := m + (η : ℂ) * I * (b - a) with hzdef
  have hz : dist z m < ε := by
    rw [dist_eq_norm, hzdef, add_sub_cancel_left, norm_mul, norm_mul, Complex.norm_real, norm_I,
      mul_one, Real.norm_of_nonneg hη.le]
    have : η * ‖b - a‖ = ε / 2 := by rw [hηdef]; field_simp
    rw [this]; linarith
  have hzpos : 0 < (wc a b z).im := by
    have hm0 := (mem_openSegment_wc hab hm).1
    have : wc a b z = wc a b m + (η : ℂ) * I := by
      simp only [hzdef, wc]; field_simp; ring
    rw [this, add_im, hm0]; simpa using hη
  have hz1 := (hE hz).1 hzpos
  have hz2 := (hE hz).2 hzpos
  rw [face_eq_component h₁.1.1 hz1, face_eq_component h₂.1.1 hz2]

/-- **Lemma 2.1 (caps).**  Every non-unit hull side `[v, w]` bounds exactly one cap.  The cap is
the interior of the convex hull of a set `S` of points of `X` in strictly convex position,
containing `v` and `w`; its boundary edges are exactly the sides of this polygon, and it has
`j + 1` sides where `j = returnLength X v w`. -/
theorem cap_polygon :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      ∀ p ∈ ccwHullSides X, 1 < dist p.1 p.2 →
        (∃! F, IsCap X p.1 p.2 F) ∧ ∀ F, IsCap X p.1 p.2 F →
          ∃ S : Finset ℂ, S ⊆ cVerts X ∧ toC p.1 ∈ S ∧ toC p.2 ∈ S ∧ 3 ≤ S.card ∧
            (∀ s ∈ S, s ∈ extremePoints ℝ (convexHull ℝ (S : Set ℂ))) ∧
            F = interior (convexHull ℝ (S : Set ℂ)) ∧
            bdryEdges (augEdges X) F = cSides S ∧ S.card = returnLength X p.1 p.2 + 1 := by
  filter_upwards [exists_cap, cap_unique, augFace_polygon] with n hex hun hpoly hfm X hX p hp hd
  obtain ⟨F0, hF0⟩ := hex hfm X hX p hp
  refine ⟨⟨F0, hF0, fun F hF => hun hfm X hX p hp F F0 hF hF0⟩, fun F hF => ?_⟩
  obtain ⟨S, hSV, h3, hext, hFint, hbd, hcard⟩ := hpoly hfm X hX F hF.1
  have habS : toC p.1 ∈ S ∧ toC p.2 ∈ S := by
    have := hF.2
    rw [hbd] at this
    exact mem_of_mem_cSides this
  refine ⟨S, hSV, habS.1, habS.2, h3, hext, hFint, hbd, ?_⟩
  have hex' : ∃ F, IsCap X p.1 p.2 F := ⟨F, hF⟩
  have hrl : returnLength X p.1 p.2 = (bdryEdges (augEdges X) F).card - 1 := by
    rw [returnLength, if_neg (ne_of_gt hd), dif_pos hex',
      hun hfm X hX p hp _ F hex'.choose_spec hF]
  rw [hrl, hcard]
  omega

/-! ## A cap has a single hull side -/

/-- A point of a strictly convex polygon on the line of a side is an endpoint of the side. -/
lemma eq_of_side_collinear {S : Finset ℂ} {a b c : ℂ} (hs : IsCSide S a b)
    (hext : ∀ s ∈ S, s ∈ extremePoints ℝ (convexHull ℝ (S : Set ℂ))) (hc : c ∈ S)
    (h0 : (wc a b c).im = 0) : c = a ∨ c = b := by
  have hab := hs.2.2.1
  have haK := subset_convexHull ℝ (S : Set ℂ) hs.1
  have hbK := subset_convexHull ℝ (S : Set ℂ) hs.2.1
  have hcK := subset_convexHull ℝ (S : Set ℂ) hc
  set t := (wc a b c).re with htdef
  have hce : c = a + (t : ℂ) * (b - a) := by
    have e1 := eq_param hab c
    have e2 : wc a b c = (t : ℂ) := Complex.ext (by simp [t]) (by simp [h0])
    rw [e1, e2]; ring
  rcases lt_trichotomy t 0 with ht | ht | ht
  · -- `a` lies strictly between `c` and `b`
    have hmem : a ∈ openSegment ℝ c b := by
      have h1t' : (1 : ℝ) - t ≠ 0 := by linarith
      refine ⟨1 / (1 - t), -t / (1 - t), by apply div_pos <;> linarith,
        by apply div_pos <;> linarith, by field_simp; ring, ?_⟩
      have h1t : (1 : ℂ) - t ≠ 0 := by
        intro h; have : ((1 - t : ℝ) : ℂ) = 0 := by push_cast; exact h
        have : (1 - t : ℝ) = 0 := by exact_mod_cast this
        linarith
      rw [Complex.real_smul, Complex.real_smul, hce]; push_cast; field_simp; ring
    exact Or.inl ((mem_extremePoints.1 (hext a hs.1)).2 c hcK b hbK hmem).1
  · left; rw [hce, ht]; simp
  · rcases lt_trichotomy t 1 with ht1 | ht1 | ht1
    · have hmem : c ∈ openSegment ℝ a b := by
        refine ⟨1 - t, t, by linarith, ht, by ring, ?_⟩
        rw [Complex.real_smul, Complex.real_smul, hce]; push_cast; ring
      exact Or.inl ((mem_extremePoints.1 (hext c hc)).2 a haK b hbK hmem).1.symm
    · right; rw [hce, ht1]; simp
    · have hmem : b ∈ openSegment ℝ a c := by
        refine ⟨(t - 1) / t, 1 / t, by apply div_pos <;> linarith, by apply div_pos <;> linarith,
          by field_simp; ring, ?_⟩
        have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (by linarith : t ≠ 0)
        rw [Complex.real_smul, Complex.real_smul, hce]; push_cast; field_simp; ring
      exact Or.inr ((mem_extremePoints.1 (hext b hs.2.1)).2 a haK c hcK hmem).2

lemma exists_cross_step {r : ℂ → ℂ → Prop} {f : ℂ → ℝ} (hf : ∀ x y, r x y → f x ≠ 0) {a b : ℂ}
    (h : Relation.ReflTransGen r a b) (ha : f a < 0) (hb : 0 < f b) :
    ∃ x y, r x y ∧ f x < 0 ∧ 0 < f y := by
  induction h with
  | refl => linarith
  | tail _ hbc ih =>
    rcases lt_or_gt_of_ne (hf _ _ hbc) with h | h
    · exact ⟨_, _, hbc, h, hb⟩
    · exact ih h

/-- The inside of a non-unit hull side avoids the drawing of the contact graph. -/
lemma hullSide_open_off_contact {X : Finset Plane} (hP : IsPlaneGraph (cVerts X) (augEdges X))
    {q : Plane × Plane} (hq : q ∈ ccwHullSides X) (hd : dist q.1 q.2 ≠ 1) {x : ℂ}
    (hx : x ∈ openSegment ℝ (toC q.1) (toC q.2)) : x ∉ drawing (cVerts X) (cUnitEdges X) := by
  have he : s(toC q.1, toC q.2) ∈ augEdges X :=
    Finset.mem_union_right _ (Finset.mem_image.2 ⟨q, hq, rfl⟩)
  have hab : toC q.1 ≠ toC q.2 := (isCSide_of_ccw (mem_ccwHullSides.1 hq)).2.2.1
  have hxs := openSegment_subset_segment ℝ _ _ hx
  have hend : x ∉ s(toC q.1, toC q.2) := by
    intro h
    rcases Sym2.mem_iff.1 h with h | h
    · rw [h] at hx; exact hab (left_mem_openSegment_iff.1 hx)
    · rw [h] at hx; exact hab (right_mem_openSegment_iff.1 hx)
  rintro (h | h)
  · exact hend (hP.vertex_mem _ he x h hxs)
  · obtain ⟨e, he', hxe⟩ := Set.mem_iUnion₂.1 h
    by_cases hee : s(toC q.1, toC q.2) = e
    · subst hee
      rw [cUnitEdges, mem_unitPairs, dist_toC] at he'
      exact hd he'.2.2
    · exact hend (hP.inter _ he e (Finset.mem_union_left _ he') hee x hxs hxe)

/-- **A convex face has at most one non-unit hull side.**  Otherwise the chord joining the
midpoints of two such sides would separate the contact graph. -/
theorem hullSides_of_polygon_eq {X : Finset Plane} (hP : IsPlaneGraph (cVerts X) (augEdges X))
    (hconn : GraphConnected (cVerts X) (cUnitEdges X)) {F : Set ℂ} {S : Finset ℂ}
    (hF : F ∈ faces (cVerts X) (augEdges X)) (hFint : F = interior (convexHull ℝ (S : Set ℂ)))
    (hSV : S ⊆ cVerts X) (hext : ∀ s ∈ S, s ∈ extremePoints ℝ (convexHull ℝ (S : Set ℂ)))
    {p p' : Plane × Plane} (hp : p ∈ ccwHullSides X) (hp' : p' ∈ ccwHullSides X)
    (hd : dist p.1 p.2 ≠ 1) (hd' : dist p'.1 p'.2 ≠ 1)
    (h1 : s(toC p.1, toC p.2) ∈ cSides S) (h2 : s(toC p'.1, toC p'.2) ∈ cSides S) :
    s(toC p.1, toC p.2) = s(toC p'.1, toC p'.2) := by
  by_contra hne
  have hcs := isCSide_of_ccw (mem_ccwHullSides.1 hp)
  have hcs' := isCSide_of_ccw (mem_ccwHullSides.1 hp')
  set a := toC p.1 with ha_def
  set b := toC p.2 with hb_def
  set a' := toC p'.1 with ha'_def
  set b' := toC p'.2 with hb'_def
  have habS := mem_of_mem_cSides h1
  have habS' := mem_of_mem_cSides h2
  have hsS : IsCSide S a b := ⟨habS.1, habS.2, hcs.2.2.1, fun c hc => hcs.2.2.2 c (hSV hc)⟩
  have hsS' : IsCSide S a' b' := ⟨habS'.1, habS'.2, hcs'.2.2.1, fun c hc => hcs'.2.2.2 c (hSV hc)⟩
  have hab := hcs.2.2.1
  have hab' := hcs'.2.2.1
  have hFo := isOpen_face hF
  have hFne : F.Nonempty := by
    obtain ⟨x, hx, hFx⟩ := mem_faces_iff.1 hF
    exact ⟨x, hFx ▸ mem_connectedComponentIn hx⟩
  have hFc : Convex ℝ F := hFint ▸ (convex_convexHull ℝ _).interior
  have hcl : closure F = convexHull ℝ (S : Set ℂ) := by
    rw [hFint, (convex_convexHull ℝ _).closure_interior_eq_closure_of_nonempty_interior
      (hFint ▸ hFne), S.finite_toSet.isCompact_convexHull.isClosed.closure_eq]
  set m := (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b with hmdef
  set m' := (1 / 2 : ℝ) • a' + (1 / 2 : ℝ) • b' with hm'def
  have hm : m ∈ openSegment ℝ a b := ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
  have hm' : m' ∈ openSegment ℝ a' b' :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
  have hm0 := (mem_openSegment_wc hab hm).1
  have hm0' := (mem_openSegment_wc hab' hm').1
  have hpos : ∀ {a b a' b' : ℂ}, IsCSide S a b → IsCSide S a' b' → s(a, b) ≠ s(a', b') →
      0 < (wc a b ((1 / 2 : ℝ) • a' + (1 / 2 : ℝ) • b')).im := by
    intro a b a' b' hs hs' hne
    have e1 := hs.2.2.2 a' hs'.1
    have e2 := hs.2.2.2 b' hs'.2.1
    rw [wc_combo _ _ _ _ (by norm_num)]
    simp only [add_im, im_ofReal_mul]
    by_contra hle
    push_neg at hle
    have f1 : (wc a b a').im = 0 := by linarith
    have f2 : (wc a b b').im = 0 := by linarith
    rcases eq_of_side_collinear hs hext hs'.1 f1 with h | h <;>
      rcases eq_of_side_collinear hs hext hs'.2.1 f2 with h' | h'
    · exact hs'.2.2.1 (h.trans h'.symm)
    · exact hne (by rw [h, h'])
    · exact hne (by rw [h, h', Sym2.eq_swap])
    · exact hs'.2.2.1 (h.trans h'.symm)
  have hP1 : 0 < (wc a b m').im := hpos hsS hsS' hne
  have hP2 : 0 < (wc a' b' m).im := hpos hsS' hsS (Ne.symm hne)
  have hm'cl : m' ∈ closure F := by
    rw [hcl]
    exact (convex_convexHull ℝ _) (subset_convexHull ℝ _ habS'.1) (subset_convexHull ℝ _ habS'.2)
      (by norm_num) (by norm_num) (by norm_num)
  -- the open chord `(m, m')` lies in `F`
  have hchord : ∀ τ : ℝ, 0 < τ → τ < 1 → m + (τ : ℂ) * (m' - m) ∈ F := by
    intro τ hτ0 hτ1
    obtain ⟨c, hc⟩ := hFne
    have hcpos := side_pos hsS (hFint ▸ hc)
    have ha : a ∈ closure F := by rw [hcl]; exact subset_convexHull ℝ _ habS.1
    have hb : b ∈ closure F := by rw [hcl]; exact subset_convexHull ℝ _ habS.2
    obtain ⟨ε, hε, hE⟩ := Metric.eventually_nhds_iff.1 (halfdisc hFc hFo ha hb hc hm hcpos)
    set t0 := min (τ / 2) (ε / (2 * (‖m' - m‖ + 1))) with ht0def
    have ht0 : 0 < t0 := lt_min (by linarith) (by positivity)
    have ht0τ : t0 < τ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hz : m + (t0 : ℂ) * (m' - m) ∈ F := by
      apply hE
      · rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg ht0.le]
        have h1 : t0 ≤ ε / (2 * (‖m' - m‖ + 1)) := min_le_right _ _
        have h2 : 0 ≤ ‖m' - m‖ := norm_nonneg _
        calc t0 * ‖m' - m‖ ≤ ε / (2 * (‖m' - m‖ + 1)) * ‖m' - m‖ := by gcongr
          _ < ε := by rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith
      · rw [wc_affine, add_im, hm0, zero_add, im_ofReal_mul, sub_im, hm0, sub_zero]
        exact mul_pos ht0 hP1
    have hmem : m + (τ : ℂ) * (m' - m) ∈ openSegment ℝ (m + (t0 : ℂ) * (m' - m)) m' := by
      have h1t : (1 : ℝ) - t0 ≠ 0 := by linarith
      refine ⟨(1 - τ) / (1 - t0), (τ - t0) / (1 - t0), by apply div_pos <;> linarith,
        by apply div_pos <;> linarith, by field_simp; ring, ?_⟩
      have h1t' : (1 : ℂ) - t0 ≠ 0 := by
        intro h; apply h1t; exact_mod_cast (show ((1 - t0 : ℝ) : ℂ) = 0 by push_cast; exact h)
      rw [Complex.real_smul, Complex.real_smul]; push_cast; field_simp; ring
    have hzI : m + (t0 : ℂ) * (m' - m) ∈ interior F := by rwa [hFo.interior_eq]
    have := hFc.openSegment_interior_closure_subset_interior hzI hm'cl hmem
    rwa [hFo.interior_eq] at this
  have hmC := hullSide_open_off_contact hP hp hd hm
  have hmC' := hullSide_open_off_contact hP hp' hd' hm'
  have hFC : F ⊆ (drawing (cVerts X) (cUnitEdges X))ᶜ := fun z hz hzD =>
    face_subset_compl hF hz (drawing_mono Finset.subset_union_left hzD)
  have hmm : m ≠ m' := by
    intro h; have := hP1; rw [← h, hm0] at this; exact lt_irrefl _ this
  set f : ℂ → ℝ := fun z => (wc m m' z).im with hfdef
  -- points of the hull on the line `m m'` lie on the chord, hence off the contact drawing
  have hline : ∀ x, 0 ≤ (wc a b x).im → 0 ≤ (wc a' b' x).im → f x = 0 →
      x ∉ drawing (cVerts X) (cUnitEdges X) := by
    intro x hx1 hx2 hfx
    set t := (wc m m' x).re with htdef
    have hxe : x = m + (t : ℂ) * (m' - m) := by
      have e1 := eq_param hmm x
      have e2 : wc m m' x = (t : ℂ) := Complex.ext (by simp [t]) (by simpa [f] using hfx)
      rw [e1, e2]; ring
    have h1 : (wc a b x).im = t * (wc a b m').im := by
      rw [hxe, wc_affine, add_im, hm0, zero_add, im_ofReal_mul, sub_im, hm0, sub_zero]
    have h2 : (wc a' b' x).im = (1 - t) * (wc a' b' m).im := by
      have : x = m' + ((1 - t : ℝ) : ℂ) * (m - m') := by rw [hxe]; push_cast; ring
      rw [this, wc_affine, add_im, hm0', zero_add, im_ofReal_mul, sub_im, hm0', sub_zero]
    have ht0 : 0 ≤ t := by
      by_contra h; push_neg at h; rw [h1] at hx1; nlinarith
    have ht1 : t ≤ 1 := by
      by_contra h; push_neg at h; rw [h2] at hx2; nlinarith
    rcases ht0.lt_or_eq with ht0 | ht0
    · rcases ht1.lt_or_eq with ht1 | ht1
      · have := hchord t ht0 ht1
        rw [← hxe] at this
        exact hFC this
      · rw [hxe, ht1]; simpa using hmC'
    · rw [hxe, ← ht0]; simpa using hmC
  have hcV : ∀ x ∈ cVerts X, 0 ≤ (wc a b x).im ∧ 0 ≤ (wc a' b' x).im := fun x hx =>
    ⟨hcs.2.2.2 x hx, hcs'.2.2.2 x hx⟩
  have hfb : f b ≠ 0 := fun h =>
    hline b (hcV b hcs.2.1).1 (hcV b hcs.2.1).2 h (Or.inl hcs.2.1)
  have hfa : f a = -(f b) := by
    have : a - m = -(b - m) := by
      rw [hmdef, Complex.real_smul, Complex.real_smul]; push_cast; ring
    simp only [hfdef, wc, this, neg_div, neg_im]
  have hfnz : ∀ x y, s(x, y) ∈ cUnitEdges X → f x ≠ 0 := by
    intro x y hxy h
    have hxV := (mem_unitPairs.1 hxy).1
    exact hline x (hcV x hxV).1 (hcV x hxV).2 h (Or.inl hxV)
  have hsym : Symmetric (fun x y => s(x, y) ∈ cUnitEdges X) := by
    intro x y h; simpa [Sym2.eq_swap] using h
  have hpath := hconn.2 a hcs.1 b hcs.2.1
  obtain ⟨x, y, hxy, hfx, hfy⟩ : ∃ x y, s(x, y) ∈ cUnitEdges X ∧ f x < 0 ∧ 0 < f y := by
    rcases lt_or_gt_of_ne hfb with h | h
    · exact exists_cross_step hfnz (Relation.ReflTransGen.symmetric hsym hpath) h
        (by linarith)
    · exact exists_cross_step hfnz hpath (by linarith) h
  obtain ⟨hxV, hyV, -⟩ := mem_unitPairs.1 hxy
  set l : ℝ := f x / (f x - f y) with hldef
  have hl0 : 0 < l := div_pos_of_neg_of_neg hfx (by linarith)
  have hl1 : l < 1 := by rw [hldef, div_lt_one_of_neg (by linarith)]; linarith
  set z := x + (l : ℂ) * (y - x) with hzdef
  have hfz : f z = 0 := by
    simp only [hfdef, hzdef]
    rw [wc_affine, add_im, im_ofReal_mul, sub_im]
    change f x + l * (f y - f x) = 0
    have hden : f x - f y ≠ 0 := by linarith
    rw [hldef]; field_simp; ring
  have hhalf : ∀ {u v : ℂ}, 0 ≤ (wc u v x).im → 0 ≤ (wc u v y).im → 0 ≤ (wc u v z).im := by
    intro u v hx hy
    rw [hzdef, wc_affine, add_im, im_ofReal_mul, sub_im]
    nlinarith
  have hzD : z ∈ drawing (cVerts X) (cUnitEdges X) := by
    refine Or.inr (Set.mem_iUnion₂.2 ⟨s(x, y), hxy, ?_⟩)
    rw [edgeSeg_mk, hzdef]
    have := mem_segment_line x (y - x) (a := 0) (b := 1) (t := l)
      (Set.mem_uIcc.2 (Or.inl ⟨hl0.le, hl1.le⟩))
    simpa [Complex.real_smul] using this
  exact hline z (hhalf (hcV x hxV).1 (hcV y hyV).1) (hhalf (hcV x hxV).2 (hcV y hyV).2) hfz hzD

/-- Lemma 2.1 (caps, continued): every cap has exactly one hull side on its boundary; its other
sides are unit edges of `X`. -/
theorem cap_other_sides_unit :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      ∀ p ∈ ccwHullSides X, 1 < dist p.1 p.2 → ∀ F, IsCap X p.1 p.2 F →
        ∀ e ∈ bdryEdges (augEdges X) F, e ≠ s(toC p.1, toC p.2) → e ∈ cUnitEdges X := by
  filter_upwards [augEdges_isPlaneGraph, cUnitEdges_connected, augFace_polygon] with
    n hPa hconn hpoly hfm X hX p hp hd F hF e he hne
  obtain ⟨S, hSV, -, hext, hFint, hbd, -⟩ := hpoly hfm X hX F hF.1
  rcases Finset.mem_union.1 (Finset.mem_filter.1 he).1 with hu | hh
  · exact hu
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hh
  have hs := mem_ccwHullSides.1 hq
  by_cases hd1 : dist q.1 q.2 = 1
  · rw [cUnitEdges, mem_unitPairs]
    exact ⟨Finset.mem_image_of_mem _ (mem_of_mem_hullVertices hs.1),
      Finset.mem_image_of_mem _ (mem_of_mem_hullVertices hs.2.1), by rw [dist_toC]; exact hd1⟩
  · exfalso
    have h1 : s(toC p.1, toC p.2) ∈ cSides S := hbd ▸ hF.2
    have h2 : s(toC q.1, toC q.2) ∈ cSides S := hbd ▸ he
    exact hne (hullSides_of_polygon_eq (hPa hfm X hX) (hconn hfm X hX) hF.1.1 hFint hSV hext hp hq
      (ne_of_gt hd) hd1 h1 h2).symm

/-! ## Consequences for the counts -/

/-- Every non-unit hull side closes a return of at least two unit edges. -/
theorem two_le_returnLength :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      ∀ p ∈ ccwHullSides X, dist p.1 p.2 ≠ 1 → 2 ≤ returnLength X p.1 p.2 := by
  filter_upwards [cap_polygon] with n hcap hfm X hX p hp hd
  have hgt : 1 < dist p.1 p.2 := by
    have hs := mem_ccwHullSides.1 hp
    have h1 := hX.1.2 p.1 (mem_of_mem_hullVertices hs.1) p.2 (mem_of_mem_hullVertices hs.2.1)
      hs.2.2.1
    exact lt_of_le_of_ne h1 (Ne.symm hd)
  obtain ⟨⟨F, hF, -⟩, hpoly⟩ := hcap hfm X hX p hp hgt
  obtain ⟨S, -, -, -, h3, -, -, -, hcard⟩ := hpoly F hF
  omega

/-- `c₁ = u`. -/
theorem hullReturns_one_eventually :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      hullReturns X 1 = numUnitHullSides X := by
  filter_upwards [two_le_returnLength] with n h hfm X hX
  exact hullReturns_one (h hfm X hX)

/-- `ℓ = 2b - u + ρ`. -/
theorem outerWalkLength_eq_eventually :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      (outerWalkLength X : ℤ) =
        2 * (hullVertices X).card - numUnitHullSides X + returnExcess X := by
  filter_upwards [two_le_returnLength, eventually_not_collinear] with n h hcol hfm X hX
  rw [outerWalkLength_eq (h hfm X hX), card_ccwHullSides (three_le_card_hullVertices (hcol X hX))]

end Erdos99

end

end Caps

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `CapCount`
-/

section CapCount

/-!
# Counting arrivals at caps (Verification Guide §8.3, §9.3)

* `convex_return_forward_le`: in a convex polygon with one side `[v, w]` of length at least one and
  all other sides of unit length (the cap of a hull side, Lemma 2.1), at most `2 (j - 2) / 3` of
  the `j` other sides, oriented counterclockwise, have direction within `arccos (9/10)` of the
  direction of `v → w` (the return capacities `return_capacity`, `return_capacity_three`,
  `return_capacity_le_two` of §8.3, applied to the return path `v → … → w`, along which these sides
  are backward edges).
* `cap_forward_sides_le`: the same for the cap of a non-unit hull side of an optimal
  configuration.

The landing lemma `cap_landing` and the cap capacity `good_cap_tokens_le` are in
`CapLanding`.
-/

open scoped BigOperators Real
open Filter Topology EstablishedExternalResults

@[expose] public noncomputable section

open Classical

namespace Erdos99

open LocalCapacity

/-- `u (i + m t) = u i` for an `m`-periodic sequence. -/
lemma periodic_add_mul {u : ℕ → ℂ} {m : ℕ} (hper : ∀ i, u (i + m) = u i) (i t : ℕ) :
    u (i + m * t) = u i := by
  induction t with
  | zero => simp
  | succ t ih => rw [Nat.mul_succ, ← add_assoc, hper, ih]

/-- **Forward sides of a convex return** (§8.3).  Let `S` be a convex polygon (in strictly convex
position, with nonempty interior) with a counterclockwise side `v → w` of length at least one,
all of whose other sides are unit, and whose vertices are pairwise at distance at least one.  Then
the counterclockwise sides `a → b` other than `v → w` with `⟨b - a, (w - v)/|w - v|⟩ ≥ 9/10` number
at most `2 (j - 2)/3`, where `j = |S| - 1` is the number of the other sides. -/
theorem convex_return_forward_le {S : Finset ℂ}
    (hext : ∀ s ∈ S, s ∈ Set.extremePoints ℝ (convexHull ℝ (S : Set ℂ)))
    (hint : (interior (convexHull ℝ (S : Set ℂ))).Nonempty) {v w : Plane}
    (hvw : IsCSide S (toC v) (toC w)) (hlen : 1 ≤ dist v w)
    (hunit : ∀ a b, IsCSide S a b → (a, b) ≠ (toC v, toC w) → ‖b - a‖ = 1)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → 1 ≤ ‖a - b‖)
    (E : Finset (ℂ × ℂ)) (hE : ∀ ab ∈ E, IsCSide S ab.1 ab.2 ∧ ab ≠ (toC v, toC w) ∧
      9 / 10 ≤ inner ℝ (toC.symm (ab.2 - ab.1)) (sideDir (v, w))) :
    (E.card : ℝ) ≤ 2 * ((S.card - 1 - 2 : ℕ) : ℝ) / 3 := by
  obtain ⟨u, hper, huS, hinj, hside⟩ := PolyCycle.exists_cyclic_enum hext hint
  set m := S.card with hmdef
  have hm3 : 3 ≤ m := three_le_card_of_interior hint
  obtain ⟨i0, hu0, hu1⟩ := (hside _ _).1 hvw
  set u' : ℕ → ℂ := fun k => u (k + i0) with hu'
  have hper' : ∀ k, u' (k + m) = u' k := by
    intro k
    simp only [hu']
    rw [show k + m + i0 = k + i0 + m by ring]
    exact hper _
  have hmod' := periodic_mod hper'
  have hinj' : Set.InjOn u' (Set.Iio m) := by
    intro a ha b hb hab
    simp only [Set.mem_Iio] at ha hb
    simp only [hu'] at hab
    rw [← periodic_mod hper (a + i0), ← periodic_mod hper (b + i0)] at hab
    have h := hinj (Set.mem_Iio.2 (Nat.mod_lt _ (by omega)))
      (Set.mem_Iio.2 (Nat.mod_lt _ (by omega))) hab
    have h2 : a % m = b % m := Nat.ModEq.add_right_cancel' i0 h
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h2
  have hside' : ∀ a b, IsCSide S a b ↔ ∃ k, u' k = a ∧ u' (k + 1) = b := by
    intro a b
    rw [hside]
    constructor
    · rintro ⟨i, hi1, hi2⟩
      refine ⟨i + m * i0 - i0, ?_, ?_⟩
      · simp only [hu']
        rw [show i + m * i0 - i0 + i0 = i + m * i0 by
          have : i0 ≤ m * i0 := Nat.le_mul_of_pos_left _ (by omega)
          omega, periodic_add_mul hper, hi1]
      · simp only [hu']
        rw [show i + m * i0 - i0 + 1 + i0 = i + 1 + m * i0 by
          have : i0 ≤ m * i0 := Nat.le_mul_of_pos_left _ (by omega)
          omega, periodic_add_mul hper, hi2]
    · rintro ⟨k, hk1, hk2⟩
      refine ⟨k + i0, hk1, ?_⟩
      simp only [hu'] at hk2
      rw [show k + i0 + 1 = k + 1 + i0 by ring]
      exact hk2
  have hv : u' 0 = toC v := by simp only [hu', zero_add]; exact hu0
  have hw : u' 1 = toC w := by simp only [hu']; rw [add_comm]; exact hu1
  have hzero : ∀ k, u' k = toC v → k % m = 0 := by
    intro k hk
    have h1 : u' (k % m) = u' 0 := by rw [hmod', hk, hv]
    exact hinj' (Set.mem_Iio.2 (Nat.mod_lt _ (by omega))) (Set.mem_Iio.2 (by omega)) h1
  -- the return path `v → … → w`
  set j := m - 1 with hj
  set P : ℕ → Plane := fun i => toC.symm (u' (m - i)) with hP
  have hP0 : P 0 = v := by
    simp only [hP, Nat.sub_zero]
    rw [show m = 0 + m by ring, hper', hv, LinearIsometryEquiv.symm_apply_apply]
  have hPj : P j = w := by
    simp only [hP]
    rw [show m - j = 1 by omega, hw, LinearIsometryEquiv.symm_apply_apply]
  have hPunit : ∀ i < j, ‖P (i + 1) - P i‖ = 1 := by
    intro i hi
    have hs : IsCSide S (u' (m - i - 1)) (u' (m - i - 1 + 1)) := (hside' _ _).2 ⟨_, rfl, rfl⟩
    have hne : (u' (m - i - 1), u' (m - i - 1 + 1)) ≠ (toC v, toC w) := by
      intro h
      have := hzero _ (Prod.mk.inj h).1
      rw [Nat.mod_eq_of_lt (by omega)] at this
      omega
    have h1 := hunit _ _ hs hne
    simp only [hP]
    rw [← map_sub, LinearIsometryEquiv.norm_map, norm_sub_rev,
      show m - i = m - i - 1 + 1 by omega, show m - (i + 1) = m - i - 1 by omega]
    exact h1
  have hvw' : v ≠ w := by
    intro h; rw [h, dist_self] at hlen; norm_num at hlen
  set c := sideDir (v, w) with hc
  have hcn : ‖c‖ = 1 := norm_sideDir hvw'
  have hchord : 1 ≤ inner ℝ (P j - P 0) c := by
    rw [hPj, hP0, hc, sideDir]
    simp only
    rw [inner_smul_right, real_inner_self_eq_norm_sq]
    have hn : 0 < ‖w - v‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hvw'))
    have hn1 : 1 ≤ ‖w - v‖ := by rw [← dist_eq_norm, dist_comm]; exact hlen
    rw [show ‖w - v‖⁻¹ * ‖w - v‖ ^ 2 = ‖w - v‖ by field_simp]
    exact hn1
  -- the indices of the forward sides
  have hidx : ∀ ab ∈ E, ∃ k, 1 ≤ k ∧ k < m ∧ u' k = ab.1 ∧ u' (k + 1) = ab.2 := by
    intro ab hab
    obtain ⟨hs, hne, -⟩ := hE ab hab
    obtain ⟨k, hk1, hk2⟩ := (hside' _ _).1 hs
    refine ⟨k % m, ?_, Nat.mod_lt _ (by omega), by rw [hmod', hk1], ?_⟩
    · by_contra h0
      have h0' : k % m = 0 := by omega
      apply hne
      have e1 : ab.1 = toC v := by rw [← hk1, ← hmod', h0', hv]
      have e2 : ab.2 = toC w := by
        rw [← hk2, ← hmod', Nat.add_mod, h0', zero_add, Nat.mod_mod, hmod' 1, hw]
      exact Prod.ext e1 e2
    · rw [← hk2, ← hmod' (k + 1), ← hmod' (k % m + 1), Nat.add_mod, Nat.mod_mod,
        ← Nat.add_mod]
  choose! kf hkf1 hkf2 hkf3 hkf4 using hidx
  set N := E.image (fun ab => m - 1 - kf ab) with hN
  have hNinj : Set.InjOn (fun ab => m - 1 - kf ab) E := by
    intro ab hab ab' hab' h
    simp only at h
    have hk : kf ab = kf ab' := by
      have := hkf2 ab hab; have := hkf2 ab' hab'; have := hkf1 ab hab; have := hkf1 ab' hab'
      omega
    exact Prod.ext (by rw [← hkf3 ab hab, ← hkf3 ab' hab', hk])
      (by rw [← hkf4 ab hab, ← hkf4 ab' hab', hk])
  have hNcard : N.card = E.card := Finset.card_image_of_injOn hNinj
  have hNsub : N ⊆ Finset.range j := by
    intro i hi
    obtain ⟨ab, hab, rfl⟩ := Finset.mem_image.1 hi
    have := hkf1 ab hab; have := hkf2 ab hab
    exact Finset.mem_range.2 (by omega)
  have hNdir : ∀ i ∈ N, inner ℝ (P (i + 1) - P i) c ≤ -(9 / 10) := by
    intro i hi
    obtain ⟨ab, hab, rfl⟩ := Finset.mem_image.1 hi
    have h1 := hkf1 ab hab
    have h2 := hkf2 ab hab
    have e : P (m - 1 - kf ab + 1) - P (m - 1 - kf ab) = -toC.symm (ab.2 - ab.1) := by
      simp only [hP]
      rw [show m - (m - 1 - kf ab + 1) = kf ab by omega,
        show m - (m - 1 - kf ab) = kf ab + 1 by omega, hkf3 ab hab, hkf4 ab hab, ← map_sub,
        ← map_neg, neg_sub]
    rw [e, inner_neg_left]
    linarith [(hE ab hab).2.2]
  rw [← hNcard]
  rcases (show j ≤ 2 ∨ j = 3 ∨ 4 ≤ j by omega) with h2 | h3 | h4
  · rw [return_capacity_le_two h2 hPunit hcn hchord (by norm_num : (0 : ℝ) < 9 / 10) hNsub hNdir]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  · have hsepP : ∀ a b, a ≤ 3 → b ≤ 3 → a ≠ b → 1 ≤ ‖P a - P b‖ := by
      intro a b ha hb hab
      simp only [hP]
      rw [← map_sub, LinearIsometryEquiv.norm_map]
      have hm4 : m = 4 := by omega
      refine hsep _ (huS _) _ (huS _) (fun h => hab ?_)
      have h' : u' ((m - a) % m) = u' ((m - b) % m) := by rw [hmod', hmod']; exact h
      have := hinj' (Set.mem_Iio.2 (Nat.mod_lt _ (by omega)))
        (Set.mem_Iio.2 (Nat.mod_lt _ (by omega))) h'
      have key : (4 - a) % 4 = (4 - b) % 4 := by rw [← hm4]; exact this
      omega
    rw [h3] at hPunit hchord hNsub
    rw [return_capacity_three hPunit hsepP hcn hchord (le_refl _) hNsub hNdir]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  · have := return_capacity h4 hPunit hcn hchord (le_refl _) hNsub hNdir
    have hcast : ((m - 1 - 2 : ℕ) : ℝ) = (j : ℝ) - 2 := by
      rw [show m - 1 - 2 = j - 2 by omega, Nat.cast_sub (by omega)]
      norm_num
    rw [hcast]
    exact this

/-- A side `a → b` of a face `F = int conv S` with `F` on its left is a counterclockwise side of
`S`. -/
lemma isCSide_of_left {E : Finset (Sym2 ℂ)} {F : Set ℂ} {S : Finset ℂ}
    (hFint : F = interior (convexHull ℝ (S : Set ℂ))) (hbd : bdryEdges E F = cSides S)
    (hne : F.Nonempty) {a b : ℂ} (hmem : s(a, b) ∈ bdryEdges E F)
    (hleft : ∀ z ∈ F, 0 < (wc a b z).im) : IsCSide S a b := by
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

/-- A *forward side* of the cap `F` of the hull side `p`: an oriented boundary edge `a → b` of `F`
other than `p`, with `F` on its left, whose direction is within `arccos (9/10)` of that of `p`.
(Along the return path from `p.1` to `p.2` it is a backward edge.) -/
def IsCapForward (X : Finset Plane) (p : Plane × Plane) (F : Set ℂ) (ab : ℂ × ℂ) : Prop :=
  s(ab.1, ab.2) ∈ bdryEdges (augEdges X) F ∧ s(ab.1, ab.2) ≠ s(toC p.1, toC p.2) ∧
    (∀ z ∈ F, 0 < (wc ab.1 ab.2 z).im) ∧
    9 / 10 ≤ inner ℝ (toC.symm (ab.2 - ab.1)) (sideDir p)

/-- **The cap capacity** (§8.3).  Eventually, the forward sides of the cap of a non-unit hull side
`p` number at most `2 (j - 2)/3`, where `j` is the length of its return. -/
theorem cap_forward_sides_le :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      ∀ p ∈ ccwHullSides X, 1 < dist p.1 p.2 → ∀ F, IsCap X p.1 p.2 F →
      ∀ E : Finset (ℂ × ℂ), (∀ ab ∈ E, IsCapForward X p F ab) →
      (E.card : ℝ) ≤ 2 * ((returnLength X p.1 p.2 - 2 : ℕ) : ℝ) / 3 := by
  filter_upwards [cap_polygon, cap_other_sides_unit] with n hcap hother hfm X hX p hp hd F hF E hE
  obtain ⟨-, hpoly⟩ := hcap hfm X hX p hp hd
  obtain ⟨S, hSV, hpS, hqS, h3, hext, hFint, hbd, hcard⟩ := hpoly F hF
  have hne : F.Nonempty := by
    obtain ⟨x, hx, hFx⟩ := mem_faces_iff.1 hF.1.1
    exact ⟨x, hFx ▸ mem_connectedComponentIn hx⟩
  have hint : (interior (convexHull ℝ (S : Set ℂ))).Nonempty := hFint ▸ hne
  have hccw := isCSide_of_ccw (mem_ccwHullSides.1 hp)
  have hvw : IsCSide S (toC p.1) (toC p.2) :=
    ⟨hpS, hqS, hccw.2.2.1, fun c hc => hccw.2.2.2 c (hSV hc)⟩
  have hrl : returnLength X p.1 p.2 - 2 = S.card - 1 - 2 := by omega
  rw [hrl]
  refine convex_return_forward_le hext hint hvw hd.le ?_ ?_ E ?_
  · intro a b hs hne'
    have hmem : s(a, b) ∈ bdryEdges (augEdges X) F := by
      rw [hbd]
      exact Finset.mem_image.2 ⟨(a, b), Finset.mem_filter.2
        ⟨Finset.mem_product.2 ⟨hs.1, hs.2.1⟩, hs⟩, rfl⟩
    have hsne : s(a, b) ≠ s(toC p.1, toC p.2) := by
      intro he
      rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hne' rfl
      · obtain ⟨z, hz⟩ := hint
        have h1 := side_pos hs hz
        have h2 := side_pos hvw hz
        rw [wc_im_swap] at h1
        linarith
    have hu := hother hfm X hX p hp hd F hF _ hmem hsne
    have hdu := (mem_unitPairs.1 hu).2.2
    rw [← dist_eq_norm, dist_comm]
    exact hdu
  · intro a ha b hb hab
    have ha' := (mem_cVerts.1 (hSV ha))
    have hb' := (mem_cVerts.1 (hSV hb))
    have := hX.1.2 _ ha' _ hb' (fun h => hab (toC.symm.injective h))
    rwa [← dist_toC, LinearIsometryEquiv.apply_symm_apply,
      LinearIsometryEquiv.apply_symm_apply, dist_eq_norm] at this
  · intro ab hab
    obtain ⟨hmem, hsne, hleft, hdir⟩ := hE ab hab
    refine ⟨isCSide_of_left hFint hbd hne hmem hleft, fun h => hsne (by rw [h]), hdir⟩

end Erdos99

end

end CapCount

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `FaceSides`
-/

section FaceSides

/-!
# The two sides of an edge of the augmented graph (WP3)

For a large optimal set `X` under finite multiplicity:

* `ncard_faces_eq`: a plane graph has exactly one unbounded face, so
  `#faces = #bounded faces + 1`;
* `frontier_cHull_cases`: a boundary point of the hull of `X` is a point of `X` or lies inside a
  hull side;
* `augSides X e`: the bounded faces of the augmented graph having the edge `e` on their boundary;
* `augSides_hullSide`: a hull side bounds exactly one bounded face of the augmented graph (its cap);
* `augSides_interior`: every other unit edge bounds exactly two bounded faces of the augmented
  graph;
* `bdryEdges_aug_contact`: the boundary edges of a bounded face of the contact graph are the same
  whether computed in the contact graph or in the augmented graph.
-/

open scoped BigOperators Real
open EstablishedExternalResults Set Complex Filter Topology Metric

@[expose] public noncomputable section

open Classical

namespace Erdos99

/-! ## One unbounded face -/

/-- The complement of a closed disc in `ℂ` is preconnected (it is the image of a punctured disc
under inversion). -/
lemma isPreconnected_compl_closedBall_zero (R : ℝ) (hR : 0 < R) :
    IsPreconnected (closedBall (0 : ℂ) R)ᶜ := by
  have h := (isPreconnected_ball_diff_singleton (0 : ℂ) R⁻¹).image (fun w : ℂ => w⁻¹)
    (continuousOn_inv₀.mono fun w hw => hw.2)
  convert h using 1
  ext z
  simp only [mem_compl_iff, mem_closedBall, dist_zero_right, not_le, mem_image, mem_diff,
    mem_ball, mem_singleton_iff]
  constructor
  · intro hz
    have hz0 : z ≠ 0 := by rintro rfl; simp at hz; linarith
    refine ⟨z⁻¹, ⟨?_, inv_ne_zero hz0⟩, inv_inv z⟩
    rw [norm_inv]
    exact inv_strictAnti₀ hR hz
  · rintro ⟨w, ⟨hw, hw0⟩, rfl⟩
    rw [norm_inv]
    have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
    calc R = (R⁻¹)⁻¹ := (inv_inv R).symm
      _ < ‖w‖⁻¹ := inv_strictAnti₀ hwpos hw

/-- **A plane graph has exactly one unbounded face**: the number of faces is the number of bounded
faces plus one. -/
theorem ncard_faces_eq {V : Finset ℂ} {E : Finset (Sym2 ℂ)} (hfin : (faces V E).Finite) :
    (faces V E).ncard = (boundedFaces V E).ncard + 1 := by
  have hc : IsCompact (drawing V E) := by
    refine V.finite_toSet.isCompact.union (E.finite_toSet.isCompact_biUnion fun e _ => ?_)
    induction e using Sym2.ind with
    | _ a b => rw [edgeSeg_mk, segment_eq_image]; exact isCompact_Icc.image (by fun_prop)
  obtain ⟨R0, hR0⟩ := hc.isBounded.subset_closedBall (0 : ℂ)
  set R := max R0 1 with hRdef
  have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  set U := (closedBall (0 : ℂ) R)ᶜ with hUdef
  have hUD : U ⊆ (drawing V E)ᶜ := fun z hz hzD =>
    hz (closedBall_subset_closedBall (le_max_left _ _) (hR0 hzD))
  have hUc : IsPreconnected U := isPreconnected_compl_closedBall_zero R hR
  set p : ℂ := ((2 * R : ℝ) : ℂ) with hpdef
  have hpU : p ∈ U := by
    simp only [hUdef, mem_compl_iff, mem_closedBall, dist_zero_right, not_le, hpdef,
      Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (by linarith)]; linarith
  set f0 := connectedComponentIn (drawing V E)ᶜ p with hf0def
  have hf0 : f0 ∈ faces V E := mem_faces_iff.2 ⟨p, hUD hpU, rfl⟩
  have hUf0 : U ⊆ f0 := hUc.subset_connectedComponentIn hpU hUD
  have hf0unb : ¬ Bornology.IsBounded f0 := by
    intro hb
    obtain ⟨r, hr⟩ := hb.subset_closedBall (0 : ℂ)
    set q : ℂ := ((max r R + 1 : ℝ) : ℂ)
    have hqU : q ∈ U := by
      simp only [hUdef, mem_compl_iff, mem_closedBall, dist_zero_right, not_le, q,
        Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_pos (by linarith [le_max_right r R])]; linarith [le_max_right r R]
    have := hr (hUf0 hqU)
    simp only [mem_closedBall, dist_zero_right, q, Complex.norm_real, Real.norm_eq_abs] at this
    rw [abs_of_pos (by linarith [le_max_right r R])] at this
    linarith [le_max_left r R]
  have hunb : ∀ f ∈ faces V E, ¬ Bornology.IsBounded f → f = f0 := by
    intro f hf hfb
    have : ¬ f ⊆ closedBall (0 : ℂ) R := fun h => hfb (isBounded_closedBall.subset h)
    obtain ⟨z, hzf, hzR⟩ := Set.not_subset.1 this
    obtain ⟨x, -, rfl⟩ := mem_faces_iff.1 hf
    rw [connectedComponentIn_eq hzf]
    exact (connectedComponentIn_eq (hUf0 hzR)).symm
  have heq : faces V E = insert f0 (boundedFaces V E) := by
    ext f
    simp only [mem_insert_iff, boundedFaces, mem_setOf_eq]
    constructor
    · intro hf
      by_cases hb : Bornology.IsBounded f
      · exact Or.inr ⟨hf, hb⟩
      · exact Or.inl (hunb f hf hb)
    · rintro (rfl | ⟨hf, -⟩)
      · exact hf0
      · exact hf
  rw [heq, Set.ncard_insert_of_notMem (fun h => hf0unb h.2)
    (hfin.subset fun f hf => hf.1)]

/-! ## Boundary points of the hull -/

/-- A boundary point of the hull of `X` is a point of `X` or lies inside a hull side. -/
theorem frontier_cHull_cases :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      ∀ m ∈ frontier (convexHull ℝ ((cVerts X : Finset ℂ) : Set ℂ)),
        m ∈ cVerts X ∨ ∃ h ∈ hullSideEdges X, m ∈ edgeOpenSeg h := by
  filter_upwards [boundary_hullVertex_eventually, eventually_not_collinear] with n hB hcol hfm X hX
  have hint := interior_cHull_nonempty (hcol X hX)
  set K := convexHull ℝ ((cVerts X : Finset ℂ) : Set ℂ) with hKdef
  have hKcl : IsClosed K := (cVerts X).finite_toSet.isCompact_convexHull.isClosed
  have eK : toC '' convexHull ℝ (X : Set Plane) = K := by
    rw [hKdef, cVerts, Finset.coe_image]
    exact LinearMap.image_convexHull toC.toLinearEquiv.toLinearMap _
  have hfr : ∀ x : Plane, toC x ∈ frontier K → x ∈ frontier (convexHull ℝ (X : Set Plane)) := by
    intro x hx
    have := toC.toHomeomorph.image_frontier (convexHull ℝ (X : Set Plane))
    simp only [LinearIsometryEquiv.coe_toHomeomorph] at this
    rw [← eK, ← this] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rw [toC.injective hyx] at hy
    exact hy
  intro m hm
  have hmK : m ∈ K := hKcl.frontier_subset hm
  have hmi : m ∉ interior K := hm.2
  by_cases hmV : m ∈ cVerts X
  · exact Or.inl hmV
  obtain ⟨a, b, hs, hmab⟩ := exists_side_of_frontier hint hmK hmi hmV
  have hHV : ∀ c ∈ cVerts X, (wc a b c).im = 0 → toC.symm c ∈ hullVertices X := by
    intro c hc hc0
    apply hB hfm X hX _ (mem_cVerts.1 hc) (hfr _ ?_)
    rw [LinearIsometryEquiv.apply_symm_apply]
    refine ⟨subset_closure (subset_convexHull ℝ _ hc), fun hint' => ?_⟩
    have := side_pos hs hint'
    linarith
  have hne : b - a ≠ 0 := sub_ne_zero.2 hs.2.2.1.symm
  have hwa : (wc a b a).im = 0 := by simp [wc]
  have hwb : (wc a b b).im = 0 := by simp [wc, div_self hne]
  have hccw : IsCcwHullSide X (toC.symm a) (toC.symm b) := by
    refine ⟨hHV a hs.1 hwa, hHV b hs.2.1 hwb, fun h => hs.2.2.1 (toC.symm.injective h),
      fun y hy => ?_⟩
    have h1 := hs.2.2.2 (toC y) (Finset.mem_image_of_mem _ hy)
    have h2 := im_wc_toC (toC.symm a) (toC.symm b) y
    simp only [LinearIsometryEquiv.apply_symm_apply] at h2
    rw [h2] at h1
    have hn : 0 < normSq (b - a) := normSq_pos.2 hne
    exact (div_nonneg_iff.1 h1).elim (fun h => h.1) (fun h => absurd h.2 (not_le.2 hn))
  refine Or.inr ⟨s(a, b), ?_, by rw [edgeOpenSeg_mk]; exact hmab⟩
  exact Finset.mem_image.2 ⟨(toC.symm a, toC.symm b), mem_ccwHullSides.2 hccw, by simp⟩

/-! ## Faces on the two sides of an edge -/

/-- The bounded faces of the augmented graph having the edge `e` on their boundary. -/
def augSides (X : Finset Plane) (e : Sym2 ℂ) : Set (Set ℂ) :=
  {F ∈ augFaces X | e ∈ bdryEdges (augEdges X) F}

/-- **A hull side bounds exactly one bounded face of the augmented graph** (its cap). -/
theorem augSides_hullSide :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      ∀ p ∈ ccwHullSides X, (augSides X s(toC p.1, toC p.2)).ncard = 1 := by
  filter_upwards [exists_cap, cap_unique] with n hex hun hfm X hX p hp
  obtain ⟨F0, hF0⟩ := hex hfm X hX p hp
  rw [Set.ncard_eq_one]
  refine ⟨F0, Set.eq_singleton_iff_unique_mem.2 ⟨hF0, fun F hF => hun hfm X hX p hp F F0 hF hF0⟩⟩

/-- `wc a b` along the normal through a point of the open segment. -/
lemma wc_add_normal {a b z : ℂ} (hab : a ≠ b) (t : ℝ) :
    wc a b (z + (t : ℂ) * (I * (b - a))) = wc a b z + (t : ℂ) * I := by
  have hne : b - a ≠ 0 := sub_ne_zero.2 hab.symm
  simp only [wc]
  field_simp
  ring

/-- **Every unit edge which is not a hull side bounds exactly two bounded faces of the augmented
graph.** -/
theorem augSides_interior :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      ∀ e ∈ cUnitEdges X, e ∉ hullSideEdges X → (augSides X e).ncard = 2 := by
  filter_upwards [augEdges_isPlaneGraph, frontier_cHull_subset_augDrawing, frontier_cHull_cases,
    augFace_polygon] with n hPa hfr hcases hpoly hfm X hX e he hnh
  have hP := hPa hfm X hX
  have heA : e ∈ augEdges X := Finset.mem_union_left _ he
  set K := convexHull ℝ ((cVerts X : Finset ℂ) : Set ℂ) with hKdef
  have hKcl : IsClosed K := (cVerts X).finite_toSet.isCompact_convexHull.isClosed
  have hKb : Bornology.IsBounded K := (cVerts X).finite_toSet.isCompact_convexHull.isBounded
  induction e using Sym2.ind with
  | _ a b =>
  have hab : a ≠ b := fun h => hP.not_diag _ heA (by simp [h])
  have hne : b - a ≠ 0 := sub_ne_zero.2 hab.symm
  set D := drawing (cVerts X) (augEdges X) with hDdef
  set H := drawing (cVerts X) ((augEdges X).erase s(a, b)) with hHdef
  have hDH : D = H ∪ segment ℝ a b := by
    rw [hDdef, hHdef, ← edgeSeg_mk, ← drawing_insert_edge, Finset.insert_erase heA]
  set z : ℂ := (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b with hzdef
  have hz : z ∈ openSegment ℝ a b := ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
  have hzH : z ∉ H := openSegment_not_mem_drawing hP heA subset_rfl subset_rfl z hz
  have hzD : z ∈ D := hDH ▸ Or.inr (openSegment_subset_segment ℝ a b hz)
  -- the midpoint lies inside the hull
  have hzK : z ∈ interior K := by
    by_contra hzi
    have hzK0 : z ∈ K := segment_subset_convexHull
      (Finset.mem_coe.2 (hP.mem_V _ heA a (Sym2.mem_mk_left _ _)))
      (Finset.mem_coe.2 (hP.mem_V _ heA b (Sym2.mem_mk_right _ _)))
      (openSegment_subset_segment ℝ a b hz)
    have hzfr : z ∈ frontier K := ⟨subset_closure hzK0, hzi⟩
    rcases hcases hfm X hX z hzfr with hv | ⟨h, hh, hzh⟩
    · exact openSegment_not_mem_drawing (V := cVerts X) (E := ∅) hP heA subset_rfl
        (Finset.empty_subset _) z hz (Or.inl hv)
    · have hhe : h ≠ s(a, b) := fun heq => hnh (heq ▸ hh)
      refine openSegment_not_mem_drawing (V := ∅) (E := {h}) hP heA (Finset.empty_subset _)
        ?_ z hz (Or.inr (Set.mem_iUnion₂.2 ⟨h, Finset.mem_singleton_self h, ?_⟩))
      · intro x hx
        rw [Finset.mem_singleton] at hx
        subst hx
        exact Finset.mem_erase.2 ⟨hhe, Finset.mem_union_right _ hh⟩
      · induction h using Sym2.ind with
        | _ c d => rw [edgeOpenSeg_mk] at hzh; rw [edgeSeg_mk]; exact openSegment_subset_segment ℝ c d hzh
  obtain ⟨r1, hr1, hr1H, -⟩ := exists_ball_local hab (isClosed_drawing _ _) hz hzH
  obtain ⟨r2, hr2, hr2K⟩ := Metric.isOpen_iff.1 isOpen_interior z hzK
  set w : ℂ := I * (b - a) with hwdef
  have hw : 0 < ‖w‖ := by rw [hwdef, norm_mul, norm_I, one_mul]; exact norm_pos_iff.2 hne
  set r := min r1 r2 with hrdef
  have hr : 0 < r := lt_min hr1 hr2
  set t0 : ℝ := r / (2 * ‖w‖) with ht0def
  have ht0 : 0 < t0 := by positivity
  set pt : ℝ → ℂ := fun t => z + (t : ℂ) * w with hptdef
  have hzw : (wc a b z).im = 0 := ((mem_openSegment_iff_wc hab z).1 hz).1
  have hpt_im : ∀ t : ℝ, (wc a b (pt t)).im = t := by
    intro t; simp only [hptdef, hwdef, wc_add_normal hab, add_im, hzw]; simp
  have hpt_dist : ∀ t : ℝ, |t| ≤ t0 → dist (pt t) z < r := by
    intro t ht
    rw [dist_eq_norm, hptdef, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |t| * ‖w‖ ≤ t0 * ‖w‖ := mul_le_mul_of_nonneg_right ht hw.le
      _ = r / 2 := by rw [ht0def]; field_simp
      _ < r := by linarith
  -- points `pt t`, `0 < |t| ≤ t0`, are off the drawing and inside the hull
  have hpt_off : ∀ t : ℝ, t ≠ 0 → |t| ≤ t0 → pt t ∉ D := by
    intro t ht0' ht hD
    rw [hDH] at hD
    have hb := hpt_dist t ht
    rcases hD with hH | hs
    · exact hr1H (ball_subset_ball (min_le_left _ _) hb) hH
    · have := wc_im_of_mem_segment hs
      rw [hpt_im] at this
      exact ht0' this
  have hpt_int : ∀ t : ℝ, |t| ≤ t0 → pt t ∈ interior K := fun t ht =>
    hr2K (ball_subset_ball (min_le_right _ _) (hpt_dist t ht))
  -- the face through `pt (σ t0)` for a sign `σ`
  have side : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
      ∃ F ∈ augSides X s(a, b), ∀ t : ℝ, 0 < t → t ≤ t0 → pt (σ * t) ∈ F := by
    intro σ hσ
    have habs : ∀ t : ℝ, |σ * t| = |t| := by
      intro t; rcases hσ with rfl | rfl <;> simp [abs_neg]
    have hσne : ∀ t : ℝ, 0 < t → σ * t ≠ 0 := by
      intro t ht; rcases hσ with rfl | rfl <;> simp <;> linarith
    set P := (fun t : ℝ => pt (σ * t)) '' Set.Ioc 0 t0 with hPdef
    have hPc : IsPreconnected P :=
      isPreconnected_Ioc.image _ (by simp only [hptdef]; fun_prop)
    have hPD : P ⊆ Dᶜ := by
      rintro _ ⟨t, ⟨ht1, ht2⟩, rfl⟩
      exact hpt_off _ (hσne t ht1) (by rw [habs, abs_of_pos ht1]; exact ht2)
    have hp0 : pt (σ * t0) ∈ P := ⟨t0, ⟨ht0, le_rfl⟩, rfl⟩
    set F := connectedComponentIn Dᶜ (pt (σ * t0)) with hFdef
    have hF : F ∈ faces (cVerts X) (augEdges X) := mem_faces_iff.2 ⟨_, hPD hp0, rfl⟩
    have hPF : P ⊆ F := hPc.subset_connectedComponentIn hp0 hPD
    have hFK : F ⊆ interior K := by
      refine isPreconnected_connectedComponentIn.subset_left_of_subset_union isOpen_interior
        hKcl.isOpen_compl (disjoint_compl_right.mono_left interior_subset) ?_
        ⟨_, mem_connectedComponentIn (hPD hp0), hpt_int _ (by
          rw [habs, abs_of_pos ht0])⟩
      intro x hx
      by_cases hxK : x ∈ K
      · by_cases hxi : x ∈ interior K
        · exact Or.inl hxi
        · exact absurd (hfr hfm X hX ⟨subset_closure hxK, hxi⟩)
            (connectedComponentIn_subset _ _ hx)
      · exact Or.inr hxK
    refine ⟨F, ⟨⟨hF, hKb.subset (hFK.trans interior_subset)⟩, ?_⟩, fun t ht ht' =>
      hPF ⟨t, ⟨ht, ht'⟩, rfl⟩⟩
    refine Finset.mem_filter.2 ⟨heA, z, by rw [edgeOpenSeg_mk]; exact hz, ?_⟩
    rw [Metric.mem_closure_iff]
    intro ε hε
    set t := min t0 (ε / (2 * ‖w‖)) with htdef
    have ht : 0 < t := lt_min ht0 (by positivity)
    refine ⟨pt (σ * t), hPF ⟨t, ⟨ht, min_le_left _ _⟩, rfl⟩, ?_⟩
    rw [dist_comm, dist_eq_norm, hptdef]
    have hσ1 : |σ| = 1 := by rcases hσ with rfl | rfl <;> simp
    simp only [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs, hσ1,
      one_mul, abs_of_pos ht]
    calc t * ‖w‖ ≤ ε / (2 * ‖w‖) * ‖w‖ := mul_le_mul_of_nonneg_right (min_le_right _ _) hw.le
      _ = ε / 2 := by field_simp
      _ < ε := by linarith
  obtain ⟨F1, hF1, hp1⟩ := side 1 (Or.inl rfl)
  obtain ⟨F2, hF2, hp2⟩ := side (-1) (Or.inr rfl)
  have hF12 : F1 ≠ F2 := by
    rintro rfl
    obtain ⟨S, -, -, -, hFint, -, -⟩ := hpoly hfm X hX F1 hF1.1
    have hconv : Convex ℝ F1 := hFint ▸ (convex_convexHull ℝ _).interior
    have h1 := hp1 t0 ht0 le_rfl
    have h2 := hp2 t0 ht0 le_rfl
    have hmid : z ∈ F1 := by
      have := hconv h1 h2 (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)
      convert this using 1
      simp only [hptdef, Complex.real_smul]
      push_cast
      ring
    exact face_subset_compl hF1.1.1 hmid hzD
  -- at most two faces
  have hle : (augSides X s(a, b)).encard ≤ 2 :=
    (encard_le_encard (t := {f ∈ faces (cVerts X) (augEdges X) | s(a, b) ∈ bdryEdges (augEdges X) f})
      fun F hF => ⟨hF.1.1, hF.2⟩).trans (encard_faces_bdry_le_two hP heA)
  have hge : 2 ≤ (augSides X s(a, b)).encard := by
    rw [← encard_pair hF12]
    exact encard_le_encard (Set.insert_subset hF1 (Set.singleton_subset_iff.2 hF2))
  have h2 : (augSides X s(a, b)).encard = 2 := le_antisymm hle hge
  rw [Set.ncard_def, h2]
  rfl

/-- **Boundary edges of contact faces.**  For a bounded face of the contact graph, the boundary
edges in the augmented graph are its boundary unit edges. -/
theorem bdryEdges_aug_contact :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      ∀ F ∈ contactFaces X, bdryEdges (augEdges X) F = bdryEdges (cUnitEdges X) F := by
  filter_upwards [augEdges_isPlaneGraph, contactFaces_subset_augFaces] with n hPa hsub hfm X hX F hF
  have hP := hPa hfm X hX
  have hFa := hsub hfm X hX hF
  ext e
  simp only [bdryEdges, Finset.mem_filter]
  constructor
  · rintro ⟨heA, x, hx, hxc⟩
    refine ⟨?_, x, hx, hxc⟩
    rcases Finset.mem_union.1 heA with hu | hh
    · exact hu
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hh
    by_cases hd : dist q.1 q.2 = 1
    · have hs := mem_ccwHullSides.1 hq
      rw [cUnitEdges, mem_unitPairs]
      exact ⟨Finset.mem_image_of_mem _ (mem_of_mem_hullVertices hs.1),
        Finset.mem_image_of_mem _ (mem_of_mem_hullVertices hs.2.1), by rw [dist_toC]; exact hd⟩
    · exfalso
      rw [edgeOpenSeg_mk] at hx
      have hxF : x ∉ F := fun hxF => face_subset_compl hFa.1 hxF
        (Or.inr (Set.mem_iUnion₂.2 ⟨_, heA, openSegment_subset_segment ℝ _ _ hx⟩))
      exact hullSide_open_off_contact hP hq hd hx (closure_face_diff hF.1 hxc hxF)
  · rintro ⟨hu, x, hx, hxc⟩
    exact ⟨Finset.mem_union_left _ hu, x, hx, hxc⟩

end Erdos99

end

end FaceSides

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `TrackEdges`
-/

section TrackEdges

/-!
# Exact edge counts of tracks, and the set of all tracks (WP3)

* `card_eq_trackLength_add_one`: a track with `r(T)` rhombi has exactly `r(T) + 1` edges;
* `card_filter_subset_rhombus`: a rhombus crossed by a track contains exactly two of its edges;
* `sum_card_rhombi_containing`: summing over the edges of `T` the number of rhombi containing
  the edge gives `2 r(T)`;
* `allTrackOf`, `allTracks`: the tracks of *all* unit edges, including the zero-rhombus tracks
  `{e}` of unit edges lying on no rhombus; `allTracks X` consists of `tracks X` together with
  these singletons;
* `card_allTracks_add`: `s + 2q = m`, where `s = |allTracks X|`.
-/

open scoped BigOperators Real

@[expose] public noncomputable section

open Classical

namespace Erdos99

/-- All points of an edge with direction `±u` have the same height `ht u e`. -/
lemma inner_rot_of_mem {u : Plane} {e : Sym2 Plane} (hd : DirOf u e) {x : Plane} (hx : x ∈ e) :
    inner ℝ x (rot u) = ht u e := by
  induction e using Sym2.ind with
  | _ p q =>
  have h0 : inner ℝ (p - q) (rot u) = 0 := by
    rcases hd with hd | hd <;> rcases dv_mk p q with h | h
    · rw [← h, hd, inner_rot_coord]; ring
    · rw [← neg_sub, ← h, hd, inner_neg_left, inner_rot_coord]; ring
    · rw [← h, hd, inner_neg_left, inner_rot_coord]; ring
    · rw [← neg_sub, ← h, hd, neg_neg, inner_rot_coord]; ring
  rw [inner_sub_left] at h0
  rw [ht, mid_mk, inner_smul_left, inner_add_left]
  simp only [RCLike.conj_to_real]
  rcases Sym2.mem_iff.1 hx with rfl | rfl <;> linarith

section
variable {X : Finset Plane} (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X)
include hX htri

/-- A track has at most `r(T) + 1` edges: the edges other than the top one inject into the rhombi
of the track (each is sent to the rhombus joining it to the edge above it). -/
lemma card_le_trackLength_add_one {T : Finset (Sym2 Plane)} (hT : T ∈ tracks X) :
    T.card ≤ trackLength X T + 1 := by
  obtain ⟨e0, he0, hu0⟩ := exists_rep_of_mem_tracks hT
  set u := dv e0
  have hu : ‖u‖ = 1 := norm_dv_of_mem_unitEdges hu0
  have hTe0 := eq_trackOf_of_mem hT he0
  have hdir : ∀ e ∈ T, DirOf u e := fun e he => by
    rw [hTe0] at he; exact sameDir_of_mem_trackOf he
  obtain ⟨top, htop, hmax⟩ := T.exists_max_image (ht u) ⟨e0, he0⟩
  obtain ⟨m, hm, hmin⟩ := T.exists_min_image (ht u) ⟨e0, he0⟩
  have hup : ∀ e ∈ T, e ≠ top → upE X u e ≠ e := by
    intro e he hne hfix
    obtain ⟨i, rfl⟩ := mem_range_iterate hX htri hT hu hdir hm hmin he
    obtain ⟨k, hk⟩ := mem_range_iterate hX htri hT hu hdir hm hmin htop
    have stuck : ∀ j, i ≤ j → (upE X u)^[j] m = (upE X u)^[i] m := by
      intro j hj
      induction j, hj using Nat.le_induction with
      | base => rfl
      | succ j hij ih => rw [Function.iterate_succ_apply', ih, hfix]
    rcases le_total i k with hik | hki
    · exact hne (by rw [← hk, stuck k hik])
    · rcases iterate_upE_mono hX htri hT hu hdir hm k i hki with h | h
      · exact hne (by rw [h, hk])
      · have := hmax _ (iterate_upE_mem (u := u) hT hm i)
        rw [hk] at h
        linarith [aStar_pos]
  have hinj : (T.erase top).card ≤ trackLength X T := by
    refine Finset.card_le_card_of_forall_subsingleton
      (fun e R => ∃ f, OppositeSides X e f ∧ ht u e < ht u f ∧ ∀ z, z ∈ R ↔ (z ∈ e ∨ z ∈ f))
      ?_ ?_
    · intro e he
      obtain ⟨hne, heT⟩ := Finset.mem_erase.1 he
      obtain ⟨o, hlt⟩ := upE_spec (hup e heT hne)
      obtain ⟨a, b, c, d, h, rfl, hf⟩ := oppositeSides_data hX htri o
      refine ⟨{a, b, c, d}, Finset.mem_filter.2 ⟨h.mem, s(a, b), heT, fun z hz => ?_⟩,
        _, o, hlt, fun z => ?_⟩
      · rcases Sym2.mem_iff.1 hz with rfl | rfl <;> simp
      · rw [hf]; simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.mem_iff]; tauto
    · intro R _ e1 he1 e2 he2
      obtain ⟨he1T, f1, o1, l1, m1⟩ := he1
      obtain ⟨he2T, f2, o2, l2, m2⟩ := he2
      have h1T := Finset.mem_of_mem_erase he1T
      have h2T := Finset.mem_of_mem_erase he2T
      have hf1 := opp_mem_track hT h1T o1
      have hf2 := opp_mem_track hT h2T o2
      -- the lowest height of a point of `R` is the height of `e1`, and also that of `e2`
      have key : ∀ {e e' f : Sym2 Plane}, e ∈ T → e' ∈ T → f ∈ T → ht u e < ht u f →
          (∀ z, z ∈ R ↔ (z ∈ e ∨ z ∈ f)) → (∀ z ∈ e', z ∈ R) → ht u e ≤ ht u e' := by
        intro e e' f he he' hf hlt hR hsub
        induction e' using Sym2.ind with
        | _ x y =>
        have hx := hsub x (Sym2.mem_mk_left _ _)
        rw [← inner_rot_of_mem (hdir _ he') (Sym2.mem_mk_left x y)]
        rcases (hR x).1 hx with h | h
        · rw [inner_rot_of_mem (hdir _ he) h]
        · rw [inner_rot_of_mem (hdir _ hf) h]; exact hlt.le
      have s1 : ∀ z ∈ e1, z ∈ R := fun z hz => (m1 z).2 (Or.inl hz)
      have s2 : ∀ z ∈ e2, z ∈ R := fun z hz => (m2 z).2 (Or.inl hz)
      have h12 := key h1T h2T hf1 l1 m1 s2
      have h21 := key h2T h1T hf2 l2 m2 s1
      by_contra hne
      have := ht_sep hX htri hT hu hdir h1T h2T hne
      rw [le_antisymm h12 h21, sub_self, abs_zero] at this
      linarith [aStar_pos]
  have := Finset.card_erase_add_one htop
  omega

/-- **A track with `r(T)` rhombi has exactly `r(T) + 1` edges.** -/
theorem card_eq_trackLength_add_one {T : Finset (Sym2 Plane)} (hT : T ∈ tracks X) :
    T.card = trackLength X T + 1 :=
  le_antisymm (card_le_trackLength_add_one hX htri hT) (trackLength_add_one_le_card hX htri hT)

omit hX htri in
/-- Edges of a common track have the same direction. -/
lemma sameDir_of_mem_tracks {T : Finset (Sym2 Plane)} (hT : T ∈ tracks X) {e f : Sym2 Plane}
    (he : e ∈ T) (hf : f ∈ T) : SameDir e f := by
  rw [eq_trackOf_of_mem hT he] at hf
  exact (sameDir_of_mem_trackOf hf).symm

omit hX htri in
lemma unitEdges_of_mem_tracks {T : Finset (Sym2 Plane)} (hT : T ∈ tracks X) {e : Sym2 Plane}
    (he : e ∈ T) : e ∈ unitEdges X := by
  rw [eq_trackOf_of_mem hT he] at he
  exact (Finset.mem_filter.1 (mem_trackOf.1 he).1).1

omit hX htri in
/-- Two adjacent sides of a rhombus are not parallel. -/
lemma RhombusData.not_sameDir_adj {R : Finset Plane} {a b c d : Plane}
    (h : RhombusData X R a b c d) : ¬ SameDir s(a, b) s(b, c) := by
  intro hs
  have h1 := h.abs_inner_dv_lt
  rw [abs_inner_of_sameDir (SameDir.refl _) hs.symm, real_inner_self_eq_norm_sq,
    norm_dv_of_mem_unitEdges h.unit_ab] at h1
  norm_num at h1

/-- **A rhombus crossed by a track contains exactly two edges of the track** (a pair of opposite
sides). -/
theorem card_filter_subset_rhombus {T : Finset (Sym2 Plane)} (hT : T ∈ tracks X)
    {R : Finset Plane} (hR : R ∈ rhombi X) (hc : Crosses T R) :
    (T.filter (fun e => ∀ x ∈ e, x ∈ R)).card = 2 := by
  obtain ⟨e, heT, hin⟩ := hc
  obtain ⟨a0, b0, c0, d0, h0⟩ := exists_rhombusData hX htri hR
  have heu := unitEdges_of_mem_tracks hT heT
  obtain ⟨⟨x, y⟩, hp, rfl⟩ := Finset.mem_image.1 heu
  simp only [Finset.mem_filter] at hp
  -- relabel the rhombus so that `e` is the side `ab`
  have hlab : ∃ a b c d, RhombusData X R a b c d ∧ s(x, y) = s(a, b) := by
    rcases h0.edge_cases (hin x (Sym2.mem_mk_left _ _)) (hin y (Sym2.mem_mk_right _ _)) hp.2 with
      e | e | e | e
    · exact ⟨_, _, _, _, h0, e⟩
    · exact ⟨_, _, _, _, h0.rotate, e⟩
    · exact ⟨_, _, _, _, h0.rotate.rotate, e⟩
    · exact ⟨_, _, _, _, h0.rotate.rotate.rotate, e⟩
  obtain ⟨a, b, c, d, h, hxy⟩ := hlab
  rw [hxy] at heT
  have hcdT : s(c, d) ∈ T := opp_mem_track hT heT h.opp
  have hfilt : T.filter (fun e => ∀ x ∈ e, x ∈ R) = {s(a, b), s(c, d)} := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hgT, hgR⟩
      have hgu := unitEdges_of_mem_tracks hT hgT
      obtain ⟨⟨p, q⟩, hpq, rfl⟩ := Finset.mem_image.1 hgu
      simp only [Finset.mem_filter] at hpq
      have hs := sameDir_of_mem_tracks hT heT hgT
      rcases h.edge_cases (hgR p (Sym2.mem_mk_left _ _)) (hgR q (Sym2.mem_mk_right _ _)) hpq.2 with
        e | e | e | e
      · exact Or.inl e
      · exact absurd (e ▸ hs) h.not_sameDir_adj
      · exact Or.inr e
      · have hda := h.rotate.rotate.rotate.not_sameDir_adj
        rw [e] at hs
        exact absurd hs.symm hda
    · rintro (rfl | rfl)
      · exact ⟨heT, fun z hz => by rw [h.eq]; rcases Sym2.mem_iff.1 hz with rfl | rfl <;> simp⟩
      · exact ⟨hcdT, fun z hz => by rw [h.eq]; rcases Sym2.mem_iff.1 hz with rfl | rfl <;> simp⟩
  rw [hfilt, Finset.card_pair]
  intro heq
  obtain ⟨-, hac, had, -, -, -⟩ := h.distinct
  rcases Sym2.eq_iff.1 heq with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact hac h1
  · exact had h1

/-- Summing, over the edges of a track, the number of rhombi containing the edge gives `2 r(T)`. -/
theorem sum_card_rhombi_containing {T : Finset (Sym2 Plane)} (hT : T ∈ tracks X) :
    ∑ e ∈ T, ((rhombi X).filter (fun R => ∀ x ∈ e, x ∈ R)).card = 2 * trackLength X T := by
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm, trackLength, Finset.card_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun R hR => ?_
  rw [← Finset.card_filter]
  by_cases hc : Crosses T R
  · rw [card_filter_subset_rhombus hX htri hT hR hc, if_pos hc, mul_one]
  · rw [if_neg hc, mul_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun e he hsub => hc ⟨e, he, hsub⟩

end

/-! ## All tracks, including tracks without rhombi -/

/-- The track of an arbitrary unit edge `e`: the unit edges equivalent to `e` under passing to the
opposite side of a rhombus.  For a unit edge on no rhombus this is `{e}`. -/
def allTrackOf (X : Finset Plane) (e : Sym2 Plane) : Finset (Sym2 Plane) :=
  (unitEdges X).filter (fun f => Relation.EqvGen (OppositeSides X) e f)

/-- All tracks of `X`, including the zero-rhombus tracks `{e}` of unit edges on no rhombus. -/
def allTracks (X : Finset Plane) : Finset (Finset (Sym2 Plane)) :=
  (unitEdges X).image (allTrackOf X)

lemma allTrackOf_of_mem_rhombusEdges {X : Finset Plane} {e : Sym2 Plane}
    (he : e ∈ rhombusEdges X) : allTrackOf X e = trackOf X e := by
  ext f
  rw [mem_trackOf, allTrackOf, Finset.mem_filter]
  constructor
  · rintro ⟨-, hr⟩
    exact ⟨mem_rhombusEdges_of_eqvGen (Relation.EqvGen.symm _ _ hr) he, hr⟩
  · rintro ⟨hf, hr⟩; exact ⟨(Finset.mem_filter.1 hf).1, hr⟩

lemma eq_of_eqvGen_of_not_mem {X : Finset Plane} {e f : Sym2 Plane} (he : e ∉ rhombusEdges X)
    (h : Relation.EqvGen (OppositeSides X) e f) : f = e := by
  have key : ∀ a b, Relation.EqvGen (OppositeSides X) a b → (a = e ↔ b = e) := by
    intro a b hab
    induction hab with
    | rel a b h =>
      have ha : a ≠ e := fun hae => he (hae ▸ mem_rhombusEdges_of_opp h)
      have hb : b ≠ e := fun hbe => he (hbe ▸ mem_rhombusEdges_of_opp (oppositeSides_symm h))
      exact ⟨fun h => absurd h ha, fun h => absurd h hb⟩
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  exact (key e f h).1 rfl

lemma allTrackOf_of_not_mem {X : Finset Plane} {e : Sym2 Plane} (heu : e ∈ unitEdges X)
    (he : e ∉ rhombusEdges X) : allTrackOf X e = {e} := by
  ext f
  simp only [allTrackOf, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨-, hr⟩; exact eq_of_eqvGen_of_not_mem he hr
  · rintro rfl; exact ⟨heu, Relation.EqvGen.refl _⟩

/-- `allTracks X` is the set of tracks together with the singletons of the unit edges lying on no
rhombus. -/
theorem allTracks_eq (X : Finset Plane) :
    allTracks X = tracks X ∪ (unitEdges X \ rhombusEdges X).image (fun e => {e}) := by
  ext T
  simp only [allTracks, tracks, Finset.mem_union, Finset.mem_image, Finset.mem_sdiff]
  constructor
  · rintro ⟨e, he, rfl⟩
    by_cases hr : e ∈ rhombusEdges X
    · exact Or.inl ⟨e, hr, (allTrackOf_of_mem_rhombusEdges hr).symm⟩
    · exact Or.inr ⟨e, ⟨he, hr⟩, (allTrackOf_of_not_mem he hr).symm⟩
  · rintro (⟨e, hr, rfl⟩ | ⟨e, ⟨he, hr⟩, rfl⟩)
    · exact ⟨e, (Finset.mem_filter.1 hr).1, allTrackOf_of_mem_rhombusEdges hr⟩
    · exact ⟨e, he, allTrackOf_of_not_mem he hr⟩

lemma tracks_subset_allTracks (X : Finset Plane) : tracks X ⊆ allTracks X := by
  rw [allTracks_eq]; exact Finset.subset_union_left

/-- Every unit edge lies in exactly one track of `allTracks X`: its own track `allTrackOf X e`. -/
lemma mem_allTrackOf_self {X : Finset Plane} {e : Sym2 Plane} (he : e ∈ unitEdges X) :
    e ∈ allTrackOf X e :=
  Finset.mem_filter.2 ⟨he, Relation.EqvGen.refl _⟩

lemma eq_allTrackOf_of_mem {X : Finset Plane} {T : Finset (Sym2 Plane)} (hT : T ∈ allTracks X)
    {e : Sym2 Plane} (he : e ∈ T) : T = allTrackOf X e := by
  obtain ⟨e0, -, rfl⟩ := Finset.mem_image.1 hT
  have h := (Finset.mem_filter.1 he).2
  ext f
  simp only [allTrackOf, Finset.mem_filter]
  constructor
  · rintro ⟨hf, h'⟩; exact ⟨hf, (Relation.EqvGen.symm _ _ h).trans _ _ _ h'⟩
  · rintro ⟨hf, h'⟩; exact ⟨hf, h.trans _ _ _ h'⟩

lemma allTracks_subset_unitEdges {X : Finset Plane} {T : Finset (Sym2 Plane)}
    (hT : T ∈ allTracks X) : T ⊆ unitEdges X := by
  obtain ⟨e0, -, rfl⟩ := Finset.mem_image.1 hT
  exact Finset.filter_subset _ _

lemma allTrackOf_mem_allTracks {X : Finset Plane} {e : Sym2 Plane} (he : e ∈ unitEdges X) :
    allTrackOf X e ∈ allTracks X := Finset.mem_image_of_mem _ he

/-- A unit edge on no rhombus lies in no rhombus. -/
lemma not_subset_rhombus_of_not_mem {X : Finset Plane} (hX : IsSeparated X)
    (htri : ¬ HasUnitTriangle X) {e : Sym2 Plane} (heu : e ∈ unitEdges X)
    (he : e ∉ rhombusEdges X) {R : Finset Plane} (hR : R ∈ rhombi X) : ¬ ∀ x ∈ e, x ∈ R := by
  intro hsub
  obtain ⟨a, b, c, d, h⟩ := exists_rhombusData hX htri hR
  obtain ⟨⟨x, y⟩, hp, rfl⟩ := Finset.mem_image.1 heu
  simp only [Finset.mem_filter] at hp
  apply he
  rcases h.edge_cases (hsub x (Sym2.mem_mk_left _ _)) (hsub y (Sym2.mem_mk_right _ _)) hp.2 with
    e | e | e | e <;> rw [e]
  · exact h.rhombusEdge_ab
  · exact h.rotate.rhombusEdge_ab
  · exact h.rotate.rotate.rhombusEdge_ab
  · exact h.rotate.rotate.rotate.rhombusEdge_ab

/-- A zero-rhombus track `{e}` has length `0`. -/
lemma trackLength_singleton {X : Finset Plane} (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X)
    {e : Sym2 Plane} (heu : e ∈ unitEdges X) (he : e ∉ rhombusEdges X) :
    trackLength X {e} = 0 := by
  rw [trackLength, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro R hR ⟨f, hf, hsub⟩
  rw [Finset.mem_singleton] at hf
  subst hf
  exact not_subset_rhombus_of_not_mem hX htri heu he hR hsub

/-- A track (through a rhombus edge) has positive length. -/
lemma trackLength_pos {X : Finset Plane} (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X)
    {T : Finset (Sym2 Plane)} (hT : T ∈ tracks X) : 0 < trackLength X T := by
  have h := trackLength_add_one_le_card hX htri hT
  obtain ⟨e, he, -⟩ := exists_rep_of_mem_tracks hT
  have hTe := eq_trackOf_of_mem hT he
  have her : e ∈ rhombusEdges X := (mem_trackOf.1 (hTe ▸ he)).1
  obtain ⟨f, o⟩ := (Finset.mem_filter.1 her).2
  have hf := opp_mem_track hT he o
  have hef : e ≠ f := by
    obtain ⟨a, b, c, d, h, rfl, rfl⟩ := oppositeSides_data hX htri o
    intro heq
    obtain ⟨-, hac, had, -, -, -⟩ := h.distinct
    rcases Sym2.eq_iff.1 heq with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hac h1
    · exact had h1
  have h2 : 2 ≤ T.card := by
    have : ({e, f} : Finset (Sym2 Plane)) ⊆ T := by
      intro g hg; simp only [Finset.mem_insert, Finset.mem_singleton] at hg
      rcases hg with rfl | rfl <;> assumption
    have := Finset.card_le_card this
    rwa [Finset.card_pair hef] at this
  have := card_eq_trackLength_add_one hX htri hT
  omega

/-- The tracks of positive length among all tracks are exactly the tracks through rhombi. -/
theorem allTracks_filter_pos {X : Finset Plane} (hX : IsSeparated X)
    (htri : ¬ HasUnitTriangle X) :
    (allTracks X).filter (fun T => 0 < trackLength X T) = tracks X := by
  ext T
  rw [Finset.mem_filter, allTracks_eq, Finset.mem_union]
  constructor
  · rintro ⟨hT | hT, hpos⟩
    · exact hT
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hT
      obtain ⟨heu, her⟩ := Finset.mem_sdiff.1 he
      rw [trackLength_singleton hX htri heu her] at hpos
      exact absurd hpos (lt_irrefl 0)
  · intro hT; exact ⟨Or.inl hT, trackLength_pos hX htri hT⟩

/-- **`s + 2q = m`** for the set `allTracks X` of all tracks (including zero-rhombus tracks). -/
theorem card_allTracks_add {X : Finset Plane} (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X) :
    (allTracks X).card + 2 * (rhombi X).card = (unitEdges X).card := by
  have hdisj : Disjoint (tracks X) ((unitEdges X \ rhombusEdges X).image (fun e => {e})) := by
    rw [Finset.disjoint_left]
    intro T hT hT'
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hT'
    have her := (Finset.mem_sdiff.1 he).2
    obtain ⟨e0, -, h0⟩ := Finset.mem_image.1 hT
    have : e ∈ trackOf X e0 := by rw [h0]; exact Finset.mem_singleton_self e
    exact her (mem_trackOf.1 this).1
  have hsd : (unitEdges X \ rhombusEdges X).card + (rhombusEdges X).card = (unitEdges X).card :=
    Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)
  have hcard : (allTracks X).card = (tracks X).card + (unitEdges X \ rhombusEdges X).card := by
    rw [allTracks_eq, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ Finset.singleton_injective]
  have hsum : (rhombusEdges X).card = 2 * (rhombi X).card + (tracks X).card := by
    rw [← sum_card_tracks, ← sum_trackLength hX htri]
    rw [Finset.sum_congr rfl fun T hT => card_eq_trackLength_add_one hX htri hT,
      Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
  have hle : (rhombusEdges X).card ≤ (unitEdges X).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  omega

end Erdos99

end

end TrackEdges

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `PortIncidence`
-/

section PortIncidence

/-!
# Ports and terminal incidences of tracks (WP3, `PortIncidence`)

The terminal structure of the tracks is modelled by *port incidences* (Verification Guide §3.1).
The nodes (`PortNode`) are

* the exceptional faces `F` (bounded faces of the contact graph with `k ≥ 5` sides), and
* the counterclockwise hull sides `p = (v, w)` (one node per hull return).

A unit edge `e` is a *port* of a node (`IsPort`) if

* `e` is a side of the exceptional face `F`; or
* `p` is a unit hull side and `e = [v, w]`; or
* `p` is a non-unit hull side and `e` is one of the unit edges of its cap.

Main results:

* `card_ports_add_card_rhombiAt`: every unit edge `e` has exactly two sides; each side is a rhombus
  containing `e` or a port incidence of `e`, so `#ports(e) + #rhombi(e) = 2`;
* `card_trackEnds`: every track (including zero-rhombus tracks) has exactly two terminal port
  incidences (`trackEnds`).  These form the terminal multigraph: a track whose two ends lie at the
  same node is a loop, and parallel tracks are allowed; nothing is collapsed;
* `portDeg_face`, `portDeg_hullSide`: a `k`-gonal exceptional face has `k` ports, a hull return of
  `j` unit edges has `j` ports;
* `sum_shortDeg`: `2 · #{short tracks} = Σ_nodes shortDeg`;
* `sum_portDeg`: `Σ_nodes deg = 2 s`.
-/

open scoped BigOperators Real
open EstablishedExternalResults Set Filter

@[expose] public noncomputable section

open Classical

namespace Erdos99

/-! ## Orientation of hull sides -/

/-- The two orientations of a hull side are not both counterclockwise (the hull has interior). -/
lemma ccwHullSides_eq_of_mk_eq {X : Finset Plane}
    (hint : (interior (convexHull ℝ ((cVerts X : Finset ℂ) : Set ℂ))).Nonempty)
    {p p' : Plane × Plane} (hp : p ∈ ccwHullSides X) (hp' : p' ∈ ccwHullSides X)
    (h : s(p.1, p.2) = s(p'.1, p'.2)) : p = p' := by
  rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Prod.ext h1 h2
  · exfalso
    obtain ⟨c, hc⟩ := hint
    have hs := isCSide_of_ccw (mem_ccwHullSides.1 hp)
    have s1 := side_pos hs hc
    have s2 := side_pos (isCSide_of_ccw (mem_ccwHullSides.1 hp')) hc
    rw [← h2, ← h1, wc_swap hs.2.2.1, Complex.sub_im, Complex.one_im] at s2
    linarith

lemma sym2_map_toC (a b : Plane) : Sym2.map toC s(a, b) = s(toC a, toC b) := rfl

lemma ccwHullSides_eq_of_toC_eq {X : Finset Plane}
    (hint : (interior (convexHull ℝ ((cVerts X : Finset ℂ) : Set ℂ))).Nonempty)
    {p p' : Plane × Plane} (hp : p ∈ ccwHullSides X) (hp' : p' ∈ ccwHullSides X)
    (h : s(toC p.1, toC p.2) = s(toC p'.1, toC p'.2)) : p = p' := by
  refine ccwHullSides_eq_of_mk_eq hint hp hp' ?_
  rw [← sym2_map_toC, ← sym2_map_toC] at h
  exact Sym2.map.injective toC.injective h

/-! ## Unit edges in `Plane` and in `ℂ` -/

lemma cUnitEdges_eq_image (X : Finset Plane) :
    cUnitEdges X = (unitEdges X).image (Sym2.map toC) := by
  rw [cUnitEdges, cVerts, unitPairs_image]

lemma map_mem_cUnitEdges {X : Finset Plane} {e : Sym2 Plane} (he : e ∈ unitEdges X) :
    Sym2.map toC e ∈ cUnitEdges X := by
  rw [cUnitEdges_eq_image]; exact Finset.mem_image_of_mem _ he

/-- Counting unit edges of `X` through their images in `ℂ`. -/
lemma card_filter_unitEdges_map (X : Finset Plane) (P : Sym2 ℂ → Prop) [DecidablePred P] :
    ((unitEdges X).filter (fun e => P (Sym2.map toC e))).card = ((cUnitEdges X).filter P).card := by
  rw [cUnitEdges_eq_image, Finset.filter_image,
    Finset.card_image_of_injective _ (Sym2.map.injective toC.injective)]

/-! ## Nodes and ports -/

/-- Nodes of the terminal multigraph: exceptional faces (`Sum.inl`) and counterclockwise hull sides,
i.e. hull returns (`Sum.inr`). -/
abbrev PortNode := Set ℂ ⊕ (Plane × Plane)

/-- The unit edge `e` is a port of the node `N`. -/
def IsPort (X : Finset Plane) : PortNode → Sym2 Plane → Prop
  | Sum.inl F, e => F ∈ exceptionalFaces X ∧ Sym2.map toC e ∈ bdryEdges (cUnitEdges X) F
  | Sum.inr p, e => p ∈ ccwHullSides X ∧ e ∈ unitEdges X ∧
      if dist p.1 p.2 = 1 then e = s(p.1, p.2)
      else ∃ F, IsCap X p.1 p.2 F ∧ Sym2.map toC e ∈ bdryEdges (augEdges X) F

/-- The exceptional faces, as a `Finset` (they are finitely many for a separated set). -/
def exceptionalFinset (X : Finset Plane) : Finset (Set ℂ) :=
  if h : (exceptionalFaces X).Finite then h.toFinset else ∅

/-- All nodes of the terminal multigraph. -/
def portNodes (X : Finset Plane) : Finset PortNode :=
  (exceptionalFinset X).map Function.Embedding.inl ∪ (ccwHullSides X).map Function.Embedding.inr

/-- The nodes at which the unit edge `e` is a port. -/
def ports (X : Finset Plane) (e : Sym2 Plane) : Finset PortNode :=
  (portNodes X).filter (fun N => IsPort X N e)

/-- The rhombi containing the unit edge `e`. -/
def rhombiAt (X : Finset Plane) (e : Sym2 Plane) : Finset (Finset Plane) :=
  (rhombi X).filter (fun R => ∀ x ∈ e, x ∈ R)

/-- The degree of a node: its number of ports. -/
def portDeg (X : Finset Plane) (N : PortNode) : ℕ :=
  ((unitEdges X).filter (IsPort X N)).card

/-- The short degree of a node: its number of ports whose track has fewer than `L` rhombi. -/
def shortDeg (X : Finset Plane) (L : ℝ) (N : PortNode) : ℕ :=
  ((unitEdges X).filter (fun e => IsPort X N e ∧ (trackLength X (allTrackOf X e) : ℝ) < L)).card

/-- The terminal port incidences (ends) of a track `T`: pairs `(node, edge)` with the edge in `T`
a port of the node. -/
def trackEnds (X : Finset Plane) (T : Finset (Sym2 Plane)) : Finset (PortNode × Sym2 Plane) :=
  ((portNodes X) ×ˢ T).filter (fun q => IsPort X q.1 q.2)

lemma finite_exceptionalFaces {X : Finset Plane} (hX : IsSeparated X) :
    (exceptionalFaces X).Finite :=
  (faces_finite (cUnitEdges_isPlaneGraph hX)).subset fun _ hF => hF.1.1

lemma coe_exceptionalFinset {X : Finset Plane} (hX : IsSeparated X) :
    (exceptionalFinset X : Set (Set ℂ)) = exceptionalFaces X := by
  rw [exceptionalFinset, dif_pos (finite_exceptionalFaces hX), Finite.coe_toFinset]

lemma mem_exceptionalFinset {X : Finset Plane} (hX : IsSeparated X) {F : Set ℂ} :
    F ∈ exceptionalFinset X ↔ F ∈ exceptionalFaces X := by
  rw [← Finset.mem_coe, coe_exceptionalFinset hX]

/-- The ports of `e` split into face ports and hull-return ports. -/
lemma card_ports (X : Finset Plane) (e : Sym2 Plane) :
    (ports X e).card = ((exceptionalFinset X).filter (fun F => IsPort X (Sum.inl F) e)).card +
      ((ccwHullSides X).filter (fun p => IsPort X (Sum.inr p) e)).card := by
  rw [ports, portNodes, Finset.filter_union, Finset.filter_map, Finset.filter_map,
    Finset.card_union_of_disjoint, Finset.card_map, Finset.card_map]
  · rfl
  · rw [Finset.disjoint_left]
    intro N h1 h2
    obtain ⟨F, -, rfl⟩ := Finset.mem_map.1 h1
    obtain ⟨p, -, hp⟩ := Finset.mem_map.1 h2
    cases hp

/-! ## Every unit edge has two sides -/

/-- The cap of a hull side (the empty set if there is none). -/
def capOf (X : Finset Plane) (p : Plane × Plane) : Set ℂ :=
  if h : ∃ F, IsCap X p.1 p.2 F then h.choose else ∅

lemma capOf_spec {X : Finset Plane} {p : Plane × Plane} (h : ∃ F, IsCap X p.1 p.2 F) :
    IsCap X p.1 p.2 (capOf X p) := by
  rw [capOf, dif_pos h]; exact h.choose_spec

/-- A unit pair inside a rhombus is a boundary edge of the rhombus face. -/
lemma map_mem_bdry_cInterior {X : Finset Plane} (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X)
    {R : Finset Plane} (hR : R ∈ rhombi X) {x y : Plane} (hx : x ∈ R) (hy : y ∈ R)
    (hxy : dist x y = 1) : s(toC x, toC y) ∈ bdryEdges (cUnitEdges X) (cInterior R) := by
  obtain ⟨a, b, c, d, himg, ha, hb, hc, hd, h1, h2, h3, h4, hac, hbd, hab', hac', had', hbc', hbd',
    hcd'⟩ := rhombi_data hX htri hR
  obtain ⟨-, hbdry, -⟩ := unit_rhombus_face (cUnitEdges_isPlaneGraph hX) (cVerts_sep hX) ha hb hc hd
    h1 h2 h3 h4 hac hbd hac' hbd'
  have hci : cInterior R = interior (convexHull ℝ ({a, b, c, d} : Set ℂ)) := by
    rw [cInterior, himg]
  rw [hci, cUnitEdges, hbdry]
  have hx' : toC x ∈ ({a, b, c, d} : Set ℂ) := himg ▸ Set.mem_image_of_mem _ hx
  have hy' : toC y ∈ ({a, b, c, d} : Set ℂ) := himg ▸ Set.mem_image_of_mem _ hy
  have hd1 : dist (toC x) (toC y) = 1 := by rw [dist_toC]; exact hxy
  generalize toC x = u at hx' hd1
  generalize toC y = v at hy' hd1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx' hy'
  rcases hx' with rfl | rfl | rfl | rfl <;> rcases hy' with rfl | rfl | rfl | rfl <;>
    simp_all [Sym2.eq_swap, dist_comm]

/-- **Every unit edge has exactly two sides**: each side is a rhombus containing it or a port
incidence, so `#ports(e) + #rhombi(e) = 2`. -/
theorem card_ports_add_card_rhombiAt :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ e ∈ unitEdges X, (ports X e).card + (rhombiAt X e).card = 2 := by
  filter_upwards [augSides_hullSide, augSides_interior, bdryEdges_aug_contact, augFace_cases,
    contactFaces_subset_augFaces, cap_unique, augFace_polygon, augEdges_isPlaneGraph,
    cUnitEdges_connected, eventually_not_collinear] with n hS1 hS2 hbd hcases hsubA huniq hpoly
    hPa hconn hcol hfm X hX htri e he
  have hsep := hX.1.2
  have hint := interior_cHull_nonempty (hcol X hX)
  set e' := Sym2.map toC e with he'def
  have he'C : e' ∈ cUnitEdges X := map_mem_cUnitEdges he
  set A := augSides X e' with hAdef
  have hAfin : A.Finite := (faces_finite (hPa hfm X hX)).subset fun F hF => hF.1.1
  set Aex := {F ∈ A | F ∈ exceptionalFaces X} with hAex
  set Arh := {F ∈ A | F ∈ rhombusFaces X} with hArh
  set Acap := {F ∈ A | F ∉ contactFaces X} with hAcap
  -- the sides split into exceptional faces, rhombi and caps
  have hsplit : A.ncard = Aex.ncard + Arh.ncard + Acap.ncard := by
    have h1 : A = (Aex ∪ Arh) ∪ Acap := by
      ext F
      simp only [hAex, hArh, hAcap, mem_union, mem_setOf_eq, exceptionalFaces, rhombusFaces]
      constructor
      · intro hF
        by_cases hc : F ∈ contactFaces X
        · have h4 := four_le_faceSize hsep htri hc
          rcases Nat.lt_or_ge 4 (faceSize X F) with h | h
          · exact Or.inl (Or.inl ⟨hF, hc, h⟩)
          · exact Or.inl (Or.inr ⟨hF, hc, le_antisymm h h4⟩)
        · exact Or.inr ⟨hF, hc⟩
      · rintro ((⟨hF, -⟩ | ⟨hF, -⟩) | ⟨hF, -⟩) <;> exact hF
    have hf1 : Aex.Finite := hAfin.subset fun F hF => hF.1
    have hf2 : Arh.Finite := hAfin.subset fun F hF => hF.1
    have hf3 : Acap.Finite := hAfin.subset fun F hF => hF.1
    rw [h1, ncard_union_eq _ (hf1.union hf2) hf3, ncard_union_eq _ hf1 hf2]
    · rw [Set.disjoint_left]
      rintro F ⟨-, -, h5⟩ ⟨-, -, h4⟩
      rw [h4] at h5; norm_num at h5
    · rw [Set.disjoint_left]
      rintro F (⟨-, hc, -⟩ | ⟨-, hc, -⟩) ⟨-, hnc⟩ <;> exact hnc hc
  -- exceptional sides are the face ports
  have hex : ((exceptionalFinset X).filter (fun F => IsPort X (Sum.inl F) e)).card = Aex.ncard := by
    rw [← Set.ncard_coe_finset, Finset.coe_filter]
    congr 1
    ext F
    simp only [mem_setOf_eq, mem_exceptionalFinset hsep, IsPort, hAex, hAdef, augSides]
    constructor
    · rintro ⟨-, hF, hb⟩
      exact ⟨⟨hsubA hfm X hX hF.1, by rw [hbd hfm X hX F hF.1]; exact hb⟩, hF⟩
    · rintro ⟨⟨-, hb⟩, hF⟩
      exact ⟨hF, hF, by rw [← hbd hfm X hX F hF.1]; exact hb⟩
  -- rhombus sides are the rhombi containing `e`
  have hrh : (rhombiAt X e).card = Arh.ncard := by
    have hinj : Set.InjOn cInterior ((rhombi X : Finset (Finset Plane)) : Set (Finset Plane)) := by
      intro R hR R' hR' h
      have e1 := (rhombus_mem_rhombusFaces hsep htri hR).2
      have e2 := (rhombus_mem_rhombusFaces hsep htri hR').2
      rw [h, ← e2] at e1
      exact Finset.coe_injective (Set.image_injective.2 toC.injective e1)
    have himg : Arh = cInterior '' ((rhombiAt X e : Finset (Finset Plane)) : Set (Finset Plane)) := by
      ext F
      simp only [hArh, hAdef, augSides, mem_setOf_eq, mem_image, Finset.mem_coe, rhombiAt,
        Finset.mem_filter]
      constructor
      · rintro ⟨⟨-, hb⟩, hF⟩
        obtain ⟨R, hR, rfl⟩ := (mem_rhombusFaces_iff hsep htri).1 hF
        refine ⟨R, ⟨hR, fun x hx => ?_⟩, rfl⟩
        rw [hbd hfm X hX _ hF.1] at hb
        have hv := (rhombus_mem_rhombusFaces hsep htri hR).2
        have : toC x ∈ toC '' (R : Set Plane) := by
          rw [hv]; exact ⟨e', hb, Sym2.mem_map.2 ⟨x, hx, rfl⟩⟩
        obtain ⟨y, hy, hyx⟩ := this
        rw [toC.injective hyx] at hy
        exact hy
      · rintro ⟨R, ⟨hR, hsub⟩, rfl⟩
        have hF := (rhombus_mem_rhombusFaces hsep htri hR).1
        obtain ⟨⟨x, y⟩, hp, rfl⟩ := Finset.mem_image.1 he
        simp only [Finset.mem_filter, Finset.mem_product] at hp
        have hb := map_mem_bdry_cInterior hsep htri hR (hsub x (Sym2.mem_mk_left _ _))
          (hsub y (Sym2.mem_mk_right _ _)) hp.2
        refine ⟨⟨hsubA hfm X hX hF.1, ?_⟩, hF⟩
        rw [hbd hfm X hX _ hF.1]; exact hb
    have hinj' : Set.InjOn cInterior ((rhombiAt X e : Finset (Finset Plane)) : Set (Finset Plane)) :=
      hinj.mono (fun R hR => (Finset.mem_filter.1 (Finset.mem_coe.1 hR)).1)
    rw [himg, hinj'.ncard_image, Set.ncard_coe_finset]
  -- cap sides are the ports at non-unit hull returns
  have hcap : ((ccwHullSides X).filter (fun p => ¬ dist p.1 p.2 = 1 ∧ IsPort X (Sum.inr p) e)).card =
      Acap.ncard := by
    have himg : Acap = capOf X '' (((ccwHullSides X).filter
        (fun p => ¬ dist p.1 p.2 = 1 ∧ IsPort X (Sum.inr p) e) : Finset _) : Set (Plane × Plane)) := by
      ext F
      simp only [hAcap, hAdef, augSides, mem_setOf_eq, mem_image, Finset.coe_filter, IsPort]
      constructor
      · rintro ⟨⟨hFa, hb⟩, hnc⟩
        rcases hcases hfm X hX F hFa with hc | ⟨p, hp, hd, hcapF⟩
        · exact absurd hc hnc
        have hd' : dist p.1 p.2 ≠ 1 := ne_of_gt hd
        refine ⟨p, ⟨hp, hd', hp, he, ?_⟩, ?_⟩
        · rw [if_neg hd']; exact ⟨F, hcapF, hb⟩
        · exact huniq hfm X hX p hp _ _ (capOf_spec ⟨F, hcapF⟩) hcapF
      · rintro ⟨p, ⟨hp, hd, -, -, hport⟩, rfl⟩
        rw [if_neg hd] at hport
        obtain ⟨F, hcapF, hb⟩ := hport
        have hF : capOf X p = F := huniq hfm X hX p hp _ _ (capOf_spec ⟨F, hcapF⟩) hcapF
        rw [hF]
        refine ⟨⟨hcapF.1, hb⟩, fun hc => hd ?_⟩
        have h2 := hcapF.2
        rw [hbd hfm X hX F hc] at h2
        have := (Finset.mem_filter.1 h2).1
        rw [cUnitEdges, mem_unitPairs, dist_toC] at this
        exact this.2.2
    rw [himg, Set.InjOn.ncard_image, Set.ncard_coe_finset]
    intro p hp p' hp' h
    simp only [Finset.coe_filter, mem_setOf_eq] at hp hp'
    have hex1 : ∃ F, IsCap X p.1 p.2 F := by
      have := hp.2.2.2.2; rw [if_neg hp.2.1] at this
      obtain ⟨F, hF, -⟩ := this; exact ⟨F, hF⟩
    have hex2 : ∃ F, IsCap X p'.1 p'.2 F := by
      have := hp'.2.2.2.2; rw [if_neg hp'.2.1] at this
      obtain ⟨F, hF, -⟩ := this; exact ⟨F, hF⟩
    have c1 := capOf_spec hex1
    have c2 := capOf_spec hex2
    rw [← h] at c2
    obtain ⟨S, hSV, -, hext, hFint, hbdS, -⟩ := hpoly hfm X hX _ c1.1
    have hb1 : s(toC p.1, toC p.2) ∈ cSides S := hbdS ▸ c1.2
    have hb2 : s(toC p'.1, toC p'.2) ∈ cSides S := hbdS ▸ c2.2
    exact ccwHullSides_eq_of_toC_eq hint hp.1 hp'.1
      (hullSides_of_polygon_eq (hPa hfm X hX) (hconn hfm X hX) c1.1.1 hFint hSV hext hp.1 hp'.1
        hp.2.1 hp'.2.1 hb1 hb2)
  -- the unit hull side through `e`
  have hunit : ((ccwHullSides X).filter (fun p => dist p.1 p.2 = 1 ∧ IsPort X (Sum.inr p) e)).card
      = if e' ∈ hullSideEdges X then 1 else 0 := by
    split_ifs with hh
    · obtain ⟨q, hq, hqe⟩ := Finset.mem_image.1 hh
      have heq : e = s(q.1, q.2) :=
        Sym2.map.injective toC.injective (by rw [sym2_map_toC]; exact hqe.symm)
      have hdq : dist q.1 q.2 = 1 := by
        rw [heq] at he; exact (mem_unitEdges.1 he).2.2
      rw [Finset.card_eq_one]
      refine ⟨q, Finset.eq_singleton_iff_unique_mem.2 ⟨Finset.mem_filter.2 ⟨hq, hdq, hq, he, ?_⟩,
        fun p hp => ?_⟩⟩
      · rw [if_pos hdq]; exact heq
      · obtain ⟨hp, hdp, -, -, hport⟩ := Finset.mem_filter.1 hp
        rw [if_pos hdp] at hport
        exact ccwHullSides_eq_of_mk_eq hint hp hq (hport ▸ heq)
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro p hp ⟨hdp, -, -, hport⟩
      rw [if_pos hdp] at hport
      exact hh (Finset.mem_image.2 ⟨p, hp, by rw [he'def, hport]; rfl⟩)
  -- the number of sides in the augmented graph
  have hA : A.ncard = if e' ∈ hullSideEdges X then 1 else 2 := by
    split_ifs with hh
    · obtain ⟨q, hq, hqe⟩ := Finset.mem_image.1 hh
      rw [hAdef, ← hqe]; exact hS1 hfm X hX q hq
    · exact hS2 hfm X hX e' he'C hh
  -- assemble
  have hsplit2 := Finset.card_filter_add_card_filter_not
    (s := (ccwHullSides X).filter (fun p => IsPort X (Sum.inr p) e))
    (fun p : Plane × Plane => dist p.1 p.2 = 1)
  rw [Finset.filter_filter, Finset.filter_filter,
    Finset.filter_congr (fun p _ => and_comm (a := IsPort X (Sum.inr p) e)),
    Finset.filter_congr (fun p _ => and_comm (a := IsPort X (Sum.inr p) e))] at hsplit2
  rw [card_ports, ← hsplit2, hex, hrh, hunit, hcap]
  by_cases hh : e' ∈ hullSideEdges X <;> simp only [hh, if_true, if_false] at hA ⊢ <;> omega

/-! ## Terminal incidences of tracks -/

/-- **Every track has exactly two terminal port incidences** (its two ends), including tracks
without rhombi.  Both ends may lie at the same node (a loop of the terminal multigraph). -/
theorem card_trackEnds :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ T ∈ allTracks X, (trackEnds X T).card = 2 := by
  filter_upwards [card_ports_add_card_rhombiAt] with n h hfm X hX htri T hT
  have hsep := hX.1.2
  have hsum : (trackEnds X T).card = ∑ e ∈ T, (ports X e).card := by
    rw [trackEnds, Finset.card_filter, Finset.sum_product_right]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [ports, Finset.card_filter]
  rw [hsum]
  rw [allTracks_eq, Finset.mem_union] at hT
  rcases hT with hT | hT
  · have key : ∑ e ∈ T, ((ports X e).card + (rhombiAt X e).card) = 2 * T.card := by
      rw [Finset.sum_congr rfl fun e he => h hfm X hX htri e (unitEdges_of_mem_tracks hT he),
        Finset.sum_const, smul_eq_mul, mul_comm]
    rw [Finset.sum_add_distrib] at key
    have h2 := sum_card_rhombi_containing hsep htri hT
    have h3 := card_eq_trackLength_add_one hsep htri hT
    simp only [rhombiAt] at key
    omega
  · obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hT
    obtain ⟨heu, her⟩ := Finset.mem_sdiff.1 he
    have := h hfm X hX htri e heu
    have h0 : (rhombiAt X e).card = 0 := by
      rw [Finset.card_eq_zero, rhombiAt, Finset.filter_eq_empty_iff]
      exact fun R hR => not_subset_rhombus_of_not_mem hsep htri heu her hR
    rw [Finset.sum_singleton]; omega

/-! ## Degrees of the nodes -/

/-- A `k`-gonal exceptional face has exactly `k` ports. -/
theorem portDeg_face {X : Finset Plane} {F : Set ℂ} (hF : F ∈ exceptionalFaces X) :
    portDeg X (Sum.inl F) = faceSize X F := by
  have : (unitEdges X).filter (IsPort X (Sum.inl F)) =
      (unitEdges X).filter (fun e => Sym2.map toC e ∈ bdryEdges (cUnitEdges X) F) :=
    Finset.filter_congr (fun e _ => by simp only [IsPort, hF, true_and])
  rw [portDeg, this, card_filter_unitEdges_map X (· ∈ bdryEdges (cUnitEdges X) F), faceSize, Finset.filter_mem_eq_inter,
    Finset.inter_eq_right.2 (show bdryEdges (cUnitEdges X) F ⊆ cUnitEdges X from
      Finset.filter_subset _ _)]

/-- A hull return of `j` unit edges has exactly `j` ports. -/
theorem portDeg_hullSide :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      ∀ p ∈ ccwHullSides X, portDeg X (Sum.inr p) = returnLength X p.1 p.2 := by
  filter_upwards [exists_cap, cap_unique, cap_other_sides_unit] with n hex huniq hother hfm X hX p hp
  have hs := mem_ccwHullSides.1 hp
  have hvX := mem_of_mem_hullVertices hs.1
  have hwX := mem_of_mem_hullVertices hs.2.1
  by_cases hd : dist p.1 p.2 = 1
  · rw [returnLength_of_dist_eq_one hd, portDeg, Finset.card_eq_one]
    refine ⟨s(p.1, p.2), Finset.eq_singleton_iff_unique_mem.2 ⟨Finset.mem_filter.2
      ⟨mem_unitEdges.2 ⟨hvX, hwX, hd⟩, hp, mem_unitEdges.2 ⟨hvX, hwX, hd⟩, by rw [if_pos hd]⟩,
      fun e he => ?_⟩⟩
    obtain ⟨-, -, -, h⟩ := Finset.mem_filter.1 he
    rwa [if_pos hd] at h
  · have hgt : 1 < dist p.1 p.2 := lt_of_le_of_ne (hX.1.2 _ hvX _ hwX hs.2.2.1) (Ne.symm hd)
    obtain ⟨F0, hF0⟩ := hex hfm X hX p hp
    have hsideU : s(toC p.1, toC p.2) ∉ cUnitEdges X := by
      intro h; rw [cUnitEdges, mem_unitPairs, dist_toC] at h; exact hd h.2.2
    have hfilt : (unitEdges X).filter (IsPort X (Sum.inr p)) =
        (unitEdges X).filter (fun e => Sym2.map toC e ∈ bdryEdges (augEdges X) F0) := by
      refine Finset.filter_congr (fun e he => ?_)
      simp only [IsPort, hp, he, true_and, if_neg hd]
      constructor
      · rintro ⟨F, hF, hb⟩; rwa [huniq hfm X hX p hp F F0 hF hF0] at hb
      · intro hb; exact ⟨F0, hF0, hb⟩
    have hbd : bdryEdges (augEdges X) F0 =
        insert (s(toC p.1, toC p.2)) ((cUnitEdges X).filter (· ∈ bdryEdges (augEdges X) F0)) := by
      ext e
      simp only [Finset.mem_insert, Finset.mem_filter]
      constructor
      · intro he
        by_cases hes : e = s(toC p.1, toC p.2)
        · exact Or.inl hes
        · exact Or.inr ⟨hother hfm X hX p hp hgt F0 hF0 e he hes, he⟩
      · rintro (rfl | ⟨-, he⟩)
        · exact hF0.2
        · exact he
    have hret : returnLength X p.1 p.2 = (bdryEdges (augEdges X) F0).card - 1 := by
      have hE : ∃ F, IsCap X p.1 p.2 F := ⟨F0, hF0⟩
      rw [returnLength, if_neg hd, dif_pos hE, huniq hfm X hX p hp _ _ hE.choose_spec hF0]
    rw [portDeg, hfilt, card_filter_unitEdges_map X (· ∈ bdryEdges (augEdges X) F0), hret]
    have hc := congrArg Finset.card hbd
    rw [Finset.card_insert_of_notMem (fun h => hsideU (Finset.mem_filter.1 h).1)] at hc
    omega

/-! ## Degree sums -/

/-- Summing port counts over the nodes is summing over the unit edges. -/
lemma sum_card_filter_isPort (X : Finset Plane) (g : Sym2 Plane → Prop) :
    ∑ N ∈ portNodes X, ((unitEdges X).filter (fun e => IsPort X N e ∧ g e)).card =
      ∑ e ∈ (unitEdges X).filter g, (ports X e).card := by
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases hg : g e
  · simp only [hg, and_true, if_true, ports, Finset.card_filter]
  · simp [hg]

/-- The tracks partition the unit edges. -/
lemma sum_allTracks_sum (X : Finset Plane) (f : Sym2 Plane → ℕ) :
    ∑ T ∈ allTracks X, ∑ e ∈ T, f e = ∑ e ∈ unitEdges X, f e := by
  rw [← Finset.sum_biUnion]
  · congr 1
    ext e
    simp only [Finset.mem_biUnion]
    constructor
    · rintro ⟨T, hT, he⟩; exact allTracks_subset_unitEdges hT he
    · intro he; exact ⟨_, allTrackOf_mem_allTracks he, mem_allTrackOf_self he⟩
  · intro T hT T' hT' hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro e h1 h2
    exact hne ((eq_allTrackOf_of_mem hT h1).trans (eq_allTrackOf_of_mem hT' h2).symm)

/-- **Degree sum for the terminal multigraph**: for any property `g` of tracks, the ports whose
track satisfies `g`, counted over all nodes, number twice the tracks satisfying `g`. -/
theorem sum_degrees_filter :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ g : Finset (Sym2 Plane) → Prop,
        ∑ N ∈ portNodes X, ((unitEdges X).filter (fun e => IsPort X N e ∧ g (allTrackOf X e))).card
          = 2 * ((allTracks X).filter g).card := by
  filter_upwards [card_trackEnds] with n hends hfm X hX htri g
  rw [sum_card_filter_isPort, Finset.sum_filter, ← sum_allTracks_sum]
  have key : ∀ T ∈ allTracks X, ∑ e ∈ T, (if g (allTrackOf X e) then (ports X e).card else 0) =
      if g T then 2 else 0 := by
    intro T hT
    rw [Finset.sum_congr rfl fun e he => by rw [← eq_allTrackOf_of_mem hT he]]
    split_ifs with hg
    · rw [← hends hfm X hX htri T hT, trackEnds, Finset.card_filter, Finset.sum_product_right]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [ports, Finset.card_filter]
    · simp
  rw [Finset.sum_congr rfl key, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]

/-! ## The end map of the terminal multigraph -/

/-- The two end nodes of a track, as a multiset (a loop contributes its node twice). -/
def endNodes (X : Finset Plane) (T : Finset (Sym2 Plane)) : Multiset PortNode :=
  (trackEnds X T).val.map Prod.fst

/-- Every track has exactly two end nodes (counted with multiplicity). -/
theorem card_endNodes :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ T ∈ allTracks X, Multiset.card (endNodes X T) = 2 := by
  filter_upwards [card_trackEnds] with n h hfm X hX htri T hT
  rw [endNodes, Multiset.card_map, ← h hfm X hX htri T hT]
  rfl

/-- The multiplicity of a node among the ends of `T` is its number of ports in `T`. -/
lemma count_endNodes (X : Finset Plane) (T : Finset (Sym2 Plane)) {N : PortNode}
    (hN : N ∈ portNodes X) : (endNodes X T).count N = (T.filter (IsPort X N)).card := by
  rw [endNodes, Multiset.count_map, ← Finset.filter_val, Finset.card_val, trackEnds,
    Finset.filter_filter, Finset.card_filter, Finset.sum_product_right, Finset.card_filter]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only
  rw [Finset.sum_eq_single N (fun b _ hb => by simp [Ne.symm hb]) (fun h => absurd hN h)]
  simp

/-- **The degree of a node is the number of track ends at it** (loops counted twice). -/
theorem sum_count_endNodes (X : Finset Plane) {N : PortNode} (hN : N ∈ portNodes X) :
    ∑ T ∈ allTracks X, (endNodes X T).count N = portDeg X N := by
  have : ∀ T ∈ allTracks X, (endNodes X T).count N =
      ∑ e ∈ T, (if IsPort X N e then 1 else 0) := fun T _ => by
    rw [count_endNodes X T hN, Finset.card_filter]
  rw [Finset.sum_congr rfl this, sum_allTracks_sum, portDeg, Finset.card_filter]

/-- **`2 · #{short tracks} = Σ_nodes shortDeg`.** -/
theorem sum_shortDeg :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ L : ℝ, ∑ N ∈ portNodes X, shortDeg X L N =
        2 * ((allTracks X).filter (fun T => (trackLength X T : ℝ) < L)).card := by
  filter_upwards [sum_degrees_filter] with n h hfm X hX htri L
  exact h hfm X hX htri (fun T => (trackLength X T : ℝ) < L)

/-- **`Σ_nodes deg = 2s`.** -/
theorem sum_portDeg :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∑ N ∈ portNodes X, portDeg X N = 2 * (allTracks X).card := by
  filter_upwards [sum_degrees_filter] with n h hfm X hX htri
  have := h hfm X hX htri (fun _ => True)
  simp only [and_true, Finset.filter_true] at this
  exact this

end Erdos99

end

end PortIncidence

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `ExactCounts`
-/

section ExactCounts

/-!
# Exact counting identities (WP3)

For a large optimal set `X` without unit triangles, under finite multiplicity, with

* `n = |X|`, `m` unit edges, `q` rhombi, `f` exceptional faces, `σ = Σ (k - 4) f_k`,
* `b` hull vertices (= hull sides = hull returns), `u` unit hull sides, `c₂` two-edge returns,
  `v = Σ_{j ≥ 3} c_j` (`numLongReturns`), `ρ = Σ_{j ≥ 3} (j - 2) c_j`, `ℓ = Σ_j j c_j`,
* `Δ = u - σ - ρ` (`lockingDefect`, an integer), and `s` the number of *all* tracks
  (`allTracks`, including tracks without rhombi),

we prove the exact identities

* `euler_count` (Lemma 2.2): `q + f = m - n + 1`;
* `two_mul_card_unitEdges` (Lemma 2.2): `2m = ℓ + 4(q + f) + σ`;
* `two_mul_card_allTracks` (equation (2)): `2s = ℓ + σ + 4f`;
* `two_mul_card_allTracks_eq_defect` (equation (2)): `2s = 2b - Δ + 4f`;
* `hullVertices_card_split`: `b = u + c₂ + v` and `v ≤ ρ`;
* `numExceptional_split`, `faceExcess_split`: `f = p + h + f_hi`, `σ = p + 2h + σ_hi`;
* `card_longTracks_add_short`: `R + E = s` for a positive cutoff `L`;
* `exact_counts`: all of the above as real-valued identities, in the form used by
  `DirectCount.two_R_eq` (WP1).
-/

open scoped BigOperators Real
open EstablishedExternalResults Set Filter

@[expose] public noncomputable section

open Classical

namespace Erdos99

/-- **Lemma 2.2 (Euler's formula for the contact graph)**: `q + f + n = m + 1`, i.e.
`q + f = m - n + 1`. -/
theorem euler_count :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      (rhombi X).card + numExceptional X + X.card = (unitEdges X).card + 1 := by
  filter_upwards [cUnitEdges_connected] with n hconn hfm X hX htri
  have hsep := hX.1.2
  have hP := cUnitEdges_isPlaneGraph hsep
  obtain ⟨hfin, heul⟩ := euler_formula hP (hconn hfm X hX)
  rw [ncard_faces_eq hfin] at heul
  have hV : (cVerts X).card = X.card := Finset.card_image_of_injective _ toC.injective
  have hE : (cUnitEdges X).card = (unitEdges X).card := by
    rw [cUnitEdges_eq_image, Finset.card_image_of_injective _ (Sym2.map.injective toC.injective)]
  have hB : (boundedFaces (cVerts X) (cUnitEdges X)).ncard =
      (rhombi X).card + numExceptional X := by
    have hsplit : boundedFaces (cVerts X) (cUnitEdges X) = rhombusFaces X ∪ exceptionalFaces X := by
      ext F
      constructor
      · intro hF
        have h4 := four_le_faceSize hsep htri (F := F) hF
        rcases Nat.lt_or_ge 4 (faceSize X F) with h | h
        · exact Or.inr ⟨hF, h⟩
        · exact Or.inl ⟨hF, le_antisymm h h4⟩
      · rintro (⟨hF, -⟩ | ⟨hF, -⟩) <;> exact hF
    have hfB : (boundedFaces (cVerts X) (cUnitEdges X)).Finite := hfin.subset fun F hF => hF.1
    rw [hsplit] at hfB
    rw [hsplit, Set.ncard_union_eq _ (hfB.subset subset_union_left)
      (hfB.subset subset_union_right), ncard_rhombusFaces hsep htri]
    · rfl
    · rw [Set.disjoint_left]
      rintro F ⟨-, h4⟩ ⟨-, h5⟩
      rw [h4] at h5; norm_num at h5
  rw [hV, hE, hB] at heul
  omega

lemma disjoint_portNodes (X : Finset Plane) :
    Disjoint ((exceptionalFinset X).map Function.Embedding.inl)
      ((ccwHullSides X).map Function.Embedding.inr) := by
  rw [Finset.disjoint_left]
  intro N h1 h2
  obtain ⟨F, -, rfl⟩ := Finset.mem_map.1 h1
  obtain ⟨p, -, hp⟩ := Finset.mem_map.1 h2
  cases hp

/-- `Σ_{k ≥ 5} k f_k = 4 f + σ`. -/
lemma sum_faceSize_exceptional {X : Finset Plane} (hX : IsSeparated X) :
    ∑ F ∈ exceptionalFinset X, faceSize X F = 4 * numExceptional X + faceExcess X := by
  have hfin := finite_exceptionalFaces hX
  have hE : exceptionalFinset X = hfin.toFinset := by rw [exceptionalFinset, dif_pos hfin]
  have hn : numExceptional X = (exceptionalFinset X).card := by
    rw [numExceptional, ← coe_exceptionalFinset hX, Set.ncard_coe_finset]
  rw [faceExcess, finsum_mem_eq_finite_toFinset_sum _ hfin, ← hE, hn, mul_comm,
    ← smul_eq_mul, ← Finset.sum_const, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun F hF => ?_
  have h5 := ((mem_exceptionalFinset hX).1 hF).2
  omega

/-- **Equation (2)**: `2s = ℓ + σ + 4f`, where `s` counts all tracks (including tracks without
rhombi). -/
theorem two_mul_card_allTracks :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      2 * (allTracks X).card = outerWalkLength X + faceExcess X + 4 * numExceptional X := by
  filter_upwards [sum_portDeg, portDeg_hullSide] with n hsum hdeg hfm X hX htri
  have hsep := hX.1.2
  rw [← hsum hfm X hX htri, portNodes, Finset.sum_union (disjoint_portNodes X), Finset.sum_map,
    Finset.sum_map]
  simp only [Function.Embedding.inl_apply, Function.Embedding.inr_apply]
  rw [Finset.sum_congr rfl (fun F hF => portDeg_face ((mem_exceptionalFinset hsep).1 hF)),
    Finset.sum_congr rfl (fun p hp => hdeg hfm X hX p hp), sum_faceSize_exceptional hsep,
    outerWalkLength]
  ring

/-- **Lemma 2.2 (edge count)**: `2m = ℓ + 4(q + f) + σ`. -/
theorem two_mul_card_unitEdges :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      2 * (unitEdges X).card =
        outerWalkLength X + 4 * ((rhombi X).card + numExceptional X) + faceExcess X := by
  filter_upwards [two_mul_card_allTracks] with n h hfm X hX htri
  have h1 := h hfm X hX htri
  have h2 := card_allTracks_add hX.1.2 htri
  omega

/-- **Equation (2), signed form**: `2s = 2b - Δ + 4f`, with `Δ = u - σ - ρ` the (signed) locking
defect. -/
theorem two_mul_card_allTracks_eq_defect :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      (2 * (allTracks X).card : ℤ) =
        2 * (hullVertices X).card - lockingDefect X + 4 * numExceptional X := by
  filter_upwards [two_mul_card_allTracks, outerWalkLength_eq_eventually] with n h hl hfm X hX htri
  have h1 : (2 * (allTracks X).card : ℤ) =
      outerWalkLength X + faceExcess X + 4 * numExceptional X := by
    exact_mod_cast h hfm X hX htri
  rw [h1, hl hfm X hX, lockingDefect]
  ring

/-- `v = Σ_{j ≥ 3} c_j`: the number of hull returns of at least three unit edges. -/
def numLongReturns (X : Finset Plane) : ℕ :=
  ((ccwHullSides X).filter (fun p => 3 ≤ returnLength X p.1 p.2)).card

/-- **`b = u + c₂ + v`, and `v ≤ ρ`.** -/
theorem hullVertices_card_split :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      (hullVertices X).card = numUnitHullSides X + hullReturns X 2 + numLongReturns X ∧
        numLongReturns X ≤ returnExcess X := by
  filter_upwards [two_le_returnLength, hullReturns_one_eventually, eventually_not_collinear] with
    n h2 h1 hcol hfm X hX
  refine ⟨?_, ?_⟩
  · rw [← card_ccwHullSides (three_le_card_hullVertices (hcol X hX)), ← h1 hfm X hX, hullReturns,
      hullReturns, numLongReturns, Finset.card_filter, Finset.card_filter, Finset.card_filter,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.card_eq_sum_ones]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hj : 1 ≤ returnLength X p.1 p.2 := by
      by_cases hd : dist p.1 p.2 = 1
      · rw [returnLength_of_dist_eq_one hd]
      · have := h2 hfm X hX p hp hd; omega
    rcases Nat.lt_or_ge (returnLength X p.1 p.2) 3 with h | h
    · interval_cases (returnLength X p.1 p.2) <;> simp
    · have h1' : returnLength X p.1 p.2 ≠ 1 := by omega
      have h2' : returnLength X p.1 p.2 ≠ 2 := by omega
      simp [h1', h2', h]
  · rw [numLongReturns, returnExcess, Finset.card_filter]
    refine Finset.sum_le_sum fun p _ => ?_
    split_ifs with h <;> omega

/-! ## High faces -/

/-- `f_hi = Σ_{k ≥ 7} f_k`: the number of exceptional faces with at least seven sides. -/
def numHighFaces (X : Finset Plane) : ℕ :=
  ((exceptionalFinset X).filter (fun F => 7 ≤ faceSize X F)).card

/-- `σ_hi = Σ_{k ≥ 7} (k - 4) f_k`. -/
def highFaceExcess (X : Finset Plane) : ℕ :=
  ∑ F ∈ (exceptionalFinset X).filter (fun F => 7 ≤ faceSize X F), (faceSize X F - 4)

lemma faceCount_eq_card_exceptionalFinset {X : Finset Plane} (hX : IsSeparated X) {k : ℕ}
    (hk : 5 ≤ k) : faceCount X k = ((exceptionalFinset X).filter (fun F => faceSize X F = k)).card := by
  rw [faceCount, ← Set.ncard_coe_finset, Finset.coe_filter]
  congr 1
  ext F
  simp only [mem_setOf_eq, ← Finset.mem_coe, coe_exceptionalFinset hX, exceptionalFaces]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2 ▸ hk⟩, h2⟩
  · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩

/-- `f = p + h + f_hi`. -/
theorem numExceptional_split {X : Finset Plane} (hX : IsSeparated X) :
    numExceptional X = numPentagons X + numHexagons X + numHighFaces X := by
  rw [numPentagons, numHexagons, faceCount_eq_card_exceptionalFinset hX (le_refl 5),
    faceCount_eq_card_exceptionalFinset hX (by norm_num : 5 ≤ 6), numHighFaces, numExceptional,
    ← coe_exceptionalFinset hX, Set.ncard_coe_finset, Finset.card_filter, Finset.card_filter,
    Finset.card_filter, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun F hF => ?_
  have h5 := ((mem_exceptionalFinset hX).1 hF).2
  rcases Nat.lt_or_ge (faceSize X F) 7 with h | h
  · interval_cases (faceSize X F) <;> simp
  · have h1 : faceSize X F ≠ 5 := by omega
    have h2 : faceSize X F ≠ 6 := by omega
    simp [h1, h2, h]

/-- `σ = p + 2h + σ_hi`. -/
theorem faceExcess_split {X : Finset Plane} (hX : IsSeparated X) :
    faceExcess X = numPentagons X + 2 * numHexagons X + highFaceExcess X := by
  have hfin := finite_exceptionalFaces hX
  have hE : exceptionalFinset X = hfin.toFinset := by rw [exceptionalFinset, dif_pos hfin]
  rw [faceExcess, finsum_mem_eq_finite_toFinset_sum _ hfin, ← hE, numPentagons, numHexagons,
    faceCount_eq_card_exceptionalFinset hX (le_refl 5),
    faceCount_eq_card_exceptionalFinset hX (by norm_num : 5 ≤ 6), highFaceExcess,
    Finset.sum_filter, Finset.card_filter, Finset.card_filter, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun F hF => ?_
  have h5 := ((mem_exceptionalFinset hX).1 hF).2
  rcases Nat.lt_or_ge (faceSize X F) 7 with h | h
  · interval_cases (faceSize X F) <;> simp
  · have h1 : faceSize X F ≠ 5 := by omega
    have h2 : faceSize X F ≠ 6 := by omega
    simp [h1, h2, h]

/-! ## Long and short tracks -/

/-- For a positive cutoff `L`, the long tracks are the tracks of `allTracks X` with at least `L`
rhombi. -/
lemma longTracks_eq_filter_allTracks {X : Finset Plane} (hX : IsSeparated X)
    (htri : ¬ HasUnitTriangle X) {L : ℝ} (hL : 0 < L) :
    longTracks X L = (allTracks X).filter (fun T => L ≤ (trackLength X T : ℝ)) := by
  ext T
  simp only [longTracks, Finset.mem_filter]
  constructor
  · rintro ⟨hT, hl⟩; exact ⟨tracks_subset_allTracks X hT, hl⟩
  · rintro ⟨hT, hl⟩
    have hpos : 0 < trackLength X T := by exact_mod_cast hL.trans_le hl
    rw [← allTracks_filter_pos hX htri]
    exact ⟨Finset.mem_filter.2 ⟨hT, hpos⟩, hl⟩

/-- **`R + E = s`**: for a positive cutoff `L`, the long tracks (`r(T) ≥ L`) and the short tracks
(`r(T) < L`, among all tracks) together are all tracks. -/
theorem card_longTracks_add_short {X : Finset Plane} (hX : IsSeparated X)
    (htri : ¬ HasUnitTriangle X) {L : ℝ} (hL : 0 < L) :
    (longTracks X L).card + ((allTracks X).filter (fun T => (trackLength X T : ℝ) < L)).card =
      (allTracks X).card := by
  rw [longTracks_eq_filter_allTracks hX htri hL, ← Finset.card_filter_add_card_filter_not
    (s := allTracks X) (fun T => L ≤ (trackLength X T : ℝ))]
  congr 2
  ext T; simp only [not_le]

/-! ## The exact identities in real form -/

/-- **The exact identities of WP3, as real numbers**, in the form of the hypotheses of
`DirectCount.two_R_eq`: with `s` all tracks, `E` the short tracks (`r(T) < L`), `R` the long
tracks, `b, u, c₂, v, f, p, h, f_hi, σ, σ_hi, Δ, ρ` as in §2.1 of the Verification Guide,

`b = u + c₂ + v`, `2s = 2b - Δ + 4f`, `f = p + h + f_hi`, `σ = p + 2h + σ_hi`, `Δ = u - σ - ρ`,
`R = s - E`, and moreover `v ≤ ρ`. -/
theorem exact_counts :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ L : ℝ, 0 < L →
        ((hullVertices X).card : ℝ) =
            numUnitHullSides X + hullReturns X 2 + numLongReturns X ∧
          (2 * (allTracks X).card : ℝ) =
            2 * (hullVertices X).card - lockingDefect X + 4 * numExceptional X ∧
          (numExceptional X : ℝ) = numPentagons X + numHexagons X + numHighFaces X ∧
          (faceExcess X : ℝ) = numPentagons X + 2 * numHexagons X + highFaceExcess X ∧
          (lockingDefect X : ℝ) = numUnitHullSides X - faceExcess X - returnExcess X ∧
          ((longTracks X L).card : ℝ) = (allTracks X).card -
            ((allTracks X).filter (fun T => (trackLength X T : ℝ) < L)).card ∧
          (numLongReturns X : ℝ) ≤ returnExcess X := by
  filter_upwards [hullVertices_card_split, two_mul_card_allTracks_eq_defect] with n hb hs hfm X hX
    htri L hL
  have hsep := hX.1.2
  obtain ⟨hb1, hb2⟩ := hb hfm X hX
  have hs1 := hs hfm X hX htri
  have hR := card_longTracks_add_short hsep htri hL
  refine ⟨by exact_mod_cast hb1, ?_, by exact_mod_cast numExceptional_split hsep,
    by exact_mod_cast faceExcess_split hsep, ?_, ?_, by exact_mod_cast hb2⟩
  · have : ((2 * (allTracks X).card : ℤ) : ℝ) =
        ((2 * (hullVertices X).card - lockingDefect X + 4 * numExceptional X : ℤ) : ℝ) := by
      rw [hs1]
    push_cast at this
    exact this
  · rw [lockingDefect]; push_cast; ring
  · have : ((longTracks X L).card : ℝ) +
        ((allTracks X).filter (fun T => (trackLength X T : ℝ) < L)).card = (allTracks X).card := by
      exact_mod_cast hR
    linarith

end Erdos99

end

end ExactCounts

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `StressLocking`
-/

section StressLocking

/-!
# WP4: first-order locking and `Δ ≥ 0` (Verification Guide §7)

This file collects the WP4 results.

* `lockingDefect_nonneg_of_rowCount` (§7.5, per configuration): the row count
  `2n ≤ m + t + 2` together with Euler's formula `q + f + n = m + 1`, the edge count
  `2m = ℓ + 4(q + f) + σ`, `ℓ = 2b - u + ρ` and the planar diameter bound `t ≤ b` give
  `Δ = u - σ - ρ ≥ 0`.
* `lockingDefect_nonneg_eventually` (§7.5): the same eventually, for optimal sets without unit
  triangles under finite multiplicity, from `locking_count` (Corollary 2.5) and WP3.

The only open input is `first_order_locking` (in `Overview`, used through
`locking_count`).
-/

open scoped BigOperators Real
open Filter EstablishedExternalResults

@[expose] public noncomputable section

open Classical

namespace Erdos99

/-- **§7.5, per configuration.** From the locking row count `2n ≤ m + t + 2`, the planar counts
`q + f + n = m + 1` and `2m = ℓ + 4(q + f) + σ`, the outer-walk identity `ℓ = 2b - u + ρ`, and
`t ≤ b`, the locking defect `Δ = u - σ - ρ` is nonnegative.  (Indeed `ℓ + σ ≤ 2t ≤ 2b`.) -/
theorem lockingDefect_nonneg_of_rowCount {X : Finset Plane}
    (hrows : 2 * X.card ≤ (unitEdges X).card + (diamPairs X).card + 2)
    (heuler : (rhombi X).card + numExceptional X + X.card = (unitEdges X).card + 1)
    (hedges : 2 * (unitEdges X).card =
        outerWalkLength X + 4 * ((rhombi X).card + numExceptional X) + faceExcess X)
    (hwalk : (outerWalkLength X : ℤ) =
        2 * (hullVertices X).card - numUnitHullSides X + returnExcess X) :
    0 ≤ lockingDefect X := by
  have ht := diamPairs_card_le_hullVertices X
  have h1 : (outerWalkLength X : ℤ) + faceExcess X ≤ 2 * (diamPairs X).card := by
    have hr : (2 * X.card : ℤ) ≤ (unitEdges X).card + (diamPairs X).card + 2 := by
      exact_mod_cast hrows
    have he : ((rhombi X).card : ℤ) + numExceptional X + X.card = (unitEdges X).card + 1 := by
      exact_mod_cast heuler
    have hm : (2 * (unitEdges X).card : ℤ) =
        outerWalkLength X + 4 * ((rhombi X).card + numExceptional X) + faceExcess X := by
      exact_mod_cast hedges
    linarith
  have ht' : ((diamPairs X).card : ℤ) ≤ (hullVertices X).card := by exact_mod_cast ht
  rw [lockingDefect]
  linarith

/-- **`Δ ≥ 0`** (§7.5): eventually, for optimal sets without unit triangles under finite
multiplicity, the locking defect `Δ = u - σ - ρ` is nonnegative.  Derived from Corollary 2.5
(`locking_count`, which rests on the open lemma `first_order_locking`) and the exact counting
identities of WP3. -/
theorem lockingDefect_nonneg_eventually :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      0 ≤ lockingDefect X := by
  filter_upwards [locking_count, euler_count, two_mul_card_unitEdges,
    outerWalkLength_eq_eventually] with n hl he hm hw hfm X hX htri
  have hrows := hl hfm X hX
  rw [← hX.1.1] at hrows
  exact lockingDefect_nonneg_of_rowCount hrows (he hfm X hX htri) (hm hfm X hX htri) (hw hfm X hX)

end Erdos99
end

end StressLocking

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `CapLanding`
-/

section CapLanding

/-!
# Cap arrivals land on forward cap sides (Verification Guide §9.3)

This file proves the cap landing lemma `cap_landing` and, from it, the cap capacity
`good_cap_tokens_le` used by the emission lemma.

* `leftStep_of_rhombusFace_left`: a quadrilateral face on the left of a unit edge gives a left
  step (the track continues).
* `exists_augFace_left`: on the left of a unit edge lies a bounded face of the augmented graph,
  unless the reversed edge is a hull side.
* `far_end_cases`: the far end of a track ending on a cap is either a reversed unit hull side, or
  an oriented boundary edge of the cap of a non-unit hull side, with the cap on its left.
* `cap_vertex_near`: the vertices of the cap of `p` are within `j` of `p.1`, where `j` is the
  length of the return.
* `cap_area_le`: caps have area `O(D)`; hence (`cap_two_balls`, `large_cap_two_balls`) labels
  starting near one cap start in two balls of radius `D^{1 - e/4}`.
* `card_long_returns_le`: given `Δ ≥ 0`, at most `π D / (B - 2)` returns have more than `B` edges.
-/

open scoped BigOperators Real
open Filter Topology MeasureTheory Set EstablishedExternalResults

@[expose] public noncomputable section

open Classical

namespace Erdos99

variable {X : Finset Plane}

/-! ## The face on the left of the far end -/

/-- A unit rhombus `a b c d` whose convex hull contains a nonempty set lying on the left of
`a → b` gives the left step `(a, b) → (d, c)`. -/
lemma leftStep_of_rhombus_left {a b c d : Plane} (ha : a ∈ X) (hb : b ∈ X) (hc : c ∈ X)
    (hd : d ∈ X) (h1 : dist a b = 1) (h2 : dist b c = 1) (h3 : dist c d = 1) (h4 : dist d a = 1)
    (hac : a ≠ c) (hbd : b ≠ d) {F : Set ℂ} (hFne : F.Nonempty)
    (hFsub : F ⊆ convexHull ℝ ({toC a, toC b, toC c, toC d} : Set ℂ))
    (hl : ∀ z ∈ F, 0 < (wc (toC a) (toC b) z).im) : LeftStep X (a, b) (d, c) := by
  have hpar := rhombus_parallelogram hac hbd h1 h2 h3 h4
  have ne1 : ∀ {x y : Plane}, dist x y = 1 → x ≠ y := fun h e => by
    rw [e, dist_self] at h; norm_num at h
  have hab := ne1 h1
  have hbc := ne1 h2
  have hcd := ne1 h3
  have hda := ne1 h4
  have hca : c - a = (b - a) + (d - a) := by
    have : c = b + d - a := by rw [← hpar]; abel
    rw [this]; abel
  refine ⟨?_, h1, h2, h3, h4, ?_, ?_⟩
  · refine Finset.mem_filter.2 ⟨Finset.mem_powersetCard.2 ⟨?_, ?_⟩, a, b, c, d, rfl, h1, h2, h3,
      h4⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl <;> assumption
    · rw [Finset.card_insert_of_notMem (by simp [hab, hac, hda.symm]),
        Finset.card_insert_of_notMem (by simp [hbc, hbd]), Finset.card_pair hcd]
  · show c - d = b - a
    rw [sub_eq_sub_iff_add_eq_add, add_comm, hpar, add_comm]
  · show 0 < det2 (b - a) (d - a)
    by_contra hδ
    push_neg at hδ
    obtain ⟨z0, hz0⟩ := hFne
    have hsq : 0 ≤ ‖b - a‖ ^ 2 := sq_nonneg _
    have hsub : convexHull ℝ ({toC a, toC b, toC c, toC d} : Set ℂ) ⊆
        {z | 0 ≤ (wc (toC b) (toC a) z).im} := by
      refine convexHull_min ?_ (convex_wc_im_nonneg _ _)
      intro v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      show 0 ≤ (wc (toC b) (toC a) v).im
      rw [wc_im_swap]
      rcases hv with rfl | rfl | rfl | rfl
      · rw [wc_toC_im, sub_self]; simp [det2]
      · rw [wc_toC_im, det2_self']; simp
      · rw [wc_toC_im, hca, det2_add_right_hop, det2_self', zero_add]
        exact neg_nonneg.2 (div_nonpos_of_nonpos_of_nonneg hδ hsq)
      · rw [wc_toC_im]
        exact neg_nonneg.2 (div_nonpos_of_nonpos_of_nonneg hδ hsq)
    have h5 := hsub (hFsub hz0)
    have h6 := hl z0 hz0
    rw [Set.mem_setOf_eq, wc_im_swap] at h5
    linarith

/-- **A quadrilateral face on the left of a unit edge gives a left step.** -/
theorem leftStep_of_rhombusFace_left (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X)
    {F : Set ℂ} (hF : F ∈ contactFaces X) (h4 : faceSize X F = 4) {a b : Plane}
    (hb : s(toC a, toC b) ∈ bdryEdges (cUnitEdges X) F)
    (hl : ∀ z ∈ F, 0 < (wc (toC a) (toC b) z).im) : ∃ q, LeftStep X (a, b) q := by
  have hP := cUnitEdges_isPlaneGraph hX
  obtain ⟨-, hcyc⟩ := cycle_of_not_forest (Finset.filter_subset _ _) (cVerts_tri htri)
    (not_forest_bdryEdges_of_bounded hP hF.1 hF.2)
  obtain ⟨a', b', c', d', hab, hac, had, hbc, hbd, hcd, hB⟩ := hcyc h4
  have hE : ∀ e ∈ ({s(a', b'), s(b', c'), s(c', d'), s(d', a')} : Finset (Sym2 ℂ)),
      e ∈ unitPairs (cVerts X) := by
    intro e he; rw [← hB] at he; exact (Finset.mem_filter.1 he).1
  obtain ⟨ha, hb', h1⟩ := mem_unitPairs.1 (hE s(a', b') (by simp))
  obtain ⟨-, hc, h2⟩ := mem_unitPairs.1 (hE s(b', c') (by simp))
  obtain ⟨-, hd, h3⟩ := mem_unitPairs.1 (hE s(c', d') (by simp))
  obtain ⟨-, -, h4'⟩ := mem_unitPairs.1 (hE s(d', a') (by simp))
  have htr := cVerts_tri htri
  have hac1 : dist a' c' ≠ 1 := fun h => htr a' ha b' hb' c' hc h1 h2 (by rw [dist_comm]; exact h)
  have hbd1 : dist b' d' ≠ 1 := fun h => htr b' hb' c' hc d' hd h2 h3 (by rw [dist_comm]; exact h)
  obtain ⟨hface, hbdry, hbdd⟩ := unit_rhombus_face hP (cVerts_sep hX)
    ha hb' hc hd h1 h2 h3 h4' hac1 hbd1 hac hbd
  have hFG := eq_of_bdryEdges_cycle4_bounded hP hF.1 hface hF.2 hbdd hab hac had hbc hbd hcd
    hB hbdry
  have hFne : F.Nonempty := by
    obtain ⟨x, hx, hFx⟩ := mem_faces_iff.1 hF.1
    exact ⟨x, hFx ▸ mem_connectedComponentIn hx⟩
  have gen : ∀ w x y z : ℂ, w ∈ cVerts X → x ∈ cVerts X → y ∈ cVerts X → z ∈ cVerts X →
      dist w x = 1 → dist x y = 1 → dist y z = 1 → dist z w = 1 → w ≠ y → x ≠ z →
      ({w, x, y, z} : Set ℂ) = {a', b', c', d'} → toC a = w → toC b = x →
      ∃ q, LeftStep X (a, b) q := by
    intro w x y z hw hx hy hz e1 e2 e3 e4 hwy hxz hset hA hB'
    refine ⟨(toC.symm z, toC.symm y), ?_⟩
    have ea : a = toC.symm w := by rw [← hA, LinearIsometryEquiv.symm_apply_apply]
    have eb : b = toC.symm x := by rw [← hB', LinearIsometryEquiv.symm_apply_apply]
    have dd : ∀ u v : ℂ, dist (toC.symm u) (toC.symm v) = dist u v := fun u v =>
      LinearIsometryEquiv.dist_map _ _ _
    rw [ea, eb]
    refine leftStep_of_rhombus_left (mem_cVerts.1 hw) (mem_cVerts.1 hx) (mem_cVerts.1 hy)
      (mem_cVerts.1 hz) (by rw [dd]; exact e1) (by rw [dd]; exact e2) (by rw [dd]; exact e3)
      (by rw [dd]; exact e4) (fun h => hwy (toC.symm.injective h))
      (fun h => hxz (toC.symm.injective h)) hFne ?_ ?_
    · simp only [LinearIsometryEquiv.apply_symm_apply]
      rw [hset, hFG]
      exact interior_subset
    · simp only [LinearIsometryEquiv.apply_symm_apply]
      rw [← hA, ← hB']
      exact hl
  have hb2 : s(toC a, toC b) ∈ ({s(a', b'), s(b', c'), s(c', d'), s(d', a')} :
      Finset (Sym2 ℂ)) := by rw [← hB]; exact hb
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb2
  rcases hb2 with h | h | h | h <;> rcases Sym2.eq_iff.1 h with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact gen a' b' c' d' ha hb' hc hd h1 h2 h3 h4' hac hbd rfl e1 e2
  · exact gen b' a' d' c' hb' ha hd hc (by rw [dist_comm]; exact h1) (by rw [dist_comm]; exact h4')
      (by rw [dist_comm]; exact h3) (by rw [dist_comm]; exact h2) hbd hac
      (by ext; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_comm, or_left_comm]) e1 e2
  · exact gen b' c' d' a' hb' hc hd ha h2 h3 h4' h1 hbd hac.symm
      (by ext; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_comm, or_left_comm]) e1 e2
  · exact gen c' b' a' d' hc hb' ha hd (by rw [dist_comm]; exact h2) (by rw [dist_comm]; exact h1)
      (by rw [dist_comm]; exact h4') (by rw [dist_comm]; exact h3) hac.symm hbd
      (by ext; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_comm, or_left_comm]) e1 e2
  · exact gen c' d' a' b' hc hd ha hb' h3 h4' h1 h2 hac.symm hbd.symm
      (by ext; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_comm, or_left_comm]) e1 e2
  · exact gen d' c' b' a' hd hc hb' ha (by rw [dist_comm]; exact h3) (by rw [dist_comm]; exact h2)
      (by rw [dist_comm]; exact h1) (by rw [dist_comm]; exact h4') hbd.symm hac.symm
      (by ext; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_comm, or_left_comm]) e1 e2
  · exact gen d' a' b' c' hd ha hb' hc h4' h1 h2 h3 hbd.symm hac
      (by ext; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_comm, or_left_comm]) e1 e2
  · exact gen a' d' c' b' ha hd hc hb' (by rw [dist_comm]; exact h4') (by rw [dist_comm]; exact h3)
      (by rw [dist_comm]; exact h2) (by rw [dist_comm]; exact h1) hac hbd.symm
      (by ext; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_comm, or_left_comm]) e1 e2

/-- **The bounded face on the left of a unit edge.**  On the left of an oriented unit edge
`a → b` lies a bounded face of the augmented graph having the edge on its boundary, unless
`b → a` is a counterclockwise hull side. -/
theorem exists_augFace_left :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      ∀ a ∈ X, ∀ b ∈ X, dist a b = 1 →
        (b, a) ∈ ccwHullSides X ∨ ∃ F ∈ augFaces X,
          s(toC a, toC b) ∈ bdryEdges (augEdges X) F ∧ ∀ z ∈ F, 0 < (wc (toC a) (toC b) z).im := by
  filter_upwards [exists_cap, augSides_interior, augFace_polygon, augEdges_isPlaneGraph,
    augFace_convex] with n hex hint2 hpoly hPa hconv hfm X hX a ha b hb hab
  have hAB : toC a ≠ toC b := by
    intro h
    rw [toC.injective h, dist_self] at hab
    norm_num at hab
  -- an augmented face with the edge on its boundary lies on one side of it
  have side : ∀ F ∈ augFaces X, s(toC a, toC b) ∈ bdryEdges (augEdges X) F →
      ∃ S : Finset ℂ, F = interior (convexHull ℝ (S : Set ℂ)) ∧ toC a ∈ S ∧ toC b ∈ S ∧
        ((∀ z ∈ F, 0 < (wc (toC a) (toC b) z).im) ∨ (∀ z ∈ F, 0 < (wc (toC b) (toC a) z).im)) := by
    intro F hF hbF
    obtain ⟨S, -, -, -, hFint, hbd, -⟩ := hpoly hfm X hX F hF
    rw [hbd] at hbF
    obtain ⟨⟨u, w⟩, huw, he⟩ := Finset.mem_image.1 hbF
    have hs : IsCSide S u w := (Finset.mem_filter.1 huw).2
    rcases Sym2.eq_iff.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [show u = toC a from h1, show w = toC b from h2] at hs
      exact ⟨S, hFint, hs.1, hs.2.1, Or.inl fun z hz => side_pos hs (hFint ▸ hz)⟩
    · rw [show u = toC b from h1, show w = toC a from h2] at hs
      exact ⟨S, hFint, hs.2.1, hs.1, Or.inr fun z hz => side_pos hs (hFint ▸ hz)⟩
  by_cases hh : s(toC a, toC b) ∈ hullSideEdges X
  · obtain ⟨v, w, hvw, he⟩ := hullSideEdges_cases hh
    rcases Sym2.eq_iff.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hv : a = v := toC.injective h1
      have hw : b = w := toC.injective h2
      subst hv hw
      obtain ⟨F, hF⟩ := hex hfm X hX (a, b) (mem_ccwHullSides.2 hvw)
      refine Or.inr ⟨F, hF.1, hF.2, fun z hz => ?_⟩
      have hzK : z ∈ interior (convexHull ℝ ((cVerts X : Finset ℂ) : Set ℂ)) :=
        interior_maximal (boundedFace_subset_hull (hPa hfm X hX) hF.1.1 hF.1.2)
          (isOpen_face hF.1.1) hz
      exact side_pos (isCSide_of_ccw hvw) hzK
    · have hv : a = w := toC.injective h1
      have hw : b = v := toC.injective h2
      subst hv hw
      exact Or.inl (mem_ccwHullSides.2 hvw)
  · have heU : s(toC a, toC b) ∈ cUnitEdges X := by
      rw [cUnitEdges, mem_unitPairs]
      exact ⟨Finset.mem_image_of_mem _ ha, Finset.mem_image_of_mem _ hb, by rw [dist_toC]; exact hab⟩
    obtain ⟨F1, F2, hne, hF12⟩ := Set.ncard_eq_two.1 (hint2 hfm X hX _ heU hh)
    have hF1 : F1 ∈ augSides X s(toC a, toC b) := by rw [hF12]; exact Set.mem_insert _ _
    have hF2 : F2 ∈ augSides X s(toC a, toC b) := by rw [hF12]; simp
    obtain ⟨S1, hS1, ha1, hb1, h1 | h1⟩ := side F1 hF1.1 hF1.2
    · exact Or.inr ⟨F1, hF1.1, hF1.2, h1⟩
    obtain ⟨S2, hS2, ha2, hb2, h2 | h2⟩ := side F2 hF2.1 hF2.2
    · exact Or.inr ⟨F2, hF2.1, hF2.2, h2⟩
    exfalso
    apply hne
    set m := (1 / 2 : ℝ) • toC b + (1 / 2 : ℝ) • toC a with hmdef
    have hm : m ∈ openSegment ℝ (toC b) (toC a) :=
      ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
    have key : ∀ F ∈ augFaces X, ∀ S : Finset ℂ, F = interior (convexHull ℝ (S : Set ℂ)) →
        toC a ∈ S → toC b ∈ S → (∀ z ∈ F, 0 < (wc (toC b) (toC a) z).im) →
        ∀ᶠ z in 𝓝 m, 0 < (wc (toC b) (toC a) z).im → z ∈ F := by
      intro F hF S hFint haS hbS hl
      have hFo := isOpen_face hF.1
      have hFc : Convex ℝ F := hconv hfm X hX F hF
      have hFne : F.Nonempty := by
        obtain ⟨x, hx, hFx⟩ := mem_faces_iff.1 hF.1
        exact ⟨x, hFx ▸ mem_connectedComponentIn hx⟩
      have hcl : closure F = convexHull ℝ (S : Set ℂ) := by
        rw [hFint, (convex_convexHull ℝ _).closure_interior_eq_closure_of_nonempty_interior
          (hFint ▸ hFne), S.finite_toSet.isCompact_convexHull.isClosed.closure_eq]
      obtain ⟨c, hc⟩ := hFne
      exact halfdisc hFc hFo (by rw [hcl]; exact subset_convexHull ℝ _ hbS)
        (by rw [hcl]; exact subset_convexHull ℝ _ haS) hc hm (hl c hc)
    obtain ⟨ε, hε, hE⟩ := Metric.eventually_nhds_iff.1
      ((key F1 hF1.1 S1 hS1 ha1 hb1 h1).and (key F2 hF2.1 S2 hS2 ha2 hb2 h2))
    have hn : 0 < ‖toC a - toC b‖ := norm_pos_iff.2 (sub_ne_zero.2 hAB)
    set η : ℝ := ε / (2 * ‖toC a - toC b‖) with hηdef
    have hη : 0 < η := by positivity
    set z := m + (η : ℂ) * (Complex.I * (toC a - toC b)) with hzdef
    have hz : dist z m < ε := by
      rw [dist_eq_norm, hzdef, add_sub_cancel_left, norm_mul, norm_mul, Complex.norm_real, Complex.norm_I,
        one_mul, Real.norm_of_nonneg hη.le]
      have : η * ‖toC a - toC b‖ = ε / 2 := by rw [hηdef]; field_simp
      rw [this]; linarith
    have hzpos : 0 < (wc (toC b) (toC a) z).im := by
      have hm0 := (mem_openSegment_wc hAB.symm hm).1
      rw [hzdef, wc_add_normal hAB.symm, Complex.add_im, hm0]
      simpa using hη
    have hz1 := (hE hz).1 hzpos
    have hz2 := (hE hz).2 hzpos
    rw [face_eq_component hF1.1.1 hz1, face_eq_component hF2.1.1 hz2]

/-- **Where a track ending on a cap ends.**  The far end of the track of a unit edge whose token
goes to a cap is a reversed unit hull side, or an oriented boundary edge of the cap of a non-unit
hull side, with the cap on its left. -/
theorem far_end_cases :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ q ∈ X ×ˢ X, dist q.1 q.2 = 1 → hopDest X q = .cap →
        ((hopEnd X q).2, (hopEnd X q).1) ∈ unitHullSides X ∨
        ∃ p ∈ ccwHullSides X, 1 < dist p.1 p.2 ∧ ∃ F, IsCap X p.1 p.2 F ∧
          s(toC (hopEnd X q).1, toC (hopEnd X q).2) ∈ bdryEdges (augEdges X) F ∧
          ∀ z ∈ F, 0 < (wc (toC (hopEnd X q).1) (toC (hopEnd X q).2) z).im := by
  filter_upwards [exists_augFace_left, augFace_cases, bdryEdges_aug_contact] with
    n hleft hcases hbdc hfm X hX htri q hq hq1 hdest
  have hmem := hopEnd_mem hq
  have haX := (Finset.mem_product.1 hmem).1
  have hbX := (Finset.mem_product.1 hmem).2
  have hba : (hopEnd X q).2 - (hopEnd X q).1 = q.2 - q.1 := hopEnd_sub _
  have hab : dist (hopEnd X q).1 (hopEnd X q).2 = 1 := by
    rw [dist_eq_norm', hba, ← dist_eq_norm', hq1]
  have hterm := hopEnd_terminal hq
  rcases hleft hfm X hX _ haX _ hbX hab with hrev | ⟨F, hF, hbd, hl⟩
  · left
    exact Finset.mem_filter.2 ⟨hrev, by rw [dist_comm]; exact hab⟩
  · rcases hcases hfm X hX F hF with hc | ⟨p, hp, hpd, hcap⟩
    · exfalso
      rw [hbdc hfm X hX F hc] at hbd
      have h4 := four_le_faceSize hX.1.2 htri hc
      rcases eq_or_lt_of_le h4 with h4 | h5
      · exact hterm (leftStep_of_rhombusFace_left hX.1.2 htri hc h4.symm hbd hl)
      · have hex : F ∈ exceptionalFaces X := ⟨hc, h5⟩
        have hor : (toC (hopEnd X q).1, toC (hopEnd X q).2) ∈ orientedSides X F :=
          Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨Finset.mem_image_of_mem _ haX,
            Finset.mem_image_of_mem _ hbX⟩, hbd, hl⟩
        rw [hopDest, dif_pos ⟨F, hex, hor⟩] at hdest
        cases hdest
    · right
      exact ⟨p, hp, hpd, F, hcap, hbd, hl⟩

/-! ## Caps: vertices, area and two-arc covering -/


lemma capCyc_mod {v : ℕ → ℂ} {m : ℕ} (hper : ∀ i, v (i + m) = v i) (x : ℕ) : v x = v (x % m) := by
  have key : ∀ r q, v (r + m * q) = v r := by
    intro r q
    induction q with
    | zero => simp
    | succ q ih => rw [Nat.mul_succ, ← add_assoc, hper, ih]
  conv_lhs => rw [← Nat.mod_add_div x m]
  exact key _ _

lemma capCyc_dvd {v : ℕ → ℂ} {m : ℕ} (hper : ∀ i, v (i + m) = v i) (hm : 0 < m)
    (hinj : Set.InjOn v (Set.Iio m)) {i0 t : ℕ} (h : v (i0 + t) = v i0) : m ∣ t := by
  rw [capCyc_mod hper (i0 + t), capCyc_mod hper i0] at h
  have h2 := hinj (Nat.mod_lt _ hm) (Nat.mod_lt _ hm) h
  have h3 : i0 + t ≡ i0 + 0 [MOD m] := by simpa [Nat.ModEq] using h2
  exact (Nat.modEq_zero_iff_dvd).1 (Nat.ModEq.add_left_cancel' i0 h3)

/-- In an `m`-periodic polygon `v` (injective on one period) in which every side not starting at
`v i0` has length at most one, every vertex is within `m - 1` of `v i0`. -/
lemma capCyc_dist {v : ℕ → ℂ} {m : ℕ} (hper : ∀ i, v (i + m) = v i) (hm : 0 < m)
    (hinj : Set.InjOn v (Set.Iio m)) (i0 : ℕ)
    (hunit : ∀ i, v i ≠ v i0 → ‖v (i + 1) - v i‖ ≤ 1) (k : ℕ) :
    ‖v k - v i0‖ ≤ (m : ℝ) - 1 := by
  have back : ∀ r, r ≤ m - 1 → ‖v (i0 + (m - r)) - v i0‖ ≤ r := by
    intro r
    induction r with
    | zero => intro _; simp [hper]
    | succ r ih =>
      intro hr
      have hne : v (i0 + (m - (r + 1))) ≠ v i0 := by
        intro h
        have := Nat.le_of_dvd (by omega) (capCyc_dvd hper hm hinj h)
        omega
      have h1 := hunit _ hne
      rw [show i0 + (m - (r + 1)) + 1 = i0 + (m - r) by omega] at h1
      have h2 := ih (by omega)
      have := norm_sub_le_norm_sub_add_norm_sub (v (i0 + (m - (r + 1)))) (v (i0 + (m - r))) (v i0)
      rw [norm_sub_rev] at h1
      push_cast
      linarith
  set d := (k + (m - 1) * i0) % m with hd
  have hdm : d < m := Nat.mod_lt _ hm
  have e1 : v k = v (i0 + d) := by
    rw [capCyc_mod hper k, capCyc_mod hper (i0 + d), hd, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    congr 1
    have : i0 + (k + (m - 1) * i0) = k + m * i0 := by
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    rw [this, Nat.add_mul_mod_self_left]
  rw [e1]
  rcases Nat.eq_zero_or_pos d with h0 | h0
  · rw [h0, add_zero, sub_self, norm_zero]
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  · have := back (m - d) (by omega)
    rw [show m - (m - d) = d by omega] at this
    refine this.trans ?_
    have : ((m - d : ℕ) : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : m - d ≤ m - 1)
    rw [Nat.cast_sub (by omega : 1 ≤ m)] at this
    simpa using this

/-- The endpoints of the boundary edges of the cap of `p` lie in its closure, within `j` of
`p.1`, where `j` is the number of edges of the return. -/
theorem cap_vertex_near :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      ∀ p ∈ ccwHullSides X, 1 < dist p.1 p.2 → ∀ F, IsCap X p.1 p.2 F →
      ∀ a b : Plane, s(toC a, toC b) ∈ bdryEdges (augEdges X) F →
        toC a ∈ closure F ∧ dist a p.1 ≤ returnLength X p.1 p.2 := by
  filter_upwards [cap_polygon, cap_other_sides_unit] with n hcap hother hfm X hX p hp hpd F hF a b hab
  obtain ⟨-, hpoly⟩ := hcap hfm X hX p hp hpd
  obtain ⟨S, hSV, hpS, hqS, h3, hext, hFint, hbd, hcard⟩ := hpoly F hF
  have hne : F.Nonempty := by
    obtain ⟨x, hx, hFx⟩ := mem_faces_iff.1 hF.1.1
    exact ⟨x, hFx ▸ mem_connectedComponentIn hx⟩
  have hint : (interior (convexHull ℝ (S : Set ℂ))).Nonempty := hFint ▸ hne
  have haS : toC a ∈ S := (mem_of_mem_cSides (hbd ▸ hab)).1
  have hcl : closure F = convexHull ℝ (S : Set ℂ) := by
    rw [hFint, (convex_convexHull ℝ _).closure_interior_eq_closure_of_nonempty_interior hint,
      S.finite_toSet.isCompact_convexHull.isClosed.closure_eq]
  refine ⟨hcl ▸ subset_convexHull ℝ _ haS, ?_⟩
  obtain ⟨v, hper, hvS, hinj, hside⟩ := PolyCycle.exists_cyclic_enum hext hint
  have hccw := isCSide_of_ccw (mem_ccwHullSides.1 hp)
  have hvw : IsCSide S (toC p.1) (toC p.2) :=
    ⟨hpS, hqS, hccw.2.2.1, fun c hc => hccw.2.2.2 c (hSV hc)⟩
  obtain ⟨i0, hv0, hv1⟩ := (hside _ _).1 hvw
  have hsurj : ∃ k, v k = toC a := by
    by_contra hno
    push_neg at hno
    have hsub : (Finset.range S.card).image v ⊆ S.erase (toC a) := by
      intro z hz
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hz
      exact Finset.mem_erase.2 ⟨hno k, hvS k⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_image_of_injOn (fun x hx y hy h => hinj (by simpa using hx)
      (by simpa using hy) h), Finset.card_range, Finset.card_erase_of_mem haS] at this
    omega
  obtain ⟨k, hk⟩ := hsurj
  have hm : 0 < S.card := by omega
  have hunit : ∀ i, v i ≠ v i0 → ‖v (i + 1) - v i‖ ≤ 1 := by
    intro i hi
    have hs : IsCSide S (v i) (v (i + 1)) := (hside _ _).2 ⟨i, rfl, rfl⟩
    have hmem : s(v i, v (i + 1)) ∈ bdryEdges (augEdges X) F := by
      rw [hbd]
      exact Finset.mem_image.2 ⟨(v i, v (i + 1)), Finset.mem_filter.2
        ⟨Finset.mem_product.2 ⟨hs.1, hs.2.1⟩, hs⟩, rfl⟩
    have hsne : s(v i, v (i + 1)) ≠ s(toC p.1, toC p.2) := by
      intro he
      rcases Sym2.eq_iff.1 he with ⟨h1, -⟩ | ⟨h1, h2⟩
      · exact hi (h1.trans hv0.symm)
      · obtain ⟨z, hz⟩ := hint
        have h1' := side_pos hs hz
        have h2' := side_pos hvw hz
        rw [h1, h2, wc_im_swap] at h1'
        linarith
    have hu := hother hfm X hX p hp hpd F hF _ hmem hsne
    have hdu := (mem_unitPairs.1 hu).2.2
    rw [dist_eq_norm] at hdu
    rw [norm_sub_rev]
    exact hdu.le
  have := capCyc_dist hper hm hinj i0 hunit k
  rw [hk, hv0, hcard] at this
  rw [← dist_toC, dist_eq_norm]
  push_cast at this
  linarith

/-- Bounded faces of the augmented graph, pulled back to the plane, have total area at most
`π D² / 4`. -/
theorem sum_volume_augFaces_le (hP : IsPlaneGraph (cVerts X) (augEdges X)) (hne : X.Nonempty)
    (S : Finset (Set ℂ)) (hmemS : ∀ F ∈ S, F ∈ augFaces X) :
    ∑ F ∈ S, volume (toC ⁻¹' F) ≤ ENNReal.ofReal (π * diam X ^ 2 / 4) := by
  have hdisj : (↑S : Set (Set ℂ)).PairwiseDisjoint (fun F => toC ⁻¹' F) := by
    intro F hF G hG hne
    exact (faces_disjoint (hmemS F hF).1 (hmemS G hG).1 hne).preimage _
  have hsub : (⋃ F ∈ S, toC ⁻¹' F) ⊆ convexHull ℝ (X : Set Plane) := by
    refine Set.iUnion₂_subset fun F hF => ?_
    intro z hz
    have h1 := boundedFace_subset_hull hP (hmemS F hF).1 (hmemS F hF).2 hz
    have e : ((cVerts X : Finset ℂ) : Set ℂ) = toC '' (X : Set Plane) := by
      unfold cVerts; rw [Finset.coe_image]
    rw [e, convexHull_image_toC] at h1
    obtain ⟨y, hy, hyz⟩ := h1
    have : y = z := toC.injective hyz
    exact this ▸ hy
  calc ∑ F ∈ S, volume (toC ⁻¹' F) = volume (⋃ F ∈ S, toC ⁻¹' F) :=
        (measure_biUnion_finset hdisj fun F hF =>
          ((isOpen_of_mem_faces (hmemS F hF).1).preimage toC.continuous).measurableSet).symm
    _ ≤ volume (convexHull ℝ (X : Set Plane)) := measure_mono hsub
    _ ≤ _ := volume_convexHull_le X hne

/-- **Caps have area `O(D)`.** -/
theorem cap_area_le : ∃ C : ℝ, ∀ᶠ n in atTop, numOptimalClasses n < ⊤ →
    ∀ X, IsOptimal n X → ¬ HasUnitTriangle X → ∀ p ∈ ccwHullSides X, 1 < dist p.1 p.2 →
      ∀ F, IsCap X p.1 p.2 F → (volume (toC ⁻¹' F)).toReal ≤ C * diam X := by
  obtain ⟨C, hC⟩ := rhombi_card_ge
  refine ⟨aStar * C, ?_⟩
  filter_upwards [hC, eventually_ge_atTop 1, augEdges_isPlaneGraph, contactFaces_subset_augFaces,
    bdryEdges_aug_contact] with n h hn hPa hsub hbd hfm X hX htri p hp hpd F hF
  have hq := (h hfm X hX htri).2
  have hne : X.Nonempty := by rw [← Finset.card_pos, hX.1.1]; omega
  have hsep := hX.1.2
  set Rh := (rhombi X).image cInterior
  have hRh : ∀ G ∈ Rh, G ∈ contactFaces X := by
    intro G hG
    obtain ⟨R, hR, rfl⟩ := Finset.mem_image.1 hG
    exact (rhombus_mem_rhombusFaces hsep htri hR).1.1
  have hFRh : F ∉ Rh := by
    intro hFm
    have hc := hRh F hFm
    have h1 := hF.2
    rw [hbd hfm X hX F hc] at h1
    have h2 := (Finset.mem_filter.1 h1).1
    rw [cUnitEdges, mem_unitPairs, dist_toC] at h2
    linarith [h2.2.2]
  have hinj : Set.InjOn cInterior (rhombi X : Set (Finset Plane)) := by
    intro R hR R' hR' hRR
    have e1 := (rhombus_mem_rhombusFaces hsep htri hR).2
    have e2 := (rhombus_mem_rhombusFaces hsep htri hR').2
    rw [hRR, ← e2] at e1
    exact Finset.coe_injective (Set.image_injective.2 toC.injective e1)
  have htot := sum_volume_augFaces_le (hPa hfm X hX) hne (insert F Rh) (by
    intro G hG
    rcases Finset.mem_insert.1 hG with rfl | hG
    · exact hF.1
    · exact hsub hfm X hX (hRh G hG))
  rw [Finset.sum_insert hFRh, Finset.sum_image hinj] at htot
  have hRhv : (rhombi X).card * ENNReal.ofReal aStar ≤
      ∑ R ∈ rhombi X, volume (toC ⁻¹' cInterior R) := by
    calc ((rhombi X).card : ENNReal) * ENNReal.ofReal aStar
        = ∑ R ∈ rhombi X, ENNReal.ofReal aStar := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum fun R hR => aStar_le_volume_rhombusFace hsep htri hR
  have hsum : volume (toC ⁻¹' F) + (rhombi X).card * ENNReal.ofReal aStar ≤
      ENNReal.ofReal (π * diam X ^ 2 / 4) :=
    le_trans (add_le_add_right hRhv _) htot
  have hFt : volume (toC ⁻¹' F) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_trans le_self_add hsum)
  have hB : ((rhombi X).card : ENNReal) * ENNReal.ofReal aStar ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top
  have hs := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsum
  rw [ENNReal.toReal_add hFt hB, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by unfold aStar; positivity),
    ENNReal.toReal_ofReal (by positivity)] at hs
  simp only [ENNReal.toReal_natCast] at hs
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

/-- Any three points of the closure of a cap span a parallelogram of area `O(D)`. -/
theorem cap_cr_le : ∃ C : ℝ, ∀ᶠ n in atTop, numOptimalClasses n < ⊤ →
    ∀ X, IsOptimal n X → ¬ HasUnitTriangle X → ∀ p ∈ ccwHullSides X, 1 < dist p.1 p.2 →
      ∀ F, IsCap X p.1 p.2 F → ∀ x y z : Plane,
      toC x ∈ closure F → toC y ∈ closure F → toC z ∈ closure F →
        |cr (y - x) (z - x)| ≤ C * diam X := by
  obtain ⟨C, hC⟩ := cap_area_le
  refine ⟨4 * C, ?_⟩
  filter_upwards [hC, augFace_convex] with n h hconv hfm X hX htri p hp hpd F hF x y z hx hy hz
  have hvol0 := h hfm X hX htri p hp hpd F hF
  have hFc : Convex ℝ (toC ⁻¹' F) :=
    (hconv hfm X hX F hF.1).linear_preimage toC.toLinearEquiv.toLinearMap
  have hcl : closure (toC ⁻¹' F) = toC ⁻¹' closure F :=
    (toC.toHomeomorph.preimage_closure F).symm
  have hvol := volume_ge_of_mem_closure hFc (p := x) (q := y) (r := z) (by rw [hcl]; exact hx)
    (by rw [hcl]; exact hy) (by rw [hcl]; exact hz)
  have hbdd : Bornology.IsBounded (toC ⁻¹' F) :=
    toC.isometry.antilipschitz.isBounded_preimage hF.1.2
  have hlt : volume (toC ⁻¹' F) ≠ ⊤ := hbdd.measure_lt_top.ne
  rw [ENNReal.ofReal_le_iff_le_toReal hlt] at hvol
  linarith

/-- **Two-arc covering at a cap.** -/
theorem cap_two_balls : ∃ C : ℝ, ∀ᶠ n in atTop, numOptimalClasses n < ⊤ →
    ∀ X, IsOptimal n X → ¬ HasUnitTriangle X → ∀ p ∈ ccwHullSides X, 1 < dist p.1 p.2 →
    ∀ F, IsCap X p.1 p.2 F →
    ∀ (O : Plane) (R ε δ s : ℝ), 0 < R → 0 ≤ ε → 0 ≤ δ → ε + δ < R →
      2 * (ε + δ) ≤ s - 2 * δ →
      C * diam X < (s - 2 * δ - 2 * (ε + δ)) ^ 3 / (2 * R) - 24 * (ε + δ) * (R + (ε + δ)) →
      ∀ P : Set Plane, (∀ x ∈ P, |dist x O - R| ≤ ε ∧ ∃ z, toC z ∈ closure F ∧ dist x z ≤ δ) →
      ∀ x₀ ∈ P, ∃ x₁ ∈ P, P ⊆ Metric.ball x₀ s ∪ Metric.ball x₁ s := by
  obtain ⟨C, hC⟩ := cap_cr_le
  refine ⟨C, ?_⟩
  filter_upwards [hC] with n h hfm X hX htri p0 hp0 hpd F hF O R ε δ s hR hε hδ hεR hs hbig P hP
  refine two_ball_cover fun x hx y hy z hz hxy hyz hxz => ?_
  obtain ⟨hx1, x', hx'F, hxx'⟩ := hP x hx
  obtain ⟨hy1, y', hy'F, hyy'⟩ := hP y hy
  obtain ⟨hz1, z', hz'F, hzz'⟩ := hP z hz
  have near : ∀ w w' : Plane, |dist w O - R| ≤ ε → dist w w' ≤ δ →
      |dist w' O - R| ≤ ε + δ := by
    intro w w' hw hww'
    have t1 := dist_triangle w' w O
    have t2 := dist_triangle w w' O
    rw [dist_comm w' w] at t1
    rw [abs_le] at hw ⊢
    constructor <;> linarith [hw.1, hw.2]
  have far : ∀ w v w' v' : Plane, s ≤ dist w v → dist w w' ≤ δ → dist v v' ≤ δ →
      s - 2 * δ ≤ dist w' v' := by
    intro w v w' v' h1 h2 h3
    have := dist_triangle4 w w' v' v
    rw [dist_comm v' v] at this
    linarith
  have key := cr_ge_of_near_circle (O := O) (p := x') (q := y') (r := z') hR (by linarith)
    hεR hs (near x x' hx1 hxx') (near y y' hy1 hyy') (near z z' hz1 hzz')
    (far x y x' y' hxy hxx' hyy') (far y z y' z' hyz hyy' hzz')
    (far z x z' x' (by rwa [dist_comm]) hzz' hxx')
  have hcr := h hfm X hX htri p0 hp0 hpd F hF x' y' z' hx'F hy'F hz'F
  linarith

/-- **Labels near a cap start in two short arcs.**  Fix `0 < e ≤ 1/20`.  Eventually, at every cap
`F`, unit hull sides (labels) starting within `D^{1 - e} + 1` of the closure of `F` start in two
balls of radius `D^{1 - e/4}`. -/
theorem large_cap_two_balls {e : ℝ} (he0 : 0 < e) (he1 : e ≤ 1 / 20) :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ p ∈ ccwHullSides X, 1 < dist p.1 p.2 → ∀ F, IsCap X p.1 p.2 F →
      ∀ {ι : Type} (S : Finset ι) (lab : ι → Plane × Plane),
        (∀ t ∈ S, lab t ∈ unitHullSides X) →
        (∀ t ∈ S, ∃ z : Plane, toC z ∈ closure F ∧ dist (lab t).1 z ≤ diam X ^ (1 - e) + 1) →
        ∃ c₀ c₁ : Plane, ∀ t ∈ S, dist (lab t).1 c₀ ≤ diam X ^ (1 - e / 4) ∨
          dist (lab t).1 c₁ ≤ diam X ^ (1 - e / 4) := by
  obtain ⟨CF, hCF⟩ := cap_two_balls
  have c1 := eventually_const_mul_rpow_le 144 (show (8 / 9 : ℝ) < 1 by norm_num)
  have c2 := eventually_const_mul_rpow_le 8 (show 1 - e < 1 by linarith)
  have c4 := eventually_const_mul_rpow_le 24 (show 1 - e < 1 - e / 4 by linarith)
  have c5 := eventually_const_mul_rpow_le 216 (show (8 / 9 : ℝ) < 1 - e / 4 by linarith)
  have c6 := eventually_const_mul_rpow_le 24 (show (0 : ℝ) < 1 - e / 4 by linarith)
  have c7 := eventually_const_mul_rpow_le (40 * |CF|) (show (2 : ℝ) < 3 - 3 * e / 4 by linarith)
  have c8 := eventually_const_mul_rpow_le (5 * 3456) (show (26 / 9 : ℝ) < 3 - 3 * e / 4 by
    linarith)
  have c9 := eventually_const_mul_rpow_le (5 * 192) (show 3 - e < 3 - 3 * e / 4 by linarith)
  have c10 := eventually_const_mul_rpow_le (5 * 192) (show (2 : ℝ) < 3 - 3 * e / 4 by linarith)
  filter_upwards [hCF, eventually_roundData_rate, tendsto_minDiam.eventually c1,
    tendsto_minDiam.eventually c2, tendsto_minDiam.eventually c4, tendsto_minDiam.eventually c5,
    tendsto_minDiam.eventually c6, tendsto_minDiam.eventually c7, tendsto_minDiam.eventually c8,
    tendsto_minDiam.eventually c9, tendsto_minDiam.eventually c10,
    tendsto_minDiam.eventually_ge_atTop 8]
    with n hCFn hround d1 d2 d4 d5 d6 d7 d8 d9 d10 d8' hfm X hX htri p0 hp0 hpd F hF ι S lab hlab hnear
  rw [← hX.diam_eq] at d1 d2 d4 d5 d6 d7 d8 d9 d10 d8'
  obtain ⟨O, η, hR⟩ := hround X hX
  set D := diam X with hDdef
  have hD0 : 0 < D := by linarith
  set a := D ^ (1 - e) with ha
  set b := D ^ (8 / 9 : ℝ) with hb
  set s := D ^ (1 - e / 4) with hs
  have ha0 : 0 < a := Real.rpow_pos_of_pos hD0 _
  have hb0 : 0 < b := Real.rpow_pos_of_pos hD0 _
  have hs0 : 0 < s := Real.rpow_pos_of_pos hD0 _
  rw [Real.rpow_zero, mul_one] at d6
  rw [Real.rpow_one] at d1 d2
  -- the hull vertices are within `18 D^{8/9}` of the circle
  have hε : D * √(3 * (100 * D ^ (-(2 / 9 : ℝ)))) ≤ 18 * b := by
    have h1 : √(3 * (100 * D ^ (-(2 / 9 : ℝ)))) ≤ 18 * D ^ (-(1 / 9 : ℝ)) := by
      have hsq : (18 * D ^ (-(1 / 9 : ℝ))) ^ 2 = 324 * D ^ (-(2 / 9 : ℝ)) := by
        rw [mul_pow, ← Real.rpow_natCast (D ^ _) 2, ← Real.rpow_mul hD0.le]; norm_num
      calc √(3 * (100 * D ^ (-(2 / 9 : ℝ)))) ≤ √((18 * D ^ (-(1 / 9 : ℝ))) ^ 2) := by
            apply Real.sqrt_le_sqrt
            rw [hsq]
            have := Real.rpow_pos_of_pos hD0 (-(2 / 9 : ℝ))
            nlinarith
        _ = 18 * D ^ (-(1 / 9 : ℝ)) := Real.sqrt_sq (by positivity)
    have h2 : D * D ^ (-(1 / 9 : ℝ)) = b := by
      rw [hb, ← Real.rpow_one_add' hD0.le (by norm_num)]; norm_num
    calc D * √(3 * (100 * D ^ (-(2 / 9 : ℝ)))) ≤ D * (18 * D ^ (-(1 / 9 : ℝ))) :=
          mul_le_mul_of_nonneg_left h1 hD0.le
      _ = 18 * b := by rw [← h2]; ring
  -- the products of powers
  have p8 : b * D ^ 2 = D ^ (26 / 9 : ℝ) := by
    rw [hb, ← Real.rpow_natCast D 2, ← Real.rpow_add hD0]; norm_num
  have p9 : a * D ^ 2 = D ^ (3 - e) := by
    rw [ha, ← Real.rpow_natCast D 2, ← Real.rpow_add hD0]; ring_nf
  have p2 : D ^ 2 = D ^ (2 : ℝ) := by rw [← Real.rpow_natCast]; norm_num
  have ps : s ^ 3 = D ^ (3 - 3 * e / 4) := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hD0.le]; ring_nf
  -- the set of starting points
  set P : Set Plane := (S.image (fun t => (lab t).1) : Set Plane)
  rcases S.eq_empty_or_nonempty with rfl | ⟨t₀, ht₀⟩
  · exact ⟨0, 0, fun t ht => absurd ht (Finset.notMem_empty t)⟩
  have k7 : 40 * (|CF| * D ^ 2) ≤ s ^ 3 := by rw [← mul_assoc, p2, ps]; exact d7
  have k8 : 5 * 3456 * (b * D ^ 2) ≤ s ^ 3 := by rw [p8, ps]; exact d8
  have k9 : 5 * 192 * (a * D ^ 2) ≤ s ^ 3 := by rw [p9, ps]; exact d9
  have k10 : 5 * 192 * D ^ 2 ≤ s ^ 3 := by rw [p2, ps]; exact d10
  obtain ⟨hm1, hm2, hbig⟩ := two_ball_arith hD0 ha0 hb0 hs0 d1 d2 d8' d4 d5 d6 k7 k8 k9 k10
  have hPprop : ∀ p ∈ P, |dist p O - D / 2| ≤ 18 * b ∧
      ∃ z, toC z ∈ closure F ∧ dist p z ≤ a + 1 := by
    intro p hp
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hp)
    have hcc : IsCcwHullSide X (lab t).1 (lab t).2 :=
      mem_ccwHullSides.1 (Finset.mem_filter.1 (hlab t ht)).1
    exact ⟨(abs_dist_center_sub_le hR hcc).trans hε, hnear t ht⟩
  have hp₀ : (lab t₀).1 ∈ P := Finset.mem_coe.2 (Finset.mem_image.2 ⟨t₀, ht₀, rfl⟩)
  obtain ⟨p₁, -, hcov⟩ := hCFn hfm X hX htri p0 hp0 hpd F hF O (D / 2) (18 * b) (a + 1) s (by positivity)
    (by positivity) (by positivity) hm1 hm2 hbig P hPprop _ hp₀
  refine ⟨(lab t₀).1, p₁, fun t ht => ?_⟩
  have hpt : (lab t).1 ∈ P := Finset.mem_coe.2 (Finset.mem_image.2 ⟨t, ht, rfl⟩)
  rcases hcov hpt with h | h
  · exact Or.inl (Metric.mem_ball.1 h).le
  · exact Or.inr (Metric.mem_ball.1 h).le

/-! ## Few long returns -/

/-- **Few long returns.**  If `Δ ≥ 0`, at most `π D / (B - 2)` hull sides close returns of more
than `B > 2` unit edges: `Σ (j - 2) = ρ ≤ u ≤ b ≤ π D`. -/
theorem card_long_returns_le (hX : IsSeparated X) (h2 : 2 ≤ X.card) (hΔ : 0 ≤ lockingDefect X)
    {B : ℝ} (hB : 2 < B) :
    (((ccwHullSides X).filter (fun p => B < returnLength X p.1 p.2)).card : ℝ) ≤
      π * diam X / (B - 2) := by
  set L := (ccwHullSides X).filter (fun p => B < returnLength X p.1 p.2)
  have h3 := numUnitHullSides_le X
  have h4 := hullVertices_card_le_pi_mul_diam hX h2
  unfold lockingDefect at hΔ
  have hρ : (returnExcess X : ℝ) ≤ π * diam X := by
    have : returnExcess X ≤ (hullVertices X).card := by
      have : (0 : ℤ) ≤ faceExcess X := by positivity
      omega
    exact le_trans (by exact_mod_cast this) h4
  have hsum : (L.card : ℝ) * (B - 2) ≤ returnExcess X := by
    calc (L.card : ℝ) * (B - 2) = ∑ p ∈ L, (B - 2) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ p ∈ L, ((returnLength X p.1 p.2 - 2 : ℕ) : ℝ) := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hlt := (Finset.mem_filter.1 hp).2
          have h3 : 2 ≤ returnLength X p.1 p.2 := by
            have : (2 : ℝ) < returnLength X p.1 p.2 := by linarith
            exact_mod_cast this.le
          rw [Nat.cast_sub h3]
          push_cast
          linarith
      _ ≤ ∑ p ∈ ccwHullSides X, ((returnLength X p.1 p.2 - 2 : ℕ) : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => Nat.cast_nonneg _)
      _ = returnExcess X := by rw [returnExcess, Nat.cast_sum]
  rw [le_div_iff₀ (by linarith)]
  linarith

/-! ## Directions -/

lemma sideDir_of_dist_eq_one {p : Plane × Plane} (h : dist p.1 p.2 = 1) :
    sideDir p = p.2 - p.1 := by
  rw [sideDir, ← dist_eq_norm', h, inv_one, one_smul]

/-- A label close in direction to a unit edge `a → b` cannot start near `b` if `b → a` is a hull
side. -/
lemma two_le_of_reversed_side {O : Plane} {D η δ : ℝ} (hR : RoundData X O D η δ)
    {ℓ : Plane × Plane} (hℓ : IsCcwHullSide X ℓ.1 ℓ.2) {a b : Plane} (hba : IsCcwHullSide X b a)
    (hab : dist a b = 1) {α : ℝ} (h : ‖(b - a) - sideDir ℓ‖ ≤ α) :
    2 ≤ α + 2 * dist ℓ.1 b / D + 4 * √(3 * δ) := by
  have h1 := sideDir_sub_le hR (p := ℓ) (q := (b, a)) hℓ hba
  have e : sideDir (b, a) = a - b := sideDir_of_dist_eq_one (by rw [dist_comm]; exact hab)
  rw [e] at h1
  have h2 : ‖(2 : ℝ) • (b - a)‖ = 2 := by
    rw [norm_smul, ← dist_eq_norm', hab]; norm_num
  have e2 : (2 : ℝ) • (b - a) = ((b - a) - sideDir ℓ) + (sideDir ℓ - (a - b)) := by
    rw [two_smul]; abel
  have := norm_add_le ((b - a) - sideDir ℓ) (sideDir ℓ - (a - b))
  rw [← e2, h2] at this
  simp only at h1
  linarith

/-- A label close in direction to a unit edge `a → b` and starting near the hull side `p` makes
`a → b` a forward edge for `p`. -/
lemma inner_ge_of_near_side {O : Plane} {D η δ : ℝ} (hR : RoundData X O D η δ)
    {ℓ p : Plane × Plane} (hℓ : IsCcwHullSide X ℓ.1 ℓ.2) (hp : IsCcwHullSide X p.1 p.2)
    {a b : Plane} (hab : dist a b = 1) {α : ℝ} (h : ‖(b - a) - sideDir ℓ‖ ≤ α)
    (hsmall : α + (2 * dist ℓ.1 p.1 / D + 4 * √(3 * δ)) ≤ 2 / 5) :
    9 / 10 ≤ inner ℝ (b - a) (sideDir p) := by
  have h1 := sideDir_sub_le hR hℓ hp
  have h2 : ‖(b - a) - sideDir p‖ ≤ 2 / 5 := by
    have := norm_sub_le_norm_sub_add_norm_sub (b - a) (sideDir ℓ) (sideDir p)
    linarith
  have hu : ‖b - a‖ = 1 := by rw [← dist_eq_norm', hab]
  have := inner_ge_of_norm_sub_le hu (norm_sideDir hp.2.2.1) h2
  linarith

/-! ## Cap arrivals -/

/-- **Cap arrivals land on forward cap sides** (§9.3).  Fix `0 < e ≤ 1/20` and `ε > 0`.
Eventually, if `q` maps a finite family `S` injectively to initial unit exit edges whose tracks
end on a cap (no exceptional face lies beyond the far end of the track), and `lab` labels `S`
injectively by unit hull sides whose directions are within `D^{-3e/2}` of the exit directions and
which start within `D^{1-e}` of the far ends, then, except for at most `ε D` members of `S`, the far
end of the track is a forward side of the cap of a non-unit hull side.

Proof: by `far_end_cases`, the far end is a reversed unit hull side (excluded, since its direction
would be opposite to that of the nearby label, `two_le_of_reversed_side`) or a side of the cap of
a non-unit hull side `p` with the cap on its left.  If the label starts within `D/20` of `p.1`, the
far end is a forward side (tangent regularity, `inner_ge_of_near_side`).  Otherwise the far end is
at distance more than `D/40` from `p.1`, so the return of `p` has more than `D/40` edges
(`cap_vertex_near`); at most `80 π` returns are that long (`card_long_returns_le`, using `Δ ≥ 0`),
and the labels arriving at one cap start in two balls of radius `D^{1 - e/4}`
(`large_cap_two_balls`), so there are at most `2 (2π D^{1 - e/4} + 1)` of them
(`card_le_of_labels_two_balls`).  In total the exceptions are `O(D^{1 - e/4}) ≤ ε D`. -/
theorem cap_landing {e ε : ℝ} (he0 : 0 < e) (he1 : e ≤ 1 / 20) (hε : 0 < ε) :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ {ι : Type} (S : Finset ι) (q lab : ι → Plane × Plane), Set.InjOn q S →
        Set.InjOn lab S →
        (∀ i ∈ S, q i ∈ X ×ˢ X ∧ Initial X (q i) ∧ dist (q i).1 (q i).2 = 1 ∧
          hopDest X (q i) = .cap) →
        (∀ i ∈ S, lab i ∈ unitHullSides X ∧
          ‖sideDir (q i) - sideDir (lab i)‖ ≤ diam X ^ (-(3 / 2 * e)) ∧
          dist (lab i).1 (hopEnd X (q i)).1 ≤ diam X ^ (1 - e)) →
        ∃ S' ⊆ S, ((S \ S').card : ℝ) ≤ ε * diam X ∧ ∀ i ∈ S', ∃ p ∈ ccwHullSides X,
          1 < dist p.1 p.2 ∧ ∃ F, IsCap X p.1 p.2 F ∧
            IsCapForward X p F (toC (hopEnd X (q i)).1, toC (hopEnd X (q i)).2) := by
  have d1 := eventually_const_mul_rpow_le 10 (show -(3 / 2 * e) < 0 by linarith)
  have d2 := eventually_const_mul_rpow_le 480000 (show (-(2 / 9 : ℝ)) < 0 by norm_num)
  have d3 := eventually_const_mul_rpow_le 50 (show 1 - e < 1 by linarith)
  have d5 := eventually_const_mul_rpow_le (640 * π ^ 2 / ε) (show 1 - e / 4 < 1 by linarith)
  filter_upwards [far_end_cases, cap_vertex_near, large_cap_two_balls he0 he1, cap_unique,
    lockingDefect_nonneg_eventually, eventually_roundData_rate, eventually_ge_atTop 2,
    tendsto_minDiam.eventually d1, tendsto_minDiam.eventually d2, tendsto_minDiam.eventually d3,
    tendsto_minDiam.eventually d5, tendsto_minDiam.eventually_ge_atTop (max 160 (640 * π / ε))]
    with n hfar hvert htwo huniq hΔ hround hn2 d1 d2 d3 d5 d4
  intro hfm X hX htri ι S q lab hq hlab hS hL
  rw [← hX.diam_eq] at d1 d2 d3 d5 d4
  rw [Real.rpow_zero] at d1 d2
  rw [Real.rpow_one] at d3 d5
  obtain ⟨O, η', hR⟩ := hround X hX
  set D := diam X with hDdef
  have hD160 : 160 ≤ D := le_trans (le_max_left _ _) d4
  have hD0 : 0 < D := by linarith
  have hsq : 4 * √(3 * (100 * D ^ (-(2 / 9 : ℝ)))) ≤ 1 / 10 := by
    have h0 : 3 * (100 * D ^ (-(2 / 9 : ℝ))) ≤ (1 / 40) ^ 2 := by nlinarith
    have := Real.sqrt_le_sqrt h0
    rw [Real.sqrt_sq (by norm_num)] at this
    linarith
  have hdir : D ^ (-(3 / 2 * e)) ≤ 1 / 10 := by linarith
  have hfar' : 2 * (D ^ (1 - e) + 1) / D ≤ 1 / 10 := by
    rw [div_le_iff₀ hD0]; nlinarith
  -- the good members
  set S' := S.filter (fun i => ∃ p ∈ ccwHullSides X, 1 < dist p.1 p.2 ∧ ∃ F, IsCap X p.1 p.2 F ∧
      IsCapForward X p F (toC (hopEnd X (q i)).1, toC (hopEnd X (q i)).2)) with hS'
  refine ⟨S', Finset.filter_subset _ _, ?_, fun i hi => (Finset.mem_filter.1 hi).2⟩
  -- every bad member reaches the cap of a long return
  have hbad : ∀ i ∈ S \ S', ∃ p ∈ ccwHullSides X, D / 40 < returnLength X p.1 p.2 ∧
      ∃ F, IsCap X p.1 p.2 F ∧ toC (hopEnd X (q i)).1 ∈ closure F := by
    intro i hi
    obtain ⟨hiS, hiS'⟩ := Finset.mem_sdiff.1 hi
    obtain ⟨hqX, -, hq1, hdest⟩ := hS i hiS
    obtain ⟨hlabU, hlabd, hlabn⟩ := hL i hiS
    set a := (hopEnd X (q i)).1 with ha
    set b := (hopEnd X (q i)).2 with hb
    have hba : b - a = (q i).2 - (q i).1 := hopEnd_sub _
    have hab : dist a b = 1 := by rw [dist_eq_norm', hba, ← dist_eq_norm', hq1]
    have hsdq : sideDir (q i) = b - a := by rw [sideDir_of_dist_eq_one hq1, hba]
    rw [hsdq] at hlabd
    have hℓ : IsCcwHullSide X (lab i).1 (lab i).2 :=
      mem_ccwHullSides.1 (Finset.mem_filter.1 hlabU).1
    rcases hfar hfm X hX htri (q i) hqX hq1 hdest with hrev | ⟨p, hp, hpd, F, hF, hbd, hleft⟩
    · exfalso
      have hrs : IsCcwHullSide X b a := mem_ccwHullSides.1 (Finset.mem_filter.1 hrev).1
      have h1 := two_le_of_reversed_side hR hℓ hrs hab hlabd
      have h2 : dist (lab i).1 b ≤ D ^ (1 - e) + 1 := by
        have := dist_triangle (lab i).1 a b
        rw [hab] at this; linarith
      have h3 : 2 * dist (lab i).1 b / D ≤ 2 * (D ^ (1 - e) + 1) / D := by
        gcongr
      linarith
    · have hpc : IsCcwHullSide X p.1 p.2 := mem_ccwHullSides.1 hp
      obtain ⟨hcl, hdl⟩ := hvert hfm X hX p hp hpd F hF a b hbd
      refine ⟨p, hp, ?_, F, hF, hcl⟩
      by_contra hshort
      push_neg at hshort
      apply hiS'
      refine Finset.mem_filter.2 ⟨hiS, p, hp, hpd, F, hF, hbd, ?_, hleft, ?_⟩
      · intro he
        rcases Sym2.eq_iff.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [← toC.injective h1, ← toC.injective h2] at hpd; linarith
        · rw [← toC.injective h1, ← toC.injective h2, dist_comm] at hpd; linarith
      · have hnear : dist (lab i).1 p.1 ≤ D / 20 := by
          have := dist_triangle (lab i).1 a p.1
          have : D ^ (1 - e) ≤ D / 50 := by linarith
          linarith
        have e1 : toC.symm (toC b - toC a) = b - a := by
          rw [← map_sub, LinearIsometryEquiv.symm_apply_apply]
        show 9 / 10 ≤ inner ℝ (toC.symm (toC b - toC a)) (sideDir p)
        rw [e1]
        refine inner_ge_of_near_side hR hℓ hpc hab hlabd ?_
        have : 2 * dist (lab i).1 p.1 / D ≤ 1 / 10 := by
          rw [div_le_iff₀ hD0]; linarith
        linarith
  choose! pf hpf hpl Ff hFf hFcl using hbad
  set L := (ccwHullSides X).filter (fun p => D / 40 < returnLength X p.1 p.2) with hLdef
  have hmaps : ∀ i ∈ S \ S', pf i ∈ L := fun i hi => Finset.mem_filter.2 ⟨hpf i hi, hpl i hi⟩
  set s := D ^ (1 - e / 4) with hsdef
  have hs0 : 0 < s := Real.rpow_pos_of_pos hD0 _
  have hfib : ∀ p ∈ L, (((S \ S').filter (fun i => pf i = p)).card : ℝ) ≤
      2 * (2 * π * s + 1) := by
    intro p hp
    obtain ⟨hpc, hpl'⟩ := Finset.mem_filter.1 hp
    by_cases hT : ((S \ S').filter (fun i => pf i = p)).Nonempty
    · obtain ⟨i0, hi0⟩ := hT
      obtain ⟨hi0S, hpi0⟩ := Finset.mem_filter.1 hi0
      have hpd : 1 < dist p.1 p.2 := by
        have hs := mem_ccwHullSides.1 hpc
        have h1 := hX.1.2 p.1 (mem_of_mem_hullVertices hs.1) p.2
          (mem_of_mem_hullVertices hs.2.1) hs.2.2.1
        refine lt_of_le_of_ne h1 (fun h => ?_)
        rw [returnLength_of_dist_eq_one h.symm] at hpl'
        push_cast at hpl'
        linarith
      have hF0 : IsCap X p.1 p.2 (Ff i0) := hpi0 ▸ hFf i0 hi0S
      have hsub : ∀ t ∈ (S \ S').filter (fun i => pf i = p), t ∈ S := fun t ht =>
        (Finset.mem_sdiff.1 (Finset.mem_filter.1 ht).1).1
      obtain ⟨c₀, c₁, hc⟩ := htwo hfm X hX htri p hpc hpd (Ff i0) hF0
        ((S \ S').filter (fun i => pf i = p)) lab (fun t ht => (hL t (hsub t ht)).1)
        (fun t ht => by
          obtain ⟨htS, hpt⟩ := Finset.mem_filter.1 ht
          have hFt : IsCap X p.1 p.2 (Ff t) := hpt ▸ hFf t htS
          have hcl := hFcl t htS
          rw [huniq hfm X hX p hpc _ _ hFt hF0] at hcl
          refine ⟨(hopEnd X (q t)).1, hcl, ?_⟩
          have := (hL t (hsub t ht)).2.2
          linarith)
      exact card_le_of_labels_two_balls hX.1.2 _ lab (hlab.mono (fun t ht => hsub t ht))
        (fun t ht => (hL t (hsub t ht)).1) c₀ c₁ hs0.le hc
    · rw [Finset.not_nonempty_iff_eq_empty.1 hT]
      simp only [Finset.card_empty, Nat.cast_zero]
      positivity
  have hL' : (L.card : ℝ) ≤ 80 * π := by
    have h := card_long_returns_le hX.1.2 (by rw [hX.1.1]; exact hn2) (hΔ hfm X hX htri)
      (B := D / 40) (by linarith)
    have h2 : π * D / (D / 40 - 2) ≤ 80 * π := by
      rw [div_le_iff₀ (by linarith)]; nlinarith [Real.pi_pos]
    exact h.trans h2
  have htot : ((S \ S').card : ℝ) ≤ L.card * (2 * (2 * π * s + 1)) := by
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    push_cast
    calc ∑ p ∈ L, (((S \ S').filter (fun i => pf i = p)).card : ℝ)
        ≤ ∑ p ∈ L, 2 * (2 * π * s + 1) := Finset.sum_le_sum hfib
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hc : 640 * π / ε ≤ D := le_trans (le_max_right _ _) d4
  have h1 : 640 * π ^ 2 * s ≤ ε * D := by
    have := mul_le_mul_of_nonneg_left d5 hε.le
    have e2 : ε * (640 * π ^ 2 / ε * s) = 640 * π ^ 2 * s := by field_simp
    linarith
  have h2 : 640 * π ≤ ε * D := by
    have := mul_le_mul_of_nonneg_left hc hε.le
    have e2 : ε * (640 * π / ε) = 640 * π := by field_simp
    linarith
  have h3 : (L.card : ℝ) * (2 * (2 * π * s + 1)) ≤ 80 * π * (2 * (2 * π * s + 1)) :=
    mul_le_mul_of_nonneg_right hL' (by positivity)
  nlinarith [Real.pi_pos]

/-- **Good tokens at the caps** (§8.3 applied in §9.3).  Fix `0 < e ≤ 1/20` and `ε > 0`.
Eventually, if `q` maps a finite family `S` injectively to unit exit edges whose tracks end on a
cap (no exceptional face lies beyond the far end of the track), and `lab` labels `S` injectively by
unit hull sides whose directions are within `D^{-3e/2}` of the exit directions and which start
within `D^{1-e}` of the far ends, then `|S| ≤ 2ρ/3 + ε D`.

Proved from `cap_landing` (all but `ε D` far ends are forward sides of caps) and the cap
capacities `cap_forward_sides_le`: the far ends are distinct (`hopEnd_injOn`), and the forward
sides of the cap of `p` number at most `2 (j_p - 2)/3`, which sum to `2ρ/3`. -/
theorem good_cap_tokens_le {e ε : ℝ} (he0 : 0 < e) (he1 : e ≤ 1 / 20) (hε : 0 < ε) :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ {ι : Type} (S : Finset ι) (q lab : ι → Plane × Plane), Set.InjOn q S →
        Set.InjOn lab S →
        (∀ i ∈ S, q i ∈ X ×ˢ X ∧ Initial X (q i) ∧ dist (q i).1 (q i).2 = 1 ∧
          hopDest X (q i) = .cap) →
        (∀ i ∈ S, lab i ∈ unitHullSides X ∧
          ‖sideDir (q i) - sideDir (lab i)‖ ≤ diam X ^ (-(3 / 2 * e)) ∧
          dist (lab i).1 (hopEnd X (q i)).1 ≤ diam X ^ (1 - e)) →
        (S.card : ℝ) ≤ 2 * (returnExcess X : ℝ) / 3 + ε * diam X := by
  filter_upwards [cap_landing he0 he1 hε, cap_forward_sides_le, cap_unique]
    with n hland hcount huniq
  intro hfm X hX htri ι S q lab hq hlab hS hL
  obtain ⟨S', hS'S, hsmall, hS'⟩ := hland hfm X hX htri S q lab hq hlab hS hL
  choose! pf hpf hpd Ff hFf hfw using hS'
  have hfib : (S'.card : ℝ) ≤
      ∑ p ∈ ccwHullSides X, 2 * ((returnLength X p.1 p.2 - 2 : ℕ) : ℝ) / 3 := by
    rw [Finset.card_eq_sum_card_fiberwise (f := pf) (t := ccwHullSides X)
      (fun i hi => hpf i hi)]
    push_cast
    apply Finset.sum_le_sum
    intro p hp
    by_cases hT : (S'.filter (fun i => pf i = p)).Nonempty
    · obtain ⟨i0, hi0⟩ := hT
      obtain ⟨hi0S, hpi0⟩ := Finset.mem_filter.1 hi0
      have hd : 1 < dist p.1 p.2 := by rw [← hpi0]; exact hpd i0 hi0S
      have hFcap : IsCap X p.1 p.2 (Ff i0) := by rw [← hpi0]; exact hFf i0 hi0S
      have hinj : Set.InjOn (fun i => (toC (hopEnd X (q i)).1, toC (hopEnd X (q i)).2))
          (S'.filter (fun i => pf i = p)) := by
        intro i hi i' hi' h
        have hiS := hS'S (Finset.mem_filter.1 hi).1
        have hiS' := hS'S (Finset.mem_filter.1 hi').1
        have hend : hopEnd X (q i) = hopEnd X (q i') :=
          Prod.ext (toC.injective (Prod.mk.inj h).1) (toC.injective (Prod.mk.inj h).2)
        exact hq hiS hiS' (hopEnd_injOn hX.1.2 htri (hS i hiS).1 (hS i' hiS').1 (hS i hiS).2.1
          (hS i' hiS').2.1 hend)
      have hE : ∀ ab ∈ (S'.filter (fun i => pf i = p)).image
          (fun i => (toC (hopEnd X (q i)).1, toC (hopEnd X (q i)).2)),
          IsCapForward X p (Ff i0) ab := by
        intro ab hab
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hab
        obtain ⟨hiS', hpi⟩ := Finset.mem_filter.1 hi
        have hFi : IsCap X p.1 p.2 (Ff i) := by rw [← hpi]; exact hFf i hiS'
        have hF' : Ff i = Ff i0 := huniq hfm X hX p hp _ _ hFi hFcap
        have := hfw i hiS'
        rw [hF', hpi] at this
        exact this
      have := hcount hfm X hX p hp hd (Ff i0) hFcap _ hE
      rwa [Finset.card_image_of_injOn hinj] at this
    · rw [Finset.not_nonempty_iff_eq_empty.1 hT]
      simp only [Finset.card_empty, Nat.cast_zero]
      positivity
  have hsum : ∑ p ∈ ccwHullSides X, 2 * ((returnLength X p.1 p.2 - 2 : ℕ) : ℝ) / 3 =
      2 * (returnExcess X : ℝ) / 3 := by
    rw [← Finset.sum_div, ← Finset.mul_sum, returnExcess, Nat.cast_sum]
  have hsplit := Finset.card_sdiff_add_card_eq_card hS'S
  have hsplit' : (S.card : ℝ) = (S \ S').card + S'.card := by exact_mod_cast hsplit.symm
  linarith

end Erdos99

end

end CapLanding
