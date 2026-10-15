module

public import Mathlib
public import Erdos99.Part01Basics
public import Erdos99.Part02LockingAndFans

/-!
# Erdős Problem 99 under finite multiplicity — Part 3 of 9: The lifted fan theorem, first-order locking, density and annulus estimates

This is one of the supporting files of the formalization; the main theorem and a precise
description of what is proved are at the top of `Erdos99.lean`.

The file is divided into the following sections (each `section Name … end Name`); comments
elsewhere in the development refer to these sections by name.

* `FacetFrame`
* `CircleOrder`
* `FanLink`
* `RegularFan`
* `PolytopeFan`
* `FacetLinksProof`
* `FanTheorem`
* `LiftedFan`
* `StressSign`
* `FirstOrderLocking`
* `Isodiametric`
* `Density`
* `Directions`
* `Clustering`
* `RhombusArea`
* `Annulus`
-/

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `FacetFrame`
-/

section FacetFrame

/-!
# An oriented orthonormal frame around a unit vector, and angles around it

For a unit vector `a ∈ ℝ³` we choose an oriented orthonormal frame `(a, e1, e2)`
(`exists_frame`).  The plane coordinates `planeC e1 e2 x = ⟪e1, x⟫ + ⟪e2, x⟫ i` identify the plane
`a^⊥` with `ℂ`; the arguments of these complex numbers measure angles around `a`.  The sine and the
cosine of the angle from `x` to `y` around `a` are expressed through `vol3 a x y` and
`⟪x, y⟫ - ⟪a, x⟫ ⟪a, y⟫` (`sin_arg_sub`, `cos_arg_sub`).
-/

open scoped BigOperators Real

@[expose] public noncomputable section

open Classical Real

namespace Erdos99

/-- An oriented orthonormal frame `(a, e1, e2)` around a unit vector `a`. -/
lemma exists_frame {a : Space3} (ha : ‖a‖ = 1) : ∃ e1 e2 : Space3,
    inner ℝ e1 a = 0 ∧ inner ℝ e2 a = 0 ∧
    (∀ x : Space3, x = inner ℝ a x • a + inner ℝ e1 x • e1 + inner ℝ e2 x • e2) ∧
    (∀ x y : Space3, vol3 a x y = inner ℝ e1 x * inner ℝ e2 y - inner ℝ e2 x * inner ℝ e1 y) := by
  obtain ⟨n, hn0, hna, -⟩ := exists_orth_pair a a
  set e := ‖n‖⁻¹ • n with he_def
  have hnpos : 0 < ‖n‖ := norm_pos_iff.2 hn0
  have hE : inner ℝ e e = 1 := by
    rw [real_inner_self_eq_norm_sq, he_def, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ hnpos.ne']; norm_num
  have hP : inner ℝ a e = 0 := by
    rw [he_def, inner_smul_right, real_inner_comm, hna, mul_zero]
  have hA : inner ℝ a a = 1 := by rw [real_inner_self_eq_norm_sq, ha]; norm_num
  have hP' : inner ℝ e a = 0 := by rw [real_inner_comm]; exact hP
  rw [inner_eq_coords] at hE hP hA
  refine ⟨e, cross3 a e, hP', inner_cross3_left a e, fun x => ?_, fun x y => ?_⟩
  · ext k
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, inner_eq_coords]
    fin_cases k
    · simp only [Fin.zero_eta, cross3_apply_zero, cross3_apply_one,
        cross3_apply_two]
      linear_combination (-(x 0) * (e 0 * e 0 + e 1 * e 1 + e 2 * e 2) + (e 0 * x 0 + e 1 * x 1 + e 2 * x 2) * e 0) * hA +
        (-(x 0) + (a 0 * x 0 + a 1 * x 1 + a 2 * x 2) * a 0) * hE +
        (x 0 * (a 0 * e 0 + a 1 * e 1 + a 2 * e 2) - (e 0 * x 0 + e 1 * x 1 + e 2 * x 2) * a 0 - (a 0 * x 0 + a 1 * x 1 + a 2 * x 2) * e 0) * hP
    · simp only [Fin.mk_one, cross3_apply_zero, cross3_apply_one,
        cross3_apply_two]
      linear_combination (-(x 1) * (e 0 * e 0 + e 1 * e 1 + e 2 * e 2) + (e 0 * x 0 + e 1 * x 1 + e 2 * x 2) * e 1) * hA +
        (-(x 1) + (a 0 * x 0 + a 1 * x 1 + a 2 * x 2) * a 1) * hE +
        (x 1 * (a 0 * e 0 + a 1 * e 1 + a 2 * e 2) - (e 0 * x 0 + e 1 * x 1 + e 2 * x 2) * a 1 - (a 0 * x 0 + a 1 * x 1 + a 2 * x 2) * e 1) * hP
    · simp only [Fin.reduceFinMk, cross3_apply_zero, cross3_apply_one,
        cross3_apply_two]
      linear_combination (-(x 2) * (e 0 * e 0 + e 1 * e 1 + e 2 * e 2) + (e 0 * x 0 + e 1 * x 1 + e 2 * x 2) * e 2) * hA +
        (-(x 2) + (a 0 * x 0 + a 1 * x 1 + a 2 * x 2) * a 2) * hE +
        (x 2 * (a 0 * e 0 + a 1 * e 1 + a 2 * e 2) - (e 0 * x 0 + e 1 * x 1 + e 2 * x 2) * a 2 - (a 0 * x 0 + a 1 * x 1 + a 2 * x 2) * e 2) * hP
  · simp only [inner_eq_coords, cross3_apply_zero, cross3_apply_one, cross3_apply_two, vol3]
    linear_combination (norm := skip) (-(vol3 a x y)) * hE + (vol3 e x y) * hP
    simp only [vol3]; ring

end Erdos99

namespace Erdos99

/-- Plane coordinates with respect to the vectors `e1, e2`. -/
def planeC (e1 e2 x : Space3) : ℂ := ⟨inner ℝ e1 x, inner ℝ e2 x⟩

section Frame

variable {a e1 e2 : Space3}
  (hC : ∀ x : Space3, x = inner ℝ a x • a + inner ℝ e1 x • e1 + inner ℝ e2 x • e2)
  (hV : ∀ x y : Space3, vol3 a x y = inner ℝ e1 x * inner ℝ e2 y - inner ℝ e2 x * inner ℝ e1 y)

include hC in
lemma frame_inner (x y : Space3) : inner ℝ x y =
    inner ℝ a x * inner ℝ a y + inner ℝ e1 x * inner ℝ e1 y + inner ℝ e2 x * inner ℝ e2 y := by
  conv_lhs => rw [hC x]
  simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real]

include hC in
lemma planeC_norm_sq (x : Space3) : ‖planeC e1 e2 x‖ ^ 2 = ‖x‖ ^ 2 - inner ℝ a x ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, ← real_inner_self_eq_norm_sq, frame_inner hC x x]
  simp only [planeC]
  ring

include hC in
lemma planeC_norm_of_unit {x : Space3} (hx : ‖x‖ = 1) :
    ‖planeC e1 e2 x‖ = √(1 - inner ℝ a x ^ 2) := by
  have := planeC_norm_sq hC x
  rw [hx, one_pow] at this
  rw [← this, Real.sqrt_sq (norm_nonneg _)]

lemma planeC_re_im (x : Space3) :
    ‖planeC e1 e2 x‖ * Real.cos (Complex.arg (planeC e1 e2 x)) = inner ℝ e1 x ∧
      ‖planeC e1 e2 x‖ * Real.sin (Complex.arg (planeC e1 e2 x)) = inner ℝ e2 x :=
  ⟨Complex.norm_mul_cos_arg _, Complex.norm_mul_sin_arg _⟩

include hV in
/-- The sine of the angle from `x` to `y` around `a`. -/
lemma sin_arg_sub (x y : Space3) :
    Real.sin (Complex.arg (planeC e1 e2 y) - Complex.arg (planeC e1 e2 x)) *
      (‖planeC e1 e2 x‖ * ‖planeC e1 e2 y‖) = vol3 a x y := by
  obtain ⟨h1, h2⟩ := planeC_re_im (e1 := e1) (e2 := e2) x
  obtain ⟨h3, h4⟩ := planeC_re_im (e1 := e1) (e2 := e2) y
  rw [hV, ← h1, ← h2, ← h3, ← h4, Real.sin_sub]
  ring

include hC in
/-- The cosine of the angle from `x` to `y` around `a`. -/
lemma cos_arg_sub (x y : Space3) :
    Real.cos (Complex.arg (planeC e1 e2 y) - Complex.arg (planeC e1 e2 x)) *
      (‖planeC e1 e2 x‖ * ‖planeC e1 e2 y‖) = inner ℝ x y - inner ℝ a x * inner ℝ a y := by
  obtain ⟨h1, h2⟩ := planeC_re_im (e1 := e1) (e2 := e2) x
  obtain ⟨h3, h4⟩ := planeC_re_im (e1 := e1) (e2 := e2) y
  rw [frame_inner hC x y, ← h1, ← h2, ← h3, ← h4, Real.cos_sub]
  ring

include hC in
/-- A vector is determined by its frame coordinates. -/
lemma frame_ext {v w : Space3} (h0 : inner ℝ a v = inner ℝ a w) (h1 : inner ℝ e1 v = inner ℝ e1 w)
    (h2 : inner ℝ e2 v = inner ℝ e2 w) : v = w := by
  rw [hC v, hC w, h0, h1, h2]

end Frame

end Erdos99
end

end FacetFrame

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `CircleOrder`
-/

section CircleOrder

/-!
# Cyclic order of finitely many directions on the circle

Finitely many points `j ∈ N` with distinct angles `φ j ∈ (-π, π]` are enumerated in increasing
order of angle (`exists_sorted_enum`).  If every point has a successor at a positive angle less
than `π` with no point of `N` strictly in between (`hnext`), then the successor of the `m`-th point
is the `(m + 1)`-th one (cyclically), and the gaps between consecutive angles are admissible gaps
in the sense of `ValidGaps` (`circle_cycle`).  Moreover every direction lies in one of the closed
sectors between consecutive points.
-/

open scoped BigOperators Real

@[expose] public noncomputable section

open Classical Real Finset

namespace Erdos99

/-- Enumerating a finite set in increasing order of an injective real function. -/
lemma exists_sorted_enum {ι : Type*} {N : Finset ι} (hN : N.Nonempty) (φ : ι → ℝ)
    (hinj : Set.InjOn φ N) :
    ∃ e : ℕ → ι, (∀ m < N.card, e m ∈ N) ∧
      (∀ m < N.card, ∀ m' < N.card, m < m' → φ (e m) < φ (e m')) ∧
      (∀ j ∈ N, ∃ m < N.card, e m = j) := by
  set s := N.image φ with hs_def
  have hs : s.card = N.card := Finset.card_image_of_injOn hinj
  set f := s.orderEmbOfFin hs
  have hmem : ∀ m : Fin N.card, ∃ j ∈ N, φ j = f m := fun m =>
    Finset.mem_image.1 (Finset.orderEmbOfFin_mem s hs m)
  choose g hgN hgφ using hmem
  have hpos : 0 < N.card := Finset.card_pos.2 hN
  refine ⟨fun m => if h : m < N.card then g ⟨m, h⟩ else g ⟨0, hpos⟩, ?_, ?_, ?_⟩
  · intro m hm
    simp only [hm, dif_pos]
    exact hgN _
  · intro m hm m' hm' hlt
    simp only [hm, hm', dif_pos, hgφ]
    exact f.strictMono (Fin.mk_lt_mk.2 hlt)
  · intro j hj
    have : φ j ∈ Set.range f := by
      rw [Finset.range_orderEmbOfFin]
      exact Finset.mem_image_of_mem φ hj
    obtain ⟨m, hm⟩ := this
    refine ⟨m, m.2, ?_⟩
    simp only [m.2, dif_pos, Fin.eta]
    exact hinj (hgN m) hj (by rw [hgφ, hm])

lemma sin_pos_lt_pi_of_lt_two_pi {x : ℝ} (h2 : x ≤ 2 * π) (hs : 0 < Real.sin x) :
    x < π := by
  by_contra hc
  push_neg at hc
  have := Real.sin_nonpos_of_nonpos_of_neg_pi_le (x := x - 2 * π) (by linarith) (by linarith)
  rw [Real.sin_sub_two_pi] at this
  linarith

lemma sin_pos_lt_neg_pi {x : ℝ} (h0 : x < 0) (hs : 0 < Real.sin x) :
    x < -π := by
  have := sin_pos_lt_pi_of_lt_two_pi (x := x + 2 * π) (by linarith)
    (by rwa [Real.sin_add_two_pi])
  linarith

lemma sin_pos_of_lt_neg_pi {x : ℝ} (h1 : x < -π) (h2 : -(2 * π) < x) : 0 < Real.sin x := by
  rw [← Real.sin_add_two_pi]
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)

/-- **The cyclic order of directions.** -/
lemma circle_cycle {ι : Type*} {N : Finset ι} (hN : N.Nonempty) (φ : ι → ℝ)
    (hφ : ∀ j ∈ N, -π < φ j ∧ φ j ≤ π) (hinj : Set.InjOn φ N)
    (hnext : ∀ j ∈ N, ∃ b ∈ N, 0 < Real.sin (φ b - φ j) ∧
      ∀ l ∈ N, ¬ (0 < Real.sin (φ l - φ j) ∧ 0 < Real.sin (φ b - φ l))) :
    ∃ (k : ℕ) (e : ℕ → ι) (θ : ℕ → ℝ), ValidGaps k θ ∧ (∀ m < k, e m ∈ N) ∧
      (∀ m < k, ∀ m' < k, e m = e m' → m = m') ∧ (∀ j ∈ N, ∃ m < k, e m = j) ∧
      (∀ m < k, ∃ n : ℤ, θ m = φ (e ((m + 1) % k)) - φ (e m) + n * (2 * π)) ∧
      (∀ m < k, ∀ b ∈ N, 0 < Real.sin (φ b - φ (e m)) →
        (∀ l ∈ N, ¬ (0 < Real.sin (φ l - φ (e m)) ∧ 0 < Real.sin (φ b - φ l))) →
          b = e ((m + 1) % k)) ∧
      (∀ ψ : ℝ, -π < ψ → ψ ≤ π → ∃ m < k, ∃ t : ℝ, 0 ≤ t ∧ t ≤ θ m ∧
        ∃ n : ℤ, ψ = φ (e m) + t + n * (2 * π)) := by
  obtain ⟨e, heN, hmono, hsurj⟩ := exists_sorted_enum hN φ hinj
  set k := N.card with hk_def
  have hkpos : 0 < k := Finset.card_pos.2 hN
  set F : ℕ → ℝ := fun m => φ (e m) with hF
  have hFr : ∀ m < k, -π < F m ∧ F m ≤ π := fun m hm => hφ _ (heN m hm)
  have hFle : ∀ m < k, ∀ m' < k, m ≤ m' → F m ≤ F m' := by
    intro m hm m' hm' hle
    rcases hle.lt_or_eq with h | h
    · exact (hmono m hm m' hm' h).le
    · rw [h]
  have heinj : ∀ m < k, ∀ m' < k, e m = e m' → m = m' := by
    intro m hm m' hm' he
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := hmono m hm m' hm' h; rw [he] at this; exact lt_irrefl _ this
    · have := hmono m' hm' m hm h; rw [he] at this; exact lt_irrefl _ this
  -- the successor index
  have hsucc_lt : ∀ m < k, (m + 1) % k < k := fun m _ => Nat.mod_lt _ hkpos
  -- key claim: the successor is the next point
  have key : ∀ m < k, ∀ b ∈ N, 0 < Real.sin (φ b - φ (e m)) →
      (∀ l ∈ N, ¬ (0 < Real.sin (φ l - φ (e m)) ∧ 0 < Real.sin (φ b - φ l))) →
        b = e ((m + 1) % k) := by
    intro m hm b hb hsb hnone
    obtain ⟨m', hm', rfl⟩ := hsurj b hb
    have hmm' : m' ≠ m := by
      rintro rfl; simp at hsb
    by_contra hne
    have hm'n : m' ≠ (m + 1) % k := fun h => hne (by rw [h])
    apply hnone (e ((m + 1) % k)) (heN _ (hsucc_lt m hm))
    have hb1 := hFr m' hm'
    have hj1 := hFr m hm
    rcases Nat.lt_or_ge (m + 1) k with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at hm'n ⊢
      have hn1 := hFr (m + 1) hlt
      have hjn : F m < F (m + 1) := hmono m hm (m + 1) hlt (by omega)
      rcases Nat.lt_or_gt_of_ne hm'n with h1 | h1
      · -- m' < m + 1, so m' < m
        have h2 : m' < m := by omega
        have hbj : F m' < F m := hmono m' hm' m hm h2
        have hd := sin_pos_lt_neg_pi (x := F m' - F m) (by linarith) hsb
        refine ⟨Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith),
          sin_pos_of_lt_neg_pi (by linarith) (by linarith)⟩
      · have hnb : F (m + 1) < F m' := hmono (m + 1) hlt m' hm' h1
        have hd := sin_pos_lt_pi_of_lt_two_pi (x := F m' - F m) (by linarith) hsb
        exact ⟨Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith),
          Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)⟩
    · have hmk : m + 1 = k := by omega
      rw [hmk, Nat.mod_self] at hm'n ⊢
      have h0 := hFr 0 hkpos
      have h2 : 0 < m' := Nat.pos_of_ne_zero hm'n
      have h3 : m' < m := by omega
      have hnb : F 0 < F m' := hmono 0 hkpos m' hm' h2
      have hbj : F m' < F m := hmono m' hm' m hm h3
      have hd := sin_pos_lt_neg_pi (x := F m' - F m) (by linarith) hsb
      exact ⟨sin_pos_of_lt_neg_pi (by linarith) (by linarith),
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)⟩
  -- the gaps
  set θ : ℕ → ℝ := fun m => if m + 1 < k then F (m + 1) - F m else F 0 - F m + 2 * π with hθ
  have hθcong : ∀ m < k, ∃ n : ℤ, θ m = φ (e ((m + 1) % k)) - φ (e m) + n * (2 * π) := by
    intro m hm
    rcases Nat.lt_or_ge (m + 1) k with hlt | hge
    · refine ⟨0, ?_⟩
      simp only [hθ, hlt, if_true, Nat.mod_eq_of_lt hlt, hF]; simp
    · refine ⟨1, ?_⟩
      have hmk : m + 1 = k := by omega
      simp only [hθ, hmk, Nat.mod_self, hF]; simp
  have hθsin : ∀ m < k, 0 < Real.sin (θ m) := by
    intro m hm
    obtain ⟨b, hb, hsb, hnone⟩ := hnext (e m) (heN m hm)
    have hbe := key m hm b hb hsb hnone
    obtain ⟨n, hn⟩ := hθcong m hm
    rw [hn, ← hbe, Real.sin_add_int_mul_two_pi]
    exact hsb
  have hθpos : ∀ m < k, 0 < θ m ∧ θ m ≤ 2 * π := by
    intro m hm
    rcases Nat.lt_or_ge (m + 1) k with hlt | hge
    · have := hmono m hm (m + 1) hlt (by omega)
      have h1 := hFr m hm
      have h2 := hFr (m + 1) hlt
      simp only [hθ, hlt, if_true]
      constructor <;> linarith
    · have := hFle 0 hkpos m hm (Nat.zero_le _)
      have h1 := hFr m hm
      have h2 := hFr 0 hkpos
      simp only [hθ, show ¬ (m + 1 < k) by omega, if_false]
      constructor <;> linarith
  have hθlt : ∀ m < k, θ m < π := fun m hm =>
    sin_pos_lt_pi_of_lt_two_pi (hθpos m hm).2 (hθsin m hm)
  have hsum : ∑ m ∈ range k, θ m = 2 * π := by
    obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [hk', Finset.sum_range_succ]
    have h1 : ∑ m ∈ range k', θ m = ∑ m ∈ range k', (F (m + 1) - F m) := by
      refine Finset.sum_congr rfl fun m hm => ?_
      have : m + 1 < k := by rw [hk']; simp at hm; omega
      simp only [hθ, this, if_true]
    rw [h1, Finset.sum_range_sub]
    simp only [hθ, show ¬ (k' + 1 < k) by omega, if_false]
    ring
  have hk3 : 3 ≤ k := by
    by_contra hc
    push_neg at hc
    have : ∑ m ∈ range k, θ m < ∑ m ∈ range k, π :=
      Finset.sum_lt_sum_of_nonempty (by simp; omega) fun m hm => hθlt m (Finset.mem_range.1 hm)
    rw [hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
    have hk2 : (k : ℝ) ≤ 2 := by exact_mod_cast (by omega : k ≤ 2)
    nlinarith [Real.pi_pos]
  refine ⟨k, e, θ, ⟨hk3, fun m hm => (hθpos m hm).1, hθlt, hsum⟩, heN, heinj, hsurj, hθcong, key,
    ?_⟩
  -- every direction lies in a sector
  intro ψ hψ1 hψ2
  have h0 := hFr 0 hkpos
  by_cases hψ0 : ψ < F 0
  · refine ⟨k - 1, by omega, ψ + 2 * π - F (k - 1), ?_, ?_, -1, by push_cast; ring⟩
    · have := hFr (k - 1) (by omega); linarith
    · simp only [hθ, show ¬ (k - 1 + 1 < k) by omega, if_false]
      linarith
  · push_neg at hψ0
    set A := (range k).filter (fun m => F m ≤ ψ) with hA
    have hAne : A.Nonempty := ⟨0, by simp [hA, hkpos, hψ0]⟩
    set m := A.max' hAne with hm_def
    have hmA : m ∈ A := A.max'_mem hAne
    simp only [hA, Finset.mem_filter, Finset.mem_range] at hmA
    refine ⟨m, hmA.1, ψ - F m, by linarith [hmA.2], ?_, 0, by push_cast; ring⟩
    rcases Nat.lt_or_ge (m + 1) k with hlt | hge
    · simp only [hθ, hlt, if_true]
      have : ¬ (F (m + 1) ≤ ψ) := by
        intro h
        have : m + 1 ∈ A := by simp [hA, hlt, h]
        have := A.le_max' _ this
        omega
      push_neg at this
      linarith
    · simp only [hθ, show ¬ (m + 1 < k) by omega, if_false]
      linarith

end Erdos99
end

end CircleOrder

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `FanLink`
-/

section FanLink

/-!
# The link of a ray in a complete simplicial fan

For a complete simplicial fan `T` in `ℝ³` with unit rays `u i` (`i ∈ S`), each of which lies in a
cone of the fan, the neighbours of a ray `i` (the rays `j` with `{i, j}` an edge of the fan),
ordered by angle around `u i`, form a single cycle: consecutive neighbours span, together with `i`,
a positively oriented cone of the fan, every positively oriented cone `{i, j, b}` arises in this
way, and the angles between consecutive neighbours are admissible gaps
(`IsSimplicialFan.exists_link_at`).  Every vector is a combination of `u i` and two consecutive
neighbours with nonnegative coefficients on the neighbours (a sector of the link).
-/

open scoped BigOperators Real

@[expose] public noncomputable section

open Classical Real Finset

namespace Erdos99

variable {ι : Type*} {S : Finset ι} {u : ι → Space3} {T : Finset (Finset ι)}

lemma vol3_eq_inner_cross3 (a b c : Space3) : vol3 a b c = inner ℝ (cross3 a b) c :=
  (inner_cross3 a b c).symm

lemma vol3_self_mid' (a c : Space3) : vol3 a a c = 0 := by unfold vol3; ring

lemma vol3_self_right' (a b : Space3) : vol3 a b b = 0 := by unfold vol3; ring

lemma vol3_self_out' (a b : Space3) : vol3 a b a = 0 := by unfold vol3; ring

/-- The two rays of a fan edge are not parallel. -/
lemma IsSimplicialFan.inner_sq_lt_one_of_edge (hfan : IsSimplicialFan S u T)
    (hu : ∀ i ∈ S, ‖u i‖ = 1) {i j : ι} (hij : FanEdge T i j) : inner ℝ (u i) (u j) ^ 2 < 1 := by
  obtain ⟨hne, τ, hτ, hiτ, hjτ⟩ := hij
  exact hfan.inner_sq_lt_one hu hτ hiτ hjτ hne

lemma ne_of_vol3_pos {a b c : Space3} (h : 0 < vol3 a b c) : a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl
  · rw [vol3_self_mid'] at h; exact lt_irrefl _ h
  · rw [vol3_self_out'] at h; exact lt_irrefl _ h
  · rw [vol3_self_right'] at h; exact lt_irrefl _ h

lemma ne_idx_of_vol3_pos {i j b : ι} (h : 0 < vol3 (u i) (u j) (u b)) : i ≠ j ∧ i ≠ b ∧ j ≠ b := by
  obtain ⟨h1, h2, h3⟩ := ne_of_vol3_pos h
  exact ⟨fun e => h1 (by rw [e]), fun e => h2 (by rw [e]), fun e => h3 (by rw [e])⟩

/-- Across the edge `ij` there is a cone `{i, j, b}` with `(u i, u j, u b)` positively oriented. -/
lemma IsSimplicialFan.exists_next (hfan : IsSimplicialFan S u T) (hu : ∀ i ∈ S, ‖u i‖ = 1)
    {i j : ι} (hij : FanEdge T i j) :
    ∃ b, ({i, j, b} : Finset ι) ∈ T ∧ 0 < vol3 (u i) (u j) (u b) := by
  have hc := hfan.inner_sq_lt_one_of_edge hu hij
  obtain ⟨hne, τ, hτ, hiτ, hjτ⟩ := hij
  have hi := hfan.subset τ hτ hiτ
  have hj := hfan.subset τ hτ hjτ
  set n := -cross3 (u i) (u j) with hn_def
  have hn : n ≠ 0 := by
    intro h0
    have h1 : cross3 (u i) (u j) = 0 := neg_eq_zero.1 h0
    have h2 := norm_cross3_sq (u i) (u j)
    rw [h1, hu i hi, hu j hj, norm_zero] at h2
    nlinarith
  have hni : inner ℝ (u i) n = 0 := by
    rw [hn_def, inner_neg_right, real_inner_comm, inner_cross3_left, neg_zero]
  have hnj : inner ℝ (u j) n = 0 := by
    rw [hn_def, inner_neg_right, real_inner_comm, inner_cross3_right, neg_zero]
  obtain ⟨τ', hτ', hiτ', hjτ', b, hbτ', hb⟩ :=
    hfan.exists_cone_other_side hτ hiτ hjτ hne hn hni hnj
  have hv : 0 < vol3 (u i) (u j) (u b) := by
    rw [hn_def, inner_neg_right, real_inner_comm, inner_cross3] at hb
    linarith
  obtain ⟨-, hbi, hbj⟩ := ne_idx_of_vol3_pos hv
  obtain ⟨a, hai, haj, rfl⟩ := hfan.exists_third hτ' hiτ' hjτ' hne
  have hba : b = a := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hbτ'
    rcases hbτ' with h | h | h
    · exact absurd h.symm hbi
    · exact absurd h.symm hbj
    · exact h
  subst hba
  exact ⟨b, hτ', hv⟩

/-- No fan edge at `i` lies strictly inside a cone `{i, j, b}`. -/
lemma IsSimplicialFan.no_between (hfan : IsSimplicialFan S u T) {i j b l : ι}
    (hτ : ({i, j, b} : Finset ι) ∈ T) (hv : 0 < vol3 (u i) (u j) (u b)) (hl : FanEdge T i l)
    (h1 : 0 < vol3 (u i) (u j) (u l)) (h2 : 0 < vol3 (u i) (u l) (u b)) : False := by
  obtain ⟨hij, hib, hjb⟩ := ne_idx_of_vol3_pos hv
  set D := vol3 (u i) (u j) (u b)
  set V' := vol3 (u l) (u j) (u b)
  set ε := D / (2 * (|V'| + 1)) with hε_def
  have hε : 0 < ε := by positivity
  have hεV : ε * |V'| ≤ D / 2 := by
    rw [hε_def, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg V']
  set z := (1 : ℝ) • u i + ε • u l with hz_def
  have hz : z ∈ intCone u {i, j, b} := by
    rw [mem_intCone_three_iff hij hib hjb hv.ne']
    refine ⟨div_pos ?_ hv, div_pos ?_ hv, div_pos ?_ hv⟩
    · rw [hz_def, vol3_comb_left]
      have := neg_abs_le V'
      nlinarith
    · rw [hz_def, vol3_comb_mid, vol3_self_mid']
      nlinarith
    · rw [hz_def, vol3_comb_right, vol3_self_out']
      nlinarith
  exact hfan.not_mem_edge_of_int hτ hz hl (mem_finCone_pair hl.1 zero_le_one hε.le)

/-- **The link of a ray of a complete simplicial fan.** -/
theorem IsSimplicialFan.exists_link_at (hfan : IsSimplicialFan S u T) (hu : ∀ i ∈ S, ‖u i‖ = 1)
    (hused : ∀ i ∈ S, ∃ τ ∈ T, i ∈ τ) {i : ι} (hi : i ∈ S) :
    ∃ (k : ℕ) (e : ℕ → ι) (θ : ℕ → ℝ), ValidGaps k θ ∧
      (∀ m < k, e m ∈ S.erase i) ∧
      (∀ m < k, ∀ m' < k, e m = e m' → m = m') ∧
      (∀ m < k, inner ℝ (u i) (u (e m)) ^ 2 < 1) ∧
      (∀ m < k, Real.sin (θ m) * (√(1 - inner ℝ (u i) (u (e m)) ^ 2) *
        √(1 - inner ℝ (u i) (u (e ((m + 1) % k))) ^ 2)) =
          vol3 (u i) (u (e m)) (u (e ((m + 1) % k)))) ∧
      (∀ m < k, Real.cos (θ m) * (√(1 - inner ℝ (u i) (u (e m)) ^ 2) *
        √(1 - inner ℝ (u i) (u (e ((m + 1) % k))) ^ 2)) =
          inner ℝ (u (e m)) (u (e ((m + 1) % k))) -
            inner ℝ (u i) (u (e m)) * inner ℝ (u i) (u (e ((m + 1) % k)))) ∧
      (∀ m < k, ({i, e m, e ((m + 1) % k)} : Finset ι) ∈ T) ∧
      (∀ m < k, 0 < vol3 (u i) (u (e m)) (u (e ((m + 1) % k)))) ∧
      (∀ j b, ({i, j, b} : Finset ι) ∈ T → 0 < vol3 (u i) (u j) (u b) →
        ∃ m < k, e m = j ∧ e ((m + 1) % k) = b) ∧
      (∀ x : Space3, ∃ m < k, ∃ γ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧
        x = γ • u i + α • u (e m) + β • u (e ((m + 1) % k))) := by
  obtain ⟨e1, e2, he1a, he2a, hC, hV⟩ := exists_frame (hu i hi)
  have haa : inner ℝ (u i) (u i) = 1 := by
    rw [real_inner_self_eq_norm_sq, hu i hi]; norm_num
  set N := S.filter (fun j => FanEdge T i j) with hN_def
  have hmemN : ∀ {j}, j ∈ N ↔ j ∈ S ∧ FanEdge T i j := by intro j; simp [hN_def]
  set z : ι → ℂ := fun j => planeC e1 e2 (u j) with hz_def
  set φ : ι → ℝ := fun j => Complex.arg (z j) with hφ_def
  have hnd : ∀ j ∈ N, inner ℝ (u i) (u j) ^ 2 < 1 := fun j hj =>
    hfan.inner_sq_lt_one_of_edge hu (hmemN.1 hj).2
  have hznorm : ∀ j ∈ N, ‖z j‖ = √(1 - inner ℝ (u i) (u j) ^ 2) := fun j hj =>
    planeC_norm_of_unit hC (hu j (hmemN.1 hj).1)
  have hzpos : ∀ j ∈ N, 0 < ‖z j‖ := fun j hj => by
    rw [hznorm j hj]; exact Real.sqrt_pos.2 (by linarith [hnd j hj])
  have hsinv : ∀ j l, Real.sin (φ l - φ j) * (‖z j‖ * ‖z l‖) = vol3 (u i) (u j) (u l) :=
    fun j l => sin_arg_sub hV (u j) (u l)
  have hcosv : ∀ j l, Real.cos (φ l - φ j) * (‖z j‖ * ‖z l‖) =
      inner ℝ (u j) (u l) - inner ℝ (u i) (u j) * inner ℝ (u i) (u l) :=
    fun j l => cos_arg_sub hC (u j) (u l)
  have hsign : ∀ j ∈ N, ∀ l ∈ N, (0 < Real.sin (φ l - φ j) ↔ 0 < vol3 (u i) (u j) (u l)) := by
    intro j hj l hl
    rw [← hsinv j l]
    have := mul_pos (hzpos j hj) (hzpos l hl)
    exact (mul_pos_iff_of_pos_right this).symm
  have hNne : N.Nonempty := by
    obtain ⟨τ, hτ, hiτ⟩ := hused i hi
    obtain ⟨p, q, hpi, -, -, rfl⟩ := hfan.exists_two_others hτ hiτ
    exact ⟨p, hmemN.2 ⟨hfan.subset _ hτ (by simp), hpi.symm, _, hτ, by simp, by simp⟩⟩
  have hφr : ∀ j ∈ N, -π < φ j ∧ φ j ≤ π := fun j _ =>
    ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩
  have hinj : Set.InjOn φ N := by
    intro j hj l hl hφeq
    by_contra hjl
    have hjN := hmemN.1 hj
    have hlN := hmemN.1 hl
    set r := ‖z l‖ / ‖z j‖ with hr_def
    have hr : 0 < r := div_pos (hzpos l hl) (hzpos j hj)
    obtain ⟨hj1, hj2⟩ := planeC_re_im (e1 := e1) (e2 := e2) (u j)
    obtain ⟨hl1, hl2⟩ := planeC_re_im (e1 := e1) (e2 := e2) (u l)
    have hφeq' : Complex.arg (planeC e1 e2 (u l)) = Complex.arg (planeC e1 e2 (u j)) :=
      hφeq.symm
    have hzj : ‖planeC e1 e2 (u j)‖ ≠ 0 := (hzpos j hj).ne'
    have hre : inner ℝ e1 (u l) = r * inner ℝ e1 (u j) := by
      rw [← hj1, ← hl1, hφeq']; simp only [hr_def, hz_def]; field_simp
    have him : inner ℝ e2 (u l) = r * inner ℝ e2 (u j) := by
      rw [← hj2, ← hl2, hφeq']; simp only [hr_def, hz_def]; field_simp
    set γ := inner ℝ (u i) (u l) - r * inner ℝ (u i) (u j) with hγ
    have hlin : u l = γ • u i + r • u j := by
      apply frame_ext hC
      · simp only [inner_add_right, inner_smul_right, haa, hγ]; ring
      · simp only [inner_add_right, inner_smul_right, he1a, hre]; ring
      · simp only [inner_add_right, inner_smul_right, he2a, him]; ring
    obtain ⟨hij, τ, hτ, hiτ, hjτ⟩ := hjN.2
    obtain ⟨hil, σ, hσ, hiσ, hlσ⟩ := hlN.2
    by_cases hγ0 : 0 ≤ γ
    · apply hfan.ray_not_mem_finCone ⟨σ, hσ, hlσ⟩ hτ (B := {i, j})
        (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption)
        (by simp; exact ⟨hil.symm, Ne.symm hjl⟩)
      rw [hlin]
      exact mem_finCone_pair hij hγ0 hr.le
    · push_neg at hγ0
      apply hfan.ray_not_mem_finCone ⟨τ, hτ, hjτ⟩ hσ (B := {i, l})
        (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption)
        (by simp; exact ⟨hij.symm, hjl⟩)
      have : u j = (-γ / r) • u i + (1 / r) • u l := by
        rw [hlin, smul_add, smul_smul, smul_smul, ← add_assoc, ← add_smul]
        field_simp
        simp
      rw [this]
      exact mem_finCone_pair hil (div_nonneg (by linarith) hr.le) (by positivity)
  have hbN : ∀ {j b}, ({i, j, b} : Finset ι) ∈ T → 0 < vol3 (u i) (u j) (u b) → j ∈ N ∧ b ∈ N := by
    intro j b hT hv
    obtain ⟨hij, hib, -⟩ := ne_idx_of_vol3_pos hv
    exact ⟨hmemN.2 ⟨hfan.subset _ hT (by simp), hij, _, hT, by simp, by simp⟩,
      hmemN.2 ⟨hfan.subset _ hT (by simp), hib, _, hT, by simp, by simp⟩⟩
  have hnone : ∀ {j b}, ({i, j, b} : Finset ι) ∈ T → 0 < vol3 (u i) (u j) (u b) →
      ∀ l ∈ N, ¬ (0 < Real.sin (φ l - φ j) ∧ 0 < Real.sin (φ b - φ l)) := by
    intro j b hT hv l hl ⟨h1, h2⟩
    obtain ⟨hjN, hbN'⟩ := hbN hT hv
    exact hfan.no_between hT hv (hmemN.1 hl).2 ((hsign j hjN l hl).1 h1)
      ((hsign l hl b hbN').1 h2)
  have hnext' : ∀ j ∈ N, ∃ b ∈ N, 0 < Real.sin (φ b - φ j) ∧
      ∀ l ∈ N, ¬ (0 < Real.sin (φ l - φ j) ∧ 0 < Real.sin (φ b - φ l)) := by
    intro j hj
    obtain ⟨b, hbT, hbv⟩ := hfan.exists_next hu (hmemN.1 hj).2
    have hb := (hbN hbT hbv).2
    exact ⟨b, hb, (hsign j hj b hb).2 hbv, hnone hbT hbv⟩
  obtain ⟨k, e, θ, hval, heN, heinj, hsurj, hcong, hkey, hsector⟩ :=
    circle_cycle hNne φ hφr hinj hnext'
  have hkpos : 0 < k := by have := hval.three_le; omega
  have hmodN : ∀ m < k, e ((m + 1) % k) ∈ N := fun m _ => heN _ (Nat.mod_lt _ hkpos)
  have hsucc : ∀ m < k, ({i, e m, e ((m + 1) % k)} : Finset ι) ∈ T ∧
      0 < vol3 (u i) (u (e m)) (u (e ((m + 1) % k))) := by
    intro m hm
    have hj := heN m hm
    obtain ⟨b, hbT, hbv⟩ := hfan.exists_next hu (hmemN.1 hj).2
    have hb := (hbN hbT hbv).2
    have := hkey m hm b hb ((hsign _ hj b hb).2 hbv) (hnone hbT hbv)
    rw [← this]
    exact ⟨hbT, hbv⟩
  refine ⟨k, e, θ, hval, ?_, heinj, fun m hm => hnd _ (heN m hm), ?_, ?_,
    fun m hm => (hsucc m hm).1, fun m hm => (hsucc m hm).2, ?_, ?_⟩
  · intro m hm
    obtain ⟨h1, h2⟩ := hmemN.1 (heN m hm)
    exact Finset.mem_erase.2 ⟨h2.1.symm, h1⟩
  · intro m hm
    obtain ⟨n, hn⟩ := hcong m hm
    rw [hn, Real.sin_add_int_mul_two_pi, ← hznorm _ (heN m hm), ← hznorm _ (hmodN m hm)]
    exact hsinv _ _
  · intro m hm
    obtain ⟨n, hn⟩ := hcong m hm
    rw [hn, Real.cos_add_int_mul_two_pi, ← hznorm _ (heN m hm), ← hznorm _ (hmodN m hm)]
    exact hcosv _ _
  · intro j b hT hv
    obtain ⟨hjN, hbN'⟩ := hbN hT hv
    obtain ⟨m, hm, rfl⟩ := hsurj j hjN
    exact ⟨m, hm, rfl, (hkey m hm b hbN' ((hsign _ hjN _ hbN').2 hv) (hnone hT hv)).symm⟩
  · intro x
    by_cases hx0 : planeC e1 e2 x = 0
    · refine ⟨0, hkpos, inner ℝ (u i) x, 0, 0, le_refl _, le_refl _, ?_⟩
      have h1 : inner ℝ e1 x = 0 := by
        have := congrArg Complex.re hx0; simpa [planeC] using this
      have h2 : inner ℝ e2 x = 0 := by
        have := congrArg Complex.im hx0; simpa [planeC] using this
      apply frame_ext hC
      · simp only [inner_add_right, inner_smul_right, haa]; ring
      · simp only [inner_add_right, inner_smul_right, he1a, h1]; ring
      · simp only [inner_add_right, inner_smul_right, he2a, h2]; ring
    · set ψ := Complex.arg (planeC e1 e2 x) with hψ_def
      obtain ⟨m, hm, t, ht0, htθ, n, hψ⟩ :=
        hsector ψ (Complex.neg_pi_lt_arg _) (Complex.arg_le_pi _)
      have hja := heN m hm
      have hjb := hmodN m hm
      obtain ⟨n', hn'⟩ := hcong m hm
      have hθ0 := hval.pos m hm
      have hθπ := hval.lt_pi m hm
      have hθs : 0 < Real.sin (θ m) := Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ
      have hst : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi ht0 (by linarith)
      have hsθt : 0 ≤ Real.sin (θ m - t) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
      have hza := hzpos _ hja
      have hzb := hzpos _ hjb
      set W := ‖planeC e1 e2 x‖ with hW
      have hW0 : 0 ≤ W := norm_nonneg _
      set α := W * Real.sin (θ m - t) / (Real.sin (θ m) * ‖z (e m)‖) with hα
      set β := W * Real.sin t / (Real.sin (θ m) * ‖z (e ((m + 1) % k))‖) with hβ
      refine ⟨m, hm, inner ℝ (u i) x - α * inner ℝ (u i) (u (e m)) -
        β * inner ℝ (u i) (u (e ((m + 1) % k))), α, β, by positivity, by positivity, ?_⟩
      obtain ⟨hx1, hx2⟩ := planeC_re_im (e1 := e1) (e2 := e2) x
      obtain ⟨ha1, ha2⟩ := planeC_re_im (e1 := e1) (e2 := e2) (u (e m))
      obtain ⟨hb1, hb2⟩ := planeC_re_im (e1 := e1) (e2 := e2) (u (e ((m + 1) % k)))
      have hψ' : ψ = (φ (e m) + t) + n * (2 * π) := by rw [hψ]
      have hφb : φ (e ((m + 1) % k)) = (φ (e m) + θ m) + ((-n' : ℤ) : ℝ) * (2 * π) := by
        rw [hn']; push_cast; ring
      have hcψ : Real.cos ψ = Real.cos (φ (e m) + t) := by
        rw [hψ', Real.cos_add_int_mul_two_pi]
      have hsψ : Real.sin ψ = Real.sin (φ (e m) + t) := by
        rw [hψ', Real.sin_add_int_mul_two_pi]
      have hcb : Real.cos (φ (e ((m + 1) % k))) = Real.cos (φ (e m) + θ m) := by
        rw [hφb, Real.cos_add_int_mul_two_pi]
      have hsb : Real.sin (φ (e ((m + 1) % k))) = Real.sin (φ (e m) + θ m) := by
        rw [hφb, Real.sin_add_int_mul_two_pi]
      apply frame_ext hC
      · simp only [inner_add_right, inner_smul_right, haa]; ring
      · simp only [inner_add_right, inner_smul_right, he1a]
        rw [← hx1, ← ha1, ← hb1]
        simp only [hφ_def, hz_def] at hcb
        rw [hcψ, hcb, hα, hβ]
        field_simp
        rw [Real.cos_add, Real.cos_add, Real.sin_sub]
        ring
      · simp only [inner_add_right, inner_smul_right, he2a]
        rw [← hx2, ← ha2, ← hb2]
        simp only [hφ_def, hz_def] at hsb
        rw [hsψ, hsb, hα, hβ]
        field_simp
        rw [Real.sin_add, Real.sin_add, Real.sin_sub]
        ring

/-- Splitting a rotation-invariant sum of flags into rotation classes. -/
lemma sum_rot3 {P : Finset (ι × ι × ι)} (key : ι → ℕ)
    (hrot : ∀ t ∈ P, (t.2.1, t.2.2, t.1) ∈ P)
    (hdist : ∀ t ∈ P, key t.1 ≠ key t.2.1 ∧ key t.1 ≠ key t.2.2 ∧ key t.2.1 ≠ key t.2.2)
    (F : ι → ι → ι → ℝ) :
    ∑ t ∈ P, F t.1 t.2.1 t.2.2 =
      ∑ t ∈ P.filter (fun t => key t.1 < key t.2.1 ∧ key t.1 < key t.2.2),
        (F t.1 t.2.1 t.2.2 + F t.2.1 t.2.2 t.1 + F t.2.2 t.1 t.2.1) := by
  set Q := P.filter (fun t => key t.1 < key t.2.1 ∧ key t.1 < key t.2.2) with hQ
  set B := P.filter (fun t => key t.2.2 < key t.1 ∧ key t.2.2 < key t.2.1) with hB
  set C := P.filter (fun t => key t.2.1 < key t.1 ∧ key t.2.1 < key t.2.2) with hC
  have hrot2 : ∀ t ∈ P, (t.2.2, t.1, t.2.1) ∈ P := fun t ht => hrot _ (hrot t ht)
  have hB' : (P.filter (fun t => ¬ (key t.1 < key t.2.1 ∧ key t.1 < key t.2.2))).filter
      (fun t => key t.2.2 < key t.1 ∧ key t.2.2 < key t.2.1) = B := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun t ht => ?_
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨fun h' => by omega, h⟩
  have hC' : (P.filter (fun t => ¬ (key t.1 < key t.2.1 ∧ key t.1 < key t.2.2))).filter
      (fun t => ¬ (key t.2.2 < key t.1 ∧ key t.2.2 < key t.2.1)) = C := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun t ht => ?_
    obtain ⟨h1, h2, h3⟩ := hdist t ht
    constructor
    · intro ⟨ha, hb⟩; omega
    · intro h; omega
  have hsplit : ∑ t ∈ P, F t.1 t.2.1 t.2.2 =
      ∑ t ∈ Q, F t.1 t.2.1 t.2.2 + ∑ t ∈ B, F t.1 t.2.1 t.2.2 + ∑ t ∈ C, F t.1 t.2.1 t.2.2 := by
    rw [← Finset.sum_filter_add_sum_filter_not P
      (fun t => key t.1 < key t.2.1 ∧ key t.1 < key t.2.2),
      ← Finset.sum_filter_add_sum_filter_not
      (P.filter (fun t => ¬ (key t.1 < key t.2.1 ∧ key t.1 < key t.2.2)))
      (fun t => key t.2.2 < key t.1 ∧ key t.2.2 < key t.2.1), hB', hC', add_assoc]
  have hBQ : ∑ t ∈ B, F t.1 t.2.1 t.2.2 = ∑ t ∈ Q, F t.2.1 t.2.2 t.1 := by
    symm
    refine Finset.sum_nbij' (fun t => (t.2.1, t.2.2, t.1)) (fun t => (t.2.2, t.1, t.2.1))
      ?_ ?_ ?_ ?_ ?_
    · intro t ht
      simp only [hQ, hB, Finset.mem_filter] at ht ⊢
      exact ⟨hrot t ht.1, ht.2⟩
    · intro t ht
      simp only [hQ, hB, Finset.mem_filter] at ht ⊢
      exact ⟨hrot2 t ht.1, ht.2⟩
    · intro t _; rfl
    · intro t _; rfl
    · intro t _; rfl
  have hCQ : ∑ t ∈ C, F t.1 t.2.1 t.2.2 = ∑ t ∈ Q, F t.2.2 t.1 t.2.1 := by
    symm
    refine Finset.sum_nbij' (fun t => (t.2.2, t.1, t.2.1)) (fun t => (t.2.1, t.2.2, t.1))
      ?_ ?_ ?_ ?_ ?_
    · intro t ht
      simp only [hQ, hC, Finset.mem_filter] at ht ⊢
      exact ⟨hrot2 t ht.1, ht.2.2, ht.2.1⟩
    · intro t ht
      simp only [hQ, hC, Finset.mem_filter] at ht ⊢
      exact ⟨hrot t ht.1, ht.2.2, ht.2.1⟩
    · intro t _; rfl
    · intro t _; rfl
    · intro t _; rfl
  rw [hsplit, hBQ, hCQ, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]

/-- **Triangulated links of a complete simplicial fan.**  The links of all rays, with the gaps
between consecutive neighbours, form triangulated link data (`LinkData`) whose triangles are the
positively oriented cones of the fan. -/
theorem IsSimplicialFan.exists_links (hfan : IsSimplicialFan S u T) (hu : ∀ i ∈ S, ‖u i‖ = 1)
    (hused : ∀ i ∈ S, ∃ τ ∈ T, i ∈ τ) :
    ∃ (k : ι → ℕ) (nbr : ι → ℕ → ι) (θ : ι → ℕ → ℝ) (T' : Finset (ι × ι × ι)),
      (∀ i ∈ S, ValidGaps (k i) (θ i)) ∧ LinkData S u k nbr θ T' ∧
      (∀ i ∈ S, ∀ m < k i, nbr i m ∈ S.erase i) ∧
      (∀ i ∈ S, ∀ m < k i, ∀ m' < k i, nbr i m = nbr i m' → m = m') ∧
      (∀ i ∈ S, ∀ m < k i, ({i, nbr i m, nbr i ((m + 1) % k i)} : Finset ι) ∈ T) ∧
      (∀ i ∈ S, ∀ m < k i, 0 < vol3 (u i) (u (nbr i m)) (u (nbr i ((m + 1) % k i)))) ∧
      (∀ i ∈ S, ∀ x : Space3, ∃ m < k i, ∃ γ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧
        x = γ • u i + α • u (nbr i m) + β • u (nbr i ((m + 1) % k i))) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨fun _ => 0, fun i => (IsEmpty.false i).elim, fun _ _ => 0, ∅, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩ <;> try (intro i; exact (IsEmpty.false i).elim)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try (intro i; exact (IsEmpty.false i).elim)
    · intro F
      have hS : S = ∅ := Finset.eq_empty_of_forall_notMem fun i => (IsEmpty.false i).elim
      simp [hS]
  have hloc := fun i (hi : i ∈ S) => hfan.exists_link_at hu hused hi
  choose! k nbr θ hval hmem hinj hnd hsin hcos hcone hpos hconv hsec using hloc
  set key : ι → ℕ := fun j => if h : j ∈ S then (S.equivFin ⟨j, h⟩ : ℕ) else 0 with hkey
  have hkeyinj : ∀ a ∈ S, ∀ b ∈ S, key a = key b → a = b := by
    intro a ha b hb hab
    simp only [hkey, ha, hb, dif_pos] at hab
    have := S.equivFin.injective (Fin.ext hab)
    simpa using this
  set P := (S ×ˢ S ×ˢ S).filter (fun t => ({t.1, t.2.1, t.2.2} : Finset ι) ∈ T ∧
    0 < vol3 (u t.1) (u t.2.1) (u t.2.2)) with hP
  have hmemP : ∀ {t : ι × ι × ι}, t ∈ P ↔ ({t.1, t.2.1, t.2.2} : Finset ι) ∈ T ∧
      0 < vol3 (u t.1) (u t.2.1) (u t.2.2) := by
    intro t
    simp only [hP, Finset.mem_filter, Finset.mem_product]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨⟨hfan.subset _ h.1 (by simp), hfan.subset _ h.1 (by simp),
        hfan.subset _ h.1 (by simp)⟩, h⟩
  set T' := P.filter (fun t => key t.1 < key t.2.1 ∧ key t.1 < key t.2.2) with hT'
  have hflagP : ∀ F : ι → ι → ι → ℝ,
      ∑ i ∈ S, ∑ m ∈ range (k i), F i (nbr i m) (nbr i ((m + 1) % k i)) =
        ∑ t ∈ P, F t.1 t.2.1 t.2.2 := by
    intro F
    rw [Finset.sum_sigma']
    refine Finset.sum_bij (fun a _ => (a.1, nbr a.1 a.2, nbr a.1 ((a.2 + 1) % k a.1)))
      ?_ ?_ ?_ ?_
    · intro a ha
      rw [Finset.mem_sigma, Finset.mem_range] at ha
      exact hmemP.2 ⟨hcone a.1 ha.1 a.2 ha.2, hpos a.1 ha.1 a.2 ha.2⟩
    · intro a ha b hb hab
      rw [Finset.mem_sigma, Finset.mem_range] at ha hb
      simp only [Prod.mk.injEq] at hab
      obtain ⟨h1, h2, -⟩ := hab
      obtain ⟨a1, a2⟩ := a
      obtain ⟨b1, b2⟩ := b
      simp only at h1 h2 ha hb
      subst h1
      have := hinj a1 ha.1 a2 ha.2 b2 hb.2 h2
      subst this
      rfl
    · intro t ht
      obtain ⟨hT, hv⟩ := hmemP.1 ht
      have ha : t.1 ∈ S := hfan.subset _ hT (by simp)
      obtain ⟨m, hm, h1, h2⟩ := hconv t.1 ha t.2.1 t.2.2 hT hv
      refine ⟨⟨t.1, m⟩, Finset.mem_sigma.2 ⟨ha, Finset.mem_range.2 hm⟩, ?_⟩
      simp only [h1, h2]
    · intro a _; rfl
  refine ⟨k, nbr, θ, T', hval, ⟨hnd, ?_, hsin, hcos, ?_, ?_⟩, hmem, hinj, hcone, hpos, hsec⟩
  · intro i hi m hm
    exact (Real.sin_pos_of_pos_of_lt_pi ((hval i hi).pos m hm) ((hval i hi).lt_pi m hm)).ne'
  · intro t ht
    obtain ⟨hT, hv⟩ := hmemP.1 (Finset.mem_filter.1 ht).1
    obtain ⟨h12, h13, h23⟩ := ne_idx_of_vol3_pos hv
    exact ⟨hfan.inner_sq_lt_one hu hT (by simp) (by simp) h12,
      hfan.inner_sq_lt_one hu hT (by simp) (by simp) h13,
      hfan.inner_sq_lt_one hu hT (by simp) (by simp) h23⟩
  · intro F
    rw [hflagP F]
    refine sum_rot3 key ?_ ?_ F
    · intro t ht
      obtain ⟨hT, hv⟩ := hmemP.1 ht
      refine hmemP.2 ⟨?_, ?_⟩
      · have : ({t.2.1, t.2.2, t.1} : Finset ι) = {t.1, t.2.1, t.2.2} := by
          ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
        simpa only [this] using hT
      · simpa only [vol3_cyc] using hv
    · intro t ht
      obtain ⟨hT, hv⟩ := hmemP.1 ht
      obtain ⟨h12, h13, h23⟩ := ne_idx_of_vol3_pos hv
      have h1 : t.1 ∈ S := hfan.subset _ hT (by simp)
      have h2 : t.2.1 ∈ S := hfan.subset _ hT (by simp)
      have h3 : t.2.2 ∈ S := hfan.subset _ hT (by simp)
      exact ⟨fun h => h12 (hkeyinj _ h1 _ h2 h), fun h => h13 (hkeyinj _ h1 _ h3 h),
        fun h => h23 (hkeyinj _ h2 _ h3 h)⟩

end Erdos99
end

end FanLink

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `RegularFan`
-/

section RegularFan

/-!
# Regular fans in `ℝ³`

Given finitely many rays `v m` (`m ∈ S`) and heights `u m`, consider the polyhedron
`P = {a : ⟪a, v m⟫ ≤ u m for all m ∈ S}` of "support vectors" and, for `a ∈ P`, its active set
`act a = {m ∈ S : ⟪a, v m⟫ = u m}`.  The *regular fan* `cones S v u` consists of the active sets of
size three.  (Equivalently: the faces of the convex hull of the points `v m / u m`.)

Main result (`RegularFan.isSimplicialFan`): if the rays positively span `ℝ³` (`PosSpan`), the
heights are nonnegative, and the heights are *generic* (`Generic`: every active set is linearly
independent), then `cones S v u` is a complete simplicial fan.  Moreover
(`RegularFan.exists_cone_superset`) every set of indices which is contained in some active set is
contained in a cone of the fan.

The proof is linear programming in three variables: completeness maximizes `⟪a, z⟫` over `P` and
tilts a maximizer until it has three active constraints; two cones meet properly because their
supporting vectors separate them.
-/

open scoped BigOperators
open Filter Topology

@[expose] public noncomputable section

open Classical

namespace Erdos99

namespace RegularFan

variable {ι : Type*} (S : Finset ι) (v : ι → Space3) (u : ι → ℝ)

/-- `a` is feasible: `⟪a, v m⟫ ≤ u m` for all `m ∈ S`. -/
def Feas (a : Space3) : Prop := ∀ m ∈ S, inner ℝ a (v m) ≤ u m

/-- The active set of `a`. -/
def act (a : Space3) : Finset ι := S.filter (fun m => inner ℝ a (v m) = u m)

/-- Genericity of the heights: every active set (of any vector) is linearly independent. -/
def Generic : Prop := ∀ a : Space3, LinearIndependent ℝ (fun m : act S v u a => v m)

/-- The rays positively span `ℝ³`. -/
def PosSpan : Prop := ∀ d : Space3, d ≠ 0 → ∃ m ∈ S, 0 < inner ℝ d (v m)

/-- The regular fan: active sets of feasible vectors which have three elements. -/
def cones : Finset (Finset ι) :=
  S.powerset.filter (fun τ => τ.card = 3 ∧ ∃ a, Feas S v u a ∧ act S v u a = τ)

variable {S v u}

lemma act_subset (a : Space3) : act S v u a ⊆ S := Finset.filter_subset _ _

lemma mem_act {a : Space3} {m : ι} : m ∈ act S v u a ↔ m ∈ S ∧ inner ℝ a (v m) = u m := by
  simp [act]

lemma mem_cones_of {a : Space3} (ha : Feas S v u a) (h3 : (act S v u a).card = 3) :
    act S v u a ∈ cones S v u := by
  simp only [cones, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨act_subset a, h3, a, ha, rfl⟩

lemma card_act_le (hgen : Generic S v u) (a : Space3) : (act S v u a).card ≤ 3 := by
  have := (hgen a).fintype_card_le_finrank
  simpa [finrank_euclideanSpace_fin] using this

/-- Fewer than three vectors have a common nonzero orthogonal vector. -/
lemma exists_perp (A : Finset ι) (hA : A.card < 3) :
    ∃ d : Space3, d ≠ 0 ∧ ∀ m ∈ A, inner ℝ d (v m) = 0 := by
  set K : Submodule ℝ Space3 := Submodule.span ℝ ((A.image v : Finset Space3) : Set Space3)
  have hK : K ≠ ⊤ := by
    intro hK
    have h1 := finrank_span_finset_le_card (R := ℝ) (A.image v)
    have h2 : Set.finrank ℝ ((A.image v : Finset Space3) : Set Space3) = 3 := by
      unfold Set.finrank
      change Module.finrank ℝ K = 3
      rw [hK, finrank_top, finrank_euclideanSpace_fin]
    have h3 := Finset.card_image_le (s := A) (f := v)
    omega
  have hKo : Kᗮ ≠ ⊥ := fun h => hK (Submodule.orthogonal_eq_bot_iff.1 h)
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hKo
  refine ⟨d, hd0, fun m hm => ?_⟩
  have hvm : v m ∈ K := Submodule.subset_span (by simp; exact ⟨m, hm, rfl⟩)
  rw [real_inner_comm]
  exact Submodule.inner_right_of_mem_orthogonal hvm hd

/-- Dual vectors for a linearly independent family. -/
lemma exists_dual {A : Finset ι} (hli : LinearIndependent ℝ (fun m : A => v m)) {k : ι}
    (hk : k ∈ A) : ∃ d : Space3, inner ℝ d (v k) = 1 ∧ ∀ m ∈ A, m ≠ k → inner ℝ d (v m) = 0 := by
  set w : A → Space3 := fun m => v m
  set K : Submodule ℝ Space3 := Submodule.span ℝ (w '' {x | x ≠ ⟨k, hk⟩})
  have hnot : w ⟨k, hk⟩ ∉ K := hli.notMem_span_image (by simp)
  obtain ⟨y, hy, z, hz, hyz⟩ := K.exists_add_mem_mem_orthogonal (v k)
  have hz0 : z ≠ 0 := by
    rintro rfl
    apply hnot
    simp only [add_zero] at hyz
    change v k ∈ K
    rw [hyz]; exact hy
  have hzk : inner ℝ z (v k) = ‖z‖ ^ 2 := by
    rw [hyz, inner_add_right, real_inner_self_eq_norm_sq, real_inner_comm,
      Submodule.inner_right_of_mem_orthogonal hy hz, zero_add]
  have hn : ‖z‖ ^ 2 ≠ 0 := by positivity
  refine ⟨(‖z‖ ^ 2)⁻¹ • z, ?_, fun m hm hmk => ?_⟩
  · rw [real_inner_smul_left, hzk, inv_mul_cancel₀ hn]
  · have hvm : v m ∈ K := Submodule.subset_span ⟨⟨m, hm⟩, by simpa using hmk, rfl⟩
    rw [real_inner_smul_left, real_inner_comm, Submodule.inner_right_of_mem_orthogonal hvm hz,
      mul_zero]

/-- Small steps in a direction which does not increase the active constraints stay feasible. -/
lemma eventually_feas {a d : Space3} (ha : Feas S v u a)
    (hd : ∀ m ∈ act S v u a, inner ℝ d (v m) ≤ 0) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), Feas S v u (a + s • d) := by
  unfold Feas
  rw [Filter.eventually_all_finset]
  intro m hm
  have hval : ∀ s : ℝ, inner ℝ (a + s • d) (v m) = inner ℝ a (v m) + s * inner ℝ d (v m) := by
    intro s; rw [inner_add_left, real_inner_smul_left]
  by_cases hma : m ∈ act S v u a
  · have hm' := (mem_act.1 hma).2
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [hval, hm']
    have := hd m hma
    have hs' : (0 : ℝ) < s := hs
    nlinarith
  · have hlt : inner ℝ a (v m) < u m :=
      lt_of_le_of_ne (ha m hm) fun h => hma (mem_act.2 ⟨hm, h⟩)
    have ht : Tendsto (fun s : ℝ => inner ℝ a (v m) + s * inner ℝ d (v m)) (𝓝[>] 0)
        (𝓝 (inner ℝ a (v m))) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds
      have : Continuous (fun s : ℝ => inner ℝ a (v m) + s * inner ℝ d (v m)) := by fun_prop
      simpa using this.tendsto 0
    filter_upwards [ht.eventually_lt_const hlt] with s hs
    rw [hval]; exact hs.le

/-- **Tilting.**  Moving a feasible vector in a direction orthogonal to its active rays, until a
new constraint becomes active, strictly enlarges the active set. -/
lemma tilt {a d : Space3} (ha : Feas S v u a) (hd : ∀ m ∈ act S v u a, inner ℝ d (v m) = 0)
    (hpos : ∃ m ∈ S, 0 < inner ℝ d (v m)) :
    ∃ t : ℝ, Feas S v u (a + t • d) ∧ act S v u a ⊆ act S v u (a + t • d) ∧
      (act S v u a).card < (act S v u (a + t • d)).card := by
  set Q := S.filter (fun m => 0 < inner ℝ d (v m))
  have hQ : Q.Nonempty := by
    obtain ⟨m, hm, hmd⟩ := hpos; exact ⟨m, Finset.mem_filter.2 ⟨hm, hmd⟩⟩
  obtain ⟨m0, hm0, hmin⟩ := Q.exists_min_image
    (fun m => (u m - inner ℝ a (v m)) / inner ℝ d (v m)) hQ
  obtain ⟨hm0S, hm0d⟩ := Finset.mem_filter.1 hm0
  set t := (u m0 - inner ℝ a (v m0)) / inner ℝ d (v m0)
  have hval : ∀ m, inner ℝ (a + t • d) (v m) = inner ℝ a (v m) + t * inner ℝ d (v m) := by
    intro m; rw [inner_add_left, real_inner_smul_left]
  have ht0 : 0 ≤ t := div_nonneg (by linarith [ha m0 hm0S]) hm0d.le
  have hfeas : Feas S v u (a + t • d) := by
    intro m hm
    rw [hval]
    by_cases hmd : 0 < inner ℝ d (v m)
    · have := hmin m (Finset.mem_filter.2 ⟨hm, hmd⟩)
      rw [le_div_iff₀ hmd] at this
      linarith
    · push_neg at hmd
      nlinarith [ha m hm]
  have hsub : act S v u a ⊆ act S v u (a + t • d) := by
    intro m hm
    obtain ⟨hmS, hmu⟩ := mem_act.1 hm
    refine mem_act.2 ⟨hmS, ?_⟩
    rw [hval, hd m hm, hmu, mul_zero, add_zero]
  have hm0new : m0 ∈ act S v u (a + t • d) := by
    refine mem_act.2 ⟨hm0S, ?_⟩
    rw [hval]
    simp only [t]
    field_simp
    ring
  have hm0old : m0 ∉ act S v u a := fun h => by
    have := hd m0 h; linarith
  refine ⟨t, hfeas, hsub, Finset.card_lt_card ?_⟩
  exact (Finset.ssubset_iff_of_subset hsub).2 ⟨m0, hm0new, hm0old⟩

/-- Every set of indices contained in an active set is contained in a cone of the regular fan. -/
theorem exists_cone_superset (hgen : Generic S v u) (hspan : PosSpan S v) {a : Space3}
    (ha : Feas S v u a) {B : Finset ι} (hB : B ⊆ act S v u a) :
    ∃ τ ∈ cones S v u, B ⊆ τ := by
  suffices h : ∀ n, ∀ a, Feas S v u a → B ⊆ act S v u a → S.card - (act S v u a).card = n →
      ∃ τ ∈ cones S v u, B ⊆ τ from h _ a ha hB rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a ha hB hn
    rcases (card_act_le hgen a).lt_or_eq with hlt | heq
    · obtain ⟨d, hd0, hd⟩ := exists_perp (v := v) (act S v u a) hlt
      obtain ⟨t, hfeas, hsub, hcard⟩ := tilt ha hd (hspan d hd0)
      have hle := Finset.card_le_card (act_subset (S := S) (v := v) (u := u) (a + t • d))
      exact ih _ (by omega) _ hfeas (hB.trans hsub) rfl
    · exact ⟨_, mem_cones_of ha heq, hB⟩

lemma isCompact_feas (hspan : PosSpan S v) : IsCompact {a | Feas S v u a} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · have : {a | Feas S v u a} = ⋂ m ∈ S, {a : Space3 | inner ℝ a (v m) ≤ u m} := by
      ext a; simp [Feas]
    rw [this]
    exact isClosed_biInter fun m _ => isClosed_le (by fun_prop) continuous_const
  · set g : Space3 → ℝ := fun d => ∑ m ∈ S, max 0 (inner ℝ d (v m))
    have hgc : Continuous g := by fun_prop
    obtain ⟨d0, hd0, hmin⟩ := (isCompact_sphere (0 : Space3) 1).exists_isMinOn
      (NormedSpace.sphere_nonempty.2 zero_le_one) hgc.continuousOn
    have hpos : ∀ d : Space3, d ≠ 0 → 0 < g d := by
      intro d hd
      obtain ⟨m, hm, hmd⟩ := hspan d hd
      exact lt_of_lt_of_le (lt_max_of_lt_right hmd)
        (Finset.single_le_sum (f := fun m => max 0 (inner ℝ d (v m)))
          (fun _ _ => le_max_left _ _) hm)
    have hd0' : d0 ≠ 0 := by
      intro h; rw [h] at hd0; simp at hd0
    set c := g d0
    have hc : 0 < c := hpos d0 hd0'
    set U := ∑ m ∈ S, max 0 (u m)
    have hU : 0 ≤ U := Finset.sum_nonneg fun _ _ => le_max_left _ _
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨U / c, fun a ha => ?_⟩
    rw [mem_closedBall_zero_iff, le_div_iff₀ hc]
    by_cases ha0 : a = 0
    · rw [ha0, norm_zero, zero_mul]; exact hU
    have hna : 0 < ‖a‖ := norm_pos_iff.2 ha0
    have hsph : ‖a‖⁻¹ • a ∈ Metric.sphere (0 : Space3) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hna.ne']
    have h1 : c ≤ g (‖a‖⁻¹ • a) := hmin hsph
    have h2 : g a = ‖a‖ * g (‖a‖⁻¹ • a) := by
      simp only [g, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [mul_max_of_nonneg _ _ hna.le, real_inner_smul_left, ← mul_assoc,
        mul_inv_cancel₀ hna.ne', one_mul, mul_zero]
    have h3 : g a ≤ U :=
      Finset.sum_le_sum fun m hm => max_le_max le_rfl (ha m hm)
    nlinarith

lemma finCone_mono {σ τ : Finset ι} (h : σ ⊆ τ) : finCone v σ ⊆ finCone v τ := by
  rintro z ⟨c, hc, rfl⟩
  refine ⟨fun m => if m ∈ σ then c m else 0, fun m _ => ?_, ?_⟩
  · by_cases hm : m ∈ σ
    · simp only [hm, if_true]; exact hc m hm
    · simp [hm]
  · symm
    rw [← Finset.sum_subset h]
    · exact Finset.sum_congr rfl fun m hm => by simp [hm]
    · intro m _ hm; simp [hm]

/-- **Completeness** of the regular fan. -/
theorem complete (hgen : Generic S v u) (hspan : PosSpan S v) (hu : ∀ m ∈ S, 0 ≤ u m)
    (z : Space3) : ∃ τ ∈ cones S v u, z ∈ finCone v τ := by
  have hne : ({a | Feas S v u a} : Set Space3).Nonempty :=
    ⟨0, fun m hm => by simpa using hu m hm⟩
  obtain ⟨a0, ha0, hmax⟩ := (isCompact_feas (u := u) hspan).exists_isMaxOn hne
    (f := fun a => inner ℝ a z) (by fun_prop)
  set M := inner ℝ a0 z
  have hmax' : ∀ a, Feas S v u a → inner ℝ a z ≤ M := fun a ha => hmax ha
  suffices h : ∀ n, ∀ a, Feas S v u a → inner ℝ a z = M → S.card - (act S v u a).card = n →
      ∃ τ ∈ cones S v u, z ∈ finCone v τ from h _ a0 ha0 rfl rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a ha haM hn
    have hval : ∀ (s : ℝ) (d w : Space3), inner ℝ (a + s • d) w = inner ℝ a w + s * inner ℝ d w :=
      fun s d w => by rw [inner_add_left, real_inner_smul_left]
    rcases (card_act_le hgen a).lt_or_eq with hlt | heq
    · obtain ⟨d, hd0, hd⟩ := exists_perp (v := v) (act S v u a) hlt
      -- first-order condition: `⟪d, z⟫ = 0`
      have hdz : inner ℝ d z = 0 := by
        by_contra hne0
        obtain ⟨e, he, hez⟩ : ∃ e : Space3, (∀ m ∈ act S v u a, inner ℝ e (v m) = 0) ∧
            0 < inner ℝ e z := by
          rcases lt_or_gt_of_ne hne0 with h | h
          · refine ⟨-d, fun m hm => by rw [inner_neg_left, hd m hm, neg_zero], ?_⟩
            rw [inner_neg_left]; linarith
          · exact ⟨d, hd, h⟩
        obtain ⟨s, hs, hspos⟩ := ((eventually_feas ha fun m hm => (he m hm).le).and
          self_mem_nhdsWithin).exists
        have := hmax' _ hs
        rw [hval] at this
        have hspos' : (0 : ℝ) < s := hspos
        nlinarith
      obtain ⟨t, hfeas, hsub, hcard⟩ := tilt ha hd (hspan d hd0)
      have hle := Finset.card_le_card (act_subset (S := S) (v := v) (u := u) (a + t • d))
      exact ih _ (by omega) _ hfeas (by rw [hval, hdz, mul_zero, add_zero, haM]) rfl
    · refine ⟨_, mem_cones_of ha heq, ?_⟩
      set A := act S v u a
      have hli := hgen a
      haveI : Nonempty A := by
        have : 0 < A.card := by omega
        obtain ⟨m, hm⟩ := Finset.card_pos.1 this
        exact ⟨⟨m, hm⟩⟩
      have hspanA := hli.span_eq_top_of_card_eq_finrank
        (by rw [Fintype.card_coe, finrank_euclideanSpace_fin]; exact heq)
      have hz : z ∈ Submodule.span ℝ (Set.range fun m : A => v m) := by
        rw [hspanA]; exact Submodule.mem_top
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hz
      have hcnn : ∀ k : A, 0 ≤ c k := by
        intro k
        by_contra hk
        push_neg at hk
        obtain ⟨d, hdk, hd⟩ := exists_dual hli k.2
        have hdz : inner ℝ d z = c k := by
          rw [← hc, inner_sum]
          rw [Finset.sum_eq_single k]
          · rw [real_inner_smul_right, hdk, mul_one]
          · intro m _ hmk
            rw [real_inner_smul_right, hd m m.2 (fun h => hmk (Subtype.ext h)), mul_zero]
          · simp
        have hstep : ∀ m ∈ A, inner ℝ (-d) (v m) ≤ 0 := by
          intro m hm
          rw [inner_neg_left]
          by_cases hmk : m = k
          · rw [hmk, hdk]; norm_num
          · rw [hd m hm hmk, neg_zero]
        obtain ⟨s, hs, hspos⟩ := ((eventually_feas ha hstep).and self_mem_nhdsWithin).exists
        have := hmax' _ hs
        rw [hval, inner_neg_left, hdz] at this
        have hspos' : (0 : ℝ) < s := hspos
        nlinarith
      refine ⟨fun m => if h : m ∈ A then c ⟨m, h⟩ else 0, fun m hm => by
        simp only [hm, dif_pos]; exact hcnn _, ?_⟩
      rw [← hc, ← Finset.sum_coe_sort A]
      exact Finset.sum_congr rfl fun m _ => by simp

/-- Two cones of the regular fan meet in their common face. -/
theorem inter {τ τ' : Finset ι} (hτ : τ ∈ cones S v u) (hτ' : τ' ∈ cones S v u) :
    finCone v τ ∩ finCone v τ' = finCone v (τ ∩ τ') := by
  apply Set.Subset.antisymm
  · rintro z ⟨⟨c, hc, hzc⟩, ⟨d, hd, hzd⟩⟩
    obtain ⟨-, -, a, ha, rfl⟩ := Finset.mem_filter.1 hτ
    obtain ⟨-, -, a', ha', rfl⟩ := Finset.mem_filter.1 hτ'
    set A := act S v u a
    set A' := act S v u a'
    have e1 : inner ℝ a z = ∑ m ∈ A, c m * u m := by
      rw [hzc, inner_sum]
      exact Finset.sum_congr rfl fun m hm => by rw [real_inner_smul_right, (mem_act.1 hm).2]
    have e2 : inner ℝ a z = ∑ m ∈ A', d m * inner ℝ a (v m) := by
      rw [hzd, inner_sum]
      exact Finset.sum_congr rfl fun m _ => by rw [real_inner_smul_right]
    have e3 : inner ℝ a' z = ∑ m ∈ A', d m * u m := by
      rw [hzd, inner_sum]
      exact Finset.sum_congr rfl fun m hm => by rw [real_inner_smul_right, (mem_act.1 hm).2]
    have e4 : inner ℝ a' z ≤ ∑ m ∈ A, c m * u m := by
      rw [hzc, inner_sum]
      exact Finset.sum_le_sum fun m hm => by
        rw [real_inner_smul_right]
        exact mul_le_mul_of_nonneg_left (ha' m (act_subset a hm)) (hc m hm)
    have hsum : ∑ m ∈ A', d m * (u m - inner ℝ a (v m)) = 0 := by
      apply le_antisymm
      · have : ∑ m ∈ A', d m * (u m - inner ℝ a (v m)) =
            ∑ m ∈ A', d m * u m - ∑ m ∈ A', d m * inner ℝ a (v m) := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun m _ => by ring
        linarith
      · exact Finset.sum_nonneg fun m hm =>
          mul_nonneg (hd m hm) (by linarith [ha m (act_subset a' hm)])
    rw [Finset.sum_eq_zero_iff_of_nonneg fun m hm =>
      mul_nonneg (hd m hm) (by linarith [ha m (act_subset a' hm)])] at hsum
    have hzero : ∀ m ∈ A', m ∉ A → d m = 0 := by
      intro m hm hmA
      have hlt : inner ℝ a (v m) < u m :=
        lt_of_le_of_ne (ha m (act_subset a' hm)) fun h => hmA (mem_act.2 ⟨act_subset a' hm, h⟩)
      rcases mul_eq_zero.1 (hsum m hm) with h | h
      · exact h
      · linarith
    refine ⟨d, fun m hm => hd m (Finset.mem_inter.1 hm).2, ?_⟩
    rw [hzd]
    symm
    apply Finset.sum_subset Finset.inter_subset_right
    intro m hm hmn
    have : m ∉ A := fun h => hmn (Finset.mem_inter.2 ⟨h, hm⟩)
    rw [hzero m hm this, zero_smul]
  · exact Set.subset_inter (finCone_mono Finset.inter_subset_left)
      (finCone_mono Finset.inter_subset_right)

/-- **The regular fan is a complete simplicial fan.** -/
theorem isSimplicialFan (hgen : Generic S v u) (hspan : PosSpan S v) (hu : ∀ m ∈ S, 0 ≤ u m) :
    IsSimplicialFan S v (cones S v u) where
  subset τ hτ := Finset.mem_powerset.1 (Finset.mem_filter.1 hτ).1
  card τ hτ := (Finset.mem_filter.1 hτ).2.1
  indep τ hτ := by
    obtain ⟨-, -, a, -, rfl⟩ := Finset.mem_filter.1 hτ
    exact hgen a
  complete z := complete hgen hspan hu z
  inter τ hτ τ' hτ' := inter hτ hτ'

/-! ## Perturbing the heights -/

variable (S v u) in
/-- `a` is a strict witness for `B`: the constraints in `B` are active, all others strict. -/
def StrictWit (B : Finset ι) (a : Space3) : Prop :=
  ∀ m ∈ S, (m ∈ B → inner ℝ a (v m) = u m) ∧ (m ∉ B → inner ℝ a (v m) < u m)

variable (v) in
/-- The rays indexed by `B` admit dual vectors. -/
def HasDual (B : Finset ι) : Prop :=
  ∀ j ∈ B, ∃ d : Space3, inner ℝ d (v j) = 1 ∧ ∀ m ∈ B, m ≠ j → inner ℝ d (v m) = 0

lemma hasDual_single {i : ι} (h : ∃ d : Space3, inner ℝ d (v i) = 1) : HasDual v {i} := by
  intro j hj
  rw [Finset.mem_singleton] at hj
  subst hj
  obtain ⟨d, hd⟩ := h
  exact ⟨d, hd, fun m hm hmj => absurd (Finset.mem_singleton.1 hm) hmj⟩

lemma hasDual_pair {i j : ι} (h1 : ∃ d : Space3, inner ℝ d (v i) = 1 ∧ inner ℝ d (v j) = 0)
    (h2 : ∃ d : Space3, inner ℝ d (v j) = 1 ∧ inner ℝ d (v i) = 0) : HasDual v {i, j} := by
  intro l hl
  rcases Finset.mem_insert.1 hl with rfl | hl
  · obtain ⟨d, hd1, hd2⟩ := h1
    refine ⟨d, hd1, fun m hm hml => ?_⟩
    rcases Finset.mem_insert.1 hm with rfl | hm
    · exact absurd rfl hml
    · rw [Finset.mem_singleton.1 hm]; exact hd2
  · rw [Finset.mem_singleton.1 hl]
    obtain ⟨d, hd1, hd2⟩ := h2
    refine ⟨d, hd1, fun m hm hml => ?_⟩
    rcases Finset.mem_insert.1 hm with rfl | hm
    · exact hd2
    · exact absurd (Finset.mem_singleton.1 hm) hml

/-- Under genericity, a vector making the constraints of `B ⊆ S` active (and all constraints
feasible) yields a cone of the regular fan containing `B`. -/
lemma exists_cone_of_active (hgen : Generic S v u) (hspan : PosSpan S v) {B : Finset ι}
    (hBS : B ⊆ S) (h : ∃ a, Feas S v u a ∧ ∀ m ∈ B, m ∈ S → inner ℝ a (v m) = u m) :
    ∃ τ ∈ cones S v u, B ⊆ τ := by
  obtain ⟨a, ha, hB⟩ := h
  exact exists_cone_superset hgen hspan ha fun m hm =>
    mem_act.2 ⟨hBS hm, hB m hm (hBS hm)⟩

/-- A strict witness survives a small perturbation `u m + t ^ k m` of the heights. -/
theorem eventually_wit_perturb {k : ι → ℕ} (hk : ∀ m, 1 ≤ k m) {B : Finset ι} {a0 : Space3}
    (hwit : StrictWit S v u B a0) (hdual : HasDual v B) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ∃ a, Feas S v (fun m => u m + t ^ k m) a ∧
      ∀ m ∈ B, m ∈ S → inner ℝ a (v m) = u m + t ^ k m := by
  choose D hD1 hD2 using hdual
  set a : ℝ → Space3 := fun t => a0 + ∑ j ∈ B.attach, (t ^ k j.1) • D j.1 j.2 with ha_def
  have hval : ∀ t m, inner ℝ (a t) (v m) =
      inner ℝ a0 (v m) + ∑ j ∈ B.attach, t ^ k j.1 * inner ℝ (D j.1 j.2) (v m) := by
    intro t m
    simp only [ha_def, inner_add_left, sum_inner, real_inner_smul_left]
  have hB : ∀ t, ∀ m ∈ B, inner ℝ (a t) (v m) = inner ℝ a0 (v m) + t ^ k m := by
    intro t m hm
    rw [hval, Finset.sum_eq_single ⟨m, hm⟩]
    · rw [hD1, mul_one]
    · intro j _ hj
      rw [hD2 j.1 j.2 m hm (fun h => hj (Subtype.ext h.symm)), mul_zero]
    · simp
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ m ∈ S, m ∉ B →
      inner ℝ (a t) (v m) - (u m + t ^ k m) < 0 := by
    rw [Filter.eventually_all_finset]
    intro m hm
    by_cases hmB : m ∈ B
    · exact Filter.Eventually.of_forall fun _ h => absurd hmB h
    have hlt := (hwit m hm).2 hmB
    have hcont : Continuous fun t : ℝ => inner ℝ a0 (v m) +
        ∑ j ∈ B.attach, t ^ k j.1 * inner ℝ (D j.1 j.2) (v m) - (u m + t ^ k m) := by fun_prop
    have h0 : (fun t : ℝ => inner ℝ a0 (v m) +
        ∑ j ∈ B.attach, t ^ k j.1 * inner ℝ (D j.1 j.2) (v m) - (u m + t ^ k m)) 0 =
        inner ℝ a0 (v m) - u m := by
      simp only
      rw [zero_pow (by have := hk m; omega)]
      rw [Finset.sum_eq_zero fun j _ => by rw [zero_pow (by have := hk j.1; omega), zero_mul]]
      ring
    have ht : Tendsto (fun t : ℝ => inner ℝ a0 (v m) +
        ∑ j ∈ B.attach, t ^ k j.1 * inner ℝ (D j.1 j.2) (v m) - (u m + t ^ k m)) (𝓝[>] 0)
        (𝓝 (inner ℝ a0 (v m) - u m)) := by
      rw [← h0]; exact tendsto_nhdsWithin_of_tendsto_nhds (hcont.tendsto 0)
    filter_upwards [ht.eventually_lt_const (by linarith : inner ℝ a0 (v m) - u m < 0)] with t ht
      hmB'
    rw [hval]; exact ht
  filter_upwards [hev] with t ht
  refine ⟨a t, fun m hm => ?_, fun m hm hmS => ?_⟩
  · by_cases hmB : m ∈ B
    · rw [hB t m hmB, (hwit m hm).1 hmB]
    · linarith [ht m hm hmB]
  · rw [hB t m hm, (hwit m hmS).1 hm]

/-- A finite set of reals is eventually avoided as `t → 0⁺`. -/
lemma eventually_notMem_finset (F : Finset ℝ) : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∉ F := by
  have : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ b ∈ F, t ≠ b := by
    rw [Filter.eventually_all_finset]
    intro b _
    by_cases hb : b = 0
    · filter_upwards [self_mem_nhdsWithin] with t ht
      rw [hb]; exact ne_of_gt ht
    · exact nhdsWithin_le_nhds (eventually_ne_nhds (Ne.symm hb))
  filter_upwards [this] with t ht htF
  exact ht t htF rfl

/-- For a linearly dependent set `R` of rays, only finitely many perturbation parameters allow
all constraints of `R` to be active simultaneously. -/
lemma finite_bad_params {k : ι → ℕ} (hk : ∀ m, 1 ≤ k m) (hinj : Set.InjOn k (S : Set ι))
    {R : Finset ι} (hR : R ⊆ S) (hdep : ¬ LinearIndependent ℝ (fun m : R => v m)) :
    ∃ F : Finset ℝ, ∀ t, t ∉ F → ¬ ∃ a : Space3, ∀ m ∈ R, inner ℝ a (v m) = u m + t ^ k m := by
  obtain ⟨g, hg, i0, hi0⟩ := Fintype.not_linearIndependent_iff.1 hdep
  set p : Polynomial ℝ := ∑ i : R, Polynomial.C (g i) *
    (Polynomial.C (u i) + Polynomial.X ^ k i) with hp
  have hcoeff : p.coeff (k i0) = g i0 := by
    rw [hp, Polynomial.finset_sum_coeff]
    rw [Finset.sum_eq_single i0]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_add, Polynomial.coeff_C,
        Polynomial.coeff_X_pow]
      have := hk i0.1
      rw [if_neg (by omega)]; simp
    · intro i _ hi
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_add, Polynomial.coeff_C,
        Polynomial.coeff_X_pow]
      have h1 := hk i0.1
      have h2 : k i0.1 ≠ k i.1 := fun h =>
        hi (Subtype.ext (hinj (hR i.2) (hR i0.2) h.symm))
      rw [if_neg (by omega), if_neg h2]; ring
    · simp
  have hp0 : p ≠ 0 := fun h => hi0 (by rw [← hcoeff, h, Polynomial.coeff_zero])
  refine ⟨p.roots.toFinset, fun t ht ⟨a, ha⟩ => ht ?_⟩
  rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0, Polynomial.IsRoot.def]
  have : p.eval t = inner ℝ a (∑ i : R, g i • v i) := by
    rw [hp, Polynomial.eval_finset_sum, inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_smul_right, ha i i.2]
    simp
  rw [this, hg, inner_zero_right]

/-- **Generic perturbation.**  For all small `t > 0`, the heights `u m + t ^ k m` (with `k`
injective and positive on `S`) are generic. -/
theorem eventually_generic {k : ι → ℕ} (hk : ∀ m, 1 ≤ k m) (hinj : Set.InjOn k (S : Set ι)) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), Generic S v (fun m => u m + t ^ k m) := by
  have hall : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ R ∈ S.powerset,
      ¬ LinearIndependent ℝ (fun m : R => v m) →
        ¬ ∃ a : Space3, ∀ m ∈ R, inner ℝ a (v m) = u m + t ^ k m := by
    rw [Filter.eventually_all_finset]
    intro R hR
    by_cases hdep : LinearIndependent ℝ (fun m : R => v m)
    · exact Filter.Eventually.of_forall fun _ h => absurd hdep h
    obtain ⟨F, hF⟩ := finite_bad_params (u := u) hk hinj (Finset.mem_powerset.1 hR) hdep
    filter_upwards [eventually_notMem_finset F] with t ht _
    exact hF t ht
  filter_upwards [hall] with t ht a
  by_contra hdep
  exact ht _ (Finset.mem_powerset.2 (act_subset a)) hdep ⟨a, fun m hm => (mem_act.1 hm).2⟩

end RegularFan

end Erdos99
end

end RegularFan

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `PolytopeFan`
-/

section PolytopeFan

/-!
# A triangulation of the normal fan of a polytope

For a bounded polytope `polyK S u h` in `ℝ³` with unit normals all of whose facets are present,
there is a complete simplicial fan `T` on the normals in which every normal lies in a cone and
every cone `τ ∈ T` is contained in the normal cone of a vertex: some point `x` of the polytope lies
on all the facets `τ` (`polytope_refined_fan`).  It is the regular fan (`RegularFan`) of the
support numbers `h' + t ^ k(m)` (with respect to an interior point) for small `t > 0`.
-/

open scoped BigOperators
open Filter Topology

@[expose] public noncomputable section

open Classical

namespace Erdos99

variable {ι : Type*}

/-- The normals of a bounded nonempty polytope positively span `ℝ³`. -/
lemma posSpan_of_bounded {S : Finset ι} {u : ι → Space3} {h : ι → ℝ}
    (hbdd : Bornology.IsBounded (polyK S u h)) {x0 : Space3} (hx0 : x0 ∈ polyK S u h) :
    RegularFan.PosSpan S u := by
  intro d hd
  by_contra hcon
  push_neg at hcon
  obtain ⟨R, hR⟩ := hbdd.subset_closedBall 0
  have hdpos : 0 < ‖d‖ := norm_pos_iff.2 hd
  set t := (R + ‖x0‖ + 1) / ‖d‖ with ht
  have hR0 : 0 ≤ R := by
    have := hR hx0
    rw [Metric.mem_closedBall, dist_zero_right] at this
    linarith [norm_nonneg x0]
  have htpos : 0 ≤ t := by positivity
  have hmem : x0 + t • d ∈ polyK S u h := by
    intro m hm
    rw [inner_add_right, inner_smul_right]
    have h1 : inner ℝ (u m) d ≤ 0 := by rw [real_inner_comm]; exact hcon m hm
    have := hx0 m hm
    have := mul_nonpos_of_nonneg_of_nonpos htpos h1
    linarith
  have h1 := hR hmem
  rw [Metric.mem_closedBall, dist_zero_right] at h1
  have h2 : ‖t • d‖ = R + ‖x0‖ + 1 := by
    rw [norm_smul, Real.norm_of_nonneg htpos, ht, div_mul_cancel₀ _ hdpos.ne']
  have h3 : ‖t • d‖ ≤ ‖x0 + t • d‖ + ‖x0‖ := by
    have := norm_sub_le (x0 + t • d) x0
    simp only [add_sub_cancel_left] at this
    linarith
  linarith

/-- Perturbed active sets disappear if they are not active sets of the unperturbed problem. -/
lemma eventually_not_active {S : Finset ι} {u : ι → Space3} {g : ι → ℝ}
    (hspan : RegularFan.PosSpan S u) {kk : ι → ℕ} (hk : ∀ m, 1 ≤ kk m) {B : Finset ι}
    (hbad : ¬ ∃ a, RegularFan.Feas S u g a ∧ ∀ m ∈ B, inner ℝ a (u m) = g m) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ¬ ∃ a, RegularFan.Feas S u (fun m => g m + t ^ kk m) a ∧
      ∀ m ∈ B, inner ℝ a (u m) = g m + t ^ kk m := by
  set G : Space3 → ℝ := fun a => ∑ m ∈ S, max (inner ℝ a (u m) - g m) 0 +
    ∑ m ∈ B, |inner ℝ a (u m) - g m| with hG
  have hGc : Continuous G := by
    simp only [hG]
    fun_prop
  have hG0 : ∀ a, 0 ≤ G a := fun a =>
    add_nonneg (Finset.sum_nonneg fun m _ => le_max_right _ _)
      (Finset.sum_nonneg fun m _ => abs_nonneg _)
  have hGpos : ∀ a, 0 < G a := by
    intro a
    rcases (hG0 a).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hbad
      have h' := h.symm
      rw [hG, add_eq_zero_iff_of_nonneg (Finset.sum_nonneg fun m _ => le_max_right _ _)
        (Finset.sum_nonneg fun m _ => abs_nonneg _)] at h'
      obtain ⟨h1, h2⟩ := h'
      rw [Finset.sum_eq_zero_iff_of_nonneg fun m _ => le_max_right _ _] at h1
      rw [Finset.sum_eq_zero_iff_of_nonneg fun m _ => abs_nonneg _] at h2
      refine ⟨a, fun m hm => ?_, fun m hm => ?_⟩
      · have := h1 m hm
        have := le_max_left (inner ℝ a (u m) - g m) 0
        linarith
      · have := h2 m hm
        rw [abs_eq_zero, sub_eq_zero] at this
        exact this
  set Kc := {a | RegularFan.Feas S u (fun m => g m + 1) a} with hKc
  have hKcc : IsCompact Kc := RegularFan.isCompact_feas hspan
  -- a positive lower bound for `G` on the compact set
  obtain ⟨δ, hδ, hδG⟩ : ∃ δ > 0, ∀ a ∈ Kc, δ ≤ G a := by
    rcases Kc.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun a ha => by rw [he] at ha; exact absurd ha (Set.notMem_empty a)⟩
    · obtain ⟨a0, ha0, hmin⟩ := hKcc.exists_isMinOn hne hGc.continuousOn
      exact ⟨G a0, hGpos a0, fun a ha => hmin ha⟩
  set c := min 1 (δ / (2 * ((S.card : ℝ) + B.card + 1))) with hc
  have hcpos : 0 < c := lt_min one_pos (by positivity)
  filter_upwards [Ioo_mem_nhdsGT hcpos] with t ht
  obtain ⟨ht0, htc⟩ := ht
  have ht1 : t ≤ 1 := le_trans htc.le (min_le_left _ _)
  have htδ : t < δ / (2 * ((S.card : ℝ) + B.card + 1)) := lt_of_lt_of_le htc (min_le_right _ _)
  have hpow : ∀ m, t ^ kk m ≤ t := fun m => by
    calc t ^ kk m ≤ t ^ 1 := pow_le_pow_of_le_one ht0.le ht1 (hk m)
      _ = t := pow_one t
  have hpow0 : ∀ m, 0 ≤ t ^ kk m := fun m => by positivity
  rintro ⟨a, ha, hB⟩
  have haK : a ∈ Kc := fun m hm => by
    have := ha m hm
    have := hpow m
    simp only at this ⊢
    linarith
  have h1 : G a ≤ ∑ m ∈ S, t + ∑ m ∈ B, t := by
    simp only [hG]
    gcongr with m hm m hm
    · refine max_le ?_ ht0.le
      have := ha m hm
      have := hpow m
      simp only at this
      linarith
    · rw [hB m hm, add_sub_cancel_left, abs_of_nonneg (hpow0 m)]
      exact hpow m
  rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul] at h1
  have h2 := hδG a haK
  have h3 : ((S.card : ℝ) + B.card) * t < δ := by
    have hpos : (0 : ℝ) < 2 * ((S.card : ℝ) + B.card + 1) := by positivity
    rw [lt_div_iff₀ hpos] at htδ
    nlinarith
  linarith

/-- **A triangulation of the normal fan of a polytope.** -/
theorem polytope_refined_fan {S : Finset ι} {u : ι → Space3} {h : ι → ℝ}
    (hu : ∀ i ∈ S, ‖u i‖ = 1) (hbdd : Bornology.IsBounded (polyK S u h))
    (hfac : FacetsPresent S u h) :
    ∃ (c0 : Space3) (T : Finset (Finset ι)), (∀ m ∈ S, inner ℝ (u m) c0 < h m) ∧
      IsSimplicialFan S u T ∧ (∀ i ∈ S, ∃ τ ∈ T, i ∈ τ) ∧
      ∀ τ ∈ T, ∃ x ∈ polyK S u h, ∀ m ∈ τ, inner ℝ (u m) x = h m := by
  have hSne : S.Nonempty := by
    by_contra hS
    rw [Finset.not_nonempty_iff_eq_empty] at hS
    have : polyK S u h = Set.univ := by ext x; simp [polyK, hS]
    rw [this] at hbdd
    exact NormedSpace.unbounded_univ ℝ Space3 hbdd
  obtain ⟨i0, hi0⟩ := hSne
  have hwit : ∀ i ∈ S, ∃ x ∈ polyK S u h, inner ℝ (u i) x = h i ∧
      ∀ m ∈ S, m ≠ i → inner ℝ (u m) x < h m := by
    intro i hi
    obtain ⟨x, hxi, hxo⟩ := hfac i hi
    refine ⟨x, fun m hm => ?_, hxi, hxo⟩
    by_cases hmi : m = i
    · subst hmi; exact hxi.le
    · exact (hxo m hm hmi).le
  obtain ⟨x0, hx0, -, -⟩ := hwit i0 hi0
  have hspan := posSpan_of_bounded hbdd hx0
  have hui0 : u i0 ≠ 0 := by
    intro h0; have := hu i0 hi0; rw [h0, norm_zero] at this; exact zero_ne_one this
  obtain ⟨j0, hj0, hj0pos⟩ := hspan (-u i0) (neg_ne_zero.2 hui0)
  have hij : i0 ≠ j0 := by
    rintro rfl
    rw [inner_neg_left, real_inner_self_eq_norm_sq, hu i0 hi0] at hj0pos
    norm_num at hj0pos
  obtain ⟨c0, hc0⟩ := exists_interior_point hfac hi0 hj0 hij
  set h' : ι → ℝ := fun m => h m - inner ℝ (u m) c0 with hh'
  have hh'pos : ∀ m ∈ S, 0 < h' m := fun m hm => by simp only [hh']; linarith [hc0 m hm]
  have hshift : ∀ a m, inner ℝ (u m) (a + c0) = inner ℝ a (u m) + inner ℝ (u m) c0 := by
    intro a m; rw [inner_add_right, real_inner_comm]
  -- injective positive exponents for the generic perturbation
  obtain ⟨kk, hk, hkinj⟩ : ∃ kk : ι → ℕ, (∀ m, 1 ≤ kk m) ∧ Set.InjOn kk (S : Set ι) := by
    refine ⟨fun m => if h : m ∈ S then (S.equivFin ⟨m, h⟩ : ℕ) + 1 else 1,
      fun m => by dsimp only; split_ifs <;> omega, ?_⟩
    intro m hm m' hm' h
    simp only [Finset.mem_coe] at hm hm'
    simp only [hm, hm', dif_pos, add_left_inj] at h
    have := S.equivFin.injective (Fin.ext h)
    simpa using this
  set Good : ℝ → Finset ι → Prop := fun t B =>
    ∃ a, RegularFan.Feas S u (fun m => h' m + t ^ kk m) a ∧
      ∀ m ∈ B, m ∈ S → inner ℝ a (u m) = h' m + t ^ kk m with hGood
  have hev_ray : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i ∈ S, Good t {i} := by
    rw [Filter.eventually_all_finset]
    intro i hi
    obtain ⟨x, -, hxi, hxo⟩ := hwit i hi
    refine RegularFan.eventually_wit_perturb hk (a0 := x - c0) ?_
      (RegularFan.hasDual_single ⟨u i, ?_⟩)
    · intro m hm
      have e : inner ℝ (x - c0) (u m) = inner ℝ (u m) x - inner ℝ (u m) c0 := by
        rw [inner_sub_left, real_inner_comm x, real_inner_comm c0]
      refine ⟨fun hmB => ?_, fun hmB => ?_⟩
      · rw [Finset.mem_singleton] at hmB; subst hmB
        rw [e, hxi]
      · rw [Finset.mem_singleton] at hmB
        rw [e]; simp only [hh']; linarith [hxo m hm hmB]
    · rw [real_inner_self_eq_norm_sq, hu i hi]; norm_num
  have hev_bad : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ B ∈ S.powerset,
      (¬ ∃ a, RegularFan.Feas S u h' a ∧ ∀ m ∈ B, inner ℝ a (u m) = h' m) →
      ¬ ∃ a, RegularFan.Feas S u (fun m => h' m + t ^ kk m) a ∧
        ∀ m ∈ B, inner ℝ a (u m) = h' m + t ^ kk m := by
    rw [Filter.eventually_all_finset]
    intro B _
    by_cases hbad : ∃ a, RegularFan.Feas S u h' a ∧ ∀ m ∈ B, inner ℝ a (u m) = h' m
    · exact Filter.Eventually.of_forall fun _ h => absurd hbad h
    · filter_upwards [eventually_not_active hspan hk hbad] with t ht _
      exact ht
  obtain ⟨t, ht, hgen, hr, hb⟩ := ((show ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t from self_mem_nhdsWithin).and
    ((RegularFan.eventually_generic (S := S) (v := u) (u := h') hk hkinj).and
      (hev_ray.and hev_bad))).exists
  have ht0 : (0 : ℝ) < t := ht
  set g : ι → ℝ := fun m => h' m + t ^ kk m with hg
  have hg0 : ∀ m ∈ S, 0 ≤ g m := fun m hm => by
    have := hh'pos m hm; have : 0 ≤ t ^ kk m := by positivity
    simp only [hg]; linarith
  refine ⟨c0, RegularFan.cones S u g, hc0, RegularFan.isSimplicialFan hgen hspan hg0, ?_, ?_⟩
  · intro i hi
    obtain ⟨τ, hτ, hiτ⟩ := RegularFan.exists_cone_of_active hgen hspan
      (Finset.singleton_subset_iff.2 hi) (hr i hi)
    exact ⟨τ, hτ, hiτ (Finset.mem_singleton_self i)⟩
  · intro τ hτ
    have hτ' := hτ
    simp only [RegularFan.cones, Finset.mem_filter] at hτ'
    obtain ⟨hτS, -, a, ha, hact⟩ := hτ'
    by_cases hgood : ∃ a, RegularFan.Feas S u h' a ∧ ∀ m ∈ τ, inner ℝ a (u m) = h' m
    · obtain ⟨b, hb1, hb2⟩ := hgood
      refine ⟨b + c0, fun m hm => ?_, fun m hm => ?_⟩
      · rw [hshift]; have := hb1 m hm; simp only [hh'] at this; linarith
      · rw [hshift, hb2 m hm]; simp only [hh']; ring
    · exfalso
      apply hb τ hτS hgood
      refine ⟨a, ha, fun m hm => ?_⟩
      rw [← hact] at hm
      exact (RegularFan.mem_act.1 hm).2

end Erdos99
end

end PolytopeFan

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `FacetLinksProof`
-/

section FacetLinksProof

/-!
# The triangulated facet links of a three-dimensional polytope

This file proves the bookkeeping of the facial structure of a bounded polytope
`polyK S u h ⊆ ℝ³` with unit normals all of whose facets are present
(`polytope_facetLinks_proof`, the statement of `polytope_facetLinks` in `FanTheorem`):

* a triangulation `T` of the normal fan refining the vertex cones (`polytope_refined_fan`,
  `PolytopeFan`) gives triangulated link data (`IsSimplicialFan.exists_links`,
  `FanLink`);
* the `m`-th edge of the facet polygon is the segment between the vertices of the two triangles
  of `T` on the edge `{i, nbr i m}`, and its length is given by the support numbers
  (`edge_half_right`, `edge_half_left`, `facet_inter_diam`);
* a facet outside the link of `i` meets `F_i` in at most one point (`facet_inter_subsingleton`);
* each facet polygon has positive area (`facet_area_pos`).
-/

open scoped BigOperators Real

@[expose] public noncomputable section

open Classical Real Finset

namespace Erdos99

variable {ι : Type*}

/-! ## Linear algebra -/

/-- A vector orthogonal to `a` and `e` is a multiple of `a × e`. -/
lemma perp_two_smul (a e d : Space3) (ha : inner ℝ a d = 0) (he : inner ℝ e d = 0) :
    ‖cross3 a e‖ ^ 2 • d = inner ℝ (cross3 a e) d • cross3 a e := by
  rw [norm_cross3_sq, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  rw [inner_eq_coords] at ha he
  ext k
  simp only [PiLp.smul_apply, smul_eq_mul, inner_eq_coords]
  fin_cases k
  · simp only [Fin.zero_eta, cross3_apply_zero, cross3_apply_one, cross3_apply_two]
    linear_combination ((e 0 * e 0 + e 1 * e 1 + e 2 * e 2) * a 0 -
      (a 0 * e 0 + a 1 * e 1 + a 2 * e 2) * e 0) * ha +
      ((a 0 * a 0 + a 1 * a 1 + a 2 * a 2) * e 0 - (a 0 * e 0 + a 1 * e 1 + a 2 * e 2) * a 0) * he
  · simp only [Fin.mk_one, cross3_apply_zero, cross3_apply_one, cross3_apply_two]
    linear_combination ((e 0 * e 0 + e 1 * e 1 + e 2 * e 2) * a 1 -
      (a 0 * e 0 + a 1 * e 1 + a 2 * e 2) * e 1) * ha +
      ((a 0 * a 0 + a 1 * a 1 + a 2 * a 2) * e 1 - (a 0 * e 0 + a 1 * e 1 + a 2 * e 2) * a 1) * he
  · simp only [Fin.reduceFinMk, cross3_apply_zero, cross3_apply_one, cross3_apply_two]
    linear_combination ((e 0 * e 0 + e 1 * e 1 + e 2 * e 2) * a 2 -
      (a 0 * e 0 + a 1 * e 1 + a 2 * e 2) * e 2) * ha +
      ((a 0 * a 0 + a 1 * a 1 + a 2 * a 2) * e 2 - (a 0 * e 0 + a 1 * e 1 + a 2 * e 2) * a 2) * he

/-- The Gram identity used for the edge lengths. -/
lemma gram_edge_identity {ui uj ub y : Space3} (hui : ‖ui‖ = 1) (huj : ‖uj‖ = 1) :
    (1 - inner ℝ ui uj ^ 2) * (inner ℝ ub y - inner ℝ ui ub * inner ℝ ui y) -
      (inner ℝ uj ub - inner ℝ ui uj * inner ℝ ui ub) * (inner ℝ uj y - inner ℝ ui uj * inner ℝ ui y) =
      vol3 ui uj ub * vol3 y ui uj := by
  have hA : inner ℝ ui ui = 1 := by rw [real_inner_self_eq_norm_sq, hui]; norm_num
  have hB : inner ℝ uj uj = 1 := by rw [real_inner_self_eq_norm_sq, huj]; norm_num
  rw [inner_eq_coords] at hA hB
  simp only [inner_eq_coords, vol3]
  linear_combination (-((uj 0 * uj 0 + uj 1 * uj 1 + uj 2 * uj 2) *
      (ub 0 * y 0 + ub 1 * y 1 + ub 2 * y 2) -
      (uj 0 * y 0 + uj 1 * y 1 + uj 2 * y 2) * (ub 0 * uj 0 + ub 1 * uj 1 + ub 2 * uj 2))) * hA +
    (-((ub 0 * y 0 + ub 1 * y 1 + ub 2 * y 2) -
      (ui 0 * y 0 + ui 1 * y 1 + ui 2 * y 2) * (ub 0 * ui 0 + ub 1 * ui 1 + ub 2 * ui 2))) * hB

/-- The half of an edge after its normal `uj`, towards the next normal `ub` (gap `θ`). -/
lemma edge_half_right {ui uj ub y : Space3} (hui : ‖ui‖ = 1) (huj : ‖uj‖ = 1) {θ : ℝ}
    (hs : Real.sin θ ≠ 0) (hnd : inner ℝ ui uj ^ 2 < 1) (hnd' : inner ℝ ui ub ^ 2 < 1)
    (hsin : Real.sin θ * (√(1 - inner ℝ ui uj ^ 2) * √(1 - inner ℝ ui ub ^ 2)) = vol3 ui uj ub)
    (hcos : Real.cos θ * (√(1 - inner ℝ ui uj ^ 2) * √(1 - inner ℝ ui ub ^ 2)) =
      inner ℝ uj ub - inner ℝ ui uj * inner ℝ ui ub) :
    ((inner ℝ ub y - inner ℝ ui ub * inner ℝ ui y) / √(1 - inner ℝ ui ub ^ 2) -
      (inner ℝ uj y - inner ℝ ui uj * inner ℝ ui y) / √(1 - inner ℝ ui uj ^ 2) * Real.cos θ) /
        Real.sin θ = vol3 y ui uj / √(1 - inner ℝ ui uj ^ 2) := by
  set sj := √(1 - inner ℝ ui uj ^ 2) with hsj_def
  set sb := √(1 - inner ℝ ui ub ^ 2) with hsb_def
  have hsj : 0 < sj := Real.sqrt_pos.2 (by linarith)
  have hsb : 0 < sb := Real.sqrt_pos.2 (by linarith)
  have hsj2 : sj ^ 2 = 1 - inner ℝ ui uj ^ 2 := Real.sq_sqrt (by linarith)
  have hV : vol3 ui uj ub ≠ 0 := by
    rw [← hsin]; exact mul_ne_zero hs (mul_ne_zero hsj.ne' hsb.ne')
  have hsθ : Real.sin θ = vol3 ui uj ub / (sj * sb) := by
    rw [eq_div_iff (mul_ne_zero hsj.ne' hsb.ne')]; exact hsin
  have hcθ : Real.cos θ = (inner ℝ uj ub - inner ℝ ui uj * inner ℝ ui ub) / (sj * sb) := by
    rw [eq_div_iff (mul_ne_zero hsj.ne' hsb.ne')]; exact hcos
  have key := gram_edge_identity (ub := ub) (y := y) hui huj
  rw [← hsj2] at key
  rw [hsθ, hcθ]
  field_simp
  linear_combination key

/-- The half of an edge before its normal `uj`, from the previous normal `ua` (gap `θ`). -/
lemma edge_half_left {ui uj ua y : Space3} (hui : ‖ui‖ = 1) (huj : ‖uj‖ = 1) {θ : ℝ}
    (hs : Real.sin θ ≠ 0) (hnd : inner ℝ ui uj ^ 2 < 1) (hnd' : inner ℝ ui ua ^ 2 < 1)
    (hsin : Real.sin θ * (√(1 - inner ℝ ui ua ^ 2) * √(1 - inner ℝ ui uj ^ 2)) = vol3 ui ua uj)
    (hcos : Real.cos θ * (√(1 - inner ℝ ui ua ^ 2) * √(1 - inner ℝ ui uj ^ 2)) =
      inner ℝ ua uj - inner ℝ ui ua * inner ℝ ui uj) :
    ((inner ℝ ua y - inner ℝ ui ua * inner ℝ ui y) / √(1 - inner ℝ ui ua ^ 2) -
      (inner ℝ uj y - inner ℝ ui uj * inner ℝ ui y) / √(1 - inner ℝ ui uj ^ 2) * Real.cos θ) /
        Real.sin θ = -vol3 y ui uj / √(1 - inner ℝ ui uj ^ 2) := by
  set sj := √(1 - inner ℝ ui uj ^ 2) with hsj_def
  set sa := √(1 - inner ℝ ui ua ^ 2) with hsa_def
  have hsj : 0 < sj := Real.sqrt_pos.2 (by linarith)
  have hsa : 0 < sa := Real.sqrt_pos.2 (by linarith)
  have hsj2 : sj ^ 2 = 1 - inner ℝ ui uj ^ 2 := Real.sq_sqrt (by linarith)
  have hV : vol3 ui ua uj ≠ 0 := by
    rw [← hsin]; exact mul_ne_zero hs (mul_ne_zero hsa.ne' hsj.ne')
  have hsθ : Real.sin θ = vol3 ui ua uj / (sa * sj) := by
    rw [eq_div_iff (mul_ne_zero hsa.ne' hsj.ne')]; exact hsin
  have hcθ : Real.cos θ = (inner ℝ ua uj - inner ℝ ui ua * inner ℝ ui uj) / (sa * sj) := by
    rw [eq_div_iff (mul_ne_zero hsa.ne' hsj.ne')]; exact hcos
  have key := gram_edge_identity (ub := ua) (y := y) hui huj
  rw [← hsj2, real_inner_comm ua uj] at key
  have hswap : vol3 ui uj ua = -vol3 ui ua uj := by unfold vol3; ring
  rw [hswap] at key
  rw [hsθ, hcθ]
  field_simp
  linear_combination key

/-- **The common edge of two adjacent facets.**  If the vertices `xm` (on the facets `i, a, j`)
and `xp` (on the facets `i, j, b`) are the ends of the edge `F_i ∩ F_j`, with
`(u i, u a, u j)` and `(u i, u j, u b)` positively oriented, then `F_i ∩ F_j` is the segment
`[xm, xp]`, which points in the direction of `u i × u j`. -/
lemma facet_inter_diam {S : Finset ι} {u : ι → Space3} {h : ι → ℝ} (hu : ∀ i ∈ S, ‖u i‖ = 1)
    {i j a b : ι} (hi : i ∈ S) (hj : j ∈ S) (ha : a ∈ S) (hb : b ∈ S)
    (hnd : inner ℝ (u i) (u j) ^ 2 < 1) {xm xp : Space3}
    (hxm : xm ∈ polyK S u h) (hxmi : inner ℝ (u i) xm = h i) (hxmj : inner ℝ (u j) xm = h j)
    (hxma : inner ℝ (u a) xm = h a)
    (hxp : xp ∈ polyK S u h) (hxpi : inner ℝ (u i) xp = h i) (hxpj : inner ℝ (u j) xp = h j)
    (hxpb : inner ℝ (u b) xp = h b)
    (hva : 0 < vol3 (u i) (u a) (u j)) (hvb : 0 < vol3 (u i) (u j) (u b)) :
    Metric.diam (polyFacet S u h i ∩ polyFacet S u h j) =
        vol3 (xp - xm) (u i) (u j) / √(1 - inner ℝ (u i) (u j) ^ 2) ∧
      0 ≤ vol3 (xp - xm) (u i) (u j) ∧
      xp - xm = (vol3 (xp - xm) (u i) (u j) / (1 - inner ℝ (u i) (u j) ^ 2)) •
        cross3 (u i) (u j) := by
  set A := cross3 (u i) (u j) with hA_def
  set s2 := 1 - inner ℝ (u i) (u j) ^ 2 with hs2_def
  have hs2pos : 0 < s2 := by linarith
  have hA2 : ‖A‖ ^ 2 = s2 := by rw [hA_def, norm_cross3_sq, hu i hi, hu j hj]; ring
  have hperp : ∀ d, inner ℝ (u i) d = 0 → inner ℝ (u j) d = 0 → d = (inner ℝ A d / s2) • A := by
    intro d h1 h2
    have := perp_two_smul (u i) (u j) d h1 h2
    rw [← hA_def, hA2] at this
    rw [div_eq_inv_mul, mul_smul, ← this, smul_smul, inv_mul_cancel₀ hs2pos.ne', one_smul]
  have hvolA : ∀ x, vol3 x (u i) (u j) = inner ℝ A x := by
    intro x; rw [hA_def, inner_cross3]; exact (vol3_cyc x (u i) (u j)).symm
  have hAb : inner ℝ (u b) A = vol3 (u i) (u j) (u b) := by
    rw [real_inner_comm, hA_def, inner_cross3]
  have hAa : inner ℝ (u a) A = -vol3 (u i) (u a) (u j) := by
    rw [real_inner_comm, hA_def, inner_cross3]; unfold vol3; ring
  set W := vol3 (xp - xm) (u i) (u j) with hW_def
  have hd0 : xp - xm = (W / s2) • A := by
    rw [hW_def, hvolA]
    exact hperp _ (by rw [inner_sub_right, hxpi, hxmi, sub_self])
      (by rw [inner_sub_right, hxpj, hxmj, sub_self])
  have hWnn : 0 ≤ W := by
    have h1 : 0 ≤ inner ℝ (u b) (xp - xm) := by
      rw [inner_sub_right, hxpb]; linarith [hxm b hb]
    rw [hd0, inner_smul_right, hAb] at h1
    have := nonneg_of_mul_nonneg_left h1 hvb
    exact (div_nonneg_iff.1 this).elim (fun h => h.1) (fun h => by linarith [h.2])
  have hseg : polyFacet S u h i ∩ polyFacet S u h j = segment ℝ xm xp := by
    rw [segment_eq_image']
    ext y
    constructor
    · rintro ⟨⟨hyK, hyi⟩, ⟨-, hyj⟩⟩
      set μ := inner ℝ A (y - xm) / s2 with hμ
      have hy : y - xm = μ • A := hperp _ (by rw [inner_sub_right, hyi, hxmi, sub_self])
        (by rw [inner_sub_right, hyj, hxmj, sub_self])
      have hμ0 : 0 ≤ μ := by
        have h1 : inner ℝ (u a) (y - xm) ≤ 0 := by
          rw [inner_sub_right, hxma]; linarith [hyK a ha]
        rw [hy, inner_smul_right, hAa] at h1
        nlinarith
      have hμ1 : μ ≤ W / s2 := by
        have h1 : inner ℝ (u b) (y - xp) ≤ 0 := by
          rw [inner_sub_right, hxpb]; linarith [hyK b hb]
        have : y - xp = (μ - W / s2) • A := by
          rw [sub_smul, ← hy, ← hd0]; abel
        rw [this, inner_smul_right, hAb] at h1
        nlinarith
      by_cases hW0 : W = 0
      · refine ⟨0, ⟨le_refl _, zero_le_one⟩, ?_⟩
        have : μ = 0 := by rw [hW0, zero_div] at hμ1; linarith
        rw [this, zero_smul, sub_eq_zero] at hy
        simp [hy]
      · have hWpos : 0 < W / s2 := div_pos (lt_of_le_of_ne hWnn (Ne.symm hW0)) hs2pos
        refine ⟨μ / (W / s2), ⟨div_nonneg hμ0 hWpos.le, (div_le_one hWpos).2 hμ1⟩, ?_⟩
        simp only
        rw [hd0, smul_smul, div_mul_cancel₀ _ hWpos.ne', ← hy]
        abel
    · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
      have hlin : ∀ k, inner ℝ (u k) (xm + t • (xp - xm)) =
          (1 - t) * inner ℝ (u k) xm + t * inner ℝ (u k) xp := by
        intro k; rw [inner_add_right, inner_smul_right, inner_sub_right]; ring
      have hK : xm + t • (xp - xm) ∈ polyK S u h := by
        intro k hk
        rw [hlin]
        have := hxm k hk; have := hxp k hk
        nlinarith
      refine ⟨⟨hK, ?_⟩, ⟨hK, ?_⟩⟩
      · rw [hlin, hxmi, hxpi]; ring
      · rw [hlin, hxmj, hxpj]; ring
  refine ⟨?_, hWnn, hd0⟩
  rw [hseg, ← convexHull_pair, convexHull_diam, Metric.diam_pair, dist_comm, dist_eq_norm, hd0,
    norm_smul, Real.norm_of_nonneg (div_nonneg hWnn hs2pos.le)]
  have hAn : ‖A‖ = √s2 := by rw [← hA2, Real.sqrt_sq (norm_nonneg _)]
  rw [hAn]
  have hsq : √s2 ^ 2 = s2 := Real.sq_sqrt hs2pos.le
  have hsqpos : 0 < √s2 := Real.sqrt_pos.2 hs2pos
  rw [eq_div_iff hsqpos.ne', mul_assoc, ← sq, hsq, div_mul_cancel₀ _ hs2pos.ne']

/-- A facet normal which is a nonnegative combination of two other normals, all three facets
passing through a common point, contradicts the presence of the facet. -/
lemma not_present_comb {S : Finset ι} {u : ι → Space3} {h : ι → ℝ}
    (hfac : FacetsPresent S u h) (hu : ∀ i ∈ S, ‖u i‖ = 1) {k a b : ι} (hk : k ∈ S)
    (ha : a ∈ S) (hb : b ∈ S) (hka : k ≠ a) (hkb : k ≠ b) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hcomb : u k = α • u a + β • u b) {y : Space3} (hyk : inner ℝ (u k) y = h k)
    (hya : inner ℝ (u a) y = h a) (hyb : inner ℝ (u b) y = h b) : False := by
  obtain ⟨x, hxk, hxo⟩ := hfac k hk
  have hxa := hxo a ha (Ne.symm hka)
  have hxb := hxo b hb (Ne.symm hkb)
  have e1 : inner ℝ (u k) x = α * inner ℝ (u a) x + β * inner ℝ (u b) x := by
    rw [hcomb, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have e2 : h k = α * h a + β * h b := by
    rw [← hyk, ← hya, ← hyb, hcomb, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have hne : α ≠ 0 ∨ β ≠ 0 := by
    by_contra hc
    push_neg at hc
    have := hu k hk
    rw [hcomb, hc.1, hc.2, zero_smul, zero_smul, add_zero, norm_zero] at this
    exact zero_ne_one this
  rcases hne with h1 | h1
  · have : 0 < α := lt_of_le_of_ne hα (Ne.symm h1)
    nlinarith
  · have : 0 < β := lt_of_le_of_ne hβ (Ne.symm h1)
    nlinarith

/-- **Facets outside the link.**  If `u j` lies in the sector `γ u i + α u a + β u b`
(`α, β ≥ 0`) of a cone `{i, a, b}` of the triangulated normal fan with vertex `x`, and `j` is
none of `i, a, b`, then `F_i ∩ F_j` has at most one point. -/
lemma facet_inter_subsingleton {S : Finset ι} {u : ι → Space3} {h : ι → ℝ}
    (hu : ∀ i ∈ S, ‖u i‖ = 1) (hfac : FacetsPresent S u h) {i j a b : ι} (hi : i ∈ S)
    (hj : j ∈ S) (ha : a ∈ S) (hb : b ∈ S) (hji : j ≠ i) (hja : j ≠ a) (hjb : j ≠ b)
    (hai : a ≠ i) (hbi : b ≠ i) (hV : vol3 (u i) (u a) (u b) ≠ 0) {x : Space3}
    (hx : x ∈ polyK S u h) (hxi : inner ℝ (u i) x = h i) (hxa : inner ℝ (u a) x = h a)
    (hxb : inner ℝ (u b) x = h b) {γ α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hcomb : u j = γ • u i + α • u a + β • u b) :
    (polyFacet S u h i ∩ polyFacet S u h j).Subsingleton := by
  have hlin : ∀ y, inner ℝ (u j) y =
      γ * inner ℝ (u i) y + α * inner ℝ (u a) y + β * inner ℝ (u b) y := by
    intro y
    rw [hcomb, inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_smul_left]
  have key : ∀ y ∈ polyFacet S u h i ∩ polyFacet S u h j,
      α * (h a - inner ℝ (u a) y) = 0 ∧ β * (h b - inner ℝ (u b) y) = 0 := by
    rintro y ⟨⟨hyK, hyi⟩, ⟨-, hyj⟩⟩
    have h1 := hlin y
    have h2 := hlin x
    have h3 := hx j hj
    have h4 : 0 ≤ α * (h a - inner ℝ (u a) y) := mul_nonneg hα (by linarith [hyK a ha])
    have h5 : 0 ≤ β * (h b - inner ℝ (u b) y) := mul_nonneg hβ (by linarith [hyK b hb])
    rw [hyj, hyi] at h1
    rw [hxi, hxa, hxb] at h2
    constructor <;> nlinarith
  rintro y1 hy1 y2 hy2
  obtain ⟨⟨hy1K, hy1i⟩, ⟨-, hy1j⟩⟩ := hy1
  obtain ⟨⟨hy2K, hy2i⟩, ⟨-, hy2j⟩⟩ := hy2
  have k1 := key y1 ⟨⟨hy1K, hy1i⟩, ⟨hy1K, hy1j⟩⟩
  have k2 := key y2 ⟨⟨hy2K, hy2i⟩, ⟨hy2K, hy2j⟩⟩
  by_cases hα0 : α = 0 <;> by_cases hβ0 : β = 0
  · -- `u j` is a multiple of `u i`
    exfalso
    rw [hα0, hβ0, zero_smul, zero_smul, add_zero, add_zero] at hcomb
    by_cases hγ : 0 ≤ γ
    · exact not_present_comb hfac hu hj hi hi hji hji hγ (le_refl 0)
        (by rw [hcomb, zero_smul, add_zero]) hy1j hy1i hy1i
    · push_neg at hγ
      obtain ⟨w, hwi, hwo⟩ := hfac i hi
      have hw := hwo j hj hji
      rw [hcomb, real_inner_smul_left, hwi] at hw
      rw [hcomb, real_inner_smul_left, hy1i] at hy1j
      linarith
  · -- `u j` is a combination of `u i` and `u b`
    exfalso
    have hβp : 0 < β := lt_of_le_of_ne hβ (Ne.symm hβ0)
    have hy1b : inner ℝ (u b) y1 = h b := by
      have := k1.2
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hβ0
      · linarith
    rw [hα0, zero_smul, add_zero] at hcomb
    by_cases hγ : 0 ≤ γ
    · exact not_present_comb hfac hu hj hi hb hji hjb hγ hβ hcomb hy1j hy1i hy1b
    · push_neg at hγ
      refine not_present_comb hfac hu hb hj hi (Ne.symm hjb) hbi (α := 1 / β) (β := -γ / β)
        (by positivity) (div_nonneg (by linarith) hβ) ?_ hy1b hy1j hy1i
      rw [hcomb, smul_add, smul_smul, smul_smul, one_div, inv_mul_cancel₀ hβ0, one_smul,
        add_comm, ← add_assoc, ← add_smul]
      have : -γ / β + β⁻¹ * γ = 0 := by field_simp; ring
      rw [this, zero_smul, zero_add]
  · -- `u j` is a combination of `u i` and `u a`
    exfalso
    have hαp : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
    have hy1a : inner ℝ (u a) y1 = h a := by
      have := k1.1
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hα0
      · linarith
    rw [hβ0, zero_smul, add_zero] at hcomb
    by_cases hγ : 0 ≤ γ
    · exact not_present_comb hfac hu hj hi ha hji hja hγ hα hcomb hy1j hy1i hy1a
    · push_neg at hγ
      refine not_present_comb hfac hu ha hj hi (Ne.symm hja) hai (α := 1 / α) (β := -γ / α)
        (by positivity) (div_nonneg (by linarith) hα) ?_ hy1a hy1j hy1i
      rw [hcomb, smul_add, smul_smul, smul_smul, one_div, inv_mul_cancel₀ hα0, one_smul,
        add_comm, ← add_assoc, ← add_smul]
      have : -γ / α + α⁻¹ * γ = 0 := by field_simp; ring
      rw [this, zero_smul, zero_add]
  · -- both points lie on the three independent facets `i, a, b`
    have ha1 : inner ℝ (u a) y1 = h a := by
      rcases mul_eq_zero.1 k1.1 with h | h
      · exact absurd h hα0
      · linarith
    have ha2 : inner ℝ (u a) y2 = h a := by
      rcases mul_eq_zero.1 k2.1 with h | h
      · exact absurd h hα0
      · linarith
    have hb1 : inner ℝ (u b) y1 = h b := by
      rcases mul_eq_zero.1 k1.2 with h | h
      · exact absurd h hβ0
      · linarith
    have hb2 : inner ℝ (u b) y2 = h b := by
      rcases mul_eq_zero.1 k2.2 with h | h
      · exact absurd h hβ0
      · linarith
    set d := y2 - y1 with hd
    have hdi : inner ℝ (u i) d = 0 := by rw [hd, inner_sub_right, hy1i, hy2i, sub_self]
    have hda : inner ℝ (u a) d = 0 := by rw [hd, inner_sub_right, ha1, ha2, sub_self]
    have hdb : inner ℝ (u b) d = 0 := by rw [hd, inner_sub_right, hb1, hb2, sub_self]
    have hp := perp_two_smul (u i) (u a) d hdi hda
    have hAb : inner ℝ (u b) (cross3 (u i) (u a)) = vol3 (u i) (u a) (u b) := by
      rw [real_inner_comm, inner_cross3]
    have h1 := congrArg (fun v => inner ℝ (u b) v) hp
    simp only [inner_smul_right, hdb, mul_zero, hAb] at h1
    have h2 : inner ℝ (cross3 (u i) (u a)) d = 0 := by
      rcases mul_eq_zero.1 h1.symm with h | h
      · exact h
      · exact absurd h hV
    rw [h2, zero_smul] at hp
    have hA : cross3 (u i) (u a) ≠ 0 := by
      intro h0; rw [h0, inner_zero_right] at hAb; exact hV hAb.symm
    have hA2 : ‖cross3 (u i) (u a)‖ ^ 2 ≠ 0 := by positivity
    have := (smul_eq_zero.1 hp).resolve_left hA2
    rw [hd, sub_eq_zero] at this
    exact this.symm

lemma inner_cross3_cross3 (a b v : Space3) :
    inner ℝ (cross3 a b) (cross3 a v) =
      inner ℝ a a * inner ℝ b v - inner ℝ a v * inner ℝ a b := by
  simp only [inner_eq_coords, cross3_apply_zero, cross3_apply_one, cross3_apply_two]; ring

lemma mod_pred_succ {k m : ℕ} (hm : m < k) : ((m + 1) % k + k - 1) % k = m := by
  rcases Nat.lt_or_ge (m + 1) k with h | h
  · rw [Nat.mod_eq_of_lt h, show m + 1 + k - 1 = m + k by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hm]
  · have : m + 1 = k := by omega
    rw [this, Nat.mod_self, show 0 + k - 1 = m by omega, Nat.mod_eq_of_lt hm]

lemma succ_mod_pred {k m : ℕ} (hm : m < k) : ((m + k - 1) % k + 1) % k = m := by
  have hk : 0 < k := by omega
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    rw [show 0 + k - 1 = k - 1 by omega, Nat.mod_eq_of_lt (show k - 1 < k by omega),
      Nat.sub_add_cancel hk, Nat.mod_self]
  · rw [show m + k - 1 = (m - 1) + k by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega : m - 1 < k), Nat.sub_add_cancel hpos, Nat.mod_eq_of_lt hm]

lemma sum_range_pred_mod (k : ℕ) (G : ℕ → ℝ) :
    ∑ m ∈ range k, G ((m + k - 1) % k) = ∑ m ∈ range k, G m := by
  rw [← sum_range_succ_mod k (fun m => G ((m + k - 1) % k))]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [mod_pred_succ (Finset.mem_range.1 hm)]

lemma polyForm_eq_polyBilin (k : ℕ) (θ p : ℕ → ℝ) : polyForm k θ p = polyBilin k θ p p := by
  unfold polyForm polyBilin
  refine Finset.sum_congr rfl fun m _ => ?_
  unfold edgeForm edgeBilin
  ring

/-- **Positive area of a facet.**  With the vertices `x m` of the triangles
`(i, nbr i m, nbr i (m + 1))` and the edges `x m - x (m - 1)` pointing along
`u i × u (nbr i m)` with the lengths of the polygon edges, the facet polygon has positive area. -/
lemma facet_area_pos {S : Finset ι} {u : ι → Space3} {h : ι → ℝ} (hu : ∀ i ∈ S, ‖u i‖ = 1)
    (hfac : FacetsPresent S u h) {i : ι} (hi : i ∈ S) (c0 : Space3) {k : ℕ}
    {nbr : ι → ℕ → ι} {θ : ℕ → ℝ} (hk : 0 < k) (x : ℕ → Space3)
    (hxi : ∀ m < k, inner ℝ (u i) (x m) = h i)
    (hxj : ∀ m < k, inner ℝ (u (nbr i m)) (x m) = h (nbr i m))
    (hxb : ∀ m < k, inner ℝ (u (nbr i ((m + 1) % k))) (x m) = h (nbr i ((m + 1) % k)))
    (hmem : ∀ m < k, nbr i m ∈ S.erase i)
    (hnd : ∀ m < k, inner ℝ (u i) (u (nbr i m)) ^ 2 < 1)
    (hlen : ∀ m < k, edgeLen k θ (linkSupport u nbr i (fun l => h l - inner ℝ (u l) c0)) m =
      vol3 (x m - x ((m + k - 1) % k)) (u i) (u (nbr i m)) /
        √(1 - inner ℝ (u i) (u (nbr i m)) ^ 2))
    (hW : ∀ m < k, 0 ≤ vol3 (x m - x ((m + k - 1) % k)) (u i) (u (nbr i m)))
    (hdir : ∀ m < k, x m - x ((m + k - 1) % k) =
      (vol3 (x m - x ((m + k - 1) % k)) (u i) (u (nbr i m)) /
        (1 - inner ℝ (u i) (u (nbr i m)) ^ 2)) • cross3 (u i) (u (nbr i m)))
    (hsec : ∀ d : Space3, ∃ m < k, ∃ γ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧
      d = γ • u i + α • u (nbr i m) + β • u (nbr i ((m + 1) % k))) :
    0 < polyForm k θ (linkSupport u nbr i (fun l => h l - inner ℝ (u l) c0)) := by
  set h' : ι → ℝ := fun l => h l - inner ℝ (u l) c0 with hh'
  set p := linkSupport u nbr i h' with hp
  have haa : inner ℝ (u i) (u i) = 1 := by rw [real_inner_self_eq_norm_sq, hu i hi]; norm_num
  obtain ⟨w, hwi, hwo⟩ := hfac i hi
  set v := w - c0 with hv
  set z := cross3 (u i) v with hz
  set c : ℕ → ℝ := fun m => inner ℝ (u i) (u (nbr i m)) with hc
  set W : ℕ → ℝ := fun m => vol3 (x m - x ((m + k - 1) % k)) (u i) (u (nbr i m)) with hWdef
  set lam : ℕ → ℝ := fun m => W m / (1 - c m ^ 2) with hlam
  have hs2 : ∀ m < k, 0 < 1 - c m ^ 2 := fun m hm => by simp only [hc]; linarith [hnd m hm]
  have hjS : ∀ m < k, nbr i m ∈ S := fun m hm => (Finset.mem_erase.1 (hmem m hm)).2
  have hji : ∀ m < k, nbr i m ≠ i := fun m hm => (Finset.mem_erase.1 (hmem m hm)).1
  have hgap : ∀ m < k, 0 < h (nbr i m) - inner ℝ (u (nbr i m)) w := fun m hm => by
    have := hwo (nbr i m) (hjS m hm) (hji m hm); linarith
  -- each term of the polar form
  have hterm : ∀ m < k, edgeLen k θ p m * p m =
      lam m * (h (nbr i m) - inner ℝ (u (nbr i m)) w) +
        inner ℝ (x m - x ((m + k - 1) % k)) z := by
    intro m hm
    have hsq : √(1 - c m ^ 2) ^ 2 = 1 - c m ^ 2 := Real.sq_sqrt (hs2 m hm).le
    have hspos : 0 < √(1 - c m ^ 2) := Real.sqrt_pos.2 (hs2 m hm)
    have hz' : inner ℝ (x m - x ((m + k - 1) % k)) z =
        lam m * (inner ℝ (u (nbr i m)) v - c m * inner ℝ (u i) v) := by
      rw [hdir m hm, real_inner_smul_left, hz, inner_cross3_cross3, haa]
      simp only [hlam, hWdef, hc]
      ring
    rw [hlen m hm, hz']
    have e2 : lam m * (h (nbr i m) - inner ℝ (u (nbr i m)) w) +
        lam m * (inner ℝ (u (nbr i m)) v - c m * inner ℝ (u i) v) =
        lam m * (h' (nbr i m) - c m * h' i) := by
      simp only [hh', hv, inner_sub_right, hwi]; ring
    rw [e2]
    show W m / √(1 - c m ^ 2) * ((h' (nbr i m) - c m * h' i) / √(1 - c m ^ 2)) =
      lam m * (h' (nbr i m) - c m * h' i)
    rw [div_mul_div_comm, ← sq, hsq]
    simp only [hlam]
    ring
  have hsumz : ∑ m ∈ range k, inner ℝ (x m - x ((m + k - 1) % k)) z = 0 := by
    simp only [inner_sub_left, Finset.sum_sub_distrib]
    rw [sum_range_pred_mod k (fun m => inner ℝ (x m) z), sub_self]
  have hpf : polyForm k θ p =
      ∑ m ∈ range k, lam m * (h (nbr i m) - inner ℝ (u (nbr i m)) w) := by
    rw [polyForm_eq_polyBilin, polyBilin_eq_sum_edgeLen,
      Finset.sum_congr rfl fun m hm => hterm m (Finset.mem_range.1 hm), Finset.sum_add_distrib,
      hsumz, add_zero]
  have hlam0 : ∀ m < k, 0 ≤ lam m := fun m hm => div_nonneg (hW m hm) (hs2 m hm).le
  rw [hpf]
  by_contra hcon
  push_neg at hcon
  have hzero : ∀ m < k, lam m = 0 := by
    intro m hm
    have hle := Finset.sum_eq_zero_iff_of_nonneg
      (s := range k) (f := fun m => lam m * (h (nbr i m) - inner ℝ (u (nbr i m)) w))
      (fun m hm => mul_nonneg (hlam0 m (Finset.mem_range.1 hm)) (hgap m (Finset.mem_range.1 hm)).le)
    have hsum0 : ∑ m ∈ range k, lam m * (h (nbr i m) - inner ℝ (u (nbr i m)) w) = 0 :=
      le_antisymm hcon (Finset.sum_nonneg fun m hm =>
        mul_nonneg (hlam0 m (Finset.mem_range.1 hm)) (hgap m (Finset.mem_range.1 hm)).le)
    have := hle.1 hsum0 m (Finset.mem_range.2 hm)
    rcases mul_eq_zero.1 this with h1 | h1
    · exact h1
    · exact absurd h1 (hgap m hm).ne'
  have hstep : ∀ m < k, x m = x ((m + k - 1) % k) := by
    intro m hm
    have := hdir m hm
    have h0 : W m / (1 - c m ^ 2) = 0 := hzero m hm
    simp only [hWdef, hc] at h0
    rw [h0, zero_smul, sub_eq_zero] at this
    exact this
  have hall : ∀ m < k, x m = x 0 := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      rw [hstep (n + 1) hn, show n + 1 + k - 1 = n + k by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega : n < k)]
      exact ih (by omega)
  obtain ⟨m, hm, γ, α, β, hα, hβ, hd⟩ := hsec (w - x 0)
  have hm1 : (m + 1) % k < k := Nat.mod_lt _ hk
  have hda : inner ℝ (u (nbr i m)) (w - x 0) < 0 := by
    rw [inner_sub_right, ← hall m hm, hxj m hm]; linarith [hgap m hm]
  have hdb : inner ℝ (u (nbr i ((m + 1) % k))) (w - x 0) < 0 := by
    rw [inner_sub_right, ← hall m hm, hxb m hm]; linarith [hgap _ hm1]
  have hdi : inner ℝ (u i) (w - x 0) = 0 := by
    rw [inner_sub_right, hwi, hxi 0 hk, sub_self]
  have hnorm : ‖w - x 0‖ ^ 2 = α * inner ℝ (u (nbr i m)) (w - x 0) +
      β * inner ℝ (u (nbr i ((m + 1) % k))) (w - x 0) := by
    rw [← real_inner_self_eq_norm_sq]
    conv_lhs => arg 2; rw [hd]
    rw [inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_smul_left, hdi]
    ring
  have h1 : ‖w - x 0‖ ^ 2 ≤ 0 := by
    rw [hnorm]
    have := mul_nonpos_of_nonneg_of_nonpos hα hda.le
    have := mul_nonpos_of_nonneg_of_nonpos hβ hdb.le
    linarith
  have h2 : w - x 0 = 0 := by
    have := sq_nonneg ‖w - x 0‖
    exact norm_eq_zero.1 (by nlinarith)
  rw [h2, inner_zero_right] at hda
  exact lt_irrefl _ hda

lemma vol3_sub_left (a b c d : Space3) : vol3 (a - b) c d = vol3 a c d - vol3 b c d := by
  simp only [vol3, PiLp.sub_apply]; ring

/-- **The triangulated facet links of a polytope** (the statement of `polytope_facetLinks`). -/
theorem polytope_facetLinks_proof {S : Finset ι} {u : ι → Space3} {h : ι → ℝ}
    (hu : ∀ i ∈ S, ‖u i‖ = 1) (hbdd : Bornology.IsBounded (polyK S u h))
    (hfac : FacetsPresent S u h) :
    ∃ h' : ι → ℝ, (∀ i ∈ S, 0 < h' i) ∧
      ∃ (k : ι → ℕ) (nbr : ι → ℕ → ι) (θ : ι → ℕ → ℝ) (T : Finset (ι × ι × ι)),
        (∀ i ∈ S, ValidGaps (k i) (θ i)) ∧ LinkData S u k nbr θ T ∧
        (∀ i ∈ S, ∀ m < k i, nbr i m ∈ S.erase i) ∧
        (∀ i ∈ S, ∀ m < k i, ∀ m' < k i, nbr i m = nbr i m' → m = m') ∧
        (∀ i ∈ S, ∀ m < k i, edgeLen (k i) (θ i) (linkSupport u nbr i h') m =
          Metric.diam (polyFacet S u h i ∩ polyFacet S u h (nbr i m))) ∧
        (∀ i ∈ S, ∀ j ∈ S.erase i, (∀ m < k i, nbr i m ≠ j) →
          Metric.diam (polyFacet S u h i ∩ polyFacet S u h j) = 0) ∧
        (∀ i ∈ S, 0 < polyForm (k i) (θ i) (linkSupport u nbr i h')) := by
  obtain ⟨c0, T, hc0, hfan, hused, hvert⟩ := polytope_refined_fan hu hbdd hfac
  choose! vx hvxK hvx using hvert
  obtain ⟨k, nbr, θ, T', hval, hL, hmem, hinj, hcone, hpos, hsec⟩ := hfan.exists_links hu hused
  set h' : ι → ℝ := fun l => h l - inner ℝ (u l) c0 with hh'
  set X : ι → ℕ → Space3 := fun i m => vx {i, nbr i m, nbr i ((m + 1) % k i)} with hX
  have hkpos : ∀ i ∈ S, 0 < k i := fun i hi => by have := (hval i hi).three_le; omega
  have hm1 : ∀ i ∈ S, ∀ m < k i, (m + 1) % k i < k i := fun i hi m _ =>
    Nat.mod_lt _ (hkpos i hi)
  have hXK : ∀ i ∈ S, ∀ m < k i, X i m ∈ polyK S u h := fun i hi m hm =>
    hvxK _ (hcone i hi m hm)
  have hXi : ∀ i ∈ S, ∀ m < k i, inner ℝ (u i) (X i m) = h i := fun i hi m hm =>
    hvx _ (hcone i hi m hm) i (by simp)
  have hXj : ∀ i ∈ S, ∀ m < k i, inner ℝ (u (nbr i m)) (X i m) = h (nbr i m) := fun i hi m hm =>
    hvx _ (hcone i hi m hm) _ (by simp)
  have hXb : ∀ i ∈ S, ∀ m < k i, inner ℝ (u (nbr i ((m + 1) % k i))) (X i m) =
      h (nbr i ((m + 1) % k i)) := fun i hi m hm => hvx _ (hcone i hi m hm) _ (by simp)
  have hnS : ∀ i ∈ S, ∀ m < k i, nbr i m ∈ S := fun i hi m hm =>
    (Finset.mem_erase.1 (hmem i hi m hm)).2
  -- the link support numbers in terms of a vertex
  have hlink : ∀ i ∈ S, ∀ l (y : Space3), inner ℝ (u i) y = h i → inner ℝ (u (nbr i l)) y =
      h (nbr i l) → linkSupport u nbr i h' l =
        (inner ℝ (u (nbr i l)) (y - c0) - inner ℝ (u i) (u (nbr i l)) * inner ℝ (u i) (y - c0)) /
          √(1 - inner ℝ (u i) (u (nbr i l)) ^ 2) := by
    intro i hi l y hyi hyl
    simp only [linkSupport, hh', inner_sub_right, hyi, hyl]
  -- the edges
  have hE : ∀ i ∈ S, ∀ m < k i,
      edgeLen (k i) (θ i) (linkSupport u nbr i h') m =
        vol3 (X i m - X i ((m + k i - 1) % k i)) (u i) (u (nbr i m)) /
          √(1 - inner ℝ (u i) (u (nbr i m)) ^ 2) ∧
      Metric.diam (polyFacet S u h i ∩ polyFacet S u h (nbr i m)) =
        vol3 (X i m - X i ((m + k i - 1) % k i)) (u i) (u (nbr i m)) /
          √(1 - inner ℝ (u i) (u (nbr i m)) ^ 2) ∧
      0 ≤ vol3 (X i m - X i ((m + k i - 1) % k i)) (u i) (u (nbr i m)) ∧
      X i m - X i ((m + k i - 1) % k i) =
        (vol3 (X i m - X i ((m + k i - 1) % k i)) (u i) (u (nbr i m)) /
          (1 - inner ℝ (u i) (u (nbr i m)) ^ 2)) • cross3 (u i) (u (nbr i m)) := by
    intro i hi m hm
    set mp := (m + k i - 1) % k i with hmp_def
    have hmp : mp < k i := Nat.mod_lt _ (hkpos i hi)
    have hmpm : (mp + 1) % k i = m := succ_mod_pred hm
    have hva : 0 < vol3 (u i) (u (nbr i mp)) (u (nbr i m)) := by
      have := hpos i hi mp hmp; rwa [hmpm] at this
    have hvb := hpos i hi m hm
    have hXmpj : inner ℝ (u (nbr i m)) (X i mp) = h (nbr i m) := by
      have := hXb i hi mp hmp; rwa [hmpm] at this
    obtain ⟨hdiam, hW, hdir⟩ := facet_inter_diam hu hi (hnS i hi m hm) (hnS i hi mp hmp)
      (hnS i hi _ (hm1 i hi m hm)) (hL.nondeg i hi m hm) (hXK i hi mp hmp) (hXi i hi mp hmp)
      hXmpj (hXj i hi mp hmp) (hXK i hi m hm) (hXi i hi m hm) (hXj i hi m hm) (hXb i hi m hm)
      hva hvb
    refine ⟨?_, hdiam, hW, hdir⟩
    have t2 : (linkSupport u nbr i h' ((m + 1) % k i) -
        linkSupport u nbr i h' m * Real.cos (θ i m)) / Real.sin (θ i m) =
        vol3 (X i m - c0) (u i) (u (nbr i m)) / √(1 - inner ℝ (u i) (u (nbr i m)) ^ 2) := by
      rw [hlink i hi _ (X i m) (hXi i hi m hm) (hXb i hi m hm),
        hlink i hi m (X i m) (hXi i hi m hm) (hXj i hi m hm)]
      exact edge_half_right (hu i hi) (hu _ (hnS i hi m hm)) (hL.sin_ne i hi m hm)
        (hL.nondeg i hi m hm) (hL.nondeg i hi _ (hm1 i hi m hm)) (hL.sin_eq i hi m hm)
        (hL.cos_eq i hi m hm)
    have t1 : (linkSupport u nbr i h' mp - linkSupport u nbr i h' m * Real.cos (θ i mp)) /
        Real.sin (θ i mp) =
        -vol3 (X i mp - c0) (u i) (u (nbr i m)) / √(1 - inner ℝ (u i) (u (nbr i m)) ^ 2) := by
      rw [hlink i hi mp (X i mp) (hXi i hi mp hmp) (hXj i hi mp hmp),
        hlink i hi m (X i mp) (hXi i hi mp hmp) hXmpj]
      have hs := hL.sin_eq i hi mp hmp
      have hc := hL.cos_eq i hi mp hmp
      rw [hmpm] at hs hc
      exact edge_half_left (hu i hi) (hu _ (hnS i hi m hm)) (hL.sin_ne i hi mp hmp)
        (hL.nondeg i hi m hm) (hL.nondeg i hi mp hmp) hs hc
    unfold edgeLen
    rw [← hmp_def, t1, t2, vol3_sub_left (X i m) (X i mp)]
    rw [vol3_sub_left (X i m) c0, vol3_sub_left (X i mp) c0]
    ring
  refine ⟨h', fun i hi => by simp only [hh']; linarith [hc0 i hi], k, nbr, θ, T', hval, hL, hmem,
    hinj, fun i hi m hm => (hE i hi m hm).1.trans (hE i hi m hm).2.1.symm, ?_, ?_⟩
  · intro i hi j hj hnot
    obtain ⟨hji, hjS⟩ := Finset.mem_erase.1 hj
    obtain ⟨m, hm, γ, α, β, hα, hβ, hcomb⟩ := hsec i hi (u j)
    have hb := hm1 i hi m hm
    apply Metric.diam_subsingleton
    exact facet_inter_subsingleton hu hfac hi hjS (hnS i hi m hm) (hnS i hi _ hb) hji
      (Ne.symm (hnot m hm)) (Ne.symm (hnot _ hb)) (Finset.mem_erase.1 (hmem i hi m hm)).1
      (Finset.mem_erase.1 (hmem i hi _ hb)).1 (hpos i hi m hm).ne' (hXK i hi m hm)
      (hXi i hi m hm) (hXj i hi m hm) (hXb i hi m hm) hα hβ hcomb
  · intro i hi
    exact facet_area_pos hu hfac hi c0 (hkpos i hi) (X i) (hXi i hi) (hXj i hi) (hXb i hi)
      (hmem i hi) (hL.nondeg i hi) (fun m hm => (hE i hi m hm).1)
      (fun m hm => (hE i hi m hm).2.2.1) (fun m hm => (hE i hi m hm).2.2.2) (hsec i hi)

end Erdos99
end

end FacetLinksProof

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `FanTheorem`
-/

section FanTheorem

/-!
# The fan theorem (Verification Guide §7.3)

The fan theorem: for a complete simplicial fan in `ℝ³` with ray vectors `v`, a symmetric matrix
`W` with nonpositive off-diagonal entries supported on edges of the fan and with `W v = 0` has at
most one negative direction, in the form "no two-dimensional negative-definite restriction"
(`fan_theorem`).

Following §7.3 of the Verification Guide, the proof is split into four steps:

* (a) normalisation of the rays to unit vectors by a positive diagonal congruence
  (`noNegativePlane_of_diag_congr`, `fan_normalize`; proved here);
* (b)–(f) approximation of `W` (for unit rays) by minus the support-number volume Hessians of
  genuine polytopes `K_t` (`fan_matrix_approx`).  Steps (d) and (f) (the shifted polytopes are
  bounded, have all facets present, and their Hessians converge to `W`) are proved in
  `FanApprox` from support data integrating `W`; the convexity step (c) is proved in
  `FanConvexity`, and the integration step (b) is `fan_gradient_exists`, proved in
  `FanGradientExists` by an explicit potential;
* (e) the volume-Hessian theorem for a polytope in `ℝ³` (Izmestiev, Theorem 2.4):
  `polytopeHessian_noNegativePlane`, proved by Hilbert's argument (`HilbertLorentz`, using
  the two-dimensional Minkowski inequality of `MinkowskiPlane`) from the connectivity of the
  facet graph (`polytopeHessian_connected`, proved in `PolytopeConnected`) and the facet
  decomposition `polytope_facetForms`.  The latter is derived from the row identity
  (`facetRow_of_edges`, `FacetLinks`) and the symmetry of mixed volumes
  (`facetForms_sym_of_row`, `MixedVolume`), both proved, and the geometric input about the
  facial structure, `polytope_facetLinks`, proved in `FacetLinksProof`;
* (g) "no negative plane" is closed under entrywise limits (`noNegativePlane_of_approx`;
  proved here).

All matrices are indexed by an arbitrary type `ι` and restricted to a finite index set `S`.
-/

open scoped BigOperators

@[expose] public noncomputable section

open Classical

namespace Erdos99

variable {ι : Type*}

/-! ## (g) Closedness under limits -/

/-- **Step (g).**  "No negative plane" is closed under entrywise limits: if `W` can be
approximated on `S` arbitrarily well by matrices with no negative plane, then `W` has no negative
plane. -/
theorem noNegativePlane_of_approx {S : Finset ι} {W : ι → ι → ℝ}
    (happrox : ∀ ε > 0, ∃ M : ι → ι → ℝ, NoNegativePlane S M ∧
      ∀ i ∈ S, ∀ j ∈ S, |M i j - W i j| < ε) :
    NoNegativePlane S W := by
  intro f g hneg
  obtain ⟨hA, hD⟩ := gram_of_negPlane hneg
  -- approximating sequence
  choose M hM hMW using fun n : ℕ => happrox (1 / ((n : ℝ) + 1)) (by positivity)
  have hconv : ∀ i ∈ S, ∀ j ∈ S,
      Filter.Tendsto (fun n => M n i j) Filter.atTop (nhds (W i j)) := by
    intro i hi j hj
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq]
    calc |M n i j - W i j| < 1 / ((n : ℝ) + 1) := hMW n i hi j hj
      _ ≤ 1 / ((N : ℝ) + 1) := by
          gcongr
      _ < ε := hN
  have hbil : ∀ p q : ι → ℝ, Filter.Tendsto (fun n => bilinForm S (M n) p q) Filter.atTop
      (nhds (bilinForm S W p q)) := by
    intro p q
    unfold bilinForm
    refine tendsto_finset_sum _ fun i hi => tendsto_finset_sum _ fun j hj => ?_
    exact ((hconv i hi j hj).mul tendsto_const_nhds).mul tendsto_const_nhds
  have hAt := hbil f f
  have hCt := hbil g g
  have hBt := (hbil f g).add (hbil g f)
  have hDt := ((tendsto_const_nhds (x := (4 : ℝ))).mul hAt |>.mul hCt).sub (hBt.pow 2)
  have e1 := hAt.eventually (gt_mem_nhds hA)
  have e2 := hDt.eventually (lt_mem_nhds hD)
  obtain ⟨n, hn1, hn2⟩ := (e1.and e2).exists
  apply hM n f g
  intro a b hab
  rw [quadForm_comb]
  have := binary_neg_of_disc hn1 hn2 a b hab
  linarith

/-! ## (a) Diagonal congruence -/

/-- **Step (a), algebraic part.**  A positive diagonal congruence `W' i j = r i * W i j * r j`
(with `r i ≠ 0` on `S`) preserves the absence of negative planes. -/
theorem noNegativePlane_of_diag_congr {S : Finset ι} {W : ι → ι → ℝ} (r : ι → ℝ)
    (hr : ∀ i ∈ S, r i ≠ 0) (h : NoNegativePlane S (fun i j => r i * W i j * r j)) :
    NoNegativePlane S W := by
  intro f g hneg
  apply h (fun i => f i / r i) (fun i => g i / r i)
  intro a b hab
  have := hneg a b hab
  convert this using 1
  unfold quadForm
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
  have hri := hr i hi
  have hrj := hr j hj
  field_simp

/-! ## The volume-Hessian theorem (step (e)) -/

/-- **Step (e), geometric input 1: the facet graph is connected.**  For a bounded polytope with
unit normals all of whose facets are present, the pairs of facets sharing an edge of positive
length connect all the facets.  Proved in `PolytopeConnected`. -/
theorem polytopeHessian_connected {S : Finset ι} {u : ι → Space3} {h : ι → ℝ}
    (hu : ∀ i ∈ S, ‖u i‖ = 1) (hbdd : Bornology.IsBounded (polyK S u h))
    (hfac : FacetsPresent S u h) :
    ∀ U ⊆ S, U.Nonempty → U ≠ S → ∃ i ∈ U, ∃ j ∈ S, j ∉ U ∧ polytopeHessian S u h i j < 0 :=
  polytopeHessian_connected_aux hu hbdd hfac

/-- **Step (e), geometric input 2: the triangulated facet links**.  For a bounded
polytope with unit normals all of whose facets are present, after translating an interior point
to the origin (support numbers `h' > 0`):

* triangulate the normal fan of the polytope (a non-simple vertex is split into triangles by
  zero-length edges); `T` is its set of positively oriented triangles, and for each facet `i`,
  `nbr i 0, …, nbr i (k i - 1)` are its neighbours in the triangulated fan in counterclockwise
  order (distinct facets other than `i`), with gaps `θ i m` the exterior angles of the facet
  polygon (`ValidGaps`, `LinkData`);
* the `m`-th edge of the facet polygon with support numbers `linkSupport u nbr i h'` has length
  `|F_i ∩ F_{nbr i m}|` (zero for the added edges), and every facet not in the link meets `F_i`
  in a set of diameter `0`;
* each facet has positive area, `qᵢ(linkSupport u nbr i h') > 0`.

This is the bookkeeping of the facial structure of a three-dimensional polytope.  The row identity
(`facetRow_of_edges`, `FacetLinks`) and the mixed-volume symmetry (`facetForms_sym_of_row`,
`MixedVolume`), which used to be part of this step, are proved; the facial bookkeeping itself is `polytope_facetLinks_proof`
(`FacetLinksProof`). -/
theorem polytope_facetLinks {S : Finset ι} {u : ι → Space3} {h : ι → ℝ}
    (hu : ∀ i ∈ S, ‖u i‖ = 1) (hbdd : Bornology.IsBounded (polyK S u h))
    (hfac : FacetsPresent S u h) :
    ∃ h' : ι → ℝ, (∀ i ∈ S, 0 < h' i) ∧
      ∃ (k : ι → ℕ) (nbr : ι → ℕ → ι) (θ : ι → ℕ → ℝ) (T : Finset (ι × ι × ι)),
        (∀ i ∈ S, ValidGaps (k i) (θ i)) ∧ LinkData S u k nbr θ T ∧
        (∀ i ∈ S, ∀ m < k i, nbr i m ∈ S.erase i) ∧
        (∀ i ∈ S, ∀ m < k i, ∀ m' < k i, nbr i m = nbr i m' → m = m') ∧
        (∀ i ∈ S, ∀ m < k i, edgeLen (k i) (θ i) (linkSupport u nbr i h') m =
          Metric.diam (polyFacet S u h i ∩ polyFacet S u h (nbr i m))) ∧
        (∀ i ∈ S, ∀ j ∈ S.erase i, (∀ m < k i, nbr i m ≠ j) →
          Metric.diam (polyFacet S u h i ∩ polyFacet S u h j) = 0) ∧
        (∀ i ∈ S, 0 < polyForm (k i) (θ i) (linkSupport u nbr i h')) :=
  polytope_facetLinks_proof hu hbdd hfac

/-- **Step (e), geometric input 2': the facet decomposition.**  For a bounded polytope with unit
normals all of whose facets are present, after translating an interior point to the origin
(support numbers `h' > 0`), each facet `i` is a convex polygon in its own plane: its outer edge
normals, taken in cyclic order, have admissible gaps `θ i` (a triangulation of each non-simple
vertex adds zero-length edges), and `G i f` lists the induced support numbers
`(f j - ⟪u i, u j⟫ f i) / |u i × u j|` of the neighbouring facets `j`.  Then

* `-(M f)ᵢ` is the polar area form of the facet polygon `G i h'` against `G i f` (the
  first variation of the facet area; `M` is minus the volume Hessian, i.e. `polytopeHessian`);
* `-fᵀ M f = ∑ᵢ h'ᵢ qᵢ(G i f)` (symmetry of the mixed volume `V(h', f, f)`);
* each facet has positive area, `qᵢ(G i h') > 0`.

Derived from the triangulated facet links `polytope_facetLinks` (proved), the row identity
`facetRow_of_edges` and the symmetry of mixed volumes `facetForms_sym_of_row` (both proved). -/
theorem polytope_facetForms {S : Finset ι} {u : ι → Space3} {h : ι → ℝ}
    (hu : ∀ i ∈ S, ‖u i‖ = 1) (hbdd : Bornology.IsBounded (polyK S u h))
    (hfac : FacetsPresent S u h) :
    ∃ h' : ι → ℝ, (∀ i ∈ S, 0 < h' i) ∧
      ∃ (k : ι → ℕ) (θ : ι → ℕ → ℝ) (G : ι → (ι → ℝ) → ℕ → ℝ),
        (∀ i ∈ S, ValidGaps (k i) (θ i)) ∧
        (∀ f : ι → ℝ, ∀ i ∈ S, -∑ j ∈ S, polytopeHessian S u h i j * f j =
          polyBilin (k i) (θ i) (G i h') (G i f)) ∧
        (∀ f : ι → ℝ, -quadForm S (polytopeHessian S u h) f =
          ∑ i ∈ S, h' i * polyForm (k i) (θ i) (G i f)) ∧
        (∀ i ∈ S, 0 < polyForm (k i) (θ i) (G i h')) := by
  obtain ⟨h', hh', k, nbr, θ, T, hθ, hL, hmem, hinj, hlen, hzero, harea⟩ :=
    polytope_facetLinks hu hbdd hfac
  have hrow : ∀ f : ι → ℝ, ∀ i ∈ S, -∑ j ∈ S, polytopeHessian S u h i j * f j =
      polyBilin (k i) (θ i) (linkSupport u nbr i h') (linkSupport u nbr i f) :=
    fun f i hi => facetRow_of_edges h' hi (hmem i hi) (hinj i hi) (hlen i hi) (hzero i hi) f
  exact ⟨h', hh', k, θ, fun i f => linkSupport u nbr i f, hθ, hrow,
    facetForms_sym_of_row hL _ h' hrow, harea⟩

/-- **Step (e): the volume-Hessian theorem in `ℝ³`** (Izmestiev, *The Colin de Verdière number
and graphs of polytopes*, Theorem 2.4 and Appendix A.3).  For a bounded polytope with unit facet
normals all of whose facets are genuinely present, minus the support-number volume Hessian has at
most one negative direction.

Proved from Hilbert's argument (`noNegativePlane_of_facetForms`, which uses the two-dimensional
Minkowski inequality `polyForm_minkowski`), the connectivity of the facet graph
(`polytopeHessian_connected`, proved) and the facet decomposition `polytope_facetForms`
(derived from the triangulated facet links `polytope_facetLinks`). -/
theorem polytopeHessian_noNegativePlane {S : Finset ι} {u : ι → Space3} {h : ι → ℝ}
    (hu : ∀ i ∈ S, ‖u i‖ = 1) (hbdd : Bornology.IsBounded (polyK S u h))
    (hfac : FacetsPresent S u h) :
    NoNegativePlane S (polytopeHessian S u h) := by
  obtain ⟨h', hh', k, θ, G, hθ, hrow, hsym, harea⟩ := polytope_facetForms hu hbdd hfac
  exact noNegativePlane_of_facetForms (polytopeHessian_symm S u h)
    (fun i _ j _ hij => polytopeHessian_offdiag_nonpos S u h hij)
    (polytopeHessian_connected hu hbdd hfac) h' hh' k θ hθ G hrow hsym harea

/-- **Steps (b), (c): integrating a fan matrix.**  For a complete simplicial fan with
unit rays `u`, every one of which lies in a cone of the fan, and a symmetric `W` with
nonpositive off-diagonal entries supported on fan edges and `W u = 0`, there is support data
(`FanSupport`, `FanApprox`): a point `g τ` for each cone `τ` and numbers `h` with
`⟪u k, g τ⟫ = h k` for `k ∈ τ`, `⟪u k, g τ⟫ ≤ h k` for all `k ∈ S`, and
`‖g τ - g τ'‖ = -W i j |u i × u j|` whenever the distinct cones `τ, τ'` share the edge `ij`.

Derived from the integration step (b) `fan_gradient_exists` (proved in
`FanGradientExists`) and the convexity step (c)
`FanGradient.fanSupport` (proved in `FanConvexity`: the piecewise-linear function with the
integrated gradients is convex, by a local-to-global argument along generic segments). -/
theorem fan_support_exists {S : Finset ι} {u : ι → Space3} {T : Finset (Finset ι)}
    (hfan : IsSimplicialFan S u T) (hu : ∀ i ∈ S, ‖u i‖ = 1) (hused : ∀ i ∈ S, ∃ τ ∈ T, i ∈ τ)
    {W : ι → ι → ℝ} (hWs : ∀ i j, W i j = W j i)
    (hneg : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → W i j ≤ 0)
    (hsupp : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → W i j ≠ 0 → FanEdge T i j)
    (hker : ∀ i ∈ S, ∑ j ∈ S, W i j • u j = 0) :
    ∃ (g : Finset ι → Space3) (h : ι → ℝ), FanSupport S u T W g h := by
  obtain ⟨g, hg⟩ := fan_gradient_exists hfan hused hWs hsupp hker
  obtain ⟨h, hs⟩ := hg.fanSupport hfan hu hused hneg
  exact ⟨g, h, hs⟩

/-- **Steps (b)–(f): approximation by polytopes.**  For a complete simplicial fan with distinct
unit rays `u`, every one of which lies in a cone of the fan, and a symmetric `W` with nonpositive
off-diagonal entries supported on fan edges and `W u = 0`, the matrix `W` is an entrywise limit of
minus volume Hessians of bounded polytopes `K_t = {x : ⟪u i, x⟫ ≤ h(u i) + t}` with all facets
present.

Derived from the integration step `fan_support_exists` (steps (b), (c)) and steps (d), (f)
(`IsSimplicialFan.matrix_approx_of_support`, proved in `FanApprox`).

The hypothesis `hused` was missing from an earlier version of this statement, which was false
without it: a ray `u k` lying in the relative interior of a two-dimensional cone of the fan
spanned by `u i, u j` with `W i j ≠ 0` (allowed when `k` belongs to no cone, since then row `k`
of `W` vanishes) forces `F_i ∩ F_j = ∅` in every polytope in which the facet `k` is present, so
the entry `(i, j)` of every such Hessian is `0`. -/
theorem fan_matrix_approx {S : Finset ι} {u : ι → Space3} {T : Finset (Finset ι)}
    (hfan : IsSimplicialFan S u T) (hu : ∀ i ∈ S, ‖u i‖ = 1)
    (hinj : ∀ i ∈ S, ∀ j ∈ S, u i = u j → i = j) (hused : ∀ i ∈ S, ∃ τ ∈ T, i ∈ τ)
    {W : ι → ι → ℝ} (hWs : ∀ i j, W i j = W j i)
    (hneg : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → W i j ≤ 0)
    (hsupp : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → W i j ≠ 0 → FanEdge T i j)
    (hker : ∀ i ∈ S, ∑ j ∈ S, W i j • u j = 0) :
    ∀ ε > 0, ∃ h : ι → ℝ, Bornology.IsBounded (polyK S u h) ∧ FacetsPresent S u h ∧
      ∀ i ∈ S, ∀ j ∈ S, |polytopeHessian S u h i j - W i j| < ε := by
  obtain ⟨g, h, hs⟩ := fan_support_exists hfan hu hused hWs hneg hsupp hker
  exact hfan.matrix_approx_of_support hu hinj hused hsupp hker hs

/-- The fan theorem for unit rays: steps (b)–(g). -/
theorem fan_theorem_unit {S : Finset ι} {u : ι → Space3} {T : Finset (Finset ι)}
    (hfan : IsSimplicialFan S u T) (hu : ∀ i ∈ S, ‖u i‖ = 1)
    (hinj : ∀ i ∈ S, ∀ j ∈ S, u i = u j → i = j) (hused : ∀ i ∈ S, ∃ τ ∈ T, i ∈ τ)
    {W : ι → ι → ℝ} (hWs : ∀ i j, W i j = W j i)
    (hneg : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → W i j ≤ 0)
    (hsupp : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → W i j ≠ 0 → FanEdge T i j)
    (hker : ∀ i ∈ S, ∑ j ∈ S, W i j • u j = 0) :
    NoNegativePlane S W := by
  apply noNegativePlane_of_approx
  intro ε hε
  obtain ⟨h, hbdd, hfac, hclose⟩ := fan_matrix_approx hfan hu hinj hused hWs hneg hsupp hker ε hε
  exact ⟨_, polytopeHessian_noNegativePlane hu hbdd hfac, hclose⟩

/-- **The fan theorem** (§7.3 of the Verification Guide).  Let `T` be a complete simplicial fan
in `ℝ³` with nonzero rays `v i` (`i ∈ S`), each belonging to some cone of `T`, no two of which
are positively proportional.  Let `W`
be symmetric with nonpositive off-diagonal entries, supported (off the diagonal) on edges of the
fan, and with `∑_j W i j v j = 0` for every `i`.  Then `W` has no two-dimensional
negative-definite restriction.

Proved here from the normalisation step (a), the closedness step (g), the approximation
`fan_matrix_approx` ((b)–(f); steps (d), (f) proved in `FanApprox`, the integration step
(b) in `FanGradientExists`, (c) in `FanConvexity`) and
`polytopeHessian_noNegativePlane` ((e)). -/
theorem fan_theorem {S : Finset ι} {v : ι → Space3} {T : Finset (Finset ι)}
    (hfan : IsSimplicialFan S v T) (hused : ∀ i ∈ S, ∃ τ ∈ T, i ∈ τ) (hv : ∀ i ∈ S, v i ≠ 0)
    (hray : ∀ i ∈ S, ∀ j ∈ S, ∀ c : ℝ, 0 < c → v i = c • v j → i = j)
    {W : ι → ι → ℝ} (hWs : ∀ i j, W i j = W j i)
    (hneg : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → W i j ≤ 0)
    (hsupp : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → W i j ≠ 0 → FanEdge T i j)
    (hker : ∀ i ∈ S, ∑ j ∈ S, W i j • v j = 0) :
    NoNegativePlane S W := by
  set r : ι → ℝ := fun i => ‖v i‖
  have hr : ∀ i ∈ S, 0 < r i := fun i hi => norm_pos_iff.2 (hv i hi)
  apply noNegativePlane_of_diag_congr r fun i hi => (hr i hi).ne'
  set u : ι → Space3 := fun i => (r i)⁻¹ • v i
  have hfan' : IsSimplicialFan S u T := hfan.smul _ fun i hi => inv_pos.2 (hr i hi)
  have hu : ∀ i ∈ S, ‖u i‖ = 1 := by
    intro i hi
    simp only [u, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (hr i hi)]
    exact inv_mul_cancel₀ (hr i hi).ne'
  refine fan_theorem_unit hfan' hu ?_ hused ?_ ?_ ?_ ?_
  · intro i hi j hj hij
    apply hray i hi j hj (r i / r j) (div_pos (hr i hi) (hr j hj))
    have := congrArg (fun w => r i • w) hij
    simp only [u, smul_smul, mul_inv_cancel₀ (hr i hi).ne', one_smul] at this
    rw [this, div_eq_mul_inv]
  · intro i j
    simp only [hWs i j]
    ring
  · intro i hi j hj hij
    have := hneg i hi j hj hij
    have := (hr i hi).le
    have := (hr j hj).le
    have : 0 ≤ r i * r j := by positivity
    nlinarith
  · intro i hi j hj hij hW
    apply hsupp i hi j hj hij
    intro h0
    apply hW
    simp [h0]
  · intro i hi
    have := hker i hi
    calc ∑ j ∈ S, (r i * W i j * r j) • u j = r i • ∑ j ∈ S, W i j • v j := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun j hj => ?_
          simp only [u, smul_smul]
          congr 1
          field_simp [(hr j hj).ne']
      _ = 0 := by rw [this, smul_zero]

end Erdos99
end

end FanTheorem

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `LiftedFan`
-/

section LiftedFan

/-!
# The lifted configuration and its fan (Verification Guide §7.2–§7.3)

For a finite planar set `X`, the manuscript lifts `X` to the centrally symmetric point set
`v⁺ₓ = (x, 1)`, `v⁻ₓ = -(x, 1)` in `ℝ³` (`liftVec`, indexed by `Plane ⊕ Plane`).  Given stresses
`λ` (on unit pairs) and `μ` (on diameter pairs), the block matrix

  `W = [[B₀, -C_μ], [-C_μ, B₀]]`,   `B₀ = L(λ) - diag(C_μ 1)`

is `liftedMatrix X λ μ`; its quadratic form is `liftedForm X λ μ s t`.

Proved here:
* `liftedForm_eq_quadForm`: the lifted form is the quadratic form of `W`;
* `liftedMatrix_ker`: `W V = 0` for the ray matrix `V`, including the final lifted coordinate
  (from the equilibrium condition);
* signs and support of `W` (`liftedMatrix_offdiag_nonpos`, `liftedMatrix_support`);
* the lifted rays are nonzero and pairwise non-proportional (`liftVec_ne_zero`, `liftVec_ray`);
* `lifted_form_no_negative_plane_of_fan`: the fan theorem for the lift, from the abstract
  `fan_theorem` and the existence of a suitable fan.

* `lifted_fan_exists`: the existence of a complete simplicial fan on the lifted rays in which every
  unit pair (on both caps) and every diameter pair (across the caps) is an edge.  It is the regular
  fan (`RegularFan`) for the heights `1 + ε |x|² + t ^ k(x)` with `ε, t > 0` small.
-/

open scoped BigOperators
open Filter Topology

@[expose] public noncomputable section

open Classical

namespace Erdos99

/-- The quadratic form of the lifted block matrix `W = [[B₀, -C_μ], [-C_μ, B₀]]` on the pair
`(s, t)` (values at the upper lifted points `(x, 1)` and at the lower lifted points `-(x, 1)`),
written with ordered-pair sums:
`½ ∑ λ(x,y) ((s x - s y)² + (t x - t y)²) - ∑ μ(x,y) (s x + t y)²`. -/
def liftedForm (X : Finset Plane) (lam mu : Plane → Plane → ℝ) (s t : Plane → ℝ) : ℝ :=
  (1 / 2) * ∑ x ∈ X, ∑ y ∈ X, lam x y * ((s x - s y) ^ 2 + (t x - t y) ^ 2) -
    ∑ x ∈ X, ∑ y ∈ X, mu x y * (s x + t y) ^ 2

/-- The lifted point `(x, 1) ∈ ℝ³`. -/
def liftPt (x : Plane) : Space3 := !₂[x 0, x 1, 1]

/-- The lifted rays: `inl x ↦ (x, 1)` (upper cap) and `inr x ↦ -(x, 1)` (lower cap). -/
def liftVec : Plane ⊕ Plane → Space3
  | Sum.inl x => liftPt x
  | Sum.inr x => -liftPt x

/-- The block matrix `W = [[B₀, -C_μ], [-C_μ, B₀]]` with `B₀ = L(λ) - diag(C_μ 1)`, indexed by
`Plane ⊕ Plane` (upper copy `inl`, lower copy `inr`). -/
def liftedMatrix (X : Finset Plane) (lam mu : Plane → Plane → ℝ) :
    Plane ⊕ Plane → Plane ⊕ Plane → ℝ
  | Sum.inl x, Sum.inl y => (if x = y then ∑ z ∈ X, (lam x z - mu x z) else 0) - lam x y
  | Sum.inr x, Sum.inr y => (if x = y then ∑ z ∈ X, (lam x z - mu x z) else 0) - lam x y
  | Sum.inl x, Sum.inr y => -mu x y
  | Sum.inr x, Sum.inl y => -mu x y

/-- A double sum of an antisymmetric function vanishes. -/
lemma sum_sum_antisymm (X : Finset Plane) (g : Plane → Plane → ℝ)
    (hg : ∀ x y, g x y = -g y x) : ∑ x ∈ X, ∑ y ∈ X, g x y = 0 := by
  have h : ∑ x ∈ X, ∑ y ∈ X, g x y = -∑ x ∈ X, ∑ y ∈ X, g x y := by
    conv_rhs => rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => hg x y
  linarith

lemma sum_ite_mul_eq (X : Finset Plane) {x : Plane} (hx : x ∈ X) (c a : ℝ) (b : Plane → ℝ) :
    ∑ y ∈ X, (if x = y then c else 0) * a * b y = c * a * b x := by
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hyx; simp [Ne.symm hyx]
  · intro h; exact absurd hx h

/-- The lifted form is the quadratic form of the lifted block matrix. -/
theorem liftedForm_eq_quadForm (X : Finset Plane) (lam mu : Plane → Plane → ℝ)
    (hlams : ∀ x y, lam x y = lam y x) (hmus : ∀ x y, mu x y = mu y x) (s t : Plane → ℝ) :
    liftedForm X lam mu s t = quadForm (X.disjSum X) (liftedMatrix X lam mu) (Sum.elim s t) := by
  unfold quadForm
  rw [Finset.sum_disjSum]
  simp only [Finset.sum_disjSum, Sum.elim_inl, Sum.elim_inr, liftedMatrix]
  have hrow : ∀ x ∈ X, ∀ f : Plane → ℝ,
      ∑ y ∈ X, ((if x = y then ∑ z ∈ X, (lam x z - mu x z) else 0) - lam x y) * f x * f y =
        ∑ y ∈ X, ((lam x y - mu x y) * f x * f x - lam x y * f x * f y) := by
    intro x hx f
    simp only [sub_mul, Finset.sum_sub_distrib, sum_ite_mul_eq X hx, Finset.sum_mul]
  rw [← Finset.sum_add_distrib, ← sub_eq_zero]
  unfold liftedForm
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  have : ∀ x ∈ X,
      ((1 / 2) * ∑ y ∈ X, lam x y * ((s x - s y) ^ 2 + (t x - t y) ^ 2) -
        ∑ y ∈ X, mu x y * (s x + t y) ^ 2) -
      ((∑ y ∈ X, ((if x = y then ∑ z ∈ X, (lam x z - mu x z) else 0) - lam x y) * s x * s y +
          ∑ y ∈ X, -mu x y * s x * t y) +
        (∑ y ∈ X, -mu x y * t x * s y +
          ∑ y ∈ X, ((if x = y then ∑ z ∈ X, (lam x z - mu x z) else 0) - lam x y) * t x * t y)) =
      ∑ y ∈ X, ((1 / 2) * lam x y * (s y ^ 2 - s x ^ 2 + t y ^ 2 - t x ^ 2) +
        (mu x y * t x ^ 2 - mu x y * t y ^ 2) + (mu x y * t x * s y - mu x y * s x * t y)) := by
    intro x hx
    rw [hrow x hx s, hrow x hx t, Finset.mul_sum]
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  rw [Finset.sum_congr rfl this]
  apply sum_sum_antisymm
  intro x y
  rw [hlams y x, hmus y x]
  ring

/-- Coordinates of the lifted points. -/
@[simp] lemma liftPt_apply_zero (x : Plane) : liftPt x 0 = x 0 := rfl
@[simp] lemma liftPt_apply_one (x : Plane) : liftPt x 1 = x 1 := rfl
@[simp] lemma liftPt_apply_two (x : Plane) : liftPt x 2 = 1 := rfl

lemma liftPt_ne_zero (x : Plane) : liftPt x ≠ 0 := by
  intro h
  have := congrArg (fun w : Space3 => w 2) h
  simp at this

lemma liftVec_ne_zero (i : Plane ⊕ Plane) : liftVec i ≠ 0 := by
  cases i with
  | inl x => exact liftPt_ne_zero x
  | inr x => simpa [liftVec] using liftPt_ne_zero x

lemma liftPt_eq_iff (x y : Plane) : liftPt x = liftPt y ↔ x = y := by
  constructor
  · intro h
    have h0 := congrArg (fun w : Space3 => w 0) h
    have h1 := congrArg (fun w : Space3 => w 1) h
    simp only [liftPt_apply_zero, liftPt_apply_one] at h0 h1
    ext k; fin_cases k <;> simp [h0, h1]
  · rintro rfl; rfl

/-- No two distinct lifted rays are positively proportional. -/
lemma liftVec_ray (i j : Plane ⊕ Plane) (c : ℝ) (hc : 0 < c) (h : liftVec i = c • liftVec j) :
    i = j := by
  have h2 := congrArg (fun w : Space3 => w 2) h
  cases i with
  | inl x =>
    cases j with
    | inl y =>
      simp [liftVec] at h2
      subst h2
      simp only [liftVec, one_smul, liftPt_eq_iff] at h
      rw [h]
    | inr y =>
      simp [liftVec] at h2
      linarith
  | inr x =>
    cases j with
    | inl y =>
      simp [liftVec] at h2
      linarith
    | inr y =>
      simp [liftVec] at h2
      subst h2
      simp only [liftVec, one_smul, neg_inj, liftPt_eq_iff] at h
      rw [h]

/-- The lifted block matrix is symmetric. -/
lemma liftedMatrix_symm (X : Finset Plane) (lam mu : Plane → Plane → ℝ)
    (hlams : ∀ x y, lam x y = lam y x) (hmus : ∀ x y, mu x y = mu y x) (i j : Plane ⊕ Plane) :
    liftedMatrix X lam mu i j = liftedMatrix X lam mu j i := by
  cases i <;> cases j <;> simp only [liftedMatrix] <;>
    first
    | (rw [hmus])
    | (split_ifs with h1 h2 h2 <;> subst_vars <;> simp_all)

/-- Off-diagonal entries of the lifted matrix are nonpositive. -/
lemma liftedMatrix_offdiag_nonpos (X : Finset Plane) (lam mu : Plane → Plane → ℝ)
    (hlam0 : ∀ x y, 0 ≤ lam x y) (hmu0 : ∀ x y, 0 ≤ mu x y) (i j : Plane ⊕ Plane) (hij : i ≠ j) :
    liftedMatrix X lam mu i j ≤ 0 := by
  cases i with
  | inl x =>
    cases j with
    | inl y =>
      have hxy : x ≠ y := fun h => hij (by rw [h])
      simp [liftedMatrix, hxy, hlam0 x y]
    | inr y => simp [liftedMatrix, hmu0 x y]
  | inr x =>
    cases j with
    | inl y => simp [liftedMatrix, hmu0 x y]
    | inr y =>
      have hxy : x ≠ y := fun h => hij (by rw [h])
      simp [liftedMatrix, hxy, hlam0 x y]

/-- Support of the lifted matrix: a nonzero off-diagonal entry is a unit pair on one cap or a
diameter pair across the caps. -/
lemma liftedMatrix_support (X : Finset Plane) (lam mu : Plane → Plane → ℝ)
    (hlam1 : ∀ x y, dist x y ≠ 1 → lam x y = 0) (hmuD : ∀ x y, dist x y ≠ diam X → mu x y = 0)
    (i j : Plane ⊕ Plane) (hij : i ≠ j) (hW : liftedMatrix X lam mu i j ≠ 0) :
    (∃ x y, dist x y = 1 ∧
      ((i = Sum.inl x ∧ j = Sum.inl y) ∨ (i = Sum.inr x ∧ j = Sum.inr y))) ∨
    (∃ x y, dist x y = diam X ∧
      ((i = Sum.inl x ∧ j = Sum.inr y) ∨ (i = Sum.inr x ∧ j = Sum.inl y))) := by
  cases i with
  | inl x =>
    cases j with
    | inl y =>
      have hxy : x ≠ y := fun h => hij (by rw [h])
      refine Or.inl ⟨x, y, ?_, Or.inl ⟨rfl, rfl⟩⟩
      by_contra h
      exact hW (by simp [liftedMatrix, hxy, hlam1 x y h])
    | inr y =>
      refine Or.inr ⟨x, y, ?_, Or.inl ⟨rfl, rfl⟩⟩
      by_contra h
      exact hW (by simp [liftedMatrix, hmuD x y h])
  | inr x =>
    cases j with
    | inl y =>
      refine Or.inr ⟨x, y, ?_, Or.inr ⟨rfl, rfl⟩⟩
      by_contra h
      exact hW (by simp [liftedMatrix, hmuD x y h])
    | inr y =>
      have hxy : x ≠ y := fun h => hij (by rw [h])
      refine Or.inl ⟨x, y, ?_, Or.inr ⟨rfl, rfl⟩⟩
      by_contra h
      exact hW (by simp [liftedMatrix, hxy, hlam1 x y h])

/-- **`W V = 0`** (§7.2): the lifted matrix annihilates the ray matrix, coordinate by coordinate,
including the final lifted coordinate.  The planar coordinates use the equilibrium condition. -/
theorem liftedMatrix_ker (X : Finset Plane) (lam mu : Plane → Plane → ℝ)
    (heq : ∀ x ∈ X, ∑ y ∈ X, lam x y • (x - y) = ∑ y ∈ X, mu x y • (x - y))
    (i : Plane ⊕ Plane) (hi : i ∈ X.disjSum X) :
    ∑ j ∈ X.disjSum X, liftedMatrix X lam mu i j • liftVec j = 0 := by
  have key : ∀ x ∈ X, ∀ F : Plane → ℝ,
      ∑ y ∈ X, ((if x = y then ∑ z ∈ X, (lam x z - mu x z) else 0) - lam x y) * F y +
        ∑ y ∈ X, -mu x y * -F y =
      ∑ y ∈ X, lam x y * (F x - F y) - ∑ y ∈ X, mu x y * (F x - F y) := by
    intro x hx F
    have h1 : ∑ y ∈ X, (if x = y then ∑ z ∈ X, (lam x z - mu x z) else 0) * F y =
        (∑ z ∈ X, (lam x z - mu x z)) * F x := by
      have := sum_ite_mul_eq X hx (∑ z ∈ X, (lam x z - mu x z)) 1 F
      simpa using this
    have e : ∑ y ∈ X, ((if x = y then ∑ z ∈ X, (lam x z - mu x z) else 0) - lam x y) * F y =
        ∑ y ∈ X, (if x = y then ∑ z ∈ X, (lam x z - mu x z) else 0) * F y -
          ∑ y ∈ X, lam x y * F y := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [e, h1]
    simp only [neg_mul_neg, mul_sub, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
    ring
  have hcoord : ∀ x ∈ X, ∀ k : Fin 2,
      ∑ y ∈ X, lam x y * (x k - y k) = ∑ y ∈ X, mu x y * (x k - y k) := by
    intro x hx k
    have := congrArg (fun w : Plane => w k) (heq x hx)
    simpa using this
  have hF : ∀ x ∈ X, ∀ k : Fin 3,
      ∑ y ∈ X, lam x y * (liftPt x k - liftPt y k) =
        ∑ y ∈ X, mu x y * (liftPt x k - liftPt y k) := by
    intro x hx k
    fin_cases k
    · simpa using hcoord x hx 0
    · simpa using hcoord x hx 1
    · simp
  rcases i with x | x
  · have hx : x ∈ X := by simpa using hi
    ext k
    rw [Finset.sum_disjSum]
    have := key x hx (fun y => liftPt y k)
    simp only [WithLp.ofLp_add, WithLp.ofLp_sum, WithLp.ofLp_smul, WithLp.ofLp_neg,
      WithLp.ofLp_zero, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.neg_apply,
      Pi.zero_apply, smul_eq_mul, liftedMatrix, liftVec]
    linarith [hF x hx k]
  · have hx : x ∈ X := by simpa using hi
    ext k
    rw [Finset.sum_disjSum]
    have := key x hx (fun y => liftPt y k)
    simp only [WithLp.ofLp_add, WithLp.ofLp_sum, WithLp.ofLp_smul, WithLp.ofLp_neg,
      WithLp.ofLp_zero, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.neg_apply,
      Pi.zero_apply, smul_eq_mul, liftedMatrix, liftVec]
    have h2 : ∑ y ∈ X, -mu x y * liftPt y k +
        ∑ y ∈ X, ((if x = y then ∑ z ∈ X, (lam x z - mu x z) else 0) - lam x y) *
          -liftPt y k =
        -(∑ y ∈ X, ((if x = y then ∑ z ∈ X, (lam x z - mu x z) else 0) - lam x y) *
            liftPt y k + ∑ y ∈ X, -mu x y * -liftPt y k) := by
      simp only [mul_neg, neg_mul, Finset.sum_neg_distrib]
      ring
    linarith [hF x hx k]

/-- The functional exposing the cross-cap edge of a diameter pair `x, y` (§7.2):
`(x - y) · p - ((x - y) · (x + y)) z / 2` at `w = (p, z)`. -/
def exposeFun (x y : Plane) (w : Space3) : ℝ :=
  (x 0 - y 0) * w 0 + (x 1 - y 1) * w 1 -
    ((x 0 - y 0) * (x 0 + y 0) + (x 1 - y 1) * (x 1 + y 1)) / 2 * w 2

lemma dist_sq_coords (x y : Plane) : dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _),
    Fin.sum_univ_two, Real.dist_eq, Real.dist_eq, sq_abs, sq_abs]

/-- For a diameter pair `x, y` of `X` and `z ∈ X`, `(x - y) · (z - y) ≤ D²`, with equality only
at `z = x`. -/
lemma diam_pair_inner_le {X : Finset Plane} {x y z : Plane} (hy : y ∈ X) (hz : z ∈ X)
    (hxy : dist x y = diam X) :
    (x 0 - y 0) * (z 0 - y 0) + (x 1 - y 1) * (z 1 - y 1) ≤ diam X ^ 2 ∧
      ((x 0 - y 0) * (z 0 - y 0) + (x 1 - y 1) * (z 1 - y 1) = diam X ^ 2 → z = x) := by
  have ha : (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 = diam X ^ 2 := by
    rw [← dist_sq_coords, hxy]
  have hb : (z 0 - y 0) ^ 2 + (z 1 - y 1) ^ 2 ≤ diam X ^ 2 := by
    rw [← dist_sq_coords]
    have h1 := dist_le_diam hz hy
    have h0 := dist_nonneg (x := z) (y := y)
    nlinarith
  refine ⟨by nlinarith [sq_nonneg (x 0 - z 0), sq_nonneg (x 1 - z 1)], fun heq => ?_⟩
  have h0 : (x 0 - z 0) ^ 2 + (x 1 - z 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x 0 - z 0), sq_nonneg (x 1 - z 1)]
  have e0 : z 0 = x 0 := by nlinarith [sq_nonneg (x 0 - z 0), sq_nonneg (x 1 - z 1)]
  have e1 : z 1 = x 1 := by nlinarith [sq_nonneg (x 0 - z 0), sq_nonneg (x 1 - z 1)]
  ext k; fin_cases k
  · exact e0
  · exact e1

/-- **Diameter pairs give exposed cross-cap edges** (§7.2).  For a diameter pair `x, y` of `X`,
the functional `exposeFun x y` is at most `D² / 2` on every lifted point, with equality exactly at
the upper point `(x, 1)` and the lower point `-(y, 1)`. -/
theorem lifted_diam_exposed {X : Finset Plane} {x y : Plane} (hx : x ∈ X) (hy : y ∈ X)
    (hxy : dist x y = diam X) (i : Plane ⊕ Plane) (hi : i ∈ X.disjSum X) :
    exposeFun x y (liftVec i) ≤ diam X ^ 2 / 2 ∧
      (exposeFun x y (liftVec i) = diam X ^ 2 / 2 ↔ i = Sum.inl x ∨ i = Sum.inr y) := by
  have ha : (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 = diam X ^ 2 := by
    rw [← dist_sq_coords, hxy]
  rcases i with z | z
  · have hz : z ∈ X := by simpa using hi
    obtain ⟨hle, heq⟩ := diam_pair_inner_le hy hz hxy
    have hval : exposeFun x y (liftVec (Sum.inl z)) =
        (x 0 - y 0) * (z 0 - y 0) + (x 1 - y 1) * (z 1 - y 1) - diam X ^ 2 / 2 := by
      simp only [exposeFun, liftVec, liftPt_apply_zero, liftPt_apply_one, liftPt_apply_two]
      linarith
    rw [hval]
    refine ⟨by linarith, ⟨fun h => Or.inl ?_, ?_⟩⟩
    · rw [heq (by linarith)]
    · rintro (h | h)
      · cases h; linarith
      · cases h
  · have hz : z ∈ X := by simpa using hi
    obtain ⟨hle, heq⟩ := diam_pair_inner_le hx hz (by rw [dist_comm]; exact hxy)
    have hval : exposeFun x y (liftVec (Sum.inr z)) =
        (y 0 - x 0) * (z 0 - x 0) + (y 1 - x 1) * (z 1 - x 1) - diam X ^ 2 / 2 := by
      simp only [exposeFun, liftVec, PiLp.neg_apply, liftPt_apply_zero, liftPt_apply_one,
        liftPt_apply_two]
      linarith
    rw [hval]
    refine ⟨by linarith, ⟨fun h => Or.inr ?_, ?_⟩⟩
    · rw [heq (by linarith)]
    · rintro (h | h)
      · cases h
      · cases h; linarith

/-! ## Construction of the lifted fan

The fan is the regular fan (`RegularFan`) of the lifted rays with heights
`1 + ε |x|² + t ^ k(x)`: the paraboloid term `ε |x|²` makes the upper cap a Delaunay-type
subdivision of `X` (which contains every unit pair of the separated set `X`, since the circle on a
unit pair as diameter contains no other point of `X`), diameter pairs give cross-cap edges (the
perturbation of the exposing functional `exposeFun`), and the tiny generic perturbation
`t ^ k(x)` makes the fan simplicial. -/

lemma inner_liftPt (a : Space3) (z : Plane) :
    inner ℝ a (liftPt z) = a 0 * z 0 + a 1 * z 1 + a 2 := by
  rw [inner_eq_coords]; simp

lemma inner_liftVec_inl (a : Space3) (z : Plane) :
    inner ℝ a (liftVec (Sum.inl z)) = a 0 * z 0 + a 1 * z 1 + a 2 := inner_liftPt a z

lemma inner_liftVec_inr (a : Space3) (z : Plane) :
    inner ℝ a (liftVec (Sum.inr z)) = -(a 0 * z 0 + a 1 * z 1 + a 2) := by
  simp only [liftVec, inner_neg_right, inner_liftPt]

/-- The lifted rays positively span `ℝ³` (`X` is not collinear). -/
lemma liftVec_posSpan {X : Finset Plane} (hcol : ¬ Collinear ℝ (X : Set Plane)) :
    RegularFan.PosSpan (X.disjSum X) liftVec := by
  intro d hd
  by_contra h
  push_neg at h
  have hz : ∀ x ∈ X, d 0 * x 0 + d 1 * x 1 + d 2 = 0 := by
    intro x hx
    have h1 := h (Sum.inl x) (by simpa using hx)
    have h2 := h (Sum.inr x) (by simpa using hx)
    rw [inner_liftVec_inl] at h1
    rw [inner_liftVec_inr] at h2
    linarith
  apply hcol
  rcases X.eq_empty_or_nonempty with hX | ⟨p0, hp0⟩
  · rw [hX, Finset.coe_empty]; exact collinear_empty ℝ _
  by_cases h01 : d 0 = 0 ∧ d 1 = 0
  · exfalso
    have h2 : d 2 = 0 := by have := hz p0 hp0; rw [h01.1, h01.2] at this; linarith
    apply hd
    ext i; fin_cases i
    · exact h01.1
    · exact h01.2
    · exact h2
  have hn : 0 < d 0 ^ 2 + d 1 ^ 2 := by
    rcases not_and_or.1 h01 with h0 | h0
    · have := sq_pos_of_ne_zero h0; nlinarith [sq_nonneg (d 1)]
    · have := sq_pos_of_ne_zero h0; nlinarith [sq_nonneg (d 0)]
  rw [collinear_iff_of_mem (Finset.mem_coe.2 hp0)]
  refine ⟨!₂[-d 1, d 0], fun p hp => ?_⟩
  have hp' := hz p (Finset.mem_coe.1 hp)
  have hp0' := hz p0 hp0
  refine ⟨(d 0 * (p 1 - p0 1) - d 1 * (p 0 - p0 0)) / (d 0 ^ 2 + d 1 ^ 2), ?_⟩
  ext i; fin_cases i
  · simp only [vadd_eq_add]
    simp
    field_simp
    linear_combination (d 0) * (hp' - hp0')
  · simp only [vadd_eq_add]
    simp
    field_simp
    linear_combination (d 1) * (hp' - hp0')

/-- The heights `1 + ε |x|²` on both copies of `X`. -/
def liftHt (ε : ℝ) : Plane ⊕ Plane → ℝ :=
  Sum.elim (fun x => 1 + ε * (x 0 ^ 2 + x 1 ^ 2)) (fun x => 1 + ε * (x 0 ^ 2 + x 1 ^ 2))

/-- Central symmetry: a strict witness for `B` gives one for the swapped set. -/
lemma strictWit_swap {X : Finset Plane} {ε : ℝ} {B : Finset (Plane ⊕ Plane)} {a : Space3}
    (h : RegularFan.StrictWit (X.disjSum X) liftVec (liftHt ε) B a) :
    RegularFan.StrictWit (X.disjSum X) liftVec (liftHt ε) (B.image Sum.swap) (-a) := by
  intro m hm
  have hm' : m.swap ∈ X.disjSum X := by cases m <;> simpa using hm
  obtain ⟨h1, h2⟩ := h m.swap hm'
  have hinner : inner ℝ (-a) (liftVec m) = inner ℝ a (liftVec m.swap) := by
    cases m <;> simp [liftVec, inner_neg_left, inner_neg_right]
  have hht : liftHt ε m = liftHt ε m.swap := by cases m <;> rfl
  have hmem : m ∈ B.image Sum.swap ↔ m.swap ∈ B := by
    rw [Finset.mem_image]
    constructor
    · rintro ⟨b, hb, rfl⟩; simpa using hb
    · intro hb; exact ⟨_, hb, Sum.swap_swap _⟩
  rw [hinner, hht, hmem]
  exact ⟨h1, h2⟩

/-- **Circle witnesses** (upper cap): for a circle with centre `c` and squared radius `ρ`
containing no point of `X` in its interior, the points of `X` on it are the active upper rays. -/
lemma circle_wit {X : Finset Plane} {ε : ℝ} (hε : 0 < ε) (c : Plane) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hc : ε * (c 0 ^ 2 + c 1 ^ 2) < 1) (B : Finset (Plane ⊕ Plane))
    (hB : ∀ z ∈ X, (Sum.inl z ∈ B → (z 0 - c 0) ^ 2 + (z 1 - c 1) ^ 2 = ρ) ∧
      (Sum.inl z ∉ B → ρ < (z 0 - c 0) ^ 2 + (z 1 - c 1) ^ 2))
    (hBr : ∀ z, Sum.inr z ∉ B) :
    RegularFan.StrictWit (X.disjSum X) liftVec (liftHt ε) B
      !₂[2 * ε * c 0, 2 * ε * c 1, 1 - ε * (c 0 ^ 2 + c 1 ^ 2) + ε * ρ] := by
  rintro (z | z) hz
  · have hz' : z ∈ X := by simpa using hz
    rw [inner_liftVec_inl]
    simp only [liftHt, Sum.elim_inl]
    obtain ⟨h1, h2⟩ := hB z hz'
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have := h1 h
      simp
      linear_combination (-ε) * this
    · have := h2 h
      simp
      nlinarith
  · refine ⟨fun h => absurd h (hBr z), fun _ => ?_⟩
    rw [inner_liftVec_inr]
    simp only [liftHt, Sum.elim_inr]
    simp
    nlinarith [mul_nonneg hε.le (sq_nonneg (z 0 + c 0)), mul_nonneg hε.le (sq_nonneg (z 1 + c 1)),
      mul_nonneg hε.le hρ]

lemma coords_eq_of_sq_eq_zero {x y : Plane} (h : (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 = 0) :
    x = y := by
  have h0 : x 0 = y 0 := by nlinarith [sq_nonneg (x 0 - y 0), sq_nonneg (x 1 - y 1)]
  have h1 : x 1 = y 1 := by nlinarith [sq_nonneg (x 0 - y 0), sq_nonneg (x 1 - y 1)]
  ext i; fin_cases i
  · exact h0
  · exact h1

/-- Two distinct planar points have lifts with a dual vector. -/
lemma liftPt_dual {x y : Plane} (hxy : x ≠ y) :
    ∃ d : Space3, inner ℝ d (liftPt x) = 1 ∧ inner ℝ d (liftPt y) = 0 := by
  set n := (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2
  have hn : n ≠ 0 := fun h => hxy (coords_eq_of_sq_eq_zero h)
  refine ⟨!₂[(x 0 - y 0) / n, (x 1 - y 1) / n, -((x 0 - y 0) * y 0 + (x 1 - y 1) * y 1) / n],
    ?_, ?_⟩
  · rw [inner_liftPt]; simp; field_simp; ring
  · rw [inner_liftPt]; simp; field_simp; ring

lemma liftVec_dual_single (i : Plane ⊕ Plane) : ∃ d : Space3, inner ℝ d (liftVec i) = 1 := by
  rcases i with z | z
  · exact ⟨!₂[0, 0, 1], by rw [inner_liftVec_inl]; simp⟩
  · exact ⟨!₂[0, 0, -1], by rw [inner_liftVec_inr]; simp⟩

lemma liftVec_dual (i j : Plane ⊕ Plane) (h : Sum.elim id id i ≠ Sum.elim id id j) :
    ∃ d : Space3, inner ℝ d (liftVec i) = 1 ∧ inner ℝ d (liftVec j) = 0 := by
  rcases i with x | x <;> rcases j with y | y <;> simp only [Sum.elim_inl, Sum.elim_inr, id] at h
  · exact liftPt_dual h
  · obtain ⟨d, h1, h2⟩ := liftPt_dual h
    exact ⟨d, h1, by simp [liftVec, inner_neg_right, h2]⟩
  · obtain ⟨d, h1, h2⟩ := liftPt_dual h
    exact ⟨-d, by simp [liftVec, inner_neg_right, h1], by simp [liftVec, h2]⟩
  · obtain ⟨d, h1, h2⟩ := liftPt_dual h
    exact ⟨-d, by simp [liftVec, inner_neg_right, h1], by simp [liftVec, inner_neg_right, h2]⟩

lemma lifted_hasDual_pair {i j : Plane ⊕ Plane} (h : Sum.elim id id i ≠ Sum.elim id id j) :
    RegularFan.HasDual liftVec {i, j} := by
  convert RegularFan.hasDual_pair (liftVec_dual i j h) (liftVec_dual j i (Ne.symm h))

/-- **Diameter witnesses**: for a diameter pair `x, y`, and all small `ε > 0`, a perturbation of
the exposing functional `exposeFun x y` is a strict witness for the cross-cap pair
`(x, 1), -(y, 1)`. -/
lemma diam_wit_eventually {X : Finset Plane} {x y : Plane} (hx : x ∈ X) (hy : y ∈ X)
    (hxy : dist x y = diam X) (hD : 0 < diam X) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ a, RegularFan.StrictWit (X.disjSum X) liftVec (liftHt ε)
      {Sum.inl x, Sum.inr y} a := by
  set D := diam X
  have hD2 : (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 = D ^ 2 := by rw [← dist_sq_coords, hxy]
  have hDne : D ^ 2 ≠ 0 := by positivity
  set sx := x 0 ^ 2 + x 1 ^ 2
  set sy := y 0 ^ 2 + y 1 ^ 2
  set q : Plane → ℝ := fun z =>
    (x 0 - y 0) * (z 0 - (x 0 + y 0) / 2) + (x 1 - y 1) * (z 1 - (x 1 + y 1) / 2)
  set A : Plane → ℝ := fun z => 2 / D ^ 2 * q z
  set Bc : Plane → ℝ := fun z => (sx + sy) / D ^ 2 * q z + (sx - sy) / 2
  set a : ℝ → Space3 := fun ε =>
    !₂[(2 / D ^ 2 + ε * (sx + sy) / D ^ 2) * (x 0 - y 0),
      (2 / D ^ 2 + ε * (sx + sy) / D ^ 2) * (x 1 - y 1),
      ε * (sx - sy) / 2 - (2 / D ^ 2 + ε * (sx + sy) / D ^ 2) *
        ((x 0 - y 0) * (x 0 + y 0) / 2 + (x 1 - y 1) * (x 1 + y 1) / 2)]
  have hval : ∀ ε z, inner ℝ (a ε) (liftPt z) = A z + ε * Bc z := by
    intro ε z
    rw [inner_liftPt]
    simp [a, A, Bc, q]
    field_simp
    ring
  have hqx : q x = D ^ 2 / 2 := by simp only [q]; linear_combination hD2 / 2
  have hqy : q y = -(D ^ 2 / 2) := by simp only [q]; linear_combination -hD2 / 2
  have hlim : ∀ {p r s w : ℝ}, p < r → ∀ᶠ ε in 𝓝[>] (0 : ℝ), p + ε * s < r + ε * w := by
    intro p r s w hpr
    have h1 : Tendsto (fun ε : ℝ => p + ε * s) (𝓝[>] 0) (𝓝 p) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds
      have : Continuous (fun ε : ℝ => p + ε * s) := by fun_prop
      simpa using this.tendsto 0
    have h2 : Tendsto (fun ε : ℝ => r + ε * w) (𝓝[>] 0) (𝓝 r) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds
      have : Continuous (fun ε : ℝ => r + ε * w) := by fun_prop
      simpa using this.tendsto 0
    exact h1.eventually_lt h2 hpr
  have key : ∀ z ∈ X, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (z ≠ x → A z + ε * Bc z < 1 + ε * (z 0 ^ 2 + z 1 ^ 2)) ∧
      (z ≠ y → -1 + ε * (-(z 0 ^ 2 + z 1 ^ 2)) < A z + ε * Bc z) := by
    intro z hz
    refine Filter.Eventually.and ?_ ?_
    · by_cases hzx : z = x
      · exact Filter.Eventually.of_forall fun _ h => absurd hzx h
      · obtain ⟨hle, heq⟩ := diam_pair_inner_le hy hz hxy
        have hlt : (x 0 - y 0) * (z 0 - y 0) + (x 1 - y 1) * (z 1 - y 1) < D ^ 2 :=
          lt_of_le_of_ne hle fun h => hzx (heq h)
        have : A z < 1 := by
          simp only [A, q]
          rw [div_mul_eq_mul_div, div_lt_one (by positivity)]
          nlinarith
        filter_upwards [hlim (s := Bc z) (w := z 0 ^ 2 + z 1 ^ 2) this] with ε hε _
        exact hε
    · by_cases hzy : z = y
      · exact Filter.Eventually.of_forall fun _ h => absurd hzy h
      · obtain ⟨hle, heq⟩ := diam_pair_inner_le hx hz (by rw [dist_comm]; exact hxy)
        have hlt : (y 0 - x 0) * (z 0 - x 0) + (y 1 - x 1) * (z 1 - x 1) < D ^ 2 :=
          lt_of_le_of_ne hle fun h => hzy (heq h)
        have : -1 < A z := by
          simp only [A, q]
          rw [div_mul_eq_mul_div, lt_div_iff₀ (by positivity)]
          nlinarith
        filter_upwards [hlim (s := -(z 0 ^ 2 + z 1 ^ 2)) (w := Bc z) this] with ε hε _
        exact hε
  rw [← Filter.eventually_all_finset] at key
  filter_upwards [key] with ε hε
  refine ⟨a ε, ?_⟩
  rintro (z | z) hz
  · have hz' : z ∈ X := by simpa using hz
    rw [inner_liftVec_inl, ← inner_liftPt, hval]
    simp only [liftHt, Sum.elim_inl, Finset.mem_insert, Finset.mem_singleton, Sum.inl.injEq,
      reduceCtorEq, or_false]
    refine ⟨fun h => ?_, fun h => (hε z hz').1 h⟩
    subst h
    simp only [A, Bc, hqx]
    field_simp
    ring
  · have hz' : z ∈ X := by simpa using hz
    rw [inner_liftVec_inr, ← inner_liftPt, hval]
    simp only [liftHt, Sum.elim_inr, Finset.mem_insert, Finset.mem_singleton, Sum.inr.injEq,
      reduceCtorEq, false_or]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · subst h
      simp only [A, Bc, hqy]
      field_simp
      ring
    · have := (hε z hz').2 h
      linarith

lemma diam_pos_of_not_collinear {X : Finset Plane} (hsep : IsSeparated X)
    (hcol : ¬ Collinear ℝ (X : Set Plane)) : 0 < diam X := by
  obtain ⟨p, hp, q, hq, hpq⟩ : ∃ p ∈ X, ∃ q ∈ X, p ≠ q := by
    by_contra h
    push_neg at h
    apply hcol
    rcases X.eq_empty_or_nonempty with hX | ⟨p, hp⟩
    · rw [hX, Finset.coe_empty]; exact collinear_empty ℝ _
    · refine (collinear_singleton (k := ℝ) p).subset fun q hq => ?_
      exact (h q hq p hp).symm ▸ rfl
  have h1 := hsep p hp q hq hpq
  have h2 := dist_le_diam hp hq
  linarith

/-- **The unperturbed witnesses.**  For some `ε > 0`, every upper ray, every upper unit pair and
every cross-cap diameter pair has a strict witness for the heights `1 + ε |x|²`. -/
lemma lifted_base_witnesses {X : Finset Plane} (hsep : IsSeparated X)
    (hcol : ¬ Collinear ℝ (X : Set Plane)) :
    ∃ ε > 0,
      (∀ x ∈ X, ∃ a, RegularFan.StrictWit (X.disjSum X) liftVec (liftHt ε) {Sum.inl x} a) ∧
      (∀ x ∈ X, ∀ y ∈ X, dist x y = 1 →
        ∃ a, RegularFan.StrictWit (X.disjSum X) liftVec (liftHt ε) {Sum.inl x, Sum.inl y} a) ∧
      (∀ x ∈ X, ∀ y ∈ X, dist x y = diam X →
        ∃ a, RegularFan.StrictWit (X.disjSum X) liftVec (liftHt ε) {Sum.inl x, Sum.inr y} a) := by
  set Mx := ∑ x ∈ X, (x 0 ^ 2 + x 1 ^ 2)
  have hMx : ∀ x ∈ X, x 0 ^ 2 + x 1 ^ 2 ≤ Mx := fun x hx =>
    Finset.single_le_sum (f := fun x : Plane => x 0 ^ 2 + x 1 ^ 2)
      (fun _ _ => by positivity) hx
  have hev1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε * (1 + Mx) < 1 := by
    refine Filter.Eventually.and self_mem_nhdsWithin ?_
    have h : Tendsto (fun ε : ℝ => ε * (1 + Mx)) (𝓝[>] 0) (𝓝 0) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds
      have : Continuous (fun ε : ℝ => ε * (1 + Mx)) := by fun_prop
      simpa using this.tendsto 0
    exact h.eventually_lt_const one_pos
  have hD := diam_pos_of_not_collinear hsep hcol
  have hev2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ x ∈ X, ∀ y ∈ X, dist x y = diam X →
      ∃ a, RegularFan.StrictWit (X.disjSum X) liftVec (liftHt ε) {Sum.inl x, Sum.inr y} a := by
    rw [Filter.eventually_all_finset]
    intro x hx
    rw [Filter.eventually_all_finset]
    intro y hy
    by_cases h : dist x y = diam X
    · filter_upwards [diam_wit_eventually hx hy h hD] with ε hε _
      exact hε
    · exact Filter.Eventually.of_forall fun _ h' => absurd h' h
  obtain ⟨ε, ⟨hε, hεM⟩, hdiam⟩ := (hev1.and hev2).exists
  have hMx0 : 0 ≤ Mx := Finset.sum_nonneg fun _ _ => by positivity
  have hsmall : ∀ c : Plane, c 0 ^ 2 + c 1 ^ 2 ≤ Mx → ε * (c 0 ^ 2 + c 1 ^ 2) < 1 := by
    intro c hc
    nlinarith
  refine ⟨ε, hε, fun x hx => ?_, fun x hx y hy hxy => ?_, hdiam⟩
  · refine ⟨_, circle_wit hε x 0 le_rfl (hsmall x (hMx x hx)) {Sum.inl x} (fun z hz => ?_)
      (by simp)⟩
    simp only [Finset.mem_singleton, Sum.inl.injEq]
    refine ⟨fun h => by subst h; ring, fun h => ?_⟩
    by_contra hle
    push_neg at hle
    exact h (coords_eq_of_sq_eq_zero (le_antisymm hle (by positivity)))
  · have hxy' : x ≠ y := by
      intro h; rw [h, dist_self] at hxy; exact zero_ne_one hxy
    have hd2 : (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 = 1 := by rw [← dist_sq_coords, hxy]; norm_num
    set c : Plane := !₂[(x 0 + y 0) / 2, (x 1 + y 1) / 2]
    have hc0 : c 0 = (x 0 + y 0) / 2 := by simp [c]
    have hc1 : c 1 = (x 1 + y 1) / 2 := by simp [c]
    have hcM : c 0 ^ 2 + c 1 ^ 2 ≤ Mx := by
      rw [hc0, hc1]
      nlinarith [hMx x hx, hMx y hy, sq_nonneg (x 0 - y 0), sq_nonneg (x 1 - y 1)]
    refine ⟨_, circle_wit hε c (1 / 4) (by norm_num) (hsmall c hcM) {Sum.inl x, Sum.inl y}
      (fun z hz => ?_) (by simp)⟩
    rw [hc0, hc1]
    simp only [Finset.mem_insert, Finset.mem_singleton, Sum.inl.injEq]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases h with rfl | rfl
      · linear_combination hd2 / 4
      · linear_combination hd2 / 4
    · push_neg at h
      have h1 := hsep z hz x hx h.1
      have h2 := hsep z hz y hy h.2
      have e1 := dist_sq_coords z x
      have e2 := dist_sq_coords z y
      have : 1 ≤ dist z x ^ 2 := by nlinarith
      have : 1 ≤ dist z y ^ 2 := by nlinarith
      nlinarith

/-- **The lifted fan** (§7.2).  For a separated non-collinear finite set `X`, there is a complete
simplicial fan on the lifted rays `±(x, 1)`, each of which lies in a cone of the fan, in which every
unit pair is an edge on both caps and every diameter pair is an edge across the caps.

Proof.  The fan is the regular fan `RegularFan.cones` of the lifted rays for the heights
`1 + ε |x|² + t ^ k(x)` (`k` injective, `ε > 0` small, then `t > 0` small and generic):
* for the heights `1 + ε |x|²`, every point of `X` and every unit pair has a strict witness given by
  an empty circle (`circle_wit`; the circle with a unit pair as diameter contains no other point
  of the separated set `X`), and every diameter pair has a strict witness obtained by perturbing
  the exposing functional `(x - y) · p - ((x - y) · (x + y)) z / 2` (`diam_wit_eventually`);
* strict witnesses survive the perturbation `t ^ k(x)` (`RegularFan.eventually_wit_perturb`), which
  makes the heights generic (`RegularFan.eventually_generic`), so that the regular fan is a
  complete simplicial fan (`RegularFan.isSimplicialFan`) and each witnessed set lies in one of its
  cones (`RegularFan.exists_cone_superset`). -/
theorem lifted_fan_exists {X : Finset Plane} (hsep : IsSeparated X)
    (hcol : ¬ Collinear ℝ (X : Set Plane)) :
    ∃ T : Finset (Finset (Plane ⊕ Plane)), IsSimplicialFan (X.disjSum X) liftVec T ∧
      (∀ i ∈ X.disjSum X, ∃ τ ∈ T, i ∈ τ) ∧
      (∀ x ∈ X, ∀ y ∈ X, dist x y = 1 →
        FanEdge T (Sum.inl x) (Sum.inl y) ∧ FanEdge T (Sum.inr x) (Sum.inr y)) ∧
      (∀ x ∈ X, ∀ y ∈ X, dist x y = diam X →
        FanEdge T (Sum.inl x) (Sum.inr y) ∧ FanEdge T (Sum.inr x) (Sum.inl y)) := by
  set S := X.disjSum X with hS
  obtain ⟨ε, hε, hray, hunit, hdiam⟩ := lifted_base_witnesses hsep hcol
  -- injective positive exponents for the generic perturbation
  obtain ⟨k, hk, hkinj⟩ : ∃ k : Plane ⊕ Plane → ℕ, (∀ m, 1 ≤ k m) ∧ Set.InjOn k (S : Set _) := by
    refine ⟨fun m => if h : m ∈ S then (S.equivFin ⟨m, h⟩ : ℕ) + 1 else 1,
      fun m => by dsimp only; split_ifs <;> omega, ?_⟩
    intro m hm m' hm' h
    simp only [Finset.mem_coe] at hm hm'
    simp only [hm, hm', dif_pos, add_left_inj] at h
    have := S.equivFin.injective (Fin.ext h)
    simpa using this
  -- the perturbed problem
  set Good : ℝ → Finset (Plane ⊕ Plane) → Prop := fun t B =>
    ∃ a, RegularFan.Feas S liftVec (fun m => liftHt ε m + t ^ k m) a ∧
      ∀ m ∈ B, m ∈ S → inner ℝ a (liftVec m) = liftHt ε m + t ^ k m with hGood
  have hperturb : ∀ {B : Finset (Plane ⊕ Plane)} {a0 : Space3},
      RegularFan.StrictWit S liftVec (liftHt ε) B a0 → RegularFan.HasDual liftVec B →
      ∀ᶠ t in 𝓝[>] (0 : ℝ), Good t B := fun hw hd => RegularFan.eventually_wit_perturb hk hw hd
  have hne : ∀ {x y : Plane}, x ≠ y → ∀ (i j : Plane ⊕ Plane),
      (i = Sum.inl x ∨ i = Sum.inr x) → (j = Sum.inl y ∨ j = Sum.inr y) →
      Sum.elim id id i ≠ Sum.elim id id j := by
    intro x y hxy i j hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> simpa using hxy
  have hev_ray : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ x ∈ X, Good t {Sum.inl x} ∧ Good t {Sum.inr x} := by
    rw [Filter.eventually_all_finset]
    intro x hx
    obtain ⟨a, ha⟩ := hray x hx
    refine (hperturb ha (RegularFan.hasDual_single (liftVec_dual_single _))).and ?_
    have hsw := strictWit_swap ha
    simp only [Finset.image_singleton, Sum.swap_inl] at hsw
    exact hperturb hsw (RegularFan.hasDual_single (liftVec_dual_single _))
  have hev_unit : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ x ∈ X, ∀ y ∈ X, dist x y = 1 →
      Good t {Sum.inl x, Sum.inl y} ∧ Good t {Sum.inr x, Sum.inr y} := by
    rw [Filter.eventually_all_finset]; intro x hx
    rw [Filter.eventually_all_finset]; intro y hy
    by_cases hxy : dist x y = 1
    · have hxy' : x ≠ y := by intro h; rw [h, dist_self] at hxy; exact zero_ne_one hxy
      obtain ⟨a, ha⟩ := hunit x hx y hy hxy
      have h1 := hperturb ha (lifted_hasDual_pair (hne hxy' _ _ (Or.inl rfl) (Or.inl rfl)))
      have hsw := strictWit_swap ha
      simp only [Finset.image_insert, Finset.image_singleton, Sum.swap_inl] at hsw
      have h2 := hperturb hsw (lifted_hasDual_pair (hne hxy' _ _ (Or.inr rfl) (Or.inr rfl)))
      filter_upwards [h1, h2] with t ht1 ht2 _
      exact ⟨ht1, ht2⟩
    · exact Filter.Eventually.of_forall fun _ h => absurd h hxy
  have hD := diam_pos_of_not_collinear hsep hcol
  have hev_diam : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ x ∈ X, ∀ y ∈ X, dist x y = diam X →
      Good t {Sum.inl x, Sum.inr y} := by
    rw [Filter.eventually_all_finset]; intro x hx
    rw [Filter.eventually_all_finset]; intro y hy
    by_cases hxy : dist x y = diam X
    · have hxy' : x ≠ y := by intro h; rw [h, dist_self] at hxy; linarith
      obtain ⟨a, ha⟩ := hdiam x hx y hy hxy
      filter_upwards [hperturb ha (lifted_hasDual_pair (hne hxy' _ _ (Or.inl rfl) (Or.inr rfl)))]
        with t ht _
      exact ht
    · exact Filter.Eventually.of_forall fun _ h => absurd h hxy
  obtain ⟨t, ht, hgen, hr, hu, hd⟩ := ((show ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t from self_mem_nhdsWithin).and ((RegularFan.eventually_generic (S := S) (v := liftVec) (u := liftHt ε)
      hk hkinj).and (hev_ray.and (hev_unit.and hev_diam)))).exists
  have ht0 : (0 : ℝ) < t := ht
  set u : Plane ⊕ Plane → ℝ := fun m => liftHt ε m + t ^ k m
  have hspan := liftVec_posSpan hcol
  have hu0 : ∀ m ∈ S, 0 ≤ u m := by
    intro m _
    have : 0 ≤ liftHt ε m := by
      rcases m with z | z <;> simp only [liftHt, Sum.elim_inl, Sum.elim_inr] <;> positivity
    have : 0 ≤ t ^ k m := by positivity
    simp only [u]; linarith
  have hcone : ∀ {B : Finset (Plane ⊕ Plane)}, B ⊆ S → Good t B →
      ∃ τ ∈ RegularFan.cones S liftVec u, B ⊆ τ :=
    fun hBS hB => RegularFan.exists_cone_of_active hgen hspan hBS hB
  have hedge : ∀ {i j : Plane ⊕ Plane}, i ∈ S → j ∈ S → i ≠ j → Good t {i, j} →
      FanEdge (RegularFan.cones S liftVec u) i j := by
    intro i j hi hj hij hB
    obtain ⟨τ, hτ, hBτ⟩ := hcone (Finset.insert_subset hi (Finset.singleton_subset_iff.2 hj)) hB
    exact ⟨hij, τ, hτ, hBτ (by simp), hBτ (by simp)⟩
  refine ⟨RegularFan.cones S liftVec u, RegularFan.isSimplicialFan hgen hspan hu0, ?_, ?_, ?_⟩
  · intro i hi
    have hB : Good t {i} := by
      rcases i with x | x
      · exact (hr x (by simpa [hS] using hi)).1
      · exact (hr x (by simpa [hS] using hi)).2
    obtain ⟨τ, hτ, hiτ⟩ := hcone (Finset.singleton_subset_iff.2 hi) hB
    exact ⟨τ, hτ, hiτ (Finset.mem_singleton_self i)⟩
  · intro x hx y hy hxy
    have hxy' : x ≠ y := by intro h; rw [h, dist_self] at hxy; exact zero_ne_one hxy
    obtain ⟨h1, h2⟩ := hu x hx y hy hxy
    exact ⟨hedge (by simpa [hS] using hx) (by simpa [hS] using hy) (by simpa using hxy') h1,
      hedge (by simpa [hS] using hx) (by simpa [hS] using hy) (by simpa using hxy') h2⟩
  · intro x hx y hy hxy
    refine ⟨hedge (by simpa [hS] using hx) (by simpa [hS] using hy) (by simp) (hd x hx y hy hxy),
      ?_⟩
    have h2 := hd y hy x hx (by rw [dist_comm]; exact hxy)
    have : ({Sum.inr x, Sum.inl y} : Finset (Plane ⊕ Plane)) = {Sum.inl y, Sum.inr x} :=
      Finset.pair_comm _ _
    exact hedge (by simpa [hS] using hx) (by simpa [hS] using hy) (by simp) (this ▸ h2)

/-- **The fan theorem for the lifted configuration**, derived from the abstract `fan_theorem`
and the existence of the lifted fan `lifted_fan_exists`. -/
theorem lifted_form_no_negative_plane_of_fan {X : Finset Plane} (hsep : IsSeparated X)
    (hcol : ¬ Collinear ℝ (X : Set Plane))
    (lam mu : Plane → Plane → ℝ) (hlam0 : ∀ x y, 0 ≤ lam x y) (hmu0 : ∀ x y, 0 ≤ mu x y)
    (hlams : ∀ x y, lam x y = lam y x) (hmus : ∀ x y, mu x y = mu y x)
    (hlam1 : ∀ x y, dist x y ≠ 1 → lam x y = 0) (hmuD : ∀ x y, dist x y ≠ diam X → mu x y = 0)
    (heq : ∀ x ∈ X, ∑ y ∈ X, lam x y • (x - y) = ∑ y ∈ X, mu x y • (x - y))
    (s₁ t₁ s₂ t₂ : Plane → ℝ) :
    ¬ ∀ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) →
      liftedForm X lam mu (fun x => a * s₁ x + b * s₂ x) (fun x => a * t₁ x + b * t₂ x) < 0 := by
  obtain ⟨T, hfan, hused, hunit, hdiam⟩ := lifted_fan_exists hsep hcol
  have hnp : NoNegativePlane (X.disjSum X) (liftedMatrix X lam mu) := by
    refine fan_theorem hfan hused (fun i _ => liftVec_ne_zero i)
      (fun i _ j _ c hc h => liftVec_ray i j c hc h) (liftedMatrix_symm X lam mu hlams hmus)
      (fun i _ j _ hij => liftedMatrix_offdiag_nonpos X lam mu hlam0 hmu0 i j hij) ?_
      (fun i hi => liftedMatrix_ker X lam mu heq i hi)
    intro i hi j hj hij hW
    rcases liftedMatrix_support X lam mu hlam1 hmuD i j hij hW with
      ⟨x, y, hxy, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨x, y, hxy, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact (hunit x (by simpa using hi) y (by simpa using hj) hxy).1
    · exact (hunit x (by simpa using hi) y (by simpa using hj) hxy).2
    · exact (hdiam x (by simpa using hi) y (by simpa using hj) hxy).1
    · exact (hdiam x (by simpa using hi) y (by simpa using hj) hxy).2
  intro hneg
  apply hnp (Sum.elim s₁ t₁) (Sum.elim s₂ t₂)
  intro a b hab
  have := hneg a b hab
  rw [liftedForm_eq_quadForm X lam mu hlams hmus] at this
  convert this using 2
  ext i
  cases i <;> rfl

end Erdos99
end

end LiftedFan

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `StressSign`
-/

section StressSign

/-!
# The stress-sign theorem (Verification Guide §7.2)

Let `X` be a finite planar set, `λ ≥ 0` a symmetric stress on its unit pairs and `μ ≥ 0` a
symmetric stress on its diameter pairs, in equilibrium.  The manuscript lifts `X` to the
centrally symmetric point set `v⁺ₓ = (x, 1)`, `v⁻ₓ = -(x, 1)` in `ℝ³` and considers the block matrix

  `W = [[B₀, -C_μ], [-C_μ, B₀]]`,   `B₀ = L(λ) - diag(C_μ 1)`,

whose quadratic form on a pair `(s, t)` of scalar functions (values at the upper and lower lifted
points) is `liftedForm X λ μ s t`.  The fan theorem (§7.3) says that `W` has no two-dimensional
negative-definite restriction (`lifted_form_no_negative_plane`).  It is derived in
`LiftedFan` from the abstract fan theorem (`FanTheorem`) (the lifted fan `lifted_fan_exists` and the facet-link step `polytope_facetLinks` are proved).

Here we carry out the algebraic reduction of §7.2: the vectors `(1, 1)` and `(s, -s)` are
`W`-orthogonal, `W(1, 1) = -4 ∑ μ < 0` and `W(s, -s) = 2 sᵀ Ω s` with `Ω = L(λ) - L(μ)`, so the
fan theorem forces `Ω` to be positive semidefinite (`stress_sign`).
-/

open scoped BigOperators Real

@[expose] public noncomputable section

open Classical

namespace Erdos99

/-- **The fan theorem for the lifted configuration** (§7.3 of the Verification Guide).  For a
separated, non-collinear finite set `X` and nonnegative symmetric equilibrium stresses `λ` (on unit
pairs) and `μ` (on diameter pairs), the lifted form `W` has no two-dimensional subspace on which it
is negative definite.

Proved from `lifted_form_no_negative_plane_of_fan` (`LiftedFan`): the lifted form is the
quadratic form of the block matrix `W`, which satisfies `W V = 0`, has nonpositive off-diagonal
entries supported on fan edges, and so falls under the abstract `fan_theorem`.  All inputs (the facet-link step
`polytope_facetLinks` of `FanTheorem`, the lifted fan `lifted_fan_exists` and the integration
step `fan_gradient_exists`) are proved. -/
theorem lifted_form_no_negative_plane {X : Finset Plane} (hsep : IsSeparated X)
    (hcol : ¬ Collinear ℝ (X : Set Plane))
    (lam mu : Plane → Plane → ℝ) (hlam0 : ∀ x y, 0 ≤ lam x y) (hmu0 : ∀ x y, 0 ≤ mu x y)
    (hlams : ∀ x y, lam x y = lam y x) (hmus : ∀ x y, mu x y = mu y x)
    (hlam1 : ∀ x y, dist x y ≠ 1 → lam x y = 0) (hmuD : ∀ x y, dist x y ≠ diam X → mu x y = 0)
    (heq : ∀ x ∈ X, ∑ y ∈ X, lam x y • (x - y) = ∑ y ∈ X, mu x y • (x - y))
    (s₁ t₁ s₂ t₂ : Plane → ℝ) :
    ¬ ∀ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) →
      liftedForm X lam mu (fun x => a * s₁ x + b * s₂ x) (fun x => a * t₁ x + b * t₂ x) < 0 :=
  lifted_form_no_negative_plane_of_fan hsep hcol lam mu hlam0 hmu0 hlams hmus hlam1 hmuD heq
    s₁ t₁ s₂ t₂

/-- The lifted form on `a (1, 1) + b (s, -s)`. -/
lemma liftedForm_one_anti (X : Finset Plane) (lam mu : Plane → Plane → ℝ)
    (hmus : ∀ x y, mu x y = mu y x) (s : Plane → ℝ) (a b : ℝ) :
    liftedForm X lam mu (fun x => a * 1 + b * s x) (fun x => a * 1 + b * (-s x)) =
      b ^ 2 * (∑ x ∈ X, ∑ y ∈ X, lam x y * (s x - s y) ^ 2 -
        ∑ x ∈ X, ∑ y ∈ X, mu x y * (s x - s y) ^ 2) -
      4 * a ^ 2 * ∑ x ∈ X, ∑ y ∈ X, mu x y := by
  have hanti : ∑ x ∈ X, ∑ y ∈ X, mu x y * (s x - s y) = 0 := by
    have h : ∑ x ∈ X, ∑ y ∈ X, mu x y * (s x - s y) =
        -∑ x ∈ X, ∑ y ∈ X, mu x y * (s x - s y) := by
      conv_rhs => rw [Finset.sum_comm]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [hmus]; ring
    linarith
  have e1 : ∀ x y, (a * 1 + b * s x - (a * 1 + b * s y)) ^ 2 +
      (a * 1 + b * -s x - (a * 1 + b * -s y)) ^ 2 = 2 * (b ^ 2 * (s x - s y) ^ 2) := by
    intro x y; ring
  have e2 : ∀ x y, (a * 1 + b * s x + (a * 1 + b * -s y)) ^ 2 =
      4 * a ^ 2 + 4 * a * b * (s x - s y) + b ^ 2 * (s x - s y) ^ 2 := by
    intro x y; ring
  have key : liftedForm X lam mu (fun x => a * 1 + b * s x) (fun x => a * 1 + b * (-s x)) =
      ∑ x ∈ X, ∑ y ∈ X, (b ^ 2 * (lam x y * (s x - s y) ^ 2 - mu x y * (s x - s y) ^ 2) -
        4 * a ^ 2 * mu x y - 4 * a * b * (mu x y * (s x - s y))) := by
    unfold liftedForm
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [e1, e2]; ring
  rw [key]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, hanti, mul_zero, sub_zero]

/-- **Stress sign** (§7.2–§7.3 of the Verification Guide; Lemma 2.4 of the manuscript).  Let `X`
be a separated, non-collinear finite set.  Let `λ ≥ 0` be a symmetric stress supported on unit
pairs and `μ ≥ 0` a symmetric stress supported on diameter pairs, in equilibrium at every point:
`∑_y λ(x,y)(x - y) = ∑_y μ(x,y)(x - y)`.  Then the stress form `Ω = L(λ) - L(μ)` is positive
semidefinite.

Proved here from the fan theorem for the lift, `lifted_form_no_negative_plane` (open). -/
theorem stress_sign {X : Finset Plane} (hsep : IsSeparated X)
    (hcol : ¬ Collinear ℝ (X : Set Plane))
    (lam mu : Plane → Plane → ℝ) (hlam0 : ∀ x y, 0 ≤ lam x y) (hmu0 : ∀ x y, 0 ≤ mu x y)
    (hlams : ∀ x y, lam x y = lam y x) (hmus : ∀ x y, mu x y = mu y x)
    (hlam1 : ∀ x y, dist x y ≠ 1 → lam x y = 0) (hmuD : ∀ x y, dist x y ≠ diam X → mu x y = 0)
    (heq : ∀ x ∈ X, ∑ y ∈ X, lam x y • (x - y) = ∑ y ∈ X, mu x y • (x - y))
    (z : Plane → Plane) :
    ∑ x ∈ X, ∑ y ∈ X, mu x y * ‖z x - z y‖ ^ 2 ≤ ∑ x ∈ X, ∑ y ∈ X, lam x y * ‖z x - z y‖ ^ 2 := by
  -- reduce to one coordinate
  have hnorm : ∀ x y : Plane, ‖z x - z y‖ ^ 2 = (z x 0 - z y 0) ^ 2 + (z x 1 - z y 1) ^ 2 := by
    intro x y
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _),
      Fin.sum_univ_two]
    simp [sq_abs]
  have hcoord : ∀ k : Fin 2,
      ∑ x ∈ X, ∑ y ∈ X, mu x y * (z x k - z y k) ^ 2 ≤
        ∑ x ∈ X, ∑ y ∈ X, lam x y * (z x k - z y k) ^ 2 := by
    intro k
    set s : Plane → ℝ := fun x => z x k
    by_contra hlt
    push_neg at hlt
    set M := ∑ x ∈ X, ∑ y ∈ X, mu x y
    have hM : 0 < M := by
      rcases (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => hmu0 x y :
          0 ≤ M).eq_or_lt with h0 | h0
      · exfalso
        have hz : ∀ x ∈ X, ∀ y ∈ X, mu x y = 0 := by
          intro x hx y hy
          have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun x _ =>
            Finset.sum_nonneg fun y _ => hmu0 x y).1 h0.symm x hx
          exact (Finset.sum_eq_zero_iff_of_nonneg fun y _ => hmu0 x y).1 h1 y hy
        have : ∑ x ∈ X, ∑ y ∈ X, mu x y * (s x - s y) ^ 2 = 0 :=
          Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun y hy => by rw [hz x hx y hy]; ring
        have hl : 0 ≤ ∑ x ∈ X, ∑ y ∈ X, lam x y * (s x - s y) ^ 2 :=
          Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
            mul_nonneg (hlam0 x y) (sq_nonneg _)
        simp only [s] at this hl
        linarith
      · exact h0
    apply lifted_form_no_negative_plane hsep hcol lam mu hlam0 hmu0 hlams hmus hlam1 hmuD heq
      (fun _ => 1) (fun _ => 1) s (fun x => -s x)
    intro a b hab
    rw [liftedForm_one_anti X lam mu hmus s a b]
    rcases hab with ha | hb
    · by_cases hb : b = 0
      · subst hb
        have : 0 < a ^ 2 := by positivity
        nlinarith
      · have : 0 < b ^ 2 := by positivity
        have : 0 ≤ a ^ 2 := sq_nonneg a
        nlinarith
    · have : 0 < b ^ 2 := by positivity
      have : 0 ≤ a ^ 2 := sq_nonneg a
      nlinarith
  have h0 := hcoord 0
  have h1 := hcoord 1
  simp only [hnorm, mul_add, Finset.sum_add_distrib]
  linarith

end Erdos99
end

end StressSign

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `FirstOrderLocking`
-/

section FirstOrderLocking

/-!
# WP4: first-order locking (Verification Guide §7)

Let `X` be an optimal `n`-point set (minimal diameter `D` subject to mutual distances `≥ 1`),
under finite multiplicity.  A velocity `v` is *first-order feasible* if it does not shorten unit
pairs and does not lengthen diameter pairs:
`⟨x - y, v x - v y⟩ ≥ 0` when `|x - y| = 1`, and `⟨x - y, v x - v y⟩ ≤ 0` when `|x - y| = D`.
First-order locking says that every such velocity is trivial.

The proof is split into four steps.

1. `stress_sign` (§7.2, `StressSign`): for a separated, non-collinear finite set, every
   nonnegative equilibrium stress `λ` on unit pairs balanced by `μ` on diameter pairs has a
   positive semidefinite stress form `∑ λ |z x - z y|² - ∑ μ |z x - z y|² ≥ 0`.  It is proved
   from the fan theorem for the lifted configuration, `lifted_form_no_negative_plane` (§7.3,
   **open**: the fan theorem / volume-Hessian argument of the manuscript).  This is the only
   open input of first-order locking.
2. `secondOrder_extension` (§7.4): from the stress sign, via Farkas' lemma, Hoffman's bound and
   a contraction (`Locking.exists_secondOrder_solution`), every first-order feasible `v` is the
   direction of exactly feasible displacements `z(t) = t v + O(t²)`.
3. `distances_preserved_of_small` (§7.1, local isolation): under finite multiplicity, a small
   displacement of an optimal set that keeps unit pairs at least `1` apart and diameter pairs at
   most `D` apart preserves *all* distances.
4. `trivial_of_rigid_family` : if `t v + O(t²)` is distance-preserving for all small `t > 0`,
   then `v` is an infinitesimal isometry of `X`, hence trivial since `X` is not collinear.

`first_order_locking_of` combines them.
-/

open scoped BigOperators Real

@[expose] public noncomputable section

open Classical

namespace Erdos99


namespace Locking

/-- The planar cross product `d × e`. -/
def cross2 (d e : Plane) : ℝ := d 0 * e 1 - d 1 * e 0

lemma inner_plane (d e : Plane) : inner ℝ d e = d 0 * e 0 + d 1 * e 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]; ring

lemma cross2_sub_right (a b c : Plane) : cross2 a (b - c) = cross2 a b - cross2 a c := by
  simp [cross2]; ring

lemma cross2_self (a : Plane) : cross2 a a = 0 := by simp [cross2]; ring

lemma cross2_comm (a b : Plane) : cross2 a b = - cross2 b a := by simp [cross2]; ring

lemma cross2_smul_left (r : ℝ) (a b : Plane) : cross2 (r • a) b = r * cross2 a b := by
  simp [cross2]; ring

lemma cross2_rot (d : Plane) : cross2 d (rot d) = d 0 ^ 2 + d 1 ^ 2 := by
  simp [cross2, rot]; ring

lemma inner_rot_rot (d : Plane) : inner ℝ (rot d) (rot d) = d 0 ^ 2 + d 1 ^ 2 := by
  rw [inner_plane]; simp [rot]; ring

lemma rot_sub' (x y : Plane) : rot (x - y) = rot x - rot y := by
  ext i; fin_cases i <;> simp [rot]; ring

/-- A vector orthogonal to two non-parallel vectors vanishes. -/
lemma eq_zero_of_inner_eq_zero_two {d1 d2 u : Plane} (h : cross2 d1 d2 ≠ 0)
    (h1 : inner ℝ d1 u = 0) (h2 : inner ℝ d2 u = 0) : u = 0 := by
  rw [inner_plane] at h1 h2
  unfold cross2 at h
  have e0 : u 0 * (d1 0 * d2 1 - d1 1 * d2 0) = 0 := by linear_combination d2 1 * h1 - d1 1 * h2
  have e1 : u 1 * (d1 0 * d2 1 - d1 1 * d2 0) = 0 := by linear_combination d1 0 * h2 - d2 0 * h1
  ext i; fin_cases i
  · simpa [h] using e0
  · simpa [h] using e1

lemma exists_smul_of_cross_eq_zero {d e : Plane} (hd : d ≠ 0) (h : cross2 d e = 0) :
    ∃ r : ℝ, e = r • d := by
  have hn : d 0 ^ 2 + d 1 ^ 2 ≠ 0 := by
    intro h0
    apply hd; ext i; fin_cases i <;> simp <;> nlinarith [sq_nonneg (d 0), sq_nonneg (d 1)]
  refine ⟨(e 0 * d 0 + e 1 * d 1) / (d 0 ^ 2 + d 1 ^ 2), ?_⟩
  unfold cross2 at h
  ext i; fin_cases i
  · simp; field_simp; linear_combination (-(d 1)) * h
  · simp; field_simp; linear_combination (d 0) * h

lemma exists_cross_ne_zero {X : Finset Plane} (hcol : ¬ Collinear ℝ (X : Set Plane)) {a p : Plane}
    (ha : a ∈ X) (hap : a ≠ p) : ∃ c ∈ X, cross2 (p - a) (c - a) ≠ 0 := by
  by_contra h
  push_neg at h
  apply hcol
  rw [collinear_iff_of_mem (p₀ := a) (by exact_mod_cast ha)]
  refine ⟨p - a, fun c hc => ?_⟩
  obtain ⟨r, hr⟩ := exists_smul_of_cross_eq_zero (sub_ne_zero.2 hap.symm) (h c hc)
  exact ⟨r, by rw [← hr, vadd_eq_add, sub_add_cancel]⟩

lemma exists_two_of_not_collinear {X : Finset Plane} (hcol : ¬ Collinear ℝ (X : Set Plane)) :
    ∃ a ∈ X, ∃ p ∈ X, a ≠ p := by
  by_contra h
  push_neg at h
  apply hcol
  rcases X.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · simp [collinear_empty]
  · refine (collinear_singleton (k := ℝ) a).subset fun p hp => ?_
    exact (h a ha p hp).symm

lemma eq_zero_of_abs_le_mul {c K δ : ℝ} (hδ : 0 < δ) (h : ∀ t ∈ Set.Ioo 0 δ, |c| ≤ K * t) :
    c = 0 := by
  by_contra hc
  have hc' : 0 < |c| := abs_pos.2 hc
  have hK : 0 < K := by
    have := h (δ / 2) ⟨by linarith, by linarith⟩
    by_contra hK; push_neg at hK; nlinarith
  set t := min (δ / 2) (|c| / (2 * K))
  have ht : t ∈ Set.Ioo 0 δ := ⟨lt_min (by linarith) (by positivity),
    (min_le_left _ _).trans_lt (by linarith)⟩
  have h1 := h t ht
  have h2 : t ≤ |c| / (2 * K) := min_le_right _ _
  rw [le_div_iff₀ (by positivity)] at h2
  nlinarith

lemma exists_pos_le_of_finite' {S : Set ℝ} (hS : S.Finite) (hpos : ∀ s ∈ S, 0 < s) :
    ∃ ε > 0, ∀ s ∈ S, ε ≤ s := by
  rcases hS.toFinset.eq_empty_or_nonempty with h | h
  · refine ⟨1, one_pos, fun s hs => ?_⟩
    have : s ∈ hS.toFinset := hS.mem_toFinset.2 hs
    rw [h] at this; simp at this
  · refine ⟨hS.toFinset.min' h, hpos _ (hS.mem_toFinset.1 (Finset.min'_mem _ h)),
      fun s hs => Finset.min'_le _ _ (hS.mem_toFinset.2 hs)⟩

/-- Under finite multiplicity, the labelled distance patterns of optimal sets indexed by the
points of `X` form a finite set. -/
lemma finite_distance_patterns {n : ℕ} (hfm : numOptimalClasses n < ⊤) (X : Finset Plane) :
    ∃ F : Set (X → X → ℝ), F.Finite ∧ ∀ g : X → Plane, IsOptimal n (Finset.univ.image g) →
      (fun x y => dist (g x) (g y)) ∈ F := by
  set K := {C : Set (Finset Plane) |
    ∃ X, IsOptimal n X ∧ C = {Y | IsOptimal n Y ∧ Congruent X Y}}
  have hK : K.Finite := Set.encard_lt_top_iff.1 hfm
  have hrep : ∀ C ∈ K, ∃ R : Finset Plane, R ∈ C := by
    rintro C ⟨Y, hY, rfl⟩
    exact ⟨Y, hY, congruent_refl Y⟩
  choose! R hR using hrep
  let F : Set (X → X → ℝ) := ⋃ C ∈ K,
    Set.range (fun σ : X → R C => fun x y => dist (σ x : Plane) (σ y))
  refine ⟨F, hK.biUnion fun C _ => Set.finite_range _, fun g hg => ?_⟩
  set Y := Finset.univ.image g
  set C := {Y' | IsOptimal n Y' ∧ Congruent Y Y'}
  have hC : C ∈ K := ⟨Y, hg, rfl⟩
  obtain ⟨-, e, he⟩ := hR C hC
  have hmem : ∀ x : X, e (g x) ∈ R C := by
    intro x; rw [← he]; exact Finset.mem_image.2 ⟨g x, Finset.mem_image.2 ⟨x, by simp, rfl⟩, rfl⟩
  refine Set.mem_biUnion hC ⟨fun x => ⟨e (g x), hmem x⟩, ?_⟩
  funext x y
  simp [e.dist_eq]

lemma dist_add_sub_le (p q a b : Plane) : |dist (p + a) (q + b) - dist p q| ≤ ‖a‖ + ‖b‖ := by
  simpa using dist_move_le p q a b 1 zero_le_one

end Locking

open Locking

/-- `v` extends to second order: for all small `t > 0` there is a displacement `z = t v + O(t²)`
of `X` that keeps unit pairs at least `1` apart and diameter pairs at most `diam X` apart. -/
def HasSecondOrderExtension (X : Finset Plane) (v : Plane → Plane) : Prop :=
  ∃ M δ : ℝ, 0 < δ ∧ ∀ t ∈ Set.Ioo 0 δ, ∃ z : Plane → Plane,
    (∀ x ∈ X, ‖z x - t • v x‖ ≤ M * t ^ 2) ∧
    (∀ x ∈ X, ∀ y ∈ X, dist x y = 1 → 1 ≤ dist (x + z x) (y + z y)) ∧
    (∀ x ∈ X, ∀ y ∈ X, dist x y = diam X → dist (x + z x) (y + z y) ≤ diam X)

namespace Locking

section ActiveRows

variable {X : Finset Plane}

/-- The rigidity row `u ↦ c ⟨x - y, u x - u y⟩`. -/
def rowLin (c : ℝ) (x y : X) : (X → Plane) →ₗ[ℝ] ℝ where
  toFun u := c * inner ℝ ((x : Plane) - y) (u x - u y)
  map_add' u u' := by simp only [Pi.add_apply]; rw [add_sub_add_comm, inner_add_right]; ring
  map_smul' r u := by
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    rw [← smul_sub, inner_smul_right]; ring

lemma rowLin_apply (c : ℝ) (x y : X) (u : X → Plane) :
    rowLin c x y u = c * inner ℝ ((x : Plane) - y) (u x - u y) := rfl

/-- The quadratic part `(u, u') ↦ c ⟨u x - u y, u' x - u' y⟩`. -/
def rowBil (c : ℝ) (x y : X) : (X → Plane) →L[ℝ] (X → Plane) →L[ℝ] ℝ :=
  c • (innerSL ℝ (E := Plane)).bilinearComp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : X => Plane) x -
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : X => Plane) y)
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : X => Plane) x -
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : X => Plane) y)

lemma rowBil_apply (c : ℝ) (x y : X) (u u' : X → Plane) :
    rowBil c x y u u' = c * inner ℝ (u x - u y) (u' x - u' y) := by
  simp [rowBil, inner_sub_left]

/-- The rows of the active constraints: unit pairs (`inl`) and diameter pairs (`inr`). -/
def actA (X : Finset Plane) : (X × X) ⊕ (X × X) → (X → Plane) →ₗ[ℝ] ℝ
  | Sum.inl p => rowLin (if dist (p.1 : Plane) p.2 = 1 then 2 else 0) p.1 p.2
  | Sum.inr p => rowLin (if dist (p.1 : Plane) p.2 = diam X then -2 else 0) p.1 p.2

def actB (X : Finset Plane) : (X × X) ⊕ (X × X) → (X → Plane) →L[ℝ] (X → Plane) →L[ℝ] ℝ
  | Sum.inl p => rowBil (if dist (p.1 : Plane) p.2 = 1 then 1 else 0) p.1 p.2
  | Sum.inr p => rowBil (if dist (p.1 : Plane) p.2 = diam X then -1 else 0) p.1 p.2

lemma dist_sq_expand (x y a b : Plane) :
    dist (x + a) (y + b) ^ 2 = dist x y ^ 2 + 2 * inner ℝ (x - y) (a - b) + ‖a - b‖ ^ 2 := by
  rw [dist_eq_norm, dist_eq_norm, show x + a - (y + b) = (x - y) + (a - b) by abel,
    norm_add_sq_real]

lemma actA_add_actB_inl (p : X × X) (u : X → Plane) :
    actA X (Sum.inl p) u + actB X (Sum.inl p) u u =
      (if dist (p.1 : Plane) p.2 = 1 then 1 else 0) *
        (dist ((p.1 : Plane) + u p.1) (p.2 + u p.2) ^ 2 - dist (p.1 : Plane) p.2 ^ 2) := by
  simp only [actA, actB, rowLin_apply, rowBil_apply, dist_sq_expand, real_inner_self_eq_norm_sq]
  split_ifs <;> ring

lemma actA_add_actB_inr (p : X × X) (u : X → Plane) :
    actA X (Sum.inr p) u + actB X (Sum.inr p) u u =
      (if dist (p.1 : Plane) p.2 = diam X then 1 else 0) *
        (dist (p.1 : Plane) p.2 ^ 2 - dist ((p.1 : Plane) + u p.1) (p.2 + u p.2) ^ 2) := by
  simp only [actA, actB, rowLin_apply, rowBil_apply, dist_sq_expand, real_inner_self_eq_norm_sq]
  split_ifs <;> ring

/-- Extend a function on pairs of points of `X` by zero. -/
def ext2 (f : X × X → ℝ) : Plane → Plane → ℝ :=
  fun p q => if h : p ∈ X ∧ q ∈ X then f (⟨p, h.1⟩, ⟨q, h.2⟩) else 0

lemma ext2_coe (f : X × X → ℝ) (i : X × X) : ext2 f i.1 i.2 = f i := by
  simp [ext2]

lemma sum_pairs {M : Type*} [AddCommMonoid M] (H : Plane → Plane → M) :
    ∑ i : X × X, H i.1 i.2 = ∑ p ∈ X, ∑ q ∈ X, H p q := by
  rw [Fintype.sum_prod_type, ← Finset.sum_coe_sort X]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_coe_sort X (H p)

lemma sum_pairs_inner (c : Plane → Plane → ℝ) {x0 : Plane} (hx0 : x0 ∈ X) (w : Plane) :
    ∑ p ∈ X, ∑ q ∈ X, c p q * inner ℝ (p - q) ((if p = x0 then w else 0) - if q = x0 then w else 0)
      = inner ℝ (∑ q ∈ X, (c x0 q + c q x0) • (x0 - q)) w := by
  simp only [inner_sub_right, mul_sub, Finset.sum_sub_distrib]
  have h1 : ∑ p ∈ X, ∑ q ∈ X, c p q * inner ℝ (p - q) (if p = x0 then w else 0) =
      ∑ q ∈ X, c x0 q * inner ℝ (x0 - q) w := by
    rw [Finset.sum_eq_single x0 (fun p _ hp => by simp [hp]) (fun h => absurd hx0 h)]
    simp
  have h2 : ∑ p ∈ X, ∑ q ∈ X, c p q * inner ℝ (p - q) (if q = x0 then w else 0) =
      ∑ q ∈ X, c q x0 * inner ℝ (q - x0) w := by
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_eq_single x0 (fun q _ hq => by simp [hq]) (fun h => absurd hx0 h)]
    simp
  rw [h1, h2, sum_inner, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [inner_smul_left, show q - x0 = -(x0 - q) by abel, inner_neg_left]
  simp; ring

end ActiveRows

/-- The stress-sign theorem, transported to the active rows. -/
lemma act_stress {X : Finset Plane} (hsep : IsSeparated X) (hcol : ¬ Collinear ℝ (X : Set Plane))
    (η : (X × X) ⊕ (X × X) → ℝ) (hη : ∀ i, 0 ≤ η i) (h0 : ∑ i, η i • actA X i = 0)
    (z : X → Plane) : 0 ≤ ∑ i, η i * actB X i z z := by
  set c1 : Plane → Plane → ℝ := fun p q =>
    if dist p q = 1 then ext2 (fun i : X × X => η (Sum.inl i)) p q else 0
  set c2 : Plane → Plane → ℝ := fun p q =>
    if dist p q = diam X then ext2 (fun i : X × X => η (Sum.inr i)) p q else 0
  have hc1 : ∀ i : X × X, c1 i.1 i.2 =
      if dist (i.1 : Plane) i.2 = 1 then η (Sum.inl i) else 0 := fun i => by
    simp only [c1, ext2_coe]
  have hc2 : ∀ i : X × X, c2 i.1 i.2 =
      if dist (i.1 : Plane) i.2 = diam X then η (Sum.inr i) else 0 := fun i => by
    simp only [c2, ext2_coe]
  have hc1n : ∀ p q, 0 ≤ c1 p q := fun p q => by
    simp only [c1, ext2]; split_ifs <;> simp [hη]
  have hc2n : ∀ p q, 0 ≤ c2 p q := fun p q => by
    simp only [c2, ext2]; split_ifs <;> simp [hη]
  set lam : Plane → Plane → ℝ := fun p q => c1 p q + c1 q p
  set mu : Plane → Plane → ℝ := fun p q => c2 p q + c2 q p
  -- equilibrium
  have heq : ∀ x ∈ X, ∑ y ∈ X, lam x y • (x - y) = ∑ y ∈ X, mu x y • (x - y) := by
    intro x0 hx0
    refine ext_inner_right ℝ fun w => ?_
    set u : X → Plane := fun x => if (x : Plane) = x0 then w else 0
    have hu : ∑ i, η i * actA X i u = 0 := by
      have := congrArg (fun f : (X → Plane) →ₗ[ℝ] ℝ => f u) h0
      simpa [LinearMap.sum_apply] using this
    rw [Fintype.sum_sum_type] at hu
    simp only [actA, rowLin_apply] at hu
    have k1 : ∑ i : X × X, η (Sum.inl i) * ((if dist (i.1 : Plane) i.2 = 1 then 2 else 0) *
        inner ℝ ((i.1 : Plane) - i.2) (u i.1 - u i.2)) =
        2 * inner ℝ (∑ y ∈ X, lam x0 y • (x0 - y)) w := by
      have hp := sum_pairs (X := X) (fun p q => (2 * c1 p q) *
            inner ℝ (p - q) ((if p = x0 then w else 0) - if q = x0 then w else 0))
      beta_reduce at hp
      calc _ = ∑ i : X × X, (2 * c1 i.1 i.2) *
            inner ℝ ((i.1 : Plane) - i.2)
              ((if (i.1 : Plane) = x0 then w else 0) - if (i.2 : Plane) = x0 then w else 0) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            simp only [hc1, u]; split_ifs <;> ring
        _ = _ := by
            rw [hp, sum_pairs_inner _ hx0, ← real_inner_smul_left, Finset.smul_sum]
            congr 1
            refine Finset.sum_congr rfl fun q _ => ?_
            rw [smul_smul]; congr 1; simp only [lam]; ring
    have k2 : ∑ i : X × X, η (Sum.inr i) *
        ((if dist (i.1 : Plane) i.2 = diam X then -2 else 0) *
        inner ℝ ((i.1 : Plane) - i.2) (u i.1 - u i.2)) =
        -2 * inner ℝ (∑ y ∈ X, mu x0 y • (x0 - y)) w := by
      have hp := sum_pairs (X := X) (fun p q => (-2 * c2 p q) *
            inner ℝ (p - q) ((if p = x0 then w else 0) - if q = x0 then w else 0))
      beta_reduce at hp
      calc _ = ∑ i : X × X, (-2 * c2 i.1 i.2) *
            inner ℝ ((i.1 : Plane) - i.2)
              ((if (i.1 : Plane) = x0 then w else 0) - if (i.2 : Plane) = x0 then w else 0) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            simp only [hc2, u]; split_ifs <;> ring
        _ = _ := by
            rw [hp, sum_pairs_inner _ hx0, ← real_inner_smul_left, Finset.smul_sum]
            congr 1
            refine Finset.sum_congr rfl fun q _ => ?_
            rw [smul_smul]; congr 1; simp only [mu]; ring
    rw [k1, k2] at hu
    linarith
  set z' := extV X z
  have hz' : ∀ i : X, z' i = z i := fun i => extV_mem X z i.2
  have hS := stress_sign hsep hcol lam mu (fun p q => add_nonneg (hc1n p q) (hc1n q p))
    (fun p q => add_nonneg (hc2n p q) (hc2n q p)) (fun p q => add_comm _ _)
    (fun p q => add_comm _ _)
    (fun p q h => by simp only [lam, c1, dist_comm q p, if_neg h, add_zero])
    (fun p q h => by simp only [mu, c2, dist_comm q p, if_neg h, add_zero]) heq z'
  set N : Plane → Plane → ℝ := fun p q => ‖z' p - z' q‖ ^ 2
  have hNs : ∀ p q, N p q = N q p := fun p q => by simp only [N]; rw [norm_sub_rev]
  have hsym : ∀ c : Plane → Plane → ℝ, ∑ p ∈ X, ∑ q ∈ X, (c p q + c q p) * N p q =
      2 * ∑ p ∈ X, ∑ q ∈ X, c p q * N p q := by
    intro c
    simp only [add_mul, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun p q => c q p * N p q)]
    simp only [hNs]; ring
  have hB : ∑ i, η i * actB X i z z =
      ∑ p ∈ X, ∑ q ∈ X, c1 p q * N p q - ∑ p ∈ X, ∑ q ∈ X, c2 p q * N p q := by
    simp only [Fintype.sum_sum_type, actB, rowBil_apply, real_inner_self_eq_norm_sq]
    rw [sub_eq_add_neg, ← sum_pairs (fun p q => c1 p q * N p q),
      ← sum_pairs (fun p q => c2 p q * N p q), ← Finset.sum_neg_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hc1, N, hz']; split_ifs <;> ring
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hc2, N, hz']; split_ifs <;> ring
  have h1 := hsym c1
  have h2 := hsym c2
  simp only [lam, mu] at hS
  rw [hB]
  change ∑ p ∈ X, ∑ q ∈ X, (c2 p q + c2 q p) * N p q ≤
    ∑ p ∈ X, ∑ q ∈ X, (c1 p q + c1 q p) * N p q at hS
  linarith

end Locking

/-- **Second-order extension** (§7.4).  For a separated, non-collinear finite set, every
first-order feasible velocity extends to second order. -/
theorem secondOrder_extension {X : Finset Plane} (hsep : IsSeparated X)
    (hcol : ¬ Collinear ℝ (X : Set Plane)) (v : Plane → Plane)
    (hU : ∀ x ∈ X, ∀ y ∈ X, dist x y = 1 → 0 ≤ inner ℝ (x - y) (v x - v y))
    (hT : ∀ x ∈ X, ∀ y ∈ X, dist x y = diam X → inner ℝ (x - y) (v x - v y) ≤ 0) :
    HasSecondOrderExtension X v := by
  set v' : X → Plane := fun x => v x
  have hv : ∀ i, 0 ≤ actA X i v' := by
    rintro (⟨x, y⟩ | ⟨x, y⟩)
    · simp only [actA, rowLin_apply, v']
      split_ifs with h
      · have := hU x x.2 y y.2 h; linarith
      · simp
    · simp only [actA, rowLin_apply, v']
      split_ifs with h
      · have := hT x x.2 y y.2 h; linarith
      · simp
  obtain ⟨M, δ, hδ, hsol⟩ := exists_secondOrder_solution (actA X) (actB X)
    (fun η hη h0 z => act_stress hsep hcol η hη h0 z) v' hv
  refine ⟨M, δ, hδ, fun t ht => ?_⟩
  obtain ⟨z, hz, hfeas⟩ := hsol t ht
  refine ⟨extV X z, fun x hx => ?_, fun x hx y hy hxy => ?_, fun x hx y hy hxy => ?_⟩
  · rw [extV_mem X z hx]
    calc ‖z ⟨x, hx⟩ - t • v x‖ = ‖(z - t • v') ⟨x, hx⟩‖ := rfl
      _ ≤ ‖z - t • v'‖ := norm_le_pi_norm _ _
      _ ≤ M * t ^ 2 := hz
  · have h := hfeas (Sum.inl (⟨x, hx⟩, ⟨y, hy⟩))
    rw [actA_add_actB_inl] at h
    simp only [hxy, if_true, one_mul, one_pow] at h
    rw [extV_mem X z hx, extV_mem X z hy]
    nlinarith [dist_nonneg (x := x + z ⟨x, hx⟩) (y := y + z ⟨y, hy⟩)]
  · have h := hfeas (Sum.inr (⟨x, hx⟩, ⟨y, hy⟩))
    rw [actA_add_actB_inr] at h
    simp only [hxy, if_true, one_mul] at h
    rw [extV_mem X z hx, extV_mem X z hy]
    have hD : 0 ≤ diam X := by rw [← hxy]; exact dist_nonneg
    nlinarith [dist_nonneg (x := x + z ⟨x, hx⟩) (y := y + z ⟨y, hy⟩)]


/-- **Local isolation** (§7.1).  Under finite multiplicity, every sufficiently small displacement
of an optimal set which keeps unit pairs at least `1` apart and diameter pairs at most `diam X`
apart preserves all mutual distances. -/
theorem distances_preserved_of_small {n : ℕ} (hn : 2 ≤ n) (hfm : numOptimalClasses n < ⊤)
    {X : Finset Plane} (hX : IsOptimal n X) :
    ∃ ε > 0, ∀ z : Plane → Plane, (∀ x ∈ X, ‖z x‖ < ε) →
      (∀ x ∈ X, ∀ y ∈ X, dist x y = 1 → 1 ≤ dist (x + z x) (y + z y)) →
      (∀ x ∈ X, ∀ y ∈ X, dist x y = diam X → dist (x + z x) (y + z y) ≤ diam X) →
      ∀ x ∈ X, ∀ y ∈ X, dist (x + z x) (y + z y) = dist x y := by
  set D := diam X
  have hD : 0 < D := hX.diam_pos hn
  haveI : Nonempty X := by
    obtain ⟨x, hx⟩ := Finset.card_pos.1 (by rw [hX.1.1]; omega : 0 < X.card)
    exact ⟨⟨x, hx⟩⟩
  obtain ⟨γ1, hγ1, hg1⟩ := exists_gap X 1
  obtain ⟨γ2, hγ2, hg2⟩ := exists_gap X D
  obtain ⟨F, hF, hFmem⟩ := finite_distance_patterns hfm X
  set d0 : X → X → ℝ := fun x y => dist (x : Plane) y
  have hsep : ∀ f ∈ F, f ≠ d0 → ∃ x y : X, f x y ≠ d0 x y := by
    intro f _ hf
    by_contra h; push_neg at h; exact hf (funext fun x => funext fun y => h x y)
  choose! px py hpxy using hsep
  set S : Set ℝ := (fun f => |f (px f) (py f) - d0 (px f) (py f)|) '' {f ∈ F | f ≠ d0}
  have hS : S.Finite := (hF.subset fun f hf => hf.1).image _
  obtain ⟨η, hη, hηS⟩ := exists_pos_le_of_finite' hS (by
    rintro _ ⟨f, hf, rfl⟩; exact abs_pos.2 (sub_ne_zero.2 (hpxy f hf.1 hf.2)))
  refine ⟨min (min γ1 γ2) η / 4, by positivity, fun z hz hz1 hzD => ?_⟩
  have hε1 : min (min γ1 γ2) η / 4 ≤ γ1 / 4 := by
    gcongr; exact (min_le_left _ _).trans (min_le_left _ _)
  have hε2 : min (min γ1 γ2) η / 4 ≤ γ2 / 4 := by
    gcongr; exact (min_le_left _ _).trans (min_le_right _ _)
  have hε3 : min (min γ1 γ2) η / 4 ≤ η / 4 := by gcongr; exact min_le_right _ _
  have hclose : ∀ x ∈ X, ∀ y ∈ X,
      |dist (x + z x) (y + z y) - dist x y| < 2 * (min (min γ1 γ2) η / 4) := by
    intro x hx y hy
    have := dist_add_sub_le x y (z x) (z y)
    have := hz x hx; have := hz y hy
    linarith
  let g : X → Plane := fun x => (x : Plane) + z x
  have hsepg : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → 1 ≤ dist (x + z x) (y + z y) := by
    intro x hx y hy hxy
    by_cases h1 : dist x y = 1
    · exact hz1 x hx y hy h1
    · have hg := hg1 x hx y hy h1
      have hge := hX.1.2 x hx y hy hxy
      rw [abs_of_nonneg (by linarith)] at hg
      have := abs_lt.1 (hclose x hx y hy)
      linarith
  have hupper : ∀ x ∈ X, ∀ y ∈ X, dist (x + z x) (y + z y) ≤ D := by
    intro x hx y hy
    by_cases h2 : dist x y = D
    · exact hzD x hx y hy h2
    · have hg := hg2 x hx y hy h2
      have hle := dist_le_diam hx hy
      rw [abs_of_nonpos (by linarith)] at hg
      have := abs_lt.1 (hclose x hx y hy)
      linarith
  have hinj : Function.Injective g := by
    intro x y hxy
    by_contra hne
    have := hsepg x x.2 y y.2 (fun h => hne (Subtype.ext h))
    simp only [g] at hxy
    rw [hxy, dist_self] at this; linarith
  have hopt : IsOptimal n (Finset.univ.image g) := by
    have hcard : (Finset.univ.image g).card = n := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_coe, hX.1.1]
    have hsepF : IsSeparated (Finset.univ.image g) := by
      intro a ha b hb hab
      obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 ha
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hb
      exact hsepg x x.2 y y.2 (fun h => hab (by simp only [g, h]))
    have hdiam : diam (Finset.univ.image g) ≤ D := by
      apply Metric.diam_le_of_forall_dist_le hD.le
      intro a ha b hb
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at ha hb
      obtain ⟨x, -, rfl⟩ := ha
      obtain ⟨y, -, rfl⟩ := hb
      exact hupper x x.2 y y.2
    exact ⟨⟨hcard, hsepF⟩, fun Y hY => hdiam.trans (hX.2 Y hY)⟩
  have hmem := hFmem g hopt
  set f : X → X → ℝ := fun x y => dist (g x) (g y)
  have hfd : f = d0 := by
    by_contra hne
    have hfS : |f (px f) (py f) - d0 (px f) (py f)| ∈ S := ⟨f, ⟨hmem, hne⟩, rfl⟩
    have h1 := hηS _ hfS
    have h2 := hclose _ (px f).2 _ (py f).2
    simp only [f, d0, g] at h1
    linarith
  intro x hx y hy
  have := congrFun (congrFun hfd ⟨x, hx⟩) ⟨y, hy⟩
  simpa [f, d0, g] using this

/-- An infinitesimal isometry of a non-collinear planar set is trivial. -/
theorem trivial_of_infinitesimal_isometry {X : Finset Plane}
    (hcol : ¬ Collinear ℝ (X : Set Plane)) (v : Plane → Plane)
    (hv : ∀ x ∈ X, ∀ y ∈ X, inner ℝ (x - y) (v x - v y) = 0) :
    IsTrivialVelocity X v := by
  obtain ⟨a, ha, p, hp, hap⟩ := exists_two_of_not_collinear hcol
  set d := p - a with hd
  have hd0 : d 0 ^ 2 + d 1 ^ 2 ≠ 0 := by
    intro h0
    apply hap; symm; rw [← sub_eq_zero]
    ext i; fin_cases i <;> simp [d] at h0 ⊢ <;>
      nlinarith [sq_nonneg (p 0 - a 0), sq_nonneg (p 1 - a 1)]
  set ω := inner ℝ (rot d) (v p - v a) / (d 0 ^ 2 + d 1 ^ 2)
  set u : Plane → Plane := fun x => v x - v a - ω • rot (x - a)
  have hu : ∀ x ∈ X, ∀ y ∈ X, inner ℝ (x - y) (u x - u y) = 0 := by
    intro x hx y hy
    have : u x - u y = (v x - v y) - ω • rot (x - y) := by
      simp only [u, rot_sub', smul_sub]; abel
    rw [this, inner_sub_right, inner_smul_right, inner_rot_self, hv x hx y hy]; ring
  have hua : u a = 0 := by simp [u, rot_sub']
  have hup : u p = 0 := by
    apply eq_zero_of_inner_eq_zero_two (d1 := d) (d2 := rot d)
    · rw [cross2_rot]; exact hd0
    · have := hu p hp a ha; rwa [hua, sub_zero] at this
    · show inner ℝ (rot d) (v p - v a - ω • rot d) = 0
      rw [inner_sub_right, inner_smul_right, inner_rot_rot]
      simp only [ω]; field_simp; ring
  have hoff : ∀ x ∈ X, cross2 d (x - a) ≠ 0 → u x = 0 := by
    intro x hx hx0
    apply eq_zero_of_inner_eq_zero_two (d1 := x - a) (d2 := x - p)
    · have : x - p = (x - a) - d := by simp [d]
      rw [this, cross2_sub_right, cross2_self, cross2_comm]; simpa using hx0
    · have := hu x hx a ha; rwa [hua, sub_zero] at this
    · have := hu x hx p hp; rwa [hup, sub_zero] at this
  obtain ⟨c, hc, hc0⟩ := exists_cross_ne_zero hcol ha hap
  have huc := hoff c hc hc0
  have hall : ∀ x ∈ X, u x = 0 := by
    intro x hx
    by_cases hx0 : cross2 d (x - a) = 0
    · by_cases hxa : x = a
      · rw [hxa, hua]
      obtain ⟨r, hr⟩ := exists_smul_of_cross_eq_zero (sub_ne_zero.2 hap.symm) hx0
      have hr0 : r ≠ 0 := by rintro rfl; apply hxa; rw [← sub_eq_zero, hr, zero_smul]
      apply eq_zero_of_inner_eq_zero_two (d1 := x - a) (d2 := x - c)
      · have : x - c = (x - a) - (c - a) := by abel
        rw [this, cross2_sub_right, cross2_self, hr, cross2_smul_left]
        simpa [hr0] using hc0
      · have := hu x hx a ha; rwa [hua, sub_zero] at this
      · have := hu x hx c hc; rwa [huc, sub_zero] at this
    · exact hoff x hx hx0
  refine ⟨ω, v a - ω • rot a, fun x hx => ?_⟩
  have := hall x hx
  simp only [u, rot_sub', smul_sub] at this
  rw [← sub_eq_zero, ← this]; abel

/-- If `t v + O(t²)` is a distance-preserving displacement for all small `t > 0`, then `v` is an
infinitesimal isometry. -/
theorem inner_eq_zero_of_rigid_family {X : Finset Plane} (v : Plane → Plane) {M δ : ℝ}
    (hδ : 0 < δ)
    (hfam : ∀ t ∈ Set.Ioo 0 δ, ∃ z : Plane → Plane, (∀ x ∈ X, ‖z x - t • v x‖ ≤ M * t ^ 2) ∧
      ∀ x ∈ X, ∀ y ∈ X, dist (x + z x) (y + z y) = dist x y) :
    ∀ x ∈ X, ∀ y ∈ X, inner ℝ (x - y) (v x - v y) = 0 := by
  intro x hx y hy
  set d := x - y
  set w := v x - v y
  refine eq_zero_of_abs_le_mul (K := 2 * ‖d‖ * |M| + ‖w‖ ^ 2 + 4 * M ^ 2 * δ ^ 2) hδ
    fun t ht => ?_
  obtain ⟨z, hz, hiso⟩ := hfam t ht
  set r := (z x - t • v x) - (z y - t • v y)
  have hr : ‖r‖ ≤ 2 * |M| * t ^ 2 := by
    have := norm_sub_le (z x - t • v x) (z y - t • v y)
    have h1 := hz x hx; have h2 := hz y hy
    have : M ≤ |M| := le_abs_self M
    nlinarith [sq_nonneg t]
  have he : z x - z y = t • w + r := by
    simp only [r, w, smul_sub]; abel
  have hdist := hiso x hx y hy
  have hsq : ‖d + (t • w + r)‖ ^ 2 = ‖d‖ ^ 2 := by
    rw [dist_eq_norm, dist_eq_norm] at hdist
    rw [← he, show d + (z x - z y) = x + z x - (y + z y) by simp only [d]; abel, hdist]
  rw [norm_add_sq_real, inner_add_right, inner_smul_right] at hsq
  have hdr : |inner ℝ d r| ≤ ‖d‖ * ‖r‖ := abs_real_inner_le_norm d r
  have htw : ‖t • w + r‖ ≤ t * ‖w‖ + ‖r‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg ht.1.le]
  have ht0 := ht.1
  have htδ := ht.2
  have hr0 := norm_nonneg r
  have hw0 := norm_nonneg w
  have hd0 := norm_nonneg d
  have hM : 0 ≤ |M| := abs_nonneg M
  have hsq2 : ‖t • w + r‖ ^ 2 ≤ (t * ‖w‖ + 2 * |M| * t ^ 2) ^ 2 := by
    have := norm_nonneg (t • w + r)
    nlinarith
  have hb : (t * ‖w‖ + 2 * |M| * t ^ 2) ^ 2 ≤ t ^ 2 * (2 * ‖w‖ ^ 2 + 8 * M ^ 2 * δ ^ 2) := by
    have h1 : (t * ‖w‖ + 2 * |M| * t ^ 2) ^ 2 ≤
        2 * (t * ‖w‖) ^ 2 + 2 * (2 * |M| * t ^ 2) ^ 2 := by
      nlinarith [sq_nonneg (t * ‖w‖ - 2 * |M| * t ^ 2)]
    have h2 : t ^ 2 ≤ δ ^ 2 := by nlinarith
    have h3 : (2 * |M| * t ^ 2) ^ 2 = 4 * M ^ 2 * t ^ 2 * t ^ 2 := by rw [← sq_abs M]; ring
    have h4 : M ^ 2 * t ^ 2 * t ^ 2 ≤ M ^ 2 * t ^ 2 * δ ^ 2 :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    nlinarith
  have hdr' : |inner ℝ d r| ≤ ‖d‖ * (2 * |M| * t ^ 2) :=
    hdr.trans (mul_le_mul_of_nonneg_left hr hd0)
  rw [abs_le] at hdr'
  have hnn := sq_nonneg ‖t • w + r‖
  have key : |2 * t * inner ℝ d w| ≤
      t * (2 * (2 * ‖d‖ * |M| + ‖w‖ ^ 2 + 4 * M ^ 2 * δ ^ 2) * t) := by
    rw [abs_le]; constructor <;> nlinarith
  rw [abs_mul, abs_of_pos (by linarith : (0:ℝ) < 2 * t)] at key
  nlinarith

/-- **First-order locking** for a single optimal, non-collinear configuration, under finite
multiplicity. -/
theorem first_order_locking_of {n : ℕ} (hn : 2 ≤ n) (hfm : numOptimalClasses n < ⊤)
    {X : Finset Plane} (hX : IsOptimal n X) (hcol : ¬ Collinear ℝ (X : Set Plane))
    (v : Plane → Plane)
    (hU : ∀ x ∈ X, ∀ y ∈ X, dist x y = 1 → 0 ≤ inner ℝ (x - y) (v x - v y))
    (hT : ∀ x ∈ X, ∀ y ∈ X, dist x y = diam X → inner ℝ (x - y) (v x - v y) ≤ 0) :
    IsTrivialVelocity X v := by
  apply trivial_of_infinitesimal_isometry hcol v
  obtain ⟨ε, hε, hiso⟩ := distances_preserved_of_small hn hfm hX
  obtain ⟨M, δ, hδ, hext⟩ := secondOrder_extension hX.1.2 hcol v hU hT
  -- a bound for `v` on `X`
  set K := ∑ x ∈ X, ‖v x‖
  have hK : ∀ x ∈ X, ‖v x‖ ≤ K := fun x hx =>
    Finset.single_le_sum (f := fun x => ‖v x‖) (fun _ _ => norm_nonneg _) hx
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ => norm_nonneg _
  set M' := |M|
  -- choose `δ'` so small that `t K + M' t² < ε` for `t < δ'`
  set δ' := min δ (min 1 (ε / (K + M' + 1)))
  have hδ' : 0 < δ' := lt_min hδ (lt_min one_pos (div_pos hε (by positivity)))
  refine inner_eq_zero_of_rigid_family v (M := M) hδ' fun t ht => ?_
  have ht1 : t ∈ Set.Ioo 0 δ := ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩
  obtain ⟨z, hz, hz1, hzD⟩ := hext t ht1
  refine ⟨z, hz, hiso z (fun x hx => ?_) hz1 hzD⟩
  have htle1 : t ≤ 1 := ht.2.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have htε : t < ε / (K + M' + 1) := ht.2.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  rw [lt_div_iff₀ (by positivity)] at htε
  have h1 : ‖z x‖ ≤ ‖z x - t • v x‖ + ‖t • v x‖ := by
    simpa using norm_add_le (z x - t • v x) (t • v x)
  have h2 : ‖t • v x‖ ≤ t * K := by
    rw [norm_smul, Real.norm_of_nonneg ht.1.le]
    exact mul_le_mul_of_nonneg_left (hK x hx) ht.1.le
  have h3 : M * t ^ 2 ≤ M' * t := by
    have : M * t ^ 2 ≤ M' * t ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self M) (sq_nonneg t)
    have h4 : M' * t ^ 2 ≤ M' * t := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg M)
      nlinarith [ht.1]
    linarith
  have := hz x hx
  nlinarith [ht.1]

end Erdos99
end

end FirstOrderLocking

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `Isodiametric`
-/

section Isodiametric

/-!
# The planar isodiametric inequality

A measurable planar set `A` of diameter at most `d` has area at most `π d² / 4`, provided it has a
lowest point (e.g. `A` compact and nonempty).  We use polar coordinates about a lowest point
`x₀`: the set lies in the closed upper half-plane, and for `θ ∈ [0, π/2)` the radial extents
`R(θ)`, `R(θ + π/2)` of the set along two perpendicular rays satisfy `R(θ)² + R(θ + π/2)² ≤ d²`
(Pythagoras), so the area `∫₀^π R(θ)²/2 dθ` is at most `(π/2) · d²/2`.

This is used in the manuscript's Lemma 3.1 (`|H| ≤ π D² / 4`).
-/

open scoped Real
open MeasureTheory Set

@[expose] public noncomputable section

namespace Erdos99

/-- The radial integral over a set of radii bounded by `a`. -/
lemma lintegral_ray_le {S : Set ℝ} {a : ℝ} (ha : 0 ≤ a) (hS : ∀ r ∈ S, 0 < r → r ≤ a) :
    ∫⁻ r in Ioi 0, ENNReal.ofReal r * S.indicator 1 r ≤ ENNReal.ofReal (a ^ 2 / 2) := by
  calc ∫⁻ r in Ioi 0, ENNReal.ofReal r * S.indicator 1 r
      ≤ ∫⁻ r in Ioi 0, (Iic a).indicator (fun r => ENNReal.ofReal r) r := by
        refine setLIntegral_mono' measurableSet_Ioi fun r hr => ?_
        by_cases hrS : r ∈ S
        · have : r ∈ Iic a := hS r hrS hr
          simp [hrS, this]
        · simp [hrS]
    _ = ∫⁻ r in Ioc 0 a, ENNReal.ofReal r := by
        rw [lintegral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
          Set.Iic_inter_Ioi]
    _ = ENNReal.ofReal (a ^ 2 / 2) := by
        rw [← ofReal_integral_eq_lintegral_ofReal]
        · rw [← intervalIntegral.integral_of_le ha, integral_id]; ring_nf
        · exact (continuous_id.integrableOn_Icc).mono_set Ioc_subset_Icc_self
        · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr using hr.1.le

/-- Suprema of two sets of radii that are pairwise Pythagorean-bounded. -/
lemma sSup_sq_add_sSup_sq_le {S T : Set ℝ} {d : ℝ} (hd : 0 ≤ d) (hS : ∀ r ∈ S, 0 < r ∧ r ≤ d)
    (hT : ∀ r ∈ T, 0 < r ∧ r ≤ d) (hST : ∀ r ∈ S, ∀ s ∈ T, r ^ 2 + s ^ 2 ≤ d ^ 2) :
    sSup S ^ 2 + sSup T ^ 2 ≤ d ^ 2 ∧ 0 ≤ sSup S ∧ 0 ≤ sSup T := by
  have h0S : 0 ≤ sSup S := Real.sSup_nonneg fun r hr => (hS r hr).1.le
  have h0T : 0 ≤ sSup T := Real.sSup_nonneg fun r hr => (hT r hr).1.le
  have hleS : sSup S ≤ d := by
    rcases S.eq_empty_or_nonempty with h | h
    · rw [h, Real.sSup_empty]; exact hd
    · exact csSup_le h fun r hr => (hS r hr).2
  have hleT : sSup T ≤ d := by
    rcases T.eq_empty_or_nonempty with h | h
    · rw [h, Real.sSup_empty]; exact hd
    · exact csSup_le h fun r hr => (hT r hr).2
  refine ⟨?_, h0S, h0T⟩
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · rw [hSe, Real.sSup_empty]; nlinarith
  rcases T.eq_empty_or_nonempty with hTe | hTne
  · rw [hTe, Real.sSup_empty]; nlinarith
  -- every `s ∈ T` satisfies `s² ≤ d² - (sup S)²`
  have key : ∀ s ∈ T, s ^ 2 ≤ d ^ 2 - sSup S ^ 2 := by
    intro s hs
    have : sSup S ≤ √(d ^ 2 - s ^ 2) :=
      csSup_le hSne fun r hr => Real.le_sqrt_of_sq_le (by linarith [hST r hr s hs])
    have h2 := pow_le_pow_left₀ h0S this 2
    rw [Real.sq_sqrt (by nlinarith [hST _ hSne.some_mem s hs, sq_nonneg (hSne.some)])] at h2
    linarith
  have : sSup T ≤ √(d ^ 2 - sSup S ^ 2) :=
    csSup_le hTne fun s hs => Real.le_sqrt_of_sq_le (key s hs)
  have h2 := pow_le_pow_left₀ h0T this 2
  rw [Real.sq_sqrt (by nlinarith)] at h2
  linarith

/-- **Planar isodiametric inequality** (in `ℝ × ℝ`, with the Euclidean distance written in
coordinates).  A measurable set with a lowest point and all squared distances at most `d²` has
area at most `π d² / 4`. -/
theorem volume_le_of_sq_dist_le {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) {d : ℝ} (hd : 0 ≤ d)
    (hdist : ∀ p ∈ A, ∀ q ∈ A, (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 ≤ d ^ 2)
    {x₀ : ℝ × ℝ} (hx₀ : x₀ ∈ A) (hlow : ∀ p ∈ A, x₀.2 ≤ p.2) :
    volume A ≤ ENNReal.ofReal (π * d ^ 2 / 4) := by
  set A' := (fun p => p + x₀) ⁻¹' A with hA'def
  have hA' : MeasurableSet A' := hA.preimage (measurable_id.add_const _)
  have hvol : volume A' = volume A := measure_preimage_add_right _ _ _
  have h0 : (0 : ℝ × ℝ) ∈ A' := by simp [A', hx₀]
  have hup : ∀ p ∈ A', 0 ≤ p.2 := fun p hp => by
    have := hlow _ hp; simp at this; linarith
  have hd' : ∀ p ∈ A', ∀ q ∈ A', (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 ≤ d ^ 2 := by
    intro p hp q hq
    have := hdist _ hp _ hq
    simp only [Prod.fst_add, Prod.snd_add, add_sub_add_right_eq_sub] at this
    exact this
  -- the radial integrand
  set P : ℝ → ℝ → ℝ × ℝ := fun r θ => (r * Real.cos θ, r * Real.sin θ) with hP
  set F : ℝ → ENNReal := fun θ =>
    ∫⁻ r in Ioi 0, ENNReal.ofReal r * {r | P r θ ∈ A'}.indicator 1 r with hF
  have hmeas : Measurable (fun q : ℝ × ℝ => ENNReal.ofReal q.1 * A'.indicator 1 (P q.1 q.2)) := by
    refine (ENNReal.measurable_ofReal.comp measurable_fst).mul ?_
    exact (measurable_one.indicator hA').comp (by fun_prop)
  have hpolar : volume A' = ∫⁻ θ in Ioo (-π) π, F θ := by
    rw [← lintegral_indicator_one hA', ← lintegral_comp_polarCoord_symm, polarCoord_target,
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
  -- points of `A'` on a ray at distance `r > 0` from the origin
  have hray : ∀ θ r, P r θ ∈ A' → 0 < r → r ≤ d := by
    intro θ r hr hr0
    have := hd' _ hr _ h0
    simp only [P, Prod.fst_zero, Prod.snd_zero, sub_zero] at this
    have e : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq θ]
    rw [e] at this
    exact (pow_le_pow_iff_left₀ hr0.le hd two_ne_zero).1 this
  -- the lower half-plane contributes nothing
  have hneg : ∀ θ ∈ Ioo (-π) 0, F θ = 0 := by
    intro θ hθ
    have hs : Real.sin θ < 0 := Real.sin_neg_of_neg_of_neg_pi_lt hθ.2 hθ.1
    refine setLIntegral_eq_zero_iff' measurableSet_Ioi ?_ |>.2 ?_
    · exact (ENNReal.measurable_ofReal.mul ((measurable_one.indicator hA').comp
        (by fun_prop))).aemeasurable
    · refine Filter.Eventually.of_forall fun r hr => ?_
      have : P r θ ∉ A' := fun h => by
        have := hup _ h; simp only [P] at this; nlinarith [mem_Ioi.1 hr]
      simp [Set.indicator, this]
  -- the pair bound
  have hpair : ∀ θ, F θ + F (θ + π / 2) ≤ ENNReal.ofReal (d ^ 2 / 2) := by
    intro θ
    set S := {r | P r θ ∈ A'} ∩ Ioi 0
    set T := {r | P r (θ + π / 2) ∈ A'} ∩ Ioi 0
    obtain ⟨hsum, h0S, h0T⟩ := sSup_sq_add_sSup_sq_le (S := S) (T := T) hd
      (fun r hr => ⟨hr.2, hray θ r hr.1 hr.2⟩)
      (fun r hr => ⟨hr.2, hray _ r hr.1 hr.2⟩) (by
        intro r hr s hs
        have := hd' _ hr.1 _ hs.1
        simp only [P, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two] at this
        nlinarith [Real.sin_sq_add_cos_sq θ])
    have b1 : F θ ≤ ENNReal.ofReal (sSup S ^ 2 / 2) := lintegral_ray_le h0S fun r hr hr0 =>
      le_csSup ⟨d, fun x hx => hray θ x hx.1 hx.2⟩ ⟨hr, hr0⟩
    have b2 : F (θ + π / 2) ≤ ENNReal.ofReal (sSup T ^ 2 / 2) :=
      lintegral_ray_le h0T fun r hr hr0 =>
        le_csSup ⟨d, fun x hx => hray _ x hx.1 hx.2⟩ ⟨hr, hr0⟩
    calc F θ + F (θ + π / 2) ≤ ENNReal.ofReal (sSup S ^ 2 / 2) + ENNReal.ofReal (sSup T ^ 2 / 2) :=
          add_le_add b1 b2
      _ = ENNReal.ofReal (sSup S ^ 2 / 2 + sSup T ^ 2 / 2) :=
          (ENNReal.ofReal_add (by positivity) (by positivity)).symm
      _ ≤ ENNReal.ofReal (d ^ 2 / 2) := ENNReal.ofReal_le_ofReal (by linarith)
  -- assemble
  rw [← hvol, hpolar]
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
  calc ∫⁻ θ in Ioo (-π) π, F θ
      ≤ (∫⁻ θ in Ioo (-π) 0, F θ) + ((∫⁻ θ in Ico 0 (π / 2), F θ) +
          ∫⁻ θ in Ico (π / 2) π, F θ) := by
        rw [hsplit]
        exact (lintegral_union_le _ _ _).trans (add_le_add le_rfl (lintegral_union_le _ _ _))
    _ = (∫⁻ θ in Ico 0 (π / 2), F θ) + ∫⁻ θ in Ico 0 (π / 2), F (θ + π / 2) := by
        rw [setLIntegral_congr_fun measurableSet_Ioo hneg, lintegral_zero, zero_add, hshift]
    _ ≤ ∫⁻ θ in Ico 0 (π / 2), (F θ + F (θ + π / 2)) := le_lintegral_add _ _
    _ ≤ ∫⁻ θ in Ico 0 (π / 2), ENNReal.ofReal (d ^ 2 / 2) := lintegral_mono fun θ => hpair θ
    _ = ENNReal.ofReal (π * d ^ 2 / 4) := by
        rw [setLIntegral_const, Real.volume_Ico, sub_zero, ← ENNReal.ofReal_mul (by positivity)]
        ring_nf

end Erdos99

namespace Erdos99

/-- **Planar isodiametric inequality.**  A nonempty compact set of the plane whose points are
pairwise at distance at most `d` has area at most `π d² / 4`. -/
theorem volume_le_of_isCompact {K : Set Plane} (hK : IsCompact K) (hne : K.Nonempty) {d : ℝ}
    (hd : 0 ≤ d) (hdist : ∀ p ∈ K, ∀ q ∈ K, dist p q ≤ d) :
    volume K ≤ ENNReal.ofReal (π * d ^ 2 / 4) := by
  set e : Plane → ℝ × ℝ := fun p => (p 0, p 1) with he
  have hpres : MeasurePreserving e volume volume :=
    (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (ι := Fin 2))
  have hcont : Continuous e := by fun_prop
  have hinj : Function.Injective e := fun p q h => by
    simp only [e, Prod.mk.injEq] at h
    ext i; fin_cases i
    · exact h.1
    · exact h.2
  set A := e '' K
  have hA : IsCompact A := hK.image hcont
  obtain ⟨x₀, hx₀, hmin⟩ := hA.exists_isMinOn (hne.image e) continuous_snd.continuousOn
  have hpre : e ⁻¹' A = K := hinj.preimage_image K
  rw [← hpre, hpres.measure_preimage hA.isClosed.measurableSet.nullMeasurableSet]
  refine volume_le_of_sq_dist_le hA.isClosed.measurableSet hd ?_ hx₀ fun p hp => hmin hp
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
  have h := dist_sq_coord p q
  have h2 := pow_le_pow_left₀ dist_nonneg (hdist p hp q hq) 2
  simp only [e]
  linarith

/-- `|conv X| ≤ π D² / 4` for a finite planar set `X` of diameter `D`. -/
theorem volume_convexHull_le (X : Finset Plane) (hX : X.Nonempty) :
    volume (convexHull ℝ (X : Set Plane)) ≤ ENNReal.ofReal (π * diam X ^ 2 / 4) := by
  have hK : IsCompact (convexHull ℝ (X : Set Plane)) := X.finite_toSet.isCompact_convexHull
  refine volume_le_of_isCompact hK ((Finset.coe_nonempty.2 hX).mono (subset_convexHull ℝ _))
    Metric.diam_nonneg fun p hp q hq => ?_
  have hb : Bornology.IsBounded (X : Set Plane) := X.finite_toSet.isBounded
  have := Metric.dist_le_diam_of_mem (isBounded_convexHull.2 hb) hp hq
  rwa [convexHull_diam] at this

end Erdos99
end

end Isodiametric

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `Density`
-/

section Density

/-!
# The density bound `n ≤ c D² + O(D)` (Lemma 3.1, density side)

For a separated planar set `X` (mutual distances at least `1`) the Voronoi cells of the points,
truncated to discs of radius `1/√3`, are pairwise disjoint, each has area at least `√3/2` (the area
of the regular hexagon of inradius `1/2`), and all of them lie in the `1`-neighbourhood of `X`,
whose area is at most `π (D + 2)² / 4` by the isodiametric inequality.  Hence
`n · √3/2 ≤ π (D + 2)² / 4`, i.e. `n ≤ c D² + O(D)` with `c = π / (2√3)`.

The area bound for a truncated cell is proved in polar coordinates about its centre: in each
direction at most one neighbour cuts the disc of radius `1/√3` (three points pairwise at distance
`≥ 1` have no common point within distance `< 1/√3`), and the area removed by a neighbour is at
most `(2π - 3√3)/(12π)` times the angle it subtends (the worst case being a neighbour at
distance `1`, which cuts off exactly a hexagon side's cap).
-/

open Real MeasureTheory Set

@[expose] public noncomputable section

namespace Erdos99
def tdot (θ : ℝ) (y : ℝ × ℝ) : ℝ := cos θ * y.1 + sin θ * y.2
def nsq (y : ℝ × ℝ) : ℝ := y.1 ^ 2 + y.2 ^ 2

def capLoss (y : ℝ × ℝ) (θ : ℝ) : ℝ :=
  if √3 / 2 * nsq y < tdot θ y then 1 / 6 - nsq y ^ 2 / (8 * tdot θ y ^ 2) else 0
def capAct (y : ℝ × ℝ) (θ : ℝ) : ℝ := if √3 / 2 * nsq y < tdot θ y then 1 else 0

lemma cos_gt_iff {α x : ℝ} (hα0 : 0 ≤ α) (hαπ : α ≤ π) (hx1 : -π ≤ x) (hx2 : x ≤ π) :
    cos α < cos x ↔ x ∈ Ioo (-α) α := by
  have key : ∀ y, 0 ≤ y → y ≤ π → (cos α < cos y ↔ y < α) := by
    intro y hy0 hyπ
    constructor
    · intro h; by_contra hc; push_neg at hc
      rcases hc.lt_or_eq with hc | rfl
      · exact absurd h (not_lt.2 (cos_lt_cos_of_nonneg_of_le_pi hα0 hyπ hc).le)
      · exact lt_irrefl _ h
    · intro h; exact cos_lt_cos_of_nonneg_of_le_pi hy0 hαπ h
  rcases le_total 0 x with hx | hx
  · rw [key x hx hx2]; constructor
    · intro h; exact ⟨by linarith, h⟩
    · intro h; exact h.2
  · rw [← cos_neg x, key (-x) (by linarith) (by linarith)]; constructor
    · intro h; exact ⟨by linarith, by linarith⟩
    · intro h; linarith [h.1]

lemma integral_indicator_Ioo {α : ℝ} (hα0 : 0 ≤ α) (hαπ : α ≤ π) (F : ℝ → ℝ) :
    ∫ x in (-π)..π, (if cos α < cos x then F x else 0) = ∫ x in (-α)..α, F x := by
  have hπ := pi_pos
  rw [intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le (by linarith)]
  have h1 : ∀ x ∈ Ioc (-π) π, (if cos α < cos x then F x else 0) = (Ioo (-α) α).indicator F x := by
    intro x hx
    by_cases h : cos α < cos x
    · rw [if_pos h, indicator_of_mem ((cos_gt_iff hα0 hαπ hx.1.le hx.2).1 h)]
    · rw [if_neg h, indicator_of_notMem (fun hm => h ((cos_gt_iff hα0 hαπ hx.1.le hx.2).2 hm))]
  rw [setIntegral_congr_fun measurableSet_Ioc h1, integral_indicator measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo]
  have : Ioo (-α) α ∩ Ioc (-π) π = Ioo (-α) α := by
    ext x; simp only [mem_inter_iff, mem_Ioo, mem_Ioc]; constructor
    · intro h; exact h.1
    · intro h; exact ⟨h, by linarith [h.1], by linarith [h.2]⟩
  rw [this, integral_Ioc_eq_integral_Ioo]

/-- The cap computation. -/
lemma cap_integral_le {c : ℝ} (hc1 : √3 / 2 ≤ c) (hc2 : c < 1) :
    ∫ x in (-π)..π, (if c < cos x then 1 / 6 - c ^ 2 / (6 * cos x ^ 2) else 0) ≤
      (2 * π - 3 * √3) / (12 * π) * ∫ x in (-π)..π, (if c < cos x then (1 : ℝ) else 0) := by
  have hπ := pi_pos
  have h3 : (0 : ℝ) < √3 := by positivity
  have h33 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hc0 : 0 < c := by linarith
  set α := arccos c with hαdef
  have hcα : cos α = c := cos_arccos (by linarith) hc2.le
  have hα0 : 0 < α := arccos_pos.2 hc2
  have hα6 : α ≤ π / 6 := by
    have : arccos c ≤ arccos (√3 / 2) := arccos_le_arccos hc1
    rwa [show √3 / 2 = cos (π / 6) by rw [cos_pi_div_six], arccos_cos (by positivity)
      (by linarith)] at this
  have hαπ : α ≤ π := by linarith
  have e1 := integral_indicator_Ioo hα0.le hαπ (fun x => 1 / 6 - c ^ 2 / (6 * cos x ^ 2))
  have e2 := integral_indicator_Ioo hα0.le hαπ (fun _ => (1 : ℝ))
  rw [hcα] at e1 e2
  rw [e1, e2]
  -- the cos is positive on `[-α, α]`
  have hcos : ∀ x ∈ uIcc (-α) α, 0 < cos x := by
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    exact cos_pos_of_mem_Ioo ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have htan : ∫ x in (-α)..α, 1 / cos x ^ 2 = tan α - tan (-α) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x hx; exact hasDerivAt_tan (hcos x hx).ne'
    · apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.div continuousOn_const (continuous_cos.pow 2).continuousOn
      intro x hx; exact pow_ne_zero _ (hcos x hx).ne'
  have hint : ∫ x in (-α)..α, (1 / 6 - c ^ 2 / (6 * cos x ^ 2)) =
      α / 3 - c ^ 2 / 6 * (2 * tan α) := by
    have hi : IntervalIntegrable (fun x => 1 / cos x ^ 2) volume (-α) α := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.div continuousOn_const (continuous_cos.pow 2).continuousOn
      intro x hx; exact pow_ne_zero _ (hcos x hx).ne'
    have : (fun x => 1 / 6 - c ^ 2 / (6 * cos x ^ 2)) =
        fun x => 1 / 6 - c ^ 2 / 6 * (1 / cos x ^ 2) := by
      ext x; field_simp
    rw [this, intervalIntegral.integral_sub intervalIntegrable_const (hi.const_mul _),
      intervalIntegral.integral_const_mul, htan, intervalIntegral.integral_const, tan_neg]
    simp; ring
  rw [hint, intervalIntegral.integral_const]
  simp only [smul_eq_mul, mul_one, sub_neg_eq_add]
  -- `tan α = √(1 - c²) / c` and `sin 2α ≥ (3√3/π) α`
  rw [hαdef, tan_arccos]
  have hs : 0 ≤ √(1 - c ^ 2) := Real.sqrt_nonneg _
  have hsin : sin (2 * α) = 2 * c * √(1 - c ^ 2) := by
    rw [sin_two_mul, hαdef, sin_arccos, cos_arccos (by linarith) hc2.le]; ring
  have hconc : 3 * √3 / π * α ≤ sin (2 * α) := by
    have hcon := strictConcaveOn_sin_Icc.concaveOn
    have ht0 : 0 ≤ 6 * α / π := by positivity
    have ht1 : 6 * α / π ≤ 1 := by rw [div_le_one hπ]; linarith
    have := hcon.2 (show (0:ℝ) ∈ Icc 0 π from ⟨le_rfl, hπ.le⟩)
      (show π / 3 ∈ Icc 0 π from ⟨by positivity, by linarith⟩)
      (show 0 ≤ 1 - 6 * α / π by linarith) ht0 (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add, sin_zero, sin_pi_div_three] at this
    have e : 6 * α / π * (π / 3) = 2 * α := by field_simp; ring
    rw [e] at this
    have e2 : 3 * √3 / π * α = 6 * α / π * (√3 / 2) := by field_simp; ring
    linarith
  rw [hsin] at hconc
  rw [← hαdef]
  have e3 : c ^ 2 / 6 * (2 * (√(1 - c ^ 2) / c)) = c * √(1 - c ^ 2) / 3 := by
    field_simp; ring
  rw [e3]
  have e4 : (2 * π - 3 * √3) / (12 * π) * (α + α) = α / 3 - √3 / (2 * π) * α := by
    field_simp; ring
  rw [e4]
  have e5 : 3 * √3 / π * α = 6 * (√3 / (2 * π) * α) := by field_simp; ring
  linarith

lemma exists_polar (y : ℝ × ℝ) : ∃ φ, y.1 = √(nsq y) * cos φ ∧ y.2 = √(nsq y) * sin φ := by
  refine ⟨Complex.arg ⟨y.1, y.2⟩, ?_, ?_⟩
  · have := Complex.norm_mul_cos_arg (⟨y.1, y.2⟩ : ℂ)
    rw [Complex.norm_eq_sqrt_sq_add_sq] at this
    simpa [nsq] using this.symm
  · have := Complex.norm_mul_sin_arg (⟨y.1, y.2⟩ : ℂ)
    rw [Complex.norm_eq_sqrt_sq_add_sq] at this
    simpa [nsq] using this.symm

lemma tdot_polar {y : ℝ × ℝ} {φ R : ℝ} (h1 : y.1 = R * cos φ) (h2 : y.2 = R * sin φ)
    (θ : ℝ) : tdot θ y = R * cos (θ - φ) := by
  rw [tdot, h1, h2, cos_sub]; ring


lemma periodic_shift_integral {G : ℝ → ℝ} (hG : Function.Periodic G (2 * π)) (φ : ℝ) :
    ∫ θ in (-π)..π, G (θ - φ) = ∫ x in (-π)..π, G x := by
  rw [intervalIntegral.integral_comp_sub_right]
  have e1 : π - φ = (-π - φ) + 2 * π := by ring
  have e2 : π = -π + 2 * π := by ring
  rw [e1, hG.intervalIntegral_add_eq (-π - φ) (-π), ← e2]

lemma capLoss_integral_le {y : ℝ × ℝ} (hy : 1 ≤ nsq y) :
    ∫ θ in (-π)..π, capLoss y θ ≤
      (2 * π - 3 * √3) / (12 * π) * ∫ θ in (-π)..π, capAct y θ := by
  obtain ⟨φ, h1, h2⟩ := exists_polar y
  set R := √(nsq y) with hR
  have hR1 : 1 ≤ R := by rw [hR]; exact Real.one_le_sqrt.2 hy
  have hRsq : nsq y = R ^ 2 := by rw [hR, Real.sq_sqrt (by linarith)]
  clear_value R
  have h3 : (0 : ℝ) < √3 := by positivity
  have h33 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3ge : √3 / 2 ≤ √3 / 2 * R := by nlinarith
  have hcond : ∀ θ, (√3 / 2 * nsq y < tdot θ y ↔ √3 / 2 * R < cos (θ - φ)) := by
    intro θ
    rw [tdot_polar h1 h2, hRsq]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  by_cases hc : 1 ≤ √3 / 2 * R
  · have hz : ∀ θ, ¬ (√3 / 2 * nsq y < tdot θ y) := by
      intro θ h; rw [hcond] at h; linarith [cos_le_one (θ - φ)]
    simp [capLoss, capAct, hz]
  push_neg at hc
  set c := √3 / 2 * R with hcdef
  set G : ℝ → ℝ := fun x => if c < cos x then 1 / 6 - c ^ 2 / (6 * cos x ^ 2) else 0
  set A : ℝ → ℝ := fun x => if c < cos x then 1 else 0
  have hL : ∀ θ, capLoss y θ = G (θ - φ) := by
    intro θ
    simp only [capLoss, G]
    by_cases h : c < cos (θ - φ)
    · rw [if_pos ((hcond θ).2 h), if_pos h, tdot_polar h1 h2, hRsq, hcdef]
      have hcos : 0 < cos (θ - φ) := by linarith
      field_simp
      rw [h33]; ring
    · rw [if_neg (fun h' => h ((hcond θ).1 h')), if_neg h]
  have hA : ∀ θ, capAct y θ = A (θ - φ) := by
    intro θ
    simp only [capAct, A]
    by_cases h : c < cos (θ - φ)
    · rw [if_pos ((hcond θ).2 h), if_pos h]
    · rw [if_neg (fun h' => h ((hcond θ).1 h')), if_neg h]
  have hGp : Function.Periodic G (2 * π) := fun x => by simp only [G, cos_add_two_pi]
  have hAp : Function.Periodic A (2 * π) := fun x => by simp only [A, cos_add_two_pi]
  simp_rw [hL, hA]
  rw [periodic_shift_integral hGp, periodic_shift_integral hAp]
  exact cap_integral_le h3ge hc

lemma act_unique {y1 y2 : ℝ × ℝ} {θ : ℝ} (hn1 : 1 ≤ nsq y1) (hn2 : 1 ≤ nsq y2)
    (h12 : 1 ≤ nsq (y1 - y2)) (ha1 : √3 / 2 * nsq y1 < tdot θ y1)
    (ha2 : √3 / 2 * nsq y2 < tdot θ y2) : False := by
  have hs : (0 : ℝ) < √3 := by positivity
  have h33 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hcs := sin_sq_add_cos_sq θ
  have m1 := mul_lt_mul_of_pos_left ha1 hs
  have m2 := mul_lt_mul_of_pos_left ha2 hs
  have hsq := add_nonneg (sq_nonneg (3 * cos θ - √3 * (y1.1 + y2.1)))
    (sq_nonneg (3 * sin θ - √3 * (y1.2 + y2.2)))
  simp only [nsq, tdot, Prod.fst_sub, Prod.snd_sub] at *
  nlinarith

lemma not_act_lt {y : ℝ × ℝ} {θ r : ℝ} (hn : 1 ≤ nsq y) (hr : 0 < r) (hr3 : r ^ 2 < 1 / 3)
    (hna : ¬ √3 / 2 * nsq y < tdot θ y) : 2 * r * tdot θ y < nsq y := by
  push_neg at hna
  have hs : (0 : ℝ) < √3 := by positivity
  have h33 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rcases le_or_gt (tdot θ y) 0 with ht | ht
  · nlinarith
  · have h1 : √3 * r < 1 := by nlinarith
    nlinarith

lemma capLoss_nonneg (y : ℝ × ℝ) (θ : ℝ) (hn : 1 ≤ nsq y) : 0 ≤ capLoss y θ := by
  unfold capLoss
  split_ifs with h
  · have hs : (0 : ℝ) < √3 := by positivity
    have h33 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have ht : 0 < tdot θ y := by nlinarith
    have h2 : 3 * nsq y ^ 2 < 4 * tdot θ y ^ 2 := by
      have h0 : 0 ≤ √3 * nsq y := by nlinarith
      have := pow_lt_pow_left₀ (show √3 * nsq y < 2 * tdot θ y by linarith) h0 two_ne_zero
      nlinarith
    rw [sub_nonneg, div_le_iff₀ (by positivity)]
    nlinarith
  · exact le_rfl

lemma capLoss_le (y : ℝ × ℝ) (θ : ℝ) : capLoss y θ ≤ 1 / 6 := by
  unfold capLoss
  split_ifs with h
  · have : 0 ≤ nsq y ^ 2 / (8 * tdot θ y ^ 2) := by positivity
    linarith
  · norm_num

lemma measurable_capLoss (y : ℝ × ℝ) : Measurable (capLoss y) := by
  unfold capLoss tdot
  refine Measurable.ite (measurableSet_lt measurable_const (by fun_prop)) (by fun_prop)
    measurable_const

lemma measurable_capAct (y : ℝ × ℝ) : Measurable (capAct y) := by
  unfold capAct tdot
  exact Measurable.ite (measurableSet_lt measurable_const (by fun_prop)) measurable_const
    measurable_const

lemma intervalIntegrable_of_bdd {f : ℝ → ℝ} (hf : Measurable f) (M : ℝ) (hM : ∀ x, |f x| ≤ M)
    (a b : ℝ) : IntervalIntegrable f volume a b := by
  refine (intervalIntegrable_iff).2 ?_
  refine Measure.integrableOn_of_bounded (M := M) (by simp) hf.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun x => by simpa using hM x

lemma ray_ge {S : Set ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hS : Ioo 0 ρ ⊆ S) :
    ENNReal.ofReal (ρ ^ 2 / 2) ≤ ∫⁻ r in Ioi 0, ENNReal.ofReal r * S.indicator 1 r := by
  calc ENNReal.ofReal (ρ ^ 2 / 2) = ∫⁻ r in Ioo 0 ρ, ENNReal.ofReal r := by
        rw [← ofReal_integral_eq_lintegral_ofReal]
        · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hρ, integral_id]
          ring_nf
        · exact (continuous_id.integrableOn_Icc).mono_set Ioo_subset_Icc_self
        · filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr using hr.1.le
    _ = ∫⁻ r in Ioi 0, (Ioo 0 ρ).indicator (fun r => ENNReal.ofReal r) r := by
        rw [lintegral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
          Set.inter_eq_left.2 Ioo_subset_Ioi_self]
    _ ≤ _ := by
        refine lintegral_mono fun r => ?_
        by_cases hr : r ∈ Ioo 0 ρ
        · simp [hr, hS hr]
        · simp [hr]

def cellSet (Y : Finset (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  {z | nsq z < 1 / 3 ∧ ∀ y ∈ Y, 2 * (z.1 * y.1 + z.2 * y.2) < nsq y}

lemma mem_cellSet_ray (Y : Finset (ℝ × ℝ)) (r θ : ℝ) :
    (r * cos θ, r * sin θ) ∈ cellSet Y ↔ r ^ 2 < 1 / 3 ∧ ∀ y ∈ Y, 2 * r * tdot θ y < nsq y := by
  have e1 : nsq (r * cos θ, r * sin θ) = r ^ 2 := by
    simp only [nsq]; nlinarith [sin_sq_add_cos_sq θ]
  have e2 : ∀ y : ℝ × ℝ, 2 * ((r * cos θ, r * sin θ).1 * y.1 + (r * cos θ, r * sin θ).2 * y.2) =
      2 * r * tdot θ y := fun y => by simp only [tdot]; ring
  simp only [cellSet, mem_setOf_eq, e1, e2]

section
variable {Y : Finset (ℝ × ℝ)} (hY1 : ∀ y ∈ Y, 1 ≤ nsq y)
  (hY2 : ∀ y1 ∈ Y, ∀ y2 ∈ Y, y1 ≠ y2 → 1 ≤ nsq (y1 - y2))
include hY1 hY2

lemma not_act_of_act {y y' : ℝ × ℝ} {θ : ℝ} (hy : y ∈ Y) (hy' : y' ∈ Y) (hne : y' ≠ y)
    (ha : √3 / 2 * nsq y < tdot θ y) : ¬ √3 / 2 * nsq y' < tdot θ y' := fun ha' =>
  act_unique (hY1 y' hy') (hY1 y hy) (hY2 y' hy' y hy hne) ha' ha

lemma exists_rho (θ : ℝ) : ∃ ρ, 0 ≤ ρ ∧ Ioo 0 ρ ⊆ {r | (r * cos θ, r * sin θ) ∈ cellSet Y} ∧
    ρ ^ 2 / 2 = 1 / 6 - ∑ y ∈ Y, capLoss y θ := by
  have hs : (0 : ℝ) < √3 := by positivity
  have h33 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  by_cases h : ∃ y ∈ Y, √3 / 2 * nsq y < tdot θ y
  · obtain ⟨y, hy, ha⟩ := h
    have hn := hY1 y hy
    have ht : 0 < tdot θ y := by nlinarith
    have hlt : √3 * nsq y < 2 * tdot θ y := by linarith
    have hsum : ∑ y' ∈ Y, capLoss y' θ = capLoss y θ := by
      refine Finset.sum_eq_single_of_mem y hy fun y' hy' hne => ?_
      simp only [capLoss, if_neg (not_act_of_act hY1 hY2 hy hy' hne ha)]
    refine ⟨nsq y / (2 * tdot θ y), by positivity, ?_, ?_⟩
    · intro r hr
      obtain ⟨hr0, hr1⟩ := hr
      rw [lt_div_iff₀ (by positivity)] at hr1
      have hr3 : r ^ 2 < 1 / 3 := by
        have : √3 * r < 1 := by nlinarith
        nlinarith
      refine (mem_cellSet_ray Y r θ).2 ⟨hr3, fun y' hy' => ?_⟩
      by_cases hne : y' = y
      · subst hne; linarith
      · exact not_act_lt (hY1 y' hy') hr0 hr3 (not_act_of_act hY1 hY2 hy hy' hne ha)
    · rw [hsum, capLoss, if_pos ha]
      field_simp
      ring
  · push_neg at h
    have hsum : ∑ y' ∈ Y, capLoss y' θ = 0 :=
      Finset.sum_eq_zero fun y' hy' => by simp only [capLoss, if_neg (not_lt.2 (h y' hy'))]
    refine ⟨1 / √3, by positivity, ?_, ?_⟩
    · intro r hr
      obtain ⟨hr0, hr1⟩ := hr
      rw [lt_div_iff₀ hs] at hr1
      have hr3 : r ^ 2 < 1 / 3 := by nlinarith
      exact (mem_cellSet_ray Y r θ).2 ⟨hr3, fun y' hy' =>
        not_act_lt (hY1 y' hy') hr0 hr3 (not_lt.2 (h y' hy'))⟩
    · rw [hsum, div_pow, h33]; ring

lemma sum_capAct_le (θ : ℝ) : ∑ y ∈ Y, capAct y θ ≤ 1 := by
  by_cases h : ∃ y ∈ Y, √3 / 2 * nsq y < tdot θ y
  · obtain ⟨y, hy, ha⟩ := h
    rw [Finset.sum_eq_single_of_mem y hy fun y' hy' hne => by
      simp only [capAct, if_neg (not_act_of_act hY1 hY2 hy hy' hne ha)]]
    simp only [capAct, if_pos ha, le_refl]
  · push_neg at h
    rw [Finset.sum_eq_zero fun y' hy' => by simp only [capAct, if_neg (not_lt.2 (h y' hy'))]]
    norm_num

end

theorem volume_cellSet_ge {Y : Finset (ℝ × ℝ)} (hY1 : ∀ y ∈ Y, 1 ≤ nsq y)
    (hY2 : ∀ y1 ∈ Y, ∀ y2 ∈ Y, y1 ≠ y2 → 1 ≤ nsq (y1 - y2)) :
    ENNReal.ofReal (√3 / 2) ≤ volume (cellSet Y) := by
  have hπ := pi_gt_three
  have hs : (0 : ℝ) < √3 := by positivity
  have h33 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hmeas : MeasurableSet (cellSet Y) := by
    have : cellSet Y = {z | nsq z < 1 / 3} ∩
        ⋂ y ∈ Y, {z : ℝ × ℝ | 2 * (z.1 * y.1 + z.2 * y.2) < nsq y} := by
      ext z; simp [cellSet]
    rw [this]
    exact (measurableSet_lt (by unfold nsq; fun_prop) measurable_const).inter
      (Finset.measurableSet_biInter Y fun y _ => measurableSet_lt (by fun_prop) measurable_const)
  set A' := cellSet Y
  set P : ℝ → ℝ → ℝ × ℝ := fun r θ => (r * Real.cos θ, r * Real.sin θ) with hP
  set F : ℝ → ENNReal := fun θ =>
    ∫⁻ r in Ioi 0, ENNReal.ofReal r * {r | P r θ ∈ A'}.indicator 1 r with hF
  have hmeas2 : Measurable
      (fun q : ℝ × ℝ => ENNReal.ofReal q.1 * A'.indicator 1 (P q.1 q.2)) := by
    refine (ENNReal.measurable_ofReal.comp measurable_fst).mul ?_
    exact (measurable_one.indicator hmeas).comp (by fun_prop)
  have hpolar : volume A' = ∫⁻ θ in Ioo (-π) π, F θ := by
    rw [← lintegral_indicator_one hmeas, ← lintegral_comp_polarCoord_symm, polarCoord_target,
      Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ ?_]
    · rw [lintegral_lintegral_swap]
      · refine lintegral_congr fun θ => lintegral_congr fun r => ?_
        simp only [polarCoord_symm_apply, smul_eq_mul, P, Set.indicator, Set.mem_setOf_eq,
          Pi.one_apply]
      · exact hmeas2.aemeasurable.congr
          (Filter.Eventually.of_forall fun q => by
            simp only [Function.uncurry, polarCoord_symm_apply, smul_eq_mul, P])
    · exact hmeas2.aemeasurable.congr (Filter.Eventually.of_forall fun q => by
        simp only [polarCoord_symm_apply, smul_eq_mul, P])
  set h : ℝ → ℝ := fun θ => 1 / 6 - ∑ y ∈ Y, capLoss y θ with hhdef
  have hFge : ∀ θ, ENNReal.ofReal (h θ) ≤ F θ := by
    intro θ
    obtain ⟨ρ, hρ0, hS, hρ⟩ := exists_rho hY1 hY2 θ
    show ENNReal.ofReal (1 / 6 - ∑ y ∈ Y, capLoss y θ) ≤ F θ
    rw [← hρ]; exact ray_ge hρ0 hS
  have hh0 : ∀ θ, 0 ≤ h θ := by
    intro θ
    obtain ⟨ρ, hρ0, hS, hρ⟩ := exists_rho hY1 hY2 θ
    show 0 ≤ 1 / 6 - ∑ y ∈ Y, capLoss y θ
    rw [← hρ]; positivity
  have hLi : ∀ y ∈ Y, IntervalIntegrable (capLoss y) volume (-π) π := fun y hy =>
    intervalIntegrable_of_bdd (measurable_capLoss y) (1 / 6) (fun θ => by
      rw [abs_of_nonneg (capLoss_nonneg y θ (hY1 y hy))]; exact capLoss_le y θ) _ _
  have hAi : ∀ y ∈ Y, IntervalIntegrable (capAct y) volume (-π) π := fun y _ =>
    intervalIntegrable_of_bdd (measurable_capAct y) 1 (fun θ => by
      unfold capAct; split_ifs <;> norm_num) _ _
  have hSi : IntervalIntegrable (fun θ => ∑ y ∈ Y, capLoss y θ) volume (-π) π := by
    have := IntervalIntegrable.sum Y hLi
    convert this using 1; ext θ; simp [Finset.sum_apply]
  have hSA : IntervalIntegrable (fun θ => ∑ y ∈ Y, capAct y θ) volume (-π) π := by
    have := IntervalIntegrable.sum Y hAi
    convert this using 1; ext θ; simp [Finset.sum_apply]
  have hint : IntervalIntegrable h volume (-π) π :=
    IntervalIntegrable.sub intervalIntegrable_const hSi
  have hK : 0 ≤ (2 * π - 3 * √3) / (12 * π) := by
    apply div_nonneg _ (by positivity)
    nlinarith
  have hcalc : √3 / 2 ≤ ∫ θ in (-π)..π, h θ := by
    show √3 / 2 ≤ ∫ θ in (-π)..π, (1 / 6 - ∑ y ∈ Y, capLoss y θ)
    rw [intervalIntegral.integral_sub intervalIntegrable_const hSi,
      intervalIntegral.integral_finset_sum hLi, intervalIntegral.integral_const]
    have h1 : ∑ y ∈ Y, ∫ θ in (-π)..π, capLoss y θ ≤
        (2 * π - 3 * √3) / (12 * π) * ∫ θ in (-π)..π, ∑ y ∈ Y, capAct y θ := by
      rw [intervalIntegral.integral_finset_sum hAi, Finset.mul_sum]
      exact Finset.sum_le_sum fun y hy => capLoss_integral_le (hY1 y hy)
    have h2 : ∫ θ in (-π)..π, ∑ y ∈ Y, capAct y θ ≤ ∫ θ in (-π)..π, (1 : ℝ) :=
      intervalIntegral.integral_mono_on (by linarith) hSA
        intervalIntegrable_const fun θ _ => sum_capAct_le hY1 hY2 θ
    rw [intervalIntegral.integral_const] at h2
    simp only [smul_eq_mul, mul_one, sub_neg_eq_add] at h2 ⊢
    have h3 := mul_le_mul_of_nonneg_left h2 hK
    have e : (2 * π - 3 * √3) / (12 * π) * (π + π) = π / 3 - √3 / 2 := by
      field_simp; ring
    rw [e] at h3
    linarith
  have hIoo : IntegrableOn h (Ioo (-π) π) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)).1 hint
  calc ENNReal.ofReal (√3 / 2) ≤ ENNReal.ofReal (∫ θ in Ioo (-π) π, h θ) := by
        apply ENNReal.ofReal_le_ofReal
        rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith)]
        exact hcalc
    _ = ∫⁻ θ in Ioo (-π) π, ENNReal.ofReal (h θ) :=
        ofReal_integral_eq_lintegral_ofReal hIoo (Filter.Eventually.of_forall hh0)
    _ ≤ ∫⁻ θ in Ioo (-π) π, F θ := lintegral_mono hFge
    _ = volume A' := hpolar.symm

lemma measurableSet_cellSet (Y : Finset (ℝ × ℝ)) : MeasurableSet (cellSet Y) := by
  have : cellSet Y = {z | nsq z < 1 / 3} ∩
      ⋂ y ∈ Y, {z : ℝ × ℝ | 2 * (z.1 * y.1 + z.2 * y.2) < nsq y} := by
    ext z; simp [cellSet]
  rw [this]
  exact (measurableSet_lt (by unfold nsq; fun_prop) measurable_const).inter
    (Finset.measurableSet_biInter Y fun y _ => measurableSet_lt (by fun_prop) measurable_const)

/-! ### Truncated Voronoi cells of a separated planar set -/

/-- The Voronoi cell of `p ∈ X`, truncated to the disc of radius `1/√3` about `p`. -/
def voronoiCell (X : Finset Plane) (p : Plane) : Set Plane :=
  {z | dist z p ^ 2 < 1 / 3 ∧ ∀ q ∈ X, q ≠ p → dist z p < dist z q}

/-- Coordinates of a point of the plane. -/
def toR2 (z : Plane) : ℝ × ℝ := (z 0, z 1)

lemma nsq_toR2_sub (z p : Plane) : nsq (toR2 (z - p)) = dist z p ^ 2 := by
  rw [dist_sq_coord]; simp [nsq, toR2]

lemma measurableSet_voronoiCell (X : Finset Plane) (p : Plane) :
    MeasurableSet (voronoiCell X p) := by
  have : voronoiCell X p = {z | dist z p ^ 2 < 1 / 3} ∩
      ⋂ q ∈ X.erase p, {z : Plane | dist z p < dist z q} := by
    ext z; simp only [voronoiCell, mem_setOf_eq, mem_inter_iff, mem_iInter, Finset.mem_erase]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun q ⟨hq, hqX⟩ => h2 q hqX hq⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun q hqX hq => h2 q ⟨hq, hqX⟩⟩
  rw [this]
  exact (measurableSet_lt (by fun_prop) measurable_const).inter
    (Finset.measurableSet_biInter _ fun q _ => measurableSet_lt (by fun_prop) (by fun_prop))

/-- Each truncated Voronoi cell of a separated set has area at least `√3/2`, the area of the
regular hexagon of inradius `1/2`. -/
theorem volume_voronoiCell_ge {X : Finset Plane} (hX : IsSeparated X) {p : Plane} (hp : p ∈ X) :
    ENNReal.ofReal (√3 / 2) ≤ volume (voronoiCell X p) := by
  set Y := (X.erase p).image (fun q => toR2 (q - p)) with hYdef
  have hY1 : ∀ y ∈ Y, 1 ≤ nsq y := by
    intro y hy
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨hqp, hqX⟩ := Finset.mem_erase.1 hq
    rw [nsq_toR2_sub]
    have := hX q hqX p hp hqp
    nlinarith
  have hY2 : ∀ y1 ∈ Y, ∀ y2 ∈ Y, y1 ≠ y2 → 1 ≤ nsq (y1 - y2) := by
    intro y1 h1 y2 h2 hne
    obtain ⟨q1, hq1, rfl⟩ := Finset.mem_image.1 h1
    obtain ⟨q2, hq2, rfl⟩ := Finset.mem_image.1 h2
    have hq : q1 ≠ q2 := by rintro rfl; exact hne rfl
    have e : toR2 (q1 - p) - toR2 (q2 - p) = toR2 (q1 - q2) := by
      simp only [toR2, PiLp.sub_apply, Prod.mk_sub_mk]; congr 1 <;> ring
    rw [e, nsq_toR2_sub]
    have := hX q1 (Finset.mem_erase.1 hq1).2 q2 (Finset.mem_erase.1 hq2).2 hq
    nlinarith
  set g : Plane → ℝ × ℝ := fun z => toR2 (z - p) with hg
  have hgm : MeasurePreserving g volume volume :=
    ((volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (ι := Fin 2))).comp
      (measurePreserving_sub_right volume p)
  have hsub : g ⁻¹' cellSet Y ⊆ voronoiCell X p := by
    intro z hz
    obtain ⟨h1, h2⟩ := hz
    simp only [g] at h1 h2
    rw [nsq_toR2_sub] at h1
    refine ⟨h1, fun q hqX hqp => ?_⟩
    have hy : toR2 (q - p) ∈ Y := Finset.mem_image.2 ⟨q, Finset.mem_erase.2 ⟨hqp, hqX⟩, rfl⟩
    have h3 := h2 _ hy
    rw [nsq_toR2_sub] at h3
    have e1 := dist_sq_coord z p
    have e2 := dist_sq_coord z q
    have e3 := dist_sq_coord q p
    simp only [toR2, PiLp.sub_apply] at h3
    have : dist z p ^ 2 < dist z q ^ 2 := by nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 dist_nonneg this
  calc ENNReal.ofReal (√3 / 2) ≤ volume (cellSet Y) := volume_cellSet_ge hY1 hY2
    _ = volume (g ⁻¹' cellSet Y) :=
        (hgm.measure_preimage (measurableSet_cellSet Y).nullMeasurableSet).symm
    _ ≤ volume (voronoiCell X p) := measure_mono hsub

/-- Packing bound: a separated set of `n` points with diameter `D` satisfies
`n · √3/2 ≤ π (D + 2)² / 4`. -/
theorem card_mul_le_of_separated {X : Finset Plane} (hX : IsSeparated X) (hne : X.Nonempty) :
    (X.card : ℝ) * (√3 / 2) ≤ π * (diam X + 2) ^ 2 / 4 := by
  have hdisj : (X : Set Plane).PairwiseDisjoint (voronoiCell X) := by
    intro p hp q hq hpq
    rw [Function.onFun, Set.disjoint_left]
    intro z hzp hzq
    have a := hzp.2 q hq (Ne.symm hpq)
    have b := hzq.2 p hp hpq
    linarith
  set K := ⋃ p ∈ X, Metric.closedBall p 1 with hK
  have hKc : IsCompact K := X.finite_toSet.isCompact_biUnion fun p _ => isCompact_closedBall p 1
  obtain ⟨p0, hp0⟩ := hne
  have hKne : K.Nonempty := ⟨p0, mem_biUnion hp0 (Metric.mem_closedBall_self zero_le_one)⟩
  have hD : 0 ≤ diam X := Metric.diam_nonneg
  have hKd : ∀ a ∈ K, ∀ b ∈ K, dist a b ≤ diam X + 2 := by
    intro a ha b hb
    obtain ⟨p, hp, hap⟩ := mem_iUnion₂.1 ha
    obtain ⟨q, hq, hbq⟩ := mem_iUnion₂.1 hb
    have h1 := Metric.mem_closedBall.1 hap
    have h2 := Metric.mem_closedBall.1 hbq
    have h3 := dist_le_diam hp hq
    have := dist_triangle4 a p q b
    rw [dist_comm q b] at this
    linarith
  have hsub : (⋃ p ∈ X, voronoiCell X p) ⊆ K := by
    refine iUnion₂_mono fun p _ z hz => Metric.mem_closedBall.2 ?_
    have h := hz.1
    have : dist z p < 1 := by nlinarith [dist_nonneg (x := z) (y := p)]
    exact this.le
  have hvol := (measure_mono (μ := volume) hsub).trans (volume_le_of_isCompact hKc hKne
    (by linarith) hKd)
  rw [measure_biUnion_finset hdisj fun p _ => measurableSet_voronoiCell X p] at hvol
  have hcard : X.card • ENNReal.ofReal (√3 / 2) ≤ ∑ p ∈ X, volume (voronoiCell X p) :=
    Finset.card_nsmul_le_sum _ _ _ fun p hp => volume_voronoiCell_ge hX hp
  rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at hcard
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 (hcard.trans hvol)

/-- Lemma 3.1 (density side) for separated sets: `n ≤ c D² + 8 c D` when `n ≥ 2`. -/
theorem card_le_density_of_separated {X : Finset Plane} (hX : IsSeparated X)
    (hcard : 2 ≤ X.card) :
    (X.card : ℝ) ≤ cDensity * diam X ^ 2 + 8 * cDensity * diam X := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 (by omega : 1 < X.card)
  have hD : 1 ≤ diam X := (hX x hx y hy hxy).trans (dist_le_diam hx hy)
  have h := card_mul_le_of_separated hX ⟨x, hx⟩
  have hs : (0 : ℝ) < √3 := by positivity
  have hc : 0 < cDensity := by unfold cDensity; positivity
  have e : π * (diam X + 2) ^ 2 / 4 = cDensity * (diam X + 2) ^ 2 * (√3 / 2) := by
    unfold cDensity; field_simp; norm_num
  rw [e] at h
  have h2 : (X.card : ℝ) ≤ cDensity * (diam X + 2) ^ 2 :=
    le_of_mul_le_mul_right h (by positivity)
  nlinarith

end Erdos99
end

end Density

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `Directions`
-/

section Directions

/-!
# Directions modulo `π/3`

The manuscript measures directions of unit edges modulo `π/3` (Lemma 3.3: clustering "modulo
`π/3`").  We encode the direction of a nonzero vector `u` modulo `π/3` by the unit complex number
`dir6 u = (u / |u|)⁶`, identifying the plane with `ℂ`.  Two directions agree modulo `π/3` iff their
`dir6` agree, and `dir6 (-u) = dir6 u`, so the direction of an (unordered) edge is well defined.

The key computation (`dir6_chord`) is used for two-edge hull returns in Lemma 3.4: if two unit
vectors have directions (mod `π/3`) close to `c₁`, `c₂`, then the direction of their sum (the hull
chord) is close to one of the two square roots of `c₁ c₂`.
-/

open scoped BigOperators Real ComplexConjugate

@[expose] public noncomputable section

open Classical

namespace Erdos99

/-- The direction of `u` modulo `π/3`, as the unit complex number `(u / |u|)⁶`. -/
def dir6 (u : Plane) : ℂ := (toC u / (‖u‖ : ℂ)) ^ 6

lemma norm_toC (u : Plane) : ‖toC u‖ = ‖u‖ := toC.norm_map u

lemma dir6_neg (u : Plane) : dir6 (-u) = dir6 u := by
  simp only [dir6, map_neg, norm_neg, neg_div]
  exact Even.neg_pow ⟨3, rfl⟩ _

lemma norm_dir6 {u : Plane} (hu : u ≠ 0) : ‖dir6 u‖ = 1 := by
  have h : ‖u‖ ≠ 0 := norm_ne_zero_iff.2 hu
  simp [dir6, norm_pow, h]

lemma dir6_of_norm_eq_one {u : Plane} (hu : ‖u‖ = 1) : dir6 u = (toC u) ^ 6 := by
  simp [dir6, hu]

lemma dir6_eq_of_sameDir {e f : Sym2 Plane} (h : SameDir e f) : dir6 (dv e) = dir6 (dv f) := by
  rcases h with h | h <;> rw [h]; rw [dir6_neg]

/-- For unit complex numbers `z₁, z₂` with `s = z₁ + z₂ ≠ 0`, `(s / |s|)² = z₁ z₂`. -/
lemma sq_div_norm_add {z1 z2 : ℂ} (h1 : ‖z1‖ = 1) (h2 : ‖z2‖ = 1) (hs : z1 + z2 ≠ 0) :
    ((z1 + z2) / (‖z1 + z2‖ : ℂ)) ^ 2 = z1 * z2 := by
  have hc1 : z1 * conj z1 = 1 := by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]; simp
  have hc2 : z2 * conj z2 = 1 := by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h2]; simp
  have hr : ((‖z1 + z2‖ : ℝ) : ℂ) ^ 2 = (z1 + z2) * conj (z1 + z2) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hr0 : ((‖z1 + z2‖ : ℝ) : ℂ) ^ 2 ≠ 0 := by
    have : ‖z1 + z2‖ ≠ 0 := norm_ne_zero_iff.2 hs
    exact pow_ne_zero _ (Complex.ofReal_ne_zero.2 this)
  rw [div_pow, div_eq_iff hr0, hr, map_add]
  linear_combination -(z1 + z2) * z2 * hc1 - (z1 + z2) * z1 * hc2

/-- `dir6 (u₁ + u₂)² = dir6 u₁ · dir6 u₂` for unit vectors with nonzero sum. -/
lemma dir6_add_sq {u1 u2 : Plane} (h1 : ‖u1‖ = 1) (h2 : ‖u2‖ = 1) (hs : u1 + u2 ≠ 0) :
    dir6 (u1 + u2) ^ 2 = dir6 u1 * dir6 u2 := by
  rw [dir6_of_norm_eq_one h1, dir6_of_norm_eq_one h2, dir6, map_add,
    show ‖u1 + u2‖ = ‖toC u1 + toC u2‖ by rw [← map_add, norm_toC]]
  have hs' : toC u1 + toC u2 ≠ 0 := by
    rw [← map_add]; exact (map_ne_zero_iff _ toC.injective).2 hs
  have key := sq_div_norm_add (by rwa [norm_toC]) (by rwa [norm_toC]) hs'
  rw [← pow_mul, show 6 * 2 = 2 * 6 by rfl, pow_mul, key]
  ring

/-- A chosen square root of a complex number. -/
def sqrtC (c : ℂ) : ℂ := c ^ ((↑(2 : ℕ) : ℂ)⁻¹)

lemma sqrtC_sq (c : ℂ) : sqrtC c ^ 2 = c := Complex.cpow_nat_inv_pow c (by norm_num)

/-- **Direction of a chord.**  If unit vectors `u₁`, `u₂` (with `u₁ + u₂ ≠ 0`) have directions
modulo `π/3` within `ρ` of the unit complex numbers `c₁`, `c₂`, then the direction of `u₁ + u₂`
is within `2ρ` of one of the two square roots `± √(c₁ c₂)`. -/
lemma dir6_chord {u1 u2 : Plane} (h1 : ‖u1‖ = 1) (h2 : ‖u2‖ = 1) (hs : u1 + u2 ≠ 0)
    {c1 c2 : ℂ} (hc1 : ‖c1‖ = 1) (hc2 : ‖c2‖ = 1) {ρ : ℝ}
    (d1 : ‖dir6 u1 - c1‖ ≤ ρ) (d2 : ‖dir6 u2 - c2‖ ≤ ρ) :
    ‖dir6 (u1 + u2) - sqrtC (c1 * c2)‖ ≤ 2 * ρ ∨
      ‖dir6 (u1 + u2) - -sqrtC (c1 * c2)‖ ≤ 2 * ρ := by
  set z := dir6 (u1 + u2)
  set ξ := sqrtC (c1 * c2)
  have hz : ‖z‖ = 1 := norm_dir6 hs
  have hξ2 : ξ ^ 2 = c1 * c2 := sqrtC_sq _
  have hξ : ‖ξ‖ = 1 := by
    have : ‖ξ‖ ^ 2 = 1 := by rw [← norm_pow, hξ2, norm_mul, hc1, hc2, one_mul]
    have h0 := norm_nonneg ξ
    nlinarith
  have hu2 : ‖dir6 u2‖ = 1 := norm_dir6 (by rintro rfl; simp at h2)
  have hsq : ‖z ^ 2 - ξ ^ 2‖ ≤ 2 * ρ := by
    rw [dir6_add_sq h1 h2 hs, hξ2,
      show dir6 u1 * dir6 u2 - c1 * c2 = (dir6 u1 - c1) * dir6 u2 + c1 * (dir6 u2 - c2) by ring]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, hu2, hc1]
    linarith
  have hfac : z ^ 2 - ξ ^ 2 = (z - ξ) * (z + ξ) := by ring
  rw [hfac, norm_mul] at hsq
  have htri : 2 ≤ ‖z - ξ‖ + ‖z + ξ‖ := by
    have := norm_sub_le (z + ξ) (z - ξ)
    rw [show z + ξ - (z - ξ) = 2 * ξ by ring, norm_mul, hξ] at this
    norm_num at this
    linarith
  have n1 := norm_nonneg (z - ξ)
  have n2 := norm_nonneg (z + ξ)
  rcases le_total ‖z - ξ‖ ‖z + ξ‖ with h | h
  · left; nlinarith
  · right; rw [sub_neg_eq_add]; nlinarith

end Erdos99
end

end Directions

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `Clustering`
-/

section Clustering

/-!
# Clustering of long track directions (Lemma 3.3, last assertion)

For a rhombus `Q` with smaller angle `α_Q ∈ (π/3, π/2]`, the two side directions agree modulo
`π/3` up to `α_Q - π/3`.  We measure this by the *defect* `rhombusDefect Q`, the sum over the
eight (vertex, two neighbours) triples of `Q` of `|dir6 (a - b) - dir6 (c - b)|`; each summand is at
most `6 (α_Q - π/3)`, so equation (1) of the manuscript bounds the total defect by `O(D)`.

The clustering statement of Lemma 3.3 is a purely combinatorial consequence: if the total defect is
at most `K`, then for a cutoff `L` and tolerance `ε`, after removing at most `4K / (εL)` tracks,
all remaining tracks of length at least `L` have directions (mod `π/3`) within `2ε` of at most
`2s / L` centres.
-/

open scoped BigOperators Real

@[expose] public noncomputable section

open Classical

namespace Erdos99

/-- Ordered triples `(a, b, c)` of points of `Q` with `ab`, `bc` unit and `a ≠ c`. -/
def defectTriples (Q : Finset Plane) : Finset (Plane × Plane × Plane) :=
  (Q ×ˢ Q ×ˢ Q).filter (fun t => dist t.1 t.2.1 = 1 ∧ dist t.2.1 t.2.2 = 1 ∧ t.1 ≠ t.2.2)

/-- The defect of a rhombus: `∑ |dir6 (a - b) - dir6 (c - b)|` over ordered triples `(a, b, c)`
of its points with `ab`, `bc` unit and `a ≠ c`. -/
def rhombusDefect (Q : Finset Plane) : ℝ :=
  ∑ t ∈ defectTriples Q, ‖dir6 (t.1 - t.2.1) - dir6 (t.2.2 - t.2.1)‖

lemma rhombusDefect_nonneg (Q : Finset Plane) : 0 ≤ rhombusDefect Q :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- The direction (mod `π/3`) of a track. -/
def tdir (T : Finset (Sym2 Plane)) : ℂ := if h : T.Nonempty then dir6 (dv h.choose) else 0

lemma tdir_eq {X : Finset Plane} {T : Finset (Sym2 Plane)} (hT : T ∈ tracks X)
    {e : Sym2 Plane} (he : e ∈ T) : tdir T = dir6 (dv e) := by
  have hne : T.Nonempty := ⟨e, he⟩
  rw [tdir, dif_pos hne]
  have h2 : ∀ f ∈ T, f ∈ trackOf X e := fun f hf => (eq_trackOf_of_mem hT he) ▸ hf
  exact dir6_eq_of_sameDir (sameDir_of_mem_trackOf (h2 _ hne.choose_spec))

lemma norm_tdir {X : Finset Plane} {T : Finset (Sym2 Plane)} (hT : T ∈ tracks X) :
    ‖tdir T‖ = 1 := by
  obtain ⟨e, he, hu⟩ := exists_rep_of_mem_tracks hT
  rw [tdir_eq hT he]
  have h1 := norm_dv_of_mem_unitEdges hu
  exact norm_dir6 (fun h => by rw [h, norm_zero] at h1; norm_num at h1)

lemma dir6_dv_mk (x y : Plane) : dir6 (dv s(x, y)) = dir6 (x - y) := by
  rcases dv_mk x y with h | h <;> rw [h]
  rw [← neg_sub, dir6_neg]

/-- Two distinct tracks crossing at a rhombus have directions within its defect. -/
lemma norm_tdir_sub_le_defect {X : Finset Plane} (hX : IsSeparated X)
    (htri : ¬ HasUnitTriangle X) {Q : Finset Plane} (hQ : Q ∈ rhombi X)
    {T T' : Finset (Sym2 Plane)} (hT : T ∈ tracks X) (hT' : T' ∈ tracks X) (hne : T ≠ T')
    (hc : Crosses T Q) (hc' : Crosses T' Q) : ‖tdir T - tdir T'‖ ≤ rhombusDefect Q := by
  obtain ⟨a, b, c, d, h⟩ := exists_rhombusData hX htri hQ
  have h1 : tdir (trackOf X s(a, b)) = dir6 (a - b) := by
    rw [tdir_eq (Finset.mem_image_of_mem _ h.rhombusEdge_ab) (mem_trackOf_self h.rhombusEdge_ab),
      dir6_dv_mk]
  have h2 : tdir (trackOf X s(b, c)) = dir6 (c - b) := by
    rw [tdir_eq (Finset.mem_image_of_mem _ h.rotate.rhombusEdge_ab)
      (mem_trackOf_self h.rotate.rhombusEdge_ab), dir6_dv_mk, ← neg_sub, dir6_neg]
  have ha : a ∈ Q := by rw [h.eq]; simp
  have hb : b ∈ Q := by rw [h.eq]; simp
  have hc0 : c ∈ Q := by rw [h.eq]; simp
  have hmem : (a, b, c) ∈ defectTriples Q :=
    Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨ha, Finset.mem_product.2 ⟨hb, hc0⟩⟩,
      h.hab, h.hbc, h.distinct.2.1⟩
  have hle : ‖dir6 (a - b) - dir6 (c - b)‖ ≤ rhombusDefect Q := by
    have := Finset.single_le_sum (f := fun t : Plane × Plane × Plane =>
      ‖dir6 (t.1 - t.2.1) - dir6 (t.2.2 - t.2.1)‖) (fun _ _ => norm_nonneg _) hmem
    exact this
  rcases h.crosses hT hc with e1 | e1 <;> rcases h.crosses hT' hc' with e2 | e2
  · exact absurd (e1.trans e2.symm) hne
  · rw [e1, e2, h1, h2]; exact hle
  · rw [e1, e2, h1, h2, norm_sub_rev]; exact hle
  · exact absurd (e1.trans e2.symm) hne

/-- Double counting: every rhombus lies on exactly two tracks. -/
lemma sum_card_filter_crosses {X : Finset Plane} (hX : IsSeparated X)
    (htri : ¬ HasUnitTriangle X) {B : Finset (Finset Plane)} (hB : B ⊆ rhombi X) :
    ∑ T ∈ tracks X, (B.filter (Crosses T)).card = 2 * B.card := by
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm, mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun R hR => ?_
  rw [← Finset.card_filter]
  obtain ⟨T, hT, T', hT', hne, hiff⟩ := rhombus_two_tracks_of_separated hX htri (hB hR)
  have : (tracks X).filter (fun T'' => Crosses T'' R) = {T, T'} := by
    ext T''
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩; exact (hiff T'' h1).1 h2
    · rintro (rfl | rfl)
      · exact ⟨hT, (hiff _ hT).2 (Or.inl rfl)⟩
      · exact ⟨hT', (hiff _ hT').2 (Or.inr rfl)⟩
  rw [this, Finset.card_pair hne]

/-- A family of tracks with pairwise `2ε`-separated directions. -/
def SepFam (ε : ℝ) (F : Finset (Finset (Sym2 Plane))) : Prop :=
  ∀ T1 ∈ F, ∀ T2 ∈ F, T1 ≠ T2 → 2 * ε < ‖tdir T1 - tdir T2‖

/-- **Clustering of long tracks (Lemma 3.3, last assertion).**  If the total rhombus defect is at
most `K`, then for every tolerance `ε > 0` and cutoff `L > 0` there are a set `Disc` of at most
`4K / (εL)` tracks and a set `Cs` of at most `2s / L` unit complex numbers such that every track of
length at least `L` outside `Disc` has direction (mod `π/3`) within `2ε` of some element of
`Cs`. -/
theorem track_clustering {X : Finset Plane} (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X)
    {K ε L : ℝ} (hε : 0 < ε) (hL : 0 < L) (hK : ∑ Q ∈ rhombi X, rhombusDefect Q ≤ K) :
    ∃ Disc ⊆ tracks X, ∃ Cs : Finset ℂ, (∀ c ∈ Cs, ‖c‖ = 1) ∧
      (Disc.card : ℝ) * (ε * L) ≤ 4 * K ∧ (Cs.card : ℝ) * L ≤ 2 * (tracks X).card ∧
      ∀ T ∈ tracks X, T ∉ Disc → L ≤ trackLength X T → ∃ c ∈ Cs, ‖tdir T - c‖ ≤ 2 * ε := by
  set bad := (rhombi X).filter (fun Q => ε < rhombusDefect Q)
  have hbad : (bad.card : ℝ) * ε ≤ K := by
    have h1 : ∑ Q ∈ bad, ε ≤ ∑ Q ∈ bad, rhombusDefect Q :=
      Finset.sum_le_sum fun Q hQ => (Finset.mem_filter.1 hQ).2.le
    have h2 : ∑ Q ∈ bad, rhombusDefect Q ≤ ∑ Q ∈ rhombi X, rhombusDefect Q :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun Q _ _ => rhombusDefect_nonneg Q)
    rw [Finset.sum_const, nsmul_eq_mul] at h1
    linarith
  set Disc := (tracks X).filter (fun T => L ≤ trackLength X T ∧
    L / 2 ≤ ((bad.filter (Crosses T)).card : ℝ))
  have hDisc : (Disc.card : ℝ) * (ε * L) ≤ 4 * K := by
    have h1 : (Disc.card : ℝ) * (L / 2) ≤ ∑ T ∈ Disc, ((bad.filter (Crosses T)).card : ℝ) := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_le_sum fun T hT => (Finset.mem_filter.1 hT).2.2
    have h2 : ∑ T ∈ Disc, ((bad.filter (Crosses T)).card : ℝ) ≤
        ∑ T ∈ tracks X, ((bad.filter (Crosses T)).card : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
    have h3 : ∑ T ∈ tracks X, ((bad.filter (Crosses T)).card : ℝ) = 2 * bad.card := by
      exact_mod_cast sum_card_filter_crosses hX htri (Finset.filter_subset _ _)
    have h4 : (Disc.card : ℝ) * (L / 2) ≤ 2 * bad.card := by linarith
    have h5 : (Disc.card : ℝ) * (ε * L) = 2 * ε * ((Disc.card : ℝ) * (L / 2)) := by ring
    rw [h5]
    have := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 2 * ε)
    linarith
  set Surv := (tracks X).filter (fun T => T ∉ Disc ∧ L ≤ trackLength X T)
  -- good neighbours
  set Nb : Finset (Sym2 Plane) → Finset (Finset (Sym2 Plane)) := fun T =>
    (tracks X).filter (fun T' => T' ≠ T ∧ ∃ Q ∈ rhombi X, rhombusDefect Q ≤ ε ∧ Crosses T Q ∧
      Crosses T' Q)
  have hNb_close : ∀ T ∈ tracks X, ∀ T' ∈ Nb T, ‖tdir T - tdir T'‖ ≤ ε := by
    intro T hT T' hT'
    obtain ⟨hT'1, hne, Q, hQ, hdef, hc, hc'⟩ := Finset.mem_filter.1 hT'
    exact (norm_tdir_sub_le_defect hX htri hQ hT hT'1 (Ne.symm hne) hc hc').trans hdef
  have hNb_card : ∀ T ∈ Surv, L / 2 ≤ ((Nb T).card : ℝ) := by
    intro T hT
    obtain ⟨hT, hnd, hlong⟩ := Finset.mem_filter.1 hT
    have hfew : ((bad.filter (Crosses T)).card : ℝ) < L / 2 := by
      by_contra h
      push_neg at h
      exact hnd (Finset.mem_filter.2 ⟨hT, hlong, h⟩)
    set G := (rhombi X).filter (fun Q => Crosses T Q ∧ rhombusDefect Q ≤ ε)
    have hsplit : trackLength X T = (bad.filter (Crosses T)).card + G.card := by
      unfold trackLength
      rw [← Finset.card_filter_add_card_filter_not (fun Q => ε < rhombusDefect Q)]
      congr 1
      · congr 1; ext Q; simp only [bad, Finset.mem_filter]; tauto
      · congr 1; ext Q; simp only [G, Finset.mem_filter, not_lt]; tauto
    have hG : L / 2 < (G.card : ℝ) := by
      have : (trackLength X T : ℝ) = (bad.filter (Crosses T)).card + G.card := by
        exact_mod_cast hsplit
      linarith
    have hGN : G.card ≤ (Nb T).card := by
      refine Finset.card_le_card_of_forall_subsingleton
        (fun Q T' => Crosses T' Q ∧ T' ≠ T) ?_ ?_
      · intro Q hQ
        obtain ⟨hQ, hc, hdef⟩ := Finset.mem_filter.1 hQ
        obtain ⟨T1, hT1, T2, hT2, hne, hiff⟩ := rhombus_two_tracks_of_separated hX htri hQ
        rcases (hiff T hT).1 hc with rfl | rfl
        · have c2 := (hiff T2 hT2).2 (Or.inr rfl)
          exact ⟨T2, Finset.mem_filter.2 ⟨hT2, Ne.symm hne, Q, hQ, hdef, hc, c2⟩, c2, Ne.symm hne⟩
        · have c1 := (hiff T1 hT1).2 (Or.inl rfl)
          exact ⟨T1, Finset.mem_filter.2 ⟨hT1, hne, Q, hQ, hdef, hc, c1⟩, c1, hne⟩
      · intro T' hT' Q1 hQ1 Q2 hQ2
        have hT'1 := (Finset.mem_filter.1 hT').1
        have hsub := tracks_cross_at_most_once_of_separated hX htri hT hT'1
          (Ne.symm hQ1.2.2)
        have m1 : Q1 ∈ (rhombi X).filter (fun R => Crosses T R ∧ Crosses T' R) :=
          Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hQ1.1).1,
            (Finset.mem_filter.1 hQ1.1).2.1, hQ1.2.1⟩
        have m2 : Q2 ∈ (rhombi X).filter (fun R => Crosses T R ∧ Crosses T' R) :=
          Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hQ2.1).1,
            (Finset.mem_filter.1 hQ2.1).2.1, hQ2.2.1⟩
        exact Finset.card_le_one.1 hsub _ m1 _ m2
    have : (G.card : ℝ) ≤ (Nb T).card := by exact_mod_cast hGN
    linarith
  -- a maximal `2ε`-separated family of surviving tracks
  set Sep := Surv.powerset.filter (SepFam ε)
  have hSep : Sep.Nonempty :=
    ⟨∅, Finset.mem_filter.2 ⟨Finset.empty_mem_powerset _, by simp [SepFam]⟩⟩
  obtain ⟨F, hF, hFmax⟩ := Sep.exists_max_image Finset.card hSep
  obtain ⟨hFsub, hFsep⟩ := Finset.mem_filter.1 hF
  unfold SepFam at hFsep
  rw [Finset.mem_powerset] at hFsub
  have hcover : ∀ T ∈ Surv, ∃ T0 ∈ F, ‖tdir T - tdir T0‖ ≤ 2 * ε := by
    intro T hT
    by_contra hno
    push_neg at hno
    have hTF : T ∉ F := fun h => by have := hno T h; rw [sub_self, norm_zero] at this; linarith
    have hins : insert T F ∈ Sep := by
      refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.insert_subset hT hFsub), ?_⟩
      unfold SepFam
      intro T1 hT1 T2 hT2 hne
      rw [Finset.mem_insert] at hT1 hT2
      rcases hT1 with rfl | hT1 <;> rcases hT2 with rfl | hT2
      · exact absurd rfl hne
      · exact hno T2 hT2
      · rw [norm_sub_rev]; exact hno T1 hT1
      · exact hFsep T1 hT1 T2 hT2 hne
    have := hFmax _ hins
    rw [Finset.card_insert_of_notMem hTF] at this
    omega
  have hdisj : (F : Set (Finset (Sym2 Plane))).PairwiseDisjoint Nb := by
    intro T1 hT1 T2 hT2 hne
    rw [Function.onFun, Finset.disjoint_left]
    intro T' h1 h2
    have hT1t := (Finset.mem_filter.1 (hFsub hT1)).1
    have hT2t := (Finset.mem_filter.1 (hFsub hT2)).1
    have a1 := hNb_close T1 hT1t T' h1
    have a2 := hNb_close T2 hT2t T' h2
    have := hFsep T1 hT1 T2 hT2 hne
    have := norm_sub_le_norm_sub_add_norm_sub (tdir T1) (tdir T') (tdir T2)
    rw [norm_sub_rev (tdir T') (tdir T2)] at this
    linarith
  have hFcard : (F.card : ℝ) * L ≤ 2 * (tracks X).card := by
    have h1 : (F.card : ℝ) * (L / 2) ≤ ∑ T ∈ F, ((Nb T).card : ℝ) := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_le_sum fun T hT => hNb_card T (hFsub hT)
    have h2 : ∑ T ∈ F, (Nb T).card = (F.biUnion Nb).card := (Finset.card_biUnion hdisj).symm
    have h3 : (F.biUnion Nb).card ≤ (tracks X).card :=
      Finset.card_le_card (Finset.biUnion_subset.2 fun T _ => Finset.filter_subset _ _)
    have h4 : ∑ T ∈ F, ((Nb T).card : ℝ) ≤ (tracks X).card := by
      have : ∑ T ∈ F, (Nb T).card ≤ (tracks X).card := h2 ▸ h3
      exact_mod_cast this
    linarith
  refine ⟨Disc, Finset.filter_subset _ _, F.image tdir, ?_, hDisc, ?_, ?_⟩
  · intro c hc
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hc
    exact norm_tdir (Finset.mem_filter.1 (hFsub hT)).1
  · have : ((F.image tdir).card : ℝ) ≤ F.card := by exact_mod_cast Finset.card_image_le
    nlinarith
  · intro T hT hnd hlong
    obtain ⟨T0, hT0, hclose⟩ := hcover T (Finset.mem_filter.2 ⟨hT, hnd, hlong⟩)
    exact ⟨tdir T0, Finset.mem_image_of_mem _ hT0, hclose⟩

end Erdos99
end

end Clustering

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `RhombusArea`
-/

section RhombusArea

/-!
# Rhombus areas and the angle-excess bound

For a unit rhombus `Q` of a separated set without unit triangles we consider the open
parallelogram it spans.  We show:

* these open parallelograms are pairwise disjoint (unit edges do not cross, and a closed unit
  rhombus contains no further point of the set), and they lie in the convex hull of the set;
* the area of `Q` is `|u × w|` for its side vectors `u, w`;
* the defect `rhombusDefect Q` is at most `1024 (|Q| - a*)`.

Together with the isodiametric inequality and `q ≥ n - O(D)` this gives the angle-excess half of
equation (1) of the manuscript (`rhombus_defect_sum`).
-/

open scoped BigOperators Real
open MeasureTheory Set

@[expose] public noncomputable section

open Classical

namespace Erdos99

/-! ## Parallelograms -/

/-- The cross product `u × w = u₀ w₁ - u₁ w₀`. -/
def cr (u w : Plane) : ℝ := u 0 * w 1 - u 1 * w 0

/-- The open parallelogram with vertex `a` and sides `u`, `w`. -/
def paraOpen (a u w : Plane) : Set Plane :=
  {z | ∃ s t : ℝ, 0 < s ∧ s < 1 ∧ 0 < t ∧ t < 1 ∧ z = a + s • u + t • w}

/-- The closed parallelogram with vertex `a` and sides `u`, `w`. -/
def paraClosed (a u w : Plane) : Set Plane :=
  {z | ∃ s t : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ 0 ≤ t ∧ t ≤ 1 ∧ z = a + s • u + t • w}

lemma cr_coords (a u w : Plane) (s t : ℝ) :
    cr (a + s • u + t • w - a) w = s * cr u w ∧ cr u (a + s • u + t • w - a) = t * cr u w := by
  simp only [cr, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  constructor <;> ring

lemma eq_of_cr {a u w z : Plane} (h : cr u w ≠ 0) :
    z = a + (cr (z - a) w / cr u w) • u + (cr u (z - a) / cr u w) • w := by
  have k0 : (z - a) 0 * cr u w = cr (z - a) w * u 0 + cr u (z - a) * w 0 := by
    simp only [cr, PiLp.sub_apply]; ring
  have k1 : (z - a) 1 * cr u w = cr (z - a) w * u 1 + cr u (z - a) * w 1 := by
    simp only [cr, PiLp.sub_apply]; ring
  simp only [PiLp.sub_apply] at k0 k1
  rw [plane_ext_iff]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  constructor
  · field_simp; linear_combination k0
  · field_simp; linear_combination k1

lemma paraOpen_eq {a u w : Plane} (h : cr u w ≠ 0) :
    paraOpen a u w = {z | 0 < cr (z - a) w / cr u w ∧ cr (z - a) w / cr u w < 1 ∧
      0 < cr u (z - a) / cr u w ∧ cr u (z - a) / cr u w < 1} := by
  ext z
  constructor
  · rintro ⟨s, t, h1, h2, h3, h4, rfl⟩
    obtain ⟨e1, e2⟩ := cr_coords a u w s t
    simp only [mem_setOf_eq, e1, e2, mul_div_cancel_right₀ _ h]
    exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨_, _, h1, h2, h3, h4, eq_of_cr h⟩

lemma paraClosed_eq {a u w : Plane} (h : cr u w ≠ 0) :
    paraClosed a u w = {z | 0 ≤ cr (z - a) w / cr u w ∧ cr (z - a) w / cr u w ≤ 1 ∧
      0 ≤ cr u (z - a) / cr u w ∧ cr u (z - a) / cr u w ≤ 1} := by
  ext z
  constructor
  · rintro ⟨s, t, h1, h2, h3, h4, rfl⟩
    obtain ⟨e1, e2⟩ := cr_coords a u w s t
    simp only [mem_setOf_eq, e1, e2, mul_div_cancel_right₀ _ h]
    exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨_, _, h1, h2, h3, h4, eq_of_cr h⟩

lemma continuous_cr_left (a w : Plane) : Continuous fun z : Plane => cr (z - a) w := by
  unfold cr; fun_prop

lemma continuous_cr_right (a u : Plane) : Continuous fun z : Plane => cr u (z - a) := by
  unfold cr; fun_prop

lemma isOpen_paraOpen {a u w : Plane} (h : cr u w ≠ 0) : IsOpen (paraOpen a u w) := by
  rw [paraOpen_eq h]
  have c1 := (continuous_cr_left a w).div_const (cr u w)
  have c2 := (continuous_cr_right a u).div_const (cr u w)
  have k : Continuous fun _ : Plane => (0 : ℝ) := continuous_const
  have k1 : Continuous fun _ : Plane => (1 : ℝ) := continuous_const
  have := ((isOpen_lt k c1).inter (isOpen_lt c1 k1)).inter ((isOpen_lt k c2).inter (isOpen_lt c2 k1))
  convert this using 1
  ext z; simp [and_assoc]

lemma isClosed_paraClosed {a u w : Plane} (h : cr u w ≠ 0) : IsClosed (paraClosed a u w) := by
  rw [paraClosed_eq h]
  have c1 := (continuous_cr_left a w).div_const (cr u w)
  have c2 := (continuous_cr_right a u).div_const (cr u w)
  have k : Continuous fun _ : Plane => (0 : ℝ) := continuous_const
  have k1 : Continuous fun _ : Plane => (1 : ℝ) := continuous_const
  have := ((isClosed_le k c1).inter (isClosed_le c1 k1)).inter
    ((isClosed_le k c2).inter (isClosed_le c2 k1))
  convert this using 1
  ext z; simp [and_assoc]

lemma paraOpen_subset_paraClosed (a u w : Plane) : paraOpen a u w ⊆ paraClosed a u w := by
  rintro z ⟨s, t, h1, h2, h3, h4, rfl⟩
  exact ⟨s, t, h1.le, h2.le, h3.le, h4.le, rfl⟩

lemma convex_paraOpen (a u w : Plane) : Convex ℝ (paraOpen a u w) := by
  rintro _ ⟨s, t, h1, h2, h3, h4, rfl⟩ _ ⟨s', t', h1', h2', h3', h4', rfl⟩ α β hα hβ hαβ
  obtain ⟨c1, c2⟩ := convex_Ioo (0 : ℝ) 1 ⟨h1, h2⟩ ⟨h1', h2'⟩ hα hβ hαβ
  obtain ⟨c3, c4⟩ := convex_Ioo (0 : ℝ) 1 ⟨h3, h4⟩ ⟨h3', h4'⟩ hα hβ hαβ
  simp only [smul_eq_mul] at c1 c2 c3 c4
  refine ⟨α * s + β * s', α * t + β * t', c1, c2, c3, c4, ?_⟩
  rw [plane_ext_iff]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  constructor
  · linear_combination (a 0) * hαβ
  · linear_combination (a 1) * hαβ

lemma paraClosed_subset_closure (a u w : Plane) : paraClosed a u w ⊆ closure (paraOpen a u w) := by
  rintro _ ⟨s, t, h1, h2, h3, h4, rfl⟩
  set f : ℝ → Plane := fun ε => a + ((1 - ε) * s + ε / 2) • u + ((1 - ε) * t + ε / 2) • w
  have hf : Continuous f := by fun_prop
  have hlim : Filter.Tendsto f (nhdsWithin 0 (Ioi 0)) (nhds (a + s • u + t • w)) := by
    have := (hf.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa [f] using this
  refine mem_closure_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with ε hε
  obtain ⟨e1, e2⟩ := hε
  exact ⟨_, _, by nlinarith, by nlinarith, by nlinarith, by nlinarith, rfl⟩

lemma add_smul_mem_segment (x v : Plane) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    x + θ • v ∈ segment ℝ x (x + v) :=
  ⟨1 - θ, θ, by linarith, h0, by ring, by module⟩

lemma coords_unique {a u w : Plane} (h : cr u w ≠ 0) {s t s' t' : ℝ}
    (he : a + s • u + t • w = a + s' • u + t' • w) : s = s' ∧ t = t' := by
  obtain ⟨e1, e2⟩ := cr_coords a u w s t
  obtain ⟨e1', e2'⟩ := cr_coords a u w s' t'
  rw [he] at e1 e2
  exact ⟨mul_right_cancel₀ h (e1.symm.trans e1'), mul_right_cancel₀ h (e2.symm.trans e2')⟩

/-- A point of the closed parallelogram that is not in the open one lies on a side. -/
lemma mem_sides_of_mem_paraClosed {a u w z : Plane} (hz : z ∈ paraClosed a u w)
    (hz' : z ∉ paraOpen a u w) :
    z ∈ segment ℝ a (a + u) ∨ z ∈ segment ℝ (a + u) (a + u + w) ∨
      z ∈ segment ℝ (a + w) (a + u + w) ∨ z ∈ segment ℝ a (a + w) := by
  obtain ⟨s, t, h1, h2, h3, h4, rfl⟩ := hz
  rcases h1.lt_or_eq with h1 | rfl
  · rcases h2.lt_or_eq with h2 | rfl
    · rcases h3.lt_or_eq with h3 | rfl
      · rcases h4.lt_or_eq with h4 | rfl
        · exact absurd ⟨s, t, h1, h2, h3, h4, rfl⟩ hz'
        · right; right; left
          have := add_smul_mem_segment (a + w) u h1.le h2.le
          rw [show a + w + u = a + u + w by abel] at this
          convert this using 1; module
      · left
        convert add_smul_mem_segment a u h1.le h2.le using 1; module
    · right; left
      convert add_smul_mem_segment (a + u) w h3 h4 using 1; module
  · right; right; right
    convert add_smul_mem_segment a w h3 h4 using 1; module

/-- No point of a side lies in the open parallelogram. -/
lemma not_mem_paraOpen_of_mem_sides {a u w z : Plane} (h : cr u w ≠ 0)
    (hz : z ∈ segment ℝ a (a + u) ∨ z ∈ segment ℝ (a + u) (a + u + w) ∨
      z ∈ segment ℝ (a + w) (a + u + w) ∨ z ∈ segment ℝ a (a + w)) :
    z ∉ paraOpen a u w := by
  rintro ⟨s, t, h1, h2, h3, h4, rfl⟩
  rcases hz with hz | hz | hz | hz <;> rw [segment_eq_image'] at hz <;>
    obtain ⟨θ, -, hθ⟩ := hz
  · have := (coords_unique h (s' := θ) (t' := 0) (hθ.symm.trans (by module))).2
    linarith
  · have := (coords_unique h (s' := 1) (t' := θ) (hθ.symm.trans (by module))).1
    linarith
  · have := (coords_unique h (s' := θ) (t' := 1) (hθ.symm.trans (by module))).2
    linarith
  · have := (coords_unique h (s' := 0) (t' := θ) (hθ.symm.trans (by module))).1
    linarith

lemma near_vertex_aux {s t u0 u1 w0 w1 : ℝ} (h1 : 0 ≤ s) (h2 : s ≤ 1) (h3 : 0 ≤ t) (h4 : t ≤ 1)
    (hu2 : u0 ^ 2 + u1 ^ 2 = 1) (hw2 : w0 ^ 2 + w1 ^ 2 = 1)
    (ea : 1 ≤ (s * u0 + t * w0) ^ 2 + (s * u1 + t * w1) ^ 2)
    (eb : 1 ≤ ((s - 1) * u0 + t * w0) ^ 2 + ((s - 1) * u1 + t * w1) ^ 2)
    (ed : 1 ≤ (s * u0 + (t - 1) * w0) ^ 2 + (s * u1 + (t - 1) * w1) ^ 2)
    (ec : 1 ≤ ((s - 1) * u0 + (t - 1) * w0) ^ 2 + ((s - 1) * u1 + (t - 1) * w1) ^ 2) :
    False := by
  have iden : (1 - s) * (1 - t) * ((s * u0 + t * w0) ^ 2 + (s * u1 + t * w1) ^ 2) +
      s * (1 - t) * (((s - 1) * u0 + t * w0) ^ 2 + ((s - 1) * u1 + t * w1) ^ 2) +
      (1 - s) * t * ((s * u0 + (t - 1) * w0) ^ 2 + (s * u1 + (t - 1) * w1) ^ 2) +
      s * t * (((s - 1) * u0 + (t - 1) * w0) ^ 2 + ((s - 1) * u1 + (t - 1) * w1) ^ 2) =
      s * (1 - s) + t * (1 - t) := by
    linear_combination (s * (1 - s)) * hu2 + (t * (1 - t)) * hw2
  have k1 := mul_le_mul_of_nonneg_left ea
    (mul_nonneg (by linarith : 0 ≤ 1 - s) (by linarith : 0 ≤ 1 - t))
  have k2 := mul_le_mul_of_nonneg_left eb (mul_nonneg h1 (by linarith : 0 ≤ 1 - t))
  have k3 := mul_le_mul_of_nonneg_left ed (mul_nonneg (by linarith : 0 ≤ 1 - s) h3)
  have k4 := mul_le_mul_of_nonneg_left ec (mul_nonneg h1 h3)
  nlinarith [sq_nonneg (s - 1 / 2), sq_nonneg (t - 1 / 2)]

/-- Every point of a closed parallelogram with unit sides is within distance `< 1` of a
vertex. -/
lemma exists_near_vertex {a u w z : Plane} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (hz : z ∈ paraClosed a u w) :
    dist z a < 1 ∨ dist z (a + u) < 1 ∨ dist z (a + w) < 1 ∨ dist z (a + u + w) < 1 := by
  obtain ⟨s, t, h1, h2, h3, h4, rfl⟩ := hz
  by_contra hc
  push_neg at hc
  obtain ⟨da, db, dd, dc⟩ := hc
  have sq : ∀ x : Plane, 1 ≤ dist (a + s • u + t • w) x → 1 ≤ dist (a + s • u + t • w) x ^ 2 :=
    fun x hx => by nlinarith
  have ea := sq _ da; have eb := sq _ db; have ed := sq _ dd; have ec := sq _ dc
  have hu2 := norm_sq_coord u; have hw2 := norm_sq_coord w
  rw [hu] at hu2; rw [hw] at hw2
  rw [dist_sq_coord] at ea eb ed ec
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at ea eb ed ec
  exact near_vertex_aux (u0 := u 0) (u1 := u 1) (w0 := w 0) (w1 := w 1) h1 h2 h3 h4
    (by linarith) (by linarith) (ea.trans_eq (by ring))
    (eb.trans_eq (by ring)) (ed.trans_eq (by ring)) (ec.trans_eq (by ring))

lemma paraClosed_subset_convexHull (a u w : Plane) :
    paraClosed a u w ⊆ convexHull ℝ {a, a + u, a + w, a + u + w} := by
  rintro _ ⟨s, t, h1, h2, h3, h4, rfl⟩
  have hc := convex_convexHull ℝ ({a, a + u, a + w, a + u + w} : Set Plane)
  have m : ∀ x ∈ ({a, a + u, a + w, a + u + w} : Set Plane),
      x ∈ convexHull ℝ ({a, a + u, a + w, a + u + w} : Set Plane) :=
    fun x hx => subset_convexHull ℝ _ hx
  have p1 := hc (m a (by simp)) (m (a + u) (by simp)) (by linarith : 0 ≤ 1 - s) h1
    (by ring : 1 - s + s = 1)
  have p2 := hc (m (a + w) (by simp)) (m (a + u + w) (by simp)) (by linarith : 0 ≤ 1 - s) h1
    (by ring : 1 - s + s = 1)
  have p3 := hc p1 p2 (by linarith : 0 ≤ 1 - t) h3 (by ring : 1 - t + t = 1)
  convert p3 using 1
  module

lemma volume_paraOpen (a u w : Plane) :
    volume (paraOpen a u w) = ENNReal.ofReal |cr u w| := by
  let M : Plane →L[ℝ] Plane :=
    (EuclideanSpace.proj (0 : Fin 2) : Plane →L[ℝ] ℝ).smulRight u +
      (EuclideanSpace.proj (1 : Fin 2) : Plane →L[ℝ] ℝ).smulRight w
  have hM : ∀ t : Plane, M t = t 0 • u + t 1 • w := fun t => rfl
  set S0 : Set Plane := {t | 0 < t 0 ∧ t 0 < 1 ∧ 0 < t 1 ∧ t 1 < 1}
  have hS : paraOpen a u w = (fun x => a + x) '' (M '' S0) := by
    ext z; constructor
    · rintro ⟨s, t, h1, h2, h3, h4, rfl⟩
      refine ⟨s • u + t • w, ⟨!₂[s, t], ⟨by simpa using h1, by simpa using h2, by simpa using h3,
        by simpa using h4⟩, ?_⟩, by simp [add_assoc]⟩
      rw [hM]; simp
    · rintro ⟨_, ⟨t, ⟨h1, h2, h3, h4⟩, rfl⟩, rfl⟩
      exact ⟨t 0, t 1, h1, h2, h3, h4, by rw [hM, add_assoc]⟩
  have hS0 : volume S0 = 1 := by
    have : S0 = (WithLp.ofLp) ⁻¹' (Set.pi univ fun _ => Ioo (0:ℝ) 1) := by
      ext t; simp [S0, Fin.forall_fin_two, and_assoc]
    rw [this, (PiLp.volume_preserving_ofLp (ι := Fin 2)).measure_preimage
      (MeasurableSet.univ_pi fun _ => measurableSet_Ioo).nullMeasurableSet, volume_pi_pi]
    simp
  have hdet : LinearMap.det (M : Plane →ₗ[ℝ] Plane) = cr u w := by
    rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis, Matrix.det_fin_two]
    simp [LinearMap.toMatrix_apply, hM, cr]
    ring
  rw [hS, image_add_left, measure_preimage_add, Measure.addHaar_image_continuousLinearMap, hS0,
    mul_one, hdet]

/-! ## Unit segments -/

/-- Unit edges of a separated set do not cross: if two different unit segments meet, they meet
at an endpoint. -/
lemma unit_seg_inter {X : Finset Plane} (hX : IsSeparated X) {p q v w y : Plane}
    (hp : p ∈ X) (hq : q ∈ X) (hv : v ∈ X) (hw : w ∈ X) (hpq : dist p q = 1)
    (hvw : dist v w = 1) (hne : s(p, q) ≠ s(v, w)) (hy : y ∈ segment ℝ p q)
    (hy' : y ∈ segment ℝ v w) : y = p ∨ y = q := by
  have hXC : ∀ x ∈ X.image toC, ∀ y ∈ X.image toC, x ≠ y → 1 ≤ dist x y := by
    simp only [Finset.mem_image]
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hne
    rw [dist_toC]; exact hX x hx y hy (fun h => hne (h ▸ rfl))
  have hP := EstablishedExternalResults.isPlaneGraph_unitPairs hXC
  have he : s(toC p, toC q) ∈ EstablishedExternalResults.unitPairs (X.image toC) :=
    EstablishedExternalResults.mem_unitPairs.2 ⟨Finset.mem_image_of_mem _ hp,
      Finset.mem_image_of_mem _ hq, by rw [dist_toC]; exact hpq⟩
  have he' : s(toC v, toC w) ∈ EstablishedExternalResults.unitPairs (X.image toC) :=
    EstablishedExternalResults.mem_unitPairs.2 ⟨Finset.mem_image_of_mem _ hv,
      Finset.mem_image_of_mem _ hw, by rw [dist_toC]; exact hvw⟩
  have hne' : s(toC p, toC q) ≠ s(toC v, toC w) := by
    intro h; apply hne
    rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [toC.injective h1, toC.injective h2]
    · rw [toC.injective h1, toC.injective h2, Sym2.eq_swap]
  have hy1 : toC y ∈ EstablishedExternalResults.edgeSeg s(toC p, toC q) := by
    have h := image_segment ℝ (toC.toLinearEquiv.toLinearMap.toAffineMap) p q
    simp only [LinearMap.coe_toAffineMap, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv] at h
    rw [EstablishedExternalResults.edgeSeg_mk, ← h]; exact Set.mem_image_of_mem _ hy
  have hy2 : toC y ∈ EstablishedExternalResults.edgeSeg s(toC v, toC w) := by
    have h := image_segment ℝ (toC.toLinearEquiv.toLinearMap.toAffineMap) v w
    simp only [LinearMap.coe_toAffineMap, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv] at h
    rw [EstablishedExternalResults.edgeSeg_mk, ← h]; exact Set.mem_image_of_mem _ hy'
  rcases Sym2.mem_iff.1 (hP.inter _ he _ he' hne' _ hy1 hy2) with h | h
  · exact Or.inl (toC.injective h)
  · exact Or.inr (toC.injective h)

/-! ## Rhombi as parallelograms -/

/-- The parallelogram form of a unit rhombus of a separated set without unit triangles. -/
lemma rhombus_rep {X : Finset Plane} (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X)
    {Q : Finset Plane} (hQ : Q ∈ rhombi X) :
    ∃ a u w : Plane, Q = {a, a + u, a + w, a + u + w} ∧ ‖u‖ = 1 ∧ ‖w‖ = 1 ∧
      |inner ℝ u w| < 1 / 2 := by
  have hQ' := hQ
  obtain ⟨hP, a, b, c, d, rfl, hab, hbc, hcd, hda⟩ := Finset.mem_filter.1 hQ
  obtain ⟨-, hac, -, -, hbd, -⟩ := distinct_of_card_four (Finset.mem_powersetCard.1 hP).2
  obtain ⟨d1, d2⟩ := rhombus_diagonals_gt_one hX htri hQ' hab hbc hcd hda
  have hpar := rhombus_parallelogram hac hbd hab hbc hcd hda
  refine ⟨a, b - a, d - a, ?_, ?_, ?_, ?_⟩
  · have e1 : a + (b - a) = b := by abel
    have e2 : a + (d - a) = d := by abel
    have e3 : a + (b - a) + (d - a) = c := by
      have : c = b + d - a := by rw [← hpar]; abel
      rw [this]; abel
    rw [e3, e1, e2]
    ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  · rw [← dist_eq_norm, dist_comm]; exact hab
  · rw [← dist_eq_norm]; exact hda
  · have hu : ‖b - a‖ = 1 := by rw [← dist_eq_norm, dist_comm]; exact hab
    have hw : ‖d - a‖ = 1 := by rw [← dist_eq_norm]; exact hda
    have h1 : ‖(b - a) - (d - a)‖ ^ 2 > 1 := by
      rw [show (b - a) - (d - a) = b - d by abel, ← dist_eq_norm]; nlinarith
    have h2 : ‖(b - a) + (d - a)‖ ^ 2 > 1 := by
      have hc : c = b + d - a := by rw [← hpar]; abel
      rw [show (b - a) + (d - a) = c - a by rw [hc]; abel,
        ← dist_eq_norm, dist_comm]; nlinarith
    rw [norm_sub_sq_real, hu, hw] at h1
    rw [norm_add_sq_real, hu, hw] at h2
    rw [abs_lt]; constructor <;> linarith

lemma cr_sq_add_inner_sq (u w : Plane) :
    cr u w ^ 2 + inner ℝ u w ^ 2 = ‖u‖ ^ 2 * ‖w‖ ^ 2 := by
  rw [norm_sq_coord, norm_sq_coord, inner_coord, cr]; ring

lemma cr_ne_zero_of_rep {u w : Plane} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (hi : |inner ℝ u w| < 1 / 2) : cr u w ≠ 0 := by
  intro h
  have := cr_sq_add_inner_sq u w
  rw [h, hu, hw] at this
  have h2 : inner ℝ u w ^ 2 < 1 / 4 := by
    have := sq_lt_sq' (by linarith [abs_nonneg (inner ℝ u w)]) hi
    rw [sq_abs] at this; linarith
  linarith

/-- A point of the set in a closed unit rhombus is one of its vertices. -/
lemma mem_of_mem_paraClosed {X : Finset Plane} (hX : IsSeparated X) {a u w z : Plane}
    (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (hQ : ({a, a + u, a + w, a + u + w} : Finset Plane) ⊆ X)
    (hz : z ∈ X) (hzP : z ∈ paraClosed a u w) :
    z ∈ ({a, a + u, a + w, a + u + w} : Finset Plane) := by
  have mem : ∀ v ∈ ({a, a + u, a + w, a + u + w} : Finset Plane), dist z v < 1 →
      z ∈ ({a, a + u, a + w, a + u + w} : Finset Plane) := by
    intro v hv hd
    by_contra hne
    have hzv : z ≠ v := fun h => hne (h ▸ hv)
    linarith [hX z hz v (hQ hv) hzv]
  rcases exists_near_vertex hu hw hzP with h | h | h | h
  · exact mem _ (by simp) h
  · exact mem _ (by simp) h
  · exact mem _ (by simp) h
  · exact mem _ (by simp) h

/-- `y` lies on one of the four sides of the parallelogram. -/
def OnSides (a u w y : Plane) : Prop :=
  y ∈ segment ℝ a (a + u) ∨ y ∈ segment ℝ (a + u) (a + u + w) ∨
    y ∈ segment ℝ (a + w) (a + u + w) ∨ y ∈ segment ℝ a (a + w)

lemma vertices_mem_paraClosed {a u w v : Plane}
    (hv : v ∈ ({a, a + u, a + w, a + u + w} : Finset Plane)) : v ∈ paraClosed a u w := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · exact ⟨0, 0, le_rfl, zero_le_one, le_rfl, zero_le_one, by simp⟩
  · exact ⟨1, 0, zero_le_one, le_rfl, le_rfl, zero_le_one, by simp⟩
  · exact ⟨0, 1, le_rfl, zero_le_one, zero_le_one, le_rfl, by simp⟩
  · exact ⟨1, 1, zero_le_one, le_rfl, zero_le_one, le_rfl, by simp⟩

lemma onSides_of_mem_segment {a u w p q y : Plane} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (hi : |inner ℝ u w| < 1 / 2)
    (hp : p ∈ ({a, a + u, a + w, a + u + w} : Finset Plane))
    (hq : q ∈ ({a, a + u, a + w, a + u + w} : Finset Plane)) (hpq : dist p q = 1)
    (hy : y ∈ segment ℝ p q) : OnSides a u w y := by
  have h1 : 1 < ‖u + w‖ := by
    have := norm_add_sq_real u w
    rw [hu, hw] at this
    have : 1 < ‖u + w‖ ^ 2 := by rw [abs_lt] at hi; nlinarith
    nlinarith [norm_nonneg (u + w)]
  have h2 : 1 < ‖u - w‖ := by
    have := norm_sub_sq_real u w
    rw [hu, hw] at this
    have : 1 < ‖u - w‖ ^ 2 := by rw [abs_lt] at hi; nlinarith
    nlinarith [norm_nonneg (u - w)]
  have hd1 : dist a (a + u + w) ≠ 1 := by
    rw [dist_eq_norm, show a - (a + u + w) = -(u + w) by abel, norm_neg]; linarith
  have hd2 : dist (a + u + w) a ≠ 1 := by
    rw [dist_eq_norm, show a + u + w - a = u + w by abel]; linarith
  have hd3 : dist (a + u) (a + w) ≠ 1 := by
    rw [dist_eq_norm, show a + u - (a + w) = u - w by abel]; linarith
  have hd4 : dist (a + w) (a + u) ≠ 1 := by
    rw [dist_eq_norm, show a + w - (a + u) = -(u - w) by abel, norm_neg]; linarith
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
  unfold OnSides
  rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;>
    try simp only [dist_self, zero_ne_one] at hpq
  all_goals first
    | (left; exact hy)
    | (right; left; exact hy)
    | (right; right; left; exact hy)
    | (right; right; right; exact hy)
    | (left; rw [segment_symm]; exact hy)
    | (right; left; rw [segment_symm]; exact hy)
    | (right; right; left; rw [segment_symm]; exact hy)
    | (right; right; right; rw [segment_symm]; exact hy)
    | skip
  all_goals exfalso
  all_goals first | exact hd1 hpq | exact hd2 hpq | exact hd3 hpq | exact hd4 hpq

lemma exists_side_of_onSides {a u w y : Plane} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (hy : OnSides a u w y) :
    ∃ v₁ ∈ ({a, a + u, a + w, a + u + w} : Finset Plane),
      ∃ v₂ ∈ ({a, a + u, a + w, a + u + w} : Finset Plane),
        dist v₁ v₂ = 1 ∧ y ∈ segment ℝ v₁ v₂ := by
  rcases hy with hy | hy | hy | hy
  · exact ⟨a, by simp, a + u, by simp, by rw [dist_eq_norm]; simp [hu], hy⟩
  · exact ⟨a + u, by simp, a + u + w, by simp, by rw [dist_eq_norm]; simp [hw], hy⟩
  · exact ⟨a + w, by simp, a + u + w, by simp,
      by rw [dist_eq_norm, show a + w - (a + u + w) = -u by abel, norm_neg, hu], hy⟩
  · exact ⟨a, by simp, a + w, by simp, by rw [dist_eq_norm]; simp [hw], hy⟩

lemma eq_of_mem_segment_of_mem_segment {p q y : Plane} (hy : y ∈ segment ℝ p q)
    (hq : q ∈ segment ℝ y p) : y = q := by
  have e1 := dist_add_dist_of_mem_segment hy
  have e2 := dist_add_dist_of_mem_segment hq
  rw [dist_comm y p] at e2
  rw [dist_comm p y] at e1
  have : dist y q = 0 := by linarith [dist_nonneg (x := y) (y := q), dist_comm q p, dist_comm p y]
  exact dist_eq_zero.1 this

/-- A segment from a point of an open set to a point outside meets the boundary region. -/
lemma exists_mem_segment_diff {a u w y x : Plane} (h : cr u w ≠ 0) (hy : y ∈ paraOpen a u w)
    (hx : x ∉ paraOpen a u w) :
    ∃ y₁ ∈ segment ℝ y x, y₁ ∈ paraClosed a u w ∧ y₁ ∉ paraOpen a u w := by
  by_contra hc
  push_neg at hc
  have hsub : segment ℝ y x ⊆ paraOpen a u w ∪ (paraClosed a u w)ᶜ := by
    intro z hz
    by_cases hzc : z ∈ paraClosed a u w
    · exact Or.inl (by_contra fun h' => h' (hc z hz hzc))
    · exact Or.inr hzc
  have := (convex_segment y x).isPreconnected.subset_left_of_subset_union (isOpen_paraOpen h)
    (isClosed_paraClosed h).isOpen_compl
    (disjoint_compl_right.mono_left (paraOpen_subset_paraClosed a u w)) hsub
    ⟨y, left_mem_segment ℝ y x, hy⟩
  exact hx (this (right_mem_segment ℝ y x))

/-- A unit segment of the set does not meet the open parallelogram of a unit rhombus. -/
lemma unit_seg_disjoint_paraOpen {X : Finset Plane} (hX : IsSeparated X) {a u w : Plane}
    (hV : ({a, a + u, a + w, a + u + w} : Finset Plane) ⊆ X) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (hi : |inner ℝ u w| < 1 / 2) {p q : Plane} (hp : p ∈ X) (hq : q ∈ X) (hpq : dist p q = 1) :
    Disjoint (segment ℝ p q) (paraOpen a u w) := by
  have h := cr_ne_zero_of_rep hu hw hi
  set V : Finset Plane := {a, a + u, a + w, a + u + w}
  have notX : ∀ x ∈ X, x ∉ paraOpen a u w := by
    intro x hx hxo
    have hxV := mem_of_mem_paraClosed hX hu hw hV hx (paraOpen_subset_paraClosed a u w hxo)
    have hxs : OnSides a u w x := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxV
      unfold OnSides
      rcases hxV with rfl | rfl | rfl | rfl
      · exact Or.inl (left_mem_segment ℝ _ _)
      · exact Or.inl (right_mem_segment ℝ _ _)
      · exact Or.inr (Or.inr (Or.inr (right_mem_segment ℝ _ _)))
      · exact Or.inr (Or.inl (right_mem_segment ℝ _ _))
    exact not_mem_paraOpen_of_mem_sides h hxs hxo
  -- the endpoint claim
  have claim : ∀ p q : Plane, p ∈ X → q ∈ X → dist p q = 1 → ∀ y ∈ segment ℝ p q,
      y ∈ paraOpen a u w → p ∈ V := by
    intro p q hp hq hpq y hy hyo
    obtain ⟨y₁, hy₁, hy₁c, hy₁o⟩ := exists_mem_segment_diff h hyo (notX p hp)
    have hsides := mem_sides_of_mem_paraClosed hy₁c hy₁o
    obtain ⟨v₁, hv₁, v₂, hv₂, hv12, hy₁v⟩ := exists_side_of_onSides hu hw hsides
    have hy₁pq : y₁ ∈ segment ℝ p q :=
      (convex_segment p q).segment_subset hy (left_mem_segment ℝ p q) hy₁
    by_cases he : s(p, q) = s(v₁, v₂)
    · exfalso
      have : y ∈ segment ℝ v₁ v₂ := by
        rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hy
        · rw [segment_symm]; exact hy
      exact not_mem_paraOpen_of_mem_sides h
        (onSides_of_mem_segment hu hw hi hv₁ hv₂ hv12 this) hyo
    have e1 := unit_seg_inter hX hp hq (hV hv₁) (hV hv₂) hpq hv12 he hy₁pq hy₁v
    have e2 := unit_seg_inter hX (hV hv₁) (hV hv₂) hp hq hv12 hpq (Ne.symm he) hy₁v hy₁pq
    rcases e1 with rfl | rfl
    · rcases e2 with rfl | rfl
      · exact hv₁
      · exact hv₂
    · exfalso
      have := eq_of_mem_segment_of_mem_segment hy hy₁
      subst this
      exact notX _ hq hyo
  rw [Set.disjoint_left]
  intro y hy hyo
  have hpV := claim p q hp hq hpq y hy hyo
  have hqV := claim q p hq hp (by rw [dist_comm]; exact hpq) y (by rw [segment_symm]; exact hy) hyo
  exact not_mem_paraOpen_of_mem_sides h (onSides_of_mem_segment hu hw hi hpV hqV hpq hy) hyo

/-- The open parallelograms of distinct unit rhombi are disjoint. -/
lemma paraOpen_disjoint {X : Finset Plane} (hX : IsSeparated X)
    {a u w a' u' w' : Plane}
    (hV : ({a, a + u, a + w, a + u + w} : Finset Plane) ⊆ X) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (hi : |inner ℝ u w| < 1 / 2)
    (hV' : ({a', a' + u', a' + w', a' + u' + w'} : Finset Plane) ⊆ X) (hu' : ‖u'‖ = 1)
    (hw' : ‖w'‖ = 1) (hi' : |inner ℝ u' w'| < 1 / 2)
    (hcard : ({a', a' + u', a' + w', a' + u' + w'} : Finset Plane).card = 4)
    (hne : ({a, a + u, a + w, a + u + w} : Finset Plane) ≠
      ({a', a' + u', a' + w', a' + u' + w'} : Finset Plane)) :
    Disjoint (paraOpen a u w) (paraOpen a' u' w') := by
  have h := cr_ne_zero_of_rep hu hw hi
  have h' := cr_ne_zero_of_rep hu' hw' hi'
  rw [Set.disjoint_left]
  intro z hz hz'
  -- the second open parallelogram avoids the sides of the first
  have hsub : paraOpen a' u' w' ⊆ paraOpen a u w ∪ (paraClosed a u w)ᶜ := by
    intro x hx
    by_cases hxc : x ∈ paraClosed a u w
    · left
      by_contra hxo
      obtain ⟨v₁, hv₁, v₂, hv₂, hv12, hxv⟩ :=
        exists_side_of_onSides hu hw (mem_sides_of_mem_paraClosed hxc hxo)
      exact Set.disjoint_left.1 (unit_seg_disjoint_paraOpen hX hV' hu' hw' hi' (hV hv₁) (hV hv₂)
        hv12) hxv hx
    · exact Or.inr hxc
  have hin : paraOpen a' u' w' ⊆ paraOpen a u w :=
    (convex_paraOpen a' u' w').isPreconnected.subset_left_of_subset_union (isOpen_paraOpen h)
      (isClosed_paraClosed h).isOpen_compl
      (disjoint_compl_right.mono_left (paraOpen_subset_paraClosed a u w)) hsub ⟨z, hz', hz⟩
  have hsub2 : ({a', a' + u', a' + w', a' + u' + w'} : Finset Plane) ⊆
      ({a, a + u, a + w, a + u + w} : Finset Plane) := by
    intro v hv
    have h1 : v ∈ closure (paraOpen a' u' w') :=
      paraClosed_subset_closure a' u' w' (vertices_mem_paraClosed hv)
    have h2 : v ∈ paraClosed a u w :=
      (closure_minimal (hin.trans (paraOpen_subset_paraClosed a u w)) (isClosed_paraClosed h)) h1
    exact mem_of_mem_paraClosed hX hu hw hV (hV' hv) h2
  have hcard0 : ({a, a + u, a + w, a + u + w} : Finset Plane).card ≤ 4 := Finset.card_le_four
  exact hne (Finset.eq_of_subset_of_card_le hsub2 (by rw [hcard]; exact hcard0)).symm

/-! ## The defect of a rhombus -/

/-- For `ζ = c + s i` on the unit circle with `c² ≤ 1/4`, `|1 - ζ⁶| ≤ 16 (|s| - √3/2)`. -/
lemma norm_one_sub_pow_six_le {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) (hc : c ^ 2 ≤ 1 / 4) :
    ‖(1 : ℂ) - (⟨c, s⟩ : ℂ) ^ 6‖ ≤ 16 * (|s| - √3 / 2) := by
  set ζ : ℂ := ⟨c, s⟩
  have hfac : (1 : ℂ) - ζ ^ 6 = (1 - ζ ^ 2) * ζ ^ 2 * ((1 + 2 * (c ^ 2 - s ^ 2) : ℝ) : ℂ) := by
    have e : (1 : ℂ) + ζ ^ 2 + ζ ^ 4 = ζ ^ 2 * ((1 + 2 * (c ^ 2 - s ^ 2) : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [ζ, pow_succ, Complex.mul_re, Complex.mul_im] <;>
        first | ring1 | linear_combination (-(1 + c ^ 2 + s ^ 2)) * h
    rw [mul_assoc, ← e]; ring
  have hn1 : ‖(1 : ℂ) - ζ ^ 2‖ = 2 * |s| := by
    have : ‖(1 : ℂ) - ζ ^ 2‖ ^ 2 = (2 * |s|) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [ζ, pow_succ, Complex.mul_re, Complex.mul_im]
      have hs : |s| * |s| = s * s := abs_mul_abs_self s
      linear_combination (c ^ 2 + s ^ 2 - 1) * h - 4 * hs
    exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 this
  have hn2 : ‖ζ ^ 2‖ = 1 := by
    rw [norm_pow]
    have : ‖ζ‖ = 1 := by
      rw [Complex.norm_def, Complex.normSq_apply]; simp [ζ]; rw [← sq, ← sq, h]
    rw [this]; simp
  have h3 : |1 + 2 * (c ^ 2 - s ^ 2)| = 1 - 4 * c ^ 2 := by
    rw [abs_of_nonpos (by nlinarith)]; linarith
  rw [hfac, norm_mul, norm_mul, hn1, hn2, Complex.norm_real, Real.norm_eq_abs, h3, mul_one]
  have hs1 : |s| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith
  have hs0 : 0 ≤ |s| := abs_nonneg s
  have h33 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3l : √3 < 2 := by nlinarith [Real.sqrt_nonneg 3]
  have hss : |s| ^ 2 = 1 - c ^ 2 := by rw [sq_abs]; linarith
  have hge : √3 / 2 ≤ |s| := by nlinarith [Real.sqrt_nonneg 3]
  nlinarith [Real.sqrt_nonneg 3]

/-- For unit vectors `u, w` with `|u · w| ≤ 1/2`,
`|dir6 u - dir6 w| ≤ 16 (|u × w| - √3/2)`. -/
lemma norm_dir6_sub_le {u w : Plane} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (hi : |inner ℝ u w| ≤ 1 / 2) :
    ‖dir6 u - dir6 w‖ ≤ 16 * (|cr u w| - aStar) := by
  rw [dir6_of_norm_eq_one hu, dir6_of_norm_eq_one hw]
  set c := inner ℝ u w with hcdef
  set s := cr u w with hsdef
  have hu2 := norm_sq_coord u; have hw2 := norm_sq_coord w
  rw [hu] at hu2; rw [hw] at hw2
  have hcs : c ^ 2 + s ^ 2 = 1 := by
    have := cr_sq_add_inner_sq u w; rw [hu, hw] at this; linarith
  have hc : c ^ 2 ≤ 1 / 4 := by
    have := sq_le_sq' (by linarith [abs_nonneg c, neg_abs_le c, le_abs_self c]) hi
    rw [sq_abs] at this; linarith
  have hW : toC w = (⟨c, s⟩ : ℂ) * toC u := by
    apply Complex.ext
    · simp only [Complex.mul_re, toC, hcdef, hsdef, cr, inner_coord]
      simp
      linear_combination (w 0) * hu2
    · simp only [Complex.mul_im, toC, hcdef, hsdef, cr, inner_coord]
      simp
      linear_combination (w 1) * hu2
  have hU : ‖toC u‖ = 1 := by rw [norm_toC, hu]
  rw [hW, mul_pow, ← one_sub_mul, norm_mul, norm_pow, hU, one_pow, mul_one]
  exact norm_one_sub_pow_six_le hcs hc

lemma aStar_le_abs_cr {u w : Plane} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (hi : |inner ℝ u w| < 1 / 2) : aStar ≤ |cr u w| := by
  have h := cr_sq_add_inner_sq u w
  rw [hu, hw] at h
  have hc : inner ℝ u w ^ 2 < 1 / 4 := by
    have := sq_lt_sq' (by linarith [abs_nonneg (inner ℝ u w)]) hi
    rw [sq_abs] at this; linarith
  have h33 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have : (√3 / 2) ^ 2 ≤ |cr u w| ^ 2 := by rw [sq_abs]; nlinarith
  unfold aStar
  exact (pow_le_pow_iff_left₀ (by positivity) (abs_nonneg _) two_ne_zero).1 this

/-- The defect of a unit rhombus is at most `1024 (|u × w| - a*)`. -/
lemma rhombusDefect_le {a u w : Plane} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (hi : |inner ℝ u w| < 1 / 2) :
    rhombusDefect {a, a + u, a + w, a + u + w} ≤ 1024 * (|cr u w| - aStar) := by
  have B := norm_dir6_sub_le hu hw hi.le
  have hpos : 0 ≤ |cr u w| - aStar := by linarith [aStar_le_abs_cr hu hw hi]
  have h1' : 1 < ‖u + w‖ := by
    have := norm_add_sq_real u w
    rw [hu, hw] at this
    have : 1 < ‖u + w‖ ^ 2 := by rw [abs_lt] at hi; nlinarith
    nlinarith [norm_nonneg (u + w)]
  have h2' : 1 < ‖u - w‖ := by
    have := norm_sub_sq_real u w
    rw [hu, hw] at this
    have : 1 < ‖u - w‖ ^ 2 := by rw [abs_lt] at hi; nlinarith
    nlinarith [norm_nonneg (u - w)]
  have hd1 : dist a (a + u + w) ≠ 1 := by
    rw [dist_eq_norm, show a - (a + u + w) = -(u + w) by abel, norm_neg]; linarith
  have hd2 : dist (a + u + w) a ≠ 1 := by
    rw [dist_eq_norm, show a + u + w - a = u + w by abel]; linarith
  have hd3 : dist (a + u) (a + w) ≠ 1 := by
    rw [dist_eq_norm, show a + u - (a + w) = u - w by abel]; linarith
  have hd4 : dist (a + w) (a + u) ≠ 1 := by
    rw [dist_eq_norm, show a + w - (a + u) = -(u - w) by abel, norm_neg]; linarith
  have f1 : a + u - a = u := by abel
  have f2 : a - (a + u) = -u := by abel
  have f3 : a + w - a = w := by abel
  have f4 : a - (a + w) = -w := by abel
  have f5 : a + u + w - (a + u) = w := by abel
  have f6 : a + u - (a + u + w) = -w := by abel
  have f7 : a + u + w - (a + w) = u := by abel
  have f8 : a + w - (a + u + w) = -u := by abel
  set Q : Finset Plane := {a, a + u, a + w, a + u + w} with hQ
  have hterm : ∀ t ∈ defectTriples Q,
      ‖dir6 (t.1 - t.2.1) - dir6 (t.2.2 - t.2.1)‖ ≤ 16 * (|cr u w| - aStar) := by
    rintro ⟨x, y, z⟩ ht
    simp only [defectTriples, Finset.mem_filter, Finset.mem_product] at ht
    obtain ⟨⟨hx, hy, hz⟩, e1, e2, hxz⟩ := ht
    simp only [hQ, Finset.mem_insert, Finset.mem_singleton] at hx hy hz
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      rcases hz with rfl | rfl | rfl | rfl
    all_goals first
      | (simp only [dist_self] at e1; norm_num at e1)
      | (simp only [dist_self] at e2; norm_num at e2)
      | (with_reducible exact absurd e1 hd1) | (with_reducible exact absurd e1 hd2)
      | (with_reducible exact absurd e1 hd3) | (with_reducible exact absurd e1 hd4)
      | (with_reducible exact absurd e2 hd1) | (with_reducible exact absurd e2 hd2)
      | (with_reducible exact absurd e2 hd3) | (with_reducible exact absurd e2 hd4)
      | (with_reducible exact absurd rfl hxz)
      | (simp only [f1, f2, f3, f4, f5, f6, f7, f8, dir6_neg]
         first | exact B | (rw [norm_sub_rev]; exact B))
  have hcardT : (defectTriples Q).card ≤ 64 := by
    calc (defectTriples Q).card ≤ (Q ×ˢ Q ×ˢ Q).card := Finset.card_filter_le _ _
      _ = Q.card * (Q.card * Q.card) := by rw [Finset.card_product, Finset.card_product]
      _ ≤ 4 * (4 * 4) := by
          have := Finset.card_le_four (a := a) (b := a + u) (c := a + w) (d := a + u + w)
          gcongr
      _ = 64 := by norm_num
  unfold rhombusDefect
  calc ∑ t ∈ defectTriples Q, ‖dir6 (t.1 - t.2.1) - dir6 (t.2.2 - t.2.1)‖
      ≤ ∑ t ∈ defectTriples Q, 16 * (|cr u w| - aStar) := Finset.sum_le_sum hterm
    _ = (defectTriples Q).card * (16 * (|cr u w| - aStar)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 64 * (16 * (|cr u w| - aStar)) := by
        gcongr
        exact_mod_cast hcardT
    _ = 1024 * (|cr u w| - aStar) := by ring

/-! ## Total area of the rhombi -/

/-- The rhombus areas add up to at most `π D² / 4`, with the defect bounded termwise. -/
theorem sum_rhombusDefect_le {X : Finset Plane} (hX : IsSeparated X)
    (htri : ¬ HasUnitTriangle X) (hne : X.Nonempty) :
    ∑ Q ∈ rhombi X, rhombusDefect Q ≤
      1024 * (π * diam X ^ 2 / 4 - aStar * (rhombi X).card) := by
  have hrepQ := fun Q (hQ : Q ∈ rhombi X) => rhombus_rep hX htri hQ
  choose! A U W hrep hu hw hi using hrepQ
  have hsubX : ∀ Q ∈ rhombi X, Q ⊆ X ∧ Q.card = 4 := fun Q hQ =>
    Finset.mem_powersetCard.1 (Finset.mem_filter.1 hQ).1
  -- the open parallelograms are disjoint and lie in the hull
  have hdisj : (↑(rhombi X) : Set (Finset Plane)).PairwiseDisjoint
      (fun Q => paraOpen (A Q) (U Q) (W Q)) := by
    intro Q hQ Q' hQ' hne
    have h1 := hsubX Q hQ; have h2 := hsubX Q' hQ'
    rw [hrep Q hQ] at h1 hne
    rw [hrep Q' hQ'] at h2 hne
    exact paraOpen_disjoint hX h1.1 (hu Q hQ) (hw Q hQ) (hi Q hQ) h2.1 (hu Q' hQ') (hw Q' hQ')
      (hi Q' hQ') h2.2 hne
  have hsub : (⋃ Q ∈ rhombi X, paraOpen (A Q) (U Q) (W Q)) ⊆ convexHull ℝ (X : Set Plane) := by
    refine Set.iUnion₂_subset fun Q hQ => ?_
    refine (paraOpen_subset_paraClosed _ _ _).trans
      ((paraClosed_subset_convexHull _ _ _).trans (convexHull_mono ?_))
    intro v hv
    have h1 := (hsubX Q hQ).1
    rw [hrep Q hQ] at h1
    exact h1 (by simpa using hv)
  have hvol : ∑ Q ∈ rhombi X, ENNReal.ofReal |cr (U Q) (W Q)| ≤
      ENNReal.ofReal (π * diam X ^ 2 / 4) := by
    calc ∑ Q ∈ rhombi X, ENNReal.ofReal |cr (U Q) (W Q)|
        = ∑ Q ∈ rhombi X, volume (paraOpen (A Q) (U Q) (W Q)) :=
          Finset.sum_congr rfl fun Q _ => (volume_paraOpen _ _ _).symm
      _ = volume (⋃ Q ∈ rhombi X, paraOpen (A Q) (U Q) (W Q)) :=
          (measure_biUnion_finset hdisj fun Q hQ =>
            (isOpen_paraOpen (cr_ne_zero_of_rep (hu Q hQ) (hw Q hQ) (hi Q hQ))).measurableSet).symm
      _ ≤ volume (convexHull ℝ (X : Set Plane)) := measure_mono hsub
      _ ≤ ENNReal.ofReal (π * diam X ^ 2 / 4) := volume_convexHull_le X hne
  have hsum : ∑ Q ∈ rhombi X, |cr (U Q) (W Q)| ≤ π * diam X ^ 2 / 4 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun Q _ => abs_nonneg _)] at hvol
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hvol
  calc ∑ Q ∈ rhombi X, rhombusDefect Q
      ≤ ∑ Q ∈ rhombi X, 1024 * (|cr (U Q) (W Q)| - aStar) := by
        refine Finset.sum_le_sum fun Q hQ => ?_
        exact (congrArg rhombusDefect (hrep Q hQ)).le.trans
          (rhombusDefect_le (hu Q hQ) (hw Q hQ) (hi Q hQ))
    _ = 1024 * (∑ Q ∈ rhombi X, |cr (U Q) (W Q)| - aStar * (rhombi X).card) := by
        rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ 1024 * (π * diam X ^ 2 / 4 - aStar * (rhombi X).card) := by
        gcongr

end Erdos99
end

end RhombusArea

/-! ═══════════════════════════════════════════════════════════════════════════
## Section `Annulus`
-/

section Annulus

/-!
# Selected tracks and the annular cost (Lemma 6.1)

This file proves the geometric half of Lemma 6.1 of the manuscript.  A *selected* track is one
that starts (at a terminal edge `e`) within `η D` of the circle of radius `D / 2` about a centre
`O`, at the radial direction `ν`, and whose outgoing spine normal `n` satisfies `n · ν ≥ -η`
(`IsSelectedTrack`).  If the whole configuration lies in the disc of radius `D/2 + η D` about `O`
(roundness, Lemma 3.1), then:

* a selected track has at most `(1/2 + 20 η) D` rhombi (the direction–length estimate of
  Lemma 3.5 / Lemma 6.1, `selected_trackLength_le`);
* its spine stays at distance at least `(D/2) √(1 - (1/2 + η)²) - η D` from `O`
  (`selected_spine_far`);
* consequently the rhombi touched by a family of selected tracks lie in an annulus of area
  about `π D² / 16`, and since unit rhombi have disjoint interiors of area at least `a*`, their
  number is at most `(c / 4 + O(η)) D²` (`selected_rhombi_bounds`).
-/

open scoped BigOperators Real
open MeasureTheory Set

@[expose] public noncomputable section

open Classical

namespace Erdos99

/-- The tracks with at least `L` rhombi (the tracks kept after deleting the short ones). -/
def longTracks (X : Finset Plane) (L : ℝ) : Finset (Finset (Sym2 Plane)) :=
  (tracks X).filter (fun T => L ≤ (trackLength X T : ℝ))

/-- A track `T` is *selected* (with centre `O`, scale `D` and tolerance `η`) if it has an edge `e`
whose midpoint lies within `η D` of the point `O + (D/2) ν` of the circle of radius `D / 2`, such
that the track leaves `e` in the direction `n` normal to `e` (all spine midpoints have
nonnegative height above `e` in the direction `n`) and `n · ν ≥ -η`.  This is the condition
`z · τ ≥ -ε` on the selected ports of §6 of the manuscript (`n · ν = z · τ`). -/
def IsSelectedTrack (O : Plane) (D η : ℝ) (T : Finset (Sym2 Plane)) : Prop :=
  ∃ e ∈ T, ∃ ν n : Plane, ‖ν‖ = 1 ∧ (n = rot (dv e) ∨ n = -rot (dv e)) ∧
    ‖mid e - O - (D / 2) • ν‖ ≤ η * D ∧ -η ≤ inner ℝ n ν ∧
    ∀ f ∈ T, 0 ≤ inner ℝ (mid f - mid e) n

/-! ## Real-variable estimates -/

/-- The distance estimate behind `selected_spine_far`, in coordinates, for `b ≥ 0`. -/
lemma spine_alg_pos {D η a b p q : ℝ} (hD : 0 ≤ D) (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 2)
    (hab : a ^ 2 + b ^ 2 = 1) (ha : -η ≤ a) (hb : 0 ≤ b) (hc : √3 * |q| ≤ p) :
    D ^ 2 / 4 * (1 - (1 / 2 + η) ^ 2) ≤ (D * a / 2 + p) ^ 2 + (D * b / 2 + q) ^ 2 := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3p : 0 < √3 := by positivity
  have h32 : √3 < 2 := by nlinarith
  have hp : 0 ≤ p := le_trans (by positivity) hc
  have hqb : -|q| * b ≤ q * b := mul_le_mul_of_nonneg_right (neg_abs_le q) hb
  rcases le_or_gt (1/2) a with ha2 | ha2
  · have hb2 : b ^ 2 ≤ 3 * a ^ 2 := by nlinarith
    have hb3 : b ≤ √3 * a := by
      have : b ^ 2 ≤ (√3 * a) ^ 2 := by rw [mul_pow, h3]; linarith
      exact (abs_le_of_sq_le_sq' this (by positivity)).2
    have hpq : 0 ≤ p * a + q * b := by
      have h1 := mul_le_mul_of_nonneg_left hb3 (abs_nonneg q)
      have h2 := mul_le_mul_of_nonneg_right hc (by linarith : (0:ℝ) ≤ a)
      nlinarith
    have e : (D * a / 2 + p) * a + (D * b / 2 + q) * b = D / 2 + (p * a + q * b) := by
      linear_combination (D / 2) * hab
    nlinarith [sq_nonneg ((D * a / 2 + p) * b - (D * b / 2 + q) * a)]
  · have hb1 : 3 / 4 ≤ b ^ 2 := by nlinarith
    have hbb : √3 / 2 ≤ b := by
      have : (√3 / 2) ^ 2 ≤ b ^ 2 := by rw [div_pow, h3]; linarith
      exact (abs_le_of_sq_le_sq' this hb).2
    have hb1' : b ≤ 1 := by nlinarith
    have e2 : √3 / 2 * (√3 / 2) = 3 / 4 := by linear_combination (1 / 4) * h3
    have hsq : 1 - (1 / 2 + η) ^ 2 ≤ (a / 2 + √3 / 2 * b) ^ 2 := by
      have e : (a / 2 + √3 / 2 * b) ^ 2 = 3 / 4 - a ^ 2 / 2 + √3 / 2 * a * b := by
        linear_combination (b ^ 2 / 4) * h3 + (3 / 4) * hab
      rw [e]
      rcases le_or_gt 0 a with ha0 | ha0
      · have : √3 / 2 * (√3 / 2) * a ≤ √3 / 2 * a * b := by
          have := mul_le_mul_of_nonneg_left hbb (by positivity : 0 ≤ √3 / 2 * a)
          linarith
        rw [e2] at this
        nlinarith
      · have h1 : √3 / 2 * a ≤ √3 / 2 * a * b := by
          have := mul_le_mul_of_nonpos_left hb1' (by nlinarith : √3 / 2 * a ≤ 0)
          linarith
        have h2 : 0 ≤ (1 - √3 / 2) * (-a) := mul_nonneg (by linarith) (by linarith)
        have h4 : a ^ 2 ≤ η ^ 2 := by nlinarith
        nlinarith
    have hcs : (D * a / 2 + p) ^ 2 + (D * b / 2 + q) ^ 2 =
        ((D * a / 2 + p) / 2 + √3 / 2 * (D * b / 2 + q)) ^ 2 +
          (√3 / 2 * (D * a / 2 + p) - (D * b / 2 + q) / 2) ^ 2 := by
      linear_combination (-(((D * a / 2 + p)) ^ 2 + (D * b / 2 + q) ^ 2) / 4) * h3
    have et : (D * a / 2 + p) / 2 + √3 / 2 * (D * b / 2 + q) =
        D / 2 * (a / 2 + √3 / 2 * b) + (p / 2 + √3 / 2 * q) := by ring
    have hq1 : 0 ≤ p / 2 + √3 / 2 * q := by
      have := mul_nonneg h3p.le (by linarith [neg_abs_le q] : 0 ≤ q + |q|)
      linarith
    have hab0 : 0 ≤ a / 2 + √3 / 2 * b := by
      have := mul_le_mul_of_nonneg_left hbb (by positivity : 0 ≤ √3 / 2)
      linarith
    have h0 : 0 ≤ D / 2 * (a / 2 + √3 / 2 * b) := by positivity
    rw [hcs, et]
    calc D ^ 2 / 4 * (1 - (1 / 2 + η) ^ 2) ≤ (D / 2) ^ 2 * (a / 2 + √3 / 2 * b) ^ 2 := by
          rw [show (D / 2) ^ 2 = D ^ 2 / 4 by ring]
          exact mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = (D / 2 * (a / 2 + √3 / 2 * b)) ^ 2 := by ring
      _ ≤ (D / 2 * (a / 2 + √3 / 2 * b) + (p / 2 + √3 / 2 * q)) ^ 2 :=
          pow_le_pow_left₀ h0 (le_add_of_nonneg_right hq1) 2
      _ ≤ _ := le_add_of_nonneg_right (sq_nonneg _)

/-- In the frame `(J u, u)`, write `ν = (a, b)` (`a = n · ν ≥ -η`) and let `(p, q)` lie in the
cone `√3 |q| ≤ p` of half-angle `π/6` about `J u`.  Then `|(D/2) ν + (p, q)|` is at least
`(D/2) √(1 - (1/2 + η)²)`. -/
lemma spine_alg {D η a b p q : ℝ} (hD : 0 ≤ D) (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 2)
    (hab : a ^ 2 + b ^ 2 = 1) (ha : -η ≤ a) (hc : √3 * |q| ≤ p) :
    D ^ 2 / 4 * (1 - (1 / 2 + η) ^ 2) ≤ (D * a / 2 + p) ^ 2 + (D * b / 2 + q) ^ 2 := by
  rcases le_total 0 b with hb | hb
  · exact spine_alg_pos hD hη0 hη1 hab ha hb hc
  · have := spine_alg_pos (b := -b) (p := p) (q := -q) hD hη0 hη1 (by rw [neg_sq]; exact hab) ha
      (by linarith) (by rwa [abs_neg])
    calc _ ≤ _ := this
      _ = _ := by ring

lemma length_alg_A {D η A s : ℝ} (hD : 0 ≤ D) (hη0 : 0 ≤ η) (hs0 : 0 ≤ s) (hsA : s ≤ A)
    (h : 3 * A ^ 2 + s ^ 2 - D * s - 2 * D * η * A ≤ (2 * η + 4 * η ^ 2) * D ^ 2) :
    A ≤ (1 / 4 + 10 * η) * D := by
  by_contra hA
  push_neg at hA
  set P := (1 / 4 + 10 * η) * D with hP
  have hP0 : 0 ≤ P := by positivity
  rcases le_or_gt (s + A) D with hsD | hsD
  · have h1 : D * s - s ^ 2 ≤ A * D - A ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.2 hsA) (by linarith : 0 ≤ D - A - s)]
    have h2 : 0 < (A - P) * (4 * (A + P) - D * (1 + 2 * η)) :=
      mul_pos (by linarith) (by nlinarith)
    have h3 : 0 ≤ D ^ 2 * (15 / 2 * η + 376 * η ^ 2) := by positivity
    nlinarith
  · have h1 : D * s - s ^ 2 ≤ D ^ 2 / 4 := by nlinarith [sq_nonneg (s - D / 2)]
    have hAD : D / 2 < A := by linarith
    rcases le_or_gt η (1 / 40) with hη | hη
    · have h2 : 0 < (A - D / 2) * (3 * (A + D / 2) - 2 * D * η) :=
        mul_pos (by linarith) (by nlinarith)
      have h3 : 0 ≤ D ^ 2 * (1 / 2 - 3 * η - 4 * η ^ 2) := mul_nonneg (sq_nonneg D) (by nlinarith)
      nlinarith
    · have h2 : 0 < (A - P) * (3 * (A + P) - 2 * D * η) := mul_pos (by linarith) (by nlinarith)
      have h3 : 0 ≤ D ^ 2 * (-1 / 16 + 25 / 2 * η + 276 * η ^ 2) :=
        mul_nonneg (sq_nonneg D) (by nlinarith)
      nlinarith

/-- The length estimate behind `selected_trackLength_le`, in coordinates: if `(p, q)` lies in the
cone `√3 |q| ≤ p` and `|(D/2) ν + (p, q)| ≤ (1/2 + 2η) D`, where `ν = (a, b)` is a unit vector with
`a ≥ -η`, then `p ≤ (√3/2) (1/2 + 20η) D`. -/
lemma length_alg {D η a b p q : ℝ} (hD : 0 ≤ D) (hη0 : 0 ≤ η)
    (hab : a ^ 2 + b ^ 2 = 1) (ha : -η ≤ a) (hc : √3 * |q| ≤ p)
    (hy : (D * a / 2 + p) ^ 2 + (D * b / 2 + q) ^ 2 ≤ ((1 / 2 + 2 * η) * D) ^ 2) :
    p ≤ √3 / 2 * ((1 / 2 + 20 * η) * D) := by
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3p : 0 < √3 := by positivity
  have h32 : √3 < 2 := by nlinarith
  have hp : 0 ≤ p := le_trans (by positivity) hc
  set A := p / √3 with hA
  have hpA : p = √3 * A := by rw [hA]; field_simp
  have hsA : |q| ≤ A := by rw [hA, le_div_iff₀ h3p]; linarith
  have hA0 : 0 ≤ A := le_trans (abs_nonneg q) hsA
  have hbq : -|q| ≤ b * q := by
    have : |b * q| ≤ |q| := by
      rw [abs_mul]
      have : |b| ≤ 1 := abs_le.2 (abs_le_of_sq_le_sq' (by nlinarith : b ^ 2 ≤ 1 ^ 2) zero_le_one)
      nlinarith [abs_nonneg q]
    linarith [neg_abs_le (b * q)]
  have hap : -(2 * η * A) ≤ a * p := by
    rw [hpA]
    have h1 : -η * (√3 * A) ≤ a * (√3 * A) := mul_le_mul_of_nonneg_right ha (by positivity)
    have h2 : η * (√3 * A) ≤ η * (2 * A) := mul_le_mul_of_nonneg_left (by nlinarith) hη0
    linarith
  have hexp : (D * a / 2 + p) ^ 2 + (D * b / 2 + q) ^ 2 =
      D ^ 2 / 4 + D * (a * p + b * q) + p ^ 2 + q ^ 2 := by
    linear_combination (D ^ 2 / 4) * hab
  have hp2 : p ^ 2 = 3 * A ^ 2 := by rw [hpA, mul_pow, h3]
  have hq2 : q ^ 2 = |q| ^ 2 := (sq_abs q).symm
  have key : 3 * A ^ 2 + |q| ^ 2 - D * |q| - 2 * D * η * A ≤ (2 * η + 4 * η ^ 2) * D ^ 2 := by
    have := mul_le_mul_of_nonneg_left (add_le_add hap hbq) hD
    nlinarith
  have := length_alg_A hD hη0 (abs_nonneg q) hsA key
  rw [hpA]
  nlinarith

/-! ## The cone of a track -/

lemma mid_sub_of_rhombusData {X R : Finset Plane} {a b c d : Plane}
    (h : RhombusData X R a b c d) : mid s(c, d) - mid s(a, b) = d - a := by
  rw [mid_mk, mid_mk, h.c_eq]; module

/-- A step `w` across a rhombus (unit, at angle `< π/6` from the normal `J u`, upwards) lies in
the cone `√3 |w · u| ≤ w · J u`. -/
lemma cone_step {u w : Plane} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (h : |inner ℝ w u| < 1 / 2)
    (hpos : 0 < inner ℝ w (rot u)) : √3 * |inner ℝ w u| ≤ inner ℝ w (rot u) := by
  have e := inner_sq_add_inner_rot_sq u w
  rw [hu, hw] at e
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h1 : inner ℝ w u ^ 2 < 1 / 4 := by
    rw [← sq_abs]; nlinarith [abs_nonneg (inner ℝ w u)]
  have : (√3 * |inner ℝ w u|) ^ 2 ≤ inner ℝ w (rot u) ^ 2 := by
    rw [mul_pow, h3, sq_abs]; nlinarith
  exact (abs_le_of_sq_le_sq' this hpos.le).2

/-- Starting from its lowest edge `e`, a track stays in the cone of half-angle `π/6` about the
normal `J u`: every edge `f` satisfies `√3 |(m_f - m_e) · u| ≤ (m_f - m_e) · J u`. -/
lemma track_cone {X : Finset Plane} (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X)
    {T : Finset (Sym2 Plane)} (hT : T ∈ tracks X) {u : Plane} (hu : ‖u‖ = 1)
    (hdir : ∀ e ∈ T, DirOf u e) {e : Sym2 Plane} (he : e ∈ T)
    (hmin : ∀ f ∈ T, ht u e ≤ ht u f) :
    ∀ f ∈ T, √3 * |inner ℝ (mid f - mid e) u| ≤ inner ℝ (mid f - mid e) (rot u) := by
  intro f hf
  obtain ⟨k, rfl⟩ := mem_range_iterate hX htri hT hu hdir he hmin hf
  clear hf
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    set x := (upE X u)^[k] e
    have hx : x ∈ T := iterate_upE_mem (u := u) hT he k
    by_cases h : upE X u x = x
    · rw [h]; exact ih
    · obtain ⟨o, hlt⟩ := upE_spec h
      obtain ⟨a, b, c, d, hR, hxe, hye⟩ := oppositeSides_data hX htri o
      obtain ⟨g, i, n⟩ := hR.step (hxe ▸ hdir x hx)
      have hm : mid (upE X u x) - mid e = (mid x - mid e) + (d - a) := by
        rw [← mid_sub_of_rhombusData hR, ← hxe, ← hye]; abel
      have hpos : 0 < inner ℝ (d - a) (rot u) := by
        rw [← g, ← hxe, ← hye]; linarith
      have hw := cone_step hu n i hpos
      rw [hm, inner_add_left, inner_add_left]
      calc √3 * |inner ℝ (mid x - mid e) u + inner ℝ (d - a) u|
          ≤ √3 * (|inner ℝ (mid x - mid e) u| + |inner ℝ (d - a) u|) :=
            mul_le_mul_of_nonneg_left (abs_add_le _ _) (by positivity)
        _ ≤ _ := by linarith

/-! ## Selected tracks -/

/-- Unpacking `IsSelectedTrack`: a unit direction `u` of the track with `J u = n`. -/
lemma selected_setup {X : Finset Plane} {T : Finset (Sym2 Plane)} (hT : T ∈ tracks X)
    {O : Plane} {D η : ℝ} (hsel : IsSelectedTrack O D η T) :
    ∃ e ∈ T, ∃ ν u : Plane, ‖ν‖ = 1 ∧ ‖u‖ = 1 ∧ (∀ f ∈ T, DirOf u f) ∧
      ‖mid e - O - (D / 2) • ν‖ ≤ η * D ∧ -η ≤ inner ℝ (rot u) ν ∧
      ∀ f ∈ T, ht u e ≤ ht u f := by
  obtain ⟨e, he, ν, n, hν, hn, hm, hnν, hf⟩ := hsel
  have hTe := eq_trackOf_of_mem hT he
  have hunit : e ∈ unitEdges X := by
    have he' := he
    rw [hTe] at he'
    exact (Finset.mem_filter.1 (mem_trackOf.1 he').1).1
  have hdv : ‖dv e‖ = 1 := norm_dv_of_mem_unitEdges hunit
  have hdir : ∀ f ∈ T, DirOf (dv e) f := fun f hf => by
    rw [hTe] at hf; exact sameDir_of_mem_trackOf hf
  have hht : ∀ u, rot u = n → ∀ f ∈ T, ht u e ≤ ht u f := fun u hu f hfT => by
    have := hf f hfT
    rw [← hu, inner_sub_left] at this
    unfold ht; linarith
  rcases hn with rfl | rfl
  · exact ⟨e, he, ν, dv e, hν, hdv, hdir, hm, hnν, hht _ rfl⟩
  · refine ⟨e, he, ν, -dv e, hν, by rw [norm_neg]; exact hdv, fun f hf => ?_, hm,
      by rwa [rot_neg], hht _ (rot_neg _)⟩
    rcases hdir f hf with h | h
    · right; rw [neg_neg]; exact h
    · left; exact h

lemma norm_sq_frame {u : Plane} (hu : ‖u‖ = 1) (y : Plane) :
    ‖y‖ ^ 2 = inner ℝ y (rot u) ^ 2 + inner ℝ y u ^ 2 := by
  have := inner_sq_add_inner_rot_sq u y
  rw [hu] at this; linarith

lemma inner_frame_add (D : ℝ) (ν v w : Plane) :
    inner ℝ ((D / 2) • ν + v) w = D * inner ℝ ν w / 2 + inner ℝ v w := by
  rw [inner_add_left, real_inner_smul_left]; ring

lemma mem_unitEdges_of_mem_tracks {X : Finset Plane} {T : Finset (Sym2 Plane)}
    (hT : T ∈ tracks X) {f : Sym2 Plane} (hf : f ∈ T) : f ∈ unitEdges X := by
  rw [eq_trackOf_of_mem hT hf] at hf
  exact (Finset.mem_filter.1 (mem_trackOf.1 hf).1).1

/-- Lemma 3.5 / Lemma 6.1 (direction–length estimate): a selected track inside the disc of
radius `D/2 + η D` has at most `(1/2 + 20 η) D` rhombi. -/
theorem selected_trackLength_le {X : Finset Plane} (hX : IsSeparated X)
    (htri : ¬ HasUnitTriangle X) {T : Finset (Sym2 Plane)} (hT : T ∈ tracks X) {O : Plane}
    {D η : ℝ} (hD : 0 < D) (hη0 : 0 ≤ η)
    (hball : ∀ x ∈ X, dist x O ≤ D / 2 + η * D) (hsel : IsSelectedTrack O D η T) :
    (trackLength X T : ℝ) ≤ (1 / 2 + 20 * η) * D := by
  obtain ⟨e, he, ν, u, hν, hu, hdir, hm, hnν, hmin⟩ := selected_setup hT hsel
  have hcone := track_cone hX htri hT hu hdir he hmin
  have hab : inner ℝ ν (rot u) ^ 2 + inner ℝ ν u ^ 2 = 1 := by
    rw [← norm_sq_frame hu, hν, one_pow]
  have ha : -η ≤ inner ℝ ν (rot u) := by rwa [real_inner_comm]
  have hasq : aStar = √3 / 2 := rfl
  -- every edge lies at most `a* (1/2 + 20η) D` above `e`
  have hbound : ∀ f ∈ T, ht u f - ht u e ≤ aStar * ((1 / 2 + 20 * η) * D) := by
    intro f hf
    have hmidball : ‖mid f - O‖ ≤ D / 2 + η * D := by
      obtain ⟨⟨x, z⟩, hxz, hfe⟩ := Finset.mem_image.1 (mem_unitEdges_of_mem_tracks hT hf)
      simp only [Finset.mem_filter, Finset.mem_product] at hxz
      rw [← hfe, mid_mk]
      have h1 := hball x hxz.1.1
      have h2 := hball z hxz.1.2
      rw [dist_eq_norm] at h1 h2
      calc ‖(1 / 2 : ℝ) • (x + z) - O‖ = ‖(1 / 2 : ℝ) • ((x - O) + (z - O))‖ := by
            congr 1; module
        _ ≤ (1 / 2) * (‖x - O‖ + ‖z - O‖) := by
            rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
            exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
        _ ≤ _ := by linarith
    have hyle : ‖(D / 2) • ν + (mid f - mid e)‖ ≤ (1 / 2 + 2 * η) * D := by
      have : (D / 2) • ν + (mid f - mid e) = (mid f - O) - (mid e - O - (D / 2) • ν) := by abel
      rw [this]
      calc _ ≤ ‖mid f - O‖ + ‖mid e - O - (D / 2) • ν‖ := norm_sub_le _ _
        _ ≤ _ := by linarith
    have hy := pow_le_pow_left₀ (norm_nonneg _) hyle 2
    rw [norm_sq_frame hu, inner_frame_add, inner_frame_add] at hy
    have := length_alg hD.le hη0 hab ha (hcone f hf) hy
    have hp : inner ℝ (mid f - mid e) (rot u) = ht u f - ht u e := by
      simp only [ht, inner_sub_left]
    rw [hasq, ← hp]; exact this
  -- counting: heights of `T` are `a*`-separated in an interval of length `a* (1/2 + 20η) D`
  have h12 := trackLength_add_one_le_card hX htri hT
  have hap := aStar_pos
  set S := T.image (fun e => ht u e / aStar)
  have hinj : Set.InjOn (fun e => ht u e / aStar) T := fun e1 he1 f hf hef => by
    by_contra hne
    have := ht_sep hX htri hT hu hdir he1 hf hne
    simp only at hef
    rw [div_left_inj' hap.ne', ← sub_eq_zero] at hef
    rw [hef, abs_zero] at this; linarith
  have hS : S.card = T.card := Finset.card_image_of_injOn hinj
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_spread_of_separated_real S ⟨_, Finset.mem_image_of_mem _ he⟩
    (by
      simp only [S, Finset.mem_image]
      rintro _ ⟨e1, he1, rfl⟩ _ ⟨f, hf, rfl⟩ hne
      have hef : e1 ≠ f := fun h => hne (by rw [h])
      have := ht_sep hX htri hT hu hdir he1 hf hef
      rw [← sub_div, abs_div, abs_of_pos hap, le_div_iff₀ hap]; linarith)
  obtain ⟨e1, he1, rfl⟩ := Finset.mem_image.1 hx
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hy
  have hdiff : ht u f - ht u e1 ≤ aStar * ((1 / 2 + 20 * η) * D) := by
    linarith [hbound f hf, hmin e1 he1]
  rw [hS, ← sub_div] at hxy
  have h3 : (T.card : ℝ) - 1 ≤ (1 / 2 + 20 * η) * D := by
    refine hxy.trans ?_
    rw [div_le_iff₀ hap]; linarith
  have h4 : (trackLength X T : ℝ) + 1 ≤ T.card := by exact_mod_cast h12
  linarith

/-- Lemma 6.1: the spine of a selected track stays at distance at least
`(D/2) √(1 - (1/2 + η)²) - η D` from the centre. -/
theorem selected_spine_far {X : Finset Plane} (hX : IsSeparated X)
    (htri : ¬ HasUnitTriangle X) {T : Finset (Sym2 Plane)} (hT : T ∈ tracks X) {O : Plane}
    {D η : ℝ} (hD : 0 < D) (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 2) (hsel : IsSelectedTrack O D η T) :
    ∀ f ∈ T, D / 2 * √(1 - (1 / 2 + η) ^ 2) - η * D ≤ dist (mid f) O := by
  obtain ⟨e, he, ν, u, hν, hu, hdir, hm, hnν, hmin⟩ := selected_setup hT hsel
  have hcone := track_cone hX htri hT hu hdir he hmin
  have hab : inner ℝ ν (rot u) ^ 2 + inner ℝ ν u ^ 2 = 1 := by
    rw [← norm_sq_frame hu, hν, one_pow]
  have ha : -η ≤ inner ℝ ν (rot u) := by rwa [real_inner_comm]
  intro f hf
  have hy := spine_alg hD.le hη0 hη1 hab ha (hcone f hf)
  rw [← inner_frame_add, ← inner_frame_add, ← norm_sq_frame hu] at hy
  set y := (D / 2) • ν + (mid f - mid e)
  have hyn : D / 2 * √(1 - (1 / 2 + η) ^ 2) ≤ ‖y‖ := by
    rw [show D / 2 * √(1 - (1 / 2 + η) ^ 2) = √((D / 2) ^ 2 * (1 - (1 / 2 + η) ^ 2)) by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]]
    rw [← Real.sqrt_sq (norm_nonneg y)]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hdecomp : mid f - O = y + (mid e - O - (D / 2) • ν) := by simp only [y]; abel
  rw [dist_eq_norm, hdecomp]
  have := norm_sub_le (y + (mid e - O - (D / 2) • ν)) (mid e - O - (D / 2) • ν)
  rw [add_sub_cancel_right] at this
  linarith

/-! ## Rhombi in an annulus -/

/-- Every vertex of a unit rhombus lies within `3/2` of the midpoint of each of its sides. -/
lemma dist_midpoint_side_le {X : Finset Plane} (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X)
    {R : Finset Plane} (hR : R ∈ rhombi X) {p q : Plane} (hp : p ∈ R) (hq : q ∈ R)
    (hpq : dist p q = 1) : ∀ x ∈ R, dist x (midpoint ℝ p q) ≤ 3 / 2 := by
  obtain ⟨a, b, c, d, h⟩ := exists_rhombusData hX htri hR
  have hab := h.hab; have hbc := h.hbc; have hcd := h.hcd; have hda := h.hda
  have hba : dist b a = 1 := by rw [dist_comm]; exact hab
  have hcb : dist c b = 1 := by rw [dist_comm]; exact hbc
  have hdc : dist d c = 1 := by rw [dist_comm]; exact hcd
  have had : dist a d = 1 := by rw [dist_comm]; exact hda
  have hac := h.diag1; have hbd := h.diag2
  have hca : 1 < dist c a := by rw [dist_comm]; exact hac
  have hdb : 1 < dist d b := by rw [dist_comm]; exact hbd
  have key : ∀ x ∈ R, dist x p ≤ 1 ∨ dist x q ≤ 1 := by
    intro x hx
    rw [h.eq] at hp hq hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq hx
    rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;>
      rcases hx with rfl | rfl | rfl | rfl <;>
      first
        | exact Or.inl (by simp)
        | exact Or.inr (by simp)
        | exact Or.inl (le_of_eq (by assumption))
        | exact Or.inr (le_of_eq (by assumption))
        | (exfalso; simp at hpq)
  intro x hx
  have hmid : dist p (midpoint ℝ p q) = 1 / 2 := by
    rw [dist_left_midpoint, hpq]; norm_num
  have hmid' : dist q (midpoint ℝ p q) = 1 / 2 := by
    rw [dist_right_midpoint, hpq]; norm_num
  rcases key x hx with h1 | h1
  · linarith [dist_triangle x p (midpoint ℝ p q)]
  · linarith [dist_triangle x q (midpoint ℝ p q)]

/-- The volume of the annulus `{r ≤ |z - O| ≤ ρ}`. -/
lemma volume_annulus (O : Plane) {r ρ : ℝ} (hr : 0 ≤ r) (hrρ : r ≤ ρ) :
    volume (Metric.closedBall O ρ \ Metric.ball O r) = ENNReal.ofReal (π * (ρ ^ 2 - r ^ 2)) := by
  rw [measure_diff (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall hrρ))
      measurableSet_ball.nullMeasurableSet (measure_ball_lt_top).ne,
    EuclideanSpace.volume_closedBall_fin_two, EuclideanSpace.volume_ball_fin_two,
    ← ENNReal.ofReal_pow (hr.trans hrρ), ← ENNReal.ofReal_pow hr,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_sub _ (by positivity)]
  congr 1; ring

/-- The rhombi in a family `S`, each having a side whose midpoint is at distance at least
`r + 3/2` from `O`, inside the disc of radius `ρ ≥ r`, number at most `π (ρ² - r²) / a*`. -/
theorem card_mul_aStar_le_annulus {X : Finset Plane} (hX : IsSeparated X)
    (htri : ¬ HasUnitTriangle X) {S : Finset (Finset Plane)} (hS : S ⊆ rhombi X) {O : Plane}
    {r ρ : ℝ} (hr : 0 ≤ r) (hrρ : r ≤ ρ) (hball : ∀ x ∈ X, dist x O ≤ ρ)
    (hfar : ∀ R ∈ S, ∃ p ∈ R, ∃ q ∈ R, dist p q = 1 ∧ r + 3 / 2 ≤ dist (midpoint ℝ p q) O) :
    (S.card : ℝ) * aStar ≤ π * (ρ ^ 2 - r ^ 2) := by
  have hrepQ := fun Q (hQ : Q ∈ S) => rhombus_rep hX htri (hS hQ)
  choose! A U W hrep hu hw hi using hrepQ
  have hsubX : ∀ Q ∈ S, Q ⊆ X ∧ Q.card = 4 := fun Q hQ =>
    Finset.mem_powersetCard.1 (Finset.mem_filter.1 (hS hQ)).1
  have hdisj : (↑S : Set (Finset Plane)).PairwiseDisjoint
      (fun Q => paraOpen (A Q) (U Q) (W Q)) := by
    intro Q hQ Q' hQ' hne
    have h1 := hsubX Q hQ; have h2 := hsubX Q' hQ'
    rw [hrep Q hQ] at h1 hne
    rw [hrep Q' hQ'] at h2 hne
    exact paraOpen_disjoint hX h1.1 (hu Q hQ) (hw Q hQ) (hi Q hQ) h2.1 (hu Q' hQ') (hw Q' hQ')
      (hi Q' hQ') h2.2 hne
  have hsub : (⋃ Q ∈ S, paraOpen (A Q) (U Q) (W Q)) ⊆
      Metric.closedBall O ρ \ Metric.ball O r := by
    refine Set.iUnion₂_subset fun Q hQ => ?_
    have hconv : paraOpen (A Q) (U Q) (W Q) ⊆ convexHull ℝ (Q : Set Plane) := by
      refine (paraOpen_subset_paraClosed _ _ _).trans
        ((paraClosed_subset_convexHull _ _ _).trans (convexHull_mono ?_))
      intro v hv
      rw [hrep Q hQ]
      simpa using hv
    obtain ⟨p, hp, q, hq, hpq, hfarQ⟩ := hfar Q hQ
    have hQball : convexHull ℝ (Q : Set Plane) ⊆ Metric.closedBall O ρ :=
      convexHull_min (fun v hv => Metric.mem_closedBall.2 (hball v ((hsubX Q hQ).1 hv)))
        (convex_closedBall O ρ)
    have hQmid : convexHull ℝ (Q : Set Plane) ⊆ Metric.closedBall (midpoint ℝ p q) (3 / 2) :=
      convexHull_min (fun v hv => Metric.mem_closedBall.2
        (dist_midpoint_side_le hX htri (hS hQ) hp hq hpq v hv)) (convex_closedBall _ _)
    intro z hz
    refine ⟨hQball (hconv hz), fun hzr => ?_⟩
    have h1 := Metric.mem_closedBall.1 (hQmid (hconv hz))
    have h2 := Metric.mem_ball.1 hzr
    linarith [dist_triangle (midpoint ℝ p q) z O, dist_comm z (midpoint ℝ p q)]
  have hvol : ∑ Q ∈ S, ENNReal.ofReal |cr (U Q) (W Q)| ≤
      ENNReal.ofReal (π * (ρ ^ 2 - r ^ 2)) := by
    calc ∑ Q ∈ S, ENNReal.ofReal |cr (U Q) (W Q)|
        = ∑ Q ∈ S, volume (paraOpen (A Q) (U Q) (W Q)) :=
          Finset.sum_congr rfl fun Q _ => (volume_paraOpen _ _ _).symm
      _ = volume (⋃ Q ∈ S, paraOpen (A Q) (U Q) (W Q)) :=
          (measure_biUnion_finset hdisj fun Q hQ =>
            (isOpen_paraOpen (cr_ne_zero_of_rep (hu Q hQ) (hw Q hQ) (hi Q hQ))).measurableSet).symm
      _ ≤ volume (Metric.closedBall O ρ \ Metric.ball O r) := measure_mono hsub
      _ = ENNReal.ofReal (π * (ρ ^ 2 - r ^ 2)) := volume_annulus O hr hrρ
  have hsum : ∑ Q ∈ S, |cr (U Q) (W Q)| ≤ π * (ρ ^ 2 - r ^ 2) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun Q _ => abs_nonneg _)] at hvol
    have hnn : 0 ≤ π * (ρ ^ 2 - r ^ 2) := by
      have : r ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ hr hrρ 2
      have := Real.pi_pos
      nlinarith
    exact (ENNReal.ofReal_le_ofReal_iff hnn).1 hvol
  calc (S.card : ℝ) * aStar = ∑ Q ∈ S, aStar := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ Q ∈ S, |cr (U Q) (W Q)| :=
        Finset.sum_le_sum fun Q hQ => aStar_le_abs_cr (hu Q hQ) (hw Q hQ) (hi Q hQ)
    _ ≤ _ := hsum

/-- **Lemma 6.1 (annular cost of the selected tracks).**  For a family `sel` of selected tracks in
a configuration contained in the disc of radius `D/2 + η D`, the number `Q_P` of rhombi touched
by `sel` satisfies `Q_P ≤ (1/2 + 20η) D P` and `Q_P ≤ (c/4 + 40 η) D²`, where `P = |sel|`. -/
theorem selected_rhombi_bounds {X : Finset Plane} (hX : IsSeparated X)
    (htri : ¬ HasUnitTriangle X) {O : Plane} {D η : ℝ} (hD : 0 < D) (hη0 : 0 ≤ η)
    (hη1 : η ≤ 1 / 8) (hDη : 3 ≤ η * D) (hball : ∀ x ∈ X, dist x O ≤ D / 2 + η * D)
    {sel : Finset (Finset (Sym2 Plane))} (hsel : sel ⊆ tracks X)
    (hs : ∀ T ∈ sel, IsSelectedTrack O D η T) :
    (((rhombi X).filter (fun R => ∃ T ∈ sel, Crosses T R)).card : ℝ) ≤
        (1 / 2 + 20 * η) * D * sel.card ∧
      (((rhombi X).filter (fun R => ∃ T ∈ sel, Crosses T R)).card : ℝ) ≤
        (cDensity / 4 + 40 * η) * D ^ 2 := by
  set Sel := (rhombi X).filter (fun R => ∃ T ∈ sel, Crosses T R) with hSel_def
  constructor
  · -- union bound over the selected tracks
    have hSel : Sel ⊆ sel.biUnion (fun T => (rhombi X).filter (Crosses T)) := by
      intro R hR
      obtain ⟨hR, T, hT, hc⟩ := Finset.mem_filter.1 hR
      exact Finset.mem_biUnion.2 ⟨T, hT, Finset.mem_filter.2 ⟨hR, hc⟩⟩
    have h1 : (Sel.card : ℝ) ≤ ∑ T ∈ sel, (trackLength X T : ℝ) := by
      have := (Finset.card_le_card hSel).trans Finset.card_biUnion_le
      exact_mod_cast this
    have h2 : ∑ T ∈ sel, (trackLength X T : ℝ) ≤ ∑ T ∈ sel, (1 / 2 + 20 * η) * D :=
      Finset.sum_le_sum fun T hT =>
        selected_trackLength_le hX htri (hsel hT) hD hη0 hball (hs T hT)
    rw [Finset.sum_const, nsmul_eq_mul] at h2
    linarith
  · -- the touched rhombi lie in an annulus
    set s := √(1 - (1 / 2 + η) ^ 2) with hs_def
    have hs2 : s ^ 2 = 1 - (1 / 2 + η) ^ 2 := Real.sq_sqrt (by nlinarith)
    have hs1 : s ≤ 1 := Real.sqrt_le_one.mpr (by nlinarith)
    have hs34 : 3 / 4 ≤ s := Real.le_sqrt_of_sq_le (by nlinarith)
    set r := D / 2 * s - η * D - 3 / 2 with hr_def
    have hr0 : 0 ≤ r := by nlinarith
    have hrρ : r ≤ D / 2 + η * D := by nlinarith
    have hfar : ∀ R ∈ Sel, ∃ p ∈ R, ∃ q ∈ R, dist p q = 1 ∧
        r + 3 / 2 ≤ dist (midpoint ℝ p q) O := by
      intro R hR
      obtain ⟨-, T, hT, f, hf, hfR⟩ := Finset.mem_filter.1 hR
      obtain ⟨⟨p, q⟩, hpq, rfl⟩ := Finset.mem_image.1 (mem_unitEdges_of_mem_tracks (hsel hT) hf)
      simp only [Finset.mem_filter, Finset.mem_product] at hpq
      refine ⟨p, hfR p (by simp), q, hfR q (by simp), hpq.2, ?_⟩
      have := selected_spine_far hX htri (hsel hT) hD hη0 (by linarith) (hs T hT) _ hf
      have hmid : mid s(p, q) = midpoint ℝ p q := by
        rw [mid_mk, midpoint_eq_smul_add]; norm_num
      rw [hmid] at this
      linarith
    have hcard := card_mul_aStar_le_annulus hX htri (Finset.filter_subset _ _) hr0 hrρ hball hfar
    -- numerics
    have hr1 : D * (s / 2 - 3 / 2 * η) ≤ r := by nlinarith
    have hr2 : 0 ≤ D * (s / 2 - 3 / 2 * η) := mul_nonneg hD.le (by nlinarith)
    have hrsq : (D * (s / 2 - 3 / 2 * η)) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hr2 hr1 2
    have hdiff : (D / 2 + η * D) ^ 2 - r ^ 2 ≤ D ^ 2 * (1 / 16 + 3 * η) := by
      have : (D * (s / 2 - 3 / 2 * η)) ^ 2 = D ^ 2 * (s ^ 2 / 4 - 3 / 2 * η * s + 9 / 4 * η ^ 2) := by
        ring
      rw [this, hs2] at hrsq
      have h1 : D ^ 2 * (η * s) ≤ D ^ 2 * η := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg D); nlinarith
      nlinarith [sq_nonneg D]
    have hca : cDensity * aStar = π / 4 := by
      unfold cDensity aStar
      have : √3 ≠ 0 := by positivity
      field_simp
      norm_num
    have hap := aStar_pos
    have hpi := Real.pi_pos
    have hpi4 := Real.pi_lt_four
    have ha8 : 4 / 5 < aStar := by
      unfold aStar
      have : (8 / 5 : ℝ) < √3 := Real.lt_sqrt_of_sq_lt (by norm_num)
      linarith
    have hfinal : π * ((D / 2 + η * D) ^ 2 - r ^ 2) ≤ (cDensity / 4 + 40 * η) * D ^ 2 * aStar := by
      have e : (cDensity / 4 + 40 * η) * D ^ 2 * aStar =
          D ^ 2 * (cDensity * aStar / 4 + 40 * η * aStar) := by ring
      rw [e, hca]
      have h1 := mul_le_mul_of_nonneg_left hdiff hpi.le
      have h2 : 0 ≤ D ^ 2 * η * (40 * aStar - 3 * π) :=
        mul_nonneg (by positivity) (by nlinarith)
      linarith
    exact le_of_mul_le_mul_right (hcard.trans hfinal) hap

end Erdos99
end

end Annulus
