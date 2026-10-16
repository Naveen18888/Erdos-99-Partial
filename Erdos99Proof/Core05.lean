module

public import Mathlib
public import Erdos99Proof.Core04

section BoundaryPortBounds

open scoped BigOperators Real
open ComplexConjugate

@[expose] public noncomputable section

open Classical

namespace Erdos99

namespace BoundaryPort

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

lemma aStar_sq : aStar ^ 2 = 3 / 4 := by
  unfold aStar; rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num

lemma aStar_lt_one : aStar < 1 := by
  have := aStar_sq; have := aStar_pos; nlinarith

lemma one_le_sqrt_three : 1 ≤ √3 := by
  rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)

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

lemma sum_sq_unit_identity {c1 c2 c3 : ℂ} (h1 : c1 * conj c1 = 1) (h2 : c2 * conj c2 = 1)
    (h3 : c3 * conj c3 = 1) :
    c1 ^ 2 + c2 ^ 2 + c3 ^ 2 =
      (c1 + c2 + c3) ^ 2 - 2 * (c1 * c2 * c3) * conj (c1 + c2 + c3) := by
  simp only [map_add]
  linear_combination (2 * c2 * c3) * h1 + (2 * c1 * c3) * h2 + (2 * c1 * c2) * h3

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

theorem three_ports_noncancel {u1 u2 u3 τ : Plane} {k : ℝ} (hk : 0 < k) (hu1 : ‖u1‖ = 1)
    (hu2 : ‖u2‖ = 1) (hu3 : ‖u3‖ = 1) (hτ : ‖τ‖ = 1)
    (h1 : inner ℝ u1 τ ≤ 1 / 2 - k) (h2 : inner ℝ u2 τ ≤ 1 / 2 - k)
    (h3 : inner ℝ u3 τ ≤ 1 / 2 - k) :
    min 1 k ≤ ‖u1 + u2 + u3‖ := by

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

theorem three_ports_inner {u1 u2 u3 : Plane} (hu1 : ‖u1‖ = 1) (hu2 : ‖u2‖ = 1)
    (hu3 : ‖u3‖ = 1) (h0 : u1 + u2 + u3 = 0) : inner ℝ u1 u2 = -1 / 2 := by
  have h : u1 + u2 = -u3 := eq_neg_of_add_eq_zero_left h0
  have e := norm_add_sq_real u1 u2
  rw [h, norm_neg, hu1, hu2, hu3] at e
  linarith

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
  ·
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
  ·
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

theorem IsSelectedTrack.mono {O : Plane} {D η η' : ℝ} {T : Finset (Sym2 Plane)} (hD : 0 ≤ D)
    (hη : η ≤ η') (h : IsSelectedTrack O D η T) : IsSelectedTrack O D η' T := by
  obtain ⟨e, he, ν, n, hν, hn, hm, hf, hside⟩ := h
  exact ⟨e, he, ν, n, hν, hn, hm.trans (mul_le_mul_of_nonneg_right hη hD), by linarith, hside⟩

theorem isSelectedTrack_of_port {O : Plane} {D θ δ η : ℝ} {T : Finset (Sym2 Plane)} (hD : 0 ≤ D)
    (hθ : θ ≤ η) (hδ : δ ≤ η) {e : Sym2 Plane} (he : e ∈ T) {ν n : Plane} (hν : ‖ν‖ = 1)
    (hn : n = rot (dv e) ∨ n = -rot (dv e)) (hm : ‖mid e - O - (D / 2) • ν‖ ≤ δ * D)
    (hf : -θ ≤ inner ℝ n ν) (hside : ∀ f ∈ T, 0 ≤ inner ℝ (mid f - mid e) n) :
    IsSelectedTrack O D η T :=
  ⟨e, he, ν, n, hν, hn, hm.trans (mul_le_mul_of_nonneg_right hδ hD), by linarith, hside⟩

theorem mem_longTracks_of_le {X : Finset Plane} {T : Finset (Sym2 Plane)} {L : ℝ}
    (hT : T ∈ tracks X) (hL : L ≤ trackLength X T) : T ∈ longTracks X L :=
  Finset.mem_filter.2 ⟨hT, hL⟩

end BoundaryPort

end Erdos99
end

end BoundaryPortBounds

section ChargingGraph

open scoped BigOperators Real
open Filter

@[expose] public noncomputable section

open Classical

namespace Erdos99

open LocalCharge

namespace GoodFaces

variable {X : Finset Plane}

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

lemma card_good_le (hX : IsSeparated X) (G : GoodFaces X) : G.good.card ≤ numExceptional X := by
  rw [numExceptional_eq_card hX]; exact Finset.card_le_card G.good_subset

lemma numExceptional_le (hX : IsSeparated X) (G : GoodFaces X) :
    numExceptional X ≤ G.good.card + G.Bface := by
  rw [numExceptional_eq_card hX, ← Finset.card_filter_add_card_filter_not (fun F => F ∈ G.good)]
  refine add_le_add (Finset.card_le_card fun F hF => (Finset.mem_filter.1 hF).2) ?_
  rw [Bface, Finset.card_eq_sum_ones]
  refine Finset.sum_le_sum fun F hF => ?_
  have := ((mem_exceptionalFinset hX).1 (Finset.mem_filter.1 hF).1).2
  omega

end GoodFaces

structure ChargingGraph (X : Finset Plane) (L : ℝ) (G : GoodFaces X) where

  g : StubGraph (Set ℂ)

  flagged : Finset (Set ℂ)
  edges_good : ∀ e ∈ g.E, g.src e ∈ G.good ∧ g.tgt e ∈ G.good
  deg_add_marks : ∀ F ∈ G.good, g.deg F + G.marks F = shortDeg X L (Sum.inl F)
  deg_mem : ∀ F ∈ G.good, 2 ≤ g.deg F ∧ g.deg F ≤ 4

namespace ChargingGraph

variable {X : Finset Plane} {L : ℝ} {G : GoodFaces X} (cg : ChargingGraph X L G)

def capInc : ℝ := cg.g.bIn G.good + 2 * cg.g.eIn (cg.g.Hs G.good) (cg.g.Hs G.good)

def hCapInc : ℝ :=
  cg.g.bIn (cg.g.Hs G.good) + 2 * cg.g.eIn (cg.g.Hs G.good) (cg.g.Hs G.good)

def pinned (M : ℕ) : ℝ :=
  cg.g.stublessSmall (cg.g.Gs G.good) M + cg.g.stublessSmall (cg.g.Ks G.good) M +
    4 * cg.g.defJ G.good cg.flagged + cg.g.excE G.good cg.flagged

lemma Ysum_eq : cg.g.Ysum G.good = G.Y L := by
  rw [G.Y_eq_sum_good, StubGraph.Ysum]
  refine Finset.sum_congr rfl fun F hF => ?_
  rw [← cg.deg_add_marks F hF]; push_cast; ring

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

def IsFlaggedPort (X : Finset Plane) (O : Plane) (D lam θ δ : ℝ) (F : Set ℂ)
    (T : Finset (Sym2 Plane)) : Prop :=
  lam * D ≤ trackLength X T ∧ ∃ e ∈ T, IsPort X (Sum.inl F) e ∧ ∃ ν n : Plane, ‖ν‖ = 1 ∧
    (n = rot (dv e) ∨ n = -rot (dv e)) ∧ ‖mid e - O - (D / 2) • ν‖ ≤ δ * D ∧
    -θ ≤ inner ℝ n ν ∧ ∀ f ∈ T, 0 ≤ inner ℝ (mid f - mid e) n

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

section HalfEdgeGraph

open scoped BigOperators

@[expose] public noncomputable section

open Classical

namespace Erdos99

namespace LocalCharge

namespace StubGraph

variable {α β : Type*} [Inhabited β]

def hEnum (P : Finset β) (i : ℕ) : β := P.toList.getD i default

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

def ofHalfEdges : StubGraph α where
  E := (Finset.range P.card).filter
    (fun i => mated (hEnum P i) ∧ i < hIdx P (mate (hEnum P i)))
  src i := v (hEnum P i)
  tgt i := v (mate (hEnum P i))
  S := (Finset.range P.card).filter (fun i => ¬ mated (hEnum P i))
  stub i := v (hEnum P i)

def IsMatching : Prop :=
  ∀ q ∈ P, mated q → mate q ∈ P ∧ mate q ≠ q ∧ mate (mate q) = q ∧ mated (mate q)

variable {P v mate mated}

lemma ofHalfEdges_edges_mem (hM : IsMatching P mate mated) :
    ∀ e ∈ (ofHalfEdges P v mate mated).E, (ofHalfEdges P v mate mated).src e ∈ P.image v ∧
      (ofHalfEdges P v mate mated).tgt e ∈ P.image v := by
  intro i hi
  simp only [ofHalfEdges, Finset.mem_filter, Finset.mem_range] at hi
  have hm := hEnum_mem P hi.1
  exact ⟨Finset.mem_image_of_mem _ hm, Finset.mem_image_of_mem _ (hM _ hm hi.2.1).1⟩

lemma ofHalfEdges_stub_mem :
    ∀ s ∈ (ofHalfEdges P v mate mated).S, (ofHalfEdges P v mate mated).stub s ∈ P.image v := by
  intro i hi
  simp only [ofHalfEdges, Finset.mem_filter, Finset.mem_range] at hi
  exact Finset.mem_image_of_mem _ (hEnum_mem P hi.1)

theorem deg_ofHalfEdges (hM : IsMatching P mate mated) (a : α) :
    (ofHalfEdges P v mate mated).deg a = (P.filter (fun q => v q = a)).card := by
  set g := ofHalfEdges P v mate mated

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

theorem bIn_ofHalfEdges (A : Finset α) :
    (ofHalfEdges P v mate mated).bIn A = (P.filter (fun q => ¬ mated q ∧ v q ∈ A)).card := by
  classical
  unfold bIn
  dsimp only [ofHalfEdges]
  refine Finset.card_nbij' (hEnum P) (hIdx P) ?_ ?_ ?_ ?_
  · intro i hi
    change i ∈ ((Finset.range P.card).filter (fun i => ¬ mated (hEnum P i))).filter
      (fun i => v (hEnum P i) ∈ A) at hi
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_range] at hi
    change hEnum P i ∈ P.filter (fun q => ¬ mated q ∧ v q ∈ A)
    rw [Finset.mem_filter]
    exact ⟨hEnum_mem P hi.1.1, hi.1.2, hi.2⟩
  · intro q hq
    simp only [Finset.mem_coe, Finset.mem_filter] at hq
    change hIdx P q ∈ ((Finset.range P.card).filter (fun i => ¬ mated (hEnum P i))).filter
      (fun i => v (hEnum P i) ∈ A)
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_range, hEnum_hIdx P hq.1]
    exact ⟨⟨hIdx_lt P hq.1, hq.2.1⟩, hq.2.2⟩
  · intro i hi
    change i ∈ ((Finset.range P.card).filter (fun i => ¬ mated (hEnum P i))).filter
      (fun i => v (hEnum P i) ∈ A) at hi
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_range] at hi
    exact hIdx_hEnum P hi.1.1
  · intro q hq
    simp only [Finset.mem_coe, Finset.mem_filter] at hq
    exact hEnum_hIdx P hq.1

end StubGraph

end LocalCharge

end Erdos99

end

end HalfEdgeGraph

section TrackChargingGraph

open scoped BigOperators

@[expose] public noncomputable section

open Classical

namespace Erdos99

open LocalCharge

def shortPorts (X : Finset Plane) (L : ℝ) (F : Set ℂ) : Finset (Sym2 Plane) :=
  (unitEdges X).filter (fun e => IsPort X (Sum.inl F) e ∧ (trackLength X (allTrackOf X e) : ℝ) < L)

lemma card_shortPorts (X : Finset Plane) (L : ℝ) (F : Set ℂ) :
    (shortPorts X L F).card = shortDeg X L (Sum.inl F) := rfl

def otherEnd (X : Finset Plane) (q : Set ℂ × Sym2 Plane) : PortNode × Sym2 Plane :=
  if h : ((trackEnds X (allTrackOf X q.2)).erase (Sum.inl q.1, q.2)).Nonempty then h.choose
  else (Sum.inl q.1, q.2)

def nodeFace : PortNode → Set ℂ := Sum.elim id (fun _ => ∅)

def unmarkedPorts (X : Finset Plane) (L : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane)) :
    Finset (Set ℂ × Sym2 Plane) :=
  (G.good ×ˢ unitEdges X).filter (fun q => q.2 ∈ shortPorts X L q.1 ∧ q.2 ∉ mk q.1)

def trackMate (X : Finset Plane) (q : Set ℂ × Sym2 Plane) : Set ℂ × Sym2 Plane :=
  (nodeFace (otherEnd X q).1, (otherEnd X q).2)

def TrackMated (X : Finset Plane) (L : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane))
    (q : Set ℂ × Sym2 Plane) : Prop :=
  (otherEnd X q).1 = Sum.inl (nodeFace (otherEnd X q).1) ∧ trackMate X q ∈ unmarkedPorts X L G mk

def trackGraph (X : Finset Plane) (L : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane)) :
    StubGraph (Set ℂ) :=
  StubGraph.ofHalfEdges (unmarkedPorts X L G mk) Prod.fst (trackMate X) (TrackMated X L G mk)

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

theorem trackMate_isMatching {X : Finset Plane}
    (hends : ∀ T ∈ allTracks X, (trackEnds X T).card = 2) (L : ℝ) (G : GoodFaces X)
    (mk : Set ℂ → Finset (Sym2 Plane)) :
    StubGraph.IsMatching (unmarkedPorts X L G mk) (trackMate X) (TrackMated X L G mk) := by
  rintro ⟨F, e⟩ hq ⟨hleft, hmP⟩
  obtain ⟨hF, hsh, -⟩ := mem_unmarkedPorts.1 hq
  have hsh' := Finset.mem_filter.1 hsh
  have hFe := G.good_subset hF
  obtain ⟨hT, hne⟩ := trackEnds_eq_otherEnd hends hFe hsh'.1 hsh'.2.1

  set o := otherEnd X (F, e) with ho
  set F' := nodeFace o.1
  set e' := o.2
  have hoF : o = (Sum.inl F', e') := Prod.ext hleft rfl
  have hmate : trackMate X (F, e) = (F', e') := rfl
  rw [hmate] at hmP ⊢
  obtain ⟨hF', hsh2, -⟩ := mem_unmarkedPorts.1 hmP
  have hsh2' := Finset.mem_filter.1 hsh2

  have hoT : o ∈ trackEnds X (allTrackOf X e) := by rw [hT]; simp
  have he'T : e' ∈ allTrackOf X e := (Finset.mem_product.1 (Finset.mem_filter.1 hoT).1).2
  have htr : allTrackOf X e' = allTrackOf X e :=
    (eq_allTrackOf_of_mem (allTrackOf_mem_allTracks hsh'.1) he'T).symm
  obtain ⟨hT', hne'⟩ := trackEnds_eq_otherEnd hends (G.good_subset hF') hsh2'.1 hsh2'.2.1
  rw [htr, hT, hoF] at hT'
  have hdist : (Sum.inl F', e') ≠ ((Sum.inl F, e) : PortNode × Sym2 Plane) := hoF ▸ hne

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

def IsMarking (X : Finset Plane) (L : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane)) :
    Prop :=
  ∀ F ∈ G.good, mk F ⊆ shortPorts X L F ∧ (mk F).card = G.marks F

def DegreeWindow (X : Finset Plane) (L : ℝ) (G : GoodFaces X) : Prop :=
  ∀ F ∈ G.good, G.marks F + 2 ≤ shortDeg X L (Sum.inl F) ∧ shortDeg X L (Sum.inl F) ≤ G.marks F + 4

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

section TrackCapBounds

open scoped BigOperators

@[expose] public noncomputable section

open Classical

namespace Erdos99

open LocalCharge

variable {X : Finset Plane} {L : ℝ} {G : GoodFaces X} {mk : Set ℂ → Finset (Sym2 Plane)}

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

lemma otherEnd_mem_trackEnds (hends : ∀ T ∈ allTracks X, (trackEnds X T).card = 2)
    {q : Set ℂ × Sym2 Plane} (hq : q ∈ facePorts X) :
    otherEnd X q ∈ trackEnds X (allTrackOf X q.2) := by
  obtain ⟨F, e⟩ := q
  obtain ⟨hF, he, hp⟩ := hq
  rw [(trackEnds_eq_otherEnd hends hF he hp).1]
  exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

lemma otherEnd_track (hends : ∀ T ∈ allTracks X, (trackEnds X T).card = 2)
    {q : Set ℂ × Sym2 Plane} (hq : q ∈ facePorts X) :
    (otherEnd X q).1 ∈ portNodes X ∧ (otherEnd X q).2 ∈ unitEdges X ∧
      IsPort X (otherEnd X q).1 (otherEnd X q).2 ∧
      allTrackOf X (otherEnd X q).2 = allTrackOf X q.2 := by
  obtain ⟨h1, h2, h3⟩ := mem_trackEnds.1 (otherEnd_mem_trackEnds hends hq)
  have hT := allTrackOf_mem_allTracks hq.2.1
  exact ⟨h1, allTracks_subset_unitEdges hT h2, h3, (eq_allTrackOf_of_mem hT h2).symm⟩

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

def shortEnds (X : Finset Plane) (L : ℝ) (R : PortNode → Prop) : Finset (PortNode × Sym2 Plane) :=
  (((portNodes X).filter R) ×ˢ unitEdges X).filter
    (fun r => IsPort X r.1 r.2 ∧ (trackLength X (allTrackOf X r.2) : ℝ) < L)

lemma card_shortEnds (R : PortNode → Prop) :
    (shortEnds X L R).card = ∑ N ∈ (portNodes X).filter R, shortDeg X L N := by
  rw [shortEnds, Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun N _ => ?_
  rw [shortDeg, Finset.card_filter]

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

def stubsAt (X : Finset Plane) (L : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane))
    (V : Finset (Set ℂ)) : Finset (Set ℂ × Sym2 Plane) :=
  (unmarkedPorts X L G mk).filter (fun q => ¬ TrackMated X L G mk q ∧ q.1 ∈ V)

def stubsTo (X : Finset Plane) (L : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane))
    (V : Finset (Set ℂ)) (K : PortNode × Sym2 Plane → Prop) : Finset (Set ℂ × Sym2 Plane) :=
  (stubsAt X L G mk V).filter (fun q => K (otherEnd X q))

def UnitEnd (X : Finset Plane) (r : PortNode × Sym2 Plane) : Prop :=
  ∃ p, r.1 = Sum.inr p ∧ returnLength X p.1 p.2 ≤ 1

def OneShortEnd (X : Finset Plane) (L : ℝ) (r : PortNode × Sym2 Plane) : Prop :=
  ∃ p, r.1 = Sum.inr p ∧ returnLength X p.1 p.2 = 2 ∧ shortDeg X L (Sum.inr p) = 1

def TwoShortEnd (X : Finset Plane) (L : ℝ) (r : PortNode × Sym2 Plane) : Prop :=
  ∃ p, r.1 = Sum.inr p ∧ returnLength X p.1 p.2 = 2 ∧ shortDeg X L (Sum.inr p) ≠ 1

def LongReturnEnd (X : Finset Plane) (r : PortNode × Sym2 Plane) : Prop :=
  ∃ p, r.1 = Sum.inr p ∧ 3 ≤ returnLength X p.1 p.2

def OmittedEnd (G : GoodFaces X) (r : PortNode × Sym2 Plane) : Prop :=
  ∃ F, r.1 = Sum.inl F ∧ F ∉ G.good

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

theorem trackGraph_bIn (V : Finset (Set ℂ)) :
    (trackGraph X L G mk).bIn V = (stubsAt X L G mk V).card := by
  rw [trackGraph, StubGraph.bIn_ofHalfEdges]
  rfl

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

section DirectionPinning

open Polynomial

@[expose] public noncomputable section

namespace Erdos99

namespace DirectionPinning

variable {d : ℕ}

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

section PinnedCount

open Filter Polynomial

@[expose] public noncomputable section

open Classical

namespace Erdos99

open DirectionPinning

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

section QuadraticResponseH1

open Filter Topology Polynomial ComplexConjugate

@[expose] public section

namespace Erdos99

namespace QuadraticResponse

noncomputable def hhPoly (k l : ℝ) (Z W : ℂ) : ℂ[X] :=
  (C (k : ℂ) * X + C Z) * (C (k : ℂ) + C (conj Z) * X) *
      ((C (l : ℂ) * X + C W) * (C (l : ℂ) + C (conj W) * X)) *
      (((C (k : ℂ) * X + C Z) + (C (l : ℂ) * X + C W)) *
        ((C (k : ℂ) + C (conj Z) * X) + (C (l : ℂ) + C (conj W) * X))) +
    X * ((C (k : ℂ) * X + C Z) * (C (l : ℂ) + C (conj W) * X) -
      (C (k : ℂ) + C (conj Z) * X) * (C (l : ℂ) * X + C W)) ^ 2

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

theorem hhPoly_eval_eq_zero {ζ Z W w : ℂ} (k l : ℝ) (hζ : ‖ζ‖ = 1) (hw : ‖w‖ = 1)
    (ha : ‖w + ((k : ℂ) * ζ + Z)‖ = 1) (hb : ‖w - ((l : ℂ) * ζ + W)‖ = 1) :
    (hhPoly k l Z W).eval ζ = 0 := by
  rw [hhPoly_eval hζ, hh_identity_star k l hζ hw ha hb, mul_zero]

def hhCoeff0 (K L Z W : ℂ) : ℂ :=
  K * L ^ 2 * Z * W ^ 2 + K * L ^ 2 * Z ^ 2 * W + K ^ 2 * L * Z * W ^ 2 + K ^ 2 * L * Z ^ 2 * W

def hhCoeff1 (K L Z Zc W Wc : ℂ) : ℂ :=
  L ^ 2 * Z * Zc * W ^ 2 + L ^ 2 * Z ^ 2 + L ^ 2 * Z ^ 2 * Zc * W - 2 * K * L * Z * W + 2 * K * L
    * Z * W ^ 2 * Wc + 2 * K * L * Z * Zc * W ^ 2 + 2 * K * L * Z ^ 2 * W * Wc + 2 * K * L * Z ^ 2
    * Zc * W + 2 * K * L ^ 3 * Z * W + K * L ^ 3 * Z ^ 2 + K ^ 2 * W ^ 2 + K ^ 2 * Z * W ^ 2 * Wc
    + K ^ 2 * Z ^ 2 * W * Wc + K ^ 2 * L ^ 2 * W ^ 2 + 4 * K ^ 2 * L ^ 2 * Z * W + K ^ 2 * L ^ 2 *
    Z ^ 2 + K ^ 3 * L * W ^ 2 + 2 * K ^ 3 * L * Z * W

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

def hhCoeff5 (K L Z Zc W Wc : ℂ) : ℂ :=
  L ^ 2 * Zc ^ 2 + L ^ 2 * Z * Zc * Wc ^ 2 + L ^ 2 * Z * Zc ^ 2 * Wc - 2 * K * L * Zc * Wc + 2 * K
    * L * Zc * W * Wc ^ 2 + 2 * K * L * Zc ^ 2 * W * Wc + 2 * K * L * Z * Zc * Wc ^ 2 + 2 * K * L
    * Z * Zc ^ 2 * Wc + 2 * K * L ^ 3 * Zc * Wc + K * L ^ 3 * Zc ^ 2 + K ^ 2 * Wc ^ 2 + K ^ 2 * Zc
    * W * Wc ^ 2 + K ^ 2 * Zc ^ 2 * W * Wc + K ^ 2 * L ^ 2 * Wc ^ 2 + 4 * K ^ 2 * L ^ 2 * Zc * Wc
    + K ^ 2 * L ^ 2 * Zc ^ 2 + K ^ 3 * L * Wc ^ 2 + 2 * K ^ 3 * L * Zc * Wc

def hhCoeff6 (K L Zc Wc : ℂ) : ℂ :=
  K * L ^ 2 * Zc * Wc ^ 2 + K * L ^ 2 * Zc ^ 2 * Wc + K ^ 2 * L * Zc * Wc ^ 2 + K ^ 2 * L * Zc ^ 2
    * Wc

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

theorem hhPoly_coeff_six (k l : ℝ) (Z W : ℂ) :
    (hhPoly k l Z W).coeff 6 = (k : ℂ) * l * (k + l) * conj Z * conj W * (conj Z + conj W) := by
  rw [hhPoly_eq]
  simp only [coeff_add, coeff_C_mul, coeff_X_pow]
  norm_num [hhCoeff6]
  ring

theorem hhPoly_coeff_five_of_Z_eq_zero (k l : ℝ) (W : ℂ) :
    (hhPoly k l 0 W).coeff 5 = (k : ℂ) ^ 2 * (l * (k + l) + 1) * conj W ^ 2 := by
  rw [hhPoly_eq]
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, map_zero]
  norm_num [hhCoeff5]
  ring

theorem hhPoly_coeff_five_of_W_eq_zero (k l : ℝ) (Z : ℂ) :
    (hhPoly k l Z 0).coeff 5 = (l : ℂ) ^ 2 * (k * (k + l) + 1) * conj Z ^ 2 := by
  rw [hhPoly_eq]
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, map_zero]
  norm_num [hhCoeff5]
  ring

theorem hhPoly_zero_zero (k l : ℝ) :
    hhPoly k l 0 0 = C ((k : ℂ) ^ 2 * l ^ 2 * (k + l) ^ 2) * X ^ 3 := by
  simp only [hhPoly, map_zero, map_mul, map_pow, map_add]
  ring

theorem hhPoly_one_one_neg (Z : ℂ) :
    hhPoly 1 1 Z (-Z) = C (4 * (1 - Z * conj Z) ^ 2) * X ^ 3 := by
  simp only [hhPoly, map_neg, Complex.ofReal_one, map_one, map_mul, map_pow, map_sub,
    map_ofNat]
  ring

def oppQuad (k l r x : ℝ) : ℝ :=
  (k ^ 2 + r ^ 2) * (l ^ 2 + r ^ 2) - 4 * r ^ 2 + 2 * (k * (l ^ 2 + r ^ 2) - l * (k ^ 2 + r ^ 2)) * x +
    4 * (1 - k * l) * x ^ 2

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

theorem oppQuad_vanishes_iff {k l r : ℝ} (hk : k = 1 ∨ k = 2) (hl : l = 1 ∨ l = 2) (hr : 0 < r) :
    (∀ x ∈ Set.Icc (-r) r, oppQuad k l r x = 0) ↔ k = 1 ∧ l = 1 ∧ r = 1 := by
  constructor
  · intro h
    exact oppQuad_three_points hk hl hr (h 0 ⟨by linarith, hr.le⟩) (h r ⟨by linarith, le_rfl⟩)
      (h (-r) ⟨le_rfl, by linarith⟩)
  · rintro ⟨rfl, rfl, rfl⟩ x _
    unfold oppQuad; ring

lemma div_norm_mul_conj {Z : ℂ} (hZ : Z ≠ 0) : (Z / (‖Z‖ : ℂ)) * conj Z = ((‖Z‖ : ℝ) : ℂ) := by
  have hr : (‖Z‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 hZ).ne'
  rw [div_mul_eq_mul_div, ← norm_sq_eq_mul_conj]
  push_cast
  field_simp

lemma norm_unit_of_ne_zero {Z : ℂ} (hZ : Z ≠ 0) : ‖Z / (‖Z‖ : ℂ)‖ = 1 := by
  have hr : 0 < ‖Z‖ := norm_pos_iff.2 hZ
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le, div_self hr.ne']

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

theorem hhPoly_natDegree_le (k l : ℝ) (Z W : ℂ) : (hhPoly k l Z W).natDegree ≤ 6 := by
  rw [hhPoly_eq]
  compute_degree

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

lemma tendsto_inv_ofReal {ι : Type*} {F : Filter ι} {T : ι → ℝ} (hT : Tendsto T F atTop) :
    Tendsto (fun i => ((T i : ℝ) : ℂ)⁻¹) F (𝓝 0) := by
  have h := (tendsto_inv_atTop_zero.comp hT)
  have h2 := (Complex.continuous_ofReal.tendsto 0).comp h
  simpa [Function.comp_def] using h2

lemma J_coeff_div {T : ℝ} (hT : T ≠ 0) (l : ℝ) (v z : ℂ) :
    ((l : ℂ) * T + v + z) / T = l + v * ((T : ℂ))⁻¹ + z / T := by
  have : (T : ℂ) ≠ 0 := by exact_mod_cast hT
  field_simp

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

lemma root_ne_zero {k : ℝ} {d : ℂ} (hd : d ^ 2 - k * d + 1 = 0) : d ≠ 0 := by
  rintro rfl; simp at hd

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

section QuadraticResponseJ

open Filter Topology Polynomial ComplexConjugate

@[expose] public section

namespace Erdos99

namespace QuadraticResponse

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

theorem sum_ne_zero_of_proj_le {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (f : ι → ℂ) {τ : ℂ}
    (hτ : ‖τ‖ = 1) {θ : ℝ} (hθ : 0 < θ) (hf : ∀ i ∈ s, (f i * conj τ).re ≤ -θ) :
    ∑ i ∈ s, f i ≠ 0 := by
  intro h
  have := norm_sum_ge_of_proj_le s f hτ hf
  rw [h, norm_zero] at this
  have : (0 : ℝ) < θ * s.card := mul_pos hθ (by exact_mod_cast hs.card_pos)
  linarith

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

def hhExpr (a aS b bS : ℂ) : ℂ := a * aS * (b * bS) * ((a + b) * (aS + bS)) + (a * bS - aS * b) ^ 2

theorem jj_cubic_coeff_ne_zero {A₁ A₂ B₁ B₂ : ℂ} (h₁ : 0 < A₁.re) (h₂ : 0 < A₂.re)
    (hB : B₁ * B₂ * (B₁ + B₂) ≠ 0) : A₁ * A₂ * (A₁ + A₂) * (B₁ * B₂ * (B₁ + B₂)) ≠ 0 := by
  have hne : ∀ z : ℂ, 0 < z.re → z ≠ 0 := fun z hz h => by
    rw [h, Complex.zero_re] at hz; exact lt_irrefl _ hz
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (hne _ h₁) (hne _ h₂)) (hne _ ?_)) hB
  rw [Complex.add_re]; linarith

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

noncomputable def hLoopPoly (k : ℝ) (Z : ℂ) : ℂ[X] := C (k : ℂ) * X + C Z

theorem hLoopPoly_eval (k : ℝ) (Z ζ : ℂ) : (hLoopPoly k Z).eval ζ = (k : ℂ) * ζ + Z := by
  simp [hLoopPoly]

theorem hLoopPoly_ne_zero {k : ℝ} (hk : k ≠ 0) (Z : ℂ) : hLoopPoly k Z ≠ 0 := by
  intro h
  have := congrArg (fun p => p.coeff 1) h
  simp [hLoopPoly, coeff_C] at this
  exact hk this

noncomputable def jLoopPoly (l : ℝ) (v : ℂ) : ℂ[X] :=
  C ((l : ℂ) * conj v) * X ^ 2 + C ((l : ℂ) ^ 2 + v * conj v - 1) * X + C ((l : ℂ) * v)

theorem jLoopPoly_eval {ζ : ℂ} (hζ : ‖ζ‖ = 1) (l : ℝ) (v : ℂ) :
    (jLoopPoly l v).eval ζ = ζ * (((‖(l : ℂ) * ζ + v‖ ^ 2 - 1 : ℝ)) : ℂ) := by
  have hζ0 := ne_zero_of_norm_eq_one hζ
  push_cast
  rw [← Complex.ofReal_pow, norm_sq_eq_mul_conj]
  simp only [jLoopPoly, eval_add, eval_mul, eval_C, eval_X, eval_pow, map_add, map_mul,
    Complex.conj_ofReal, conj_eq_inv hζ]
  field_simp
  ring

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

section PinnedPolys

open Filter Polynomial ComplexConjugate

@[expose] public noncomputable section

open Classical

namespace Erdos99

open DirectionPinning QuadraticResponse

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

lemma capPoly_expand (k : ℝ) (v Z : ℂ) : capPoly k v Z =
    C (conj v * conj Z) * X ^ 4 + C ((k : ℂ) * conj Z + (k : ℂ) * conj v) * X ^ 3 +
      C ((k : ℂ) ^ 2 + v * conj v + Z * conj Z - 1) * X ^ 2 + C ((k : ℂ) * v + (k : ℂ) * Z) * X +
      C (Z * v) := by
  simp only [capPoly, map_add, map_mul, map_sub, map_pow, map_one]
  ring

lemma natDegree_capPoly_le (k : ℝ) (v Z : ℂ) : (capPoly k v Z).natDegree ≤ 4 := by
  rw [capPoly_expand]
  compute_degree

lemma one_le_norm_capCoeffs {k : ℝ} (hk : k = 1 ∨ k = 2) {v : ℂ} (hv : ‖v‖ = 1) (Z : ℂ) :
    1 ≤ ‖polyCoeffs 4 (capPoly k v Z)‖ := by
  refine le_trans ?_ (norm_coeff_le_norm_polyCoeffs 4 _ (by norm_num : 2 ≤ 4))
  rw [capPoly_coeff_two, mul_conj_eq_one hv, ← norm_sq_eq_mul_conj]
  have e : (k : ℂ) ^ 2 + 1 + ((‖Z‖ ^ 2 : ℝ) : ℂ) - 1 = ((k ^ 2 + ‖Z‖ ^ 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [e, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have : 1 ≤ k ^ 2 := by rcases hk with rfl | rfl <;> norm_num
  nlinarith [sq_nonneg ‖Z‖]

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

section ReturnBudgets

open scoped BigOperators
open EstablishedExternalResults Filter

@[expose] public noncomputable section

open Classical

namespace Erdos99

lemma trackLength_allTrackOf_le_srcLen {X : Finset Plane} (hX : IsSeparated X)
    (htri : ¬ HasUnitTriangle X) {e : Sym2 Plane} (he : e ∈ unitEdges X) :
    trackLength X (allTrackOf X e) ≤ srcLen X e := by
  by_cases hr : e ∈ rhombusEdges X
  · rw [allTrackOf_of_mem_rhombusEdges hr, srcLen]
  · rw [allTrackOf_of_not_mem he hr, trackLength_singleton hX htri he hr]
    exact Nat.zero_le _

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

lemma le_srcLen_of_not_short {X : Finset Plane} (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X)
    {L : ℝ} {N : PortNode} (h0 : shortDeg X L N = 0) {e : Sym2 Plane} (he : e ∈ unitEdges X)
    (hp : IsPort X N e) : L ≤ srcLen X e := by
  rw [shortDeg, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
  have h := h0 he
  rw [not_and, not_lt] at h
  exact (h hp).trans (by exact_mod_cast trackLength_allTrackOf_le_srcLen hX htri he)

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

lemma sym2_cases_of_three {P₁ P₂ Y a b : ℂ} (ha : a = P₁ ∨ a = P₂ ∨ a = Y)
    (hb : b = P₁ ∨ b = P₂ ∨ b = Y) (hab : a ≠ b) (hne : s(a, b) ≠ s(P₁, P₂)) :
    s(a, b) = s(P₁, Y) ∨ s(a, b) = s(Y, P₂) := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    simp_all [Sym2.eq_swap]

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

  have hsideU : s(P1, P2) ∉ cUnitEdges X := by
    intro h; rw [cUnitEdges, mem_unitPairs, hP1def, hP2def, dist_toC] at h; exact hd h.2.2

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

section FaceClosure

open scoped BigOperators Real
open EstablishedExternalResults Set Complex Filter Topology

@[expose] public noncomputable section

open Classical

namespace Erdos99

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

theorem card_orientedSides :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ∀ F ∈ exceptionalFaces X,
      (orientedSides X F).card = faceSize X F := by
  filter_upwards [exists_cyclic_orientedSides] with n h hfm X hX F hF
  obtain ⟨v, -, hinj, heq⟩ := h hfm X hX F hF
  rw [heq, Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj hij
  simp only [Prod.mk.injEq] at hij
  exact hinj (Set.mem_Iio.2 (Finset.mem_range.1 hi)) (Set.mem_Iio.2 (Finset.mem_range.1 hj)) hij.1

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

section ChargingResidual

open scoped BigOperators Real
open Filter

@[expose] public noncomputable section

open Classical

namespace Erdos99

open LocalCharge

def markedSum (X : Finset Plane) (F : Set ℂ) (S : Finset (Sym2 Plane)) : ℂ :=
  ∑ ab ∈ (orientedSides X F).filter (fun ab => ∃ e ∈ S, Sym2.map toC e = s(ab.1, ab.2)),
    (ab.2 - ab.1)

def GoodFaces.markMult {X : Finset Plane} (G : GoodFaces X) (F : Set ℂ) : ℂ :=
  if F ∈ G.hex then 2 else 1

def IsLabelled (X : Finset Plane) (tol : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane)) :
    Prop :=
  ∃ lab : Set ℂ → Plane × Plane, Set.InjOn lab G.good ∧ ∀ F ∈ G.good,
    lab F ∈ unitHullSides X ∧
    ‖markedSum X F (mk F) - G.markMult F * toC (sideDir (lab F))‖ ≤ tol ∧
    ∀ ab ∈ orientedSides X F, ‖ab.1 - toC (lab F).1‖ ≤ tol * diam X

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

lemma sameDir_of_mem_allTrackOf {X : Finset Plane} {e f : Sym2 Plane} (he : e ∈ unitEdges X)
    (hf : f ∈ allTrackOf X e) : SameDir e f := by
  by_cases hr : e ∈ rhombusEdges X
  · rw [allTrackOf_of_mem_rhombusEdges hr] at hf
    exact sameDir_of_mem_tracks (Finset.mem_image_of_mem _ hr) (mem_trackOf_self hr) hf
  · rw [allTrackOf_of_not_mem he hr, Finset.mem_singleton] at hf
    rw [hf]; exact SameDir.refl e

lemma sameDir_otherEnd {X : Finset Plane}
    (hends : ∀ T ∈ allTracks X, (trackEnds X T).card = 2) {F : Set ℂ} {e : Sym2 Plane}
    (hF : F ∈ exceptionalFinset X) (he : e ∈ unitEdges X) (hp : IsPort X (Sum.inl F) e) :
    SameDir e (otherEnd X (F, e)).2 := by
  obtain ⟨hT, -⟩ := trackEnds_eq_otherEnd hends hF he hp
  have hmem : otherEnd X (F, e) ∈ trackEnds X (allTrackOf X e) := by rw [hT]; simp
  exact sameDir_of_mem_allTrackOf he (Finset.mem_product.1 (Finset.mem_filter.1 hmem).1).2

def NoIntermediatePorts (X : Finset Plane) (L Λ : ℝ) (G : GoodFaces X) : Prop :=
  ∀ F ∈ G.good, ∀ e ∈ unitEdges X, IsPort X (Sum.inl F) e →
    (trackLength X (allTrackOf X e) : ℝ) < L ∨ Λ ≤ trackLength X (allTrackOf X e)

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

def flaggedFaces (X : Finset Plane) (O : Plane) (L lam θ δ : ℝ) (G : GoodFaces X) :
    Finset (Set ℂ) :=
  G.good.filter (fun F => ∃ T ∈ longTracks X L, IsFlaggedPort X O (diam X) lam θ δ F T)

lemma mem_flaggedFaces {X : Finset Plane} {O : Plane} {L lam θ δ : ℝ} {G : GoodFaces X}
    {F : Set ℂ} (hF : F ∈ flaggedFaces X O L lam θ δ G) :
    ∃ T ∈ longTracks X L, IsFlaggedPort X O (diam X) lam θ δ F T :=
  (Finset.mem_filter.1 hF).2

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

lemma defJ_antitone {V Fl Fl' : Finset α} (h : Fl ⊆ Fl') : g.defJ V Fl' ≤ g.defJ V Fl := by
  refine Finset.card_le_card fun v hv => ?_
  obtain ⟨hv, hnf, h2⟩ := Finset.mem_filter.1 hv
  refine Finset.mem_filter.2 ⟨hv, fun h' => hnf (h h'), h2.trans ?_⟩
  exact g.inc_mono v (Finset.sdiff_subset_sdiff (subset_refl _) h)

lemma excE_antitone {V Fl Fl' : Finset α} (h : Fl ⊆ Fl') : g.excE V Fl' ≤ g.excE V Fl := by
  refine Finset.card_le_card fun e he => ?_
  obtain ⟨he, h1, h2, h3, h4⟩ := Finset.mem_filter.1 he
  exact Finset.mem_filter.2 ⟨he, h1, h2, fun hq => h3 (g.qual_mono h hq),
    fun hq => h4 (g.qual_mono h hq)⟩

end LocalCharge.StubGraph

def GoodFaces.omittedSmall {X : Finset Plane} (G : GoodFaces X) : ℕ :=
  ((exceptionalFinset X).filter (fun F => faceSize X F ≤ 6 ∧ F ∉ G.good)).card

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
  ·
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

abbrev ChargeQuantity : Type :=
  (X : Finset Plane) → ℝ → (G : GoodFaces X) → (Set ℂ → Finset (Sym2 Plane)) → Finset (Set ℂ) → ℝ

def LocalExclusion (η : ℝ) (Q : ChargeQuantity) : Prop :=
  ∀ ε, 0 < ε → ∀ lam, 0 < lam → ∀ θ δ : ℝ, 0 < θ → 0 < δ →
    ∃ tol, 0 < tol ∧ ∃ a₀, 0 < a₀ ∧ ∀ a, 0 < a → a ≤ a₀ →
      ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
        ∀ O : Plane, (∀ x ∈ X, dist x O ≤ diam X / 2 + η * diam X) →
        ∀ (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane)), IsMarking X (a * diam X) G mk →
          DegreeWindow X (a * diam X) G → IsSaturated X (a * diam X) (lam * diam X) tol G mk →
          Q X (a * diam X) G mk (flaggedFaces X O (a * diam X) lam θ δ G) ≤ ε * diam X

def qHH : ChargeQuantity := fun X L G mk _ =>
  2 * ((trackGraph X L G mk).eIn ((trackGraph X L G mk).Hs G.good)
    ((trackGraph X L G mk).Hs G.good) : ℝ)

def qOneShort : ChargeQuantity := fun X L G mk _ =>
  ((stubsTo X L G mk ((trackGraph X L G mk).Hs G.good) (OneShortEnd X L)).card : ℝ)

def qCapless (M : ℕ) : ChargeQuantity := fun X L G mk _ =>
  ((trackGraph X L G mk).stublessSmall ((trackGraph X L G mk).Gs G.good) M +
    (trackGraph X L G mk).stublessSmall ((trackGraph X L G mk).Ks G.good) M : ℝ)

def qDefJ : ChargeQuantity := fun X L G mk Fl => 4 * ((trackGraph X L G mk).defJ G.good Fl : ℝ)

def qExcE : ChargeQuantity := fun X L G mk Fl => ((trackGraph X L G mk).excE G.good Fl : ℝ)

end Erdos99

end

end ChargingResidual

section HHAdjacencyAlgebra

open scoped BigOperators Real
open Filter Polynomial ComplexConjugate

@[expose] public noncomputable section

open Classical

namespace Erdos99

open LocalCharge QuadraticResponse DirectionPinning EstablishedExternalResults

def hhPorts (X : Finset Plane) (L : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane)) :
    Finset (Set ℂ × Sym2 Plane) :=
  (unmarkedPorts X L G mk).filter (fun q => TrackMated X L G mk q ∧
    q.1 ∈ (trackGraph X L G mk).Hs G.good ∧ (trackMate X q).1 ∈ (trackGraph X L G mk).Hs G.good)

def hhFaces (X : Finset Plane) (L : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane)) :
    Finset (Set ℂ) :=
  (hhPorts X L G mk).image Prod.fst

theorem qHH_le_four_mul {X : Finset Plane}
    (hends : ∀ T ∈ allTracks X, (trackEnds X T).card = 2) (L : ℝ) (G : GoodFaces X)
    (mk : Set ℂ → Finset (Sym2 Plane)) (Fl : Finset (Set ℂ)) :
    qHH X L G mk Fl ≤ 4 * ((hhFaces X L G mk).card : ℝ) := by
  set P := unmarkedPorts X L G mk with hP
  set g := trackGraph X L G mk with hg
  have hM := trackMate_isMatching hends L G mk

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

def hhExpr (a b : ℂ) : ℂ :=
  a * conj a * (b * conj b) * ((a + b) * (conj a + conj b)) + (a * conj b - conj a * b) ^ 2

lemma continuous_hhExpr : Continuous (fun p : ℂ × ℂ => hhExpr p.1 p.2) := by
  unfold hhExpr; fun_prop

lemma hhPoly_eval_eq_hhExpr {τ : ℂ} (hτ : ‖τ‖ = 1) (k l : ℝ) (Z W : ℂ) :
    (hhPoly k l Z W).eval τ = τ ^ 3 * hhExpr ((k : ℂ) * τ + Z) ((l : ℂ) * τ + W) := by
  rw [hhPoly_eval hτ, hhExpr, conj_response hτ, conj_response hτ]

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

def HHAdm (κ : ℝ) (d : ℝ × ℝ × ℂ × ℂ) : Prop :=
  (d.1 = 1 ∨ d.1 = 2) ∧ (d.2.1 = 1 ∨ d.2.1 = 2) ∧ ‖d.2.2.1‖ ≤ 6 ∧ ‖d.2.2.2‖ ≤ 6 ∧
    ¬ (d.1 = 1 ∧ d.2.1 = 1 ∧ ‖d.2.2.1 + d.2.2.2‖ < κ ∧ |‖d.2.2.1‖ - 1| < κ)

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

def GoodFaces.kMult {X : Finset Plane} (G : GoodFaces X) (F : Set ℂ) : ℝ :=
  if F ∈ G.hex then 2 else 1

lemma GoodFaces.kMult_cases {X : Finset Plane} (G : GoodFaces X) (F : Set ℂ) :
    G.kMult F = 1 ∨ G.kMult F = 2 := by
  unfold GoodFaces.kMult; split_ifs <;> simp

lemma GoodFaces.markMult_eq {X : Finset Plane} (G : GoodFaces X) (F : Set ℂ) :
    G.markMult F = (G.kMult F : ℂ) := by
  unfold GoodFaces.markMult GoodFaces.kMult; split_ifs <;> simp

def longSides (X : Finset Plane) (L : ℝ) (F : Set ℂ) : Finset (ℂ × ℂ) :=
  (orientedSides X F).filter (fun ab => ¬ ∃ e ∈ shortPorts X L F, Sym2.map toC e = s(ab.1, ab.2))

def longSum (X : Finset Plane) (L : ℝ) (F : Set ℂ) : ℂ :=
  ∑ ab ∈ longSides X L F, (ab.2 - ab.1)

def labDir (lab : Set ℂ → Plane × Plane) (F : Set ℂ) : ℂ := toC (sideDir (lab F))

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

section HopMargin

open scoped BigOperators Real

@[expose] public noncomputable section

open Classical

namespace Erdos99

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

  have hcs : c ^ 2 + s' ^ 2 = 1 := by
    have := inner_sq_add_inner_rot_sq τ u
    rw [hu, hτ] at this; rw [hcdef, hsdef]; linarith
  have hΔ : ‖Δ‖ ^ 2 = α ^ 2 + β ^ 2 := by
    have := inner_sq_add_inner_rot_sq u Δ
    rw [hu] at this; rw [hαdef, hβdef]; linarith
  have hframe : inner ℝ Δ (rot τ) = α * s' + β * c := by
    rw [inner_eq_frame u Δ (rot τ) hu, inner_rot_rot_eq, real_inner_comm u (rot τ),
      real_inner_comm u τ]

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

section HHAdjacencyGeometry

open scoped BigOperators Real
open Filter Polynomial ComplexConjugate

@[expose] public noncomputable section

open Classical

namespace Erdos99

open LocalCharge QuadraticResponse DirectionPinning EstablishedExternalResults

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

section HHAdjacency

open scoped BigOperators Real
open Filter Polynomial ComplexConjugate

@[expose] public noncomputable section

open Classical

namespace Erdos99

open LocalCharge QuadraticResponse DirectionPinning EstablishedExternalResults

def sumCentres (U : Finset ℂ) : Finset ℂ :=
  (Finset.univ : Finset (U → Fin 7)).image (fun m => ∑ u : U, ((m u : ℕ) : ℂ) * (u : ℂ))

lemma card_sumCentres_le (U : Finset ℂ) : (sumCentres U).card ≤ 7 ^ U.card := by
  refine Finset.card_image_le.trans ?_
  simp

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
    ·
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

section CapReflection

@[expose] public noncomputable section

open ComplexConjugate Classical

namespace Erdos99

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

section OneShortAlgebra

open scoped BigOperators Real
open Filter Polynomial ComplexConjugate

@[expose] public noncomputable section

open Classical

namespace Erdos99

open LocalCharge QuadraticResponse DirectionPinning EstablishedExternalResults

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

def CapAdm (d : ℝ × ℂ × ℂ) : Prop := (d.1 = 1 ∨ d.1 = 2) ∧ ‖d.2.1‖ = 1 ∧ ‖d.2.2‖ ≤ 6

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

section OneShortGeometry

open scoped BigOperators Real
open Filter Polynomial ComplexConjugate

@[expose] public noncomputable section

open Classical

namespace Erdos99

open LocalCharge QuadraticResponse DirectionPinning EstablishedExternalResults

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
      exact Sym2.map_mk toC z₁ z₂
    obtain ⟨hv1, hv6⟩ := side_pow_six he hmap
    have hr : 2 * ε' ≤ 1 / 2 := by have := min_le_right (εc / 4) (1 / 4); linarith
    obtain ⟨ζ, hζ, hclose⟩ := sixth_root_near hv1 (hrt1 c hc) hr
      (by rw [hv6, hrt6 c hc]; exact hcd)
    refine ⟨ζ * rt c, Finset.mem_image.2 ⟨(c, ζ), Finset.mem_product.2 ⟨hc, hζ⟩, rfl⟩, ?_⟩
    have := min_le_left (εc / 4) (1 / 4)
    simp only at hclose
    linarith

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

section SaturationHop

open scoped BigOperators Real
open Filter Topology

@[expose] public noncomputable section

open Classical

namespace Erdos99

section
variable {X : Finset Plane}

lemma hopEnd_eq_of_stuck {p : Plane × Plane} (hp : p ∈ X ×ˢ X) {k : ℕ}
    (h : ¬ ∃ q, LeftStep X ((stepL X)^[k] p) q) : hopEnd X p = (stepL X)^[k] p := by
  have h1 := iterate_stepL_stuck h (max k (X ×ˢ X).card) (le_max_left _ _)
  have h2 := iterate_stepL_stuck (k := (X ×ˢ X).card) (hopEnd_terminal hp)
    (max k (X ×ˢ X).card) (le_max_right _ _)
  rw [← h1]
  exact h2.symm

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

lemma mem_unitEdges_of_mem_orientedSides {F : Set ℂ} {a b : Plane}
    (h : (toC a, toC b) ∈ orientedSides X F) : s(b, a) ∈ unitEdges X := by
  have hm := mem_of_mem_orientedSides h
  rw [mem_unitEdges]
  exact ⟨hm.2, hm.1, by rw [dist_comm]; exact dist_eq_one_of_mem_orientedSides h⟩

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

lemma allTrackOf_hopEnd {p : Plane × Plane} (hp : p ∈ X ×ˢ X)
    (hu : s(p.1, p.2) ∈ unitEdges X) :
    allTrackOf X s((hopEnd X p).1, (hopEnd X p).2) = allTrackOf X s(p.1, p.2) :=
  (eq_allTrackOf_of_mem (allTrackOf_mem_allTracks hu) (hopEnd_mem_allTrackOf hp hu)).symm

end

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

section CaplessGeometry

open scoped BigOperators Real
open Filter

@[expose] public noncomputable section

open Classical

namespace Erdos99

open LocalCharge

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

lemma exists_side_of_port :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ∀ F : Set ℂ, ∀ e : Sym2 Plane,
      IsPort X (Sum.inl F) e → ∃ ab ∈ orientedSides X F, Sym2.map toC e = s(ab.1, ab.2) := by
  filter_upwards [image_orientedSides_eq] with n himg hfm X hX F e hp
  have hb := hp.2
  rw [← himg hfm X hX F hp.1] at hb
  obtain ⟨ab, hab, habe⟩ := Finset.mem_image.1 hb
  exact ⟨ab, hab, habe.symm⟩

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

section SaturationProcess

open scoped BigOperators Real
open Filter Topology

@[expose] public noncomputable section

open Classical

namespace Erdos99

namespace Sat

open Propagation

variable {X : Finset Plane} (hX : IsSeparated X) (K m : ℕ)

abbrev proc : TokenProcess X := hopProcess hX (hopEmit X)

def Clean (F : Set ℂ) : Prop := ∀ t ∈ (proc hX).arrivals m F, ¬ hopBad hX K t

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

def entry (X : Finset Plane) (x : Plane × Plane) : Sym2 Plane :=
  s((hopEnd X x).1, (hopEnd X x).2)

def mk (F : Set ℂ) : Finset (Sym2 Plane) :=
  ((proc hX).arrivals m F).image (fun t => entry X (exitEdge (hopEmit X) t)) ∪
    (if (proc hX).Emits m F then {s((hopEmit X F).1, (hopEmit X F).2)} else ∅)

def ret (F : Set ℂ) : (Plane × Plane) ⊕ Set ℂ :=
  if (proc hX).Emits m F then
    (if h : (((proc hX).arrivals m F).erase ((proc hX).parent F)).Nonempty then h.choose
      else (proc hX).parent F)
  else (if h : ((proc hX).arrivals m F).Nonempty then h.choose else Sum.inr F)

def lab (F : Set ℂ) : Plane × Plane := (proc hX).labelAt K (ret hX m F)

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

lemma parent_mem_arrivals {F : Set ℂ} (h : (proc hX).Emits m F) :
    (proc hX).parent F ∈ (proc hX).arrivals m F := by
  have hp := (proc hX).parent_mem h
  obtain ⟨-, hle, -⟩ := (proc hX).firstEmit_spec h
  exact (proc hX).arrivals_mono (by omega) F hp

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

theorem lab_injOn (hmK : m ≤ K) : Set.InjOn (lab hX K m) ((faces hX K m).good : Set (Set ℂ)) := by
  set P := proc hX

  have key : ∀ F ∈ (faces hX K m).good, ∀ F' : Set ℂ, ∀ t', t' ∈ P.arrivals m F' →
      P.Desc (ret hX m F) t' → ret hX m F = t' := by
    intro F hF F' t' ht' hd
    obtain ⟨hr, hne⟩ := ret_spec hX K m hF
    rcases Relation.ReflTransGen.cases_head hd with h | ⟨c, ⟨G, rfl, ⟨i, hG⟩, hpar⟩, hct'⟩
    · exact h
    · exfalso

      have hGF : G = F := P.face_eq_of_mem_arrivals (hpar ▸ P.parent_mem hG) hr
      subst hGF

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

variable {hX}

lemma dest_eq_hopDest (t : (Plane × Plane) ⊕ Set ℂ) :
    (proc hX).dest t = hopDest X (exitEdge (hopEmit X) t) := by
  rcases t with p | G <;> rfl

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
    ·
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
    ·
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
    ·
      by_cases hEm : (proc hsep).Emits m G
      · rw [if_pos hEm, Finset.mem_singleton] at hem
        have hm := hopEmit_mem' hsides G hG
        have hs : s((toC h.1, toC h.2).1, (toC h.1, toC h.2).2) =
            s(((toC (hopEmit X G).2, toC (hopEmit X G).1) : ℂ × ℂ).1,
              ((toC (hopEmit X G).2, toC (hopEmit X G).1) : ℂ × ℂ).2) := by
          have h3 : s(toC h.1, toC h.2) = s(toC (hopEmit X G).1, toC (hopEmit X G).2) := by
            have := congrArg (Sym2.map toC) hem
            simpa [Sym2.map_mk] using this
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

section SaturationCount

open scoped BigOperators Real
open Filter Topology

@[expose] public noncomputable section

open Classical

namespace Erdos99

namespace Sat

open Propagation

variable {X : Finset Plane} (hX : IsSeparated X) (K m : ℕ)

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

lemma card_arrivals_le (htri : ¬ HasUnitTriangle X)
    (hsides : ∀ G ∈ exceptionalFaces X, (orientedSides X G).Nonempty)
    (hcard : ∀ F ∈ exceptionalFaces X, (orientedSides X F).card = faceSize X F)
    {F : Set ℂ} (hF : F ∈ exceptionalFaces X) :
    ((proc hX).arrivals m F).card ≤ faceSize X F := by
  obtain ⟨hinj, hside⟩ := hopProcess_incidences hX htri (hopEmit X) (hopEmit_mem' hsides) m F
  rw [← hcard F hF]
  exact Finset.card_le_card_of_injOn _ (fun t ht => (hside t ht).1) hinj

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

  set Def := S.filter (fun F => faceSize X F ≤ 6 ∧ B F = 0 ∧
    ((faceSize X F = 5 ∧ a F = 0) ∨ (faceSize X F = 6 ∧ a F ≤ 1))) with hDef
  set Dirty := S.filter (fun F => B F ≠ 0) with hDirty
  set Front := S.filter (fun F => emitted (faceSize X F) (P.faceArr (m + 1) F) = 1 ∧
    emitted (faceSize X F) (P.faceArr m F) = 0) with hFront
  set Prim := S.filter (fun F => hopBad hX K (Sum.inr F)) with hPrim

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

  have hcons := P.conservation m
  rw [hopProcess_lostArr, Nat.cast_zero, add_zero] at hcons
  set S6 := S.filter (fun F => faceSize X F ≤ 6) with hS6
  set S7 := S.filter (fun F => ¬ faceSize X F ≤ 6) with hS7
  have hsplit := Finset.sum_filter_add_sum_filter_not S (fun F => faceSize X F ≤ 6)
    (fun F => netAbsorbed (faceSize X F) (P.faceArr (m + 1) F))

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

section SaturationLabels

open scoped BigOperators Real
open Filter Topology

@[expose] public noncomputable section

open Classical

namespace Erdos99

namespace Sat

open Propagation

variable {X : Finset Plane} {hX : IsSeparated X} {K m : ℕ}

lemma sideDir_eq_of_dist {x : Plane × Plane} (h : dist x.1 x.2 = 1) : sideDir x = x.2 - x.1 := by
  rw [sideDir, ← dist_eq_norm', h, inv_one, one_smul]

lemma toC_sub_eq_sideDir {x : Plane × Plane} (h : dist x.1 x.2 = 1) :
    toC x.2 - toC x.1 = toC (sideDir x) := by
  rw [sideDir_eq_of_dist h, map_sub]

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

def theta (X : Finset Plane) (K : ℕ) (δ : ℝ) : ℝ :=
  2 * (2 * disB (diam X) K + 6) / diam X + 4 * √(3 * δ)

include htri hsides hmK hTB hR hdist in

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

section Entries

variable (htri : ¬ HasUnitTriangle X)
  (hsides : ∀ G ∈ exceptionalFaces X, (orientedSides X G).Nonempty)

abbrev side (X : Finset Plane) (t : (Plane × Plane) ⊕ Set ℂ) : ℂ × ℂ :=
  (toC (hopEnd X (exitEdge (hopEmit X) t)).1, toC (hopEnd X (exitEdge (hopEmit X) t)).2)

include htri hsides in

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
    rw [entry, Sym2.map_mk]
  refine ⟨hs, ?_, hmap, ?_, ⟨hF, ?_⟩, ?_⟩
  · rw [← map_sub, hopEnd_sub, map_sub, toC_sub_eq_sideDir hd1]
  · have := mem_unitEdges_of_mem_orientedSides hs
    rw [entry, Sym2.eq_swap]; exact this
  · rw [hmap]; exact (Finset.mem_filter.1 hs).2.1
  · rw [entry, allTrackOf_hopEnd hxX hu]
    exact trackLength_allTrackOf_le_srcLen hX htri hu

include htri hsides in

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

section SaturationMarks

open scoped BigOperators Real
open Filter Topology

@[expose] public noncomputable section

open Classical

namespace Erdos99

namespace Sat

open Propagation

variable {X : Finset Plane} {hX : IsSeparated X} {K m : ℕ}

lemma srcLen_lt_of_good_inr (hD1 : 1 ≤ diam X) (hmK : m ≤ K) {G : Set ℂ}
    (hG : (proc hX).Emits m G) (hg : ¬ hopBad hX K (Sum.inr G)) :
    (srcLen X s((hopEmit X G).1, (hopEmit X G).2) : ℝ) < cutB (diam X) K := by
  have h := ((proc hX).good_inputs (hopSrcBad X) (hopPrimBad X) (n := K)
    ((proc hX).emits_mono hmK hG) hg).1
  unfold hopPrimBad at h
  push_neg at h
  obtain ⟨-, hle, -⟩ := (proc hX).firstEmit_spec hG
  exact h.trans_le (cutB_mono hD1 (by omega))

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
    rw [← m1, he, Sym2.map_mk]; exact Sym2.eq_swap
  have heq := orientedSides_injOn (nonempty_of_mem_exceptionalFaces hF') s1 hm hs
  rw [heq] at v1
  have hd1 : dist (hopEmit X F).1 (hopEmit X F).2 = 1 := by
    rw [dist_comm]; exact dist_eq_one_of_mem_orientedSides hm
  have hneg : sideDir (exitEdge (hopEmit X) t) = -sideDir (hopEmit X F) := by
    apply toC.injective
    rw [← v1, map_neg, ← toC_sub_eq_sideDir hd1]
    try simp only; ring
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
    rw [Sym2.map_mk]; exact Sym2.eq_swap
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
      try simp only; ring
    · simp

include htri hsides hmK hTB hR hdist in

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
        · rw [Sym2.map_mk, Sym2.eq_swap]; exact (Finset.mem_filter.1 hm).2.1
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

section SaturationMarked

open scoped BigOperators Real
open Filter Topology

@[expose] public noncomputable section

open Classical

namespace Erdos99

open Propagation

namespace Sat

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

theorem saturation_marked {ε a tol : ℝ} (hε : 0 < ε) (ha : 0 < a) (htol : 0 < tol) :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∃ (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane)),
        IsMarking X (a * diam X) G mk ∧ IsLabelled X tol G mk ∧
        (G.omittedSmall : ℝ) ≤ ε * diam X ∧
        stubsTo X (a * diam X) G mk G.good (UnitEnd X) = ∅ ∧
        stubsTo X (a * diam X) G mk G.good (MarkedEnd G mk) = ∅ := by

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

  have hTB : ∀ t, (Sat.proc hsep).Timed K t → ¬ hopBad hsep K t →
      (∀ p, t = Sum.inl p → p ∈ unitHullSides X) →
      (∀ G, t = Sum.inr G → G ∈ exceptionalFaces X) → TokBound hsep K K t :=
    fun t ht hg h1 h2 => tokenBound hsep htri hsides hR hD1 hstep h1920 (hopp hfm X hX)
      (hdist hfm X hX) K le_rfl t ht hg h1 h2

  obtain ⟨m, hmK, hfront⟩ := Sat.exists_frontier_le hsep hK0
  have hmK' : m ≤ K := hmK.le

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
  ·
    have hcap2 : ∀ F ∈ exceptionalFaces X, faceSize X F ≤ 6 →
        (((Sat.proc hsep).arrivals m F).filter (fun t => ¬ hopBad hsep K t)).card ≤ 2 :=
      fun F hF h6 => Sat.card_good_arrivals_le_two htri hsides hmK' hTB hR (hdist hfm X hX)
        (hcapF hfm X hX) hsmall hF h6
    have hΔ0 := hΔ hfm X hX htri
    have hcount := Sat.omitted_count hsep K m htri hsides (hcard hfm X hX) hcap2 hΔ0

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

    have hcapK := Sat.capArr_le hsep htri hsides hTB (hcap hfm X hX htri)
    have hcapm : ((Sat.proc hsep).capArr (m + 1) : ℝ) ≤ (Sat.proc hsep).capArr (K + 1) := by
      exact_mod_cast (Sat.proc hsep).capArr_mono' (by omega)

    have h2 : 2 ≤ X.card := by rw [hX.1.1]; exact hn2
    have hpf := pentagons_add_heptagons_le_pi_mul_diam hsep h2 hΔ0
    have hKpos : (0 : ℝ) < K := by exact_mod_cast hK0
    have hfr : Sat.frontier hsep m ≤ ε / 8 * diam X := by
      have h1 : Sat.frontier hsep m * K ≤ π * diam X := hfront.trans hpf
      have hK8 : 8 * π ≤ ε * K := by have := (div_lt_iff₀ hε).1 hKgt; linarith
      have h3 := mul_le_mul_of_nonneg_right hK8 hD.le
      have h2' : Sat.frontier hsep m * K ≤ ε / 8 * diam X * K := by linarith
      exact le_of_mul_le_mul_right h2' hKpos

    have hI := (hstab hfm X hX htri).2.2.2.2.2
    have hρ : (0 : ℝ) ≤ returnExcess X := Nat.cast_nonneg _
    have hηD : η * diam X = ε / 10 * diam X := by rw [hηdef]
    linarith

end Erdos99

end

end SaturationMarked

section SaturationWindow

open scoped BigOperators Real
open Filter Polynomial ComplexConjugate

@[expose] public noncomputable section

open Classical

namespace Erdos99

open LocalCharge QuadraticResponse DirectionPinning EstablishedExternalResults

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

def windowPolyA (k : ℝ) (z : ℂ) : ℂ[X] := C (k : ℂ) * X + C z

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

lemma inner_toC_symm (z τ : ℂ) : inner ℝ (toC.symm z) (toC.symm τ) = (z * conj τ).re := by
  rw [LinearIsometryEquiv.inner_map_map, Complex.inner]
  simp [Complex.mul_re]; ring

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
    ·
      refine ⟨windowPolyA k z, Finset.mem_union_left _ (Finset.mem_image.2
        ⟨(k, z), Finset.mem_product.2 ⟨hkK, hz⟩, rfl⟩), ?_⟩
      rw [← hτe, windowPolyA_eval]
      calc ‖(k : ℂ) * τ + z‖ ≤ ‖(k : ℂ) * τ + Z‖ + ‖((k : ℂ) * τ + z) - ((k : ℂ) * τ + Z)‖ :=
            norm_le_norm_add_norm_sub' _ _
        _ ≤ tol + 6 * εc := add_le_add h hshift
        _ < r := by linarith
    ·
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

      have hadm : k = 2 ∨ cm / 2 ≤ ‖z‖ := by
        rcases hk with hk1 | hk2
        · right
          have hZcm : cm ≤ ‖Z‖ := by
            have hnh : F ∉ G.hex := by
              intro hh; rw [hkdef, GoodFaces.kMult, if_pos hh] at hk1; norm_num at hk1
            have hFg' := hFg
            simp only [GoodFaces.good, Finset.mem_union] at hFg'
            rcases hFg' with (hp | hh) | hac
            ·
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
            ·
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

section Saturation

open scoped BigOperators Real
open Filter

@[expose] public noncomputable section

open Classical

namespace Erdos99

open LocalCharge

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
  ·
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

section OneShortCap

open scoped BigOperators Real
open Filter Polynomial ComplexConjugate

@[expose] public noncomputable section

open Classical

namespace Erdos99

open LocalCharge QuadraticResponse DirectionPinning EstablishedExternalResults

def nodeSide : PortNode → Plane × Plane := Sum.elim (fun _ => (0, 0)) id

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
      by try simp only; linarith⟩
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

section CaplessComponents

open scoped BigOperators Real
open Filter

@[expose] public noncomputable section

open Classical

namespace Erdos99

open LocalCharge

namespace LocalCharge.StubGraph

variable {α β : Type*} [Inhabited β] {P : Finset β} {v : β → α} {mate : β → β} {mated : β → Prop}

lemma ofHalfEdges_stub_of_not_mated {q : β} (hq : q ∈ P) (hm : ¬ mated q) :
    ∃ s ∈ (ofHalfEdges P v mate mated).S, (ofHalfEdges P v mate mated).stub s = v q := by
  refine ⟨hIdx P q, ?_, ?_⟩
  · simp only [ofHalfEdges, Finset.mem_filter, Finset.mem_range]
    exact ⟨hIdx_lt P hq, by rw [hEnum_hIdx P hq]; exact hm⟩
  · simp only [ofHalfEdges]; rw [hEnum_hIdx P hq]

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

lemma ofHalfEdges_edge_mated {e : ℕ} (he : e ∈ (ofHalfEdges P v mate mated).E) :
    ∃ q ∈ P, mated q ∧ (ofHalfEdges P v mate mated).src e = v q ∧
      (ofHalfEdges P v mate mated).tgt e = v (mate q) := by
  simp only [ofHalfEdges, Finset.mem_filter, Finset.mem_range] at he ⊢
  exact ⟨hEnum P e, hEnum_mem P he.1, he.2.1, rfl, rfl⟩

end LocalCharge.StubGraph

section components

variable {X : Finset Plane} {L : ℝ} {G : GoodFaces X} {mk : Set ℂ → Finset (Sym2 Plane)}

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

lemma card_halfEdges_le_four {X : Finset Plane} (hends : ∀ T ∈ allTracks X, (trackEnds X T).card = 2) {L : ℝ}
    {G : GoodFaces X} {mk : Set ℂ → Finset (Sym2 Plane)} (hmk : IsMarking X L G mk)
    (hwin : DegreeWindow X L G) (F : Set ℂ) :
    ((unmarkedPorts X L G mk).filter (fun q => q.1 = F)).card ≤ 4 := by
  by_cases hF : F ∈ G.good
  · have hdeg := trackGraph_deg hends L G mk hF
    rw [trackGraph, StubGraph.deg_ofHalfEdges (trackMate_isMatching hends L G mk)] at hdeg
    have hdeg' : ((unmarkedPorts X L G mk).filter (fun q => q.1 = F)).card =
        (shortPorts X L F \ mk F).card := by
      convert hdeg using 3
    rw [hdeg', Finset.card_sdiff_of_subset (hmk F hF).1, (hmk F hF).2, card_shortPorts]
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

section CaplessElim

open Polynomial

@[expose] public noncomputable section

namespace Erdos99

namespace CaplessElim

variable {B : Type*} [CommRing B]

def respA (k Z : B) : B[X] := C k * X + C Z

def respC (k Zc : B) : B[X] := C k + X * C Zc

def respQ (k Z Zc : B) : B[X][X] :=
  C (respC k Zc) * X ^ 2 - C (respA k Z * respC k Zc) * X + C (X * respA k Z)

def elimStep (q : B[X][X]) (n : ℕ) (P : B[X][X]) : B[X][X] :=
  resultant (q.map C) (taylor (X : B[X][X]) (P.map C)) 2 n

def elimP (k Z Zc : ℕ → B) : ℕ → B[X][X]
  | 0 => X
  | j + 1 => elimStep (respQ (k j) (Z j) (Zc j)) (2 ^ j) (elimP k Z Zc j)

def elimQ (k0 Z0 : B) (k Z Zc : ℕ → B) (m : ℕ) : B[X] :=
  (elimP k Z Zc m).eval (respA k0 Z0)

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

lemma hasseDeriv_map' {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S) (p : R[X]) (i : ℕ) :
    hasseDeriv i (p.map f) = (hasseDeriv i p).map f := by
  ext n; simp [hasseDeriv_coeff, coeff_map]

lemma coeff_taylor_map_C (P : B[X][X]) (i : ℕ) :
    (taylor (X : B[X][X]) (P.map C)).coeff i = hasseDeriv i P := by
  rw [taylor_coeff, hasseDeriv_map', eval_map, eval₂_C_X]

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

lemma eval_map_evalRingHom (P : ℂ[X][X]) (ζ x : ℂ) :
    (P.map (evalRingHom ζ)).eval x = (P.eval (C x)).eval ζ := by
  rw [eval_map, ← coe_evalRingHom, ← eval₂_at_apply (evalRingHom ζ) (C x)]
  simp

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

section CaplessPoly

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

theorem elimQ_ne_zero {k0 : ℝ} (hk0 : 0 < k0) (Z0 : ℂ) (k : ℕ → ℝ) (hk : ∀ i, k i = 1 ∨ k i = 2)
    (Z : ℕ → ℂ) (m : ℕ) :
    elimQ (k0 : ℂ) Z0 (fun i => (k i : ℂ)) Z (fun i => conj (Z i)) m ≠ 0 := by
  intro hQ

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

abbrev UnivRing : Type := MvPolynomial (Fin 2 ⊕ ℕ × Fin 3) ℂ

def univElimQ (m : ℕ) : UnivRing[X] :=
  elimQ (MvPolynomial.X (Sum.inl 0)) (MvPolynomial.X (Sum.inl 1))
    (fun i => MvPolynomial.X (Sum.inr (i, 0))) (fun i => MvPolynomial.X (Sum.inr (i, 1)))
    (fun i => MvPolynomial.X (Sum.inr (i, 2))) m

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

section CaplessPinning

open Filter Topology Metric

@[expose] public noncomputable section

namespace Erdos99

namespace CaplessElim

abbrev CapData (m : ℕ) : Type := ℝ × ℂ × (Fin m → ℝ) × (Fin m → ℂ)

def capAdm (m : ℕ) (R : ℝ) : Set (CapData m) :=
  Set.Icc 1 R ×ˢ closedBall 0 R ×ˢ Set.univ.pi (fun _ => ({1, 2} : Set ℝ)) ×ˢ
    Set.univ.pi (fun _ => closedBall (0 : ℂ) R)

lemma isCompact_capAdm (m : ℕ) (R : ℝ) : IsCompact (capAdm m R) :=
  isCompact_Icc.prod ((isCompact_closedBall _ _).prod
    ((isCompact_univ_pi fun _ => (Set.toFinite _).isCompact).prod
      (isCompact_univ_pi fun _ => isCompact_closedBall _ _)))

def capRes0 {m : ℕ} (d : CapData m) (ζ : ℂ) (p : Fin m → ℂ) : ℝ :=
  ‖(d.1 : ℂ) * ζ + d.2.1 + ∑ i, p i‖

def capRes1 {m : ℕ} (d : CapData m) (ζ : ℂ) (p u : Fin m → ℂ) (i : Fin m) : ℝ :=
  ‖(d.2.2.1 i : ℂ) * ζ + d.2.2.2 i - p i + u i‖

def CapApprox (m : ℕ) (r : ℝ) (d : CapData m) (ζ : ℂ) : Prop :=
  ∃ p u : Fin m → ℂ, (∀ i, ‖p i‖ = 1 ∧ ‖u i‖ = 1) ∧ capRes0 d ζ p < r ∧ ∀ i, capRes1 d ζ p u i < r

lemma exact_solutions_card_le (m : ℕ) (R : ℝ) {d : CapData m} (hd : d ∈ capAdm m R) :
    ∃ S : Finset ℂ, S.card ≤ capDeg m ∧ ∀ ζ : ℂ, ‖ζ‖ = 1 → ∀ p u : Fin m → ℂ,
      (∀ i, ‖p i‖ = 1 ∧ ‖u i‖ = 1) → capRes0 d ζ p = 0 → (∀ i, capRes1 d ζ p u i = 0) → ζ ∈ S := by
  obtain ⟨⟨hk1, -⟩, -, hk, -⟩ := hd
  set k : ℕ → ℝ := fun i => if h : i < m then d.2.2.1 ⟨i, h⟩ else 1
  set Z : ℕ → ℂ := fun i => if h : i < m then d.2.2.2 ⟨i, h⟩ else 0
  have hk' : ∀ i, k i = 1 ∨ k i = 2 := by
    intro i
    simp only [k]
    split_ifs with h
    · exact hk ⟨i, h⟩ (Set.mem_univ _)
    · exact Or.inl rfl
  obtain ⟨S, hS, hsol⟩ := capless_solutions_card_le (by linarith : (0 : ℝ) < d.1) d.2.1 k hk' Z m
  refine ⟨S, hS, fun ζ hζ p u hpu h0 h1 => ?_⟩
  set p' : ℕ → ℂ := fun i => if h : i < m then p ⟨i, h⟩ else 0
  set u' : ℕ → ℂ := fun i => if h : i < m then u ⟨i, h⟩ else 0
  refine hsol ζ hζ p' u' (fun i hi => ?_) ?_
  · simp only [p', u', k, Z, dif_pos hi]
    refine ⟨(hpu _).1, (hpu _).2, ?_⟩
    exact norm_eq_zero.1 (h1 ⟨i, hi⟩)
  · have : ∑ i ∈ Finset.range m, p' i = ∑ i, p i := by
      rw [Finset.sum_range (fun i => p' i)]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [p', i.2]
    rw [this]
    exact norm_eq_zero.1 h0

abbrev CapState (m : ℕ) : Type := CapData m × ℂ × (Fin m → ℂ) × (Fin m → ℂ)

def capStates (m : ℕ) (R : ℝ) : Set (CapState m) :=
  capAdm m R ×ˢ sphere 0 1 ×ˢ Set.univ.pi (fun _ => sphere (0 : ℂ) 1) ×ˢ
    Set.univ.pi (fun _ => sphere (0 : ℂ) 1)

lemma isCompact_capStates (m : ℕ) (R : ℝ) : IsCompact (capStates m R) :=
  (isCompact_capAdm m R).prod ((isCompact_sphere _ _).prod
    ((isCompact_univ_pi fun _ => isCompact_sphere _ _).prod
      (isCompact_univ_pi fun _ => isCompact_sphere _ _)))

lemma continuous_capRes0 (m : ℕ) :
    Continuous (fun s : CapState m => capRes0 s.1 s.2.1 s.2.2.1) := by
  unfold capRes0
  fun_prop

lemma continuous_capRes1 (m : ℕ) (i : Fin m) :
    Continuous (fun s : CapState m => capRes1 s.1 s.2.1 s.2.2.1 s.2.2.2 i) := by
  unfold capRes1
  fun_prop

theorem capless_pinning (m : ℕ) (R : ℝ) {w : ℝ} (hw : 0 < w) :
    ∃ r > 0, ∃ μ > 0, ∀ (c : CapData m) (A : Finset ℂ),
      (∀ ζ ∈ A, ‖ζ‖ = 1 ∧ ∃ d ∈ capAdm m R, ‖d - c‖ < μ ∧ CapApprox m r d ζ) →
      (A : Set ℂ).Pairwise (fun a b => w ≤ ‖a - b‖) → A.card ≤ capDeg m := by
  set N := capDeg m
  by_contra hcon
  push_neg at hcon
  have hseq : ∀ n : ℕ, ∃ s : Fin (N + 1) → CapState m, (∀ j, s j ∈ capStates m R) ∧
      (∀ j j', ‖(s j).1 - (s j').1‖ < 2 / (n + 1)) ∧
      (∀ j j', j ≠ j' → w ≤ ‖(s j).2.1 - (s j').2.1‖) ∧
      (∀ j, capRes0 (s j).1 (s j).2.1 (s j).2.2.1 < 1 / (n + 1)) ∧
      (∀ j i, capRes1 (s j).1 (s j).2.1 (s j).2.2.1 (s j).2.2.2 i < 1 / (n + 1)) := by
    intro n
    obtain ⟨c, A, hA, hsep, hcard⟩ := hcon (1 / (n + 1)) (by positivity) (1 / (n + 1)) (by positivity)
    obtain ⟨A', hA'A, hA'card⟩ := Finset.exists_subset_card_eq (Nat.succ_le_of_lt hcard)
    set e := A'.equivFin
    have hmem : ∀ j : Fin (N + 1), ((e.symm (Fin.cast hA'card.symm j)) : ℂ) ∈ A :=
      fun j => hA'A (e.symm _).2
    choose hζ1 d hdK hdc p u hpu h0 h1 using fun j => hA _ (hmem j)
    refine ⟨fun j => (d j, (e.symm (Fin.cast hA'card.symm j) : ℂ), p j, u j), fun j => ?_,
      fun j j' => ?_, fun j j' hjj' => ?_, fun j => h0 j, fun j i => h1 j i⟩
    · refine ⟨hdK j, ?_, fun i _ => ?_, fun i _ => ?_⟩
      · simpa using hζ1 j
      · simpa using (hpu j i).1
      · simpa using (hpu j i).2
    · calc ‖d j - d j'‖ = ‖(d j - c) - (d j' - c)‖ := by congr 1; abel
        _ ≤ ‖d j - c‖ + ‖d j' - c‖ := norm_sub_le _ _
        _ < 1 / (n + 1) + 1 / (n + 1) := add_lt_add (hdc j) (hdc j')
        _ = 2 / (n + 1) := by ring
    · refine hsep (Finset.mem_coe.2 (hmem j)) (Finset.mem_coe.2 (hmem j')) ?_
      intro heq
      apply hjj'
      have := Subtype.ext heq
      have := e.symm.injective this
      exact Fin.cast_injective _ this
  choose s hsK hsd hsw hs0 hs1 using hseq
  have hK : IsCompact (Set.univ.pi fun _ : Fin (N + 1) => capStates m R) :=
    isCompact_univ_pi fun _ => isCompact_capStates m R
  obtain ⟨a, ha, φ, hφ, hlim⟩ := hK.tendsto_subseq (x := s) (fun n j _ => hsK n j)
  have hlimj : ∀ j, Tendsto (fun n => s (φ n) j) atTop (𝓝 (a j)) :=
    fun j => (continuous_apply j).continuousAt.tendsto.comp hlim
  have hinv : Tendsto (fun n : ℕ => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact h1.comp hφ.tendsto_atTop

  have hdata : ∀ j, (a j).1 = (a 0).1 := by
    intro j
    have ht : Tendsto (fun n => (s (φ n) j).1 - (s (φ n) 0).1) atTop (𝓝 ((a j).1 - (a 0).1)) :=
      ((continuous_fst.tendsto _).comp (hlimj j)).sub ((continuous_fst.tendsto _).comp (hlimj 0))
    have ht0 : Tendsto (fun n => (s (φ n) j).1 - (s (φ n) 0).1) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero (fun _ => norm_nonneg _) (fun n => (hsd (φ n) j 0).le) ?_
      simpa [div_eq_mul_inv] using hinv.const_mul 2
    exact sub_eq_zero.1 (tendsto_nhds_unique ht ht0)
  have hres0 : ∀ j, capRes0 (a j).1 (a j).2.1 (a j).2.2.1 = 0 := by
    intro j
    have ht := ((continuous_capRes0 m).tendsto _).comp (hlimj j)
    refine le_antisymm (le_of_tendsto_of_tendsto' ht hinv fun n => (hs0 (φ n) j).le) ?_
    exact norm_nonneg _
  have hres1 : ∀ j i, capRes1 (a j).1 (a j).2.1 (a j).2.2.1 (a j).2.2.2 i = 0 := by
    intro j i
    have ht := ((continuous_capRes1 m i).tendsto _).comp (hlimj j)
    refine le_antisymm (le_of_tendsto_of_tendsto' ht hinv fun n => (hs1 (φ n) j i).le) ?_
    exact norm_nonneg _
  have hsep : ∀ j j', j ≠ j' → w ≤ ‖(a j).2.1 - (a j').2.1‖ := by
    intro j j' hjj'
    have ht : Tendsto (fun n => ‖(s (φ n) j).2.1 - (s (φ n) j').2.1‖) atTop
        (𝓝 ‖(a j).2.1 - (a j').2.1‖) :=
      (((continuous_fst.comp continuous_snd).tendsto _).comp (hlimj j)).sub
        (((continuous_fst.comp continuous_snd).tendsto _).comp (hlimj j')) |>.norm
    exact ge_of_tendsto' ht fun n => hsw (φ n) j j' hjj'

  obtain ⟨S, hS, hsol⟩ := exact_solutions_card_le m R (ha 0 (Set.mem_univ _)).1
  have hmemS : ∀ j, (a j).2.1 ∈ S := by
    intro j
    have hj := ha j (Set.mem_univ _)
    obtain ⟨-, hζ, hp, hu⟩ := hj
    refine hsol _ (by simpa using hζ) (a j).2.2.1 (a j).2.2.2
      (fun i => ⟨by simpa using hp i (Set.mem_univ _), by simpa using hu i (Set.mem_univ _)⟩) ?_ ?_
    · rw [← hdata j]; exact hres0 j
    · intro i; rw [← hdata j]; exact hres1 j i
  have hinj : Function.Injective (fun j => (a j).2.1) := by
    intro j j' h
    by_contra hne
    have := hsep j j' hne
    try simp only at h
    rw [h, sub_self, norm_zero] at this
    linarith
  have := Finset.card_le_card_of_injOn (s := Finset.univ) (fun j => (a j).2.1)
    (fun j _ => hmemS j) hinj.injOn
  simp only [Finset.card_univ, Fintype.card_fin] at this
  omega

end CaplessElim

end Erdos99
end

end CaplessPinning

section CaplessCount

open Filter

@[expose] public noncomputable section

open Classical

namespace Erdos99

namespace CaplessElim

lemma exists_maximal_separated (T : Finset ℂ) {w : ℝ} (hw : 0 < w) :
    ∃ S ⊆ T, (S : Set ℂ).Pairwise (fun a b => w ≤ ‖a - b‖) ∧ ∀ t ∈ T, ∃ s ∈ S, ‖t - s‖ < w := by
  set F : Finset (Finset ℂ) :=
    T.powerset.filter (fun S : Finset ℂ => (↑S : Set ℂ).Pairwise (fun a b => w ≤ ‖a - b‖))
  have hF : F.Nonempty := ⟨∅, Finset.mem_filter.2 ⟨Finset.empty_mem_powerset _, by simp⟩⟩
  obtain ⟨S, hS, hmax⟩ := F.exists_max_image Finset.card hF
  obtain ⟨hST, hsep⟩ := Finset.mem_filter.1 hS
  refine ⟨S, Finset.mem_powerset.1 hST, hsep, fun t ht => ?_⟩
  by_contra hcon
  push_neg at hcon
  have htS : t ∉ S := fun h => by have := hcon t h; simp at this; linarith
  have hins : insert t S ∈ F := by
    refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.insert_subset ht
      (Finset.mem_powerset.1 hST)), ?_⟩
    rw [Finset.coe_insert]
    refine hsep.insert fun b hb _ => ⟨hcon b hb, ?_⟩
    rw [norm_sub_rev]; exact hcon b hb
  have := hmax _ hins
  rw [Finset.card_insert_of_notMem htS] at this
  omega

theorem capless_directions_few (m : ℕ) (R : ℝ) (Nc : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∃ μ > 0, ∀ᶠ n in atTop, ∀ X, IsOptimal n X →
      ∀ Cs : Finset (CapData m), Cs.card ≤ Nc →
      ∀ A ⊆ ccwHullSides X, (∀ p ∈ A, ∃ d ∈ capAdm m R, (∃ c ∈ Cs, ‖d - c‖ < μ) ∧
        CapApprox m r d (toC (sideDir p))) →
      (A.card : ℝ) ≤ ε * diam X := by
  obtain ⟨C, hC, hcount⟩ := card_sides_near_finset
  set K : ℝ := Nc * capDeg m with hK
  have hK0 : 0 ≤ K := by positivity
  set w : ℝ := min 1 (ε / (2 * (C * K + 1))) with hw
  have hw0 : 0 < w := lt_min one_pos (by positivity)
  have hw1 : w ≤ 1 := min_le_left _ _
  obtain ⟨r, hr, μ, hμ, hpin⟩ := capless_pinning m R hw0
  refine ⟨r, hr, μ, hμ, ?_⟩
  have hsmall : ∀ᶠ n in atTop, minDiam n ^ (-(1 / 9 : ℝ)) ≤ w :=
    ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 9)).comp tendsto_minDiam).eventually
      (Iic_mem_nhds hw0)
  filter_upwards [hcount, hsmall] with n hn hsm X hX Cs hCs A hA hpA
  rw [← hX.diam_eq] at hsm

  set T : CapData m → Finset ℂ := fun c => (A.filter (fun p => ∃ d ∈ capAdm m R, ‖d - c‖ < μ ∧
    CapApprox m r d (toC (sideDir p)))).image (fun p => toC (sideDir p))
  have hunit : ∀ p ∈ A, ‖toC (sideDir p)‖ = 1 := by
    intro p hp
    have hne : p.1 ≠ p.2 := (Finset.mem_filter.1 (hA hp)).2.2.2.1
    rw [LinearIsometryEquiv.norm_map]; exact norm_sideDir hne
  choose! Sc hScT hScsep hScdense using fun c => exists_maximal_separated (T c) hw0
  have hSccard : ∀ c, (Sc c).card ≤ capDeg m := by
    intro c
    refine hpin c (Sc c) (fun ζ hζ => ?_) (hScsep c)
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 (hScT c hζ)
    obtain ⟨hpA', d, hd, hdc, hap⟩ := Finset.mem_filter.1 hp
    exact ⟨hunit p hpA', d, hd, hdc, hap⟩
  set S : Finset ℂ := Cs.biUnion Sc with hS
  have hScard : (S.card : ℝ) ≤ K := by
    have : S.card ≤ Nc * capDeg m := by
      refine Finset.card_biUnion_le.trans ?_
      calc ∑ c ∈ Cs, (Sc c).card ≤ ∑ _c ∈ Cs, capDeg m := Finset.sum_le_sum fun c _ => hSccard c
        _ = Cs.card * capDeg m := by simp
        _ ≤ Nc * capDeg m := Nat.mul_le_mul_right _ hCs
    rw [hK]; exact_mod_cast this
  have hsub : A ⊆ (ccwHullSides X).filter (fun p => ∃ s ∈ S, ‖toC (sideDir p) - s‖ ≤ w) := by
    intro p hp
    refine Finset.mem_filter.2 ⟨hA hp, ?_⟩
    obtain ⟨d, hd, ⟨c, hc, hdc⟩, hap⟩ := hpA p hp
    have hT : toC (sideDir p) ∈ T c :=
      Finset.mem_image.2 ⟨p, Finset.mem_filter.2 ⟨hp, d, hd, hdc, hap⟩, rfl⟩
    obtain ⟨s, hs, hps⟩ := hScdense c _ hT
    exact ⟨s, Finset.mem_biUnion.2 ⟨c, hc, hs⟩, hps.le⟩
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

end CaplessElim

end Erdos99
end

end CaplessCount

section CaplessG

open scoped BigOperators Real
open Filter

@[expose] public noncomputable section

open Classical

namespace Erdos99

open LocalCharge CaplessElim

def compData {X : Finset Plane} (L : ℝ) (G : GoodFaces X) (Cf : Finset (Set ℂ))
    {Ext : Finset (Set ℂ × Sym2 Plane)} {m : ℕ} (e : Ext ≃ Fin m) : CapData m :=
  (∑ F ∈ Cf, G.kMult F, ∑ F ∈ Cf, longSum X L F,
    fun i => G.kMult (trackMate X (e.symm i)).1, fun i => longSum X L (trackMate X (e.symm i)).1)

theorem component_data :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ (L tol ρ : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane))
        (lab : Set ℂ → Plane × Plane), IsMarking X L G mk → LabelledBy X tol G mk lab →
      ∀ (Cf : Finset (Set ℂ)) (F0 : Set ℂ), Cf ⊆ G.good →
      (∀ q ∈ unmarkedPorts X L G mk, q.1 ∈ Cf → TrackMated X L G mk q) →
      (∀ q ∈ unmarkedPorts X L G mk, q.1 ∈ Cf → (trackMate X q).1 ∉ Cf →
        (trackMate X q).1 ∈ (trackGraph X L G mk).Hs G.good) →
      (∀ F ∈ Cf, ‖labDir lab F - labDir lab F0‖ ≤ ρ) →
      (∀ q ∈ unmarkedPorts X L G mk, q.1 ∈ Cf →
        ‖labDir lab (trackMate X q).1 - labDir lab F0‖ ≤ ρ) →
      ∀ {m : ℕ} (e : ((unmarkedPorts X L G mk).filter
          (fun q => q.1 ∈ Cf ∧ (trackMate X q).1 ∉ Cf)) ≃ Fin m),
      ∃ p u : Fin m → ℂ, (∀ i, ‖p i‖ = 1 ∧ ‖u i‖ = 1) ∧
        capRes0 (compData L G Cf e) (labDir lab F0) p ≤ Cf.card * tol + 2 * Cf.card * ρ ∧
        ∀ i, capRes1 (compData L G Cf e) (labDir lab F0) p u i ≤ tol + 2 * ρ := by
  filter_upwards [set_closure, ext_H_equation, exists_side_of_port, face_side_facts] with n hclo
    hext hside hfacts hfm X hX htri L tol ρ G mk lab hmk hlab Cf F0 hCf hmat hH hloc hloc' m e
  have hExtP : ∀ q ∈ (unmarkedPorts X L G mk).filter (fun q => q.1 ∈ Cf ∧ (trackMate X q).1 ∉ Cf),
      q ∈ unmarkedPorts X L G mk ∧ q.1 ∈ Cf ∧ (trackMate X q).1 ∉ Cf := fun q hq => by
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hq; exact ⟨h1, h2⟩
  have hu : ∀ i : Fin m, ∃ u : ℂ, ‖u‖ = 1 ∧ ‖(G.kMult (trackMate X (e.symm i)).1 : ℂ) *
      labDir lab (trackMate X (e.symm i)).1 - portVec X (e.symm i) + u +
        longSum X L (trackMate X (e.symm i)).1‖ ≤ tol := by
    intro i
    obtain ⟨hq, hq1, hq2⟩ := hExtP _ (e.symm i).2
    exact hext hfm X hX htri L tol G mk lab hmk hlab _ hq (hmat _ hq hq1) (hH _ hq hq1 hq2)
  choose u hu1 hu2 using hu
  have hk2 : ∀ F, ‖(G.kMult F : ℂ)‖ ≤ 2 := fun F => by
    rcases G.kMult_cases F with h | h <;> rw [h] <;> norm_num
  refine ⟨fun i => portVec X (e.symm i), u, fun i => ⟨?_, hu1 i⟩, ?_, fun i => ?_⟩
  · obtain ⟨hq, -, -⟩ := hExtP _ (e.symm i).2
    obtain ⟨hFg, hsp, -⟩ := mem_unmarkedPorts.1 hq
    obtain ⟨-, hpF, -⟩ := Finset.mem_filter.1 hsp
    obtain ⟨ab, hab, habe⟩ := hside hfm X hX _ _ hpF
    show ‖portVec X (e.symm i)‖ = 1
    rw [portVec_eq (nonempty_of_mem_exceptionalFaces hpF.1) hab habe]
    exact (hfacts hfm X hX G _ hFg).2 ab hab
  · have hsum : ∑ i, portVec X (e.symm i) = ∑ q ∈ (unmarkedPorts X L G mk).filter
        (fun q => q.1 ∈ Cf ∧ (trackMate X q).1 ∉ Cf), portVec X q := by
      rw [← Finset.sum_coe_sort _ (portVec X)]
      exact Equiv.sum_comp e.symm (fun q => portVec X q)
    have hc := hclo hfm X hX htri L tol G mk lab hmk hlab Cf hCf hmat
    unfold capRes0 compData
    simp only
    rw [hsum]
    have e1 : ((∑ F ∈ Cf, G.kMult F : ℝ) : ℂ) * labDir lab F0 + ∑ F ∈ Cf, longSum X L F +
        ∑ q ∈ (unmarkedPorts X L G mk).filter (fun q => q.1 ∈ Cf ∧ (trackMate X q).1 ∉ Cf),
          portVec X q =
        (∑ F ∈ Cf, ((G.kMult F : ℂ) * labDir lab F + longSum X L F) +
          ∑ q ∈ (unmarkedPorts X L G mk).filter (fun q => q.1 ∈ Cf ∧ (trackMate X q).1 ∉ Cf),
            portVec X q) +
          ∑ F ∈ Cf, (G.kMult F : ℂ) * (labDir lab F0 - labDir lab F) := by
      push_cast
      rw [Finset.sum_mul, Finset.sum_add_distrib]
      simp only [mul_sub, Finset.sum_sub_distrib]
      ring
    rw [e1]
    refine (norm_add_le _ _).trans ?_
    have h2 : ‖∑ F ∈ Cf, (G.kMult F : ℂ) * (labDir lab F0 - labDir lab F)‖ ≤ 2 * Cf.card * ρ := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ F ∈ Cf, ‖(G.kMult F : ℂ) * (labDir lab F0 - labDir lab F)‖ ≤ ∑ _F ∈ Cf, 2 * ρ := by
            refine Finset.sum_le_sum fun F hF => ?_
            rw [norm_mul, norm_sub_rev]
            exact mul_le_mul (hk2 F) (hloc F hF) (norm_nonneg _) (by norm_num)
        _ = 2 * Cf.card * ρ := by rw [Finset.sum_const, nsmul_eq_mul]; ring
    linarith
  · obtain ⟨hq, hq1, -⟩ := hExtP _ (e.symm i).2
    unfold capRes1 compData
    simp only
    have e1 : (G.kMult (trackMate X (e.symm i)).1 : ℂ) * labDir lab F0 +
        longSum X L (trackMate X (e.symm i)).1 - portVec X (e.symm i) + u i =
        ((G.kMult (trackMate X (e.symm i)).1 : ℂ) * labDir lab (trackMate X (e.symm i)).1 -
          portVec X (e.symm i) + u i + longSum X L (trackMate X (e.symm i)).1) +
        (G.kMult (trackMate X (e.symm i)).1 : ℂ) *
          (labDir lab F0 - labDir lab (trackMate X (e.symm i)).1) := by ring
    rw [e1]
    refine (norm_add_le _ _).trans ?_
    have h2 : ‖(G.kMult (trackMate X (e.symm i)).1 : ℂ) *
        (labDir lab F0 - labDir lab (trackMate X (e.symm i)).1)‖ ≤ 2 * ρ := by
      rw [norm_mul, norm_sub_rev]
      exact mul_le_mul (hk2 _) (hloc' _ hq hq1) (norm_nonneg _) (by norm_num)
    linarith [hu2 i]

def sumCentresK (U : Finset ℂ) (K : ℕ) : Finset ℂ :=
  (Finset.univ : Finset (U → Fin (K + 1))).image (fun f => ∑ u : U, ((f u : ℕ) : ℂ) * (u : ℂ))

lemma card_sumCentresK_le (U : Finset ℂ) (K : ℕ) : (sumCentresK U K).card ≤ (K + 1) ^ U.card := by
  refine Finset.card_image_le.trans ?_
  simp

lemma sum_near_sumCentresK {ι : Type*} (S : Finset ι) (v : ι → ℂ) (U : Finset ℂ) {K : ℕ} {ε : ℝ}
    (hε : 0 ≤ ε) (hS : S.card ≤ K) (h : ∀ i ∈ S, ∃ u ∈ U, ‖v i - u‖ ≤ ε) :
    ∃ z ∈ sumCentresK U K, ‖∑ i ∈ S, v i - z‖ ≤ K * ε := by
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
      _ ≤ K * ε := mul_le_mul_of_nonneg_right (by exact_mod_cast hS) hε

def capCentres (U : Finset ℂ) (M m : ℕ) : Finset (CapData m) :=
  ((Finset.range (2 * M + 1)).image (fun j : ℕ => (j : ℝ))) ×ˢ sumCentresK U (6 * M) ×ˢ
    Fintype.piFinset (fun _ : Fin m => ({1, 2} : Finset ℝ)) ×ˢ
    Fintype.piFinset (fun _ : Fin m => sumCentresK U 6)

def capNcent (Nc M m : ℕ) : ℕ := (2 * M + 1) * (6 * M + 1) ^ Nc * (2 ^ m * (7 ^ Nc) ^ m)

lemma card_capCentres_le {U : Finset ℂ} {Nc : ℕ} (hU : U.card ≤ Nc) (M m : ℕ) :
    (capCentres U M m).card ≤ capNcent Nc M m := by
  unfold capCentres capNcent
  rw [Finset.card_product, Finset.card_product, Finset.card_product, Fintype.card_piFinset,
    Fintype.card_piFinset, Finset.prod_const, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  have h1 : ((Finset.range (2 * M + 1)).image (fun j : ℕ => (j : ℝ))).card ≤ 2 * M + 1 :=
    Finset.card_image_le.trans (by simp)
  have h2 : (sumCentresK U (6 * M)).card ≤ (6 * M + 1) ^ Nc :=
    (card_sumCentresK_le U _).trans (Nat.pow_le_pow_right (by omega) hU)
  have h3 : (({1, 2} : Finset ℝ)).card ≤ 2 := Finset.card_le_two
  have h4 : (sumCentresK U 6).card ≤ 7 ^ Nc :=
    (card_sumCentresK_le U _).trans (Nat.pow_le_pow_right (by omega) hU)
  calc _ ≤ (2 * M + 1) * ((6 * M + 1) ^ Nc * (2 ^ m * (7 ^ Nc) ^ m)) := by
        gcongr
    _ = _ := by ring

lemma capData_norm_lt {m : ℕ} {d c : CapData m} {μ : ℝ} (hμ : 0 < μ) (h1 : d.1 = c.1)
    (h2 : ‖d.2.1 - c.2.1‖ < μ) (h3 : d.2.2.1 = c.2.2.1) (h4 : ∀ i, ‖d.2.2.2 i - c.2.2.2 i‖ < μ) :
    ‖d - c‖ < μ := by
  obtain ⟨d1, d2, d3, d4⟩ := d
  obtain ⟨c1, c2, c3, c4⟩ := c
  simp only at h1 h2 h3 h4
  subst h1 h3
  simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, sub_self, norm_zero]
  refine max_lt hμ (max_lt h2 (max_lt hμ ((pi_norm_lt_iff hμ).2 fun i => ?_)))
  simpa using h4 i

end Erdos99
end

end CaplessG

section CaplessGMain

open scoped BigOperators Real
open Filter

@[expose] public noncomputable section

open Classical

namespace Erdos99

open LocalCharge CaplessElim

def extPorts (X : Finset Plane) (L : ℝ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane))
    (Cf : Finset (Set ℂ)) : Finset (Set ℂ × Sym2 Plane) :=
  (unmarkedPorts X L G mk).filter (fun q => q.1 ∈ Cf ∧ (trackMate X q).1 ∉ Cf)

theorem component_witness :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ (L Λ tol ρ cρ εc μ0 r0 : ℝ) (M : ℕ) (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane))
        (lab : Set ℂ → Plane × Plane) (Ucl : Finset ℂ) (Bad : Finset (Set ℂ)),
      IsMarking X L G mk → NoIntermediatePorts X L Λ G → LabelledBy X tol G mk lab →
      (∀ F ∈ exceptionalFaces X, F ∉ Bad → ∀ ab ∈ orientedSides X F,
        (∃ e ∈ unitEdges X, Sym2.map toC e = s(ab.1, ab.2) ∧ Λ ≤ trackLength X (allTrackOf X e)) →
        ∃ u ∈ Ucl, ‖(ab.2 - ab.1) - u‖ ≤ εc) →
      (∀ p ∈ ccwHullSides X, ∀ q ∈ ccwHullSides X, dist p.1 q.1 ≤ cρ * diam X →
        ‖toC (sideDir p) - toC (sideDir q)‖ ≤ ρ) →
      (M + 1) * (2 * tol * diam X + 1 + L) ≤ cρ * diam X →
      M * tol + 2 * M * ρ < r0 → tol + 2 * ρ < r0 → 6 * M * εc < μ0 → 0 < μ0 → 0 ≤ εc →
      0 ≤ tol → 0 ≤ L →
      ∀ (Cf : Finset (Set ℂ)) (F0 : Set ℂ), F0 ∈ Cf → Cf ⊆ G.good → Cf.card ≤ M →
      (∀ F ∈ Cf, F ∉ Bad) →
      (∀ q ∈ unmarkedPorts X L G mk, q.1 ∈ Cf → (trackMate X q).1 ∉ Bad) →
      (∀ q ∈ unmarkedPorts X L G mk, q.1 ∈ Cf → TrackMated X L G mk q) →
      (∀ q ∈ unmarkedPorts X L G mk, q.1 ∈ Cf → (trackMate X q).1 ∉ Cf →
        (trackMate X q).1 ∈ (trackGraph X L G mk).Hs G.good) →
      (∀ F ∈ Cf, dist (lab F0).1 (lab F).1 ≤ M * (2 * tol * diam X + 1 + L)) →
      ∃ d ∈ capAdm (extPorts X L G mk Cf).card (6 * M + 6),
        (∃ c ∈ capCentres Ucl M (extPorts X L G mk Cf).card, ‖d - c‖ < μ0) ∧
        CapApprox (extPorts X L G mk Cf).card r0 d (labDir lab F0) := by
  filter_upwards [component_data, face_side_facts, mated_label_dist] with n hdata hfacts hmld hfm X
    hX htri L Λ tol ρ cρ εc μ0 r0 M G mk lab Ucl Bad hmk hnoint hlab hcl hclose hpar hr1 hr2 hμ1
    hμ0 hεc htol hL Cf F0 hF0 hCf hCM hnB hnB' hmat hH hdist
  set D := diam X with hDdef
  have hD0 : 0 ≤ D := Metric.diam_nonneg
  set δ0 := 2 * tol * D + 1 + L with hδ0
  have hδ0nn : 0 ≤ δ0 := by positivity
  have hM1 : 1 ≤ M := le_trans (Finset.card_pos.2 ⟨F0, hF0⟩) hCM
  have hM1' : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hccw : ∀ F ∈ G.good, lab F ∈ ccwHullSides X := fun F hF =>
    (Finset.mem_filter.1 (hlab.2 F hF).1).1
  have hpar' : (M : ℝ) * δ0 + δ0 ≤ cρ * D := by
    have : ((M : ℝ) + 1) * δ0 = M * δ0 + δ0 := by ring
    linarith
  have hloc : ∀ F ∈ Cf, ‖labDir lab F - labDir lab F0‖ ≤ ρ := by
    intro F hF
    refine hclose _ (hccw F (hCf hF)) _ (hccw F0 (hCf hF0)) ?_
    rw [dist_comm]; linarith [hdist F hF]
  have hρ0 : 0 ≤ ρ := by have := hloc F0 hF0; rw [sub_self, norm_zero] at this; exact this
  have hloc' : ∀ q ∈ unmarkedPorts X L G mk, q.1 ∈ Cf →
      ‖labDir lab (trackMate X q).1 - labDir lab F0‖ ≤ ρ := by
    intro q hq hqC
    have hm := hmat q hq hqC
    obtain ⟨hg', -, -⟩ := mem_unmarkedPorts.1 hm.2
    refine hclose _ (hccw _ hg') _ (hccw F0 (hCf hF0)) ?_
    have h1 := hmld hfm X hX htri L tol G mk lab hlab q hq hm
    have h2 := hdist q.1 hqC
    calc dist (lab (trackMate X q).1).1 (lab F0).1 ≤
        dist (lab (trackMate X q).1).1 (lab q.1).1 + dist (lab q.1).1 (lab F0).1 :=
          dist_triangle _ _ _
      _ ≤ δ0 + M * δ0 := by
        rw [← hDdef, ← hδ0, dist_comm] at h1; rw [dist_comm] at h2; linarith
      _ ≤ cρ * D := by linarith
  set e := (extPorts X L G mk Cf).equivFin
  obtain ⟨p, u, hpu, h0, h1⟩ := hdata hfm X hX htri L tol ρ G mk lab hmk hlab Cf F0 hCf hmat hH
    hloc hloc' e
  have hexF : ∀ F ∈ G.good, F ∈ exceptionalFaces X := fun F hF =>
    (mem_exceptionalFinset hX.1.2).1 (G.good_subset hF)
  have hcard6 : ∀ F ∈ G.good, (longSides X L F).card ≤ 6 := fun F hF =>
    (Finset.card_le_card (Finset.filter_subset _ _)).trans (hfacts hfm X hX G F hF).1
  have hZ6 : ∀ F ∈ G.good, ‖longSum X L F‖ ≤ 6 := fun F hF =>
    norm_longSum_le (hfacts hfm X hX G F hF).1 (hfacts hfm X hX G F hF).2
  have hlongcl : ∀ F ∈ G.good, F ∉ Bad → ∀ ab ∈ longSides X L F,
      ∃ u ∈ Ucl, ‖(ab.2 - ab.1) - u‖ ≤ εc := by
    intro F hF hFB ab hab
    obtain ⟨e', he', hmap, hport', hlong⟩ := longSide_edge (hexF F hF) hab
    refine hcl F (hexF F hF) hFB ab (Finset.mem_filter.1 hab).1 ⟨e', he', hmap, ?_⟩
    rcases hnoint F hF e' he' hport' with h | h
    · exact absurd h hlong
    · exact h
  have hk2 : ∀ F, G.kMult F ≤ 2 := fun F => by rcases G.kMult_cases F with h | h <;> norm_num [h]
  have hk1 : ∀ F, 1 ≤ G.kMult F := fun F => by rcases G.kMult_cases F with h | h <;> norm_num [h]
  have hext : ∀ i, (trackMate X (e.symm i)).1 ∈ G.good ∧ (trackMate X (e.symm i)).1 ∉ Bad := by
    intro i
    obtain ⟨hq, hq1, -⟩ := Finset.mem_filter.1 (e.symm i).2
    exact ⟨(mem_unmarkedPorts.1 (hmat _ hq hq1).2).1, hnB' _ hq hq1⟩

  obtain ⟨z0, hz0, hz0d⟩ := sum_near_sumCentresK (Cf.sigma (fun F => longSides X L F))
    (fun x => x.2.2 - x.2.1) Ucl (K := 6 * M) hεc (by
      rw [Finset.card_sigma]
      calc ∑ F ∈ Cf, (longSides X L F).card ≤ ∑ _F ∈ Cf, 6 :=
            Finset.sum_le_sum fun F hF => hcard6 F (hCf hF)
        _ = 6 * Cf.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ 6 * M := by omega)
    (fun x hx => hlongcl x.1 (hCf (Finset.mem_sigma.1 hx).1) (hnB _ (Finset.mem_sigma.1 hx).1) x.2
      (Finset.mem_sigma.1 hx).2)
  have hZ0 : ∑ x ∈ Cf.sigma (fun F => longSides X L F), (x.2.2 - x.2.1) =
      ∑ F ∈ Cf, longSum X L F := by
    rw [Finset.sum_sigma]; rfl
  rw [hZ0] at hz0d

  have hzi : ∀ i, ∃ z ∈ sumCentresK Ucl 6,
      ‖longSum X L (trackMate X (e.symm i)).1 - z‖ ≤ 6 * εc := by
    intro i
    obtain ⟨hg', hB'⟩ := hext i
    have := sum_near_sumCentresK (longSides X L (trackMate X (e.symm i)).1)
      (fun ab => ab.2 - ab.1) Ucl (K := 6) hεc (hcard6 _ hg') (hlongcl _ hg' hB')
    simpa [longSum] using this
  choose z hz hzd using hzi
  set j : ℕ := ∑ F ∈ Cf, (if F ∈ G.hex then 2 else 1 : ℕ) with hj
  have hjk : (j : ℝ) = ∑ F ∈ Cf, G.kMult F := by
    rw [hj, Nat.cast_sum]
    refine Finset.sum_congr rfl fun F _ => ?_
    unfold GoodFaces.kMult; split_ifs <;> simp
  have hjM : j ≤ 2 * M := by
    have : j ≤ ∑ _F ∈ Cf, 2 := Finset.sum_le_sum fun F _ => by split_ifs <;> omega
    rw [Finset.sum_const, smul_eq_mul] at this
    omega
  refine ⟨compData L G Cf e, ?_, ⟨((j : ℝ), z0, fun i => G.kMult (trackMate X (e.symm i)).1, z),
    ?_, ?_⟩, ⟨p, u, hpu, ?_, fun i => ?_⟩⟩
  · refine ⟨⟨?_, ?_⟩, ?_, fun i _ => ?_, fun i _ => ?_⟩
    · show 1 ≤ ∑ F ∈ Cf, G.kMult F
      exact (hk1 F0).trans (Finset.single_le_sum (fun F _ => by linarith [hk1 F]) hF0)
    · show ∑ F ∈ Cf, G.kMult F ≤ 6 * M + 6
      rw [← hjk]
      have : (j : ℝ) ≤ 2 * M := by exact_mod_cast hjM
      linarith
    · show ∑ F ∈ Cf, longSum X L F ∈ Metric.closedBall 0 (6 * M + 6)
      rw [mem_closedBall_zero_iff]
      calc ‖∑ F ∈ Cf, longSum X L F‖ ≤ ∑ F ∈ Cf, ‖longSum X L F‖ := norm_sum_le _ _
        _ ≤ ∑ _F ∈ Cf, (6 : ℝ) := Finset.sum_le_sum fun F hF => hZ6 F (hCf hF)
        _ = 6 * Cf.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
        _ ≤ 6 * M + 6 := by
          have : (Cf.card : ℝ) ≤ M := by exact_mod_cast hCM
          linarith
    · show G.kMult (trackMate X (e.symm i)).1 ∈ ({1, 2} : Set ℝ)
      rcases G.kMult_cases (trackMate X (e.symm i)).1 with h | h <;> simp [h]
    · show longSum X L (trackMate X (e.symm i)).1 ∈ Metric.closedBall 0 (6 * M + 6)
      rw [mem_closedBall_zero_iff]
      linarith [hZ6 _ (hext i).1]
  · refine Finset.mem_product.2 ⟨Finset.mem_image.2 ⟨j, Finset.mem_range.2 (by omega), rfl⟩,
      Finset.mem_product.2 ⟨hz0, Finset.mem_product.2 ⟨Fintype.mem_piFinset.2 fun i => ?_,
        Fintype.mem_piFinset.2 fun i => hz i⟩⟩⟩
    rcases G.kMult_cases (trackMate X (e.symm i)).1 with h | h <;> simp [h]
  · refine capData_norm_lt hμ0 hjk.symm ?_ rfl fun i => ?_
    · show ‖∑ F ∈ Cf, longSum X L F - z0‖ < μ0
      have : ((6 * M : ℕ) : ℝ) * εc = 6 * M * εc := by push_cast; ring
      linarith
    · show ‖longSum X L (trackMate X (e.symm i)).1 - z i‖ < μ0
      have := hzd i
      nlinarith
  · have hc : (Cf.card : ℝ) ≤ M := by exact_mod_cast hCM
    have : (Cf.card : ℝ) * tol + 2 * Cf.card * ρ ≤ M * tol + 2 * M * ρ := by
      have := mul_le_mul_of_nonneg_right hc htol
      have := mul_le_mul_of_nonneg_right hc hρ0
      nlinarith
    exact h0.trans_lt (this.trans_lt hr1)
  · exact (h1 i).trans_lt hr2

end Erdos99
end

end CaplessGMain

section CaplessGFew

open scoped BigOperators Real
open Filter

@[expose] public noncomputable section

open Classical

namespace Erdos99

open LocalCharge CaplessElim

variable {X : Finset Plane} {L : ℝ} {G : GoodFaces X} {mk : Set ℂ → Finset (Sym2 Plane)}

lemma card_ports_in_le (hends : ∀ T ∈ allTracks X, (trackEnds X T).card = 2)
    (hmk : IsMarking X L G mk) (hwin : DegreeWindow X L G) (B : Finset (Set ℂ)) :
    ((unmarkedPorts X L G mk).filter (fun q => q.1 ∈ B)).card ≤ 4 * B.card := by
  refine Finset.card_le_mul_card_image_of_maps_to (f := Prod.fst)
    (fun q hq => (Finset.mem_filter.1 hq).2) 4 fun b _ => ?_
  refine le_trans (Finset.card_le_card ?_) (card_halfEdges_le_four hends hmk hwin b)
  intro q hq
  obtain ⟨hq1, hq2⟩ := Finset.mem_filter.1 hq
  exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hq1).1, hq2⟩

lemma card_extPorts_le (hends : ∀ T ∈ allTracks X, (trackEnds X T).card = 2)
    (hmk : IsMarking X L G mk) (hwin : DegreeWindow X L G) (Cf : Finset (Set ℂ)) :
    (extPorts X L G mk Cf).card ≤ 4 * Cf.card := by
  refine le_trans (Finset.card_le_card ?_) (card_ports_in_le hends hmk hwin Cf)
  intro q hq
  obtain ⟨hq1, hq2, -⟩ := Finset.mem_filter.1 hq
  exact Finset.mem_filter.2 ⟨hq1, hq2⟩

lemma card_excComp_le (hends : ∀ T ∈ allTracks X, (trackEnds X T).card = 2)
    (hmk : IsMarking X L G mk) (hwin : DegreeWindow X L G) (U Bad : Finset (Set ℂ))
    (T : Finset (StubGraph.cgraph (trackGraph X L G mk) U).ConnectedComponent) :
    (T.filter (fun C => (∃ F ∈ U, (StubGraph.cgraph (trackGraph X L G mk) U).connectedComponentMk F
        = C ∧ F ∈ Bad) ∨ ∃ q ∈ unmarkedPorts X L G mk, q.1 ∈ U ∧
        (StubGraph.cgraph (trackGraph X L G mk) U).connectedComponentMk q.1 = C ∧
        TrackMated X L G mk q ∧ (trackMate X q).1 ∈ Bad)).card ≤ 5 * Bad.card := by
  have hM := trackMate_isMatching hends L G mk
  set Q := (unmarkedPorts X L G mk).filter (fun q => TrackMated X L G mk q ∧ (trackMate X q).1 ∈ Bad)
    with hQ
  have hQc : Q.card ≤ 4 * Bad.card := by
    refine le_trans ?_ (card_ports_in_le hends hmk hwin Bad)
    refine Finset.card_le_card_of_injOn (trackMate X) ?_ ?_
    · intro q hq
      obtain ⟨hqP, hm, hB⟩ := Finset.mem_filter.1 hq
      exact Finset.mem_filter.2 ⟨(hM q hqP hm).1, hB⟩
    · intro q hq q' hq' h
      obtain ⟨hqP, hm, -⟩ := Finset.mem_filter.1 hq
      obtain ⟨hqP', hm', -⟩ := Finset.mem_filter.1 hq'
      rw [← (hM q hqP hm).2.2.1, ← (hM q' hqP' hm').2.2.1]
      exact congrArg (trackMate X) h
  calc _ ≤ ((Bad.image (StubGraph.cgraph (trackGraph X L G mk) U).connectedComponentMk) ∪
        (Q.image (fun q => (StubGraph.cgraph (trackGraph X L G mk) U).connectedComponentMk q.1))).card := by
        refine Finset.card_le_card fun C hC => ?_
        rcases (Finset.mem_filter.1 hC).2 with ⟨F, -, rfl, hFB⟩ | ⟨q, hq, -, rfl, hm, hB⟩
        · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hFB)
        · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨q, Finset.mem_filter.2 ⟨hq, hm, hB⟩,
            rfl⟩)
    _ ≤ Bad.card + Q.card := (Finset.card_union_le _ _).trans
        (add_le_add Finset.card_image_le Finset.card_image_le)
    _ ≤ 5 * Bad.card := by omega

lemma stubless_component_facts (hends : ∀ T ∈ allTracks X, (trackEnds X T).card = 2)
    {U : Finset (Set ℂ)} (hU : U ⊆ G.good)
    (hUH : ∀ F ∈ G.good, F ∉ U → F ∈ (trackGraph X L G mk).Hs G.good)
    (lab : Set ℂ → Plane × Plane) {δ : ℝ} (hδ : 0 ≤ δ)
    (hmd : ∀ q ∈ unmarkedPorts X L G mk, TrackMated X L G mk q →
      dist (lab q.1).1 (lab (trackMate X q).1).1 ≤ δ)
    {M : ℕ} {C : (StubGraph.cgraph (trackGraph X L G mk) U).ConnectedComponent}
    (hstub : ∀ s ∈ (trackGraph X L G mk).S, (trackGraph X L G mk).stub s ∈ U →
      (StubGraph.cgraph (trackGraph X L G mk) U).connectedComponentMk
        ((trackGraph X L G mk).stub s) ≠ C)
    (hsmall : (U.filter (fun x =>
      (StubGraph.cgraph (trackGraph X L G mk) U).connectedComponentMk x = C)).card ≤ M)
    {F0 : Set ℂ} (hF0 : F0 ∈ U)
    (hF0C : (StubGraph.cgraph (trackGraph X L G mk) U).connectedComponentMk F0 = C)
    (Cf : Finset (Set ℂ))
    (hCfdef : Cf = U.filter (fun x =>
      (StubGraph.cgraph (trackGraph X L G mk) U).connectedComponentMk x = C)) :
    F0 ∈ Cf ∧ Cf ⊆ G.good ∧ Cf.card ≤ M ∧
      (∀ q ∈ unmarkedPorts X L G mk, q.1 ∈ Cf → TrackMated X L G mk q) ∧
      (∀ q ∈ unmarkedPorts X L G mk, q.1 ∈ Cf → (trackMate X q).1 ∉ Cf →
        (trackMate X q).1 ∈ (trackGraph X L G mk).Hs G.good) ∧
      (∀ F ∈ Cf, dist (lab F0).1 (lab F).1 ≤ M * δ) := by
  subst hCfdef
  have hmat : ∀ q ∈ unmarkedPorts X L G mk, q.1 ∈ U.filter (fun x =>
      (StubGraph.cgraph (trackGraph X L G mk) U).connectedComponentMk x = C) →
      TrackMated X L G mk q := fun q hq hqC =>
    mated_of_stubless hstub hq (Finset.mem_filter.1 hqC).1 (Finset.mem_filter.1 hqC).2
  refine ⟨Finset.mem_filter.2 ⟨hF0, hF0C⟩, fun F hF => hU (Finset.mem_filter.1 hF).1, hsmall,
    hmat, fun q hq hqC hnot => ?_, fun F hF => ?_⟩
  · have hm := hmat q hq hqC
    have hg : (trackMate X q).1 ∈ G.good := (mem_unmarkedPorts.1 hm.2).1
    refine hUH _ hg fun hU' => hnot (Finset.mem_filter.2 ⟨hU', ?_⟩)
    rw [← mate_same_component hends hq hm (Finset.mem_filter.1 hqC).1 hU']
    exact (Finset.mem_filter.1 hqC).2
  · refine component_label_dist lab hδ ?_ hF0 ((hF0C.trans (Finset.mem_filter.1 hF).2.symm)) ?_
    · intro x y hxy
      obtain ⟨-, -, q, hq, hm, he⟩ := cgraph_adj_cases hxy
      rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hmd q hq hm
      · rw [dist_comm]; exact hmd q hq hm
    · rw [hF0C]; exact hsmall

lemma card_le_of_fibres {ι : Type*} (T : Finset ι) (f : ι → ℕ) (K : ℕ) (hf : ∀ C ∈ T, f C ≤ K)
    {B : ℝ} (h : ∀ m ≤ K, ((T.filter (fun C => f C = m)).card : ℝ) ≤ B) :
    (T.card : ℝ) ≤ (K + 1) * B := by
  rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := Finset.range (K + 1))
    (fun C hC => Finset.mem_range.2 (Nat.lt_succ_of_le (hf C hC)))]
  push_cast
  calc ∑ m ∈ Finset.range (K + 1), ((T.filter (fun C => f C = m)).card : ℝ)
      ≤ ∑ _m ∈ Finset.range (K + 1), B :=
        Finset.sum_le_sum fun m hm => h m (Nat.lt_succ_iff.1 (Finset.mem_range.1 hm))
    _ = (K + 1) * B := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

theorem capless_G_few (M : ℕ) {ε lam : ℝ} (hε : 0 < ε) (hlam : 0 < lam) :
    ∃ tol > 0, ∃ a₀ > 0, ∀ a, 0 < a → a ≤ a₀ →
      ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
        ∀ (G : GoodFaces X) (mk : Set ℂ → Finset (Sym2 Plane)), IsMarking X (a * diam X) G mk →
          DegreeWindow X (a * diam X) G → IsSaturated X (a * diam X) (lam * diam X) tol G mk →
          ((trackGraph X (a * diam X) G mk).stublessSmall
            ((trackGraph X (a * diam X) G mk).Gs G.good) M : ℝ) ≤ ε * diam X := by
  obtain ⟨Nc, hclus⟩ := long_sides_clustered hlam
  have hε'0 : 0 < ε / (2 * (4 * M + 1)) := by positivity
  choose r hr μ hμ hfew using fun m : ℕ =>
    capless_directions_few m (6 * M + 6) (capNcent Nc M m) hε'0
  have hI : (Finset.range (4 * M + 1)).Nonempty := ⟨0, by simp⟩
  obtain ⟨r0, hr0, hr0m⟩ : ∃ r0 > 0, ∀ m ∈ Finset.range (4 * M + 1), r0 ≤ r m :=
    ⟨_, (Finset.lt_inf'_iff hI).2 fun m _ => hr m, fun m hm => Finset.inf'_le _ hm⟩
  obtain ⟨μ0, hμ0, hμ0m⟩ : ∃ μ0 > 0, ∀ m ∈ Finset.range (4 * M + 1), μ0 ≤ μ m :=
    ⟨_, (Finset.lt_inf'_iff hI).2 fun m _ => hμ m, fun m hm => Finset.inf'_le _ hm⟩
  obtain ⟨ρ, hρ, hρr⟩ : ∃ ρ > 0, ρ * (4 * M + 4) = r0 :=
    ⟨r0 / (4 * M + 4), by positivity, div_mul_cancel₀ _ (by positivity)⟩
  obtain ⟨cρ, hcρ, hclose⟩ := labDir_close hρ
  obtain ⟨εc, hεc, hεcμ⟩ : ∃ εc > 0, εc * (6 * M + 7) = μ0 :=
    ⟨μ0 / (6 * M + 7), by positivity, div_mul_cancel₀ _ (by positivity)⟩
  obtain ⟨Mb, hclusM⟩ := hclus εc hεc
  obtain ⟨c8, hc8, hc8e⟩ : ∃ c8 > 0, c8 * (8 * (M + 1)) = cρ :=
    ⟨cρ / (8 * (M + 1)), by positivity, div_mul_cancel₀ _ (by positivity)⟩
  refine ⟨min ρ c8, lt_min hρ hc8, c8, hc8, fun a ha hab => ?_⟩
  filter_upwards [(Filter.eventually_all_finset (Finset.range (4 * M + 1))).2 fun m _ => hfew m,
    hclose, hclusM, component_witness, mated_label_dist, card_trackEnds,
    eventually_diam_ge (10 * |Mb| / ε), eventually_diam_ge (2 * (M + 1) / cρ),
    eventually_diam_ge 1] with n hfewn hclosen hclusn hwit hmld hends hDbig hDbig2 hD1
  intro hfm X hX htri G mk hmk hwin hsat
  have hD : 0 < diam X := lt_of_lt_of_le one_pos (hD1 X hX)
  obtain ⟨hnoint, lab, hlab⟩ := hsat
  obtain ⟨Ucl, hUcl, Bad, hBad, hcl⟩ := hclusn hfm X hX htri
  have hends' := hends hfm X hX htri
  have htolρ : min ρ c8 ≤ ρ := min_le_left _ _
  have htolc : min ρ c8 ≤ c8 := min_le_right _ _
  have htol0 : 0 ≤ min ρ c8 := (lt_min hρ hc8).le

  have hpar : (M + 1) * (2 * min ρ c8 * diam X + 1 + a * diam X) ≤ cρ * diam X := by
    have h1 : 2 * (M + 1) ≤ cρ * diam X := by
      have := hDbig2 X hX
      rw [div_le_iff₀ hcρ] at this; linarith
    have h2 := mul_le_mul_of_nonneg_right htolc hD.le
    have h3 := mul_le_mul_of_nonneg_right hab hD.le
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    have h4 : (M + 1 : ℝ) * (min ρ c8 * diam X) ≤ (M + 1) * (c8 * diam X) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    have h5 : (M + 1 : ℝ) * (a * diam X) ≤ (M + 1) * (c8 * diam X) :=
      mul_le_mul_of_nonneg_left h3 (by linarith)
    have h6 : (M + 1 : ℝ) * (c8 * diam X) * 8 = cρ * diam X := by rw [← hc8e]; ring
    nlinarith
  have hr1 : M * min ρ c8 + 2 * M * ρ < r0 := by
    have := mul_le_mul_of_nonneg_left htolρ (Nat.cast_nonneg M)
    have := mul_nonneg (Nat.cast_nonneg M) hρ.le
    nlinarith
  have hr2 : min ρ c8 + 2 * ρ < r0 := by
    have := mul_nonneg (Nat.cast_nonneg M) hρ.le
    nlinarith
  have hμ1 : 6 * M * εc < μ0 := by
    have := mul_nonneg (Nat.cast_nonneg M) hεc.le
    nlinarith
  have hL0 : 0 ≤ a * diam X := by positivity
  have hδ0 : 0 ≤ 2 * min ρ c8 * diam X + 1 + a * diam X := by positivity

  have hUgood : (trackGraph X (a * diam X) G mk).Gs G.good ⊆ G.good := Finset.filter_subset _ _
  have hUH : ∀ F ∈ G.good, F ∉ (trackGraph X (a * diam X) G mk).Gs G.good →
      F ∈ (trackGraph X (a * diam X) G mk).Hs G.good := fun F hF hFU =>
    Finset.mem_filter.2 ⟨hF, by_contra fun h => hFU (Finset.mem_filter.2 ⟨hF, h⟩)⟩
  have hmd := hmld hfm X hX htri (a * diam X) (min ρ c8) G mk lab hlab
  set U := (trackGraph X (a * diam X) G mk).Gs G.good with hUdef
  set T := (U.image (StubGraph.cgraph (trackGraph X (a * diam X) G mk) U).connectedComponentMk).filter
    (fun C => (∀ s ∈ (trackGraph X (a * diam X) G mk).S, (trackGraph X (a * diam X) G mk).stub s ∈ U →
      (StubGraph.cgraph (trackGraph X (a * diam X) G mk) U).connectedComponentMk
        ((trackGraph X (a * diam X) G mk).stub s) ≠ C) ∧
      (U.filter (fun x => (StubGraph.cgraph (trackGraph X (a * diam X) G mk) U).connectedComponentMk x
        = C)).card ≤ M) with hTdef
  change (T.card : ℝ) ≤ ε * diam X
  have hsplit := Finset.card_filter_add_card_filter_not (s := T) (p := fun C =>
    (∃ F ∈ U, (StubGraph.cgraph (trackGraph X (a * diam X) G mk) U).connectedComponentMk F
        = C ∧ F ∈ Bad) ∨ ∃ q ∈ unmarkedPorts X (a * diam X) G mk, q.1 ∈ U ∧
        (StubGraph.cgraph (trackGraph X (a * diam X) G mk) U).connectedComponentMk q.1 = C ∧
        TrackMated X (a * diam X) G mk q ∧ (trackMate X q).1 ∈ Bad)
  have hExc := card_excComp_le hends' hmk hwin U Bad T
  have hrep : ∀ C ∈ T, ∃ F ∈ U,
      (StubGraph.cgraph (trackGraph X (a * diam X) G mk) U).connectedComponentMk F = C :=
    fun C hC => Finset.mem_image.1 (Finset.mem_filter.1 hC).1
  choose! rep hrepU hrepC using hrep
  have hGood := card_le_of_fibres (T.filter (fun C => ¬ ((∃ F ∈ U,
      (StubGraph.cgraph (trackGraph X (a * diam X) G mk) U).connectedComponentMk F
        = C ∧ F ∈ Bad) ∨ ∃ q ∈ unmarkedPorts X (a * diam X) G mk, q.1 ∈ U ∧
        (StubGraph.cgraph (trackGraph X (a * diam X) G mk) U).connectedComponentMk q.1 = C ∧
        TrackMated X (a * diam X) G mk q ∧ (trackMate X q).1 ∈ Bad)))
    (fun C => (extPorts X (a * diam X) G mk (U.filter (fun x =>
      (StubGraph.cgraph (trackGraph X (a * diam X) G mk) U).connectedComponentMk x = C))).card)
    (4 * M) (B := ε / (2 * (4 * M + 1)) * diam X) ?_ ?_
  rotate_left
  · intro C hC
    have := (Finset.mem_filter.1 (Finset.mem_filter.1 hC).1).2.2
    exact (card_extPorts_le hends' hmk hwin _).trans (by omega)
  · intro m hm
    have hinj : Set.InjOn (fun C => lab (rep C)) ((T.filter (fun C => ¬ ((∃ F ∈ U,
      (StubGraph.cgraph (trackGraph X (a * diam X) G mk) U).connectedComponentMk F
        = C ∧ F ∈ Bad) ∨ ∃ q ∈ unmarkedPorts X (a * diam X) G mk, q.1 ∈ U ∧
        (StubGraph.cgraph (trackGraph X (a * diam X) G mk) U).connectedComponentMk q.1 = C ∧
        TrackMated X (a * diam X) G mk q ∧ (trackMate X q).1 ∈ Bad))).filter (fun C =>
          (extPorts X (a * diam X) G mk (U.filter (fun x =>
      (StubGraph.cgraph (trackGraph X (a * diam X) G mk) U).connectedComponentMk x = C))).card = m)) := by
      intro C hC C' hC' h
      have hCT : C ∈ T := (Finset.mem_filter.1 (Finset.mem_filter.1 hC).1).1
      have hCT' : C' ∈ T := (Finset.mem_filter.1 (Finset.mem_filter.1 hC').1).1
      have := hlab.1 (hUgood (hrepU C hCT)) (hUgood (hrepU C' hCT')) h
      rw [← hrepC C hCT, ← hrepC C' hCT', this]
    rw [← Finset.card_image_of_injOn hinj]
    refine hfewn m (Finset.mem_range.2 (by omega)) X hX (capCentres Ucl M m)
      (card_capCentres_le hUcl M m) _ ?_ ?_
    · intro p hp
      obtain ⟨C, hC, rfl⟩ := Finset.mem_image.1 hp
      have hCT : C ∈ T := (Finset.mem_filter.1 (Finset.mem_filter.1 hC).1).1
      exact (Finset.mem_filter.1 (hlab.2 _ (hUgood (hrepU C hCT))).1).1
    · intro p hp
      obtain ⟨C, hC, rfl⟩ := Finset.mem_image.1 hp
      obtain ⟨hCG, hfC⟩ := Finset.mem_filter.1 hC
      obtain ⟨hCT, hnexc⟩ := Finset.mem_filter.1 hCG
      obtain ⟨-, hstub, hsmall⟩ := Finset.mem_filter.1 hCT
      obtain ⟨hF0, hCf, hCM, hmat, hH, hdist⟩ := stubless_component_facts hends' hUgood hUH lab hδ0
        hmd hstub hsmall (hrepU C hCT) (hrepC C hCT) _ rfl
      have hnB : ∀ F ∈ U.filter (fun x =>
          (StubGraph.cgraph (trackGraph X (a * diam X) G mk) U).connectedComponentMk x = C),
          F ∉ Bad := fun F hF hFB =>
        hnexc (Or.inl ⟨F, (Finset.mem_filter.1 hF).1, (Finset.mem_filter.1 hF).2, hFB⟩)
      have hnB' : ∀ q ∈ unmarkedPorts X (a * diam X) G mk, q.1 ∈ U.filter (fun x =>
          (StubGraph.cgraph (trackGraph X (a * diam X) G mk) U).connectedComponentMk x = C) →
          (trackMate X q).1 ∉ Bad := fun q hq hqC hB =>
        hnexc (Or.inr ⟨q, hq, (Finset.mem_filter.1 hqC).1, (Finset.mem_filter.1 hqC).2,
          hmat q hq hqC, hB⟩)
      obtain ⟨d, hd, ⟨c, hc, hdc⟩, ⟨pp, uu, hpu, h0, h1⟩⟩ := hwit hfm X hX htri (a * diam X)
        (lam * diam X) (min ρ c8) ρ cρ εc μ0 r0 M G mk lab Ucl Bad hmk hnoint hlab hcl
        (hclosen X hX) hpar hr1 hr2 hμ1 hμ0 hεc.le htol0 hL0 _ _ hF0 hCf hCM hnB hnB' hmat hH hdist
      have hmr : m ∈ Finset.range (4 * M + 1) := Finset.mem_range.2 (by omega)
      subst hfC
      exact ⟨d, hd, ⟨c, hc, hdc.trans_le (hμ0m _ hmr)⟩, pp, uu, hpu, h0.trans_le (hr0m _ hmr),
        fun i => (h1 i).trans_le (hr0m _ hmr)⟩
  have hB1 : (5 * Bad.card : ℝ) ≤ ε / 2 * diam X := by
    have h1 : (Bad.card : ℝ) ≤ |Mb| := hBad.trans (le_abs_self Mb)
    have h2 := hDbig X hX
    rw [div_le_iff₀ hε] at h2
    linarith
  have hExc' : ((T.filter (fun C => (∃ F ∈ U,
      (StubGraph.cgraph (trackGraph X (a * diam X) G mk) U).connectedComponentMk F
        = C ∧ F ∈ Bad) ∨ ∃ q ∈ unmarkedPorts X (a * diam X) G mk, q.1 ∈ U ∧
        (StubGraph.cgraph (trackGraph X (a * diam X) G mk) U).connectedComponentMk q.1 = C ∧
        TrackMated X (a * diam X) G mk q ∧ (trackMate X q).1 ∈ Bad)).card : ℝ) ≤ 5 * Bad.card := by
    exact_mod_cast hExc
  have hK : ((4 * M : ℕ) + 1 : ℝ) * (ε / (2 * (4 * M + 1)) * diam X) = ε / 2 * diam X := by
    push_cast; field_simp
  rw [← hsplit, Nat.cast_add]
  linarith

end Erdos99
end

end CaplessGFew
