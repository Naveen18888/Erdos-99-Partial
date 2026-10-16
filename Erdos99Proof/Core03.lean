module

public import Mathlib
public import Erdos99Proof.Core02

section Crux

open scoped Real ComplexConjugate
open Complex Set Metric EstablishedExternalResults

@[expose] public noncomputable section

namespace Erdos99

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

lemma cr_lagrange (e B H : ℂ) :
    normSq e * ccr B H = (conj e * B).re * ccr e H - ccr e B * (conj e * H).re := by
  simp only [cr_eq, normSq_apply, mul_re, conj_re, conj_im]
  ring

lemma ev_lin_pos {c d : ℝ} (hc : 0 < c) : ∀ᶠ ε in nhds (0 : ℝ), 0 < c + ε * d := by
  have hcont : Continuous (fun ε : ℝ => c + ε * d) := by fun_prop
  have := hcont.tendsto 0
  simp only [zero_mul, add_zero] at this
  exact this.eventually (lt_mem_nhds hc)

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

  have hjun : (∀ y ∈ Y, 0 ≤ ccr (h - b) (y - b)) ∧ 0 < ccr (h - b) (o - b) := by
    have hl : (a2 :: L1').getLast? = some b := by
      rw [List.getLast?_eq_some_getLast (by simp), hL1]
    exact (List.isChain_append.1 hchain).2.2 b (by simp [hl]) h (by simp)
  set κ := ccr (h - b) (o - b) with hκ
  have hκ0 : 0 < κ := hjun.2
  have hbh : b ≠ h := by rintro rfl; rw [hκ, sub_self] at hκ0; simp [cr_eq] at hκ0

  set supp : ℂ → ℂ → Prop :=
    fun g g' => (∀ y ∈ Y, 0 ≤ ccr (g' - g) (y - g)) ∧ 0 < ccr (g' - g) (o - g) with hsupp
  have hc1 : (a2 :: L1').IsChain supp := (List.isChain_append.1 hchain).1
  have hc2 : (h :: L2').IsChain supp := (List.isChain_append.1 hchain).2.1

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

  set dil : ℂ → ℂ := fun z => z + (ε : ℂ) * (z - o) with hdil
  set R : List ℂ := L2'.map dil ++ (a1 :: P') ++ (a2 :: L1').map dil with hR
  have hRne : R ≠ [] := by simp [hR]
  have hΓl : (dil b :: dil h :: R).getLast (by simp) = dil b := by
    rw [List.getLast_cons (by simp), List.getLast_cons hRne]
    simp only [hR]
    rw [List.getLast_append_of_ne_nil _ (by simp), List.getLast_map (by simp), hL1]

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

  have hA3 : ms ∉ polyline (dil h :: R) := by
    intro hm
    rcases mem_polyline_of_chain _ _ hchR ms hm with ⟨hR0, -⟩ | ⟨x, y, hxy, hz⟩
    · exact hRne hR0
    rcases hxy with ⟨g, g', hs, hpart, hx, hy⟩ | ⟨hx, hy⟩ | ⟨hsub, -, -⟩ | ⟨hx, hy⟩ <;>
      try rw [hx, hy] at hz
    ·
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
    ·
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
    ·
      have := polyline_cr_nonneg hjun.1 a1 P' hPY ms (hsub hz)
      rw [hF1] at this
      nlinarith
    ·
      obtain ⟨t, ht0, htε, hmz⟩ := rad_param2 hε.le hz
      have := rad_cr_ge (c := h - b) (g := b) (o := o) ht0 htε (a := a2)
      rw [← hmz, hF1] at this
      nlinarith

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

section Arc

open scoped Real ComplexConjugate
open Complex Set Metric EstablishedExternalResults

@[expose] public noncomputable section

namespace Erdos99

abbrev IsHV (Y : Finset ℂ) (z : ℂ) : Prop := z ∈ extremePoints ℝ (convexHull ℝ (Y : Set ℂ))

lemma IsHV.mem {Y : Finset ℂ} {z : ℂ} (h : IsHV Y z) : z ∈ Y := by
  have := extremePoints_convexHull_subset h
  exact_mod_cast this

lemma clm_apply_C (f : ℂ →L[ℝ] ℝ) (z : ℂ) : f z = z.re * f 1 + z.im * f I := by
  have e : z = z.re • (1 : ℂ) + z.im • I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [e]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

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
    ((Y.finite_toSet.diff).isCompact_convexHull ℝ |>.isClosed) hvt
  refine ⟨-⟨f 1, f I⟩, fun y hy hyv => ?_⟩
  have := hb y (subset_convexHull ℝ _ ⟨hy, hyv⟩)
  rw [clm_apply_C] at this hfu
  simp only [mul_re, conj_re, conj_im, neg_re, neg_im, sub_re, sub_im]
  nlinarith

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
  have hcomp : IsCompact (convexHull ℝ (Y : Set ℂ)) := Y.finite_toSet.isCompact_convexHull ℝ
  have hcl := closure_convexHull_extremePoints hcomp (convex_convexHull ℝ _)
  have hy' : y ∈ convexHull ℝ (Y : Set ℂ) := subset_convexHull ℝ _ (by exact_mod_cast hy)
  rw [← hcl] at hy'
  have hyK : y ∈ K := (closure_minimal (convexHull_min hsub hKv) hKc) hy'
  exact absurd hyK (not_le.2 hneg)

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

  set φ : ℂ → ℝ := fun z => -(conj e * (z - o)).re / ccr e (z - o) with hφ
  set V := Y.filter (fun z => IsHV Y z ∧ 0 < ccr e (z - o)) with hVdef
  have hV : ∀ z, z ∈ V ↔ z ∈ Y ∧ IsHV Y z ∧ 0 < ccr e (z - o) := fun z => by
    rw [hVdef, Finset.mem_filter]
  have hbV : b ∈ V := (hV b).2 ⟨hb.mem, hb, hbp⟩
  have hφlt : ∀ x ∈ V, ∀ y ∈ V, φ x < φ y ↔ 0 < ccr (x - o) (y - o) := fun x hx y hy =>
    phi_lt_iff ((hV x).1 hx).2.2 ((hV y).1 hy).2.2

  have hinj : ∀ x ∈ V, ∀ y ∈ V, ccr (x - o) (y - o) = 0 → x = y := fun x hx y hy h0 =>
    eq_of_same_ray_extreme hoH ((hV x).1 hx).2.1 ((hV y).1 hy).2.1 ((hV x).1 hx).2.2
      ((hV y).1 hy).2.2 h0

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

section ContactRelease

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
  ·
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

section RotationRelease

open scoped BigOperators Real

@[expose] public noncomputable section

open Classical

namespace Erdos99

lemma exists_uniform_neg {α : Type*} (s : Finset α) (g : α → ℝ) :
    ∃ β > 0, ∀ x ∈ s, g x < 0 → g x ≤ -β := by
  by_cases h : (s.filter (fun x => g x < 0)).Nonempty
  · obtain ⟨x0, hx0, hmax⟩ := (s.filter (fun x => g x < 0)).exists_max_image g h
    rw [Finset.mem_filter] at hx0
    refine ⟨-g x0, by linarith [hx0.2], fun x hx hgx => ?_⟩
    have := hmax x (Finset.mem_filter.2 ⟨hx, hgx⟩)
    linarith
  · exact ⟨1, one_pos, fun x hx hgx => absurd ⟨x, Finset.mem_filter.2 ⟨hx, hgx⟩⟩ h⟩

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

section Connected

open scoped Real ComplexConjugate
open Complex Set Metric EstablishedExternalResults

@[expose] public noncomputable section

open Classical

namespace Erdos99

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

def contactRel (X : Finset Plane) (z w : ℂ) : Prop :=
  z = w ∨ ∃ (hp : toC.symm z ∈ X) (hq : toC.symm w ∈ X),
    (contactGraph X).Reachable ⟨toC.symm z, hp⟩ ⟨toC.symm w, hq⟩

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

section DirectCountAlgebra

open scoped Real

@[expose] public section

namespace Erdos99

namespace DirectCount

theorem two_R_eq (b u c₂ v f p h fhi σhi σ Δ ρ s E R Y A C₁ d : ℝ)
    (hb : b = u + c₂ + v) (hs : 2 * s = 2 * b - Δ + 4 * f) (hf : f = p + h + fhi)
    (hσ : σ = p + 2 * h + σhi) (hΔ : Δ = u - σ - ρ) (hR : R = s - E)
    (hD1 : 2 * E = u + 2 * c₂ - C₁ + 3 * p + 4 * h + Y + 2 * A + d) :
    2 * R = 2 * f - Y - 2 * A + C₁ + σhi + 2 * fhi + ρ + 2 * v - d := by
  subst hR; linarith

noncomputable def eR (fhi σhi ρ v d : ℝ) : ℝ := (σhi + 2 * fhi + ρ + 2 * v + |d|) / 2

theorem R_le {f fhi σhi ρ v R Y A C₁ d : ℝ}
    (h : 2 * R = 2 * f - Y - 2 * A + C₁ + σhi + 2 * fhi + ρ + 2 * v - d) :
    R ≤ f - Y / 2 - A + C₁ / 2 + eR fhi σhi ρ v d := by
  unfold eR
  have := neg_abs_le d
  linarith

theorem f_add_c₂_le {b u c₂ v f p h fhi σhi σ Δ ρ : ℝ}
    (hb : b = u + c₂ + v) (hf : f = p + h + fhi) (hσ : σ = p + 2 * h + σhi)
    (hΔ : Δ = u - σ - ρ) (hΔ0 : 0 ≤ Δ) (hh : 0 ≤ h) (hhi : fhi ≤ σhi) (hv : 0 ≤ v)
    (hρ : 0 ≤ ρ) :
    f + c₂ ≤ b := by
  linarith

theorem charge_lower (H g₂ Y fgood j₁ j₂ j₃ x hC C κG κK eJJ : ℝ)
    (hf : fgood = H + Y - g₂) (hx : x ≤ 4 * g₂)
    (hC1 : 2 * H = j₁ + 2 * j₂ + 3 * j₃ + x + hC)
    (hC3 : g₂ ≤ 3 / 2 * Y + C / 2 + κG - fgood)
    (hC4 : 3 * j₁ + 2 * j₂ + j₃ + x ≤ Y + 2 * eJJ + C - hC + 2 * κK) :
    4 * fgood - 5 * Y - hC - C - κG - κK ≤ eJJ + 2 * j₂ + 4 * j₃ := by
  linarith

noncomputable def eCharge (κG κK eFlag eCap eHCap Bf : ℝ) : ℝ :=
  κG + κK + eFlag + eCap + eHCap + 4 * Bf

theorem four_f_le {f Bf fgood Y P c₂ C₁ C hC M κG κK eFlag eCap eHCap : ℝ}
    (hfg : fgood = f - Bf)
    (hC5 : 4 * fgood - 5 * Y - hC - C - κG - κK ≤ M)
    (hC6 : M ≤ 4 * P + eFlag)
    (hCap : C ≤ 2 * c₂ - C₁ + eCap) (hHCap : hC ≤ 2 * (c₂ - C₁) + eHCap) :
    4 * f ≤ 5 * Y + 4 * P + 4 * c₂ - 3 * C₁ + eCharge κG κK eFlag eCap eHCap Bf := by
  unfold eCharge
  linarith

theorem direct_track_count_algebra (R P f Y A c₂ C₁ B eR eC : ℝ)
    (hR : R ≤ f - Y / 2 - A + C₁ / 2 + eR)
    (hC : 4 * f ≤ 5 * Y + 4 * P + 4 * c₂ - 3 * C₁ + eC)
    (hA : 0 ≤ A) (hCap : C₁ ≤ c₂) (hBudget : f + c₂ ≤ B) :
    R - P ≤ (3 / 5 : ℝ) * (B - P) + eR + eC / 10 := by
  linarith

theorem direct_track_count_slack (R P f Y A c₂ C₁ B eR eC : ℝ) :
    ((3 / 5 : ℝ) * (B - P) + eR + eC / 10) - (R - P) =
      (f - Y / 2 - A + C₁ / 2 + eR - R) + (5 * Y + 4 * P + 4 * c₂ - 3 * C₁ + eC - 4 * f) / 10 +
        (c₂ - C₁) / 5 + 3 / 5 * (B - f - c₂) + A := by
  ring

theorem abs_defect_le {d dFace Bface Bunit Btwo cLong ρ : ℝ}
    (hd : d = dFace - Bunit - 2 * Btwo + cLong) (hFace : |dFace| ≤ Bface)
    (hunit : 0 ≤ Bunit) (htwo : 0 ≤ Btwo) (hcL : 0 ≤ cLong) (hcL' : cLong ≤ 3 * ρ) :
    |d| ≤ Bface + Bunit + 2 * Btwo + 3 * ρ := by
  rw [abs_le] at hFace ⊢
  constructor <;> linarith

theorem eR_le {fhi σhi ρ v d Hinc Bface Bunit Btwo : ℝ}
    (hHinc : σhi + 2 * fhi ≤ Hinc) (hv : v ≤ ρ)
    (hd : |d| ≤ Bface + Bunit + 2 * Btwo + 3 * ρ) :
    eR fhi σhi ρ v d ≤ (Hinc + Bface + Bunit + 2 * Btwo + 6 * ρ) / 2 := by
  unfold eR
  linarith

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

theorem track_count_of_ledger {ε D : ℝ} (hε : 0 < ε) (hD : 0 < D)

    {b u c₂ v f p h fhi σhi σ Δ ρ s E R Y A C₁ d P : ℝ}
    (hb : b = u + c₂ + v) (hs : 2 * s = 2 * b - Δ + 4 * f) (hf : f = p + h + fhi)
    (hσ : σ = p + 2 * h + σhi) (hΔ : Δ = u - σ - ρ) (hR : R = s - E)
    (hD1 : 2 * E = u + 2 * c₂ - C₁ + 3 * p + 4 * h + Y + 2 * A + d)
    (hΔ0 : 0 ≤ Δ) (hh : 0 ≤ h) (hhi : fhi ≤ σhi) (hv0 : 0 ≤ v) (hv : v ≤ ρ)
    (hbD : b ≤ π * D) (hA : 0 ≤ A) (hC₁ : C₁ ≤ c₂)

    {H g₂ fgood Bf j₁ j₂ j₃ x hC C κG κK eJJ eFlag eCap eHCap : ℝ}
    (hfg : fgood = f - Bf) (hfH : fgood = H + Y - g₂) (hx : x ≤ 4 * g₂)
    (hC1 : 2 * H = j₁ + 2 * j₂ + 3 * j₃ + x + hC)
    (hC3 : g₂ ≤ 3 / 2 * Y + C / 2 + κG - fgood)
    (hC4 : 3 * j₁ + 2 * j₂ + j₃ + x ≤ Y + 2 * eJJ + C - hC + 2 * κK)
    (hC6 : eJJ + 2 * j₂ + 4 * j₃ ≤ 4 * P + eFlag)
    (hCap : C ≤ 2 * c₂ - C₁ + eCap) (hHCap : hC ≤ 2 * (c₂ - C₁) + eHCap)

    {Hinc Bface Bunit Btwo : ℝ}
    (hHinc : σhi + 2 * fhi ≤ Hinc) (hd : |d| ≤ Bface + Bunit + 2 * Btwo + 3 * ρ)

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

section FiniteCutoff

open Filter

@[expose] public section

namespace Erdos99

theorem shell_disjoint {a : ℕ → ℝ} (ha : Antitone a) {D x : ℝ} (hD : 0 ≤ D) {i j : ℕ}
    (hij : i < j) (hi : a (i + 1) * D ≤ x) (hj : x < a j * D) : False := by
  have : a j * D ≤ a (i + 1) * D := mul_le_mul_of_nonneg_right (ha hij) hD
  linarith

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

section QuadraticResponseAlgebra

open Filter Polynomial ComplexConjugate

@[expose] public section

namespace Erdos99

namespace QuadraticResponse

lemma mul_conj_eq_one {z : ℂ} (hz : ‖z‖ = 1) : z * conj z = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; simp

lemma ne_zero_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) : z ≠ 0 := by
  rintro rfl; simp at hz

lemma conj_eq_inv {z : ℂ} (hz : ‖z‖ = 1) : conj z = z⁻¹ :=
  eq_inv_of_mul_eq_one_right (mul_conj_eq_one hz)

lemma norm_sq_eq_mul_conj (w : ℂ) : ((‖w‖ ^ 2 : ℝ) : ℂ) = w * conj w := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma conj_response {ζ : ℂ} (hζ : ‖ζ‖ = 1) (k : ℝ) (Z : ℂ) :
    conj ((k : ℂ) * ζ + Z) = (k : ℂ) / ζ + conj Z := by
  rw [map_add, map_mul, Complex.conj_ofReal, conj_eq_inv hζ, div_eq_mul_inv]

theorem two_circle_eq {z a : ℂ} (hz : ‖z‖ = 1) (hza : ‖z - a‖ = 1) :
    conj a * z ^ 2 - a * conj a * z + a = 0 := by
  have h0 := mul_conj_eq_one hz
  have h1 := mul_conj_eq_one hza
  rw [map_sub] at h1
  linear_combination -z * h1 + z * h0 - a * h0

theorem two_circle_eq_zeta {ζ Z z : ℂ} (k : ℝ) (hζ : ‖ζ‖ = 1) (hz : ‖z‖ = 1)
    (hza : ‖z - ((k : ℂ) * ζ + Z)‖ = 1) :
    ((k : ℂ) / ζ + conj Z) * z ^ 2 - ((k : ℂ) * ζ + Z) * ((k : ℂ) / ζ + conj Z) * z +
      ((k : ℂ) * ζ + Z) = 0 := by
  have := two_circle_eq hz hza
  rwa [conj_response hζ] at this

theorem two_circle_eq_poly {ζ Z z : ℂ} (k : ℝ) (hζ : ‖ζ‖ = 1) (hz : ‖z‖ = 1)
    (hza : ‖z - ((k : ℂ) * ζ + Z)‖ = 1) :
    ((k : ℂ) + ζ * conj Z) * z ^ 2 - ((k : ℂ) * ζ + Z) * ((k : ℂ) + ζ * conj Z) * z +
      ζ * ((k : ℂ) * ζ + Z) = 0 := by
  have h := two_circle_eq_zeta k hζ hz hza
  have hζ0 := ne_zero_of_norm_eq_one hζ
  have hinv : ζ * ζ⁻¹ = 1 := mul_inv_cancel₀ hζ0
  simp only [div_eq_mul_inv] at h ⊢
  linear_combination ζ * h + ((k : ℂ) * z * Z - (k : ℂ) * z ^ 2 + (k : ℂ) ^ 2 * ζ * z) * hinv

theorem quadratic_norm {R : Type*} [CommRing R] {z a b U V : R} (h : z ^ 2 - a * z + b = 0) :
    (U + V * z) * (U + V * (a - z)) = U ^ 2 + a * U * V + b * V ^ 2 := by
  linear_combination (-V ^ 2) * h

theorem quadratic_root_elim {R : Type*} [CommRing R] {z A B C U V : R}
    (h : A * z ^ 2 + B * z + C = 0) (hUV : U + V * z = 0) :
    A * U ^ 2 - B * U * V + C * V ^ 2 = 0 := by
  linear_combination V ^ 2 * h + (A * (U - V * z) - B * V) * hUV

theorem response_factor {R : Type*} [CommRing R] {a aS z : R}
    (h : aS * z ^ 2 - a * aS * z + a = 0) : (z - a) * (aS * z - 1) = -z := by
  linear_combination h

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

theorem response_zero_Z {k T : ℝ} (hk : k ≠ 0) (hT : T ≠ 0) (z : ℂ) :
    ((k : ℂ) / T) * z ^ 2 - ((k : ℂ) * T) * ((k : ℂ) / T) * z + (k : ℂ) * T = 0 ↔
      (z / T) ^ 2 - k * (z / T) + 1 = 0 := by
  have hT' : (T : ℂ) ≠ 0 := by exact_mod_cast hT
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk
  have key : ((k : ℂ) / T) * z ^ 2 - ((k : ℂ) * T) * ((k : ℂ) / T) * z + (k : ℂ) * T =
      ((k : ℂ) * T) * ((z / T) ^ 2 - k * (z / T) + 1) := by
    field_simp
  rw [key, mul_eq_zero, or_iff_right (mul_ne_zero hk' hT')]

theorem re_eq_of_root {k : ℝ} (hk : k ^ 2 ≤ 4) {d : ℂ} (hd : d ^ 2 - k * d + 1 = 0) :
    d.re = k / 2 := by
  have hre := congrArg Complex.re hd
  have him := congrArg Complex.im hd
  simp [pow_two] at hre him

  have him' : d.im * (2 * d.re - k) = 0 := by linarith
  rcases mul_eq_zero.1 him' with h | h
  · rw [h] at hre
    nlinarith [sq_nonneg (2 * d.re - k)]
  · linarith

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

theorem hh_identity_ring {R : Type*} [CommRing R] {a a' b b' u u' : R}
    (h0 : u * u' = 1) (h1 : u * a' + u' * a + a * a' = 0) (h2 : u * b' + u' * b - b * b' = 0) :
    a * a' * (b * b') * ((a + b) * (a' + b')) + (a * b' - a' * b) ^ 2 = 0 := by
  linear_combination (-(a' * b - a * b') ^ 2) * h0 +
    (a' * b' * (a + b) * b - u * (a' * b - a * b') * b') * h1 +
    (-(a' * b' * (a + b) * a) + u * (a' * b - a * b') * a') * h2

theorem hh_identity {w a b : ℂ} (hw : ‖w‖ = 1) (ha : ‖w + a‖ = 1) (hb : ‖w - b‖ = 1) :
    a * conj a * (b * conj b) * ((a + b) * (conj a + conj b)) + (a * conj b - conj a * b) ^ 2 =
      0 := by
  have h0 := mul_conj_eq_one hw
  have h1 := mul_conj_eq_one ha
  have h2 := mul_conj_eq_one hb
  rw [map_add] at h1
  rw [map_sub] at h2
  exact hh_identity_ring h0 (by linear_combination h1 - h0) (by linear_combination h0 - h2)

theorem hh_identity_star {ζ Z W w : ℂ} (k l : ℝ) (hζ : ‖ζ‖ = 1) (hw : ‖w‖ = 1)
    (ha : ‖w + ((k : ℂ) * ζ + Z)‖ = 1) (hb : ‖w - ((l : ℂ) * ζ + W)‖ = 1) :
    ((k : ℂ) * ζ + Z) * ((k : ℂ) / ζ + conj Z) * (((l : ℂ) * ζ + W) * ((l : ℂ) / ζ + conj W)) *
        ((((k : ℂ) * ζ + Z) + ((l : ℂ) * ζ + W)) * (((k : ℂ) / ζ + conj Z) +
          ((l : ℂ) / ζ + conj W))) +
      (((k : ℂ) * ζ + Z) * ((l : ℂ) / ζ + conj W) - ((k : ℂ) / ζ + conj Z) *
        ((l : ℂ) * ζ + W)) ^ 2 = 0 := by
  have := hh_identity hw ha hb
  rwa [conj_response hζ, conj_response hζ] at this

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

noncomputable def capPoly (k : ℝ) (v Z : ℂ) : ℂ[X] :=
  (C (k : ℂ) * X + C (conj v) * X ^ 2 + C Z) * (C (k : ℂ) * X + C v + C (conj Z) * X ^ 2) - X ^ 2

theorem capPoly_eval {ζ : ℂ} (hζ : ‖ζ‖ = 1) (k : ℝ) (v Z : ℂ) :
    (capPoly k v Z).eval ζ = ζ ^ 2 * (((‖(k : ℂ) * ζ + ζ ^ 2 * conj v + Z‖ ^ 2 - 1 : ℝ)) : ℂ) := by
  have hζ0 := ne_zero_of_norm_eq_one hζ
  push_cast
  rw [← Complex.ofReal_pow, norm_sq_eq_mul_conj]
  simp only [capPoly, eval_sub, eval_mul, eval_add, eval_C, eval_X, eval_pow, map_add, map_mul,
    map_pow, Complex.conj_ofReal, Complex.conj_conj, conj_eq_inv hζ]
  field_simp

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

section Overview

open scoped BigOperators Real
open Filter

@[expose] public noncomputable section

open Classical

namespace Erdos99

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

lemma boundary_point_hullVertex_and_diam_endpoint :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      ∀ x ∈ X, x ∈ frontier (convexHull ℝ (X : Set Plane)) →
        x ∈ hullVertices X ∧ ∃ y ∈ X, dist x y = diam X := by
  filter_upwards [eventually_not_collinear, eventually_ge_atTop 2] with n hcol hn hfm X hX x hx hfr
  obtain ⟨y, hy, hd⟩ := exists_diam_partner_of_frontier hn hfm hX (hcol X hX) hx hfr
  have hxy : x ≠ y := by
    rintro rfl; rw [dist_self] at hd; exact (hX.diam_pos hn).ne hd
  exact ⟨mem_hullVertices_of_diam hx hy hxy hd, y, hy, hd⟩

lemma contactGraph_connected :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      (contactGraph X).Connected := by
  filter_upwards [eventually_ge_atTop 2] with n hn hfm X hX
  exact contactGraph_connected_of_optimal hn hfm hX

lemma first_order_locking :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      ∀ v : Plane → Plane,
        (∀ x ∈ X, ∀ y ∈ X, dist x y = 1 → 0 ≤ inner ℝ (x - y) (v x - v y)) →
        (∀ x ∈ X, ∀ y ∈ X, dist x y = diam X → inner ℝ (x - y) (v x - v y) ≤ 0) →
        IsTrivialVelocity X v := by
  filter_upwards [eventually_ge_atTop 2, eventually_not_collinear] with n hn hcol hfm X hX v hU hT
  exact first_order_locking_of hn hfm hX (hcol X hX) v hU hT

lemma locking_count :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      2 * n ≤ (unitEdges X).card + (diamPairs X).card + 2 := by
  filter_upwards [first_order_locking, tendsto_minDiam.eventually_ge_atTop 2,
    eventually_ge_atTop 2] with n hl hD hn hfm X hX
  have h := card_rows_of_locking (X := X) (by rw [hX.1.1]; exact hn)
    (by rw [hX.diam_eq]; linarith) (hl hfm X hX)
  rwa [hX.1.1] at h

lemma card_le_density :
    ∃ C : ℝ, ∀ᶠ n in atTop, ∀ X, IsOptimal n X → (n : ℝ) ≤ cDensity * diam X ^ 2 + C * diam X := by
  refine ⟨8 * cDensity, ?_⟩
  filter_upwards [eventually_ge_atTop 2] with n hn X hX
  have h := card_le_density_of_separated hX.1.2 (by rw [hX.1.1]; exact hn)
  rwa [hX.1.1] at h

lemma hullVertices_card_le {n : ℕ} {X : Finset Plane} (hX : IsOptimal n X) (hn : 2 ≤ n) :
    ((hullVertices X).card : ℝ) ≤ π * diam X :=
  hullVertices_card_le_pi_mul_diam hX.1.2 (by rw [hX.1.1]; exact hn)

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

lemma rhombus_two_tracks :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ R ∈ rhombi X, ∃ T ∈ tracks X, ∃ T' ∈ tracks X, T ≠ T' ∧
        ∀ T'' ∈ tracks X, Crosses T'' R ↔ (T'' = T ∨ T'' = T') :=
  Eventually.of_forall fun _ _ _ hX htri _ hR => rhombus_two_tracks_of_separated hX.1.2 htri hR

lemma tracks_cross_at_most_once :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ T ∈ tracks X, ∀ T' ∈ tracks X, T ≠ T' →
        ((rhombi X).filter (fun R => Crosses T R ∧ Crosses T' R)).card ≤ 1 :=
  Eventually.of_forall fun _ _ _ hX htri _ hT _ hT' hne =>
    tracks_cross_at_most_once_of_separated hX.1.2 htri hT hT' hne

lemma crossingGraph_cliqueFree :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      (crossingGraph X).CliqueFree 3 :=
  Eventually.of_forall fun _ _ _ hX htri => crossingGraph_cliqueFree_of_separated hX.1.2 htri

lemma trackLength_le :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ T ∈ tracks X, (trackLength X T : ℝ) ≤ diam X / aStar :=
  Eventually.of_forall fun _ _ _ hX htri _ hT => trackLength_le_of_separated hX.1.2 htri hT

lemma tracks_card_le :
    ∃ C : ℝ, ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      ¬ HasUnitTriangle X → ((tracks X).card : ℝ) ≤ C * diam X := by

  obtain ⟨C, hC⟩ := rhombi_card_ge
  refine ⟨2 * C, ?_⟩
  filter_upwards [hC] with n h hfm X hX htri
  obtain ⟨hm, hq⟩ := h hfm X hX htri
  have hs := card_tracks_add_two_mul_card_rhombi_le hX.1.2 htri
  have hm' : ((unitEdges X).card : ℝ) + 2 ≤ 2 * n := by exact_mod_cast hm
  have hs' : ((tracks X).card : ℝ) + 2 * (rhombi X).card ≤ (unitEdges X).card := by
    exact_mod_cast hs
  linarith

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

lemma mantel {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.CliqueFree 3) : (G.edgeFinset.card : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 / 4 := by

  have h1 := hG.card_edgeFinset_le (r := 2)
  rw [SimpleGraph.turanNumber_two] at h1
  have h2 : 4 * G.edgeFinset.card ≤ Fintype.card V ^ 2 := by omega
  have h3 : (4 * G.edgeFinset.card : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
    exact_mod_cast h2
  linarith

lemma rhombi_inside_card_le :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X → ¬ HasUnitTriangle X →
      ∀ S ⊆ tracks X,
        (((rhombi X).filter (fun R => ∀ T ∈ tracks X, Crosses T R → T ∈ S)).card : ℝ) ≤
          (S.card : ℝ) ^ 2 / 4 := by
  filter_upwards [tracks_cross_at_most_once] with n hcross hfm X hX htri S hS
  let G : SimpleGraph {T // T ∈ S} :=
    (crossingGraph X).comap (Function.Embedding.subtype (· ∈ S))
  have hG : G.CliqueFree 3 := SimpleGraph.CliqueFree.comap
    (SimpleGraph.Embedding.comap _ _).isContained
    (crossingGraph_cliqueFree_of_separated hX.1.2 htri)
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

structure CountingWitness (X : Finset Plane) (ε : ℝ) where

  f : ℕ

  β : ℕ

  c₂ : ℕ

  C₁ : ℕ

  A : ℕ

  long : Finset (Finset (Sym2 Plane))

  sel : Finset (Finset (Sym2 Plane))
  long_subset : long ⊆ tracks X
  sel_subset : sel ⊆ long

  abs_R_sub : |(long.card : ℝ) - ((f : ℝ) - β)| ≤ ε * diam X

  f_add_c₂_le : (f : ℝ) + c₂ ≤ π * diam X + ε * diam X

  two_fifths : 2 / 5 * (f : ℝ) + A - ε * diam X ≤ β + 2 / 5 * (sel.card : ℝ) + 2 / 5 * c₂ + 1 / 5 * C₁
  C₁_le_c₂ : C₁ ≤ c₂

  short_loss : (((rhombi X).filter
      (fun R => ∃ T ∈ tracks X, T ∉ long ∧ Crosses T R)).card : ℝ) ≤ ε * diam X ^ 2

  annular_linear : (((rhombi X).filter (fun R => ∃ T ∈ sel, Crosses T R)).card : ℝ) ≤
      diam X * sel.card / 2 + ε * diam X ^ 2

  annular_quadratic : (((rhombi X).filter (fun R => ∃ T ∈ sel, Crosses T R)).card : ℝ) ≤
      cDensity / 4 * diam X ^ 2 + ε * diam X ^ 2

lemma exists_round_center (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n in atTop, ∀ X, IsOptimal n X →
      ∃ O : Plane, ∀ x ∈ X, dist x O ≤ diam X / 2 + η * diam X :=
  round_center_of_optimal η hη

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

def finalF (x : ℝ) : ℝ := 9 / 100 * (π - x) ^ 2 + x / 2

def finalA : ℝ := π - 5 / 3 * Real.sqrt (3 * cDensity)

lemma sqrt3_bounds : 1.732 < √3 ∧ √3 < 1.7321 := by
  constructor
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

lemma cDensity_bounds : 0.9068 < cDensity ∧ cDensity < 0.907 := by
  obtain ⟨h1, h2⟩ := sqrt3_bounds
  have p1 := Real.pi_gt_d6
  have p2 := Real.pi_lt_d6
  unfold cDensity
  constructor
  · rw [lt_div_iff₀ (by positivity)]; nlinarith
  · rw [div_lt_iff₀ (by positivity)]; nlinarith

lemma finalF_zero_lt : finalF 0 < cDensity := by
  have := cDensity_bounds.1
  have p2 := Real.pi_lt_d6
  have p1 := Real.pi_gt_d6
  unfold finalF; nlinarith

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

lemma eq14 {D ε R P f β c₂ C₁ A : ℝ}
    (hR : R ≤ f - β + ε * D) (hfc : f + c₂ ≤ π * D + ε * D)
    (h25 : 2 / 5 * f + A - ε * D ≤ β + 2 / 5 * P + 2 / 5 * c₂ + 1 / 5 * C₁)
    (hC : C₁ ≤ c₂) (hA : 0 ≤ A) :
    R - P ≤ 3 / 5 * (π * D - P) + 13 / 5 * ε * D := by
  linarith

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

  by_cases hs : P ≤ 9 / 20 * D
  ·
    have f2 : π * D ^ 2 ≤ 3.1416 * D ^ 2 := mul_le_mul_of_nonneg_right p2.le hD2.le
    have f3 : 0 ≤ P * D := mul_nonneg hP0 hD.le
    have f3' : 3 * (P * D) ≤ π * (P * D) := mul_le_mul_of_nonneg_right (by linarith) f3
    have f4 : 0 ≤ P * (9 / 20 * D - P) := mul_nonneg hP0 (by linarith)
    nlinarith
  ·
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

end Erdos99
end

end Overview

section InnerRound

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

section ConvexFaces

open scoped BigOperators Real
open EstablishedExternalResults Set Filter

@[expose] public noncomputable section

open Classical

namespace Erdos99

lemma mem_ccwHullSides {X : Finset Plane} {p : Plane × Plane} :
    p ∈ ccwHullSides X ↔ IsCcwHullSide X p.1 p.2 := by
  unfold ccwHullSides
  simp only [Finset.mem_filter, Finset.mem_product]
  exact ⟨fun h => h.2, fun h => ⟨⟨mem_of_mem_hullVertices h.1, mem_of_mem_hullVertices h.2.1⟩, h⟩⟩

lemma convexHull_hullVertices (X : Finset Plane) :
    convexHull ℝ ((hullVertices X : Finset Plane) : Set Plane) = convexHull ℝ (X : Set Plane) := by
  have e : ((hullVertices X : Finset Plane) : Set Plane) =
      extremePoints ℝ (convexHull ℝ (X : Set Plane)) := by
    ext x
    simp only [hullVertices, Finset.coe_filter, Set.mem_setOf_eq]
    exact ⟨fun h => h.2, fun h => ⟨extremePoints_convexHull_subset h, h⟩⟩
  rw [e]
  have hc := (X.finite_toSet).isCompact_convexHull ℝ
  have h := closure_convexHull_extremePoints hc (convex_convexHull ℝ _)
  refine le_antisymm (convexHull_min (extremePoints_subset) (convex_convexHull ℝ _)) ?_
  calc convexHull ℝ (X : Set Plane) = _ := h.symm
    _ ⊆ _ := closure_minimal subset_rfl ?_
  exact ((X.finite_toSet.subset extremePoints_convexHull_subset)).isClosed_convexHull ℝ

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

lemma card_ccwHullSides {X : Finset Plane} (hb : 3 ≤ (hullVertices X).card) :
    (ccwHullSides X).card = (hullVertices X).card := by
  refine Finset.card_bij (fun p _ => p.1) (fun p hp => (mem_ccwHullSides.1 hp).1) ?_ ?_
  · intro p hp q hq h
    have hq' := mem_ccwHullSides.1 hq
    rw [← h] at hq'
    exact Prod.ext h ((mem_ccwHullSides.1 hp).succ_unique hq')
  · intro v hv
    have h2 := two_le_card_hullPairs_fst hv hb

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

lemma hull_subset_halfplane {X : Finset Plane} {v w : Plane} (hs : IsCcwHullSide X v w) :
    convexHull ℝ (X : Set Plane) ⊆ {z : Plane | 0 ≤ det2 (w - v) (z - v)} :=
  convexHull_min (fun y hy => hs.2.2.2 y hy) (convex_det2_halfplane _ _)

lemma det2_segment_zero {v w z : Plane} (hz : z ∈ segment ℝ v w) : det2 (w - v) (z - v) = 0 := by
  obtain ⟨a, b, -, -, hab, rfl⟩ := hz
  have : a • v + b • w - v = b • (w - v) := by
    rw [show a = 1 - b by linarith, sub_smul, one_smul, smul_sub]; abel
  rw [this, det2_smul_right]; unfold det2; ring

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

lemma mem_segment_of_det2_zero {X : Finset Plane} {v w : Plane} (hs : IsCcwHullSide X v w)
    {y : Plane} (hy : y ∈ X) (h0 : det2 (w - v) (y - v) = 0) : y ∈ segment ℝ v w := by
  have hd : w - v ≠ 0 := sub_ne_zero.2 hs.2.2.1.symm
  obtain ⟨s, hs'⟩ := eq_smul_of_det2_eq_zero hd h0
  have hvX := mem_of_mem_hullVertices hs.1
  have hwX := mem_of_mem_hullVertices hs.2.1
  have hy' : y = v + s • (w - v) := by rw [← hs']; abel
  rcases lt_or_ge s 0 with hneg | hnn
  ·
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
  ·
    exfalso
    refine not_mem_openSegment_of_hull hs.2.1 hvX hy hs.2.2.1 ?_
    refine ⟨1 - 1 / s, 1 / s, by
      rw [sub_pos, div_lt_one (by linarith)]; exact hgt, by positivity, by ring, ?_⟩
    rw [hy']
    have hs0 : s ≠ 0 := by linarith
    match_scalars <;> field_simp <;> ring

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

lemma boundary_hullVertex_eventually :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      ∀ x ∈ X, x ∈ frontier (convexHull ℝ (X : Set Plane)) → x ∈ hullVertices X := by
  filter_upwards [eventually_not_collinear, eventually_ge_atTop 2] with n hcol hn hfm X hX x hx hfr
  obtain ⟨y, hy, hd⟩ := exists_diam_partner_of_frontier hn hfm hX (hcol X hX) hx hfr
  have hxy : x ≠ y := by
    rintro rfl; rw [dist_self] at hd; exact (hX.diam_pos hn).ne hd
  exact mem_hullVertices_of_diam hx hy hxy hd

theorem augEdges_isPlaneGraph :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      IsPlaneGraph (cVerts X) (augEdges X) := by
  filter_upwards [boundary_hullVertex_eventually] with n hB hfm X hX
  exact augEdges_isPlaneGraph_of hX.1.2 (hB hfm X hX)

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
    Relation.ReflTransGen.lift (fun v : X => toC v.1) key _ _ hr
  exact h2

theorem cUnitEdges_connected :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      GraphConnected (cVerts X) (cUnitEdges X) := by
  filter_upwards [eventually_ge_atTop 2] with n hn hfm X hX
  exact cUnitEdges_connected_of_optimal hn hfm hX

theorem augEdges_connected :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      GraphConnected (cVerts X) (augEdges X) := by
  filter_upwards [cUnitEdges_connected] with n h hfm X hX
  obtain ⟨hne, hr⟩ := h hfm X hX
  exact ⟨hne, fun u hu v hv => Relation.ReflTransGen.mono (fun a b hab => Finset.mem_union_left _ hab) _ _ (hr u hu v hv)⟩

end Erdos99

end

end ConvexFaces

section HullSpread

open scoped BigOperators Real ComplexConjugate
open Filter MeasureTheory

@[expose] public noncomputable section

open Classical

namespace Erdos99

def omega3 : ℂ := ⟨-1 / 2, √3 / 2⟩

def sixRoots : Finset ℂ := {1, omega3, omega3 ^ 2, -1, -omega3, -omega3 ^ 2}

lemma card_sixRoots_le : sixRoots.card ≤ 6 := Finset.card_le_six

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

def sideDir (p : Plane × Plane) : Plane := ‖p.2 - p.1‖⁻¹ • (p.2 - p.1)

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

lemma inner_sideNormal_nonpos {X : Finset Plane} {p : Plane × Plane} (hp : IsCcwHullSide X p.1 p.2)
    {y : Plane} (hy : y ∈ X) : inner ℝ (y - p.1) (-rot (sideDir p)) ≤ 0 := by
  rw [inner_neg_right, inner_rot_eq_det2, sideDir, det2_smul_left, neg_nonpos]
  exact mul_nonneg (inv_nonneg.2 (norm_nonneg _)) (hp.2.2.2 y hy)

lemma inner_sideNormal_side (p : Plane × Plane) :
    inner ℝ (p.2 - p.1) (-rot (sideDir p)) = 0 := by
  rw [inner_neg_right, inner_rot_eq_det2, sideDir, det2_smul_left, neg_eq_zero]
  unfold det2; ring

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

section PropagationLedger

open scoped BigOperators Real
open Filter Topology

@[expose] public noncomputable section

namespace Erdos99

namespace Propagation

def markedCap (k : ℕ) : ℝ :=
  if k ≤ 6 then 2 else if k ≤ 8 then 3 else ((k : ℝ) - 4) - ((k : ℝ) - 8) / 4

def netAbsorbed (k a : ℕ) : ℝ :=
  (a : ℝ) - (if k = 5 ∧ 2 ≤ a then 1 else 0) - (if k = 7 ∧ 3 ≤ a then 1 else 0)

def emitted (k a : ℕ) : ℕ := if (k = 5 ∧ 2 ≤ a) ∨ (k = 7 ∧ 3 ≤ a) then 1 else 0

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

lemma netAbsorbed_add_emitted (k a : ℕ) : netAbsorbed k a + emitted k a = a := by
  unfold netAbsorbed emitted
  by_cases h5 : k = 5 ∧ 2 ≤ a
  · have h7 : ¬ (k = 7 ∧ 3 ≤ a) := by omega
    simp [h5]
  · by_cases h7 : k = 7 ∧ 3 ≤ a
    · simp [h7]
    · simp [h5, h7]

lemma emitted_eq_zero {k a : ℕ} (hk : k ≠ 5 ∧ k ≠ 7) : emitted k a = 0 := by
  unfold emitted; rw [if_neg (by omega)]

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

def returnCap (j : ℕ) : ℝ :=
  if j ≤ 3 then 0 else if j = 4 then 1 else if j = 5 then 2 else 2 * ((j : ℝ) - 2) / 3

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

lemma le_highIncidence {k : ℕ} (hk : 7 ≤ k) :
    (k : ℝ) ≤ 7 * (if k = 7 then 1 else 0) + 8 * (if k = 8 then 1 else 0) + 9 * ((k - 8 : ℕ) : ℝ) := by
  rcases (show k = 7 ∨ k = 8 ∨ 9 ≤ k by omega) with rfl | rfl | h9
  · norm_num
  · norm_num
  · rw [if_neg (by omega), if_neg (by omega), Nat.cast_sub (by omega)]
    have : (9 : ℝ) ≤ k := by exact_mod_cast h9
    push_cast; linarith

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

theorem frontier_ge_of_ledger {u σ ρ Δ f₇ f₈ Q₉ Aface Acap Lost F Bsrc B₁ B₂ B₃ : ℝ}
    (hΔ : Δ = u - σ - ρ) (hcons : u - Bsrc ≤ Aface + Acap + Lost + F)
    (hface : Aface ≤ σ - f₇ - f₈ - Q₉ / 4 + B₁) (hcap : Acap ≤ 2 * ρ / 3 + B₂)
    (hlost : Lost ≤ B₃) :
    (Δ + ρ / 3 + f₇ + f₈ + Q₉ / 4) - (Bsrc + B₁ + B₂ + B₃) ≤ F := by
  subst hΔ; linarith

theorem conservation_S1 (K : ℕ) (F : ℕ → ℝ) {S B N : ℝ}
    (hF : ∀ j ∈ Finset.Icc 1 K, S - B ≤ F j) (hsum : ∑ j ∈ Finset.Icc 1 K, F j ≤ N) :
    K * S ≤ N + K * B := by
  have h := Finset.card_nsmul_le_sum (Finset.Icc 1 K) F (S - B) hF
  rw [Nat.card_Icc, nsmul_eq_mul] at h
  simp only [add_tsub_cancel_right] at h
  nlinarith

theorem stability_of_S1 {K : ℕ} (hK : 0 < K) {Δ ρ f₇ f₈ Q₉ N B D : ℝ}
    (hΔ : 0 ≤ Δ) (hρ : 0 ≤ ρ) (h7 : 0 ≤ f₇) (h8 : 0 ≤ f₈) (hQ : 0 ≤ Q₉)
    (hS1 : K * (Δ + ρ / 3 + f₇ + f₈ + Q₉ / 4) ≤ N + K * B) (hN : N ≤ π * D) :
    Δ ≤ π * D / K + B ∧ ρ / 3 ≤ π * D / K + B ∧ f₇ ≤ π * D / K + B ∧ f₈ ≤ π * D / K + B ∧
      Q₉ / 4 ≤ π * D / K + B := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hS : Δ + ρ / 3 + f₇ + f₈ + Q₉ / 4 ≤ π * D / K + B := by
    rw [div_add' _ _ _ hK'.ne', le_div_iff₀ hK']; nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith

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

def scaleExp (j : ℕ) : ℝ := 1 / (20 * 4 ^ j)

def scale (D : ℝ) (j : ℕ) : ℝ := D ^ (1 - scaleExp j)

lemma scaleExp_pos (j : ℕ) : 0 < scaleExp j := by unfold scaleExp; positivity

lemma scaleExp_le (j : ℕ) : scaleExp j ≤ 1 / 20 := by
  unfold scaleExp
  apply one_div_le_one_div_of_le (by norm_num)
  have : (1 : ℝ) ≤ 4 ^ j := one_le_pow₀ (by norm_num)
  linarith

lemma scaleExp_succ (j : ℕ) : scaleExp j = 4 * scaleExp (j + 1) := by
  unfold scaleExp; rw [pow_succ]; field_simp

lemma scaleExp_anti {i j : ℕ} (h : i ≤ j) : scaleExp j ≤ scaleExp i := by
  unfold scaleExp
  apply one_div_le_one_div_of_le (by positivity)
  have : (4 : ℝ) ^ i ≤ 4 ^ j := pow_le_pow_right₀ (by norm_num) h
  linarith

lemma scale_mono {D : ℝ} (hD : 1 ≤ D) {i j : ℕ} (h : i ≤ j) : scale D i ≤ scale D j := by
  unfold scale
  exact Real.rpow_le_rpow_of_exponent_le hD (by linarith [scaleExp_anti h])

theorem tendsto_rpow_div_self {a : ℝ} (ha : a < 1) :
    Tendsto (fun D : ℝ => D ^ a / D) atTop (𝓝 0) := by
  have h := tendsto_rpow_neg_atTop (show 0 < 1 - a by linarith)
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with D hD
  rw [Real.rpow_neg hD.le, Real.rpow_sub hD, Real.rpow_one, inv_div]

theorem tendsto_sum_rpow_div_self {ι : Type*} (s : Finset ι) (c a : ι → ℝ) (ha : ∀ i ∈ s, a i < 1) :
    Tendsto (fun D : ℝ => (∑ i ∈ s, c i * D ^ a i) / D) atTop (𝓝 0) := by
  have : (fun D : ℝ => (∑ i ∈ s, c i * D ^ a i) / D) = fun D => ∑ i ∈ s, c i * (D ^ a i / D) := by
    funext D; rw [Finset.sum_div]; congr 1; funext i; ring
  rw [this]
  rw [show (0 : ℝ) = ∑ i ∈ s, c i * 0 by simp]
  exact tendsto_finset_sum _ (fun i hi => (tendsto_rpow_div_self (ha i hi)).const_mul (c i))

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

def triDet (p q r : ℝ × ℝ) : ℝ := (q.1 - p.1) * (r.2 - p.2) - (r.1 - p.1) * (q.2 - p.2)

lemma triDet_eq (p q r : ℝ × ℝ) :
    triDet p q r = p.1 * q.2 - q.1 * p.2 + q.1 * r.2 - r.1 * q.2 + r.1 * p.2 - p.1 * r.2 := by
  unfold triDet; ring

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

theorem inscribed_sides_sq (x1 y1 x2 y2 x3 y3 R : ℝ) (h1 : x1^2 + y1^2 = R^2)
    (h2 : x2^2 + y2^2 = R^2) (h3 : x3^2 + y3^2 = R^2) :
    ((x1-x2)^2+(y1-y2)^2)*((x2-x3)^2+(y2-y3)^2)*((x3-x1)^2+(y3-y1)^2) =
      4*R^2*((x2-x1)*(y3-y1)-(x3-x1)*(y2-y1))^2 := by
  linear_combination (-3*R^2*x2^2 + 6*R^2*x2*x3 - 3*R^2*x3^2 + R^2*y2^2 - 2*R^2*y2*y3 + R^2*y3^2 + x1^2*x2^2 - 2*x1^2*x2*x3 + x1^2*x3^2 + x1^2*y2^2 - 2*x1^2*y2*y3 + x1^2*y3^2 - 2*x1*x2^3 + 2*x1*x2^2*x3 + 2*x1*x2*x3^2 - 2*x1*x2*y2^2 + 4*x1*x2*y2*y3 - 2*x1*x2*y3^2 - 2*x1*x3^3 - 2*x1*x3*y2^2 + 4*x1*x3*y2*y3 - 2*x1*x3*y3^2 + x2^4 - 2*x2^3*x3 + 2*x2^2*x3^2 + x2^2*y1^2 - 2*x2^2*y1*y2 - 2*x2^2*y1*y3 + 2*x2^2*y2^2 + 2*x2^2*y2*y3 + 2*x2^2*y3^2 - 2*x2*x3^3 - 2*x2*x3*y1^2 + 4*x2*x3*y1*y2 + 4*x2*x3*y1*y3 - 2*x2*x3*y2^2 - 8*x2*x3*y2*y3 - 2*x2*x3*y3^2 + x3^4 + x3^2*y1^2 - 2*x3^2*y1*y2 - 2*x3^2*y1*y3 + 2*x3^2*y2^2 + 2*x3^2*y2*y3 + 2*x3^2*y3^2 + y1^2*y2^2 - 2*y1^2*y2*y3 + y1^2*y3^2 - 2*y1*y2^3 + 2*y1*y2^2*y3 + 2*y1*y2*y3^2 - 2*y1*y3^3 + y2^4 + 2*y2^3*y3 - 6*y2^2*y3^2 + 2*y2*y3^3 + y3^4) * h1 + (2*R^4 - 4*R^2*x1^2 - 2*R^2*x1*x2 + 4*R^2*x1*x3 + R^2*x2^2 - 2*R^2*x2*x3 - R^2*x3^2 - 2*R^2*y1*y2 + R^2*y2^2 + 2*R^2*y2*y3 - 5*R^2*y3^2 + 4*x1^2*x2*x3 - 4*x1^2*y2*y3 + 8*x1^2*y3^2 - 2*x1*x2^2*x3 + 2*x1*x2*x3^2 + 4*x1*x2*y1*y3 - 2*x1*x2*y3^2 - 2*x1*x3^3 + 4*x1*x3*y1*y2 - 8*x1*x3*y1*y3 - 2*x1*x3*y2^2 + 4*x1*x3*y2*y3 - 2*x1*x3*y3^2 + x2^2*x3^2 - 2*x2^2*y1*y3 + x2^2*y3^2 - 2*x2*x3^3 + 4*x2*x3*y1*y3 - 2*x2*x3*y3^2 + x3^4 - 2*x3^2*y1*y2 + 2*x3^2*y1*y3 + x3^2*y2^2 - 2*x3^2*y2*y3 + 2*x3^2*y3^2 - 2*y1*y2^2*y3 + 2*y1*y2*y3^2 + 2*y1*y3^3 + y2^2*y3^2 - 2*y2*y3^3 + y3^4) * h2 + (-2*R^4 + 4*R^2*x1^2 + 2*R^2*x1*x2 - 4*R^2*x1*x3 + 4*R^2*x2^2 - 4*R^2*x2*x3 + 2*R^2*x3^2 + 2*R^2*y1*y2 + 2*R^2*y3^2 - 8*x1^2*x2^2 + 4*x1^2*x2*x3 - 4*x1^2*y2*y3 + 4*x1*x2^2*x3 - 2*x1*x2*x3^2 - 8*x1*x2*y1*y2 + 4*x1*x2*y1*y3 + 4*x1*x2*y2*y3 - 2*x1*x2*y3^2 + 4*x1*x3*y1*y2 - 4*x2^2*y1*y3 + 4*x2*x3*y1*y2 - 2*x3^2*y1*y2 - 2*y1*y2*y3^2) * h3

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

section LocalCapacity

open scoped BigOperators Real

@[expose] public noncomputable section

open Classical

namespace Erdos99

open Fin.NatCast Fin.CommRing

structure UnitPolygon (k : ℕ) [NeZero k] where

  P : Fin k → Plane
  unit_edge : ∀ i, ‖P (i + 1) - P i‖ = 1
  sep : ∀ i j, i ≠ j → 1 ≤ dist (P i) (P j)

namespace UnitPolygon

variable {k : ℕ} [NeZero k] (Q : UnitPolygon k)

def edge (i : Fin k) : Plane := Q.P (i + 1) - Q.P i

lemma norm_edge (i : Fin k) : ‖Q.edge i‖ = 1 := Q.unit_edge i

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

theorem capacity_five (Q : UnitPolygon 5) {e : Plane} (he : ‖e‖ = 1) {c : ℝ} (hc : 2 / 3 < c)
    {M : Finset (Fin 5)} (hM : ∀ i ∈ M, c ≤ inner ℝ (Q.edge i) e) : M.card ≤ 2 := by
  have h := Q.projection_bound he hM
  by_contra hcon
  have : (3 : ℝ) ≤ M.card := by exact_mod_cast (show 3 ≤ M.card by omega)
  push_cast at h
  nlinarith

theorem capacity_seven (Q : UnitPolygon 7) {e : Plane} (he : ‖e‖ = 1) {c : ℝ} (hc : 3 / 4 < c)
    {M : Finset (Fin 7)} (hM : ∀ i ∈ M, c ≤ inner ℝ (Q.edge i) e) : M.card ≤ 3 := by
  have h := Q.projection_bound he hM
  by_contra hcon
  have : (4 : ℝ) ≤ M.card := by exact_mod_cast (show 4 ≤ M.card by omega)
  push_cast at h
  nlinarith

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

namespace LocalCapacity

lemma sqrt3_half_sq : (√3 / 2) ^ 2 = 3 / 4 := by
  rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num

lemma sqrt3_half_bounds : 4 / 5 < √3 / 2 ∧ √3 / 2 < 1 := by
  have h := sqrt3_half_sq
  have h0 : 0 ≤ √3 / 2 := by positivity
  constructor <;> nlinarith

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

  have hsum : (p1 + 1 / 2) + (1 / 2 - p2) ≤ δ ^ 2 := by linarith
  have ha1 : |p1 + 1 / 2| ≤ δ + δ ^ 2 := abs_le.2 ⟨by linarith, by linarith⟩
  have ha2 : |p2 - 1 / 2| ≤ δ + δ ^ 2 := abs_le.2 ⟨by linarith, by linarith⟩
  have hhp : |h + 1| ≤ 3 * δ := abs_le.2 ⟨by linarith, by linarith⟩
  have sa1 : (p1 + 1 / 2) ^ 2 ≤ (δ + δ ^ 2) ^ 2 := sq_le_sq' (abs_le.1 ha1).1 (abs_le.1 ha1).2
  have sa2 : (p2 - 1 / 2) ^ 2 ≤ (δ + δ ^ 2) ^ 2 := sq_le_sq' (abs_le.1 ha2).1 (abs_le.1 ha2).2

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

lemma norm_le_of_frame {e w : Plane} (he : ‖e‖ = 1) {r : ℝ} (hr : 0 ≤ r)
    (h : inner ℝ w e ^ 2 + inner ℝ w (rot e) ^ 2 ≤ r ^ 2) : ‖w‖ ≤ r := by
  have e1 := frame_norm_sq he w
  exact (pow_le_pow_iff_left₀ (norm_nonneg w) hr two_ne_zero).1 (by linarith)

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

lemma inner_ge_of_close {u e : Plane} (hu : ‖u‖ = 1) (he : ‖e‖ = 1) {δ : ℝ}
    (h : ‖u - e‖ ≤ δ) : 1 - δ ^ 2 / 2 ≤ inner ℝ u e := by
  have e1 := norm_sub_sq_real u e
  rw [hu, he] at e1
  have := pow_le_pow_left₀ (norm_nonneg _) h 2
  linarith

lemma inner_close {u e w : Plane} {δ : ℝ} (h : ‖u - e‖ ≤ δ) :
    |inner ℝ w u - inner ℝ w e| ≤ ‖w‖ * δ := by
  rw [← inner_sub_right]
  exact (abs_real_inner_le_norm w (u - e)).trans (mul_le_mul_of_nonneg_left h (norm_nonneg w))

lemma inner_ge_of_sep {a u : Plane} (ha : ‖a‖ = 1) (hu : ‖u‖ = 1) (h : 1 ≤ ‖a + u‖) :
    -1 / 2 ≤ inner ℝ a u := by
  have e1 := norm_add_sq_real a u
  rw [ha, hu] at e1
  have := pow_le_pow_left₀ zero_le_one h 2
  linarith

theorem pentagon_estimate {A B C X Y e : Plane} {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 100)
    (he : ‖e‖ = 1) (hAB : ‖B - A‖ = 1) (hBC : ‖C - B‖ = 1) (hu0 : ‖(B - A) - e‖ ≤ δ)
    (hu1 : ‖(C - B) - e‖ ≤ δ) (hCX : ‖X - C‖ = 1) (hXY : ‖Y - X‖ = 1) (hYA : ‖A - Y‖ = 1)
    (hXB : 1 ≤ ‖X - B‖) (hYB : 1 ≤ ‖Y - B‖) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      ‖(X - C) - ((-1 / 2 : ℝ) • e + (σ * (√3 / 2)) • rot e)‖ ≤ 4 * δ ∧
      ‖(Y - X) + e‖ ≤ 10 * δ ∧
      ‖(A - Y) - ((-1 / 2 : ℝ) • e + (-(σ * (√3 / 2))) • rot e)‖ ≤ 4 * δ := by
  have hYA' : ‖Y - A‖ = 1 := by rw [norm_sub_rev]; exact hYA

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

  have hp1 : -1 / 2 - δ ≤ inner ℝ (X1 - P3) e := by
    have h1 := inner_ge_of_sep hX1 h23 (by
      rw [show X1 - P3 + (P3 - P2) = X1 - P2 by abel]; exact hs1)
    have h2 := abs_le.1 (inner_close (w := X1 - P3) hu2)
    rw [hX1, one_mul] at h2
    linarith

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

def NearAngle (θ φ δ : ℝ) : Prop := ∃ n : ℤ, |θ - φ - 2 * π * n| ≤ δ

def OrdConvex {k : ℕ} (S : Finset (Fin k)) : Prop :=
  ∀ i j l : Fin k, i < j → j < l → i ∈ S → l ∈ S → j ∈ S

instance {k : ℕ} (S : Finset (Fin k)) : Decidable (OrdConvex S) := by
  unfold OrdConvex; infer_instance

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

  have hai : i < a := by
    by_contra h; push_neg at h
    exact ha (near_outside hmono hwrap hδ hij hjl hi hl hj a (Or.inl h))
  have hcl : c < l := by
    by_contra h; push_neg at h
    exact hc (near_outside hmono hwrap hδ hij hjl hi hl hj c (Or.inr h))

  exact hc (near_outside hmono hwrap hδ hai hab hi hb ha c (Or.inr hbc.le))

set_option maxRecDepth 100000 in

theorem consecutive_five : ∀ M : Finset (Fin 5), M.card = 2 → (OrdConvex M ∨ OrdConvex Mᶜ) →
    ∃ s : Fin 5, M = {s, s + 1} := by
  decide +kernel

set_option maxRecDepth 100000 in

theorem consecutive_seven : ∀ M : Finset (Fin 7), M.card = 3 → (OrdConvex M ∨ OrdConvex Mᶜ) →
    ∃ s : Fin 7, M = {s, s + 1, s + 2} := by
  decide +kernel

theorem pentagon_marked_consecutive {θ : Fin 5 → ℝ} (hmono : Monotone θ)
    (hwrap : ∀ a b, θ b ≤ θ a + 2 * π) {φ δ : ℝ} (hδ : δ < π)
    (hcard : (Finset.univ.filter fun i => NearAngle (θ i) φ δ).card = 2) :
    ∃ s : Fin 5, (Finset.univ.filter fun i => NearAngle (θ i) φ δ) = {s, s + 1} :=
  consecutive_five _ hcard (marked_orderConvex hmono hwrap hδ)

theorem heptagon_marked_consecutive {θ : Fin 7 → ℝ} (hmono : Monotone θ)
    (hwrap : ∀ a b, θ b ≤ θ a + 2 * π) {φ δ : ℝ} (hδ : δ < π)
    (hcard : (Finset.univ.filter fun i => NearAngle (θ i) φ δ).card = 3) :
    ∃ s : Fin 7, (Finset.univ.filter fun i => NearAngle (θ i) φ δ) = {s, s + 1, s + 2} :=
  consecutive_seven _ hcard (marked_orderConvex hmono hwrap hδ)

theorem cos_ge_of_nearAngle {θ φ δ : ℝ} (hδ : δ ≤ π) (h : NearAngle θ φ δ) :
    Real.cos δ ≤ Real.cos (θ - φ) := by
  obtain ⟨n, hn⟩ := h
  have e : Real.cos (θ - φ) = Real.cos (|θ - φ - 2 * π * n|) := by
    rw [Real.cos_abs, show θ - φ - 2 * π * n = θ - φ - (n : ℤ) * (2 * π) by ring,
      Real.cos_sub_int_mul_two_pi]
  rw [e]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hδ hn

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

section FinitePropagation

open scoped BigOperators Real
open Filter Topology EstablishedExternalResults

@[expose] public noncomputable section

open Classical

namespace Erdos99

open Propagation

def highExcess (X : Finset Plane) : ℕ := ∑ᶠ F ∈ exceptionalFaces X, (faceSize X F - 8)

def highIncidence (X : Finset Plane) : ℕ :=
  ∑ᶠ F ∈ {F ∈ contactFaces X | 7 ≤ faceSize X F}, faceSize X F

def stabilityDefect (X : Finset Plane) : ℝ :=
  (lockingDefect X : ℝ) + (returnExcess X : ℝ) / 3 + faceCount X 7 + faceCount X 8 +
    (highExcess X : ℝ) / 4

section Bookkeeping

variable {X : Finset Plane}

lemma contactFaces_finite (hX : IsSeparated X) : (contactFaces X).Finite :=
  (faces_finite (cUnitEdges_isPlaneGraph hX)).subset (fun _ hF => hF.1)

lemma exceptionalFaces_finite (hX : IsSeparated X) : (exceptionalFaces X).Finite :=
  (contactFaces_finite hX).subset (fun _ hF => hF.1)

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

theorem sum_faceNetCap_eq (hfin : (exceptionalFaces X).Finite) :
    ∑ F ∈ hfin.toFinset, faceNetCap (faceSize X F) =
      (faceExcess X : ℝ) - faceCount X 7 - faceCount X 8 - (highExcess X : ℝ) / 4 := by
  rw [sum_faceNetCap hfin.toFinset (faceSize X)
    (fun F hF => ((Set.Finite.mem_toFinset hfin).1 hF).2), faceExcess_eq_sum hfin,
    highExcess_eq_sum hfin, faceCount_eq_card_filter hfin (by norm_num : 5 ≤ 7),
    faceCount_eq_card_filter hfin (by norm_num : 5 ≤ 8)]
  push_cast
  ring

theorem highIncidence_le (hX : IsSeparated X) :
    (highIncidence X : ℝ) ≤ 7 * faceCount X 7 + 8 * faceCount X 8 + 9 * highExcess X := by
  have hfin := exceptionalFaces_finite hX
  rw [highIncidence_eq_sum hfin, highExcess_eq_sum hfin,
    faceCount_eq_card_filter hfin (by norm_num : 5 ≤ 7),
    faceCount_eq_card_filter hfin (by norm_num : 5 ≤ 8)]
  push_cast
  exact sum_highIncidence_le hfin.toFinset (faceSize X)

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

structure TokenLedger (X : Finset Plane) (K : ℕ) (B : ℝ) where

  fin : (exceptionalFaces X).Finite

  arr : ℕ → Set ℂ → ℕ
  arr_zero : ∀ F, arr 0 F = 0
  arr_mono : ∀ j F, arr j F ≤ arr (j + 1) F
  arr_cap : ∀ F ∈ exceptionalFaces X, (arr K F : ℝ) ≤ markedCap (faceSize X F)

  capAbs : ℕ → ℝ
  cap_le : ∀ j ≤ K, capAbs j ≤ 2 * (returnExcess X : ℝ) / 3 + B

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

def frontier (j : ℕ) : ℝ :=
  ∑ F ∈ T.fin.toFinset,
    ((emitted (faceSize X F) (T.arr j F) : ℝ) - emitted (faceSize X F) (T.arr (j - 1) F))

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

section TokenProcess

open scoped BigOperators Real
open Filter Topology

@[expose] public noncomputable section

open Classical

namespace Erdos99

open Propagation

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

inductive TokenDest
  | face (F : Set ℂ)
  | cap
  | lost

structure TokenProcess (X : Finset Plane) where

  fin : (exceptionalFaces X).Finite

  start : Plane × Plane → TokenDest

  out : Set ℂ → TokenDest

namespace TokenProcess

variable {X : Finset Plane} (P : TokenProcess X)

def toFace (d : TokenDest) (F : Set ℂ) : ℕ := if d = .face F then 1 else 0

def toCap (d : TokenDest) : ℕ := if d = .cap then 1 else 0

def toLost (S : Finset (Set ℂ)) : TokenDest → ℕ
  | .face F => if F ∈ S then 0 else 1
  | .cap => 0
  | .lost => 1

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

def faceArr : ℕ → Set ℂ → ℕ
  | 0, _ => 0
  | j + 1, F => ∑ p ∈ unitHullSides X, toFace (P.start p) F +
      ∑ G ∈ P.fin.toFinset, toFace (P.out G) F * emitted (faceSize X G) (faceArr j G)

def capArr : ℕ → ℕ
  | 0 => 0
  | j + 1 => ∑ p ∈ unitHullSides X, toCap (P.start p) +
      ∑ G ∈ P.fin.toFinset, toCap (P.out G) * emitted (faceSize X G) (P.faceArr j G)

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

lemma markedCap_nonneg (k : ℕ) : 0 ≤ markedCap k := by
  unfold markedCap
  split_ifs with h1 h2
  · norm_num
  · norm_num
  · have : (9 : ℝ) ≤ k := by exact_mod_cast (show 9 ≤ k by omega)
    linarith

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

    have hfr : 0 ≤ ∑ F ∈ hfin.toFinset,
        ((emitted (faceSize X F) (if j = 0 then 0 else ⌊markedCap (faceSize X F)⌋₊) : ℝ) -
          emitted (faceSize X F) (if j - 1 = 0 then 0 else ⌊markedCap (faceSize X F)⌋₊)) := by
      refine Finset.sum_nonneg (fun F _ => sub_nonneg.2 ?_)
      have hle : (if j - 1 = 0 then 0 else ⌊markedCap (faceSize X F)⌋₊) ≤
          (if j = 0 then 0 else ⌊markedCap (faceSize X F)⌋₊) := by
        rw [if_neg hj1]; split_ifs <;> simp
      exact_mod_cast TokenLedger.emitted_mono _ hle

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
  ·
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

section FaceConvexity

open scoped BigOperators Real
open EstablishedExternalResults Set Complex Filter Topology

@[expose] public noncomputable section

open Classical

namespace Erdos99

def FanCondition (V : Finset ℂ) (E : Finset (Sym2 ℂ)) : Prop :=
  ∀ y ∈ V, y ∉ extremePoints ℝ (convexHull ℝ (V : Set ℂ)) → ∀ ν : ℂ, ν ≠ 0 →
    ∃ y', s(y, y') ∈ E ∧ 0 < ((y' - y) / ν).im

lemma wc_affine (z w y p : ℂ) (l : ℝ) :
    wc z w (y + (l : ℂ) * (p - y)) = wc z w y + (l : ℂ) * (wc z w p - wc z w y) := by
  simp only [wc]; ring

lemma continuousAt_wc {z w : ℂ} (hzw : z ≠ w) (x : ℂ) :
    ContinuousAt (fun w' => wc z w' x) w := by
  unfold wc
  exact continuousAt_const.div (continuousAt_id.sub continuousAt_const) (sub_ne_zero.2 hzw.symm)

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

lemma cross_stable {z w y a b : ℂ} (hzw : z ≠ w) (hy : y ∈ openSegment ℝ z w)
    (ha : 0 < (wc z w a).im) (hb : (wc z w b).im < 0) :
    ∀ᶠ w' in 𝓝 w, (segment ℝ z w' ∩ (segment ℝ y a ∪ segment ℝ y b)).Nonempty := by

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
  ·
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
  ·
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

lemma subset_face {F : Set ℂ} (hF : F ∈ faces V E) {S : Set ℂ} (hS : IsPreconnected S)
    (hSD : S ⊆ (drawing V E)ᶜ) {z : ℂ} (hzS : z ∈ S) (hzF : z ∈ F) : S ⊆ F := by
  rw [face_eq_component hF hzF]
  exact hS.subset_connectedComponentIn hzS hSD

lemma closure_face_diff {F : Set ℂ} (hF : F ∈ faces V E) {z : ℂ} (hz : z ∈ closure F)
    (hzF : z ∉ F) : z ∈ drawing V E := by
  by_contra hD
  obtain ⟨x, -, rfl⟩ := mem_faces_iff.1 hF
  exact hzF (mem_face_of_mem_closure (isClosed_drawing V E).isOpen_compl hz hD)

lemma boundedFace_subset_hull (hP : IsPlaneGraph V E) {F : Set ℂ} (hF : F ∈ faces V E)
    (hb : Bornology.IsBounded F) : F ⊆ convexHull ℝ (V : Set ℂ) := by
  intro z hzF
  by_contra hzK
  obtain ⟨f, u, hfz, hfK⟩ := geometric_hahn_banach_point_closed (convex_convexHull ℝ _)
    (V.finite_toSet.isClosed_convexHull ℝ) hzK
  set d : ℂ := -((f 1 : ℂ) + (f I : ℂ) * I)
  have hfd : f d = -((f 1) ^ 2 + (f I) ^ 2) := by
    rw [clm_C f d]; simp [d]; ring

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

section FacePolygon

open scoped BigOperators Real
open EstablishedExternalResults Set Complex Filter Topology

@[expose] public noncomputable section

open Classical

namespace Erdos99

def IsCSide (S : Finset ℂ) (a b : ℂ) : Prop :=
  a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ ∀ c ∈ S, 0 ≤ (wc a b c).im

def cSides (S : Finset ℂ) : Finset (Sym2 ℂ) :=
  ((S ×ˢ S).filter (fun p => IsCSide S p.1 p.2)).image (fun p => s(p.1, p.2))

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

lemma exists_side_of_frontier {S : Finset ℂ} (hint : (interior (convexHull ℝ (S : Set ℂ))).Nonempty)
    {m : ℂ} (hm : m ∈ convexHull ℝ (S : Set ℂ)) (hmi : m ∉ interior (convexHull ℝ (S : Set ℂ)))
    (hmS : m ∉ S) : ∃ a b, IsCSide S a b ∧ m ∈ openSegment ℝ a b := by
  set K := convexHull ℝ (S : Set ℂ) with hKdef
  have hKcl : IsClosed K := S.finite_toSet.isCompact_convexHull ℝ |>.isClosed
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
      · rw [hwz y hy hyT, zero_mul])
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, hsumσ] at h
    linarith
  have hσb : 0 ≤ σ b := by
    have h := Finset.sum_nonneg (s := S) (f := fun y => w y * (σ b - σ y)) (fun y hy => by
      by_cases hyT : f y = f m
      · exact mul_nonneg (hw0 y hy) (sub_nonneg.2 (hbmax y (Finset.mem_filter.2 ⟨hy, hyT⟩)))
      · rw [hwz y hy hyT, zero_mul])
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

lemma extremePoints_closure_face_subset (hP : IsPlaneGraph V E) {F : Set ℂ} (hF : F ∈ faces V E)
    (hFc : Convex ℝ F) {p : ℂ} (hp : p ∈ extremePoints ℝ (closure F)) : p ∈ V := by
  have hFo := isOpen_face hF
  have hFne : F.Nonempty := by
    obtain ⟨x, hx, rfl⟩ := mem_faces_iff.1 hF
    exact ⟨x, mem_connectedComponentIn hx⟩
  have hpK := hp.1
  have hext := (mem_extremePoints.1 hp).2

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
    rw [← hSe, (S.finite_toSet.isCompact_convexHull ℝ |>.isClosed).closure_eq] at h1
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

section ContactFan

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
  ·
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
  ·
    intro p hp q hq hd
    left
    have hpq : p ≠ q := by
      rintro rfl; simp at hd; exact (hX.diam_pos hn).ne' hd.symm
    have hpx : p ≠ x := by
      rintro rfl; exact hxH (mem_hullVertices_of_diam hp hq hpq hd)
    have hqx : q ≠ x := by
      rintro rfl; exact hxH (mem_hullVertices_of_diam hq hp hpq.symm (by rw [dist_comm]; exact hd))
    simp [hpx, hqx]
  ·
    have hcard : 1 < X.card := by rw [hX.1.1]; omega
    obtain ⟨q, hq, hqx⟩ := Finset.exists_mem_ne hcard x
    exact ⟨x, hyX, q, hq, by simp [hqx, hw]⟩

lemma FanCondition.mono {V : Finset ℂ} {E E' : Finset (Sym2 ℂ)} (h : FanCondition V E)
    (hEE : E ⊆ E') : FanCondition V E' := by
  intro y hy hext ν hν
  obtain ⟨y', h1, h2⟩ := h y hy hext ν hν
  exact ⟨y', hEE h1, h2⟩

theorem augEdges_fan {n : ℕ} (hn : 2 ≤ n) (hfm : numOptimalClasses n < ⊤) {X : Finset Plane}
    (hX : IsOptimal n X) : FanCondition (cVerts X) (augEdges X) :=
  (cUnitEdges_fan hn hfm hX).mono Finset.subset_union_left

theorem contactFace_convex :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      ∀ F ∈ contactFaces X, Convex ℝ F := by
  filter_upwards [eventually_ge_atTop 2] with n hn hfm X hX F hF
  exact boundedFace_convex (cUnitEdges_isPlaneGraph hX.1.2) (cUnitEdges_fan hn hfm hX) hF.1 hF.2

theorem augFace_convex :
    ∀ᶠ n in atTop, numOptimalClasses n < ⊤ → ∀ X, IsOptimal n X →
      ∀ F ∈ augFaces X, Convex ℝ F := by
  filter_upwards [augEdges_isPlaneGraph, eventually_ge_atTop 2] with n hP hn hfm X hX F hF
  exact boundedFace_convex (hP hfm X hX) (augEdges_fan hn hfm hX) hF.1 hF.2

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
    rcases Sym2.eq_iff.1 h with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Prod.ext e1 e2
    · exfalso
      change a = b' at e1
      change b = a' at e2
      subst e1 e2
      refine not_interior_of_line hs.2.2.1 (fun c hc => ?_) hint
      have f1 := hs.2.2.2 c hc
      have f2 := hs'.2.2.2 c hc
      rw [wc_im_swap] at f2
      linarith
  rw [h2, h1, card_ccwHullSides h3, hhv, hPcard]

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

lemma not_mem_hullSide_of_interior {X : Finset Plane} {e : Sym2 ℂ} (he : e ∈ hullSideEdges X)
    {z : ℂ} (hz : z ∈ interior (convexHull ℝ ((cVerts X : Finset ℂ) : Set ℂ))) :
    z ∉ edgeSeg e := by
  obtain ⟨v, w, hs, rfl⟩ := hullSideEdges_cases he
  intro hze
  rw [edgeSeg_mk] at hze
  have h1 := side_pos (isCSide_of_ccw hs) hz
  rw [wc_im_of_mem_segment hze] at h1
  exact lt_irrefl _ h1

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

section PolygonCycle

open scoped BigOperators Real
open EstablishedExternalResults Set Complex Filter Topology

@[expose] public noncomputable section

open Classical

namespace Erdos99

namespace PolyCycle

def tcr (u v : ℂ) : ℝ := u.re * v.im - u.im * v.re

def tdot (u v : ℂ) : ℝ := u.re * v.re + u.im * v.im

lemma wc_im_eq (a b z : ℂ) : (wc a b z).im = tcr (b - a) (z - a) / normSq (b - a) := by
  simp only [wc, div_im, tcr, sub_re, sub_im]; ring

lemma tdot_sq_add_tcr_sq (Y V : ℂ) : tdot Y V ^ 2 + tcr Y V ^ 2 = normSq Y * normSq V := by
  simp only [tdot, tcr, normSq_apply]; ring

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
  ·
    have hseg : x ∈ openSegment ℝ c y := by
      refine ⟨1 - t, t, by linarith, ht0, by ring, ?_⟩
      rw [hxe]; simp only [Complex.real_smul]; push_cast; ring
    exact absurd (extreme_eq hext hx hcK hyK hseg).1 (center_ne hext hc hx).symm
  · rw [hxe, heq]; simp
  ·
    have hseg : y ∈ openSegment ℝ c x := by
      refine ⟨1 - 1 / t, 1 / t, by rw [sub_pos, div_lt_one ht0]; exact hgt, by positivity,
        by ring, ?_⟩
      rw [hxe]; simp only [Complex.real_smul]
      have : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
      push_cast
      field_simp
      ring
    exact absurd (extreme_eq hext hy hcK hxK hseg).1 (center_ne hext hc hy).symm

lemma side_succ_unique {a b b' : ℂ} (hs : IsCSide S a b) (hs' : IsCSide S a b') : b = b' := by
  have h1 := tcr_pos_of_side hc hs
  have h2 := tcr_pos_of_side hc hs'
  rcases lt_trichotomy (tcr (b - c) (b' - c)) 0 with hlt | heq | hgt
  · exact (not_mem_cone hext hc hs hs'.2.1 h2 (by
      have : tcr (b' - c) (b - c) = -tcr (b - c) (b' - c) := by simp only [tcr]; ring
      linarith)).elim
  · exact eq_of_same_ray hext hc hs.2.1 hs'.2.1 heq (tdot_pos_of_collinear h1 h2 heq)
  · exact (not_mem_cone hext hc hs' hs.2.1 h1 hgt).elim

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

section Cycle

variable {S : Finset ℂ} (hext : ∀ s ∈ S, s ∈ extremePoints ℝ (convexHull ℝ (S : Set ℂ)))
  (hint : (interior (convexHull ℝ (S : Set ℂ))).Nonempty)

include hext hint

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

section FaceCapacity

open scoped BigOperators Real
open EstablishedExternalResults Set Complex Filter Topology

@[expose] public noncomputable section

open Classical

namespace Erdos99

open Propagation

def orientedSides (X : Finset Plane) (F : Set ℂ) : Finset (ℂ × ℂ) :=
  ((cVerts X) ×ˢ (cVerts X)).filter (fun ab => s(ab.1, ab.2) ∈ bdryEdges (cUnitEdges X) F ∧
    ∀ z ∈ F, 0 < (wc ab.1 ab.2 z).im)

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
    dsimp only at this
    rw [← map_sub, ← LinearIsometryEquiv.apply_symm_apply toC e,
      LinearIsometryEquiv.inner_map_map] at this
    simpa [UnitPolygon.edge] using this
  have := Q.marked_card_le_markedCap hF.2 he' le_rfl hmark'
  calc (M.card : ℝ) ≤ M'.card := by exact_mod_cast hcard
    _ ≤ markedCap k := this

end Erdos99

end

end FaceCapacity

section TokenRouting

open scoped BigOperators Real
open Filter Topology

@[expose] public noncomputable section

open Classical

namespace Erdos99

open Propagation

namespace TokenProcess

variable {X : Finset Plane} (P : TokenProcess X)

def arrivals (j : ℕ) (F : Set ℂ) : Finset ((Plane × Plane) ⊕ Set ℂ) :=
  ((unitHullSides X).filter (fun p => P.start p = .face F)).disjSum
    (P.fin.toFinset.filter (fun G => P.out G = .face F ∧ emitted (faceSize X G) (P.faceArr j G) = 1))

lemma emitted_eq_zero_or_one (k a : ℕ) : emitted k a = 0 ∨ emitted k a = 1 := by
  unfold emitted; split_ifs <;> simp

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

structure Entry (X : Finset Plane) where

  src : Plane × Plane → ℂ × ℂ

  emit : Set ℂ → ℂ × ℂ

def Entry.edge {X : Finset Plane} (E : Entry X) : (Plane × Plane) ⊕ Set ℂ → ℂ × ℂ :=
  Sum.elim E.src E.emit

def MarkedArrivals (E : Entry X) (j : ℕ) (F : Set ℂ) : Prop :=
  Set.InjOn E.edge (P.arrivals j F) ∧ ∃ e : ℂ, ‖e‖ = 1 ∧ ∀ t ∈ P.arrivals j F,
    E.edge t ∈ orientedSides X F ∧ 19 / 20 ≤ inner ℝ ((E.edge t).2 - (E.edge t).1) e

end TokenProcess

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

def TokenProcess.trivial {X : Finset Plane} (hX : IsSeparated X) : TokenProcess X where
  fin := exceptionalFaces_finite hX
  start _ := .lost
  out _ := .lost

end Erdos99

end

end TokenRouting

section WindingJump

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

section Crosscut

open scoped BigOperators Real ComplexConjugate
open Set EstablishedExternalResults

@[expose] public noncomputable section

open Classical

namespace Erdos99

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

section CrosscutShore

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

section PortCap

open scoped BigOperators Real
open Set

@[expose] public noncomputable section

open Classical

namespace Erdos99

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

lemma det2_segment {d b p q y : Plane} (hy : y ∈ segment ℝ p q) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ y = p + t • (q - p) ∧
      det2 d (y - b) = (1 - t) * det2 d (p - b) + t * det2 d (q - b) := by
  obtain ⟨a, t, ha, ht, hat, rfl⟩ := hy
  refine ⟨t, ht, by linarith, ?_, ?_⟩
  · rw [show a = 1 - t by linarith]; module
  · rw [show a = 1 - t by linarith]
    simp only [det2, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]; ring

include hX hx hbx hxc hbc hε hhalf hdeg in

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

  rcases eq_or_lt_of_le ht0 with rfl | ht0'
  · simp only [zero_smul, add_zero] at hyt
    exact hcap p hp γ hγ (by linarith) (by rw [← hyt, show α = 1 - γ by linarith])
  rcases eq_or_lt_of_le ht1 with rfl | ht1'
  · rw [one_smul, add_sub_cancel] at hyt
    exact hcap q hq γ hγ (by linarith) (by rw [← hyt, show α = 1 - γ by linarith])

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

  obtain ⟨α, β, γ, hα, hβ, hγ, hs, hze⟩ := hzT
  have hFt0 : 0 < F t0 := by
    have hb' : Bf z = β := by
      simp only [hBf]; rw [hze, det2_comb_sub hs]; field_simp
    have hg' : Gf z = γ := by
      simp only [hGf]; rw [hze, det2_comb_sub' hs]; field_simp
    simp only [hF]; rw [← hzt, hb', hg']
    refine lt_min (by linarith) (lt_min hβ hγ)

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
  ·
    have hseg : y ∈ segment ℝ x c := ⟨Bf y, Gf y, hB0, hG0, by linarith, by
      rw [h0, zero_smul, zero_add] at hyc; exact hyc.symm⟩
    by_cases hpc : p = c
    · subst hpc
      exact hqx (eq_of_segments_from (by rw [dist_comm]; exact hxc) hpq
        (segment_symm ℝ x p ▸ hseg) hys hyp)
    · exact Set.disjoint_left.1 (unit_segments_disjoint hX hp hq hx hc hpq hxc hpx hpc hqx hqc)
        hys hseg
  ·
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
  ·
    have hseg : y ∈ segment ℝ b x := ⟨1 - Bf y - Gf y, Bf y, hA0, hB0, by linarith, by
      rw [h0, zero_smul, add_zero] at hyc; rw [h0]; exact hyc.symm⟩
    by_cases hpb : p = b
    · subst hpb
      exact hqx (eq_of_segments_from hbx hpq hseg hys hyp)
    · exact Set.disjoint_left.1 (unit_segments_disjoint hX hp hq hb hx hpq hbx hpb hpx hqb hqx)
        hys hseg

omit hX in

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

section PortRay

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
