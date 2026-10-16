module

public import Mathlib

namespace Erdos99Migration

public theorem reflTransGenSymmetric {α : Type*} {r : α → α → Prop}
    (hsym : ∀ a b, r a b → r b a) {a b : α}
    (h : Relation.ReflTransGen r a b) : Relation.ReflTransGen r b a := by
  induction h with
  | refl => exact .refl
  | tail _ hab ih => exact ih.head (hsym _ _ hab)

end Erdos99Migration

section Basic

open scoped BigOperators Real
open Filter

@[expose] public noncomputable section

open Classical

namespace Erdos99

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def IsSeparated (X : Finset Plane) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, x ≠ y → 1 ≤ dist x y

def diam (X : Finset Plane) : ℝ := Metric.diam (X : Set Plane)

def Admissible (n : ℕ) (X : Finset Plane) : Prop :=
  X.card = n ∧ IsSeparated X

def minDiam (n : ℕ) : ℝ := sInf (diam '' {X | Admissible n X})

def IsOptimal (n : ℕ) (X : Finset Plane) : Prop :=
  Admissible n X ∧ ∀ Y, Admissible n Y → diam X ≤ diam Y

def Congruent (X Y : Finset Plane) : Prop :=
  ∃ e : Plane ≃ᵢ Plane, X.image e = Y

def numOptimalClasses (n : ℕ) : ℕ∞ :=
  Set.encard {C : Set (Finset Plane) |
    ∃ X, IsOptimal n X ∧ C = {Y | IsOptimal n Y ∧ Congruent X Y}}

def HasUnitTriangle (X : Finset Plane) : Prop :=
  ∃ a ∈ X, ∃ b ∈ X, ∃ c ∈ X, dist a b = 1 ∧ dist b c = 1 ∧ dist a c = 1

def MinDistOne (X : Finset Plane) : Prop :=
  IsSeparated X ∧ ∃ x ∈ X, ∃ y ∈ X, dist x y = 1

def IsErdosOptimal (n : ℕ) (X : Finset Plane) : Prop :=
  X.card = n ∧ MinDistOne X ∧ ∀ Y : Finset Plane, Y.card = n → MinDistOne Y → diam X ≤ diam Y

def Erdos99Conjecture : Prop :=
  ∀ᶠ n in atTop, ∀ X : Finset Plane, IsErdosOptimal n X → HasUnitTriangle X

lemma dist_le_diam {X : Finset Plane} {x y : Plane} (hx : x ∈ X) (hy : y ∈ X) :
    dist x y ≤ diam X :=
  Metric.dist_le_diam_of_mem X.finite_toSet.isBounded hx hy

lemma dist_vec2 (a b c d : ℝ) : dist !₂[a, b] !₂[c, d] = √((a - c) ^ 2 + (b - d) ^ 2) := by
  rw [EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp [Real.dist_eq, sq_abs]

lemma exists_admissible (n : ℕ) : ∃ X, Admissible n X := by
  refine ⟨Finset.univ.image (fun i : Fin n => !₂[(i : ℝ), 0]), ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ ?_, Finset.card_univ, Fintype.card_fin]
    intro i j h
    have := congrArg (fun v : Plane => v 0) h
    simp at this
    exact Fin.ext (by exact_mod_cast this)
  · simp only [IsSeparated, Finset.mem_image, Finset.mem_univ, true_and]
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne
    have hij : (i : ℕ) ≠ j := by rintro h; exact hne (by rw [Fin.ext h])
    rw [dist_vec2, sub_self, sq (0:ℝ), mul_zero, add_zero, Real.sqrt_sq_eq_abs]
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · have : ((i:ℕ):ℝ) + 1 ≤ j := by exact_mod_cast h
      rw [le_abs]; right; linarith
    · have : ((j:ℕ):ℝ) + 1 ≤ i := by exact_mod_cast h
      rw [le_abs]; left; linarith

lemma exists_enum_of_admissible {n : ℕ} (hn : 0 < n) {Y : Finset Plane} (hY : Admissible n Y) :
    ∃ f : Fin n → Plane, (∀ i, ‖f i‖ ≤ diam Y) ∧ (∀ i j, i ≠ j → 1 ≤ dist (f i) (f j)) ∧
      ∀ i j, dist (f i) (f j) ≤ diam Y := by
  let e : Fin n ≃ Y := (Y.equivFin.trans (finCongr hY.1)).symm
  refine ⟨fun i => (e i : Plane) - e ⟨0, hn⟩, fun i => ?_, fun i j hij => ?_, fun i j => ?_⟩
  · rw [← dist_eq_norm]; exact dist_le_diam (e i).2 (e _).2
  · rw [dist_sub_right]
    exact hY.2 _ (e i).2 _ (e j).2 (fun h => hij (e.injective (Subtype.ext h)))
  · rw [dist_sub_right]; exact dist_le_diam (e i).2 (e j).2

lemma exists_isOptimal (n : ℕ) : ∃ X, IsOptimal n X := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨∅, ⟨rfl, by simp [IsSeparated]⟩, fun Y _ => ?_⟩
    simp [diam]; exact Metric.diam_nonneg
  obtain ⟨L, hL⟩ := exists_admissible n
  have hne : (Finset.univ : Finset (Fin n × Fin n)).Nonempty :=
    Finset.univ_nonempty_iff.2 ⟨⟨⟨0, hn⟩, ⟨0, hn⟩⟩⟩

  let g : (Fin n → Plane) → ℝ := fun f => Finset.univ.sup' hne (fun p => dist (f p.1) (f p.2))
  let M := diam L
  let K : Set (Fin n → Plane) :=
    Metric.closedBall 0 M ∩ {f | ∀ i j, i ≠ j → 1 ≤ dist (f i) (f j)}
  have hM : 0 ≤ M := Metric.diam_nonneg
  have mem_K : ∀ f : Fin n → Plane, (∀ i, ‖f i‖ ≤ M) →
      (∀ i j, i ≠ j → 1 ≤ dist (f i) (f j)) → f ∈ K := fun f h1 h2 =>
    ⟨by rw [mem_closedBall_zero_iff]; exact (pi_norm_le_iff_of_nonneg hM).2 h1, h2⟩
  have hKc : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded (Metric.isClosed_closedBall.inter ?_)
      (Metric.isBounded_closedBall.subset Set.inter_subset_left)
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_le continuous_const (by fun_prop)
  have hgc : Continuous g := Continuous.finset_sup'_apply hne (fun p _ => by fun_prop)
  obtain ⟨fL, hfL1, hfL2, hfL3⟩ := exists_enum_of_admissible hn hL
  obtain ⟨f, hfK, hfmin⟩ := hKc.exists_isMinOn ⟨fL, mem_K fL hfL1 hfL2⟩ hgc.continuousOn
  have hg_le : ∀ (h : Fin n → Plane) (C : ℝ), (∀ i j, dist (h i) (h j) ≤ C) → g h ≤ C :=
    fun h C hC => Finset.sup'_le _ _ fun p _ => hC p.1 p.2
  have hinj : Function.Injective f := fun i j hij => by
    by_contra h; have := hfK.2 i j h; rw [hij, dist_self] at this; linarith
  refine ⟨Finset.univ.image f, ⟨?_, ?_⟩, fun Y hY => ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  · simp only [IsSeparated, Finset.mem_image, Finset.mem_univ, true_and]
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne
    exact hfK.2 i j (fun h => hne (by rw [h]))
  have hdX : diam (Finset.univ.image f) ≤ g f := by
    have h0 : 0 ≤ g f := (dist_self _).symm.le.trans
      (Finset.le_sup' (fun p : Fin n × Fin n => dist (f p.1) (f p.2))
        (Finset.mem_univ (⟨0, hn⟩, ⟨0, hn⟩)))
    refine Metric.diam_le_of_forall_dist_le h0 ?_
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact Finset.le_sup' (fun p : Fin n × Fin n => dist (f p.1) (f p.2)) (Finset.mem_univ (i, j))
  refine hdX.trans ?_
  by_cases hYM : diam Y ≤ M
  · obtain ⟨fY, h1, h2, h3⟩ := exists_enum_of_admissible hn hY
    exact (hfmin (mem_K fY (fun i => (h1 i).trans hYM) h2)).trans (hg_le _ _ h3)
  · exact (hfmin (mem_K fL hfL1 hfL2)).trans ((hg_le _ _ hfL3).trans (le_of_not_ge hYM))

lemma minDiam_le_of_admissible {n : ℕ} {Y : Finset Plane} (hY : Admissible n Y) :
    minDiam n ≤ diam Y :=
  csInf_le ⟨0, by rintro _ ⟨Z, -, rfl⟩; exact Metric.diam_nonneg⟩ ⟨Y, hY, rfl⟩

lemma IsOptimal.diam_eq {n : ℕ} {X : Finset Plane} (hX : IsOptimal n X) :
    diam X = minDiam n := by
  have : IsLeast (diam '' {X | Admissible n X}) (diam X) :=
    ⟨⟨X, hX.1, rfl⟩, by rintro _ ⟨Y, hY, rfl⟩; exact hX.2 Y hY⟩
  exact this.csInf_eq.symm

lemma IsOptimal.diam_pos {n : ℕ} {X : Finset Plane} (hX : IsOptimal n X) (hn : 2 ≤ n) :
    0 < diam X := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 (hX.1.1 ▸ hn : 1 < X.card)
  exact one_pos.trans_le ((hX.1.2 x hx y hy hxy).trans (dist_le_diam hx hy))

lemma IsOptimal.minDistOne {n : ℕ} {X : Finset Plane} (hX : IsOptimal n X) (hn : 2 ≤ n) :
    MinDistOne X := by
  refine ⟨hX.1.2, ?_⟩
  by_contra hcon
  push_neg at hcon
  have hne : X.offDiag.Nonempty := by
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 (hX.1.1 ▸ hn : 1 < X.card)
    exact ⟨(x, y), Finset.mem_offDiag.2 ⟨hx, hy, hxy⟩⟩
  obtain ⟨d, hd⟩ : ∃ d, d = X.offDiag.inf' hne (fun p => dist p.1 p.2) := ⟨_, rfl⟩
  have hd1 : 1 < d := by
    rw [hd, Finset.lt_inf'_iff]
    rintro ⟨x, y⟩ hp
    obtain ⟨hx, hy, hxy⟩ := Finset.mem_offDiag.1 hp
    exact lt_of_le_of_ne (hX.1.2 x hx y hy hxy) (hcon x hx y hy).symm
  have hdle : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → d ≤ dist x y := fun x hx y hy hxy => by
    have hm : (x, y) ∈ X.offDiag := Finset.mem_offDiag.2 ⟨hx, hy, hxy⟩
    rw [hd]
    exact Finset.inf'_le (fun p : Plane × Plane => dist p.1 p.2) hm
  clear hd
  have hd0 : 0 < d := one_pos.trans hd1
  have hds : ∀ x y : Plane, dist (d⁻¹ • x) (d⁻¹ • y) = d⁻¹ * dist x y := fun x y => by
    rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hd0)]
  have hinj : Function.Injective (fun x : Plane => d⁻¹ • x) := by
    intro x y h
    have := hds x y
    simp only at h
    rw [h, dist_self] at this
    exact dist_eq_zero.1 ((mul_eq_zero.1 this.symm).resolve_left (inv_ne_zero hd0.ne'))
  have hadm : Admissible n (X.image (fun x => d⁻¹ • x)) := by
    refine ⟨by rw [Finset.card_image_of_injective _ hinj, hX.1.1], ?_⟩
    simp only [IsSeparated, Finset.mem_image]
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hne
    have hxy : x ≠ y := fun h => hne (by rw [h])
    rw [hds, ← div_eq_inv_mul, le_div_iff₀ hd0, one_mul]
    exact hdle x hx y hy hxy
  have hle := hX.2 _ hadm
  have hDpos := hX.diam_pos hn
  have : diam (X.image (fun x => d⁻¹ • x)) ≤ d⁻¹ * diam X := by
    refine Metric.diam_le_of_forall_dist_le (by positivity) ?_
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hds]
    exact mul_le_mul_of_nonneg_left (dist_le_diam hx hy) (by positivity)
  have : d⁻¹ * diam X < diam X := by
    rw [← div_eq_inv_mul, div_lt_iff₀ hd0]; nlinarith
  linarith

lemma isErdosOptimal_iff_isOptimal {n : ℕ} (hn : 2 ≤ n) (X : Finset Plane) :
    IsErdosOptimal n X ↔ IsOptimal n X := by
  constructor
  · rintro ⟨hc, hm, hmin⟩
    refine ⟨⟨hc, hm.1⟩, fun Y hY => ?_⟩
    obtain ⟨Z, hZ⟩ := exists_isOptimal n
    exact (hmin Z hZ.1.1 (hZ.minDistOne hn)).trans (hZ.2 Y hY)
  · intro hX
    exact ⟨hX.1.1, hX.minDistOne hn, fun Y hY hm => hX.2 Y ⟨hY, hm.1⟩⟩

lemma card_le_two_diam_add_one_sq {X : Finset Plane} (hX : IsSeparated X) :
    (X.card : ℝ) ≤ (2 * diam X + 1) ^ 2 := by
  rcases X.eq_empty_or_nonempty with rfl | ⟨x0, hx0⟩
  · simp; positivity
  set D := diam X
  have hD : 0 ≤ D := Metric.diam_nonneg
  have hdisj : (X : Set Plane).PairwiseDisjoint (fun x => Metric.ball x (1/2 : ℝ)) := by
    intro x hx y hy hxy
    exact Metric.ball_disjoint_ball (by have := hX x hx y hy hxy; linarith)
  have hsub : (⋃ x ∈ X, Metric.ball x (1/2 : ℝ)) ⊆ Metric.ball x0 (D + 1/2) := by
    refine Set.iUnion₂_subset fun x hx => Metric.ball_subset_ball' ?_
    have := dist_le_diam hx hx0; linarith
  have hmeas := MeasureTheory.measure_mono (μ := (MeasureTheory.volume : MeasureTheory.Measure Plane)) hsub
  rw [MeasureTheory.measure_biUnion_finset hdisj (fun _ _ => measurableSet_ball)] at hmeas
  simp only [MeasureTheory.Measure.addHaar_ball _ _ (by norm_num : (0:ℝ) ≤ 1/2),
    MeasureTheory.Measure.addHaar_ball _ _ (by positivity : (0:ℝ) ≤ D + 1/2), Finset.sum_const,
    finrank_euclideanSpace, Fintype.card_fin, nsmul_eq_mul] at hmeas
  have hpos : MeasureTheory.volume (Metric.ball (0 : Plane) 1) ≠ 0 :=
    (Metric.measure_ball_pos _ _ one_pos).ne'
  have hfin : MeasureTheory.volume (Metric.ball (0 : Plane) 1) ≠ ⊤ :=
    MeasureTheory.measure_ball_lt_top.ne
  rw [← mul_assoc, ENNReal.mul_le_mul_iff_left hpos hfin, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hmeas
  nlinarith

lemma tendsto_minDiam : Tendsto minDiam atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [eventually_gt_atTop ⌈(2 * |b| + 1) ^ 2⌉₊] with n hn
  obtain ⟨X, hX⟩ := exists_isOptimal n
  have h1 := card_le_two_diam_add_one_sq hX.1.2
  rw [hX.1.1, hX.diam_eq] at h1
  have h2 : (2 * |b| + 1) ^ 2 < n := (Nat.lt_of_ceil_lt hn)
  have h0 : 0 ≤ minDiam n := hX.diam_eq ▸ Metric.diam_nonneg
  by_contra hlt
  push_neg at hlt
  have : 2 * minDiam n + 1 < 2 * |b| + 1 := by linarith [le_abs_self b]
  nlinarith

lemma minDiam_le_sqrt (n : ℕ) : minDiam n ≤ √(2 * n) := by
  set s := Nat.sqrt n
  let G : Finset Plane := (Finset.range (s+1) ×ˢ Finset.range (s+1)).image
    (fun ij => !₂[(ij.1 : ℝ), ij.2])
  have hinj : Function.Injective (fun ij : ℕ × ℕ => !₂[(ij.1 : ℝ), ij.2]) := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    have h0 := congrArg (fun v : Plane => v 0) h
    have h1 := congrArg (fun v : Plane => v 1) h
    simp at h0 h1
    simp [h0, h1]
  have hG : n ≤ G.card := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_product, Finset.card_range]
    exact (Nat.lt_succ_sqrt n).le
  obtain ⟨Y, hYG, hYc⟩ := Finset.exists_subset_card_eq hG
  have memG : ∀ x ∈ G, ∃ a b : ℕ, a ≤ s ∧ b ≤ s ∧ x = !₂[(a : ℝ), b] := by
    intro x hx
    simp only [G, Finset.mem_image, Finset.mem_product, Finset.mem_range] at hx
    obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩ := hx
    exact ⟨a, b, by omega, by omega, rfl⟩
  have hsq : (s : ℝ) ^ 2 ≤ n := by exact_mod_cast Nat.sqrt_le' n
  have one_le : ∀ a c : ℕ, a ≠ c → (1:ℝ) ≤ ((a:ℝ) - c) ^ 2 := by
    intro a c hac
    rcases Nat.lt_or_gt_of_ne hac with h | h
    · have : (a:ℝ) + 1 ≤ c := by exact_mod_cast h
      nlinarith
    · have : (c:ℝ) + 1 ≤ a := by exact_mod_cast h
      nlinarith
  have hadm : Admissible n Y := by
    refine ⟨hYc, fun x hx y hy hxy => ?_⟩
    obtain ⟨a, b, -, -, rfl⟩ := memG x (hYG hx)
    obtain ⟨c, d, -, -, rfl⟩ := memG y (hYG hy)
    rw [dist_vec2, Real.one_le_sqrt]
    by_cases hac : a = c
    · subst hac
      have := one_le b d (fun h => hxy (by rw [h]))
      nlinarith
    · have := one_le a c hac
      nlinarith
  refine (minDiam_le_of_admissible hadm).trans
    (Metric.diam_le_of_forall_dist_le (by positivity) ?_)
  intro x hx y hy
  obtain ⟨a, b, ha, hb, rfl⟩ := memG x (hYG hx)
  obtain ⟨c, d, hc, hd, rfl⟩ := memG y (hYG hy)
  rw [dist_vec2]
  apply Real.sqrt_le_sqrt
  have ha' : (a:ℝ) ≤ s := by exact_mod_cast ha
  have hb' : (b:ℝ) ≤ s := by exact_mod_cast hb
  have hc' : (c:ℝ) ≤ s := by exact_mod_cast hc
  have hd' : (d:ℝ) ≤ s := by exact_mod_cast hd
  have h1 : ((a:ℝ) - c) ^ 2 ≤ (s:ℝ) ^ 2 := by
    apply sq_le_sq' <;> nlinarith [(Nat.cast_nonneg a : (0:ℝ) ≤ a), (Nat.cast_nonneg c : (0:ℝ) ≤ c)]
  have h2 : ((b:ℝ) - d) ^ 2 ≤ (s:ℝ) ^ 2 := by
    apply sq_le_sq' <;> nlinarith [(Nat.cast_nonneg b : (0:ℝ) ≤ b), (Nat.cast_nonneg d : (0:ℝ) ≤ d)]
  linarith

lemma exists_spread_of_separated_real (S : Finset ℝ) (hS : S.Nonempty)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|) :
    ∃ x ∈ S, ∃ y ∈ S, (S.card : ℝ) - 1 ≤ y - x := by
  induction S using Finset.induction_on_max with
  | empty => simp at hS
  | insert a s hlt ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · exact ⟨a, by simp, a, by simp, by simp⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := ih hs (fun x hx y hy h =>
      hsep x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) h)
    have hya := hlt y hy
    have h1 := hsep a (Finset.mem_insert_self _ _) y (Finset.mem_insert_of_mem hy) hya.ne'
    rw [abs_of_pos (sub_pos.2 hya)] at h1
    have hcard : ((insert a s).card : ℝ) = s.card + 1 := by
      rw [Finset.card_insert_of_notMem (fun h => (hlt a h).false)]; push_cast; ring
    exact ⟨x, Finset.mem_insert_of_mem hx, a, Finset.mem_insert_self _ _, by linarith⟩

lemma diam_ge_of_collinear {X : Finset Plane} (hX : IsSeparated X)
    (hcol : Collinear ℝ (X : Set Plane)) : (X.card : ℝ) - 1 ≤ diam X := by
  have hD0 : 0 ≤ diam X := Metric.diam_nonneg
  rcases X.eq_empty_or_nonempty with rfl | ⟨p0, hp0⟩
  · simp; linarith
  obtain ⟨v, hv⟩ := (collinear_iff_of_mem (Finset.mem_coe.2 hp0)).1 hcol

  let φ : Plane → ℝ := fun p => inner ℝ (p - p0) v
  have key : ∀ p ∈ X, ∀ q ∈ X, |φ p - φ q| = dist p q * ‖v‖ := by
    intro p hp q hq
    obtain ⟨r, hr⟩ := hv p hp
    obtain ⟨t, ht⟩ := hv q hq
    simp only [vadd_eq_add] at hr ht
    have : p - q = (r - t) • v := by rw [hr, ht, sub_smul]; abel
    simp only [φ, ← inner_sub_left, sub_sub_sub_cancel_right, this, dist_eq_norm,
      inner_smul_left, real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs]
    simp [abs_mul, sq]
    ring
  by_cases hv0 : v = 0
  · have : X.card ≤ 1 := Finset.card_le_one.2 fun p hp q hq => by
      obtain ⟨r, hr⟩ := hv p hp
      obtain ⟨t, ht⟩ := hv q hq
      rw [hr, ht, hv0]; simp
    have : (X.card : ℝ) ≤ 1 := by exact_mod_cast this
    linarith
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
  have hinj : Set.InjOn φ X := fun p hp q hq h => by
    have := key p hp q hq
    rw [h, sub_self, abs_zero] at this
    exact dist_eq_zero.1 ((mul_eq_zero.1 this.symm).resolve_right hvpos.ne')
  obtain ⟨_, hx, _, hy, hxy⟩ := exists_spread_of_separated_real ((X.image φ).image (· / ‖v‖))
    (by simp; exact ⟨p0, hp0⟩) (by
      simp only [Finset.mem_image]
      rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩ _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩ hne
      have hpq : p ≠ q := fun h => hne (by rw [h])
      rw [← sub_div, abs_div, abs_of_pos hvpos, key p hp q hq, mul_div_assoc,
        div_self hvpos.ne', mul_one]
      exact hX p hp q hq hpq)
  simp only [Finset.mem_image] at hx hy
  obtain ⟨_, ⟨p, hp, rfl⟩, rfl⟩ := hx
  obtain ⟨_, ⟨q, hq, rfl⟩, rfl⟩ := hy
  have hcard : ((X.image φ).image (· / ‖v‖)).card = X.card := by
    rw [Finset.card_image_of_injective _ (fun a b h => by
      simpa [div_left_inj' hvpos.ne'] using h), Finset.card_image_of_injOn hinj]
  rw [hcard] at hxy
  have h2 : φ q / ‖v‖ - φ p / ‖v‖ ≤ dist q p := by
    rw [← sub_div, div_le_iff₀ hvpos, ← key q hq p hp]; exact le_abs_self _
  linarith [dist_le_diam hq hp]

lemma eventually_not_collinear :
    ∀ᶠ n in atTop, ∀ X, IsOptimal n X → ¬ Collinear ℝ (X : Set Plane) := by
  filter_upwards [eventually_ge_atTop 4] with n hn X hX hcol
  have h1 := diam_ge_of_collinear hX.1.2 hcol
  rw [hX.1.1, hX.diam_eq] at h1
  have h2 := minDiam_le_sqrt n
  have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have h3 : √(2 * n) < n - 1 := by
    rw [Real.sqrt_lt' (by linarith)]; nlinarith
  linarith

def unitEdges (X : Finset Plane) : Finset (Sym2 Plane) :=
  ((X ×ˢ X).filter (fun p => dist p.1 p.2 = 1)).image (fun p => s(p.1, p.2))

def diamPairs (X : Finset Plane) : Finset (Sym2 Plane) :=
  ((X ×ˢ X).filter (fun p => p.1 ≠ p.2 ∧ dist p.1 p.2 = diam X)).image (fun p => s(p.1, p.2))

def hullVertices (X : Finset Plane) : Finset Plane :=
  X.filter (fun x => x ∈ Set.extremePoints ℝ (convexHull ℝ (X : Set Plane)))

def contactGraph (X : Finset Plane) : SimpleGraph X where
  Adj x y := dist (x : Plane) y = 1
  symm := ⟨fun x y h => by simpa [dist_comm] using h⟩
  loopless := ⟨fun x h => by simp at h⟩

def rot (x : Plane) : Plane := !₂[-(x 1), x 0]

def IsTrivialVelocity (X : Finset Plane) (v : Plane → Plane) : Prop :=
  ∃ ω : ℝ, ∃ w : Plane, ∀ x ∈ X, v x = ω • rot x + w

def aStar : ℝ := Real.sqrt 3 / 2

def cDensity : ℝ := π / (2 * Real.sqrt 3)

end Erdos99
end

end Basic

section DiamGraph

open scoped BigOperators Real
open Filter

@[expose] public noncomputable section

open Classical

namespace Erdos99

def det2 (u v : Plane) : ℝ := u 0 * v 1 - u 1 * v 0

lemma dist_sq_coord (p q : Plane) : dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by
  rw [EuclideanSpace.dist_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]
  simp [Real.dist_eq, sq_abs]

lemma mem_hullVertices_of_diam {X : Finset Plane} {x y : Plane} (hx : x ∈ X) (hy : y ∈ X)
    (hxy : x ≠ y) (hd : dist x y = diam X) : x ∈ hullVertices X := by
  refine Finset.mem_filter.2 ⟨hx, mem_extremePoints.2 ⟨subset_convexHull ℝ _ hx, ?_⟩⟩
  have hD : 0 < diam X := hd ▸ dist_pos.2 hxy
  have hsub : convexHull ℝ (X : Set Plane) ⊆ Metric.closedBall y (diam X) :=
    convexHull_min (fun z hz => Metric.mem_closedBall.2 (dist_le_diam hz hy))
      (convex_closedBall _ _)
  intro x₁ h₁ x₂ h₂ hseg
  by_cases h12 : x₁ = x₂
  · subst h12
    rw [openSegment_same] at hseg
    exact ⟨hseg.symm, hseg.symm⟩
  · have := (strictConvex_closedBall ℝ y (diam X)).openSegment_subset (hsub h₁) (hsub h₂) h12 hseg
    rw [interior_closedBall _ hD.ne'] at this
    exact absurd (Metric.mem_ball.1 this) (by rw [hd]; exact lt_irrefl _)

noncomputable def diamNbrs (X : Finset Plane) (x : Plane) : Finset Plane :=
  X.filter (fun y => dist x y = diam X ∧ y ≠ x)

lemma far_aux (a1 a2 b1 b2 e1 e2 D : ℝ) (hD : 0 < D)
    (ha : a1 ^ 2 + a2 ^ 2 = D ^ 2) (hb : b1 ^ 2 + b2 ^ 2 = D ^ 2) (he : e1 ^ 2 + e2 ^ 2 = D ^ 2)
    (h1 : 0 < a1 * e2 - a2 * e1) (h2 : 0 < e1 * b2 - e2 * b1) :
    D ^ 2 < (a1 - e1 - b1) ^ 2 + (a2 - e2 - b2) ^ 2 := by
  have k1 : 0 ≤ (D ^ 2 - (a1 * e1 + a2 * e2)) * (D ^ 2 + (b1 * e1 + b2 * e2)) := by
    apply mul_nonneg <;> nlinarith [sq_nonneg (a1 - e1), sq_nonneg (a2 - e2), sq_nonneg (b1 + e1),
      sq_nonneg (b2 + e2)]
  have k2 := mul_pos h1 h2
  have key : D ^ 2 * ((a1 - e1 - b1) ^ 2 + (a2 - e2 - b2) ^ 2 - D ^ 2) =
      2 * ((D ^ 2 - (a1 * e1 + a2 * e2)) * (D ^ 2 + (b1 * e1 + b2 * e2))) +
        2 * ((a1 * e2 - a2 * e1) * (e1 * b2 - e2 * b1)) := by
    have hD2 : D ^ 2 = e1 ^ 2 + e2 ^ 2 := he.symm
    rw [show (a1 - e1 - b1) ^ 2 + (a2 - e2 - b2) ^ 2 = (a1 ^ 2 + a2 ^ 2) + (e1 ^ 2 + e2 ^ 2) +
      (b1 ^ 2 + b2 ^ 2) - 2 * (a1 * e1 + a2 * e2) - 2 * (a1 * b1 + a2 * b2) +
        2 * (e1 * b1 + e2 * b2) by ring, ha, hb, he]
    rw [hD2]; ring
  have : 0 < D ^ 2 * ((a1 - e1 - b1) ^ 2 + (a2 - e2 - b2) ^ 2 - D ^ 2) := by rw [key]; linarith
  have := (pos_iff_pos_of_mul_pos this).1 (by positivity)
  linarith

lemma inner_pos_aux (u1 u2 v1 v2 D : ℝ) (hu : u1 ^ 2 + u2 ^ 2 = D ^ 2)
    (hv : v1 ^ 2 + v2 ^ 2 = D ^ 2) (huv : (u1 - v1) ^ 2 + (u2 - v2) ^ 2 ≤ D ^ 2) :
    D ^ 2 / 2 ≤ u1 * v1 + u2 * v2 := by nlinarith

lemma parallel_aux (u1 u2 v1 v2 D : ℝ) (hD : 0 < D) (hu : u1 ^ 2 + u2 ^ 2 = D ^ 2)
    (hv : v1 ^ 2 + v2 ^ 2 = D ^ 2) (huv : (u1 - v1) ^ 2 + (u2 - v2) ^ 2 ≤ D ^ 2)
    (hdet : u1 * v2 - u2 * v1 = 0) : u1 = v1 ∧ u2 = v2 := by
  have hp := inner_pos_aux u1 u2 v1 v2 D hu hv huv
  have lag : (u1 * v1 + u2 * v2) ^ 2 + (u1 * v2 - u2 * v1) ^ 2 =
      (u1 ^ 2 + u2 ^ 2) * (v1 ^ 2 + v2 ^ 2) := by ring
  rw [hdet, hu, hv] at lag
  have hD2 : 0 < D ^ 2 := by positivity
  have hin : u1 * v1 + u2 * v2 = D ^ 2 := by
    have : (u1 * v1 + u2 * v2 - D ^ 2) * (u1 * v1 + u2 * v2 + D ^ 2) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · nlinarith
  have hz : (u1 - v1) ^ 2 + (u2 - v2) ^ 2 = 0 := by nlinarith
  constructor <;> nlinarith [sq_nonneg (u1 - v1), sq_nonneg (u2 - v2)]

lemma trans_aux (u1 u2 v1 v2 w1 w2 D : ℝ) (hv : v1 ^ 2 + v2 ^ 2 = D ^ 2) (hD : 0 < D)
    (i1 : 0 < u1 * v1 + u2 * v2) (i2 : 0 < v1 * w1 + v2 * w2)
    (h1 : 0 < u1 * v2 - u2 * v1) (h2 : 0 < v1 * w2 - v2 * w1) : 0 < u1 * w2 - u2 * w1 := by
  have key : (u1 * w2 - u2 * w1) * (v1 ^ 2 + v2 ^ 2) =
      (u1 * v2 - u2 * v1) * (v1 * w1 + v2 * w2) + (v1 * w2 - v2 * w1) * (u1 * v1 + u2 * v2) := by
    ring
  rw [hv] at key
  have : 0 < (u1 * w2 - u2 * w1) * D ^ 2 := by rw [key]; positivity
  exact (pos_iff_pos_of_mul_pos this).2 (by positivity)

lemma diam_far {x y x' y' : Plane} {D : ℝ} (hD : 0 < D) (hxy : dist x y = D)
    (hxx : dist x x' = D) (hyy : dist y y' = D)
    (h1 : 0 < det2 (x' - x) (y - x)) (h2 : 0 < det2 (y' - y) (x - y)) : D < dist x' y' := by
  have e1 := dist_sq_coord x y; have e2 := dist_sq_coord x x'; have e3 := dist_sq_coord y y'
  rw [hxy] at e1; rw [hxx] at e2; rw [hyy] at e3
  simp only [det2, PiLp.sub_apply] at h1 h2
  have := far_aux (x' 0 - x 0) (x' 1 - x 1) (y' 0 - y 0) (y' 1 - y 1) (y 0 - x 0) (y 1 - x 1) D hD
    (by rw [e2]; ring) (by rw [e3]; ring) (by rw [e1]; ring) h1 (by linarith)
  have hlt : D ^ 2 < dist x' y' ^ 2 := by rw [dist_sq_coord]; convert this using 2 <;> ring
  exact lt_of_pow_lt_pow_left₀ 2 dist_nonneg hlt

lemma finset_exists_first {α : Type*} (s : Finset α) (hs : s.Nonempty) (r : α → α → Prop)
    (htrans : ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, r a b → r b c → r a c)
    (htot : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → r a b ∨ r b a) :
    ∃ m ∈ s, ∀ y ∈ s, y ≠ m → r m y := by
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert a t hat ih =>
    rcases t.eq_empty_or_nonempty with rfl | ht
    · exact ⟨a, by simp, fun y hy hne => by simp at hy; exact absurd hy hne⟩
    obtain ⟨m, hm, hmin⟩ := ih ht
      (fun a ha b hb c hc => htrans a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb)
        c (Finset.mem_insert_of_mem hc))
      (fun a ha b hb => htot a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb))
    have ham : a ≠ m := fun h => hat (h ▸ hm)
    rcases htot a (Finset.mem_insert_self _ _) m (Finset.mem_insert_of_mem hm) ham with h | h
    · refine ⟨a, Finset.mem_insert_self _ _, fun y hy hne => ?_⟩
      have hyt : y ∈ t := (Finset.mem_insert.1 hy).resolve_left hne
      by_cases hym : y = m
      · exact hym ▸ h
      · exact htrans a (Finset.mem_insert_self _ _) m (Finset.mem_insert_of_mem hm) y hy h
          (hmin y hyt hym)
    · refine ⟨m, Finset.mem_insert_of_mem hm, fun y hy hne => ?_⟩
      rcases Finset.mem_insert.1 hy with rfl | hyt
      · exact h
      · exact hmin y hyt hne

lemma exists_cw_neighbor (X : Finset Plane) (x : Plane) (hN : (diamNbrs X x).Nonempty) :
    ∃ m ∈ diamNbrs X x, ∀ y ∈ diamNbrs X x, y ≠ m → 0 < det2 (m - x) (y - x) := by
  have mem : ∀ y ∈ diamNbrs X x, y ∈ X ∧ dist x y = diam X ∧ y ≠ x := fun y hy => by
    simpa [diamNbrs] using hy
  have nrm : ∀ y ∈ diamNbrs X x, (y 0 - x 0) ^ 2 + (y 1 - x 1) ^ 2 = diam X ^ 2 := fun y hy => by
    rw [← (mem y hy).2.1, dist_sq_coord]; ring
  have close : ∀ y ∈ diamNbrs X x, ∀ z ∈ diamNbrs X x,
      (y 0 - x 0 - (z 0 - x 0)) ^ 2 + (y 1 - x 1 - (z 1 - x 1)) ^ 2 ≤ diam X ^ 2 :=
    fun y hy z hz => by
      have := pow_le_pow_left₀ dist_nonneg (dist_le_diam (mem y hy).1 (mem z hz).1) 2
      rw [dist_sq_coord] at this
      convert this using 2 <;> ring
  obtain ⟨y0, hy0⟩ := hN
  have hD : 0 < diam X := (mem y0 hy0).2.1 ▸ dist_pos.2 (mem y0 hy0).2.2.symm
  have inner_pos : ∀ y ∈ diamNbrs X x, ∀ z ∈ diamNbrs X x,
      0 < (y 0 - x 0) * (z 0 - x 0) + (y 1 - x 1) * (z 1 - x 1) := fun y hy z hz => by
    have := inner_pos_aux _ _ _ _ _ (nrm y hy) (nrm z hz) (close y hy z hz)
    have : 0 < diam X ^ 2 / 2 := by positivity
    linarith
  apply finset_exists_first _ ⟨y0, hy0⟩
  · intro a ha b hb c hc hab hbc
    simp only [det2, PiLp.sub_apply] at hab hbc ⊢
    exact trans_aux _ _ _ _ _ _ _ (nrm b hb) hD (inner_pos a ha b hb) (inner_pos b hb c hc) hab hbc
  · intro a ha b hb hab
    simp only [det2, PiLp.sub_apply]
    by_contra hcon
    push_neg at hcon
    have hdet : (a 0 - x 0) * (b 1 - x 1) - (a 1 - x 1) * (b 0 - x 0) = 0 := by linarith
    obtain ⟨h0, h1⟩ := parallel_aux _ _ _ _ _ hD (nrm a ha) (nrm b hb) (close a ha b hb) hdet
    exact hab (by ext i; fin_cases i <;> simp <;> linarith)

theorem diamPairs_card_le_hullVertices (X : Finset Plane) :
    (diamPairs X).card ≤ (hullVertices X).card := by
  choose! g hg using fun x (h : (diamNbrs X x).Nonempty) => exists_cw_neighbor X x h
  have hsub : diamPairs X ⊆ (hullVertices X).image (fun v => s(v, g v)) := by
    intro p hp
    simp only [diamPairs, Finset.mem_image, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨x, y⟩, ⟨⟨hx, hy⟩, hxy, hd⟩, rfl⟩ := hp
    have hyN : y ∈ diamNbrs X x := by simp [diamNbrs, hy, hd, hxy.symm]
    have hxN : x ∈ diamNbrs X y := by simp [diamNbrs, hx, dist_comm, hd, hxy]
    obtain ⟨hgx, hgx'⟩ := hg x ⟨y, hyN⟩
    obtain ⟨hgy, hgy'⟩ := hg y ⟨x, hxN⟩
    simp only [Finset.mem_image]
    by_cases h1 : g x = y
    · exact ⟨x, mem_hullVertices_of_diam hx hy hxy hd, by rw [h1]⟩
    by_cases h2 : g y = x
    · refine ⟨y, mem_hullVertices_of_diam hy hx hxy.symm (by rw [dist_comm, hd]), ?_⟩
      rw [h2, Sym2.eq_swap]
    exfalso
    have d1 := hgx' y hyN (Ne.symm h1)
    have d2 := hgy' x hxN (Ne.symm h2)
    have m1 : g x ∈ X ∧ dist x (g x) = diam X := by
      simp only [diamNbrs, Finset.mem_filter] at hgx; exact ⟨hgx.1, hgx.2.1⟩
    have m2 : g y ∈ X ∧ dist y (g y) = diam X := by
      simp only [diamNbrs, Finset.mem_filter] at hgy; exact ⟨hgy.1, hgy.2.1⟩
    have hD : 0 < diam X := hd ▸ dist_pos.2 hxy
    have := diam_far hD hd m1.2 m2.2 d1 d2
    exact absurd (dist_le_diam m1.1 m2.1) (not_le.2 this)
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

end Erdos99
end

end DiamGraph

section Tracks

open scoped BigOperators Real
open Filter

@[expose] public noncomputable section

open Classical

namespace Erdos99

def rhombi (X : Finset Plane) : Finset (Finset Plane) :=
  (X.powersetCard 4).filter (fun S => ∃ a b c d : Plane, S = {a, b, c, d} ∧
    dist a b = 1 ∧ dist b c = 1 ∧ dist c d = 1 ∧ dist d a = 1)

lemma rhombus_diagonals_gt_one {X : Finset Plane} (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X)
    {a b c d : Plane} (hS : ({a, b, c, d} : Finset Plane) ∈ rhombi X)
    (hab : dist a b = 1) (hbc : dist b c = 1) (hcd : dist c d = 1) (hda : dist d a = 1) :
    1 < dist a c ∧ 1 < dist b d := by
  obtain ⟨hP, -⟩ := Finset.mem_filter.1 hS
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.1 hP
  have mem : ∀ x ∈ ({a, b, c, d} : Finset Plane), x ∈ X := fun x hx => hsub hx
  have ha := mem a (by simp); have hb := mem b (by simp)
  have hc := mem c (by simp); have hd := mem d (by simp)
  have hac : a ≠ c := by
    rintro rfl
    have : ({a, b, a, d} : Finset Plane).card ≤ 3 := by
      have : ({a, b, a, d} : Finset Plane) = {a, b, d} := by ext; simp; tauto
      rw [this]; exact Finset.card_le_three
    omega
  have hbd : b ≠ d := by
    rintro rfl
    have : ({a, b, c, b} : Finset Plane).card ≤ 3 := by
      have : ({a, b, c, b} : Finset Plane) = {a, b, c} := by ext; simp; tauto
      rw [this]; exact Finset.card_le_three
    omega

  exact ⟨lt_of_le_of_ne (hX a ha c hc hac) fun h => htri ⟨a, ha, b, hb, c, hc, hab, hbc, h.symm⟩,
    lt_of_le_of_ne (hX b hb d hd hbd) fun h => htri ⟨b, hb, c, hc, d, hd, hbc, hcd, h.symm⟩⟩

def OppositeSides (X : Finset Plane) (e e' : Sym2 Plane) : Prop :=
  ∃ a b c d : Plane, ({a, b, c, d} : Finset Plane) ∈ rhombi X ∧
    dist a b = 1 ∧ dist b c = 1 ∧ dist c d = 1 ∧ dist d a = 1 ∧ e = s(a, b) ∧ e' = s(c, d)

def rhombusEdges (X : Finset Plane) : Finset (Sym2 Plane) :=
  (unitEdges X).filter (fun e => ∃ e', OppositeSides X e e')

def trackOf (X : Finset Plane) (e : Sym2 Plane) : Finset (Sym2 Plane) :=
  (rhombusEdges X).filter (fun e' => Relation.EqvGen (OppositeSides X) e e')

def tracks (X : Finset Plane) : Finset (Finset (Sym2 Plane)) :=
  (rhombusEdges X).image (trackOf X)

def Crosses (T : Finset (Sym2 Plane)) (R : Finset Plane) : Prop :=
  ∃ e ∈ T, ∀ x ∈ e, x ∈ R

def trackLength (X : Finset Plane) (T : Finset (Sym2 Plane)) : ℕ :=
  ((rhombi X).filter (Crosses T)).card

def crossingGraph (X : Finset Plane) : SimpleGraph (Finset (Sym2 Plane)) where
  Adj T T' := T ≠ T' ∧ T ∈ tracks X ∧ T' ∈ tracks X ∧ ∃ R ∈ rhombi X, Crosses T R ∧ Crosses T' R
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2.1, h.2.1, h.2.2.2.imp fun _ hR => ⟨hR.1, hR.2.2, hR.2.1⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

end Erdos99
end

end Tracks

section RhombusGeom

open scoped BigOperators Real

@[expose] public noncomputable section

open Classical

namespace Erdos99

lemma rh_lagrange_aux (p0 p1 q0 q1 : ℝ) (hpq : p0^2 + p1^2 = q0^2 + q1^2)
    (hdet : p0 * q1 - p1 * q0 = 0) : (p0 + q0 = 0 ∧ p1 + q1 = 0) ∨ (p0 = q0 ∧ p1 = q1) := by
  have key : ((p0 + q0)^2 + (p1 + q1)^2) * ((p0 - q0)^2 + (p1 - q1)^2) = 0 := by
    linear_combination (p0^2 + p1^2 - q0^2 - q1^2) * hpq + 4 * (p0 * q1 - p1 * q0) * hdet
  rcases mul_eq_zero.1 key with h | h
  · left; constructor <;> nlinarith
  · right; constructor <;> nlinarith

lemma rh_para_aux (a0 a1 b0 b1 c0 c1 d0 d1 : ℝ) (h1 : (a0-b0)^2+(a1-b1)^2=1)
    (h2 : (b0-c0)^2+(b1-c1)^2=1) (h3 : (c0-d0)^2+(c1-d1)^2=1) (h4 : (d0-a0)^2+(d1-a1)^2=1)
    (hac : a0 ≠ c0 ∨ a1 ≠ c1) (hbd : b0 ≠ d0 ∨ b1 ≠ d1) :
    a0 + c0 = b0 + d0 ∧ a1 + c1 = b1 + d1 := by
  have hp : (b0 - (a0 + c0)/2) * (a0 - c0) + (b1 - (a1 + c1)/2) * (a1 - c1) = 0 := by nlinarith
  have hq : (d0 - (a0 + c0)/2) * (a0 - c0) + (d1 - (a1 + c1)/2) * (a1 - c1) = 0 := by nlinarith
  have hpq : (b0 - (a0 + c0)/2)^2 + (b1 - (a1 + c1)/2)^2 =
      (d0 - (a0 + c0)/2)^2 + (d1 - (a1 + c1)/2)^2 := by nlinarith
  have hdet0 : ((b0 - (a0 + c0)/2) * (d1 - (a1 + c1)/2) - (b1 - (a1 + c1)/2) * (d0 - (a0 + c0)/2))
      * (a0 - c0) = 0 := by
    linear_combination (d1 - (a1 + c1)/2) * hp - (b1 - (a1 + c1)/2) * hq
  have hdet1 : ((b0 - (a0 + c0)/2) * (d1 - (a1 + c1)/2) - (b1 - (a1 + c1)/2) * (d0 - (a0 + c0)/2))
      * (a1 - c1) = 0 := by
    linear_combination -(d0 - (a0 + c0)/2) * hp + (b0 - (a0 + c0)/2) * hq
  have hdet : (b0 - (a0 + c0)/2) * (d1 - (a1 + c1)/2) - (b1 - (a1 + c1)/2) * (d0 - (a0 + c0)/2) = 0 := by
    rcases hac with h | h
    · exact (mul_eq_zero.1 hdet0).resolve_right (sub_ne_zero.2 h)
    · exact (mul_eq_zero.1 hdet1).resolve_right (sub_ne_zero.2 h)
  rcases rh_lagrange_aux _ _ _ _ hpq hdet with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · constructor <;> linarith
  · exfalso; rcases hbd with h | h
    · exact h (by linarith)
    · exact h (by linarith)

lemma plane_ext_iff {x y : Plane} : x = y ↔ x 0 = y 0 ∧ x 1 = y 1 := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h0, h1⟩; ext i; fin_cases i <;> simp [h0, h1]

lemma coord_ne_of_ne {x y : Plane} (h : x ≠ y) : x 0 ≠ y 0 ∨ x 1 ≠ y 1 := by
  by_contra hc; push_neg at hc; exact h (plane_ext_iff.2 hc)

lemma rhombus_parallelogram {a b c d : Plane} (hac : a ≠ c) (hbd : b ≠ d)
    (hab : dist a b = 1) (hbc : dist b c = 1) (hcd : dist c d = 1) (hda : dist d a = 1) :
    a + c = b + d := by
  have e1 := dist_sq_coord a b; have e2 := dist_sq_coord b c
  have e3 := dist_sq_coord c d; have e4 := dist_sq_coord d a
  rw [hab] at e1; rw [hbc] at e2; rw [hcd] at e3; rw [hda] at e4
  obtain ⟨h0, h1⟩ := rh_para_aux _ _ _ _ _ _ _ _ (by linarith) (by linarith) (by linarith)
    (by linarith) (coord_ne_of_ne hac) (coord_ne_of_ne hbd)
  rw [plane_ext_iff]; simp [h0, h1]

lemma distinct_of_card_four {a b c d : Plane} (h : ({a, b, c, d} : Finset Plane).card = 4) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  have key : ∀ x y z : Plane, ({a, b, c, d} : Finset Plane) ⊆ {x, y, z} → False := by
    intro x y z hs
    have := (Finset.card_le_card hs).trans Finset.card_le_three
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl
  · exact key a c d (by intro z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
  · exact key a b d (by intro z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
  · exact key a b c (by intro z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
  · exact key a b d (by intro z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
  · exact key a b c (by intro z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
  · exact key a b c (by intro z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)

lemma inner_sub_eq (x y z w : Plane) : inner ℝ (x - y) (z - w) =
    (x 0 - y 0) * (z 0 - w 0) + (x 1 - y 1) * (z 1 - w 1) := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]; ring

structure RhombusData (X : Finset Plane) (R : Finset Plane) (a b c d : Plane) : Prop where
  eq : R = {a, b, c, d}
  mem : ({a, b, c, d} : Finset Plane) ∈ rhombi X
  ha : a ∈ X
  hb : b ∈ X
  hc : c ∈ X
  hd : d ∈ X
  hab : dist a b = 1
  hbc : dist b c = 1
  hcd : dist c d = 1
  hda : dist d a = 1
  para : a + c = b + d
  diag1 : 1 < dist a c
  diag2 : 1 < dist b d
  distinct : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d

lemma exists_rhombusData {X : Finset Plane} (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X)
    {R : Finset Plane} (hR : R ∈ rhombi X) : ∃ a b c d, RhombusData X R a b c d := by
  obtain ⟨hP, a, b, c, d, rfl, hab, hbc, hcd, hda⟩ := Finset.mem_filter.1 hR
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.1 hP
  have hdist := distinct_of_card_four hcard
  obtain ⟨d1, d2⟩ := rhombus_diagonals_gt_one hX htri hR hab hbc hcd hda
  exact ⟨a, b, c, d, rfl, hR, hsub (by simp), hsub (by simp), hsub (by simp), hsub (by simp),
    hab, hbc, hcd, hda, rhombus_parallelogram hdist.2.1 hdist.2.2.2.2.1 hab hbc hcd hda, d1, d2,
    hdist⟩

lemma RhombusData.abs_inner_lt {X R} {a b c d : Plane} (h : RhombusData X R a b c d) :
    |inner ℝ (a - b) (b - c)| < 1 / 2 := by
  have e1 := dist_sq_coord a b; have e2 := dist_sq_coord b c
  have e5 := dist_sq_coord a c; have e6 := dist_sq_coord b d
  have hp := h.para
  rw [plane_ext_iff] at hp
  simp only [PiLp.add_apply] at hp
  rw [h.hab] at e1; rw [h.hbc] at e2
  have q5 : 1 < dist a c ^ 2 := by nlinarith [h.diag1]
  have q6 : 1 < dist b d ^ 2 := by nlinarith [h.diag2]
  rw [inner_sub_eq, abs_lt]
  have hd0 : d 0 = a 0 + c 0 - b 0 := by linarith [hp.1]
  have hd1 : d 1 = a 1 + c 1 - b 1 := by linarith [hp.2]
  rw [e6, hd0, hd1] at q6
  rw [e5] at q5
  constructor <;> nlinarith

def dv (e : Sym2 Plane) : Plane := e.out.1 - e.out.2

lemma dv_mk (x y : Plane) : dv s(x, y) = x - y ∨ dv s(x, y) = y - x := by
  have h : s((s(x, y)).out.1, (s(x, y)).out.2) = s(x, y) := by simp [Sym2.mk]
  rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left; simp [dv, h1, h2]
  · right; simp [dv, h1, h2]

def SameDir (e f : Sym2 Plane) : Prop := dv e = dv f ∨ dv e = -dv f

lemma SameDir.refl (e : Sym2 Plane) : SameDir e e := Or.inl rfl

lemma SameDir.symm {e f : Sym2 Plane} (h : SameDir e f) : SameDir f e := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by rw [h, neg_neg])

lemma SameDir.trans {e f g : Sym2 Plane} (h1 : SameDir e f) (h2 : SameDir f g) : SameDir e g := by
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact Or.inl (h1.trans h2)
  · exact Or.inr (h1.trans h2)
  · exact Or.inr (by rw [h1, h2])
  · exact Or.inl (by rw [h1, h2, neg_neg])

lemma abs_inner_of_sameDir {e e' f f' : Sym2 Plane} (he : SameDir e e') (hf : SameDir f f') :
    |inner ℝ (dv e) (dv f)| = |inner ℝ (dv e') (dv f')| := by
  rcases he with he | he <;> rcases hf with hf | hf <;>
    simp [he, hf, inner_neg_left, inner_neg_right, abs_neg]

lemma abs_inner_dv_mk (x y z w : Plane) :
    |inner ℝ (dv s(x, y)) (dv s(z, w))| = |inner ℝ (x - y) (z - w)| := by
  rcases dv_mk x y with h1 | h1 <;> rcases dv_mk z w with h2 | h2 <;> rw [h1, h2] <;>
    simp only [← neg_sub x y, ← neg_sub z w, inner_neg_left, inner_neg_right, abs_neg, neg_neg]

lemma norm_dv_of_mem_unitEdges {X : Finset Plane} {e : Sym2 Plane} (he : e ∈ unitEdges X) :
    ‖dv e‖ = 1 := by
  obtain ⟨⟨x, y⟩, hp, rfl⟩ := Finset.mem_image.1 he
  simp only [Finset.mem_filter] at hp
  rcases dv_mk x y with h | h <;> rw [h, ← dist_eq_norm]
  · exact hp.2
  · rw [dist_comm]; exact hp.2

lemma oppositeSides_sameDir {X : Finset Plane} {e e' : Sym2 Plane} (h : OppositeSides X e e') :
    SameDir e e' := by
  obtain ⟨a, b, c, d, hR, hab, hbc, hcd, hda, rfl, rfl⟩ := h
  have hcard := (Finset.mem_powersetCard.1 (Finset.mem_filter.1 hR).1).2
  have hd := distinct_of_card_four hcard
  have hp := rhombus_parallelogram hd.2.1 hd.2.2.2.2.1 hab hbc hcd hda
  have hcd' : c - d = -(a - b) := by
    rw [neg_sub, sub_eq_sub_iff_add_eq_add, add_comm c a, hp, add_comm]
  rcases dv_mk a b with h1 | h1 <;> rcases dv_mk c d with h2 | h2 <;> rw [SameDir, h1, h2]
  · right; rw [hcd', neg_neg]
  · left; rw [← neg_sub c d, hcd', neg_neg]
  · left; rw [hcd', neg_sub]
  · right; rw [← neg_sub c d, hcd']; simp

lemma eqvGen_sameDir {X : Finset Plane} {e f : Sym2 Plane}
    (h : Relation.EqvGen (OppositeSides X) e f) : SameDir e f := by
  induction h with
  | rel _ _ h => exact oppositeSides_sameDir h
  | refl => exact SameDir.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

lemma mem_trackOf {X : Finset Plane} {e f : Sym2 Plane} :
    f ∈ trackOf X e ↔ f ∈ rhombusEdges X ∧ Relation.EqvGen (OppositeSides X) e f :=
  Finset.mem_filter

lemma trackOf_eq_of_eqvGen {X : Finset Plane} {e f : Sym2 Plane}
    (h : Relation.EqvGen (OppositeSides X) e f) : trackOf X e = trackOf X f := by
  ext g
  simp only [mem_trackOf]
  constructor
  · rintro ⟨hg, h'⟩; exact ⟨hg, (h.symm _ _).trans _ _ _ h'⟩
  · rintro ⟨hg, h'⟩; exact ⟨hg, h.trans _ _ _ h'⟩

lemma eq_trackOf_of_mem {X : Finset Plane} {T : Finset (Sym2 Plane)} {e : Sym2 Plane}
    (hT : T ∈ tracks X) (he : e ∈ T) : T = trackOf X e := by
  obtain ⟨e0, -, rfl⟩ := Finset.mem_image.1 hT
  exact trackOf_eq_of_eqvGen (mem_trackOf.1 he).2

lemma mem_trackOf_self {X : Finset Plane} {e : Sym2 Plane} (he : e ∈ rhombusEdges X) :
    e ∈ trackOf X e :=
  mem_trackOf.2 ⟨he, Relation.EqvGen.refl _⟩

lemma exists_rep_of_mem_tracks {X : Finset Plane} {T : Finset (Sym2 Plane)} (hT : T ∈ tracks X) :
    ∃ e ∈ T, e ∈ unitEdges X := by
  obtain ⟨e0, h0, rfl⟩ := Finset.mem_image.1 hT
  exact ⟨e0, mem_trackOf_self h0, (Finset.mem_filter.1 h0).1⟩

lemma sameDir_of_mem_trackOf {X : Finset Plane} {e f : Sym2 Plane} (hf : f ∈ trackOf X e) :
    SameDir f e :=
  (eqvGen_sameDir (mem_trackOf.1 hf).2).symm

namespace RhombusData

variable {X R : Finset Plane} {a b c d : Plane}

lemma rotate (h : RhombusData X R a b c d) : RhombusData X R b c d a := by
  have e : ({b, c, d, a} : Finset Plane) = {a, b, c, d} := by
    ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := h.distinct
  exact ⟨e ▸ h.eq, e ▸ h.mem, h.hb, h.hc, h.hd, h.ha, h.hbc, h.hcd, h.hda, h.hab,
    by rw [add_comm c a, h.para, add_comm], h.diag2, by rw [dist_comm]; exact h.diag1,
    ⟨d4, d5, d1.symm, d6, d2.symm, d3.symm⟩⟩

lemma opp (h : RhombusData X R a b c d) : OppositeSides X s(a, b) s(c, d) :=
  ⟨a, b, c, d, h.mem, h.hab, h.hbc, h.hcd, h.hda, rfl, rfl⟩

lemma unit_ab (h : RhombusData X R a b c d) : s(a, b) ∈ unitEdges X :=
  Finset.mem_image.2 ⟨(a, b), by simp [h.ha, h.hb, h.hab], rfl⟩

lemma rhombusEdge_ab (h : RhombusData X R a b c d) : s(a, b) ∈ rhombusEdges X :=
  Finset.mem_filter.2 ⟨h.unit_ab, _, h.opp⟩

lemma edge_cases (h : RhombusData X R a b c d) {x y : Plane} (hx : x ∈ R) (hy : y ∈ R)
    (hxy : dist x y = 1) :
    s(x, y) = s(a, b) ∨ s(x, y) = s(b, c) ∨ s(x, y) = s(c, d) ∨ s(x, y) = s(d, a) := by
  have d1 := h.diag1; have d2 := h.diag2
  rw [h.eq] at hx hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    simp_all [Sym2.eq_swap, dist_comm]

lemma crosses (h : RhombusData X R a b c d) {T : Finset (Sym2 Plane)} (hT : T ∈ tracks X)
    (hc : Crosses T R) : T = trackOf X s(a, b) ∨ T = trackOf X s(b, c) := by
  obtain ⟨e, heT, hin⟩ := hc
  have hTe := eq_trackOf_of_mem hT heT
  obtain ⟨e0, -, rfl⟩ := Finset.mem_image.1 hT
  have heu : e ∈ unitEdges X := (Finset.mem_filter.1 (mem_trackOf.1 heT).1).1
  obtain ⟨⟨x, y⟩, hp, rfl⟩ := Finset.mem_image.1 heu
  simp only [Finset.mem_filter] at hp
  have hx := hin x (Sym2.mem_mk_left _ _)
  have hy := hin y (Sym2.mem_mk_right _ _)
  rw [hTe]
  rcases h.edge_cases hx hy hp.2 with e | e | e | e <;> rw [e]
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inl (trackOf_eq_of_eqvGen (Relation.EqvGen.rel _ _ h.opp)).symm
  · exact Or.inr (trackOf_eq_of_eqvGen (Relation.EqvGen.rel _ _ h.rotate.opp)).symm

lemma crosses_ab (h : RhombusData X R a b c d) : Crosses (trackOf X s(a, b)) R :=
  ⟨_, mem_trackOf_self h.rhombusEdge_ab, fun z hz => by
    rw [h.eq]; rcases Sym2.mem_iff.1 hz with rfl | rfl <;> simp⟩

lemma abs_inner_dv_lt (h : RhombusData X R a b c d) :
    |inner ℝ (dv s(a, b)) (dv s(b, c))| < 1 / 2 := by
  rw [abs_inner_dv_mk]; exact h.abs_inner_lt

lemma trackOf_ne (h : RhombusData X R a b c d) : trackOf X s(a, b) ≠ trackOf X s(b, c) := by
  intro he
  have hm : s(b, c) ∈ trackOf X s(a, b) := he ▸ mem_trackOf_self h.rotate.rhombusEdge_ab
  have hs := sameDir_of_mem_trackOf hm
  have h1 := h.abs_inner_dv_lt
  rw [abs_inner_of_sameDir (SameDir.refl _) hs, real_inner_self_eq_norm_sq,
    norm_dv_of_mem_unitEdges h.unit_ab] at h1
  norm_num at h1

end RhombusData

theorem rhombus_two_tracks_of_separated {X : Finset Plane} (hX : IsSeparated X)
    (htri : ¬ HasUnitTriangle X) {R : Finset Plane} (hR : R ∈ rhombi X) :
    ∃ T ∈ tracks X, ∃ T' ∈ tracks X, T ≠ T' ∧
      ∀ T'' ∈ tracks X, Crosses T'' R ↔ (T'' = T ∨ T'' = T') := by
  obtain ⟨a, b, c, d, h⟩ := exists_rhombusData hX htri hR
  refine ⟨_, Finset.mem_image_of_mem _ h.rhombusEdge_ab, _,
    Finset.mem_image_of_mem _ h.rotate.rhombusEdge_ab, h.trackOf_ne, fun T hT => ⟨h.crosses hT, ?_⟩⟩
  rintro (rfl | rfl)
  · exact h.crosses_ab
  · exact h.rotate.crosses_ab

lemma abs_inner_lt_of_adj {X : Finset Plane} (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X)
    {T T' : Finset (Sym2 Plane)} (hadj : (crossingGraph X).Adj T T') {e f : Sym2 Plane}
    (he : e ∈ T) (hf : f ∈ T') : |inner ℝ (dv e) (dv f)| < 1 / 2 := by
  obtain ⟨hne, hT, hT', R, hR, hc, hc'⟩ := hadj
  obtain ⟨a, b, c, d, h⟩ := exists_rhombusData hX htri hR
  have key := h.abs_inner_dv_lt
  rcases h.crosses hT hc with rfl | rfl <;> rcases h.crosses hT' hc' with rfl | rfl
  · exact absurd rfl hne
  · rwa [abs_inner_of_sameDir (sameDir_of_mem_trackOf he) (sameDir_of_mem_trackOf hf)]
  · rw [abs_inner_of_sameDir (sameDir_of_mem_trackOf he) (sameDir_of_mem_trackOf hf),
      real_inner_comm]; exact key
  · exact absurd rfl hne

lemma inner_coord (u v : Plane) : inner ℝ u v = u 0 * v 0 + u 1 * v 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]; ring

lemma gram_identity (u0 u1 v0 v1 w0 w1 : ℝ) :
    (u0 ^ 2 + u1 ^ 2) * (v0 ^ 2 + v1 ^ 2) * (w0 ^ 2 + w1 ^ 2)
      - (u0 ^ 2 + u1 ^ 2) * (v0 * w0 + v1 * w1) ^ 2 - (v0 ^ 2 + v1 ^ 2) * (u0 * w0 + u1 * w1) ^ 2
      - (w0 ^ 2 + w1 ^ 2) * (u0 * v0 + u1 * v1) ^ 2
      + 2 * (u0 * v0 + u1 * v1) * (v0 * w0 + v1 * w1) * (u0 * w0 + u1 * w1) = 0 := by
  ring

lemma gram_aux (x y z : ℝ) (g : 1 - y ^ 2 - z ^ 2 - x ^ 2 + 2 * x * y * z = 0)
    (h1 : |x| < 1 / 2) (h2 : |y| < 1 / 2) (h3 : |z| < 1 / 2) : False := by
  have hxyz : |x * y * z| < 1 / 8 := by
    rw [abs_mul, abs_mul]
    have := mul_lt_mul'' (mul_lt_mul'' h1 h2 (abs_nonneg _) (abs_nonneg _)) h3
      (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)
    linarith
  have ex : x ^ 2 < 1 / 4 := by rw [← sq_abs]; nlinarith [abs_nonneg x]
  have ey : y ^ 2 < 1 / 4 := by rw [← sq_abs]; nlinarith [abs_nonneg y]
  have ez : z ^ 2 < 1 / 4 := by rw [← sq_abs]; nlinarith [abs_nonneg z]
  have := neg_abs_le (x * y * z)
  linarith

lemma no_three_spread_unit_vectors (u v w : Plane) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (h1 : |inner ℝ u v| < 1 / 2) (h2 : |inner ℝ v w| < 1 / 2) (h3 : |inner ℝ u w| < 1 / 2) :
    False := by
  have nu : u 0 ^ 2 + u 1 ^ 2 = 1 := by
    have := real_inner_self_eq_norm_sq u; rw [hu, inner_coord] at this; linarith
  have nv : v 0 ^ 2 + v 1 ^ 2 = 1 := by
    have := real_inner_self_eq_norm_sq v; rw [hv, inner_coord] at this; linarith
  have nw : w 0 ^ 2 + w 1 ^ 2 = 1 := by
    have := real_inner_self_eq_norm_sq w; rw [hw, inner_coord] at this; linarith
  rw [inner_coord] at h1 h2 h3
  have gram := gram_identity (u 0) (u 1) (v 0) (v 1) (w 0) (w 1)
  rw [nu, nv, nw] at gram
  exact gram_aux _ _ _ (by linarith) h1 h2 h3

theorem crossingGraph_cliqueFree_of_separated {X : Finset Plane} (hX : IsSeparated X)
    (htri : ¬ HasUnitTriangle X) : (crossingGraph X).CliqueFree 3 := by
  intro s hs
  obtain ⟨T1, T2, T3, h12, h13, h23, rfl⟩ := SimpleGraph.is3Clique_iff.1 hs
  obtain ⟨e1, he1, hu1⟩ := exists_rep_of_mem_tracks h12.2.1
  obtain ⟨e2, he2, hu2⟩ := exists_rep_of_mem_tracks h12.2.2.1
  obtain ⟨e3, he3, hu3⟩ := exists_rep_of_mem_tracks h13.2.2.1
  exact no_three_spread_unit_vectors _ _ _ (norm_dv_of_mem_unitEdges hu1)
    (norm_dv_of_mem_unitEdges hu2) (norm_dv_of_mem_unitEdges hu3)
    (abs_inner_lt_of_adj hX htri h12 he1 he2) (abs_inner_lt_of_adj hX htri h23 he2 he3)
    (abs_inner_lt_of_adj hX htri h13 he1 he3)

end Erdos99
end

end RhombusGeom

section LinAlg

@[expose] public section

namespace Erdos99

open Module

theorem finrank_add_one_le_of_cone_trivial {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] {ι : Type*} [Fintype ι] (L : V →ₗ[ℝ] (ι → ℝ))
    (W : Submodule ℝ V) (hW : W ≤ LinearMap.ker L) (h : ∀ v, (∀ i, 0 ≤ L v i) → v ∈ W)
    (hlt : finrank ℝ W < finrank ℝ V) :
    finrank ℝ V + 1 ≤ finrank ℝ W + Fintype.card ι := by
  classical
  have hker : LinearMap.ker L ≤ W := fun v hv => h v (fun i => by
    rw [LinearMap.mem_ker.1 hv]; simp)
  have hrn := LinearMap.finrank_range_add_finrank_ker L
  have hr : finrank ℝ (LinearMap.range L) ≤ Fintype.card ι := by
    have := Submodule.finrank_le (LinearMap.range L); simpa using this
  have hk := Submodule.finrank_mono hker
  by_contra hcon
  push_neg at hcon
  have htop : LinearMap.range L = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    simp; omega
  have hpos : 0 < Fintype.card ι := by omega
  obtain ⟨i0⟩ := Fintype.card_pos_iff.1 hpos
  obtain ⟨v, hv⟩ := LinearMap.range_eq_top.1 htop (Pi.single i0 1)
  have hvW : v ∈ W := h v (fun i => by
    rw [hv]; by_cases hi : i = i0
    · subst hi; simp
    · simp [hi])
  have := LinearMap.mem_ker.1 (hW hvW)
  rw [hv] at this
  have := congrFun this i0
  simp at this

end Erdos99
end

end LinAlg

section Rows

open scoped BigOperators Real

@[expose] public noncomputable section

open Classical Module

namespace Erdos99

def extV (X : Finset Plane) : (X → Plane) →ₗ[ℝ] (Plane → Plane) where
  toFun u p := if h : p ∈ X then u ⟨p, h⟩ else 0
  map_add' u u' := by ext p i; by_cases h : p ∈ X <;> simp [h]
  map_smul' c u := by ext p i; by_cases h : p ∈ X <;> simp [h]

lemma extV_mem (X : Finset Plane) (u : X → Plane) {p : Plane} (hp : p ∈ X) :
    extV X u p = u ⟨p, hp⟩ := by simp [extV, hp]

def rowVal (v : Plane → Plane) (e : Sym2 Plane) : ℝ :=
  inner ℝ (e.out.1 - e.out.2) (v e.out.1 - v e.out.2)

lemma rowVal_mk (v : Plane → Plane) (x y : Plane) :
    rowVal v s(x, y) = inner ℝ (x - y) (v x - v y) := by
  have h : s((s(x, y)).out.1, (s(x, y)).out.2) = s(x, y) := by
    simp [Sym2.mk]
  rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [rowVal, h1, h2]
  · rw [rowVal, h1, h2, ← neg_sub x y, ← neg_sub (v x) (v y), inner_neg_neg]

lemma out_mem {X : Finset Plane} {e : Sym2 Plane} (he : ∀ z ∈ e, z ∈ X) :
    e.out.1 ∈ X ∧ e.out.2 ∈ X := by
  exact ⟨he _ (Sym2.out_fst_mem e), he _ (Sym2.out_snd_mem e)⟩

lemma mem_of_mem_unitEdges {X : Finset Plane} {e : Sym2 Plane} (he : e ∈ unitEdges X) :
    ∀ z ∈ e, z ∈ X := by
  obtain ⟨⟨x, y⟩, hp, rfl⟩ := Finset.mem_image.1 he
  simp only [Finset.mem_filter, Finset.mem_product] at hp
  intro z hz; rcases Sym2.mem_iff.1 hz with rfl | rfl <;> tauto

lemma mem_of_mem_diamPairs {X : Finset Plane} {e : Sym2 Plane} (he : e ∈ diamPairs X) :
    ∀ z ∈ e, z ∈ X := by
  obtain ⟨⟨x, y⟩, hp, rfl⟩ := Finset.mem_image.1 he
  simp only [Finset.mem_filter, Finset.mem_product] at hp
  intro z hz; rcases Sym2.mem_iff.1 hz with rfl | rfl <;> tauto

def rotL : Plane →ₗ[ℝ] Plane where
  toFun := rot
  map_add' x y := by ext i; fin_cases i <;> simp [rot] ; ring
  map_smul' c x := by ext i; fin_cases i <;> simp [rot]

lemma inner_rot_self (z : Plane) : inner ℝ z (rot z) = 0 := by
  simp [rot, PiLp.inner_apply, Fin.sum_univ_two]; ring

def trivMap (X : Finset Plane) : (ℝ × Plane) →ₗ[ℝ] (X → Plane) where
  toFun p x := p.1 • rot x + p.2
  map_add' p q := by funext x; simp only [Pi.add_apply, Prod.fst_add, Prod.snd_add, add_smul]; abel
  map_smul' c p := by ext x i; simp [smul_smul, smul_add]

lemma finrank_range_trivMap_le (X : Finset Plane) :
    finrank ℝ (LinearMap.range (trivMap X)) ≤ 3 := by
  have := LinearMap.finrank_range_le (trivMap X)
  simpa using this

lemma rowVal_trivMap {X : Finset Plane} {e : Sym2 Plane} (he : ∀ z ∈ e, z ∈ X) (p : ℝ × Plane) :
    rowVal (extV X (trivMap X p)) e = 0 := by
  obtain ⟨h1, h2⟩ := out_mem he
  rw [rowVal, extV_mem X _ h1, extV_mem X _ h2]
  simp only [trivMap, LinearMap.coe_mk, AddHom.coe_mk]
  have : p.1 • rot e.out.1 + p.2 - (p.1 • rot e.out.2 + p.2) = p.1 • rot (e.out.1 - e.out.2) := by
    rw [show rot (e.out.1 - e.out.2) = rotL (e.out.1 - e.out.2) from rfl, map_sub]
    simp [rotL, smul_sub]
  rw [this, inner_smul_right, inner_rot_self, mul_zero]

theorem card_rows_of_locking {X : Finset Plane} (hn : 2 ≤ X.card) (hD : diam X ≠ 1)
    (hlock : ∀ v : Plane → Plane,
        (∀ x ∈ X, ∀ y ∈ X, dist x y = 1 → 0 ≤ inner ℝ (x - y) (v x - v y)) →
        (∀ x ∈ X, ∀ y ∈ X, dist x y = diam X → inner ℝ (x - y) (v x - v y) ≤ 0) →
        IsTrivialVelocity X v) :
    2 * X.card ≤ (unitEdges X).card + (diamPairs X).card + 2 := by
  set E := unitEdges X ∪ diamPairs X
  let sgn : Sym2 Plane → ℝ := fun e => if e ∈ unitEdges X then 1 else -1
  let L : (X → Plane) →ₗ[ℝ] (E → ℝ) :=
    { toFun := fun u e => sgn e * rowVal (extV X u) e
      map_add' := fun u u' => by
        ext e; simp only [rowVal, map_add, Pi.add_apply]
        rw [show extV X u e.1.out.1 + extV X u' e.1.out.1 - (extV X u e.1.out.2 +
          extV X u' e.1.out.2) = (extV X u e.1.out.1 - extV X u e.1.out.2) +
          (extV X u' e.1.out.1 - extV X u' e.1.out.2) by abel, inner_add_right]; ring
      map_smul' := fun c u => by
        ext e; simp only [rowVal, map_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
        rw [← smul_sub, inner_smul_right]; ring }
  have hmemE : ∀ e ∈ E, ∀ z ∈ e, z ∈ X := fun e he => by
    rcases Finset.mem_union.1 he with h | h
    · exact mem_of_mem_unitEdges h
    · exact mem_of_mem_diamPairs h
  have hW : LinearMap.range (trivMap X) ≤ LinearMap.ker L := by
    rintro _ ⟨p, rfl⟩
    rw [LinearMap.mem_ker]; ext e
    simp [L, rowVal_trivMap (hmemE e.1 e.2) p]
  have hcone : ∀ u, (∀ e, 0 ≤ L u e) → u ∈ LinearMap.range (trivMap X) := by
    intro u hu
    obtain ⟨ω, w, hw⟩ := hlock (extV X u) (fun x hx y hy hxy => by
        have hU : s(x, y) ∈ unitEdges X := Finset.mem_image.2
          ⟨(x, y), by simp [hx, hy, hxy], rfl⟩
        have := hu ⟨_, Finset.mem_union_left _ hU⟩
        simpa [L, sgn, rowVal_mk, hU] using this)
      (fun x hx y hy hxy => by
        by_cases hxy' : x = y
        · subst hxy'; simp
        have hmem : s(x, y) ∈ E := Finset.mem_union_right _ (Finset.mem_image.2
          ⟨(x, y), by simp [hx, hy, hxy, hxy'], rfl⟩)
        have hnot : s(x, y) ∉ unitEdges X := by
          intro h
          obtain ⟨⟨a, b⟩, hp, hab⟩ := Finset.mem_image.1 h
          simp only [Finset.mem_filter] at hp
          have : dist x y = dist a b := by
            rcases Sym2.eq_iff.1 hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · rfl
            · exact dist_comm _ _
          exact hD (by rw [← hxy, this, hp.2])
        have := hu ⟨_, hmem⟩
        simp [L, sgn, rowVal_mk, hnot] at this
        linarith)
    refine ⟨(ω, w), funext fun x => ?_⟩
    have := hw x x.2
    rw [extV_mem X u x.2] at this
    simp [trivMap, this]
  have hfr : finrank ℝ (X → Plane) = 2 * X.card := by
    rw [Module.finrank_pi_fintype]; simp [mul_comm]
  have h3 := finrank_range_trivMap_le X
  have key := finrank_add_one_le_of_cone_trivial L _ hW hcone (by omega)
  have hE : Fintype.card E ≤ (unitEdges X).card + (diamPairs X).card := by
    rw [Fintype.card_coe]; exact Finset.card_union_le _ _
  omega

end Erdos99
end

end Rows

section TrackLength

open scoped BigOperators Real

@[expose] public noncomputable section

open Classical

namespace Erdos99

def mid (e : Sym2 Plane) : Plane := (1 / 2 : ℝ) • (e.out.1 + e.out.2)

lemma mid_mk (x y : Plane) : mid s(x, y) = (1 / 2 : ℝ) • (x + y) := by
  have h : s((s(x, y)).out.1, (s(x, y)).out.2) = s(x, y) := by simp [Sym2.mk]
  rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp [mid, h1, h2]
  · simp [mid, h1, h2, add_comm]

lemma rot_neg (u : Plane) : rot (-u) = -rot u := by
  ext i; fin_cases i <;> simp [rot]

lemma norm_sq_coord (w : Plane) : ‖w‖ ^ 2 = w 0 ^ 2 + w 1 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_coord]; ring

lemma inner_rot_coord (w u : Plane) : inner ℝ w (rot u) = -(w 0 * u 1) + w 1 * u 0 := by
  rw [inner_coord]; simp [rot]

lemma inner_sq_add_inner_rot_sq (u w : Plane) :
    inner ℝ w u ^ 2 + inner ℝ w (rot u) ^ 2 = ‖w‖ ^ 2 * ‖u‖ ^ 2 := by
  rw [inner_rot_coord, inner_coord, norm_sq_coord, norm_sq_coord]; ring

lemma inner_eq_frame (u w1 w2 : Plane) (hu : ‖u‖ = 1) :
    inner ℝ w1 w2 = inner ℝ w1 u * inner ℝ w2 u + inner ℝ w1 (rot u) * inner ℝ w2 (rot u) := by
  have h := norm_sq_coord u
  rw [hu] at h
  rw [inner_rot_coord, inner_rot_coord, inner_coord, inner_coord, inner_coord]
  linear_combination (w1 0 * w2 0 + w1 1 * w2 1) * h

lemma norm_sub_lt_one_of_same_side (u w1 w2 : Plane) (hu : ‖u‖ = 1) (hw1 : ‖w1‖ = 1)
    (hw2 : ‖w2‖ = 1) (h1 : |inner ℝ w1 u| < 1 / 2) (h2 : |inner ℝ w2 u| < 1 / 2)
    (hs : 0 < inner ℝ w1 (rot u) * inner ℝ w2 (rot u)) : ‖w1 - w2‖ < 1 := by
  have e1 := inner_sq_add_inner_rot_sq u w1
  have e2 := inner_sq_add_inner_rot_sq u w2
  rw [hu, hw1] at e1; rw [hu, hw2] at e2
  have hframe := inner_eq_frame u w1 w2 hu
  set a1 := inner ℝ w1 u; set a2 := inner ℝ w2 u
  set b1 := inner ℝ w1 (rot u); set b2 := inner ℝ w2 (rot u)
  have ha1 : a1 ^ 2 < 1 / 4 := by rw [← sq_abs]; nlinarith [abs_nonneg a1]
  have ha2 : a2 ^ 2 < 1 / 4 := by rw [← sq_abs]; nlinarith [abs_nonneg a2]
  have hb : 9 / 16 < (b1 * b2) ^ 2 := by
    rw [mul_pow]; nlinarith
  have hb' : 3 / 4 < b1 * b2 := by nlinarith
  have ha : -(1 / 4) < a1 * a2 := by
    have := abs_mul a1 a2
    have : |a1 * a2| < 1 / 4 := by
      rw [abs_mul]
      have := mul_lt_mul'' h1 h2 (abs_nonneg _) (abs_nonneg _); linarith
    linarith [neg_abs_le (a1 * a2)]
  have hsq : ‖w1 - w2‖ ^ 2 < 1 := by
    rw [@norm_sub_sq_real, hw1, hw2, hframe]; nlinarith
  nlinarith [norm_nonneg (w1 - w2)]

lemma aStar_lt_of_sq {x : ℝ} (hx : 0 < x) (h : 3 / 4 < x ^ 2) : aStar < x := by
  unfold aStar
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3' : 0 ≤ √3 := Real.sqrt_nonneg 3
  nlinarith

lemma rhombusData_of_mem {X : Finset Plane} (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X)
    {a b c d : Plane} (hR : ({a, b, c, d} : Finset Plane) ∈ rhombi X)
    (hab : dist a b = 1) (hbc : dist b c = 1) (hcd : dist c d = 1) (hda : dist d a = 1) :
    RhombusData X {a, b, c, d} a b c d := by
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.1 (Finset.mem_filter.1 hR).1
  have hdist := distinct_of_card_four hcard
  obtain ⟨d1, d2⟩ := rhombus_diagonals_gt_one hX htri hR hab hbc hcd hda
  exact ⟨rfl, hR, hsub (by simp), hsub (by simp), hsub (by simp), hsub (by simp),
    hab, hbc, hcd, hda, rhombus_parallelogram hdist.2.1 hdist.2.2.2.2.1 hab hbc hcd hda, d1, d2,
    hdist⟩

lemma oppositeSides_data {X : Finset Plane} (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X)
    {e f : Sym2 Plane} (h : OppositeSides X e f) :
    ∃ a b c d, RhombusData X {a, b, c, d} a b c d ∧ e = s(a, b) ∧ f = s(c, d) := by
  obtain ⟨a, b, c, d, hR, hab, hbc, hcd, hda, rfl, rfl⟩ := h
  exact ⟨a, b, c, d, rhombusData_of_mem hX htri hR hab hbc hcd hda, rfl, rfl⟩

lemma oppositeSides_symm {X : Finset Plane} {e f : Sym2 Plane} (h : OppositeSides X e f) :
    OppositeSides X f e := by
  obtain ⟨a, b, c, d, hR, hab, hbc, hcd, hda, rfl, rfl⟩ := h
  refine ⟨c, d, a, b, ?_, hcd, hda, hab, hbc, rfl, rfl⟩
  have : ({c, d, a, b} : Finset Plane) = {a, b, c, d} := by
    ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  rwa [this]

def ht (u : Plane) (e : Sym2 Plane) : ℝ := inner ℝ (mid e) (rot u)

def DirOf (u : Plane) (e : Sym2 Plane) : Prop := dv e = u ∨ dv e = -u

lemma RhombusData.c_eq {X R : Finset Plane} {a b c d : Plane} (h : RhombusData X R a b c d) :
    c = b + (d - a) := by
  have := h.para
  calc c = (a + c) - a := by abel
    _ = b + (d - a) := by rw [this]; abel

lemma RhombusData.step {X R : Finset Plane} {a b c d u : Plane} (h : RhombusData X R a b c d)
    (hdir : DirOf u s(a, b)) :
    ht u s(c, d) - ht u s(a, b) = inner ℝ (d - a) (rot u) ∧ |inner ℝ (d - a) u| < 1 / 2 ∧
      ‖d - a‖ = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ht, ht, ← inner_sub_left, mid_mk, mid_mk, h.c_eq]
    congr 1
    module
  · have key := h.abs_inner_lt
    have hbc : b - c = -(d - a) := by rw [h.c_eq]; abel
    rw [hbc, inner_neg_right, abs_neg, real_inner_comm] at key
    have hu' : u = a - b ∨ u = -(a - b) := by
      rcases hdir with hd | hd <;> rcases dv_mk a b with h1 | h1 <;> rw [h1] at hd
      · exact Or.inl hd.symm
      · right; rw [← hd, neg_sub]
      · right; rw [← neg_neg u, ← hd]
      · left; rw [← neg_neg u, ← hd, neg_sub]
    rcases hu' with rfl | rfl
    · exact key
    · rw [inner_neg_right, abs_neg]; exact key
  · rw [← dist_eq_norm]; exact h.hda

lemma sq_gap_of_step {u w : Plane} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (h : |inner ℝ w u| < 1 / 2) :
    3 / 4 < inner ℝ w (rot u) ^ 2 := by
  have e := inner_sq_add_inner_rot_sq u w
  rw [hu, hw] at e
  have : inner ℝ w u ^ 2 < 1 / 4 := by rw [← sq_abs]; nlinarith [abs_nonneg (inner ℝ w u)]
  linarith

lemma dirOf_of_opp {X : Finset Plane} {u : Plane} {e f : Sym2 Plane} (hd : DirOf u e)
    (h : OppositeSides X e f) : DirOf u f := by
  rcases oppositeSides_sameDir h with h1 | h1 <;> rcases hd with h2 | h2
  · exact Or.inl (h1 ▸ h2)
  · exact Or.inr (h1 ▸ h2)
  · exact Or.inr (by rw [← neg_neg (dv f), ← h1, h2])
  · exact Or.inl (by rw [← neg_neg (dv f), ← h1, h2, neg_neg])

section
variable {X : Finset Plane} (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X)
include hX htri

lemma step_sq_gap {u : Plane} (hu : ‖u‖ = 1) {e f : Sym2 Plane} (hd : DirOf u e)
    (h : OppositeSides X e f) : 3 / 4 < (ht u f - ht u e) ^ 2 := by
  obtain ⟨a, b, c, d, hR, rfl, rfl⟩ := oppositeSides_data hX htri h
  obtain ⟨g, i, n⟩ := hR.step hd
  rw [g]; exact sq_gap_of_step hu n i

lemma opp_unique {u : Plane} (hu : ‖u‖ = 1) {e f1 f2 : Sym2 Plane} (hd : DirOf u e)
    (o1 : OppositeSides X e f1) (o2 : OppositeSides X e f2)
    (hs : 0 < (ht u f1 - ht u e) * (ht u f2 - ht u e)) : f1 = f2 := by
  obtain ⟨a1, b1, c1, d1, h1, he1, rfl⟩ := oppositeSides_data hX htri o1
  obtain ⟨a2, b2, c2, d2, h2, he2, rfl⟩ := oppositeSides_data hX htri o2
  obtain ⟨g1, i1, n1⟩ := h1.step (he1 ▸ hd)
  obtain ⟨g2, i2, n2⟩ := h2.step (he2 ▸ hd)
  have g1' : ht u s(c1, d1) - ht u e = inner ℝ (d1 - a1) (rot u) := by rw [he1]; exact g1
  have g2' : ht u s(c2, d2) - ht u e = inner ℝ (d2 - a2) (rot u) := by rw [he2]; exact g2
  rw [g1', g2'] at hs
  have hclose := norm_sub_lt_one_of_same_side u _ _ hu n1 n2 i1 i2 hs
  have hc1 := h1.c_eq
  have hc2 := h2.c_eq
  have hsep : ∀ x ∈ X, ∀ y ∈ X, dist x y < 1 → x = y := fun x hx y hy hxy => by
    by_contra hne; exact absurd (hX x hx y hy hne) (not_le.2 hxy)
  rcases Sym2.eq_iff.1 (he1.symm.trans he2) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hdd : d1 = d2 := hsep _ h1.hd _ h2.hd (by
      rw [dist_eq_norm, show d1 - d2 = (d1 - a1) - (d2 - a1) by abel]; exact hclose)
    subst hdd
    rw [hc1, hc2]
  · have hdc : d1 = c2 := hsep _ h1.hd _ h2.hc (by
      rw [dist_eq_norm, hc2, show d1 - (a1 + (d2 - b1)) = (d1 - a1) - (d2 - b1) by abel]
      exact hclose)
    have hw : d1 - a1 = d2 - b1 := by
      rw [hdc, hc2]; abel
    have hcd : c1 = d2 := by rw [hc1, hw]; abel
    rw [hcd, hdc, Sym2.eq_swap]

end

lemma aStar_pos : 0 < aStar := by unfold aStar; positivity

lemma opp_mem_track {X : Finset Plane} {T : Finset (Sym2 Plane)} (hT : T ∈ tracks X)
    {e f : Sym2 Plane} (he : e ∈ T) (h : OppositeSides X e f) : f ∈ T := by
  rw [eq_trackOf_of_mem hT he]
  refine mem_trackOf.2 ⟨Finset.mem_filter.2 ⟨?_, e, oppositeSides_symm h⟩,
    Relation.EqvGen.rel _ _ h⟩
  obtain ⟨a, b, c, d, hR, hab, hbc, hcd, hda, rfl, rfl⟩ := h
  have hsub := (Finset.mem_powersetCard.1 (Finset.mem_filter.1 hR).1).1
  exact Finset.mem_image.2 ⟨(c, d), by simp [hsub (by simp : c ∈ _), hsub (by simp : d ∈ _), hcd],
    rfl⟩

def upE (X : Finset Plane) (u : Plane) (e : Sym2 Plane) : Sym2 Plane :=
  if h : ∃ f, OppositeSides X e f ∧ ht u e < ht u f then h.choose else e

lemma upE_spec {X : Finset Plane} {u : Plane} {e : Sym2 Plane} (hne : upE X u e ≠ e) :
    OppositeSides X e (upE X u e) ∧ ht u e < ht u (upE X u e) := by
  by_cases h : ∃ f, OppositeSides X e f ∧ ht u e < ht u f
  · simp only [upE, dif_pos h]; exact h.choose_spec
  · simp [upE, dif_neg h] at hne

section
variable {X : Finset Plane} (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X)
  {T : Finset (Sym2 Plane)} (hT : T ∈ tracks X) {u : Plane} (hu : ‖u‖ = 1)
  (hdir : ∀ e ∈ T, DirOf u e)
include hX htri hT hu hdir

omit hT in
lemma upE_eq {e f : Sym2 Plane} (he : e ∈ T) (o : OppositeSides X e f) (hlt : ht u e < ht u f) :
    upE X u e = f := by
  have hex : ∃ f, OppositeSides X e f ∧ ht u e < ht u f := ⟨f, o, hlt⟩
  have hs : OppositeSides X e (upE X u e) ∧ ht u e < ht u (upE X u e) := by
    simp only [upE, dif_pos hex]; exact hex.choose_spec
  exact opp_unique hX htri hu (hdir e he) hs.1 o (mul_pos (by linarith [hs.2]) (by linarith))

omit hX htri hu hdir in
lemma upE_mem {e : Sym2 Plane} (he : e ∈ T) : upE X u e ∈ T := by
  by_cases h : upE X u e = e
  · rwa [h]
  · exact opp_mem_track hT he (upE_spec h).1

omit hT in
lemma upE_gap {e : Sym2 Plane} (he : e ∈ T) (hne : upE X u e ≠ e) :
    ht u e + aStar < ht u (upE X u e) := by
  obtain ⟨o, hlt⟩ := upE_spec hne
  have := aStar_lt_of_sq (by linarith) (step_sq_gap hX htri hu (hdir e he) o)
  linarith

omit hX htri hu hdir in
lemma iterate_upE_mem {m : Sym2 Plane} (hm : m ∈ T) (k : ℕ) : (upE X u)^[k] m ∈ T := by
  induction k with
  | zero => exact hm
  | succ k ih => rw [Function.iterate_succ_apply']; exact upE_mem hT ih

lemma iterate_upE_mono {m : Sym2 Plane} (hm : m ∈ T) (i j : ℕ) (hij : i ≤ j) :
    (upE X u)^[j] m = (upE X u)^[i] m ∨
      ht u ((upE X u)^[i] m) + aStar < ht u ((upE X u)^[j] m) := by
  induction j, hij using Nat.le_induction with
  | base => exact Or.inl rfl
  | succ j hij ih =>
    rw [Function.iterate_succ_apply']
    set x := (upE X u)^[j] m
    have hx : x ∈ T := iterate_upE_mem (u := u) hT hm j
    by_cases h : upE X u x = x
    · rw [h]; exact ih
    · have hg := upE_gap hX htri hu hdir hx h
      have hpos := aStar_pos
      right
      rcases ih with ih | ih
      · rw [← ih]; exact hg
      · linarith

lemma mem_range_iterate {m : Sym2 Plane} (hm : m ∈ T) (hmin : ∀ f ∈ T, ht u m ≤ ht u f)
    {f : Sym2 Plane} (hf : f ∈ T) : ∃ k, (upE X u)^[k] m = f := by

  have hclos : ∀ x y, (∃ k, (upE X u)^[k] m = x) → OppositeSides X x y →
      ∃ k, (upE X u)^[k] m = y := by
    rintro x y ⟨k, rfl⟩ o
    have hx := iterate_upE_mem (u := u) hT hm k
    have hy := opp_mem_track hT hx o
    have hgap := step_sq_gap hX htri hu (hdir _ hx) o
    rcases lt_or_gt_of_ne (show ht u ((upE X u)^[k] m) ≠ ht u y from fun h => by
      rw [h, sub_self] at hgap; norm_num at hgap) with hlt | hlt
    · exact ⟨k + 1, by rw [Function.iterate_succ_apply']; exact upE_eq hX htri hu hdir hx o hlt⟩
    · induction k with
      | zero =>
        exact absurd (hmin y hy) (not_le.2 (by simpa using hlt))
      | succ k ih =>
        set z := (upE X u)^[k] m
        have hz : z ∈ T := iterate_upE_mem (u := u) hT hm k
        rw [Function.iterate_succ_apply'] at o hx hgap hlt
        by_cases h : upE X u z = z
        · rw [h] at o hx hgap hlt; exact ih o hx hgap hlt
        · obtain ⟨o', hlt'⟩ := upE_spec h
          refine ⟨k, opp_unique hX htri hu (hdir _ hx) (oppositeSides_symm o') o
            (mul_pos_of_neg_of_neg (by linarith) (by linarith))⟩
  have hTm := eq_trackOf_of_mem hT hm
  rw [hTm] at hf
  have heq := (mem_trackOf.1 hf).2
  suffices H : ∀ a b, Relation.EqvGen (OppositeSides X) a b →
      ((∃ k, (upE X u)^[k] m = a) ↔ (∃ k, (upE X u)^[k] m = b)) from
    (H m f heq).1 ⟨0, rfl⟩
  intro a b hab
  induction hab with
  | rel a b h => exact ⟨fun ha => hclos a b ha h, fun hb => hclos b a hb (oppositeSides_symm h)⟩
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

lemma ht_sep {e f : Sym2 Plane} (he : e ∈ T) (hf : f ∈ T) (hne : e ≠ f) :
    aStar < |ht u e - ht u f| := by
  obtain ⟨m, hm, hmin⟩ := T.exists_min_image (ht u) ⟨e, he⟩
  obtain ⟨i, rfl⟩ := mem_range_iterate hX htri hT hu hdir hm hmin he
  obtain ⟨j, rfl⟩ := mem_range_iterate hX htri hT hu hdir hm hmin hf
  rcases le_total i j with hij | hij
  · rcases iterate_upE_mono hX htri hT hu hdir hm i j hij with h | h
    · exact absurd h.symm hne
    · rw [abs_sub_comm, abs_of_pos (by linarith [aStar_pos])]; linarith
  · rcases iterate_upE_mono hX htri hT hu hdir hm j i hij with h | h
    · exact absurd h hne
    · rw [abs_of_pos (by linarith [aStar_pos])]; linarith

end

lemma norm_rot (u : Plane) : ‖rot u‖ = ‖u‖ := by
  have h1 := norm_sq_coord (rot u)
  have h2 := norm_sq_coord u
  have e0 : rot u 0 = -(u 1) := by simp [rot]
  have e1 : rot u 1 = u 0 := by simp [rot]
  rw [e0, e1] at h1
  have : ‖rot u‖ ^ 2 = ‖u‖ ^ 2 := by rw [h1, h2]; ring
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this

lemma ht_sub_le {X : Finset Plane} {u : Plane} (hu : ‖u‖ = 1) {e f : Sym2 Plane}
    (he : e ∈ unitEdges X) (hf : f ∈ unitEdges X) : ht u f - ht u e ≤ diam X := by
  obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.1 he
  obtain ⟨⟨p, q⟩, hpq, rfl⟩ := Finset.mem_image.1 hf
  simp only [Finset.mem_filter, Finset.mem_product] at hxy hpq
  rw [ht, ht, ← inner_sub_left, mid_mk, mid_mk]
  refine (real_inner_le_norm _ _).trans ?_
  rw [norm_rot, hu, mul_one, ← smul_sub,
    show p + q - (x + y) = (p - x) + (q - y) by abel, norm_smul]
  have h1 := norm_add_le (p - x) (q - y)
  rw [← dist_eq_norm, ← dist_eq_norm] at h1
  have h2 := dist_le_diam hpq.1.1 hxy.1.1
  have h3 := dist_le_diam hpq.1.2 hxy.1.2
  norm_num
  linarith

lemma trackLength_add_one_le_card {X : Finset Plane} (hX : IsSeparated X)
    (htri : ¬ HasUnitTriangle X) {T : Finset (Sym2 Plane)} (hT : T ∈ tracks X) :
    trackLength X T + 1 ≤ T.card := by
  obtain ⟨e0, he0, hu0⟩ := exists_rep_of_mem_tracks hT
  set u := dv e0
  have hu : ‖u‖ = 1 := norm_dv_of_mem_unitEdges hu0
  have hTe0 := eq_trackOf_of_mem hT he0
  have hdir : ∀ e ∈ T, DirOf u e := fun e he => by
    rw [hTe0] at he; exact sameDir_of_mem_trackOf he
  have hunit : ∀ e ∈ T, e ∈ unitEdges X := fun e he => by
    rw [hTe0] at he; exact (Finset.mem_filter.1 (mem_trackOf.1 he).1).1
  set Tup := T.filter (fun e => ∃ f, OppositeSides X e f ∧ ht u e < ht u f)

  have h1 : trackLength X T ≤ Tup.card := by
    refine Finset.card_le_card_of_forall_subsingleton
      (fun R e => ∃ f, OppositeSides X e f ∧ ht u e < ht u f ∧ ∀ z, z ∈ R ↔ (z ∈ e ∨ z ∈ f))
      ?_ ?_
    · intro R hR
      obtain ⟨hR, hc⟩ := Finset.mem_filter.1 hR
      obtain ⟨a, b, c, d, h⟩ := exists_rhombusData hX htri hR
      have key : ∀ {a b c d : Plane}, RhombusData X R a b c d → T = trackOf X s(a, b) →
          ∃ e ∈ Tup, ∃ f, OppositeSides X e f ∧ ht u e < ht u f ∧
            ∀ z, z ∈ R ↔ (z ∈ e ∨ z ∈ f) := by
        intro a b c d h hTab
        have hab : s(a, b) ∈ T := hTab ▸ mem_trackOf_self h.rhombusEdge_ab
        have hcd : s(c, d) ∈ T := opp_mem_track hT hab h.opp
        have hmem : ∀ z, z ∈ R ↔ (z ∈ s(a, b) ∨ z ∈ s(c, d)) := fun z => by
          rw [h.eq]; simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.mem_iff]; tauto
        have hgap := step_sq_gap hX htri hu (hdir _ hab) h.opp
        rcases lt_or_gt_of_ne (show ht u s(a, b) ≠ ht u s(c, d) from fun he => by
          rw [he, sub_self] at hgap; norm_num at hgap) with hlt | hlt
        · exact ⟨_, Finset.mem_filter.2 ⟨hab, _, h.opp, hlt⟩, _, h.opp, hlt, hmem⟩
        · exact ⟨_, Finset.mem_filter.2 ⟨hcd, _, oppositeSides_symm h.opp, hlt⟩, _,
            oppositeSides_symm h.opp, hlt, fun z => (hmem z).trans or_comm⟩
      rcases h.crosses hT hc with hTab | hTbc
      · exact key h hTab
      · exact key h.rotate hTbc
    · intro e he R1 hR1 R2 hR2
      obtain ⟨f1, o1, l1, m1⟩ := hR1.2
      obtain ⟨f2, o2, l2, m2⟩ := hR2.2
      have hf : f1 = f2 := opp_unique hX htri hu (hdir e (Finset.mem_filter.1 he).1) o1 o2
        (mul_pos (by linarith) (by linarith))
      subst hf
      ext z; rw [m1, m2]

  obtain ⟨top, htop, hmax⟩ := T.exists_max_image (ht u) ⟨e0, he0⟩
  have h2 : Tup.card + 1 ≤ T.card := by
    have hss : Tup ⊂ T := by
      refine Finset.ssubset_iff_subset_ne.2 ⟨Finset.filter_subset _ _, fun heq => ?_⟩
      have : top ∈ Tup := heq ▸ htop
      obtain ⟨f, o, hlt⟩ := (Finset.mem_filter.1 this).2
      exact absurd (hmax f (opp_mem_track hT htop o)) (not_le.2 hlt)
    exact Finset.card_lt_card hss
  omega

theorem trackLength_le_of_separated {X : Finset Plane} (hX : IsSeparated X)
    (htri : ¬ HasUnitTriangle X) {T : Finset (Sym2 Plane)} (hT : T ∈ tracks X) :
    (trackLength X T : ℝ) ≤ diam X / aStar := by
  obtain ⟨e0, he0, hu0⟩ := exists_rep_of_mem_tracks hT
  set u := dv e0
  have hu : ‖u‖ = 1 := norm_dv_of_mem_unitEdges hu0
  have hTe0 := eq_trackOf_of_mem hT he0
  have hdir : ∀ e ∈ T, DirOf u e := fun e he => by
    rw [hTe0] at he; exact sameDir_of_mem_trackOf he
  have hunit : ∀ e ∈ T, e ∈ unitEdges X := fun e he => by
    rw [hTe0] at he; exact (Finset.mem_filter.1 (mem_trackOf.1 he).1).1
  have h12 := trackLength_add_one_le_card hX htri hT

  have ha := aStar_pos
  set S := T.image (fun e => ht u e / aStar)
  have hinj : Set.InjOn (fun e => ht u e / aStar) T := fun e he f hf hef => by
    by_contra hne
    have := ht_sep hX htri hT hu hdir he hf hne
    simp only at hef
    rw [div_left_inj' ha.ne', ← sub_eq_zero] at hef
    rw [hef, abs_zero] at this; linarith
  have hS : S.card = T.card := Finset.card_image_of_injOn hinj
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_spread_of_separated_real S ⟨_, Finset.mem_image_of_mem _ he0⟩
    (by
      simp only [S, Finset.mem_image]
      rintro _ ⟨e, he, rfl⟩ _ ⟨f, hf, rfl⟩ hne
      have hef : e ≠ f := fun h => hne (by rw [h])
      have := ht_sep hX htri hT hu hdir he hf hef
      rw [← sub_div, abs_div, abs_of_pos ha, le_div_iff₀ ha]; linarith)
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hx
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hy
  have hD := ht_sub_le (X := X) hu (hunit e he) (hunit f hf)
  rw [hS, ← sub_div] at hxy
  have h3 : (T.card : ℝ) - 1 ≤ diam X / aStar :=
    hxy.trans (div_le_div_of_nonneg_right hD ha.le)
  have h4n : trackLength X T + 1 ≤ T.card := h12
  have h4 : (trackLength X T : ℝ) + 1 ≤ T.card := by exact_mod_cast h4n
  linarith

end Erdos99
end

end TrackLength

section HullPerimeter

open scoped BigOperators Real
open MeasureTheory

@[expose] public noncomputable section

open Classical

namespace Erdos99

lemma integral_abs_cos_pi : ∫ x in (0:ℝ)..π, |Real.cos x| = 2 := by
  have hper : Function.Periodic (fun x => |Real.cos x|) π := fun x => by
    simp [Real.cos_add_pi]
  have h1 := hper.intervalIntegral_add_eq 0 (-(π/2))
  simp only [zero_add] at h1
  rw [h1, show -(π/2) + π = π/2 by ring]
  rw [intervalIntegral.integral_congr (g := Real.cos) (fun x hx => by
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hx
    exact abs_of_nonneg (Real.cos_nonneg_of_mem_Icc hx))]
  simp [integral_cos]; norm_num

lemma integral_abs_lin (a b : ℝ) :
    ∫ x in (0:ℝ)..π, |a * Real.cos x + b * Real.sin x| = 2 * √(a ^ 2 + b ^ 2) := by
  set z : ℂ := ⟨a, b⟩
  have ha : ‖z‖ * Real.cos (Complex.arg z) = a := Complex.norm_mul_cos_arg z
  have hb : ‖z‖ * Real.sin (Complex.arg z) = b := Complex.norm_mul_sin_arg z
  have hr : ‖z‖ = √(a ^ 2 + b ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]; simp [z, sq]
  have e : ∀ x, a * Real.cos x + b * Real.sin x = ‖z‖ * Real.cos (x - Complex.arg z) := by
    intro x; rw [Real.cos_sub, ← ha, ← hb]; ring
  simp_rw [e, abs_mul, abs_norm]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_right
    (fun x => |Real.cos x|)]
  have hper : Function.Periodic (fun x => |Real.cos x|) π := fun x => by
    simp [Real.cos_add_pi]
  have h1 := hper.intervalIntegral_add_eq (0 - Complex.arg z) 0
  simp only [zero_add] at h1
  rw [show π - Complex.arg z = (0 - Complex.arg z) + π by ring, h1, integral_abs_cos_pi, hr]
  ring

lemma det2_comb (d a b q : Plane) (l : ℝ) :
    det2 d ((1 - l) • a + l • b - q) = (1 - l) * det2 d (a - q) + l * det2 d (b - q) := by
  simp [det2]; ring

lemma det2_self_smul (d : Plane) (l : ℝ) : det2 d (l • d) = 0 := by
  simp [det2]; ring

lemma det2_rot (d n : Plane) : det2 d (rot n) = inner ℝ d n := by
  rw [inner_coord]; simp [det2, rot]

lemma det2_sub_right (d a b : Plane) : det2 d (a - b) = det2 d a - det2 d b := by
  simp [det2]; ring

lemma det2_smul_right (d a : Plane) (l : ℝ) : det2 d (l • a) = l * det2 d a := by
  simp [det2]; ring

lemma eq_smul_of_det2_eq_zero {d z : Plane} (hd : d ≠ 0) (h : det2 d z = 0) :
    ∃ s : ℝ, z = s • d := by
  have hn : d 0 ^ 2 + d 1 ^ 2 ≠ 0 := by
    intro h0
    apply hd
    have h1 : d 0 = 0 := by nlinarith
    have h2 : d 1 = 0 := by nlinarith
    rw [plane_ext_iff]; simp [h1, h2]
  refine ⟨(z 0 * d 0 + z 1 * d 1) / (d 0 ^ 2 + d 1 ^ 2), ?_⟩
  unfold det2 at h
  rw [plane_ext_iff]
  simp only [PiLp.smul_apply, smul_eq_mul]
  constructor
  · field_simp; linear_combination (-(d 1)) * h
  · field_simp; linear_combination (d 0) * h

section
variable {X : Finset Plane}

lemma mem_of_mem_hullVertices {x : Plane} (hx : x ∈ hullVertices X) : x ∈ X :=
  (Finset.mem_filter.1 hx).1

lemma extreme_of_mem_hullVertices {x : Plane} (hx : x ∈ hullVertices X) :
    x ∈ Set.extremePoints ℝ (convexHull ℝ (X : Set Plane)) :=
  (Finset.mem_filter.1 hx).2

lemma not_mem_openSegment_of_hull {u v w : Plane} (hu : u ∈ hullVertices X) (hv : v ∈ X)
    (hw : w ∈ X) (hvu : v ≠ u) (h : u ∈ openSegment ℝ v w) : False :=
  hvu ((mem_extremePoints.1 (extreme_of_mem_hullVertices hu)).2 v
    (subset_convexHull ℝ _ hv) w (subset_convexHull ℝ _ hw) h).1

lemma hullVertices_not_collinear {u v w : Plane} (hu : u ∈ hullVertices X)
    (hv : v ∈ hullVertices X) (hw : w ∈ hullVertices X) (huv : u ≠ v) (huw : u ≠ w)
    (hvw : v ≠ w) (hdet : det2 (v - u) (w - u) = 0) : False := by
  have hd : v - u ≠ 0 := sub_ne_zero.2 huv.symm
  obtain ⟨s, hs⟩ := eq_smul_of_det2_eq_zero hd hdet
  have hv' := mem_of_mem_hullVertices hv
  have hw' := mem_of_mem_hullVertices hw
  have hu' := mem_of_mem_hullVertices hu
  have hwu : w = u + s • (v - u) := by rw [← hs]; abel
  rcases lt_trichotomy s 0 with h0 | h0 | h0
  ·
    refine not_mem_openSegment_of_hull hu hv' hw' huv.symm ⟨-s / (1 - s), 1 / (1 - s),
      div_pos (by linarith) (by linarith), div_pos one_pos (by linarith), ?_, ?_⟩
    · have : (1 - s) ≠ 0 := by linarith
      field_simp; ring
    · rw [hwu]
      have : (1 - s) ≠ 0 := by linarith
      rw [plane_ext_iff]; simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
        smul_eq_mul]
      constructor <;> field_simp <;> ring
  · exact huw (by rw [hwu, h0, zero_smul, add_zero])
  · rcases lt_trichotomy s 1 with h1 | h1 | h1
    ·
      refine not_mem_openSegment_of_hull hw hu' hv' huw ⟨1 - s, s, by linarith, h0, by ring, ?_⟩
      rw [hwu]; module
    · exact hvw (by rw [hwu, h1, one_smul]; abel)
    ·
      refine not_mem_openSegment_of_hull hv hu' hw' huv ⟨1 - 1 / s, 1 / s,
        by rw [sub_pos, div_lt_one (by linarith)]; exact h1, by positivity, by ring, ?_⟩
      rw [hwu]
      have : s ≠ 0 := by linarith
      rw [plane_ext_iff]; simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply,
        smul_eq_mul]
      constructor <;> field_simp <;> ring

lemma exists_exposing {v : Plane} (hv : v ∈ hullVertices X) :
    ∃ g : Plane, ∀ x ∈ X, x ≠ v → inner ℝ (x - v) g < 0 := by
  set t := convexHull ℝ ((X : Set Plane) \ {v})
  have hvt : v ∉ t := by
    intro h
    have h1 : v ∈ Set.extremePoints ℝ t :=
      inter_extremePoints_subset_extremePoints_of_subset
        (convexHull_mono Set.diff_subset) ⟨h, extreme_of_mem_hullVertices hv⟩
    have := extremePoints_convexHull_subset h1
    exact this.2 rfl
  obtain ⟨f, u, hfu, hb⟩ := geometric_hahn_banach_point_closed (convex_convexHull ℝ _)
    ((X.finite_toSet.diff).isCompact_convexHull (𝕜 := ℝ) |>.isClosed) hvt
  refine ⟨-(InnerProductSpace.toDual ℝ Plane).symm f, fun x hx hxv => ?_⟩
  have hx' : x ∈ t := subset_convexHull ℝ _ ⟨hx, hxv⟩
  rw [inner_neg_right, real_inner_comm, InnerProductSpace.toDual_symm_apply, map_sub]
  linarith [hb x hx']

lemma frame_det2 (a z g : Plane) :
    inner ℝ a g * inner ℝ z (rot g) - inner ℝ a (rot g) * inner ℝ z g = ‖g‖ ^ 2 * det2 a z := by
  rw [inner_rot_coord, inner_rot_coord, inner_coord, inner_coord, norm_sq_coord]
  simp [det2]; ring

def hullPairs (X : Finset Plane) : Finset (Plane × Plane) :=
  (hullVertices X).offDiag.filter (fun p =>
    (∀ x ∈ hullVertices X, 0 ≤ det2 (p.2 - p.1) (x - p.1)) ∨
      (∀ x ∈ hullVertices X, det2 (p.2 - p.1) (x - p.1) ≤ 0))

lemma two_le_card_hullPairs_fst {v : Plane} (hv : v ∈ hullVertices X)
    (hb : 3 ≤ (hullVertices X).card) :
    2 ≤ ((hullPairs X).filter (fun p => p.1 = v)).card := by
  obtain ⟨g, hg⟩ := exists_exposing hv
  set S := (hullVertices X).erase v
  have hS : 2 ≤ S.card := by rw [Finset.card_erase_of_mem hv]; omega
  have hSne : S.Nonempty := Finset.card_pos.1 (by omega)
  have hneg : ∀ x ∈ S, inner ℝ (x - v) g < 0 := fun x hx =>
    hg x (mem_of_mem_hullVertices (Finset.mem_of_mem_erase hx)) (Finset.ne_of_mem_erase hx)
  set φ : Plane → ℝ := fun x => inner ℝ (x - v) (rot g) / (-inner ℝ (x - v) g)

  have cmp : ∀ a ∈ S, ∀ z ∈ S, φ z ≤ φ a → 0 ≤ det2 (a - v) (z - v) := by
    intro a ha z hz h
    have h1 := hneg a ha; have h2 := hneg z hz
    simp only [φ] at h
    rw [div_le_div_iff₀ (by linarith) (by linarith)] at h
    have e := frame_det2 (a - v) (z - v) g
    have hg0 : 0 < ‖g‖ ^ 2 := by
      have : g ≠ 0 := by rintro rfl; simp at h1
      positivity
    have : 0 ≤ ‖g‖ ^ 2 * det2 (a - v) (z - v) := by rw [← e]; nlinarith
    exact (mul_nonneg_iff_of_pos_left hg0).1 this
  obtain ⟨w1, hw1, hmax⟩ := S.exists_max_image φ hSne
  obtain ⟨w2, hw2, hmin⟩ := S.exists_min_image φ hSne
  have hv1 := Finset.mem_of_mem_erase hw1
  have hv2 := Finset.mem_of_mem_erase hw2
  have p1 : (v, w1) ∈ (hullPairs X).filter (fun p => p.1 = v) := by
    refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_offDiag.2
      ⟨hv, hv1, (Finset.ne_of_mem_erase hw1).symm⟩, Or.inl fun x hx => ?_⟩, rfl⟩
    by_cases hxv : x = v
    · subst hxv; simp [det2]
    · exact cmp w1 hw1 x (Finset.mem_erase.2 ⟨hxv, hx⟩) (hmax x (Finset.mem_erase.2 ⟨hxv, hx⟩))
  have p2 : (v, w2) ∈ (hullPairs X).filter (fun p => p.1 = v) := by
    refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_offDiag.2
      ⟨hv, hv2, (Finset.ne_of_mem_erase hw2).symm⟩, Or.inr fun x hx => ?_⟩, rfl⟩
    by_cases hxv : x = v
    · subst hxv; simp [det2]
    · have hx' : x ∈ S := Finset.mem_erase.2 ⟨hxv, hx⟩
      have := cmp x hx' w2 hw2 (hmin x hx')
      have e : det2 (w2 - v) (x - v) = -det2 (x - v) (w2 - v) := by simp [det2]; ring
      linarith
  have hne : w1 ≠ w2 := by
    intro h12
    subst h12
    obtain ⟨x, hx, hxw⟩ := Finset.exists_mem_ne (by omega : 1 < S.card) w1
    have c1 := cmp w1 hw1 x hx (hmax x hx)
    have c2 := cmp x hx w1 hw1 (hmin x hx)
    have e : det2 (x - v) (w1 - v) = -det2 (w1 - v) (x - v) := by simp [det2]; ring
    exact hullVertices_not_collinear hv hv1 (Finset.mem_of_mem_erase hx)
      (Finset.ne_of_mem_erase hw1).symm (Finset.ne_of_mem_erase hx).symm hxw.symm (by linarith)
  have : ({(v, w1), (v, w2)} : Finset (Plane × Plane)) ⊆
      (hullPairs X).filter (fun p => p.1 = v) := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact p1
    · exact p2
  refine le_trans ?_ (Finset.card_le_card this)
  rw [Finset.card_pair (by simp [hne])]

lemma two_mul_card_le_card_hullPairs (hb : 3 ≤ (hullVertices X).card) :
    2 * (hullVertices X).card ≤ (hullPairs X).card := by
  have hmaps : ∀ p ∈ hullPairs X, p.1 ∈ hullVertices X := fun p hp =>
    (Finset.mem_offDiag.1 (Finset.mem_filter.1 hp).1).1
  rw [Finset.card_eq_sum_card_fiberwise hmaps, mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  exact Finset.sum_le_sum fun v hv => two_le_card_hullPairs_fst hv hb

end

def CrossesLvl (n : Plane) (t : ℝ) (p : Plane × Plane) : Prop :=
  (inner ℝ p.1 n - t) * (inner ℝ p.2 n - t) < 0

def crossPar (n : Plane) (t : ℝ) (p : Plane × Plane) : ℝ :=
  (t - inner ℝ p.1 n) / (inner ℝ p.2 n - inner ℝ p.1 n)

def crossPt (n : Plane) (t : ℝ) (p : Plane × Plane) : Plane :=
  (1 - crossPar n t p) • p.1 + crossPar n t p • p.2

lemma CrossesLvl.ne {n : Plane} {t : ℝ} {p : Plane × Plane} (h : CrossesLvl n t p) :
    inner ℝ p.2 n - inner ℝ p.1 n ≠ 0 := by
  intro h0
  unfold CrossesLvl at h
  have : inner ℝ p.2 n = inner ℝ p.1 n := by linarith
  rw [this] at h; nlinarith

lemma CrossesLvl.par_mem {n : Plane} {t : ℝ} {p : Plane × Plane} (h : CrossesLvl n t p) :
    0 < crossPar n t p ∧ crossPar n t p < 1 := by
  unfold CrossesLvl at h
  unfold crossPar
  rcases mul_neg_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · constructor
    · exact div_pos_of_neg_of_neg (by linarith) (by linarith)
    · rw [div_lt_one_of_neg (by linarith)]; linarith
  · constructor
    · exact div_pos (by linarith) (by linarith)
    · rw [div_lt_one (by linarith)]; linarith

lemma crossPt_lvl {n : Plane} {t : ℝ} {p : Plane × Plane} (h : CrossesLvl n t p) :
    inner ℝ (crossPt n t p) n = t := by
  have hne := h.ne
  unfold crossPt crossPar
  rw [inner_add_left, inner_smul_left, inner_smul_left]
  simp only [conj_trivial]
  field_simp
  ring

lemma eq_smul_rot_of_inner_eq_zero {n z : Plane} (hn : ‖n‖ = 1) (hz : inner ℝ z n = 0) :
    z = inner ℝ z (rot n) • rot n := by
  have h := norm_sq_coord n
  rw [hn] at h
  rw [inner_coord] at hz
  rw [inner_rot_coord, plane_ext_iff]
  simp only [PiLp.smul_apply, smul_eq_mul, rot]
  simp
  constructor
  · linear_combination (z 0) * h + (n 0) * hz
  · linear_combination (z 1) * h + (n 1) * hz

section
variable {X : Finset Plane}

lemma hullPairs_sign {q : Plane × Plane} (hq : q ∈ hullPairs X) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ x ∈ hullVertices X, 0 ≤ σ * det2 (q.2 - q.1) (x - q.1) := by
  rcases (Finset.mem_filter.1 hq).2 with h | h
  · exact ⟨1, Or.inl rfl, fun x hx => by simpa using h x hx⟩
  · exact ⟨-1, Or.inr rfl, fun x hx => by have := h x hx; linarith⟩

lemma hullPairs_mem {p : Plane × Plane} (hp : p ∈ hullPairs X) :
    p.1 ∈ hullVertices X ∧ p.2 ∈ hullVertices X ∧ p.1 ≠ p.2 :=
  Finset.mem_offDiag.1 (Finset.mem_filter.1 hp).1

lemma hullPairs_sign_comb {q : Plane × Plane} {σ : ℝ}
    (hσ : ∀ x ∈ hullVertices X, 0 ≤ σ * det2 (q.2 - q.1) (x - q.1)) {a b : Plane}
    (ha : a ∈ hullVertices X) (hb : b ∈ hullVertices X) {l : ℝ} (h0 : 0 ≤ l) (h1 : l ≤ 1) :
    0 ≤ σ * det2 (q.2 - q.1) ((1 - l) • a + l • b - q.1) := by
  rw [det2_comb]
  have := hσ a ha; have := hσ b hb
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (hσ a ha), mul_nonneg h0 (hσ b hb)]

lemma det2_crossPt_self {n : Plane} {t : ℝ} (q : Plane × Plane) :
    det2 (q.2 - q.1) (crossPt n t q - q.1) = 0 := by
  have : crossPt n t q - q.1 = crossPar n t q • (q.2 - q.1) := by
    unfold crossPt; module
  rw [this, det2_self_smul]

lemma crossPt_ne {n : Plane} {t : ℝ} {p q : Plane × Plane} (hp : p ∈ hullPairs X)
    (hq : q ∈ hullPairs X) (cp : CrossesLvl n t p)
    (hpq : s(p.1, p.2) ≠ s(q.1, q.2)) : crossPt n t p ≠ crossPt n t q := by
  intro heq
  obtain ⟨σ, hσ1, hσ⟩ := hullPairs_sign hq
  obtain ⟨hp1, hp2, hp12⟩ := hullPairs_mem hp
  obtain ⟨hq1, hq2, hq12⟩ := hullPairs_mem hq
  have h0 : det2 (q.2 - q.1) (crossPt n t p - q.1) = 0 := by rw [heq]; exact det2_crossPt_self q
  obtain ⟨l0, l1⟩ := cp.par_mem
  have e := det2_comb (q.2 - q.1) p.1 p.2 q.1 (crossPar n t p)
  unfold crossPt at h0
  rw [e] at h0
  have s1 := hσ p.1 hp1; have s2 := hσ p.2 hp2
  have hσ0 : σ ≠ 0 := by rcases hσ1 with rfl | rfl <;> norm_num

  have z1 : det2 (q.2 - q.1) (p.1 - q.1) = 0 := by
    rcases hσ1 with rfl | rfl
    · nlinarith [mul_pos (sub_pos.2 l1) l0]
    · nlinarith [mul_pos (sub_pos.2 l1) l0]
  have z2 : det2 (q.2 - q.1) (p.2 - q.1) = 0 := by
    rcases hσ1 with rfl | rfl
    · nlinarith [mul_pos (sub_pos.2 l1) l0]
    · nlinarith [mul_pos (sub_pos.2 l1) l0]
  have third : ∀ x ∈ hullVertices X, x ≠ q.1 → x ≠ q.2 → det2 (q.2 - q.1) (x - q.1) = 0 →
      False := fun x hx h1 h2 hz =>
    hullVertices_not_collinear hq1 hq2 hx hq12 (Ne.symm h1) (Ne.symm h2) hz
  by_cases a1 : p.1 = q.1 ∨ p.1 = q.2
  · by_cases a2 : p.2 = q.1 ∨ p.2 = q.2
    · apply hpq
      rcases a1 with a1 | a1 <;> rcases a2 with a2 | a2
      · exact absurd (a1.trans a2.symm) hp12
      · rw [a1, a2]
      · rw [a1, a2, Sym2.eq_swap]
      · exact absurd (a1.trans a2.symm) hp12
    · push_neg at a2; exact third p.2 hp2 a2.1 a2.2 z2
  · push_neg at a1; exact third p.1 hp1 a1.1 a1.2 z1

lemma crossPt_no_middle {n : Plane} (hn : ‖n‖ = 1) {t : ℝ} {p q r : Plane × Plane}
    (hp : p ∈ hullPairs X) (hq : q ∈ hullPairs X) (hr : r ∈ hullPairs X)
    (cp : CrossesLvl n t p) (cq : CrossesLvl n t q) (cr : CrossesLvl n t r)
    (h1 : inner ℝ (crossPt n t p) (rot n) < inner ℝ (crossPt n t q) (rot n))
    (h2 : inner ℝ (crossPt n t q) (rot n) < inner ℝ (crossPt n t r) (rot n)) : False := by
  obtain ⟨σ, hσ1, hσ⟩ := hullPairs_sign hq
  obtain ⟨hp1, hp2, -⟩ := hullPairs_mem hp
  obtain ⟨hr1, hr2, -⟩ := hullPairs_mem hr
  set P := crossPt n t p; set Q := crossPt n t q; set R := crossPt n t r
  set sp := inner ℝ P (rot n); set sq := inner ℝ Q (rot n); set sr := inner ℝ R (rot n)
  have oQP : Q - P = (sq - sp) • rot n := by
    have := eq_smul_rot_of_inner_eq_zero hn (z := Q - P)
      (by rw [inner_sub_left, crossPt_lvl cq, crossPt_lvl cp, sub_self])
    rw [this, inner_sub_left]
  have oRP : R - P = (sr - sp) • rot n := by
    have := eq_smul_rot_of_inner_eq_zero hn (z := R - P)
      (by rw [inner_sub_left, crossPt_lvl cr, crossPt_lvl cp, sub_self])
    rw [this, inner_sub_left]
  set β := (sq - sp) / (sr - sp)
  have hβ0 : 0 < β := div_pos (by linarith) (by linarith)
  have hβ1 : β < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hQ : Q = (1 - β) • P + β • R := by
    have : Q - P = β • (R - P) := by
      have hne : sr - sp ≠ 0 := by linarith
      rw [oQP, oRP, smul_smul]; congr 1; exact (div_mul_cancel₀ _ hne).symm
    calc Q = P + (Q - P) := by abel
      _ = (1 - β) • P + β • R := by rw [this]; module
  set d := q.2 - q.1
  have hQ0 : det2 d (Q - q.1) = 0 := det2_crossPt_self q
  rw [hQ, det2_comb] at hQ0
  obtain ⟨l0, l1⟩ := cp.par_mem
  obtain ⟨m0, m1⟩ := cr.par_mem
  have sP := hullPairs_sign_comb hσ hp1 hp2 l0.le l1.le
  have sR := hullPairs_sign_comb hσ hr1 hr2 m0.le m1.le
  change 0 ≤ σ * det2 d (P - q.1) at sP
  change 0 ≤ σ * det2 d (R - q.1) at sR
  have zP : det2 d (P - q.1) = 0 := by
    rcases hσ1 with rfl | rfl <;> nlinarith [mul_pos (sub_pos.2 hβ1) hβ0]
  have zR : det2 d (R - q.1) = 0 := by
    rcases hσ1 with rfl | rfl <;> nlinarith [mul_pos (sub_pos.2 hβ1) hβ0]
  have : det2 d (R - P) = 0 := by
    rw [show R - P = (R - q.1) - (P - q.1) by abel, det2_sub_right, zR, zP, sub_self]
  rw [oRP, det2_smul_right, det2_rot] at this
  have hd : inner ℝ d n = 0 := by
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (by linarith)
    · exact h
  apply cq.ne
  rw [← inner_sub_left]; exact hd

lemma card_crossing_le {n : Plane} (hn : ‖n‖ = 1) (t : ℝ) :
    ((hullPairs X).filter (CrossesLvl n t)).card ≤ 4 := by
  set C := (hullPairs X).filter (CrossesLvl n t)
  set I := C.image (fun p => s(p.1, p.2))
  have hmem : ∀ p ∈ C, p ∈ hullPairs X ∧ CrossesLvl n t p := fun p hp => Finset.mem_filter.1 hp
  have hI : I.card ≤ 2 := by
    by_contra hlt
    push_neg at hlt
    obtain ⟨e1, he1, e2, he2, e3, he3, h12, h13, h23⟩ := Finset.two_lt_card.1 hlt
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 he1
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 he2
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 he3
    obtain ⟨hp, cp⟩ := hmem p hp
    obtain ⟨hq, cq⟩ := hmem q hq
    obtain ⟨hr, cr⟩ := hmem r hr

    have pos_ne : ∀ {a b : Plane × Plane}, a ∈ hullPairs X → b ∈ hullPairs X →
        CrossesLvl n t a → CrossesLvl n t b → s(a.1, a.2) ≠ s(b.1, b.2) →
        inner ℝ (crossPt n t a) (rot n) ≠ inner ℝ (crossPt n t b) (rot n) := by
      intro a b ha hb ca cb hab he
      apply crossPt_ne ha hb ca hab
      have := eq_smul_rot_of_inner_eq_zero hn (z := crossPt n t a - crossPt n t b)
        (by rw [inner_sub_left, crossPt_lvl ca, crossPt_lvl cb, sub_self])
      rw [inner_sub_left, he, sub_self, zero_smul] at this
      exact sub_eq_zero.1 this
    have n12 := pos_ne hp hq cp cq h12
    have n13 := pos_ne hp hr cp cr h13
    have n23 := pos_ne hq hr cq cr h23
    rcases lt_or_gt_of_ne n12 with a | a <;> rcases lt_or_gt_of_ne n13 with b | b <;>
      rcases lt_or_gt_of_ne n23 with c | c
    · exact crossPt_no_middle hn hp hq hr cp cq cr a c
    · exact crossPt_no_middle hn hp hr hq cp cr cq b c
    · linarith
    · exact crossPt_no_middle hn hr hp hq cr cp cq b a
    · exact crossPt_no_middle hn hq hp hr cq cp cr a b
    · linarith
    · exact crossPt_no_middle hn hq hr hp cq cr cp c b
    · exact crossPt_no_middle hn hr hq hp cr cq cp c a
  have hfib : ∀ e ∈ I, (C.filter (fun p => s(p.1, p.2) = e)).card ≤ 2 := by
    intro e he
    obtain ⟨p0, -, rfl⟩ := Finset.mem_image.1 he
    refine le_trans (Finset.card_le_card (t := {p0, (p0.2, p0.1)}) ?_) Finset.card_le_two
    intro p hp
    have := (Finset.mem_filter.1 hp).2
    rcases Sym2.eq_iff.1 this with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp [Prod.ext_iff, h1, h2]
    · simp [Prod.ext_iff, h1, h2]
  calc C.card ≤ 2 * I.card := Finset.card_le_mul_card_image C 2 hfib
    _ ≤ 4 := by omega

end

lemma mem_Ioo_min_max_iff (A B t : ℝ) :
    t ∈ Set.Ioo (min A B) (max A B) ↔ (A - t) * (B - t) < 0 := by
  rcases le_total A B with h | h
  · rw [min_eq_left h, max_eq_right h, Set.mem_Ioo, mul_neg_iff]
    constructor
    · rintro ⟨h1, h2⟩; right; exact ⟨by linarith, by linarith⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> constructor <;> linarith
  · rw [min_eq_right h, max_eq_left h, Set.mem_Ioo, mul_neg_iff]
    constructor
    · rintro ⟨h1, h2⟩; left; exact ⟨by linarith, by linarith⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> constructor <;> linarith

lemma integrable_indicator_one_Ioo (a b : ℝ) :
    Integrable ((Set.Ioo a b).indicator (fun _ => (1:ℝ))) :=
  (integrable_indicator_iff measurableSet_Ioo).2 (integrableOn_const (by simp))

lemma sum_abs_inner_hullPairs_le {X : Finset Plane} {n : Plane} (hn : ‖n‖ = 1)
    (hV : (hullVertices X).Nonempty) :
    ∑ p ∈ hullPairs X, |inner ℝ (p.2 - p.1) n| ≤ 4 * diam X := by
  set L := (hullVertices X).image (fun x => inner ℝ x n)
  have hL : L.Nonempty := hV.image _
  set m0 := L.min' hL
  set M0 := L.max' hL
  have hlev : ∀ x ∈ hullVertices X, m0 ≤ inner ℝ x n ∧ inner ℝ x n ≤ M0 := fun x hx =>
    ⟨L.min'_le _ (Finset.mem_image_of_mem _ hx), L.le_max' _ (Finset.mem_image_of_mem _ hx)⟩
  have hwidth : M0 - m0 ≤ diam X := by
    obtain ⟨xM, hxM, hM⟩ := Finset.mem_image.1 (L.max'_mem hL)
    obtain ⟨xm, hxm, hm⟩ := Finset.mem_image.1 (L.min'_mem hL)
    have h1 : M0 - m0 = inner ℝ (xM - xm) n := by
      rw [inner_sub_left, hM, hm]
    have h2 := real_inner_le_norm (xM - xm) n
    rw [hn, mul_one, ← dist_eq_norm] at h2
    have h3 := dist_le_diam (mem_of_mem_hullVertices hxM) (mem_of_mem_hullVertices hxm)
    linarith
  have hm0M0 : m0 ≤ M0 := L.min'_le_max' hL
  set a : Plane × Plane → ℝ := fun p => min (inner ℝ p.1 n) (inner ℝ p.2 n)
  set b : Plane × Plane → ℝ := fun p => max (inner ℝ p.1 n) (inner ℝ p.2 n)
  have habs : ∀ p : Plane × Plane, |inner ℝ (p.2 - p.1) n| =
      ∫ t, (Set.Ioo (a p) (b p)).indicator (fun _ => (1:ℝ)) t := by
    intro p
    rw [integral_indicator_const _ measurableSet_Ioo, Real.volume_real_Ioo_of_le
      (min_le_max), smul_eq_mul, mul_one, inner_sub_left, max_sub_min_eq_abs]
  simp_rw [habs]
  rw [← integral_finset_sum _ (fun p _ => integrable_indicator_one_Ioo _ _)]
  have hpt : ∀ t, ∑ p ∈ hullPairs X, (Set.Ioo (a p) (b p)).indicator (fun _ => (1:ℝ)) t ≤
      (Set.Icc m0 M0).indicator (fun _ => (4:ℝ)) t := by
    intro t
    have hsum : ∑ p ∈ hullPairs X, (Set.Ioo (a p) (b p)).indicator (fun _ => (1:ℝ)) t =
        (((hullPairs X).filter (CrossesLvl n t)).card : ℝ) := by
      simp only [Set.indicator_apply]
      rw [Finset.sum_boole]
      congr 2
      ext p
      simp only [Finset.mem_filter, a, b, mem_Ioo_min_max_iff, CrossesLvl]
    rw [hsum]
    by_cases ht : t ∈ Set.Icc m0 M0
    · rw [Set.indicator_of_mem ht]
      exact_mod_cast card_crossing_le hn t
    · rw [Set.indicator_of_notMem ht]
      have : (hullPairs X).filter (CrossesLvl n t) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro p hp hc
        obtain ⟨h1, h2, -⟩ := hullPairs_mem hp
        unfold CrossesLvl at hc
        rw [← mem_Ioo_min_max_iff] at hc
        apply ht
        obtain ⟨l1, u1⟩ := hlev _ h1
        obtain ⟨l2, u2⟩ := hlev _ h2
        exact ⟨le_trans (le_min l1 l2) hc.1.le, le_trans hc.2.le (max_le u1 u2)⟩
      rw [this]; simp
  refine (integral_mono (integrable_finset_sum _ fun p _ => integrable_indicator_one_Ioo _ _)
    ((integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))) hpt).trans ?_
  rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le hm0M0,
    smul_eq_mul]
  linarith

def unitVec (θ : ℝ) : Plane := !₂[Real.cos θ, Real.sin θ]

lemma norm_unitVec (θ : ℝ) : ‖unitVec θ‖ = 1 := by
  rw [unitVec, EuclideanSpace.norm_eq, Fin.sum_univ_two]; simp

lemma inner_unitVec (d : Plane) (θ : ℝ) :
    inner ℝ d (unitVec θ) = d 0 * Real.cos θ + d 1 * Real.sin θ := by
  rw [inner_coord]; simp [unitVec]

theorem hullVertices_card_le_pi_mul_diam {X : Finset Plane} (hX : IsSeparated X)
    (h2 : 2 ≤ X.card) : ((hullVertices X).card : ℝ) ≤ π * diam X := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 (by omega : 1 < X.card)
  have hD : 1 ≤ diam X := (hX x hx y hy hxy).trans (dist_le_diam hx hy)
  have hpi := Real.pi_gt_three
  by_cases hb : (hullVertices X).card ≤ 3
  · have : ((hullVertices X).card : ℝ) ≤ 3 := by exact_mod_cast hb
    nlinarith
  push_neg at hb
  have hV : (hullVertices X).Nonempty := Finset.card_pos.1 (by omega)
  have hP := two_mul_card_le_card_hullPairs (X := X) (by omega)
  set F : ℝ → ℝ := fun θ => ∑ p ∈ hullPairs X, |inner ℝ (p.2 - p.1) (unitVec θ)|
  have hcont : ∀ p : Plane × Plane,
      Continuous (fun θ => |(p.2 - p.1) 0 * Real.cos θ + (p.2 - p.1) 1 * Real.sin θ|) :=
    fun p => by fun_prop
  have hF : F = fun θ => ∑ p ∈ hullPairs X,
      |(p.2 - p.1) 0 * Real.cos θ + (p.2 - p.1) 1 * Real.sin θ| := by
    funext θ; simp only [F, inner_unitVec]

  have hup : ∫ θ in (0:ℝ)..π, F θ ≤ ∫ θ in (0:ℝ)..π, 4 * diam X := by
    refine intervalIntegral.integral_mono_on Real.pi_pos.le ?_ (by simp) fun θ _ =>
      sum_abs_inner_hullPairs_le (norm_unitVec θ) hV
    rw [hF]
    exact (continuous_finset_sum _ fun p _ => hcont p).intervalIntegrable _ _

  have hval : ∫ θ in (0:ℝ)..π, F θ = ∑ p ∈ hullPairs X, 2 * ‖p.2 - p.1‖ := by
    rw [hF, intervalIntegral.integral_finset_sum fun p _ => (hcont p).intervalIntegrable _ _]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [integral_abs_lin, ← norm_sq_coord, Real.sqrt_sq (norm_nonneg _)]
  have hlow : (2 * (hullPairs X).card : ℝ) ≤ ∑ p ∈ hullPairs X, 2 * ‖p.2 - p.1‖ := by
    rw [mul_comm, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun p hp => ?_
    obtain ⟨h1, h2, h12⟩ := hullPairs_mem hp
    have := hX _ (mem_of_mem_hullVertices h2) _ (mem_of_mem_hullVertices h1) (Ne.symm h12)
    rw [dist_eq_norm] at this
    linarith
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hup
  have hP' : (2 * (hullVertices X).card : ℝ) ≤ (hullPairs X).card := by exact_mod_cast hP
  nlinarith

end Erdos99
end

end HullPerimeter

section HullSides

open scoped BigOperators Real

@[expose] public noncomputable section

open Classical

namespace Erdos99

def IsCcwHullSide (X : Finset Plane) (v w : Plane) : Prop :=
  v ∈ hullVertices X ∧ w ∈ hullVertices X ∧ v ≠ w ∧ ∀ y ∈ X, 0 ≤ det2 (w - v) (y - v)

def ccwHullSides (X : Finset Plane) : Finset (Plane × Plane) :=
  (X ×ˢ X).filter (fun p => IsCcwHullSide X p.1 p.2)

def unitHullSides (X : Finset Plane) : Finset (Plane × Plane) :=
  (ccwHullSides X).filter (fun p => dist p.1 p.2 = 1)

def twoEdgeReturns (X : Finset Plane) : Finset (Plane × Plane × Plane) :=
  (X ×ˢ X ×ˢ X).filter (fun t => IsCcwHullSide X t.1 t.2.2 ∧ dist t.1 t.2.1 = 1 ∧
    dist t.2.1 t.2.2 = 1 ∧ 1 < dist t.1 t.2.2)

def sourceEdges (X : Finset Plane) : Finset (Sym2 Plane) :=
  (unitHullSides X).image (fun p => s(p.1, p.2)) ∪
    (twoEdgeReturns X).image (fun t => s(t.1, t.2.1)) ∪
    (twoEdgeReturns X).image (fun t => s(t.2.1, t.2.2))

def srcLen (X : Finset Plane) (e : Sym2 Plane) : ℕ := trackLength X (trackOf X e)

def IsTerminal (X : Finset Plane) (e : Sym2 Plane) : Prop :=
  ∀ f₁ f₂, OppositeSides X e f₁ → OppositeSides X e f₂ → f₁ = f₂

lemma det2_swap (u v : Plane) : det2 v u = -det2 u v := by unfold det2; ring

lemma det2_neg_neg (u v : Plane) : det2 (-u) (-v) = det2 u v := by
  unfold det2; simp

lemma IsCcwHullSide.succ_unique {X : Finset Plane} {v w w' : Plane} (h : IsCcwHullSide X v w)
    (h' : IsCcwHullSide X v w') : w = w' := by
  by_contra hne
  obtain ⟨hv, hw, hvw, hl⟩ := h
  obtain ⟨-, hw', hvw', hl'⟩ := h'
  have a1 := hl w' (mem_of_mem_hullVertices hw')
  have a2 := hl' w (mem_of_mem_hullVertices hw)
  rw [det2_swap] at a2
  exact hullVertices_not_collinear hv hw hw' hvw hvw' hne (by linarith)

lemma IsCcwHullSide.pred_unique {X : Finset Plane} {v v' w : Plane} (h : IsCcwHullSide X v w)
    (h' : IsCcwHullSide X v' w) : v = v' := by
  by_contra hne
  obtain ⟨hv, hw, hvw, hl⟩ := h
  obtain ⟨hv', -, hvw', hl'⟩ := h'
  have a1 := hl v' (mem_of_mem_hullVertices hv')
  have a2 := hl' v (mem_of_mem_hullVertices hv)
  have e1 : det2 (w - v) (v' - v) = -det2 (v - w) (v' - w) := by unfold det2; simp; ring
  have e2 : det2 (w - v') (v - v') = det2 (v - w) (v' - w) := by unfold det2; simp; ring
  exact hullVertices_not_collinear hw hv hv' hvw.symm hvw'.symm hne (by linarith)

lemma mem_rhombusEdges_of_opp {X : Finset Plane} {e f : Sym2 Plane} (h : OppositeSides X e f) :
    e ∈ rhombusEdges X := by
  refine Finset.mem_filter.2 ⟨?_, f, h⟩
  obtain ⟨a, b, c, d, hR, hab, -, -, -, rfl, -⟩ := h
  have hsub := (Finset.mem_powersetCard.1 (Finset.mem_filter.1 hR).1).1
  exact Finset.mem_image.2 ⟨(a, b), by simp [hsub (by simp : a ∈ _), hsub (by simp : b ∈ _), hab],
    rfl⟩

lemma mem_rhombusEdges_of_eqvGen {X : Finset Plane} {e f : Sym2 Plane}
    (h : Relation.EqvGen (OppositeSides X) e f) (hf : f ∈ rhombusEdges X) :
    e ∈ rhombusEdges X := by
  by_contra he
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
  have : f = e := (key e f h).1 rfl
  exact he (this ▸ hf)

lemma mem_rhombusEdges_of_srcLen_pos {X : Finset Plane} {e : Sym2 Plane} (h : 0 < srcLen X e) :
    e ∈ rhombusEdges X := by
  obtain ⟨R, hR⟩ := Finset.card_pos.1 h
  obtain ⟨f, hf, -⟩ := (Finset.mem_filter.1 hR).2
  obtain ⟨hf1, hf2⟩ := mem_trackOf.1 hf
  exact mem_rhombusEdges_of_eqvGen hf2 hf1

lemma trackOf_mem_tracks {X : Finset Plane} {e : Sym2 Plane} (h : e ∈ rhombusEdges X) :
    trackOf X e ∈ tracks X := Finset.mem_image_of_mem _ h

lemma terminal_aux (A B P R N : ℝ) (hA : A ^ 2 < 1 / 4) (hAB : A ^ 2 + B ^ 2 = 1)
    (hPR : P ^ 2 + R ^ 2 = N) (hP : 4 * P ^ 2 < 3 * N) (h0 : 0 ≤ A * P + B * R) :
    0 < B * R := by
  have hN : 0 < N := by nlinarith [sq_nonneg P]
  have hB : 3 / 4 < B ^ 2 := by linarith
  have hR : N / 4 < R ^ 2 := by linarith
  have h1 : (A * P) ^ 2 ≤ (1 / 4) * P ^ 2 := by
    rw [mul_pow]; exact mul_le_mul_of_nonneg_right hA.le (sq_nonneg P)
  have h1' : (A * P) ^ 2 < 3 * N / 16 := by linarith
  have h2 : 3 / 4 * R ^ 2 < (B * R) ^ 2 := by
    rw [mul_pow]; exact mul_lt_mul_of_pos_right hB (by linarith)
  have h2' : 3 * N / 16 < (B * R) ^ 2 := by linarith
  by_contra hneg
  push_neg at hneg
  have h3 : -(B * R) ≤ A * P := by linarith
  have h4 : 0 ≤ -(B * R) := by linarith
  have : (B * R) ^ 2 ≤ (A * P) ^ 2 := by nlinarith
  linarith

lemma isTerminal_of_halfplane {X : Finset Plane} (hX : IsSeparated X)
    (htri : ¬ HasUnitTriangle X) {p q n : Plane} (hpq : dist p q = 1)
    (hhalf : ∀ z ∈ X, 0 ≤ inner ℝ (z - p) n)
    (hang : 4 * inner ℝ (q - p) n ^ 2 < 3 * ‖n‖ ^ 2) : IsTerminal X s(p, q) := by
  set u := q - p
  have hu : ‖u‖ = 1 := by rw [← dist_eq_norm, dist_comm]; exact hpq
  have hd : DirOf u s(p, q) := by
    rcases dv_mk p q with h | h
    · right; simp [h, u]
    · left; simp [h, u]

  have key : ∀ f, OppositeSides X s(p, q) f →
      0 < (ht u f - ht u s(p, q)) * inner ℝ n (rot u) := by
    intro f o
    obtain ⟨a, b, c, d, h, he, rfl⟩ := oppositeSides_data hX htri o
    obtain ⟨g, i, nm⟩ := h.step (he ▸ hd)
    rw [he, g]
    set y := d - a
    have hpy : p + y ∈ X := by
      rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [show p + (d - p) = d by abel]; exact h.hd
      · rw [show p + (d - q) = c by rw [h.c_eq]; try abel]; exact h.hc
    have h0 : 0 ≤ inner ℝ y n := by
      have := hhalf _ hpy; rwa [add_sub_cancel_left] at this
    have fr := inner_eq_frame u y n hu
    have e1 := inner_sq_add_inner_rot_sq u y
    have e2 := inner_sq_add_inner_rot_sq u n
    rw [hu, nm] at e1
    rw [hu] at e2
    have hP : inner ℝ n u = inner ℝ u n := real_inner_comm _ _
    have hA : inner ℝ y u ^ 2 < 1 / 4 := by
      have := abs_lt.1 i; nlinarith
    have hP2 : 4 * inner ℝ n u ^ 2 < 3 * ‖n‖ ^ 2 := by rw [hP]; exact hang
    rw [fr] at h0
    exact terminal_aux _ _ _ _ _ hA (by linarith) (by rw [e2]; ring) hP2 h0
  intro f1 f2 o1 o2
  have k1 := key f1 o1
  have k2 := key f2 o2
  refine opp_unique hX htri hu hd o1 o2 ?_
  by_contra hle
  push_neg at hle
  have := mul_pos k1 k2
  nlinarith [sq_nonneg (inner ℝ n (rot u))]

lemma inner_rot_eq_det2 (u z : Plane) : inner ℝ z (rot u) = det2 u z := by
  rw [inner_rot_coord]; unfold det2; ring

lemma isTerminal_of_mem_unitHullSides {X : Finset Plane} (hX : IsSeparated X)
    (htri : ¬ HasUnitTriangle X) {v w : Plane} (h : (v, w) ∈ unitHullSides X) :
    IsTerminal X s(v, w) := by
  obtain ⟨h1, hd⟩ := Finset.mem_filter.1 h
  obtain ⟨-, -, -, -, hl⟩ := Finset.mem_filter.1 h1
  refine isTerminal_of_halfplane hX htri hd (n := rot (w - v)) (fun z hz => ?_) ?_
  · rw [inner_rot_eq_det2]; exact hl z hz
  · rw [inner_rot_eq_det2]
    have : det2 (w - v) (w - v) = 0 := by unfold det2; ring
    rw [this, norm_rot, ← dist_eq_norm, dist_comm, hd]; norm_num

lemma port_det_sq {v x w : Plane} (h1 : dist v x = 1) (h2 : dist x w = 1) :
    4 * det2 (w - v) (x - v) ^ 2 = 4 * ‖w - v‖ ^ 2 - ‖w - v‖ ^ 4 := by
  have e1 := dist_sq_coord v x
  have e2 := dist_sq_coord x w
  rw [h1] at e1; rw [h2] at e2
  rw [show ‖w - v‖ ^ 4 = (‖w - v‖ ^ 2) ^ 2 by ring, norm_sq_coord]
  unfold det2
  simp only [PiLp.sub_apply]
  set a0 := w 0 - v 0
  set a1 := w 1 - v 1
  set b0 := x 0 - v 0
  set b1 := x 1 - v 1
  have h1' : b0 ^ 2 + b1 ^ 2 = 1 := by simp only [b0, b1]; linarith
  have h2' : (b0 - a0) ^ 2 + (b1 - a1) ^ 2 = 1 := by
    simp only [a0, a1, b0, b1]; linear_combination -e2
  linear_combination (4 * (a0 ^ 2 + a1 ^ 2) - (2 * (a0 * b0 + a1 * b1) + (a0 ^ 2 + a1 ^ 2))) * h1' +
    (2 * (a0 * b0 + a1 * b1) + (a0 ^ 2 + a1 ^ 2)) * h2'

lemma isTerminal_of_mem_twoEdgeReturns {X : Finset Plane} (hX : IsSeparated X)
    (htri : ¬ HasUnitTriangle X) {v x w : Plane} (h : (v, x, w) ∈ twoEdgeReturns X) :
    IsTerminal X s(v, x) ∧ IsTerminal X s(x, w) := by
  obtain ⟨-, ⟨-, -, -, hl⟩, h1, h2, h3⟩ := Finset.mem_filter.1 h
  simp only at hl h1 h2 h3
  have hdet := port_det_sq h1 h2
  have hn : ‖rot (w - v)‖ ^ 2 = ‖w - v‖ ^ 2 := by rw [norm_rot]
  have hd1 : 1 < ‖w - v‖ ^ 2 := by
    rw [← dist_eq_norm, dist_comm]; nlinarith
  have hang : 4 * det2 (w - v) (x - v) ^ 2 < 3 * ‖w - v‖ ^ 2 := by
    rw [hdet]; nlinarith
  constructor
  · refine isTerminal_of_halfplane hX htri h1 (n := rot (w - v)) (fun z hz => ?_) ?_
    · rw [inner_rot_eq_det2]; exact hl z hz
    · rw [inner_rot_eq_det2, hn]; exact hang
  · rw [Sym2.eq_swap]
    refine isTerminal_of_halfplane hX htri (by rw [dist_comm]; exact h2) (n := rot (w - v))
      (fun z hz => ?_) ?_
    · rw [inner_rot_eq_det2]
      have : det2 (w - v) (z - w) = det2 (w - v) (z - v) := by unfold det2; simp; ring
      rw [this]; exact hl z hz
    · rw [inner_rot_eq_det2, hn]
      have : det2 (w - v) (x - w) = det2 (w - v) (x - v) := by unfold det2; simp; ring
      rw [this]; exact hang

lemma card_filter_isTerminal_le_two {X : Finset Plane} (hX : IsSeparated X)
    (htri : ¬ HasUnitTriangle X) {T : Finset (Sym2 Plane)} (hT : T ∈ tracks X) :
    (T.filter (IsTerminal X)).card ≤ 2 := by
  obtain ⟨e0, he0, hu0⟩ := exists_rep_of_mem_tracks hT
  set u := dv e0
  have hu : ‖u‖ = 1 := norm_dv_of_mem_unitEdges hu0
  have hTe0 := eq_trackOf_of_mem hT he0
  have hdir : ∀ e ∈ T, DirOf u e := fun e he => by
    rw [hTe0] at he; exact sameDir_of_mem_trackOf he
  obtain ⟨m, hm, hmin⟩ := T.exists_min_image (ht u) ⟨e0, he0⟩
  obtain ⟨top, htop, hmax⟩ := T.exists_max_image (ht u) ⟨e0, he0⟩
  have hsub : T.filter (IsTerminal X) ⊆ {m, top} := by
    intro f hf
    obtain ⟨hfT, hterm⟩ := Finset.mem_filter.1 hf
    simp only [Finset.mem_insert, Finset.mem_singleton]
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
  exact (Finset.card_le_card hsub).trans Finset.card_le_two

end Erdos99
end

end HullSides

section EstablishedExternalResults

open scoped BigOperators Real
open Set Metric Complex

@[expose] public noncomputable section

open Classical

namespace EstablishedExternalResults

section Components

variable {X : Type*} [TopologicalSpace X]

def comps (S : Set X) : Set (Set X) := connectedComponentIn S '' S

lemma connectedComponentIn_diff_of_mem {S A : Set X} {p x : X}
    (hx : x ∈ connectedComponentIn S p) (hxA : x ∉ A) :
    connectedComponentIn (S \ A) x = connectedComponentIn (connectedComponentIn S p \ A) x := by
  apply le_antisymm
  · apply (isPreconnected_connectedComponentIn).subset_connectedComponentIn
    · exact mem_connectedComponentIn ⟨connectedComponentIn_subset _ _ hx, hxA⟩
    · intro y hy
      have hy' := connectedComponentIn_subset _ _ hy
      refine ⟨?_, hy'.2⟩
      have h1 : connectedComponentIn (S \ A) x ⊆ connectedComponentIn S x :=
        connectedComponentIn_mono _ diff_subset
      rw [connectedComponentIn_eq hx]
      exact h1 hy
  · exact connectedComponentIn_mono _ (diff_subset_diff_left (connectedComponentIn_subset _ _))

lemma connectedComponentIn_diff_of_not_mem {S A : Set X} {p x : X}
    (hA : A ⊆ connectedComponentIn S p) (hxS : x ∈ S) (hx : x ∉ connectedComponentIn S p) :
    connectedComponentIn (S \ A) x = connectedComponentIn S x := by
  have hdisj : ∀ y ∈ connectedComponentIn S x, y ∉ A := by
    intro y hy hyA
    apply hx
    rw [connectedComponentIn_eq (hA hyA), ← connectedComponentIn_eq hy]
    exact mem_connectedComponentIn hxS
  apply le_antisymm
  · exact connectedComponentIn_mono _ diff_subset
  · apply (isPreconnected_connectedComponentIn).subset_connectedComponentIn
      (mem_connectedComponentIn hxS)
    intro y hy
    exact ⟨connectedComponentIn_subset _ _ hy, hdisj y hy⟩

lemma encard_comps_diff {S A : Set X} {p : X} (hp : p ∈ S)
    (hA : A ⊆ connectedComponentIn S p) :
    (comps (S \ A)).encard + 1 =
      (comps S).encard + (comps (connectedComponentIn S p \ A)).encard := by
  set U := connectedComponentIn S p with hU
  have hUmem : U ∈ comps S := ⟨p, hp, rfl⟩
  have heq : comps (S \ A) = (comps S \ {U}) ∪ comps (U \ A) := by
    ext C
    constructor
    · rintro ⟨x, hx, rfl⟩
      by_cases hxU : x ∈ U
      · right
        exact ⟨x, ⟨hxU, hx.2⟩, (connectedComponentIn_diff_of_mem hxU hx.2).symm⟩
      · left
        refine ⟨⟨x, hx.1, (connectedComponentIn_diff_of_not_mem hA hx.1 hxU).symm⟩, ?_⟩
        intro h
        simp only [mem_singleton_iff] at h
        rw [connectedComponentIn_diff_of_not_mem hA hx.1 hxU] at h
        exact hxU (h ▸ mem_connectedComponentIn hx.1)
    · rintro (⟨⟨x, hx, rfl⟩, hne⟩ | ⟨x, hx, rfl⟩)
      · have hxU : x ∉ U := by
          intro hxU
          apply hne
          simp only [mem_singleton_iff]
          rw [hU, connectedComponentIn_eq hxU]
        have hxA : x ∉ A := fun h => hxU (hA h)
        exact ⟨x, ⟨hx, hxA⟩, connectedComponentIn_diff_of_not_mem hA hx hxU⟩
      · exact ⟨x, ⟨connectedComponentIn_subset _ _ hx.1, hx.2⟩,
          connectedComponentIn_diff_of_mem hx.1 hx.2⟩
  have hdisj : Disjoint (comps S \ {U}) (comps (U \ A)) := by
    rw [Set.disjoint_left]
    rintro C ⟨⟨x, hx, rfl⟩, hne⟩ ⟨y, hy, hyC⟩
    apply hne
    simp only [mem_singleton_iff]
    have hyx : y ∈ connectedComponentIn S x := by
      rw [← hyC]
      exact mem_connectedComponentIn hy
    rw [connectedComponentIn_eq hyx, hU, connectedComponentIn_eq hy.1]
  rw [heq, encard_union_eq hdisj, ← encard_diff_singleton_add_one hUmem]
  ring

lemma comps_eq_singleton {S : Set X} {x : X} (hx : x ∈ S)
    (h : ∀ y ∈ S, y ∈ connectedComponentIn S x) :
    comps S = {connectedComponentIn S x} := by
  ext C
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (connectedComponentIn_eq (h y hy)).symm
  · rintro rfl; exact ⟨x, hx, rfl⟩

lemma comps_eq_pair {S : Set X} {x y : X} (hx : x ∈ S) (hy : y ∈ S)
    (h : ∀ z ∈ S, z ∈ connectedComponentIn S x ∨ z ∈ connectedComponentIn S y) :
    comps S = {connectedComponentIn S x, connectedComponentIn S y} := by
  ext C
  constructor
  · rintro ⟨z, hz, rfl⟩
    rcases h z hz with h1 | h1
    · left; exact (connectedComponentIn_eq h1).symm
    · right; exact (connectedComponentIn_eq h1).symm
  · rintro (rfl | rfl)
    · exact ⟨x, hx, rfl⟩
    · exact ⟨y, hy, rfl⟩

end Components

section Winding

def windSum (x : ℂ) : List ℂ → ℝ
  | u :: v :: l => arg ((v - x) / (u - x)) + windSum x (v :: l)
  | _ => 0

def polyline : List ℂ → Set ℂ
  | u :: v :: l => segment ℝ u v ∪ polyline (v :: l)
  | [u] => {u}
  | [] => ∅

lemma head_mem_polyline (u : ℂ) (l : List ℂ) : u ∈ polyline (u :: l) := by
  cases l with
  | nil => simp [polyline]
  | cons v l => exact Or.inl (left_mem_segment ℝ u v)

def unitDir (x z : ℂ) : ℂ := (z - x) / (‖z - x‖ : ℂ)

lemma exp_windSum (x : ℂ) : ∀ (u : ℂ) (l : List ℂ), x ∉ polyline (u :: l) →
    cexp (windSum x (u :: l) * I) * unitDir x u = unitDir x ((u :: l).getLast (by simp))
  | u, [], _ => by simp [windSum]
  | u, v :: l, h => by
    have hu : u - x ≠ 0 := by
      intro h0; apply h; left; rw [sub_eq_zero.mp h0]; exact left_mem_segment ℝ x v
    have hv : v - x ≠ 0 := by
      intro h0; apply h; left; rw [sub_eq_zero.mp h0]; exact right_mem_segment ℝ u x
    have ih := exp_windSum x v l (fun h' => h (Or.inr h'))
    have key : cexp (arg ((v - x) / (u - x)) * I) * unitDir x u = unitDir x v := by
      have hq := norm_mul_exp_arg_mul_I ((v - x) / (u - x))
      have hn : (‖(v - x) / (u - x)‖ : ℂ) ≠ 0 := by
        rw [ofReal_ne_zero, norm_ne_zero_iff]; exact div_ne_zero hv hu
      have he : cexp (↑(arg ((v - x) / (u - x))) * I) =
          (v - x) / (u - x) / ‖(v - x) / (u - x)‖ := by
        rw [eq_div_iff hn, mul_comm]; exact hq
      rw [he]
      simp only [unitDir, norm_div]
      have h1 : (‖u - x‖ : ℂ) ≠ 0 := by rw [ofReal_ne_zero, norm_ne_zero_iff]; exact hu
      have h2 : (‖v - x‖ : ℂ) ≠ 0 := by rw [ofReal_ne_zero, norm_ne_zero_iff]; exact hv
      push_cast
      field_simp
    rw [List.getLast_cons_cons, ← ih]
    simp only [windSum]
    rw [ofReal_add, add_mul, Complex.exp_add, mul_comm (cexp _) (cexp _), mul_assoc, key]

lemma windSum_mem_int (x u : ℂ) (l : List ℂ) (hx : x ∉ polyline (u :: l))
    (hc : (u :: l).getLast (by simp) = u) : ∃ n : ℤ, windSum x (u :: l) = 2 * π * n := by
  have h := exp_windSum x u l hx
  rw [hc] at h
  have hu : u - x ≠ 0 := by
    intro h0; apply hx; rw [sub_eq_zero.mp h0]; exact head_mem_polyline _ _
  have hd : unitDir x u ≠ 0 := by
    rw [unitDir]; refine div_ne_zero hu ?_
    rw [ofReal_ne_zero, norm_ne_zero_iff]; exact hu
  have h1 : cexp (windSum x (u :: l) * I) = 1 :=
    mul_right_cancel₀ hd (h.trans (one_mul _).symm)
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
  refine ⟨n, ?_⟩
  have : ((windSum x (u :: l) : ℝ) : ℂ) = ((2 * π * n : ℝ) : ℂ) := by
    have hI : (I : ℂ) ≠ 0 := I_ne_zero
    apply mul_right_cancel₀ hI
    rw [hn]; push_cast; ring
  exact_mod_cast this

lemma mem_slitPlane_of_not_mem_segment {u v x : ℂ} (h : x ∉ segment ℝ u v) :
    (v - x) / (u - x) ∈ slitPlane := by
  have hu : u - x ≠ 0 := by
    intro h0; apply h; rw [sub_eq_zero.mp h0]; exact left_mem_segment ℝ x v
  by_contra hq
  rw [mem_slitPlane_iff] at hq
  push_neg at hq
  obtain ⟨hre, him⟩ := hq
  set q := (v - x) / (u - x) with hqdef
  have hqr : q = ((q.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [him]
  have hvx : v - x = q * (u - x) := by rw [hqdef]; field_simp
  set s := -q.re with hs
  have hs0 : 0 ≤ s := by linarith
  apply h
  rw [segment_eq_image]
  refine ⟨1 / (1 + s), ⟨by positivity, ?_⟩, ?_⟩
  · rw [div_le_one (by positivity)]; linarith
  · have h1s : (1 + (s:ℂ)) ≠ 0 := by
      have : (0:ℝ) < 1 + s := by linarith
      exact_mod_cast this.ne'
    rw [hqr] at hvx
    have hv : v = x + (-(s:ℂ)) * (u - x) := by
      rw [hs]; push_cast; linear_combination hvx
    simp only [Complex.real_smul]
    rw [hv]
    push_cast
    field_simp
    ring

lemma continuousAt_windSum (x : ℂ) : ∀ (u : ℂ) (l : List ℂ), x ∉ polyline (u :: l) →
    ContinuousAt (fun y => windSum y (u :: l)) x
  | u, [], _ => by simp only [windSum]; exact continuousAt_const
  | u, v :: l, h => by
    have hu : u - x ≠ 0 := by
      intro h0; apply h; left; rw [sub_eq_zero.mp h0]; exact left_mem_segment ℝ x v
    have ih := continuousAt_windSum x v l (fun h' => h (Or.inr h'))
    simp only [windSum]
    refine ContinuousAt.add ?_ ih
    exact ContinuousAt.comp (g := arg) (f := fun y => (v - y) / (u - y))
      (continuousAt_arg (mem_slitPlane_of_not_mem_segment (fun h' => h (Or.inl h'))))
      ((continuousAt_const.sub continuousAt_id).div (continuousAt_const.sub continuousAt_id) hu)

lemma windSum_eq_of_isPreconnected {C : Set ℂ} (hC : IsPreconnected C) (u : ℂ) (l : List ℂ)
    (hc : (u :: l).getLast (by simp) = u) (hCp : ∀ y ∈ C, y ∉ polyline (u :: l))
    {y z : ℂ} (hy : y ∈ C) (hz : z ∈ C) : windSum y (u :: l) = windSum z (u :: l) := by
  have hd : IsDiscrete (range ((↑) : ℤ → ℝ)) :=
    IsEmbedding.isDiscrete_range Int.isClosedEmbedding_coe_real.isEmbedding.isInducing
  have hcont : ContinuousOn (fun w => windSum w (u :: l) / (2 * π)) C := by
    intro w hw
    exact ((continuousAt_windSum w u l (hCp w hw)).div_const _).continuousWithinAt
  have hmaps : MapsTo (fun w => windSum w (u :: l) / (2 * π)) C (range ((↑) : ℤ → ℝ)) := by
    intro w hw
    obtain ⟨n, hn⟩ := windSum_mem_int w u l (hCp w hw) hc
    refine ⟨n, ?_⟩
    simp only [hn]
    field_simp
  have := hC.constant_of_mapsTo hd hcont hmaps hy hz
  have hpi : (2 * π) ≠ 0 := by positivity
  field_simp at this
  exact this

end Winding

section Sides

def wc (a b z : ℂ) : ℂ := (z - a) / (b - a)

variable {a b : ℂ}

lemma wc_param (hab : a ≠ b) (w : ℂ) : wc a b (a + (b - a) * w) = w := by
  have : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  simp only [wc]; field_simp; ring

lemma eq_param (hab : a ≠ b) (z : ℂ) : z = a + (b - a) * wc a b z := by
  have : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  simp only [wc]; field_simp; ring

lemma wc_sub (z p : ℂ) : wc a b z - wc a b p = (z - p) / (b - a) := by
  simp only [wc]; ring

lemma norm_wc_sub (hab : a ≠ b) (z p : ℂ) :
    ‖wc a b z - wc a b p‖ * ‖b - a‖ = dist z p := by
  have : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  rw [wc_sub, norm_div, dist_eq_norm, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr this)]

lemma dist_param (w w' : ℂ) :
    dist (a + (b - a) * w) (a + (b - a) * w') = ‖b - a‖ * ‖w - w'‖ := by
  rw [dist_eq_norm, ← norm_mul]; congr 1; ring

lemma wc_swap (hab : a ≠ b) (z : ℂ) : wc b a z = 1 - wc a b z := by
  have : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have : a - b ≠ 0 := sub_ne_zero.mpr hab
  simp only [wc]; field_simp; ring

lemma wc_combo (x y : ℂ) (s t : ℝ) (hst : s + t = 1) :
    wc a b (s • x + t • y) = (s : ℂ) * wc a b x + (t : ℂ) * wc a b y := by
  have ht : (s : ℂ) + t = 1 := by exact_mod_cast hst
  have : s • x + t • y - a = (s : ℂ) * (x - a) + (t : ℂ) * (y - a) := by
    simp only [Complex.real_smul]; linear_combination a * ht
  rw [wc, this, add_div, mul_div_assoc, mul_div_assoc]
  rfl

lemma mem_openSegment_iff_wc (hab : a ≠ b) (z : ℂ) :
    z ∈ openSegment ℝ a b ↔ (wc a b z).im = 0 ∧ 0 < (wc a b z).re ∧ (wc a b z).re < 1 := by
  rw [openSegment_eq_image]
  constructor
  · rintro ⟨θ, ⟨h0, h1⟩, rfl⟩
    have : (1 - θ) • a + θ • b = a + (b - a) * (θ : ℂ) := by
      simp only [Complex.real_smul]; push_cast; ring
    dsimp only
    rw [this, wc_param hab]
    exact ⟨ofReal_im θ, by rw [ofReal_re]; exact h0, by rw [ofReal_re]; exact h1⟩
  · rintro ⟨him, h0, h1⟩
    refine ⟨(wc a b z).re, ⟨h0, h1⟩, ?_⟩
    have hw : ((wc a b z).re : ℂ) = wc a b z := Complex.ext (by simp) (by simp [him])
    conv_rhs => rw [eq_param hab z]
    simp only [Complex.real_smul]; push_cast; rw [hw]; ring

lemma mem_segment_iff_wc (hab : a ≠ b) (z : ℂ) :
    z ∈ segment ℝ a b ↔ (wc a b z).im = 0 ∧ 0 ≤ (wc a b z).re ∧ (wc a b z).re ≤ 1 := by
  rw [segment_eq_image]
  constructor
  · rintro ⟨θ, ⟨h0, h1⟩, rfl⟩
    have : (1 - θ) • a + θ • b = a + (b - a) * (θ : ℂ) := by
      simp only [Complex.real_smul]; push_cast; ring
    dsimp only
    rw [this, wc_param hab]
    exact ⟨ofReal_im θ, by rw [ofReal_re]; exact h0, by rw [ofReal_re]; exact h1⟩
  · rintro ⟨him, h0, h1⟩
    refine ⟨(wc a b z).re, ⟨h0, h1⟩, ?_⟩
    have hw : ((wc a b z).re : ℂ) = wc a b z := Complex.ext (by simp) (by simp [him])
    conv_rhs => rw [eq_param hab z]
    simp only [Complex.real_smul]; push_cast; rw [hw]; ring

def leftHalf (a b : ℂ) : Set ℂ := {z | 0 < (wc a b z).im}

lemma convex_leftHalf : Convex ℝ (leftHalf a b) := by
  intro x hx y hy s t hs ht hst
  have hx' : 0 < (wc a b x).im := hx
  have hy' : 0 < (wc a b y).im := hy
  show 0 < (wc a b (s • x + t • y)).im
  rw [wc_combo x y s t hst, add_im, im_ofReal_mul, im_ofReal_mul]
  have h1 := mul_nonneg hs hx'.le
  have h2 := mul_nonneg ht hy'.le
  by_cases hs0 : s = 0
  · have : t = 1 := by linarith
    rw [this, one_mul]; linarith
  · have := mul_pos (lt_of_le_of_ne hs (Ne.symm hs0)) hx'
    linarith

lemma mem_leftHalf_swap (hab : a ≠ b) (z : ℂ) : z ∈ leftHalf b a ↔ (wc a b z).im < 0 := by
  show 0 < (wc b a z).im ↔ _
  rw [wc_swap hab, sub_im, one_im]
  constructor <;> intro h <;> linarith

lemma exists_ball_local {H : Set ℂ} (hab : a ≠ b) (hH : IsClosed H) {p : ℂ}
    (hp : p ∈ openSegment ℝ a b) (hpH : p ∉ H) :
    ∃ r > 0, ball p r ⊆ Hᶜ ∧ ∀ z ∈ ball p r, (wc a b z).im = 0 → z ∈ openSegment ℝ a b := by
  obtain ⟨r1, hr1, hball⟩ := Metric.isOpen_iff.mp hH.isOpen_compl p hpH
  rw [mem_openSegment_iff_wc hab] at hp
  obtain ⟨_, h0, h1⟩ := hp
  have hba : 0 < ‖b - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab.symm)
  have hm : 0 < min (wc a b p).re (1 - (wc a b p).re) := lt_min h0 (by linarith)
  refine ⟨min r1 (min (wc a b p).re (1 - (wc a b p).re) * ‖b - a‖),
    lt_min hr1 (mul_pos hm hba), (ball_subset_ball (min_le_left _ _)).trans hball, ?_⟩
  intro z hz him
  rw [mem_openSegment_iff_wc hab]
  have hd := norm_wc_sub hab z p
  rw [mem_ball] at hz
  have hlt : ‖wc a b z - wc a b p‖ < min (wc a b p).re (1 - (wc a b p).re) := by
    have := lt_of_lt_of_le hz (min_le_right _ _)
    rw [← hd] at this
    exact lt_of_mul_lt_mul_right this hba.le
  have hre := (abs_re_le_norm (wc a b z - wc a b p)).trans_lt hlt
  rw [sub_re, abs_lt] at hre
  have := min_le_left (wc a b p).re (1 - (wc a b p).re)
  have := min_le_right (wc a b p).re (1 - (wc a b p).re)
  exact ⟨him, by linarith, by linarith⟩

lemma exists_strip {H : Set ℂ} (hab : a ≠ b) (hH : IsClosed H)
    (hseg : ∀ z ∈ openSegment ℝ a b, z ∉ H) {t1 t2 : ℝ} (h1 : t1 ∈ Ioo (0:ℝ) 1)
    (h2 : t2 ∈ Ioo (0:ℝ) 1) :
    ∃ ε > 0, ∀ t ∈ uIcc t1 t2, ∀ s : ℝ, |s| < ε → a + (b - a) * (t + s * I) ∉ H := by
  set K := (fun t : ℝ => a + (b - a) * t) '' uIcc t1 t2 with hK
  have hKc : IsCompact K := isCompact_uIcc.image (by fun_prop)
  have hKH : K ⊆ Hᶜ := by
    rintro _ ⟨t, ht, rfl⟩
    apply hseg
    have ht' := (ordConnected_Ioo.uIcc_subset h1 h2) ht
    rw [mem_openSegment_iff_wc hab, wc_param hab]
    exact ⟨ofReal_im t, by rw [ofReal_re]; exact ht'.1, by rw [ofReal_re]; exact ht'.2⟩
  obtain ⟨δ, hδ, hth⟩ := hKc.exists_thickening_subset_open hH.isOpen_compl hKH
  have hba : 0 < ‖b - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab.symm)
  refine ⟨δ / ‖b - a‖, div_pos hδ hba, ?_⟩
  intro t ht s hs
  apply hth
  rw [mem_thickening_iff]
  refine ⟨a + (b - a) * t, ⟨t, ht, rfl⟩, ?_⟩
  rw [dist_param]
  have : (t : ℂ) + s * I - t = s * I := by ring
  rw [this, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs]
  rw [lt_div_iff₀ hba] at hs
  linarith

def box (a b : ℂ) (T S : Set ℝ) : Set ℂ :=
  (fun q : ℝ × ℝ => a + (b - a) * (q.1 + q.2 * I)) '' (T ×ˢ S)

lemma isPreconnected_box {T S : Set ℝ} (hT : IsPreconnected T) (hS : IsPreconnected S) :
    IsPreconnected (box a b T S) :=
  (hT.prod hS).image _ (by fun_prop)

lemma mem_box {T S : Set ℝ} {t s : ℝ} (ht : t ∈ T) (hs : s ∈ S) :
    a + (b - a) * (t + s * I) ∈ box a b T S := ⟨(t, s), ⟨ht, hs⟩, rfl⟩

lemma ball_subset_comp {H : Set ℂ} {p0 p : ℂ} {r : ℝ} (hr : ball p r ⊆ Hᶜ)
    (hp : p ∈ connectedComponentIn Hᶜ p0) (hr0 : 0 < r) :
    ball p r ⊆ connectedComponentIn Hᶜ p0 := by
  rw [connectedComponentIn_eq hp]
  exact (convex_ball p r).isPreconnected.subset_connectedComponentIn (mem_ball_self hr0) hr

lemma openSegment_subset_comp {H : Set ℂ} {p0 : ℂ} (hseg : ∀ z ∈ openSegment ℝ a b, z ∉ H)
    (hp0 : p0 ∈ openSegment ℝ a b) : openSegment ℝ a b ⊆ connectedComponentIn Hᶜ p0 :=
  (convex_openSegment a b).isPreconnected.subset_connectedComponentIn hp0 hseg

lemma exists_left_comp {H A : Set ℂ} (hab : a ≠ b) (hH : IsClosed H)
    (hseg : ∀ z ∈ openSegment ℝ a b, z ∉ H) (hA : ∀ z ∈ A, (wc a b z).im = 0) {p0 : ℂ}
    (hp0 : p0 ∈ openSegment ℝ a b) :
    ∃ xL ∈ connectedComponentIn Hᶜ p0 \ A, ∀ p ∈ openSegment ℝ a b, ∃ r > 0,
      ball p r ⊆ connectedComponentIn Hᶜ p0 ∧
      (∀ z ∈ ball p r, (wc a b z).im = 0 → z ∈ openSegment ℝ a b) ∧
      ball p r ∩ leftHalf a b ⊆ connectedComponentIn (connectedComponentIn Hᶜ p0 \ A) xL := by
  set U := connectedComponentIn Hᶜ p0 with hU
  have hsegU := openSegment_subset_comp (H := H) hseg hp0
  have hba : 0 < ‖b - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab.symm)

  have hloc : ∀ p ∈ openSegment ℝ a b, ∃ r > 0, ball p r ⊆ U ∧
      ∀ z ∈ ball p r, (wc a b z).im = 0 → z ∈ openSegment ℝ a b := by
    intro p hp
    obtain ⟨r, hr, hrH, hline⟩ := exists_ball_local hab hH hp (hseg p hp)
    exact ⟨r, hr, ball_subset_comp hrH (hsegU hp) hr, hline⟩
  have hDsub : ∀ p ∈ openSegment ℝ a b, ∀ r > 0, ball p r ⊆ U →
      ball p r ∩ leftHalf a b ⊆ U \ A := by
    intro p _ r _ hr z hz
    refine ⟨hr hz.1, fun hzA => ?_⟩
    have := hA z hzA
    have h2 : 0 < (wc a b z).im := hz.2
    linarith

  set m := a + (b - a) * ((1/2 : ℝ) : ℂ) with hm
  have hmseg : m ∈ openSegment ℝ a b := by
    rw [mem_openSegment_iff_wc hab, hm, wc_param hab]
    norm_num
  obtain ⟨rm, hrm, hrmU, _⟩ := hloc m hmseg
  set s0 := rm / (2 * ‖b - a‖) with hs0
  have hs0pos : 0 < s0 := by positivity
  set xL := a + (b - a) * (((1/2 : ℝ) : ℂ) + s0 * I) with hxL
  have hxLball : xL ∈ ball m rm := by
    rw [mem_ball, hxL, hm, dist_param]
    have : ((1/2 : ℝ) : ℂ) + s0 * I - ((1/2 : ℝ) : ℂ) = s0 * I := by ring
    rw [this, norm_mul, norm_I, mul_one, norm_real, Real.norm_of_nonneg hs0pos.le, hs0]
    field_simp
    linarith
  have hxLleft : xL ∈ leftHalf a b := by
    show 0 < (wc a b xL).im
    rw [hxL, wc_param hab]; simpa using hs0pos
  have hxLUA : xL ∈ U \ A := hDsub m hmseg rm hrm hrmU ⟨hxLball, hxLleft⟩
  refine ⟨xL, hxLUA, ?_⟩
  intro p hp
  obtain ⟨r, hr, hrU, hline⟩ := hloc p hp
  refine ⟨r, hr, hrU, hline, ?_⟩

  have hpw := (mem_openSegment_iff_wc hab p).mp hp
  set τ := (wc a b p).re with hτ
  have hpτ : p = a + (b - a) * (τ : ℂ) := by
    conv_lhs => rw [eq_param hab p]
    congr 2
    exact Complex.ext (by simp [hτ]) (by simp [hpw.1])
  obtain ⟨ε, hε, hstrip⟩ := exists_strip hab hH hseg (t1 := τ) (t2 := 1/2)
    ⟨hpw.2.1, hpw.2.2⟩ (by norm_num)
  set Q := box a b (uIcc τ (1/2)) (Ioo 0 ε) with hQ
  set Q' := box a b (uIcc τ (1/2)) (Ico 0 ε) with hQ'
  have hQ'H : Q' ⊆ Hᶜ := by
    rintro _ ⟨⟨t, s⟩, ⟨ht, hs⟩, rfl⟩
    exact hstrip t ht s (by rw [abs_of_nonneg hs.1]; exact hs.2)
  have hQ'U : Q' ⊆ U := by
    rw [hU, connectedComponentIn_eq (hsegU hp)]
    refine (isPreconnected_box isPreconnected_uIcc (convex_Ico 0 ε).isPreconnected
      ).subset_connectedComponentIn ?_ hQ'H
    rw [hpτ]
    have := mem_box (a := a) (b := b) (left_mem_uIcc (a := τ) (b := 1/2))
      (show (0:ℝ) ∈ Ico 0 ε from ⟨le_rfl, hε⟩)
    simpa using this
  have hQUA : Q ⊆ U \ A := by
    rintro _ ⟨⟨t, s⟩, ⟨ht, hs⟩, rfl⟩
    refine ⟨hQ'U (mem_box ht ⟨hs.1.le, hs.2⟩), fun hzA => ?_⟩
    have := hA _ hzA
    rw [wc_param hab] at this
    simp at this
    exact hs.1.ne' this

  have hDp : IsPreconnected (ball p r ∩ leftHalf a b) :=
    ((convex_ball p r).inter convex_leftHalf).isPreconnected
  have hDm : IsPreconnected (ball m rm ∩ leftHalf a b) :=
    ((convex_ball m rm).inter convex_leftHalf).isPreconnected
  have hQc : IsPreconnected Q :=
    isPreconnected_box isPreconnected_uIcc (convex_Ioo 0 ε).isPreconnected

  have hmeet : ∀ (t : ℝ) (c : ℂ) (ρ : ℝ), 0 < ρ → t ∈ uIcc τ (1/2) →
      c = a + (b - a) * (t : ℂ) →
      ∃ z, z ∈ ball c ρ ∩ leftHalf a b ∧ z ∈ Q := by
    intro t c ρ hρ ht hc
    set s := min (ε / 2) (ρ / (2 * ‖b - a‖)) with hsdef
    have hspos : 0 < s := lt_min (by positivity) (by positivity)
    refine ⟨a + (b - a) * (t + s * I), ⟨?_, ?_⟩, mem_box ht ⟨hspos, ?_⟩⟩
    · rw [mem_ball, hc, dist_param]
      have : (t : ℂ) + s * I - t = s * I := by ring
      rw [this, norm_mul, norm_I, mul_one, norm_real, Real.norm_of_nonneg hspos.le]
      have h1 : s ≤ ρ / (2 * ‖b - a‖) := min_le_right _ _
      calc ‖b - a‖ * s ≤ ‖b - a‖ * (ρ / (2 * ‖b - a‖)) := by gcongr
        _ = ρ / 2 := by field_simp
        _ < ρ := by linarith
    · show 0 < (wc a b _).im
      rw [wc_param hab]; simpa using hspos
    · have : s ≤ ε / 2 := min_le_left _ _
      linarith
  obtain ⟨z1, hz1D, hz1Q⟩ := hmeet τ p r hr left_mem_uIcc hpτ
  obtain ⟨z2, hz2D, hz2Q⟩ := hmeet (1/2) m rm hrm right_mem_uIcc (by rw [hm])
  have hU1 : IsPreconnected ((ball m rm ∩ leftHalf a b) ∪ Q) :=
    hDm.union z2 hz2D hz2Q hQc
  have hU2 : IsPreconnected (((ball m rm ∩ leftHalf a b) ∪ Q) ∪ (ball p r ∩ leftHalf a b)) :=
    hU1.union z1 (Or.inr hz1Q) hz1D hDp
  have hsub : ((ball m rm ∩ leftHalf a b) ∪ Q) ∪ (ball p r ∩ leftHalf a b) ⊆ U \ A := by
    refine union_subset (union_subset (hDsub m hmseg rm hrm hrmU) hQUA)
      (hDsub p hp r hr hrU)
  have := hU2.subset_connectedComponentIn (Or.inl (Or.inl ⟨hxLball, hxLleft⟩)) hsub
  exact fun z hz => this (Or.inr hz)

end Sides

section Cutting

variable {a b : ℂ}

lemma isClosed_segment' (a b : ℂ) : IsClosed (segment ℝ a b) := by
  rw [segment_eq_image]
  exact (isCompact_Icc.image (by fun_prop)).isClosed

lemma cover_two {U A : Set ℂ} (hUc : IsPreconnected U) (hUA : IsOpen (U \ A))
    {xL xR : ℂ} (hxL : xL ∈ U \ A)
    (hloc : ∀ p ∈ A, ∃ r > 0, ball p r ⊆
      connectedComponentIn (U \ A) xL ∪ connectedComponentIn (U \ A) xR ∪ A) :
    ∀ z ∈ U \ A, z ∈ connectedComponentIn (U \ A) xL ∨ z ∈ connectedComponentIn (U \ A) xR := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨z, hz, hzL, hzR⟩ := hcon
  choose! r hr hrsub using hloc
  set CL := connectedComponentIn (U \ A) xL with hCL
  set CR := connectedComponentIn (U \ A) xR with hCR
  set Z := {y | y ∈ U \ A ∧ y ∉ CL ∧ y ∉ CR} with hZ
  set O := CL ∪ CR ∪ ⋃ p ∈ A, ball p (r p) with hO
  have hZo : IsOpen Z := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    apply Filter.mem_of_superset ((hUA.connectedComponentIn (x := y)).mem_nhds
      (mem_connectedComponentIn hy.1))
    intro w hw
    refine ⟨connectedComponentIn_subset _ _ hw, ?_, ?_⟩
    · intro hwL; apply hy.2.1
      rw [hCL, connectedComponentIn_eq hwL, ← connectedComponentIn_eq hw]
      exact mem_connectedComponentIn hy.1
    · intro hwR; apply hy.2.2
      rw [hCR, connectedComponentIn_eq hwR, ← connectedComponentIn_eq hw]
      exact mem_connectedComponentIn hy.1
  have hOo : IsOpen O :=
    ((hUA.connectedComponentIn).union hUA.connectedComponentIn).union
      (isOpen_biUnion fun _ _ => isOpen_ball)
  have hcov : U ⊆ Z ∪ O := by
    intro y hy
    by_cases hyA : y ∈ A
    · right; right
      exact mem_biUnion hyA (mem_ball_self (hr y hyA))
    · by_cases hyL : y ∈ CL
      · right; left; left; exact hyL
      · by_cases hyR : y ∈ CR
        · right; left; right; exact hyR
        · left; exact ⟨⟨hy, hyA⟩, hyL, hyR⟩
  obtain ⟨y, _, hyZ, hyO⟩ := hUc Z O hZo hOo hcov ⟨z, hz.1, hz, hzL, hzR⟩
    ⟨xL, hxL.1, Or.inl (Or.inl (mem_connectedComponentIn hxL))⟩
  rcases hyO with (hyL | hyR) | hyB
  · exact hyZ.2.1 hyL
  · exact hyZ.2.2 hyR
  · obtain ⟨p, hp, hyp⟩ := mem_iUnion₂.mp hyB
    rcases hrsub p hp hyp with (h1 | h1) | h1
    · exact hyZ.2.1 h1
    · exact hyZ.2.2 h1
    · exact hyZ.1.2 h1

lemma div_param_eq (hab : a ≠ b) {w : ℂ} (hw : w ≠ 0) :
    (b - (a + (b - a) * w)) / (a - (a + (b - a) * w)) = (w - 1) / w := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  rw [div_eq_div_iff (by
    intro h; apply hw
    have : (b - a) * w = 0 := by linear_combination -h
    exact (mul_eq_zero.mp this).resolve_left hba) hw]
  ring

lemma arg_jump_pos {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1 / 2) :
    π / 2 < arg ((((1/2 : ℝ) : ℂ) + s * I - 1) / (((1/2 : ℝ) : ℂ) + s * I)) := by
  set q := (((1/2 : ℝ) : ℂ) + s * I - 1) / (((1/2 : ℝ) : ℂ) + s * I) with hq
  have hn : 0 < normSq (((1/2 : ℝ) : ℂ) + s * I) := by
    rw [normSq_pos]; intro h
    have := congrArg Complex.re h; simp at this
  have hre : q.re < 0 := by
    rw [hq, div_re]
    simp only [sub_re, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, one_re, sub_im, add_im,
      mul_im, one_im]
    rw [← add_div]
    apply div_neg_of_neg_of_pos _ hn
    nlinarith
  have him : 0 < q.im := by
    rw [hq, div_im]
    simp only [sub_re, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, one_re, sub_im, add_im,
      mul_im, one_im]
    rw [← sub_div]
    apply div_pos _ hn
    nlinarith
  have h1 : ¬ |arg q| ≤ π / 2 := by rw [abs_arg_le_pi_div_two_iff]; linarith
  have h2 : 0 ≤ arg q := arg_nonneg_iff.mpr him.le
  rw [abs_of_nonneg h2] at h1
  linarith

lemma arg_jump_neg {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1 / 2) :
    arg ((((1/2 : ℝ) : ℂ) + ((-s : ℝ) : ℂ) * I - 1) / (((1/2 : ℝ) : ℂ) + ((-s : ℝ) : ℂ) * I))
      < -(π / 2) := by
  set q := (((1/2 : ℝ) : ℂ) + ((-s : ℝ) : ℂ) * I - 1) / (((1/2 : ℝ) : ℂ) + ((-s : ℝ) : ℂ) * I)
    with hq
  have hn : 0 < normSq (((1/2 : ℝ) : ℂ) + ((-s : ℝ) : ℂ) * I) := by
    rw [normSq_pos]; intro h
    have := congrArg Complex.re h; simp at this
  have hre : q.re < 0 := by
    rw [hq, div_re]
    simp only [sub_re, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, one_re, sub_im, add_im,
      mul_im, one_im]
    rw [← add_div]
    apply div_neg_of_neg_of_pos _ hn
    nlinarith
  have him : q.im < 0 := by
    rw [hq, div_im]
    simp only [sub_re, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, one_re, sub_im, add_im,
      mul_im, one_im]
    rw [← sub_div]
    apply div_neg_of_neg_of_pos _ hn
    nlinarith
  have h1 : ¬ |arg q| ≤ π / 2 := by rw [abs_arg_le_pi_div_two_iff]; linarith
  have h2 : arg q < 0 := arg_neg_iff.mpr him
  rw [abs_of_neg h2] at h1
  linarith

lemma polyline_subset {H : Set ℂ} : ∀ (u : ℂ) (l : List ℂ),
    List.IsChain (fun x y => segment ℝ x y ⊆ H) (u :: l) → u ∈ H → polyline (u :: l) ⊆ H
  | u, [], _, hu => by simpa [polyline] using hu
  | u, v :: l, h, _ => by
    rw [List.isChain_cons_cons] at h
    refine union_subset h.1 (polyline_subset v l h.2 (h.1 (right_mem_segment ℝ u v)))

lemma encard_comps_cut_cycle {H : Set ℂ} (hH : IsClosed H) (hab : a ≠ b) (ha : a ∈ H)
    (hb : b ∈ H) (hseg : ∀ z ∈ openSegment ℝ a b, z ∉ H) {l : List ℂ}
    (hchain : List.IsChain (fun x y => segment ℝ x y ⊆ H) (b :: l))
    (hlast : (b :: l).getLast (by simp) = a) {p0 : ℂ} (hp0 : p0 ∈ openSegment ℝ a b) :
    (comps (connectedComponentIn Hᶜ p0 \ openSegment ℝ a b)).encard = 2 := by
  set U := connectedComponentIn Hᶜ p0 with hU
  set A := openSegment ℝ a b with hAdef
  have hA : ∀ z ∈ A, (wc a b z).im = 0 := fun z hz => ((mem_openSegment_iff_wc hab z).mp hz).1
  have hA' : ∀ z ∈ A, (wc b a z).im = 0 := by
    intro z hz; rw [wc_swap hab, sub_im, one_im, hA z hz]; ring
  have hseg' : ∀ z ∈ openSegment ℝ b a, z ∉ H := by rw [openSegment_symm]; exact hseg
  have hp0' : p0 ∈ openSegment ℝ b a := by rw [openSegment_symm]; exact hp0
  obtain ⟨xL, hxL, hL⟩ := exists_left_comp hab hH hseg hA hp0
  obtain ⟨xR, hxR, hR⟩ := exists_left_comp hab.symm hH hseg' hA' hp0'
  set CL := connectedComponentIn (U \ A) xL with hCL
  set CR := connectedComponentIn (U \ A) xR with hCR
  have hUH : U ⊆ Hᶜ := connectedComponentIn_subset _ _
  have hUA : IsOpen (U \ A) := by
    have : U \ A = U ∩ (segment ℝ a b)ᶜ := by
      ext z
      simp only [mem_diff, mem_inter_iff, mem_compl_iff, hAdef,
        ← insert_endpoints_openSegment, mem_insert_iff, not_or]
      constructor
      · rintro ⟨hz, hzA⟩
        exact ⟨hz, fun h => hUH hz (h ▸ ha), fun h => hUH hz (h ▸ hb), hzA⟩
      · rintro ⟨hz, _, _, hzA⟩; exact ⟨hz, hzA⟩
    rw [this]
    exact (hH.isOpen_compl.connectedComponentIn).inter (isClosed_segment' a b).isOpen_compl

  have hloc : ∀ p ∈ A, ∃ r > 0, ball p r ⊆ CL ∪ CR ∪ A := by
    intro p hp
    obtain ⟨r1, hr1, -, hline, hsub1⟩ := hL p hp
    obtain ⟨r2, hr2, -, -, hsub2⟩ := hR p (by rw [openSegment_symm]; exact hp)
    refine ⟨min r1 r2, lt_min hr1 hr2, ?_⟩
    intro z hz
    have hz1 : z ∈ ball p r1 := ball_subset_ball (min_le_left _ _) hz
    have hz2 : z ∈ ball p r2 := ball_subset_ball (min_le_right _ _) hz
    rcases lt_trichotomy (wc a b z).im 0 with h | h | h
    · left; right; exact hsub2 ⟨hz2, (mem_leftHalf_swap hab z).mpr h⟩
    · right; exact hline z hz1 h
    · left; left; exact hsub1 ⟨hz1, h⟩
  have hcov := cover_two isPreconnected_connectedComponentIn hUA hxL hloc
  rw [comps_eq_pair hxL hxR hcov]
  apply encard_pair

  intro hLR
  have hba : 0 < ‖b - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab.symm)
  set m := a + (b - a) * ((1/2 : ℝ) : ℂ) with hm
  have hmseg : m ∈ A := by
    rw [hAdef, mem_openSegment_iff_wc hab, hm, wc_param hab]
    norm_num
  obtain ⟨r1, hr1, -, -, hsub1⟩ := hL m hmseg
  obtain ⟨r2, hr2, -, -, hsub2⟩ := hR m (by rw [openSegment_symm]; exact hmseg)
  have hmH : m ∉ H := hseg m hmseg
  have hpolyH : polyline (b :: l) ⊆ H := polyline_subset b l hchain hb
  have hgc := continuousAt_windSum m b l (fun h => hmH (hpolyH h))
  obtain ⟨δ, hδ, hδg⟩ := Metric.continuousAt_iff.mp hgc (π / 2) (by positivity)
  set r0 := min (min r1 r2) (min δ (‖b - a‖ / 2)) with hr0
  have hr0pos : 0 < r0 := lt_min (lt_min hr1 hr2) (lt_min hδ (by positivity))
  set s := r0 / (2 * ‖b - a‖) with hs
  have hspos : 0 < s := by positivity
  have hs_half : s < 1 / 2 := by
    rw [hs, div_lt_iff₀ (by positivity)]
    have : r0 ≤ ‖b - a‖ / 2 := (min_le_right _ _).trans (min_le_right _ _)
    linarith
  have hdist : ∀ σ : ℝ, |σ| = s →
      dist (a + (b - a) * (((1/2 : ℝ) : ℂ) + σ * I)) m = r0 / 2 := by
    intro σ hσ
    rw [hm, dist_param]
    have : ((1/2 : ℝ) : ℂ) + σ * I - ((1/2 : ℝ) : ℂ) = σ * I := by ring
    rw [this, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, hσ, hs]
    field_simp
  set xL' := a + (b - a) * (((1/2 : ℝ) : ℂ) + s * I) with hxL'
  set xR' := a + (b - a) * (((1/2 : ℝ) : ℂ) + ((-s : ℝ) : ℂ) * I) with hxR'
  have hdL : dist xL' m < r0 := by rw [hdist s (abs_of_pos hspos)]; linarith
  have hdR : dist xR' m < r0 := by rw [hdist (-s) (by rw [abs_neg, abs_of_pos hspos])]; linarith
  have hr0r1 : r0 ≤ r1 := (min_le_left _ _).trans (min_le_left _ _)
  have hr0r2 : r0 ≤ r2 := (min_le_left _ _).trans (min_le_right _ _)
  have hr0δ : r0 ≤ δ := (min_le_right _ _).trans (min_le_left _ _)
  have hxL'C : xL' ∈ CL := by
    refine hsub1 ⟨lt_of_lt_of_le hdL hr0r1, ?_⟩
    show 0 < (wc a b xL').im
    rw [hxL', wc_param hab]; simpa using hspos
  have hxR'C : xR' ∈ CR := by
    refine hsub2 ⟨lt_of_lt_of_le hdR hr0r2, ?_⟩
    rw [mem_leftHalf_swap hab, hxR', wc_param hab]; simpa using hspos

  have hclosed : (a :: b :: l).getLast (by simp) = a := by
    rw [List.getLast_cons_cons]; exact hlast
  have havoid : ∀ y ∈ CL, y ∉ polyline (a :: b :: l) := by
    intro y hy hpoly
    have hyUA : y ∈ U \ A := connectedComponentIn_subset _ _ hy
    rcases hpoly with hy1 | hy1
    · rw [← insert_endpoints_openSegment] at hy1
      rcases hy1 with rfl | rfl | hy1
      · exact hUH hyUA.1 ha
      · exact hUH hyUA.1 hb
      · exact hyUA.2 hy1
    · exact hUH hyUA.1 (hpolyH hy1)
  have heq := windSum_eq_of_isPreconnected isPreconnected_connectedComponentIn a (b :: l)
    hclosed havoid hxL'C (by show xR' ∈ connectedComponentIn (U \ A) xL; rw [hLR]; exact hxR'C)
  simp only [windSum] at heq
  have hw1 : (((1/2 : ℝ) : ℂ) + s * I) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have hw2 : (((1/2 : ℝ) : ℂ) + ((-s : ℝ) : ℂ) * I) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  rw [hxL', hxR', div_param_eq hab hw1, div_param_eq hab hw2] at heq
  have hj1 := arg_jump_pos hspos hs_half
  have hj2 := arg_jump_neg hspos hs_half
  have hgL := hδg (lt_of_lt_of_le hdL hr0δ)
  have hgR := hδg (lt_of_lt_of_le hdR hr0δ)
  rw [Real.dist_eq, abs_lt] at hgL hgR
  rw [← hxL', ← hxR'] at heq
  linarith

lemma convex_re_gt (c : ℝ) : Convex ℝ {z | c < (wc a b z).re} := by
  intro x hx y hy s t hs ht hst
  have hx' : c < (wc a b x).re := hx
  have hy' : c < (wc a b y).re := hy
  show c < (wc a b (s • x + t • y)).re
  rw [wc_combo x y s t hst, add_re, re_ofReal_mul, re_ofReal_mul]
  by_cases hs0 : s = 0
  · have : t = 1 := by linarith
    rw [this, hs0]; simp; linarith
  · have hs' : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
    have h1 := mul_pos hs' (sub_pos.mpr hx')
    have h2 := mul_nonneg ht (sub_pos.mpr hy').le
    have key : s * (wc a b x).re + t * (wc a b y).re - c =
        s * ((wc a b x).re - c) + t * ((wc a b y).re - c) := by linear_combination c * hst
    linarith

lemma encard_comps_cut_leaf {H : Set ℂ} (hH : IsClosed H) (hab : a ≠ b) (ha : a ∈ H)
    (hb : b ∉ H) (hseg : ∀ z ∈ openSegment ℝ a b, z ∉ H) {p0 : ℂ}
    (hp0 : p0 ∈ openSegment ℝ a b) :
    (comps (connectedComponentIn Hᶜ p0 \ insert b (openSegment ℝ a b))).encard = 1 := by
  set U := connectedComponentIn Hᶜ p0 with hU
  set A := insert b (openSegment ℝ a b) with hAdef
  have hwb : wc a b b = 1 := by
    have : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
    simp [wc, this]
  have hA : ∀ z ∈ A, (wc a b z).im = 0 := by
    rintro z (rfl | hz)
    · rw [hwb]; simp
    · exact ((mem_openSegment_iff_wc hab z).mp hz).1
  have hA' : ∀ z ∈ A, (wc b a z).im = 0 := by
    intro z hz; rw [wc_swap hab, sub_im, one_im, hA z hz]; ring
  have hseg' : ∀ z ∈ openSegment ℝ b a, z ∉ H := by rw [openSegment_symm]; exact hseg
  have hp0' : p0 ∈ openSegment ℝ b a := by rw [openSegment_symm]; exact hp0
  obtain ⟨xL, hxL, hL⟩ := exists_left_comp hab hH hseg hA hp0
  obtain ⟨xR, hxR, hR⟩ := exists_left_comp hab.symm hH hseg' hA' hp0'
  set CL := connectedComponentIn (U \ A) xL with hCL
  set CR := connectedComponentIn (U \ A) xR with hCR
  have hUH : U ⊆ Hᶜ := connectedComponentIn_subset _ _
  have hsegU : openSegment ℝ a b ⊆ U := openSegment_subset_comp hseg hp0
  have hUA : IsOpen (U \ A) := by
    have : U \ A = U ∩ (segment ℝ a b)ᶜ := by
      ext z
      simp only [mem_diff, mem_inter_iff, mem_compl_iff, hAdef,
        ← insert_endpoints_openSegment, mem_insert_iff, not_or]
      constructor
      · rintro ⟨hz, hzb, hzA⟩
        exact ⟨hz, fun h => hUH hz (h ▸ ha), hzb, hzA⟩
      · rintro ⟨hz, _, hzb, hzA⟩; exact ⟨hz, hzb, hzA⟩
    rw [this]
    exact (hH.isOpen_compl.connectedComponentIn).inter (isClosed_segment' a b).isOpen_compl
  have hba : 0 < ‖b - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab.symm)

  obtain ⟨r0, hr0, hr0H⟩ := Metric.isOpen_iff.mp hH.isOpen_compl b hb
  set ρ := min r0 (‖b - a‖ / 2) with hρ
  have hρpos : 0 < ρ := lt_min hr0 (by positivity)
  set σ := ρ / (4 * ‖b - a‖) with hσ
  have hσpos : 0 < σ := by positivity
  have hσρ : σ * ‖b - a‖ = ρ / 4 := by rw [hσ]; field_simp
  have hσ1 : σ < 1 / 2 := by
    have : ρ ≤ ‖b - a‖ / 2 := min_le_right _ _
    rw [hσ, div_lt_iff₀ (by positivity)]; linarith
  set p1 := a + (b - a) * (((1 - σ : ℝ)) : ℂ) with hp1
  have hp1seg : p1 ∈ openSegment ℝ a b := by
    rw [mem_openSegment_iff_wc hab, hp1, wc_param hab]
    simp only [ofReal_im, ofReal_re, true_and]
    constructor <;> linarith
  have hbeq : b = a + (b - a) * ((1 : ℝ) : ℂ) := by push_cast; ring
  have hdist_b : ∀ w : ℂ, dist (a + (b - a) * w) b = ‖b - a‖ * ‖w - 1‖ := by
    intro w; rw [dist_eq_norm, ← norm_mul]; congr 1; ring
  have hp1ball : p1 ∈ ball b ρ := by
    rw [mem_ball, hp1, hdist_b]
    have : ((1 - σ : ℝ) : ℂ) - 1 = ((-σ : ℝ) : ℂ) := by push_cast; ring
    rw [this, norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hσpos, mul_comm, hσρ]
    linarith
  have hballH : ball b ρ ⊆ Hᶜ := (ball_subset_ball (min_le_left _ _)).trans hr0H
  have hballU : ball b ρ ⊆ U := by
    rw [hU, connectedComponentIn_eq (hsegU hp1seg)]
    exact (convex_ball b ρ).isPreconnected.subset_connectedComponentIn hp1ball hballH

  have hnotA : ∀ z, (wc a b z).im ≠ 0 ∨ 1 < (wc a b z).re → z ∉ A := by
    intro z hz hzA
    rcases hzA with rfl | hzA
    · rw [hwb] at hz; simp at hz
    · rw [mem_openSegment_iff_wc hab] at hzA
      rcases hz with hz | hz
      · exact hz hzA.1
      · linarith [hzA.2.2]

  set BL := ball b ρ ∩ leftHalf a b with hBL
  set BR := ball b ρ ∩ leftHalf b a with hBR
  set BK := ball b ρ ∩ {z | 1 < (wc a b z).re} with hBK
  have hBLsub : BL ⊆ U \ A := fun z hz =>
    ⟨hballU hz.1, hnotA z (Or.inl (ne_of_gt hz.2))⟩
  have hBRsub : BR ⊆ U \ A := fun z hz =>
    ⟨hballU hz.1, hnotA z (Or.inl (ne_of_lt ((mem_leftHalf_swap hab z).mp hz.2)))⟩
  have hBKsub : BK ⊆ U \ A := fun z hz => ⟨hballU hz.1, hnotA z (Or.inr hz.2)⟩
  have hBLc : IsPreconnected BL := ((convex_ball b ρ).inter convex_leftHalf).isPreconnected
  have hBRc : IsPreconnected BR := ((convex_ball b ρ).inter convex_leftHalf).isPreconnected
  have hBKc : IsPreconnected BK := ((convex_ball b ρ).inter (convex_re_gt 1)).isPreconnected

  have hnear : ∀ w : ℂ, ‖w - 1‖ * ‖b - a‖ < ρ → a + (b - a) * w ∈ ball b ρ := by
    intro w hw; rw [mem_ball, hdist_b, mul_comm]; exact hw

  obtain ⟨r1, hr1, -, -, hsub1⟩ := hL p1 hp1seg
  obtain ⟨r2, hr2, -, -, hsub2⟩ := hR p1 (by rw [openSegment_symm]; exact hp1seg)
  set τ := min σ (min r1 r2 / (2 * ‖b - a‖)) with hτ
  have hτpos : 0 < τ := lt_min hσpos (by have := lt_min hr1 hr2; positivity)
  have hτσ : τ ≤ σ := min_le_left _ _
  have hτr : τ * ‖b - a‖ ≤ min r1 r2 / 2 := by
    have : τ ≤ min r1 r2 / (2 * ‖b - a‖) := min_le_right _ _
    calc τ * ‖b - a‖ ≤ min r1 r2 / (2 * ‖b - a‖) * ‖b - a‖ := by gcongr
      _ = min r1 r2 / 2 := by field_simp
  have hnorm2 : ∀ x y : ℝ, ‖((x : ℂ) + y * I)‖ ≤ |x| + |y| := by
    intro x y
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_I, mul_one, norm_real, norm_real, Real.norm_eq_abs, Real.norm_eq_abs]

  have hpt : ∀ ε : ℝ, |ε| = τ → a + (b - a) * (((1 - σ : ℝ) : ℂ) + ε * I) ∈ ball b ρ ∧
      a + (b - a) * (((1 - σ : ℝ) : ℂ) + ε * I) ∈ ball p1 r1 ∧
      a + (b - a) * (((1 - σ : ℝ) : ℂ) + ε * I) ∈ ball p1 r2 := by
    intro ε hε
    have hd1 : dist (a + (b - a) * (((1 - σ : ℝ) : ℂ) + ε * I)) p1 = τ * ‖b - a‖ := by
      rw [hp1, dist_param]
      have : ((1 - σ : ℝ) : ℂ) + ε * I - ((1 - σ : ℝ) : ℂ) = ε * I := by ring
      rw [this, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, hε, mul_comm]
    have hm1 : min r1 r2 ≤ r1 := min_le_left _ _
    have hm2 : min r1 r2 ≤ r2 := min_le_right _ _
    have hmpos : 0 < min r1 r2 := lt_min hr1 hr2
    refine ⟨hnear _ ?_, ?_, ?_⟩
    · have : ((1 - σ : ℝ) : ℂ) + ε * I - 1 = ((-σ : ℝ) : ℂ) + ε * I := by push_cast; ring
      rw [this]
      calc ‖((-σ : ℝ) : ℂ) + ε * I‖ * ‖b - a‖ ≤ (|-σ| + |ε|) * ‖b - a‖ := by
            gcongr; exact hnorm2 _ _
        _ = σ * ‖b - a‖ + τ * ‖b - a‖ := by rw [abs_neg, abs_of_pos hσpos, hε]; ring
        _ ≤ σ * ‖b - a‖ + σ * ‖b - a‖ := by gcongr
        _ < ρ := by rw [hσρ]; linarith
    · rw [mem_ball, hd1]; linarith
    · rw [mem_ball, hd1]; linarith
  set zL := a + (b - a) * (((1 - σ : ℝ) : ℂ) + τ * I) with hzL
  set zR := a + (b - a) * (((1 - σ : ℝ) : ℂ) + ((-τ : ℝ) : ℂ) * I) with hzR
  obtain ⟨hzLb, hzL1, -⟩ := hpt τ (abs_of_pos hτpos)
  obtain ⟨hzRb, -, hzR2⟩ := hpt (-τ) (by rw [abs_neg, abs_of_pos hτpos])
  have hzLleft : zL ∈ leftHalf a b := by
    show 0 < (wc a b zL).im; rw [hzL, wc_param hab]; simpa using hτpos
  have hzRright : zR ∈ leftHalf b a := by
    rw [mem_leftHalf_swap hab, hzR, wc_param hab]; simpa using hτpos
  have hzLC : zL ∈ CL := hsub1 ⟨hzL1, hzLleft⟩
  have hzRC : zR ∈ CR := hsub2 ⟨hzR2, hzRright⟩
  have hBL_CL : BL ⊆ CL := by
    rw [hCL, connectedComponentIn_eq hzLC]
    exact hBLc.subset_connectedComponentIn ⟨hzLb, hzLleft⟩ hBLsub
  have hBR_CR : BR ⊆ CR := by
    rw [hCR, connectedComponentIn_eq hzRC]
    exact hBRc.subset_connectedComponentIn ⟨hzRb, hzRright⟩ hBRsub

  set κ := ρ / (4 * ‖b - a‖) with hκ
  have hκpos : 0 < κ := by positivity
  have hback : ∀ ε : ℝ, |ε| = κ → a + (b - a) * (((1 + κ : ℝ) : ℂ) + ε * I) ∈ BK := by
    intro ε hε
    refine ⟨hnear _ ?_, ?_⟩
    · have : ((1 + κ : ℝ) : ℂ) + ε * I - 1 = ((κ : ℝ) : ℂ) + ε * I := by push_cast; ring
      rw [this]
      calc ‖((κ : ℝ) : ℂ) + ε * I‖ * ‖b - a‖ ≤ (|κ| + |ε|) * ‖b - a‖ := by
            gcongr; exact hnorm2 _ _
        _ = 2 * (κ * ‖b - a‖) := by rw [abs_of_pos hκpos, hε]; ring
        _ = ρ / 2 := by rw [hκ]; field_simp; ring
        _ < ρ := by linarith
    · show 1 < (wc a b _).re
      rw [wc_param hab]; simp; linarith
  set kL := a + (b - a) * (((1 + κ : ℝ) : ℂ) + κ * I) with hkLdef
  set kR := a + (b - a) * (((1 + κ : ℝ) : ℂ) + ((-κ : ℝ) : ℂ) * I) with hkRdef
  have hkL : kL ∈ BK := hback κ (abs_of_pos hκpos)
  have hkR : kR ∈ BK := hback (-κ) (by rw [abs_neg, abs_of_pos hκpos])
  have hkLleft : kL ∈ BL := ⟨hkL.1, by
    show 0 < (wc a b kL).im; rw [hkLdef, wc_param hab]; simpa using hκpos⟩
  have hkRright : kR ∈ BR := ⟨hkR.1, by
    rw [mem_leftHalf_swap hab, hkRdef, wc_param hab]; simpa using hκpos⟩
  have hBK_CL : BK ⊆ CL := by
    rw [hCL, connectedComponentIn_eq (hBL_CL hkLleft)]
    exact hBKc.subset_connectedComponentIn hkL hBKsub
  have hCLR : CR = CL := by
    rw [hCR, connectedComponentIn_eq (hBR_CR hkRright), hCL,
      connectedComponentIn_eq (hBK_CL hkR)]

  have hloc : ∀ p ∈ A, ∃ r > 0, ball p r ⊆ CL ∪ CR ∪ A := by
    intro p hp
    rcases hp with hpb | hp
    · rw [hpb]
      refine ⟨ρ, hρpos, ?_⟩
      intro z hz
      rcases lt_trichotomy (wc a b z).im 0 with h | h | h
      · left; right; exact hBR_CR ⟨hz, (mem_leftHalf_swap hab z).mpr h⟩
      · rcases lt_or_ge 1 (wc a b z).re with h1 | h1
        · left; left; exact hBK_CL ⟨hz, h1⟩
        · right
          have hdz : ‖wc a b z - 1‖ * ‖b - a‖ < ‖b - a‖ / 2 := by
            have h' := norm_wc_sub hab z b
            rw [hwb] at h'
            rw [h']; exact lt_of_lt_of_le (mem_ball.mp hz) (min_le_right _ _)
          have hdz' : ‖wc a b z - 1‖ < 1 / 2 := by
            rw [← lt_div_iff₀ hba] at hdz
            calc ‖wc a b z - 1‖ < ‖b - a‖ / 2 / ‖b - a‖ := hdz
              _ = 1 / 2 := by field_simp
          have hre := (abs_re_le_norm (wc a b z - 1)).trans_lt hdz'
          rw [sub_re, one_re, abs_lt] at hre
          rcases h1.lt_or_eq with h1 | h1
          · right
            rw [mem_openSegment_iff_wc hab]
            exact ⟨h, by linarith, h1⟩
          · left
            have : wc a b z = 1 := Complex.ext (by simp [h1]) (by simp [h])
            rw [eq_param hab z, this]; ring
      · left; left; exact hBL_CL ⟨hz, h⟩
    · obtain ⟨r1, hr1, -, hline, hsub1⟩ := hL p hp
      obtain ⟨r2, hr2, -, -, hsub2⟩ := hR p (by rw [openSegment_symm]; exact hp)
      refine ⟨min r1 r2, lt_min hr1 hr2, ?_⟩
      intro z hz
      have hz1 : z ∈ ball p r1 := ball_subset_ball (min_le_left _ _) hz
      have hz2 : z ∈ ball p r2 := ball_subset_ball (min_le_right _ _) hz
      rcases lt_trichotomy (wc a b z).im 0 with h | h | h
      · left; right; exact hsub2 ⟨hz2, (mem_leftHalf_swap hab z).mpr h⟩
      · right; right; exact hline z hz1 h
      · left; left; exact hsub1 ⟨hz1, h⟩
  have hcov := cover_two isPreconnected_connectedComponentIn hUA hxL hloc
  rw [comps_eq_singleton hxL (fun z hz => by
    rcases hcov z hz with h | h
    · exact h
    · rw [← hCR, hCLR] at h; exact h)]
  exact encard_singleton _

end Cutting

section AddEdge

variable {a b : ℂ}

lemma exists_mem_openSegment (hab : a ≠ b) : ∃ p, p ∈ openSegment ℝ a b :=
  ⟨a + (b - a) * ((1/2 : ℝ) : ℂ), by rw [mem_openSegment_iff_wc hab, wc_param hab]; norm_num⟩

lemma encard_comps_add_cycle_edge {H : Set ℂ} (hH : IsClosed H) (hab : a ≠ b) (ha : a ∈ H)
    (hb : b ∈ H) (hseg : ∀ z ∈ openSegment ℝ a b, z ∉ H) {l : List ℂ}
    (hchain : List.IsChain (fun x y => segment ℝ x y ⊆ H) (b :: l))
    (hlast : (b :: l).getLast (by simp) = a) :
    (comps (H ∪ segment ℝ a b)ᶜ).encard = (comps Hᶜ).encard + 1 := by
  obtain ⟨p0, hp0⟩ := exists_mem_openSegment hab
  have hcompl : (H ∪ segment ℝ a b)ᶜ = Hᶜ \ openSegment ℝ a b := by
    ext z
    simp only [mem_compl_iff, mem_union, mem_diff, ← insert_endpoints_openSegment,
      mem_insert_iff, not_or]
    constructor
    · rintro ⟨h1, _, _, h4⟩; exact ⟨h1, h4⟩
    · rintro ⟨h1, h4⟩
      exact ⟨h1, fun h => h1 (h ▸ ha), fun h => h1 (h ▸ hb), h4⟩
  have h1 := encard_comps_diff (S := Hᶜ) (A := openSegment ℝ a b) (hseg p0 hp0)
    (openSegment_subset_comp hseg hp0)
  rw [encard_comps_cut_cycle hH hab ha hb hseg hchain hlast hp0] at h1
  rw [hcompl]
  apply ENat.add_left_injective_of_ne_top (n := 1) (by simp)
  convert h1 using 1 <;> norm_num [add_assoc]

lemma encard_comps_add_leaf_edge {H : Set ℂ} (hH : IsClosed H) (hab : a ≠ b) (ha : a ∈ H)
    (hb : b ∉ H) (hseg : ∀ z ∈ openSegment ℝ a b, z ∉ H) :
    (comps (H ∪ segment ℝ a b)ᶜ).encard = (comps Hᶜ).encard := by
  obtain ⟨p0, hp0⟩ := exists_mem_openSegment hab
  have hcompl : (H ∪ segment ℝ a b)ᶜ = Hᶜ \ insert b (openSegment ℝ a b) := by
    ext z
    simp only [mem_compl_iff, mem_union, mem_diff, ← insert_endpoints_openSegment,
      mem_insert_iff, not_or]
    constructor
    · rintro ⟨h1, _, h3, h4⟩; exact ⟨h1, h3, h4⟩
    · rintro ⟨h1, h3, h4⟩
      exact ⟨h1, fun h => h1 (h ▸ ha), h3, h4⟩
  have hA : insert b (openSegment ℝ a b) ⊆ connectedComponentIn Hᶜ p0 := by
    have hconv : IsPreconnected (insert b (openSegment ℝ a b)) := by
      have : insert b (openSegment ℝ a b) = (fun t : ℝ => a + (b - a) * t) '' Ioc 0 1 := by
        ext z
        simp only [mem_insert_iff, mem_image, mem_Ioc]
        constructor
        · rintro (rfl | hz)
          · exact ⟨1, ⟨one_pos, le_rfl⟩, by push_cast; ring⟩
          · rw [mem_openSegment_iff_wc hab] at hz
            refine ⟨(wc a b z).re, ⟨hz.2.1, hz.2.2.le⟩, ?_⟩
            conv_rhs => rw [eq_param hab z]
            congr 2
            exact Complex.ext (by simp) (by simp [hz.1])
        · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
          rcases h1.lt_or_eq with h1 | rfl
          · right
            rw [mem_openSegment_iff_wc hab, wc_param hab]
            exact ⟨ofReal_im t, by rw [ofReal_re]; exact h0, by rw [ofReal_re]; exact h1⟩
          · left; push_cast; ring
      rw [this]
      exact isPreconnected_Ioc.image _ (by fun_prop)
    refine hconv.subset_connectedComponentIn (Or.inr hp0) ?_
    rintro z (rfl | hz)
    · exact hb
    · exact hseg z hz
  have h1 := encard_comps_diff (S := Hᶜ) (A := insert b (openSegment ℝ a b)) (hseg p0 hp0) hA
  rw [encard_comps_cut_leaf hH hab ha hb hseg hp0] at h1
  rw [hcompl]
  exact ENat.add_left_injective_of_ne_top (n := 1) (by simp) h1

end AddEdge

section PlaneGraph

def edgeSeg (e : Sym2 ℂ) : Set ℂ :=
  Sym2.lift ⟨fun a b => segment ℝ a b, fun a b => segment_symm ℝ a b⟩ e

@[simp] lemma edgeSeg_mk (a b : ℂ) : edgeSeg s(a, b) = segment ℝ a b := rfl

structure IsPlaneGraph (V : Finset ℂ) (E : Finset (Sym2 ℂ)) : Prop where
  mem_V : ∀ e ∈ E, ∀ v ∈ e, v ∈ V
  not_diag : ∀ e ∈ E, ¬ e.IsDiag
  vertex_mem : ∀ e ∈ E, ∀ v ∈ V, v ∈ edgeSeg e → v ∈ e
  inter : ∀ e ∈ E, ∀ e' ∈ E, e ≠ e' → ∀ z ∈ edgeSeg e, z ∈ edgeSeg e' → z ∈ e

def drawing (V : Finset ℂ) (E : Finset (Sym2 ℂ)) : Set ℂ :=
  (V : Set ℂ) ∪ ⋃ e ∈ E, edgeSeg e

def faces (V : Finset ℂ) (E : Finset (Sym2 ℂ)) : Set (Set ℂ) :=
  comps (drawing V E)ᶜ

def GraphConnected (V : Finset ℂ) (E : Finset (Sym2 ℂ)) : Prop :=
  V.Nonempty ∧ ∀ u ∈ V, ∀ v ∈ V, Relation.ReflTransGen (fun x y => s(x, y) ∈ E) u v

lemma isClosed_edgeSeg (e : Sym2 ℂ) : IsClosed (edgeSeg e) := by
  induction e using Sym2.ind with
  | _ a b => exact isClosed_segment' a b

lemma isClosed_drawing (V : Finset ℂ) (E : Finset (Sym2 ℂ)) : IsClosed (drawing V E) :=
  V.finite_toSet.isClosed.union (E.finite_toSet.isClosed_biUnion fun e _ => isClosed_edgeSeg e)

lemma drawing_insert_edge (V : Finset ℂ) (E : Finset (Sym2 ℂ)) (e : Sym2 ℂ) :
    drawing V (insert e E) = drawing V E ∪ edgeSeg e := by
  simp only [drawing, Finset.set_biUnion_insert]
  ext z; simp only [mem_union]; tauto

lemma drawing_insert_vertex (V : Finset ℂ) (E : Finset (Sym2 ℂ)) (v w : ℂ) :
    drawing (insert v V) (insert s(w, v) E) = drawing V E ∪ segment ℝ w v := by
  rw [drawing_insert_edge, edgeSeg_mk]
  simp only [drawing, Finset.coe_insert]
  ext z
  simp only [mem_union, mem_insert_iff]
  constructor
  · rintro (((rfl | h) | h) | h)
    · right; exact right_mem_segment ℝ w z
    · left; left; exact h
    · left; right; exact h
    · right; exact h
  · rintro ((h | h) | h)
    · left; left; right; exact h
    · left; right; exact h
    · right; exact h

lemma openSegment_not_mem_drawing {V V' : Finset ℂ} {E E' : Finset (Sym2 ℂ)} {a b : ℂ}
    (hP : IsPlaneGraph V' E') (he : s(a, b) ∈ E') (hV : V ⊆ V') (hE : E ⊆ E'.erase s(a, b)) :
    ∀ z ∈ openSegment ℝ a b, z ∉ drawing V E := by
  have hab : a ≠ b := fun h => hP.not_diag _ he (by simp [h])
  intro z hz hzd
  have hend : z ∈ s(a, b) := by
    rcases hzd with hzV | hzE
    · exact hP.vertex_mem _ he z (hV hzV) (openSegment_subset_segment ℝ a b hz)
    · obtain ⟨e', he', hze'⟩ := mem_iUnion₂.mp hzE
      have he'E := hE he'
      rw [Finset.mem_erase] at he'E
      exact hP.inter _ he e' he'E.2 (Ne.symm he'E.1) z (openSegment_subset_segment ℝ a b hz) hze'
  rcases Sym2.mem_iff.mp hend with rfl | rfl
  · exact hab ((left_mem_openSegment_iff).mp hz)
  · exact hab ((right_mem_openSegment_iff).mp hz)

lemma IsPlaneGraph.mono {V V' : Finset ℂ} {E E' : Finset (Sym2 ℂ)} (hP : IsPlaneGraph V' E')
    (hV : V ⊆ V') (hE : E ⊆ E') (hEV : ∀ e ∈ E, ∀ v ∈ e, v ∈ V) : IsPlaneGraph V E where
  mem_V := hEV
  not_diag e he := hP.not_diag e (hE he)
  vertex_mem e he v hv := hP.vertex_mem e (hE he) v (hV hv)
  inter e he e' he' := hP.inter e (hE he) e' (hE he')

lemma encard_faces_insert_cycle {V : Finset ℂ} {E : Finset (Sym2 ℂ)} {a b : ℂ}
    (hP : IsPlaneGraph V (insert s(a, b) E)) (heE : s(a, b) ∉ E)
    (hreach : Relation.ReflTransGen (fun x y => s(x, y) ∈ E) b a) (ha : a ∈ V) :
    (faces V (insert s(a, b) E)).encard = (faces V E).encard + 1 := by
  have hab : a ≠ b := fun h => hP.not_diag _ (Finset.mem_insert_self _ _) (by simp [h])
  have hb : b ∈ V := hP.mem_V _ (Finset.mem_insert_self _ _) b (by simp)
  have hseg := openSegment_not_mem_drawing hP (Finset.mem_insert_self _ _) subset_rfl
    (by intro e he; rw [Finset.mem_erase]; exact ⟨fun h => heE (h ▸ he), Finset.mem_insert_of_mem he⟩)
  obtain ⟨l, hl, hlast⟩ := List.exists_isChain_cons_of_relationReflTransGen hreach
  have hchain : List.IsChain (fun x y => segment ℝ x y ⊆ drawing V E) (b :: l) := by
    refine hl.imp ?_
    intro x y hxy z hz
    right
    exact mem_iUnion₂.mpr ⟨_, hxy, hz⟩
  unfold faces
  rw [drawing_insert_edge, edgeSeg_mk]
  exact encard_comps_add_cycle_edge (isClosed_drawing V E) hab (Or.inl ha) (Or.inl hb) hseg
    hchain hlast

lemma encard_faces_insert_leaf {V : Finset ℂ} {E : Finset (Sym2 ℂ)} {v w : ℂ}
    (hP : IsPlaneGraph (insert v V) (insert s(w, v) E)) (hv : v ∉ V) (hw : w ∈ V)
    (hEV : ∀ e ∈ E, ∀ x ∈ e, x ∈ V) :
    (faces (insert v V) (insert s(w, v) E)).encard = (faces V E).encard := by
  have hwv : w ≠ v := fun h => hP.not_diag _ (Finset.mem_insert_self _ _) (by simp [h])
  have heE : s(w, v) ∉ E := fun h => hv (hEV _ h v (by simp))
  have hseg := openSegment_not_mem_drawing hP (Finset.mem_insert_self _ _)
    (Finset.subset_insert _ _)
    (by intro e he; rw [Finset.mem_erase]; exact ⟨fun h => heE (h ▸ he), Finset.mem_insert_of_mem he⟩)
  have hvd : v ∉ drawing V E := by
    rintro (h | h)
    · exact hv h
    · obtain ⟨e', he', hve'⟩ := mem_iUnion₂.mp h
      exact hv (hEV e' he' v (hP.vertex_mem e' (Finset.mem_insert_of_mem he') v
        (Finset.mem_insert_self _ _) hve'))
  unfold faces
  rw [drawing_insert_vertex]
  exact encard_comps_add_leaf_edge (isClosed_drawing V E) hwv (Or.inl hw) hvd hseg

end PlaneGraph

section Euler

lemma exists_noncut_vertex {V : Finset ℂ} {E : Finset (Sym2 ℂ)}
    (hEV : ∀ e ∈ E, ∀ x ∈ e, x ∈ V) (hnd : ∀ e ∈ E, ¬ e.IsDiag) (hC : GraphConnected V E)
    (h2 : 2 ≤ V.card) :
    ∃ v ∈ V, GraphConnected (V.erase v) (E.filter (fun e => v ∉ e)) := by
  let G : SimpleGraph V :=
    { Adj := fun x y => x ≠ y ∧ s(x.1, y.1) ∈ E
      symm := ⟨fun x y h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
      loopless := ⟨fun x h => h.1 rfl⟩ }
  have hreach : ∀ u w, Relation.ReflTransGen (fun x y => s(x, y) ∈ E) u w →
      ∀ (hu : u ∈ V) (hw : w ∈ V), G.Reachable ⟨u, hu⟩ ⟨w, hw⟩ := by
    intro u w h
    induction h with
    | refl => intro hu hw; rfl
    | @tail b c _ hbc ih =>
      intro hu hc
      have hb : b ∈ V := hEV _ hbc b (Sym2.mem_mk_left _ _)
      refine (ih hu hb).trans (SimpleGraph.Adj.reachable ⟨?_, hbc⟩)
      intro h
      have : b = c := congrArg Subtype.val h
      exact hnd _ hbc (Sym2.mk_isDiag_iff.mpr this)
  obtain ⟨x0, hx0⟩ := hC.1
  haveI : Nonempty V := ⟨⟨x0, hx0⟩⟩
  have hGc : G.Connected :=
    SimpleGraph.Connected.mk fun x y => hreach _ _ (hC.2 x.1 x.2 y.1 y.2) x.2 y.2
  haveI : Nontrivial V := by
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < V.card)
    exact ⟨⟨⟨x, hx⟩, ⟨y, hy⟩, fun h => hxy (congrArg Subtype.val h)⟩⟩
  obtain ⟨v, hv⟩ := hGc.exists_connected_induce_compl_singleton_of_finite_nontrivial
  refine ⟨v.1, v.2, ?_, ?_⟩
  · rw [← Finset.card_pos, Finset.card_erase_of_mem v.2]; omega
  · intro u hu w hw
    rw [Finset.mem_erase] at hu hw
    have hu' : (⟨u, hu.2⟩ : V) ∈ ({v}ᶜ : Set V) := by
      simp only [mem_compl_iff, mem_singleton_iff]
      intro h; exact hu.1 (congrArg Subtype.val h)
    have hw' : (⟨w, hw.2⟩ : V) ∈ ({v}ᶜ : Set V) := by
      simp only [mem_compl_iff, mem_singleton_iff]
      intro h; exact hw.1 (congrArg Subtype.val h)
    have hr := hv.preconnected ⟨_, hu'⟩ ⟨_, hw'⟩
    rw [SimpleGraph.reachable_iff_reflTransGen] at hr
    refine hr.lift (fun x => x.1.1) ?_
    intro x y hxy
    rw [SimpleGraph.induce_adj] at hxy
    change s(x.1.1, y.1.1) ∈ E.filter (fun e => v.1 ∉ e)
    rw [Finset.mem_filter]
    refine ⟨hxy.2, ?_⟩
    have hx : x.1 ≠ v := x.2
    have hy : y.1 ≠ v := y.2
    rw [Sym2.mem_iff, not_or]
    exact ⟨fun h => hx (Subtype.ext h.symm), fun h => hy (Subtype.ext h.symm)⟩

lemma encard_faces_singleton (v : ℂ) : (faces {v} ∅).encard = 1 := by
  have hd : drawing {v} ∅ = {v} := by simp [drawing]
  have hconn : IsConnected ({v}ᶜ : Set ℂ) :=
    isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num) v
  have hx : v + 1 ∈ ({v}ᶜ : Set ℂ) := by simp
  unfold faces
  rw [hd, comps_eq_singleton hx (fun y hy => by
    rw [hconn.isPreconnected.connectedComponentIn hx]; exact hy)]
  exact encard_singleton _

theorem euler_formula_encard : ∀ (n : ℕ) (V : Finset ℂ) (E : Finset (Sym2 ℂ)), V.card = n →
    IsPlaneGraph V E → GraphConnected V E → (faces V E).encard + V.card = E.card + 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V E hn hP hC
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain ⟨v, hV⟩ : ∃ v, V = {v} := Finset.card_eq_one.mp (by have := hC.1.card_pos; omega)
    have hE : E = ∅ := by
      ext e
      simp only [Finset.notMem_empty, iff_false]
      intro he
      induction e using Sym2.ind with
      | _ x y =>
        have hx := hP.mem_V _ he x (Sym2.mem_mk_left _ _)
        have hy := hP.mem_V _ he y (Sym2.mem_mk_right _ _)
        rw [hV, Finset.mem_singleton] at hx hy
        exact hP.not_diag _ he (Sym2.mk_isDiag_iff.mpr (hx.trans hy.symm))
    subst hV hE
    rw [encard_faces_singleton]
    simp only [Finset.card_singleton, Finset.card_empty, Nat.cast_one, Nat.cast_zero, zero_add]
    rfl
  · obtain ⟨v, hv, hC'⟩ := exists_noncut_vertex hP.mem_V hP.not_diag hC (hn ▸ h)
    set E0 := E.filter (fun e => v ∉ e) with hE0
    set S := E.filter (fun e => v ∈ e) with hS
    have hE0V : ∀ e ∈ E0, ∀ x ∈ e, x ∈ V.erase v := by
      intro e he x hx
      rw [hE0, Finset.mem_filter] at he
      rw [Finset.mem_erase]
      exact ⟨fun h => he.2 (h ▸ hx), hP.mem_V e he.1 x hx⟩
    have hP0 : IsPlaneGraph (V.erase v) E0 :=
      hP.mono (Finset.erase_subset _ _) (Finset.filter_subset _ _) hE0V
    have ih0 := ih (n - 1) (by omega) (V.erase v) E0
      (by rw [Finset.card_erase_of_mem hv, hn]) hP0 hC'

    have hSform : ∀ e ∈ S, ∃ w ∈ V.erase v, e = s(v, w) := by
      intro e he
      rw [hS, Finset.mem_filter] at he
      refine ⟨Sym2.Mem.other he.2, ?_, (Sym2.other_spec he.2).symm⟩
      rw [Finset.mem_erase]
      constructor
      · intro hw
        apply hP.not_diag e he.1
        rw [← Sym2.other_spec he.2, Sym2.mk_isDiag_iff]; exact hw.symm
      · exact hP.mem_V e he.1 _ (Sym2.other_mem he.2)
    have hstar : ∀ T : Finset (Sym2 ℂ), T ⊆ S → T.Nonempty →
        (faces V (E0 ∪ T)).encard + 1 = (faces (V.erase v) E0).encard + T.card := by
      intro T
      induction T using Finset.induction_on with
      | empty => intro _ h; exact absurd h Finset.not_nonempty_empty
      | @insert e T heT ihT =>
        intro hsub _
        have he : e ∈ S := hsub (Finset.mem_insert_self _ _)
        have hTS : T ⊆ S := (Finset.subset_insert _ _).trans hsub
        obtain ⟨w, hw, rfl⟩ := hSform _ he
        have hPsub : ∀ T' ⊆ S, IsPlaneGraph V (E0 ∪ T') := fun T' hT' =>
          hP.mono subset_rfl (Finset.union_subset (Finset.filter_subset _ _)
            (hT'.trans (Finset.filter_subset _ _)))
            (fun e he x hx => hP.mem_V e ((Finset.union_subset (Finset.filter_subset _ _)
              (hT'.trans (Finset.filter_subset _ _))) he) x hx)
        have hnotE0 : s(v, w) ∉ E0 := by
          rw [hE0, Finset.mem_filter]; intro h; exact h.2 (Sym2.mem_mk_left _ _)
        rcases T.eq_empty_or_nonempty with hT | hT
        · subst hT
          have hEq : E0 ∪ insert s(v, w) ∅ = insert s(w, v) E0 := by
            rw [Sym2.eq_swap]; ext x; simp
          have hVeq : V = insert v (V.erase v) := (Finset.insert_erase hv).symm
          have hP1 : IsPlaneGraph (insert v (V.erase v)) (insert s(w, v) E0) := by
            rw [← hEq, ← hVeq]; exact hPsub _ hsub
          rw [hEq, hVeq, encard_faces_insert_leaf hP1 (Finset.notMem_erase v V) hw hE0V]
          simp
        · have ihT' := ihT hTS hT
          have heq : E0 ∪ insert s(v, w) T = insert s(v, w) (E0 ∪ T) := by
            ext x; simp only [Finset.mem_union, Finset.mem_insert]; tauto
          have hnot : s(v, w) ∉ E0 ∪ T := by
            rw [Finset.mem_union, not_or]; exact ⟨hnotE0, heT⟩
          obtain ⟨t, htT⟩ := hT
          obtain ⟨w', hw', rfl⟩ := hSform _ (hTS htT)
          have hreach : Relation.ReflTransGen (fun x y => s(x, y) ∈ E0 ∪ T) w v := by
            have h1 : Relation.ReflTransGen (fun x y => s(x, y) ∈ E0 ∪ T) w w' :=
              Relation.ReflTransGen.mono (fun x y hxy => Finset.mem_union_left _ hxy) _ _ (hC'.2 w hw w' hw')
            exact h1.tail (by rw [Sym2.eq_swap]; exact Finset.mem_union_right _ htT)
          have hP2 : IsPlaneGraph V (insert s(v, w) (E0 ∪ T)) := by
            rw [← heq]; exact hPsub _ hsub
          rw [heq, encard_faces_insert_cycle hP2 hnot hreach hv,
            Finset.card_insert_of_notMem heT, add_right_comm, ihT']
          push_cast; ring
    have hSne : S.Nonempty := by
      obtain ⟨u, hu, huv⟩ : ∃ u ∈ V, u ≠ v := by
        obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < V.card)
        by_cases hxv : x = v
        · exact ⟨y, hy, fun h => hxy (hxv.trans h.symm)⟩
        · exact ⟨x, hx, hxv⟩
      rcases (hC.2 v hv u hu).cases_head with h | ⟨c, hc, _⟩
      · exact absurd h.symm huv
      · exact ⟨s(v, c), by rw [hS, Finset.mem_filter]; exact ⟨hc, Sym2.mem_mk_left _ _⟩⟩
    have hfin := hstar S subset_rfl hSne
    have hES : E0 ∪ S = E := by
      ext e; simp only [hE0, hS, Finset.mem_union, Finset.mem_filter]; tauto
    have hcard : E0.card + S.card = E.card := by
      rw [hE0, hS, add_comm]; exact Finset.card_filter_add_card_filter_not _
    rw [hES] at hfin
    rw [Finset.card_erase_of_mem hv] at ih0
    have hf' : (faces (V.erase v) E0).encard ≠ ⊤ := by
      intro htop; rw [htop, top_add] at ih0; exact (ENat.coe_ne_top _) (by exact_mod_cast ih0.symm)
    obtain ⟨f', hf'eq⟩ := ENat.ne_top_iff_exists.mp hf'
    have hf : (faces V E).encard ≠ ⊤ := by
      intro htop; rw [htop, top_add, ← hf'eq] at hfin
      exact (ENat.coe_ne_top (f' + S.card)) (by exact_mod_cast hfin.symm)
    obtain ⟨f, hfeq⟩ := ENat.ne_top_iff_exists.mp hf
    rw [← hfeq, ← hf'eq] at hfin
    rw [← hf'eq] at ih0
    rw [← hfeq, ← hcard]
    have e1 : f + 1 = f' + S.card := by exact_mod_cast hfin
    have e2 : f' + (V.card - 1) = E0.card + 2 := by exact_mod_cast ih0
    have : 1 ≤ S.card := hSne.card_pos
    have : 2 ≤ V.card := hn ▸ h
    norm_cast
    omega

theorem euler_formula {V : Finset ℂ} {E : Finset (Sym2 ℂ)} (hP : IsPlaneGraph V E)
    (hC : GraphConnected V E) :
    (faces V E).Finite ∧ V.card + (faces V E).ncard = E.card + 2 := by
  have h := euler_formula_encard _ V E rfl hP hC
  have hf : (faces V E).encard ≠ ⊤ := by
    intro htop; rw [htop, top_add] at h
    exact (ENat.coe_ne_top (E.card + 2)) (by exact_mod_cast h.symm)
  have hfin : (faces V E).Finite := Set.encard_ne_top_iff.mp hf
  refine ⟨hfin, ?_⟩
  rw [← hfin.cast_ncard_eq] at h
  have : (faces V E).ncard + V.card = E.card + 2 := by exact_mod_cast h
  omega

end Euler

section Oler

def triArea (a b c : ℂ) : ℝ := |((b - a) * (starRingEnd ℂ) (c - a)).im| / 2

def edgeLen (σ : Sym2 ℂ) : ℝ := Sym2.lift ⟨fun a b => dist a b, fun a b => dist_comm a b⟩ σ

def faceArea (t : Finset ℂ) : ℝ := (∑ a ∈ t, ∑ b ∈ t, ∑ c ∈ t, triArea a b c) / 6

def faceEdges (t : Finset ℂ) : Finset (Sym2 ℂ) := t.sym2.filter (fun σ => ¬ σ.IsDiag)

def edgeMult (T : Finset (Finset ℂ)) (σ : Sym2 ℂ) : ℕ := (T.filter (fun t => σ ∈ faceEdges t)).card

structure IsDelaunayComplex (V : Finset ℂ) (E : Finset (Sym2 ℂ)) (T : Finset (Finset ℂ)) :
    Prop where
  edge_mem : ∀ σ ∈ E, ¬ σ.IsDiag ∧ ∀ x ∈ σ, x ∈ V
  face_card : ∀ t ∈ T, t.card = 3
  face_edges : ∀ t ∈ T, faceEdges t ⊆ E
  mult_le_two : ∀ σ ∈ E, edgeMult T σ ≤ 2
  delaunay : ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → ∀ x y z w : ℂ, t = {x, y, z} → t' = {x, y, w} →
    EuclideanGeometry.angle x z y + EuclideanGeometry.angle x w y ≤ π

def eulerChar (V : Finset ℂ) (E : Finset (Sym2 ℂ)) (T : Finset (Finset ℂ)) : ℤ :=
  V.card - E.card + T.card

def cxArea (T : Finset (Finset ℂ)) : ℝ := ∑ t ∈ T, faceArea t

def cxPerim (E : Finset (Sym2 ℂ)) (T : Finset (Finset ℂ)) : ℝ :=
  ∑ σ ∈ E, (2 - (edgeMult T σ : ℝ)) * edgeLen σ

lemma fg_lemma_one {d s t A : ℝ} (hA : 0 ≤ A) (hs : 1 ≤ s) (ht : 1 ≤ t) (hds : s ≤ d)
    (hdt : t ≤ d) (hH : 16 * A ^ 2 = 4 * s ^ 2 * t ^ 2 - (s ^ 2 + t ^ 2 - d ^ 2) ^ 2) :
    s + t - d ≤ 4 / √3 * A := by
  have h3 : (0:ℝ) < √3 := by positivity
  have h33 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [div_mul_eq_mul_div, le_div_iff₀ h3]
  rcases le_or_gt (s + t - d) 0 with hu | hu
  · nlinarith
  have e : 4 * s ^ 2 * t ^ 2 - (s ^ 2 + t ^ 2 - d ^ 2) ^ 2 =
      ((d - s + t) * (d + s - t)) * ((s + t - d) * (s + t + d)) := by ring
  have h1 : 1 ≤ (d - s + t) * (d + s - t) := by nlinarith
  have h2 : 3 * (s + t - d) ^ 2 ≤ (s + t - d) * (s + t + d) := by nlinarith
  have h4 : 3 * (s + t - d) ^ 2 ≤ 16 * A ^ 2 := by
    rw [hH, e]; nlinarith
  nlinarith [sq_nonneg ((s + t - d) * √3 - 4 * A)]

lemma sqrt3_mul_le {x A : ℝ} (hx : 0 ≤ x) (hA : 0 ≤ A) (h : 3 * x ^ 2 ≤ 16 * A ^ 2) :
    √3 * x ≤ 4 * A := by
  have h33 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have : (√3 * x) ^ 2 ≤ (4 * A) ^ 2 := by rw [mul_pow, h33]; linarith
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 this

lemma fg_lemma_two {d s t s' t' A A' : ℝ} (hA : 0 ≤ A) (hA' : 0 ≤ A')
    (hs : 1 ≤ s) (ht : 1 ≤ t) (hs' : 1 ≤ s') (ht' : 1 ≤ t')
    (hds : s ≤ d) (hdt : t ≤ d) (hds' : s' ≤ d) (hdt' : t' ≤ d)
    (hH : 16 * A ^ 2 = 4 * s ^ 2 * t ^ 2 - (s ^ 2 + t ^ 2 - d ^ 2) ^ 2)
    (hH' : 16 * A' ^ 2 = 4 * s' ^ 2 * t' ^ 2 - (s' ^ 2 + t' ^ 2 - d ^ 2) ^ 2)
    (hdel : 0 ≤ (s ^ 2 + t ^ 2 - d ^ 2) / (s * t) + (s' ^ 2 + t' ^ 2 - d ^ 2) / (s' * t')) :
    s + t + s' + t' - 2 ≤ 4 / √3 * (A + A') := by
  have h3 : (0:ℝ) < √3 := by positivity
  set c := s ^ 2 + t ^ 2 - d ^ 2 with hc
  set c' := s' ^ 2 + t' ^ 2 - d ^ 2 with hc'
  have hst : 0 < s * t := by positivity
  have hst' : 0 < s' * t' := by positivity
  have u1 : c ≤ s * t := by
    rcases le_total s t with h | h <;> nlinarith
  have u1' : c' ≤ s' * t' := by
    rcases le_total s' t' with h | h <;> nlinarith
  have q1 : c / (s * t) ≤ 1 := (div_le_one hst).2 u1
  have q1' : c' / (s' * t') ≤ 1 := (div_le_one hst').2 u1'
  have l1 : -1 ≤ c / (s * t) := by linarith
  have l1' : -1 ≤ c' / (s' * t') := by linarith
  rw [le_div_iff₀ hst] at l1
  rw [le_div_iff₀ hst'] at l1'
  have a1 : √3 * (s * t) ≤ 4 * A := by
    refine sqrt3_mul_le hst.le hA ?_
    rw [hH]; nlinarith
  have a1' : √3 * (s' * t') ≤ 4 * A' := by
    refine sqrt3_mul_le hst'.le hA' ?_
    rw [hH']; nlinarith
  rw [div_mul_eq_mul_div, le_div_iff₀ h3]
  have k : 0 ≤ (s - 1) * (t - 1) + (s' - 1) * (t' - 1) := by
    have := mul_nonneg (sub_nonneg.2 hs) (sub_nonneg.2 ht)
    have := mul_nonneg (sub_nonneg.2 hs') (sub_nonneg.2 ht')
    linarith
  have e : (s + t + s' + t' - 2) * √3 + √3 * ((s - 1) * (t - 1) + (s' - 1) * (t' - 1)) =
    √3 * (s * t) + √3 * (s' * t') := by ring
  nlinarith

lemma triArea_nonneg (a b c : ℂ) : 0 ≤ triArea a b c := by
  unfold triArea; positivity

lemma triArea_heron (x y z : ℂ) :
    16 * triArea z x y ^ 2 = 4 * dist x z ^ 2 * dist y z ^ 2 -
      (dist x z ^ 2 + dist y z ^ 2 - dist x y ^ 2) ^ 2 := by
  unfold triArea
  rw [div_pow, sq_abs]
  simp only [Complex.dist_eq, Complex.sq_norm, Complex.normSq_apply, mul_im, conj_re, conj_im,
    sub_re, sub_im]
  ring

lemma triArea_perm (a b c : ℂ) :
    triArea a b c = triArea b c a ∧ triArea a b c = triArea a c b := by
  unfold triArea
  simp only [mul_im, conj_re, conj_im, sub_re, sub_im]
  constructor
  · congr 2; ring
  · rw [← abs_neg]; congr 2; ring

lemma triArea_self_left (a c : ℂ) : triArea a a c = 0 := by simp [triArea]

lemma triArea_self_right (a b : ℂ) : triArea a b a = 0 := by simp [triArea]

lemma triArea_self_mid (a b : ℂ) : triArea a b b = 0 := by
  unfold triArea
  simp only [mul_im, conj_re, conj_im, sub_re, sub_im]
  ring_nf; simp

lemma sum_three {M : Type*} [AddCommMonoid M] {a b c : ℂ} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (f : ℂ → M) : ∑ x ∈ ({a, b, c} : Finset ℂ), f x = f a + f b + f c := by
  rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
    Finset.sum_singleton, add_assoc]

lemma faceArea_eq {a b c : ℂ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    faceArea {a, b, c} = triArea c a b := by
  unfold faceArea
  simp only [sum_three hab hac hbc, triArea_self_left, triArea_self_right, triArea_self_mid]
  have e1 := (triArea_perm c a b)
  have e2 := (triArea_perm a b c)
  have e3 := (triArea_perm b c a)
  linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2]

lemma edgeLen_mk (a b : ℂ) : edgeLen s(a, b) = dist a b := rfl

lemma mem_faceEdges {t : Finset ℂ} {x y : ℂ} :
    s(x, y) ∈ faceEdges t ↔ x ∈ t ∧ y ∈ t ∧ x ≠ y := by
  simp [faceEdges, Finset.mem_sym2_iff, and_assoc]

lemma faceEdges_eq {a b c : ℂ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    faceEdges {a, b, c} = {s(a, b), s(a, c), s(b, c)} := by
  ext σ
  induction σ using Sym2.ind with
  | h x y =>
    rw [mem_faceEdges]
    simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]
    constructor
    · rintro ⟨hx, hy, hxy⟩
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> simp_all
    · rintro (h | h | h) <;> rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all [Ne.symm]

lemma sum_faceEdges {a b c : ℂ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∑ σ ∈ faceEdges {a, b, c}, edgeLen σ = dist a b + dist a c + dist b c := by
  rw [faceEdges_eq hab hac hbc, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
  · simp only [edgeLen_mk]; ring
  · simp [hab, hac]
  · simp [hab, hac, hbc]

lemma exists_third {t : Finset ℂ} (ht : t.card = 3) {x y : ℂ} (hx : x ∈ t) (hy : y ∈ t)
    (hxy : x ≠ y) : ∃ z, z ≠ x ∧ z ≠ y ∧ t = {x, y, z} := by
  have h1 : ((t.erase x).erase y).card = 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hxy.symm, hy⟩),
      Finset.card_erase_of_mem hx, ht]
  obtain ⟨z, hz⟩ := Finset.card_eq_one.1 h1
  have hzm : z ∈ (t.erase x).erase y := by rw [hz]; exact Finset.mem_singleton_self z
  simp only [Finset.mem_erase] at hzm
  refine ⟨z, hzm.2.1, hzm.1, ?_⟩
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl
    · exact hx
    · exact hy
    · exact hzm.2.2
  · rw [ht, Finset.card_insert_of_notMem (by simp [hxy, Ne.symm hzm.2.1]),
      Finset.card_insert_of_notMem (by simp [Ne.symm hzm.1]), Finset.card_singleton]

lemma cos_form_of_angle_add_le {x y z w : ℂ} (hxz : x ≠ z) (hyz : y ≠ z) (hxw : x ≠ w)
    (hyw : y ≠ w)
    (h : EuclideanGeometry.angle x z y + EuclideanGeometry.angle x w y ≤ π) :
    0 ≤ (dist x z ^ 2 + dist y z ^ 2 - dist x y ^ 2) / (dist x z * dist y z) +
      (dist x w ^ 2 + dist y w ^ 2 - dist x y ^ 2) / (dist x w * dist y w) := by
  have l1 := EuclideanGeometry.law_cos x z y
  have l2 := EuclideanGeometry.law_cos x w y
  have p1 : 0 < dist x z := dist_pos.2 hxz
  have p2 : 0 < dist y z := dist_pos.2 hyz
  have p3 : 0 < dist x w := dist_pos.2 hxw
  have p4 : 0 < dist y w := dist_pos.2 hyw
  have hc : Real.cos (π - EuclideanGeometry.angle x w y) ≤
      Real.cos (EuclideanGeometry.angle x z y) :=
    Real.cos_le_cos_of_nonneg_of_le_pi (EuclideanGeometry.angle_nonneg _ _ _)
      (by linarith [EuclideanGeometry.angle_nonneg x w y]) (by linarith)
  rw [Real.cos_pi_sub] at hc
  have e1 : (dist x z ^ 2 + dist y z ^ 2 - dist x y ^ 2) / (dist x z * dist y z) =
      2 * Real.cos (EuclideanGeometry.angle x z y) := by
    rw [div_eq_iff (by positivity)]; simp only [sq]; linarith
  have e2 : (dist x w ^ 2 + dist y w ^ 2 - dist x y ^ 2) / (dist x w * dist y w) =
      2 * Real.cos (EuclideanGeometry.angle x w y) := by
    rw [div_eq_iff (by positivity)]; simp only [sq]; linarith
  rw [e1, e2]; linarith

def faceDefect (t : Finset ℂ) : ℝ :=
  2 / √3 * faceArea t - (∑ σ ∈ faceEdges t, edgeLen σ) / 2 + 1

lemma sum_mult_len {E : Finset (Sym2 ℂ)} {T : Finset (Finset ℂ)}
    (hT : ∀ t ∈ T, faceEdges t ⊆ E) :
    ∑ σ ∈ E, (edgeMult T σ : ℝ) * edgeLen σ = ∑ t ∈ T, ∑ σ ∈ faceEdges t, edgeLen σ := by
  simp only [edgeMult, Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t ht => ?_
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  congr 1
  ext σ
  simp only [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨hT t ht h, h⟩⟩

lemma rhs_sub_eq {V : Finset ℂ} {E : Finset (Sym2 ℂ)} {T : Finset (Finset ℂ)}
    (hT : ∀ t ∈ T, faceEdges t ⊆ E) :
    2 / √3 * cxArea T + cxPerim E T / 2 + eulerChar V E T - V.card =
      ∑ σ ∈ E, (edgeLen σ - 1) + ∑ t ∈ T, faceDefect t := by
  have h := sum_mult_len hT
  unfold cxArea cxPerim eulerChar faceDefect
  simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum] at h ⊢
  rw [h]
  push_cast
  have k1 : ∑ x ∈ E, 2 * edgeLen x = 2 * ∑ x ∈ E, edgeLen x := Finset.mul_sum _ _ _ |>.symm
  have k2 : ∑ x ∈ T, (∑ σ ∈ faceEdges x, edgeLen σ) / 2 =
      (∑ t ∈ T, ∑ σ ∈ faceEdges t, edgeLen σ) / 2 := by rw [Finset.sum_div]
  rw [k1, k2]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  ring

lemma face_data {V : Finset ℂ} {E : Finset (Sym2 ℂ)} {T : Finset (Finset ℂ)}
    (hV : ∀ x ∈ V, ∀ y ∈ V, x ≠ y → 1 ≤ dist x y) (hK : IsDelaunayComplex V E T)
    {x y : ℂ} {t : Finset ℂ} (ht : t ∈ T) (hσ : s(x, y) ∈ faceEdges t)
    (hlong : ∀ τ ∈ faceEdges t, edgeLen τ ≤ edgeLen s(x, y)) :
    ∃ z, z ≠ x ∧ z ≠ y ∧ x ≠ y ∧ t = {x, y, z} ∧ 1 ≤ dist x z ∧ 1 ≤ dist y z ∧
      dist x z ≤ dist x y ∧ dist y z ≤ dist x y ∧
      faceDefect t = 2 / √3 * triArea z x y - (dist x y + dist x z + dist y z) / 2 + 1 := by
  obtain ⟨hx, hy, hxy⟩ := mem_faceEdges.1 hσ
  obtain ⟨z, hzx, hzy, rfl⟩ := exists_third (hK.face_card t ht) hx hy hxy
  have hz : z ∈ ({x, y, z} : Finset ℂ) := by simp
  have exz : s(x, z) ∈ faceEdges {x, y, z} := mem_faceEdges.2 ⟨hx, hz, hzx.symm⟩
  have eyz : s(y, z) ∈ faceEdges {x, y, z} := mem_faceEdges.2 ⟨hy, hz, hzy.symm⟩
  have mem : ∀ a b, s(a, b) ∈ faceEdges {x, y, z} → a ∈ V ∧ b ∈ V := fun a b h =>
    ⟨(hK.edge_mem _ (hK.face_edges _ ht h)).2 a (Sym2.mem_mk_left a b),
     (hK.edge_mem _ (hK.face_edges _ ht h)).2 b (Sym2.mem_mk_right a b)⟩
  refine ⟨z, hzx, hzy, hxy, rfl, hV x (mem x z exz).1 z (mem x z exz).2 hzx.symm,
    hV y (mem y z eyz).1 z (mem y z eyz).2 hzy.symm, hlong _ exz, hlong _ eyz, ?_⟩
  unfold faceDefect
  rw [faceArea_eq hxy hzx.symm hzy.symm, sum_faceEdges hxy hzx.symm hzy.symm]

lemma local_charge {V : Finset ℂ} {E : Finset (Sym2 ℂ)} {T : Finset (Finset ℂ)}
    (hV : ∀ x ∈ V, ∀ y ∈ V, x ≠ y → 1 ≤ dist x y) (hK : IsDelaunayComplex V E T)
    {σ : Sym2 ℂ} (hσ : σ ∈ E) (F : Finset (Finset ℂ)) (hF : F ⊆ T.filter (σ ∈ faceEdges ·))
    (hlong : ∀ t ∈ F, ∀ τ ∈ faceEdges t, edgeLen τ ≤ edgeLen σ) :
    0 ≤ (edgeLen σ - 1) + ∑ t ∈ F, faceDefect t := by
  obtain ⟨⟨x, y⟩, rfl⟩ := Quot.exists_rep σ
  change s(x, y) ∈ E at hσ
  change 0 ≤ (edgeLen s(x, y) - 1) + ∑ t ∈ F, faceDefect t
  change ∀ t ∈ F, ∀ τ ∈ faceEdges t, edgeLen τ ≤ edgeLen s(x, y) at hlong
  change F ⊆ T.filter (s(x, y) ∈ faceEdges ·) at hF
  rw [edgeLen_mk]
  have hxyV := (hK.edge_mem _ hσ)
  have hxy : x ≠ y := fun h => hxyV.1 (by rw [h]; exact Sym2.mk_isDiag_iff.2 rfl)
  have hd : 1 ≤ dist x y :=
    hV x (hxyV.2 x (Sym2.mem_mk_left x y)) y (hxyV.2 y (Sym2.mem_mk_right x y)) hxy
  have hcard : F.card ≤ 2 := (Finset.card_le_card hF).trans (hK.mult_le_two _ hσ)
  have memF : ∀ t ∈ F, t ∈ T ∧ s(x, y) ∈ faceEdges t := fun t ht => Finset.mem_filter.1 (hF ht)
  have h3 : (0:ℝ) < √3 := by positivity
  interval_cases hc : F.card
  · rw [Finset.card_eq_zero.1 hc]; simp; linarith
  · obtain ⟨t, rfl⟩ := Finset.card_eq_one.1 hc
    obtain ⟨ht, hσt⟩ := memF t (Finset.mem_singleton_self t)
    obtain ⟨z, -, -, -, -, h1, h2, h3', h4, hdef⟩ :=
      face_data hV hK ht hσt (hlong t (Finset.mem_singleton_self t))
    rw [Finset.sum_singleton, hdef]
    have := fg_lemma_one (triArea_nonneg z x y) h1 h2 h3' h4 (triArea_heron x y z)
    have e : 4 / √3 * triArea z x y = 2 * (2 / √3 * triArea z x y) := by ring
    linarith
  · obtain ⟨t, t', hne, rfl⟩ := Finset.card_eq_two.1 hc
    obtain ⟨ht, hσt⟩ := memF t (by simp)
    obtain ⟨ht', hσt'⟩ := memF t' (by simp)
    obtain ⟨z, hzx, hzy, -, rfl, h1, h2, h3', h4, hdef⟩ := face_data hV hK ht hσt (hlong _ (by simp))
    obtain ⟨w, hwx, hwy, -, rfl, k1, k2, k3, k4, kdef⟩ :=
      face_data hV hK ht' hσt' (hlong _ (by simp))
    rw [Finset.sum_pair hne, hdef, kdef]
    have hdel := cos_form_of_angle_add_le hzx.symm hzy.symm hwx.symm hwy.symm
      (hK.delaunay _ ht _ ht' hne x y z w rfl rfl)
    have := fg_lemma_two (triArea_nonneg z x y) (triArea_nonneg w x y) h1 h2 k1 k2 h3' h4 k3 k4
      (triArea_heron x y z) (triArea_heron x y w) hdel
    have e : 4 / √3 * (triArea z x y + triArea w x y) =
      2 * (2 / √3 * triArea z x y) + 2 * (2 / √3 * triArea w x y) := by ring
    linarith

theorem folkman_graham {V : Finset ℂ} {E : Finset (Sym2 ℂ)} {T : Finset (Finset ℂ)}
    (hV : ∀ x ∈ V, ∀ y ∈ V, x ≠ y → 1 ≤ dist x y) (hK : IsDelaunayComplex V E T) :
    (V.card : ℝ) ≤ 2 / √3 * cxArea T + cxPerim E T / 2 + eulerChar V E T := by
  rw [← sub_nonneg, rhs_sub_eq hK.face_edges]
  have hL : ∀ t ∈ T, ∃ σ ∈ faceEdges t, ∀ τ ∈ faceEdges t, edgeLen τ ≤ edgeLen σ := by
    intro t ht
    apply Finset.exists_max_image
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by rw [hK.face_card t ht]; norm_num)
    exact ⟨s(a, b), mem_faceEdges.2 ⟨ha, hb, hab⟩⟩
  choose! L hLmem hLmax using hL
  rw [← Finset.sum_fiberwise_of_maps_to (g := L) (t := E)
    (fun t ht => hK.face_edges t ht (hLmem t ht)), ← Finset.sum_add_distrib]
  refine Finset.sum_nonneg fun σ hσ => local_charge hV hK hσ _ ?_ ?_
  · intro t ht
    obtain ⟨hT, rfl⟩ := Finset.mem_filter.1 ht
    exact Finset.mem_filter.2 ⟨hT, hLmem t hT⟩
  · intro t ht
    obtain ⟨hT, rfl⟩ := Finset.mem_filter.1 ht
    exact hLmax t hT

end Oler

end EstablishedExternalResults
end

end EstablishedExternalResults

section PlaneFaces

open scoped BigOperators Real
open Set Metric Complex

@[expose] public noncomputable section

open Classical

namespace EstablishedExternalResults

section Puncture

lemma isPreconnected_ball_diff_singleton (v : ℂ) (r : ℝ) :
    IsPreconnected (ball v r \ {v}) := by
  have : ball v r \ {v} =
      (fun q : ℝ × ℝ => v + (q.1 : ℂ) * cexp (q.2 * I)) '' (Ioo 0 r ×ˢ univ) := by
    ext z
    simp only [mem_diff, mem_ball, mem_singleton_iff, mem_image, mem_prod, mem_Ioo, mem_univ,
      and_true, Prod.exists]
    constructor
    · rintro ⟨hz, hne⟩
      refine ⟨‖z - v‖, arg (z - v), ⟨norm_pos_iff.2 (sub_ne_zero.2 hne), ?_⟩, ?_⟩
      · rwa [← dist_eq_norm]
      · rw [Complex.norm_mul_exp_arg_mul_I]; ring
    · rintro ⟨s, θ, ⟨hs0, hsr⟩, rfl⟩
      have hn : ‖(s : ℂ) * cexp (θ * I)‖ = s := by
        rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
          Real.norm_of_nonneg hs0.le]
      refine ⟨?_, ?_⟩
      · rw [dist_eq_norm, add_sub_cancel_left, hn]; exact hsr
      · intro h
        have : (s : ℂ) * cexp (θ * I) = 0 := by linear_combination h
        rw [← hn, this, norm_zero] at hs0
        exact lt_irrefl _ hs0
  rw [this]
  exact (isPreconnected_Ioo.prod isPreconnected_univ).image _ (by fun_prop)

lemma diff_singleton_aux {U P Q : Set ℂ} {v : ℂ} {r : ℝ} (hP : IsOpen P) (hQ : IsOpen Q)
    (hvU : v ∈ U) (hc : IsPreconnected U) (hr : 0 < r)
    (hUPQ : U \ {v} ⊆ P ∪ Q) (hdis : (U \ {v}) ∩ (P ∩ Q) = ∅) (hBP : ball v r \ {v} ⊆ P) :
    U \ {v} ⊆ P := by
  have hP' : IsOpen (P ∪ ball v r) := hP.union isOpen_ball
  have hQ' : IsOpen (Q \ {v}) := hQ.sdiff isClosed_singleton
  have hcov : U ⊆ (P ∪ ball v r) ∪ (Q \ {v}) := by
    intro x hx
    by_cases hxv : x = v
    · left; right; rw [hxv]; exact mem_ball_self hr
    · rcases hUPQ ⟨hx, hxv⟩ with h | h
      · left; left; exact h
      · right; exact ⟨h, hxv⟩
  have hdis' : U ∩ ((P ∪ ball v r) ∩ (Q \ {v})) = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_union, mem_diff, mem_empty_iff_false, iff_false, not_and]
    intro hx hPB hxQ hxv
    have hxP : x ∈ P := by
      rcases hPB with h | h
      · exact h
      · exact hBP ⟨h, hxv⟩
    have : x ∈ (U \ {v}) ∩ (P ∩ Q) := ⟨⟨hx, hxv⟩, hxP, hxQ⟩
    rw [hdis] at this; exact this
  rcases (isPreconnected_iff_subset_of_disjoint.1 hc) _ _ hP' hQ' hcov hdis' with h | h
  · intro x hx
    rcases h hx.1 with h1 | h1
    · exact h1
    · exact hBP ⟨h1, hx.2⟩
  · exact absurd rfl (h hvU).2

lemma isPreconnected_diff_singleton {U : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U) (v : ℂ) :
    IsPreconnected (U \ {v}) := by
  by_cases hvU : v ∈ U
  · obtain ⟨r, hr, hB⟩ := Metric.isOpen_iff.1 hU v hvU
    rw [isPreconnected_iff_subset_of_disjoint]
    intro P Q hP hQ hUPQ hdis
    have hBsub : ball v r \ {v} ⊆ P ∪ Q := fun x hx => hUPQ ⟨hB hx.1, hx.2⟩
    have hBdis : (ball v r \ {v}) ∩ (P ∩ Q) = ∅ := by
      ext x; simp only [mem_empty_iff_false, iff_false]
      intro hx
      have : x ∈ (U \ {v}) ∩ (P ∩ Q) := ⟨⟨hB hx.1.1, hx.1.2⟩, hx.2⟩
      rw [hdis] at this; exact this
    rcases (isPreconnected_iff_subset_of_disjoint.1 (isPreconnected_ball_diff_singleton v r))
      P Q hP hQ hBsub hBdis with h | h
    · exact Or.inl (diff_singleton_aux hP hQ hvU hc hr hUPQ hdis h)
    · refine Or.inr (diff_singleton_aux hQ hP hvU hc hr (by rwa [union_comm]) ?_ h)
      rwa [inter_comm Q P]
  · rwa [diff_singleton_eq_self hvU]

lemma isPreconnected_diff_finset {U : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U)
    (S : Finset ℂ) : IsPreconnected (U \ (S : Set ℂ)) := by
  induction S using Finset.induction_on with
  | empty => simpa using hc
  | insert a S _ ih =>
    rw [Finset.coe_insert, insert_eq, union_comm, ← diff_diff]
    exact isPreconnected_diff_singleton (hU.sdiff S.finite_toSet.isClosed) ih a

end Puncture

section Forest

def IsForestE (E : Finset (Sym2 ℂ)) : Prop :=
  ∀ a b, s(a, b) ∈ E → ¬ Relation.ReflTransGen (fun x y => s(x, y) ∈ E.erase s(a, b)) a b

lemma IsForestE.mono {E E' : Finset (Sym2 ℂ)} (h : IsForestE E) (h' : E' ⊆ E) :
    IsForestE E' := by
  intro a b hab hr
  exact h a b (h' hab) (Relation.ReflTransGen.mono (fun x y hxy => Finset.erase_subset_erase _ h' hxy) _ _ hr)

lemma reach_symm {E : Finset (Sym2 ℂ)} {u w : ℂ}
    (h : Relation.ReflTransGen (fun x y => s(x, y) ∈ E) u w) :
    Relation.ReflTransGen (fun x y => s(x, y) ∈ E) w u :=
  Erdos99Migration.reflTransGenSymmetric (fun x y hxy => by rwa [Sym2.eq_swap]) h

lemma reach_of_mem {E : Finset (Sym2 ℂ)} {z u : ℂ} {f : Sym2 ℂ} (hf : f ∈ E) (hu : u ∈ f)
    (hz : Relation.ReflTransGen (fun x y => s(x, y) ∈ E) z u) :
    ∀ t ∈ f, Relation.ReflTransGen (fun x y => s(x, y) ∈ E) z t := by
  intro t ht
  have hfe : f = s(u, Sym2.Mem.other hu) := (Sym2.other_spec hu).symm
  rw [hfe] at ht hf
  rcases Sym2.mem_iff.1 ht with rfl | rfl
  · exact hz
  · exact hz.tail hf

lemma exists_leaf : ∀ (k : ℕ) {E : Finset (Sym2 ℂ)}, E.card = k → (∀ e ∈ E, ¬ e.IsDiag) →
    IsForestE E → E.Nonempty → ∀ a : ℂ,
    ∃ v w, v ≠ a ∧ s(w, v) ∈ E ∧ ∀ e ∈ E, v ∈ e → e = s(w, v) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro E hk hnd hF hne a
  obtain ⟨e, he⟩ := hne
  induction e using Sym2.ind with
  | _ x y =>
  set R := E.erase s(x, y) with hR
  have hxy := hF x y he

  obtain ⟨z, z', hez, hza⟩ : ∃ z z', s(x, y) = s(z', z) ∧
      ¬ Relation.ReflTransGen (fun u w => s(u, w) ∈ R) a z := by
    by_cases h1 : Relation.ReflTransGen (fun u w => s(u, w) ∈ R) a y
    · refine ⟨x, y, Sym2.eq_swap, fun h2 => hxy ?_⟩
      exact (reach_symm h2).trans h1
    · exact ⟨y, x, rfl, h1⟩
  have hzz' : ¬ Relation.ReflTransGen (fun u w => s(u, w) ∈ R) z z' := by
    intro h
    rcases Sym2.eq_iff.1 hez with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hxy (reach_symm h)
    · exact hxy h
  set B := R.filter (fun f => ∀ u ∈ f, Relation.ReflTransGen (fun x y => s(x, y) ∈ R) z u)
    with hB
  have hRE : R ⊆ E := Finset.erase_subset _ _
  have hBR : B ⊆ R := Finset.filter_subset _ _
  have hinB : ∀ f ∈ R, ∀ u ∈ f, Relation.ReflTransGen (fun x y => s(x, y) ∈ R) z u → f ∈ B :=
    fun f hf u hu hz => Finset.mem_filter.2 ⟨hf, reach_of_mem hf hu hz⟩
  have heE : s(z', z) ∈ E := hez ▸ he
  rcases B.eq_empty_or_nonempty with hBe | hBne
  · refine ⟨z, z', fun h => hza (h ▸ Relation.ReflTransGen.refl), heE, ?_⟩
    intro f hf hzf
    by_contra hne
    have hfR : f ∈ R := Finset.mem_erase.2 ⟨fun h => hne (h.trans hez), hf⟩
    have := hinB f hfR z hzf Relation.ReflTransGen.refl
    rw [hBe] at this; exact absurd this (Finset.notMem_empty _)
  · have hcard : B.card < k := by
      rw [← hk]
      exact lt_of_le_of_lt (Finset.card_le_card hBR) (Finset.card_erase_lt_of_mem he)
    obtain ⟨v, w, hvz, hwv, hleaf⟩ := ih _ hcard rfl (fun f hf => hnd f (hRE (hBR hf)))
      (hF.mono (hBR.trans hRE)) hBne z
    have hvreach : Relation.ReflTransGen (fun x y => s(x, y) ∈ R) z v :=
      (Finset.mem_filter.1 hwv).2 v (Sym2.mem_mk_right _ _)
    refine ⟨v, w, fun h => hza (h ▸ reach_symm hvreach), hRE (hBR hwv), ?_⟩
    intro f hf hvf
    by_cases hfe : f = s(x, y)
    · exfalso
      rw [hfe, hez] at hvf
      rcases Sym2.mem_iff.1 hvf with rfl | rfl
      · exact hzz' hvreach
      · exact hvz rfl
    · exact hleaf f (hinB f (Finset.mem_erase.2 ⟨hfe, hf⟩) v hvf hvreach) hvf

lemma isPreconnected_of_encard_comps_eq_one {X : Type*} [TopologicalSpace X] {S : Set X}
    (h : (comps S).encard = 1) : IsPreconnected S := by
  obtain ⟨C, hC⟩ := Set.encard_eq_one.1 h
  have hS : ∀ x ∈ S, connectedComponentIn S x = C := fun x hx => by
    have : connectedComponentIn S x ∈ comps S := ⟨x, hx, rfl⟩
    rw [hC] at this; exact this
  by_cases hne : S.Nonempty
  · obtain ⟨x, hx⟩ := hne
    have : S = connectedComponentIn S x := by
      apply le_antisymm
      · intro y hy
        rw [hS x hx, ← hS y hy]; exact mem_connectedComponentIn hy
      · exact connectedComponentIn_subset _ _
    rw [this]; exact isPreconnected_connectedComponentIn
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne]; exact isPreconnected_empty

lemma encard_faces_empty {V : Finset ℂ} : (faces V ∅).encard = 1 := by
  have hd : drawing V ∅ = (V : Set ℂ) := by simp [drawing]
  have hconn : IsConnected ((V : Set ℂ)ᶜ) :=
    Set.Countable.isConnected_compl_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; norm_num) V.finite_toSet.countable
  obtain ⟨x, hx⟩ := hconn.nonempty
  unfold faces
  rw [hd, comps_eq_singleton hx (fun y hy => by
    rw [hconn.isPreconnected.connectedComponentIn hx]; exact hy)]
  exact encard_singleton _

lemma leaf_data {V : Finset ℂ} {E : Finset (Sym2 ℂ)} (hEV : ∀ e ∈ E, ∀ v ∈ e, v ∈ V)
    (hnd : ∀ e ∈ E, ¬ e.IsDiag) {v w : ℂ} (hwv : s(w, v) ∈ E)
    (hleaf : ∀ e ∈ E, v ∈ e → e = s(w, v)) :
    v ∈ V ∧ w ∈ V.erase v ∧ (∀ e ∈ E.erase s(w, v), ∀ x ∈ e, x ∈ V.erase v) ∧
      V = insert v (V.erase v) ∧ E = insert s(w, v) (E.erase s(w, v)) := by
  have hvw : w ≠ v := fun h => hnd _ hwv (by rw [h]; exact Sym2.mk_isDiag_iff.2 rfl)
  have hv : v ∈ V := hEV _ hwv v (Sym2.mem_mk_right _ _)
  refine ⟨hv, Finset.mem_erase.2 ⟨hvw, hEV _ hwv w (Sym2.mem_mk_left _ _)⟩, ?_,
    (Finset.insert_erase hv).symm, (Finset.insert_erase hwv).symm⟩
  intro e he x hx
  obtain ⟨hne, heE⟩ := Finset.mem_erase.1 he
  refine Finset.mem_erase.2 ⟨?_, hEV e heE x hx⟩
  rintro rfl
  exact hne (hleaf e heE hx)

lemma encard_faces_forest : ∀ (k : ℕ) {V : Finset ℂ} {E : Finset (Sym2 ℂ)}, E.card = k →
    IsPlaneGraph V E → IsForestE E → (faces V E).encard = 1 := by
  intro k
  induction k with
  | zero =>
    intro V E hk _ _
    rw [Finset.card_eq_zero.1 hk]; exact encard_faces_empty
  | succ k ih =>
    intro V E hk hP hF
    obtain ⟨v, w, -, hwv, hleaf⟩ := exists_leaf _ rfl hP.not_diag hF
      (Finset.card_pos.1 (by omega)) 0
    obtain ⟨hv, hw, hE0V, hVeq, hEeq⟩ := leaf_data hP.mem_V hP.not_diag hwv hleaf
    have hP0 : IsPlaneGraph (V.erase v) (E.erase s(w, v)) :=
      hP.mono (Finset.erase_subset _ _) (Finset.erase_subset _ _) hE0V
    have hP' : IsPlaneGraph (insert v (V.erase v)) (insert s(w, v) (E.erase s(w, v))) := by
      rw [← hVeq, ← hEeq]; exact hP
    rw [hVeq, hEeq, encard_faces_insert_leaf hP' (Finset.notMem_erase v V) hw hE0V]
    exact ih (by rw [Finset.card_erase_of_mem hwv, hk]; rfl) hP0
      (hF.mono (Finset.erase_subset _ _))

lemma card_forest : ∀ (k : ℕ) {V : Finset ℂ} {E : Finset (Sym2 ℂ)}, E.card = k →
    (∀ e ∈ E, ∀ v ∈ e, v ∈ V) → (∀ e ∈ E, ¬ e.IsDiag) → IsForestE E → V.Nonempty →
    E.card + 1 ≤ V.card := by
  intro k
  induction k with
  | zero =>
    intro V E hk _ _ _ hV
    rw [hk]; exact hV.card_pos
  | succ k ih =>
    intro V E hk hEV hnd hF _
    obtain ⟨v, w, -, hwv, hleaf⟩ := exists_leaf _ rfl hnd hF (Finset.card_pos.1 (by omega)) 0
    obtain ⟨hv, hw, hE0V, -, -⟩ := leaf_data hEV hnd hwv hleaf
    have := ih (by rw [Finset.card_erase_of_mem hwv, hk]; rfl) hE0V
      (fun e he => hnd e (Finset.mem_erase.1 he).2) (hF.mono (Finset.erase_subset _ _)) ⟨w, hw⟩
    rw [Finset.card_erase_of_mem hwv, Finset.card_erase_of_mem hv] at this
    have := Finset.card_pos.2 ⟨v, hv⟩
    have := Finset.card_pos.2 ⟨_, hwv⟩
    omega

theorem euler_ineq : ∀ (k : ℕ) {V : Finset ℂ} {E : Finset (Sym2 ℂ)}, E.card = k →
    IsPlaneGraph V E → V.Nonempty → ((E.card : ℕ∞) + 2 ≤ (faces V E).encard + V.card) := by
  intro k
  induction k with
  | zero =>
    intro V E hk hP hV
    rw [Finset.card_eq_zero.1 hk, encard_faces_empty]
    have : 1 ≤ V.card := hV.card_pos
    simp only [Finset.card_empty, Nat.cast_zero, zero_add]
    have : (1 : ℕ∞) ≤ V.card := by exact_mod_cast this
    calc (2 : ℕ∞) = 1 + 1 := by norm_num
      _ ≤ 1 + V.card := add_le_add le_rfl this
  | succ k ih =>
    intro V E hk hP hV
    by_cases hcyc : ∃ a b, s(a, b) ∈ E ∧
        Relation.ReflTransGen (fun x y => s(x, y) ∈ E.erase s(a, b)) a b
    · obtain ⟨a, b, hab, hr⟩ := hcyc
      have hEeq : E = insert s(a, b) (E.erase s(a, b)) := (Finset.insert_erase hab).symm
      have hP' : IsPlaneGraph V (insert s(a, b) (E.erase s(a, b))) := by rw [← hEeq]; exact hP
      have hcard : E.card = (E.erase s(a, b)).card + 1 := (Finset.card_erase_add_one hab).symm
      have ih0 := ih (by rw [Finset.card_erase_of_mem hab, hk]; rfl)
        (hP.mono subset_rfl (Finset.erase_subset _ _)
          (fun e he => hP.mem_V e (Finset.mem_erase.1 he).2)) hV
      rw [hEeq, encard_faces_insert_cycle hP' (Finset.notMem_erase _ _) (reach_symm hr)
        (hP.mem_V _ hab a (Sym2.mem_mk_left _ _)), ← hEeq, hcard]
      push_cast
      calc ((E.erase s(a, b)).card : ℕ∞) + 1 + 2 = ((E.erase s(a, b)).card + 2) + 1 := by
            rw [add_right_comm]
        _ ≤ ((faces V (E.erase s(a, b))).encard + V.card) + 1 := add_le_add ih0 le_rfl
        _ = (faces V (E.erase s(a, b))).encard + 1 + V.card := by rw [add_right_comm]
    · push_neg at hcyc
      have hF : IsForestE E := fun a b hab => hcyc a b hab
      rw [encard_faces_forest _ rfl hP hF]
      have h := card_forest _ rfl hP.mem_V hP.not_diag hF hV
      have h' : ((E.card + 1 : ℕ) : ℕ∞) ≤ V.card := by exact_mod_cast h
      push_cast at h'
      calc (E.card : ℕ∞) + 2 = (E.card + 1) + 1 := by rw [add_assoc]; norm_num
        _ ≤ V.card + 1 := add_le_add h' le_rfl
        _ = 1 + V.card := add_comm _ _

end Forest

section Boundary

def edgeOpenSeg (e : Sym2 ℂ) : Set ℂ :=
  Sym2.lift ⟨fun a b => openSegment ℝ a b, fun a b => openSegment_symm ℝ a b⟩ e

@[simp] lemma edgeOpenSeg_mk (a b : ℂ) : edgeOpenSeg s(a, b) = openSegment ℝ a b := rfl

def bdryEdges (E : Finset (Sym2 ℂ)) (f : Set ℂ) : Finset (Sym2 ℂ) :=
  E.filter (fun e => (edgeOpenSeg e ∩ closure f).Nonempty)

lemma mem_faces_iff {V : Finset ℂ} {E : Finset (Sym2 ℂ)} {f : Set ℂ} :
    f ∈ faces V E ↔ ∃ x ∈ (drawing V E)ᶜ, f = connectedComponentIn (drawing V E)ᶜ x := by
  unfold faces comps
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩

lemma isOpen_face {V : Finset ℂ} {E : Finset (Sym2 ℂ)} {f : Set ℂ} (hf : f ∈ faces V E) :
    IsOpen f := by
  obtain ⟨x, -, rfl⟩ := mem_faces_iff.1 hf
  exact (isClosed_drawing V E).isOpen_compl.connectedComponentIn

lemma mem_face_of_mem_closure {S : Set ℂ} (hS : IsOpen S) {x z : ℂ}
    (hz : z ∈ closure (connectedComponentIn S x)) (hzS : z ∈ S) :
    z ∈ connectedComponentIn S x := by
  obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.1 hz _ hS.connectedComponentIn
    (mem_connectedComponentIn hzS)
  rw [connectedComponentIn_eq hy2, ← connectedComponentIn_eq hy1]
  exact mem_connectedComponentIn hzS

lemma drawing_mono {V : Finset ℂ} {E E' : Finset (Sym2 ℂ)} (h : E' ⊆ E) :
    drawing V E' ⊆ drawing V E := by
  intro z hz
  rcases hz with hz | hz
  · exact Or.inl hz
  · obtain ⟨e, he, hze⟩ := mem_iUnion₂.1 hz
    exact Or.inr (mem_iUnion₂.2 ⟨e, h he, hze⟩)

lemma mem_faces_bdryEdges {V : Finset ℂ} {E : Finset (Sym2 ℂ)} (hP : IsPlaneGraph V E)
    {f : Set ℂ} (hf : f ∈ faces V E) : f ∈ faces V (bdryEdges E f) := by
  have hsub : drawing V (bdryEdges E f) ⊆ drawing V E := drawing_mono (Finset.filter_subset _ _)
  obtain ⟨x, hx, rfl⟩ := mem_faces_iff.1 hf
  set S := (drawing V E)ᶜ
  set f := connectedComponentIn S x with hfdef
  have hS : IsOpen S := (isClosed_drawing V E).isOpen_compl
  have hxS' : x ∈ (drawing V (bdryEdges E f))ᶜ := fun h => hx (hsub h)
  refine mem_faces_iff.2 ⟨x, hxS', le_antisymm ?_ ?_⟩
  · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hx) ((connectedComponentIn_subset _ _).trans
        (compl_subset_compl.2 hsub))
  · refine isPreconnected_connectedComponentIn.subset_of_closure_inter_subset
      hS.connectedComponentIn ⟨x, mem_connectedComponentIn hxS', mem_connectedComponentIn hx⟩ ?_
    rintro z ⟨hzc, hz'⟩
    have hzB : z ∉ drawing V (bdryEdges E f) := connectedComponentIn_subset _ _ hz'
    by_cases hzd : z ∈ drawing V E
    · exfalso
      rcases hzd with hzV | hzE
      · exact hzB (Or.inl hzV)
      · obtain ⟨e, he, hze⟩ := mem_iUnion₂.1 hzE
        induction e using Sym2.ind with
        | _ a b =>
        have ha : a ∈ V := hP.mem_V _ he a (Sym2.mem_mk_left _ _)
        have hb : b ∈ V := hP.mem_V _ he b (Sym2.mem_mk_right _ _)
        rw [edgeSeg_mk, ← insert_endpoints_openSegment] at hze
        rcases hze with rfl | rfl | hzo
        · exact hzB (Or.inl ha)
        · exact hzB (Or.inl hb)
        · apply hzB
          refine Or.inr (mem_iUnion₂.2 ⟨s(a, b), ?_, ?_⟩)
          · exact Finset.mem_filter.2 ⟨he, z, hzo, hzc⟩
          · rw [edgeSeg_mk]; exact openSegment_subset_segment ℝ a b hzo
    · exact mem_face_of_mem_closure hS hzc hzd

lemma side_face {V : Finset ℂ} {E : Finset (Sym2 ℂ)} (hP : IsPlaneGraph V E) {a b : ℂ}
    (he : s(a, b) ∈ E) :
    ∃ F, ∀ z ∈ openSegment ℝ a b, ∃ ρ > 0, ∀ f ∈ faces V E, ∀ y ∈ ball z ρ ∩ f,
      (wc a b y).im > 0 → f = F := by
  have hab : a ≠ b := fun h => hP.not_diag _ he (by simp [h])
  set H := drawing V (E.erase s(a, b)) with hH
  have hHc : IsClosed H := isClosed_drawing _ _
  have hseg : ∀ z ∈ openSegment ℝ a b, z ∉ H :=
    openSegment_not_mem_drawing hP he subset_rfl subset_rfl
  have hA : ∀ z ∈ openSegment ℝ a b, (wc a b z).im = 0 := fun z hz =>
    ((mem_openSegment_iff_wc hab z).1 hz).1
  obtain ⟨p0, hp0⟩ := exists_mem_openSegment hab
  obtain ⟨xL, hxL, hloc⟩ := exists_left_comp hab hHc hseg hA hp0
  set U := connectedComponentIn Hᶜ p0
  have ha : a ∈ H := Or.inl (hP.mem_V _ he a (Sym2.mem_mk_left _ _))
  have hb : b ∈ H := Or.inl (hP.mem_V _ he b (Sym2.mem_mk_right _ _))
  have hdr : (drawing V E)ᶜ = Hᶜ \ openSegment ℝ a b := by
    have : drawing V E = H ∪ segment ℝ a b := by
      rw [hH, ← edgeSeg_mk, ← drawing_insert_edge, Finset.insert_erase he]
    rw [this]
    ext z
    simp only [mem_compl_iff, mem_union, mem_diff, ← insert_endpoints_openSegment,
      mem_insert_iff, not_or]
    constructor
    · rintro ⟨h1, _, _, h4⟩; exact ⟨h1, h4⟩
    · rintro ⟨h1, h4⟩
      exact ⟨h1, fun h => h1 (h ▸ ha), fun h => h1 (h ▸ hb), h4⟩

  have hcomp : ∀ y ∈ U \ openSegment ℝ a b, connectedComponentIn (drawing V E)ᶜ y =
      connectedComponentIn (U \ openSegment ℝ a b) y := fun y hy => by
    rw [hdr]; exact connectedComponentIn_diff_of_mem hy.1 hy.2
  refine ⟨connectedComponentIn (drawing V E)ᶜ xL, ?_⟩
  intro z hz
  obtain ⟨ρ, hρ, hρU, hline, hleft⟩ := hloc z hz
  refine ⟨ρ, hρ, ?_⟩
  rintro f hf y ⟨hyb, hyf⟩ hyim
  have hyL : y ∈ connectedComponentIn (U \ openSegment ℝ a b) xL :=
    hleft ⟨hyb, hyim⟩
  have hyUA : y ∈ U \ openSegment ℝ a b := connectedComponentIn_subset _ _ hyL
  obtain ⟨x, hx, rfl⟩ := mem_faces_iff.1 hf
  rw [connectedComponentIn_eq hyf, hcomp y hyUA, hcomp xL hxL,
    connectedComponentIn_eq hyL]

lemma encard_faces_bdry_le_two {V : Finset ℂ} {E : Finset (Sym2 ℂ)} (hP : IsPlaneGraph V E)
    {e : Sym2 ℂ} (he : e ∈ E) : {f ∈ faces V E | e ∈ bdryEdges E f}.encard ≤ 2 := by
  induction e using Sym2.ind with
  | _ a b =>
  have hab : a ≠ b := fun h => hP.not_diag _ he (by simp [h])
  obtain ⟨F1, hF1⟩ := side_face hP he
  obtain ⟨F2, hF2⟩ := side_face hP (by rwa [Sym2.eq_swap] at he)
  have hsub : {f ∈ faces V E | s(a, b) ∈ bdryEdges E f} ⊆ {F1, F2} := by
    rintro f ⟨hf, hfe⟩
    obtain ⟨-, z, hz, hzc⟩ := Finset.mem_filter.1 hfe
    rw [edgeOpenSeg_mk] at hz
    set H := drawing V (E.erase s(a, b))
    have hseg : ∀ z ∈ openSegment ℝ a b, z ∉ H :=
      openSegment_not_mem_drawing hP he subset_rfl subset_rfl
    obtain ⟨ρ, hρ, -, hline⟩ := exists_ball_local hab (isClosed_drawing _ _) hz (hseg z hz)

    have hfo : ∀ y ∈ ball z ρ ∩ f, (wc a b y).im ≠ 0 := by
      rintro y ⟨hyb, hyf⟩ him
      have hyo := hline y hyb him
      have : y ∈ drawing V E := by
        refine Or.inr (mem_iUnion₂.2 ⟨s(a, b), he, ?_⟩)
        rw [edgeSeg_mk]; exact openSegment_subset_segment ℝ a b hyo
      obtain ⟨x, hx, rfl⟩ := mem_faces_iff.1 hf
      exact connectedComponentIn_subset _ _ hyf this
    obtain ⟨ρ1, hρ1, h1⟩ := hF1 z hz
    obtain ⟨ρ2, hρ2, h2⟩ := hF2 z (by rwa [openSegment_symm])
    obtain ⟨y, hyb, hyf⟩ := mem_closure_iff.1 hzc _ isOpen_ball
      (mem_ball_self (lt_min hρ (lt_min hρ1 hρ2)))
    have hyb0 : y ∈ ball z ρ := ball_subset_ball (min_le_left _ _) hyb
    have hyb1 : y ∈ ball z ρ1 := ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hyb
    have hyb2 : y ∈ ball z ρ2 :=
      ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hyb
    rcases lt_or_gt_of_ne (hfo y ⟨hyb0, hyf⟩) with hneg | hpos
    · right
      refine h2 f hf y ⟨hyb2, hyf⟩ ?_
      rw [wc_swap hab, sub_im, one_im]; linarith
    · left
      exact h1 f hf y ⟨hyb1, hyf⟩ hpos
  calc {f ∈ faces V E | s(a, b) ∈ bdryEdges E f}.encard ≤ ({F1, F2} : Set (Set ℂ)).encard :=
        encard_le_encard hsub
    _ ≤ 2 := by
        refine (encard_insert_le _ _).trans ?_
        rw [encard_singleton]; norm_num

lemma exists_not_mem_drawing (V : Finset ℂ) (E : Finset (Sym2 ℂ)) : ∃ p, p ∉ drawing V E := by
  have hc : IsCompact (drawing V E) := by
    refine V.finite_toSet.isCompact.union (E.finite_toSet.isCompact_biUnion fun e _ => ?_)
    induction e using Sym2.ind with
    | _ a b => rw [edgeSeg_mk, segment_eq_image]; exact isCompact_Icc.image (by fun_prop)
  by_contra h
  push_neg at h
  exact hc.ne_univ (eq_univ_of_forall h)

lemma not_forest_bdryEdges {V : Finset ℂ} {E : Finset (Sym2 ℂ)} (hP : IsPlaneGraph V E)
    {f : Set ℂ} (hf : f ∈ faces V E) {p : ℂ} (hp : p ∉ drawing V E) (hpf : p ∉ f) :
    ¬ IsForestE (bdryEdges E f) := by
  intro hF
  have hPB : IsPlaneGraph V (bdryEdges E f) := hP.mono subset_rfl (Finset.filter_subset _ _)
    (fun e he => hP.mem_V e (Finset.mem_filter.1 he).1)
  have h1 := encard_faces_forest _ rfl hPB hF
  have hfB := mem_faces_bdryEdges hP hf
  have hpB : p ∈ (drawing V (bdryEdges E f))ᶜ :=
    fun h => hp (drawing_mono (Finset.filter_subset _ _) h)
  have hgB : connectedComponentIn (drawing V (bdryEdges E f))ᶜ p ∈ faces V (bdryEdges E f) :=
    mem_faces_iff.2 ⟨p, hpB, rfl⟩
  have := Set.encard_le_one_iff.1 h1.le _ _ hfB hgB
  exact hpf (this ▸ mem_connectedComponentIn hpB)

lemma faces_finite {V : Finset ℂ} {E : Finset (Sym2 ℂ)} (hP : IsPlaneGraph V E) :
    (faces V E).Finite := by
  obtain ⟨p, hp⟩ := exists_not_mem_drawing V E
  have hsub : faces V E ⊆ {connectedComponentIn (drawing V E)ᶜ p} ∪
      ⋃ e ∈ E, {f ∈ faces V E | e ∈ bdryEdges E f} := by
    intro f hf
    by_cases hpf : p ∈ f
    · left
      obtain ⟨x, hx, rfl⟩ := mem_faces_iff.1 hf
      exact connectedComponentIn_eq hpf
    · right
      have hnf := not_forest_bdryEdges hP hf hp hpf
      obtain ⟨e, he⟩ : (bdryEdges E f).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        rintro h
        rw [h] at hnf
        exact hnf (fun a b hab => absurd hab (Finset.notMem_empty _))
      exact mem_iUnion₂.2 ⟨e, (Finset.mem_filter.1 he).1, hf, he⟩
  refine Set.Finite.subset ((Set.finite_singleton _).union
    (E.finite_toSet.biUnion fun e he => ?_)) hsub
  exact Set.encard_lt_top_iff.1 ((encard_faces_bdry_le_two hP he).trans_lt (by decide))

lemma reach_cycle4 {a b c d : ℂ} {C : Finset (Sym2 ℂ)}
    (hC : C = {s(a, b), s(b, c), s(c, d), s(d, a)}) :
    ∀ u ∈ ({a, b, c, d} : Finset ℂ), ∀ v ∈ ({a, b, c, d} : Finset ℂ),
      Relation.ReflTransGen (fun x y => s(x, y) ∈ C) u v := by
  have h1 : Relation.ReflTransGen (fun x y => s(x, y) ∈ C) a b :=
    Relation.ReflTransGen.single (by rw [hC]; simp)
  have h2 : Relation.ReflTransGen (fun x y => s(x, y) ∈ C) a c :=
    h1.tail (by rw [hC]; simp)
  have h3 : Relation.ReflTransGen (fun x y => s(x, y) ∈ C) a d :=
    h2.tail (by rw [hC]; simp)
  have hfrom : ∀ u ∈ ({a, b, c, d} : Finset ℂ), Relation.ReflTransGen (fun x y => s(x, y) ∈ C) a u := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact Relation.ReflTransGen.refl
    · exact h1
    · exact h2
    · exact h3
  intro u hu v hv
  exact (reach_symm (hfrom u hu)).trans (hfrom v hv)

lemma eq_of_bdryEdges_cycle4 {V : Finset ℂ} {E : Finset (Sym2 ℂ)} (hP : IsPlaneGraph V E)
    {f f' : Set ℂ} (hf : f ∈ faces V E) (hf' : f' ∈ faces V E) {p : ℂ} (hp : p ∉ drawing V E)
    (hpf : p ∉ f) (hpf' : p ∉ f') {a b c d : ℂ} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hB : bdryEdges E f = {s(a, b), s(b, c), s(c, d), s(d, a)})
    (hB' : bdryEdges E f' = {s(a, b), s(b, c), s(c, d), s(d, a)}) : f = f' := by
  set C : Finset (Sym2 ℂ) := {s(a, b), s(b, c), s(c, d), s(d, a)} with hCdef
  set W : Finset ℂ := {a, b, c, d} with hWdef
  have hCE : C ⊆ E := hB ▸ Finset.filter_subset _ _
  have hab' : s(a, b) ∈ E := hCE (by simp [hCdef])
  have hcd' : s(c, d) ∈ E := hCE (by simp [hCdef])
  have hWV : W ⊆ V := by
    intro x hx
    simp only [hWdef, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hP.mem_V _ hab' _ (Sym2.mem_mk_left _ _)
    · exact hP.mem_V _ hab' _ (Sym2.mem_mk_right _ _)
    · exact hP.mem_V _ hcd' _ (Sym2.mem_mk_left _ _)
    · exact hP.mem_V _ hcd' _ (Sym2.mem_mk_right _ _)
  have hCW : ∀ e ∈ C, ∀ v ∈ e, v ∈ W := by
    intro e he v hv
    simp only [hCdef, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl <;> rcases Sym2.mem_iff.1 hv with rfl | rfl <;>
      simp [hWdef]
  have hPW : IsPlaneGraph W C := hP.mono hWV hCE hCW
  have hconn : GraphConnected W C := ⟨⟨a, by simp [hWdef]⟩, reach_cycle4 hCdef⟩
  obtain ⟨hfin, heul⟩ := euler_formula hPW hconn
  have hWc : W.card = 4 := by
    rw [hWdef, Finset.card_insert_of_notMem (by simp [hab, hac, had]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd]),
      Finset.card_insert_of_notMem (by simp [hcd]), Finset.card_singleton]
  have hCc : C.card = 4 := by
    rw [hCdef, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [hcd, had.symm, hac.symm]
    · simp [hbc, hbd, hab.symm]
    · simp [hab, hac, had, hbc, hbd, hab.symm]
  have hF2 : (faces W C).ncard = 2 := by omega

  have hdr : (drawing V C)ᶜ = (drawing W C)ᶜ \ (V : Set ℂ) := by
    ext z
    simp only [drawing, mem_compl_iff, mem_union, mem_diff, Finset.mem_coe, not_or]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨fun h => h1 (hWV h), h2⟩, h1⟩
    · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
  have key : ∀ g ∈ faces V E, bdryEdges E g = C →
      ∃ x ∈ (drawing W C)ᶜ, g = connectedComponentIn (drawing W C)ᶜ x \ (V : Set ℂ) := by
    intro g hg hgB
    have hgC := mem_faces_bdryEdges hP hg
    rw [hgB] at hgC
    obtain ⟨x, hx, rfl⟩ := mem_faces_iff.1 hgC
    have hx' : x ∈ (drawing W C)ᶜ \ (V : Set ℂ) := hdr ▸ hx
    refine ⟨x, hx'.1, le_antisymm ?_ ?_⟩
    · intro y hy
      have hy' := connectedComponentIn_subset _ _ hy
      rw [hdr] at hy'
      refine ⟨?_, hy'.2⟩
      rw [hdr] at hy
      exact connectedComponentIn_mono _ diff_subset hy
    · rw [hdr]
      refine (isPreconnected_diff_finset
        (isClosed_drawing W C).isOpen_compl.connectedComponentIn
        isPreconnected_connectedComponentIn V).subset_connectedComponentIn
        ⟨mem_connectedComponentIn hx'.1, hx'.2⟩ ?_
      exact diff_subset_diff_left (connectedComponentIn_subset _ _)
  obtain ⟨x, hx, hfx⟩ := key f hf hB
  obtain ⟨x', hx', hfx'⟩ := key f' hf' hB'
  have hpW : p ∈ (drawing W C)ᶜ := fun h => hp (drawing_mono hCE
    (show p ∈ drawing V C from by
      rcases h with h | h
      · exact Or.inl (hWV h)
      · exact Or.inr h))
  have hpV : p ∉ (V : Set ℂ) := fun h => hp (Or.inl h)
  set g := connectedComponentIn (drawing W C)ᶜ x
  set g' := connectedComponentIn (drawing W C)ᶜ x'
  set g0 := connectedComponentIn (drawing W C)ᶜ p
  have hg : g ∈ faces W C := mem_faces_iff.2 ⟨x, hx, rfl⟩
  have hg' : g' ∈ faces W C := mem_faces_iff.2 ⟨x', hx', rfl⟩
  have hg0 : g0 ∈ faces W C := mem_faces_iff.2 ⟨p, hpW, rfl⟩
  have hne : g ≠ g0 := fun h => hpf (hfx ▸ ⟨h ▸ mem_connectedComponentIn hpW, hpV⟩)
  have hne' : g' ≠ g0 := fun h => hpf' (hfx' ▸ ⟨h ▸ mem_connectedComponentIn hpW, hpV⟩)
  have hgg : g = g' := by
    by_contra hgg
    have : ({g, g', g0} : Set (Set ℂ)).ncard ≤ (faces W C).ncard :=
      Set.ncard_le_ncard (by
        intro h hh
        simp only [mem_insert_iff, mem_singleton_iff] at hh
        rcases hh with rfl | rfl | rfl
        · exact hg
        · exact hg'
        · exact hg0) hfin
    rw [Set.ncard_insert_of_notMem (by simp [hgg, hne]), Set.ncard_pair hne', hF2] at this
    omega
  rw [hfx, hfx', hgg]

end Boundary

section UnitGraph

def unitPairs (X : Finset ℂ) : Finset (Sym2 ℂ) :=
  X.sym2.filter (fun e => edgeLen e = 1)

def unitRhombi (X : Finset ℂ) : Finset (Finset ℂ) :=
  (X.powersetCard 4).filter (fun S => ∃ a b c d : ℂ, S = {a, b, c, d} ∧
    dist a b = 1 ∧ dist b c = 1 ∧ dist c d = 1 ∧ dist d a = 1)

lemma mem_unitPairs {X : Finset ℂ} {a b : ℂ} :
    s(a, b) ∈ unitPairs X ↔ a ∈ X ∧ b ∈ X ∧ dist a b = 1 := by
  simp [unitPairs, Finset.mem_sym2_iff, edgeLen_mk, and_assoc]

lemma seg_inter_common {a b d z : ℂ} (hab : dist a b = 1) (had : dist a d = 1)
    (hz1 : z ∈ segment ℝ a b) (hz2 : z ∈ segment ℝ a d) (hbd : b ≠ d) : z = a := by
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := (segment_eq_image_lineMap ℝ a b ▸ hz1 :)
  obtain ⟨s, ⟨hs0, hs1⟩, hs⟩ := (segment_eq_image_lineMap ℝ a d ▸ hz2 :)
  simp only [AffineMap.lineMap_apply_module'] at hs ⊢
  have hn1 : ‖b - a‖ = 1 := by rw [← dist_eq_norm, dist_comm]; exact hab
  have hn2 : ‖d - a‖ = 1 := by rw [← dist_eq_norm, dist_comm]; exact had
  have hts : s = t := by
    have := congrArg (fun w => ‖w - a‖) hs
    simp only [add_sub_cancel_right, norm_smul, Real.norm_eq_abs, hn1, hn2, mul_one,
      abs_of_nonneg ht0, abs_of_nonneg hs0] at this
    exact this
  subst hts
  by_cases hs0' : s = 0
  · subst hs0'; simp
  · exfalso; apply hbd
    have : s • (d - a) = s • (b - a) := by linear_combination (exp := 1) hs
    have := smul_right_injective ℂ hs0' this
    linear_combination -this

lemma seg_inter_disjoint {X : Finset ℂ} (hX : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → 1 ≤ dist x y)
    {a b c d : ℂ} (ha : a ∈ X) (hb : b ∈ X) (hc : c ∈ X) (hd : d ∈ X)
    (hab : dist a b = 1) (hcd : dist c d = 1)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) {p : ℂ}
    (hp1 : p ∈ segment ℝ a b) (hp2 : p ∈ segment ℝ c d) : False := by
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
  exact hbc (by rw [hpb] at hpc; linear_combination hpc)

lemma isPlaneGraph_unitPairs {X : Finset ℂ} (hX : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → 1 ≤ dist x y) :
    IsPlaneGraph X (unitPairs X) where
  mem_V e he v hv := by
    unfold unitPairs at he
    exact Finset.mem_sym2_iff.1 (Finset.mem_filter.1 he).1 v hv
  not_diag e he := by
    induction e using Sym2.ind with
    | _ a b =>
    intro h
    rw [Sym2.mk_isDiag_iff] at h
    subst h
    have := (mem_unitPairs.1 he).2.2
    simp at this
  vertex_mem e he v hv hve := by
    induction e using Sym2.ind with
    | _ a b =>
    obtain ⟨ha, hb, hab⟩ := mem_unitPairs.1 he
    rw [edgeSeg_mk] at hve
    have h := dist_add_dist_of_mem_segment hve
    by_contra hne
    simp only [Sym2.mem_iff, not_or] at hne
    have := hX a ha v hv (Ne.symm hne.1)
    have := hX v hv b hb hne.2
    linarith
  inter e he e' he' hne z hz hz' := by
    induction e using Sym2.ind with
    | _ a b =>
    induction e' using Sym2.ind with
    | _ c d =>
    obtain ⟨ha, hb, hab⟩ := mem_unitPairs.1 he
    obtain ⟨hc, hd, hcd⟩ := mem_unitPairs.1 he'
    rw [edgeSeg_mk] at hz hz'
    have hdc : dist d c = 1 := by rw [dist_comm]; exact hcd
    have hba : dist b a = 1 := by rw [dist_comm]; exact hab
    by_cases hac : a = c
    · subst hac
      have hbd : b ≠ d := fun h => hne (by rw [h])
      rw [seg_inter_common hab hcd hz hz' hbd]; exact Sym2.mem_mk_left _ _
    by_cases had : a = d
    · subst had
      have hbc : b ≠ c := fun h => hne (by rw [h, Sym2.eq_swap])
      rw [segment_symm] at hz'
      rw [seg_inter_common hab hdc hz hz' hbc]; exact Sym2.mem_mk_left _ _
    by_cases hbc : b = c
    · subst hbc
      rw [segment_symm] at hz
      rw [seg_inter_common hba hcd hz hz' had]; exact Sym2.mem_mk_right _ _
    by_cases hbd : b = d
    · subst hbd
      rw [segment_symm] at hz hz'
      rw [seg_inter_common hba hdc hz hz' hac]; exact Sym2.mem_mk_right _ _
    exact (seg_inter_disjoint hX ha hb hc hd hab hcd hac had hbc hbd hz hz').elim

lemma cycle_of_not_forest {X : Finset ℂ} {B : Finset (Sym2 ℂ)} (hB : B ⊆ unitPairs X)
    (htri : ∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X, dist x y = 1 → dist y z = 1 → dist z x ≠ 1)
    (hnf : ¬ IsForestE B) :
    4 ≤ B.card ∧ (B.card = 4 → ∃ a b c d, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      B = {s(a, b), s(b, c), s(c, d), s(d, a)}) := by
  unfold IsForestE at hnf
  push_neg at hnf
  obtain ⟨a, b, hab, hr⟩ := hnf
  set R := B.erase s(a, b) with hR
  have hRu : ∀ x y, s(x, y) ∈ R → x ∈ X ∧ y ∈ X ∧ dist x y = 1 := fun x y h =>
    mem_unitPairs.1 (hB (Finset.mem_of_mem_erase h))
  obtain ⟨ha, hb, hdab⟩ := mem_unitPairs.1 (hB hab)
  have hane : a ≠ b := fun h => by rw [h, dist_self] at hdab; norm_num at hdab
  let G : SimpleGraph ℂ := SimpleGraph.fromEdgeSet (R : Set (Sym2 ℂ))
  have hadj : ∀ x y, G.Adj x y ↔ s(x, y) ∈ R ∧ x ≠ y := fun x y => by
    simp [G, SimpleGraph.fromEdgeSet_adj]
  have key : ∀ y, Relation.ReflTransGen (fun x y => s(x, y) ∈ R) a y → G.Reachable a y := by
    intro y hy
    induction hy with
    | refl => exact SimpleGraph.Reachable.refl _
    | @tail x y _ hxy ih =>
      refine SimpleGraph.Reachable.trans ih (SimpleGraph.Adj.reachable ((hadj x y).2 ⟨hxy, ?_⟩))
      intro h; have := (hRu x y hxy).2.2; rw [h, dist_self] at this; norm_num at this
  have hreach : G.Reachable a b := key b hr
  obtain ⟨⟨w, hw⟩⟩ : Nonempty (G.Path a b) := ⟨hreach.some.toPath⟩
  have hedges : ∀ e ∈ w.edges, e ∈ R := by
    intro e he
    have := w.edges_subset_edgeSet he
    induction e using Sym2.ind with
    | _ x y => exact ((hadj x y).1 this).1
  have hlen : w.length ≤ R.card := by
    rw [← SimpleGraph.Walk.length_edges, ← List.toFinset_card_of_nodup hw.isTrail.edges_nodup]
    exact Finset.card_le_card (fun e he => hedges e (List.mem_toFinset.1 he))
  have hBc : B.card = R.card + 1 := (Finset.card_erase_add_one hab).symm
  have hunit : ∀ x y, G.Adj x y → dist x y = 1 ∧ x ∈ X ∧ y ∈ X := fun x y h =>
    let h' := hRu x y ((hadj x y).1 h).1; ⟨h'.2.2, h'.1, h'.2.1⟩
  cases w with
  | nil => exact absurd rfl hane
  | cons h1 w1 =>
    rename_i c
    cases w1 with
    | nil => exact absurd ((hadj _ _).1 h1).1 (Finset.notMem_erase _ _)
    | cons h2 w2 =>
      rename_i d
      cases w2 with
      | nil =>
        obtain ⟨u1, -, hc⟩ := hunit _ _ h1
        obtain ⟨u2, -, -⟩ := hunit _ _ h2
        exact absurd (by rw [dist_comm]; exact hdab) (htri a ha c hc b hb u1 u2)
      | cons h3 w3 =>
        rename_i e
        simp only [SimpleGraph.Walk.length_cons] at hlen
        refine ⟨by omega, fun h4 => ?_⟩
        have hw3 : w3.length = 0 := by omega
        have hw3' := SimpleGraph.Walk.eq_of_length_eq_zero hw3
        subst hw3'
        rw [SimpleGraph.Walk.length_eq_zero_iff] at hw3
        rw [SimpleGraph.Walk.nil_iff_eq_nil] at hw3
        subst w3

        have hsupp := hw.support_nodup
        simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
          List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hsupp
        obtain ⟨⟨hac, had, hab'⟩, ⟨hcd, hcb⟩, hdb, -⟩ := hsupp
        have hRe : R = {s(a, c), s(c, d), s(d, e)} := by
          have hsub : ({s(a, c), s(c, d), s(d, e)} : Finset (Sym2 ℂ)) ⊆ R := by
            intro f hf
            simp only [Finset.mem_insert, Finset.mem_singleton] at hf
            rcases hf with rfl | rfl | rfl
            · exact ((hadj _ _).1 h1).1
            · exact ((hadj _ _).1 h2).1
            · exact ((hadj _ _).1 h3).1
          symm
          apply Finset.eq_of_subset_of_card_le hsub
          rw [Finset.card_insert_of_notMem (by simp [hac, had, hcd]),
            Finset.card_insert_of_notMem (by simp [hcd, hcb]),
            Finset.card_singleton]
          omega
        refine ⟨a, e, d, c, hab', had, hac, Ne.symm hdb, Ne.symm hcb, Ne.symm hcd, ?_⟩
        rw [← Finset.insert_erase hab, ← hR, hRe]
        ext f
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro (h | h | h | h) <;> subst h <;> simp [Sym2.eq_swap]
        · rintro (h | h | h | h) <;> subst h <;> simp [Sym2.eq_swap]

lemma unit_pair_in_cycle {X : Finset ℂ}
    (htri : ∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X, dist x y = 1 → dist y z = 1 → dist z x ≠ 1)
    {a b c d : ℂ} (ha : a ∈ X) (hb : b ∈ X) (hc : c ∈ X) (hd : d ∈ X)
    (hab' : a ≠ b) (hac' : a ≠ c) (had' : a ≠ d) (hbc' : b ≠ c) (hbd' : b ≠ d) (hcd' : c ≠ d)
    (hab : dist a b = 1) (hbc : dist b c = 1) (hcd : dist c d = 1) (hda : dist d a = 1)
    {x y : ℂ} (hx : x ∈ ({a, b, c, d} : Finset ℂ)) (hy : y ∈ ({a, b, c, d} : Finset ℂ))
    (hxy : dist x y = 1) :
    s(x, y) ∈ ({s(a, b), s(b, c), s(c, d), s(d, a)} : Finset (Sym2 ℂ)) := by
  have t1 : dist c a ≠ 1 := htri a ha b hb c hc hab hbc
  have t2 : dist d b ≠ 1 := htri b hb c hc d hd hbc hcd
  have t1' : dist a c ≠ 1 := by rwa [dist_comm]
  have t2' : dist b d ≠ 1 := by rwa [dist_comm]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    simp_all [Sym2.eq_swap]

theorem unit_graph_counts {X : Finset ℂ} (hX : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → 1 ≤ dist x y)
    (htri : ∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X, dist x y = 1 → dist y z = 1 → dist z x ≠ 1)
    (hne : X.Nonempty) :
    (unitPairs X).card + 2 ≤ 2 * X.card ∧
      3 * (unitPairs X).card + 5 ≤ 5 * X.card + (unitRhombi X).card := by
  set E := unitPairs X with hEdef
  have hP := isPlaneGraph_unitPairs hX
  obtain ⟨p, hp⟩ := exists_not_mem_drawing X E
  have hfin := faces_finite hP
  set F := hfin.toFinset with hFdef
  set f0 := connectedComponentIn (drawing X E)ᶜ p with hf0def
  have hf0 : f0 ∈ F := hfin.mem_toFinset.2 (mem_faces_iff.2 ⟨p, hp, rfl⟩)
  set F' := F.erase f0 with hF'def
  have hfaces : ∀ f ∈ F', f ∈ faces X E := fun f hf =>
    hfin.mem_toFinset.1 (Finset.mem_of_mem_erase hf)
  have hpf : ∀ f ∈ F', p ∉ f := by
    intro f hf hpf
    obtain ⟨x, hx, rfl⟩ := mem_faces_iff.1 (hfaces f hf)
    exact (Finset.mem_erase.1 hf).1 (connectedComponentIn_eq hpf)
  have hcyc : ∀ f ∈ F', 4 ≤ (bdryEdges E f).card ∧ ((bdryEdges E f).card = 4 →
      ∃ a b c d, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
        bdryEdges E f = {s(a, b), s(b, c), s(c, d), s(d, a)}) := fun f hf =>
    cycle_of_not_forest (Finset.filter_subset _ _) htri
      (not_forest_bdryEdges hP (hfaces f hf) hp (hpf f hf))

  have heul := euler_ineq _ rfl hP hne
  rw [hfin.encard_eq_coe_toFinset_card] at heul
  have heul' : E.card + 2 ≤ F.card + X.card := by exact_mod_cast heul
  have hF'c : F'.card + 1 = F.card := Finset.card_erase_add_one hf0

  have hsum : ∑ f ∈ F', (bdryEdges E f).card ≤ 2 * E.card := by
    calc ∑ f ∈ F', (bdryEdges E f).card
        = ∑ f ∈ F', ∑ e ∈ E, if e ∈ bdryEdges E f then 1 else 0 := by
          refine Finset.sum_congr rfl fun f _ => ?_
          rw [Finset.sum_boole, Nat.cast_id]
          congr 1
          ext e
          simp only [Finset.mem_filter]
          exact ⟨fun h => ⟨Finset.mem_of_mem_filter _ h, h⟩, fun h => h.2⟩
      _ = ∑ e ∈ E, (F'.filter (fun f => e ∈ bdryEdges E f)).card := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [Finset.sum_boole, Nat.cast_id]
      _ ≤ ∑ e ∈ E, 2 := by
          refine Finset.sum_le_sum fun e he => ?_
          have h2 := encard_faces_bdry_le_two hP he
          have hsub : ((F'.filter (fun f => e ∈ bdryEdges E f) : Finset (Set ℂ)) : Set (Set ℂ)) ⊆
              {f ∈ faces X E | e ∈ bdryEdges E f} := by
            intro f hf
            rw [Finset.coe_filter] at hf
            exact ⟨hfaces f hf.1, hf.2⟩
          have := (encard_le_encard hsub).trans h2
          rw [Set.encard_coe_eq_coe_finsetCard] at this
          exact_mod_cast this
      _ = 2 * E.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

  set F4 := F'.filter (fun f => (bdryEdges E f).card = 4) with hF4def
  have hsplit : 4 * F4.card + 5 * (F'.card - F4.card) ≤ ∑ f ∈ F', (bdryEdges E f).card := by
    rw [← Finset.sum_filter_add_sum_filter_not F' (fun f => (bdryEdges E f).card = 4)]
    have h1 : ∑ f ∈ F4, (bdryEdges E f).card = 4 * F4.card := by
      rw [Finset.sum_congr rfl (fun f hf => (Finset.mem_filter.1 hf).2), Finset.sum_const,
        smul_eq_mul, mul_comm]
    have h2 : 5 * (F'.filter (fun f => ¬ (bdryEdges E f).card = 4)).card ≤
        ∑ f ∈ F'.filter (fun f => ¬ (bdryEdges E f).card = 4), (bdryEdges E f).card := by
      rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
      refine Finset.sum_le_sum fun f hf => ?_
      obtain ⟨hf, hne4⟩ := Finset.mem_filter.1 hf
      have := (hcyc f hf).1
      omega
    have h3 := Finset.card_filter_add_card_filter_not
      (s := F') (fun f => (bdryEdges E f).card = 4)
    rw [← hF4def] at h3 ⊢
    rw [h1]
    have : F'.card - F4.card = (F'.filter (fun f => ¬ (bdryEdges E f).card = 4)).card := by
      omega
    rw [this]
    omega
  have hq : F4.card ≤ (unitRhombi X).card := by
    let g : Set ℂ → Finset ℂ := fun f => X.filter (fun x => ∃ e ∈ bdryEdges E f, x ∈ e)

    have hdata : ∀ f ∈ F4, ∃ a b c d, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
        bdryEdges E f = {s(a, b), s(b, c), s(c, d), s(d, a)} ∧ a ∈ X ∧ b ∈ X ∧ c ∈ X ∧
        d ∈ X ∧ dist a b = 1 ∧ dist b c = 1 ∧ dist c d = 1 ∧ dist d a = 1 ∧
        g f = {a, b, c, d} := by
      intro f hf
      obtain ⟨hf', h4⟩ := Finset.mem_filter.1 hf
      obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hB⟩ := (hcyc f hf').2 h4
      have hu : ∀ x y, s(x, y) ∈ bdryEdges E f → x ∈ X ∧ y ∈ X ∧ dist x y = 1 :=
        fun x y h => mem_unitPairs.1 (Finset.mem_of_mem_filter _ h)
      obtain ⟨ha, hb, h1⟩ := hu a b (by rw [hB]; simp)
      obtain ⟨-, hc, h2⟩ := hu b c (by rw [hB]; simp)
      obtain ⟨-, hd, h3⟩ := hu c d (by rw [hB]; simp)
      obtain ⟨-, -, h4'⟩ := hu d a (by rw [hB]; simp)
      refine ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hB, ha, hb, hc, hd, h1, h2, h3, h4', ?_⟩
      ext x
      simp only [g, Finset.mem_filter, hB, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨-, e, he, hxe⟩
        rcases he with rfl | rfl | rfl | rfl <;> rcases Sym2.mem_iff.1 hxe with rfl | rfl <;>
          simp
      · rintro (rfl | rfl | rfl | rfl)
        · exact ⟨ha, s(x, b), Or.inl rfl, Sym2.mem_mk_left _ _⟩
        · exact ⟨hb, s(a, x), Or.inl rfl, Sym2.mem_mk_right _ _⟩
        · exact ⟨hc, s(x, d), Or.inr (Or.inr (Or.inl rfl)), Sym2.mem_mk_left _ _⟩
        · exact ⟨hd, s(c, x), Or.inr (Or.inr (Or.inl rfl)), Sym2.mem_mk_right _ _⟩
    refine Finset.card_le_card_of_injOn g ?_ ?_
    · intro f hf
      obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, -, ha, hb, hc, hd, h1, h2, h3, h4,
        hg⟩ := hdata f hf
      rw [Finset.mem_coe, hg]
      refine Finset.mem_filter.2 ⟨Finset.mem_powersetCard.2 ⟨?_, ?_⟩,
        a, b, c, d, rfl, h1, h2, h3, h4⟩
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> assumption
      · rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
          Finset.card_insert_of_notMem (by simp [hbc, hbd]),
          Finset.card_insert_of_notMem (by simp [hcd]), Finset.card_singleton]
    · intro f hf f' hf' hgg
      obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hB, ha, hb, hc, hd, h1, h2, h3, h4,
        hg⟩ := hdata f hf
      obtain ⟨a', b', c', d', -, -, -, -, -, -, hB', -, -, -, -, -, -, -, -, hg'⟩ :=
        hdata f' hf'
      have hsub : bdryEdges E f' ⊆ bdryEdges E f := by
        intro e he
        induction e using Sym2.ind with
        | _ x y =>
        have hxy := mem_unitPairs.1 (Finset.mem_of_mem_filter _ he)
        have hxg : x ∈ g f' := Finset.mem_filter.2 ⟨hxy.1, _, he, Sym2.mem_mk_left _ _⟩
        have hyg : y ∈ g f' := Finset.mem_filter.2 ⟨hxy.2.1, _, he, Sym2.mem_mk_right _ _⟩
        have hgg' : g f' = g f := hgg.symm
        rw [hgg', hg] at hxg hyg
        rw [hB]
        exact unit_pair_in_cycle htri ha hb hc hd hab hac had hbc hbd hcd h1 h2 h3 h4 hxg hyg
          hxy.2.2
      have hBB : bdryEdges E f' = bdryEdges E f := Finset.eq_of_subset_of_card_le hsub
        (by rw [(Finset.mem_filter.1 hf).2, (Finset.mem_filter.1 hf').2])
      have hff := Finset.mem_of_mem_filter _ hf
      have hff' := Finset.mem_of_mem_filter _ hf'
      exact eq_of_bdryEdges_cycle4 hP (hfaces f hff) (hfaces f' hff') hp (hpf f hff)
        (hpf f' hff') hab hac had hbc hbd hcd hB (hBB.trans hB)
  have hF4le : F4.card ≤ F'.card := Finset.card_filter_le _ _
  constructor
  · omega
  · omega

end UnitGraph

end EstablishedExternalResults
end

end PlaneFaces

section FaceCount

open scoped BigOperators Real
open EstablishedExternalResults

@[expose] public noncomputable section

open Classical

namespace Erdos99

def toC : Plane ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm

lemma dist_toC (x y : Plane) : dist (toC x) (toC y) = dist x y := toC.dist_map x y

lemma mem_unitEdges {X : Finset Plane} {a b : Plane} :
    s(a, b) ∈ unitEdges X ↔ a ∈ X ∧ b ∈ X ∧ dist a b = 1 := by
  unfold unitEdges
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨x, y, ⟨⟨hx, hy⟩, hxy⟩, he⟩
    rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hx, hy, hxy⟩
    · exact ⟨hy, hx, by rw [dist_comm]; exact hxy⟩
  · rintro ⟨ha, hb, hab⟩
    exact ⟨a, b, ⟨⟨ha, hb⟩, hab⟩, rfl⟩

lemma unitPairs_image (X : Finset Plane) :
    unitPairs (X.image toC) = (unitEdges X).image (Sym2.map toC) := by
  ext e
  induction e using Sym2.ind with
  | _ u v =>
  rw [mem_unitPairs]
  constructor
  · rintro ⟨hu, hv, huv⟩
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hv
    exact Finset.mem_image.2 ⟨s(x, y), mem_unitEdges.2 ⟨hx, hy, by rwa [dist_toC] at huv⟩, rfl⟩
  · intro h
    obtain ⟨e', he', hmap⟩ := Finset.mem_image.1 h
    induction e' using Sym2.ind with
    | _ x y =>
    obtain ⟨hx, hy, hxy⟩ := mem_unitEdges.1 he'
    rw [Sym2.map_mk] at hmap
    rcases Sym2.eq_iff.1 hmap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨Finset.mem_image_of_mem _ hx, Finset.mem_image_of_mem _ hy, by rwa [dist_toC]⟩
    · exact ⟨Finset.mem_image_of_mem _ hy, Finset.mem_image_of_mem _ hx,
        by rw [dist_toC, dist_comm]; exact hxy⟩

lemma card_unitRhombi_image_le (X : Finset Plane) :
    (unitRhombi (X.image toC)).card ≤ (rhombi X).card := by
  refine Finset.card_le_card_of_injOn (fun S => S.image toC.symm) ?_ ?_
  · intro S hS
    rw [Finset.mem_coe] at hS ⊢
    obtain ⟨hP, a, b, c, d, rfl, h1, h2, h3, h4⟩ := Finset.mem_filter.1 hS
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.1 hP
    refine Finset.mem_filter.2 ⟨Finset.mem_powersetCard.2 ⟨?_, ?_⟩, toC.symm a, toC.symm b,
      toC.symm c, toC.symm d, by simp [Finset.image_insert], ?_, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 (hsub hy)
      simpa using hz
    · rw [Finset.card_image_of_injective _ toC.symm.injective, hcard]
    all_goals rw [LinearIsometryEquiv.dist_map]; assumption
  · intro S _ T _ h
    exact Finset.image_injective toC.symm.injective h

theorem unitEdges_rhombi_counts {X : Finset Plane} (hX : IsSeparated X)
    (htri : ¬ HasUnitTriangle X) (hne : X.Nonempty) :
    (unitEdges X).card + 2 ≤ 2 * X.card ∧
      3 * (unitEdges X).card + 5 ≤ 5 * X.card + (rhombi X).card := by
  set Y := X.image toC
  have hY : ∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → 1 ≤ dist x y := by
    intro x' hx' y' hy' hxy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hx'
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hy'
    rw [dist_toC]; exact hX x hx y hy (fun h => hxy (by rw [h]))
  have htriY : ∀ x ∈ Y, ∀ y ∈ Y, ∀ z ∈ Y, dist x y = 1 → dist y z = 1 → dist z x ≠ 1 := by
    intro x' hx' y' hy' z' hz' h1 h2 h3
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hx'
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hy'
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hz'
    rw [dist_toC] at h1 h2 h3
    exact htri ⟨x, hx, y, hy, z, hz, h1, h2, by rw [dist_comm]; exact h3⟩
  obtain ⟨c1, c2⟩ := unit_graph_counts hY htriY (hne.image _)
  have hYc : Y.card = X.card := Finset.card_image_of_injective _ toC.injective
  have hm : (unitPairs Y).card = (unitEdges X).card := by
    rw [unitPairs_image, Finset.card_image_of_injective _ (Sym2.map.injective toC.injective)]
  have hq : (unitRhombi Y).card ≤ (rhombi X).card := card_unitRhombi_image_le X
  rw [hm, hYc] at c1 c2
  exact ⟨c1, by omega⟩

end Erdos99
end

end FaceCount

section ContactFaces

open scoped BigOperators Real
open EstablishedExternalResults Set

@[expose] public noncomputable section

open Classical

namespace Erdos99

structure IsStrictConvexPolygon (k : ℕ) (v : ℕ → ℂ) : Prop where
  three_le : 3 ≤ k
  periodic : ∀ i, v (i + k) = v i
  left : ∀ i j, j % k ≠ i % k → j % k ≠ (i + 1) % k → v j ∈ leftHalf (v i) (v (i + 1))

def polygonEdges (k : ℕ) (v : ℕ → ℂ) : Finset (Sym2 ℂ) :=
  (Finset.range k).image (fun i => s(v i, v (i + 1)))

def cVerts (X : Finset Plane) : Finset ℂ := X.image toC

def cUnitEdges (X : Finset Plane) : Finset (Sym2 ℂ) := unitPairs (cVerts X)

def hullSideEdges (X : Finset Plane) : Finset (Sym2 ℂ) :=
  (ccwHullSides X).image (fun p => s(toC p.1, toC p.2))

def augEdges (X : Finset Plane) : Finset (Sym2 ℂ) := cUnitEdges X ∪ hullSideEdges X

def boundedFaces (V : Finset ℂ) (E : Finset (Sym2 ℂ)) : Set (Set ℂ) :=
  {F ∈ faces V E | Bornology.IsBounded F}

def contactFaces (X : Finset Plane) : Set (Set ℂ) := boundedFaces (cVerts X) (cUnitEdges X)

def faceSize (X : Finset Plane) (F : Set ℂ) : ℕ := (bdryEdges (cUnitEdges X) F).card

def faceCount (X : Finset Plane) (k : ℕ) : ℕ := {F ∈ contactFaces X | faceSize X F = k}.ncard

def rhombusFaces (X : Finset Plane) : Set (Set ℂ) := {F ∈ contactFaces X | faceSize X F = 4}

def exceptionalFaces (X : Finset Plane) : Set (Set ℂ) := {F ∈ contactFaces X | 5 ≤ faceSize X F}

def numExceptional (X : Finset Plane) : ℕ := (exceptionalFaces X).ncard

def numPentagons (X : Finset Plane) : ℕ := faceCount X 5

def numHexagons (X : Finset Plane) : ℕ := faceCount X 6

def faceExcess (X : Finset Plane) : ℕ := ∑ᶠ F ∈ exceptionalFaces X, (faceSize X F - 4)

def augFaces (X : Finset Plane) : Set (Set ℂ) := boundedFaces (cVerts X) (augEdges X)

def IsCap (X : Finset Plane) (v w : Plane) (F : Set ℂ) : Prop :=
  F ∈ augFaces X ∧ s(toC v, toC w) ∈ bdryEdges (augEdges X) F

def returnLength (X : Finset Plane) (v w : Plane) : ℕ :=
  if dist v w = 1 then 1 else
    if h : ∃ F, IsCap X v w F then (bdryEdges (augEdges X) h.choose).card - 1 else 0

def hullReturns (X : Finset Plane) (j : ℕ) : ℕ :=
  ((ccwHullSides X).filter (fun p => returnLength X p.1 p.2 = j)).card

def numUnitHullSides (X : Finset Plane) : ℕ := (unitHullSides X).card

def returnExcess (X : Finset Plane) : ℕ := ∑ p ∈ ccwHullSides X, (returnLength X p.1 p.2 - 2)

def outerWalkLength (X : Finset Plane) : ℕ := ∑ p ∈ ccwHullSides X, returnLength X p.1 p.2

def lockingDefect (X : Finset Plane) : ℤ :=
  (numUnitHullSides X : ℤ) - faceExcess X - returnExcess X

lemma returnLength_of_dist_eq_one {X : Finset Plane} {v w : Plane} (h : dist v w = 1) :
    returnLength X v w = 1 := by
  simp [returnLength, h]

lemma hullReturns_one {X : Finset Plane}
    (h2 : ∀ p ∈ ccwHullSides X, dist p.1 p.2 ≠ 1 → 2 ≤ returnLength X p.1 p.2) :
    hullReturns X 1 = numUnitHullSides X := by
  unfold hullReturns numUnitHullSides unitHullSides
  congr 1
  refine Finset.filter_congr (fun p hp => ?_)
  constructor
  · intro h
    by_contra hd
    have := h2 p hp hd
    omega
  · intro h; exact returnLength_of_dist_eq_one h

lemma sum_hullReturns {X : Finset Plane} (N : ℕ)
    (hN : ∀ p ∈ ccwHullSides X, returnLength X p.1 p.2 < N) :
    ∑ j ∈ Finset.range N, hullReturns X j = (ccwHullSides X).card := by
  unfold hullReturns
  rw [← Finset.card_biUnion]
  · congr 1
    ext p
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter]
    constructor
    · rintro ⟨j, -, hp, -⟩; exact hp
    · intro hp; exact ⟨_, hN p hp, hp, rfl⟩
  · intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_filter]
    intro p _ h1 h2
    exact hij (h1.symm.trans h2)

lemma outerWalkLength_eq {X : Finset Plane}
    (h2 : ∀ p ∈ ccwHullSides X, dist p.1 p.2 ≠ 1 → 2 ≤ returnLength X p.1 p.2) :
    (outerWalkLength X : ℤ) =
      2 * (ccwHullSides X).card - numUnitHullSides X + returnExcess X := by
  have key : ∀ p ∈ ccwHullSides X, (returnLength X p.1 p.2 : ℤ) =
      2 - (if dist p.1 p.2 = 1 then 1 else 0) + ((returnLength X p.1 p.2 - 2 : ℕ) : ℤ) := by
    intro p hp
    by_cases hd : dist p.1 p.2 = 1
    · simp [returnLength_of_dist_eq_one hd, hd]
    · have := h2 p hp hd
      simp only [hd, if_false]
      push_cast [this]
      ring
  unfold outerWalkLength returnExcess numUnitHullSides unitHullSides
  push_cast
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.card_filter]
  push_cast
  simp [mul_comm]

end Erdos99

end

end ContactFaces

section RhombusFaces

open scoped BigOperators Real
open EstablishedExternalResults Set Complex

@[expose] public noncomputable section

open Classical

namespace Erdos99

lemma rhombus_normal {a b c d : ℂ} (hab : dist a b = 1) (hbc : dist b c = 1) (hcd : dist c d = 1)
    (hda : dist d a = 1) (hac : a ≠ c) (hbd : b ≠ d) :
    ∃ t : ℝ, t ≠ 0 ∧ b = (a + c) / 2 + (I * t) * ((a - c) / 2) ∧
      d = (a + c) / 2 - (I * t) * ((a - c) / 2) := by
  set m := (a + c) / 2
  set u := (a - c) / 2
  have hu : u ≠ 0 := by
    intro h; apply hac; have : a - c = 0 := by linear_combination 2 * h
    exact sub_eq_zero.1 this
  set ζb := (b - m) / u
  set ζd := (d - m) / u
  have eb : b = m + ζb * u := by simp [ζb]; field_simp; ring
  have ed : d = m + ζd * u := by simp [ζd]; field_simp; ring
  have ea : a = m + u := by simp [m, u]; ring
  have ec : c = m - u := by simp [m, u]; ring
  have nsq : ∀ x y : ℂ, dist x y = 1 → normSq (x - y) = 1 := by
    intro x y h
    rw [dist_eq] at h
    rw [← Complex.sq_norm, h]; norm_num
  have h1 := nsq _ _ hab
  have h2 := nsq _ _ hbc
  have h3 := nsq _ _ hcd
  have h4 := nsq _ _ hda
  rw [ea, eb] at h1
  rw [eb, ec] at h2
  rw [ec, ed] at h3
  rw [ed, ea] at h4
  have r1 : m + u - (m + ζb * u) = (1 - ζb) * u := by ring
  have r2 : m + ζb * u - (m - u) = (ζb + 1) * u := by ring
  have r3 : m - u - (m + ζd * u) = (-1 - ζd) * u := by ring
  have r4 : m + ζd * u - (m + u) = (ζd - 1) * u := by ring
  rw [r1, map_mul] at h1
  rw [r2, map_mul] at h2
  rw [r3, map_mul] at h3
  rw [r4, map_mul] at h4
  have hU : 0 < normSq u := normSq_pos.2 hu
  simp only [normSq_apply, sub_re, sub_im, one_re, one_im, add_re, add_im, neg_re,
    neg_im] at h1 h2 h3 h4
  set U := u.re * u.re + u.im * u.im
  have hU' : 0 < U := by simpa [normSq_apply] using hU
  have hbre : ζb.re = 0 := by
    have : 4 * ζb.re * U = 0 := by linear_combination h2 - h1
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  have hdre : ζd.re = 0 := by
    have : 4 * ζd.re * U = 0 := by linear_combination h3 - h4
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  have hsq : ζb.im ^ 2 = ζd.im ^ 2 := by
    rw [hbre] at h1; rw [hdre] at h4
    have : (ζb.im ^ 2 - ζd.im ^ 2) * U = 0 := by linear_combination h1 - h4
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  have hne : ζb.im ≠ ζd.im := by
    intro h; apply hbd; rw [eb, ed]; congr 2; exact Complex.ext (by rw [hbre, hdre]) h
  have hdim : ζd.im = -ζb.im := by
    have : (ζb.im - ζd.im) * (ζb.im + ζd.im) = 0 := by linear_combination hsq
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (by linarith) hne
    · linarith
  refine ⟨ζb.im, fun h => hne (by rw [hdim, h]; simp), ?_, ?_⟩
  · rw [eb]; congr 2; apply Complex.ext <;> simp [hbre]
  · rw [ed]; rw [sub_eq_add_neg, ← neg_mul]; congr 2; apply Complex.ext <;> simp [hdre, hdim]

section Coord

variable (m u : ℂ) (t : ℝ)

def rX (z : ℂ) : ℝ := ((z - m) / u).re

def rY (z : ℂ) : ℝ := ((z - m) / u).im / t

def rN (z : ℂ) : ℝ := |rX m u z| + |rY m u t z|

variable {m u t}

lemma rhomb_decomp (hu : u ≠ 0) (ht : t ≠ 0) (z : ℂ) :
    z = m + (rX m u z : ℂ) * u + (rY m u t z : ℂ) * ((I * t) * u) := by
  have h : (z - m) / u = (rX m u z : ℂ) + (rY m u t z : ℂ) * (I * t) := by
    apply Complex.ext <;> simp [rX, rY, ht]
  have : z - m = ((rX m u z : ℂ) + (rY m u t z : ℂ) * (I * t)) * u := by
    rw [← h]; field_simp
  linear_combination this

lemma rX_comb (hu : u ≠ 0) (x y : ℝ) :
    rX m u (m + (x : ℂ) * u + (y : ℂ) * ((I * t) * u)) = x := by
  simp only [rX]
  have : (m + (x : ℂ) * u + (y : ℂ) * ((I * t) * u) - m) / u = x + y * (I * t) := by
    field_simp; ring
  rw [this]; simp

lemma rY_comb (hu : u ≠ 0) (ht : t ≠ 0) (x y : ℝ) :
    rY m u t (m + (x : ℂ) * u + (y : ℂ) * ((I * t) * u)) = y := by
  simp only [rY]
  have : (m + (x : ℂ) * u + (y : ℂ) * ((I * t) * u) - m) / u = x + y * (I * t) := by
    field_simp; ring
  rw [this]; simp [ht]

lemma continuous_rN : Continuous (rN m u t) := by
  unfold rN rX rY; fun_prop

lemma rX_affine (s r : ℝ) (hsr : s + r = 1) (z w : ℂ) :
    rX m u (s • z + r • w) = s * rX m u z + r * rX m u w := by
  simp only [rX, Complex.real_smul]
  have : ((s : ℂ) * z + (r : ℂ) * w - m) / u = (s : ℂ) * ((z - m) / u) + (r : ℂ) * ((w - m) / u) := by
    have : (m : ℂ) = (s : ℂ) * m + (r : ℂ) * m := by
      rw [← add_mul, ← ofReal_add, hsr, ofReal_one, one_mul]
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    conv_lhs => rw [this]
    ring
  rw [this]; simp

lemma rY_affine (s r : ℝ) (hsr : s + r = 1) (z w : ℂ) :
    rY m u t (s • z + r • w) = s * rY m u t z + r * rY m u t w := by
  simp only [rY, Complex.real_smul]
  have : ((s : ℂ) * z + (r : ℂ) * w - m) / u = (s : ℂ) * ((z - m) / u) + (r : ℂ) * ((w - m) / u) := by
    have : (m : ℂ) = (s : ℂ) * m + (r : ℂ) * m := by
      rw [← add_mul, ← ofReal_add, hsr, ofReal_one, one_mul]
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    conv_lhs => rw [this]
    ring
  rw [this]; simp; ring

end Coord

section Region

variable {m u : ℂ} {t : ℝ}

def rPt (m u : ℂ) (t x y : ℝ) : ℂ := m + (x : ℂ) * u + (y : ℂ) * ((I * t) * u)

lemma rN_rPt (hu : u ≠ 0) (ht : t ≠ 0) (x y : ℝ) : rN m u t (rPt m u t x y) = |x| + |y| := by
  simp only [rN, rPt, rX_comb hu, rY_comb hu ht]

lemma rPt_eq (hu : u ≠ 0) (ht : t ≠ 0) (z : ℂ) : rPt m u t (rX m u z) (rY m u t z) = z :=
  (rhomb_decomp hu ht z).symm

lemma rPt_comb (s r : ℝ) (hsr : s + r = 1) (x y x' y' : ℝ) :
    s • rPt m u t x y + r • rPt m u t x' y' = rPt m u t (s * x + r * x') (s * y + r * y') := by
  simp only [rPt, Complex.real_smul]
  have : (m : ℂ) = (s : ℂ) * m + (r : ℂ) * m := by
    rw [← add_mul, ← ofReal_add, hsr, ofReal_one, one_mul]
  conv_rhs => rw [this]
  push_cast; ring

lemma rN_le_one_convex : Convex ℝ {z : ℂ | rN m u t z ≤ 1} := by
  intro z hz w hw s r hs hr hsr
  simp only [Set.mem_setOf_eq, rN] at hz hw ⊢
  rw [rX_affine s r hsr, rY_affine s r hsr]
  have h1 := abs_add_le (s * rX m u z) (r * rX m u w)
  have h2 := abs_add_le (s * rY m u t z) (r * rY m u t w)
  rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg hr] at h1 h2
  nlinarith

lemma convexHull_rhombus (hu : u ≠ 0) (ht : t ≠ 0) :
    convexHull ℝ ({rPt m u t 1 0, rPt m u t 0 1, rPt m u t (-1) 0, rPt m u t 0 (-1)} : Set ℂ) =
      {z : ℂ | rN m u t z ≤ 1} := by
  apply le_antisymm
  · refine convexHull_min ?_ rN_le_one_convex
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> simp [rN_rPt hu ht]
  · intro z hz
    simp only [Set.mem_setOf_eq] at hz
    set x := rX m u z
    set y := rY m u t z
    have hz' : |x| + |y| ≤ 1 := hz
    set q := (1 - |x| - |y|) / 4
    have hq : 0 ≤ q := by simp only [q]; linarith
    set w : Fin 4 → ℝ := ![max x 0 + q, max y 0 + q, max (-x) 0 + q, max (-y) 0 + q]
    set p : Fin 4 → ℂ := ![rPt m u t 1 0, rPt m u t 0 1, rPt m u t (-1) 0, rPt m u t 0 (-1)]
    have hw0 : ∀ i ∈ Finset.univ, 0 ≤ w i := by
      intro i _
      fin_cases i <;> simp [w] <;> positivity
    have hax : max x 0 - max (-x) 0 = x := by
      rcases le_total 0 x with h | h
      · rw [max_eq_left h, max_eq_right (by linarith)]; ring
      · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    have hay : max y 0 - max (-y) 0 = y := by
      rcases le_total 0 y with h | h
      · rw [max_eq_left h, max_eq_right (by linarith)]; ring
      · rw [max_eq_right h, max_eq_left (by linarith)]; ring
    have habs : ∀ v : ℝ, max v 0 + max (-v) 0 = |v| := by
      intro v
      rcases le_total 0 v with h | h
      · rw [max_eq_left h, max_eq_right (by linarith), abs_of_nonneg h]; ring
      · rw [max_eq_right h, max_eq_left (by linarith), abs_of_nonpos h]; ring
    have hw1 : ∑ i ∈ Finset.univ, w i = 1 := by
      simp only [w, Fin.sum_univ_four]
      simp
      have := habs x; have := habs y
      simp only [q]; linarith
    have hp : ∀ i ∈ Finset.univ, p i ∈
        ({rPt m u t 1 0, rPt m u t 0 1, rPt m u t (-1) 0, rPt m u t 0 (-1)} : Set ℂ) := by
      intro i _
      fin_cases i <;> simp [p]
    have hmem := (convex_convexHull ℝ _).sum_mem hw0 hw1 (fun i hi => subset_convexHull ℝ _ (hp i hi))
    convert hmem using 1
    rw [← rPt_eq hu ht z]
    simp only [w, p, Fin.sum_univ_four, rPt, Complex.real_smul]
    simp
    have e1 : (x : ℂ) = ((max x 0 : ℝ) : ℂ) - ((max (-x) 0 : ℝ) : ℂ) := by
      rw [← ofReal_sub, hax]
    have e2 : (y : ℂ) = ((max y 0 : ℝ) : ℂ) - ((max (-y) 0 : ℝ) : ℂ) := by
      rw [← ofReal_sub, hay]
    have e3 : ((max x 0 : ℝ) : ℂ) + ((max y 0 : ℝ) : ℂ) + ((max (-x) 0 : ℝ) : ℂ) +
        ((max (-y) 0 : ℝ) : ℂ) + 4 * (q : ℂ) = 1 := by
      have := habs x; have := habs y
      have h4 : max x 0 + max y 0 + max (-x) 0 + max (-y) 0 + 4 * q = 1 := by
        simp only [q]; linarith
      exact_mod_cast h4
    rw [e1, e2]
    linear_combination (-m) * e3

lemma rX_scale (s : ℝ) (z : ℂ) : rX m u (m + (s : ℂ) * (z - m)) = s * rX m u z := by
  simp only [rX]
  rw [show m + (s : ℂ) * (z - m) - m = (s : ℂ) * (z - m) by ring, mul_div_assoc]
  simp

lemma rY_scale (s : ℝ) (z : ℂ) : rY m u t (m + (s : ℂ) * (z - m)) = s * rY m u t z := by
  simp only [rY]
  rw [show m + (s : ℂ) * (z - m) - m = (s : ℂ) * (z - m) by ring, mul_div_assoc]
  simp; ring

lemma rN_scale (s : ℝ) (z : ℂ) : rN m u t (m + (s : ℂ) * (z - m)) = |s| * rN m u t z := by
  simp only [rN, rX_scale, rY_scale, abs_mul]; ring

lemma interior_rN_le :
    interior {z : ℂ | rN m u t z ≤ 1} = {z : ℂ | rN m u t z < 1} := by
  apply le_antisymm
  · intro z hz
    simp only [Set.mem_setOf_eq]
    by_contra hge
    push_neg at hge
    have hc : Continuous fun ε : ℝ => m + ((1 + ε : ℝ) : ℂ) * (z - m) := by fun_prop
    have h0 : m + ((1 + (0 : ℝ) : ℝ) : ℂ) * (z - m) = z := by push_cast; ring
    have hz' : m + ((1 + (0 : ℝ) : ℝ) : ℂ) * (z - m) ∈ interior {z : ℂ | rN m u t z ≤ 1} := by
      rw [h0]; exact hz
    have hev := (hc.tendsto 0).eventually (mem_interior_iff_mem_nhds.1 hz')
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
    have hmem := hball (y := δ / 2) (by rw [Real.dist_eq]; rw [abs_of_pos (by linarith)]; linarith)
    simp only [rN_scale] at hmem
    rw [abs_of_pos (by linarith)] at hmem
    nlinarith
  · exact interior_maximal (fun z (hz : rN m u t z < 1) => (hz.le : rN m u t z ≤ 1))
      (isOpen_lt continuous_rN continuous_const)

lemma closure_rN_lt :
    closure {z : ℂ | rN m u t z < 1} = {z : ℂ | rN m u t z ≤ 1} := by
  apply le_antisymm
  · exact closure_minimal (fun z (hz : rN m u t z < 1) => (hz.le : rN m u t z ≤ 1))
      (isClosed_le continuous_rN continuous_const)
  · intro z hz
    simp only [Set.mem_setOf_eq] at hz
    have hc : Continuous fun s : ℝ => m + (s : ℂ) * (z - m) := by fun_prop
    have ht : Filter.Tendsto (fun s : ℝ => m + (s : ℂ) * (z - m)) (nhdsWithin 1 (Set.Iio 1))
        (nhds z) := by
      have := hc.tendsto 1
      simp only [ofReal_one, one_mul, add_sub_cancel] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    refine mem_closure_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsLT (show (-1 : ℝ) < 1 by norm_num)] with s hs
    simp only [rN_scale]
    have : |s| < 1 := abs_lt.2 ⟨hs.1, hs.2⟩
    have h0 : 0 ≤ rN m u t z := by unfold rN; positivity
    nlinarith [abs_nonneg s]

lemma rN_side (hu : u ≠ 0) (ht : t ≠ 0) {x y x' y' : ℝ} (hxy : |x| + |y| = 1)
    (hxy' : |x'| + |y'| = 1) (hs : 0 ≤ x * x') (hs' : 0 ≤ y * y') {z : ℂ}
    (hz : z ∈ segment ℝ (rPt m u t x y) (rPt m u t x' y')) : rN m u t z = 1 := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  rw [rPt_comb a b hab, rN_rPt hu ht]
  have e1 : |a * x + b * x'| = a * |x| + b * |x'| := by
    rcases le_total 0 x with h | h
    · have : 0 ≤ x' ∨ x = 0 := by
        rcases eq_or_lt_of_le h with h0 | h0
        · exact Or.inr h0.symm
        · exact Or.inl (nonneg_of_mul_nonneg_right hs h0)
      rcases this with h' | h0
      · rw [abs_of_nonneg h, abs_of_nonneg h', abs_of_nonneg (by positivity)]
      · subst h0; simp [abs_mul, abs_of_nonneg hb]
    · have : x' ≤ 0 ∨ x = 0 := by
        rcases eq_or_lt_of_le h with h0 | h0
        · exact Or.inr h0
        · left; nlinarith
      rcases this with h' | h0
      · rw [abs_of_nonpos h, abs_of_nonpos h', abs_of_nonpos (by nlinarith)]; ring
      · subst h0; simp [abs_mul, abs_of_nonneg hb]
  have e2 : |a * y + b * y'| = a * |y| + b * |y'| := by
    rcases le_total 0 y with h | h
    · have : 0 ≤ y' ∨ y = 0 := by
        rcases eq_or_lt_of_le h with h0 | h0
        · exact Or.inr h0.symm
        · exact Or.inl (nonneg_of_mul_nonneg_right hs' h0)
      rcases this with h' | h0
      · rw [abs_of_nonneg h, abs_of_nonneg h', abs_of_nonneg (by positivity)]
      · subst h0; simp [abs_mul, abs_of_nonneg hb]
    · have : y' ≤ 0 ∨ y = 0 := by
        rcases eq_or_lt_of_le h with h0 | h0
        · exact Or.inr h0
        · left; nlinarith
      rcases this with h' | h0
      · rw [abs_of_nonpos h, abs_of_nonpos h', abs_of_nonpos (by nlinarith)]; ring
      · subst h0; simp [abs_mul, abs_of_nonneg hb]
  rw [e1, e2]
  linear_combination a * hxy + b * hxy' + hab

lemma mem_side_of_rN_eq (hu : u ≠ 0) (ht : t ≠ 0) {z : ℂ} (hz : rN m u t z = 1) :
    z ∈ segment ℝ (rPt m u t 1 0) (rPt m u t 0 1) ∨ z ∈ segment ℝ (rPt m u t 0 1) (rPt m u t (-1) 0) ∨
      z ∈ segment ℝ (rPt m u t (-1) 0) (rPt m u t 0 (-1)) ∨
        z ∈ segment ℝ (rPt m u t 0 (-1)) (rPt m u t 1 0) := by
  rw [← rPt_eq hu ht z]
  set x := rX m u z
  set y := rY m u t z
  have h : |x| + |y| = 1 := hz
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy
  · left
    rw [abs_of_nonneg hx, abs_of_nonneg hy] at h
    refine ⟨x, y, hx, hy, h, ?_⟩
    rw [rPt_comb x y h]; congr 1 <;> ring
  · right; right; right
    rw [abs_of_nonneg hx, abs_of_nonpos hy] at h
    refine ⟨-y, x, by linarith, hx, by linarith, ?_⟩
    rw [rPt_comb (-y) x (by linarith)]; congr 1 <;> ring
  · right; left
    rw [abs_of_nonpos hx, abs_of_nonneg hy] at h
    refine ⟨y, -x, hy, by linarith, by linarith, ?_⟩
    rw [rPt_comb y (-x) (by linarith)]; congr 1 <;> ring
  · right; right; left
    rw [abs_of_nonpos hx, abs_of_nonpos hy] at h
    refine ⟨-x, -y, by linarith, by linarith, by linarith, ?_⟩
    rw [rPt_comb (-x) (-y) (by linarith)]; congr 1 <;> ring

lemma dist_rPt_sq (x y x' y' : ℝ) :
    dist (rPt m u t x y) (rPt m u t x' y') ^ 2 = normSq u * ((x - x') ^ 2 + t ^ 2 * (y - y') ^ 2) := by
  rw [dist_eq, ← normSq_eq_norm_sq]
  have : rPt m u t x y - rPt m u t x' y' = (((x - x' : ℝ) : ℂ) + ((t * (y - y') : ℝ) : ℂ) * I) * u := by
    simp only [rPt]; push_cast; ring
  rw [this, map_mul, normSq_add_mul_I]; ring

lemma exists_vertex_near (hu : u ≠ 0) (ht : t ≠ 0) (hunit : normSq u * (1 + t ^ 2) = 1) {z : ℂ}
    (hz : rN m u t z ≤ 1) :
    ∃ v ∈ ({rPt m u t 1 0, rPt m u t 0 1, rPt m u t (-1) 0, rPt m u t 0 (-1)} : Set ℂ),
      dist z v < 1 := by
  rw [← rPt_eq hu ht z]
  set x := rX m u z
  set y := rY m u t z
  have h : |x| + |y| ≤ 1 := hz
  have hU : 0 < normSq u := normSq_pos.2 hu
  set σ : ℝ := if 0 ≤ x then 1 else -1
  set τ : ℝ := if 0 ≤ y then 1 else -1
  have hσ : (x - σ) ^ 2 = (|x| - 1) ^ 2 := by
    simp only [σ]; split_ifs with hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_neg (not_le.1 hx)]; ring
  have hτ : (y - τ) ^ 2 = (|y| - 1) ^ 2 := by
    simp only [τ]; split_ifs with hy
    · rw [abs_of_nonneg hy]
    · rw [abs_of_neg (not_le.1 hy)]; ring
  have d1 := dist_rPt_sq (m := m) (u := u) (t := t) x y σ 0
  have d2 := dist_rPt_sq (m := m) (u := u) (t := t) x y 0 τ
  rw [hσ] at d1; rw [hτ] at d2
  have hx1 : |x| ≤ 1 := by linarith [abs_nonneg y]
  have hy1 : |y| ≤ 1 := by linarith [abs_nonneg x]
  have hsum : dist (rPt m u t x y) (rPt m u t σ 0) ^ 2 + dist (rPt m u t x y) (rPt m u t 0 τ) ^ 2
      ≤ 1 := by
    rw [d1, d2]
    have a1 : (|x| - 1) ^ 2 + x ^ 2 ≤ 1 := by
      rw [← sq_abs x]; nlinarith [abs_nonneg x]
    have a2 : y ^ 2 + (|y| - 1) ^ 2 ≤ 1 := by
      rw [← sq_abs y]; nlinarith [abs_nonneg y]
    have : normSq u * ((|x| - 1) ^ 2 + t ^ 2 * (y - 0) ^ 2) +
        normSq u * ((x - 0) ^ 2 + t ^ 2 * (|y| - 1) ^ 2) =
        normSq u * (((|x| - 1) ^ 2 + x ^ 2) + t ^ 2 * (y ^ 2 + (|y| - 1) ^ 2)) := by ring
    rw [this]
    calc _ ≤ normSq u * (1 + t ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ hU.le
          nlinarith [mul_le_mul_of_nonneg_left a2 (sq_nonneg t)]
      _ = 1 := hunit
  have hσm : rPt m u t σ 0 ∈ ({rPt m u t 1 0, rPt m u t 0 1, rPt m u t (-1) 0,
      rPt m u t 0 (-1)} : Set ℂ) := by
    simp only [σ]; split_ifs <;> simp
  have hτm : rPt m u t 0 τ ∈ ({rPt m u t 1 0, rPt m u t 0 1, rPt m u t (-1) 0,
      rPt m u t 0 (-1)} : Set ℂ) := by
    simp only [τ]; split_ifs <;> simp
  by_contra hno
  push_neg at hno
  have e1 := hno _ hσm
  have e2 := hno _ hτm
  have s1 : 1 ≤ dist (rPt m u t x y) (rPt m u t σ 0) ^ 2 := by nlinarith
  have s2 : 1 ≤ dist (rPt m u t x y) (rPt m u t 0 τ) ^ 2 := by nlinarith
  linarith

end Region

section RhombusFace

variable {m u : ℂ} {t : ℝ}

def rVerts (m u : ℂ) (t : ℝ) : Finset ℂ :=
  {rPt m u t 1 0, rPt m u t 0 1, rPt m u t (-1) 0, rPt m u t 0 (-1)}

def rSides (m u : ℂ) (t : ℝ) : Finset (Sym2 ℂ) :=
  {s(rPt m u t 1 0, rPt m u t 0 1), s(rPt m u t 0 1, rPt m u t (-1) 0),
    s(rPt m u t (-1) 0, rPt m u t 0 (-1)), s(rPt m u t 0 (-1), rPt m u t 1 0)}

lemma rN_of_mem_rSides (hu : u ≠ 0) (ht : t ≠ 0) {σ : Sym2 ℂ} (hσ : σ ∈ rSides m u t) {z : ℂ}
    (hz : z ∈ edgeSeg σ) : rN m u t z = 1 := by
  simp only [rSides, Finset.mem_insert, Finset.mem_singleton] at hσ
  rcases hσ with rfl | rfl | rfl | rfl <;> rw [edgeSeg_mk] at hz <;>
    exact rN_side hu ht (by simp) (by simp) (by norm_num) (by norm_num) hz

lemma rN_of_mem_rVerts (hu : u ≠ 0) (ht : t ≠ 0) {v : ℂ} (hv : v ∈ rVerts m u t) :
    rN m u t v = 1 := by
  simp only [rVerts, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl <;> simp [rN_rPt hu ht]

lemma mem_rVerts_of_mem_rSides {σ : Sym2 ℂ} (hσ : σ ∈ rSides m u t) {w : ℂ} (hw : w ∈ σ) :
    w ∈ rVerts m u t := by
  simp only [rSides, Finset.mem_insert, Finset.mem_singleton] at hσ
  rcases hσ with rfl | rfl | rfl | rfl <;> rcases Sym2.mem_iff.1 hw with rfl | rfl <;>
    simp [rVerts]

lemma exists_side_of_rN_eq (hu : u ≠ 0) (ht : t ≠ 0) {z : ℂ} (hz : rN m u t z = 1) :
    ∃ σ ∈ rSides m u t, z ∈ edgeSeg σ := by
  rcases mem_side_of_rN_eq hu ht hz with h | h | h | h
  · exact ⟨s(rPt m u t 1 0, rPt m u t 0 1), by simp [rSides], by rw [edgeSeg_mk]; exact h⟩
  · exact ⟨s(rPt m u t 0 1, rPt m u t (-1) 0), by simp [rSides], by rw [edgeSeg_mk]; exact h⟩
  · exact ⟨s(rPt m u t (-1) 0, rPt m u t 0 (-1)), by simp [rSides], by rw [edgeSeg_mk]; exact h⟩
  · exact ⟨s(rPt m u t 0 (-1), rPt m u t 1 0), by simp [rSides], by rw [edgeSeg_mk]; exact h⟩

lemma dist_rPt_eq_one (hunit : normSq u * (1 + t ^ 2) = 1) {x y x' y' : ℝ}
    (h : (x - x') ^ 2 + t ^ 2 * (y - y') ^ 2 = 1 + t ^ 2) :
    dist (rPt m u t x y) (rPt m u t x' y') = 1 := by
  have e := dist_rPt_sq (m := m) (u := u) (t := t) x y x' y'
  rw [h, hunit] at e
  have := dist_nonneg (x := rPt m u t x y) (y := rPt m u t x' y')
  nlinarith

lemma rSides_subset (hunit : normSq u * (1 + t ^ 2) = 1) {V : Finset ℂ}
    (hV : rVerts m u t ⊆ V) : rSides m u t ⊆ unitPairs V := by
  have mem : ∀ v ∈ rVerts m u t, v ∈ V := fun v hv => hV hv
  intro σ hσ
  simp only [rSides, Finset.mem_insert, Finset.mem_singleton] at hσ
  rcases hσ with rfl | rfl | rfl | rfl <;> rw [mem_unitPairs] <;>
    refine ⟨mem _ (by simp [rVerts]), mem _ (by simp [rVerts]), dist_rPt_eq_one hunit (by ring)⟩

lemma side_of_unit_vertices (hdiag1 : dist (rPt m u t 1 0) (rPt m u t (-1) 0) ≠ 1)
    (hdiag2 : dist (rPt m u t 0 1) (rPt m u t 0 (-1)) ≠ 1) {p q : ℂ} (hp : p ∈ rVerts m u t)
    (hq : q ∈ rVerts m u t) (hpq : dist p q = 1) : s(p, q) ∈ rSides m u t := by
  have hdiag1' := hdiag1; rw [dist_comm] at hdiag1'
  have hdiag2' := hdiag2; rw [dist_comm] at hdiag2'
  simp only [rVerts, Finset.mem_insert, Finset.mem_singleton] at hp hq
  rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;>
    first
    | (simp at hpq)
    | exact absurd hpq hdiag1
    | exact absurd hpq hdiag1'
    | exact absurd hpq hdiag2
    | exact absurd hpq hdiag2'
    | simp [rSides, Sym2.eq_swap]

variable {V : Finset ℂ}

lemma rhomb_no_vertex (hsep : ∀ x ∈ V, ∀ y ∈ V, x ≠ y → 1 ≤ dist x y) (hu : u ≠ 0) (ht : t ≠ 0)
    (hunit : normSq u * (1 + t ^ 2) = 1) (hV : rVerts m u t ⊆ V) {z : ℂ} (hz : z ∈ V) :
    ¬ rN m u t z < 1 := by
  intro hlt
  obtain ⟨v, hv, hd⟩ := exists_vertex_near hu ht hunit hlt.le
  have hv' : v ∈ rVerts m u t := by simpa [rVerts] using hv
  have hne : z ≠ v := by
    rintro rfl; rw [rN_of_mem_rVerts hu ht hv'] at hlt; exact lt_irrefl _ hlt
  exact absurd (hsep z hz v (hV hv') hne) (not_le.2 hd)

lemma eq_of_lineMap_eq {p q : ℂ} (hpq : p ≠ q) {θ : ℝ} (h : p + θ • (q - p) = q) : θ = 1 := by
  have h1 : ((1 - θ : ℝ) : ℂ) * (q - p) = 0 := by
    rw [Complex.real_smul] at h; push_cast; linear_combination -h
  rcases mul_eq_zero.1 h1 with h2 | h2
  · have := ofReal_eq_zero.1 h2; linarith
  · exact absurd (sub_eq_zero.1 h2).symm hpq

lemma eq_zero_of_lineMap_eq {p q : ℂ} (hpq : p ≠ q) {θ : ℝ} (h : p + θ • (q - p) = p) : θ = 0 := by
  have h1 : ((θ : ℝ) : ℂ) * (q - p) = 0 := by
    rw [Complex.real_smul] at h; linear_combination h
  rcases mul_eq_zero.1 h1 with h2 | h2
  · exact ofReal_eq_zero.1 h2
  · exact absurd (sub_eq_zero.1 h2).symm hpq

lemma rhomb_no_edge (hP : IsPlaneGraph V (unitPairs V))
    (hsep : ∀ x ∈ V, ∀ y ∈ V, x ≠ y → 1 ≤ dist x y) (hu : u ≠ 0) (ht : t ≠ 0)
    (hunit : normSq u * (1 + t ^ 2) = 1) (hV : rVerts m u t ⊆ V)
    (hdiag1 : dist (rPt m u t 1 0) (rPt m u t (-1) 0) ≠ 1)
    (hdiag2 : dist (rPt m u t 0 1) (rPt m u t 0 (-1)) ≠ 1)
    {e : Sym2 ℂ} (he : e ∈ unitPairs V) {z : ℂ} (hz : z ∈ edgeSeg e) : ¬ rN m u t z < 1 := by
  induction e using Sym2.ind with
  | _ p q =>
  obtain ⟨hp, hq, hpq1⟩ := mem_unitPairs.1 he
  have hpq : p ≠ q := by rintro rfl; simp at hpq1
  intro hlt
  by_cases hside : s(p, q) ∈ rSides m u t
  · rw [rN_of_mem_rSides hu ht hside hz] at hlt; exact lt_irrefl _ hlt
  have hseg : ∀ θ ∈ Set.Icc (0 : ℝ) 1, p + θ • (q - p) ∈ edgeSeg s(p, q) := by
    intro θ hθ
    rw [edgeSeg_mk, segment_eq_image']
    exact ⟨θ, hθ, rfl⟩
  rw [edgeSeg_mk, segment_eq_image'] at hz
  obtain ⟨l, ⟨hl0, hl1⟩, rfl⟩ := hz
  set g : ℝ → ℝ := fun θ => rN m u t (p + θ • (q - p)) with hgdef
  have hg : Continuous g := continuous_rN.comp (by fun_prop)
  have g0 : 1 ≤ g 0 := by
    simp only [hgdef, zero_smul, add_zero]
    exact not_lt.1 (rhomb_no_vertex hsep hu ht hunit hV hp)
  have g1 : 1 ≤ g 1 := by
    simp only [hgdef, one_smul, add_sub_cancel]
    exact not_lt.1 (rhomb_no_vertex hsep hu ht hunit hV hq)
  have glt : g l < 1 := hlt
  obtain ⟨θ1, ⟨h10, h1l⟩, hg1⟩ := intermediate_value_Icc' hl0 hg.continuousOn ⟨glt.le, g0⟩
  obtain ⟨θ2, ⟨h2l, h21⟩, hg2⟩ := intermediate_value_Icc hl1 hg.continuousOn ⟨glt.le, g1⟩
  have h1l' : θ1 < l := lt_of_le_of_ne h1l (by rintro rfl; rw [hg1] at glt; exact lt_irrefl _ glt)
  have h2l' : l < θ2 := lt_of_le_of_ne h2l (by rintro rfl; rw [hg2] at glt; exact lt_irrefl _ glt)

  have key : ∀ θ ∈ Set.Icc (0 : ℝ) 1, g θ = 1 →
      (p + θ • (q - p) = p ∨ p + θ • (q - p) = q) ∧ p + θ • (q - p) ∈ rVerts m u t := by
    intro θ hθ hgθ
    obtain ⟨σ, hσ, hsσ⟩ := exists_side_of_rN_eq hu ht hgθ
    have hσE := rSides_subset hunit hV hσ
    have hne : s(p, q) ≠ σ := fun h => hside (h ▸ hσ)
    have h1 := hP.inter _ he _ hσE hne _ (hseg θ hθ) hsσ
    have h2 := hP.inter _ hσE _ he hne.symm _ hsσ (hseg θ hθ)
    exact ⟨Sym2.mem_iff.1 h1, mem_rVerts_of_mem_rSides hσ h2⟩
  obtain ⟨k1, v1⟩ := key θ1 ⟨h10, by linarith⟩ hg1
  obtain ⟨k2, v2⟩ := key θ2 ⟨by linarith, h21⟩ hg2
  have e1 : p + θ1 • (q - p) = p := by
    rcases k1 with h | h
    · exact h
    · have := eq_of_lineMap_eq hpq h; linarith
  have e2 : p + θ2 • (q - p) = q := by
    rcases k2 with h | h
    · have := eq_zero_of_lineMap_eq hpq h; linarith
    · exact h
  rw [e1] at v1; rw [e2] at v2
  exact hside (side_of_unit_vertices hdiag1 hdiag2 v1 v2 hpq1)

lemma rhomb_not_mem_drawing (hP : IsPlaneGraph V (unitPairs V))
    (hsep : ∀ x ∈ V, ∀ y ∈ V, x ≠ y → 1 ≤ dist x y) (hu : u ≠ 0) (ht : t ≠ 0)
    (hunit : normSq u * (1 + t ^ 2) = 1) (hV : rVerts m u t ⊆ V)
    (hdiag1 : dist (rPt m u t 1 0) (rPt m u t (-1) 0) ≠ 1)
    (hdiag2 : dist (rPt m u t 0 1) (rPt m u t 0 (-1)) ≠ 1) {z : ℂ} (hz : rN m u t z < 1) :
    z ∉ drawing V (unitPairs V) := by
  rintro (hzV | hzE)
  · exact rhomb_no_vertex hsep hu ht hunit hV hzV hz
  · obtain ⟨e, he, hze⟩ := Set.mem_iUnion₂.1 hzE
    exact rhomb_no_edge hP hsep hu ht hunit hV hdiag1 hdiag2 he hze hz

lemma rhomb_side_mem_drawing (hu : u ≠ 0) (ht : t ≠ 0) (hunit : normSq u * (1 + t ^ 2) = 1)
    (hV : rVerts m u t ⊆ V) {z : ℂ} (hz : rN m u t z = 1) : z ∈ drawing V (unitPairs V) := by
  obtain ⟨σ, hσ, hzσ⟩ := exists_side_of_rN_eq hu ht hz
  exact Or.inr (Set.mem_iUnion₂.2 ⟨σ, rSides_subset hunit hV hσ, hzσ⟩)

lemma rhomb_mem_faces (hP : IsPlaneGraph V (unitPairs V))
    (hsep : ∀ x ∈ V, ∀ y ∈ V, x ≠ y → 1 ≤ dist x y) (hu : u ≠ 0) (ht : t ≠ 0)
    (hunit : normSq u * (1 + t ^ 2) = 1) (hV : rVerts m u t ⊆ V)
    (hdiag1 : dist (rPt m u t 1 0) (rPt m u t (-1) 0) ≠ 1)
    (hdiag2 : dist (rPt m u t 0 1) (rPt m u t 0 (-1)) ≠ 1) :
    {z : ℂ | rN m u t z < 1} ∈ faces V (unitPairs V) := by
  set G := {z : ℂ | rN m u t z < 1}
  have hmG : m ∈ G := by
    show rN m u t m < 1
    have := rN_scale (m := m) (u := u) (t := t) 0 m
    simp only [ofReal_zero, zero_mul, add_zero, abs_zero] at this
    rw [this]; norm_num
  have hGD : G ⊆ (drawing V (unitPairs V))ᶜ := fun z hz =>
    rhomb_not_mem_drawing hP hsep hu ht hunit hV hdiag1 hdiag2 hz
  rw [mem_faces_iff]
  refine ⟨m, hGD hmG, le_antisymm ?_ ?_⟩
  · have hconv : Convex ℝ G := by
      have := (rN_le_one_convex (m := m) (u := u) (t := t)).interior
      rwa [interior_rN_le] at this
    exact hconv.isPreconnected.subset_connectedComponentIn hmG hGD
  · have hO1 : IsOpen {z : ℂ | rN m u t z < 1} := isOpen_lt continuous_rN continuous_const
    have hO2 : IsOpen {z : ℂ | 1 < rN m u t z} := isOpen_lt continuous_const continuous_rN
    refine isPreconnected_connectedComponentIn.subset_left_of_subset_union hO1 hO2 ?_ ?_ ⟨m, mem_connectedComponentIn (hGD hmG), hmG⟩
    · rw [Set.disjoint_left]
      intro z (h1 : rN m u t z < 1) (h2 : 1 < rN m u t z)
      linarith
    · intro z hz
      have hzD := connectedComponentIn_subset _ _ hz
      rcases lt_trichotomy (rN m u t z) 1 with h | h | h
      · exact Or.inl h
      · exact absurd (rhomb_side_mem_drawing hu ht hunit hV h) hzD
      · exact Or.inr h

lemma rhomb_bdryEdges (hP : IsPlaneGraph V (unitPairs V))
    (hsep : ∀ x ∈ V, ∀ y ∈ V, x ≠ y → 1 ≤ dist x y) (hu : u ≠ 0) (ht : t ≠ 0)
    (hunit : normSq u * (1 + t ^ 2) = 1) (hV : rVerts m u t ⊆ V)
    (hdiag1 : dist (rPt m u t 1 0) (rPt m u t (-1) 0) ≠ 1)
    (hdiag2 : dist (rPt m u t 0 1) (rPt m u t 0 (-1)) ≠ 1) :
    bdryEdges (unitPairs V) {z : ℂ | rN m u t z < 1} = rSides m u t := by
  ext σ
  simp only [bdryEdges, Finset.mem_filter, closure_rN_lt]
  constructor
  · rintro ⟨hσE, z, hzo, hzc⟩
    have hzs : z ∈ edgeSeg σ := by
      induction σ using Sym2.ind with
      | _ p q => exact openSegment_subset_segment ℝ p q hzo
    have hz1 : rN m u t z = 1 := by
      rcases lt_or_eq_of_le (show rN m u t z ≤ 1 from hzc) with h | h
      · exact absurd h (rhomb_no_edge hP hsep hu ht hunit hV hdiag1 hdiag2 hσE hzs)
      · exact h
    obtain ⟨σ', hσ', hzσ'⟩ := exists_side_of_rN_eq hu ht hz1
    by_contra hne
    have hne' : σ ≠ σ' := fun h => hne (h ▸ hσ')
    have hzσ := hP.inter _ hσE _ (rSides_subset hunit hV hσ') hne' _ hzs hzσ'
    induction σ using Sym2.ind with
    | _ p q =>
    have hpq : p ≠ q := by
      rintro rfl; exact (mem_unitPairs.1 hσE).2.2 |> fun h => by simp at h
    rcases Sym2.mem_iff.1 hzσ with rfl | rfl
    · exact hpq (left_mem_openSegment_iff.1 hzo)
    · exact hpq (right_mem_openSegment_iff.1 hzo)
  · intro hσ
    refine ⟨rSides_subset hunit hV hσ, ?_⟩
    induction σ using Sym2.ind with
    | _ p q =>
    refine ⟨(1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q, ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num,
      rfl⟩, ?_⟩
    show rN m u t _ ≤ 1
    rw [rN_of_mem_rSides hu ht hσ (by rw [edgeSeg_mk]; exact ⟨1 / 2, 1 / 2, by norm_num,
      by norm_num, by norm_num, rfl⟩)]

end RhombusFace

lemma exists_rPt_of_cycle {a b c d : ℂ} (hab : dist a b = 1) (hbc : dist b c = 1)
    (hcd : dist c d = 1) (hda : dist d a = 1) (hac : a ≠ c) (hbd : b ≠ d) :
    ∃ m u : ℂ, ∃ t : ℝ, u ≠ 0 ∧ t ≠ 0 ∧ normSq u * (1 + t ^ 2) = 1 ∧
      a = rPt m u t 1 0 ∧ b = rPt m u t 0 1 ∧ c = rPt m u t (-1) 0 ∧ d = rPt m u t 0 (-1) := by
  obtain ⟨t, ht, hb, hd⟩ := rhombus_normal hab hbc hcd hda hac hbd
  have hu : (a - c) / 2 ≠ 0 := by
    intro h; apply hac; have : a - c = 0 := by linear_combination 2 * h
    exact sub_eq_zero.1 this
  have ea : a = rPt ((a + c) / 2) ((a - c) / 2) t 1 0 := by simp [rPt]; ring
  have eb : b = rPt ((a + c) / 2) ((a - c) / 2) t 0 1 := by rw [hb]; simp [rPt]
  have ec : c = rPt ((a + c) / 2) ((a - c) / 2) t (-1) 0 := by simp [rPt]; ring
  have ed : d = rPt ((a + c) / 2) ((a - c) / 2) t 0 (-1) := by rw [hd]; simp [rPt]; ring
  refine ⟨(a + c) / 2, (a - c) / 2, t, hu, ht, ?_, ea, eb, ec, ed⟩
  have h := dist_rPt_sq (m := (a + c) / 2) (u := (a - c) / 2) (t := t) 1 0 0 1
  rw [← ea, ← eb, hab] at h
  linarith

lemma isCompact_drawing (V : Finset ℂ) (E : Finset (Sym2 ℂ)) : IsCompact (drawing V E) := by
  refine V.finite_toSet.isCompact.union (E.finite_toSet.isCompact_biUnion fun e _ => ?_)
  induction e using Sym2.ind with
  | _ a b => rw [edgeSeg_mk, segment_eq_image]; exact isCompact_Icc.image (by fun_prop)

lemma exists_not_mem_of_isBounded {S : Set ℂ} (h : Bornology.IsBounded S) : ∃ p, p ∉ S := by
  obtain ⟨r, hr⟩ := h.subset_closedBall 0
  refine ⟨((|r| + 1 : ℝ) : ℂ), fun hp => ?_⟩
  have := hr hp
  rw [Metric.mem_closedBall, dist_zero_right, norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity)] at this
  linarith [le_abs_self r]

theorem unit_rhombus_face {V : Finset ℂ} (hP : IsPlaneGraph V (unitPairs V))
    (hsep : ∀ x ∈ V, ∀ y ∈ V, x ≠ y → 1 ≤ dist x y) {a b c d : ℂ}
    (ha : a ∈ V) (hb : b ∈ V) (hc : c ∈ V) (hd : d ∈ V)
    (hab : dist a b = 1) (hbc : dist b c = 1) (hcd : dist c d = 1) (hda : dist d a = 1)
    (hac : dist a c ≠ 1) (hbd : dist b d ≠ 1) (hac' : a ≠ c) (hbd' : b ≠ d) :
    interior (convexHull ℝ ({a, b, c, d} : Set ℂ)) ∈ faces V (unitPairs V) ∧
      bdryEdges (unitPairs V) (interior (convexHull ℝ ({a, b, c, d} : Set ℂ))) =
        {s(a, b), s(b, c), s(c, d), s(d, a)} ∧
      Bornology.IsBounded (interior (convexHull ℝ ({a, b, c, d} : Set ℂ))) := by
  obtain ⟨m, u, t, hu, ht, hunit, rfl, rfl, rfl, rfl⟩ :=
    exists_rPt_of_cycle hab hbc hcd hda hac' hbd'
  have hV : rVerts m u t ⊆ V := by
    intro v hv
    simp only [rVerts, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> assumption
  have hG : interior (convexHull ℝ ({rPt m u t 1 0, rPt m u t 0 1, rPt m u t (-1) 0,
      rPt m u t 0 (-1)} : Set ℂ)) = {z : ℂ | rN m u t z < 1} := by
    rw [convexHull_rhombus hu ht, interior_rN_le]
  rw [hG]
  refine ⟨rhomb_mem_faces hP hsep hu ht hunit hV hac hbd,
    rhomb_bdryEdges hP hsep hu ht hunit hV hac hbd, ?_⟩
  rw [← interior_rN_le, ← convexHull_rhombus hu ht]
  exact ((Set.toFinite _).isCompact_convexHull (𝕜 := ℝ) |>.isBounded).subset interior_subset

lemma eq_of_bdryEdges_cycle4_bounded {V : Finset ℂ} {E : Finset (Sym2 ℂ)} (hP : IsPlaneGraph V E)
    {f f' : Set ℂ} (hf : f ∈ faces V E) (hf' : f' ∈ faces V E) (hb : Bornology.IsBounded f)
    (hb' : Bornology.IsBounded f') {a b c d : ℂ} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hB : bdryEdges E f = {s(a, b), s(b, c), s(c, d), s(d, a)})
    (hB' : bdryEdges E f' = {s(a, b), s(b, c), s(c, d), s(d, a)}) : f = f' := by
  obtain ⟨p, hp⟩ := exists_not_mem_of_isBounded
    (((isCompact_drawing V E).isBounded.union hb).union hb')
  simp only [Set.mem_union, not_or] at hp
  exact eq_of_bdryEdges_cycle4 hP hf hf' hp.1.1 hp.1.2 hp.2 hab hac had hbc hbd hcd hB hB'

lemma not_forest_bdryEdges_of_bounded {V : Finset ℂ} {E : Finset (Sym2 ℂ)} (hP : IsPlaneGraph V E)
    {f : Set ℂ} (hf : f ∈ faces V E) (hb : Bornology.IsBounded f) : ¬ IsForestE (bdryEdges E f) := by
  obtain ⟨p, hp⟩ := exists_not_mem_of_isBounded ((isCompact_drawing V E).isBounded.union hb)
  simp only [Set.mem_union, not_or] at hp
  exact not_forest_bdryEdges hP hf hp.1 hp.2

section Transport

variable {X : Finset Plane}

lemma mem_cVerts {z : ℂ} : z ∈ cVerts X ↔ toC.symm z ∈ X := by
  unfold cVerts
  rw [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩; simpa using hx
  · intro h; exact ⟨_, h, by simp⟩

lemma cVerts_sep (hX : IsSeparated X) : ∀ x ∈ cVerts X, ∀ y ∈ cVerts X, x ≠ y → 1 ≤ dist x y := by
  intro x' hx' y' hy' hxy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hx'
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hy'
  rw [dist_toC]; exact hX x hx y hy (fun h => hxy (by rw [h]))

lemma cVerts_tri (htri : ¬ HasUnitTriangle X) :
    ∀ x ∈ cVerts X, ∀ y ∈ cVerts X, ∀ z ∈ cVerts X, dist x y = 1 → dist y z = 1 → dist z x ≠ 1 := by
  intro x' hx' y' hy' z' hz' h1 h2 h3
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hx'
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hy'
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hz'
  rw [dist_toC] at h1 h2 h3
  exact htri ⟨x, hx, y, hy, z, hz, h1, h2, by rw [dist_comm]; exact h3⟩

lemma cUnitEdges_isPlaneGraph (hX : IsSeparated X) : IsPlaneGraph (cVerts X) (cUnitEdges X) :=
  isPlaneGraph_unitPairs (cVerts_sep hX)

theorem four_le_faceSize (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X) {F : Set ℂ}
    (hF : F ∈ contactFaces X) : 4 ≤ faceSize X F :=
  (cycle_of_not_forest (Finset.filter_subset _ _) (cVerts_tri htri)
    (not_forest_bdryEdges_of_bounded (cUnitEdges_isPlaneGraph hX) hF.1 hF.2)).1

lemma rhombi_data (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X) {R : Finset Plane}
    (hR : R ∈ rhombi X) : ∃ a b c d : ℂ, toC '' (R : Set Plane) = {a, b, c, d} ∧
      a ∈ cVerts X ∧ b ∈ cVerts X ∧ c ∈ cVerts X ∧ d ∈ cVerts X ∧
      dist a b = 1 ∧ dist b c = 1 ∧ dist c d = 1 ∧ dist d a = 1 ∧ dist a c ≠ 1 ∧ dist b d ≠ 1 ∧
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  obtain ⟨hP, a, b, c, d, rfl, h1, h2, h3, h4⟩ := Finset.mem_filter.1 hR
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.1 hP
  have mem : ∀ x ∈ ({a, b, c, d} : Finset Plane), toC x ∈ cVerts X := fun x hx =>
    Finset.mem_image_of_mem _ (hsub hx)
  have hne : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl <;>
      simp only [Finset.mem_insert, Finset.mem_singleton, true_or, or_true,
        Finset.insert_eq_of_mem] at hcard <;>
      exact absurd hcard (ne_of_lt (lt_of_le_of_lt Finset.card_le_three (by norm_num)))
  obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := hne
  have hdg := rhombus_diagonals_gt_one hX htri hR h1 h2 h3 h4
  refine ⟨toC a, toC b, toC c, toC d, by simp [Set.image_insert_eq], mem _ (by simp),
    mem _ (by simp), mem _ (by simp), mem _ (by simp), by rw [dist_toC]; exact h1,
    by rw [dist_toC]; exact h2, by rw [dist_toC]; exact h3, by rw [dist_toC]; exact h4,
    by rw [dist_toC]; exact hdg.1.ne', by rw [dist_toC]; exact hdg.2.ne',
    fun h => hab (toC.injective h), fun h => hac (toC.injective h),
    fun h => had (toC.injective h), fun h => hbc (toC.injective h),
    fun h => hbd (toC.injective h), fun h => hcd (toC.injective h)⟩

end Transport

lemma card_cycle4 {a b c d : ℂ} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) :
    ({s(a, b), s(b, c), s(c, d), s(d, a)} : Finset (Sym2 ℂ)).card = 4 := by
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair]
  all_goals simp [hab, hac, had, hbc, hbd, hcd, hab.symm, hac.symm, had.symm]

lemma verts_cycle4 (a b c d : ℂ) :
    {v : ℂ | ∃ e ∈ ({s(a, b), s(b, c), s(c, d), s(d, a)} : Finset (Sym2 ℂ)), v ∈ e} =
      ({a, b, c, d} : Set ℂ) := by
  ext v
  simp only [Finset.mem_insert, Finset.mem_singleton, Set.mem_setOf_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨e, he, hv⟩
    rcases he with rfl | rfl | rfl | rfl <;> rcases Sym2.mem_iff.1 hv with rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨_, Or.inl rfl, Sym2.mem_mk_left _ _⟩
    · exact ⟨_, Or.inr (Or.inl rfl), Sym2.mem_mk_left _ _⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inl rfl)), Sym2.mem_mk_left _ _⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inr rfl)), Sym2.mem_mk_left _ _⟩

def cInterior (R : Finset Plane) : Set ℂ := interior (convexHull ℝ (toC '' (R : Set Plane)))

section Transport2

variable {X : Finset Plane}

theorem rhombus_mem_rhombusFaces (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X)
    {R : Finset Plane} (hR : R ∈ rhombi X) :
    cInterior R ∈ rhombusFaces X ∧
      toC '' (R : Set Plane) = {v | ∃ e ∈ bdryEdges (cUnitEdges X) (cInterior R), v ∈ e} := by
  obtain ⟨a, b, c, d, hRabcd, ha, hb, hc, hd, h1, h2, h3, h4, hac1, hbd1, hab, hac, had, hbc, hbd,
    hcd⟩ := rhombi_data hX htri hR
  obtain ⟨hface, hbdry, hbdd⟩ := unit_rhombus_face (cUnitEdges_isPlaneGraph hX) (cVerts_sep hX)
    ha hb hc hd h1 h2 h3 h4 hac1 hbd1 hac hbd
  have e : cInterior R = interior (convexHull ℝ ({a, b, c, d} : Set ℂ)) := by
    rw [cInterior, hRabcd]
  rw [e]
  refine ⟨⟨⟨hface, hbdd⟩, ?_⟩, ?_⟩
  · show (bdryEdges (cUnitEdges X) _).card = 4
    unfold cUnitEdges
    rw [hbdry, card_cycle4 hab hac had hbc hbd hcd]
  · unfold cUnitEdges
    rw [hbdry, verts_cycle4, hRabcd]

theorem mem_rhombusFaces_iff (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X) {F : Set ℂ} :
    F ∈ rhombusFaces X ↔ ∃ R ∈ rhombi X, F = cInterior R := by
  constructor
  · rintro ⟨hF, h4⟩
    have hP := cUnitEdges_isPlaneGraph hX
    obtain ⟨-, hcyc⟩ := cycle_of_not_forest (Finset.filter_subset _ _) (cVerts_tri htri)
      (not_forest_bdryEdges_of_bounded hP hF.1 hF.2)
    obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hB⟩ := hcyc h4
    have hE : ∀ e ∈ ({s(a, b), s(b, c), s(c, d), s(d, a)} : Finset (Sym2 ℂ)),
        e ∈ unitPairs (cVerts X) := by
      intro e he; rw [← hB] at he; exact (Finset.mem_filter.1 he).1
    obtain ⟨ha, hb, h1⟩ := mem_unitPairs.1 (hE s(a, b) (by simp))
    obtain ⟨-, hc, h2⟩ := mem_unitPairs.1 (hE s(b, c) (by simp))
    obtain ⟨-, hd, h3⟩ := mem_unitPairs.1 (hE s(c, d) (by simp))
    obtain ⟨-, -, h4'⟩ := mem_unitPairs.1 (hE s(d, a) (by simp))
    have htr := cVerts_tri htri
    have hac1 : dist a c ≠ 1 := fun h => htr a ha b hb c hc h1 h2 (by rw [dist_comm]; exact h)
    have hbd1 : dist b d ≠ 1 := fun h => htr b hb c hc d hd h2 h3 (by rw [dist_comm]; exact h)
    obtain ⟨hface, hbdry, hbdd⟩ := unit_rhombus_face hP (cVerts_sep hX)
      ha hb hc hd h1 h2 h3 h4' hac1 hbd1 hac hbd
    have hFG := eq_of_bdryEdges_cycle4_bounded hP hF.1 hface hF.2 hbdd hab hac had hbc hbd hcd
      hB hbdry
    set R : Finset Plane := ({a, b, c, d} : Finset ℂ).image toC.symm with hRdef
    have hmem : ∀ z ∈ ({a, b, c, d} : Finset ℂ), toC.symm z ∈ X := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl <;> exact mem_cVerts.1 (by assumption)
    have hRim : toC '' (R : Set Plane) = ({a, b, c, d} : Set ℂ) := by
      rw [hRdef, Finset.coe_image, Set.image_image]
      simp
    refine ⟨R, ?_, by rw [hFG, cInterior, hRim]⟩
    refine Finset.mem_filter.2 ⟨Finset.mem_powersetCard.2 ⟨?_, ?_⟩, toC.symm a, toC.symm b,
      toC.symm c, toC.symm d, by simp [hRdef, Finset.image_insert], ?_, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hx
      exact hmem z hz
    · rw [hRdef, Finset.card_image_of_injective _ toC.symm.injective]
      rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
        Finset.card_insert_of_notMem (by simp [hbc, hbd]), Finset.card_pair hcd]
    all_goals rw [LinearIsometryEquiv.dist_map]; assumption
  · rintro ⟨R, hR, rfl⟩
    exact (rhombus_mem_rhombusFaces hX htri hR).1

theorem ncard_rhombusFaces (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X) :
    (rhombusFaces X).ncard = (rhombi X).card := by
  have himg : rhombusFaces X = cInterior '' ((rhombi X : Finset (Finset Plane)) : Set _) := by
    ext F
    rw [mem_rhombusFaces_iff hX htri]
    simp only [Set.mem_image, Finset.mem_coe]
    exact ⟨fun ⟨R, hR, h⟩ => ⟨R, hR, h.symm⟩, fun ⟨R, hR, h⟩ => ⟨R, hR, h.symm⟩⟩
  rw [himg, Set.InjOn.ncard_image, Set.ncard_coe_finset]
  intro R hR R' hR' h
  have e1 := (rhombus_mem_rhombusFaces hX htri hR).2
  have e2 := (rhombus_mem_rhombusFaces hX htri hR').2
  rw [h, ← e2] at e1
  exact Finset.coe_injective (Set.image_injective.2 toC.injective e1)

theorem faceCount_four (hX : IsSeparated X) (htri : ¬ HasUnitTriangle X) :
    faceCount X 4 = (rhombi X).card :=
  ncard_rhombusFaces hX htri

end Transport2

end Erdos99

end

end RhombusFaces

section TriLattice

open scoped BigOperators Real
open Filter

@[expose] public noncomputable section

open Classical

open MeasureTheory

namespace Erdos99

noncomputable def triVec : Fin 2 → Plane := ![!₂[1, 0], !₂[1/2, √3/2]]

lemma triVec_linIndep : LinearIndependent ℝ triVec := by
  unfold triVec
  rw [LinearIndependent.pair_iff]
  intro s t h
  have h0 := congrArg (fun v : Plane => v 0) h
  have h1 := congrArg (fun v : Plane => v 1) h
  simp at h0 h1
  subst h1; simp at h0; exact ⟨h0, rfl⟩

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

noncomputable abbrev triLattice : Submodule ℤ Plane := Submodule.span ℤ (Set.range triBasis)

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

section TrackCross

open scoped BigOperators Real

@[expose] public noncomputable section

open Classical

namespace Erdos99

def cen (R : Finset Plane) : Plane := (1 / 4 : ℝ) • ∑ x ∈ R, x

lemma RhombusData.cen_eq {X R : Finset Plane} {a b c d : Plane} (h : RhombusData X R a b c d) :
    cen R = (1 / 2 : ℝ) • (mid s(a, b) + mid s(c, d)) := by
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := h.distinct
  rw [cen, h.eq, mid_mk, mid_mk, Finset.sum_insert (by simp [d1, d2, d3]),
    Finset.sum_insert (by simp [d4, d5]), Finset.sum_insert (by simp [d6]), Finset.sum_singleton]
  module

def ConeLe (u Δ : Plane) : Prop := |inner ℝ Δ u| * √3 ≤ inner ℝ Δ (rot u)

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

section Release

open scoped BigOperators Real

@[expose] public noncomputable section

open Classical

namespace Erdos99

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
  ⟨IsometryEquiv.refl _, by change X.image id = X; exact Finset.image_id⟩

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
  have hεy : ∀ y ∈ X, dist x y + ε ≤ D := fun y hy => by have := hmin y hy; dsimp only [ε]; linarith
  set S := X.erase x
  have hSne : S.Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hx, hX.1.1]; omega
  have hinner : ∀ y ∈ X, 0 ≤ inner ℝ (x - y) ν := fun y hy => by
    rw [real_inner_comm, inner_sub_right]; linarith [hν y hy]

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

section Pinned

open scoped BigOperators Real

@[expose] public noncomputable section

open Classical Module

namespace Erdos99

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

lemma exists_dist_eq_diam {X : Finset Plane} (hX : X.Nonempty) :
    ∃ a ∈ X, ∃ b ∈ X, dist a b = diam X := by
  obtain ⟨⟨a, b⟩, hab, hmax⟩ := Finset.exists_max_image (X ×ˢ X) (fun pq => dist pq.1 pq.2)
    (hX.product hX)
  rw [Finset.mem_product] at hab
  refine ⟨a, hab.1, b, hab.2, le_antisymm (dist_le_diam hab.1 hab.2) ?_⟩
  apply Metric.diam_le_of_forall_dist_le dist_nonneg
  intro p hp q hq
  exact hmax (p, q) (Finset.mem_product.2 ⟨hp, hq⟩)

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

section ConeFarkas

open scoped BigOperators

@[expose] public noncomputable section

open Classical

namespace Erdos99.Locking

section Cone

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {κ : Type*}

def coneOf (g : κ → F) (s : Finset κ) : Set F :=
  {x | ∃ c : κ → ℝ, (∀ k, 0 ≤ c k) ∧ x = ∑ k ∈ s, c k • g k}

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

section LockingAbstract

open scoped BigOperators

@[expose] public noncomputable section

open Classical

namespace Erdos99.Locking

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {ι : Type*} [Fintype ι]

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in

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

section NegativePlane

open scoped BigOperators

@[expose] public noncomputable section

open Classical

namespace Erdos99

variable {ι : Type*}

def quadForm (S : Finset ι) (W : ι → ι → ℝ) (f : ι → ℝ) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ S, W i j * f i * f j

def bilinForm (S : Finset ι) (W : ι → ι → ℝ) (f g : ι → ℝ) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ S, W i j * f i * g j

def NoNegativePlane (S : Finset ι) (W : ι → ι → ℝ) : Prop :=
  ∀ f g : ι → ℝ, ¬ ∀ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) → quadForm S W (fun i => a * f i + b * g i) < 0

lemma quadForm_eq_bilinForm (S : Finset ι) (W : ι → ι → ℝ) (f : ι → ℝ) :
    quadForm S W f = bilinForm S W f f := rfl

lemma quadForm_comb (S : Finset ι) (W : ι → ι → ℝ) (f g : ι → ℝ) (a b : ℝ) :
    quadForm S W (fun i => a * f i + b * g i) =
      a ^ 2 * bilinForm S W f f + a * b * (bilinForm S W f g + bilinForm S W g f) +
        b ^ 2 * bilinForm S W g g := by
  unfold quadForm bilinForm
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

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

section MinkowskiPlane

open scoped BigOperators Real

@[expose] public noncomputable section

namespace Erdos99

open Real Finset

def edgeForm (θ x y : ℝ) : ℝ := 2 * x * y / sin θ - cos θ / sin θ * (x ^ 2 + y ^ 2)

def edgeBilin (θ x y x' y' : ℝ) : ℝ :=
  (x * y' + x' * y) / sin θ - cos θ / sin θ * (x * x' + y * y')

def polyForm (k : ℕ) (θ g : ℕ → ℝ) : ℝ :=
  ∑ m ∈ range k, edgeForm (θ m) (g m) (g ((m + 1) % k))

def polyBilin (k : ℕ) (θ g g' : ℕ → ℝ) : ℝ :=
  ∑ m ∈ range k, edgeBilin (θ m) (g m) (g ((m + 1) % k)) (g' m) (g' ((m + 1) % k))

structure ValidGaps (k : ℕ) (θ : ℕ → ℝ) : Prop where
  three_le : 3 ≤ k
  pos : ∀ m < k, 0 < θ m
  lt_pi : ∀ m < k, θ m < π
  sum_eq : ∑ m ∈ range k, θ m = 2 * π

def NoPosPlane {α : Type*} (q : (α → ℝ) → ℝ) : Prop :=
  ∀ f g : α → ℝ, ¬ ∀ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) → 0 < q (fun m => a * f m + b * g m)

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

lemma edgeForm_parallelogram (α g₀ g₁ g₂ g₃ : ℝ) (hs : sin α ≠ 0) :
    edgeForm α g₀ g₁ + edgeForm (π - α) g₁ g₂ + edgeForm α g₂ g₃ + edgeForm (π - α) g₃ g₀ =
      2 / sin α * ((g₀ + g₂) * (g₁ + g₃)) := by
  unfold edgeForm
  rw [sin_pi_sub, cos_pi_sub]
  field_simp
  ring

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
  ·
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

section HilbertLorentz

open scoped BigOperators

@[expose] public noncomputable section

open Classical

namespace Erdos99

section Core

variable {κ : Type*} [Fintype κ]

def matBil (H : κ → κ → ℝ) (x w : κ → ℝ) : ℝ := ∑ i, ∑ j, H i j * x i * w j

def wNorm (D : κ → ℝ) (x : κ → ℝ) : ℝ := ∑ i, D i * x i ^ 2

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

def extS (S : Finset ι) (f : S → ℝ) (i : ι) : ℝ := if h : i ∈ S then f ⟨i, h⟩ else 0

lemma extS_coe (S : Finset ι) (f : S → ℝ) (i : S) : extS S f i = f i := by
  simp [extS, i.2]

theorem noNegativePlane_of_bochner {S : Finset ι} {W : ι → ι → ℝ} (hWs : ∀ i j, W i j = W j i)
    (hneg : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → W i j ≤ 0)
    (hconn : ∀ U ⊆ S, U.Nonempty → U ≠ S → ∃ i ∈ U, ∃ j ∈ S, j ∉ U ∧ W i j < 0)
    (h : ι → ℝ) (hh : ∀ i ∈ S, 0 < h i) (hb : ∀ i ∈ S, 0 < -∑ j ∈ S, W i j * h j)
    (hboch : ∀ f : ι → ℝ, -quadForm S W f ≤
      ∑ i ∈ S, h i / (-∑ j ∈ S, W i j * h j) * (∑ j ∈ S, W i j * f j) ^ 2) :
    NoNegativePlane S W := by
  intro f g hfg
  set c : ι → ℝ := fun i => -∑ j ∈ S, W i j * h j

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

section Polytope

open scoped BigOperators

@[expose] public noncomputable section

open Classical

namespace Erdos99

abbrev Space3 := EuclideanSpace ℝ (Fin 3)

variable {ι : Type*}

def polyK (S : Finset ι) (u : ι → Space3) (h : ι → ℝ) : Set Space3 :=
  {x | ∀ k ∈ S, inner ℝ (u k) x ≤ h k}

def polyFacet (S : Finset ι) (u : ι → Space3) (h : ι → ℝ) (i : ι) : Set Space3 :=
  {x | x ∈ polyK S u h ∧ inner ℝ (u i) x = h i}

def FacetsPresent (S : Finset ι) (u : ι → Space3) (h : ι → ℝ) : Prop :=
  ∀ i ∈ S, ∃ x : Space3, inner ℝ (u i) x = h i ∧ ∀ k ∈ S, k ≠ i → inner ℝ (u k) x < h k

def polytopeHessian (S : Finset ι) (u : ι → Space3) (h : ι → ℝ) (i j : ι) : ℝ :=
  if i = j then
    ∑ k ∈ S.erase i, Metric.diam (polyFacet S u h i ∩ polyFacet S u h k) /
      √(1 - inner ℝ (u i) (u k) ^ 2) * inner ℝ (u i) (u k)
  else
    -(Metric.diam (polyFacet S u h i ∩ polyFacet S u h j) / √(1 - inner ℝ (u i) (u j) ^ 2))

lemma polytopeHessian_symm (S : Finset ι) (u : ι → Space3) (h : ι → ℝ) (i j : ι) :
    polytopeHessian S u h i j = polytopeHessian S u h j i := by
  unfold polytopeHessian
  by_cases hij : i = j
  · subst hij; rfl
  · rw [if_neg hij, if_neg (Ne.symm hij), Set.inter_comm, real_inner_comm]

lemma polytopeHessian_offdiag_nonpos (S : Finset ι) (u : ι → Space3) (h : ι → ℝ) {i j : ι}
    (hij : i ≠ j) : polytopeHessian S u h i j ≤ 0 := by
  unfold polytopeHessian
  rw [if_neg hij, neg_nonpos]
  exact div_nonneg Metric.diam_nonneg (Real.sqrt_nonneg _)

end Erdos99
end

end Polytope

section PolytopeConnected

open scoped BigOperators
open Filter Topology

@[expose] public noncomputable section

open Classical

namespace Erdos99

variable {ι : Type*}

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

section Gauge

variable {S : Finset ι} {u : ι → Space3} {h : ι → ℝ}

def gaugeP (S : Finset ι) (hS : S.Nonempty) (u : ι → Space3) (h : ι → ℝ) (c d : Space3) : ℝ :=
  S.sup' hS (fun k => inner ℝ (u k) d / (h k - inner ℝ (u k) c))

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

lemma exists_generic_facet_point {S : Finset ι} {u : ι → Space3} {h : ι → ℝ} {b : ι}
    (hub : ‖u b‖ = 1) {q₀ : Space3} (hq₀ : inner ℝ (u b) q₀ = h b)
    (hq₀' : ∀ k ∈ S, k ≠ b → inner ℝ (u k) q₀ < h k) {c : Space3} (hcb : inner ℝ (u b) c < h b)
    (N : Finset Space3) (hN : ∀ n ∈ N, n ≠ 0) :
    ∃ q : Space3, inner ℝ (u b) q = h b ∧ (∀ k ∈ S, k ≠ b → inner ℝ (u k) q < h k) ∧
      ∀ n ∈ N, inner ℝ n (q - c) ≠ 0 := by
  have hub2 : inner ℝ (u b) (u b) = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, hub]; norm_num

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
        have := hc.continuousAt (x := 0) |>.eventually (gt_mem_nhds (by
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

  set P : Set Space3 := ⋃ i ∈ U, ⋃ j ∈ S \ U, (polyFacet S u h i ∩ polyFacet S u h j) with hPdef
  have hPfin : P.Finite := by
    refine Set.Finite.biUnion (Finset.finite_toSet U) fun i hi => ?_
    refine Set.Finite.biUnion (Finset.finite_toSet _) fun j hj => ?_
    have hj' := Finset.mem_sdiff.1 hj
    exact (hsub i hi j hj'.1 hj'.2).finite

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

section MixedVolume

open scoped BigOperators Real

@[expose] public noncomputable section

open Classical Real Finset

namespace Erdos99

variable {ι : Type*}

def vol3 (x y z : Space3) : ℝ :=
  x 0 * (y 1 * z 2 - y 2 * z 1) - x 1 * (y 0 * z 2 - y 2 * z 0) + x 2 * (y 0 * z 1 - y 1 * z 0)

lemma vol3_cyc (x y z : Space3) : vol3 y z x = vol3 x y z := by
  unfold vol3; ring

def linkSupport (u : ι → Space3) (nbr : ι → ℕ → ι) (i : ι) (f : ι → ℝ) (m : ℕ) : ℝ :=
  (f (nbr i m) - inner ℝ (u i) (u (nbr i m)) * f i) / √(1 - inner ℝ (u i) (u (nbr i m)) ^ 2)

def cornerTerm (cij cik cjk ai bi bj bk ci cj ck : ℝ) : ℝ :=
  ai * ((bj - cij * bi) * (ck - cik * ci) + (cj - cij * ci) * (bk - cik * bi) -
    (cjk - cij * cik) * ((bj - cij * bi) * (cj - cij * ci) / (1 - cij ^ 2) +
      (bk - cik * bi) * (ck - cik * ci) / (1 - cik ^ 2)))

lemma cornerTerm_cyc_symm (c12 c13 c23 a1 a2 a3 b1 b2 b3 x1 x2 x3 : ℝ)
    (h12 : 1 - c12 ^ 2 ≠ 0) (h13 : 1 - c13 ^ 2 ≠ 0) (h23 : 1 - c23 ^ 2 ≠ 0) :
    cornerTerm c12 c13 c23 a1 b1 b2 b3 x1 x2 x3 + cornerTerm c23 c12 c13 a2 b2 b3 b1 x2 x3 x1 +
        cornerTerm c13 c23 c12 a3 b3 b1 b2 x3 x1 x2 =
      cornerTerm c12 c13 c23 b1 a1 a2 a3 x1 x2 x3 + cornerTerm c23 c12 c13 b2 a2 a3 a1 x2 x3 x1 +
        cornerTerm c13 c23 c12 b3 a3 a1 a2 x3 x1 x2 := by
  unfold cornerTerm
  field_simp
  ring

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

structure LinkData (S : Finset ι) (u : ι → Space3) (k : ι → ℕ) (nbr : ι → ℕ → ι)
    (θ : ι → ℕ → ℝ) (T : Finset (ι × ι × ι)) : Prop where

  nondeg : ∀ i ∈ S, ∀ m < k i, inner ℝ (u i) (u (nbr i m)) ^ 2 < 1

  sin_ne : ∀ i ∈ S, ∀ m < k i, sin (θ i m) ≠ 0

  sin_eq : ∀ i ∈ S, ∀ m < k i,
    sin (θ i m) * (√(1 - inner ℝ (u i) (u (nbr i m)) ^ 2) *
      √(1 - inner ℝ (u i) (u (nbr i ((m + 1) % k i))) ^ 2)) =
      vol3 (u i) (u (nbr i m)) (u (nbr i ((m + 1) % k i)))

  cos_eq : ∀ i ∈ S, ∀ m < k i,
    cos (θ i m) * (√(1 - inner ℝ (u i) (u (nbr i m)) ^ 2) *
      √(1 - inner ℝ (u i) (u (nbr i ((m + 1) % k i))) ^ 2)) =
      inner ℝ (u (nbr i m)) (u (nbr i ((m + 1) % k i))) -
        inner ℝ (u i) (u (nbr i m)) * inner ℝ (u i) (u (nbr i ((m + 1) % k i)))

  tri_nondeg : ∀ t ∈ T, inner ℝ (u t.1) (u t.2.1) ^ 2 < 1 ∧ inner ℝ (u t.1) (u t.2.2) ^ 2 < 1 ∧
    inner ℝ (u t.2.1) (u t.2.2) ^ 2 < 1

  flags : ∀ F : ι → ι → ι → ℝ,
    ∑ i ∈ S, ∑ m ∈ range (k i), F i (nbr i m) (nbr i ((m + 1) % k i)) =
      ∑ t ∈ T, (F t.1 t.2.1 t.2.2 + F t.2.1 t.2.2 t.1 + F t.2.2 t.1 t.2.1)

def flagForm (u : ι → Space3) (a b c : ι → ℝ) (i j j' : ι) : ℝ :=
  cornerTerm (inner ℝ (u i) (u j)) (inner ℝ (u i) (u j')) (inner ℝ (u j) (u j'))
    (a i) (b i) (b j) (b j') (c i) (c j) (c j') / vol3 (u i) (u j) (u j')

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

section FacetLinks

open scoped BigOperators Real

@[expose] public noncomputable section

open Classical Real Finset

namespace Erdos99

variable {ι : Type*}

def edgeLen (k : ℕ) (θ p : ℕ → ℝ) (m : ℕ) : ℝ :=
  (p ((m + k - 1) % k) - p m * cos (θ ((m + k - 1) % k))) / sin (θ ((m + k - 1) % k)) +
    (p ((m + 1) % k) - p m * cos (θ m)) / sin (θ m)

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

section SimplicialFan

open scoped BigOperators

@[expose] public noncomputable section

open Classical

namespace Erdos99

variable {ι : Type*}

def finCone (v : ι → Space3) (τ : Finset ι) : Set Space3 :=
  {z | ∃ c : ι → ℝ, (∀ i ∈ τ, 0 ≤ c i) ∧ z = ∑ i ∈ τ, c i • v i}

structure IsSimplicialFan (S : Finset ι) (v : ι → Space3) (T : Finset (Finset ι)) : Prop where
  subset : ∀ τ ∈ T, τ ⊆ S
  card : ∀ τ ∈ T, τ.card = 3
  indep : ∀ τ ∈ T, LinearIndependent ℝ (fun i : τ => v i)
  complete : ∀ z : Space3, ∃ τ ∈ T, z ∈ finCone v τ
  inter : ∀ τ ∈ T, ∀ τ' ∈ T, finCone v τ ∩ finCone v τ' = finCone v (τ ∩ τ')

def FanEdge (T : Finset (Finset ι)) (i j : ι) : Prop :=
  i ≠ j ∧ ∃ τ ∈ T, i ∈ τ ∧ j ∈ τ

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
    funext i
    rfl
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

section FanGeometry

open scoped BigOperators
open Filter Topology

@[expose] public noncomputable section

open Classical

namespace Erdos99

variable {ι : Type*}

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

lemma add_le_one_of_unit {α β c : ℝ} (hc : c < 1) (hunit : α ^ 2 + β ^ 2 + 2 * α * β * c = 1)
    (hpos : ¬ (0 < α ∧ 0 < β)) : α + β ≤ 1 := by
  by_contra h
  push_neg at h
  rcases le_or_gt α 0 with h1 | h1
  · nlinarith [mul_nonpos_of_nonpos_of_nonneg h1 (show (0:ℝ) ≤ β by linarith)]
  · have : β ≤ 0 := by
      by_contra h2; exact hpos ⟨h1, by linarith⟩
    nlinarith [mul_nonpos_of_nonneg_of_nonpos h1.le this]

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

lemma IsSimplicialFan.coeff_eq_zero (hfan : IsSimplicialFan S u T) {τ : Finset ι} (hτ : τ ∈ T)
    (c : ι → ℝ) (hc : ∑ k ∈ τ, c k • u k = 0) : ∀ k ∈ τ, c k = 0 := by
  have hli := hfan.indep τ hτ
  rw [Fintype.linearIndependent_iff] at hli
  intro k hk
  have := hli (fun i : τ => c i) (by rw [← hc]; exact Finset.sum_coe_sort τ (fun i => c i • u i))
  exact this ⟨k, hk⟩

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
